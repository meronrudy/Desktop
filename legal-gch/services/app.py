import streamlit as st
import json
import bleach
import logging
import time
from neural_components.inference import main as run_inference
from neural_components.cert_verify import verify_certificate
from prometheus_client import start_http_server, Counter, Histogram, Gauge
from logstash_async.handler import AsynchronousLogstashHandler

# Setup structured logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Add Logstash handler if LOGSTASH_HOST is set
logstash_host = st.secrets.get("LOGSTASH_HOST", None)
if logstash_host:
    logger.addHandler(AsynchronousLogstashHandler(logstash_host, 5000, database_path=None))

# Prometheus metrics
REQUEST_COUNT = Counter('app_requests_total', 'Total requests', ['method', 'endpoint', 'status'])
REQUEST_LATENCY = Histogram('app_request_duration_seconds', 'Request duration', ['method', 'endpoint'])
ERROR_COUNT = Counter('app_errors_total', 'Total errors', ['type'])
ACTIVE_CONNECTIONS = Gauge('app_active_connections', 'Active connections')

# Start metrics server if METRICS_PORT is set
metrics_port = int(st.secrets.get("METRICS_PORT", 0))
if metrics_port:
    start_http_server(metrics_port)

st.title("Coq-Certified Legal AI Web App")

st.markdown("Upload legal text or input directly, select jurisdiction, and process through the inference pipeline to get IR, court outcomes, realized text, and verifiable Coq certificates.")

# Input section
st.header("Input Legal Text")
input_method = st.radio("Choose input method:", ("Upload file", "Enter text"))

text = ""
if input_method == "Upload file":
    uploaded_file = st.file_uploader("Choose a text file", type=["txt"])
    if uploaded_file is not None:
        if uploaded_file.size > 100000:
            st.error("File too large. Maximum size is 100KB.")
            logger.warning("Security event: Large file upload attempt", extra={'event': 'large_file_upload', 'file_size': uploaded_file.size})
        else:
            text = bleach.clean(uploaded_file.read().decode("utf-8"), tags=[], strip=True)
            st.text_area("Uploaded text:", text, height=200, disabled=True)
else:
    text = bleach.clean(st.text_area("Enter legal text:", height=200), tags=[], strip=True)

# Jurisdiction selector
jurisdiction = st.selectbox("Select Jurisdiction:", ("GENERAL", "GDPR_EU", "CONTRACT_NY"))

# Process button
if st.button("Process"):
    start_time = time.time()
    REQUEST_COUNT.labels(method='POST', endpoint='/process', status='started').inc()
    success = False
    try:
        # Rate limiting
        requests = st.session_state.get('requests', 0) + 1
        st.session_state.requests = requests
        if requests > 10:
            st.error("Rate limit exceeded. Please try again later.")
            logger.warning("Security event: Rate limit exceeded for session", extra={'event': 'rate_limit_exceeded', 'requests': requests})
            ERROR_COUNT.labels(type='rate_limit').inc()
            REQUEST_COUNT.labels(method='POST', endpoint='/process', status='rate_limit').inc()
        elif not text.strip():
            st.error("Please provide legal text.")
            logger.warning("Security event: Empty text input", extra={'event': 'empty_input'})
            ERROR_COUNT.labels(type='empty_input').inc()
            REQUEST_COUNT.labels(method='POST', endpoint='/process', status='bad_request').inc()
        elif len(text) > 10000:
            st.error("Text too long. Maximum 10000 characters.")
            logger.warning("Security event: Text input too long", extra={'event': 'input_too_long', 'length': len(text)})
            ERROR_COUNT.labels(type='input_too_long').inc()
            REQUEST_COUNT.labels(method='POST', endpoint='/process', status='bad_request').inc()
        else:
            logger.info("Processing inference for user", extra={'event': 'inference_start', 'jurisdiction': jurisdiction, 'text_length': len(text)})
            with st.spinner("Processing..."):
                result = run_inference(text, jurisdiction)
            processing_time = time.time() - start_time
            REQUEST_LATENCY.labels(method='POST', endpoint='/process').observe(processing_time)
            logger.info("Inference completed", extra={'event': 'inference_complete', 'processing_time': processing_time, 'certified': result.get('certified', False)})
            REQUEST_COUNT.labels(method='POST', endpoint='/process', status='success').inc()
            success = True
    except Exception as e:
        logger.error("Inference failed", extra={'event': 'inference_error', 'error': str(e)})
        ERROR_COUNT.labels(type='inference_error').inc()
        REQUEST_COUNT.labels(method='POST', endpoint='/process', status='error').inc()
        st.error("An error occurred during processing.")

    if success:

        # Display results
        st.header("Results")

        if "error" in result:
            st.error(result["error"])

        # Extracted IR
        st.subheader("Extracted Normative IR")
        st.json(result.get("ir", {}))

        # Court Outcomes
        st.subheader("Court Outcomes")
        st.json(result.get("outcome", {}))

        # Realized Text
        st.subheader("Realized Text")
        st.write(result.get("realized_text", ""))

        # Certification Status
        st.subheader("Certification Status")
        certified = result.get("certified", False)
        if certified:
            st.success("IR Certified by Coq")
        else:
            st.warning("IR Not Certified")

        # Coq Certificate
        st.subheader("Coq Certificate")
        certificate = result.get("certificate")
        if certificate:
            st.json(certificate)

            # Download button
            cert_json = json.dumps(certificate, indent=2)
            st.download_button(
                label="Download Certificate",
                data=cert_json,
                file_name="certificate.json",
                mime="application/json"
            )

            # Verify certificate
            st.subheader("Verify Certificate")
            if st.button("Verify"):
                verified = verify_certificate(certificate)
                if verified:
                    st.success("Certificate verified successfully")
                else:
                    st.error("Certificate verification failed")
        else:
            st.write("No certificate generated")

        # View Proof Details
        st.subheader("Proof Details")
        if certified:
            try:
                with open("GeneratedIR.v", "r") as f:
                    coq_code = f.read()
                st.code(coq_code, language="coq")
            except FileNotFoundError:
                st.write("Coq proof code not found.")
        else:
            st.write("No proof available as IR was not certified.")