#!/bin/bash

# Deployment script for Kubernetes

set -e

# Configuration
K8S_NAMESPACE=${K8S_NAMESPACE:-"default"}
STREAMLIT_IMAGE="gcr.io/legal-ai-project-2026/streamlit-app:latest"  # Update with actual registry
NEURAL_IMAGE="gcr.io/legal-ai-project-2026/neural-service:latest"    # Update with actual registry

echo "Building and pushing Streamlit image..."
gcloud builds submit --tag $STREAMLIT_IMAGE --dockerfile Dockerfile.streamlit .

echo "Building and pushing Neural image..."
gcloud builds submit --tag $NEURAL_IMAGE --dockerfile Dockerfile.neural .

echo "Deploying Streamlit app to Cloud Run..."
gcloud run deploy streamlit-app --image $STREAMLIT_IMAGE --platform managed --region us-central1 --allow-unauthenticated

echo "Deploying Neural service to Cloud Run..."
gcloud run deploy neural-service --image $NEURAL_IMAGE --platform managed --region us-central1 --allow-unauthenticated

echo "Deployment complete!"
echo "Streamlit URL: $(gcloud run services describe streamlit-app --region us-central1 --format 'value(status.url)')"
echo "Neural URL: $(gcloud run services describe neural-service --region us-central1 --format 'value(status.url)')"