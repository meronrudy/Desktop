# Legal AI Inference API

A REST API for processing legal text through the neural inference pipeline, providing intermediate representations, court outcomes, realized text, and certificates.

## Features

- Upload legal text for processing
- Process text through the complete inference pipeline
- Retrieve IR (Intermediate Representation)
- Retrieve court outcomes
- Retrieve realized text
- Retrieve certificates
- Authentication via API key
- Input validation
- OpenAPI documentation

## Endpoints

### Health Check
- **GET** `/` - Check API health

### Authentication
- **POST** `/auth/register` - Register a new user account
- **POST** `/auth/login` - Login and obtain JWT token

### Upload Text
- **POST** `/api/upload-text`
  - Request: `{"text": "legal text here", "jurisdiction": "GENERAL"}`
  - Response: `{"processing_id": "uuid"}`

### Process Text
- **POST** `/api/process/{processing_id}`
  - Request: `{"jurisdiction": "GENERAL", "scenario": {...}}`
  - Response: `{"processing_id": "uuid"}`

### Retrieve Results
- **GET** `/api/results/{processing_id}/ir` - Get Intermediate Representation
- **GET** `/api/results/{processing_id}/outcome` - Get court outcome
- **GET** `/api/results/{processing_id}/realized-text` - Get realized text
- **GET** `/api/results/{processing_id}/certificate` - Get certificate

## Authentication

The API uses JWT (JSON Web Token) based authentication. You must register a user account and login to obtain an access token.

### User Registration
- **POST** `/auth/register`
  - Request: `{"username": "string", "email": "string", "password": "string", "role": "user"}`
  - Response: User details

### User Login
- **POST** `/auth/login`
  - Request: `{"username": "string", "password": "string"}`
  - Response: `{"access_token": "jwt_token", "token_type": "bearer"}`

### Using JWT Tokens
All API endpoints require a JWT token in the `Authorization` header:
```
Authorization: Bearer <jwt_token>
```

Tokens expire after 30 minutes. All processing endpoints require authentication.

## Installation

1. Install dependencies:
```bash
pip install -r requirements_api.txt -r neural_components/requirements.txt
```

2. Set environment variables:
```bash
cp .env.example .env
# Edit .env with your API key
```

3. Run the API:
```bash
python api.py
```

Or with uvicorn:
```bash
uvicorn api:app --host 0.0.0.0 --port 8000
```

## Docker

Build and run with Docker:
```bash
docker build -f Dockerfile.api -t legal-ai-api .
docker run -p 8000:8000 legal-ai-api
```

## Documentation

Visit `/docs` for interactive OpenAPI documentation.