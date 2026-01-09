"""
REST API for Legal AI Inference Pipeline
Provides endpoints for uploading legal text, processing through inference, and retrieving results.
"""

from fastapi import FastAPI, HTTPException, Depends, UploadFile, File, Header
from fastapi.responses import JSONResponse
from pydantic import BaseModel, Field
from typing import Optional, Dict, Any
import uuid
import json
import os
from dotenv import load_dotenv
import sys
from datetime import timedelta
from collections import defaultdict

# Add processing/neural to path
sys.path.append('./processing/neural')
try:
    from inference import main as inference_main
except ImportError:
    # Mock for testing without neural dependencies
    def inference_main(text, jurisdiction, scenario):
        return {
            "ir": {"mock": "ir"},
            "outcome": {"mock": "outcome"},
            "realized_text": "Mock realized text",
            "certified": True,
            "certificate": {"mock": "certificate"}
        }
from database import get_db, User, Tenant
from sqlalchemy.orm import Session
from auth import authenticate_user, create_access_token, get_current_active_user, require_role, get_password_hash

load_dotenv()

app = FastAPI(
    title="Legal AI Inference API",
    description="REST API for processing legal text through neural inference pipeline",
    version="1.0.0"
)

# In-memory storage for demo (use database in production)
# results_store[tenant_id][processing_id] = data
results_store = defaultdict(dict)

# Pydantic Models
class TenantCreate(BaseModel):
    name: str = Field(..., min_length=1, max_length=100, description="Tenant name")
    description: Optional[str] = Field(None, description="Tenant description")

class TenantResponse(BaseModel):
    id: int
    name: str
    description: Optional[str]
    is_active: bool

class UserCreate(BaseModel):
    username: str = Field(..., min_length=3, max_length=50, description="Username")
    email: str = Field(..., description="Email address")
    password: str = Field(..., min_length=8, description="Password")
    role: Optional[str] = Field("user", description="User role (admin or user)")
    tenant_id: Optional[int] = Field(None, description="Tenant ID to associate user with (optional for initial setup)")

class UserLogin(BaseModel):
    username: str = Field(..., description="Username")
    password: str = Field(..., description="Password")

class Token(BaseModel):
    access_token: str
    token_type: str = "bearer"

class UserResponse(BaseModel):
    id: int
    username: str
    email: str
    role: str
    is_active: bool
    tenant_id: int

class UploadTextRequest(BaseModel):
    text: str = Field(..., min_length=1, max_length=100000, description="Legal text to process")
    jurisdiction: str = Field("GENERAL", description="Jurisdiction for processing")

class ProcessRequest(BaseModel):
    jurisdiction: str = Field("GENERAL", description="Jurisdiction for processing")
    scenario: Optional[Dict[str, Any]] = Field(None, description="Scenario parameters for outcome computation")

class ProcessingResponse(BaseModel):
    processing_id: str = Field(..., description="Unique ID for the processing request")

class ResultResponse(BaseModel):
    status: str = Field(..., description="Processing status")
    data: Optional[Any] = Field(None, description="Result data if available")

@app.get("/")
async def root():
    """Health check endpoint"""
    return {"status": "healthy", "service": "Legal AI Inference API"}

@app.post("/tenants", response_model=TenantResponse)
async def create_tenant(tenant: TenantCreate, current_user: User = Depends(require_role("admin")), db: Session = Depends(get_db)):
    """Create a new tenant (admin only)"""
    # Check if tenant exists
    db_tenant = db.query(Tenant).filter(Tenant.name == tenant.name).first()
    if db_tenant:
        raise HTTPException(status_code=400, detail="Tenant name already exists")

    # Create tenant
    db_tenant = Tenant(
        name=tenant.name,
        description=tenant.description
    )
    db.add(db_tenant)
    db.commit()
    db.refresh(db_tenant)
    return db_tenant

@app.get("/tenants", response_model=list[TenantResponse])
async def list_tenants(current_user: User = Depends(get_current_active_user), db: Session = Depends(get_db)):
    """List all active tenants"""
    tenants = db.query(Tenant).filter(Tenant.is_active == True).all()
    return tenants

@app.post("/auth/register", response_model=UserResponse)
async def register_user(user: UserCreate, db: Session = Depends(get_db)):
    """Register a new user"""
    # Check if user exists
    db_user = db.query(User).filter((User.username == user.username) | (User.email == user.email)).first()
    if db_user:
        raise HTTPException(status_code=400, detail="Username or email already registered")

    # Handle tenant
    tenant_id = user.tenant_id
    if tenant_id is None:
        # For initial setup, create default tenant if none exist
        default_tenant = db.query(Tenant).first()
        if not default_tenant:
            default_tenant = Tenant(name="Default", description="Default tenant for initial setup")
            db.add(default_tenant)
            db.commit()
            db.refresh(default_tenant)
        tenant_id = default_tenant.id
    else:
        # Check if tenant exists
        tenant = db.query(Tenant).filter(Tenant.id == tenant_id).first()
        if not tenant:
            raise HTTPException(status_code=400, detail="Tenant does not exist")

    # Only allow admin role if no users exist yet (for initial admin setup)
    if user.role == "admin":
        existing_admin = db.query(User).filter(User.role == "admin").first()
        if existing_admin:
            raise HTTPException(status_code=403, detail="Cannot create admin user")

    # Create user
    hashed_password = get_password_hash(user.password)
    db_user = User(
        username=user.username,
        email=user.email,
        hashed_password=hashed_password,
        role=user.role,
        tenant_id=tenant_id
    )
    db.add(db_user)
    db.commit()
    db.refresh(db_user)
    return db_user

@app.post("/auth/login", response_model=Token)
async def login_user(user: UserLogin, db: Session = Depends(get_db)):
    """Login user and return JWT token"""
    db_user = authenticate_user(db, user.username, user.password)
    if not db_user:
        raise HTTPException(status_code=401, detail="Incorrect username or password")

    access_token_expires = timedelta(minutes=30)
    access_token = create_access_token(
        data={"sub": db_user.username}, expires_delta=access_token_expires
    )
    return {"access_token": access_token, "token_type": "bearer"}

@app.post("/api/upload-text", response_model=ProcessingResponse)
async def upload_text(
    request: UploadTextRequest,
    current_user: User = Depends(get_current_active_user)
):
    """Upload legal text for processing"""
    try:
        processing_id = str(uuid.uuid4())
        tenant_id = current_user.tenant_id
        results_store[tenant_id][processing_id] = {
            "text": request.text,
            "jurisdiction": request.jurisdiction,
            "status": "uploaded"
        }
        return ProcessingResponse(processing_id=processing_id)
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/api/process/{processing_id}", response_model=ProcessingResponse)
async def process_text(
    processing_id: str,
    request: ProcessRequest,
    current_user: User = Depends(get_current_active_user)
):
    """Process the uploaded text through the inference pipeline"""
    tenant_id = current_user.tenant_id
    if processing_id not in results_store[tenant_id]:
        raise HTTPException(status_code=404, detail="Processing ID not found")

    data = results_store[tenant_id][processing_id]
    if data["status"] != "uploaded":
        raise HTTPException(status_code=400, detail="Text already processed")

    try:
        # Run inference
        result = inference_main(data["text"], request.jurisdiction, request.scenario)
        data.update({
            "status": "processed",
            "result": result
        })
        return ProcessingResponse(processing_id=processing_id)
    except Exception as e:
        data["status"] = "error"
        data["error"] = str(e)
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/api/results/{processing_id}/ir", response_model=ResultResponse)
async def get_ir(
    processing_id: str,
    current_user: User = Depends(get_current_active_user)
):
    """Retrieve Intermediate Representation (IR)"""
    tenant_id = current_user.tenant_id
    if processing_id not in results_store[tenant_id]:
        raise HTTPException(status_code=404, detail="Processing ID not found")

    data = results_store[tenant_id][processing_id]
    if data["status"] != "processed":
        return ResultResponse(status=data["status"])

    return ResultResponse(status="success", data=data["result"]["ir"])

@app.get("/api/results/{processing_id}/outcome", response_model=ResultResponse)
async def get_outcome(
    processing_id: str,
    current_user: User = Depends(get_current_active_user)
):
    """Retrieve court outcome"""
    tenant_id = current_user.tenant_id
    if processing_id not in results_store[tenant_id]:
        raise HTTPException(status_code=404, detail="Processing ID not found")

    data = results_store[tenant_id][processing_id]
    if data["status"] != "processed":
        return ResultResponse(status=data["status"])

    return ResultResponse(status="success", data=data["result"]["outcome"])

@app.get("/api/results/{processing_id}/realized-text", response_model=ResultResponse)
async def get_realized_text(
    processing_id: str,
    current_user: User = Depends(get_current_active_user)
):
    """Retrieve realized text"""
    tenant_id = current_user.tenant_id
    if processing_id not in results_store[tenant_id]:
        raise HTTPException(status_code=404, detail="Processing ID not found")

    data = results_store[tenant_id][processing_id]
    if data["status"] != "processed":
        return ResultResponse(status=data["status"])

    return ResultResponse(status="success", data=data["result"]["realized_text"])

@app.get("/api/results/{processing_id}/certificate", response_model=ResultResponse)
async def get_certificate(
    processing_id: str,
    current_user: User = Depends(get_current_active_user)
):
    """Retrieve certificate"""
    tenant_id = current_user.tenant_id
    if processing_id not in results_store[tenant_id]:
        raise HTTPException(status_code=404, detail="Processing ID not found")

    data = results_store[tenant_id][processing_id]
    if data["status"] != "processed":
        return ResultResponse(status=data["status"])

    return ResultResponse(status="success", data=data["result"]["certificate"])

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)