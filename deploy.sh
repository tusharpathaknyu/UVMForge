#!/bin/bash
# UVMForge - Google Cloud Run Deployment Script

set -e

# Configuration
PROJECT_ID="${GCP_PROJECT_ID:-your-project-id}"
REGION="${GCP_REGION:-us-central1}"
SERVICE_NAME="uvmforge"
IMAGE_NAME="gcr.io/${PROJECT_ID}/${SERVICE_NAME}"

echo "🚀 UVMForge Cloud Run Deployment"
echo "================================"
echo "Project: ${PROJECT_ID}"
echo "Region: ${REGION}"
echo "Image: ${IMAGE_NAME}"
echo ""

# Check if gcloud is installed
if ! command -v gcloud &> /dev/null; then
    echo "❌ gcloud CLI not found. Please install: https://cloud.google.com/sdk/docs/install"
    exit 1
fi

# Check authentication
echo "🔐 Checking authentication..."
gcloud auth print-access-token > /dev/null 2>&1 || {
    echo "❌ Not authenticated. Run: gcloud auth login"
    exit 1
}

# Set project
echo "📋 Setting project..."
gcloud config set project ${PROJECT_ID}

# Enable required APIs
echo "🔧 Enabling required APIs..."
gcloud services enable \
    cloudbuild.googleapis.com \
    run.googleapis.com \
    secretmanager.googleapis.com \
    containerregistry.googleapis.com

# Create secrets (if API keys are provided)
echo "🔑 Setting up secrets..."

# Check and create Google API key secret (for Gemini)
if [ -n "${GOOGLE_API_KEY}" ]; then
    if ! gcloud secrets describe google-api-key --project=${PROJECT_ID} > /dev/null 2>&1; then
        echo "Creating google-api-key secret..."
        echo -n "${GOOGLE_API_KEY}" | gcloud secrets create google-api-key \
            --replication-policy="automatic" \
            --data-file=-
    else
        echo "google-api-key secret already exists"
    fi
fi

# Check and create OpenAI API key secret (optional)
if [ -n "${OPENAI_API_KEY}" ]; then
    if ! gcloud secrets describe openai-api-key --project=${PROJECT_ID} > /dev/null 2>&1; then
        echo "Creating openai-api-key secret..."
        echo -n "${OPENAI_API_KEY}" | gcloud secrets create openai-api-key \
            --replication-policy="automatic" \
            --data-file=-
    else
        echo "openai-api-key secret already exists"
    fi
fi

# Build and push Docker image
echo "🐳 Building Docker image..."
gcloud builds submit --tag ${IMAGE_NAME}:latest .

# Deploy to Cloud Run
echo "☁️ Deploying to Cloud Run..."

# Base deployment command
DEPLOY_CMD="gcloud run deploy ${SERVICE_NAME} \
    --image ${IMAGE_NAME}:latest \
    --platform managed \
    --region ${REGION} \
    --allow-unauthenticated \
    --memory 2Gi \
    --cpu 2 \
    --timeout 300 \
    --min-instances 0 \
    --max-instances 10"

# Add secrets if they exist
if [ -n "${GOOGLE_API_KEY}" ]; then
    DEPLOY_CMD="${DEPLOY_CMD} --set-secrets GOOGLE_API_KEY=google-api-key:latest"
fi

# Execute deployment
eval ${DEPLOY_CMD}

# Get service URL
SERVICE_URL=$(gcloud run services describe ${SERVICE_NAME} --region ${REGION} --format 'value(status.url)')

echo ""
echo "✅ Deployment complete!"
echo "========================"
echo "Service URL: ${SERVICE_URL}"
echo ""
echo "🔗 Quick links:"
echo "  - Application: ${SERVICE_URL}"
echo "  - Health: ${SERVICE_URL}/_stcore/health"
echo ""
echo "🎉 UVMForge is now live!"
echo ""
echo "📝 To generate a UVM testbench:"
echo "  1. Open ${SERVICE_URL}"
echo "  2. Enter your specification in natural language"
echo "  3. Click 'Generate UVM Testbench'"
echo "  4. Download your generated files!"
