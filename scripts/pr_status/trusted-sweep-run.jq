.repository.full_name == "TauCetiProject/TauCeti" and
.path == ".github/workflows/pr-labels.yml" and
(.event == "schedule" or .event == "workflow_dispatch") and
.head_branch == "main" and .head_repository.full_name == "TauCetiProject/TauCeti"
