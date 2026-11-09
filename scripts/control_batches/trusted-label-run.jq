.repository.full_name == "TauCetiProject/TauCeti" and
.path == ".github/workflows/roadmap-label-reconcile.yml" and
(.event == "pull_request_target" or
  ((.event == "schedule" or .event == "workflow_dispatch") and
    .head_branch == "main" and .head_repository.full_name == "TauCetiProject/TauCeti"))
