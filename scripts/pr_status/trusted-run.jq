.repository.full_name == "TauCetiProject/TauCeti" and
.path == ".github/workflows/pr-status.yml" and
(.event == "pull_request_target" or
  ((.event == "workflow_run" or .event == "issue_comment" or .event == "schedule" or .event == "workflow_dispatch") and
    .head_branch == "main" and .head_repository.full_name == "TauCetiProject/TauCeti"))
