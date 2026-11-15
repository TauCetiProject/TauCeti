// Exercise the actual inline workflow scripts with a mocked GitHub API.
// Run: node --test scripts/test_labels_from_comments.cjs
const assert = require('node:assert/strict');
const { readFileSync } = require('node:fs');
const { resolve } = require('node:path');
const { test } = require('node:test');

const workflow = readFileSync(resolve(__dirname, '../.github/workflows/labels-from-comments.yml'), 'utf8');
const scripts = [...workflow.matchAll(/^          script: \|\n((?:            .*\n|\n)+)/gm)]
  .map(match => match[1].replace(/^            /gm, ''));
assert.equal(scripts.length, 2);
const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
const parse = new AsyncFunction('context', 'core', scripts[0]);
const apply = new AsyncFunction('context', 'github', 'process', 'core', scripts[1]);
const issue = { owner: 'TauCetiProject', repo: 'test-repo', number: 123 };
// Evaluate the actual job condition with Actions' case-insensitive contains semantics.
const jobCondition = workflow.match(/^    if: >-\n((?:      .*\n)+)/m)[1];
const admit = new Function('github', 'contains', `return (${jobCondition});`);
const repository = workflow.match(/github.repository == '([^']+)'/)[1];
const needsRunner = (body, repo = repository, commenter = 1, author = 1, isPR = true) => admit({
  repository: repo, event: { comment: { body, user: { id: commenter } },
    issue: { user: { id: author }, pull_request: isPR ? {} : null } },
}, (value, search) => value.toLowerCase().includes(search.toLowerCase()));

async function commands(body) {
  let output;
  await parse({ payload: { comment: { body } } }, {
    setOutput: (name, value) => {
      assert.equal(name, 'labels');
      output = JSON.parse(value);
    },
  });
  return output;
}

async function execute(body, initial = [], failure, options = {}) {
  const labels = new Set(initial);
  const calls = [];
  const check = args => {
    assert.deepEqual([args.owner, args.repo, args.issue_number],
      [issue.owner, issue.repo, issue.number]);
    calls.push(args);
    if (failure) throw Object.assign(new Error('API failure'), { status: failure });
  };
  const head = 'a'.repeat(40);
  const payload = { comment: { node_id: 'COMMENT', user: { id: options.commenter ?? 1 } },
    issue: { pull_request: options.isPR === false ? null : {} } };
  const initialPull = { user: { id: options.author ?? 1 }, state: options.state ?? 'open', head: { sha: head } };
  let pullReads = 0, pageReads = 0;
  const github = { rest: { pulls: { get: async () => {
    pullReads++;
    return { data: pullReads === 1 ? initialPull : { ...initialPull, ...options.freshPull } };
  } }, issues: {
    addLabels: async args => {
      check(args);
      args.labels.forEach(label => labels.add(label));
    },
    removeLabel: async args => {
      check(args);
      if (!labels.delete(args.name)) throw Object.assign(new Error('absent'), { status: 404 });
    },
  } }, graphql: async (query, variables) => {
    assert.equal(variables.number, issue.number);
    const pages = options.pages ?? [[
      { __typename: 'PullRequestCommit', commit: { oid: head } },
      { __typename: 'IssueComment', id: 'COMMENT' },
    ]];
    const index = pageReads++;
    assert.equal(variables.before, index === 0 ? null : `page-${index}`);
    return { repository: { pullRequest: {
      headRefOid: options.timelineHead ?? head,
      timelineItems: { nodes: pages[index], pageInfo: { hasPreviousPage: index + 1 < pages.length, startCursor: `page-${index + 1}` } },
    } } };
  } };
  await apply({ issue, payload }, github, { env: { LABEL_COMMANDS: JSON.stringify(await commands(body)) } }, { info: () => {} });
  return { labels, calls, pullReads, pageReads };
}

test('exact standalone commands accept whitespace, CRLF, and multiword labels', async () => {
  assert.deepEqual(await commands('  dont-repair-in-queue \r\n\t-help wanted\r\ndocumentation'), [
    ['dont-repair-in-queue', true], ['help wanted', false], ['documentation', true],
  ]);
});

test('last instruction wins independently for each label', async () => {
  assert.deepEqual(await commands('enhancement\ndocumentation\n-enhancement\n-documentation\ndocumentation'), [
    ['enhancement', false], ['documentation', true],
  ]);
});

test('prose, quoted labels, case differences, and code remain inert', async () => {
  assert.deepEqual(await commands([
    // Mathlib's regression case: a bot directive ending in a label is not a command.
    'please add enhancement', '!downstream-check enhancement', '> enhancement', '`enhancement`', 'ENHANCEMENT',
    '- enhancement', 'help  wanted', 'enhancement, documentation', '$(touch /tmp/label-injection)',
    '${{ secrets.APP_PRIVATE_KEY }}', 'process.exit(1)',
  ].join('\n')), []);
});

test('authority and generated labels cannot be changed by comments', async () => {
  assert.deepEqual(await commands([
    'administrative-hold', '-administrative-hold', 'ai-approved', '-ai-approved',
    'ready-to-merge', '-bors-staging', 'on-hold', '-ci-failed',
    'roadmap/none', '-roadmap/Unknown',
  ].join('\n')), []);
});

test('retired default labels cannot be added or removed by comment', async () => {
  assert.deepEqual(await commands('bug\n-bug\nquestion\n-question\ngood first issue\n-good first issue'), []);
});

test('repository-specific labels match the documented policies', async () => {
  const roadmap = workflow.includes("github.repository == 'TauCetiProject/TauCetiRoadmap'");
  assert.deepEqual(await commands('hold\nkeep\nmathlib-overlap'), roadmap ? [] : [
    ['hold', true], ['keep', true], ['mathlib-overlap', true],
  ]);
  assert.deepEqual(await commands('awaiting-author\nawaiting-review\nawaiting-dependencies'), roadmap ? [
    ['awaiting-author', true], ['awaiting-review', true], ['awaiting-dependencies', true],
  ] : []);
});

test('add/remove preserves unrelated labels and targets the event issue or PR', async () => {
  const { labels, calls } = await execute('dont-repair-in-queue\n-enhancement', ['enhancement', 'bors-staging']);
  assert.deepEqual([...labels].sort(), ['bors-staging', 'dont-repair-in-queue']);
  assert.equal(calls.length, 2);
});

test('absent removals are harmless; unexpected API failures are visible', async () => {
  const { calls } = await execute('-enhancement\ndocumentation');
  assert.equal(calls.length, 2);
  for (const status of [403, 422, 500]) {
    await assert.rejects(execute('-enhancement', [], status), { status });
  }
  await assert.rejects(execute('enhancement', [], 404), { status: 404 });
});

test('unrecognized comments make no API calls', async () => {
  const { calls } = await execute('Thanks!');
  assert.deepEqual(calls, []);
});

test('ordinary conversation and queue merge notifications never request a runner', () => {
  for (const body of [
    'Thanks!', 'bors merge', '/review', '',
    'Pull request successfully merged into main.\n\nBuild succeeded:\n' +
      '  * [build](https://github.com/TauCetiProject/TauCeti/actions/runs/42531937757)\n\n' +
      'Merged revision: `1d5dafa62c122f5cce5cd8f1257ade2825f1ee87`.\n\n' +
      '<!-- tauceti-queue landed:TauCetiProject/TauCeti#29193:389:313801c5491a5bb896cc9a421071385ff92e7e7a -->',
  ]) assert.equal(needsRunner(body), false, body);
  assert.equal(needsRunner('dont-repair-in-queue', 'someone/fork'), false);
});

test('every allowlisted command passes admission with whitespace and CRLF', async () => {
  const allowed = [...scripts[0].match(/new Set\(\[([\s\S]*?)\]\)/)[1].matchAll(/'([^']+)'/g)]
    .map(match => match[1]);
  for (const label of allowed) {
    for (const prefix of ['', '-']) {
      const body = `Some context\r\n\t ${prefix}${label} \r\nThanks!`;
      assert.equal(needsRunner(body), true, body);
      assert.deepEqual(await commands(body), [[label, prefix === '']]);
    }
  }
});

test('broad admission never relaxes the exact command parser', async () => {
  for (const body of ['Please add documentation.', 'DONT-REPAIR-IN-QUEUE', '> enhancement']) {
    assert.equal(needsRunner(body), true);
    assert.deepEqual(await commands(body), []);
  }
});


test('self-tested author commands admit only PR authors before runner allocation', () => {
  assert.equal(needsRunner('self-tested'), true);
  assert.equal(needsRunner('-self-tested'), true);
  assert.equal(needsRunner('self-tested', repository, 2, 1), false);
  assert.equal(needsRunner('self-tested', repository, 1, 1, false), false);
});

test('PR authors can attest and withdraw self-tested without label permissions', async () => {
  const added = await execute('self-tested');
  assert.deepEqual([...added.labels], ['self-tested']);
  assert.equal(added.pullReads, 2);
  const removed = await execute('-self-tested', ['self-tested']);
  assert.equal(removed.labels.size, 0);
  assert.equal(removed.pageReads, 0);
});

test('self-tested authorization is enforced even when an ordinary label admits the job', async () => {
  for (const command of ['self-tested', '-self-tested']) {
    const result = await execute(`enhancement\n${command}`, [], undefined, { commenter: 2 });
    assert.deepEqual([...result.labels], ['enhancement']);
    assert.equal(result.calls.length, 1);
  }
  const issueResult = await execute('self-tested', [], undefined, { isPR: false });
  assert.equal(issueResult.calls.length, 0);
});

test('a comment before the current head or a force push never attests the new head', async () => {
  for (const event of [
    { __typename: 'PullRequestCommit', commit: { oid: 'a'.repeat(40) } },
    { __typename: 'HeadRefForcePushedEvent', afterCommit: { oid: 'a'.repeat(40) } },
  ]) {
    const result = await execute('self-tested', [], undefined, { pages: [[
      { __typename: 'IssueComment', id: 'COMMENT' }, event,
    ]] });
    assert.equal(result.calls.length, 0);
  }
});

test('head binding follows paginated timeline order and exact comment identity', async () => {
  const options = { pages: [
    [{ __typename: 'IssueComment', id: 'COMMENT' }],
    [{ __typename: 'PullRequestCommit', commit: { oid: 'a'.repeat(40) } }],
  ] };
  const result = await execute('self-tested', [], undefined, options);
  assert.deepEqual([...result.labels], ['self-tested']);
  assert.equal(result.pageReads, 2);
  const other = await execute('self-tested', [], undefined, { pages: [[
    { __typename: 'PullRequestCommit', commit: { oid: 'a'.repeat(40) } },
    { __typename: 'IssueComment', id: 'OTHER-COMMENT' },
  ]] });
  assert.equal(other.calls.length, 0);
});

test('closed PRs and racing heads cannot receive a self-tested attestation', async () => {
  for (const options of [
    { state: 'closed' }, { timelineHead: 'b'.repeat(40) },
    { freshPull: { state: 'closed' } }, { freshPull: { head: { sha: 'b'.repeat(40) } } },
  ]) {
    const result = await execute('self-tested', [], undefined, options);
    assert.equal(result.calls.length, 0);
  }
});
