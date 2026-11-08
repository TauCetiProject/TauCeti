// Exercise the actual inline workflow scripts with a mocked GitHub API.
// Run: node --test .github/scripts/test-labels-from-comments.cjs
const assert = require('node:assert/strict');
const { readFileSync } = require('node:fs');
const { resolve } = require('node:path');
const { test } = require('node:test');

const workflow = readFileSync(resolve(__dirname, '../workflows/labels-from-comments.yml'), 'utf8');
const scripts = [...workflow.matchAll(/^          script: \|\n((?:            .*\n|\n)+)/gm)]
  .map(match => match[1].replace(/^            /gm, ''));
assert.equal(scripts.length, 2);
const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
const parse = new AsyncFunction('context', 'core', scripts[0]);
const apply = new AsyncFunction('context', 'github', 'process', scripts[1]);
const issue = { owner: 'TauCetiProject', repo: 'test-repo', number: 123 };

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

async function execute(body, initial = [], failure) {
  const labels = new Set(initial);
  const calls = [];
  const check = args => {
    assert.deepEqual([args.owner, args.repo, args.issue_number],
      [issue.owner, issue.repo, issue.number]);
    calls.push(args);
    if (failure) throw Object.assign(new Error('API failure'), { status: failure });
  };
  const github = { rest: { issues: {
    addLabels: async args => {
      check(args);
      args.labels.forEach(label => labels.add(label));
    },
    removeLabel: async args => {
      check(args);
      if (!labels.delete(args.name)) throw Object.assign(new Error('absent'), { status: 404 });
    },
  } } };
  await apply({ issue }, github, { env: { LABEL_COMMANDS: JSON.stringify(await commands(body)) } });
  return { labels, calls };
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
