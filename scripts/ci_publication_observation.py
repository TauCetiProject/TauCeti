#!/usr/bin/env python3
"""Observe the workflow-pinned publisher's validated, frozen upload plan.

The planner already distinguishes uploaded and inherited artifacts. Never infer
upload volume from candidate staging or reimplement its mapping parser here.
No keys are used; observations never decide publication success.
"""
import argparse
import json
import os
from pathlib import Path
import stat

MAX_METRICS = 64 * 1024
MAX_MAP = 16 * 1024 * 1024


def measure(plan):
    result = {'staged_objects': 0, 'staged_bytes': 0, 'complete': False,
              'volume_scope': 'planned-upload-artifacts-plus-full-revision-map', 'missing': []}
    directory = None
    try:
        directory = os.open(plan, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        def open_regular(name, limit):
            fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory)
            info = os.fstat(fd)
            if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
                os.close(fd)
                raise ValueError('invalid plan file')
            return fd, info.st_size
        fd, _ = open_regular('metrics.json', MAX_METRICS)
        with os.fdopen(fd, 'rb') as handle:
            raw = handle.read(MAX_METRICS + 1)
        if len(raw) > MAX_METRICS:
            raise ValueError('oversized planner statistics')
        metrics = json.loads(raw)
        keys = ('objects', 'inherited', 'uploaded_objects', 'upload_bytes', 'full_bytes')
        if not isinstance(metrics, dict) or any(
                type(metrics.get(k)) is not int or metrics[k] < 0 for k in keys):
            raise ValueError('invalid planner statistics')
        if (metrics['objects'] != metrics['inherited'] + metrics['uploaded_objects']
                or metrics['upload_bytes'] > metrics['full_bytes']):
            raise ValueError('inconsistent planner statistics')
        fd, map_bytes = open_regular('outputs.jsonl', MAX_MAP)
        os.close(fd)
        if not map_bytes:
            raise ValueError('empty revision map')
        result.update(staged_objects=metrics['uploaded_objects'] + 1,
                      staged_bytes=metrics['upload_bytes'] + map_bytes,
                      inherited_objects=metrics['inherited'], full_artifact_bytes=metrics['full_bytes'],
                      revision_map_bytes=map_bytes, complete=True)
    except (OSError, ValueError, TypeError):
        result['missing'].append('validated-publication-plan-unavailable')
    finally:
        if directory is not None:
            os.close(directory)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', required=True)
    parser.add_argument('--out', required=True)
    args = parser.parse_args()
    value = {'schema': 'tauceti-ci.publication/v1', 'trust': 'publisher-host',
             'run_id': os.environ['GITHUB_RUN_ID'],
             'run_attempt': int(os.environ['GITHUB_RUN_ATTEMPT']),
             'uploaded': os.environ.get('UPLOADED') == 'true',
             'confirmed': os.environ.get('CONFIRMED') == 'true', **measure(args.plan)}
    Path(args.out).write_text(json.dumps(value) + '\n')


if __name__ == '__main__':
    main()
