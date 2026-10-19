"""Resolve a live bors batch to its staging ref.

Train batches use immutable candidate refs; serial batches use mutable staging.
"""
import argparse
import sys

from bors_observation import observation, requested_batch


def candidate_ref(data, head, base, *, batch_id, branch="main"):
    batch = requested_batch(data, head, base, batch_id=batch_id, branch=branch)
    train = batch.get("train")
    if train is None:
        return "staging"
    if not isinstance(train, dict):
        raise ValueError("invalid bors train")
    cid, generation = train.get("candidate_id"), train.get("generation")
    if type(cid) is not int or cid <= 0 or type(generation) is not int or generation <= 0:
        raise ValueError("invalid bors generation")
    ref = f"staging-candidate-{cid}-{generation}"
    if train.get("staging_ref") != ref:
        raise ValueError("invalid bors candidate ref")
    return ref


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--batch-id", type=int, required=True)
    parser.add_argument("--branch", required=True)
    args = parser.parse_args()
    try:
        data = observation(args.batch_id, args.branch)
        print(candidate_ref(data, args.head, args.base, batch_id=args.batch_id, branch=args.branch))
    except (KeyError, TypeError, ValueError, OSError) as error:
        print(f"bors identity unavailable: {type(error).__name__}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
