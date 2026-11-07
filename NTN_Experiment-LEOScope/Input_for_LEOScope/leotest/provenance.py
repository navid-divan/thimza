"""Digests of the code that runs, so that a result can be tied to a source tree."""
import hashlib
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TREES = ("thimza", "tests", "experiments", "leotest")


def file_digests(subdir):
    base = os.path.join(ROOT, subdir)
    out = {}
    for folder, _, files in os.walk(base):
        for name in sorted(files):
            if not name.endswith(".py"):
                continue
            path = os.path.join(folder, name)
            with open(path, "rb") as handle:
                out[os.path.relpath(path, ROOT)] = hashlib.sha256(handle.read()).hexdigest()
    return dict(sorted(out.items()))


def tree_digest(digests):
    joined = "".join("%s %s\n" % (path, value) for path, value in sorted(digests.items()))
    return hashlib.sha256(joined.encode()).hexdigest()


def report():
    trees = {}
    for subdir in TREES:
        digests = file_digests(subdir)
        trees[subdir] = {"tree_sha256": tree_digest(digests), "files": digests}
    return trees


if __name__ == "__main__":
    for name, entry in report().items():
        print("%-12s %s (%d files)" % (name, entry["tree_sha256"], len(entry["files"])))
