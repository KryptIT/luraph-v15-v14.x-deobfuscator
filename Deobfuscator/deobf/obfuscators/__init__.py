"""
Obfuscator registry and detection.

To add an obfuscator: write a plugin (a module or package in this folder
with an `Obfuscator` subclass, see base.py and generic.py), then add an
instance to PLUGINS below. deob.py picks the plugin whose detect() is most
confident; `--obfuscator NAME` forces one.
"""
from obfuscators.base import Obfuscator, Job  # noqa: F401
from obfuscators.luraph_v15 import LuraphV15
from obfuscators.ironbrew1 import Ironbrew1
from obfuscators.generic import Generic

PLUGINS = [
    LuraphV15(),
    Ironbrew1(),
    Generic(),      # fallback: behaviour trace only
]

MIN_CONFIDENCE = 0.5    # below this the input counts as unrecognized (the fallback runs)


def by_name(name):
    for p in PLUGINS:
        if p.name == name:
            return p
    raise KeyError("unknown obfuscator %r (known: %s)" % (name, ", ".join(p.name for p in PLUGINS)))


def scores(source):
    """[(confidence, plugin)], most confident first."""
    out = []
    for p in PLUGINS:
        try:
            c = p.detect(source)
        except Exception:  # noqa: BLE001 - a broken detector must not stop the others
            c = 0.0
        out.append((c, p))
    return sorted(out, key=lambda cp: -cp[0])


def detect(source):
    """(plugin, confidence) for `source`; the generic fallback when no
    plugin is confident enough."""
    best = scores(source)[0]
    if best[0] >= MIN_CONFIDENCE:
        return best[1], best[0]
    return by_name(Generic.name), best[0] if best[1].name == Generic.name else 0.0
