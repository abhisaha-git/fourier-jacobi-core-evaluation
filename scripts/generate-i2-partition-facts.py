"""Generate definitional simplifier facts for the integer partition proof."""
from pathlib import Path
root=Path(__file__).resolve().parents[1]
g=root/'scripts/generate-i2-domains.py'
x={'__file__':str(g)}
exec(g.read_text(encoding='utf-8').split("s = '''")[0],x)
p=root/'FourierJacobi/Analysis/I2Predicates.lean'
facts=''
mp={'k':'p.1','j':'p.2.1','h':'p.2.2'}
for i,r in enumerate(x['rows']):
    facts+=f"@[simp] theorem i2SpatialPredicate_row{i} (p : ℤ × ℤ × ℤ) : i2SpatialPredicate {i} p ↔ ({x['subst'](r[1],mp)}) := Iff.rfl\n"
    facts+=f"@[simp] theorem i2DepthPredicate_row{i} (c : ℕ) : i2DepthPredicate {i} c ↔ ({r[-1]}) := Iff.rfl\n"
s='import FourierJacobi.Analysis.I2Domains\n\nnamespace FourierJacobi.Analysis\n\n'+facts+'\nend FourierJacobi.Analysis\n'
p.write_text(s,encoding='utf-8')
