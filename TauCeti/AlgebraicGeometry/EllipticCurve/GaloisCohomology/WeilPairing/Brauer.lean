/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cohomology
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Torsion

/-!
# The Brauer-valued Weil cup product

Composing the Weil cup product with `H²(K, μ_m) → Br K` gives a bilinear pairing on
`H¹(K, E[m])` over any field. Its comparison with the local Tate pairing is proved in
`WeilPairing.Local`; this module does not require local-field hypotheses.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : K))

/-- The Weil cup product, followed by the inclusion `H²(K, μ_m) → Br K`.
It is bilinear on the first cohomology of elliptic torsion. -/
def torsionWeilBrauerPairing : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+
    H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+ Br K :=
  (AddMonoidHom.compHom ((h2MuToBr m K).comp
    (muNRepH2Equiv m K).toAddMonoidHom)).comp (W.torsionH1WeilPairing m hm)

/-- The Brauer-valued pairing is the image of the Weil cup product. -/
@[simp]
theorem torsionWeilBrauerPairing_apply
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    W.torsionWeilBrauerPairing m hm a b =
      h2MuToBr m K (muNRepH2Equiv m K (W.torsionH1WeilPairing m hm a b)) :=
  (rfl)

end WeierstrassCurve
