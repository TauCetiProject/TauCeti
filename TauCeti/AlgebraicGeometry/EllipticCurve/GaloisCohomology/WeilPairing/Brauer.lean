/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local

/-!
# The Brauer-valued Weil cup product

Composing the Weil cup product with `H²(K, μ_m) → Br K` gives a bilinear pairing on
`H¹(K, E[m])`. Over a nonarchimedean local field its Brauer invariant is the local Tate
pairing read in `ℚ/ℤ`. This normalization allows local duality pairings to be compared with
the global Brauer sum formula.

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

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : K))

/-- The local Tate pairing, embedded in `ℚ/ℤ` by `k ↦ k/m`, is the Brauer invariant of the
Weil cup product. The exponent need only be invertible in the field, not in its residue field. -/
theorem toRatAddCircle_localTateWeilPairing
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    ZMod.toRatAddCircle m (W.localTateWeilPairing m hm a b) =
      invMap K (W.torsionWeilBrauerPairing m hm a b) := by
  rw [W.localTateWeilPairing_apply m hm, W.torsionWeilBrauerPairing_apply m hm]
  exact toRatAddCircle_h2MuEquivZMod K hm _

end WeierstrassCurve
