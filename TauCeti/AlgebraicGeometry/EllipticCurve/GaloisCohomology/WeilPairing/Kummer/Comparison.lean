/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.KummerComparison
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny

/-!
# Isogeny Weil cups and multiplication Kummer classes

For an isogeny `φ : E₁ → E₂` of degree `n` invertible in the base field, the maps
`ι : E₁[φ] → E₁[n]` and `π : E₁[n] → E₂[φ̂]` are adjoint for the Weil pairings. Hence

`e_φ(a ∪ π_* b) = e_n(ι_* a ∪ b)`.

On Kummer classes this becomes

`e_φ(δ_φ(Q) ∪ δ_φ̂(P)) = e_n(δ_n(φ̂ Q) ∪ δ_n(P))`.

Thus orthogonality of multiplication Kummer images suffices for orthogonality of the isogeny and
dual-isogeny Kummer images over any field. This comparison identity does not itself assert
orthogonality; its specialization to local Tate duality is in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/Local.lean`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §2.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

variable [DecidableEq K]

/-- The cup product of the isogeny and dual-isogeny Kummer classes is computed by the
multiplication-by-degree Kummer classes of `φ̂ Q` and `P`. -/
theorem kerH1WeilPairing_kummerMap (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    φ.kerH1WeilPairing hn (φ.kummerMap Q) (φ.dual.kummerMap P) =
      W₁.torsionH1WeilPairing φ.degree hn
        (W₁.kummerMap φ.degree hn ((ofIsogeny φ.dual).pointMap Q))
        (W₁.kummerMap φ.degree hn P) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  rw [← φ.explicitCoeff1_torsionCoeffToDualKerCoeff_kummerMap hn,
    kerH1WeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff,
    explicitCoeff1_kerCoeffToTorsionCoeff_kummerMap]

end TauCeti.Isogeny
