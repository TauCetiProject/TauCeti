/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.RepresentationTheory.Homological.ContCohomology.DeltaNaturality

/-!
# Comparing isogeny and multiplication Kummer maps

For an isogeny `φ : E₁ → E₂` of degree `n` invertible in the base field, write `ι` for
`E₁[φ] → E₁[n]` and `π` for `E₁[n] → E₂[φ̂]`. The two morphisms of Kummer sequences give

* `ι_* δ_φ(Q) = δ_n(φ̂ Q)`;
* `π_* δ_n(P) = δ_φ̂(P)`.

In particular, `π_*` maps the multiplication Kummer image onto the dual-isogeny Kummer image.
Together with compatibility of the Weil cup products, these identities reduce orthogonality
of the two isogeny Kummer images to orthogonality for multiplication by `n`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §2.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom

variable {K : Type*} [Field K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- Inclusion of the isogeny kernel into the degree-torsion sends `δ_φ(Q)` to
`δ_n(φ̂ Q)`, where `n = deg φ`. -/
theorem explicitCoeff1_kerCoeffToTorsionCoeff_kummerMap (Q : W₂.toAffine.Point) :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology
        (φ.kummerMap Q) =
      W₁.kummerMap φ.degree hn ((ofIsogeny φ.dual).pointMap Q) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have h := φ.kummerShortExact.explicitDelta0_coeffMap (W₁.kummerShortExact φ.degree hn)
    φ.kerCoeffToTorsionCoeff (DistribMulActionHom.id _) (ofIsogeny φ.dual).pointCoeffMap
    (fun P ↦ by simp [Isogeny.kummerShortExact_incl, WeierstrassCurve.kummerShortExact_incl])
    (fun P ↦ by simp [Isogeny.kummerShortExact_proj, WeierstrassCurve.kummerShortExact_proj])
    (W₂.basePointEquivInvariants Q)
  have hQ : explicitCoeff0 _ _ (ofIsogeny φ.dual).pointCoeffMap
      (W₂.basePointEquivInvariants Q) =
      W₁.basePointEquivInvariants ((ofIsogeny φ.dual).pointMap Q) := by
    ext
    simp
  simpa only [← kummerMap_apply, ← WeierstrassCurve.kummerMap_apply, hQ] using h

/-- Projection from degree-torsion to the dual kernel sends the multiplication Kummer
class `δ_n(P)` to `δ_φ̂(P)`. -/
theorem explicitCoeff1_torsionCoeffToDualKerCoeff_kummerMap (P : W₁.toAffine.Point) :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology
        (W₁.kummerMap φ.degree hn P) = φ.dual.kummerMap P := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  have h := (W₁.kummerShortExact φ.degree hn).explicitDelta0_coeffMap φ.dual.kummerShortExact
    φ.torsionCoeffToDualKerCoeff (ofIsogeny φ).pointCoeffMap (DistribMulActionHom.id _)
    (fun Q ↦ by simp [Isogeny.kummerShortExact_incl, WeierstrassCurve.kummerShortExact_incl])
    (fun Q ↦ by simp [Isogeny.kummerShortExact_proj, WeierstrassCurve.kummerShortExact_proj])
    (W₁.basePointEquivInvariants P)
  simpa only [explicitCoeff0_id, AddMonoidHom.id_apply, ← kummerMap_apply,
    ← WeierstrassCurve.kummerMap_apply] using h

/-- The image of the multiplication Kummer subgroup under `E₁[n] → E₂[φ̂]` is exactly
the dual-isogeny Kummer subgroup, with no rational surjectivity assumption on `φ`. -/
theorem map_range_kummerMap_torsionCoeffToDualKerCoeff :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    (W₁.kummerMap φ.degree hn).range.map
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology) =
      φ.dual.kummerMap.range := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  rw [← AddMonoidHom.range_comp]
  congr 1
  ext P
  exact φ.explicitCoeff1_torsionCoeffToDualKerCoeff_kummerMap hn P

end TauCeti.Isogeny
