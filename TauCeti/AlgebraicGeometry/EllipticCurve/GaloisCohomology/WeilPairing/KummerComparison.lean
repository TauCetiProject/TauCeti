/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.KummerComparison
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local

/-!
# Isogeny Weil cups and multiplication Kummer classes

For an isogeny `φ : E₁ → E₂` of degree `n` invertible in the base field, the maps
`ι : E₁[φ] → E₁[n]` and `π : E₁[n] → E₂[φ̂]` are adjoint for the Weil pairings. Hence

`e_φ(a ∪ π_* b) = e_n(ι_* a ∪ b)`.

On Kummer classes this becomes

`e_φ(δ_φ(Q) ∪ δ_φ̂(P)) = e_n(δ_n(φ̂ Q) ∪ δ_n(P))`.

The same identity holds after the local invariant over a nonarchimedean local field,
including at primes dividing `n`. Thus orthogonality of multiplication Kummer images suffices
for orthogonality of the isogeny and dual-isogeny Kummer images. These comparison identities
do not themselves assert orthogonality.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 and X.4.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §2.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- The Weil dual of the projection `E₁[n] → E₂[φ̂]` is restriction of characters along
`E₁[φ] → E₁[n]`. -/
theorem kerCoeffWeilDual_comp_torsionCoeffToDualKerCoeff :
    (φ.kerCoeffWeilDual hn).comp φ.torsionCoeffToDualKerCoeff =
      (InternalHom.precomp (AbsoluteGaloisGroup K) φ.kerCoeffToTorsionCoeff).comp
        (W₁.torsionCoeffWeilDual φ.degree hn) := by
  ext R P
  simp [InternalHom.toAddMonoidHom_precomp]

private theorem explicitCoeff1_kerCoeffWeilDual_torsionCoeffToDualKerCoeff
    (b : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)) :
    explicitCoeff1 _ _ (φ.kerCoeffWeilDual hn) continuous_of_discreteTopology
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      explicitCoeff1 _ _ (InternalHom.precomp (AbsoluteGaloisGroup K)
        φ.kerCoeffToTorsionCoeff) continuous_of_discreteTopology
        (explicitCoeff1 _ _ (W₁.torsionCoeffWeilDual φ.degree hn)
          continuous_of_discreteTopology b) := by
  have h := congrArg (fun f ↦ explicitCoeff1 _ _ f continuous_of_discreteTopology b)
    (φ.kerCoeffWeilDual_comp_torsionCoeffToDualKerCoeff hn)
  rw [explicitCoeff1_comp _ _ φ.torsionCoeffToDualKerCoeff (φ.kerCoeffWeilDual hn)
      continuous_of_discreteTopology continuous_of_discreteTopology,
    explicitCoeff1_comp _ _ (W₁.torsionCoeffWeilDual φ.degree hn)
      (InternalHom.precomp (AbsoluteGaloisGroup K) φ.kerCoeffToTorsionCoeff)
      continuous_of_discreteTopology continuous_of_discreteTopology,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at h
  exact h

/-- The isogeny Weil cup product with a class projected from degree-torsion is the
multiplication Weil cup product with the first class included into degree-torsion. -/
theorem kerH1WeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)) :
    φ.kerH1WeilPairing hn a
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      W₁.torsionH1WeilPairing φ.degree hn
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology a) b := by
  have := hn.neZero_natCast
  rw [kerH1WeilPairing_eq_dualityMap1, torsionH1WeilPairing_eq_dualityMap1,
    dualityMap1_explicitCoeff1]
  exact congrArg (dualityMap1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
    (KummerCoeff K φ.degree) a)
    (φ.explicitCoeff1_kerCoeffWeilDual_torsionCoeffToDualKerCoeff hn b)

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

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- The local Tate pairings are compatible with inclusion into degree-torsion and
projection onto the dual kernel. No restriction on the residue characteristic is needed. -/
theorem localTateKerWeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)) :
    φ.localTateKerWeilPairing hn a
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      W₁.localTateWeilPairing φ.degree hn
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology a) b := by
  simp only [localTateKerWeilPairing_apply, localTateWeilPairing_apply,
    kerH1WeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff]

variable [DecidableEq K]

/-- Local pairing of the two isogeny Kummer images reduces to local pairing of
multiplication-by-degree Kummer images. -/
theorem localTateKerWeilPairing_kummerMap (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    φ.localTateKerWeilPairing hn (φ.kummerMap Q) (φ.dual.kummerMap P) =
      W₁.localTateWeilPairing φ.degree hn
        (W₁.kummerMap φ.degree hn ((ofIsogeny φ.dual).pointMap Q))
        (W₁.kummerMap φ.degree hn P) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  simp only [localTateKerWeilPairing_apply, localTateWeilPairing_apply,
    kerH1WeilPairing_kummerMap]

end Local

end TauCeti.Isogeny
