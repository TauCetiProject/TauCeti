/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# Second group cohomology of `ℤ/2` with trivial integral coefficients

Degree-`2` category homology of `SingleObj (Multiplicative (ZMod 2))` with constant coefficients
`ℤ` vanishes (`TauCeti.isZero_categoryHomology_two_singleObj_zmod_two_int`), whereas second group
cohomology `H²(ℤ/2, ℤ)` with trivial action is isomorphic to `ℤ/2`
(`TauCeti.groupCohomologyTrivialZModTwoIntTwoIso`) and therefore nonzero
(`TauCeti.not_isZero_groupCohomology_trivial_zmod_two_int_two`). This distinguishes covariant
category homology from cohomology via universal coefficients.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
-/

public noncomputable section

open CategoryTheory Limits

namespace TauCeti

private abbrev G₂ : Type := Multiplicative (ZMod 2)

private lemma g₂_ne_one_iff (x : G₂) : x ≠ 1 ↔ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert x; decide

private lemma zpowers_gen_g₂ (x : G₂) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 2)) := by
  rcases eq_or_ne x 1 with rfl | hx
  · exact ⟨0, zpow_zero _⟩
  · exact ⟨1, (zpow_one _).trans ((g₂_ne_one_iff x).mp hx).symm⟩

/-- Second group cohomology `H²(ℤ/2, ℤ)` with trivial integral action is isomorphic to `ℤ/2`. -/
def groupCohomologyTrivialZModTwoIntTwoIso :
    groupCohomology (Rep.trivial ℤ (Multiplicative (ZMod 2)) ℤ) 2 ≅ ModuleCat.of ℤ (ZMod 2) := by
  let A₀ := Rep.trivial ℤ G₂ ℤ; let g₀ : G₂ := Multiplicative.ofAdd (1 : ZMod 2)
  let S := Rep.FiniteCyclicGroup.normHomCompSub A₀ g₀
  have hcard : Fintype.card G₂ = 2 := by decide
  have hf (x : ℤ) : S.f.hom x = 2 * x := by
    simp [S, A₀, Rep.FiniteCyclicGroup.normHomCompSub, Rep.norm, Representation.norm, hcard,
      two_mul]
  let K := LinearMap.ker S.g.hom; let R₀ := LinearMap.range S.moduleCatToCycles
  let φ : K →ₗ[ℤ] ZMod 2 := (Algebra.linearMap ℤ (ZMod 2)).comp K.subtype
  have hR₀ : R₀ ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd (S.f.hom x) 2).mpr ⟨x, hf x⟩)
  let ψ : (K ⧸ R₀) →ₗ[ℤ] ZMod 2 := Submodule.liftQ R₀ φ hR₀
  have hinj : Function.Injective ψ :=
    (injective_iff_map_eq_zero ψ).mpr fun z hz ↦ by
      obtain ⟨⟨x, _⟩, rfl⟩ := Submodule.Quotient.mk_surjective R₀ z
      obtain ⟨q, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hz
      exact (Submodule.Quotient.mk_eq_zero R₀).mpr ⟨q, Subtype.ext (hf q)⟩
  have hsurj : Function.Surjective ψ := fun y ↦ by
    obtain ⟨x, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨Submodule.Quotient.mk ⟨x, LinearMap.mem_ker.mpr (sub_self x)⟩, rfl⟩
  exact Rep.FiniteCyclicGroup.groupCohomologyIsoEven A₀ g₀ zpowers_gen_g₂ 2 ⟨1, rfl⟩ ≪≫
    S.moduleCatHomologyIso ≪≫ (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩).toModuleIso

/-- Second group cohomology `H²(ℤ/2, ℤ)` with trivial integral action is nonzero. -/
theorem not_isZero_groupCohomology_trivial_zmod_two_int_two :
    ¬ IsZero (groupCohomology (Rep.trivial ℤ (Multiplicative (ZMod 2)) ℤ) 2) := fun hz ↦ by
  have hid : (𝟙 (ModuleCat.of ℤ (ZMod 2))) = 0 :=
    (hz.of_iso groupCohomologyTrivialZModTwoIntTwoIso.symm).eq_of_src _ _
  exact absurd (congrArg (fun φ : ModuleCat.of ℤ (ZMod 2) ⟶ _ ↦ φ.hom 1) hid) (by decide)

end TauCeti
