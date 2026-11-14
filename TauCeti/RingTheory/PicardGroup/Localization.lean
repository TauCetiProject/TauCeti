/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Invertible modules and localization

Invertibility of a finitely presented module descends from a principal-open cover.
If an invertible module becomes free after localizing at a submonoid, it becomes free of
rank one after inverting a single element of that submonoid, with a generator in the original
module. In particular this applies when the localized ring is a unique factorization domain.

These are affine ingredients for constructing and descending line bundles.

## References

* The Stacks Project, Tag 0BCH.
-/

public noncomputable section

open TensorProduct in
/-- **Invertibility is a local property.** A finitely presented `R`-module `M` such that for each
`r` in a family `s` generating the unit ideal the localization `M_r` is invertible over
`R_r` is invertible. -/
theorem Module.Invertible.of_isLocalized_span {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M] (s : Set R) (spn : Ideal.span s = ⊤)
    (Rₚ : s → Type*) [∀ i, CommRing (Rₚ i)] [∀ i, Algebra R (Rₚ i)]
    [∀ i, IsLocalization.Away i.1 (Rₚ i)]
    (Mₚ : s → Type*) [∀ i, AddCommGroup (Mₚ i)] [∀ i, Module R (Mₚ i)]
    [∀ i, Module (Rₚ i) (Mₚ i)] [∀ i, IsScalarTower R (Rₚ i) (Mₚ i)]
    (f : ∀ i, M →ₗ[R] Mₚ i) [∀ i, IsLocalizedModule.Away i.1 (f i)]
    (hlocal : ∀ i, Module.Invertible (Rₚ i) (Mₚ i)) :
    Module.Invertible R M := by
  let dl (i : s) : Module.Dual R M →ₗ[R] Module.Dual (Rₚ i) (Mₚ i) :=
    IsLocalizedModule.mapExtendScalars (.powers i.1) (f i) (Algebra.linearMap R (Rₚ i)) (Rₚ i)
  let e (i : s) := IsLocalization.moduleTensorEquiv (.powers i.1) (Rₚ i)
    (Module.Dual (Rₚ i) (Mₚ i)) (Mₚ i)
  refine ⟨bijective_of_isLocalized_span s spn
    (fun i ↦ Module.Dual (Rₚ i) (Mₚ i) ⊗[R] Mₚ i) (fun i ↦ map (dl i) (f i))
    Rₚ (fun i ↦ Algebra.linearMap R (Rₚ i)) _ fun i ↦ ?_⟩
  have := hlocal i
  have hmap : IsLocalizedModule.map (.powers i.1) (map (dl i) (f i))
      (Algebra.linearMap R (Rₚ i)) (contractLeft R M) =
      ((contractLeft (Rₚ i) (Mₚ i)).restrictScalars R) ∘ₗ
        ((e i).symm.restrictScalars R).toLinearMap := by
    refine IsLocalizedModule.linearMap_ext (.powers i.1) (map (dl i) (f i))
      (Algebra.linearMap R (Rₚ i)) ?_
    rw [IsLocalizedModule.map_comp]
    ext functional m
    exact (IsLocalizedModule.map_apply (.powers i.1) (f i)
      (Algebra.linearMap R (Rₚ i)) functional m).symm
  rw [hmap]
  exact (Module.Invertible.bijective (R := Rₚ i) (M := Mₚ i)).comp
    (e i).symm.bijective

/-- The localization of the map `r ↦ r • m` is the map `a ↦ a • f m`. -/
theorem IsLocalizedModule.map_toSpanSingleton {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] (S : Submonoid R) (Rₛ : Type*) [CommSemiring Rₛ]
    [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommMonoid Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f] (m : M) :
    IsLocalizedModule.map S (Algebra.linearMap R Rₛ) f (LinearMap.toSpanSingleton R M m) =
      (LinearMap.toSpanSingleton Rₛ Mₛ (f m)).restrictScalars R := by
  refine IsLocalizedModule.linearMap_ext S (Algebra.linearMap R Rₛ) f ?_
  rw [IsLocalizedModule.map_comp]
  ext
  simp

/-- If an invertible module becomes free after a localization, a generator already gives
an isomorphism after inverting a single element of the denominator submonoid. The conclusion works
with any models of the ring and module localization. -/
theorem Module.Invertible.exists_mem_bijective_smul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Invertible R M] (S : Submonoid R)
    [Module.Free (Localization S) (LocalizedModule S M)] :
    ∃ s ∈ S, ∃ m : M, ∀ (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization.Away s Rₛ]
      (Mₛ : Type*) [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
      (f : M →ₗ[R] Mₛ) [IsLocalizedModule.Away s f], Function.Bijective fun i : Rₛ ↦ i • f m := by
  have := Module.finitePresentation_of_projective R M
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free (Localization S) (LocalizedModule S M))
  obtain ⟨m, denominator, hx⟩ : ∃ m denominator, LocalizedModule.mk m denominator = e.symm 1 := by
    induction e.symm 1 using LocalizedModule.induction_on with
    | h m denominator => exact ⟨m, denominator, rfl⟩
  have hsurj : Function.Surjective
      (LinearMap.toSpanSingleton (Localization S) _ (LocalizedModule.mk m (1 : S))) := by
    intro z
    refine ⟨e z * Localization.mk 1 denominator, ?_⟩
    rw [LinearMap.toSpanSingleton_apply, mul_smul, LocalizedModule.mk_smul_mk, one_smul, mul_one,
      hx, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  obtain ⟨s, hs, hbij⟩ := exists_bijective_map_powers S (Algebra.linearMap R (Localization S))
    (LocalizedModule.mkLinearMap S M) (LinearMap.toSpanSingleton R M m) (by
      rw [IsLocalizedModule.map_toSpanSingleton]
      exact Module.Invertible.bijective_of_surjective (R := Localization S) hsurj)
  refine ⟨s, hs, m, fun Rₛ _ _ _ Mₛ _ _ _ _ f _ ↦ ?_⟩
  have := (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Algebra.linearMap R Rₛ) f).mpr (hbij s dvd_rfl)
  rwa [IsLocalizedModule.map_toSpanSingleton] at this
