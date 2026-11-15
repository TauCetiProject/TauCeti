/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.LocalProperties.Exactness
public import TauCeti.RingTheory.Localization.Module
import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Invertible modules and localization

Invertibility of an arbitrary module descends from a principal-open cover.
Finite presentation follows from local invertibility.
If an invertible module becomes free after localizing at a submonoid, it becomes free of
rank one after inverting a single element of that submonoid, with a generator in the original
module. In particular this applies when the localized ring is a unique factorization domain.

These are affine ingredients for constructing and descending line bundles.

## References

* The Stacks Project, Tag 0BCH.
* The descent proof adapts Yongle Hu's `Module.Invertible.of_isLocalized_maximal` in
  `Mathlib/RingTheory/LocalProperties/Invertible.lean`. That source is copyright (c) 2026
  Yongle Hu, released under Apache 2.0 license as described in the file LICENSE.
-/

public noncomputable section

open TensorProduct in
/-- **Invertibility is a local property.** An `R`-module `M` such that for each
`r` in a family `s` generating the unit ideal the localization `M_r` is invertible over
`R_r` is invertible. -/
theorem Module.Invertible.of_isLocalized_span {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (s : Set R) (spn : Ideal.span s = ⊤)
    (Rₚ : s → Type*) [∀ i, CommRing (Rₚ i)] [∀ i, Algebra R (Rₚ i)]
    [∀ i, IsLocalization.Away i.1 (Rₚ i)]
    (Mₚ : s → Type*) [∀ i, AddCommGroup (Mₚ i)] [∀ i, Module R (Mₚ i)]
    [∀ i, Module (Rₚ i) (Mₚ i)] [∀ i, IsScalarTower R (Rₚ i) (Mₚ i)]
    (f : ∀ i, M →ₗ[R] Mₚ i) [∀ i, IsLocalizedModule.Away i.1 (f i)]
    (hlocal : ∀ i, Module.Invertible (Rₚ i) (Mₚ i)) :
    Module.Invertible R M := by
  have : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s spn f fun i ↦ by
      have := hlocal i
      exact Module.finitePresentation_of_projective (Rₚ i) (Mₚ i)
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
  obtain ⟨h, hh⟩ := Module.FinitePresentation.exists_bijective_map_of_isLocalizedModule S
    (Algebra.linearMap R (Localization S)) (LocalizedModule.mkLinearMap S M)
    (e.symm.restrictScalars R)
  let m := h 1
  have hm : h = LinearMap.toSpanSingleton R M m := by
    ext
    simp [m]
  obtain ⟨s, hs, hbij⟩ := exists_bijective_map_powers S (Algebra.linearMap R (Localization S))
    (LocalizedModule.mkLinearMap S M) (LinearMap.toSpanSingleton R M m) (by
      rwa [hm] at hh)
  refine ⟨s, hs, m, fun Rₛ _ _ _ Mₛ _ _ _ _ f _ ↦ ?_⟩
  have := (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Algebra.linearMap R Rₛ) f).mpr (hbij s dvd_rfl)
  rwa [IsLocalizedModule.map_toSpanSingleton] at this
