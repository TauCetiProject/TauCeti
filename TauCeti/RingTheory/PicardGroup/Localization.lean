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
import TauCeti.RingTheory.Localization.TensorProduct

/-!
# Invertible modules and localization

Invertibility of an arbitrary module descends from a principal-open cover.
No finiteness or finite-presentation hypothesis on the original module is required.
If an invertible module becomes free after localizing at a submonoid, it becomes free of
rank one after inverting a single element of that submonoid, with a generator in the original
module. In particular this applies when the localized ring is a unique factorization domain.

A Picard class vanishes after localization at a submonoid exactly when it vanishes on
one principal localization from that submonoid. This controls the affine localization kernel
used in Picard excision.

## References

* The Stacks Project, Tags 0AFW (invertible modules) and 00NX (local freeness).
* Tag 0BCH gives the UFD Picard-vanishing special case mentioned above.
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
  have hmap : IsLocalizedModule.map (.powers i.1) (map (dl i) (f i))
      (Algebra.linearMap R (Rₚ i)) (contractLeft R M) =
      ((contractLeft (Rₚ i) (Mₚ i)).restrictScalars R) ∘ₗ
        ((e i).symm.restrictScalars R).toLinearMap := by
    refine IsLocalizedModule.linearMap_ext (.powers i.1) (map (dl i) (f i))
      (Algebra.linearMap R (Rₚ i)) ?_
    rw [IsLocalizedModule.map_comp]
    ext functional m
    simp [dl, e, IsLocalizedModule.mapExtendScalars,
      IsLocalizedModule.map_apply (.powers i.1) (f i)
        (Algebra.linearMap R (Rₚ i)) functional m]
  rw [hmap]
  exact (hlocal i).bijective.comp
    (e i).symm.bijective

/-- If an invertible module becomes free in any model of a localization at `S`, an element
of the original module generates it after inverting one element of `S`, and after inverting
every multiple of that element. -/
theorem Module.Invertible.exists_mem_bijective_smul {R : Type*} [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Invertible R M] (S : Submonoid R)
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (g : M →ₗ[R] Mₛ) [IsLocalizedModule S g] [Module.Free Rₛ Mₛ] :
    ∃ s ∈ S, ∃ m : M, ∀ t, s ∣ t →
      Function.Bijective (LocalizedModule.map (.powers t) (LinearMap.toSpanSingleton R M m)) := by
  have := Module.finitePresentation_of_projective R M
  have := Module.Invertible.of_isLocalization (A := Rₛ) S g
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free Rₛ Mₛ)
  obtain ⟨h, hh⟩ := Module.FinitePresentation.exists_bijective_map_of_isLocalizedModule S
    (Algebra.linearMap R Rₛ) g (e.symm.restrictScalars R)
  let m := h 1
  have hm : h = LinearMap.toSpanSingleton R M m := by
    ext
    simp [m]
  obtain ⟨s, hs, hbij⟩ := exists_bijective_map_powers S (Algebra.linearMap R Rₛ)
    g (LinearMap.toSpanSingleton R M m) (by rwa [hm] at hh)
  exact ⟨s, hs, m, hbij⟩

namespace CommRing.Pic

open TensorProduct

/-- A Picard class vanishes after localizing at `S` exactly when it vanishes after inverting
one element of `S`. This detects the kernel of localization on a single principal open. -/
theorem mapAlgebra_eq_one_iff_exists_mem {R : Type*} [CommRing R] (P : Pic R) (S : Submonoid R)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A] :
    mapAlgebra R A P = 1 ↔ ∃ s ∈ S, mapAlgebra R (Localization.Away s) P = 1 := by
  constructor
  · intro hP
    have : Module.Free A (A ⊗[R] P) := mk_eq_one_iff_free.mp hP
    obtain ⟨s, hs, m, hm⟩ := Module.Invertible.exists_mem_bijective_smul P S A
      (TensorProduct.mk R A P 1)
    refine ⟨s, hs, mk_eq_one_iff_free.mpr ?_⟩
    have h := (LocalizedModule.bijective_map_toSpanSingleton_iff (.powers s)
      (Localization.Away s) (TensorProduct.mk R (Localization.Away s) P 1) m).mp
        (hm s dvd_rfl)
    exact Module.Free.of_equiv (LinearEquiv.ofBijective _ h)
  · rintro ⟨s, hs, hP⟩
    let f : Localization.Away s →+* A :=
      IsLocalization.Away.lift s (IsLocalization.map_units A ⟨s, hs⟩)
    have hf : f.comp (algebraMap R (Localization.Away s)) = algebraMap R A := by
      ext r
      exact IsLocalization.Away.lift_eq s (IsLocalization.map_units A ⟨s, hs⟩) r
    rw [← mapRingHom_algebraMap, ← hf, ← mapRingHom_mapRingHom,
      mapRingHom_algebraMap, hP, map_one]

end CommRing.Pic
