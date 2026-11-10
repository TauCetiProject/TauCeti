/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Etale.Field
public import TauCeti.RingTheory.Kaehler.BaseChange
import TauCeti.LinearAlgebra.Dimension.FinrankOne

/-!
# Kähler differentials of separable elements

This file records how the universal derivation detects separability and transcendence for field
extensions.

## Main results

* `TauCeti.nontrivial_kaehlerDifferential`, `TauCeti.finrank_kaehlerDifferential_pos`: an
  essentially finite type transcendental field extension has nonzero Kähler differentials.
* `TauCeti.isSeparable_of_finrank_kaehlerDifferential_eq_one`: a subfield containing an element
  with nonzero differential is a separating subfield when the differential module has dimension one.
* `TauCeti.isSeparable_left_or_right_of_adjoin_eq_top`: if the differential module is
  one-dimensional, at least one of two generating subfields is separating.
* `TauCeti.D_eq_zero_of_isSeparable`: a separable algebraic element has vanishing differential.
* `TauCeti.transcendental_of_D_ne_zero`: over a perfect base field, an element with nonzero
  differential is transcendental.
-/

public section

noncomputable section

namespace TauCeti

open Module Polynomial KaehlerDifferential

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}

/-- A separable algebraic element has vanishing universal differential, so the universal
derivation detects only the inseparable or transcendental part of an extension. -/
theorem D_eq_zero_of_isSeparable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {a : A}
    (ha : IsSeparable R a) : D R A a = 0 := by
  obtain ⟨p, q, hpq⟩ := ha
  have hunit : IsUnit (aeval a (minpoly R a).derivative) :=
    .of_mul_eq_one (aeval a q) (by simpa [mul_comm] using congr(aeval a $hpq))
  have hder := (D R A).map_aeval (minpoly R a) a
  rw [minpoly.aeval, map_zero] at hder
  exact hunit.smul_left_cancel.mp (by rw [← hder, smul_zero])

/-- If `Ω[F⁄k]` is one-dimensional, every intermediate field containing an element with nonzero
`k`-differential makes `F` separable algebraic over it. -/
theorem isSeparable_of_finrank_kaehlerDifferential_eq_one {E : Type*} [Field E]
    [Algebra k E] [Algebra E F] [IsScalarTower k E F] [Algebra.EssFiniteType E F]
    (h : finrank F Ω[F⁄k] = 1) {y : E} (hy : D k F (algebraMap E F y) ≠ 0) :
    Algebra.IsSeparable E F := by
  have hrange : (mapBaseChange k E F).range = ⊤ := by
    rw [eq_top_iff, ← (span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one h _).mpr hy,
      Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨1 ⊗ₜ D k E y, by simp⟩
  have : Algebra.FormallyUnramified E F :=
    ⟨(subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top k E F).mpr hrange⟩
  exact Algebra.FormallyUnramified.isSeparable E F

/-- If `Ω[F⁄k]` is one-dimensional and two intermediate fields generate `F`, then `F` is
separable algebraic over at least one of them. Two subfields on which the differential vanishes
cannot generate a field with nonzero differentials. -/
theorem isSeparable_left_or_right_of_adjoin_eq_top {E₁ E₂ : Type*} [Field E₁] [Field E₂]
    [Algebra k E₁] [Algebra k E₂] [Algebra E₁ F] [Algebra E₂ F]
    [IsScalarTower k E₁ F] [IsScalarTower k E₂ F]
    [Algebra.EssFiniteType E₁ F] [Algebra.EssFiniteType E₂ F]
    (h : finrank F Ω[F⁄k] = 1)
    (htop : IntermediateField.adjoin E₁ (Set.range (algebraMap E₂ F)) = ⊤) :
    Algebra.IsSeparable E₁ F ∨ Algebra.IsSeparable E₂ F := by
  by_contra! hsep
  have h₁ (y : E₁) : D k F (algebraMap E₁ F y) = 0 :=
    of_not_not fun hy ↦ hsep.1 (isSeparable_of_finrank_kaehlerDifferential_eq_one h hy)
  have h₂ (y : E₂) : D k F (algebraMap E₂ F y) = 0 :=
    of_not_not fun hy ↦ hsep.2 (isSeparable_of_finrank_kaehlerDifferential_eq_one h hy)
  have hD (y : F) : D k F y = 0 := by
    have hy : y ∈ IntermediateField.adjoin E₁ (Set.range (algebraMap E₂ F)) :=
      htop.symm ▸ IntermediateField.mem_top
    induction hy using IntermediateField.adjoin_induction with
    | mem z hz => obtain ⟨a, rfl⟩ := hz; exact h₂ a
    | algebraMap a => exact h₁ a
    | add a b _ _ ha hb => simp [map_add, ha, hb]
    | mul a b _ _ ha hb => simp [Derivation.leibniz, ha, hb]
    | inv a _ ha => simp [Derivation.leibniz_inv, ha]
  have hzero : (⊤ : Submodule F Ω[F⁄k]) = ⊥ := by
    rw [← span_range_derivation k F, Submodule.span_eq_bot]
    rintro _ ⟨y, rfl⟩
    exact hD y
  have : finrank F Ω[F⁄k] = 0 := by rw [← finrank_top F Ω[F⁄k], hzero, finrank_bot]
  omega

section Transcendental

variable [Algebra.EssFiniteType k F] [Algebra.Transcendental k F]

/-- The Kähler differentials of an essentially finite type field extension that is not algebraic
are nonzero. -/
theorem nontrivial_kaehlerDifferential : Nontrivial Ω[F⁄k] := by
  -- Were they zero, `F` would be formally unramified, hence separable algebraic, over `k`.
  refine not_subsingleton_iff_nontrivial.mp fun h ↦ ?_
  have : Algebra.FormallyUnramified k F := ⟨h⟩
  have := Algebra.FormallyUnramified.isSeparable k F
  exact Algebra.transcendental_iff_not_isAlgebraic.mp ‹_› inferInstance

/-- The Kähler differentials of an essentially finite type field extension that is not algebraic
form a nonzero finite-dimensional `F`-vector space. -/
theorem finrank_kaehlerDifferential_pos : 0 < finrank F Ω[F⁄k] :=
  Module.finrank_pos_iff.mpr nontrivial_kaehlerDifferential

end Transcendental

variable [PerfectField k]

/-- Over a perfect base field, an element with nonzero universal differential is transcendental:
an algebraic element is separable, hence has vanishing differential. -/
theorem transcendental_of_D_ne_zero (hx : D k F x ≠ 0) : Transcendental k x := by
  intro halg
  exact hx (D_eq_zero_of_isSeparable
    (PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)))

end TauCeti
