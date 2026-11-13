/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Etale.Field
import TauCeti.LinearAlgebra.Dimension.FinrankOne
import Mathlib.RingTheory.Algebraic.Integral

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
* `Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one`: the intermediate-ring
  version, with no finite-type hypothesis.
* `TauCeti.exists_transcendental_and_D_ne_zero`: choose a transcendental element detected by
  a nonzero universal derivation, without perfectness.
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

/-- An intermediate ring containing an element with nonzero differential makes a field
extension formally unramified when its differential module has dimension one. -/
theorem _root_.Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one
    {R A F : Type*} [CommRing R] [CommRing A] [Field F]
    [Algebra R A] [Algebra A F] [Algebra R F] [IsScalarTower R A F]
    (h : finrank F Ω[F⁄R] = 1) {y : F} (hy : D R F y ≠ 0)
    (hyA : y ∈ Set.range (algebraMap A F)) : Algebra.FormallyUnramified A F := by
  refine ⟨subsingleton_of_forall_eq 0 fun ω ↦ ?_⟩
  obtain ⟨η, rfl⟩ := KaehlerDifferential.map_surjective R A F ω
  obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' _ hy).mp h η
  obtain ⟨y, rfl⟩ := hyA
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply,
    Derivation.map_algebraMap, smul_zero]

/-- Over a commutative base ring `R`, if `Ω[F⁄R]` is one-dimensional, every intermediate field
containing an element with nonzero `R`-differential makes `F` separable algebraic over it. -/
theorem isSeparable_of_finrank_kaehlerDifferential_eq_one {R E : Type*} [CommRing R] [Field E]
    [Algebra R E] [Algebra R F] [Algebra E F] [IsScalarTower R E F] [Algebra.EssFiniteType E F]
    (h : finrank F Ω[F⁄R] = 1) {y : E} (hy : D R F (algebraMap E F y) ≠ 0) :
    Algebra.IsSeparable E F := by
  have := Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one h hy ⟨y, rfl⟩
  exact Algebra.FormallyUnramified.isSeparable E F

/-- Over a commutative base ring `R`, if `Ω[F⁄R]` is one-dimensional and two intermediate fields
generate `F`, then `F` is separable algebraic over at least one of them. Two subfields on which the
differential vanishes cannot generate a field with nonzero differentials. -/
theorem isSeparable_left_or_right_of_adjoin_eq_top {R E₁ E₂ : Type*} [CommRing R]
    [Field E₁] [Field E₂] [Algebra R E₁] [Algebra R E₂] [Algebra R F] [Algebra E₁ F]
    [Algebra E₂ F] [IsScalarTower R E₁ F] [IsScalarTower R E₂ F]
    [Algebra.EssFiniteType E₁ F] [Algebra.EssFiniteType E₂ F]
    (h : finrank F Ω[F⁄R] = 1)
    (htop : IntermediateField.adjoin E₁ (Set.range (algebraMap E₂ F)) = ⊤) :
    Algebra.IsSeparable E₁ F ∨ Algebra.IsSeparable E₂ F := by
  by_contra! hsep
  have h₁ (y : E₁) : D R F (algebraMap E₁ F y) = 0 :=
    of_not_not fun hy ↦ hsep.1 (isSeparable_of_finrank_kaehlerDifferential_eq_one h hy)
  have h₂ (y : E₂) : D R F (algebraMap E₂ F y) = 0 :=
    of_not_not fun hy ↦ hsep.2 (isSeparable_of_finrank_kaehlerDifferential_eq_one h hy)
  have hD (y : F) : D R F y = 0 := by
    have hy : y ∈ IntermediateField.adjoin E₁ (Set.range (algebraMap E₂ F)) :=
      htop.symm ▸ IntermediateField.mem_top
    induction hy using IntermediateField.adjoin_induction with
    | mem z hz => obtain ⟨a, rfl⟩ := hz; exact h₂ a
    | algebraMap a => exact h₁ a
    | add a b _ _ ha hb => simp [map_add, ha, hb]
    | mul a b _ _ ha hb => simp [Derivation.leibniz, ha, hb]
    | inv a _ ha => simp [Derivation.leibniz_inv, ha]
  have hzero : (⊤ : Submodule F Ω[F⁄R]) = ⊥ := by
    rw [← span_range_derivation R F, Submodule.span_eq_bot]
    rintro _ ⟨y, rfl⟩
    exact hD y
  have : finrank F Ω[F⁄R] = 0 := by rw [← finrank_top F Ω[F⁄R], hzero, finrank_bot]
  omega

/-- If the universal derivation is nonzero, a field extension with a transcendental element
has a transcendental element with nonzero differential. No perfectness assumption is needed. -/
theorem exists_transcendental_and_D_ne_zero {R : Type*} [CommRing R] [Algebra R F]
    (hD : KaehlerDifferential.D R F ≠ 0) {x : F} (hx : Transcendental k x) :
    ∃ y : F, Transcendental k y ∧ KaehlerDifferential.D R F y ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y : F, KaehlerDifferential.D R F y ≠ 0 := by
    by_contra! h
    exact hD (Derivation.ext h)
  by_cases hDx : KaehlerDifferential.D R F x = 0
  swap
  · exact ⟨x, hx, hDx⟩
  by_cases hytrans : Transcendental k y
  · exact ⟨y, hytrans, hy⟩
  rw [Transcendental, not_not] at hytrans
  have hy0 : y ≠ 0 := fun h ↦ hy (by rw [h, map_zero])
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  refine ⟨y * x, fun h ↦ hx ?_, ?_⟩
  · have heq : x = y * x * y⁻¹ := by field_simp
    rw [heq]
    exact h.mul hytrans.inv
  · rw [Derivation.leibniz, hDx, smul_zero, zero_add]
    exact smul_ne_zero hx0 hy

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
