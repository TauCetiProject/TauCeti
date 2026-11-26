/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.FiniteIndexIdeal
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# The generalised index of a finite adele of a number field

For a number field `K` with finite adeles `𝔸_f` and integral finite adeles `Ô`, the *generalised
index* `[a]` of a finite adele `a` is the absolute norm of its fractional ideal when `a` is a unit,
and `0` otherwise (`NumberField.FiniteAdeleRing.genIndex`). It is multiplicative, it is
`|N_{K/ℚ} x|` on the diagonal image of `x ∈ K`, and for an integral adele `g` that is a unit of
`𝔸_f` it is the index `[Ô : gÔ]`. It is invariant under ring automorphisms of `𝔸_f` that preserve
`Ô`, and the determinant of a square matrix over `Ô` that is invertible over `Ô` has index `1`.

## Main declarations

* `NumberField.FiniteAdeleRing.genIndex`: the generalised index `𝔸_f →*₀ ℚ`.
* `NumberField.FiniteAdeleRing.genIndex_algebraMap`: `[x] = |N_{K/ℚ} x|` for `x ∈ K`.
* `NumberField.FiniteAdeleRing.genIndex_eq_cardQuot`: `[g] = [Ô : gÔ]`.
* `NumberField.FiniteAdeleRing.genIndex_map`: invariance under automorphisms preserving `Ô`.
* `NumberField.FiniteAdeleRing.genIndex_det_map_eq_one`: `[det U] = 1` for `U ∈ GL_r(Ô)`.

## Attribution

The generalised index is `New.genIndex` in the file `src/Lib/General/Measure/HaarModulus.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where
it is defined as the inverse of the factor by which multiplication scales a Haar measure. Its
properties `genIndex_eq_cardQuot`, `genIndex_det_map_eq_one` and `genIndex_map` are adapted from
`New.genIndex_eq_card`, `New.genIndex_det_eq_one` and `New.genIndex_star` in the same file; here
they come from the fractional ideal of a finite idele instead.
-/

public section
noncomputable section

namespace NumberField.FiniteAdeleRing

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped NumberField.AdeleRing nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

open Classical in
variable (K) in
/-- The **generalised index** `[a]` of a finite adele `a` of a number field: the absolute norm of
the fractional ideal of `a` if `a` is a unit, and `0` otherwise. -/
def genIndex : 𝔸ᶠ[K] →*₀ ℚ where
  toFun a := if h : IsUnit a then
    FractionalIdeal.absNorm ((toFractionalIdeal h.unit : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) else 0
  map_zero' := dite_eq_right not_isUnit_zero
  map_one' := by
    rw [dite_eq_left isUnit_one, IsUnit.unit_one, map_one, Units.val_one,
      FractionalIdeal.absNorm_one]
  map_mul' a b := by
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · rw [dite_eq_left (ha.mul hb), dite_eq_left ha, dite_eq_left hb, ← map_mul,
          ← Units.val_mul, ← map_mul, IsUnit.unit_mul]
      · rw [dite_eq_right (fun h ↦ hb (isUnit_of_mul_isUnit_right h)), dite_eq_right hb, mul_zero]
    · rw [dite_eq_right (fun h ↦ ha (isUnit_of_mul_isUnit_left h)), dite_eq_right ha, zero_mul]

/-- The generalised index of a finite idele is the absolute norm of its fractional ideal. -/
@[simp]
theorem genIndex_units (t : 𝔸ᶠ[K]ˣ) :
    genIndex K t = FractionalIdeal.absNorm (toFractionalIdeal t : FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [genIndex, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dite_eq_left t.isUnit,
    IsUnit.unit_of_val_units]

/-- The generalised index of a finite adele that is not a unit is `0`. -/
theorem genIndex_of_not_isUnit {a : 𝔸ᶠ[K]} (ha : ¬ IsUnit a) : genIndex K a = 0 := by
  simp only [genIndex, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dite_eq_right ha]

/-- The generalised index of a finite idele is positive. -/
theorem genIndex_units_pos (t : 𝔸ᶠ[K]ˣ) : 0 < genIndex K t := by
  rw [genIndex_units]
  refine (FractionalIdeal.absNorm_nonneg _).lt_of_ne' fun h ↦ ?_
  exact (toFractionalIdeal t).ne_zero (FractionalIdeal.absNorm_eq_zero_iff.1 h)

/-- The generalised index is nonnegative. -/
theorem genIndex_nonneg (a : 𝔸ᶠ[K]) : 0 ≤ genIndex K a := by
  by_cases ha : IsUnit a
  · exact (genIndex_units_pos ha.unit).le
  · exact (genIndex_of_not_isUnit ha).ge

/-- The generalised index of a finite adele vanishes exactly when it is not a unit. -/
theorem genIndex_eq_zero_iff {a : 𝔸ᶠ[K]} : genIndex K a = 0 ↔ ¬ IsUnit a :=
  ⟨fun h ha ↦ (genIndex_units_pos ha.unit).ne' h, genIndex_of_not_isUnit⟩

/-- The generalised index of the diagonal image of `x ∈ K` is `|N_{K/ℚ} x|`. -/
@[simp]
theorem genIndex_algebraMap (x : K) : genIndex K (algebraMap K 𝔸ᶠ[K] x) = |Algebra.norm ℚ x| := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have h := genIndex_units (unitEmbedding (𝓞 K) K (Units.mk0 x hx))
  rw [toFractionalIdeal_unitEmbedding, coe_toPrincipalIdeal, Units.val_mk0,
    FractionalIdeal.absNorm_span_singleton] at h
  exact h

/-- Let `g` be an integral finite adele that is a unit of the finite adeles. Its generalised index
is the index `[Ô : gÔ]` of the ideal it generates in the integral finite adeles `Ô`. -/
theorem genIndex_eq_cardQuot {g : integralAdeles (𝓞 K) K} (hg : IsUnit (g : 𝔸ᶠ[K])) :
    genIndex K g = (Ideal.span {g}).cardQuot := by
  obtain ⟨N, hN⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1
    ((toFractionalIdeal_le_one_iff hg.unit).2 g.property)
  have hN0 : N ≠ ⊥ := by
    rintro rfl
    exact (toFractionalIdeal hg.unit).ne_zero (by rw [← hN, FractionalIdeal.coeIdeal_bot])
  have ht : toFractionalIdeal hg.unit =
      FractionalIdeal.mk0 K ⟨N, mem_nonZeroDivisors_of_ne_zero hN0⟩ :=
    Units.ext (by rw [FractionalIdeal.coe_mk0, hN])
  have h_span : Ideal.span {g} = completedIdeal K N := by
    rw [completedIdeal_eq_span_singleton hN0 ht]
    exact congrArg (fun y ↦ Ideal.span {y}) (Subtype.ext hg.unit_spec.symm)
  calc genIndex K g
    _ = FractionalIdeal.absNorm (N : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hN, ← genIndex_units, IsUnit.unit_spec]
    _ = Nat.card (𝓞 K ⧸ N) := by
      rw [FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = (Ideal.span {g}).cardQuot := by
      rw [h_span, cardQuot_completedIdeal K hN0, Submodule.cardQuot_apply]

/-- Some positive integer multiple of a finite adele is integral. -/
theorem exists_natCast_mul_mem_integralAdeles (a : 𝔸ᶠ[K]) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : 𝔸ᶠ[K]) * a ∈ integralAdeles (𝓞 K) K := by
  obtain ⟨b, hb, hab⟩ := mul_nonZeroDivisor_mem_integralAdeles (R := 𝓞 K) a
  have hb0 : Ideal.span {b} ≠ ⊥ := by simpa using nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Submodule.natCast_cardQuot_mem (Ideal.span {b}))
  refine ⟨(Ideal.span {b}).cardQuot, (Ring.HasFiniteQuotients.cardQuot_pos _ hb0).ne', ?_⟩
  have h_eq : ((Ideal.span {b}).cardQuot : 𝔸ᶠ[K]) * a =
      algebraMap (𝓞 K) 𝔸ᶠ[K] c * (a * algebraMap (𝓞 K) 𝔸ᶠ[K] b) := by
    rw [← map_natCast (algebraMap (𝓞 K) 𝔸ᶠ[K]), ← hc, map_mul]
    ring
  rw [h_eq]
  exact mul_mem ((integralAdeles (𝓞 K) K).algebraMap_mem c) hab

/-- The generalised index is invariant under a ring automorphism `σ` of the finite adeles that
preserves the integral finite adeles. -/
theorem genIndex_map (σ : 𝔸ᶠ[K] ≃+* 𝔸ᶠ[K])
    (hσ : ∀ x, σ x ∈ integralAdeles (𝓞 K) K ↔ x ∈ integralAdeles (𝓞 K) K) (a : 𝔸ᶠ[K]) :
    genIndex K (σ a) = genIndex K a := by
  by_cases ha : IsUnit a
  swap
  · rw [genIndex_of_not_isUnit ha, genIndex_of_not_isUnit (by rwa [isUnit_map_iff])]
  -- Reduce to an integral multiple `m a`, on which the index is that of an ideal of `Ô`.
  obtain ⟨m, hm, hma⟩ := exists_natCast_mul_mem_integralAdeles a
  have hm' : IsUnit (m : 𝔸ᶠ[K]) := by
    simpa using (Nat.cast_ne_zero.2 hm : (m : K) ≠ 0).isUnit.map (algebraMap K 𝔸ᶠ[K])
  let τ := σ.restrict (integralAdeles (𝓞 K) K) (integralAdeles (𝓞 K) K) fun x ↦ (hσ x).symm
  have h_int : genIndex K (σ ((m : 𝔸ᶠ[K]) * a)) = genIndex K ((m : 𝔸ᶠ[K]) * a) := by
    have h₁ := genIndex_eq_cardQuot (g := τ ⟨_, hma⟩) ((isUnit_map_iff σ _).2 (hm'.mul ha))
    have h₂ := genIndex_eq_cardQuot (g := ⟨_, hma⟩) (hm'.mul ha)
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.cardQuot_map_of_ringEquiv] at h₁
    exact h₁.trans h₂.symm
  rw [map_mul, map_natCast, map_mul, map_mul] at h_int
  exact mul_left_cancel₀ ((genIndex_units_pos hm'.unit).ne') h_int

/-- A square matrix `U` over the integral finite adeles with a right inverse over the integral
finite adeles has a determinant of generalised index `1`. -/
theorem genIndex_det_map_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {U V : Matrix n n (integralAdeles (𝓞 K) K)} (h : U * V = 1) :
    genIndex K (U.map (algebraMap (integralAdeles (𝓞 K) K) 𝔸ᶠ[K])).det = 1 := by
  have h_unit : IsUnit U.det := .of_mul_eq_one V.det (by rw [← Matrix.det_mul, h, Matrix.det_one])
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Subalgebra.algebraMap_apply,
    genIndex_eq_cardQuot (h_unit.map (algebraMap (integralAdeles (𝓞 K) K) 𝔸ᶠ[K])),
    Ideal.span_singleton_eq_top.2 h_unit, Submodule.cardQuot_top, Nat.cast_one]

end NumberField.FiniteAdeleRing
