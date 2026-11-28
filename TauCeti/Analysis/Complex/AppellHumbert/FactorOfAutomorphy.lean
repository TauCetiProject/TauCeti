/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Factors of automorphy from constant logarithmic derivatives

Let `V` be a complex normed space and `L ⊆ V` a full `ℤ`-lattice (`IsZLattice ℝ L`). Suppose
`f : V → ℂ` is nowhere vanishing and, for each `l ∈ L`, the translation quotient
`w ↦ f (l + w) / f w` has a constant `ℂ`-linear logarithmic derivative `a l : V →L[ℂ] ℂ`. When
`V` is finite-dimensional, `a` extends uniquely to a continuous form `B : V →L[ℝ] V →L[ℂ] ℂ`
(real-linear in the first variable, complex-linear in the second) whose real part is symmetric,
and `f` obeys the automorphy law `f (z + l) = f z * exp (B l z) * f l / f 0`.

## Main results

* `TauCeti.factor_of_automorphy_re_symm`: any continuous form `B : V →L[ℝ] V →L[ℂ] ℂ`
  satisfying the automorphy law on `L × V` for a nowhere-vanishing `f` has symmetric real part.
* `TauCeti.exists_factor_of_automorphy`: existence of `B` with symmetric real part from
  constant `ℂ`-linear logarithmic derivatives on `L`.
* `TauCeti.factor_of_automorphy_unique`: uniqueness of `B` given the automorphy law on `L × V`.

## Provenance

`TauCeti.exists_factor_of_automorphy` and `TauCeti.factor_of_automorphy_re_symm` are adapted
from `New.exists_factor_of_automorphy` in `src/Lib/Shimura/ComplexTheta/AppellHumbertData.lean`
of `grh-lean` (https://github.com/lsernau/grh-lean, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC);
`TauCeti.factor_of_automorphy_unique` is added as its companion uniqueness statement.
-/

public section

open Complex Submodule

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]

/-- Any continuous form `B : V →L[ℝ] V →L[ℂ] ℂ` satisfying the automorphy law
`f (z + l) = f z * exp (B l z) * f l / f 0` on `L × V` for a nowhere-vanishing `f` has
symmetric real part. -/
theorem factor_of_automorphy_re_symm {f : V → ℂ} (hf_ne : ∀ z : V, f z ≠ 0)
    {B : V →L[ℝ] V →L[ℂ] ℂ}
    (hB : ∀ l ∈ L, ∀ z : V, f (z + l) = f z * exp (B l z) * f l / f 0) (u v : V) :
    (B u v).re = (B v u).re := by
  have h_span : ∀ x : V, x ∈ span ℝ (L : Set V) := eq_top_iff'.mp IsZLattice.span_top
  induction h_span u, h_span v using span_induction₂ with
  | mem_mem x y hx hy =>
    have h_two : f y * exp (B x y) * f x / f 0 = f x * exp (B y x) * f y / f 0 := by
      rw [← hB x hx y, ← hB y hy x, add_comm]
    have h_exp : exp (B x y) = exp (B y x) := by
      simpa [mul_comm, mul_left_comm, field, hf_ne] using h_two
    simpa [norm_exp] using congrArg (‖·‖) h_exp
  | _ => simp [*]

/-- A nowhere-vanishing function `f : V → ℂ` whose translation quotients `w ↦ f (l + w) / f w`
(`l ∈ L`) have constant `ℂ`-linear logarithmic derivatives satisfies the exponential automorphy
law `f (z + l) = f z * exp (B l z) * f l / f 0` for a continuous form `B : V →L[ℝ] V →L[ℂ] ℂ`
with symmetric real part. -/
theorem exists_factor_of_automorphy [FiniteDimensional ℂ V] {f : V → ℂ} (hf_ne : ∀ z : V, f z ≠ 0)
    (h_logDeriv : ∀ l : L, ∃ a : V →L[ℂ] ℂ, ∀ z : V,
      HasFDerivAt (fun w ↦ f (l + w) / f w) ((f (l + z) / f z) • a) z) :
    ∃ B : V →L[ℝ] V →L[ℂ] ℂ,
      (∀ l ∈ L, ∀ z : V, f (z + l) = f z * exp (B l z) * f l / f 0) ∧
      ∀ u v : V, (B u v).re = (B v u).re := by
  choose a ha using h_logDeriv
  have h_add (l m : L) : a (l + m) = a l + a m := by
    have h_quot : (fun w : V ↦ f (↑(l + m) + w) / f w) =
        (fun w : V ↦ f (↑m + w) / f w) * fun w : V ↦ f (↑l + (↑m + w)) / f (↑m + w) := by
      ext w; simp [add_assoc, field, hf_ne]
    have h_prod := (ha m 0).mul ((hasFDerivAt_comp_add_left (m : V)).mpr (ha l ((m : V) + 0)))
    rw [← h_quot] at h_prod
    refine (smul_right_inj (div_ne_zero (hf_ne _) (hf_ne 0))).mp
      ((ha (l + m) 0).unique (h_prod.congr_fderiv ?_))
    ext v; simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, add_zero, coe_add]
    field_simp [hf_ne]
  have : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  obtain ⟨B, hB⟩ : ∃ B : V →L[ℝ] V →L[ℂ] ℂ, ∀ l : L, B l = a l := by
    let F : L →+ V →L[ℂ] ℂ := AddMonoidHom.mk' a h_add
    let b0 := Module.finBasis ℤ L
    let b := b0.ofZLatticeBasis ℝ L
    let φ : V →ₗ[ℝ] V →L[ℂ] ℂ := b.constr ℝ (F ∘ b0)
    refine ⟨φ.toContinuousLinearMap, fun l ↦ ?_⟩
    have hl : (l : V) = ∑ i, (b0.repr l i : ℝ) • b i := by
      calc (l : V) = L.subtype (∑ i, b0.repr l i • b0 i) := by rw [b0.sum_repr]; rfl
        _ = ∑ i, (b0.repr l i : ℝ) • b i := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_zsmul, Int.cast_smul_eq_zsmul]; simp [b]
    change φ (l : V) = F l
    rw [hl, map_sum φ]
    have hterm (i) : φ ((b0.repr l i : ℝ) • b i) = F (b0.repr l i • b0 i) := by
      rw [φ.map_smul, Int.cast_smul_eq_zsmul, map_zsmul]
      exact congrArg (b0.repr l i • ·) (b.constr_basis ℝ (F ∘ b0) i)
    simp_rw [hterm]; rw [← map_sum, b0.sum_repr]
  have h_factor (l : V) (hl : l ∈ L) (z : V) : f (z + l) = f z * exp (B l z) * f l / f 0 := by
    have h_deriv (w : V) :
        HasFDerivAt (fun w ↦ f (l + w) / f w * exp (-B l w)) (0 : V →L[ℂ] ℂ) w := by
      have h1 := (ha ⟨l, hl⟩ w).mul ((-B l).hasFDerivAt (x := w)).cexp
      rw [← hB ⟨l, hl⟩] at h1
      exact h1.congr_fderiv (by ext v; simp [_root_.add_apply, _root_.smul_apply]; ring)
    have h_const := is_const_of_fderiv_eq_zero (fun w ↦ (h_deriv w).differentiableAt)
      (fun w ↦ (h_deriv w).fderiv) z 0
    simpa [exp_neg, add_comm, field, hf_ne] using h_const
  exact ⟨B, h_factor, factor_of_automorphy_re_symm hf_ne h_factor⟩

/-- The continuous form `B : V →L[ℝ] V →L[ℂ] ℂ` in `exists_factor_of_automorphy` is uniquely
determined by the automorphy law on `L × V`. -/
theorem factor_of_automorphy_unique {f : V → ℂ} (hf_ne : ∀ z : V, f z ≠ 0)
    {B B' : V →L[ℝ] V →L[ℂ] ℂ}
    (hB : ∀ l ∈ L, ∀ z : V, f (z + l) = f z * exp (B l z) * f l / f 0)
    (hB' : ∀ l ∈ L, ∀ z : V, f (z + l) = f z * exp (B' l z) * f l / f 0) :
    B = B' := by
  have h_eq_on (l : V) (hl : l ∈ L) (z : V) : B l z = B' l z := by
    have h_exp (t : ℝ) : exp ((t : ℂ) * (B l z - B' l z)) = 1 := by
      have h1 := hB l hl ((t : ℂ) • z)
      have h2 := hB' l hl ((t : ℂ) • z)
      have h3 : exp (B l ((t : ℂ) • z)) = exp (B' l ((t : ℂ) • z)) := by
        simpa [mul_comm, mul_left_comm, field, hf_ne] using h1.symm.trans h2
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h3
      rw [mul_sub, exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]
      exact h3
    have h_deriv : HasDerivAt (fun t : ℝ ↦ exp ((t : ℂ) * (B l z - B' l z)))
        (B l z - B' l z) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (B l z - B' l z)).cexp
    have h_zero : HasDerivAt (fun t : ℝ ↦ exp ((t : ℂ) * (B l z - B' l z))) 0 0 := by
      simpa [h_exp] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
    exact sub_eq_zero.mp (h_deriv.unique h_zero)
  ext u v
  have h_span : u ∈ span ℝ (L : Set V) := eq_top_iff'.mp IsZLattice.span_top u
  induction h_span using span_induction with
  | mem x hx => exact h_eq_on x hx v
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

end TauCeti
