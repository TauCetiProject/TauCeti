/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.MvPowerSeries.LexOrder

/-!
# Convolution of power series with coefficient families

Let `R` be a semiring and `E` an `R`-module. A formal power series `f : MvPowerSeries σ R` acts
on a coefficient family `a : (σ →₀ ℕ) → E` by convolution,

```text
(f • a) t = ∑_{p + q = t} f_p • a_q.
```

This file defines the convolution `MvPowerSeries.convSMul` and proves its module laws: it is
additive in both arguments, constant series act through their constants, and it is compatible
with multiplication of series. For `E = R` it is the coefficient family of the product
(`MvPowerSeries.convSMul_coeff`), and linear maps of coefficient modules commute with it
(`MvPowerSeries.convSMul_comp`). When `E` is `R`-torsion-free over a cancellative `R`, nonzero
power series act faithfully on nonzero coefficient families (`MvPowerSeries.convSMul_eq_zero`),
which implies coefficientwise descent along submodules
(`MvPowerSeries.coeff_mem_of_coeff_map_mul_mem`). No norm or topology is needed.

## Implementation notes

The reindexing bijection in `MvPowerSeries.mul_convSMul` is the one Mathlib uses to prove
associativity of multiplication, `MvPowerSeries.mul_assoc`.
-/

public section

open Finset

namespace MvPowerSeries

variable {σ R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E]

/-- The convolution action of a formal power series `f` on a coefficient family `a`: the
coefficient of `f • a` at `t` is `∑_{p + q = t} f_p • a_q`. For `E = R` this is the coefficient
family of the product (`MvPowerSeries.convSMul_coeff`). -/
noncomputable def convSMul (f : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) : (σ →₀ ℕ) → E :=
  letI := Classical.decEq σ
  fun t ↦ ∑ p ∈ antidiagonal t, coeff p.1 f • a p.2

theorem convSMul_apply [DecidableEq σ] (f : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E)
    (t : σ →₀ ℕ) : convSMul f a t = ∑ p ∈ antidiagonal t, coeff p.1 f • a p.2 := by
  rw [convSMul, Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]

@[simp]
theorem zero_convSMul (a : (σ →₀ ℕ) → E) : convSMul (0 : MvPowerSeries σ R) a = 0 := by
  classical
  ext t
  simp [convSMul_apply]

@[simp]
theorem convSMul_zero (f : MvPowerSeries σ R) : convSMul f (0 : (σ →₀ ℕ) → E) = 0 := by
  classical
  ext t
  simp [convSMul_apply]

theorem add_convSMul (f g : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) :
    convSMul (f + g) a = convSMul f a + convSMul g a := by
  classical
  ext t
  simp [convSMul_apply, add_smul, Finset.sum_add_distrib]

theorem convSMul_add (f : MvPowerSeries σ R) (a b : (σ →₀ ℕ) → E) :
    convSMul f (a + b) = convSMul f a + convSMul f b := by
  classical
  ext t
  simp [convSMul_apply, smul_add, Finset.sum_add_distrib]

/-- A constant series acts on coefficient families through its constant. -/
@[simp]
theorem C_convSMul (r : R) (a : (σ →₀ ℕ) → E) : convSMul (C r : MvPowerSeries σ R) a = r • a := by
  classical
  ext t
  rw [convSMul_apply, Finset.sum_eq_single_of_mem (0, t) (by simp)]
  · simp
  · rintro ⟨p, q⟩ hpq hne
    have hp : p ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hpq)
    simp [coeff_C, hp]

@[simp]
theorem one_convSMul (a : (σ →₀ ℕ) → E) : convSMul (1 : MvPowerSeries σ R) a = a := by
  simpa using C_convSMul (σ := σ) (1 : R) a

/-- Convolution is compatible with multiplication of series. -/
theorem mul_convSMul (f g : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) :
    convSMul (f * g) a = convSMul f (convSMul g a) := by
  classical
  ext t
  simp only [convSMul_apply, coeff_mul, Finset.sum_smul, Finset.smul_sum, mul_smul,
    Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc])

/-- An `R`-linear map of coefficient modules commutes with convolution. -/
theorem convSMul_comp [AddCommMonoid F] [Module R F] (φ : E →ₗ[R] F) (f : MvPowerSeries σ R)
    (a : (σ →₀ ℕ) → E) : convSMul f (φ ∘ a) = φ ∘ convSMul f a := by
  classical
  ext t
  simp [convSMul_apply]

/-- For coefficients in the ring itself, convolution with the coefficients of `g` gives the
coefficients of the product `f * g`. -/
theorem convSMul_coeff (f g : MvPowerSeries σ R) :
    convSMul f (fun t ↦ coeff t g) = fun t ↦ coeff t (f * g) := by
  classical
  ext t
  simp [convSMul_apply, coeff_mul]

/-- When `E` is `R`-torsion-free over a cancellative `R`, the convolution of a nonzero series with
a nonzero coefficient family is nonzero. -/
theorem eq_zero_or_eq_zero_of_convSMul_eq_zero [IsCancelMulZero R] [Module.IsTorsionFree R E]
    {f : MvPowerSeries σ R} {a : (σ →₀ ℕ) → E} (h : convSMul f a = 0) :
    f = 0 ∨ a = 0 := by
  classical
  by_contra! hne
  obtain ⟨hf, ha⟩ := hne
  rcases exists_wellFoundedGT σ with ⟨_, _⟩
  obtain ⟨p, hp⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hf
  have hsup : (toLex '' Function.support a).Nonempty :=
    (Function.support_nonempty_iff.mpr ha).image _
  let wf : WellFounded (· < · : Lex (σ →₀ ℕ) → Lex (σ →₀ ℕ) → Prop) :=
    Finsupp.Lex.wellFoundedLT
  set qLex := wf.min (toLex '' Function.support a) hsup
  let q : σ →₀ ℕ := ofLex qLex
  have hq_ne : a q ≠ 0 := by
    have hmem := wf.min_mem (toLex '' Function.support a) hsup
    simpa only [q, Set.mem_image_equiv, toLex_symm_eq, Function.mem_support] using hmem
  have hq_min {v : σ →₀ ℕ} (hv : toLex v < toLex q) : a v = 0 := by
    by_contra hv_ne
    exact wf.not_lt_min (toLex '' Function.support a)
      (Set.mem_image_of_mem _ hv_ne) (by simpa only [q, toLex_ofLex] using hv)
  have hsum : convSMul f a (p + q) = coeff p f • a q := by
    rw [convSMul_apply, Finset.sum_eq_single_of_mem (p, q) (by simp)]
    rintro ⟨u, v⟩ huv hne_uv
    simp only [Finset.mem_antidiagonal] at huv
    rcases trichotomy_of_add_eq_add (congrArg toLex huv) with htri | htri | htri
    · exact False.elim (hne_uv (Prod.ext (toLex.injective htri.1) (toLex.injective htri.2)))
    · have hu : toLex u < lexOrder f := by rw [hp]; exact WithTop.coe_lt_coe.mpr htri
      rw [coeff_eq_zero_of_lt_lexOrder hu, zero_smul]
    · rw [hq_min htri, smul_zero]
  have hpq : coeff p f • a q = 0 := by rw [← hsum, h, Pi.zero_apply]
  exact (smul_eq_zero.mp hpq).elim (coeff_ne_zero_of_lexOrder hp.symm) hq_ne

@[simp]
theorem convSMul_eq_zero [IsCancelMulZero R] [Module.IsTorsionFree R E]
    {f : MvPowerSeries σ R} {a : (σ →₀ ℕ) → E} :
    convSMul f a = 0 ↔ f = 0 ∨ a = 0 :=
  ⟨eq_zero_or_eq_zero_of_convSMul_eq_zero, fun h ↦ h.elim (fun hf ↦ by simp [hf]) fun ha ↦ by
    simp [ha]⟩

/-- For an `R`-algebra `S` and an `R`-submodule `E ⊆ S` with torsion-free quotient `S ⧸ E`, if
`f : MvPowerSeries σ R` is nonzero and every coefficient of `map (algebraMap R S) f * g` lies in
`E`, then every coefficient of `g` lies in `E`. -/
theorem coeff_mem_of_coeff_map_mul_mem {R : Type*} {S : Type*} [CommRing R] [IsCancelMulZero R]
    [Ring S] [Algebra R S] (E : Submodule R S) [Module.IsTorsionFree R (S ⧸ E)]
    {f : MvPowerSeries σ R} (hf : f ≠ 0) {g : MvPowerSeries σ S}
    (hfg : ∀ t, coeff t (MvPowerSeries.map (algebraMap R S) f * g) ∈ E) (t : σ →₀ ℕ) :
    coeff t g ∈ E := by
  classical
  have hconv : convSMul f (E.mkQ ∘ fun d ↦ coeff d g) = 0 := by
    rw [convSMul_comp]
    ext d
    simp only [Function.comp_apply, Pi.zero_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    convert hfg d using 2
    rw [convSMul_apply, coeff_mul]
    refine Finset.sum_congr rfl fun pq _ ↦ ?_
    rw [Algebra.smul_def, coeff_map]
  have ha0 : (E.mkQ ∘ fun d ↦ coeff d g) = 0 :=
    (eq_zero_or_eq_zero_of_convSMul_eq_zero hconv).resolve_left hf
  exact (Submodule.Quotient.mk_eq_zero E).mp (congrFun ha0 t)

/-- For an `R`-algebra `S` and an `R`-saturated submodule `E ⊆ S`, if `f : MvPowerSeries σ R` is
nonzero and every coefficient of `map (algebraMap R S) f * g` lies in `E`, then every coefficient
of `g` lies in `E`. -/
theorem coeff_mem_of_coeff_map_mul_mem_of_smul_mem {R : Type*} {S : Type*} [CommRing R] [Ring S]
    [Algebra R S] (E : Submodule R S) (hE : ∀ {r : R} {s : S}, r ≠ 0 → r • s ∈ E → s ∈ E)
    {f : MvPowerSeries σ R} (hf : f ≠ 0) {g : MvPowerSeries σ S}
    (hfg : ∀ t, coeff t (MvPowerSeries.map (algebraMap R S) f * g) ∈ E) (t : σ →₀ ℕ) :
    coeff t g ∈ E := by
  by_contra ht
  have : Nontrivial R := ⟨1, 0, fun h10 ↦ ht <| by
    rw [← one_smul R (coeff t g), h10, zero_smul]
    exact E.zero_mem⟩
  have : NoZeroDivisors R := ⟨fun {a b} hab ↦ by
    by_contra! hab'
    refine ht (hE hab'.2 (hE hab'.1 ?_))
    rw [← mul_smul, hab, zero_smul]
    exact E.zero_mem⟩
  have : Module.IsTorsionFree R (S ⧸ E) := .of_smul_eq_zero fun r x hrx ↦ by
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective E x
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr ((Submodule.Quotient.mk_eq_zero E).mpr
        (hE hr ((Submodule.Quotient.mk_eq_zero E).mp hrx)))
  exact ht (coeff_mem_of_coeff_map_mul_mem E hf hfg t)

end MvPowerSeries
