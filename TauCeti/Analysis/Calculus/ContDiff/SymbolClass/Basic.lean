/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# Symbol classes along a filter

A map `f` from a real normed space `E` is a **symbol of order `ℓ` and regularity `n` along a
filter `l`** (`TauCeti.IsSymbolAlong l n ℓ f`) when it is `Cⁿ` at the points of a set of `l` and,
for every `j ≤ n`, its `j`-th derivative is `O(‖x‖ ^ (ℓ - j))` along `l`. Along the punctured
neighbourhoods of `0` with `n = ∞` these are the punctured symbols `TauCeti.IsPuncturedSymbol`,
and along the cobounded filter with finite `n` the symbols at infinity
`TauCeti.IsSymbolAtInfinity`.

This file proves, once for every filter, the rules of the symbol calculus that do not depend on
the filter:

* dependence only on the map near the points of a set of the filter
  (`IsSymbolAlong.congr_of_eventually_nhds`);
* sums, finite sums, negatives, differences, linear images and passage to lower regularity
  (`IsSymbolAlong.add`, `IsSymbolAlong.sum`, `IsSymbolAlong.neg`, `IsSymbolAlong.sub`,
  `IsSymbolAlong.continuousLinearMap_comp`, `IsSymbolAlong.of_le`), with constants of order `0`
  (`TauCeti.isSymbolAlong_const`) and the zero map of every order
  (`TauCeti.isSymbolAlong_zero`);
* **products add orders**: for a continuous bilinear map `B`, if `f` has order `ℓ` and `g` has
  order `m`, then `x ↦ B (f x) (g x)` has order `ℓ + m` (`IsSymbolAlong.bilinear`, with the
  special cases `IsSymbolAlong.smul`, `IsSymbolAlong.const_smul`, `IsSymbolAlong.mul` and
  `IsSymbolAlong.pow`), from the Leibniz bound at a fixed derivative order
  (`ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_rpow`);
* **differentiation lowers the order and the regularity by one** (`IsSymbolAlong.fderiv`), and
  conversely a map that is `C^(n + 1)` at the points of a set of `l` and `O(‖x‖ ^ ℓ)`, and whose
  derivative has order `ℓ - 1` and regularity `n`, has order `ℓ` and regularity `n + 1`
  (`TauCeti.isSymbolAlong_add_one_iff`).

The inductive step shared by the derivative bounds of inverses and compositions, where the
derivative of a map is a bilinear expression in maps of lower order, is
`TauCeti.isBigO_iteratedFDeriv_succ_rpow_of_eventuallyEq`. The rules that depend on the filter,
such as the comparison of orders, limits and compositions, are proved in the files of the two
classes.
-/

public section

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace TauCeti

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup H]

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]

/-- A map `f` is a **symbol of order `ℓ` and regularity `n` along a filter `l`** if it is `Cⁿ` at
the points of a set of `l` and, for every `j ≤ n`, its `j`-th derivative is `O(‖x‖ ^ (ℓ - j))`
along `l`. -/
def IsSymbolAlong (l : Filter E) (n : ℕ∞) (ℓ : ℝ) (f : E → F) : Prop :=
  (∀ᶠ x in l, ContDiffAt ℝ n f x) ∧
    ∀ j : ℕ, j ≤ n → iteratedFDeriv ℝ j f =O[l] fun x ↦ ‖x‖ ^ (ℓ - j)

/-- The defining properties of a symbol along `l`: `Cⁿ` regularity at the points of a set of `l`
and the bounds `D^j f = O(‖x‖ ^ (ℓ - j))` along `l` for `j ≤ n`. -/
theorem isSymbolAlong_iff {l : Filter E} {n : ℕ∞} {ℓ : ℝ} {f : E → F} :
    IsSymbolAlong l n ℓ f ↔ (∀ᶠ x in l, ContDiffAt ℝ n f x) ∧
      ∀ j : ℕ, j ≤ n → iteratedFDeriv ℝ j f =O[l] fun x ↦ ‖x‖ ^ (ℓ - j) :=
  Iff.rfl

/-! ### Basic properties -/

namespace IsSymbolAlong

variable {l : Filter E} {n n' : ℕ∞} {ℓ m : ℝ} {f f₁ : E → F} {g : E → G}

/-- A symbol of regularity `n` along `l` is `Cⁿ` at the points of a set of `l`. -/
theorem eventually_contDiffAt (hf : IsSymbolAlong l n ℓ f) : ∀ᶠ x in l, ContDiffAt ℝ n f x :=
  hf.1

/-- The `j`-th derivative of a symbol of order `ℓ` along `l` is `O(‖x‖ ^ (ℓ - j))`, for `j` at
most the regularity. -/
theorem isBigO_iteratedFDeriv (hf : IsSymbolAlong l n ℓ f) {j : ℕ} (hj : j ≤ n) :
    iteratedFDeriv ℝ j f =O[l] fun x ↦ ‖x‖ ^ (ℓ - j) :=
  hf.2 j hj

/-- A symbol of order `ℓ` along `l` is `O(‖x‖ ^ ℓ)` along `l`. -/
theorem isBigO (hf : IsSymbolAlong l n ℓ f) : f =O[l] fun x ↦ ‖x‖ ^ ℓ := by
  simpa using isBigO_iteratedFDeriv_zero_iff.1 (hf.2 0 (by simp))

/-- Being a symbol along `l` only depends on the map near the points of a set of `l`. -/
theorem congr_of_eventually_nhds (hf : IsSymbolAlong l n ℓ f) (h : ∀ᶠ x in l, f =ᶠ[𝓝 x] f₁) :
    IsSymbolAlong l n ℓ f₁ := by
  refine ⟨?_, fun j hj ↦ (hf.2 j hj).congr' ?_ EventuallyEq.rfl⟩
  · filter_upwards [hf.1, h] with x hx hx'
    exact hx.congr_of_eventuallyEq hx'.symm
  · filter_upwards [h] with x hx
    exact (hx.iteratedFDeriv ℝ j).eq_of_nhds

/-- A symbol of regularity `n` has every smaller regularity. -/
theorem of_le (hf : IsSymbolAlong l n ℓ f) (h : n' ≤ n) : IsSymbolAlong l n' ℓ f :=
  ⟨hf.1.mono fun _ hx ↦ hx.of_le (by exact_mod_cast h), fun j hj ↦ hf.2 j (hj.trans h)⟩

/-- The sum of two symbols of order `ℓ` has order `ℓ`. -/
theorem add (hf : IsSymbolAlong l n ℓ f) (hf₁ : IsSymbolAlong l n ℓ f₁) :
    IsSymbolAlong l n ℓ fun x ↦ f x + f₁ x := by
  refine ⟨?_, fun j hj ↦ ((hf.2 j hj).add (hf₁.2 j hj)).congr' ?_ EventuallyEq.rfl⟩
  · filter_upwards [hf.1, hf₁.1] with x hx hx₁
    exact hx.add hx₁
  · filter_upwards [hf.1, hf₁.1] with x hx hx₁
    exact (iteratedFDeriv_add_apply (hx.of_le (by exact_mod_cast hj))
      (hx₁.of_le (by exact_mod_cast hj))).symm

/-- The negative of a symbol of order `ℓ` has order `ℓ`. -/
theorem neg (hf : IsSymbolAlong l n ℓ f) : IsSymbolAlong l n ℓ fun x ↦ -f x := by
  refine ⟨?_, fun j hj ↦ (hf.2 j hj).neg_left.congr' ?_ EventuallyEq.rfl⟩
  · filter_upwards [hf.1] with x hx
    exact hx.neg
  · exact Eventually.of_forall fun x ↦ (iteratedFDeriv_neg_apply (f := f)).symm

/-- The difference of two symbols of order `ℓ` has order `ℓ`. -/
theorem sub (hf : IsSymbolAlong l n ℓ f) (hf₁ : IsSymbolAlong l n ℓ f₁) :
    IsSymbolAlong l n ℓ fun x ↦ f x - f₁ x := by
  simpa [sub_eq_add_neg] using hf.add hf₁.neg

/-- The image of a symbol under a continuous linear map is a symbol of the same order. -/
theorem continuousLinearMap_comp (hf : IsSymbolAlong l n ℓ f) (L : F →L[ℝ] G) :
    IsSymbolAlong l n ℓ fun x ↦ L (f x) := by
  refine ⟨?_, fun j hj ↦ (IsBigO.of_bound ‖L‖ ?_).trans (hf.2 j hj)⟩
  · filter_upwards [hf.1] with x hx
    exact L.contDiff.contDiffAt.comp x hx
  · filter_upwards [hf.1] with x hx
    exact L.norm_iteratedFDeriv_comp_left (f := f) hx (by exact_mod_cast hj)

/-- Differentiation lowers the order of a symbol by one, and its regularity by one. -/
protected theorem fderiv (hf : IsSymbolAlong l (n + 1) ℓ f) :
    IsSymbolAlong l n (ℓ - 1) (fderiv ℝ f) := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · filter_upwards [hf.1] with x hx
    exact hx.fderiv_right (m := n) (by push_cast; rfl)
  · have h := (hf.2 (j + 1) (by push_cast; gcongr)).norm_left
    simp_rw [← norm_iteratedFDeriv_fderiv (n := j)] at h
    rw [show ℓ - 1 - (j : ℝ) = ℓ - (j + 1 : ℕ) by push_cast; ring]
    exact h.of_norm_left

end IsSymbolAlong

variable {l : Filter E} {n : ℕ∞} {ℓ m : ℝ}

/-- A constant map is a symbol of order `0` along every filter. -/
theorem isSymbolAlong_const (c : F) : IsSymbolAlong l n 0 fun _ : E ↦ c := by
  refine ⟨Eventually.of_forall fun _ ↦ contDiffAt_const, fun j _ ↦ ?_⟩
  rcases eq_or_ne j 0 with rfl | hj
  · refine IsBigO.of_bound ‖c‖ (Eventually.of_forall fun x ↦ ?_)
    simp
  · rw [iteratedFDeriv_const_of_ne hj]
    exact isBigO_zero _ _

/-- The zero map is a symbol of every order along every filter. -/
theorem isSymbolAlong_zero : IsSymbolAlong l n ℓ fun _ : E ↦ (0 : F) :=
  ⟨Eventually.of_forall fun _ ↦ contDiffAt_const, fun j _ ↦ by
    rw [iteratedFDeriv_fun_zero]
    exact isBigO_zero _ _⟩

/-- **Differentiation rule.** A map has order `ℓ` and regularity `n + 1` along `l` exactly when it
is `C^(n + 1)` at the points of a set of `l`, `O(‖x‖ ^ ℓ)` along `l`, and its derivative has order
`ℓ - 1` and regularity `n`. -/
theorem isSymbolAlong_add_one_iff {f : E → F} :
    IsSymbolAlong l (n + 1) ℓ f ↔ (∀ᶠ x in l, ContDiffAt ℝ (n + 1) f x) ∧
      (f =O[l] fun x ↦ ‖x‖ ^ ℓ) ∧ IsSymbolAlong l n (ℓ - 1) (fderiv ℝ f) := by
  refine ⟨fun hf ↦ ⟨hf.1, hf.isBigO, hf.fderiv⟩, fun ⟨hC, h0, hD⟩ ↦ ⟨hC, fun j hj ↦ ?_⟩⟩
  cases j with
  | zero => simpa using h0
  | succ j =>
    have hj' : (j : ℕ∞) ≤ n := (ENat.add_le_add_iff_right ENat.one_ne_top).1 (by exact_mod_cast hj)
    have h := (hD.2 j hj').norm_left
    simp_rw [norm_iteratedFDeriv_fderiv (n := j)] at h
    rw [show ℓ - (j + 1 : ℕ) = ℓ - 1 - (j : ℝ) by push_cast; ring]
    exact h.of_norm_left

namespace IsSymbolAlong

variable {f : E → F} {g : E → G}

/-- A finite sum of symbols of order `ℓ` has order `ℓ`. -/
theorem sum {ι : Type*} {s : Finset ι} {f : ι → E → F} (hf : ∀ i ∈ s, IsSymbolAlong l n ℓ (f i)) :
    IsSymbolAlong l n ℓ fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSymbolAlong_zero (l := l) (n := n) (ℓ := ℓ) (F := F)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-! ### Products -/

/-- **Products of symbols add their orders.** For a continuous bilinear map `B`, if `f` has order
`ℓ` and `g` has order `m`, then `x ↦ B (f x) (g x)` has order `ℓ + m`. -/
theorem bilinear (hf : IsSymbolAlong l n ℓ f) (hg : IsSymbolAlong l n m g)
    (B : F →L[ℝ] G →L[ℝ] H) : IsSymbolAlong l n (ℓ + m) fun x ↦ B (f x) (g x) :=
  ⟨(hf.1.and hg.1).mono fun _ hx ↦ B.isBoundedBilinearMap.contDiff.comp₂_contDiffAt hx.1 hx.2,
    fun _ hj ↦ B.isBigO_iteratedFDeriv_of_bilinear_rpow hf.1 hg.1 (by exact_mod_cast hj)
      (fun i hi ↦ hf.2 i ((Nat.cast_le.2 hi).trans hj))
      (fun i hi ↦ hg.2 i ((Nat.cast_le.2 hi).trans hj))⟩

/-- A scalar symbol of order `ℓ` times a vector symbol of order `m` is a symbol of order
`ℓ + m`. -/
theorem smul {𝕜 : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 G] [IsBoundedSMul 𝕜 G]
    [IsScalarTower ℝ 𝕜 G] {a : E → 𝕜} (ha : IsSymbolAlong l n ℓ a) (hg : IsSymbolAlong l n m g) :
    IsSymbolAlong l n (ℓ + m) fun x ↦ a x • g x :=
  ha.bilinear hg (ContinuousLinearMap.lsmul ℝ 𝕜)

/-- A constant multiple of a symbol of order `ℓ` has order `ℓ`. -/
theorem const_smul {𝕜 : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 G]
    [IsBoundedSMul 𝕜 G] [IsScalarTower ℝ 𝕜 G] (hg : IsSymbolAlong l n ℓ g) (a : 𝕜) :
    IsSymbolAlong l n ℓ fun x ↦ a • g x := by
  simpa using (isSymbolAlong_const a).smul hg

/-- Products of symbols with values in a normed algebra add their orders. -/
theorem mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {a b : E → A}
    (ha : IsSymbolAlong l n ℓ a) (hb : IsSymbolAlong l n m b) :
    IsSymbolAlong l n (ℓ + m) fun x ↦ a x * b x :=
  ha.bilinear hb (ContinuousLinearMap.mul ℝ A)

/-- The `k`-th power of a symbol of order `ℓ` has order `k * ℓ`. -/
theorem pow {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {a : E → A}
    (ha : IsSymbolAlong l n ℓ a) (k : ℕ) : IsSymbolAlong l n (k * ℓ) fun x ↦ a x ^ k := by
  induction k with
  | zero =>
    simpa using isSymbolAlong_const (l := l) (n := n) (E := E) (1 : A)
  | succ k ih =>
    simpa [pow_succ, add_mul] using ih.mul ha

end IsSymbolAlong

end TauCeti
