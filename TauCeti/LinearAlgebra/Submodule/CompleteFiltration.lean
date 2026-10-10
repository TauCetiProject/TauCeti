/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Pi

/-!
# Complete separated filtrations and inverting `1 + T`

A descending filtration `F 0 ⊇ F 1 ⊇ ⋯` of a module by submodules is *complete and separated*
when its intersection is zero and every sequence whose consecutive differences lie deeper and
deeper in the filtration has a limit, unique by separatedness.  This is the filtered analogue of
Mathlib's `IsAdicComplete`, for a filtration which need not consist of the powers of an ideal.
The main examples are products graded by a weight, such as tensor coalgebras completed with
respect to tensor length.

On such a module, with `F 0` everything, an endomorphism `T` which raises the filtration,
`T (F n) ⊆ F (n + 1)`, has `1 + T` invertible: the geometric series `∑ₖ (-T)ᵏ y` converges.
This is the convergent counterpart of the pointwise-finite case
`Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`, and it is the input to the
perturbation lemma for complete filtered contractions, where the series need not be finite.

## Main definitions

* `TauCeti.IsCompleteFiltration`: a complete separated descending filtration by submodules.

## Main results

* `Module.End.mem_of_one_add_apply_mem`: if `T` raises a decreasing filtration with `F 0 = ⊤`,
  then `(1 + T) u ∈ F k` forces `u ∈ F k`.
* `TauCeti.IsCompleteFiltration.isUnit_one_add`: `1 + T` is a unit when `T` raises a complete
  separated filtration with `F 0 = ⊤`.
* `Module.End.ringInverse_one_add_apply_sub_sum_mem`: when `1 + T` is invertible, its inverse
  is the limit of the partial geometric sums, with an explicit rate of convergence.
* `Module.End.ringInverse_one_add_apply_mem`: the inverse preserves the filtration.
* `TauCeti.isCompleteFiltration_pi`: the filtration of a product `∀ i, E i` by vanishing of the
  coordinates of weight below `n` is complete and separated.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
-/

public section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

namespace TauCeti

/-- A descending filtration `F 0 ⊇ F 1 ⊇ ⋯` of a module by submodules is **complete and
separated** when only `0` lies in every `F n`, and every sequence `x` with
`x (n + 1) - x n ∈ F n` for all `n` has a limit `L`, meaning `L - x n ∈ F n` for all `n`.
Equivalently, the module maps isomorphically onto the inverse limit of the quotients `M ⧸ F n`. -/
structure IsCompleteFiltration (F : ℕ → Submodule R M) : Prop where
  /-- The filtration is decreasing. -/
  antitone : Antitone F
  /-- The filtration is separated: its intersection is zero. -/
  eq_zero_of_forall_mem : ∀ x, (∀ n, x ∈ F n) → x = 0
  /-- The filtration is complete: a sequence whose consecutive differences lie deeper and deeper
  in the filtration has a limit. -/
  exists_limit : ∀ x : ℕ → M, (∀ n, x (n + 1) - x n ∈ F n) → ∃ L, ∀ n, L - x n ∈ F n

end TauCeti

namespace Module.End

variable {F : ℕ → Submodule R M} {T : Module.End R M}

/-- A map raising a filtration by one step raises it by `k` steps after `k` iterations. -/
theorem pow_apply_mem_of_map_le (hT : ∀ n, (F n).map T ≤ F (n + 1)) {m : ℕ} {y : M}
    (hy : y ∈ F m) (k : ℕ) : (T ^ k) y ∈ F (m + k) := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact hT _ ⟨_, ih, rfl⟩

/-- If `T` raises a decreasing filtration with `F 0 = ⊤`, then `(1 + T) u ∈ F k` forces
`u ∈ F k`: writing `u = (1 + T) u - T u`, membership of `u` in `F j` improves to `F (j + 1)` until
it reaches `F k`.  No completeness is needed. -/
theorem mem_of_one_add_apply_mem (hanti : Antitone F) (hF0 : F 0 = ⊤)
    (hT : ∀ n, (F n).map T ≤ F (n + 1)) {u : M} {k : ℕ} (hu : (1 + T) u ∈ F k) : u ∈ F k := by
  have key : ∀ j, u ∈ F (min k j) := by
    intro j
    induction j with
    | zero => simp [hF0]
    | succ j ih =>
      have hTu : T u ∈ F (min k (j + 1)) :=
        hanti (by omega) (hT _ ⟨u, ih, rfl⟩)
      have hu' : (1 + T) u ∈ F (min k (j + 1)) := hanti (min_le_left _ _) hu
      have h : u = (1 + T) u - T u := by
        rw [LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_right]
      rw [h]
      exact sub_mem hu' hTu
  simpa using key k

private theorem map_neg_le (hT : ∀ n, (F n).map T ≤ F (n + 1)) (n : ℕ) :
    (F n).map (-T) ≤ F (n + 1) := by
  rw [Submodule.map_neg]
  exact hT n

/-- **The inverse of `1 + T` is the sum of the geometric series.**  If `T` raises a decreasing
filtration with `F 0 = ⊤` and `1 + T` is invertible, then on `y ∈ F m` the inverse of `1 + T`
differs from the partial sum `∑_{k < n} (-T)ᵏ y` by an element of `F (m + n)`.  No completeness is
needed once invertibility is known; on a complete filtration it is supplied by
`TauCeti.IsCompleteFiltration.isUnit_one_add`. -/
theorem ringInverse_one_add_apply_sub_sum_mem (hanti : Antitone F) (hF0 : F 0 = ⊤)
    (hT : ∀ n, (F n).map T ≤ F (n + 1)) (hu : IsUnit (1 + T)) {m : ℕ} {y : M} (hy : y ∈ F m)
    (n : ℕ) : Ring.inverse (1 + T) y - ∑ k ∈ Finset.range n, ((-T) ^ k) y ∈ F (m + n) := by
  refine mem_of_one_add_apply_mem hanti hF0 hT ?_
  have hinv : (1 + T) (Ring.inverse (1 + T) y) = y := by
    rw [← Module.End.mul_apply, Ring.mul_inverse_cancel _ hu, Module.End.one_apply]
  have hgeom := LinearMap.congr_fun (mul_neg_geom_sum (-T) n) y
  rw [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.sum_apply] at hgeom
  rw [map_sub, hinv, hgeom, sub_sub_cancel]
  exact pow_apply_mem_of_map_le (map_neg_le hT) hy n

/-- If `T` raises a decreasing filtration with `F 0 = ⊤` and `1 + T` is invertible, then the
inverse of `1 + T` preserves the filtration. -/
theorem ringInverse_one_add_apply_mem (hanti : Antitone F) (hF0 : F 0 = ⊤)
    (hT : ∀ n, (F n).map T ≤ F (n + 1)) (hu : IsUnit (1 + T)) {m : ℕ} {y : M} (hy : y ∈ F m) :
    Ring.inverse (1 + T) y ∈ F m := by
  simpa using ringInverse_one_add_apply_sub_sum_mem hanti hF0 hT hu hy 0

end Module.End

namespace TauCeti.IsCompleteFiltration

variable {F : ℕ → Submodule R M} (hF : IsCompleteFiltration F) (hF0 : F 0 = ⊤)
  {T : Module.End R M} (hT : ∀ n, (F n).map T ≤ F (n + 1))
include hF hF0 hT

/-- **Inverting `1 + T` on a complete filtered module.**  If `T` raises a complete separated
filtration with `F 0 = ⊤`, then `1 + T` is invertible, its inverse being the convergent geometric
series `∑ₖ (-T)ᵏ`. -/
theorem isUnit_one_add : IsUnit (1 + T) := by
  rw [Module.End.isUnit_iff]
  refine ⟨(injective_iff_map_eq_zero (1 + T)).2 fun u hu ↦ ?_, fun y ↦ ?_⟩
  · exact hF.eq_zero_of_forall_mem u fun n ↦
      Module.End.mem_of_one_add_apply_mem hF.antitone hF0 hT (hu ▸ zero_mem (F n))
  · -- The partial geometric sums form a Cauchy sequence; its limit is a preimage of `y`.
    have hy : y ∈ F 0 := by simp [hF0]
    have hpow := Module.End.pow_apply_mem_of_map_le (Module.End.map_neg_le hT) hy
    obtain ⟨L, hL⟩ := hF.exists_limit (fun n ↦ (∑ k ∈ Finset.range n, (-T) ^ k) y) fun n ↦ by
      simpa [Finset.sum_range_succ] using hpow n
    refine ⟨L, sub_eq_zero.mp (hF.eq_zero_of_forall_mem _ fun n ↦ ?_)⟩
    have hgeom := LinearMap.congr_fun (mul_neg_geom_sum (-T) n) y
    rw [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at hgeom
    have h : (1 + T) L - y =
        (1 + T) (L - (∑ k ∈ Finset.range n, (-T) ^ k) y) - ((-T) ^ n) y := by
      rw [map_sub, hgeom, sub_sub, sub_add_cancel]
    rw [h]
    refine sub_mem ?_ (by simpa using hpow n)
    rw [LinearMap.add_apply, Module.End.one_apply]
    exact add_mem (hL n) (hF.antitone (Nat.le_succ n) (hT n ⟨_, hL n, rfl⟩))

end TauCeti.IsCompleteFiltration

namespace TauCeti

/-- **Weight filtrations of products are complete.**  Let `w` assign a weight to each factor of
the product `∀ i, E i`.  The filtration whose `n`-th term consists of the families vanishing in
every coordinate of weight below `n` is complete and separated: a limit is read off one
coordinate at a time, the `i`-th coordinate of a Cauchy sequence being constant from step
`w i + 1` on. -/
theorem isCompleteFiltration_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module R (E i)] (w : ι → ℕ) (F : ℕ → Submodule R (∀ i, E i))
    (hF : ∀ n x, x ∈ F n ↔ ∀ i, w i < n → x i = 0) : IsCompleteFiltration F where
  antitone n m hnm x hx := (hF n x).2 fun i hi ↦ (hF m x).1 hx i (hi.trans_le hnm)
  eq_zero_of_forall_mem x hx := funext fun i ↦ (hF _ x).1 (hx (w i + 1)) i (Nat.lt_succ_self _)
  exists_limit x hx := by
    -- From step `w i + 1` on, the `i`-th coordinate of `x` no longer changes.
    have hconst : ∀ i, ∀ n, w i + 1 ≤ n → x n i = x (w i + 1) i := by
      intro i n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih =>
        rw [← ih, ← sub_eq_zero, ← Pi.sub_apply]
        exact (hF n _).1 (hx n) i (by omega)
    refine ⟨fun i ↦ x (w i + 1) i, fun n ↦ (hF n _).2 fun i hi ↦ ?_⟩
    rw [Pi.sub_apply, hconst i n (by omega), sub_self]

end TauCeti
