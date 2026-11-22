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
* `TauCeti.IsCompleteFiltration.surjOn`: a map sending a complete filtration into a separated one
  compatibly, and surjective on the associated graded modules, maps `F 0` onto `G 0`.
* `TauCeti.isCompleteFiltration_pi`: the filtration of a product `∀ i, E i` by vanishing of the
  coordinates of weight below `n` is complete and separated.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
-/

public section

variable {R M : Type*}

namespace Module.End

variable [Semiring R] [AddCommMonoid M] [Module R M] {F : ℕ → Submodule R M}
  {T : Module.End R M}

/-- A map raising a filtration by one step raises it by `k` steps after `k` iterations. -/
theorem pow_apply_mem_of_map_le (hT : ∀ n, (F n).map T ≤ F (n + 1)) {m : ℕ} {y : M}
    (hy : y ∈ F m) (k : ℕ) : (T ^ k) y ∈ F (m + k) := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ← add_assoc]
    exact hT _ ⟨_, ih, rfl⟩

/-- If a family of submodules starts at the whole semimodule and vanishes at order `r`,
any endomorphism raising its order by one has zero `r`-th power. The family need not
be decreasing, and the coefficient semiring need not admit subtraction.

Adapted from `Mei/LinearAlgebra/ModuleFiltration/FiniteLength.lean` by Kimi K3 and Codex
(copyright 2026 Mei contributors, Apache 2.0), at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`.
Source: https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/LinearAlgebra/ModuleFiltration/FiniteLength.lean
-/
theorem pow_eq_zero_of_map_le (hT : ∀ n, (F n).map T ≤ F (n + 1))
    (hzero : F 0 = ⊤) {r : ℕ} (hr : F r = ⊥) : T ^ r = 0 := by
  ext x
  simpa [hr] using pow_apply_mem_of_map_le hT (by simp [hzero] : x ∈ F 0) r

end Module.End

variable [Ring R] [AddCommGroup M] [Module R M]

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

namespace IsCompleteFiltration

variable {F : ℕ → Submodule R M} (hF : IsCompleteFiltration F)
include hF

/-- **Tails of a complete filtration are complete.** Dropping the first `d` terms of a complete
separated filtration gives a complete separated filtration. -/
theorem comp_add_right (d : ℕ) : IsCompleteFiltration fun n ↦ F (n + d) where
  antitone _ _ h := hF.antitone (Nat.add_le_add_right h d)
  eq_zero_of_forall_mem x hx :=
    hF.eq_zero_of_forall_mem x fun n ↦ hF.antitone (Nat.le_add_right n d) (hx n)
  exists_limit x hx := by
    -- Delay the sequence by `d` steps, repeating its first term; the delayed sequence converges
    -- for `F`, and its limit is a limit of `x` for the tail.
    obtain ⟨L, hL⟩ := hF.exists_limit (fun n ↦ x (n - d)) fun n ↦ by
      rcases Nat.lt_or_ge n d with hn | hn
      · simp [Nat.sub_eq_zero_of_le hn, Nat.sub_eq_zero_of_le hn.le]
      · simpa [Nat.sub_add_comm hn, Nat.sub_add_cancel hn] using hx (n - d)
    exact ⟨L, fun n ↦ by simpa using hL (n + d)⟩

/-- **Complete filtrations pull back along linear equivalences.** If `F` is a complete separated
filtration of `M` and `e : N ≃ₗ[R] M`, the preimages of the `F n` form a complete separated
filtration of `N`. -/
theorem comap_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] M) :
    IsCompleteFiltration fun n ↦ (F n).comap (e : N →ₗ[R] M) where
  antitone _ _ h := Submodule.comap_mono (hF.antitone h)
  eq_zero_of_forall_mem x hx :=
    e.injective ((hF.eq_zero_of_forall_mem (e x) hx).trans e.map_zero.symm)
  exists_limit x hx := by
    obtain ⟨L, hL⟩ := hF.exists_limit (fun n ↦ e (x n)) fun n ↦ by simpa using hx n
    exact ⟨e.symm L, fun n ↦ by simpa using hL n⟩

/-- **Successive approximation.** Let `f` map a complete filtration `F` into a separated
filtration `G`, with `f (F n) ⊆ G n`. If `f` is surjective on the associated graded modules, in
the sense that every element of `G n` is the image of an element of `F n` up to an element of
`G (n + 1)`, then `f` maps `F 0` onto `G 0`. This is the analogue, for filtrations which need not
come from the powers of an ideal, of Mathlib's `surjective_of_mkQ_comp_surjective`. -/
theorem surjOn {N : Type*} [AddCommGroup N] [Module R N] {G : ℕ → Submodule R N}
    (hG : ∀ y, (∀ n, y ∈ G n) → y = 0) (f : M →ₗ[R] N) (hf : ∀ n, (F n).map f ≤ G n)
    (h : ∀ n, ∀ z ∈ G n, ∃ x ∈ F n, z - f x ∈ G (n + 1)) :
    Set.SurjOn f (F 0) (G 0) := by
  intro y hy
  -- Correct `y` one filtration step at a time: `x n` satisfies `y - f (x n) ∈ G n`.
  let x : (n : ℕ) → {x : M // y - f x ∈ G n} := fun n ↦ Nat.rec ⟨0, by simpa using hy⟩
    (fun n xn ↦ ⟨xn.val + (h n _ xn.property).choose, by
      rw [map_add, ← sub_sub]
      exact (h n _ xn.property).choose_spec.2⟩) n
  have hx (n : ℕ) : (x (n + 1)).val - (x n).val = (h n _ (x n).property).choose
      := add_sub_cancel_left _ _
  obtain ⟨L, hL⟩ := hF.exists_limit (fun n ↦ (x n).val) fun n ↦ by
    rw [hx]
    exact (h n _ (x n).property).choose_spec.1
  refine ⟨L, by simpa [x] using hL 0, (sub_eq_zero.1 (hG _ fun n ↦ ?_)).symm⟩
  rw [← sub_sub_sub_cancel_right y (f L) (f (x n).val), ← map_sub]
  exact sub_mem (x n).property (hf n ⟨_, hL n, rfl⟩)

end IsCompleteFiltration

end TauCeti

namespace Module.End

variable {F : ℕ → Submodule R M} {T : Module.End R M}

/-- If `T` raises a decreasing filtration with `F 0 = ⊤`, then `(1 + T) u ∈ F k` forces
`u ∈ F k`.  No completeness is needed. -/
theorem mem_of_one_add_apply_mem (hanti : Antitone F) (hF0 : F 0 = ⊤)
    (hT : ∀ n, (F n).map T ≤ F (n + 1)) {u : M} {k : ℕ} (hu : (1 + T) u ∈ F k) : u ∈ F k := by
  induction k with
  | zero => simp [hF0]
  | succ k ih =>
    have huk : u ∈ F k := ih (hanti (Nat.le_succ k) hu)
    simpa using sub_mem hu (hT k ⟨u, huk, rfl⟩)

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
    rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hu, one_apply_eq_self]
  have hgeom := LinearMap.congr_fun (mul_neg_geom_sum (-T) n) y
  rw [sub_neg_eq_add, mul_apply_eq_comp, LinearMap.sub_apply, one_apply_eq_self,
    LinearMap.sum_apply] at hgeom
  rw [map_sub, hinv, hgeom, sub_sub_cancel]
  exact pow_apply_mem_of_map_le (by simpa using hT) hy n

/-- If `T` raises a decreasing filtration with `F 0 = ⊤`, then the inverse of `1 + T` preserves
the filtration.  When `1 + T` is not invertible, `Ring.inverse (1 + T) = 0`. -/
theorem ringInverse_one_add_apply_mem (hanti : Antitone F) (hF0 : F 0 = ⊤)
    (hT : ∀ n, (F n).map T ≤ F (n + 1)) {m : ℕ} {y : M} (hy : y ∈ F m) :
    Ring.inverse (1 + T) y ∈ F m := by
  by_cases hu : IsUnit (1 + T)
  · simpa using ringInverse_one_add_apply_sub_sum_mem hanti hF0 hT hu hy 0
  · simp [Ring.inverse_non_unit _ hu]

end Module.End

namespace TauCeti.IsCompleteFiltration

variable {F : ℕ → Submodule R M} (hF : IsCompleteFiltration F) (hF0 : F 0 = ⊤)
  {T : Module.End R M} (hT : ∀ n, (F n).map T ≤ F (n + 1))
include hF hF0 hT

/-- **Inverting `1 + T` on a complete filtered module.**  If `T` raises a complete separated
filtration with `F 0 = ⊤`, then `1 + T` is invertible, its inverse being the convergent geometric
series `∑ₖ (-T)ᵏ` (`Module.End.ringInverse_one_add_apply_sub_sum_mem`). -/
theorem isUnit_one_add : IsUnit (1 + T) := by
  rw [Module.End.isUnit_iff]
  refine ⟨(injective_iff_map_eq_zero (1 + T)).2 fun u hu ↦ ?_, fun y ↦ ?_⟩
  · exact hF.eq_zero_of_forall_mem u fun n ↦
      Module.End.mem_of_one_add_apply_mem hF.antitone hF0 hT (hu ▸ zero_mem (F n))
  · -- Successive approximation correcting `z ∈ F n` by `z` itself, as `z - (1 + T) z = -T z`;
    -- the corrections are the terms `(-T) ^ k y` of the geometric series.
    have hle (n : ℕ) {z : M} (hz : z ∈ F n) : T z ∈ F (n + 1) := hT n ⟨z, hz, rfl⟩
    have hsurj := hF.surjOn hF.eq_zero_of_forall_mem (1 + T)
      (fun n ↦ Submodule.map_le_iff_le_comap.2 fun z hz ↦ by
        rw [Submodule.mem_comap, LinearMap.add_apply, one_apply_eq_self]
        exact add_mem hz (hF.antitone n.le_succ (hle n hz)))
      fun n z hz ↦ ⟨z, hz, by simpa using hle n hz⟩
    obtain ⟨L, -, hL⟩ := hsurj (by simp [hF0] : y ∈ F 0)
    exact ⟨L, hL⟩

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
    have hconst (i : ι) (n : ℕ) (hn : w i + 1 ≤ n) : x n i = x (w i + 1) i := by
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih =>
        rw [← ih, ← sub_eq_zero, ← Pi.sub_apply]
        exact (hF n _).1 (hx n) i (by omega)
    refine ⟨fun i ↦ x (w i + 1) i, fun n ↦ (hF n _).2 fun i hi ↦ ?_⟩
    rw [Pi.sub_apply, hconst i n (by omega), sub_self]

end TauCeti
