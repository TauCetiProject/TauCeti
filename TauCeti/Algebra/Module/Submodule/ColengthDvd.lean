/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Operations

import Mathlib.Tactic.Linarith

/-!
# Colength dividing an element

For submodules `M`, `N` of a module `V` over a commutative ring `O` and `z ∈ O`, we say that *the
colength of `N` in `M` divides `z`*, written `M ⊸_z N` in the comments, when every finite family
`Φ_1, …, Φ_n` of elements of `M` is carried into `N` by an `n × n` matrix over `O` whose determinant
divides `z`: `∑ k, m i k • Φ k ∈ N` for every `i`. It needs neither bases nor an inclusion between
`M` and `N`, and makes sense over any commutative ring. It stands for a bound on the colength of
`M ⊓ N` in `M`: over a discrete valuation ring and for finitely generated `M`, applying it to a
generating family bounds the length of `M ⧸ (M ⊓ N)` by that of `O ⧸ (z)`
(`Submodule.ColengthDvd.length_quotient_le` in `TauCeti.RingTheory.Length.ColengthDvd`). Tau Ceti's
lemmas on module length, such as `TauCeti.length_quotient_comap_subtype_map_list_prod_le`, give the
analogous bounds for lengths. The bounds over a valuation domain that come from the Smith normal
form are in `TauCeti.RingTheory.Valuation.ColengthDvd`.

An endomorphism `y` of `V` is *onto `M` modulo `p ^ n` up to colength `c`* (`p ∈ O`, `c ∈ ℝ`) when
`y(M) ⊆ M` and `M ⊸_{p ^ l} (y(M) + p ^ n • M)` for some natural number `l ≤ c`.

## Main definitions

* `Submodule.ColengthDvd M N z`: the colength of `N` in `M` divides `z`.
* `Module.End.IsOntoUpToColength y M p n c`: `y` is onto `M` modulo `p ^ n` up to colength `c`.

## Main results

* `Submodule.ColengthDvd.of_le`, `Submodule.ColengthDvd.trans_dvd`: `M ≤ N` gives `M ⊸_1 N`, and
  the element may be replaced by a multiple; `Submodule.colengthDvd_iff_le_of_isUnit`: for a unit
  `z`, `M ⊸_z N` holds exactly when `M ≤ N`.
* `Submodule.ColengthDvd.exists_matrix`: the condition for families indexed by any finite type, and
  `Submodule.ColengthDvd.exists_smul_mem`: each `x ∈ M` has a multiple `a • x ∈ N` with `a ∣ z`,
  so `z • M ≤ N` (`Submodule.ColengthDvd.smul_le`).
* `Submodule.ColengthDvd.trans`: `M ⊸_z N` and `N ⊸_a P` give `M ⊸_{z * a} P`.
* `Submodule.ColengthDvd.comap`, `Submodule.ColengthDvd.map`: pull-back and push-forward along a
  linear map.
* `Submodule.ColengthDvd.map_sup_smul`: if `f(M) ⊆ M`, `M ⊸_z (f(M) + a • M)` and
  `M ⊸_{z'} (N + a • M)`, then `M ⊸_{z * z'} (f(N) + a • M)`; `Submodule.ColengthDvd.map_sup` is
  the same with any `Q` satisfying `f(Q) ⊆ Q` in place of `a • M`.
* `Module.End.IsOntoUpToColength.mul`, `Module.End.isOntoUpToColength_list_prod`,
  `Module.End.IsOntoUpToColength.pow`: the colengths add along products of endomorphisms.

## References

The statements follow the formal proof in the folder `grh` of https://github.com/lsernau/grh-lean
at commit 72fead102f663d5c7a407964a13dc0cf9d977207 (`New.ColengthDvd`, `New.ColengthDvd.trans`,
`New.ColengthDvd.comap`, `New.ColengthDvd.map`, `New.ColengthDvd.comp`,
`New.IsOntoUpToColength`, `New.IsOntoUpToColength.prod`).
-/

public section

open Matrix Pointwise

namespace Submodule

variable {O V U : Type*} [CommRing O] [AddCommMonoid V] [Module O V] [AddCommMonoid U]
  [Module O U]

/-- **The colength of `N` in `M` divides `z`**: for every `n` and every family `Φ : Fin n → V` of
elements of `M` there is a matrix `m : Matrix (Fin n) (Fin n) O` with `m.det ∣ z` and
`∑ k, m i k • Φ k ∈ N` for every `i`. No inclusion between `M` and `N` is asked. -/
def ColengthDvd (M N : Submodule O V) (z : O) : Prop :=
  ∀ (n : ℕ) (Φ : Fin n → V), (∀ k, Φ k ∈ M) →
    ∃ m : Matrix (Fin n) (Fin n) O, m.det ∣ z ∧ ∀ i, ∑ k, m i k • Φ k ∈ N

variable {M N P M' N' Q : Submodule O V} {z z' a : O}

/-- The definition of `Submodule.ColengthDvd`, restated: its body is not exposed outside this
module. -/
theorem colengthDvd_iff : M.ColengthDvd N z ↔ ∀ (n : ℕ) (Φ : Fin n → V), (∀ k, Φ k ∈ M) →
    ∃ m : Matrix (Fin n) (Fin n) O, m.det ∣ z ∧ ∀ i, ∑ k, m i k • Φ k ∈ N :=
  Iff.rfl

/-- If `M ⊸_z N`, then every family of elements of `M` indexed by a finite type `ι` is carried
into `N` by a matrix indexed by `ι` whose determinant divides `z`. -/
theorem ColengthDvd.exists_matrix (h : M.ColengthDvd N z) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Φ : ι → V) (hΦ : ∀ k, Φ k ∈ M) :
    ∃ m : Matrix ι ι O, m.det ∣ z ∧ ∀ i, ∑ k, m i k • Φ k ∈ N := by
  let e := Fintype.equivFin ι
  obtain ⟨m, hdet, hm⟩ := h _ (Φ ∘ e.symm) fun k => hΦ _
  refine ⟨reindex e.symm e.symm m, by rwa [det_reindex_self], fun i => ?_⟩
  rw [← e.symm.sum_comp]
  simpa using hm (e i)

/-- If `M ⊸_z N`, every `x ∈ M` has a multiple `a • x ∈ N` with `a ∣ z` (the case of families
of one element). -/
theorem ColengthDvd.exists_smul_mem (h : M.ColengthDvd N z) {x : V} (hx : x ∈ M) :
    ∃ a, a ∣ z ∧ a • x ∈ N := by
  obtain ⟨m, hdet, hm⟩ := h 1 (fun _ => x) fun _ => hx
  rw [det_fin_one] at hdet
  exact ⟨m 0 0, hdet, by simpa using hm 0⟩

/-- Shrinking `M` and enlarging `N` keeps `M ⊸_z N`. -/
theorem ColengthDvd.mono (h : M.ColengthDvd N z) (hM : M' ≤ M) (hN : N ≤ N') :
    M'.ColengthDvd N' z := fun n Φ hΦ =>
  let ⟨m, hdet, hm⟩ := h n Φ fun k => hM (hΦ k)
  ⟨m, hdet, fun i => hN (hm i)⟩

/-- `M ⊸_z N` and `z ∣ z'` give `M ⊸_{z'} N`. -/
theorem ColengthDvd.trans_dvd (h : M.ColengthDvd N z) (hz : z ∣ z') : M.ColengthDvd N z' :=
  fun n Φ hΦ =>
  let ⟨m, hdet, hm⟩ := h n Φ hΦ
  ⟨m, hdet.trans hz, hm⟩

/-- If `M ≤ N`, then `M ⊸_1 N`, with the identity matrix. -/
theorem ColengthDvd.of_le (h : M ≤ N) : M.ColengthDvd N 1 := fun n Φ hΦ =>
  ⟨1, by rw [det_one], fun i => by simpa [Matrix.one_apply, ite_smul] using h (hΦ i)⟩

/-- If `M ⊸_z N`, then `z • M ≤ N`. -/
theorem ColengthDvd.smul_le (h : M.ColengthDvd N z) : z • M ≤ N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_smul_pointwise_iff_exists x z M).mp hx
  obtain ⟨a, ⟨b, rfl⟩, hay⟩ := h.exists_smul_mem hy
  rw [mul_comm, mul_smul]
  exact N.smul_mem b hay

/-- `M ⊸_z M` for every `z`. -/
@[simp]
theorem colengthDvd_self (M : Submodule O V) (z : O) : M.ColengthDvd M z :=
  (ColengthDvd.of_le le_rfl).trans_dvd (one_dvd z)

/-- Every `M ⊸_0 N` holds, with the zero matrix. -/
@[simp]
theorem colengthDvd_zero (M N : Submodule O V) : M.ColengthDvd N 0 := fun _ _ _ =>
  ⟨0, dvd_zero _, fun _ => by simp⟩

/-- For a unit `z`, `M ⊸_z N` holds exactly when `M ≤ N`. -/
theorem colengthDvd_iff_le_of_isUnit (hz : IsUnit z) : M.ColengthDvd N z ↔ M ≤ N := by
  refine ⟨fun h x hx => ?_, fun h => (ColengthDvd.of_le h).trans_dvd (one_dvd z)⟩
  obtain ⟨a, ha, hax⟩ := h.exists_smul_mem hx
  exact (smul_mem_iff_of_isUnit N (isUnit_of_dvd_unit ha hz)).mp hax

/-- `M ⊸_1 N` holds exactly when `M ≤ N`. -/
@[simp]
theorem colengthDvd_one_iff : M.ColengthDvd N 1 ↔ M ≤ N :=
  colengthDvd_iff_le_of_isUnit isUnit_one

/-- **Transitivity.** `M ⊸_z N` and `N ⊸_a P` give `M ⊸_{z * a} P`, with the product of the
two matrices. -/
theorem ColengthDvd.trans (h₁ : M.ColengthDvd N z) (h₂ : N.ColengthDvd P a) :
    M.ColengthDvd P (z * a) := by
  intro n Φ hΦ
  obtain ⟨m₁, hdet₁, hm₁⟩ := h₁ n Φ hΦ
  obtain ⟨m₂, hdet₂, hm₂⟩ := h₂ n (fun i => ∑ k, m₁ i k • Φ k) hm₁
  refine ⟨m₂ * m₁, by rw [det_mul, mul_comm]; exact mul_dvd_mul hdet₁ hdet₂, fun i => ?_⟩
  have hsum : ∑ k, (m₂ * m₁) i k • Φ k = ∑ j, m₂ i j • ∑ k, m₁ j k • Φ k := by
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  rw [hsum]
  exact hm₂ i

/-- **Pull-back.** Let `f : U → V` be linear and `M', N'` submodules of `U` with `f(M') ⊆ M` and
`x ∈ N'` whenever `x ∈ M'` and `f x ∈ N`. Then `M ⊸_z N` gives `M' ⊸_z N'`. -/
theorem ColengthDvd.comap (h : M.ColengthDvd N z) {M' N' : Submodule O U} (f : U →ₗ[O] V)
    (hM : M'.map f ≤ M) (hN : M' ⊓ N.comap f ≤ N') : M'.ColengthDvd N' z := by
  intro n Φ hΦ
  obtain ⟨m, hdet, hm⟩ := h n (f ∘ Φ) fun k => hM (mem_map_of_mem (hΦ k))
  refine ⟨m, hdet, fun i => hN ⟨sum_mem fun k _ => M'.smul_mem _ (hΦ k), ?_⟩⟩
  simpa [mem_comap, map_sum, map_smul] using hm i

/-- **Push-forward.** Let `f : V → U` be linear and `M', N'` submodules of `U` with
`M' ⊆ f(M) + N'` and `f(N) ⊆ N'`. Then `M ⊸_z N` gives `M' ⊸_z N'`. -/
theorem ColengthDvd.map (h : M.ColengthDvd N z) {M' N' : Submodule O U} (f : V →ₗ[O] U)
    (hM : M' ≤ M.map f ⊔ N') (hN : N.map f ≤ N') : M'.ColengthDvd N' z := by
  intro n Φ hΦ
  choose X hX Y hY hXY using fun k => mem_sup.mp (hM (hΦ k))
  choose W hW hWX using fun k => mem_map.mp (hX k)
  obtain ⟨m, hdet, hm⟩ := h n W hW
  refine ⟨m, hdet, fun i => ?_⟩
  have hsum : ∑ k, m i k • Φ k = f (∑ k, m i k • W k) + ∑ k, m i k • Y k := by
    simp [← hXY, hWX, smul_add, Finset.sum_add_distrib]
  rw [hsum]
  exact N'.add_mem (hN (mem_map_of_mem (hm i))) (sum_mem fun k _ => N'.smul_mem _ (hY k))

/-- Let `f` be an endomorphism of `V` and `Q` a submodule with `f(Q) ⊆ Q`. If `M ⊸_z (f(M) + Q)`
and `M ⊸_{z'} (N + Q)`, then `M ⊸_{z * z'} (f(N) + Q)`. -/
theorem ColengthDvd.map_sup (f : Module.End O V) (hQ : Q.map f ≤ Q)
    (h₁ : M.ColengthDvd (M.map f ⊔ Q) z) (h₂ : M.ColengthDvd (N ⊔ Q) z') :
    M.ColengthDvd (N.map f ⊔ Q) (z * z') :=
  h₁.trans <| h₂.map f (sup_le_sup_left le_sup_right _) <| by
    rw [Submodule.map_sup]
    exact sup_le_sup_left hQ _

/-- Let `f` be an endomorphism of `V` with `f(M) ⊆ M`. If `M ⊸_z (f(M) + a • M)` and
`M ⊸_{z'} (N + a • M)`, then `M ⊸_{z * z'} (f(N) + a • M)`. -/
theorem ColengthDvd.map_sup_smul (f : Module.End O V) (hf : M.map f ≤ M)
    (h₁ : M.ColengthDvd (M.map f ⊔ a • M) z) (h₂ : M.ColengthDvd (N ⊔ a • M) z') :
    M.ColengthDvd (N.map f ⊔ a • M) (z * z') :=
  h₁.map_sup f ((map_pointwise_smul a M f).trans_le (smul_mono_right a hf)) h₂

end Submodule

namespace Module.End

open Submodule

variable {O V : Type*} [CommRing O] [AddCommMonoid V] [Module O V] {M : Submodule O V} {p : O}
  {n : ℕ} {c c' : ℝ} {y : Module.End O V}

/-- An endomorphism `y` of `V` is **onto `M` modulo `p ^ n` up to colength `c`** if `y(M) ⊆ M`
and the colength of `y(M) + p ^ n • M` in `M` divides `p ^ l` for some natural number `l ≤ c`
(`Submodule.ColengthDvd`). -/
def IsOntoUpToColength (y : Module.End O V) (M : Submodule O V) (p : O) (n : ℕ) (c : ℝ) : Prop :=
  M.map y ≤ M ∧ ∃ l : ℕ, (l : ℝ) ≤ c ∧ M.ColengthDvd (M.map y ⊔ p ^ n • M) (p ^ l)

/-- The definition of `Module.End.IsOntoUpToColength`, restated: its body is not exposed outside
this module. -/
theorem isOntoUpToColength_iff : y.IsOntoUpToColength M p n c ↔
    M.map y ≤ M ∧ ∃ l : ℕ, (l : ℝ) ≤ c ∧ M.ColengthDvd (M.map y ⊔ p ^ n • M) (p ^ l) :=
  Iff.rfl

/-- The colength bound may be raised. -/
theorem IsOntoUpToColength.mono (h : y.IsOntoUpToColength M p n c) (hc : c ≤ c') :
    y.IsOntoUpToColength M p n c' :=
  let ⟨hy, l, hl, hM⟩ := h
  ⟨hy, l, hl.trans hc, hM⟩

/-- The identity is onto `M` modulo `p ^ n` up to colength `0`. -/
theorem isOntoUpToColength_one : (1 : Module.End O V).IsOntoUpToColength M p n 0 := by
  have hM : M.map (1 : Module.End O V) = M := by rw [one_eq_id, Submodule.map_id]
  refine ⟨hM.le, 0, by simp, ?_⟩
  rw [hM, pow_zero]
  exact ColengthDvd.of_le le_sup_left

/-- **Products.** If `y₁` and `y₂` are onto `M` modulo `p ^ n` up to colengths `c₁` and `c₂`, then
`y₁ * y₂` is onto `M` modulo `p ^ n` up to colength `c₁ + c₂`. -/
theorem IsOntoUpToColength.mul {y₁ y₂ : Module.End O V} {c₁ c₂ : ℝ}
    (h₁ : y₁.IsOntoUpToColength M p n c₁) (h₂ : y₂.IsOntoUpToColength M p n c₂) :
    (y₁ * y₂).IsOntoUpToColength M p n (c₁ + c₂) := by
  obtain ⟨hy₁, l₁, hl₁, hM₁⟩ := h₁
  obtain ⟨hy₂, l₂, hl₂, hM₂⟩ := h₂
  have hmap : M.map (y₁ * y₂) = (M.map y₂).map y₁ := by rw [mul_eq_comp, map_comp]
  refine ⟨hmap ▸ (map_mono hy₂).trans hy₁, l₁ + l₂, by push_cast; linarith, ?_⟩
  rw [hmap, pow_add]
  exact hM₁.map_sup_smul y₁ hy₁ hM₂

/-- **Finite products.** If each `y i`, for `i` in a list `l`, is onto `M` modulo `p ^ n` up to
colength `c i`, then the product of the `y i` along `l` is onto `M` modulo `p ^ n` up to colength
`∑ c i` along `l`. -/
theorem isOntoUpToColength_list_prod {ι : Type*} (l : List ι) {y : ι → Module.End O V}
    {c : ι → ℝ} (h : ∀ i ∈ l, (y i).IsOntoUpToColength M p n (c i)) :
    (l.map y).prod.IsOntoUpToColength M p n (l.map c).sum := by
  induction l with
  | nil => simpa using isOntoUpToColength_one
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (h i List.mem_cons_self).mul (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- **Powers.** If `y` is onto `M` modulo `p ^ n` up to colength `c`, then `y ^ k` is onto `M`
modulo `p ^ n` up to colength `k * c`. -/
theorem IsOntoUpToColength.pow (h : y.IsOntoUpToColength M p n c) (k : ℕ) :
    (y ^ k).IsOntoUpToColength M p n (k * c) := by
  induction k with
  | zero => simpa using isOntoUpToColength_one
  | succ k ih =>
    rw [pow_succ']
    exact (h.mul ih).mono (by push_cast; linarith)

end Module.End
