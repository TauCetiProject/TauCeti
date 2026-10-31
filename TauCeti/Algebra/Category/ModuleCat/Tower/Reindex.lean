/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Exact
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.CategoryTheory.Whiskering

/-!
# Reindexing module towers along cofinal maps

Let `c : ℕ → ℕ` be monotone and cofinal, that is, every `n` is at most some `c m`. Reindexing a
tower `A` along `c` gives the tower `n ↦ A_{c n}` with the composite transition maps; this
covers subsequences, deleting finitely many initial terms, and repeating terms. Reindexing
changes neither `lim` nor `lim¹`.

On products, restriction `x ↦ (x_{c n})ₙ` does not commute with the shift maps
`δ(x)ₙ = xₙ - φₙ(xₙ₊₁)`. Instead `δ' ∘ res = Σ ∘ δ`, where `Σ` sums the images in `A_{c n}` of
the coordinates `c n ≤ k < c (n + 1)`. The pair `(res, Σ)` is a map between the two-term
complexes `δ` and `δ'` whose kernels and cokernels are `lim` and `lim¹`, and it induces both
comparisons. The key step is that a family `x` whose sum `Σ x` is a shift `δ' w` is itself a
shift `δ z` with `res z = w`: the element `z_k` is the image of `w_n` plus the images of the
`x_j` with `k ≤ j < c n`, which is independent of the choice of `n` with `k ≤ c n`. No
surjectivity or Mittag-Leffler hypothesis is needed. Both comparisons are natural in morphisms of
towers, compatible with the projections from `lim`, and compatible with the connecting map of the
six-term sequence of a levelwise short exact sequence of towers. Consequently, a tower whose
transitions are surjective from some index on has vanishing `lim¹`.

## Main declarations

* `TauCeti.ModuleTower.reindex`: the tower `n ↦ A_{c n}`.
* `TauCeti.ModuleTower.reindexRestriction`, `TauCeti.ModuleTower.reindexSum`: the maps of
  products, with `TauCeti.ModuleTower.reindexSum_comp_shift`.
* `TauCeti.ModuleTower.limReindexEquiv`: `lim A ≃ lim (A ∘ c)`, by restriction.
* `TauCeti.ModuleTower.limOneReindexEquiv`: `lim¹ A ≃ lim¹ (A ∘ c)`, induced by `reindexSum`.
* `TauCeti.ModuleTower.limOneReindexEquiv_comp_connecting`: compatibility with the connecting
  map `lim C → lim¹ A`.
* `TauCeti.ModuleTower.subsingleton_limOne_of_surjective_of_le`: towers with eventually
  surjective transitions have vanishing `lim¹`.

## References

* [Stacks: More on Algebra, Lemma 15.88.1, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* C. A. Weibel, *An introduction to homological algebra*, §3.5.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe v u

variable {R : Type u} [Ring R]

section Reindex

variable (F : ModuleTower.{v} R) {c : ℕ → ℕ} (hc : Monotone c)

/-- The reindexing `n ↦ A_{c n}` of a tower along a monotone map `c : ℕ → ℕ`, whose transition
maps are the composite transitions `A_{c (n + 1)} → A_{c n}`. -/
abbrev reindex : ModuleTower.{v} R :=
  hc.functor.op ⋙ F

@[simp]
theorem reindex_transitionOfLE {n m : ℕ} (h : n ≤ m) :
    (F.reindex hc).transitionOfLE h = F.transitionOfLE (hc h) := by
  rw [transitionOfLE_def, transitionOfLE_def]
  rfl

@[simp]
theorem reindex_transition (n : ℕ) :
    (F.reindex hc).transition n = F.transitionOfLE (hc (Nat.le_add_right n 1)) := by
  rw [← transitionOfLE_succ, reindex_transitionOfLE]

/-- Restriction of a product family along `c`. -/
def reindexRestriction : F.Product →ₗ[R] (F.reindex hc).Product :=
  LinearMap.pi fun n ↦ LinearMap.proj (c n)

@[simp]
theorem reindexRestriction_apply (x : F.Product) (n : ℕ) :
    F.reindexRestriction hc x n = x (c n) :=
  (rfl)

/-- The map of products sending `x` to the family whose `n`-th term is the sum of the images in
`A_{c n}` of the coordinates `x_k`, `c n ≤ k < c (n + 1)`. It intertwines the shift maps with
`reindexRestriction` (`reindexSum_comp_shift`). -/
def reindexSum : F.Product →ₗ[R] (F.reindex hc).Product :=
  LinearMap.pi fun n ↦ ∑ i ∈ Finset.range (c (n + 1) - c n),
    F.transitionOfLE (Nat.le_add_right (c n) i) ∘ₗ LinearMap.proj (c n + i)

@[simp]
theorem reindexSum_apply (x : F.Product) (n : ℕ) :
    F.reindexSum hc x n = ∑ i ∈ Finset.range (c (n + 1) - c n),
      F.transitionOfLE (Nat.le_add_right (c n) i) (x (c n + i)) := by
  simp only [reindexSum, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

/-- The image in `A_k` of the `j`-th coordinate of a family, or zero if `j < k`. -/
private def pull (k j : ℕ) : F.Product →ₗ[R] F.obj (op k) :=
  if h : k ≤ j then F.transitionOfLE h ∘ₗ LinearMap.proj j else 0

private theorem pull_of_le {k j : ℕ} (h : k ≤ j) (x : F.Product) :
    F.pull k j x = F.transitionOfLE h (x j) := by
  simp [pull, h]

private theorem pull_self (k : ℕ) (x : F.Product) : F.pull k k x = x k := by
  simp [pull_of_le F le_rfl]

private theorem transitionOfLE_pull {k k' j : ℕ} (h : k ≤ k') (h' : k' ≤ j) (x : F.Product) :
    F.transitionOfLE h (F.pull k' j x) = F.pull k j x := by
  simp [pull_of_le F h', pull_of_le F (h.trans h')]

private theorem transition_pull {k j : ℕ} (h : k + 1 ≤ j) (x : F.Product) :
    F.transition k (F.pull (k + 1) j x) = F.pull k j x := by
  rw [← transitionOfLE_succ, F.transitionOfLE_pull (Nat.le_add_right k 1) h]

private theorem pull_shift {k j : ℕ} (h : k ≤ j) (x : F.Product) :
    F.pull k j (F.shift x) = F.pull k j x - F.pull k (j + 1) x := by
  simp [pull_of_le F h, pull_of_le F (h.trans (Nat.le_add_right j 1))]

private theorem reindexSum_apply_eq_sum_pull (x : F.Product) (n : ℕ) :
    F.reindexSum hc x n = ∑ k ∈ Finset.Ico (c n) (c (n + 1)), F.pull (c n) k x := by
  rw [reindexSum_apply, Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ (F.pull_of_le (Nat.le_add_right _ i) x).symm

/-- Summing over the coordinates `c n ≤ k < c (n + 1)` intertwines the shift maps with
restriction: `Σ ∘ δ = δ' ∘ res`. -/
theorem reindexSum_comp_shift :
    F.reindexSum hc ∘ₗ F.shift = (F.reindex hc).shift ∘ₗ F.reindexRestriction hc := by
  ext x n
  have hn := hc (Nat.le_add_right n 1)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, reindexSum_apply_eq_sum_pull, shift_apply,
    reindex_transition, reindexRestriction_apply, reindexRestriction_apply,
    Finset.sum_congr rfl fun k hk ↦ F.pull_shift (Finset.mem_Ico.1 hk).1 x, Finset.sum_sub_distrib,
    ← F.pull_self (c n) x, ← F.pull_of_le hn x]
  -- Telescoping sum over `c n ≤ k < c (n + 1)`.
  have := Finset.sum_Ico_sub (fun k ↦ F.pull (c n) k x) hn
  rw [Finset.sum_sub_distrib] at this
  rw [← neg_sub (F.pull (c n) (c (n + 1)) x), ← this, neg_sub]

theorem reindexSum_shift (x : F.Product) :
    F.reindexSum hc (F.shift x) = (F.reindex hc).shift (F.reindexRestriction hc x) :=
  LinearMap.congr_fun (F.reindexSum_comp_shift hc) x

/-- Given `x` and `w` with `Σ x = δ' w`, the image of `w_n` in `A_k` plus the images of the `x_j`
with `k ≤ j < c n`. By `lift_eq` it does not depend on `n`. -/
private def lift (x : F.Product) (w : (F.reindex hc).Product) (k n : ℕ) (h : k ≤ c n) :
    F.obj (op k) :=
  F.transitionOfLE h (w n) + ∑ j ∈ Finset.Ico k (c n), F.pull k j x

variable {F hc}

private theorem lift_succ {x : F.Product} {w : (F.reindex hc).Product}
    (hw : F.reindexSum hc x = (F.reindex hc).shift w) {k n : ℕ} (h : k ≤ c n) :
    F.lift hc x w k (n + 1) (h.trans (hc (Nat.le_add_right n 1))) = F.lift hc x w k n h := by
  have hn := hc (Nat.le_add_right n 1)
  have hwn := congr_fun hw n
  rw [reindexSum_apply_eq_sum_pull, shift_apply, reindex_transition] at hwn
  -- The coordinates `c n ≤ j < c (n + 1)` contribute the image of `w n - φ (w (n + 1))`.
  have hsum : ∑ j ∈ Finset.Ico (c n) (c (n + 1)), F.pull k j x =
      F.transitionOfLE h (w n) - F.transitionOfLE (h.trans hn) (w (n + 1)) := by
    rw [Finset.sum_congr rfl fun j hj ↦ (F.transitionOfLE_pull h (Finset.mem_Ico.1 hj).1 x).symm,
      ← map_sum, hwn, map_sub, transitionOfLE_transitionOfLE]
  simp only [lift]
  rw [← Finset.sum_Ico_consecutive _ h hn, hsum]
  abel

private theorem lift_eq {x : F.Product} {w : (F.reindex hc).Product}
    (hw : F.reindexSum hc x = (F.reindex hc).shift w) {k n m : ℕ} (h : k ≤ c n)
    (h' : k ≤ c m) : F.lift hc x w k n h = F.lift hc x w k m h' := by
  -- Both sides agree with the value at `max n m`.
  have key {n m : ℕ} (hnm : n ≤ m) (h : k ≤ c n) :
      F.lift hc x w k m (h.trans (hc hnm)) = F.lift hc x w k n h := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => rw [lift_succ hw (h.trans (hc hnm)), ih]
  rw [← key (le_max_left n m) h, ← key (le_max_right n m) h']

/-- If `Σ x = δ' w`, then `x = δ z` for a family `z` restricting to `w`. -/
private theorem exists_shift_eq_and_reindexRestriction_eq (hc' : ∀ n, ∃ m, n ≤ c m)
    {x : F.Product} {w : (F.reindex hc).Product}
    (hw : F.reindexSum hc x = (F.reindex hc).shift w) :
    ∃ z, F.shift z = x ∧ F.reindexRestriction hc z = w := by
  choose N hN using hc'
  refine ⟨fun k ↦ F.lift hc x w k (N k) (hN k), funext fun k ↦ ?_, funext fun n ↦ ?_⟩
  · -- Compute both terms with a common index `N (k + 1)`.
    have hk : k + 1 ≤ c (N (k + 1)) := hN (k + 1)
    rw [shift_apply, lift_eq hw (hN k) ((Nat.le_add_right k 1).trans hk)]
    simp only [lift, map_add, map_sum, transition_transitionOfLE]
    rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_of_succ_le hk), pull_self,
      Finset.sum_congr rfl fun j hj ↦ F.transition_pull (Finset.mem_Ico.1 hj).1 x]
    abel
  · rw [reindexRestriction_apply, lift_eq hw (hN (c n)) le_rfl]
    simp [lift]

variable (F hc)

/-- Restriction of compatible families along `c`. -/
private def limReindexMap : F.lim →ₗ[R] (F.reindex hc).lim :=
  (F.reindexRestriction hc).restrict fun x hx ↦ by
    rw [lim_eq_ker, LinearMap.mem_ker] at hx ⊢
    rw [← reindexSum_shift, hx, map_zero]

private theorem coe_limReindexMap (x : F.lim) :
    (F.limReindexMap hc x : (F.reindex hc).Product) = F.reindexRestriction hc x :=
  (rfl)

private theorem limReindexMap_bijective (hc' : ∀ n, ∃ m, n ≤ c m) :
    Function.Bijective (F.limReindexMap hc) := by
  refine ⟨fun x y hxy ↦ lim_ext _ fun k ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hc' k
    have := congr_fun (congrArg Subtype.val hxy) n
    rw [coe_limReindexMap, coe_limReindexMap, reindexRestriction_apply,
      reindexRestriction_apply] at this
    rw [limπ_apply, limπ_apply, ← F.transitionOfLE_coe_lim x hn, ← F.transitionOfLE_coe_lim y hn,
      this]
  · have hy : F.reindexSum hc 0 = (F.reindex hc).shift y := by
      rw [map_zero, eq_comm, ← LinearMap.mem_ker, ← lim_eq_ker]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := exists_shift_eq_and_reindexRestriction_eq hc' hy
    exact ⟨⟨z, by rw [lim_eq_ker, LinearMap.mem_ker, hz]⟩,
      Subtype.ext ((F.coe_limReindexMap hc _).trans hzy)⟩

/-- **Reindexing along a cofinal map preserves `lim`.** The map restricts compatible families
along `c`; see `coe_limReindexEquiv_symm_apply` for the inverse. -/
def limReindexEquiv (hc' : ∀ n, ∃ m, n ≤ c m) : F.lim ≃ₗ[R] (F.reindex hc).lim :=
  LinearEquiv.ofBijective (F.limReindexMap hc) (F.limReindexMap_bijective hc hc')

section

variable (hc' : ∀ n, ∃ m, n ≤ c m)

@[simp]
theorem coe_limReindexEquiv_apply (x : F.lim) (n : ℕ) :
    (F.limReindexEquiv hc hc' x : (F.reindex hc).Product) n = (x : F.Product) (c n) :=
  (rfl)

theorem limπ_limReindexEquiv (x : F.lim) (n : ℕ) :
    (F.reindex hc).limπ n (F.limReindexEquiv hc hc' x) = F.limπ (c n) x := by
  rw [limπ_apply, limπ_apply, coe_limReindexEquiv_apply]

/-- The inverse of `limReindexEquiv`: the `k`-th term is the image of the `n`-th term of the
reindexed family, for any `n` with `k ≤ c n`. -/
theorem coe_limReindexEquiv_symm_apply (y : (F.reindex hc).lim) {k n : ℕ} (h : k ≤ c n) :
    ((F.limReindexEquiv hc hc').symm y : F.Product) k =
      F.transitionOfLE h ((y : (F.reindex hc).Product) n) := by
  conv_rhs => rw [← (F.limReindexEquiv hc hc').apply_symm_apply y, coe_limReindexEquiv_apply]
  exact (F.transitionOfLE_coe_lim _ h).symm

end

/-- The image in `A_k` of the `m`-th term of a reindexed family, or zero if `c m < k`. -/
private def pullReindex (k m : ℕ) : (F.reindex hc).Product →ₗ[R] F.obj (op k) :=
  if h : k ≤ c m then F.transitionOfLE h ∘ₗ LinearMap.proj m else 0

private theorem pullReindex_of_le {k m : ℕ} (h : k ≤ c m) (y : (F.reindex hc).Product) :
    F.pullReindex hc k m y = F.transitionOfLE h (y m) := by
  simp [pullReindex, h]

private theorem transitionOfLE_pullReindex {k k' m : ℕ} (h : k ≤ k') (h' : k' ≤ c m)
    (y : (F.reindex hc).Product) :
    F.transitionOfLE h (F.pullReindex hc k' m y) = F.pullReindex hc k m y := by
  simp [pullReindex_of_le F hc h', pullReindex_of_le F hc (h.trans h')]

/-- Every family of the reindexed tower is `Σ x` up to a shift. Put the sum of the images of
the `y_m` with `c m = k` in coordinate `k`; the defect is the shift of the family of partial
sums over the earlier indices `m < n` with `c m = c n`. -/
private theorem exists_reindexSum_eq_add_shift (hc' : ∀ n, ∃ m, n ≤ c m)
    (y : (F.reindex hc).Product) :
    ∃ x w, F.reindexSum hc x = y + (F.reindex hc).shift w := by
  choose N hN using fun k ↦ hc' (k + 1)
  -- Only finitely many indices `m` have `c m = k`, all below `N k`.
  have hlt {k m : ℕ} (h : c m = k) : m < N k := by
    by_contra! hm
    have := hc hm
    have := hN k
    omega
  refine ⟨fun k ↦ ∑ m ∈ (Finset.range (N k)).filter (c · = k), F.pullReindex hc k m y,
    fun n ↦ ∑ m ∈ (Finset.range n).filter (c · = c n), F.pullReindex hc (c n) m y,
    funext fun n ↦ ?_⟩
  have hn := hc (Nat.le_add_right n 1)
  have hself : F.pullReindex hc (c n) n y = y n := by simp [pullReindex_of_le F hc le_rfl]
  -- The indices `m ≤ n` with `c m = c n`.
  have hinsert : ((Finset.range n).filter (c · = c n)).sum (F.pullReindex hc (c n) · y) +
      F.pullReindex hc (c n) n y =
        ∑ m ∈ (Finset.range (n + 1)).filter (c · = c n), F.pullReindex hc (c n) m y := by
    simp only [Finset.range_add_one, Finset.filter_insert, ↓reduceIte]
    rw [Finset.sum_insert (by simp), add_comm]
  rw [reindexSum_apply_eq_sum_pull, Pi.add_apply, shift_apply, reindex_transition, map_sum,
    Finset.sum_congr rfl fun m hm ↦ F.transitionOfLE_pullReindex hc hn
      (Finset.mem_filter.1 hm).2.ge y]
  rcases hn.lt_or_eq with h | h
  · -- No `m ≤ n` has `c m = c (n + 1)`, and only the coordinate `c n` contributes to `Σ`.
    have hempty : (Finset.range (n + 1)).filter (c · = c (n + 1)) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun m hm ↦ by
        have := hc (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))
        omega
    rw [hempty, Finset.sum_empty, sub_zero,
      Finset.sum_eq_single_of_mem (c n) (Finset.left_mem_Ico.2 h), pull_self, ← hself, add_comm,
      hinsert]
    · refine Finset.sum_congr (Finset.ext fun m ↦ ?_) fun _ _ ↦ rfl
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨fun ⟨_, hm⟩ ↦ ⟨?_, hm⟩, fun ⟨_, hm⟩ ↦ ⟨hlt hm, hm⟩⟩
      by_contra! hmn
      have := hc hmn
      omega
    · intro k hk hkn
      obtain ⟨hk₁, hk₂⟩ := Finset.mem_Ico.1 hk
      simp only [pull_of_le F hk₁]
      rw [Finset.sum_eq_zero fun m hm ↦ absurd (Finset.mem_filter.1 hm).2 ?_, map_zero]
      rcases le_or_gt m n with hmn | hmn
      · have := hc hmn
        omega
      · have := hc (Nat.lt_iff_add_one_le.1 hmn)
        omega
  · -- Here `c (n + 1) = c n`: the sum `Σ` is empty and the shift cancels `y n`.
    have hfilter : (Finset.range (n + 1)).filter (c · = c (n + 1)) =
        (Finset.range (n + 1)).filter (c · = c n) :=
      Finset.filter_congr fun m _ ↦ by rw [h]
    rw [Finset.Ico_eq_empty_of_le h.ge, Finset.sum_empty, hfilter, ← hinsert, hself]
    -- The two sides live in definitionally equal types; `abel` runs in `A_{c n}`.
    have key (a b : F.obj (op (c n))) : (0 : F.obj (op (c n))) = a + (b - (b + a)) := by abel
    exact key _ _

/-- The map `lim¹ A → lim¹ (A ∘ c)` induced by `reindexSum`. -/
private def limOneReindexMap : F.limOne →ₗ[R] (F.reindex hc).limOne :=
  (LinearMap.range F.shift).mapQ (LinearMap.range (F.reindex hc).shift) (F.reindexSum hc) <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨F.reindexRestriction hc x, (F.reindexSum_shift hc x).symm⟩

private theorem limOneReindexMap_mk (x : F.Product) :
    F.limOneReindexMap hc (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.reindexSum hc x) :=
  Submodule.mapQ_apply _ _ _ x

private theorem limOneReindexMap_bijective (hc' : ∀ n, ∃ m, n ≤ c m) :
    Function.Bijective (F.limOneReindexMap hc) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · induction x using Submodule.Quotient.induction_on with | _ x
    rw [limOneReindexMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨w, hw⟩ := hx
    obtain ⟨z, hz, -⟩ := exists_shift_eq_and_reindexRestriction_eq hc' hw.symm
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, hz⟩
  · induction y using Submodule.Quotient.induction_on with | _ y
    obtain ⟨x, w, hxw⟩ := F.exists_reindexSum_eq_add_shift hc hc' y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [limOneReindexMap_mk, hxw, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ w), add_zero]

/-- **Reindexing along a cofinal map preserves `lim¹`.** The map is induced by `reindexSum`;
no condition on the transition maps is needed. -/
def limOneReindexEquiv (hc' : ∀ n, ∃ m, n ≤ c m) : F.limOne ≃ₗ[R] (F.reindex hc).limOne :=
  LinearEquiv.ofBijective (F.limOneReindexMap hc) (F.limOneReindexMap_bijective hc hc')

@[simp]
theorem limOneReindexEquiv_mk (hc' : ∀ n, ∃ m, n ≤ c m) (x : F.Product) :
    F.limOneReindexEquiv hc hc' (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.reindexSum hc x) := by
  rw [limOneReindexEquiv, LinearEquiv.ofBijective_apply, limOneReindexMap_mk]

end Reindex

section Naturality

variable {F G H : ModuleTower.{v} R} {c : ℕ → ℕ} (hc : Monotone c) (hc' : ∀ n, ∃ m, n ≤ c m)

/-- Restriction along `c` commutes with the product map of a morphism of towers. -/
theorem reindexRestriction_natural_apply (f : F ⟶ G) (x : F.Product) :
    G.reindexRestriction hc (productMap f x) =
      productMap (Functor.whiskerLeft hc.functor.op f) (F.reindexRestriction hc x) := by
  funext n
  simp [productMap_apply]

/-- `reindexSum` commutes with the product map of a morphism of towers. -/
theorem reindexSum_natural_apply (f : F ⟶ G) (x : F.Product) :
    G.reindexSum hc (productMap f x) =
      productMap (Functor.whiskerLeft hc.functor.op f) (F.reindexSum hc x) := by
  funext n
  simp only [reindexSum_apply, productMap_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (LinearMap.congr_fun (app_comp_transitionOfLE f _) _).symm

/-- The comparison `limReindexEquiv` is natural in morphisms of towers. -/
theorem limReindexEquiv_naturality (f : F ⟶ G) :
    (G.limReindexEquiv hc hc').toLinearMap ∘ₗ limMap f =
      limMap (Functor.whiskerLeft hc.functor.op f) ∘ₗ (F.limReindexEquiv hc hc').toLinearMap :=
  LinearMap.ext fun _ ↦ Subtype.ext <| funext fun _ ↦ by simp

/-- The comparison `limOneReindexEquiv` is natural in morphisms of towers. -/
theorem limOneReindexEquiv_naturality (f : F ⟶ G) :
    (G.limOneReindexEquiv hc hc').toLinearMap ∘ₗ limOneMap f =
      limOneMap (Functor.whiskerLeft hc.functor.op f) ∘ₗ
        (F.limOneReindexEquiv hc hc').toLinearMap := by
  apply Submodule.linearMap_qext
  ext x
  simp [reindexSum_natural_apply]

variable {f : F ⟶ G} {g : G ⟶ H}
  (hf : ∀ n, Function.Injective (f.app (op n)).hom)
  (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
  (hg : ∀ n, Function.Surjective (g.app (op n)).hom)

/-- **Reindexing commutes with the connecting map.** For a levelwise short exact sequence of
towers `0 → A → B → C → 0`, the comparisons `lim C ≃ lim (C ∘ c)` and `lim¹ A ≃ lim¹ (A ∘ c)`
intertwine the connecting maps of `0 → A → B → C → 0` and of its reindexing along `c`. -/
theorem limOneReindexEquiv_comp_connecting :
    (F.limOneReindexEquiv hc hc').toLinearMap ∘ₗ connecting f g hf hfg hg =
      connecting (Functor.whiskerLeft hc.functor.op f) (Functor.whiskerLeft hc.functor.op g)
          (fun n ↦ hf (c n)) (fun n ↦ hfg (c n)) (fun n ↦ hg (c n)) ∘ₗ
        (H.limReindexEquiv hc hc').toLinearMap := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨b, hb⟩ := productMap_surjective hg (z : H.Product)
  obtain ⟨a, ha⟩ := (exact_productMap hfg (G.shift b)).1 <| by
    rw [← shift_natural_apply, hb]
    exact LinearMap.mem_ker.1 (H.lim_eq_ker ▸ z.2)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, connecting_apply f g hf hfg hg z b hb a ha,
    LinearEquiv.coe_coe, limOneReindexEquiv_mk]
  -- The restriction of `b` and the sum of `a` compute the reindexed connecting map.
  refine (connecting_apply _ _ _ _ _ _ (G.reindexRestriction hc b) ?_ (F.reindexSum hc a) ?_).symm
  · rw [← reindexRestriction_natural_apply, hb]
    rfl
  · rw [← reindexSum_natural_apply, ha, reindexSum_shift]

end Naturality

/-- **Eventually surjective towers have vanishing `lim¹`.** If the transition maps `Aₙ₊₁ → Aₙ`
are surjective for all `n ≥ k`, then `lim¹ A` vanishes. -/
theorem subsingleton_limOne_of_surjective_of_le (F : ModuleTower.{v} R) (k : ℕ)
    (h : ∀ n, k ≤ n → Function.Surjective (F.transition n)) : Subsingleton F.limOne := by
  have hc : Monotone (k + ·) := fun _ _ h ↦ Nat.add_le_add_left h k
  refine (F.limOneReindexEquiv hc fun n ↦ ⟨n, Nat.le_add_left n k⟩).toEquiv.subsingleton_congr.2 <|
    (F.reindex hc).subsingleton_limOne_of_surjective fun n ↦ ?_
  have := h (k + n) (Nat.le_add_right k n)
  rw [← transitionOfLE_succ] at this
  rw [reindex_transition]
  exact this

end TauCeti.ModuleTower
