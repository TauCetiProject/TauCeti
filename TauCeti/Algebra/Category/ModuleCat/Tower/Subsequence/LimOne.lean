/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Exact
public import TauCeti.Algebra.Category.ModuleCat.Tower.Subsequence
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The first derived limit of a cofinal subsequence

Let `φ : ℕ →o ℕ` be cofinal, that is, every `n` is at most some `φ m`. Sampling a tower `A` along
`φ` gives the tower `n ↦ A_{φ n}` with the composite transition maps; this covers subsequences,
deleting finitely many initial terms, and repeating terms. By `ModuleTower.limSubsequenceEquiv`
sampling does not change `lim`; this file shows that it does not change `lim¹` either.

On products, restriction `x ↦ (x_{φ n})ₙ` does not commute with the shift maps
`δ(x)ₙ = xₙ - tₙ(xₙ₊₁)`, where `tₙ` is the transition map. Instead `δ' ∘ res = Σ ∘ δ`, where `Σ`
sums the images in `A_{φ n}` of the coordinates `φ n ≤ k < φ (n + 1)`. The pair `(res, Σ)` is a
map between the two-term complexes `δ` and `δ'` whose kernels and cokernels are `lim` and `lim¹`,
and it induces the `lim¹` comparison. The key step is that a family `x` whose sum `Σ x` is a
shift `δ' w` is itself a shift `δ z` with `res z = w`: the element `z_k` is the image of `w_n`
plus the images of the `x_j` with `k ≤ j < φ n`, which is independent of the choice of `n` with
`k ≤ φ n`. No surjectivity or Mittag-Leffler hypothesis is needed. The comparison is natural in
morphisms of towers and, together with `ModuleTower.limSubsequenceEquiv`, compatible with the
connecting map of the six-term sequence of a levelwise short exact sequence of towers.
Consequently, a tower whose transitions are surjective from some index on has vanishing `lim¹`.

## Main declarations

* `TauCeti.ModuleTower.subsequenceSum`: the map of products, intertwining the shift maps with
  `TauCeti.ModuleTower.subsequenceRestriction` (`TauCeti.ModuleTower.subsequenceSum_comp_shift`).
* `TauCeti.ModuleTower.limOneSubsequenceEquiv`: `lim¹ A ≃ lim¹ (A ∘ φ)`, induced by
  `subsequenceSum`.
* `TauCeti.ModuleTower.limOneSubsequenceEquiv_comp_connecting`: compatibility with the
  connecting map `lim C → lim¹ A`.
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

section Subsequence

variable (F : ModuleTower.{v} R) (φ : ℕ →o ℕ)

/-- The map of products sending `x` to the family whose `n`-th term is the sum of the images in
`A_{φ n}` of the coordinates `x_k`, `φ n ≤ k < φ (n + 1)`. It intertwines the shift maps with
`subsequenceRestriction` (`subsequenceSum_comp_shift`). -/
def subsequenceSum : F.Product →ₗ[R] (F.subsequence φ).Product :=
  LinearMap.pi fun n ↦ ∑ i ∈ Finset.range (φ (n + 1) - φ n),
    F.transitionOfLE (Nat.le_add_right (φ n) i) ∘ₗ LinearMap.proj (φ n + i)

@[simp]
theorem subsequenceSum_apply (x : F.Product) (n : ℕ) :
    F.subsequenceSum φ x n = ∑ i ∈ Finset.range (φ (n + 1) - φ n),
      F.transitionOfLE (Nat.le_add_right (φ n) i) (x (φ n + i)) := by
  simp only [subsequenceSum, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
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

private theorem subsequenceSum_apply_eq_sum_pull (x : F.Product) (n : ℕ) :
    F.subsequenceSum φ x n = ∑ k ∈ Finset.Ico (φ n) (φ (n + 1)), F.pull (φ n) k x := by
  rw [subsequenceSum_apply, Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ (F.pull_of_le (Nat.le_add_right _ i) x).symm

/-- Summing over the coordinates `φ n ≤ k < φ (n + 1)` intertwines the shift maps with
restriction: `Σ ∘ δ = δ' ∘ res`. -/
theorem subsequenceSum_comp_shift :
    F.subsequenceSum φ ∘ₗ F.shift = (F.subsequence φ).shift ∘ₗ F.subsequenceRestriction φ := by
  ext x n
  have hn := φ.monotone (Nat.le_add_right n 1)
  -- Telescoping sum over `φ n ≤ k < φ (n + 1)`.
  have := Finset.sum_Ico_sub (fun k ↦ F.pull (φ n) k x) hn
  rw [F.pull_self, F.pull_of_le hn] at this
  rw [LinearMap.comp_apply, LinearMap.comp_apply, subsequenceSum_apply_eq_sum_pull, shift_apply,
    subsequence_transition, subsequenceRestriction_apply, subsequenceRestriction_apply,
    Finset.sum_congr rfl fun k hk ↦ F.pull_shift (Finset.mem_Ico.1 hk).1 x]
  simp only [Finset.sum_sub_distrib] at this ⊢
  rw [← neg_sub, this, neg_sub]

theorem subsequenceSum_shift (x : F.Product) :
    F.subsequenceSum φ (F.shift x) = (F.subsequence φ).shift (F.subsequenceRestriction φ x) :=
  LinearMap.congr_fun (F.subsequenceSum_comp_shift φ) x

/-- Given `x` and `w` with `Σ x = δ' w`, the image of `w_n` in `A_k` plus the images of the `x_j`
with `k ≤ j < φ n`. By `lift_eq` it does not depend on `n`. -/
private def lift (x : F.Product) (w : (F.subsequence φ).Product) (k n : ℕ) (h : k ≤ φ n) :
    F.obj (op k) :=
  F.transitionOfLE h (w n) + ∑ j ∈ Finset.Ico k (φ n), F.pull k j x

variable {F φ}

private theorem lift_succ {x : F.Product} {w : (F.subsequence φ).Product}
    (hw : F.subsequenceSum φ x = (F.subsequence φ).shift w) {k n : ℕ} (h : k ≤ φ n) :
    F.lift φ x w k (n + 1) (h.trans (φ.monotone (Nat.le_add_right n 1))) = F.lift φ x w k n h := by
  have hn := φ.monotone (Nat.le_add_right n 1)
  have hwn := congr_fun hw n
  rw [subsequenceSum_apply_eq_sum_pull, shift_apply, subsequence_transition] at hwn
  -- The coordinates `φ n ≤ j < φ (n + 1)` contribute the image of `w n - tₙ (w (n + 1))`.
  have hsum : ∑ j ∈ Finset.Ico (φ n) (φ (n + 1)), F.pull k j x =
      F.transitionOfLE h (w n) - F.transitionOfLE (h.trans hn) (w (n + 1)) := by
    rw [Finset.sum_congr rfl fun j hj ↦ (F.transitionOfLE_pull h (Finset.mem_Ico.1 hj).1 x).symm,
      ← map_sum, hwn, map_sub, transitionOfLE_transitionOfLE]
  simp only [lift]
  rw [← Finset.sum_Ico_consecutive _ h hn, hsum]
  abel

private theorem lift_eq {x : F.Product} {w : (F.subsequence φ).Product}
    (hw : F.subsequenceSum φ x = (F.subsequence φ).shift w) {k n m : ℕ} (h : k ≤ φ n)
    (h' : k ≤ φ m) : F.lift φ x w k n h = F.lift φ x w k m h' := by
  -- Both sides agree with the value at `max n m`.
  have key {n m : ℕ} (hnm : n ≤ m) (h : k ≤ φ n) :
      F.lift φ x w k m (h.trans (φ.monotone hnm)) = F.lift φ x w k n h := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => rw [lift_succ hw (h.trans (φ.monotone hnm)), ih]
  rw [← key (le_max_left n m) h, ← key (le_max_right n m) h']

/-- If `Σ x = δ' w`, then `x = δ z` for a family `z` restricting to `w`. -/
private theorem exists_shift_eq_and_subsequenceRestriction_eq (hφ : ∀ n, ∃ m, n ≤ φ m)
    {x : F.Product} {w : (F.subsequence φ).Product}
    (hw : F.subsequenceSum φ x = (F.subsequence φ).shift w) :
    ∃ z, F.shift z = x ∧ F.subsequenceRestriction φ z = w := by
  choose N hN using hφ
  refine ⟨fun k ↦ F.lift φ x w k (N k) (hN k), funext fun k ↦ ?_, funext fun n ↦ ?_⟩
  · -- Compute both terms with a common index `N (k + 1)`.
    have hk : k + 1 ≤ φ (N (k + 1)) := hN (k + 1)
    rw [shift_apply, lift_eq hw (hN k) ((Nat.le_add_right k 1).trans hk)]
    simp only [lift, map_add, map_sum, transition_transitionOfLE]
    rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_of_succ_le hk), pull_self,
      Finset.sum_congr rfl fun j hj ↦ F.transition_pull (Finset.mem_Ico.1 hj).1 x]
    abel
  · rw [subsequenceRestriction_apply, lift_eq hw (hN (φ n)) le_rfl]
    simp [lift]

variable (F φ)

/-- The image in `A_k` of the `m`-th term of a sampled family, or zero if `φ m < k`. -/
private def pullSubsequence (k m : ℕ) : (F.subsequence φ).Product →ₗ[R] F.obj (op k) :=
  if h : k ≤ φ m then F.transitionOfLE h ∘ₗ LinearMap.proj m else 0

private theorem pullSubsequence_of_le {k m : ℕ} (h : k ≤ φ m) (y : (F.subsequence φ).Product) :
    F.pullSubsequence φ k m y = F.transitionOfLE h (y m) := by
  simp [pullSubsequence, h]

private theorem transitionOfLE_pullSubsequence {k k' m : ℕ} (h : k ≤ k') (h' : k' ≤ φ m)
    (y : (F.subsequence φ).Product) :
    F.transitionOfLE h (F.pullSubsequence φ k' m y) = F.pullSubsequence φ k m y := by
  simp [pullSubsequence_of_le F φ h', pullSubsequence_of_le F φ (h.trans h')]

/-- Every family of the sampled tower is `Σ x` up to a shift. Put the sum of the images of
the `y_m` with `φ m = k` in coordinate `k`; the defect is the shift of the family of partial
sums over the earlier indices `m < n` with `φ m = φ n`. -/
private theorem exists_subsequenceSum_eq_add_shift (hφ : ∀ n, ∃ m, n ≤ φ m)
    (y : (F.subsequence φ).Product) :
    ∃ x w, F.subsequenceSum φ x = y + (F.subsequence φ).shift w := by
  choose N hN using fun k ↦ hφ (k + 1)
  -- Only finitely many indices `m` have `φ m = k`, all below `N k`.
  have hlt {k m : ℕ} (h : φ m = k) : m < N k := by
    by_contra! hm
    have := φ.monotone hm
    have := hN k
    omega
  refine ⟨fun k ↦ ∑ m ∈ (Finset.range (N k)).filter (φ · = k), F.pullSubsequence φ k m y,
    fun n ↦ ∑ m ∈ (Finset.range n).filter (φ · = φ n), F.pullSubsequence φ (φ n) m y,
    funext fun n ↦ ?_⟩
  have hn := φ.monotone (Nat.le_add_right n 1)
  have hself : F.pullSubsequence φ (φ n) n y = y n := by simp [pullSubsequence_of_le F φ le_rfl]
  -- The indices `m ≤ n` with `φ m = φ n`.
  have hinsert : ((Finset.range n).filter (φ · = φ n)).sum (F.pullSubsequence φ (φ n) · y) +
      F.pullSubsequence φ (φ n) n y =
        ∑ m ∈ (Finset.range (n + 1)).filter (φ · = φ n), F.pullSubsequence φ (φ n) m y := by
    simp only [Finset.range_add_one, Finset.filter_insert, ↓reduceIte]
    rw [Finset.sum_insert (by simp), add_comm]
  rw [subsequenceSum_apply_eq_sum_pull, Pi.add_apply, shift_apply, subsequence_transition, map_sum,
    Finset.sum_congr rfl fun m hm ↦ F.transitionOfLE_pullSubsequence φ hn
      (Finset.mem_filter.1 hm).2.ge y]
  rcases hn.lt_or_eq with h | h
  · -- No `m ≤ n` has `φ m = φ (n + 1)`, and only the coordinate `φ n` contributes to `Σ`.
    have hempty : (Finset.range (n + 1)).filter (φ · = φ (n + 1)) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun m hm ↦ by
        have := φ.monotone (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))
        omega
    rw [hempty, Finset.sum_empty, sub_zero,
      Finset.sum_eq_single_of_mem (φ n) (Finset.left_mem_Ico.2 h), pull_self, ← hself, add_comm,
      hinsert]
    · refine Finset.sum_congr (Finset.ext fun m ↦ ?_) fun _ _ ↦ rfl
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨fun ⟨_, hm⟩ ↦ ⟨?_, hm⟩, fun ⟨_, hm⟩ ↦ ⟨hlt hm, hm⟩⟩
      by_contra! hmn
      have := φ.monotone hmn
      omega
    · intro k hk hkn
      obtain ⟨hk₁, hk₂⟩ := Finset.mem_Ico.1 hk
      simp only [pull_of_le F hk₁]
      rw [Finset.sum_eq_zero fun m hm ↦ absurd (Finset.mem_filter.1 hm).2 ?_, map_zero]
      rcases le_or_gt m n with hmn | hmn
      · have := φ.monotone hmn
        omega
      · have := φ.monotone (Nat.lt_iff_add_one_le.1 hmn)
        omega
  · -- Here `φ (n + 1) = φ n`: the sum `Σ` is empty and the shift cancels `y n`.
    have hfilter : (Finset.range (n + 1)).filter (φ · = φ (n + 1)) =
        (Finset.range (n + 1)).filter (φ · = φ n) :=
      Finset.filter_congr fun m _ ↦ by rw [h]
    rw [Finset.Ico_eq_empty_of_le h.ge, Finset.sum_empty, hfilter, ← hinsert, hself]
    -- The two sides live in definitionally equal types; `abel` runs in `A_{φ n}`.
    have key (a b : F.obj (op (φ n))) : (0 : F.obj (op (φ n))) = a + (b - (b + a)) := by abel
    exact key _ _

/-- The map `lim¹ A → lim¹ (A ∘ φ)` induced by `subsequenceSum`. -/
private def limOneSubsequenceMap : F.limOne →ₗ[R] (F.subsequence φ).limOne :=
  (LinearMap.range F.shift).mapQ (LinearMap.range (F.subsequence φ).shift)
    (F.subsequenceSum φ) <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨F.subsequenceRestriction φ x, (F.subsequenceSum_shift φ x).symm⟩

private theorem limOneSubsequenceMap_mk (x : F.Product) :
    F.limOneSubsequenceMap φ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.subsequenceSum φ x) :=
  Submodule.mapQ_apply _ _ _ x

private theorem limOneSubsequenceMap_bijective (hφ : ∀ n, ∃ m, n ≤ φ m) :
    Function.Bijective (F.limOneSubsequenceMap φ) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · induction x using Submodule.Quotient.induction_on with | _ x
    rw [limOneSubsequenceMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨w, hw⟩ := hx
    obtain ⟨z, hz, -⟩ := exists_shift_eq_and_subsequenceRestriction_eq hφ hw.symm
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, hz⟩
  · induction y using Submodule.Quotient.induction_on with | _ y
    obtain ⟨x, w, hxw⟩ := F.exists_subsequenceSum_eq_add_shift φ hφ y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [limOneSubsequenceMap_mk, hxw, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ w), add_zero]

/-- **Cofinal subsequences preserve `lim¹`.** The map is induced by `subsequenceSum`;
no condition on the transition maps is needed. -/
def limOneSubsequenceEquiv (hφ : ∀ n, ∃ m, n ≤ φ m) : F.limOne ≃ₗ[R] (F.subsequence φ).limOne :=
  LinearEquiv.ofBijective (F.limOneSubsequenceMap φ) (F.limOneSubsequenceMap_bijective φ hφ)

@[simp]
theorem limOneSubsequenceEquiv_mk (hφ : ∀ n, ∃ m, n ≤ φ m) (x : F.Product) :
    F.limOneSubsequenceEquiv φ hφ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.subsequenceSum φ x) := by
  rw [limOneSubsequenceEquiv, LinearEquiv.ofBijective_apply, limOneSubsequenceMap_mk]

end Subsequence

section Naturality

variable {F G H : ModuleTower.{v} R} (φ : ℕ →o ℕ) (hφ : ∀ n, ∃ m, n ≤ φ m)

/-- `subsequenceSum` commutes with the product map of a morphism of towers. -/
theorem subsequenceSum_natural_apply (f : F ⟶ G) (x : F.Product) :
    G.subsequenceSum φ (productMap f x) =
      productMap (Functor.whiskerLeft φ.monotone.functor.op f) (F.subsequenceSum φ x) := by
  funext n
  simp only [subsequenceSum_apply, productMap_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (LinearMap.congr_fun (app_comp_transitionOfLE f _) _).symm

/-- The comparison `limOneSubsequenceEquiv` is natural in morphisms of towers. -/
theorem limOneSubsequenceEquiv_naturality (f : F ⟶ G) :
    (G.limOneSubsequenceEquiv φ hφ).toLinearMap ∘ₗ limOneMap f =
      limOneMap (Functor.whiskerLeft φ.monotone.functor.op f) ∘ₗ
        (F.limOneSubsequenceEquiv φ hφ).toLinearMap := by
  apply Submodule.linearMap_qext
  ext x
  simp [subsequenceSum_natural_apply]

variable {f : F ⟶ G} {g : G ⟶ H}
  (hf : ∀ n, Function.Injective (f.app (op n)).hom)
  (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
  (hg : ∀ n, Function.Surjective (g.app (op n)).hom)

/-- **Cofinal restriction commutes with the connecting map.** For a levelwise short exact
sequence of towers `0 → A → B → C → 0`, the comparisons `lim C ≃ lim (C ∘ φ)`
(`limSubsequenceEquiv`) and `lim¹ A ≃ lim¹ (A ∘ φ)` intertwine the connecting maps of
`0 → A → B → C → 0` and of its restriction along `φ`. -/
theorem limOneSubsequenceEquiv_comp_connecting :
    (F.limOneSubsequenceEquiv φ hφ).toLinearMap ∘ₗ connecting f g hf hfg hg =
      connecting (Functor.whiskerLeft φ.monotone.functor.op f)
          (Functor.whiskerLeft φ.monotone.functor.op g)
          (fun n ↦ hf (φ n)) (fun n ↦ hfg (φ n)) (fun n ↦ hg (φ n)) ∘ₗ
        (H.limSubsequenceEquiv φ hφ).toLinearMap := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨b, hb⟩ := productMap_surjective hg (z : H.Product)
  obtain ⟨a, ha⟩ := (exact_productMap hfg (G.shift b)).1 <| by
    rw [← shift_natural_apply, hb]
    exact LinearMap.mem_ker.1 (H.lim_eq_ker ▸ z.2)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, connecting_apply f g hf hfg hg z b hb a ha,
    LinearEquiv.coe_coe, limOneSubsequenceEquiv_mk]
  -- The restriction of `b` and the sum of `a` compute the sampled connecting map.
  refine (connecting_apply _ _ _ _ _ _ (G.subsequenceRestriction φ b) ?_
    (F.subsequenceSum φ a) ?_).symm
  · rw [← subsequenceRestriction_natural_apply, hb]
    exact funext fun n ↦ (subsequenceRestriction_apply H φ _ n).trans
      (H.coe_limSubsequenceEquiv_apply φ hφ z n).symm
  · rw [← subsequenceSum_natural_apply, ha, subsequenceSum_shift]

end Naturality

/-- **Eventually surjective towers have vanishing `lim¹`.** If the transition maps `Aₙ₊₁ → Aₙ`
are surjective for all `n ≥ k`, then `lim¹ A` vanishes. -/
theorem subsingleton_limOne_of_surjective_of_le (F : ModuleTower.{v} R) (k : ℕ)
    (h : ∀ n, k ≤ n → Function.Surjective (F.transition n)) : Subsingleton F.limOne := by
  let φ : ℕ →o ℕ := ⟨(k + ·), fun _ _ h ↦ Nat.add_le_add_left h k⟩
  refine (F.limOneSubsequenceEquiv φ fun n ↦ ⟨n, Nat.le_add_left n k⟩).toEquiv
    |>.subsingleton_congr.2 <|
    (F.subsequence φ).subsingleton_limOne_of_surjective fun n ↦ ?_
  have := h (k + n) (Nat.le_add_right k n)
  rw [← transitionOfLE_succ] at this
  rw [subsequence_transition]
  exact this

end TauCeti.ModuleTower
