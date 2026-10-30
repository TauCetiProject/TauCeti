/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import TauCeti.Algebra.Category.ModuleCat.Tower.Topology

/-!
# The completion of a module along a decreasing sequence of submodules

Let `F 0 ⊇ F 1 ⊇ F 2 ⊇ ⋯` be a decreasing sequence of submodules of a module `M` over a ring `R`.
The quotients `M ⧸ F n`, with the quotient maps `M ⧸ F k → M ⧸ F n` for `n ≤ k` as transitions,
form a tower of `R`-modules (`TauCeti.ModuleTower.quotient`), and its limit
`lim M ⧸ F n` is the completion of `M` along `F`. The quotient maps assemble into the canonical
map `M → lim M ⧸ F n` (`TauCeti.ModuleTower.toLim`), whose kernel is `⋂ₙ F n`; it is injective
exactly when this intersection is zero.

For the inverse limit topology of `TauCeti.Algebra.Category.ModuleCat.Tower.Topology`, the limit is
complete and Hausdorff, the canonical map has dense range, and every series `∑ₖ fₖ` with `fₖ ∈ F k`
converges: its image in `M ⧸ F n` is the finite partial sum `∑_{k < n} fₖ`, because all later terms
lie in `F n`. No norm or other bound on the terms is involved.

The ring `R` need not be commutative, so this applies to a ring completed along a decreasing
sequence of left ideals, viewed as submodules of its left regular module, where the limit is only a
left module.

## Main definitions

* `TauCeti.ModuleTower.quotient`: the tower `n ↦ M ⧸ F n`.
* `TauCeti.ModuleTower.quotientπ`: the quotient maps `M → M ⧸ F n`.
* `TauCeti.ModuleTower.toLim`: the canonical map `M → lim M ⧸ F n`.

## Main results

* `TauCeti.ModuleTower.ker_toLim`: the kernel of the canonical map is `⨅ n, F n`.
* `TauCeti.ModuleTower.denseRange_toLim`: the canonical map has dense range.
* `TauCeti.ModuleTower.summable_toLim`, `TauCeti.ModuleTower.limπ_tsum_toLim`: a series with
  `n`-th term in `F n` converges, with partial sums as its projections.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10, for
  completions along filtrations by submodules.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite Filter Topology

universe v u

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  (F : ℕ → Submodule R M) (hF : Antitone F)

/-- The tower `M ⧸ F 0 ← M ⧸ F 1 ← M ⧸ F 2 ← ⋯` of quotients of `M` by a decreasing sequence of
submodules, with the quotient maps as transitions. Its terms are handled through the quotient maps
`TauCeti.ModuleTower.quotientπ`. -/
def quotient : ModuleTower.{v} R where
  obj n := ModuleCat.of R (M ⧸ F n.unop)
  map f := ModuleCat.ofHom (Submodule.factor (hF (leOfHom f.unop)))
  -- The composites of the quotient maps `Submodule.factor` are quotient maps, by definition.
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

/-- The quotient map from `M` onto the `n`-th term `M ⧸ F n` of the quotient tower. -/
def quotientπ (n : ℕ) : M →ₗ[R] (quotient F hF).obj (op n) :=
  (F n).mkQ

theorem quotientπ_surjective (n : ℕ) : Function.Surjective (quotientπ F hF n) :=
  Submodule.mkQ_surjective _

@[simp]
theorem ker_quotientπ (n : ℕ) : LinearMap.ker (quotientπ F hF n) = F n :=
  Submodule.ker_mkQ _

theorem quotientπ_eq_zero_iff {n : ℕ} {x : M} : quotientπ F hF n x = 0 ↔ x ∈ F n := by
  rw [← LinearMap.mem_ker, ker_quotientπ]

/-- Linear maps out of a term of the quotient tower agree once they agree on `M`. -/
@[ext]
theorem quotient_hom_ext {P : Type*} [AddCommGroup P] [Module R P] {n : ℕ}
    {f g : (quotient F hF).obj (op n) →ₗ[R] P}
    (h : f ∘ₗ quotientπ F hF n = g ∘ₗ quotientπ F hF n) : f = g :=
  Submodule.linearMap_qext _ h

@[simp]
theorem transitionOfLE_quotientπ {n k : ℕ} (h : n ≤ k) (x : M) :
    (quotient F hF).transitionOfLE h (quotientπ F hF k x) = quotientπ F hF n x := by
  -- The transitions of `quotient` are the quotient maps `Submodule.factor`, by definition.
  rw [transitionOfLE_def]
  rfl

@[simp]
theorem transition_quotientπ (n : ℕ) (x : M) :
    (quotient F hF).transition n (quotientπ F hF (n + 1) x) = quotientπ F hF n x := by
  rw [← transitionOfLE_succ, transitionOfLE_quotientπ]

/-- The transitions of the quotient tower are surjective. -/
theorem quotient_transition_surjective (n : ℕ) :
    Function.Surjective ((quotient F hF).transition n) := fun y ↦ by
  obtain ⟨x, rfl⟩ := quotientπ_surjective F hF n y
  exact ⟨quotientπ F hF (n + 1) x, transition_quotientπ F hF n x⟩

/-- The canonical map from `M` to the limit `lim M ⧸ F n` of its quotient tower. -/
def toLim : M →ₗ[R] (quotient F hF).lim :=
  limLift _ (quotientπ F hF) fun n ↦ LinearMap.ext (transition_quotientπ F hF n)

@[simp]
theorem coe_toLim_apply (x : M) (n : ℕ) :
    (toLim F hF x : (quotient F hF).Product) n = quotientπ F hF n x := by
  rw [toLim, coe_limLift_apply]

theorem limπ_toLim (n : ℕ) (x : M) :
    (quotient F hF).limπ n (toLim F hF x) = quotientπ F hF n x := by
  rw [limπ_apply, coe_toLim_apply]

/-- The kernel of the canonical map `M → lim M ⧸ F n` is the intersection of the `F n`. -/
theorem ker_toLim : LinearMap.ker (toLim F hF) = ⨅ n, F n := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_iInf, ← quotientπ_eq_zero_iff F hF, ← limπ_toLim]
  exact ⟨fun h n ↦ by rw [h, map_zero],
    fun h ↦ Subtype.ext <| funext fun n ↦ (limπ_apply _ n _).symm.trans (h n)⟩

/-- The canonical map `M → lim M ⧸ F n` is injective exactly when the `F n` intersect in zero. -/
theorem toLim_injective_iff : Function.Injective (toLim F hF) ↔ ⨅ n, F n = ⊥ := by
  rw [← LinearMap.ker_eq_bot, ker_toLim]

/-- **The image of `M` is dense in its completion**: every compatible family agrees at a given
index with the image of an element of `M`. -/
theorem denseRange_toLim : DenseRange (toLim F hF) := fun x ↦
  (mem_closure_iff_nhds_basis ((quotient F hF).hasBasis_nhds x)).2 fun n _ ↦ by
    obtain ⟨m, hm⟩ := quotientπ_surjective F hF n ((quotient F hF).limπ n x)
    exact ⟨_, ⟨m, rfl⟩, by rw [Set.mem_ofPred_eq, limπ_toLim, hm]⟩

/-- The compatible family of partial sums `∑_{k < n} fₖ` of a sequence with `fₖ ∈ F k`. -/
private def partialSumLim {f : ℕ → M} (hf : ∀ n, f n ∈ F n) : (quotient F hF).lim :=
  ⟨fun n ↦ quotientπ F hF n (∑ k ∈ Finset.range n, f k), (quotient F hF).mem_lim.2 fun n ↦ by
    rw [transition_quotientπ, Finset.sum_range_succ, map_add, (quotientπ_eq_zero_iff F hF).2 (hf n),
      add_zero]⟩

private theorem limπ_partialSumLim {f : ℕ → M} (hf : ∀ n, f n ∈ F n) (n : ℕ) :
    (quotient F hF).limπ n (partialSumLim F hF hf) =
      quotientπ F hF n (∑ k ∈ Finset.range n, f k) := by
  rw [limπ_apply]
  rfl

private theorem hasSum_toLim {f : ℕ → M} (hf : ∀ n, f n ∈ F n) :
    HasSum (fun k ↦ toLim F hF (f k)) (partialSumLim F hF hf) := by
  refine (atTop_basis.tendsto_iff ((quotient F hF).hasBasis_nhds _)).2 fun n _ ↦
    ⟨Finset.range n, trivial, fun s hs ↦ ?_⟩
  -- The terms of index at least `n` lie in `F n`.
  have hrest : ∑ k ∈ s \ Finset.range n, f k ∈ F n := Submodule.sum_mem _ fun k hk ↦
    hF (by simpa using (Finset.mem_sdiff.1 hk).2) (hf k)
  rw [Set.mem_ofPred_eq, map_sum]
  simp only [limπ_toLim]
  rw [← map_sum, ← Finset.sum_sdiff (Set.mem_Ici.1 hs), map_add,
    (quotientπ_eq_zero_iff F hF).2 hrest, zero_add, limπ_partialSumLim]

/-- **Series with terms in `F n` converge.** If `fₖ ∈ F k` for every `k`, the series
`∑ₖ fₖ` converges in the completion `lim M ⧸ F n`. -/
theorem summable_toLim {f : ℕ → M} (hf : ∀ n, f n ∈ F n) :
    Summable fun k ↦ toLim F hF (f k) :=
  (hasSum_toLim F hF hf).summable

/-- The sum of a series `∑ₖ fₖ` with `fₖ ∈ F k` projects to the partial sum `∑_{k < n} fₖ` in
`M ⧸ F n`. -/
theorem limπ_tsum_toLim {f : ℕ → M} (hf : ∀ n, f n ∈ F n) (n : ℕ) :
    (quotient F hF).limπ n (∑' k, toLim F hF (f k)) =
      quotientπ F hF n (∑ k ∈ Finset.range n, f k) := by
  rw [(hasSum_toLim F hF hf).tsum_eq, limπ_partialSumLim]

end TauCeti.ModuleTower
