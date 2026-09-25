/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.BigOperators.Sum.Slack
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ZetaSumPartition
public import TauCeti.NumberTheory.NumberField.DirichletDensityBounds
import Mathlib.Algebra.BigOperators.Field

/-!
# The Boolean calculus of Dirichlet density

For a number field `K`, Mathlib's `NumberField.Set.HasDirichletDensity S δ` says that

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s → δ` as `s → 1⁺`.

This file proves the elementary calculus of this predicate: uniqueness, the value `1` on all
primes, monotonicity, additivity on finite disjoint unions, complements, and two squeezes. The first
squeezes a set between two sets of the same density. The second is the finite-partition squeeze:
given a finite pairwise disjoint family whose union has `δ` as an *upper* density bound, lower
bounds on every member that already sum to `δ` leave no room, so each member's density is exactly
its bound. It also shows that one-sided density bounds move along inclusions of sets, which is
what makes the first squeeze work; the second rests instead on splitting the union's ratio exactly
and spending the summed lower bounds against it.

All of these are statements about the ratio for `s` close to `1` from the right, and on that
side both inputs they need are available: for `1 < s` each partial sum is a genuine sum rather
than the `tsum` junk value (`TauCeti.summable_absNorm_rpow_subtype_of_one_lt`), and the all-prime
denominator is positive (`NumberField.Set.primeIdealZetaSum_univ_pos_of_one_lt`). In particular
nothing here uses the divergence of the all-prime sum at `s = 1`. That divergence is what makes a
finite set of primes have density zero; the finite-error statements that use it are in
`TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible`.

## Main results

* `NumberField.Set.hasDirichletDensity_univ`: all primes have Dirichlet density `1`.
* `NumberField.Set.HasDirichletDensity.mono`: inclusion of prime sets orders their densities.
* `NumberField.Set.HasDirichletDensity.union` and
  `NumberField.Set.hasDirichletDensity_biUnion_finset`: Dirichlet density is additive on finite
  disjoint unions.
* `NumberField.Set.HasDirichletDensity.compl`: the complement of a set of density `δ` has
  density `1 - δ`.
* `NumberField.Set.IsLowerDirichletDensityBound.mono_set` and
  `NumberField.Set.IsUpperDirichletDensityBound.mono_set`: lower bounds pass to supersets and
  upper bounds to subsets.
* `NumberField.Set.hasDirichletDensity_of_subset_of_subset`: a set squeezed between two sets of
  density `δ` has density `δ`.
* `NumberField.Set.isUpperDirichletDensityBound_of_forall_isLowerDirichletDensityBound`: in a
  finite disjoint family whose union has `δ` as an upper density bound, lower bounds summing to
  `δ` bound each member from above as well.
* `NumberField.Set.hasDirichletDensity_of_squeeze`: hence each such
  member has density exactly its lower bound.

## References

* The declarations and proof structure are adapted from the `HasNaturalDensity` calculus in
  `TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity`.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* The finite-partition squeeze is adapted from C. Birkbeck,
  [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/Abelian.lean`, whose
  `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` and `ratioSum_frobeniusFibres_tendsto_one`
  are the corresponding steps: the member-sum identity divided by the all-prime sum, and the
  `#s * ε` budget that turns the other members' lower bounds into this one's upper bound.
-/

public section

namespace NumberField.Set

open Filter IsDedekindDomain NumberField TauCeti
open scoped NumberField Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T U : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}

/-- A set of prime ideals has at most one Dirichlet density. -/
theorem HasDirichletDensity.unique (hδ : HasDirichletDensity S δ)
    (hε : HasDirichletDensity S ε) : δ = ε :=
  tendsto_nhds_unique (hasDirichletDensity_iff.1 hδ) (hasDirichletDensity_iff.1 hε)

/-- The set of all prime ideals has Dirichlet density one. -/
@[simp]
theorem hasDirichletDensity_univ :
    HasDirichletDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  refine hasDirichletDensity_iff.2 <| tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact (div_self (primeIdealZetaSum_univ_pos_of_one_lt hs).ne').symm

/-- The Dirichlet density of the set of all prime ideals is one. -/
@[simp]
theorem dirichletDensity_univ :
    dirichletDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = 1 :=
  hasDirichletDensity_univ.dirichletDensity_eq

/-- Inclusion of prime sets orders their Dirichlet densities, when both densities exist. -/
theorem HasDirichletDensity.mono (hST : S ⊆ T) (hS : HasDirichletDensity S δ)
    (hT : HasDirichletDensity T ε) : δ ≤ ε := by
  refine le_of_tendsto_of_tendsto (hasDirichletDensity_iff.1 hS) (hasDirichletDensity_iff.1 hT) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact div_le_div_of_nonneg_right (primeIdealZetaSum_mono_set_of_one_lt hST hs)
    (primeIdealZetaSum_nonneg _ s)

/-- Dirichlet density is additive on a finite family of pairwise disjoint prime sets. -/
theorem hasDirichletDensity_biUnion_finset {ι : Type*} {s : Finset ι}
    {f : ι → Set (HeightOneSpectrum (𝓞 K))} {d : ι → ℝ}
    (hf : ∀ i ∈ s, HasDirichletDensity (f i) (d i))
    (hdisj : (s : Set ι).PairwiseDisjoint f) :
    HasDirichletDensity (⋃ i ∈ s, f i) (∑ i ∈ s, d i) := by
  refine hasDirichletDensity_iff.2 <|
    (tendsto_finsetSum s fun i hi ↦ hasDirichletDensity_iff.1 (hf i hi)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
  rw [primeIdealZetaSum_biUnion_of_pairwiseDisjoint s f hdisj
    fun i _ ↦ summable_absNorm_rpow_subtype_of_one_lt (f i) ht, Finset.sum_div]

/-- Dirichlet density is additive on disjoint unions of prime sets. -/
theorem HasDirichletDensity.union (hS : HasDirichletDensity S δ)
    (hT : HasDirichletDensity T ε) (hST : Disjoint S T) :
    HasDirichletDensity (S ∪ T) (δ + ε) := by
  have hdisj : ((↑({false, true} : Finset Bool)) : Set Bool).PairwiseDisjoint
      (fun b ↦ if b then S else T) := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · simpa [Function.onFun] using hST.symm
    · simpa [Function.onFun] using hST
    · exact (hij rfl).elim
  have hsets : (⋃ b ∈ ({false, true} : Finset Bool), if b then S else T) = S ∪ T := by
    rw [Finset.set_biUnion_insert, Finset.set_biUnion_singleton]
    simp [Set.union_comm]
  have hfinite := hasDirichletDensity_biUnion_finset
      (s := {false, true}) (f := fun b : Bool ↦ if b then S else T)
      (d := fun b : Bool ↦ if b then δ else ε)
      (by intro i _; cases i <;> assumption) hdisj
  rw [hsets] at hfinite
  simpa [add_comm] using hfinite

/-- The complement of a set of Dirichlet density `δ` has Dirichlet density `1 - δ`. -/
theorem HasDirichletDensity.compl (hS : HasDirichletDensity S δ) :
    HasDirichletDensity Sᶜ (1 - δ) := by
  refine hasDirichletDensity_iff.2 <|
    (hasDirichletDensity_iff.1 (hasDirichletDensity_univ :
      HasDirichletDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1)).sub
      (hasDirichletDensity_iff.1 hS) |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have hne : primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s ≠ 0 :=
    (primeIdealZetaSum_univ_pos_of_one_lt hs).ne'
  have hsplit : primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s =
      primeIdealZetaSum S s + primeIdealZetaSum Sᶜ s := by
    have hdisj : ((↑({false, true} : Finset Bool)) : Set Bool).PairwiseDisjoint
        (fun b ↦ if b then S else Sᶜ) := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · simpa [Function.onFun] using (disjoint_compl_left : Disjoint Sᶜ S)
      · simpa [Function.onFun] using (disjoint_compl_right : Disjoint S Sᶜ)
      · exact (hij rfl).elim
    have hsets : (⋃ b ∈ ({false, true} : Finset Bool), if b then S else Sᶜ) = Set.univ := by
      rw [Finset.set_biUnion_insert, Finset.set_biUnion_singleton]
      simp [Set.union_comm]
    have hzeta := primeIdealZetaSum_biUnion_of_pairwiseDisjoint
      ({false, true} : Finset Bool)
        (fun b ↦ if b then S else Sᶜ) hdisj
        (fun i _ ↦ by cases i <;> exact summable_absNorm_rpow_subtype_of_one_lt _ hs)
    rw [hsets] at hzeta
    simpa [add_comm] using hzeta
  rw [div_self hne, eq_div_iff hne, sub_mul, one_mul, div_mul_cancel₀ _ hne]
  linarith

/-- **Lower Dirichlet-density bounds pass to supersets.** -/
theorem IsLowerDirichletDensityBound.mono_set (hST : S ⊆ T)
    (hS : IsLowerDirichletDensityBound S δ) : IsLowerDirichletDensityBound T δ := by
  refine isLowerDirichletDensityBound_iff.2 fun η hη ↦ ?_
  filter_upwards [isLowerDirichletDensityBound_iff.1 hS η hη,
    self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
  exact hs.trans_le <| div_le_div_of_nonneg_right (primeIdealZetaSum_mono_set_of_one_lt hST hs1)
    (primeIdealZetaSum_nonneg _ s)

/-- **Upper Dirichlet-density bounds pass to subsets.** -/
theorem IsUpperDirichletDensityBound.mono_set (hST : S ⊆ T)
    (hT : IsUpperDirichletDensityBound T δ) : IsUpperDirichletDensityBound S δ := by
  refine isUpperDirichletDensityBound_iff.2 fun η hη ↦ ?_
  filter_upwards [isUpperDirichletDensityBound_iff.1 hT η hη,
    self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
  exact (div_le_div_of_nonneg_right (primeIdealZetaSum_mono_set_of_one_lt hST hs1)
    (primeIdealZetaSum_nonneg _ s)).trans_lt hs

/-- **Squeeze.** A set of primes lying between two sets of Dirichlet density `δ` has Dirichlet
density `δ`. -/
theorem hasDirichletDensity_of_subset_of_subset (hST : S ⊆ T) (hTU : T ⊆ U)
    (hS : HasDirichletDensity S δ) (hU : HasDirichletDensity U δ) :
    HasDirichletDensity T δ :=
  hasDirichletDensity_of_upperBound_of_lowerBound
    (hU.isUpperDirichletDensityBound.mono_set hTU)
    (hS.isLowerDirichletDensityBound.mono_set hST)

/-- **One member's ratio, read off from the others.** For `t > 1` every member's series converges,
so a pairwise disjoint family splits the union sum exactly; dividing by the all-prime sum
expresses one member's ratio as the union's ratio minus the ratios of the rest. -/
private theorem primeIdealZetaSum_div_univ_eq_sub_sum_erase {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → Set (HeightOneSpectrum (𝓞 K))} (hdisj : (s : Set ι).PairwiseDisjoint f)
    {t : ℝ} (ht : 1 < t) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    (f i₀).primeIdealZetaSum t / (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum t =
      (⋃ i ∈ s, f i).primeIdealZetaSum t /
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum t -
        ∑ i ∈ s.erase i₀, (f i).primeIdealZetaSum t /
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum t := by
  rw [← Finset.sum_div, ← sub_div, primeIdealZetaSum_biUnion_of_pairwiseDisjoint s f hdisj
    fun i _ ↦ summable_absNorm_rpow_subtype_of_one_lt (f i) ht,
    ← Finset.add_sum_erase _ _ hi₀, add_sub_cancel_right]

/-- **Every other member is eventually above its bound.** A finite conjunction of eventual
statements is eventually true, so all members but `i₀` clear `d i - η` simultaneously. -/
private theorem eventually_forall_mem_erase_sub_lt {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → Set (HeightOneSpectrum (𝓞 K))} {d : ι → ℝ}
    {i₀ : ι} (hlow : ∀ i ∈ s.erase i₀, IsLowerDirichletDensityBound (f i) (d i)) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ t : ℝ in 𝓝[>] 1, ∀ i ∈ s.erase i₀, d i - η <
      (f i).primeIdealZetaSum t /
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum t :=
  eventually_all_finset _ |>.2 fun i hi ↦ isLowerDirichletDensityBound_iff.mp (hlow i hi) η hη

/-- **Lower bounds on the other members bound this one from above.** A finite pairwise disjoint
family splits the union's ratio exactly, so one member's ratio is what the others leave behind; if
the lower bounds `d` already sum to `δ`, and `δ` bounds the union from above, what they leave
behind is `d i₀`.

Only an upper bound on the union is needed, which is what the proof consumes; a caller holding the
full density passes `.isUpperDirichletDensityBound`. -/
theorem isUpperDirichletDensityBound_of_forall_isLowerDirichletDensityBound {ι : Type*}
    {s : Finset ι} {f : ι → Set (HeightOneSpectrum (𝓞 K))} {d : ι → ℝ} {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hdisj : (s : Set ι).PairwiseDisjoint f)
    (hU : IsUpperDirichletDensityBound (⋃ i ∈ s, f i) δ)
    (hlow : ∀ i ∈ s, i ≠ i₀ → IsLowerDirichletDensityBound (f i) (d i))
    (hsum : ∑ i ∈ s, d i = δ) : IsUpperDirichletDensityBound (f i₀) (d i₀) := by
  classical
  -- `IsUpperDirichletDensityBound` is a non-exposed `def`, so unfold it through its `Iff.rfl`
  -- restatement rather than by `intro`.
  refine isUpperDirichletDensityBound_iff.mpr fun ε hε ↦ ?_
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr ⟨i₀, hi₀⟩
  obtain ⟨η, hη, hhalf⟩ : ∃ η : ℝ, 0 < η ∧ (s.card : ℝ) * η = ε / 2 :=
    ⟨ε / (2 * s.card), by positivity, by field_simp⟩
  have hUb := isUpperDirichletDensityBound_iff.mp hU (ε / 2) (by positivity)
  filter_upwards [eventually_forall_mem_erase_sub_lt
      (fun i hi ↦ hlow i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)) hη,
    hUb, self_mem_nhdsWithin]
    with t ht_oth ht_union (ht1 : 1 < t)
  rw [primeIdealZetaSum_div_univ_eq_sub_sum_erase hdisj ht1 hi₀]
  -- Erasing `i₀` only shrinks the index set, so the budget `#s * η = ε / 2` still covers it.
  have hbudget : (s.erase i₀).card • η ≤ ε / 2 := by
    rw [nsmul_eq_mul]
    exact hhalf ▸ mul_le_mul_of_nonneg_right (Nat.mono_cast Finset.card_erase_le) hη.le
  -- The union's ratio costs `ε / 2`; the other members' lower bounds cost the other half.
  linarith [Finset.sum_sub_le_sum_of_forall_sub_le (fun i hi ↦ (ht_oth i hi).le) hbudget,
    Finset.sum_erase_eq_sub (f := d) hi₀]

/-- **A lower bound on every member of a finite disjoint family is exact once the bounds saturate
the union's upper bound.**

Distinct from `hasDirichletDensity_of_subset_of_subset`, which squeezes a single set between two
sets of the same density. Here nothing is sandwiched: the upper bound on one member is
*manufactured* from the other members' lower bounds, because the total is pinned. This is how a
one-sided estimate becomes a density — an argument that exhibits enough primes in each class, and
cannot see that there are no more, still determines every class exactly. -/
theorem hasDirichletDensity_of_squeeze {ι : Type*} {s : Finset ι}
    {f : ι → Set (HeightOneSpectrum (𝓞 K))} {d : ι → ℝ} {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hdisj : (s : Set ι).PairwiseDisjoint f)
    (hU : IsUpperDirichletDensityBound (⋃ i ∈ s, f i) δ)
    (hlow : ∀ i ∈ s, IsLowerDirichletDensityBound (f i) (d i)) (hsum : ∑ i ∈ s, d i = δ) :
    HasDirichletDensity (f i₀) (d i₀) :=
  hasDirichletDensity_of_upperBound_of_lowerBound
    (isUpperDirichletDensityBound_of_forall_isLowerDirichletDensityBound hi₀ hdisj hU
      (fun i hi _ ↦ hlow i hi) hsum) (hlow i₀ hi₀)

end NumberField.Set
