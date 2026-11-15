/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.RingTheory.TwoSidedIdeal.Instances
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.RankOne
public import TauCeti.Analysis.Normed.Ring.Simple
import Mathlib.Analysis.InnerProductSpace.l2Space
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
import TauCeti.Analysis.Normed.Operator.Compact.Orthonormal
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Schmidt

/-!
# The compact-operator and separable-range ideals of bounded operators

For a topological module `M` over a ring `R`, the compact endomorphisms form a two-sided ideal
`ContinuousLinearMap.compactIdeal R M` of `M →L[R] M`, and the endomorphisms with separable range
form a larger two-sided ideal `ContinuousLinearMap.separableRangeIdeal R M`. On a Banach space `E`
over a nontrivially normed field `𝕜`, both ideals are closed in the operator-norm topology,
`compactIdeal 𝕜 E = ⊤` if and only if `E` is finite-dimensional, and `separableRangeIdeal 𝕜 E = ⊤`
if and only if `E` is separable.

On a Hilbert space `H` over `𝕜` (`ℝ` or `ℂ`), every nonzero bounded operator `T` with `T x ≠ 0`
gives all rank-one operators by the two-sided product
`rankOneDivNormSq 𝕜 u (T x) * T * rankOne 𝕜 x v = rankOne 𝕜 u v`. Combining this algebraic
extraction with the norm-convergent singular value expansion of compact operators yields:
* Every nonzero closed two-sided ideal of `H →L[𝕜] H` contains `compactIdeal 𝕜 H`.
* The nonunital ring `↥(compactIdeal 𝕜 H)` is topologically simple: its only closed two-sided
  ideals are `⊥` and `⊤`, with `⊥ ≠ ⊤` whenever `H` is nontrivial.
* When `H` is nonseparable, `compactIdeal 𝕜 H < separableRangeIdeal 𝕜 H < ⊤`, witnessed by the
  orthogonal projection onto the closed span of a countably infinite orthonormal sequence.
* When `H` is separable, every noncompact star projection `p : H →L[𝕜] H` has infinite-dimensional
  closed range, so there is a linear isometry `v : H →ₗᵢ[𝕜] H` into `p.range` satisfying
  `p * v = v` and `star v * p * v = 1`.

## Main declarations

* `ContinuousLinearMap.compactIdeal`: the two-sided ideal of compact operators on `M`, closed when
  `M` is a Banach space (`ContinuousLinearMap.isClosed_compactIdeal`).
* `ContinuousLinearMap.separableRangeIdeal`: the two-sided ideal of bounded operators with
  separable range, closed on normed spaces (`ContinuousLinearMap.isClosed_separableRangeIdeal`) and
  containing `compactIdeal` (`ContinuousLinearMap.compactIdeal_le_separableRangeIdeal`).
* `ContinuousLinearMap.compactIdeal_le_of_isClosed_of_ne_bot`: every nonzero closed two-sided ideal
  of `H →L[𝕜] H` contains `compactIdeal 𝕜 H`.
* `ContinuousLinearMap.compactIdeal_eq_bot_or_eq_top_of_isClosed`: `↥(compactIdeal 𝕜 H)` has no
  nontrivial closed two-sided ideals.
* `ContinuousLinearMap.compactIdeal_lt_separableRangeIdeal`: on a nonseparable Hilbert space,
  `compactIdeal 𝕜 H < separableRangeIdeal 𝕜 H`.
* `IsStarProjection.exists_linearIsometry_mul_eq_and_star_mul_mul_eq_one`: on a separable Hilbert
  space, a noncompact star projection `p` admits an isometry `v` with `p * v = v` and
  `star v * p * v = 1`.

## References

* J. W. Calkin, *Two-sided ideals and congruences in the ring of bounded operators in Hilbert
  space*, Annals of Mathematics 42 (1941), 839–873, §1.
* B. Blackadar, *Operator Algebras*, Encyclopaedia of Mathematical Sciences 122, Springer (2006),
  II.5.1.4 and II.5.3.10.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), Chapter IX, §4.
-/

public noncomputable section

open Filter InnerProductSpace RCLike TopologicalSpace Topology
open scoped InnerProductSpace

namespace ContinuousLinearMap

section CompactIdeal

section Topological

variable (R M : Type*) [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M]

/-- The two-sided ideal of compact continuous linear endomorphisms of `M`. -/
def compactIdeal : TwoSidedIdeal (M →L[R] M) :=
  TwoSidedIdeal.mk' {f : M →L[R] M | IsCompactOperator f}
    isCompactOperator_zero
    (fun hf hg ↦ hf.add hg)
    (fun hf ↦ hf.neg)
    (fun {f _} hg ↦ hg.mul_left f)
    (fun {_ g} hf ↦ hf.mul_right g)

variable {R M}

/-- An endomorphism belongs to `compactIdeal` precisely when it is a compact operator. -/
@[simp]
theorem mem_compactIdeal {f : M →L[R] M} : f ∈ compactIdeal R M ↔ IsCompactOperator f :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ f

/-- The underlying set of `compactIdeal` is the set of compact operators. -/
@[simp]
theorem coe_compactIdeal :
    (compactIdeal R M : Set (M →L[R] M)) = {f : M →L[R] M | IsCompactOperator f} :=
  Set.ext fun _ ↦ mem_compactIdeal

end Topological

section Banach

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section Closed

variable [CompleteSpace E]

/-- On a Banach space, `compactIdeal` is closed in the operator-norm topology. -/
theorem isClosed_compactIdeal : IsClosed (compactIdeal 𝕜 E : Set (E →L[𝕜] E)) := by
  rw [coe_compactIdeal]
  exact isClosed_setOfPred_isCompactOperator

/-- Typeclass witness that `compactIdeal` is closed on a Banach space. -/
instance instIsClosedCompactIdeal : IsClosed (compactIdeal 𝕜 E : Set (E →L[𝕜] E)) :=
  isClosed_compactIdeal

end Closed

section FiniteDimensional

variable [LocallyCompactSpace 𝕜]

/-- Over a locally compact field, every bounded operator on `E` is compact if and only if `E` is
finite-dimensional. -/
@[simp]
theorem compactIdeal_eq_top_iff_finiteDimensional :
    compactIdeal 𝕜 E = ⊤ ↔ FiniteDimensional 𝕜 E := by
  have : CompleteSpace 𝕜 := IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace 𝕜
  rw [← TwoSidedIdeal.one_mem_iff, mem_compactIdeal, one_def, coe_id',
    isCompactOperator_id_iff_finiteDimensional (𝕜 := 𝕜)]

/-- On a finite-dimensional normed space over a locally compact field, `compactIdeal` is the whole
endomorphism algebra. -/
theorem compactIdeal_eq_top [FiniteDimensional 𝕜 E] : compactIdeal 𝕜 E = ⊤ :=
  compactIdeal_eq_top_iff_finiteDimensional.mpr ‹_›

/-- On an infinite-dimensional normed space over a locally compact field, `compactIdeal` is a
proper two-sided ideal. -/
theorem compactIdeal_ne_top (hE : ¬ FiniteDimensional 𝕜 E) : compactIdeal 𝕜 E ≠ ⊤ :=
  mt compactIdeal_eq_top_iff_finiteDimensional.mp hE

/-- On an infinite-dimensional normed space over a locally compact field, `compactIdeal` is
strictly below `⊤`. -/
theorem compactIdeal_lt_top (hE : ¬ FiniteDimensional 𝕜 E) : compactIdeal 𝕜 E < ⊤ :=
  lt_top_iff_ne_top.mpr (compactIdeal_ne_top hE)

end FiniteDimensional

end Banach

end CompactIdeal

section SeparableRangeIdeal

section Topological

variable (R M : Type*) [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M]

/-- The two-sided ideal of continuous linear endomorphisms of `M` whose range is separable. -/
def separableRangeIdeal : TwoSidedIdeal (M →L[R] M) :=
  TwoSidedIdeal.mk' {f : M →L[R] M | IsSeparable (Set.range f)}
    ((Set.finite_singleton (0 : M)).isSeparable.mono <| by
      rintro _ ⟨_, rfl⟩
      simp)
    (fun {f g} hf hg ↦ ((hf.prod hg).image continuous_add).mono <| by
      rintro _ ⟨x, rfl⟩
      exact ⟨(f x, g x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩)
    (fun {f} hf ↦ (hf.image continuous_neg).mono <| by
      rintro _ ⟨x, rfl⟩
      exact ⟨f x, ⟨x, rfl⟩, rfl⟩)
    (fun {f g} hg ↦ (hg.image f.continuous).mono <| by
      rintro _ ⟨x, rfl⟩
      exact ⟨g x, ⟨x, rfl⟩, rfl⟩)
    (fun {_ g} hf ↦ hf.mono <| by
      rintro _ ⟨x, rfl⟩
      exact ⟨g x, rfl⟩)

variable {R M}

/-- An endomorphism belongs to `separableRangeIdeal` precisely when its range is separable. -/
@[simp]
theorem mem_separableRangeIdeal {f : M →L[R] M} :
    f ∈ separableRangeIdeal R M ↔ IsSeparable (Set.range f) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ f

/-- The underlying set of `separableRangeIdeal` consists of endomorphisms with separable range. -/
@[simp]
theorem coe_separableRangeIdeal :
    (separableRangeIdeal R M : Set (M →L[R] M)) = {f : M →L[R] M | IsSeparable (Set.range f)} :=
  Set.ext fun _ ↦ mem_separableRangeIdeal

/-- Every continuous linear endomorphism of `M` has separable range if and only if `M` itself is a
separable space. -/
@[simp]
theorem separableRangeIdeal_eq_top_iff : separableRangeIdeal R M = ⊤ ↔ SeparableSpace M := by
  rw [← TwoSidedIdeal.one_mem_iff, mem_separableRangeIdeal, one_def, coe_id', Set.range_id,
    isSeparable_univ_iff]

/-- On a separable space, `separableRangeIdeal` is the whole endomorphism ring. -/
theorem separableRangeIdeal_eq_top [SeparableSpace M] : separableRangeIdeal R M = ⊤ :=
  separableRangeIdeal_eq_top_iff.mpr ‹_›

/-- On a nonseparable space, `separableRangeIdeal` is a proper two-sided ideal. -/
theorem separableRangeIdeal_ne_top (hM : ¬ SeparableSpace M) : separableRangeIdeal R M ≠ ⊤ :=
  mt separableRangeIdeal_eq_top_iff.mp hM

/-- On a nonseparable space, `separableRangeIdeal` is strictly below `⊤`. -/
theorem separableRangeIdeal_lt_top (hM : ¬ SeparableSpace M) : separableRangeIdeal R M < ⊤ :=
  lt_top_iff_ne_top.mpr (separableRangeIdeal_ne_top hM)

end Topological

section Normed

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On a seminormed space, `separableRangeIdeal` is closed in the operator-norm topology: if `f` is
approximated in operator norm by a sequence `gₙ` with separable ranges, then `Set.range f` lies in
the closure of `⋃ n, Set.range (gₙ)`. -/
theorem isClosed_separableRangeIdeal :
    IsClosed (separableRangeIdeal 𝕜 E : Set (E →L[𝕜] E)) := by
  refine isClosed_of_closure_subset fun f hf ↦ mem_separableRangeIdeal.mpr ?_
  have hex : ∀ n : ℕ, ∃ g ∈ separableRangeIdeal 𝕜 E, dist f g < 1 / (n + 1 : ℝ) := fun n ↦
    Metric.mem_closure_iff.mp hf (1 / (n + 1 : ℝ)) (by positivity)
  choose g hg hdist using hex
  have hsep : IsSeparable (closure (⋃ n : ℕ, Set.range (g n))) :=
    (IsSeparable.iUnion fun n ↦ mem_separableRangeIdeal.mp (hg n)).closure
  refine hsep.mono ?_
  rintro _ ⟨x, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ / ε)
  refine ⟨g n x, Set.mem_iUnion.mpr ⟨n, x, rfl⟩, ?_⟩
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  calc dist (f x) (g n x) = ‖(f - g n) x‖ := dist_eq_norm (f x) (g n x)
    _ ≤ ‖f - g n‖ * ‖x‖ := le_opNorm (f - g n) x
    _ ≤ (1 / (n + 1 : ℝ)) * ‖x‖ := by
      gcongr
      rw [← dist_eq_norm]
      exact (hdist n).le
    _ < ε := by
      rw [one_div_mul_eq_div, div_lt_iff₀ hn1]
      have hlt : ‖x‖ < ε * n := (div_lt_iff₀' hε).mp hn
      linarith

/-- Typeclass witness that `separableRangeIdeal` is closed on a seminormed space. -/
instance instIsClosedSeparableRangeIdeal :
    IsClosed (separableRangeIdeal 𝕜 E : Set (E →L[𝕜] E)) :=
  isClosed_separableRangeIdeal

/-- Every compact operator on a seminormed space over a nontrivially normed field has separable
range: `f` maps a ball around `0` into a compact (hence separable) set `K`, and `Set.range f` is
covered by countably many scalar multiples of `K`. -/
theorem compactIdeal_le_separableRangeIdeal : compactIdeal 𝕜 E ≤ separableRangeIdeal 𝕜 E := by
  intro f hf
  obtain ⟨K, hK, hnhds⟩ := mem_compactIdeal.mp hf
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  rw [mem_separableRangeIdeal]
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hcov : Set.range f ⊆ ⋃ n : ℕ, (c ^ n • ·) '' K := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖x‖ / r) hc
    have hcn : c ^ n ≠ 0 := pow_ne_zero n (norm_pos_iff.mp (zero_lt_one.trans hc))
    refine Set.mem_iUnion.mpr ⟨n, f ((c ^ n)⁻¹ • x), ?_, ?_⟩
    · apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_smul, norm_inv, norm_pow]
      exact (inv_mul_lt_iff₀ (pow_pos (zero_lt_one.trans hc) n)).mpr ((div_lt_iff₀ hr).mp hn)
    · dsimp only
      rw [← map_smul, smul_inv_smul₀ hcn]
  exact (IsSeparable.iUnion fun n ↦ hK.isSeparable.image (continuous_const_smul (c ^ n))).mono hcov

end Normed

end SeparableRangeIdeal

end ContinuousLinearMap

section RankOneAndSimplicity

variable {𝕜 E F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Every rank-one operator between inner product spaces is compact. -/
theorem InnerProductSpace.isCompactOperator_rankOne (x : E) (y : F) :
    IsCompactOperator (rankOne 𝕜 x y) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton 𝕜 x)).comp_clm _

/-- Every normalized rank-one operator `TauCeti.rankOneDivNormSq 𝕜 y x` is compact. -/
theorem TauCeti.isCompactOperator_rankOneDivNormSq (y : F) (x : E) :
    IsCompactOperator (TauCeti.rankOneDivNormSq 𝕜 y x) := by
  rw [TauCeti.rankOneDivNormSq_def]
  exact (InnerProductSpace.isCompactOperator_rankOne y x).smul _

namespace ContinuousLinearMap

/-- Sandwiching a bounded operator `T` with `T x ≠ 0` between `rankOneDivNormSq 𝕜 u (T x)` and
`rankOne 𝕜 x v` produces the arbitrary rank-one operator `rankOne 𝕜 u v`. -/
theorem rankOneDivNormSq_mul_mul_rankOne {T : H →L[𝕜] H} {x : H} (hx : T x ≠ 0) (u v : H) :
    TauCeti.rankOneDivNormSq 𝕜 u (T x) * T * rankOne 𝕜 x v = rankOne 𝕜 u v := by
  ext w
  simp [map_smul, TauCeti.rankOneDivNormSq_apply_self u hx]

/-- Every nonzero two-sided ideal of `H →L[𝕜] H` contains every rank-one operator. -/
theorem rankOne_mem_of_ne_zero {I : TwoSidedIdeal (H →L[𝕜] H)} {T : H →L[𝕜] H}
    (hTI : T ∈ I) (hT0 : T ≠ 0) (u v : H) : rankOne 𝕜 u v ∈ I := by
  obtain ⟨x, hx⟩ : ∃ x, T x ≠ 0 := by
    by_contra! h
    exact hT0 (ext h)
  rw [← rankOneDivNormSq_mul_mul_rankOne hx u v]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hTI)

/-- On an inner product space `H`, `compactIdeal 𝕜 H` is trivial if and only if `H` is a
subsingleton. -/
@[simp]
theorem compactIdeal_eq_bot_iff : compactIdeal 𝕜 H = ⊥ ↔ Subsingleton H := by
  refine ⟨fun h ↦ subsingleton_iff_forall_eq 0 |>.mpr fun x ↦ ?_,
    fun _ ↦ eq_bot_iff.mpr fun T _ ↦ ?_⟩
  · by_contra hx
    have hmem : rankOne 𝕜 x x ∈ compactIdeal 𝕜 H :=
      mem_compactIdeal.mpr (InnerProductSpace.isCompactOperator_rankOne x x)
    rw [h, TwoSidedIdeal.mem_bot, rankOne_eq_zero, or_self] at hmem
    exact hx hmem
  · rw [TwoSidedIdeal.mem_bot]
    exact Subsingleton.elim T 0

/-- On a nontrivial inner product space, `compactIdeal` is nonzero. -/
theorem compactIdeal_ne_bot [Nontrivial H] : compactIdeal 𝕜 H ≠ ⊥ :=
  mt compactIdeal_eq_bot_iff.mp (not_subsingleton H)

/-- On a nontrivial inner product space, the nonunital ring `↥(compactIdeal 𝕜 H)` is nontrivial. -/
instance instNontrivialCompactIdeal [Nontrivial H] : Nontrivial ↥(compactIdeal 𝕜 H) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  refine ⟨⟨⟨rankOne 𝕜 x x, mem_compactIdeal.mpr (InnerProductSpace.isCompactOperator_rankOne x x)⟩,
    0, fun h ↦ ?_⟩⟩
  have h0 := congrArg Subtype.val h
  simp only [ZeroMemClass.coe_zero, rankOne_eq_zero, or_self] at h0
  exact hx h0

section Complete

variable [CompleteSpace H]

/-- Every nonzero closed two-sided ideal of `H →L[𝕜] H` on a Hilbert space contains all compact
operators: a nonzero element generates every rank-one operator algebraically, and every compact
operator is an operator-norm sum of rank-one operators. -/
theorem compactIdeal_le_of_isClosed_of_ne_bot {I : TwoSidedIdeal (H →L[𝕜] H)}
    (hI : IsClosed (I : Set (H →L[𝕜] H))) (hne : I ≠ ⊥) :
    compactIdeal 𝕜 H ≤ I := by
  obtain ⟨T, hTI, hT0⟩ : ∃ T ∈ I, T ≠ 0 := by
    by_contra! h
    refine hne (le_bot_iff.mp fun T hT ↦ ?_)
    rw [TwoSidedIdeal.mem_bot]
    exact h T hT
  intro K hK
  obtain ⟨ι, e, f, σ, -, -, -, -, -, hsum, -⟩ :=
    (mem_compactIdeal.mp hK).exists_orthonormal_hasSum_rankOne
  -- Each singular-value term `(σ i : 𝕜) • rankOne 𝕜 (f i) (e i)` rewrites to
  -- `rankOne 𝕜 ((σ i : 𝕜) • f i) (e i) ∈ I`, so `K` is a norm limit of finite sums in `I`.
  refine hI.mem_of_tendsto hsum (Eventually.of_forall fun _ ↦ sum_mem fun i _ ↦ ?_)
  rw [← smul_apply, ← map_smul]
  exact rankOne_mem_of_ne_zero hTI hT0 _ _

/-- Every closed two-sided ideal of `H →L[𝕜] H` is either `⊥` or contains `compactIdeal 𝕜 H`. -/
theorem eq_bot_or_compactIdeal_le_of_isClosed {I : TwoSidedIdeal (H →L[𝕜] H)}
    (hI : IsClosed (I : Set (H →L[𝕜] H))) :
    I = ⊥ ∨ compactIdeal 𝕜 H ≤ I :=
  or_iff_not_imp_left.mpr (compactIdeal_le_of_isClosed_of_ne_bot hI)

/-- **Topological simplicity of `K(H)`.** Every closed two-sided ideal of `↥(compactIdeal 𝕜 H)` is
either `⊥` or `⊤`. When `H` is nontrivial, `⊥ ≠ ⊤` by `instNontrivialCompactIdeal`. -/
theorem compactIdeal_eq_bot_or_eq_top_of_isClosed
    (J : TwoSidedIdeal ↥(compactIdeal 𝕜 H)) (hJ : IsClosed (J : Set ↥(compactIdeal 𝕜 H))) :
    J = ⊥ ∨ J = ⊤ := by
  refine or_iff_not_imp_left.mpr fun hne ↦ eq_top_iff.mpr fun K _ ↦ ?_
  obtain ⟨T, hTJ, hT0⟩ : ∃ T ∈ J, T ≠ 0 := by
    by_contra! h
    refine hne (le_bot_iff.mp fun T hT ↦ ?_)
    rw [TwoSidedIdeal.mem_bot]
    exact h T hT
  have hTval : (T : H →L[𝕜] H) ≠ 0 := Subtype.coe_ne_coe.mpr hT0
  obtain ⟨x, hx⟩ : ∃ x, (T : H →L[𝕜] H) x ≠ 0 := by
    by_contra! h
    exact hTval (ext h)
  -- Both sandwich factors lie in `compactIdeal 𝕜 H`, so every rank-one operator lies in `J`.
  have hrank : ∀ u v : H,
      (⟨rankOne 𝕜 u v, mem_compactIdeal.mpr (InnerProductSpace.isCompactOperator_rankOne u v)⟩ :
        ↥(compactIdeal 𝕜 H)) ∈ J := fun u v ↦ by
    let L : ↥(compactIdeal 𝕜 H) :=
      ⟨TauCeti.rankOneDivNormSq 𝕜 u ((T : H →L[𝕜] H) x),
        mem_compactIdeal.mpr (TauCeti.isCompactOperator_rankOneDivNormSq u _)⟩
    let R : ↥(compactIdeal 𝕜 H) :=
      ⟨rankOne 𝕜 x v, mem_compactIdeal.mpr (InnerProductSpace.isCompactOperator_rankOne x v)⟩
    have hprod : L * T * R =
        ⟨rankOne 𝕜 u v, mem_compactIdeal.mpr (InnerProductSpace.isCompactOperator_rankOne u v)⟩ :=
      Subtype.ext (rankOneDivNormSq_mul_mul_rankOne hx u v)
    exact hprod ▸ J.mul_mem_right _ R (J.mul_mem_left L T hTJ)
  obtain ⟨ι, e, f, σ, -, -, -, -, -, hsum, -⟩ :=
    (mem_compactIdeal.mp K.2).exists_orthonormal_hasSum_rankOne
  let term : ι → ↥(compactIdeal 𝕜 H) := fun i ↦
    ⟨rankOne 𝕜 ((σ i : 𝕜) • f i) (e i),
      mem_compactIdeal.mpr (InnerProductSpace.isCompactOperator_rankOne _ _)⟩
  have hsum_sub : HasSum term K := by
    rw [HasSum, Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    refine hsum.congr fun s ↦ ?_
    rw [Function.comp_apply]
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans
      (map_sum (compactIdeal 𝕜 H).coeAddMonoidHom term s).symm
    simp [term]
  exact hJ.mem_of_tendsto hsum_sub (Eventually.of_forall fun _ ↦ sum_mem fun _ _ ↦ hrank _ _)

end Complete

/-- On a nonzero finite-dimensional inner product space, the endomorphism algebra `H →L[𝕜] H` is a
simple ring. -/
instance instIsSimpleRing [FiniteDimensional 𝕜 H] [Nontrivial H] : IsSimpleRing (H →L[𝕜] H) := by
  have : CompleteSpace H := FiniteDimensional.completeSpace 𝕜 H
  refine IsSimpleRing.of_forall_isClosed_eq_bot_or_eq_top fun I hI ↦ ?_
  refine (eq_bot_or_compactIdeal_le_of_isClosed hI).imp_right fun hle ↦ ?_
  rwa [compactIdeal_eq_top, top_le_iff] at hle

end ContinuousLinearMap

end RankOneAndSimplicity

section SeparabilityAndProjections

variable {𝕜 ι E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- An orthonormal family in a separable inner product space has a countable index type: the open
balls of radius `1 / 2` around distinct vectors are pairwise disjoint. -/
theorem Orthonormal.countable [SeparableSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (v i) (1 / 2))
    ?_ (fun _ ↦ Metric.isOpen_ball) (fun i ↦ ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  intro i j hij
  refine Metric.ball_disjoint_ball ?_
  have hsq : dist (v i) (v j) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq (𝕜 := 𝕜), hv.2 hij, map_zero, mul_zero, sub_zero,
      hv.1 i, hv.1 j]
    norm_num
  nlinarith [dist_nonneg (x := v i) (y := v j)]

/-- On a nonseparable Hilbert space, `compactIdeal` is strictly contained in `separableRangeIdeal`:
the orthogonal projection onto the closed span of a countably infinite orthonormal sequence has
separable range but is not compact. -/
theorem ContinuousLinearMap.compactIdeal_lt_separableRangeIdeal (hH : ¬ SeparableSpace H) :
    compactIdeal 𝕜 H < separableRangeIdeal 𝕜 H := by
  refine lt_of_le_of_ne compactIdeal_le_separableRangeIdeal fun heq ↦ ?_
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 H
  have hnot_count : ¬ Countable w := fun hcw ↦ hH <| by
    have : Countable w := hcw
    have hsep : IsSeparable (closure (Submodule.span 𝕜 (Set.range b) : Set H)) :=
      (Set.countable_range b).isSeparable.span.closure
    have hcl : closure (Submodule.span 𝕜 (Set.range b) : Set H) = Set.univ := by
      rw [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe]
    exact isSeparable_univ_iff.mp (hcl ▸ hsep)
  have : Infinite w := not_finite_iff_infinite.mp fun hfin ↦ by
    have := Fintype.ofFinite w
    exact hnot_count inferInstance
  let e := Infinite.natEmbedding w
  let v : ℕ → H := fun n ↦ b (e n)
  have hv : Orthonormal 𝕜 v := b.orthonormal.comp e e.injective
  let U : Submodule 𝕜 H := (Submodule.span 𝕜 (Set.range v)).topologicalClosure
  have : CompleteSpace U :=
    (Submodule.span 𝕜 (Set.range v)).isClosed_topologicalClosure.completeSpace_coe
  have hmem_sep : U.starProjection ∈ separableRangeIdeal 𝕜 H := by
    rw [mem_separableRangeIdeal]
    have hsepU : IsSeparable (U : Set H) := by
      rw [Submodule.topologicalClosure_coe]
      exact (Set.countable_range v).isSeparable.span.closure
    refine hsepU.mono ?_
    rintro _ ⟨x, rfl⟩
    rw [Submodule.starProjection_apply]
    exact (U.orthogonalProjectionOnto x).2
  have hmem_cpt : IsCompactOperator U.starProjection :=
    mem_compactIdeal.mp (heq.symm ▸ hmem_sep)
  have hvU : ∀ n : ℕ, U.starProjection (v n) = (1 : 𝕜) • v n := fun n ↦ by
    rw [one_smul, Submodule.starProjection_eq_self_iff]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  have hfin := hmem_cpt.finite_setOf_le_norm_of_orthonormal hv hvU zero_lt_one
  simp only [norm_one, le_refl, Set.ofPred_true] at hfin
  exact Set.infinite_univ hfin

/-- On a separable Hilbert space, every noncompact star projection `p` has infinite-dimensional
closed range, so there exists a linear isometry `v : H →ₗᵢ[𝕜] H` mapping `H` into `p.range` such
that `p * v = v` and `star v * p * v = 1`. -/
theorem IsStarProjection.exists_linearIsometry_mul_eq_and_star_mul_mul_eq_one [SeparableSpace H]
    {p : H →L[𝕜] H} (hp : IsStarProjection p) (hnc : ¬ IsCompactOperator p) :
    ∃ v : H →ₗᵢ[𝕜] H,
      p * v.toContinuousLinearMap = v.toContinuousLinearMap ∧
        star v.toContinuousLinearMap * p * v.toContinuousLinearMap = 1 := by
  have hp_closed : IsClosed (p.range : Set H) := by
    have hset : (p.range : Set H) = {x : H | p x = x} := by
      ext x
      refine ⟨?_, fun hx ↦ ⟨x, hx⟩⟩
      rintro ⟨y, rfl⟩
      exact DFunLike.congr_fun hp.isIdempotentElem.eq y
    rw [hset]
    exact isClosed_eq p.continuous continuous_id
  have : CompleteSpace p.range := hp_closed.completeSpace_coe
  have hinf : ¬ FiniteDimensional 𝕜 p.range := fun _ ↦
    hnc (LinearMap.HasFiniteRange.isCompactOperator Submodule.FG.of_finite)
  obtain ⟨w₁, b₁, -⟩ := exists_hilbertBasis 𝕜 p.range
  have : Infinite w₁ := not_finite_iff_infinite.mp fun hfin ↦ by
    have := Fintype.ofFinite w₁
    exact hinf b₁.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  obtain ⟨w₂, b₂, -⟩ := exists_hilbertBasis 𝕜 H
  have : Countable w₂ := b₂.orthonormal.countable
  obtain ⟨f₂, hf₂⟩ := exists_injective_nat w₂
  -- Embed the countable Hilbert basis of `H` into the infinite Hilbert basis of `p.range`.
  let φ : w₂ → w₁ := Infinite.natEmbedding w₁ ∘ f₂
  have hφ : Function.Injective φ := (Infinite.natEmbedding w₁).injective.comp hf₂
  have hu : Orthonormal 𝕜 (b₁ ∘ φ) := b₁.orthonormal.comp φ hφ
  let v : H →ₗᵢ[𝕜] H :=
    p.range.subtypeₗᵢ.comp (hu.orthogonalFamily.linearIsometry.comp b₂.repr.toLinearIsometry)
  have hpv : p * v.toContinuousLinearMap = v.toContinuousLinearMap := by
    ext x
    obtain ⟨y, hy⟩ := (hu.orthogonalFamily.linearIsometry (b₂.repr x)).2
    have hval : v x = p y := hy.symm
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, hval]
    exact DFunLike.congr_fun hp.isIdempotentElem.eq y
  refine ⟨v, hpv, ?_⟩
  rw [mul_assoc, hpv, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    v.adjoint_comp_self]

end SeparabilityAndProjections

end
