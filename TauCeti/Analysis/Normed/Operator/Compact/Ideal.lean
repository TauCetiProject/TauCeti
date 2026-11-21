/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.RingTheory.TwoSidedIdeal.Instances
public import TauCeti.Analysis.InnerProductSpace.RankOne
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Orthonormal
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Schmidt

/-!
# The compact-operator and separable-range ideals of bounded operators

For a topological module `M` over a ring `R`, the compact continuous linear endomorphisms form a
two-sided ideal `ContinuousLinearMap.compactIdeal R M` of `M →L[R] M`, and the continuous linear
endomorphisms whose range is contained in the closure of a countable subset of `M`
(`IsSeparable (Set.range f)`) form a two-sided ideal `ContinuousLinearMap.separableRangeIdeal R M`,
with `separableRangeIdeal R M = ⊤` if and only if `M` is separable. Over a locally compact
nontrivially normed field `𝕜` (`[LocallyCompactSpace 𝕜]`), a Hausdorff topological vector space `E`
satisfies `compactIdeal 𝕜 E = ⊤` if and only if `E` is finite-dimensional. On a seminormed space
`E` over a nontrivially normed field `𝕜`, membership in `separableRangeIdeal 𝕜 E` is equivalent to
intrinsic separability `SeparableSpace (Set.range f)` of the range subtype
(`ContinuousLinearMap.mem_separableRangeIdeal_iff_separableSpace`), `separableRangeIdeal 𝕜 E` is
closed in the operator-norm topology, and `separableRangeIdeal 𝕜 E` contains `compactIdeal 𝕜 E`;
when `E` is a Banach space, `compactIdeal 𝕜 E` is also closed.

On a Hilbert space `H` over `𝕜` (`ℝ` or `ℂ`), every nonzero bounded operator `T` with `T x ≠ 0`
gives all rank-one operators by the two-sided product
`rankOneDivNormSq 𝕜 u (T x) * T * rankOne 𝕜 x v = rankOne 𝕜 u v`. Combining this algebraic
extraction with the norm-convergent singular value expansion of compact operators yields:
* The nonunital ring `↥(compactIdeal 𝕜 H)` is topologically simple: its only closed two-sided
  ideals are `⊥` and `⊤`, with `⊥ ≠ ⊤` whenever `H` is nontrivial.
* Every nonzero closed two-sided ideal of `H →L[𝕜] H` contains `compactIdeal 𝕜 H`.
* When `H` is nonseparable, `compactIdeal 𝕜 H < separableRangeIdeal 𝕜 H < ⊤`, witnessed by the
  orthogonal projection onto the closed span of a countably infinite orthonormal sequence.

## Main declarations

* `ContinuousLinearMap.compactIdeal`: the two-sided ideal of compact continuous linear
  endomorphisms of `M`, closed when `M` is a Banach space
  (`ContinuousLinearMap.isClosed_compactIdeal`).
* `ContinuousLinearMap.separableRangeIdeal`: the two-sided ideal of continuous linear endomorphisms
  of `M` whose range lies in the closure of a countable subset of `M`, characterized by
  `SeparableSpace (Set.range f)` (`ContinuousLinearMap.mem_separableRangeIdeal_iff_separableSpace`),
  closed (`ContinuousLinearMap.isClosed_separableRangeIdeal`), and containing `compactIdeal`
  (`ContinuousLinearMap.compactIdeal_le_separableRangeIdeal`) on seminormed spaces over a
  nontrivially normed field.
* `ContinuousLinearMap.twoSidedIdeal_compactIdeal_eq_bot_or_eq_top_of_isClosed`:
  `↥(compactIdeal 𝕜 H)` has no proper nonzero closed two-sided ideals.
* `ContinuousLinearMap.compactIdeal_le_of_isClosed_of_ne_bot`: every nonzero closed two-sided ideal
  of `H →L[𝕜] H` contains `compactIdeal 𝕜 H`.
* `ContinuousLinearMap.compactIdeal_lt_separableRangeIdeal`: on a nonseparable Hilbert space,
  `compactIdeal 𝕜 H < separableRangeIdeal 𝕜 H`.

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
  [CompleteSpace E]

/-- On a Banach space, `compactIdeal` is closed in the operator-norm topology. -/
theorem isClosed_compactIdeal : IsClosed (compactIdeal 𝕜 E : Set (E →L[𝕜] E)) := by
  rw [coe_compactIdeal]
  exact isClosed_setOfPred_isCompactOperator

/-- Typeclass witness that `compactIdeal` is closed on a Banach space. -/
instance instIsClosedCompactIdeal : IsClosed (compactIdeal 𝕜 E : Set (E →L[𝕜] E)) :=
  isClosed_compactIdeal

end Banach

section FiniteDimensional

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- Over a locally compact field, every continuous linear endomorphism of a Hausdorff topological
vector space `E` is compact if and only if `E` is finite-dimensional. -/
@[simp]
theorem compactIdeal_eq_top_iff_finiteDimensional :
    compactIdeal 𝕜 E = ⊤ ↔ FiniteDimensional 𝕜 E := by
  have : CompleteSpace 𝕜 := IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace 𝕜
  rw [← TwoSidedIdeal.one_mem_iff, mem_compactIdeal, one_def, coe_id',
    isCompactOperator_id_iff_finiteDimensional (𝕜 := 𝕜)]

/-- On a finite-dimensional Hausdorff topological vector space over a locally compact field,
`compactIdeal` is the whole endomorphism algebra. -/
theorem compactIdeal_eq_top [FiniteDimensional 𝕜 E] : compactIdeal 𝕜 E = ⊤ :=
  compactIdeal_eq_top_iff_finiteDimensional.mpr ‹_›

/-- On an infinite-dimensional Hausdorff topological vector space over a locally compact field,
`compactIdeal` is a proper two-sided ideal. -/
theorem compactIdeal_ne_top (hE : ¬ FiniteDimensional 𝕜 E) : compactIdeal 𝕜 E ≠ ⊤ :=
  mt compactIdeal_eq_top_iff_finiteDimensional.mp hE

/-- On an infinite-dimensional Hausdorff topological vector space over a locally compact field,
`compactIdeal` is strictly below `⊤`. -/
theorem compactIdeal_lt_top (hE : ¬ FiniteDimensional 𝕜 E) : compactIdeal 𝕜 E < ⊤ :=
  lt_top_iff_ne_top.mpr (compactIdeal_ne_top hE)

end FiniteDimensional

section NormedNontrivial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On a normed space over `ℝ` or `ℂ`, `compactIdeal 𝕜 E` is trivial if and only if `E` is a
subsingleton. -/
@[simp]
theorem compactIdeal_eq_bot_iff : compactIdeal 𝕜 E = ⊥ ↔ Subsingleton E := by
  refine ⟨fun h ↦ subsingleton_iff_forall_eq 0 |>.mpr fun x ↦ ?_,
    fun _ ↦ eq_bot_iff.mpr fun T _ ↦ ?_⟩
  · by_contra hx
    obtain ⟨g, -, hgx⟩ := exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx)
    have hmem : toSpanSingleton 𝕜 x ∘L g ∈ compactIdeal 𝕜 E :=
      mem_compactIdeal.mpr <|
        (isCompactOperator_of_locallyCompactSpace_rng (toSpanSingleton 𝕜 x)).comp_clm g
    rw [h, TwoSidedIdeal.mem_bot] at hmem
    have h0 := DFunLike.congr_fun hmem x
    simp [hgx, hx] at h0
  · rw [TwoSidedIdeal.mem_bot]
    exact Subsingleton.elim T 0

/-- On a nontrivial normed space over `ℝ` or `ℂ`, `compactIdeal` is nonzero. -/
theorem compactIdeal_ne_bot [Nontrivial E] : compactIdeal 𝕜 E ≠ ⊥ :=
  mt compactIdeal_eq_bot_iff.mp (not_subsingleton E)

/-- On a nontrivial normed space over `ℝ` or `ℂ`, the nonunital ring `↥(compactIdeal 𝕜 E)` is
nontrivial. -/
instance instNontrivialCompactIdeal [Nontrivial E] : Nontrivial ↥(compactIdeal 𝕜 E) := by
  obtain ⟨T, hT, hT0⟩ :=
    IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr (compactIdeal_ne_bot (𝕜 := 𝕜) (E := E)))
  rw [TwoSidedIdeal.mem_bot] at hT0
  exact ⟨⟨⟨T, hT⟩, 0, Subtype.coe_ne_coe.mp hT0⟩⟩

end NormedNontrivial

end CompactIdeal

section SeparableRangeIdeal

section Topological

variable (R M : Type*) [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M]

/-- The two-sided ideal of continuous linear endomorphisms of `M` whose range lies in the closure
of a countable subset of `M` (`IsSeparable (Set.range f)`). On a seminormed space, this coincides
with intrinsic separability of the range subtype (`mem_separableRangeIdeal_iff_separableSpace`). -/
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

/-- An endomorphism belongs to `separableRangeIdeal` precisely when its range lies in the closure
of a countable subset of `M`. -/
@[simp]
theorem mem_separableRangeIdeal {f : M →L[R] M} :
    f ∈ separableRangeIdeal R M ↔ IsSeparable (Set.range f) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ f

/-- The underlying set of `separableRangeIdeal` consists of endomorphisms whose range lies in the
closure of a countable subset of `M`. -/
@[simp]
theorem coe_separableRangeIdeal :
    (separableRangeIdeal R M : Set (M →L[R] M)) = {f : M →L[R] M | IsSeparable (Set.range f)} :=
  Set.ext fun _ ↦ mem_separableRangeIdeal

/-- Every continuous linear endomorphism of `M` has range contained in the closure of a countable
subset of `M` if and only if `M` itself is a separable space. -/
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

/-- On a seminormed space, an endomorphism belongs to `separableRangeIdeal` if and only if its
range subtype is a separable space. -/
theorem mem_separableRangeIdeal_iff_separableSpace {f : E →L[𝕜] E} :
    f ∈ separableRangeIdeal 𝕜 E ↔ SeparableSpace (Set.range f) :=
  mem_separableRangeIdeal.trans
    ⟨fun h ↦ h.separableSpace, fun _ ↦ IsSeparable.of_subtype (Set.range f)⟩

/-- On a seminormed space, `separableRangeIdeal` is closed in the operator-norm topology. -/
theorem isClosed_separableRangeIdeal :
    IsClosed (separableRangeIdeal 𝕜 E : Set (E →L[𝕜] E)) := by
  refine isClosed_of_closure_subset fun f hf ↦ mem_separableRangeIdeal.mpr ?_
  have hex : ∀ n : ℕ, ∃ g ∈ separableRangeIdeal 𝕜 E, dist f g < 1 / (n + 1 : ℝ) := fun n ↦
    Metric.mem_closure_iff.mp hf (1 / (n + 1 : ℝ)) (by positivity)
  choose g hg hdist using hex
  -- Approximate `f x` by `g n x` inside `⋃ n, Set.range (g n)`.
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
range. -/
theorem compactIdeal_le_separableRangeIdeal : compactIdeal 𝕜 E ≤ separableRangeIdeal 𝕜 E := by
  intro f hf
  rw [mem_separableRangeIdeal]
  choose K hK hsub using fun n : ℕ ↦
    (mem_compactIdeal.mp hf).image_closedBall_subset_compact (f := f.toLinearMap) n
  refine (IsSeparable.iUnion fun n ↦ (hK n).isSeparable).mono ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  exact Set.mem_iUnion.mpr ⟨n, hsub n ⟨x, mem_closedBall_zero_iff.mpr hn, rfl⟩⟩

end Normed

end SeparableRangeIdeal

end ContinuousLinearMap

section RankOneAndSimplicity

namespace ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Every nonzero two-sided ideal of `H →L[𝕜] H` contains every rank-one operator. -/
theorem rankOne_mem_of_ne_zero {I : TwoSidedIdeal (H →L[𝕜] H)} {T : H →L[𝕜] H}
    (hTI : T ∈ I) (hT0 : T ≠ 0) (u v : H) : rankOne 𝕜 u v ∈ I := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hT0
  have hprod : TauCeti.rankOneDivNormSq 𝕜 u (T x) * T * rankOne 𝕜 x v = rankOne 𝕜 u v := by
    simpa [mul_def, comp_assoc] using rankOneDivNormSq_comp_comp_rankOne hx u v
  rw [← hprod]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hTI)

section Complete

variable [CompleteSpace H]

/-- Any closed additive submonoid of `H →L[𝕜] H` containing every rank-one operator contains every
compact operator. -/
theorem mem_of_isCompactOperator_of_forall_rankOne_mem {S : Type*}
    [SetLike S (H →L[𝕜] H)] [AddSubmonoidClass S (H →L[𝕜] H)] {s : S}
    (hs : IsClosed (s : Set (H →L[𝕜] H))) (hrank : ∀ u v : H, rankOne 𝕜 u v ∈ s)
    {K : H →L[𝕜] H} (hK : IsCompactOperator K) : K ∈ s := by
  obtain ⟨ι, e, f, σ, -, -, -, -, -, hsum, -⟩ := hK.exists_orthonormal_hasSum_rankOne
  refine hs.mem_of_tendsto hsum (Eventually.of_forall fun _ ↦ sum_mem fun i _ ↦ ?_)
  rw [← smul_apply, ← map_smul]
  exact hrank _ _

/-- **Topological simplicity of `K(H)`.** Every closed two-sided ideal of `↥(compactIdeal 𝕜 H)` is
either `⊥` or `⊤`. When `H` is nontrivial, `⊥ ≠ ⊤` by `instNontrivialCompactIdeal`. -/
theorem twoSidedIdeal_compactIdeal_eq_bot_or_eq_top_of_isClosed
    (J : TwoSidedIdeal ↥(compactIdeal 𝕜 H)) (hJ : IsClosed (J : Set ↥(compactIdeal 𝕜 H))) :
    J = ⊥ ∨ J = ⊤ := by
  refine or_iff_not_imp_left.mpr fun hne ↦ eq_top_iff.mpr fun K _ ↦ ?_
  obtain ⟨T, hTJ, hT0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  rw [TwoSidedIdeal.mem_bot] at hT0
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (Subtype.coe_ne_coe.mpr hT0)
  let s : AddSubgroup (H →L[𝕜] H) :=
    (AddSubgroup.ofClass J).map (compactIdeal 𝕜 H).coeAddMonoidHom
  have hs_closed : IsClosed (s : Set (H →L[𝕜] H)) := by
    have hcoe : (s : Set (H →L[𝕜] H)) = Subtype.val '' (J : Set ↥(compactIdeal 𝕜 H)) := by
      ext f
      simp [s]
    rw [hcoe]
    exact isClosed_compactIdeal.isClosedMap_subtypeVal _ hJ
  have hrank : ∀ u v : H, rankOne 𝕜 u v ∈ s := fun u v ↦ by
    let L : ↥(compactIdeal 𝕜 H) :=
      ⟨TauCeti.rankOneDivNormSq 𝕜 u ((T : H →L[𝕜] H) x),
        mem_compactIdeal.mpr (TauCeti.isCompactOperator_rankOneDivNormSq u _)⟩
    let R : ↥(compactIdeal 𝕜 H) :=
      ⟨rankOne 𝕜 x v, mem_compactIdeal.mpr (InnerProductSpace.isCompactOperator_rankOne x v)⟩
    refine ⟨L * T * R, J.mul_mem_right _ R (J.mul_mem_left L T hTJ), ?_⟩
    simpa [L, R, mul_def, comp_assoc] using rankOneDivNormSq_comp_comp_rankOne hx u v
  obtain ⟨K', hK'J, hK'eq⟩ :=
    mem_of_isCompactOperator_of_forall_rankOne_mem hs_closed hrank (mem_compactIdeal.mp K.property)
  have hK' : K' = K := Subtype.ext hK'eq
  exact hK' ▸ hK'J

/-- Every nonzero closed two-sided ideal of `H →L[𝕜] H` on a Hilbert space contains all compact
operators. -/
theorem compactIdeal_le_of_isClosed_of_ne_bot {I : TwoSidedIdeal (H →L[𝕜] H)}
    (hI : IsClosed (I : Set (H →L[𝕜] H))) (hne : I ≠ ⊥) :
    compactIdeal 𝕜 H ≤ I := by
  obtain ⟨T, hTI, hT0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  rw [TwoSidedIdeal.mem_bot] at hT0
  exact fun K hK ↦
    mem_of_isCompactOperator_of_forall_rankOne_mem hI (rankOne_mem_of_ne_zero hTI hT0)
      (mem_compactIdeal.mp hK)

/-- Every closed two-sided ideal of `H →L[𝕜] H` is either `⊥` or contains `compactIdeal 𝕜 H`. -/
theorem eq_bot_or_compactIdeal_le_of_isClosed {I : TwoSidedIdeal (H →L[𝕜] H)}
    (hI : IsClosed (I : Set (H →L[𝕜] H))) :
    I = ⊥ ∨ compactIdeal 𝕜 H ≤ I :=
  or_iff_not_imp_left.mpr (compactIdeal_le_of_isClosed_of_ne_bot hI)

end Complete

end ContinuousLinearMap

end RankOneAndSimplicity

section Nonseparable

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- On a nonseparable Hilbert space, `compactIdeal` is strictly contained in `separableRangeIdeal`.
-/
theorem ContinuousLinearMap.compactIdeal_lt_separableRangeIdeal (hH : ¬ SeparableSpace H) :
    compactIdeal 𝕜 H < separableRangeIdeal 𝕜 H := by
  refine lt_of_le_of_ne compactIdeal_le_separableRangeIdeal fun heq ↦ ?_
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 H
  have hnot_count : ¬ Countable w := fun _ ↦ hH b.separableSpace
  have : Infinite w := not_finite_iff_infinite.mp fun _ ↦ hnot_count inferInstance
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
    exact (U.orthogonalProjectionOnto x).property
  have hmem_cpt : IsCompactOperator U.starProjection :=
    mem_compactIdeal.mp (heq.symm ▸ hmem_sep)
  have hvU : ∀ n : ℕ, U.starProjection (v n) = (1 : 𝕜) • v n := fun n ↦ by
    rw [one_smul, Submodule.starProjection_eq_self_iff]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  have hfin := hmem_cpt.finite_setOf_le_norm_of_orthonormal hv hvU zero_lt_one
  simp only [norm_one, le_refl, Set.ofPred_true] at hfin
  exact Set.infinite_univ hfin

end Nonseparable

end
