/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
public import TauCeti.Analysis.Normed.Group.NullFamily
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import TauCeti.Algebra.Module.LinearMap.FiniteRank

/-!
# The model space `C₀(I, E)` on a discrete index

For a discrete space `I`, the cocompact filter on `I` is the cofinite filter, so `C₀(I, E)` is
the space of families `I → E` tending to zero along the cofinite filter, with the sup norm. Over
a complete ultrametric normed ring `R`, the spaces `C₀(I, R)` are the model spaces of
nonarchimedean functional analysis: orthonormalisable Banach modules are those linearly isometric
to some `C₀(I, R)`.

This file develops the coordinate structure of `C₀(I, E)`:

* `ZeroAtInftyContinuousMap.mkOfDiscrete`: a family tending to zero along the cofinite filter as
  an element of `C₀(I, E)`;
* `ZeroAtInftyContinuousMap.single i x`: the coordinate vector supported at `i` with value `x`,
  of norm `‖x‖` (`ZeroAtInftyContinuousMap.norm_single`), so that on an infinite index the
  coordinate vectors with a fixed nonzero value are not norm null
  (`ZeroAtInftyContinuousMap.not_tendsto_single_cofinite`); a finite sum of coordinate vectors at
  distinct coordinates has the maximum of their norms
  (`ZeroAtInftyContinuousMap.nnnorm_sum_single`);
* `ZeroAtInftyContinuousMap.exists_norm_coe_eq_norm`: the sup norm is attained at some
  coordinate when `I` is nonempty;
* `ZeroAtInftyContinuousMap.hasSum_single`: every `f` is the unconditional sum of its coordinate
  vectors `single i (f i)`, and for scalar families `f = ∑ i, f i • single i 1`
  (`ZeroAtInftyContinuousMap.hasSum_smul_single_one`);
* `ZeroAtInftyContinuousMap.dense_setOf_finite_support` and
  `ZeroAtInftyContinuousMap.dense_span_single_one`: finitely supported families are dense, and
  the coordinate vectors `single i 1` span a dense submodule of `C₀(I, R)`;
* `ZeroAtInftyContinuousMap.continuousLinearMap_ext`: continuous linear maps out of `C₀(I, E)`
  are determined by their values on coordinate vectors;
* `ZeroAtInftyContinuousMap.indicatorCLM R S`: the coordinate projection `f ↦ S.indicator f`
  onto a set `S` of indices, of norm at most one; on `C₀(I, R)` it has finite rank when `S` is
  finite (`ZeroAtInftyContinuousMap.isFiniteRank_indicatorCLM`).

It also compares the model spaces over different discrete index types. These isometries send
coordinate vectors to coordinate vectors and commute with the coordinatewise action
`ZeroAtInftyContinuousMap.compLeft` of a bounded coefficient map:

* `ZeroAtInftyContinuousMap.sumEquiv`: `C₀(I ⊕ J, E) ≃ₗᵢ[R] C₀(I, E) × C₀(J, E)`;
* `ZeroAtInftyContinuousMap.equivFunOnFintype`: `C₀(I, E) ≃ₗᵢ[R] (I → E)` for finite `I`;
* `ZeroAtInftyContinuousMap.curryEquiv`: `C₀(I × J, E) ≃ₗᵢ[R] C₀(I, C₀(J, E))`.

Reindexing along an equivalence `e : I ≃ J` is the case `e.toHomeomorphOfDiscrete` of
`ZeroAtInftyContinuousMap.congrLeft`.

None of these statements needs completeness or the ultrametric inequality. The extension of
bounded families to continuous linear maps out of `C₀(I, R)` is developed in
`TauCeti.Topology.ContinuousMap.ZeroAtInfty.LinearCombination`.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §10.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {I β : Type*} [TopologicalSpace I] [DiscreteTopology I]

section Zero

variable [TopologicalSpace β] [Zero β]

/-- A function vanishing at infinity on a discrete space tends to zero along the cofinite
filter. -/
theorem tendsto_cofinite (f : C₀(I, β)) : Tendsto f cofinite (𝓝 0) := by
  simpa [cocompact_eq_cofinite] using zero_at_infty f

/-- A family on a discrete space tending to zero along the cofinite filter, as a continuous
function vanishing at infinity. -/
def mkOfDiscrete (f : I → β) (hf : Tendsto f cofinite (𝓝 0)) : C₀(I, β) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by rwa [cocompact_eq_cofinite]

/-- `mkOfDiscrete f hf` has underlying family `f`. -/
@[simp]
theorem coe_mkOfDiscrete (f : I → β) (hf : Tendsto f cofinite (𝓝 0)) :
    ⇑(mkOfDiscrete f hf) = f := (rfl)

/-- `mkOfDiscrete` recovers every function vanishing at infinity on a discrete space. -/
@[simp]
theorem mkOfDiscrete_coe (f : C₀(I, β)) : mkOfDiscrete f f.tendsto_cofinite = f := (rfl)

/-- Replacing the coordinates outside a set `S` by zero preserves vanishing at infinity. -/
theorem tendsto_indicator_cofinite (S : Set I) (f : C₀(I, β)) :
    Tendsto (S.indicator f) cofinite (𝓝 0) := by
  classical
  exact (f.tendsto_cofinite.if' tendsto_const_nhds (p := fun i ↦ i ∈ S)).congr
    fun i ↦ (Set.indicator_apply S f i).symm

variable [DecidableEq I]

/-- The coordinate vector `single i b` of `C₀(I, β)`: the family with value `b` at `i` and zero
elsewhere. -/
def single (i : I) (b : β) : C₀(I, β) :=
  mkOfDiscrete (Pi.single i b) <| tendsto_const_nhds.congr' <|
    (eventually_cofinite_ne i).mono fun _ hj ↦ by simp [hj]

/-- `single i b` has underlying family `Pi.single i b`. -/
@[simp]
theorem coe_single (i : I) (b : β) : ⇑(single i b) = Pi.single i b := (rfl)

/-- The coordinates of `single i b`. -/
theorem single_apply (i j : I) (b : β) : single i b j = if j = i then b else 0 :=
  Pi.single_apply i b j

/-- `single i b` takes the value `b` at `i`. -/
theorem single_eq_same (i : I) (b : β) : single i b i = b := by simp

/-- `single i b` vanishes away from `i`. -/
theorem single_eq_of_ne {i j : I} (h : j ≠ i) (b : β) : single i b j = 0 := by simp [h]

/-- The coordinate vector with value zero is zero. -/
@[simp]
theorem single_zero (i : I) : single i (0 : β) = 0 := by ext; simp

/-- The coordinate vector at a fixed index is injective in its entry. -/
theorem single_injective (i : I) : Function.Injective (single i : β → C₀(I, β)) :=
  fun x y h ↦ by simpa using congr($h i)

/-- A coordinate vector vanishes exactly when its entry does. -/
@[simp]
theorem single_eq_zero_iff {i : I} {b : β} : single i b = 0 ↔ b = 0 :=
  (single_injective i).eq_iff' (single_zero i)

end Zero

section Algebra

variable [DecidableEq I] [TopologicalSpace β]

/-- `single i` is additive. -/
theorem single_add [AddZeroClass β] [ContinuousAdd β] (i : I) (b c : β) :
    single i (b + c) = single i b + single i c := by
  ext; simp [Pi.single_add]

/-- The coordinate vector of a negation is the negated coordinate vector. -/
theorem single_neg [AddGroup β] [IsTopologicalAddGroup β] (i : I) (b : β) :
    single i (-b) = -single i b := by
  ext; simp [Pi.single_neg]

/-- The coordinate vector of a difference is the difference of coordinate vectors. -/
theorem single_sub [AddGroup β] [IsTopologicalAddGroup β] (i : I) (b c : β) :
    single i (b - c) = single i b - single i c := by
  ext; simp [Pi.single_sub]

/-- `single i` commutes with scalar multiplication. -/
theorem single_smul {R : Type*} [Zero β] [SMulZeroClass R β] [ContinuousConstSMul R β] (i : I)
    (r : R) (b : β) : single i (r • b) = r • single i b := by
  ext j; by_cases h : j = i <;> simp [h]

/-- In `C₀(I, R)`, the coordinate vector `single i r` is `r` times the unit vector
`single i 1`. -/
theorem smul_single_one {R : Type*} [TopologicalSpace R] [MulZeroOneClass R]
    [ContinuousConstSMul R R] (i : I) (r : R) :
    r • single i (1 : R) = single i r := by
  rw [← single_smul, smul_eq_mul, mul_one]

/-- A finite sum of coordinate vectors agrees with the given family on the summation set and
vanishes outside it. -/
theorem sum_single_apply [AddCommMonoid β] [ContinuousAdd β] (b : I → β) (s : Finset I) (j : I) :
    (∑ i ∈ s, single i (b i)) j = if j ∈ s then b j else 0 := by
  simp [Finset.sum_apply, Pi.single_apply]

end Algebra

section Normed

variable [SeminormedAddCommGroup β]

/-- A coordinate vector has the norm of its nonzero entry. -/
@[simp]
theorem norm_single [DecidableEq I] (i : I) (b : β) : ‖single i b‖ = ‖b‖ := by
  refine le_antisymm ((norm_le (norm_nonneg b)).2 fun j ↦ ?_) ?_
  · by_cases h : j = i <;> simp [h]
  · simpa using norm_coe_le_norm (single i b) i

/-- A finite sum of coordinate vectors at distinct coordinates has the maximum of their norms as
its norm; the empty sum has norm zero. -/
theorem nnnorm_sum_single [DecidableEq I] (s : Finset I) (b : I → β) :
    ‖∑ i ∈ s, single i (b i)‖₊ = s.sup fun i ↦ ‖b i‖₊ := by
  refine le_antisymm ?_ (Finset.sup_le fun i hi ↦ ?_)
  · rw [← NNReal.coe_le_coe, coe_nnnorm, norm_le (NNReal.coe_nonneg _)]
    intro j
    rw [sum_single_apply]
    split_ifs with hj
    · exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun i ↦ ‖b i‖₊) hj)
    · simp
  · rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    simpa [sum_single_apply, hi] using norm_coe_le_norm (∑ i ∈ s, single i (b i)) i

/-- **The sup norm is attained**: on a nonempty discrete index, some coordinate of `f ∈ C₀(I, β)`
has norm `‖f‖`. This covers every nonzero `f`, whose index type is necessarily nonempty. -/
theorem exists_norm_coe_eq_norm [Nonempty I] (f : C₀(I, β)) : ∃ i, ‖f i‖ = ‖f‖ := by
  obtain ⟨i, hi⟩ := f.tendsto_cofinite.exists_forall_norm_le
  exact ⟨i, le_antisymm (norm_coe_le_norm f i) ((norm_le (norm_nonneg _)).2 hi)⟩

section

variable [DecidableEq I]

/-- **Coordinate expansion**: every `f ∈ C₀(I, β)` is the unconditional sum of its coordinate
vectors `single i (f i)`. -/
theorem hasSum_single (f : C₀(I, β)) : HasSum (fun i ↦ single i (f i)) f := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hfin : {j | ¬‖f j‖ < ε / 2}.Finite := eventually_cofinite.1 <|
    (by simpa using f.tendsto_cofinite.norm : Tendsto (fun j ↦ ‖f j‖) cofinite (𝓝 0))
      |>.eventually_lt_const (half_pos hε)
  refine ⟨hfin.toFinset, fun s hs ↦ ?_⟩
  rw [dist_eq_norm]
  refine ((norm_le (half_pos hε).le).2 fun j ↦ ?_).trans_lt (half_lt_self hε)
  by_cases hj : j ∈ s
  · simpa [sum_single_apply, hj] using (half_pos hε).le
  · have : ‖f j‖ < ε / 2 := not_not.1 fun h ↦ hj (hs (by simpa using h))
    simpa [sum_single_apply, hj] using this.le

/-- Continuous linear maps out of `C₀(I, β)` agreeing on all coordinate vectors are equal. -/
theorem continuousLinearMap_ext {R M : Type*} [Semiring R] [Module R β] [ContinuousConstSMul R β]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [T2Space M]
    {φ ψ : C₀(I, β) →L[R] M} (h : ∀ i b, φ (single i b) = ψ (single i b)) : φ = ψ := by
  ext f
  exact ((hasSum_single f).mapL φ).unique (by simpa only [h] using (hasSum_single f).mapL ψ)

end

/-- **Finite-support density**: the finitely supported families are dense in `C₀(I, β)`. -/
theorem dense_setOf_finite_support : Dense {f : C₀(I, β) | (Function.support f).Finite} := by
  classical
  exact fun f ↦ mem_closure_of_tendsto (hasSum_single f) <| Eventually.of_forall fun s ↦
    s.finite_toSet.subset fun j hj ↦ by
      by_contra h
      exact hj (by simp only [sum_single_apply]; simp [Finset.mem_coe.not.1 h])

end Normed

/-- On an infinite index type, the coordinate vectors `single i b` with a fixed nonzero value `b`
do not tend to zero in norm along the cofinite filter. In particular the unit coordinate vectors
of `c₀` are not norm null. -/
theorem not_tendsto_single_cofinite [NormedAddCommGroup β] [DecidableEq I] [Infinite I] {b : β}
    (hb : b ≠ 0) : ¬ Tendsto (fun i : I ↦ single i b) cofinite (𝓝 0) := fun h ↦ by
  have h1 := h.norm
  simp only [norm_single, norm_zero] at h1
  exact hb (norm_eq_zero.1 (tendsto_const_nhds_iff.1 h1))

section Ring

variable {R : Type*} [SeminormedRing R] [DecidableEq I]

/-- **Coordinate expansion in the unit vectors**: every `f ∈ C₀(I, R)` is the unconditional sum
`∑ i, f i • single i 1`. -/
theorem hasSum_smul_single_one (f : C₀(I, R)) : HasSum (fun i ↦ f i • single i (1 : R)) f := by
  simpa only [smul_single_one] using hasSum_single f

/-- The unit vectors `single i 1` span a dense submodule of `C₀(I, R)`. -/
theorem dense_span_single_one :
    Dense (Submodule.span R (Set.range fun i : I ↦ single i (1 : R)) : Set C₀(I, R)) :=
  fun f ↦ mem_closure_of_tendsto (hasSum_smul_single_one f) <| Eventually.of_forall fun _ ↦
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Continuous linear maps out of `C₀(I, R)` agreeing on the unit vectors `single i 1` are
equal. -/
theorem continuousLinearMap_ext_single_one {M : Type*} [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [T2Space M] {φ ψ : C₀(I, R) →L[R] M}
    (h : ∀ i, φ (single i 1) = ψ (single i 1)) : φ = ψ :=
  continuousLinearMap_ext fun i r ↦ by rw [← smul_single_one, map_smul, map_smul, h]

end Ring

section Indicator

/-! ### Coordinate projections -/

variable [SeminormedAddCommGroup β]

private theorem norm_mkOfDiscrete_indicator_le (S : Set I) (f : C₀(I, β)) :
    ‖mkOfDiscrete (S.indicator f) (tendsto_indicator_cofinite S f)‖ ≤ ‖f‖ := by
  refine (norm_le (norm_nonneg f)).2 fun i ↦ ?_
  rw [coe_mkOfDiscrete]
  exact norm_indicator_le_norm_self f i |>.trans (norm_coe_le_norm f i)

variable (R : Type*) [Semiring R] [Module R β] [ContinuousConstSMul R β]

/-- The **coordinate projection** onto a set `S` of indices: the continuous linear map sending
`f` to the family `S.indicator f`, which keeps the coordinates in `S` and replaces the others by
zero. It has norm at most one (`norm_indicatorCLM_apply_le`), and for finite `S` it is the
partial sum of the coordinate expansion over `S` (`indicatorCLM_finset_apply`). -/
noncomputable def indicatorCLM (S : Set I) : C₀(I, β) →L[R] C₀(I, β) :=
  -- LinearMap.mkContinuous requires ring scalars, so attach continuity directly for semirings.
  let L : C₀(I, β) →ₗ[R] C₀(I, β) :=
    { toFun f := mkOfDiscrete (S.indicator f) (tendsto_indicator_cofinite S f)
      map_add' f g := by ext i; by_cases hi : i ∈ S <;> simp [hi]
      map_smul' c f := by ext i; by_cases hi : i ∈ S <;> simp [hi] }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun f ↦ by
      simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using
        norm_mkOfDiscrete_indicator_le S f }

variable {R}

@[simp]
theorem coe_indicatorCLM (S : Set I) (f : C₀(I, β)) : ⇑(indicatorCLM R S f) = S.indicator f :=
  (rfl)

/-- The coordinate projections have norm at most one. -/
theorem norm_indicatorCLM_apply_le (S : Set I) (f : C₀(I, β)) : ‖indicatorCLM R S f‖ ≤ ‖f‖ :=
  norm_mkOfDiscrete_indicator_le S f

@[simp]
theorem indicatorCLM_univ :
    (indicatorCLM R Set.univ : C₀(I, β) →L[R] C₀(I, β)) = ContinuousLinearMap.id R _ := by
  ext; simp

@[simp]
theorem indicatorCLM_empty : (indicatorCLM R ∅ : C₀(I, β) →L[R] C₀(I, β)) = 0 := by
  ext; simp

/-- The projections onto a set of indices and onto its complement add up to the identity. -/
theorem indicatorCLM_add_indicatorCLM_compl (S : Set I) :
    (indicatorCLM R S + indicatorCLM R Sᶜ : C₀(I, β) →L[R] C₀(I, β)) =
      ContinuousLinearMap.id R _ := by
  ext f i
  by_cases hi : i ∈ S <;> simp [hi]

/-- For a finite set `s`, the coordinate projection onto `s` is the partial sum of the coordinate
expansion over `s`. -/
theorem indicatorCLM_finset_apply [DecidableEq I] (s : Finset I) (f : C₀(I, β)) :
    indicatorCLM R (s : Set I) f = ∑ i ∈ s, single i (f i) := by
  ext j
  simp [sum_single_apply, Set.indicator_apply]

/-- The coordinate projection of `C₀(I, R)` onto a finite set of indices has finite rank: its
range lies in the span of the corresponding unit vectors. -/
theorem isFiniteRank_indicatorCLM {R : Type*} [SeminormedRing R] (s : Finset I) :
    ((indicatorCLM R (s : Set I) : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)).IsFiniteRank := by
  classical
  refine LinearMap.isFiniteRank_iff_forall_mem.2 ⟨Submodule.span R ((single · (1 : R)) '' s),
    Submodule.fg_span (s.finite_toSet.image _), fun f ↦ ?_⟩
  rw [ContinuousLinearMap.coe_coe, indicatorCLM_finset_apply]
  exact Submodule.sum_mem _ fun i hi ↦ smul_single_one i (f i) ▸
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

end Indicator

/-! ### Changes of index -/

section Comparison

variable {J R E F : Type*} [TopologicalSpace J] [DiscreteTopology J]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

section Semiring

variable [Semiring R] [Module R E] [ContinuousConstSMul R E] [Module R F]
  [ContinuousConstSMul R F]

/-- Reindexing sends coordinate vectors to coordinate vectors. -/
@[simp]
theorem congrLeft_single [DecidableEq I] [DecidableEq J] (e : I ≃ₜ J) (i : I) (b : E) :
    congrLeft R E e (single i b) = single (e i) b := by
  ext j
  simp [Pi.single_apply, e.symm_apply_eq]

/-- A bounded coefficient map sends coordinate vectors to coordinate vectors. -/
@[simp]
theorem compLeft_single [DecidableEq I] (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (i : I) (b : E) : compLeft u hu (single i b) = single i (u b) := by
  ext j
  by_cases h : j = i <;> simp [h]

variable (R E) in
/-- **Disjoint sums of index types.** Restriction to the two summands identifies
`C₀(I ⊕ J, E)` isometrically with the product `C₀(I, E) × C₀(J, E)`, which carries the max
norm. -/
def sumEquiv : C₀(I ⊕ J, E) ≃ₗᵢ[R] C₀(I, E) × C₀(J, E) where
  toFun f :=
    (mkOfDiscrete (f ∘ Sum.inl) (f.tendsto_cofinite.comp Sum.inl_injective.tendsto_cofinite),
      mkOfDiscrete (f ∘ Sum.inr) (f.tendsto_cofinite.comp Sum.inr_injective.tendsto_cofinite))
  invFun g := mkOfDiscrete (Sum.elim g.1 g.2) fun _ hs ↦
    Set.finite_preimage_inl_and_inr.1 ⟨g.1.tendsto_cofinite hs, g.2.tendsto_cofinite hs⟩
  left_inv f := by ext (_ | _) <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    have hl := f.tendsto_cofinite.comp Sum.inl_injective.tendsto_cofinite
    have hr := f.tendsto_cofinite.comp Sum.inr_injective.tendsto_cofinite
    rw [Prod.norm_def]
    refine le_antisymm (max_le ?_ ?_) ((norm_le (by positivity)).2 ?_)
    · exact (norm_le (norm_nonneg f)).2 fun i ↦ norm_coe_le_norm f (Sum.inl i)
    · exact (norm_le (norm_nonneg f)).2 fun j ↦ norm_coe_le_norm f (Sum.inr j)
    · rintro (i | j)
      · exact le_max_of_le_left (norm_coe_le_norm (mkOfDiscrete (f ∘ Sum.inl) hl) i)
      · exact le_max_of_le_right (norm_coe_le_norm (mkOfDiscrete (f ∘ Sum.inr) hr) j)

/-- The first component of `sumEquiv R E f` is the restriction of `f` to the left summand. -/
@[simp]
theorem coe_sumEquiv_fst (f : C₀(I ⊕ J, E)) : ⇑(sumEquiv R E f).1 = f ∘ Sum.inl := (rfl)

/-- The second component of `sumEquiv R E f` is the restriction of `f` to the right summand. -/
@[simp]
theorem coe_sumEquiv_snd (f : C₀(I ⊕ J, E)) : ⇑(sumEquiv R E f).2 = f ∘ Sum.inr := (rfl)

/-- The inverse of `sumEquiv` glues the two components. -/
@[simp]
theorem coe_sumEquiv_symm (g : C₀(I, E) × C₀(J, E)) :
    ⇑((sumEquiv R E).symm g) = Sum.elim g.1 g.2 := (rfl)

/-- A coordinate vector on the left summand has zero right component. -/
@[simp]
theorem sumEquiv_single_inl [DecidableEq I] [DecidableEq J] (i : I) (b : E) :
    sumEquiv R E (single (Sum.inl i : I ⊕ J) b) = (single i b, 0) := by
  ext j
  · simp [Pi.single_apply]
  · simp

/-- A coordinate vector on the right summand has zero left component. -/
@[simp]
theorem sumEquiv_single_inr [DecidableEq I] [DecidableEq J] (j : J) (b : E) :
    sumEquiv R E (single (Sum.inr j : I ⊕ J) b) = (0, single j b) := by
  ext i
  · simp
  · simp [Pi.single_apply]

/-- Splitting a disjoint sum commutes with the coordinatewise action of a bounded coefficient
map. -/
theorem sumEquiv_compLeft (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (f : C₀(I ⊕ J, E)) :
    sumEquiv R F (compLeft u hu f) = Prod.map (compLeft u hu) (compLeft u hu) (sumEquiv R E f) := by
  ext <;> simp

variable (R E) in
/-- **Finite blocks.** For a finite index type `I`, every family `I → E` vanishes at infinity,
and `C₀(I, E)` is isometric to the finite product `I → E` with its sup norm. -/
def equivFunOnFintype [Fintype I] : C₀(I, E) ≃ₗᵢ[R] (I → E) where
  toFun f := f
  invFun g := mkOfDiscrete g (by rw [cofinite_eq_bot]; exact tendsto_bot)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg f)).2 (norm_coe_le_norm f))
    ((norm_le (norm_nonneg _)).2 fun i ↦ norm_le_pi_norm (⇑f) i)

/-- `equivFunOnFintype R E f` is the underlying family of `f`. -/
@[simp]
theorem equivFunOnFintype_apply [Fintype I] (f : C₀(I, E)) : equivFunOnFintype R E f = ⇑f := (rfl)

/-- The inverse of `equivFunOnFintype` has underlying family `g`. -/
@[simp]
theorem coe_equivFunOnFintype_symm [Fintype I] (g : I → E) :
    ⇑((equivFunOnFintype R E).symm g) = g := (rfl)

/-- The identification of `C₀(I, E)` with `I → E` for finite `I` commutes with the coordinatewise
action of a bounded coefficient map. -/
theorem equivFunOnFintype_compLeft [Fintype I] (u : E →L[R] F)
    (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (f : C₀(I, E)) :
    equivFunOnFintype R F (compLeft u hu f) = u ∘ equivFunOnFintype R E f := by
  ext; simp

section Curry

/-- The rows `j ↦ f (i, j)` of a family `f` vanishing at infinity on `I × J` tend to zero
uniformly: their sup norms tend to zero along the cofinite filter on `I`. -/
private theorem tendsto_cofinite_curry (f : C₀(I × J, E)) :
    Tendsto (fun i ↦ mkOfDiscrete (fun j ↦ f (i, j))
      (f.tendsto_cofinite.comp (Prod.mk_right_injective i).tendsto_cofinite)) cofinite (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  -- The coordinates of norm at least `ε / 2` lie in finitely many rows; every other row has norm
  -- at most `ε / 2`.
  have hS : {p : I × J | ¬‖f p‖ < ε / 2}.Finite :=
    eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 f.tendsto_cofinite _ (half_pos hε))
  refine eventually_cofinite.2 ((hS.image Prod.fst).subset fun i hi ↦ ?_)
  by_contra hni
  refine hi (((norm_le (half_pos hε).le).2 fun j ↦ ?_).trans_lt (half_lt_self hε))
  rw [coe_mkOfDiscrete]
  exact not_lt.1 fun h ↦ hni ⟨(i, j), not_lt.2 h.le, rfl⟩

/-- A family of families vanishing at infinity whose sup norms vanish at infinity defines a family
vanishing at infinity on `I × J`. -/
private theorem tendsto_cofinite_uncurry (g : C₀(I, C₀(J, E))) :
    Tendsto (fun p : I × J ↦ g p.1 p.2) cofinite (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ eventually_cofinite.2 ?_
  -- A coordinate of norm at least `ε` lies in a row of norm at least `ε`; there are finitely many
  -- such rows, each with finitely many such coordinates.
  have hA : {i | ¬‖g i‖ < ε}.Finite :=
    eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 g.tendsto_cofinite ε hε)
  have hB (i : I) : {j | ¬‖g i j‖ < ε}.Finite :=
    eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 (g i).tendsto_cofinite ε hε)
  refine (hA.prod (hA.biUnion fun i _ ↦ hB i)).subset fun p hp ↦ ?_
  have h1 : p.1 ∈ {i | ¬‖g i‖ < ε} := fun h ↦ hp ((norm_coe_le_norm _ _).trans_lt h)
  exact ⟨h1, Set.mem_biUnion h1 hp⟩

variable (R E) in
/-- **Currying.** A family on `I × J` vanishing at infinity is the same as a family on `I` of
families on `J` vanishing at infinity: `C₀(I × J, E)` is isometric to `C₀(I, C₀(J, E))` by
`f ↦ (i ↦ (j ↦ f (i, j)))`. -/
noncomputable def curryEquiv : C₀(I × J, E) ≃ₗᵢ[R] C₀(I, C₀(J, E)) where
  toFun f := mkOfDiscrete _ (tendsto_cofinite_curry f)
  invFun g := mkOfDiscrete _ (tendsto_cofinite_uncurry g)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    refine le_antisymm ((norm_le (norm_nonneg f)).2 fun i ↦
      (norm_le (norm_nonneg f)).2 fun j ↦ norm_coe_le_norm f (i, j))
      ((norm_le (norm_nonneg _)).2 fun p ↦ ?_)
    exact (norm_coe_le_norm (mkOfDiscrete _ (tendsto_cofinite_curry f) p.1) p.2).trans
      (norm_coe_le_norm (mkOfDiscrete _ (tendsto_cofinite_curry f)) p.1)

/-- `curryEquiv R E f i j = f (i, j)`. -/
@[simp]
theorem curryEquiv_apply_apply (f : C₀(I × J, E)) (i : I) (j : J) :
    curryEquiv R E f i j = f (i, j) := (rfl)

/-- The inverse of `curryEquiv` uncurries. -/
@[simp]
theorem curryEquiv_symm_apply (g : C₀(I, C₀(J, E))) (p : I × J) :
    (curryEquiv R E).symm g p = g p.1 p.2 := (rfl)

/-- Currying a coordinate vector gives a coordinate vector of coordinate vectors. -/
@[simp]
theorem curryEquiv_single [DecidableEq I] [DecidableEq J] (i : I) (j : J) (b : E) :
    curryEquiv R E (single (i, j) b) = single i (single j b) := by
  ext i' j'
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]

/-- Currying commutes with the coordinatewise action of a bounded coefficient map. -/
theorem curryEquiv_compLeft (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (f : C₀(I × J, E)) :
    curryEquiv R F (compLeft u hu f) =
      compLeft (compLeft u hu) (exists_norm_compLeft_apply_le u hu) (curryEquiv R E f) := by
  ext; simp

end Curry

end Semiring

end Comparison

end ZeroAtInftyContinuousMap
