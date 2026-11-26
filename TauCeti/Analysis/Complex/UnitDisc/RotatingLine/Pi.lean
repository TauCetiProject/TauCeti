/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Isomorphism

/-!
# The augmented disc problem in `ℂⁿ` with rotating-line boundary values

Let `D` be the open unit disc, `0 < α < 1` and `ι` a finite type, so that `ι → ℂ` is `ℂⁿ` for
`n = card ι`. For an integer `k`, the elements `u` of `C^{1,α}(D, ι → ℂ)` whose continuous
extension to the closed disc takes its boundary values in the totally real subspaces
`e^{ikθ/2} ℝ^ι`, that is `u w = w ^ k • star (u w)` for `w` on the unit circle, form a closed real
subspace `X_k` of `C^{1,α}(D, ι → ℂ)` (`TauCeti.rotatingLinePiSubspace`), hence a Banach space.
An element lies in `X_k` exactly when each of its coordinates lies in the scalar subspace
`TauCeti.rotatingLineSubspace k α`.

The augmented Cauchy–Riemann operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` acts on each coordinate
separately (`TauCeti.augmentedConjWirtingerDerivL_compLeftL`), so the scalar theory of
`TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Isomorphism` applies coordinatewise. On `X_k` with
`k ≥ 3` the operator is onto `C^{0,α}(D, ι → ℂ) × (ι → ℂ) × (ι → ℂ)`, and for `k = 3` it is
one-to-one. By the open mapping theorem it is then a Banach isomorphism
`X_3 ≃L[ℝ] C^{0,α}(D, ι → ℂ) × (ι → ℂ) × (ι → ℂ)` (`TauCeti.rotatingLinePiAugmentedEquiv`), and its
inverse gives the a priori estimate
`‖u‖_{C^{1,α}} ≤ C (‖∂u/∂(conj z)‖_{C^α} + |u 0| + |∂ₛu(0)|)` on `X_3`
(`TauCeti.exists_norm_le_mul_norm_augmentedConjWirtingerDerivL_pi`). This is the normalized
real-boundary disc solver of the linear theory of holomorphic discs, for the totally real boundary
condition `e^{3iθ/2} ℝⁿ`, of Maslov index `3n`.

## Main declarations

* `TauCeti.rotatingLinePiSubspace`: the closed subspace `X_k` of `C^{1,α}(D, ι → ℂ)`, with the
  boundary characterization `TauCeti.mem_rotatingLinePiSubspace_iff` and the coordinatewise one
  `TauCeti.mem_rotatingLinePiSubspace_iff_forall`.
* `TauCeti.exists_mem_rotatingLinePiSubspace_augmentedConjWirtingerDerivL_eq`: surjectivity on
  `X_k` for `k ≥ 3`.
* `TauCeti.injOn_augmentedConjWirtingerDerivL_pi`: injectivity on `X_3`.
* `TauCeti.rotatingLinePiAugmentedEquiv`: the Banach isomorphism
  `X_3 ≃L[ℝ] C^{0,α}(D, ι → ℂ) × (ι → ℂ) × (ι → ℂ)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the boundary value problem on the disc).
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric Set CkHolderSpaceOn
open scoped ComplexConjugate NNReal

variable {k : ℤ} {α : ℝ≥0} {ι : Type*} [Fintype ι]

/-! ### The boundary subspace -/

variable (k α ι) in
/-- The closed subspace of `C^{1,α}(D, ι → ℂ)`, for the open unit disc `D`, of the elements `u`
whose continuous extension to the closed disc takes its boundary values in `e^{ikθ/2} ℝ^ι`, that is
`u w = w ^ k • star (u w)` for `w` on the unit circle: the elements each of whose coordinates lies
in `TauCeti.rotatingLineSubspace k α`. -/
def rotatingLinePiSubspace : Submodule ℝ (CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)) :=
  ⨅ i : ι, (rotatingLineSubspace k α).comap (compLeftL 1 α (unitBallOpens ℂ)
    ((ContinuousLinearMap.proj (R := ℂ) i : (ι → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)).toLinearMap

/-- An element of `C^{1,α}(D, ι → ℂ)` lies in `rotatingLinePiSubspace k α ι` exactly when each of
its coordinates lies in `rotatingLineSubspace k α`. -/
theorem mem_rotatingLinePiSubspace_iff_forall {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)} :
    u ∈ rotatingLinePiSubspace k α ι ↔ ∀ i, compLeftL 1 α (unitBallOpens ℂ)
      ((ContinuousLinearMap.proj (R := ℂ) i : (ι → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) u ∈
        rotatingLineSubspace k α := by
  simp [rotatingLinePiSubspace, Submodule.mem_iInf]

/-- An element of `C^{1,α}(D, ι → ℂ)` lies in `rotatingLinePiSubspace k α ι` exactly when its
extension to the closed disc satisfies `u w = w ^ k • star (u w)` on the unit circle. -/
theorem mem_rotatingLinePiSubspace_iff {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)} :
    u ∈ rotatingLinePiSubspace k α ι ↔
      ∀ w ∈ sphere (0 : ℂ) 1, u.closureExtend w = w ^ k • star (u.closureExtend w) := by
  have hcl {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) : w ∈ closure (unitBallOpens ℂ : Set ℂ) :=
    closure_unitBallOpens ℂ ▸ sphere_subset_closedBall hw
  simp only [mem_rotatingLinePiSubspace_iff_forall, mem_rotatingLineSubspace_iff]
  refine ⟨fun h w hw ↦ funext fun i ↦ ?_, fun h i w hw ↦ ?_⟩
  · have := h i w hw
    rw [closureExtend_compLeftL (convex_unitBallOpens ℂ) _ _ (hcl hw)] at this
    simpa using this
  · rw [closureExtend_compLeftL (convex_unitBallOpens ℂ) _ _ (hcl hw)]
    simpa using congrFun (h w hw) i

/-- The rotating-line boundary condition defines a closed subspace of `C^{1,α}(D, ι → ℂ)`. -/
theorem isClosed_rotatingLinePiSubspace :
    IsClosed
      (rotatingLinePiSubspace k α ι : Set (CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ))) := by
  rw [rotatingLinePiSubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦
    (isClosed_rotatingLineSubspace k α).preimage (ContinuousLinearMap.continuous _)

/-- The rotating-line boundary subspace of `C^{1,α}(D, ι → ℂ)` is a Banach space. -/
instance : CompleteSpace (rotatingLinePiSubspace k α ι) :=
  isClosed_rotatingLinePiSubspace.completeSpace_coe

/-! ### Reduction to coordinates -/

/-- The `i`-th coordinate projection of `ι → ℂ`, as a real-linear map. -/
private abbrev projL (i : ι) : (ι → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) i : (ι → ℂ) →L[ℂ] ℂ).restrictScalars ℝ

/-- The `i`-th coordinate projection on the target of the augmented operator. -/
private abbrev projAugL (i : ι) :
    HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℂ) × (ι → ℂ) →L[ℝ]
      HolderSpace α (unitBallOpens ℂ) ℂ × ℂ × ℂ :=
  (HolderSpace.compLeftL (projL i)).prodMap ((projL i).prodMap (projL i))

/-- A point of the target of the augmented operator is determined by its coordinates. -/
private theorem eq_of_forall_projAugL_eq
    {y y' : HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℂ) × (ι → ℂ)}
    (h : ∀ i, projAugL i y = projAugL i y') : y = y' := by
  simp only [ContinuousLinearMap.coe_prodMap', Prod.ext_iff] at h
  refine Prod.ext (HolderSpace.ext fun x ↦ funext fun i ↦ ?_)
    (Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_))
  · simpa using congrArg (· x) (h i).1
  · simpa using (h i).2.1
  · simpa using (h i).2.2

/-- The augmented operator of a coordinate is the coordinate of the augmented operator. -/
private theorem augmentedConjWirtingerDerivL_compLeftL_projL (i : ι)
    (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)) :
    augmentedConjWirtingerDerivL α ℂ (compLeftL 1 α (unitBallOpens ℂ) (projL i) u) =
      projAugL i (augmentedConjWirtingerDerivL α (ι → ℂ) u) :=
  augmentedConjWirtingerDerivL_compLeftL _ u

/-! ### Surjectivity and injectivity -/

/-- **Existence with prescribed centre value and first jet in `ℂⁿ`.** Let `k ≥ 3` and
`0 < α < 1`. For every `α`-Hölder forcing `f` on the open unit disc with values in `ι → ℂ` and all
`a b : ι → ℂ`, some element `u` of `C^{1,α}(D, ι → ℂ)` with boundary values in `e^{ikθ/2} ℝ^ι` has
`∂u/∂(conj z) = f`, `u 0 = a` and `∂ₛu(0) = b`. -/
theorem exists_mem_rotatingLinePiSubspace_augmentedConjWirtingerDerivL_eq (hk : 3 ≤ k)
    (hα0 : 0 < α) (hα1 : α < 1)
    (y : HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℂ) × (ι → ℂ)) :
    ∃ u ∈ rotatingLinePiSubspace k α ι, augmentedConjWirtingerDerivL α (ι → ℂ) u = y := by
  classical
  -- Solve the scalar problem for each coordinate of the data.
  choose U hU hUy using fun i ↦
    exists_mem_rotatingLineSubspace_augmentedConjWirtingerDerivL_eq hk hα0 hα1 (projAugL i y)
  -- Put the scalar solutions in their coordinates.
  set u := ∑ i, compLeftL 1 α (unitBallOpens ℂ) (.single ℝ (fun _ ↦ ℂ) i) (U i)
  have hu (i : ι) : compLeftL 1 α (unitBallOpens ℂ) (projL i) u = U i :=
    compLeftL_proj_sum_compLeftL_single U i
  refine ⟨u, mem_rotatingLinePiSubspace_iff_forall.2 fun i ↦ hu i ▸ hU i,
    eq_of_forall_projAugL_eq fun i ↦ ?_⟩
  rw [← augmentedConjWirtingerDerivL_compLeftL_projL, hu, hUy]

/-- **Uniqueness for Maslov index three in `ℂⁿ`.** On the elements of `C^{1,α}(D, ι → ℂ)` with
boundary values in `e^{3iθ/2} ℝ^ι`, the augmented operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` is
injective. -/
theorem injOn_augmentedConjWirtingerDerivL_pi :
    InjOn (augmentedConjWirtingerDerivL α (ι → ℂ)) (rotatingLinePiSubspace 3 α ι) := by
  intro u hu v hv huv
  refine ext_compLeftL_proj fun i ↦ ?_
  change compLeftL 1 α _ (projL i) u = compLeftL 1 α _ (projL i) v
  refine injOn_augmentedConjWirtingerDerivL
    (mem_rotatingLinePiSubspace_iff_forall.1 hu i) (mem_rotatingLinePiSubspace_iff_forall.1 hv i) ?_
  rw [augmentedConjWirtingerDerivL_compLeftL_projL, augmentedConjWirtingerDerivL_compLeftL_projL,
    huv]

/-! ### The Banach isomorphism -/

variable (ι) in
/-- **The normalized real-boundary disc solver in `ℂⁿ`.** For `0 < α < 1`, the augmented
Cauchy–Riemann operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` is a Banach isomorphism from the
elements of `C^{1,α}(D, ι → ℂ)` with boundary values in `e^{3iθ/2} ℝ^ι` onto
`C^{0,α}(D, ι → ℂ) × (ι → ℂ) × (ι → ℂ)`. -/
def rotatingLinePiAugmentedEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    rotatingLinePiSubspace 3 α ι ≃L[ℝ]
      HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℂ) × (ι → ℂ) :=
  ContinuousLinearEquiv.ofBijective
    (augmentedConjWirtingerDerivL α (ι → ℂ) ∘L (rotatingLinePiSubspace 3 α ι).subtypeL)
    (LinearMap.ker_eq_bot.2 fun u v huv ↦ Subtype.ext
      (injOn_augmentedConjWirtingerDerivL_pi u.property v.property huv))
    (LinearMap.range_eq_top.2 fun y ↦ by
      obtain ⟨u, hu, rfl⟩ :=
        exists_mem_rotatingLinePiSubspace_augmentedConjWirtingerDerivL_eq le_rfl hα0 hα1 y
      exact ⟨⟨u, hu⟩, rfl⟩)

/-- The isomorphism `TauCeti.rotatingLinePiAugmentedEquiv` is the augmented operator. -/
@[simp]
theorem rotatingLinePiAugmentedEquiv_apply (hα0 : 0 < α) (hα1 : α < 1)
    (u : rotatingLinePiSubspace 3 α ι) :
    rotatingLinePiAugmentedEquiv ι hα0 hα1 u = augmentedConjWirtingerDerivL α (ι → ℂ) u :=
  (rfl)

variable (ι) in
/-- **The Schauder estimate for the normalized disc problem in `ℂⁿ`.** For `0 < α < 1` there is a
constant `C` such that every element `u` of `C^{1,α}(D, ι → ℂ)` with boundary values in
`e^{3iθ/2} ℝ^ι` satisfies `‖u‖ ≤ C ‖(∂u/∂(conj z), u 0, ∂ₛu(0))‖`. -/
theorem exists_norm_le_mul_norm_augmentedConjWirtingerDerivL_pi (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C, ∀ u ∈ rotatingLinePiSubspace 3 α ι,
      ‖u‖ ≤ C * ‖augmentedConjWirtingerDerivL α (ι → ℂ) u‖ := by
  set e := rotatingLinePiAugmentedEquiv ι hα0 hα1
  refine ⟨‖e.symm.toContinuousLinearMap‖, fun u hu ↦ ?_⟩
  have h := e.symm.toContinuousLinearMap.le_opNorm (e ⟨u, hu⟩)
  rw [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply, rotatingLinePiAugmentedEquiv_apply] at h
  -- The norm on the subspace is the norm of `C^{1,α}(D, ι → ℂ)`.
  exact h

end TauCeti
