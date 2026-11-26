/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Isomorphism

/-!
# The normalized real-boundary disc solver on `ℂⁿ`

Let `D` be the open unit disc, `0 < α < 1` and `ι` a finite index type, so that `ι → ℂ` is a
copy of `ℂⁿ`. For an integer `k`, the elements `u` of `C^{1,α}(D, ι → ℂ)` whose continuous
extension to the closed disc takes boundary values in the totally real subspaces
`e^{ikθ/2} ℝ^ι`, that is

`u w i = w ^ k * conj (u w i)` for every `w` on the unit circle and every coordinate `i`,

form a closed real subspace `X_k` of `C^{1,α}(D, ι → ℂ)` (`TauCeti.rotatingLinePiSubspace`). It
consists of the maps whose coordinates lie in the rank-one subspace `TauCeti.rotatingLineSubspace`.
The augmented Cauchy–Riemann operator

`u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))`

of `TauCeti.augmentedConjWirtingerDerivL` commutes with the coordinate projections, which are
complex linear, so it acts coordinatewise. The rank-one existence and uniqueness theorems of
`TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Isomorphism` therefore give the same statements on
`ℂ^ι`: for `k ≥ 3` the augmented operator maps `X_k` onto `C^{0,α}(D, ι → ℂ) × (ι → ℂ) × (ι → ℂ)`,
and for the normalization `k = 3` it is injective on `X_3`. By the open mapping theorem it is a
Banach isomorphism

`X_3 ≃L[ℝ] C^{0,α}(D, ι → ℂ) × (ι → ℂ) × (ι → ℂ)`

(`TauCeti.rotatingLinePiAugmentedEquiv`), whose inverse gives the a priori estimate
`‖u‖_{C^{1,α}} ≤ C (‖∂u/∂(conj z)‖_{C^α} + |u 0| + |∂ₛu(0)|)` on `X_3`. This is the normalized
real-boundary disc solver in the Hölder setting, for the boundary condition `e^{3iθ/2} ℝⁿ` of a
disc with Maslov index `3n`. Its inverse is the one that a Neumann series perturbs to invert the
operators `∂u/∂(conj z) + A(z) ∂u/∂z + B(z) u` with small Hölder coefficients.

## Main declarations

* `TauCeti.rotatingLinePiSubspace`: the closed subspace `X_k` of `C^{1,α}(D, ι → ℂ)`, with
  `TauCeti.mem_rotatingLinePiSubspace_iff`.
* `TauCeti.exists_mem_rotatingLinePiSubspace_augmentedConjWirtingerDerivL_eq`: surjectivity on
  `X_k` for `k ≥ 3`.
* `TauCeti.injOn_augmentedConjWirtingerDerivL_pi`: injectivity on `X_3`.
* `TauCeti.rotatingLinePiAugmentedEquiv`: the Banach isomorphism
  `X_3 ≃L[ℝ] C^{0,α}(D, ι → ℂ) × (ι → ℂ) × (ι → ℂ)`.
* `TauCeti.exists_norm_le_mul_norm_augmentedConjWirtingerDerivL_pi`: the a priori estimate.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the boundary value problem on the disc).
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric Set TopologicalSpace CkHolderSpaceOn
open scoped ComplexConjugate NNReal

variable {ι : Type*} [Fintype ι] {k : ℤ} {α : ℝ≥0}

/-! ### The boundary subspace -/

variable (ι k α) in
/-- The closed subspace of `C^{1,α}(D, ι → ℂ)`, for the open unit disc `D`, of the maps each of
whose coordinates lies in `TauCeti.rotatingLineSubspace k α`: their continuous extension to the
closed disc takes boundary values in `e^{ikθ/2} ℝ^ι`, that is `u w i = w ^ k * conj (u w i)` for
`w` on the unit circle (`TauCeti.mem_rotatingLinePiSubspace_iff`). -/
def rotatingLinePiSubspace : Submodule ℝ (CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)) :=
  ⨅ i : ι, (rotatingLineSubspace k α).comap (compLeftL (k := 1) (α := α) (Ω := unitBallOpens ℂ)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ)).toLinearMap

/-- An element of `C^{1,α}(D, ι → ℂ)` lies in `rotatingLinePiSubspace ι k α` exactly when each of
its coordinates lies in `rotatingLineSubspace k α`. -/
theorem mem_rotatingLinePiSubspace_iff_forall_compLeftL_mem
    {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)} :
    u ∈ rotatingLinePiSubspace ι k α ↔ ∀ i : ι,
      compLeftL ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ) u ∈
        rotatingLineSubspace k α := by
  simp [rotatingLinePiSubspace, Submodule.mem_iInf]

/-- An element of `C^{1,α}(D, ι → ℂ)` lies in `rotatingLinePiSubspace ι k α` exactly when its
extension to the closed disc satisfies `u w i = w ^ k * conj (u w i)` on the unit circle, for
every coordinate `i`. -/
theorem mem_rotatingLinePiSubspace_iff {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)} :
    u ∈ rotatingLinePiSubspace ι k α ↔ ∀ w ∈ sphere (0 : ℂ) 1, ∀ i : ι,
      u.closureExtend w i = w ^ k * conj (u.closureExtend w i) := by
  have h {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) (i : ι) :
      (compLeftL ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ)
        u).closureExtend w = u.closureExtend w i :=
    closureExtend_compLeftL (convex_unitBallOpens ℂ) _ u
      (closure_unitBallOpens ℂ ▸ sphere_subset_closedBall hw)
  simp only [mem_rotatingLinePiSubspace_iff_forall_compLeftL_mem, mem_rotatingLineSubspace_iff]
  exact ⟨fun H w hw i ↦ h hw i ▸ H i w hw, fun H i w hw ↦ (h hw i).symm ▸ H w hw i⟩

/-- The boundary condition `e^{ikθ/2} ℝ^ι` defines a closed subspace of `C^{1,α}(D, ι → ℂ)`. -/
theorem isClosed_rotatingLinePiSubspace (ι : Type*) [Fintype ι] (k : ℤ) (α : ℝ≥0) :
    IsClosed (rotatingLinePiSubspace ι k α :
      Set (CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ))) := by
  rw [rotatingLinePiSubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦
    (isClosed_rotatingLineSubspace k α).preimage (compLeftL _).continuous

/-- The boundary subspace `X_k` of `C^{1,α}(D, ι → ℂ)` is a Banach space. -/
instance : CompleteSpace (rotatingLinePiSubspace ι k α) :=
  (isClosed_rotatingLinePiSubspace ι k α).completeSpace_coe

/-! ### The augmented operator acts coordinatewise -/

/-- The augmented operator on `C^{1,α}(D, ι → ℂ)` takes the value `y` exactly when, for every
coordinate `i`, the augmented operator takes the `i`-th coordinate of `u` to the `i`-th
coordinate of `y`. -/
private theorem augmentedConjWirtingerDerivL_pi_eq_iff
    {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)}
    {y : HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℂ) × (ι → ℂ)} :
    augmentedConjWirtingerDerivL α (ι → ℂ) u = y ↔ ∀ i : ι,
      augmentedConjWirtingerDerivL α ℂ
        (compLeftL ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ)
          u) =
        (HolderSpace.compLeftL
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ) y.1,
          y.2.1 i, y.2.2 i) := by
  obtain ⟨f, a, b⟩ := y
  simp only [augmentedConjWirtingerDerivL_compLeftL]
  simp only [augmentedConjWirtingerDerivL_apply, Prod.mk.injEq, ContinuousLinearMap.proj_apply]
  constructor
  · rintro ⟨rfl, rfl, rfl⟩ i
    exact ⟨rfl, rfl, rfl⟩
  · intro h
    exact ⟨HolderSpace.ext_compLeftL_proj fun i ↦ (h i).1, funext fun i ↦ (h i).2.1,
      funext fun i ↦ (h i).2.2⟩

/-! ### Surjectivity and injectivity -/

/-- **Existence with prescribed centre value and first jet on `ℂ^ι`.** Let `k ≥ 3` and
`0 < α < 1`. For every `α`-Hölder forcing `f` on the open unit disc with values in `ι → ℂ` and all
`a b : ι → ℂ`, some element `u` of `C^{1,α}(D, ι → ℂ)` with boundary values in `e^{ikθ/2} ℝ^ι`
has `∂u/∂(conj z) = f`, `u 0 = a` and `∂ₛu(0) = b`. -/
theorem exists_mem_rotatingLinePiSubspace_augmentedConjWirtingerDerivL_eq (hk : 3 ≤ k)
    (hα0 : 0 < α) (hα1 : α < 1)
    (y : HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℂ) × (ι → ℂ)) :
    ∃ u ∈ rotatingLinePiSubspace ι k α, augmentedConjWirtingerDerivL α (ι → ℂ) u = y := by
  classical
  -- Solve the rank-one problem in each coordinate.
  choose v hv hLv using fun i : ι ↦
    exists_mem_rotatingLineSubspace_augmentedConjWirtingerDerivL_eq hk hα0 hα1
      (HolderSpace.compLeftL
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ) y.1,
        y.2.1 i, y.2.2 i)
  -- Assemble the coordinates.
  set u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ) := ∑ j : ι,
    compLeftL ((ContinuousLinearMap.single ℂ (fun _ : ι ↦ ℂ) j).restrictScalars ℝ) (v j)
  have hu (i : ι) : compLeftL
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ) u = v i :=
    compLeftL_proj_sum_compLeftL_single v i
  exact ⟨u, mem_rotatingLinePiSubspace_iff_forall_compLeftL_mem.2 fun i ↦ hu i ▸ hv i,
    augmentedConjWirtingerDerivL_pi_eq_iff.2 fun i ↦ by rw [hu i, hLv i]⟩

/-- **Uniqueness for the boundary condition `e^{3iθ/2} ℝ^ι`.** On the elements of
`C^{1,α}(D, ι → ℂ)` with boundary values in `e^{3iθ/2} ℝ^ι`, the augmented operator
`u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` is injective. -/
theorem injOn_augmentedConjWirtingerDerivL_pi :
    InjOn (augmentedConjWirtingerDerivL α (ι → ℂ)) (rotatingLinePiSubspace ι 3 α) := by
  intro u hu v hv huv
  have h (i : ι) := injOn_augmentedConjWirtingerDerivL
    (mem_rotatingLinePiSubspace_iff_forall_compLeftL_mem.1 hu i)
    (mem_rotatingLinePiSubspace_iff_forall_compLeftL_mem.1 hv i)
    ((augmentedConjWirtingerDerivL_pi_eq_iff.1 huv i).trans
      (augmentedConjWirtingerDerivL_pi_eq_iff.1 rfl i).symm)
  exact ext_compLeftL_proj h

/-! ### The Banach isomorphism -/

/-- **The normalized real-boundary disc solver on `ℂ^ι`.** For `0 < α < 1`, the augmented
Cauchy–Riemann operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` is a Banach isomorphism from the
elements of `C^{1,α}(D, ι → ℂ)` with boundary values in `e^{3iθ/2} ℝ^ι` onto
`C^{0,α}(D, ι → ℂ) × (ι → ℂ) × (ι → ℂ)`. -/
def rotatingLinePiAugmentedEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    rotatingLinePiSubspace ι 3 α ≃L[ℝ]
      HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℂ) × (ι → ℂ) :=
  ContinuousLinearEquiv.ofBijective
    (augmentedConjWirtingerDerivL α (ι → ℂ) ∘L (rotatingLinePiSubspace ι 3 α).subtypeL)
    (LinearMap.ker_eq_bot.2 fun u v huv ↦ Subtype.ext
      (injOn_augmentedConjWirtingerDerivL_pi u.property v.property huv))
    (LinearMap.range_eq_top.2 fun y ↦ by
      obtain ⟨u, hu, rfl⟩ :=
        exists_mem_rotatingLinePiSubspace_augmentedConjWirtingerDerivL_eq le_rfl hα0 hα1 y
      exact ⟨⟨u, hu⟩, rfl⟩)

/-- The isomorphism `TauCeti.rotatingLinePiAugmentedEquiv` is the augmented operator. -/
@[simp]
theorem rotatingLinePiAugmentedEquiv_apply (hα0 : 0 < α) (hα1 : α < 1)
    (u : rotatingLinePiSubspace ι 3 α) :
    rotatingLinePiAugmentedEquiv hα0 hα1 u = augmentedConjWirtingerDerivL α (ι → ℂ) u :=
  (rfl)

/-- **The Schauder estimate for the normalized disc problem on `ℂ^ι`.** For `0 < α < 1` there is a
constant `C` such that every element `u` of `C^{1,α}(D, ι → ℂ)` with boundary values in
`e^{3iθ/2} ℝ^ι` satisfies `‖u‖ ≤ C ‖(∂u/∂(conj z), u 0, ∂ₛu(0))‖`. -/
theorem exists_norm_le_mul_norm_augmentedConjWirtingerDerivL_pi (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C, ∀ u ∈ rotatingLinePiSubspace ι 3 α,
      ‖u‖ ≤ C * ‖augmentedConjWirtingerDerivL α (ι → ℂ) u‖ := by
  set e := rotatingLinePiAugmentedEquiv (ι := ι) hα0 hα1
  refine ⟨‖e.symm.toContinuousLinearMap‖, fun u hu ↦ ?_⟩
  have h := e.symm.toContinuousLinearMap.le_opNorm (e ⟨u, hu⟩)
  rw [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply, rotatingLinePiAugmentedEquiv_apply] at h
  -- The norm on the subspace is the norm of `C^{1,α}(D, ι → ℂ)`.
  exact h

end TauCeti
