/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.Complex.UnitDisc.TotallyRealBoundary.Basic
public import TauCeti.Analysis.Holder.OpenSet.ConjWirtinger
public import TauCeti.Analysis.Normed.Module.Ball.Opens
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Fredholm
import TauCeti.Analysis.Fredholm.Criteria

/-!
# The disc with a maximal totally real boundary condition in Hölder spaces

Let `E` be a finite-dimensional complex normed space, `Λ` a real subspace of `E` which is maximal
totally real, `E = Λ ⊕ i Λ`, and `0 < α < 1`. For the open unit disc `D`, the elements `u` of the
Hölder space `C^{1,α}(D, E)` whose continuous extension to the closed disc takes its boundary values
in `Λ` form a closed real subspace `X_Λ` (`TauCeti.totallyRealBoundarySubspace Λ α`), hence a
Banach space. This file proves that the operator

`u ↦ (∂u/∂(conj z), u 1)`

is a Banach isomorphism `X_Λ ≃L[ℝ] C^{0,α}(D, E) × Λ`
(`TauCeti.IsMaximalTotallyReal.totallyRealBoundaryEvalEquiv`). This is the linearization at a
constant disc `u ≡ x` of the Cauchy–Riemann equation for discs with boundary on a totally real
submanifold `L` with `T_x L = Λ`, for instance a Lagrangian submanifold of `ℂⁿ`
(`TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_tames`), combined with evaluation at
the boundary marked point `1`. Consequently:

* **Surjectivity.** The Cauchy–Riemann operator `∂/∂(conj z) : X_Λ → C^{0,α}(D, E)`
  (`TauCeti.totallyRealConjWirtingerDerivL`) is onto
  (`TauCeti.IsMaximalTotallyReal.totallyRealConjWirtingerDerivL_surjective`).
* **The kernel.** Its kernel consists of the elements that are constant on `D`
  (`TauCeti.IsMaximalTotallyReal.mem_ker_totallyRealConjWirtingerDerivL_iff_forall_eq`),
  and evaluation at the boundary point `1` is an isomorphism from it onto `Λ`
  (`TauCeti.IsMaximalTotallyReal.totallyRealConjWirtingerDerivKerEquiv`).
* **Fredholm property and index.** The operator is Fredholm
  (`TauCeti.IsMaximalTotallyReal.isFredholm_totallyRealConjWirtingerDerivL`) of index
  `n = dim_ℂ E` (`TauCeti.IsMaximalTotallyReal.index_totallyRealConjWirtingerDerivL`), which is
  `n χ(D) + μ` for the Maslov index `μ = 0` of a constant boundary condition.

The isomorphism is transported from the case `E = ℂ^ι`, `Λ = ℝ^ι` of
`TauCeti.rotatingLinePiZeroEvalEquiv`: in the coordinates of a real basis of `Λ`, which is a
complex basis of `E` (`TauCeti.IsMaximalTotallyReal.complexBasis`), the subspace `Λ` becomes `ℝ^ι`.
The coordinate map is complex linear, so it commutes with `∂/∂(conj z)`.

The set-level counterpart of these statements, for `C²` forcing and with no Banach topology, is
`TauCeti.IsMaximalTotallyReal.existsUnique_conjWirtingerDeriv_eq_and_mem`.

## Main declarations

* `TauCeti.totallyRealBoundarySubspace Λ α`: the closed subspace `X_Λ` of `C^{1,α}(D, E)`, with
  `TauCeti.mem_totallyRealBoundarySubspace_iff`.
* `TauCeti.totallyRealConjWirtingerDerivL Λ α`: the operator `∂/∂(conj z) : X_Λ → C^{0,α}(D, E)`.
* `TauCeti.IsMaximalTotallyReal.totallyRealBoundaryEvalEquiv`: the Banach isomorphism
  `X_Λ ≃L[ℝ] C^{0,α}(D, E) × Λ`.
* `TauCeti.IsMaximalTotallyReal.index_totallyRealConjWirtingerDerivL`: the index `dim_ℂ E`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the boundary value problem on the disc,
  Theorem C.1.10).
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric Module Set CkHolderSpaceOn
open scoped ComplexConjugate NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Λ : Submodule ℝ E}
  {α : ℝ≥0}

/-! ### The boundary subspace -/

/-- The closed subspace of `C^{1,α}(D, E)`, for the open unit disc `D`, of the elements `u` whose
continuous extension to the closed disc takes its values on the unit circle in the real subspace
`Λ` of `E`. -/
def totallyRealBoundarySubspace (Λ : Submodule ℝ E) (α : ℝ≥0) :
    Submodule ℝ (CkHolderSpaceOn 1 α (unitBallOpens ℂ) E) :=
  ⨅ w : sphere (0 : ℂ) 1, Λ.comap (closureEvalL (k := 0) (convex_unitBallOpens ℂ)
    (closure_unitBallOpens ℂ ▸ sphere_subset_closedBall w.property)).toLinearMap

/-- An element of `C^{1,α}(D, E)` lies in `totallyRealBoundarySubspace Λ α` exactly when its
extension to the closed disc takes its values on the unit circle in `Λ`. -/
theorem mem_totallyRealBoundarySubspace_iff {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) E} :
    u ∈ totallyRealBoundarySubspace Λ α ↔ ∀ w ∈ sphere (0 : ℂ) 1, u.closureExtend w ∈ Λ := by
  simp [totallyRealBoundarySubspace, Submodule.mem_iInf]

/-- For a closed real subspace `Λ`, the boundary condition `u(∂D) ⊆ Λ` defines a closed subspace
of `C^{1,α}(D, E)`. -/
theorem isClosed_totallyRealBoundarySubspace (hΛ : IsClosed (Λ : Set E)) :
    IsClosed (totallyRealBoundarySubspace Λ α : Set (CkHolderSpaceOn 1 α (unitBallOpens ℂ) E)) := by
  rw [totallyRealBoundarySubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun w ↦ hΛ.preimage (ContinuousLinearMap.continuous _)

/-- For a finite-dimensional complex space `E`, the boundary subspace `X_Λ` is a Banach space. -/
instance [FiniteDimensional ℂ E] : CompleteSpace (totallyRealBoundarySubspace Λ α) :=
  (isClosed_totallyRealBoundarySubspace
    (Submodule.isClosed_of_finiteDimensional Λ)).completeSpace_coe

/-! ### The operator -/

variable (Λ α) in
/-- The Cauchy–Riemann operator `u ↦ ∂u/∂(conj z)` on the closed subspace `X_Λ` of
`C^{1,α}(D, E)` of the maps with boundary values in `Λ`, with values in `C^{0,α}(D, E)`, for the
open unit disc `D`. -/
def totallyRealConjWirtingerDerivL :
    totallyRealBoundarySubspace Λ α →L[ℝ] HolderSpace α (unitBallOpens ℂ) E :=
  conjWirtingerDerivL α (unitBallOpens ℂ) E ∘L (totallyRealBoundarySubspace Λ α).subtypeL

/-- The operator `TauCeti.totallyRealConjWirtingerDerivL` is the Cauchy–Riemann operator of
`C^{1,α}(D, E)` on the elements of `X_Λ`. -/
@[simp]
theorem totallyRealConjWirtingerDerivL_apply (u : totallyRealBoundarySubspace Λ α) :
    totallyRealConjWirtingerDerivL Λ α u = conjWirtingerDerivL α (unitBallOpens ℂ) E u :=
  (rfl)

/-- An element of `X_Λ` lies in the kernel of the Cauchy–Riemann operator on `X_Λ` exactly when
its Cauchy–Riemann derivative vanishes. -/
theorem mem_ker_totallyRealConjWirtingerDerivL_iff
    {u : totallyRealBoundarySubspace Λ α} :
    u ∈ (totallyRealConjWirtingerDerivL Λ α).ker ↔
      conjWirtingerDerivL α (unitBallOpens ℂ) E u = 0 :=
  LinearMap.mem_ker

variable (Λ α) in
/-- The operator `u ↦ (∂u/∂(conj z), u 1)` on `X_Λ`, before it is shown to be an isomorphism. -/
private def totallyRealBoundaryEvalL :
    totallyRealBoundarySubspace Λ α →L[ℝ] HolderSpace α (unitBallOpens ℂ) E × Λ :=
  (totallyRealConjWirtingerDerivL Λ α).prod
    ((closureEvalL (k := 0) (convex_unitBallOpens ℂ) (mem_closure_unitBallOpens.2 norm_one.le) ∘L
      (totallyRealBoundarySubspace Λ α).subtypeL).codRestrict Λ fun u ↦ by
        simpa using mem_totallyRealBoundarySubspace_iff.1 u.property 1 (by simp))

private theorem totallyRealBoundaryEvalL_apply (u : totallyRealBoundarySubspace Λ α) :
    totallyRealBoundaryEvalL Λ α u = (conjWirtingerDerivL α (unitBallOpens ℂ) E u,
      ⟨(u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) E).closureExtend 1,
        mem_totallyRealBoundarySubspace_iff.1 u.property 1 (by simp)⟩) :=
  Prod.ext (totallyRealConjWirtingerDerivL_apply u) (Subtype.ext (closureEvalL_apply _ _ _))

/-! ### Coordinates in which `Λ` is `ℝ^ι` -/

namespace IsMaximalTotallyReal

variable [FiniteDimensional ℂ E]
  (hΛ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) Λ)

/-- The complex coordinates of `E` in a real basis of `Λ`. -/
private abbrev coordL : E ≃L[ℂ] (Fin (finrank ℝ Λ) → ℂ) :=
  (hΛ.complexBasis (Module.finBasis ℝ Λ)).equivFunL

/-- The coordinates `coordL hΛ`, as a real-linear map. -/
private abbrev coordRL : E →L[ℝ] (Fin (finrank ℝ Λ) → ℂ) :=
  (coordL hΛ).toContinuousLinearMap.restrictScalars ℝ

omit [CompleteSpace E] in
include hΛ in
/-- A vector lies in `Λ` exactly when its coordinates are real. -/
private theorem mem_iff_coordL (x : E) :
    x ∈ Λ ↔ ∀ i, coordL hΛ x i = conj (coordL hΛ x i) := by
  rw [hΛ.mem_iff_forall_conj_complexBasis_repr (Module.finBasis ℝ Λ)]
  exact forall_congr' fun i ↦ eq_comm

omit [CompleteSpace E] in
include hΛ in
/-- Two vectors of `Λ` whose coordinates have the same real parts are equal. -/
private theorem eq_of_re_coordL_eq {x y : E} (hx : x ∈ Λ) (hy : y ∈ Λ)
    (h : ∀ i, (coordL hΛ x i).re = (coordL hΛ y i).re) : x = y := by
  refine (coordL hΛ).injective (funext fun i ↦ ?_)
  rw [← conj_eq_iff_re.1 ((mem_iff_coordL hΛ x).1 hx i).symm,
    ← conj_eq_iff_re.1 ((mem_iff_coordL hΛ y).1 hy i).symm, h i]

include hΛ in
/-- In coordinates, the extension to the closed disc of an element of `C^{1,α}(D, E)` takes its
boundary values in `Λ` exactly when the extension of its coordinates takes real boundary values. -/
private theorem mem_totallyRealBoundarySubspace_iff_compLeftL_mem
    {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) E} :
    u ∈ totallyRealBoundarySubspace Λ α ↔
      compLeftL (coordRL hΛ) u ∈ rotatingLinePiSubspace (Fin (finrank ℝ Λ)) 0 α := by
  rw [mem_totallyRealBoundarySubspace_iff, mem_rotatingLinePiSubspace_iff]
  refine forall₂_congr fun w hw ↦ ?_
  rw [closureExtend_compLeftL (convex_unitBallOpens ℂ) _ u
    (closure_unitBallOpens ℂ ▸ sphere_subset_closedBall hw), mem_iff_coordL hΛ]
  simp

/-- The coordinates of an element of `X_Λ`, an element of `C^{1,α}(D, ℂ^ι)` with boundary values
in `ℝ^ι`. -/
private def toPi : totallyRealBoundarySubspace Λ α →L[ℝ]
    rotatingLinePiSubspace (Fin (finrank ℝ Λ)) 0 α :=
  (compLeftL (coordRL hΛ) ∘L (totallyRealBoundarySubspace Λ α).subtypeL).codRestrict _ fun u ↦
    (mem_totallyRealBoundarySubspace_iff_compLeftL_mem hΛ).1 u.property

private theorem coe_toPi_apply (u : totallyRealBoundarySubspace Λ α) :
    (toPi hΛ u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (Fin (finrank ℝ Λ) → ℂ)) =
      compLeftL (coordRL hΛ) u :=
  (rfl)

/-- In coordinates, the operator `u ↦ (∂u/∂(conj z), u 1)` is the operator
`u ↦ (∂u/∂(conj z), Re u(1))` of `TauCeti.rotatingLinePiZeroEvalEquiv`. -/
private theorem rotatingLinePiZeroEvalEquiv_toPi (hα0 : 0 < α) (hα1 : α < 1)
    (u : totallyRealBoundarySubspace Λ α) :
    rotatingLinePiZeroEvalEquiv (Fin (finrank ℝ Λ)) hα0 hα1 (toPi hΛ u) =
      (HolderSpace.compLeftL (coordRL hΛ) (totallyRealBoundaryEvalL Λ α u).1,
        fun i ↦ (coordL hΛ (totallyRealBoundaryEvalL Λ α u).2 i).re) := by
  rw [rotatingLinePiZeroEvalEquiv_apply, totallyRealBoundaryEvalL_apply]
  refine Prod.ext ?_ (funext fun i ↦ ?_)
  · exact conjWirtingerDerivL_compLeftL (coordL hΛ).toContinuousLinearMap _
  · rw [coe_toPi_apply,
      closureExtend_compLeftL (convex_unitBallOpens ℂ) _ _
        (mem_closure_unitBallOpens.2 norm_one.le)]
    simp

omit [CompleteSpace E] in
/-- `C^{0,α}` functions with the same coordinates are equal. -/
private theorem eq_of_compLeftL_coordRL_eq {f g : HolderSpace α (unitBallOpens ℂ) E}
    (h : HolderSpace.compLeftL (coordRL hΛ) f = HolderSpace.compLeftL (coordRL hΛ) g) : f = g :=
  HolderSpace.ext fun z ↦ (coordL hΛ).injective (by
    simpa using congr($h z))

/-! ### The isomorphism -/

/-- **Maximal totally real boundary values with a boundary marked point.** For a maximal totally
real subspace `Λ` of a finite-dimensional complex space `E` and `0 < α < 1`, the operator
`u ↦ (∂u/∂(conj z), u 1)` is a Banach isomorphism from the elements of `C^{1,α}(D, E)` with
boundary values in `Λ` onto `C^{0,α}(D, E) × Λ`. This is the linearization of the Cauchy–Riemann
equation at a constant disc with boundary on a totally real submanifold `L` with `T_x L = Λ`,
combined with evaluation at the boundary marked point `1`. -/
def totallyRealBoundaryEvalEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    totallyRealBoundarySubspace Λ α ≃L[ℝ] HolderSpace α (unitBallOpens ℂ) E × Λ :=
  ContinuousLinearEquiv.ofBijective (totallyRealBoundaryEvalL Λ α)
    (LinearMap.ker_eq_bot.2 fun u v huv ↦ by
      rw [ContinuousLinearMap.coe_coe] at huv
      -- In coordinates, this is the injectivity of `rotatingLinePiZeroEvalEquiv`.
      have h : rotatingLinePiZeroEvalEquiv _ hα0 hα1 (toPi hΛ u) =
          rotatingLinePiZeroEvalEquiv _ hα0 hα1 (toPi hΛ v) := by
        rw [rotatingLinePiZeroEvalEquiv_toPi, rotatingLinePiZeroEvalEquiv_toPi, huv]
      have hc := congr_arg Subtype.val ((rotatingLinePiZeroEvalEquiv _ hα0 hα1).injective h)
      refine Subtype.ext (CkHolderSpaceOn.ext fun z ↦ (coordL hΛ).injective ?_)
      simpa [coe_toPi_apply] using congr($hc z))
    (LinearMap.range_eq_top.2 fun y ↦ by
      obtain ⟨f, v⟩ := y
      -- Solve the problem in coordinates and transport the solution back to `E`.
      set u' := (rotatingLinePiZeroEvalEquiv (Fin (finrank ℝ Λ)) hα0 hα1).symm
        (HolderSpace.compLeftL (coordRL hΛ) f, fun i ↦ (coordL hΛ v i).re)
      have hcomp : compLeftL (coordRL hΛ)
          (compLeftL ((coordL hΛ).symm.toContinuousLinearMap.restrictScalars ℝ) u'.val) = u'.val :=
        CkHolderSpaceOn.ext fun z ↦ by simp
      have hmem : compLeftL ((coordL hΛ).symm.toContinuousLinearMap.restrictScalars ℝ) u'.val ∈
          totallyRealBoundarySubspace Λ α :=
        (mem_totallyRealBoundarySubspace_iff_compLeftL_mem hΛ).2 (by rw [hcomp]; exact u'.property)
      have hu : toPi hΛ ⟨_, hmem⟩ = u' := Subtype.ext hcomp
      have h := rotatingLinePiZeroEvalEquiv_toPi hΛ hα0 hα1 ⟨_, hmem⟩
      rw [hu, ContinuousLinearEquiv.apply_symm_apply, Prod.mk.injEq] at h
      refine ⟨⟨_, hmem⟩, Prod.ext (eq_of_compLeftL_coordRL_eq hΛ h.1.symm)
        (Subtype.ext (eq_of_re_coordL_eq hΛ (totallyRealBoundaryEvalL Λ α _).2.property
          v.property fun i ↦ (congr_fun h.2 i).symm))⟩)

/-- The isomorphism `TauCeti.IsMaximalTotallyReal.totallyRealBoundaryEvalEquiv` is the operator
`u ↦ (∂u/∂(conj z), u 1)`. -/
private theorem totallyRealBoundaryEvalEquiv_apply (hα0 : 0 < α) (hα1 : α < 1)
    (u : totallyRealBoundarySubspace Λ α) :
    hΛ.totallyRealBoundaryEvalEquiv hα0 hα1 u = totallyRealBoundaryEvalL Λ α u := by
  rw [totallyRealBoundaryEvalEquiv, ← ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_ofBijective]

/-- The first component of `TauCeti.IsMaximalTotallyReal.totallyRealBoundaryEvalEquiv` is the
Cauchy–Riemann operator. -/
@[simp]
theorem totallyRealBoundaryEvalEquiv_apply_fst (hα0 : 0 < α) (hα1 : α < 1)
    (u : totallyRealBoundarySubspace Λ α) :
    (hΛ.totallyRealBoundaryEvalEquiv hα0 hα1 u).1 =
      conjWirtingerDerivL α (unitBallOpens ℂ) E u := by
  rw [totallyRealBoundaryEvalEquiv_apply, totallyRealBoundaryEvalL_apply]

/-- The second component of `TauCeti.IsMaximalTotallyReal.totallyRealBoundaryEvalEquiv` is the
value at the boundary point `1`. -/
@[simp]
theorem coe_totallyRealBoundaryEvalEquiv_apply_snd (hα0 : 0 < α) (hα1 : α < 1)
    (u : totallyRealBoundarySubspace Λ α) :
    ((hΛ.totallyRealBoundaryEvalEquiv hα0 hα1 u).2 : E) =
      (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) E).closureExtend 1 := by
  rw [totallyRealBoundaryEvalEquiv_apply, totallyRealBoundaryEvalL_apply]

/-! ### Surjectivity, kernel and index -/

include hΛ in
/-- **Surjectivity.** For a maximal totally real subspace `Λ` and `0 < α < 1`, every `α`-Hölder
forcing on the open unit disc is `∂u/∂(conj z)` for some `u ∈ C^{1,α}(D, E)` with boundary values
in `Λ`. -/
theorem totallyRealConjWirtingerDerivL_surjective (hα0 : 0 < α) (hα1 : α < 1) :
    Function.Surjective (totallyRealConjWirtingerDerivL Λ α) := fun f ↦
  ⟨(hΛ.totallyRealBoundaryEvalEquiv hα0 hα1).symm (f, 0), by
    rw [totallyRealConjWirtingerDerivL_apply, ← totallyRealBoundaryEvalEquiv_apply_fst hΛ hα0 hα1,
      ContinuousLinearEquiv.apply_symm_apply]⟩

include hΛ in
/-- **The kernel is the constants.** For a maximal totally real subspace `Λ`, an element of `X_Λ`
lies in the kernel of the Cauchy–Riemann operator exactly when it is constant on the open unit
disc, equal to its value at the boundary point `1`. -/
theorem mem_ker_totallyRealConjWirtingerDerivL_iff_forall_eq
    {u : totallyRealBoundarySubspace Λ α} :
    u ∈ (totallyRealConjWirtingerDerivL Λ α).ker ↔ ∀ z,
      (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) E) z =
        (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) E).closureExtend 1 := by
  set v : CkHolderSpaceOn 1 α (unitBallOpens ℂ) E := u.val
  rw [mem_ker_totallyRealConjWirtingerDerivL_iff]
  refine ⟨fun hu z ↦ ?_, fun hu ↦ HolderSpace.ext fun z ↦ ?_⟩
  · have hd := coe_unitBallOpens ℂ ▸
      diffContOnCl_closureExtend_of_conjWirtingerDerivL_eq_zero (convex_unitBallOpens ℂ) hu
    rw [← closureExtend_apply]
    exact hΛ.eqOn_closedBall_const_of_diffContOnCl hd
      (mem_totallyRealBoundarySubspace_iff.1 u.property)
      (ball_subset_closedBall (mem_unitBallOpens_iff_mem_ball.1 z.property))
  · -- Near `z`, the extension by zero of `v` is the constant `v 1`.
    have hz : v.extend =ᶠ[nhds (z : ℂ)] fun _ ↦ v.closureExtend 1 := by
      filter_upwards [(unitBallOpens ℂ).isOpen.mem_nhds z.property] with y hy
      rw [v.extend_apply_of_mem hy, hu]
    rw [conjWirtingerDerivL_apply v z hz, HolderSpace.zero_apply,
      (differentiableAt_const _).conjWirtingerDeriv_eq_zero, zero_apply]

/-- **Evaluation at the boundary mark identifies the kernel with `Λ`.** For a maximal totally real
subspace `Λ` and `0 < α < 1`, evaluation at the boundary point `1` is a real-linear isomorphism
from the kernel of the Cauchy–Riemann operator on `X_Λ` onto `Λ`. -/
def totallyRealConjWirtingerDerivKerEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    (totallyRealConjWirtingerDerivL Λ α).ker ≃ₗ[ℝ] Λ :=
  LinearEquiv.ofBijective (LinearMap.snd ℝ _ Λ ∘ₗ
      (hΛ.totallyRealBoundaryEvalEquiv hα0 hα1).toLinearEquiv.toLinearMap ∘ₗ
        (totallyRealConjWirtingerDerivL Λ α).ker.subtype)
    -- The ascription keeps the type `Function.Bijective` (rather than `∧`) on the proof, so that
    -- `LinearEquiv.ofBijective_apply` applies to this definition.
    (show Function.Bijective _ from
      ⟨fun u v huv ↦ Subtype.ext <| (hΛ.totallyRealBoundaryEvalEquiv hα0 hα1).injective <| by
        -- Both elements have vanishing Cauchy–Riemann derivative and the same value at `1`.
        refine Prod.ext ?_ huv
        rw [totallyRealBoundaryEvalEquiv_apply_fst, totallyRealBoundaryEvalEquiv_apply_fst,
          mem_ker_totallyRealConjWirtingerDerivL_iff.1 u.property,
          mem_ker_totallyRealConjWirtingerDerivL_iff.1 v.property],
      fun w ↦ ⟨⟨(hΛ.totallyRealBoundaryEvalEquiv hα0 hα1).symm (0, w),
        mem_ker_totallyRealConjWirtingerDerivL_iff.2 (by
          rw [← totallyRealBoundaryEvalEquiv_apply_fst hΛ hα0 hα1,
            ContinuousLinearEquiv.apply_symm_apply])⟩, by simp⟩⟩)

/-- The isomorphism `TauCeti.IsMaximalTotallyReal.totallyRealConjWirtingerDerivKerEquiv` is
evaluation at the boundary point `1`. -/
@[simp]
theorem coe_totallyRealConjWirtingerDerivKerEquiv_apply (hα0 : 0 < α) (hα1 : α < 1)
    (u : (totallyRealConjWirtingerDerivL Λ α).ker) :
    (hΛ.totallyRealConjWirtingerDerivKerEquiv hα0 hα1 u : E) =
      ((u : totallyRealBoundarySubspace Λ α) :
        CkHolderSpaceOn 1 α (unitBallOpens ℂ) E).closureExtend 1 := by
  simp [totallyRealConjWirtingerDerivKerEquiv]

include hΛ in
/-- The kernel of the Cauchy–Riemann operator on `X_Λ` has real dimension `n = dim_ℂ E`. -/
theorem finrank_ker_totallyRealConjWirtingerDerivL (hα0 : 0 < α) (hα1 : α < 1) :
    finrank ℝ (totallyRealConjWirtingerDerivL Λ α).ker = finrank ℂ E :=
  (hΛ.totallyRealConjWirtingerDerivKerEquiv hα0 hα1).finrank_eq.trans
    hΛ.finrank_eq_finrank_complex

include hΛ in
/-- **The Cauchy–Riemann operator with maximal totally real boundary values is Fredholm.** For a
maximal totally real subspace `Λ` and `0 < α < 1`, the operator `∂/∂(conj z) : X_Λ → C^{0,α}(D, E)`
is a Fredholm operator. -/
theorem isFredholm_totallyRealConjWirtingerDerivL (hα0 : 0 < α) (hα1 : α < 1) :
    (totallyRealConjWirtingerDerivL Λ α).IsFredholm :=
  have := (hΛ.totallyRealConjWirtingerDerivKerEquiv hα0 hα1).symm.finiteDimensional
  .of_surjective (hΛ.totallyRealConjWirtingerDerivL_surjective hα0 hα1)

include hΛ in
/-- **The Riemann–Roch formula on the disc for a constant boundary condition.** For a maximal
totally real subspace `Λ` of `E` and `0 < α < 1`, the Fredholm index of
`∂/∂(conj z) : X_Λ → C^{0,α}(D, E)` is `n = dim_ℂ E = n χ(D) + μ`, for the Maslov index `μ = 0` of
the constant loop of real subspaces `Λ`. -/
theorem index_totallyRealConjWirtingerDerivL (hα0 : 0 < α) (hα1 : α < 1) :
    (totallyRealConjWirtingerDerivL Λ α).index = finrank ℂ E := by
  rw [ContinuousLinearMap.index_of_surjective _
      (hΛ.totallyRealConjWirtingerDerivL_surjective hα0 hα1),
    hΛ.finrank_ker_totallyRealConjWirtingerDerivL hα0 hα1]

end IsMaximalTotallyReal

end TauCeti
