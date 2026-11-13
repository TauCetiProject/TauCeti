/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Fibration
import Mathlib.LinearAlgebra.Matrix.Dual
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Topology.Connected.Basic

/-!
# The cotangent action on the fibres of a Lagrangian fibration and its period lattice

Let `σ` be a symplectic form on a boundaryless manifold `M`, and let `π : M → B` be a proper
Lagrangian fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianFibration`), with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g)`. The Hamiltonian vector field of a function
`g ∘ π` pulled back from the base is vertical and complete, and along a fibre it only depends on the
differential of `g` there. So a covector `η ∈ T*_b B` acts on the fibre `π⁻¹(b)` by the time-one map
of the flow of `g ∘ π`, for any `g` with `dg_b = η`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianFibration.cotangentFiberAction` and
`IsLagrangianFibration.coe_cotangentFiberAction_apply`). Since pulled-back functions
Poisson-commute, their flows commute and this is an action of the vector group `T*_b B`. It is
constructed from the Hamiltonian flow action
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`) of the coordinates of a chart of `B` at
`b`, pulled back to `M`; the characterization by arbitrary functions `g` shows that it does not
depend on that chart.

For a regular Lagrangian torus fibration
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`), whose fibres are moreover
connected, the topological Liouville–Arnold theorem shows that the action is transitive on each
fibre (`IsLagrangianTorusFibration.exists_cotangentFiberAction_apply_eq`). Its kernel is the
**period lattice** `Λ_b ⊆ T*_b B` (`IsLagrangianTorusFibration.periodLattice`): the stabilizer of
any point of the fibre, a discrete subgroup spanning `T*_b B`, and the orbit map identifies the
fibre with the torus `T*_b B ⧸ Λ_b` (`IsLagrangianTorusFibration.quotientPeriodLatticeHomeomorph`).
These are the fibres of the torus bundle `T*B ⧸ Λ` associated with the fibration. No norm on the
cotangent spaces is chosen, so the lattice property is stated by discreteness, spanning and
compactness of the quotient.

## Main definitions

* `IsLagrangianFibration.cotangentFiberAction`: the action of `T*_b B` on the fibre over `b`.
* `IsLagrangianTorusFibration.periodLattice`: the period lattice `Λ_b ⊆ T*_b B`.
* `IsLagrangianTorusFibration.quotientPeriodLatticeHomeomorph`: the homeomorphism
  `T*_b B ⧸ Λ_b ≃ₜ π⁻¹(b)` given by the orbit map of a point of the fibre.

## Main results

* `IsLagrangianFibration.coe_cotangentFiberAction_apply`: `η` acts by the time-one map of the flow
  of `g ∘ π` for every `C²` function `g` with `dg_b = η`.
* `IsLagrangianTorusFibration.exists_cotangentFiberAction_apply_eq`: the action is transitive on
  each fibre.
* `IsLagrangianTorusFibration.mem_periodLattice_iff`: the period lattice is the stabilizer of any
  point of the fibre.
* `IsLagrangianTorusFibration.discreteTopology_periodLattice`,
  `IsLagrangianTorusFibration.span_periodLattice_eq_top`,
  `IsLagrangianTorusFibration.compactSpace_quotient_periodLattice`: the period lattice is a
  discrete, spanning and cocompact subgroup of `T*_b B`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
-/

public section

open Function Set Module
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

/-! ### Coordinates on the base -/

variable (J)

/-- A smooth map `B → F` with the germ of the extended chart at `b`. -/
private noncomputable def baseChart (b : B) : C^∞⟮J, B; 𝓘(ℝ, F), F⟯ :=
  (exists_contMDiffMap_eventuallyEq_extChartAt (I := J) b).choose

private theorem baseChart_eventuallyEq (b : B) :
    (baseChart J b : B → F) =ᶠ[𝓝 b] extChartAt J b :=
  (exists_contMDiffMap_eventuallyEq_extChartAt (I := J) b).choose_spec

/-- Linear coordinates on the model space of the base. -/
private noncomputable def modelCoord (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- Smooth coordinates on the base, valid near `b`. -/
private noncomputable def baseCoord (b : B) : B → Fin (finrank ℝ F) → ℝ :=
  modelCoord F ∘ baseChart J b

private theorem contMDiff_baseCoord (b : B) :
    ContMDiff J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ (baseCoord J b) :=
  (modelCoord F).contDiff.comp_contMDiff (baseChart J b).contMDiff

private theorem mvfderiv_baseCoord_apply (b : B) (w : TangentSpace J b) :
    mvfderiv J (baseCoord J b) b w = modelCoord F (w : F) := by
  have h := mvfderiv_comp_apply_of_differentiableAt (I := J) (g := (baseChart J b : B → F))
    (φ := (modelCoord F : F → Fin (finrank ℝ F) → ℝ)) (x := b) (modelCoord F).differentiableAt
    ((baseChart J b).contMDiff.mdifferentiableAt (by simp)) w
  rw [(modelCoord F).fderiv,
    mvfderiv_apply_of_eventuallyEq_extChartAt (baseChart_eventuallyEq J b)] at h
  exact h

private theorem exists_isOpen_injOn_baseCoord (b : B) :
    ∃ W : Set B, IsOpen W ∧ b ∈ W ∧ InjOn (baseCoord J b) W := by
  obtain ⟨W, hWsub, hWo, hbW⟩ := mem_nhds_iff.1
    ((baseChart_eventuallyEq J b).and (extChartAt_source_mem_nhds (I := J) b))
  refine ⟨W, hWo, hbW, fun c hc d hd hcd ↦ ?_⟩
  refine (extChartAt J b).injOn (hWsub hc).2 (hWsub hd).2 ?_
  rw [← (hWsub hc).1, ← (hWsub hd).1]
  exact (modelCoord F).injective hcd

variable (F) in
/-- The linear forms `w ↦ wᵢ` of the linear coordinates of `F` form a basis of its dual: the
covector with coordinates `v` is the dot product with `v`, read in the coordinates of `F`. -/
private noncomputable def coordCovector : (Fin (finrank ℝ F) → ℝ) ≃L[ℝ] (F →L[ℝ] ℝ) :=
  ((dotProductEquiv ℝ (Fin (finrank ℝ F))).trans
    ((modelCoord F).toLinearEquiv.dualMap.trans
      LinearMap.toContinuousLinearMap)).toContinuousLinearEquiv

private theorem coordCovector_apply_apply (v : Fin (finrank ℝ F) → ℝ) (w : F) :
    coordCovector F v w = ∑ i, v i * modelCoord F w i :=
  rfl

/-- A linear combination of the base coordinates is a linear form of the base coordinates. -/
private theorem sum_mul_baseCoord_eq_comp (b : B) (v : Fin (finrank ℝ F) → ℝ) :
    (fun c ↦ ∑ i, v i * baseCoord J b c i) =
      ⇑(∑ i, v i • ContinuousLinearMap.proj i : (Fin (finrank ℝ F) → ℝ) →L[ℝ] ℝ) ∘
        baseCoord J b := by
  funext c
  simp

private theorem contMDiff_sum_mul_baseCoord (b : B) (v : Fin (finrank ℝ F) → ℝ) :
    ContMDiff J 𝓘(ℝ) ∞ fun c ↦ ∑ i, v i * baseCoord J b c i := by
  rw [sum_mul_baseCoord_eq_comp]
  exact ContinuousLinearMap.contDiff _ |>.comp_contMDiff (contMDiff_baseCoord J b)

/-- In the base coordinates at `b`, the differential at `b` of `∑ i, vᵢ (baseCoord b)ᵢ` is the
covector with coordinates `v`. -/
private theorem mvfderiv_eq_coordCovector (b : B) (v : Fin (finrank ℝ F) → ℝ) :
    mvfderiv J (fun c ↦ ∑ i, v i * baseCoord J b c i) b = coordCovector F v := by
  set ψ : (Fin (finrank ℝ F) → ℝ) →L[ℝ] ℝ := ∑ i, v i • ContinuousLinearMap.proj i
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [sum_mul_baseCoord_eq_comp, mvfderiv_comp_apply_of_differentiableAt ψ.differentiableAt
    ((contMDiff_baseCoord J b).mdifferentiableAt (by simp)), ψ.fderiv,
    mvfderiv_baseCoord_apply]
  -- `coordCovector F v` is read on the tangent space at `b`.
  change _ = coordCovector F v w
  simp only [ψ, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact (coordCovector_apply_apply v w).symm

variable {J}

namespace IsLagrangianFibration

/-! ### The action of the base coordinates -/

variable (h : hσ.IsLagrangianFibration J π)
include h

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem contMDiff_baseCoord_comp (b : B) :
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ (baseCoord J b ∘ π) :=
  (contMDiff_baseCoord J b).comp h.contMDiff

omit [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem poissonBracket_baseCoord_comp (b : B) (i j : Fin (finrank ℝ F)) (y : M) :
    σ.poissonBracket ((baseCoord J b ∘ π) · i) ((baseCoord J b ∘ π) · j) y = 0 :=
  h.poissonBracket_comp_eq_zero
    ((contMDiff_pi_module_iff.1 (contMDiff_baseCoord J b) i).mdifferentiableAt (by simp))
    ((contMDiff_pi_module_iff.1 (contMDiff_baseCoord J b) j).mdifferentiableAt (by simp))

omit [I.Boundaryless] in
private theorem isCompleteVectorField_baseCoord_comp (hπ : IsProperMap π) (b : B)
    (i : Fin (finrank ℝ F)) :
    IsCompleteVectorField (σ.hamiltonianVectorField ((baseCoord J b ∘ π) · i)) :=
  h.isCompleteVectorField_hamiltonianVectorField_comp hπ
    ((contMDiff_pi_module_iff.1 (contMDiff_baseCoord J b) i).of_le (by simp))

omit [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] [FiniteDimensional ℝ F]
  [IsManifold J ∞ B] [T2Space B] in
/-- The Hamiltonian vector field of a pulled-back `C²` function is `C¹`. -/
private theorem contMDiff_hamiltonianVectorField_comp {g : B → ℝ} (hg : ContMDiff J 𝓘(ℝ) 2 g) :
    ContMDiff I I.tangent 1 fun y ↦
      (⟨y, σ.hamiltonianVectorField (g ∘ π) y⟩ : TangentBundle I M) :=
  hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp)
    (by rw [one_add_one_eq_two]; exact hg.comp (h.contMDiff.of_le (by simp)))

/-- The action of `ℝⁿ` on `M` by the Hamiltonian flows of the base coordinates at `b`, pulled back
to `M`. -/
private noncomputable def coordAction (hσc : σ.IsClosed) (hπ : IsProperMap π) (b : B) :
    (Fin (finrank ℝ F) → ℝ) →+ Additive (M ≃ₘ^∞⟮I, I⟯ M) :=
  (⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowAction (h.contMDiff_baseCoord_comp b)
    (h.poissonBracket_baseCoord_comp b) (h.isCompleteVectorField_baseCoord_comp hπ b)

/-- The vector `v` acts by the time-one map of the flow of `g ∘ π`, for every smooth `g` whose
differential at `π x` is the covector with coordinates `v`. -/
private theorem coordAction_apply_eq_globalFlow (hσc : σ.IsClosed) (hπ : IsProperMap π) (b : B)
    (v : Fin (finrank ℝ F) → ℝ) {x : M} {g : B → ℝ} (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hgv : mvfderiv J g (π x) = mvfderiv J (fun c ↦ ∑ i, v i * baseCoord J b c i) (π x))
    (hv : ContMDiff I I.tangent 1 fun y ↦
      (⟨y, σ.hamiltonianVectorField (g ∘ π) y⟩ : TangentBundle I M))
    (hc : IsCompleteVectorField (σ.hamiltonianVectorField (g ∘ π))) :
    (h.coordAction hσc hπ b v).toMul x = globalFlow _ hv hc 1 x := by
  have hσS : σ.IsSymplectic := ⟨hσc, hσ⟩
  have hk := contMDiff_sum_mul_baseCoord J b v
  have hvk := h.contMDiff_hamiltonianVectorField_comp (hk.of_le (by simp))
  have hck := hσS.isCompleteVectorField_hamiltonianVectorField_sum
    (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
    (h.isCompleteVectorField_baseCoord_comp hπ b) v
  rw [coordAction, ← one_smul ℝ v, hσS.hamiltonianFlowAction_smul_apply_eq_globalFlow _ _ _ v
    hvk hck]
  exact h.globalFlow_hamiltonianVectorField_comp_eq_of_mvfderiv_eq (hk.of_le (by simp)) hg
    hgv.symm hvk hck hv hc 1

/-- The action of the base coordinates preserves the fibres of `π`. -/
private theorem apply_coordAction_apply (hσc : σ.IsClosed) (hπ : IsProperMap π) (b : B)
    (v : Fin (finrank ℝ F) → ℝ) (x : M) :
    π ((h.coordAction hσc hπ b v).toMul x) = π x := by
  have hk := contMDiff_sum_mul_baseCoord J b v
  have hvk := h.contMDiff_hamiltonianVectorField_comp (hk.of_le (by simp))
  have hck := h.isCompleteVectorField_hamiltonianVectorField_comp hπ (hk.of_le (by simp))
  rw [h.coordAction_apply_eq_globalFlow hσc hπ b v (hk.of_le (by simp)) rfl hvk hck,
    globalFlow_apply]
  exact h.apply_maximalIntegralCurve_hamiltonianVectorField_comp (hk.of_le (by simp))
    (hck.mem_maximalIntegralCurveInterval x 1)

/-- The action of the base coordinates at `b` on the fibre over `b`. -/
private noncomputable def coordFiberAction (hσc : σ.IsClosed) (hπ : IsProperMap π) (b : B) :
    (Fin (finrank ℝ F) → ℝ) →+ Additive (Equiv.Perm (π ⁻¹' {b})) where
  toFun v := Additive.ofMul
    { toFun := fun x ↦ ⟨(h.coordAction hσc hπ b v).toMul x, by
        rw [mem_preimage, h.apply_coordAction_apply]
        exact x.2⟩
      invFun := fun x ↦ ⟨(h.coordAction hσc hπ b (-v)).toMul x, by
        rw [mem_preimage, h.apply_coordAction_apply]
        exact x.2⟩
      left_inv := fun x ↦ Subtype.ext <| by simp [map_neg]
      right_inv := fun x ↦ Subtype.ext <| by simp [map_neg] }
  map_zero' := Additive.toMul.injective <| Equiv.ext fun x ↦ Subtype.ext <| by simp
  map_add' v w := Additive.toMul.injective <| Equiv.ext fun x ↦ Subtype.ext <| by
    simp [map_add]

/-- **The action of the cotangent space of the base on a fibre.** For a proper Lagrangian
fibration `π : M → B` of a symplectic manifold, a covector `η` at `b` acts on the fibre `π⁻¹(b)` by
the time-one map of the flow of the Hamiltonian vector field of `g ∘ π`, for any smooth function
`g` on `B` with `dg_b = η` (`IsLagrangianFibration.coe_cotangentFiberAction_apply`). This is an
action of the vector group `T*_b B`, written additively as for `AddAction.toPermHom`. -/
noncomputable def cotangentFiberAction (hσc : σ.IsClosed) (hπ : IsProperMap π) (b : B) :
    (TangentSpace J b →L[ℝ] ℝ) →+ Additive (Equiv.Perm (π ⁻¹' {b})) :=
  (h.coordFiberAction hσc hπ b).comp (coordCovector F).symm.toLinearEquiv.toAddMonoidHom

private theorem coe_cotangentFiberAction_apply_eq_coordAction (hσc : σ.IsClosed)
    (hπ : IsProperMap π) {b : B} (η : TangentSpace J b →L[ℝ] ℝ) (x : π ⁻¹' {b}) :
    ((h.cotangentFiberAction hσc hπ b η).toMul x : M) =
      (h.coordAction hσc hπ b ((coordCovector F).symm η)).toMul x :=
  (rfl)

/-- **A covector acts by a vertical Hamiltonian flow.** The covector `η` at `b` moves a point `x`
of the fibre over `b` by the time-one map of the flow of `g ∘ π`, for every `C²` function `g` on
`B` with differential `η` at `b`. In particular the action does not depend on the auxiliary
coordinates used to construct it. -/
theorem coe_cotangentFiberAction_apply (hσc : σ.IsClosed) (hπ : IsProperMap π) {b : B}
    (η : TangentSpace J b →L[ℝ] ℝ) (x : π ⁻¹' {b}) {g : B → ℝ} (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hgη : mvfderiv J g b = η)
    (hv : ContMDiff I I.tangent 1 fun y ↦
      (⟨y, σ.hamiltonianVectorField (g ∘ π) y⟩ : TangentBundle I M))
    (hc : IsCompleteVectorField (σ.hamiltonianVectorField (g ∘ π))) :
    ((h.cotangentFiberAction hσc hπ b η).toMul x : M) = globalFlow _ hv hc 1 x := by
  rw [coe_cotangentFiberAction_apply_eq_coordAction]
  exact h.coordAction_apply_eq_globalFlow hσc hπ b _ hg (by
    rw [x.2, hgη, mvfderiv_eq_coordCovector]
    exact ((coordCovector F).apply_symm_apply η).symm) hv hc

end IsLagrangianFibration

/-! ### The period lattice of a regular Lagrangian torus fibration -/

namespace IsLagrangianTorusFibration

variable (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed)
include h hσc

omit [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] hσc in
/-- The data of the base coordinates at `b` needed to apply the topological Liouville–Arnold
theorem to the fibre over `b`: the fibre is the connected component of each of its points in its
level of the pulled-back coordinates, these points are regular, and the dimensions match. -/
private theorem baseCoord_comp_spec {b : B} (x : π ⁻¹' {b}) :
    connectedComponentIn ((baseCoord J b ∘ π) ⁻¹' {(baseCoord J b ∘ π) x}) x = π ⁻¹' {b} ∧
      (∀ y ∈ connectedComponentIn ((baseCoord J b ∘ π) ⁻¹' {(baseCoord J b ∘ π) x}) x,
        IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (baseCoord J b ∘ π) y) ∧
      2 * Fintype.card (Fin (finrank ℝ F)) = finrank ℝ E := by
  obtain ⟨W, hWo, hbW, hinj⟩ := exists_isOpen_injOn_baseCoord J b
  have hxb : π x = b := x.2
  have hcomp := (h.isConnected_preimage_singleton (π x)).isPreconnected
    |>.connectedComponentIn_preimage_comp_eq h.contMDiff.continuous hWo (by rwa [hxb]) hinj
  rw [hxb] at hcomp
  refine ⟨hcomp, fun y hy ↦ ?_, ?_⟩
  · rw [hcomp, mem_preimage, mem_singleton_iff] at hy
    refine IsRegularPoint.comp (isRegularPoint_iff_surjective_mvfderiv.2
      fun w ↦ ⟨(modelCoord F).symm w, ?_⟩) (isRegularPoint_iff.2 (h.surjective_mfderiv y))
    rw [hy]
    exact (mvfderiv_baseCoord_apply J b _).trans ((modelCoord F).apply_symm_apply w)
  · have : Nonempty M := ⟨x⟩
    rw [Fintype.card_fin, h.two_mul_finrank]

/-- **The cotangent action is transitive on each fibre.** Any two points of a fibre of a regular
Lagrangian torus fibration are related by the action of a covector of the base. -/
theorem exists_cotangentFiberAction_apply_eq {b : B} (x y : π ⁻¹' {b}) :
    ∃ η : TangentSpace J b →L[ℝ] ℝ, (h.cotangentFiberAction hσc h.isProperMap b η).toMul x = y := by
  obtain ⟨hcomp, hreg, hdim⟩ := h.baseCoord_comp_spec x
  have hσS : σ.IsSymplectic := ⟨hσc, hσ⟩
  have hy : (y : M) ∈ range fun v ↦ (h.coordAction hσc h.isProperMap b v).toMul x := by
    rw [IsLagrangianFibration.coordAction, hσS.range_hamiltonianFlowAction_apply _ _ _ hdim hreg,
      hcomp]
    exact y.2
  obtain ⟨v, hv⟩ := hy
  refine ⟨coordCovector F v, Subtype.ext ?_⟩
  refine (h.coe_cotangentFiberAction_apply_eq_coordAction hσc h.isProperMap _ x).trans ?_
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact hv

/-- The **period lattice** `Λ_b ⊆ T*_b B` of a regular Lagrangian torus fibration at `b`: the
covectors at `b` acting trivially on the fibre over `b`. It is the stabilizer of every point of the
fibre (`IsLagrangianTorusFibration.mem_periodLattice_iff`), and a full lattice: it is discrete
(`IsLagrangianTorusFibration.discreteTopology_periodLattice`), spans `T*_b B`
(`IsLagrangianTorusFibration.span_periodLattice_eq_top`), and the quotient `T*_b B ⧸ Λ_b` is
compact (`IsLagrangianTorusFibration.compactSpace_quotient_periodLattice`). -/
noncomputable def periodLattice (b : B) : AddSubgroup (TangentSpace J b →L[ℝ] ℝ) :=
  (h.cotangentFiberAction hσc h.isProperMap b).ker

/-- **The period lattice is the stabilizer of any point of the fibre.** Since the cotangent action
is commutative and transitive on the fibre, a covector fixing one point of the fibre fixes all of
them. -/
theorem mem_periodLattice_iff {b : B} {η : TangentSpace J b →L[ℝ] ℝ} (x : π ⁻¹' {b}) :
    η ∈ h.periodLattice hσc b ↔ (h.cotangentFiberAction hσc h.isProperMap b η).toMul x = x := by
  set A := h.cotangentFiberAction hσc h.isProperMap b
  refine ⟨fun hη ↦ by rw [show A η = 0 from AddMonoidHom.mem_ker.1 hη, toMul_zero,
    Equiv.Perm.one_apply], fun hη ↦ AddMonoidHom.mem_ker.2 <| Additive.toMul.injective <|
    Equiv.ext fun y ↦ ?_⟩
  obtain ⟨ξ, rfl⟩ := h.exists_cotangentFiberAction_apply_eq hσc x y
  -- The actions of `η` and `ξ` commute, and `η` fixes `x`.
  have hcomm : (A η).toMul ((A ξ).toMul x) = (A ξ).toMul ((A η).toMul x) := by
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← toMul_add, ← toMul_add, ← map_add,
      ← map_add, add_comm]
  rw [hcomm, hη, toMul_zero, Equiv.Perm.one_apply]

/-- The period lattice consists of the covectors whose coordinates lie in the stabilizer of a
point for the action of the base coordinates. -/
private theorem mem_periodLattice_iff_mem_hamiltonianFlowStabilizer {b : B}
    {η : TangentSpace J b →L[ℝ] ℝ} (x : π ⁻¹' {b}) :
    η ∈ h.periodLattice hσc b ↔ (coordCovector F).symm η ∈
      (⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowStabilizer
        (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
        (h.isCompleteVectorField_baseCoord_comp h.isProperMap b) x := by
  rw [h.mem_periodLattice_iff hσc x, Subtype.ext_iff,
    h.coe_cotangentFiberAction_apply_eq_coordAction hσc h.isProperMap η x,
    IsSymplectic.mem_hamiltonianFlowStabilizer]
  rfl

/-- **The period lattice is discrete.** -/
theorem discreteTopology_periodLattice (b : B) : DiscreteTopology (h.periodLattice hσc b) := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  obtain ⟨-, hreg, -⟩ := h.baseCoord_comp_spec ⟨x, hx⟩
  have := (⟨hσc, hσ⟩ : σ.IsSymplectic).discreteTopology_hamiltonianFlowStabilizer
    (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
    (h.isCompleteVectorField_baseCoord_comp h.isProperMap b)
    (hreg x (mem_connectedComponentIn (by simp)))
  -- The coordinates embed the period lattice continuously into the discrete stabilizer.
  refine DiscreteTopology.of_continuous_injective
    (f := fun η : h.periodLattice hσc b ↦ (⟨(coordCovector F).symm η.1,
      (h.mem_periodLattice_iff_mem_hamiltonianFlowStabilizer hσc ⟨x, hx⟩).1 η.2⟩ :
        (⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowStabilizer
          (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
          (h.isCompleteVectorField_baseCoord_comp h.isProperMap b) x))
    ?_ fun η η' hηη' ↦ Subtype.ext <| (coordCovector F).symm.injective (congrArg Subtype.val hηη')
  exact ((coordCovector F).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- **The period lattice has full rank**: it spans the cotangent space of the base. -/
theorem span_periodLattice_eq_top (b : B) :
    Submodule.span ℝ (h.periodLattice hσc b : Set (TangentSpace J b →L[ℝ] ℝ)) = ⊤ := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  obtain ⟨hcomp, hreg, hdim⟩ := h.baseCoord_comp_spec ⟨x, hx⟩
  have hspan := (⟨hσc, hσ⟩ : σ.IsSymplectic).span_hamiltonianFlowStabilizer_eq_top
    (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
    (h.isCompleteVectorField_baseCoord_comp h.isProperMap b) hreg hdim
    (by rw [hcomp]; exact h.isCompact_preimage_singleton b)
  -- The period lattice is the image of the stabilizer under the coordinate isomorphism.
  have himage : (h.periodLattice hσc b : Set (TangentSpace J b →L[ℝ] ℝ)) =
      (coordCovector F).toLinearEquiv.toLinearMap ''
        ((⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowStabilizer
          (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
          (h.isCompleteVectorField_baseCoord_comp h.isProperMap b) x : Set _) := by
    ext η
    rw [SetLike.mem_coe, h.mem_periodLattice_iff_mem_hamiltonianFlowStabilizer hσc ⟨x, hx⟩]
    exact ⟨fun hη ↦ ⟨_, hη, (coordCovector F).apply_symm_apply η⟩,
      fun ⟨v, hv, hvη⟩ ↦ by
        rw [← hvη]
        simpa using hv⟩
  rw [himage]
  refine (Submodule.span_image (coordCovector F).toLinearEquiv.toLinearMap).trans ?_
  rw [hspan, Submodule.map_top]
  exact LinearMap.range_eq_top.2 (coordCovector F).surjective

omit hσc in
/-- The coordinates of covectors at `b`, as an additive equivalence. -/
private noncomputable def coordAddEquiv (b : B) :
    (TangentSpace J b →L[ℝ] ℝ) ≃+ (Fin (finrank ℝ F) → ℝ) :=
  (coordCovector F).symm.toLinearEquiv.toAddEquiv

/-- The coordinates carry the period lattice onto the stabilizer of each point of the fibre. -/
private theorem map_periodLattice_eq_hamiltonianFlowStabilizer {b : B} (x : π ⁻¹' {b}) :
    (h.periodLattice hσc b).map (coordAddEquiv (J := J) b : _ →+ _) =
      (⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowStabilizer
        (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
        (h.isCompleteVectorField_baseCoord_comp h.isProperMap b) x := by
  ext v
  refine ⟨fun ⟨η, hη, hηv⟩ ↦ hηv ▸
    (h.mem_periodLattice_iff_mem_hamiltonianFlowStabilizer hσc x).1 hη, fun hv ↦
      ⟨coordCovector F v, (h.mem_periodLattice_iff_mem_hamiltonianFlowStabilizer hσc x).2 ?_, ?_⟩⟩
  · rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hv
  · exact (coordCovector F).symm_apply_apply v

/-- **The fibre is the quotient of the cotangent space by the period lattice.** For a point `x` of
the fibre over `b`, the orbit map `η ↦ η • x` of the cotangent action descends to a homeomorphism
`T*_b B ⧸ Λ_b ≃ₜ π⁻¹(b)`. -/
noncomputable def quotientPeriodLatticeHomeomorph {b : B} (x : π ⁻¹' {b}) :
    (TangentSpace J b →L[ℝ] ℝ) ⧸ h.periodLattice hσc b ≃ₜ π ⁻¹' {b} :=
  let Q := (⟨hσc, hσ⟩ : σ.IsSymplectic).quotientHamiltonianFlowStabilizerHomeomorph
    (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
    (h.isCompleteVectorField_baseCoord_comp h.isProperMap b) (h.baseCoord_comp_spec x).2.2
    (h.baseCoord_comp_spec x).2.1
  let e := ((QuotientAddGroup.congr _ _ (coordAddEquiv b)
    (h.map_periodLattice_eq_hamiltonianFlowStabilizer hσc x)).toEquiv.trans Q.toEquiv).trans
      (Homeomorph.setCongr (h.baseCoord_comp_spec x).1).toEquiv
  -- Composed with the quotient map, `e` is a composite of continuous open maps.
  have he : e ∘ QuotientAddGroup.mk = Homeomorph.setCongr (h.baseCoord_comp_spec x).1 ∘ Q ∘
      QuotientAddGroup.mk ∘ (coordCovector F).symm := rfl
  have hc : Continuous (e ∘ QuotientAddGroup.mk) := by
    rw [he]
    exact (Homeomorph.setCongr _).continuous.comp <| Q.continuous.comp <|
      QuotientAddGroup.continuous_mk.comp (coordCovector F).symm.continuous
  have ho : IsOpenMap (e ∘ QuotientAddGroup.mk) := by
    rw [he]
    exact (Homeomorph.setCongr _).isOpenMap.comp <| Q.isOpenMap.comp <|
      QuotientAddGroup.isOpenMap_coe.comp (coordCovector F).symm.toHomeomorph.isOpenMap
  e.toHomeomorphOfContinuousOpen ((QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hc)
    (IsOpenMap.of_comp QuotientAddGroup.continuous_mk QuotientAddGroup.mk_surjective ho)

@[simp]
theorem coe_quotientPeriodLatticeHomeomorph_mk {b : B} (x : π ⁻¹' {b})
    (η : TangentSpace J b →L[ℝ] ℝ) :
    h.quotientPeriodLatticeHomeomorph hσc x η =
      (h.cotangentFiberAction hσc h.isProperMap b η).toMul x := by
  refine Subtype.ext ?_
  rw [h.coe_cotangentFiberAction_apply_eq_coordAction]
  -- Both sides unfold to the orbit map of the coordinate action at `(coordCovector F).symm η`.
  exact (⟨hσc, hσ⟩ : σ.IsSymplectic).coe_quotientHamiltonianFlowStabilizerHomeomorph_mk
    (h.contMDiff_baseCoord_comp b) (h.poissonBracket_baseCoord_comp b)
    (h.isCompleteVectorField_baseCoord_comp h.isProperMap b) (h.baseCoord_comp_spec x).2.2
    (h.baseCoord_comp_spec x).2.1 _

/-- **The period lattice is cocompact.** -/
theorem compactSpace_quotient_periodLattice (b : B) :
    CompactSpace ((TangentSpace J b →L[ℝ] ℝ) ⧸ h.periodLattice hσc b) := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  have := isCompact_iff_compactSpace.1 (h.isCompact_preimage_singleton b)
  exact (h.quotientPeriodLatticeHomeomorph hσc ⟨x, hx⟩).symm.compactSpace

end IsLagrangianTorusFibration

end TauCeti.SmoothTwoForm.IsNondegenerate
