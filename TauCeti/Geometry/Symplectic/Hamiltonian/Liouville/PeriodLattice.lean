/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Fibration
public import TauCeti.Geometry.Symplectic.Hamiltonian.LiouvilleArnold.Torus

/-!
# The period lattice of a regular Lagrangian torus fibration

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
onto a Hausdorff manifold `B` of dimension `n`. This file constructs the action of the cotangent
space `T*_b B` on the fibre `π⁻¹(b)` and its stabilizer, the **period lattice** `Λ_b ⊆ T*_b B`.

Covectors at `b` are the elements of `F →L[ℝ] ℝ`, the dual of the model space `F = T_b B`. A
covector `α ∈ T*_b B` acts on the fibre over `b` by the time-one map of the Hamiltonian flow of
`g ∘ π`, for any `C²` function `g` on `B` with `dg_b = α`
(`IsLagrangianTorusFibration.fiberAction`,
`IsLagrangianTorusFibration.coe_fiberAction_eq_flowOf`). This does not depend on the choice of
`g`: the Hamiltonian vector field of `g ∘ π` is vertical, and along the fibre over `b` it is
determined by `d(g ∘ π) = dg_b ∘ dπ`
(`IsLagrangianFibration.flowOf_hamiltonianVectorField_comp_eq`).
The flows of pulled-back functions commute, since the fibres are Lagrangian, so this is an action of
the vector group `T*_b B` (`IsLagrangianTorusFibration.fiberAction_add`), and it is transitive
(`IsLagrangianTorusFibration.exists_fiberAction_eq`).

The period lattice `Λ_b` (`IsLagrangianTorusFibration.periodLattice`) is the subgroup of the
covectors acting trivially on the fibre. Since the action is transitive and commutative, a covector
lies in `Λ_b` as soon as it fixes one point of the fibre
(`IsLagrangianTorusFibration.mem_periodLattice_iff_fiberAction_eq`), and two covectors act alike
on a point exactly when they differ by an element of `Λ_b`
(`IsLagrangianTorusFibration.fiberAction_eq_fiberAction_iff`). The period lattice is a discrete
subgroup (`IsLagrangianTorusFibration.discreteTopology_periodLattice`) spanning `T*_b B`
(`IsLagrangianTorusFibration.isZLattice_periodLattice`), hence a full lattice of rank `n`
(`IsLagrangianTorusFibration.finrank_periodLattice`), and the orbit map through any point of the
fibre descends to a homeomorphism `T*_b B / Λ_b ≃ₜ π⁻¹(b)`
(`IsLagrangianTorusFibration.quotientPeriodLatticeHomeomorph`).

The proofs transport the corresponding facts for the Hamiltonian flow action of coordinates
`κ ∘ π` near the fibre (`IsLagrangianTorusFibration.exists_coordinates`), in which the vector `v`
acts by the time-one flow of `v ⬝ᵥ (κ ∘ π)`
(`TauCeti.SmoothTwoForm.IsSymplectic.flowOf_hamiltonianVectorField_dotProduct`), that is, as the
covector `d(v ⬝ᵥ κ)_b`.

These fibrewise lattices are the fibres of the period lattice `Λ ⊆ T*B` of the fibration, whose
quotient `T*B / Λ` is the torus bundle associated with the fibration; that bundle is not constructed
here. Its model, for a lattice spanned by global closed one-forms, is
`TauCeti.CotangentBundle.LatticeQuotient`.

## Main definitions

* `IsLagrangianTorusFibration.fiberAction`: the action of `T*_b B` on the fibre over `b`.
* `IsLagrangianTorusFibration.periodLattice`: the period lattice `Λ_b ⊆ T*_b B`.
* `IsLagrangianTorusFibration.quotientPeriodLatticeHomeomorph`: the homeomorphism
  `T*_b B / Λ_b ≃ₜ π⁻¹(b)` given by the orbit map through a point of the fibre.

## Main results

* `IsLagrangianTorusFibration.coe_fiberAction_eq_flowOf`: a covector `dg_b` acts by the time-one
  map of the Hamiltonian flow of `g ∘ π`.
* `IsLagrangianTorusFibration.fiberAction_add`, `IsLagrangianTorusFibration.exists_fiberAction_eq`:
  the action is an action of the additive group `T*_b B`, and it is transitive.
* `IsLagrangianTorusFibration.mem_periodLattice_iff_fiberAction_eq`,
  `IsLagrangianTorusFibration.mem_periodLattice_iff_flowOf_eq`: the period lattice is the
  stabilizer of any point of the fibre.
* `IsLagrangianTorusFibration.isZLattice_periodLattice`,
  `IsLagrangianTorusFibration.finrank_periodLattice`: the period lattice is a full lattice in
  `T*_b B`, of rank `dim B`.

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (the action of `T*B` on the fibres and the period lattice).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
-/

public section

noncomputable section

open Function Set Module
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

variable (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed) (b : B)

/-! ### Coordinates around a fibre and their Hamiltonian flow action -/

/-- The coordinates around the fibre over `b` chosen by `exists_coordinates`. -/
private def coord : B → Fin (finrank ℝ F) → ℝ :=
  (h.exists_coordinates b).choose

/-- The differential at `b` of the coordinates `coord`. -/
private def coordEquiv : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) :=
  (h.exists_coordinates b).choose_spec.choose

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem coord_spec :
    ContMDiff J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ (h.coord b) ∧
      mfderiv J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (h.coord b) b =
        (h.coordEquiv b : F →L[ℝ] Fin (finrank ℝ F) → ℝ) ∧
      (∀ y ∈ π ⁻¹' {b}, IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (h.coord b ∘ π) y) ∧
      ∀ x ∈ π ⁻¹' {b},
        connectedComponentIn ((h.coord b ∘ π) ⁻¹' {h.coord b (π x)}) x = π ⁻¹' {b} :=
  (h.exists_coordinates b).choose_spec.choose_spec

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem contMDiff_coord_comp :
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ (h.coord b ∘ π) :=
  (h.coord_spec b).1.comp h.contMDiff

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem contMDiff_coord_apply (i : Fin (finrank ℝ F)) :
    ContMDiff J 𝓘(ℝ) ∞ fun c ↦ h.coord b c i :=
  contMDiff_pi_module_iff.1 (h.coord_spec b).1 i

omit [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem poissonBracket_coord_comp (i j : Fin (finrank ℝ F)) (y : M) :
    σ.poissonBracket ((h.coord b ∘ π) · i) ((h.coord b ∘ π) · j) y = 0 :=
  h.poissonBracket_comp_eq_zero ((h.contMDiff_coord_apply b i).mdifferentiableAt (by simp))
    ((h.contMDiff_coord_apply b j).mdifferentiableAt (by simp))

omit [I.Boundaryless] in
private theorem isCompleteVectorField_coord_comp (i : Fin (finrank ℝ F)) :
    IsCompleteVectorField (σ.hamiltonianVectorField ((h.coord b ∘ π) · i)) :=
  h.isCompleteVectorField_hamiltonianVectorField_comp h.isProperMap
    ((h.contMDiff_coord_apply b i).of_le (by simp))

/-- The Hamiltonian flow action of `ℝⁿ` generated by the coordinates `coord ∘ π`. -/
private def coordAction (v : Fin (finrank ℝ F) → ℝ) : M → M :=
  ((⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowAction (h.contMDiff_coord_comp b)
    (h.poissonBracket_coord_comp b) (h.isCompleteVectorField_coord_comp b) v).toMul

/-- The coordinates of a covector at `b` in the basis dual to the coordinates `coord`. -/
private def dualCoord : (F →L[ℝ] ℝ) ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) :=
  (((h.coordEquiv b).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toLinearEquiv.trans
    (LinearMap.toContinuousLinearMap.symm.trans
      (dotProductEquiv ℝ (Fin (finrank ℝ F))).symm)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem dualCoord_apply (α : F →L[ℝ] ℝ) (i : Fin (finrank ℝ F)) :
    h.dualCoord b α i = α ((h.coordEquiv b).symm (Pi.single i 1)) :=
  (rfl)

/-! ### The action of the cotangent space on a fibre -/

/-- **The action of `T*_b B` on the fibre over `b`.** A covector `α` acts on the fibre `π⁻¹(b)` by
the time-one map of the Hamiltonian flow of `g ∘ π`, for any `C²` function `g` on `B` with
`dg_b = α` (`coe_fiberAction_eq_flowOf`). -/
def fiberAction (α : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) : π ⁻¹' {b} :=
  ⟨h.coordAction hσc b (h.dualCoord b α) x, by
    have hm : h.coordAction hσc b (h.dualCoord b α) x ∈
        connectedComponentIn ((h.coord b ∘ π) ⁻¹' {h.coord b (π x)}) x :=
      (⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowAction_apply_mem_connectedComponentIn _ _ _ x _
    rwa [(h.coord_spec b).2.2.2 x x.2] at hm⟩

private theorem coe_fiberAction (α : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) :
    (h.fiberAction hσc b α x : M) = h.coordAction hσc b (h.dualCoord b α) x :=
  (rfl)

/-- **A covector `dg_b` acts by the time-one map of the Hamiltonian flow of `g ∘ π`.** For every
`C²` function `g` on `B` with differential `α` at `b`, the action of `α` moves each point `x` of
the fibre over `b` to the time-one image of `x` under the flow of the Hamiltonian vector field of
`g ∘ π`. -/
theorem coe_fiberAction_eq_flowOf {α : F →L[ℝ] ℝ} {g : B → ℝ}
    (hg : ContMDiff J 𝓘(ℝ) 2 g) (hgα : mvfderiv J g b = α) (x : π ⁻¹' {b}) :
    (h.fiberAction hσc b α x : M) = flowOf (σ.hamiltonianVectorField (g ∘ π)) 1 x := by
  classical
  -- The covector `α` is the differential at `b` of the function `v ⬝ᵥ coord`, where `v` are the
  -- dual coordinates of `α`.
  let φ : (Fin (finrank ℝ F) → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (dotProductEquiv ℝ (Fin (finrank ℝ F)) (h.dualCoord b α))
  have hφ : ContMDiff J 𝓘(ℝ) 2 (φ ∘ h.coord b) :=
    (φ.contMDiff.comp (h.coord_spec b).1).of_le (by simp)
  have hdφ : mvfderiv J (φ ∘ h.coord b) b = α := by
    have h1 (w : TangentSpace J b) : mvfderiv J (φ ∘ h.coord b) b w = φ (h.coordEquiv b w) := by
      rw [mvfderiv_apply_eq_mfderiv_apply,
        mfderiv_comp b φ.mdifferentiableAt (((h.coord_spec b).1 b).mdifferentiableAt (by simp)),
        φ.mfderiv_eq, (h.coord_spec b).2.1]
      -- This is `ContinuousLinearMap.comp_apply`, which does not rewrite here because `w` is
      -- typed as a tangent vector rather than as an element of the model space `F`.
      rfl
    have h2 : φ.comp (h.coordEquiv b : F →L[ℝ] Fin (finrank ℝ F) → ℝ) = α :=
      (h.dualCoord b).injective (funext fun i ↦ by simp [φ, dualCoord_apply])
    exact ContinuousLinearMap.ext fun w ↦ (h1 w).trans (congrArg (· w) h2)
  have hx : π x = b := x.2
  rw [coe_fiberAction, coordAction, ← one_smul ℝ (h.dualCoord b α),
    ← (⟨hσc, hσ⟩ : σ.IsSymplectic).flowOf_hamiltonianVectorField_dotProduct]
  exact h.flowOf_hamiltonianVectorField_comp_eq h.isProperMap hφ hg
    (by rw [hx, hdφ, hgα]) 1

/-- The zero covector acts as the identity on the fibre. -/
@[simp]
theorem fiberAction_zero (x : π ⁻¹' {b}) : h.fiberAction hσc b 0 x = x :=
  Subtype.ext <| by
    rw [coe_fiberAction, map_zero, coordAction]
    exact (⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowAction_zero_apply _ _ _ x

/-- **The action of `T*_b B` on the fibre is additive**: `α + β` acts as `α` after `β`. -/
theorem fiberAction_add (α β : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) :
    h.fiberAction hσc b (α + β) x = h.fiberAction hσc b α (h.fiberAction hσc b β x) :=
  Subtype.ext <| by
    rw [coe_fiberAction, coe_fiberAction, coe_fiberAction, map_add, coordAction, coordAction]
    exact (⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowAction_add_apply _ _ _ _ _ x

/-- The actions of two covectors on the fibre commute. -/
theorem fiberAction_comm (α β : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) :
    h.fiberAction hσc b α (h.fiberAction hσc b β x) =
      h.fiberAction hσc b β (h.fiberAction hσc b α x) := by
  rw [← fiberAction_add, add_comm, fiberAction_add]

/-- **The action of `T*_b B` on the fibre over `b` is transitive.** -/
theorem exists_fiberAction_eq (x y : π ⁻¹' {b}) : ∃ α, h.fiberAction hσc b α x = y := by
  have : Nonempty M := ⟨x⟩
  have hcomp := (h.coord_spec b).2.2.2 x x.2
  have hy : (y : M) ∈ connectedComponentIn ((h.coord b ∘ π) ⁻¹' {h.coord b (π x)}) x := by
    rw [hcomp]
    exact y.2
  obtain ⟨v, hv⟩ := (⟨hσc, hσ⟩ : σ.IsSymplectic).exists_hamiltonianFlowAction_apply_eq
    (h.contMDiff_coord_comp b) (h.poissonBracket_coord_comp b)
    (h.isCompleteVectorField_coord_comp b) (by rw [Fintype.card_fin, h.two_mul_finrank])
    (fun z hz ↦ (h.coord_spec b).2.2.1 z (hcomp ▸ hz)) hy
  refine ⟨(h.dualCoord b).symm v, Subtype.ext ?_⟩
  rw [coe_fiberAction, ContinuousLinearEquiv.apply_symm_apply]
  exact hv

/-! ### The period lattice -/

/-- **The period lattice** `Λ_b ⊆ T*_b B` of the fibration at `b`: the subgroup of the covectors
acting trivially on the fibre over `b`. It is the stabilizer of any single point of the fibre
(`mem_periodLattice_iff_fiberAction_eq`), and it is a full lattice in `T*_b B`
(`isZLattice_periodLattice`). -/
def periodLattice : AddSubgroup (F →L[ℝ] ℝ) where
  carrier := {α | ∀ x, h.fiberAction hσc b α x = x}
  add_mem' {α β} hα hβ x := by
    rw [fiberAction_add, hβ x, hα x]
  zero_mem' := h.fiberAction_zero hσc b
  neg_mem' {α} hα x := by
    conv_lhs => rw [← hα x]
    rw [← fiberAction_add, neg_add_cancel, fiberAction_zero]

/-- A covector lies in the period lattice exactly when it fixes every point of the fibre. -/
@[simp]
theorem mem_periodLattice {α : F →L[ℝ] ℝ} :
    α ∈ h.periodLattice hσc b ↔ ∀ x, h.fiberAction hσc b α x = x :=
  Iff.rfl

/-- **The period lattice is the stabilizer of any point of the fibre.** A covector acts trivially
on the fibre as soon as it fixes one of its points, since the action is transitive and
commutative. -/
theorem mem_periodLattice_iff_fiberAction_eq {α : F →L[ℝ] ℝ} (x : π ⁻¹' {b}) :
    α ∈ h.periodLattice hσc b ↔ h.fiberAction hσc b α x = x := by
  refine ⟨fun hα ↦ hα x, fun hα y ↦ ?_⟩
  obtain ⟨β, rfl⟩ := h.exists_fiberAction_eq hσc b x y
  rw [fiberAction_comm, hα]

/-- Two covectors act alike on a point of the fibre exactly when they differ by an element of the
period lattice. -/
theorem fiberAction_eq_fiberAction_iff {α β : F →L[ℝ] ℝ} (x : π ⁻¹' {b}) :
    h.fiberAction hσc b α x = h.fiberAction hσc b β x ↔ -α + β ∈ h.periodLattice hσc b := by
  rw [h.mem_periodLattice_iff_fiberAction_eq hσc b x]
  constructor
  · intro hαβ
    rw [fiberAction_add, ← hαβ, ← fiberAction_add, neg_add_cancel, fiberAction_zero]
  · intro hαβ
    conv_lhs => rw [← hαβ]
    rw [← fiberAction_add, add_neg_cancel_left]

/-- **The period lattice in terms of Hamiltonian flows.** The differential `α` at `b` of a `C²`
function `g` on `B` lies in the period lattice exactly when the time-one map of the Hamiltonian
flow of `g ∘ π` fixes some, equivalently every, point of the fibre over `b`. -/
theorem mem_periodLattice_iff_flowOf_eq {α : F →L[ℝ] ℝ} {g : B → ℝ} (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hgα : mvfderiv J g b = α) (x : π ⁻¹' {b}) :
    α ∈ h.periodLattice hσc b ↔ flowOf (σ.hamiltonianVectorField (g ∘ π)) 1 x = x := by
  rw [h.mem_periodLattice_iff_fiberAction_eq hσc b x, Subtype.ext_iff,
    h.coe_fiberAction_eq_flowOf hσc b hg hgα]

/-- The period lattice is the stabilizer of the coordinate flow action, read in dual coordinates. -/
private theorem mem_periodLattice_iff_mem_hamiltonianFlowStabilizer
    {α : F →L[ℝ] ℝ} (x : π ⁻¹' {b}) :
    α ∈ h.periodLattice hσc b ↔ h.dualCoord b α ∈
      (⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowStabilizer (h.contMDiff_coord_comp b)
        (h.poissonBracket_coord_comp b) (h.isCompleteVectorField_coord_comp b) x := by
  rw [h.mem_periodLattice_iff_fiberAction_eq hσc b x, Subtype.ext_iff, coe_fiberAction,
    IsSymplectic.mem_hamiltonianFlowStabilizer]
  rfl

private theorem toIntSubmodule_periodLattice (x : π ⁻¹' {b}) :
    (h.periodLattice hσc b).toIntSubmodule = ZLattice.comap ℝ
      ((⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowStabilizer (h.contMDiff_coord_comp b)
        (h.poissonBracket_coord_comp b) (h.isCompleteVectorField_coord_comp b) x).toIntSubmodule
      (h.dualCoord b).toLinearMap := by
  ext α
  exact h.mem_periodLattice_iff_mem_hamiltonianFlowStabilizer hσc b x

/-- **The period lattice is discrete.** -/
theorem discreteTopology_periodLattice : DiscreteTopology (h.periodLattice hσc b) := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  have := (⟨hσc, hσ⟩ : σ.IsSymplectic).discreteTopology_hamiltonianFlowStabilizer
    (h.contMDiff_coord_comp b) (h.poissonBracket_coord_comp b)
    (h.isCompleteVectorField_coord_comp b) ((h.coord_spec b).2.2.1 x hx)
  have hd := (inferInstance : DiscreteTopology (ZLattice.comap ℝ
    ((⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowStabilizer (h.contMDiff_coord_comp b)
      (h.poissonBracket_coord_comp b) (h.isCompleteVectorField_coord_comp b)
      x).toIntSubmodule (h.dualCoord b).toLinearMap))
  rw [← h.toIntSubmodule_periodLattice hσc b ⟨x, hx⟩] at hd
  exact hd

/-- **The period lattice is a full lattice.** The period lattice spans `T*_b B`, so with its
discreteness (`discreteTopology_periodLattice`) it is a `ℤ`-lattice in `T*_b B`. Hence the fibre
over `b`, which is homeomorphic to `T*_b B / Λ_b` (`quotientPeriodLatticeHomeomorph`), is a torus of
dimension `dim B`. -/
theorem isZLattice_periodLattice [DiscreteTopology (h.periodLattice hσc b)] :
    IsZLattice ℝ (h.periodLattice hσc b).toIntSubmodule := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  have : Nonempty M := ⟨x⟩
  have hcomp := (h.coord_spec b).2.2.2 x hx
  have := (⟨hσc, hσ⟩ : σ.IsSymplectic).discreteTopology_hamiltonianFlowStabilizer
    (h.contMDiff_coord_comp b) (h.poissonBracket_coord_comp b)
    (h.isCompleteVectorField_coord_comp b) ((h.coord_spec b).2.2.1 x hx)
  have := (⟨hσc, hσ⟩ : σ.IsSymplectic).isZLattice_hamiltonianFlowStabilizer
    (h.contMDiff_coord_comp b) (h.poissonBracket_coord_comp b)
    (h.isCompleteVectorField_coord_comp b) (by rw [Fintype.card_fin, h.two_mul_finrank])
    (fun z hz ↦ (h.coord_spec b).2.2.1 z (hcomp ▸ hz))
    (hcomp ▸ h.isCompact_preimage_singleton b)
  refine ⟨?_⟩
  rw [h.toIntSubmodule_periodLattice hσc b ⟨x, hx⟩]
  exact IsZLattice.span_top

/-- **The period lattice has rank `dim B`.** -/
theorem finrank_periodLattice [DiscreteTopology (h.periodLattice hσc b)] :
    finrank ℤ (h.periodLattice hσc b).toIntSubmodule = finrank ℝ F := by
  have := h.isZLattice_periodLattice hσc b
  rw [ZLattice.rank ℝ, (h.dualCoord b).toLinearEquiv.finrank_eq, finrank_fin_fun]

/-! ### The fibre as the torus `T*_b B / Λ_b` -/

/-- **The fibre over `b` is the torus `T*_b B / Λ_b`.** For a point `x` of the fibre, the orbit
map `α ↦ α • x` of the action of `T*_b B` descends to a homeomorphism from the quotient of `T*_b B`
by the period lattice onto the fibre over `b`. -/
def quotientPeriodLatticeHomeomorph (x : π ⁻¹' {b}) :
    (F →L[ℝ] ℝ) ⧸ h.periodLattice hσc b ≃ₜ π ⁻¹' {b} :=
  -- The orbit map, descended to the quotient.
  let f : (F →L[ℝ] ℝ) ⧸ h.periodLattice hσc b → π ⁻¹' {b} :=
    Quotient.lift (fun α ↦ h.fiberAction hσc b α x) fun _ _ hαβ ↦
      (h.fiberAction_eq_fiberAction_iff hσc b x).2 (QuotientAddGroup.leftRel_apply.1 hαβ)
  have hf : f ∘ QuotientAddGroup.mk = fun α ↦ h.fiberAction hσc b α x := rfl
  have : Nonempty M := ⟨x⟩
  have hcomp := (h.coord_spec b).2.2.2 x x.2
  have hreg : ∀ y ∈ connectedComponentIn ((h.coord b ∘ π) ⁻¹' {(h.coord b ∘ π) x}) x,
      IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (h.coord b ∘ π) y :=
    fun y hy ↦ (h.coord_spec b).2.2.1 y (hcomp ▸ hy)
  -- The orbit map is the orbit map of the coordinate flow action, read in dual coordinates and
  -- transported to the fibre; the latter descends to a homeomorphism.
  let Q := (⟨hσc, hσ⟩ : σ.IsSymplectic).quotientHamiltonianFlowStabilizerHomeomorph
    (h.contMDiff_coord_comp b) (h.poissonBracket_coord_comp b)
    (h.isCompleteVectorField_coord_comp b) (by rw [Fintype.card_fin, h.two_mul_finrank]) hreg
  have horbit : (fun α ↦ h.fiberAction hσc b α x) =
      Homeomorph.setCongr hcomp ∘ Q ∘ QuotientAddGroup.mk ∘ h.dualCoord b :=
    funext fun α ↦ Subtype.ext
      (IsSymplectic.coe_quotientHamiltonianFlowStabilizerHomeomorph_mk _ _ _ _ _ _ _).symm
  (Equiv.ofBijective f ⟨fun a a' ↦ Quotient.inductionOn₂ a a' fun α β hαβ ↦
      QuotientAddGroup.eq.2 ((h.fiberAction_eq_fiberAction_iff hσc b x).1 hαβ),
    fun y ↦ ⟨QuotientAddGroup.mk (h.exists_fiberAction_eq hσc b x y).choose,
      (h.exists_fiberAction_eq hσc b x y).choose_spec⟩⟩).toHomeomorphOfContinuousOpen
    ((QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 <| hf ▸ horbit ▸
      (Homeomorph.setCongr hcomp).continuous.comp (Q.continuous.comp
        (QuotientAddGroup.continuous_mk.comp (h.dualCoord b).continuous)))
    (IsOpenMap.of_comp QuotientAddGroup.continuous_mk QuotientAddGroup.mk_surjective <| hf ▸
      horbit ▸ (Homeomorph.setCongr hcomp).isOpenMap.comp (Q.isOpenMap.comp
        (QuotientAddGroup.isOpenMap_coe.comp (h.dualCoord b).toHomeomorph.isOpenMap)))

/-- The homeomorphism `T*_b B / Λ_b ≃ₜ π⁻¹(b)` sends the class of `α` to `α • x`. -/
@[simp]
theorem quotientPeriodLatticeHomeomorph_mk (x : π ⁻¹' {b}) (α : F →L[ℝ] ℝ) :
    h.quotientPeriodLatticeHomeomorph hσc b x α = h.fiberAction hσc b α x := by
  rw [quotientPeriodLatticeHomeomorph]
  rfl

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
