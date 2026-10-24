/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Openness of positivity in bilinear bundles

For a finite-rank real vector bundle, strict diagonal positivity is an open condition in the
total space of the bilinear bundle. No symmetry condition is included: symmetric positive forms
are open relative to the symmetric subbundle, rather than in the full bilinear bundle.

Consequently a continuous family of bilinear fields that is positive at one parameter on a
compact subset of the base remains positive there for nearby parameters. This applies to
families of symmetric fields when constructing and perturbing Riemannian metrics. The bundle
fibres need only carry their original topological vector space structures; no background metric
or choice of norms on the fibres is required.

The proof uses the matrix-cone openness theorem
`TauCeti.isOpen_setOfPred_dotProduct_mulVec_pos`, transported through a basis and the native
iterated hom-bundle trivializations.
-/

public section

noncomputable section

open Bundle ContinuousLinearMap Filter Set
open scoped Topology

namespace TauCeti

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Reading a real bilinear form in a bundle chart preserves and reflects strict diagonal
positivity wherever the chart is defined. -/
@[simp]
theorem forall_inCoordinates_bilinear_apply_self_pos_iff {x₀ x : B}
    (hx : x ∈ (trivializationAt F V x₀).baseSet) (b : V x →L[ℝ] V x →L[ℝ] ℝ) :
    (∀ v : F, v ≠ 0 →
      0 < inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] ℝ) x₀ x x₀ x b v v) ↔
      ∀ v : V x, v ≠ 0 → 0 < b v v := by
  let e := (trivializationAt F V x₀).continuousLinearEquivAt ℝ x hx
  have heval (v w : F) :
      inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] ℝ) x₀ x x₀ x b v w =
        b (e.symm v) (e.symm w) := by
    rw [inCoordinates_apply_eq₂ hx hx (by simp)]
    simp [e]
  simp only [heval]
  constructor
  · intro h v hv
    simpa using h (e v) (by simpa using hv)
  · intro h v hv
    exact h (e.symm v) (by simpa using hv)

variable [FiniteDimensional ℝ F]

/-- In a finite-rank real bilinear bundle, strict positivity on nonzero diagonal vectors
defines an open subset of the total space. The forms are not required to be symmetric. -/
theorem isOpen_setOf_forall_bilinear_bundle_apply_self_pos :
    IsOpen {z : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
      (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) | ∀ v, v ≠ 0 → 0 < z.2 v v} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hcoord := (continuousAt_hom_bundle (RingHom.id ℝ) _).mp
    (continuousAt_id : ContinuousAt
      (id : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) → _) z)
  have hbase : ∀ᶠ w in 𝓝 z, w.1 ∈ (trivializationAt F V z.1).baseSet :=
    hcoord.1 ((trivializationAt F V z.1).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V z.1))
  have hpos : ∀ᶠ w in 𝓝 z, ∀ v : F, v ≠ 0 →
      0 < inCoordinates F V (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] ℝ)
        z.1 w.1 z.1 w.1 w.2 v v :=
    hcoord.2 (isOpen_setOf_forall_bilinear_apply_self_pos.mem_nhds
      ((forall_inCoordinates_bilinear_apply_self_pos_iff
        (mem_baseSet_trivializationAt F V z.1) z.2).mpr hz))
  filter_upwards [hbase, hpos] with w hw hp
  exact (forall_inCoordinates_bilinear_apply_self_pos_iff hw w.2).mp hp

/-- Positivity of a continuous family of bilinear fields on a compact subset of the base is
an open condition on the parameter. This applies in particular to symmetric metric fields. -/
theorem _root_.IsCompact.isOpen_setOf_forall_mem_forall_bilinear_apply_self_pos
    {P : Type*} [TopologicalSpace P] {K : Set B} (hK : IsCompact K)
    (b : P → ∀ x : B, V x →L[ℝ] V x →L[ℝ] ℝ)
    (hb : Continuous (fun z : P × B ↦
      TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) z.2 (b z.1 z.2))) :
    IsOpen {p | ∀ x ∈ K, ∀ v, v ≠ 0 → 0 < b p x v v} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  exact hK.eventually_forall_of_forall_eventually fun x hx ↦
    (isOpen_setOf_forall_bilinear_bundle_apply_self_pos.preimage hb).mem_nhds (hp x hx)

end TauCeti
