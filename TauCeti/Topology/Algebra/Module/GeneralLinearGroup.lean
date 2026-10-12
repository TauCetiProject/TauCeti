/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The topology of finite-dimensional linear automorphisms

The endomorphism algebra of a finite-dimensional vector space has its canonical module topology.
Mathlib's `IsModuleTopology.isTopologicalRing` supplies continuous composition. The unit
topology on that algebra records both an automorphism and its inverse. Transporting it
along Mathlib's `LinearMap.GeneralLinearGroup.generalLinearEquiv` equips linear automorphisms with
a topological group structure. In particular, continuity into this group is equivalent to
continuity of both the forward and inverse endomorphisms.

Over a field, the endomorphism algebra of a finite-dimensional space is itself finite-dimensional,
so its module topology is Hausdorff when the field is Hausdorff and locally compact when the field
is locally compact. The unit topology inherits both properties, so the linear automorphisms of a
finite-dimensional space over a Hausdorff locally compact field form a locally compact group. This
is the local-compactness input for the orthogonal point group over `ℝ` and `ℚ_p`.

Over a commutative topological ring the determinant is continuous on endomorphisms, being a
polynomial in the matrix entries in any finite basis, and hence `LinearEquiv.det` is a continuous
homomorphism from linear automorphisms to the units of the ring.
-/

public section

namespace TauCeti

open scoped Topology

section EndTopology

variable {K V : Type*} [CommSemiring K] [TopologicalSpace K]
  [AddCommMonoid V] [Module K V]

/-- The endomorphism algebra carries the canonical module topology. -/
noncomputable instance instTopologicalSpaceModuleEnd : TopologicalSpace (Module.End K V) :=
  moduleTopology K (Module.End K V)

end EndTopology

section EndRing

variable {K V : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K (Module.End K V)]

/-- The endomorphism algebra is a topological ring when it is finite over the scalar ring. -/
instance instIsTopologicalRingModuleEnd : IsTopologicalRing (Module.End K V) :=
  IsModuleTopology.isTopologicalRing K (Module.End K V)

end EndRing

variable {K V : Type*} [CommSemiring K] [TopologicalSpace K]
  [AddCommMonoid V] [Module K V]

/-- A linear automorphism has the topology induced by its forward and inverse endomorphisms. -/
noncomputable instance instTopologicalSpaceLinearEquiv : TopologicalSpace (V ≃ₗ[K] V) :=
  TopologicalSpace.induced
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm inferInstance

section TopologicalGroup

variable [ContinuousMul (Module.End K V)]

/-- Linear automorphisms form a topological group in the forward-and-inverse topology. -/
instance instIsTopologicalGroupLinearEquiv : IsTopologicalGroup (V ≃ₗ[K] V) :=
  isTopologicalGroup_induced
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.toMonoidHom

end TopologicalGroup

/-- The canonical equivalence between invertible endomorphisms and linear automorphisms is
continuous in both directions. -/
noncomputable def generalLinearContinuousMulEquiv :
    LinearMap.GeneralLinearGroup K V ≃ₜ* V ≃ₗ[K] V where
  __ := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    convert (continuous_id : Continuous (fun x : LinearMap.GeneralLinearGroup K V => x)) using 1
    funext x
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm_apply_apply x
  continuous_invFun := continuous_induced_dom

/-- The topological equivalence has Mathlib's canonical algebraic equivalence as its underlying
multiplicative equivalence. -/
@[simp]
theorem coe_generalLinearContinuousMulEquiv :
    (generalLinearContinuousMulEquiv (K := K) (V := V) :
      LinearMap.GeneralLinearGroup K V ≃* V ≃ₗ[K] V) =
      LinearMap.GeneralLinearGroup.generalLinearEquiv K V := (rfl)

/-- A family of linear automorphisms is continuous exactly when its forward and inverse
endomorphisms are both continuous. -/
theorem continuous_linearEquiv_iff {X : Type*} [TopologicalSpace X]
    {f : X → V ≃ₗ[K] V} :
    Continuous f ↔
      Continuous (fun x => (f x : Module.End K V)) ∧
      Continuous (fun x => (((f x)⁻¹ : V ≃ₗ[K] V) : Module.End K V)) := by
  let e := generalLinearContinuousMulEquiv (K := K) (V := V)
  have h := e.symm.isEmbedding.isInducing.continuous_iff (f := f)
  rw [h, Units.continuous_iff]
  let g := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
  have he : e.toMulEquiv = g := rfl
  have he_symm (a : V ≃ₗ[K] V) : e.symm.toHomeomorph a = g.symm a := by
    exact congrArg (fun t : LinearMap.GeneralLinearGroup K V ≃* V ≃ₗ[K] V =>
      t.symm a) he
  simp only [Function.comp_def, he_symm]
  dsimp only [g]
  have h_forward (a : V ≃ₗ[K] V) :
      (((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm a :
        LinearMap.GeneralLinearGroup K V) : Module.End K V) = (a : Module.End K V) := rfl
  have h_inverse (a : V ≃ₗ[K] V) :
      (((((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm a)⁻¹ :
        LinearMap.GeneralLinearGroup K V) : Module.End K V)) =
        ((a⁻¹ : V ≃ₗ[K] V) : Module.End K V) := rfl
  simp only [h_forward, h_inverse]

/-- The underlying endomorphism varies continuously with a linear automorphism. -/
@[fun_prop]
theorem continuous_linearEquiv_toLinearMap :
    Continuous (fun e : V ≃ₗ[K] V => (e : Module.End K V)) :=
  (continuous_linearEquiv_iff.mp (continuous_id : Continuous (fun e : V ≃ₗ[K] V => e))).1

section Basis

variable [TopologicalSpace V] [IsModuleTopology K V]

/-- A family of endomorphisms is continuous exactly when its values on the vectors of a finite
basis vary continuously. -/
theorem _root_.Module.Basis.continuous_iff_apply {X ι : Type*} [TopologicalSpace X]
    [Finite ι] (b : Module.Basis ι K V) (f : X → Module.End K V) :
    Continuous f ↔ ∀ i, Continuous (fun x ↦ f x (b i)) := by
  let _ : ContinuousAdd V := IsModuleTopology.toContinuousAdd K V
  let _ : ContinuousAdd (Module.End K V) :=
    IsModuleTopology.toContinuousAdd K (Module.End K V)
  constructor
  · intro hf i
    exact (IsModuleTopology.continuous_of_linearMap
      ((LinearMap.applyₗ : V →ₗ[K] Module.End K V →ₗ[K] V) (b i))).comp hf
  · intro h
    let : IsModuleTopology K (ι → V) := inferInstance
    have hvalues : Continuous (fun x i ↦ f x (b i)) := continuous_pi h
    have hconstr : Continuous ((b.constr K).toLinearMap : (ι → V) → Module.End K V) :=
      IsModuleTopology.continuous_of_linearMap (b.constr K).toLinearMap
    exact (hconstr.comp hvalues).congr fun x ↦ b.constr_self K (f x)

end Basis

section FiniteDimensional

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalSemiring K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [TopologicalSpace V] [IsModuleTopology K V]

/-- The endomorphism algebra of a finite-dimensional space over a Hausdorff field is Hausdorff. -/
instance instT2SpaceModuleEnd [T2Space K] : T2Space (Module.End K V) :=
  t2Space_moduleTopology

/-- The endomorphism algebra of a finite-dimensional space over a locally compact field is
locally compact. -/
instance instLocallyCompactSpaceModuleEnd [LocallyCompactSpace K] :
    LocallyCompactSpace (Module.End K V) :=
  locallyCompactSpace_moduleTopology

/-- The linear automorphisms of a finite-dimensional space over a Hausdorff field form a
Hausdorff space. -/
instance instT2SpaceLinearEquiv [T2Space K] : T2Space (V ≃ₗ[K] V) :=
  (generalLinearContinuousMulEquiv (K := K) (V := V)).toHomeomorph.symm.isEmbedding.t2Space

end FiniteDimensional

section LocallyCompact

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [LocallyCompactSpace K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The linear automorphisms of a finite-dimensional space over a Hausdorff locally compact field
form a locally compact group: the automorphism group is closed in the product of two copies of the
locally compact endomorphism algebra, through an automorphism and its inverse. -/
instance instLocallyCompactSpaceLinearEquiv : LocallyCompactSpace (V ≃ₗ[K] V) :=
  (generalLinearContinuousMulEquiv (K := K) (V := V)).toHomeomorph.locallyCompactSpace_iff.mp
    inferInstance

end LocallyCompact

section Det

variable {K V : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V]

/-- The determinant of an endomorphism is continuous in the module topology: in a finite basis it
is a polynomial in the matrix entries, and without a finite basis it is the constant `1`. -/
@[fun_prop]
theorem continuous_linearMap_det : Continuous (LinearMap.det : Module.End K V → K) := by
  classical
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s K V)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have h : Continuous (LinearMap.toMatrix b b : Module.End K V → Matrix s s K) :=
      IsModuleTopology.continuous_of_linearMap (LinearMap.toMatrix b b).toLinearMap
    exact h.matrix_det.congr fun f ↦ LinearMap.det_toMatrix b f
  · simp only [LinearMap.coe_det, H, dite_false]
    exact continuous_const

/-- The determinant of a linear automorphism is continuous as a map to the units of the scalar
ring. -/
@[fun_prop]
theorem continuous_linearEquiv_det :
    Continuous (LinearEquiv.det : (V ≃ₗ[K] V) → Kˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · simp_rw [Function.comp_def, LinearEquiv.coe_det]
    exact continuous_linearMap_det.comp continuous_linearEquiv_toLinearMap
  · simp_rw [LinearEquiv.coe_inv_det]
    exact continuous_linearMap_det.comp
      (continuous_linearEquiv_iff.mp (continuous_id : Continuous fun e : V ≃ₗ[K] V ↦ e)).2

end Det

end TauCeti
