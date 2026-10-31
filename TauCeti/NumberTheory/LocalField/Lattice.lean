/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.Module.Compact
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Lattices over a nonarchimedean local field

Let `E` be a nonarchimedean local field with valuation ring `𝒪[E]`, and `V` a finite-dimensional
`E`-vector space with its module topology. A lattice in `V` is an `𝒪[E]`-submodule `L` that is
finitely generated and spans `V` over `E` (Mathlib's `Submodule.IsLattice E L`). This file shows
that every lattice is a compact open subgroup of `V`, and that its stabilizer `GL(L)` in the group
`V ≃ₗ[E] V` of linear automorphisms, with the forward-and-inverse topology of
`TauCeti.Topology.Algebra.Module.GeneralLinearGroup`, is a compact open subgroup. These are the
topological inputs of the stable-lattice theorem for compact groups acting on `V`.

The stabilizer is Mathlib's `MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V)` for the pointwise
action on subsets of `V`; it consists of the automorphisms `g` with `g L = L`. It is the group of
units of the monoid of endomorphisms mapping `L` into itself, which is already compact and open in
`Module.End E V`: an endomorphism is determined by the images of an `E`-basis of `V` contained
in `L`, and it maps `L` into itself as soon as it maps a finite generating set of `L` into `L`.

Openness only uses that `𝒪[E]` is open in `E`, so it is proved for any field with a valuative
topology; compactness uses that `𝒪[E]` is compact.

## Main results

* `Module.Basis.isOpen_span_range`: the `𝒪[E]`-span of a finite `E`-basis is open.
* `Submodule.IsLattice.isOpen`, `Submodule.IsLattice.isClosed`, `Submodule.IsLattice.isCompact`:
  a lattice is open, closed and compact.
* `Submodule.IsLattice.isOpen_setOf_mapsTo`, `Submodule.IsLattice.isCompact_setOf_mapsTo`: the
  endomorphisms mapping a lattice into itself form a compact open subset of `Module.End E V`.
* `Submodule.IsLattice.isOpen_stabilizer`, `Submodule.IsLattice.isCompact_stabilizer`: the
  stabilizer of a lattice in `V ≃ₗ[E] V` is open and compact.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open Module ValuativeRel Set
open scoped Pointwise

namespace Submodule

section ValuativeTopology

variable {E V : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V]

/-- The `𝒪[E]`-span of a finite `E`-basis of `V` is open: it is the set of vectors whose
coordinates all lie in the open subring `𝒪[E]`. -/
theorem _root_.Module.Basis.isOpen_span_range {ι : Type*} [Finite ι] (b : Basis ι E V) :
    IsOpen (span 𝒪[E] (range b) : Set V) := by
  have h : (span 𝒪[E] (range b) : Set V) =
      TauCeti.ModuleTopology.equivFunHomeomorph b ⁻¹' univ.pi fun _ => (𝒪[E] : Set E) := by
    ext x
    simp only [SetLike.mem_coe, Basis.mem_span_iff_repr_mem, mem_preimage, mem_univ_pi,
      TauCeti.ModuleTopology.equivFunHomeomorph_apply, Basis.equivFun_apply]
    exact forall_congr' fun i => ⟨fun ⟨a, h⟩ => h ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rw [h]
  exact (isOpen_set_pi finite_univ fun _ _ => Valuation.isOpen_integer).preimage
    (TauCeti.ModuleTopology.equivFunHomeomorph b).continuous

variable (L : Submodule 𝒪[E] V) [IsLattice E L]

/-- **A lattice is open.** It contains the `𝒪[E]`-span of an `E`-basis of `V`, which is open. -/
theorem IsLattice.isOpen : IsOpen (L : Set V) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  have := Module.Finite.of_isLattice (A := E) L
  have hs : ⊤ ≤ span E (L : Set V) := (IsLattice.span_eq_top (A := E) (M := L)).ge
  let b := Basis.ofSpan hs
  have : Finite _ := Module.Finite.finite_basis b
  exact isOpen_mono (span_le.mpr (Basis.ofSpan_subset hs)) b.isOpen_span_range

/-- **A lattice is closed**, being an open subgroup. -/
theorem IsLattice.isClosed : IsClosed (L : Set V) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  exact AddSubgroup.isClosed_of_isOpen L.toAddSubgroup (IsLattice.isOpen L)

/-- **The endomorphisms preserving a lattice form an open set** of `Module.End E V`. -/
theorem IsLattice.isOpen_setOf_mapsTo : IsOpen {f : Module.End E V | MapsTo f L L} := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
  obtain ⟨s, hs⟩ := IsLattice.fg (A := E) (M := L)
  have h : {f : Module.End E V | MapsTo f L L} = ⋂ v ∈ s, {f | f v ∈ L} := by
    ext f
    have h := image_span_subset (f.restrictScalars 𝒪[E]) (s : Set V) L
    rw [hs] at h
    simpa [mapsTo_iff_image_subset] using h
  rw [h]
  exact isOpen_biInter_finset fun v _ => (IsLattice.isOpen L).preimage
    (IsModuleTopology.continuous_of_linearMap (LinearMap.applyₗ v : Module.End E V →ₗ[E] V))

/-- **The stabilizer `GL(L)` of a lattice is open** in the group of linear automorphisms. -/
theorem IsLattice.isOpen_stabilizer :
    IsOpen (MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) : Set (V ≃ₗ[E] V)) := by
  have hc := TauCeti.continuous_linearEquiv_iff.mp
    (continuous_id : Continuous fun g : V ≃ₗ[E] V => g)
  have h : (MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) : Set (V ≃ₗ[E] V)) =
      (fun g : V ≃ₗ[E] V => (g : Module.End E V)) ⁻¹' {f | MapsTo f L L} ∩
        (fun g : V ≃ₗ[E] V => ((g⁻¹ : V ≃ₗ[E] V) : Module.End E V)) ⁻¹' {f | MapsTo f L L} := by
    ext g
    rw [SetLike.mem_coe, TauCeti.mem_stabilizer_set_iff_mapsTo]
    simp [LinearEquiv.smul_def]
  rw [h]
  exact ((IsLattice.isOpen_setOf_mapsTo L).preimage hc.1).inter
    ((IsLattice.isOpen_setOf_mapsTo L).preimage hc.2)

end ValuativeTopology

section LocalField

variable {E V : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V]
  (L : Submodule 𝒪[E] V) [IsLattice E L]

/-- **A lattice is compact**: it is finitely generated over the compact ring `𝒪[E]`. -/
theorem IsLattice.isCompact : IsCompact (L : Set V) := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
  have : ContinuousSMul 𝒪[E] V := ⟨((continuous_subtype_val.comp continuous_fst).smul
    continuous_snd).congr fun p => algebraMap_smul E p.1 p.2⟩
  exact isCompact_of_fg IsLattice.fg

/-- **The endomorphisms preserving a lattice form a compact set** of `Module.End E V`: such an
endomorphism is determined by the images in the compact lattice of an `E`-basis of `V` contained
in the lattice. -/
theorem IsLattice.isCompact_setOf_mapsTo : IsCompact {f : Module.End E V | MapsTo f L L} := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
  have := Module.Finite.of_isLattice (A := E) L
  have hs : ⊤ ≤ span E (L : Set V) := (IsLattice.span_eq_top (A := E) (M := L)).ge
  let b := Basis.ofSpan hs
  have : Finite _ := Module.Finite.finite_basis b
  have hclosed : IsClosed {f : Module.End E V | MapsTo f L L} := by
    have h : {f : Module.End E V | MapsTo f L L} = ⋂ x ∈ (L : Set V), {f | f x ∈ L} := by
      ext f
      simp [MapsTo]
    rw [h]
    exact isClosed_biInter fun x _ => (IsLattice.isClosed L).preimage
      (IsModuleTopology.continuous_of_linearMap (LinearMap.applyₗ x : Module.End E V →ₗ[E] V))
  refine ((isCompact_univ_pi fun _ => IsLattice.isCompact L).image
    (IsModuleTopology.continuous_of_linearMap (b.constr E).toLinearMap)).of_isClosed_subset
    hclosed fun f hf => ⟨fun i => f (b i), fun i _ => hf (Basis.ofSpan_subset hs ⟨i, rfl⟩),
      b.constr_self E f⟩

/-- **The stabilizer `GL(L)` of a lattice is compact**: it is the group of units of the compact
monoid of endomorphisms preserving `L`. -/
theorem IsLattice.isCompact_stabilizer :
    IsCompact (MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) : Set (V ≃ₗ[E] V)) := by
  have := Module.Finite.of_isLattice (A := E) L
  let T : Submonoid (Module.End E V) :=
    { carrier := {f | MapsTo f L L}
      mul_mem' := fun hf hg => hf.comp hg
      one_mem' := mapsTo_id _ }
  let e := TauCeti.generalLinearContinuousMulEquiv (K := E) (V := V)
  have he (u : LinearMap.GeneralLinearGroup E V) : ((e u : V ≃ₗ[E] V) : Module.End E V) = u := by
    rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
    exact congrArg (fun φ : LinearMap.GeneralLinearGroup E V ≃* (V ≃ₗ[E] V) =>
      (φ u : Module.End E V)) TauCeti.coe_generalLinearContinuousMulEquiv
  have h : (MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) : Set (V ≃ₗ[E] V)) =
      e '' (T.units : Set (LinearMap.GeneralLinearGroup E V)) := by
    ext g
    obtain ⟨u, rfl⟩ := e.surjective g
    rw [SetLike.mem_coe, TauCeti.mem_stabilizer_set_iff_mapsTo, e.injective.mem_set_image,
      SetLike.mem_coe, Submonoid.mem_units_iff, ← map_inv, ← he u, ← he u⁻¹]
    simp [T, LinearEquiv.smul_def]
  rw [h]
  exact (Submonoid.units_isCompact (IsLattice.isCompact_setOf_mapsTo L)).image e.continuous

end LocalField

end Submodule
