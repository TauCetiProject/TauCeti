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
import TauCeti.NumberTheory.LocalField.Topology

/-!
# Lattices over a nonarchimedean local field

Let `E` be a nonarchimedean local field with valuation ring `𝒪[E]`, and `V` a finite-dimensional
`E`-vector space with its module topology. A lattice in `V` is an `𝒪[E]`-submodule `L` that is
finitely generated and spans `V` over `E` (Mathlib's `Submodule.IsFullLattice E L`). This file
shows that every lattice is a compact open subgroup of `V`, and that its stabilizer `GL(L)` in the
group `V ≃ₗ[E] V` of linear automorphisms, with the forward-and-inverse topology of
`TauCeti.Topology.Algebra.Module.GeneralLinearGroup`, is a compact open subgroup. These are the
topological inputs of the stable-lattice theorem for compact groups acting on `V`. In an
`𝒪[E]`-basis of `L`, taking matrices identifies this stabilizer with `GL_n(𝒪[E])` as a topological
group, `n` being the size of the basis.

The stabilizer is Mathlib's `MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V)` for the pointwise
action on subsets of `V`; it consists of the automorphisms `g` with `g L = L`. It is the group of
units of the monoid of endomorphisms mapping `L` into itself, which is already compact and open in
`Module.End E V`: an endomorphism is determined by the images of an `E`-basis of `V` contained
in `L`, and it maps `L` into itself as soon as it maps a finite generating set of `L` into `L`.

Openness, and the fact that the subspace topology on a lattice is its `𝒪[E]`-module topology,
only use that `𝒪[E]` is open in `E`, so they are proved for any field with a valuative topology;
compactness uses that `𝒪[E]` is compact. The identification of the stabilizer with `GL_n` uses
only the topology of the coefficients, so it is proved for a full lattice over any subring of a
topological commutative ring.

## Main results

* `Module.Basis.isOpen_span_range`: the `𝒪[E]`-span of a finite `E`-basis is open.
* `Submodule.IsFullLattice.isOpen`, `Submodule.IsFullLattice.isClosed`,
  `Submodule.IsFullLattice.isCompact`: a lattice is open, closed and compact.
* `Submodule.exists_isFullLattice_subset_of_isCompact`,
  `Submodule.exists_isFullLattice_subset_of_mem_nhds`: every compact subset of `V` lies in a
  lattice, and every neighbourhood of `0` contains one.
* `Submodule.IsFullLattice.isModuleTopology`: the subspace topology on a lattice is its
  `𝒪[E]`-module topology.
* `Submodule.IsFullLattice.isOpen_setOf_mapsTo`, `Submodule.IsFullLattice.isCompact_setOf_mapsTo`:
  the endomorphisms mapping a lattice into itself form a compact open subset of `Module.End E V`.
* `Submodule.IsFullLattice.isOpen_stabilizer`, `Submodule.IsFullLattice.isCompact_stabilizer`: the
  stabilizer of a lattice in `V ≃ₗ[E] V` is open and compact.
* `Module.Basis.stabilizerContinuousMulEquivGL`: in an `R`-basis of a full lattice over a subring
  `R` of a topological ring, such as `𝒪[E]`, the stabilizer of the lattice is `GL_n(R)` as a
  topological group.

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
    exact forall_congr' fun i => ⟨fun ⟨a, h⟩ => h ▸ a.property, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rw [h]
  exact (isOpen_set_pi finite_univ fun _ _ => Valuation.isOpen_integer).preimage
    (TauCeti.ModuleTopology.equivFunHomeomorph b).continuous

variable (L : Submodule 𝒪[E] V) [IsFullLattice E L]

/-- **A lattice is open.** It contains the `𝒪[E]`-span of an `E`-basis of `V`, which is open. -/
theorem IsFullLattice.isOpen : IsOpen (L : Set V) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  have := Module.Finite.of_isFullLattice (A := E) L
  have hs : ⊤ ≤ span E (L : Set V) := (IsFullLattice.span_eq_top (A := E) (M := L)).ge
  let b := Basis.ofSpan hs
  have : Finite _ := Module.Finite.finite_basis b
  exact isOpen_mono (span_le.mpr (Basis.ofSpan_subset hs)) b.isOpen_span_range

/-- **A lattice is closed**, being an open subgroup. -/
theorem IsFullLattice.isClosed : IsClosed (L : Set V) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  exact AddSubgroup.isClosed_of_isOpen L.toAddSubgroup (IsFullLattice.isOpen L)

omit L [IsFullLattice E L] in
/-- **Every compact set lies in a lattice.** Finitely many translates `c + L₀` of the lattice
`L₀` spanned by a basis cover a compact set `C`, and `C` lies in the lattice spanned by `L₀` and the
centres `c`. -/
theorem exists_isFullLattice_subset_of_isCompact [FiniteDimensional E V] {C : Set V}
    (hC : IsCompact C) : ∃ L : Submodule 𝒪[E] V, L.IsFullLattice E ∧ C ⊆ L := by
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  let b := Module.finBasis E V
  obtain ⟨T, -, hCT⟩ := hC.elim_nhds_subcover (fun c ↦ (· - c) ⁻¹' (span 𝒪[E] (range b) : Set V))
    fun c _ ↦ (b.isOpen_span_range.preimage (continuous_sub_right c)).mem_nhds (by simp)
  refine ⟨span 𝒪[E] (range b ∪ T), isFullLattice_span ((finite_range b).union T.finite_toSet)
    (eq_top_iff.2 (b.span_eq ▸ span_mono subset_union_left)), fun x hx ↦ ?_⟩
  obtain ⟨c, hcT, hxc⟩ := mem_iUnion₂.1 (hCT hx)
  -- `x = c + (x - c)` with `c` a centre and `x - c` in the span of the basis.
  rw [← sub_add_cancel x c]
  exact add_mem (span_mono subset_union_left hxc) (subset_span (subset_union_right hcT))

/-- **A lattice carries the module topology.** The subspace topology on a lattice `L ⊆ V` is its
`𝒪[E]`-module topology. -/
instance IsFullLattice.isModuleTopology : IsModuleTopology 𝒪[E] L := by
  -- For a finite generating set `s`, the map `𝒪[E] ^ s → L` is a quotient map for the subspace
  -- topology: it is the restriction of the open surjection `E ^ s → V` to the open `𝒪[E] ^ s`.
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup E V
  have : ContinuousSMul 𝒪[E] V := ⟨((continuous_subtypeVal.comp continuous_fst).smul
    continuous_snd).congr fun p => algebraMap_smul E p.1 p.2⟩
  obtain ⟨s, hs⟩ := IsLattice.fg (A := E) (M := L)
  -- `L` is the image of `𝒪[E] ^ s` under `φ`, and `V` is the image of `E ^ s` under `Φ`.
  let φ : (s → 𝒪[E]) →ₗ[𝒪[E]] L :=
    Fintype.linearCombination 𝒪[E] fun i : s => ⟨i, hs ▸ subset_span i.property⟩
  let Φ : (s → E) →ₗ[E] V := Fintype.linearCombination E fun i : s => (i : V)
  have hΦ : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, Subtype.range_coe_subtype,
      Finset.setOfPred_mem, ← span_span_of_tower 𝒪[E], hs, IsFullLattice.span_eq_top]
  have hcomm (w : s → 𝒪[E]) : (φ w : V) = Φ fun i => (w i : E) := by
    simp only [φ, Φ, Fintype.linearCombination_apply, coe_sum, coe_smul]
    exact Finset.sum_congr rfl fun i _ => (algebraMap_smul E (w i) (i : V)).symm
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨f, -, rfl⟩ := mem_span_finset.mp (hs ▸ hx)
    refine ⟨fun i => f i, Subtype.ext ?_⟩
    simp [φ, Fintype.linearCombination_apply, Finset.sum_attach s fun i => f i • i]
  -- An open set `W` of `𝒪[E] ^ s` has open image `φ W = L ∩ Φ W` in the subspace `L`.
  refine IsModuleTopology.of_continuous_id ?_
  rw [ModuleTopology.eq_coinduced_of_surjective hφ, continuous_def]
  intro U hU
  rw [isOpen_coinduced] at hU
  rw [preimage_id, ← image_preimage_eq U hφ]
  have hopen : IsOpen (Φ '' ((fun w : s → 𝒪[E] => fun i => (w i : E)) '' (φ ⁻¹' U))) :=
    IsModuleTopology.isOpenMap_of_surjective hΦ _
      ((Topology.IsOpenEmbedding.piMap fun _ =>
        Valuation.isOpen_integer.isOpenEmbedding_subtypeVal).isOpenMap _ hU)
  refine isOpen_induced_iff.mpr ⟨_, hopen, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨-, ⟨w, hw, rfl⟩, hx⟩
    exact ⟨w, hw, Subtype.ext ((hcomm w).trans hx)⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (hcomm w).symm⟩

/-- **The endomorphisms preserving a lattice form an open set** of `Module.End E V`. -/
theorem IsFullLattice.isOpen_setOf_mapsTo : IsOpen {f : Module.End E V | MapsTo f L L} := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
  obtain ⟨s, hs⟩ := IsLattice.fg (A := E) (M := L)
  have h : {f : Module.End E V | MapsTo f L L} = ⋂ v ∈ s, {f | f v ∈ L} := by
    ext f
    have h := image_span_subset (f.restrictScalars 𝒪[E]) (s : Set V) L
    rw [hs] at h
    simpa [mapsTo_iff_image_subset] using h
  rw [h]
  exact isOpen_biInter_finset fun v _ => (IsFullLattice.isOpen L).preimage
    (IsModuleTopology.continuous_of_linearMap (LinearMap.applyₗ v : Module.End E V →ₗ[E] V))

/-- **The stabilizer `GL(L)` of a lattice is open** in the group of linear automorphisms. -/
theorem IsFullLattice.isOpen_stabilizer :
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
  exact ((IsFullLattice.isOpen_setOf_mapsTo L).preimage hc.1).inter
    ((IsFullLattice.isOpen_setOf_mapsTo L).preimage hc.2)

end ValuativeTopology

section Matrix

variable {E V : Type*} [CommRing E] [TopologicalSpace E] [IsTopologicalSemiring E]
  [AddCommGroup V] [Module E V] {R : Subring E} [Module R V] [IsScalarTower R E V]
  {L : Submodule R V} [IsFullLattice E L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The stabilizer of a lattice is `GL_n` of the coefficients as a topological group.** For a
subring `R` of a topological commutative ring `E` and an `R`-basis `b` of a full lattice `L ⊆ V`,
the isomorphism `b.stabilizerMulEquivGL E` from the stabilizer of `L` in `V ≃ₗ[E] V` to
`GL ι R`, sending an automorphism to its matrix in `b`, is a homeomorphism for the subspace
topology on the stabilizer and the unit topology on matrices over `R`. For `R = 𝒪[E]` this
identifies the stabilizer of a lattice over a nonarchimedean local field with `GL_n(𝒪[E])`. -/
noncomputable def _root_.Module.Basis.stabilizerContinuousMulEquivGL (b : Basis ι R L) :
    MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) ≃ₜ* GL ι R where
  __ := b.stabilizerMulEquivGL E
  continuous_toFun := by
    let b' := b.extendOfIsFullLattice E
    let e := TauCeti.generalLinearContinuousMulEquiv (K := E) (V := V)
    -- Read in `E`, the matrix of `g` in `b` is the matrix of `g` in the ambient basis `b'`.
    refine (Topology.IsInducing.subtypeVal.matrix_map.units_map
      (f := (algebraMap R E).mapMatrix.toMonoidHom)).continuous_iff.mpr ?_
    refine ((Continuous.units_map (LinearMap.toMatrixAlgEquiv b').toMonoidHom
      (IsModuleTopology.continuous_of_linearMap (LinearMap.toMatrix b' b').toLinearMap)).comp
      ((map_continuous e.symm).comp continuous_subtypeVal)).congr fun g =>
        Units.ext (Matrix.ext fun i j => ?_)
    -- Entrywise, this is the formula `b.map_stabilizerMulEquivGL_apply` for the matrix of `g`.
    simpa [b', e, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply] using
      congr_fun₂ (b.map_stabilizerMulEquivGL_apply g).symm i j
  continuous_invFun := by
    have : ContinuousAdd (Module.End E V) := IsModuleTopology.toContinuousAdd E _
    let b' := b.extendOfIsFullLattice E
    let e := TauCeti.generalLinearContinuousMulEquiv (K := E) (V := V)
    -- The automorphism attached to `u` is the linear map with matrix `u` in the basis `b'`.
    refine Continuous.subtype_mk (((map_continuous e).comp
      ((Continuous.units_map (Matrix.toLinAlgEquiv b').toMonoidHom
        (IsModuleTopology.continuous_of_linearMap (Matrix.toLin b' b').toLinearMap)).comp
      (Continuous.units_map (algebraMap R E).mapMatrix.toMonoidHom
        (continuous_id.matrix_map continuous_subtypeVal)))).congr fun u =>
      LinearEquiv.toLinearMap_injective (LinearMap.ext fun v => ?_)) _
    -- On each vector, this is the formula `b.stabilizerMulEquivGL_symm_apply` for the automorphism.
    simpa [b', e, Matrix.toLinAlgEquiv_apply, Matrix.toLin_apply] using
      congr($(b.stabilizerMulEquivGL_symm_apply (K := E) u) v).symm

/-- The topological isomorphism `b.stabilizerContinuousMulEquivGL` has the matrix isomorphism
`b.stabilizerMulEquivGL E` as its underlying multiplicative equivalence. -/
@[simp]
theorem _root_.Module.Basis.coe_stabilizerContinuousMulEquivGL (b : Basis ι R L) :
    (b.stabilizerContinuousMulEquivGL :
      MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) ≃* GL ι R) = b.stabilizerMulEquivGL E :=
  (rfl)

/-- Applied to an automorphism, `b.stabilizerContinuousMulEquivGL` is the matrix isomorphism
`b.stabilizerMulEquivGL E`. -/
@[simp]
theorem _root_.Module.Basis.stabilizerContinuousMulEquivGL_apply (b : Basis ι R L)
    (g : MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V)) :
    b.stabilizerContinuousMulEquivGL g = b.stabilizerMulEquivGL E g :=
  (rfl)

/-- The inverse of `b.stabilizerContinuousMulEquivGL` is the inverse of the matrix isomorphism
`b.stabilizerMulEquivGL E`. -/
@[simp]
theorem _root_.Module.Basis.stabilizerContinuousMulEquivGL_symm_apply (b : Basis ι R L)
    (u : GL ι R) :
    (b.stabilizerContinuousMulEquivGL (E := E) (V := V)).symm u =
      (b.stabilizerMulEquivGL E).symm u :=
  (rfl)

end Matrix

section LocalField

variable {E V : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V]
  (L : Submodule 𝒪[E] V) [IsFullLattice E L]

/-- **A lattice is compact**: it is finitely generated over the compact ring `𝒪[E]`. -/
theorem IsFullLattice.isCompact : IsCompact (L : Set V) := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
  have : ContinuousSMul 𝒪[E] V := ⟨((continuous_subtypeVal.comp continuous_fst).smul
    continuous_snd).congr fun p => algebraMap_smul E p.1 p.2⟩
  exact isCompact_of_fg (IsLattice.fg E L)

/-- **The endomorphisms preserving a lattice form a compact set** of `Module.End E V`: such an
endomorphism is determined by the images in the compact lattice of an `E`-basis of `V` contained
in the lattice. -/
theorem IsFullLattice.isCompact_setOf_mapsTo : IsCompact {f : Module.End E V | MapsTo f L L} := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
  have := Module.Finite.of_isFullLattice (A := E) L
  have hs : ⊤ ≤ span E (L : Set V) := (IsFullLattice.span_eq_top (A := E) (M := L)).ge
  let b := Basis.ofSpan hs
  have : Finite _ := Module.Finite.finite_basis b
  have hclosed : IsClosed {f : Module.End E V | MapsTo f L L} := by
    have h : {f : Module.End E V | MapsTo f L L} = ⋂ x ∈ (L : Set V), {f | f x ∈ L} := by
      ext f
      simp [MapsTo]
    rw [h]
    exact isClosed_biInter fun x _ => (IsFullLattice.isClosed L).preimage
      (IsModuleTopology.continuous_of_linearMap (LinearMap.applyₗ x : Module.End E V →ₗ[E] V))
  refine ((isCompact_univ_pi fun _ => IsFullLattice.isCompact L).image
    (IsModuleTopology.continuous_of_linearMap (b.constr E).toLinearMap)).of_isClosed_subset
    hclosed fun f hf => ⟨fun i => f (b i), fun i _ => hf (Basis.ofSpan_subset hs ⟨i, rfl⟩),
      b.constr_self E f⟩

/-- **The stabilizer `GL(L)` of a lattice is compact**: it is the group of units of the compact
monoid of endomorphisms preserving `L`. -/
theorem IsFullLattice.isCompact_stabilizer :
    IsCompact (MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) : Set (V ≃ₗ[E] V)) := by
  have := Module.Finite.of_isFullLattice (A := E) L
  let T : Submonoid (Module.End E V) :=
    { carrier := {f | MapsTo f L L}
      mul_mem' := fun hf hg => hf.comp hg
      one_mem' := mapsTo_id _ }
  let e := TauCeti.generalLinearContinuousMulEquiv (K := E) (V := V)
  have h : (MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) : Set (V ≃ₗ[E] V)) =
      e '' (T.units : Set (LinearMap.GeneralLinearGroup E V)) := by
    ext g
    obtain ⟨u, rfl⟩ := e.surjective g
    rw [SetLike.mem_coe, TauCeti.mem_stabilizer_set_iff_mapsTo, e.injective.mem_set_image,
      SetLike.mem_coe, Submonoid.mem_units_iff, ← map_inv]
    simp [T, e, LinearEquiv.smul_def, ← TauCeti.coe_generalLinearContinuousMulEquiv_apply]
  rw [h]
  exact (Submonoid.units_isCompact (IsFullLattice.isCompact_setOf_mapsTo L)).image e.continuous

omit L [IsFullLattice E L] in
/-- **Every neighbourhood of `0` contains a lattice.** Small scalars map the compact lattice `L₀`
spanned by a basis into the neighbourhood (tube lemma), and `a • L₀` is a lattice for `a ≠ 0`. -/
theorem exists_isFullLattice_subset_of_mem_nhds [FiniteDimensional E V] {N : Set V}
    (hN : N ∈ nhds (0 : V)) : ∃ L : Submodule 𝒪[E] V, L.IsFullLattice E ∧ (L : Set V) ⊆ N := by
  let L₀ := span 𝒪[E] (range (Module.finBasis E V))
  have hL₀ : L₀.IsFullLattice E :=
    isFullLattice_span (finite_range _) (Module.finBasis E V).span_eq
  have hev : ∀ᶠ a in nhds (0 : E), ∀ v ∈ (L₀ : Set V), a • v ∈ N :=
    (IsFullLattice.isCompact L₀).eventually_forall_of_forall_eventually fun v _ ↦
      (continuous_smul.tendsto ((0 : E), v)).eventually (by simpa using hN)
  obtain ⟨a, ha, ha0⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and
    (self_mem_nhdsWithin (s := {(0 : E)}ᶜ))).exists
  refine ⟨Units.mk0 a ha0 • L₀, IsFullLattice.smul E L₀ _, fun x hx ↦ ?_⟩
  obtain ⟨v, hv, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).1 hx
  exact ha v hv

end LocalField

end Submodule
