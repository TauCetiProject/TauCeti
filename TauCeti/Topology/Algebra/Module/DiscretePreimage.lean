/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Topology.Algebra.Module.Quotient

/-!
# The preimage of a discrete subgroup modulo a subgroup

Let `E` be a real topological vector space, `L` a subgroup of `E`, and `f : E → E'` a continuous
linear map, over a ring `K` such as `ℝ` or `ℂ`, which carries `L` into a discrete subgroup `L'`
of `E'`. In the orbit space `E / L` of translation by `L`, consider the subgroup `f⁻¹(L') / L`.
This file shows that it is closed when `L'` is closed, and that its identity component is the
image of `ker f`. Combined with `Submodule.orbitRelQuotientComapQuotientEquiv`, which identifies
the quotient of `f⁻¹(L') / L` by the image of `ker f` with `(L' ∩ range f) / f(L)`, this
describes the component group of `f⁻¹(L') / L`.

For lattices `L ⊆ E` and `L' ⊆ E'` in complex vector spaces and a complex linear map `f` with
`f(L) ⊆ L'`, the subgroup `f⁻¹(L') / L` is the kernel of the homomorphism of complex tori
`E / L → E' / L'` induced by `f`. Its identity component is the image of `ker f`, which as a
group is `ker f / (L ∩ ker f)`, a complex torus because `L ∩ ker f` is a full lattice in `ker f`
(`ZLattice.isZLattice_comap_ker_subtype`); its component group is `(L' ∩ range f) / f(L)`.

## Main results

* `Submodule.isClosed_orbitRelQuotient_mk_image_preimage`: `f⁻¹(L') / L` is closed in `E / L`.
* `Submodule.connectedComponentIn_orbitRelQuotient_mk_image_preimage`: the connected component
  of `0` in `f⁻¹(L') / L` is the image of `ker f`.
* `Submodule.coe_addSubgroupOf_eq_connectedComponent_zero`: the same statement inside the
  subgroup `f⁻¹(L') / L`, in the form used by `Submodule.orbitRelQuotientComapQuotientEquiv`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.2.
-/

public section

open Set Pointwise

variable {K : Type*} [Ring K] {E : Type*} [AddCommGroup E] [Module K E]
  {E' : Type*} [AddCommGroup E'] [Module K E'] (L : Submodule ℤ E) {L' : Submodule ℤ E'}
  (f : E →ₗ[K] E')

/-- Let `U` meet `L'` only in `0`, and let `C ⊆ L'` be stable under translation by `f(L)`. For
`x ∈ f⁻¹(L')`, the orbit of `x` lies in the image of `f⁻¹(C + U)` exactly when `f x ∈ C`. -/
private theorem orbitRelQuotient_mk_mem_image_preimage_add_iff {U C : Set E'} (h0 : (0 : E') ∈ U)
    (hU : ∀ y ∈ U, y ∈ L' → y = 0) (hC : C ⊆ L') (hCL : ∀ c ∈ C, ∀ l ∈ L, c - f l ∈ C)
    (hf : L.map (f.restrictScalars ℤ) ≤ L') {x : E} (hx : f x ∈ L') :
    _root_.Quotient.mk (AddAction.orbitRel L E) x ∈
        _root_.Quotient.mk (AddAction.orbitRel L E) '' (f ⁻¹' (C + U)) ↔ f x ∈ C := by
  refine ⟨fun ⟨y, ⟨c, hc, u, hu, hcu⟩, hyx⟩ ↦ ?_, fun h ↦ ⟨x, ⟨f x, h, 0, h0, add_zero _⟩, rfl⟩⟩
  replace hcu : c + u = f y := hcu
  rw [_root_.Quotient.eq, L.orbitRel_apply_iff_sub_mem] at hyx
  have hl : f (y - x) ∈ L' := hf ⟨y - x, hyx, rfl⟩
  -- `u = f (y - x) + f x - c` lies in `L'` and in `U`, so it vanishes.
  have hu0 : u = 0 := hU u hu <| by
    have : u = f (y - x) + f x - c := by rw [map_sub, ← hcu]; abel
    exact this ▸ L'.sub_mem (L'.add_mem hl hx) (hC hc)
  have : f x = c - f (y - x) := by rw [map_sub, ← hcu, hu0]; abel
  exact this ▸ hCL c hc _ hyx

variable [TopologicalSpace E] [TopologicalSpace E']

/-- If `f` carries `L` into the closed subgroup `L'`, then `f⁻¹(L') / L` is closed in the orbit
space of translation by `L`. For lattices and a complex linear `f`, it is the kernel of the
induced homomorphism of complex tori. -/
theorem Submodule.isClosed_orbitRelQuotient_mk_image_preimage (hL' : IsClosed (L' : Set E'))
    (hfc : Continuous f) (hf : L.map (f.restrictScalars ℤ) ≤ L') :
    IsClosed (_root_.Quotient.mk (AddAction.orbitRel L E) '' (f ⁻¹' L')) :=
  isClosed_orbitRelQuotient_mk_image (S := L'.comap (f.restrictScalars ℤ))
    (Submodule.map_le_iff_le_comap.1 hf) (hL'.preimage hfc)

variable [ContinuousAdd E] [Module ℝ K] [Module ℝ E] [ContinuousSMul ℝ E] [IsScalarTower ℝ K E]
  [ContinuousAdd E']

/-- If `f` carries `L` into the discrete subgroup `L'`, then the connected component of `0` in
`f⁻¹(L') / L`, inside the orbit space of translation by `L`, is the image of `ker f`. For
lattices and a complex linear `f`, this is the identity component of the kernel of the induced
homomorphism of complex tori. -/
theorem Submodule.connectedComponentIn_orbitRelQuotient_mk_image_preimage [DiscreteTopology L']
    (hfc : Continuous f) (hf : L.map (f.restrictScalars ℤ) ≤ L') :
    connectedComponentIn (_root_.Quotient.mk (AddAction.orbitRel L E) '' (f ⁻¹' L')) 0 =
      _root_.Quotient.mk (AddAction.orbitRel L E) '' (LinearMap.ker f) := by
  set π := _root_.Quotient.mk (AddAction.orbitRel L E)
  have hπ0 : π 0 = 0 := L.orbitRelQuotient_mk_zero
  have hker : (LinearMap.ker f : Set E) ⊆ f ⁻¹' L' := fun x hx ↦ by
    simp [LinearMap.mem_ker.1 hx]
  refine Subset.antisymm ?_ <| IsPreconnected.subset_connectedComponentIn ?_
    ⟨0, (LinearMap.ker f).zero_mem, hπ0⟩ (image_mono hker)
  swap
  · exact ((LinearMap.ker f).restrictScalars ℝ).convex.isPreconnected.image _
      continuous_quotient_mk'.continuousOn
  -- A neighbourhood `U` of `0` meeting `L'` only in `0`.
  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete {(0 : L')})
  have hU0 : ∀ y ∈ U, y ∈ L' → y = 0 := fun y hy hyL ↦
    congrArg Subtype.val (show (⟨y, hyL⟩ : L') ∈ ({0} : Set L') from hU ▸ hy)
  have h0U : (0 : E') ∈ U := by
    have : (0 : L') ∈ Subtype.val ⁻¹' U := hU ▸ rfl
    exact this
  -- Split `f⁻¹(L') / L` into two relatively open pieces, according to whether `f x` lies in
  -- `f(L)`; the connected component of `0` lies in the first piece.
  set C : Set E' := ↑(L.map (f.restrictScalars ℤ))
  have hC : C ⊆ L' := hf
  have hCL : ∀ c ∈ C, ∀ l ∈ L, c - f l ∈ C := fun c hc l hl ↦
    (L.map (f.restrictScalars ℤ)).sub_mem hc ⟨l, hl, rfl⟩
  have hDL : ∀ c ∈ (L' : Set E') \ C, ∀ l ∈ L, c - f l ∈ (L' : Set E') \ C :=
    fun c ⟨hc, hcC⟩ l hl ↦ ⟨L'.sub_mem hc (hf ⟨l, hl, rfl⟩), fun h ↦ hcC <| by
      simpa [C] using (L.map (f.restrictScalars ℤ)).add_mem h ⟨l, hl, rfl⟩⟩
  have hopen (D : Set E') : IsOpen (π '' (f ⁻¹' (D + U))) :=
    AddAction.isOpenQuotientMap_quotientMk.isOpenMap _ ((hUo.add_left).preimage hfc)
  have key₁ {x : E} (hx : f x ∈ L') := orbitRelQuotient_mk_mem_image_preimage_add_iff L f h0U
    hU0 hC hCL hf hx
  have key₂ {x : E} (hx : f x ∈ L') := orbitRelQuotient_mk_mem_image_preimage_add_iff L f h0U
    hU0 sdiff_subset hDL hf hx
  have hsub := connectedComponentIn_subset (π '' (f ⁻¹' L')) 0
  have hmem : (0 : AddAction.orbitRel.Quotient L E) ∈ connectedComponentIn (π '' (f ⁻¹' L')) 0 :=
    mem_connectedComponentIn ⟨0, by simp, hπ0⟩
  have hcover : connectedComponentIn (π '' (f ⁻¹' L')) 0 ⊆
      π '' (f ⁻¹' (C + U)) ∪ π '' (f ⁻¹' ((L' : Set E') \ C + U)) := fun z hz ↦ by
    obtain ⟨x, hx, rfl⟩ := hsub hz
    by_cases hxC : f x ∈ C
    · exact .inl ((key₁ hx).2 hxC)
    · exact .inr ((key₂ hx).2 ⟨hx, hxC⟩)
  have hdisj : connectedComponentIn (π '' (f ⁻¹' L')) 0 ∩
      (π '' (f ⁻¹' (C + U)) ∩ π '' (f ⁻¹' ((L' : Set E') \ C + U))) = ∅ := by
    refine eq_empty_of_forall_notMem fun z ⟨hz, hzu, hzv⟩ ↦ ?_
    obtain ⟨x, hx, rfl⟩ := hsub hz
    exact ((key₂ hx).1 hzv).2 ((key₁ hx).1 hzu)
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn _ _
      (hopen C) (hopen ((L' : Set E') \ C)) hcover hdisj with h | h
  · rintro _ hz
    obtain ⟨x, hx, rfl⟩ := hsub hz
    obtain ⟨l, hl, hlx⟩ := (key₁ hx).1 (h hz)
    refine ⟨x - l, by simp [← hlx], ?_⟩
    rw [_root_.Quotient.eq, L.orbitRel_apply_iff_sub_mem]
    simpa using L.neg_mem hl
  · have h0 : π 0 ∈ π '' (f ⁻¹' ((L' : Set E') \ C + U)) := hπ0 ▸ h hmem
    obtain ⟨-, h0C⟩ := (key₂ (x := 0) (by simp)).1 h0
    exact (h0C ⟨0, L.zero_mem, by simp⟩).elim

/-- Inside the subgroup `K = f⁻¹(L') / L` of the orbit space of translation by `L`, the image of
`ker f` is the connected component of `0`. Thus the quotient of `K` by this image, which
`Submodule.orbitRelQuotientComapQuotientEquiv` identifies with `(L' ∩ range f) / f(L)`, is the
component group of `K`. -/
theorem Submodule.coe_addSubgroupOf_eq_connectedComponent_zero [DiscreteTopology L']
    (hfc : Continuous f) (hf : L.map (f.restrictScalars ℤ) ≤ L') :
    ((LinearMap.ker (f.restrictScalars ℤ)).toAddSubgroup.map L.orbitRelQuotientMkHom).addSubgroupOf
        ((L'.comap (f.restrictScalars ℤ)).toAddSubgroup.map L.orbitRelQuotientMkHom) =
      connectedComponent (0 : (L'.comap (f.restrictScalars ℤ)).toAddSubgroup.map
        L.orbitRelQuotientMkHom) := by
  have hK : ((L'.comap (f.restrictScalars ℤ)).toAddSubgroup.map L.orbitRelQuotientMkHom :
      Set (AddAction.orbitRel.Quotient L E)) =
      _root_.Quotient.mk (AddAction.orbitRel L E) '' (f ⁻¹' L') := by
    simp
  have hK₀ : ((LinearMap.ker (f.restrictScalars ℤ)).toAddSubgroup.map L.orbitRelQuotientMkHom :
      Set (AddAction.orbitRel.Quotient L E)) =
      _root_.Quotient.mk (AddAction.orbitRel L E) '' (LinearMap.ker f) := by
    simp
  refine image_injective.2 Subtype.val_injective <|
    Eq.trans ?_ (connectedComponentIn_eq_image (zero_mem _))
  rw [AddSubgroup.coe_addSubgroupOf, AddSubgroup.coe_subtype, image_preimage_eq_inter_range,
    Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq, hK, hK₀,
    connectedComponentIn_orbitRelQuotient_mk_image_preimage L f hfc hf, inter_eq_left]
  exact image_mono fun x hx ↦ by simp [LinearMap.mem_ker.1 hx]
