/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Center.Basic
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Centers of disconnected skew-zigzag algebras

For a finite simple graph without isolated vertices, the center of its skew-zigzag relation
quotient has one basis vector for each connected component and one for each vertex. The former
is the sum of the vertex idempotents on that component, and the latter is a chosen backtrack
volume. Thus the center is free of rank `|π₀(G)| + |V|`, independently of the skew parameter.

The coordinate equivalence below separates component-constant degree-zero coefficients from
arbitrary volume coefficients. It is a linear equivalence, not an algebra equivalence with a
product of copies of the coefficient ring: the volume classes are square-zero. The incident-edge
choice excludes isolated vertices; no dual-number convention for isolated vertices is asserted
for this relation quotient. The empty graph is allowed.

## References

* C. Couture, *Skew-Zigzag Algebras*, Section 3, https://arxiv.org/abs/1509.08405.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
  https://arxiv.org/abs/math/0002060.

The construction uses the centrality criterion and vertex–arrow–volume basis from
`TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Center.Basic`.
-/

public section

noncomputable section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Fintype V]
  (c : SkewZigzagParameter k G) (t : ∀ i : V, {j : V // G.Adj i j})

private def centerAssembly :
    ((G.ConnectedComponent → k) × (V → k)) →ₗ[k] skewZigzagQuotient k G c where
  toFun x := (∑ i, x.1 (G.connectedComponentMk i) •
    skewZigzagMk k G c (vertexIdempotent k (vertex G i))) +
      ∑ i, x.2 i • skewZigzagVolume k G c (t i)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' a x := by
    simp [Finset.smul_sum, smul_add, smul_smul]

private theorem centerAssembly_mem_center (x : (G.ConnectedComponent → k) × (V → k)) :
    centerAssembly k G c t x ∈ Subalgebra.center k (skewZigzagQuotient k G c) := by
  apply (mem_center_skewZigzagQuotient_iff k G c t).mpr
  exact ⟨fun i => x.1 (G.connectedComponentMk i), x.2,
    fun _ _ h => congrArg x.1 (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h),
    rfl⟩

private theorem centerAssembly_repr_vertex (x : (G.ConnectedComponent → k) × (V → k))
    (i : V) :
    (skewZigzagBasis k G c t).repr (centerAssembly k G c t x) (.inl i) =
      x.1 (G.connectedComponentMk i) := by
  classical
  simp only [centerAssembly, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sum, map_smul,
    ← skewZigzagBasisFun_inl k G c t, ← skewZigzagBasisFun_inr_inr k G c t,
    ← skewZigzagBasis_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

private theorem centerAssembly_repr_volume (x : (G.ConnectedComponent → k) × (V → k))
    (i : V) :
    (skewZigzagBasis k G c t).repr (centerAssembly k G c t x) (.inr (.inr i)) = x.2 i := by
  classical
  simp only [centerAssembly, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sum, map_smul,
    ← skewZigzagBasisFun_inl k G c t, ← skewZigzagBasisFun_inr_inr k G c t,
    ← skewZigzagBasis_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

private theorem centerAssembly_injective : Function.Injective (centerAssembly k G c t) := by
  intro x y h
  apply Prod.ext
  · funext C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h i =>
      simpa only [centerAssembly_repr_vertex] using
        congrArg (fun z => (skewZigzagBasis k G c t).repr z (.inl i)) h
  · funext i
    simpa only [centerAssembly_repr_volume] using
      congrArg (fun z => (skewZigzagBasis k G c t).repr z (.inr (.inr i))) h

private theorem centerAssembly_surjective : Function.Surjective
    ((centerAssembly k G c t).codRestrict
      (Subalgebra.center k (skewZigzagQuotient k G c)).toSubmodule
      (centerAssembly_mem_center k G c t)) := by
  rintro ⟨z, hz⟩
  obtain ⟨f, g, hf, hz⟩ := (mem_center_skewZigzagQuotient_iff k G c t).mp hz
  have hreach {i j : V} (h : G.Reachable i j) : f i = f j := by
    rw [SimpleGraph.reachable_eq_reflTransGen] at h
    simpa only [Relation.reflTransGen_eq_self] using h.lift f (fun _ _ h => hf h)
  let F : G.ConnectedComponent → k :=
    SimpleGraph.ConnectedComponent.lift f (fun _ _ p _ => hreach p.reachable)
  refine ⟨(F, g), Subtype.ext ?_⟩
  simp only [LinearMap.codRestrict_apply]
  rw [hz, centerAssembly, LinearMap.coe_mk, AddHom.coe_mk]
  apply congrArg (· + ∑ i, g i • skewZigzagVolume k G c (t i))
  apply Finset.sum_congr rfl
  intro i _
  simp only [F, SimpleGraph.ConnectedComponent.lift_mk]

/-- Coordinates for the center of a finite skew-zigzag relation quotient without isolated
vertices: one scalar per connected component and one volume coefficient per vertex. -/
noncomputable def skewZigzagCenterEquiv :
    ((G.ConnectedComponent → k) × (V → k)) ≃ₗ[k]
      Subalgebra.center k (skewZigzagQuotient k G c) :=
  LinearEquiv.ofBijective
    ((centerAssembly k G c t).codRestrict _ (centerAssembly_mem_center k G c t))
    ⟨fun _ _ h => centerAssembly_injective k G c t (congrArg Subtype.val h),
      centerAssembly_surjective k G c t⟩

/-- The coordinate equivalence assembles component-constant idempotent coefficients and volumes. -/
theorem skewZigzagCenterEquiv_apply_coe (x : (G.ConnectedComponent → k) × (V → k)) :
    (skewZigzagCenterEquiv k G c t x : skewZigzagQuotient k G c) =
      (∑ i, x.1 (G.connectedComponentMk i) •
        skewZigzagMk k G c (vertexIdempotent k (vertex G i))) +
        ∑ i, x.2 i • skewZigzagVolume k G c (t i) := (rfl)

/-- The inverse equivalence reads the vertex coefficient at any vertex of the component. -/
@[simp]
theorem skewZigzagCenterEquiv_symm_apply_fst
    (z : Subalgebra.center k (skewZigzagQuotient k G c)) (i : V) :
    ((skewZigzagCenterEquiv k G c t).symm z).1 (G.connectedComponentMk i) =
      (skewZigzagBasis k G c t).repr z (.inl i) := by
  obtain ⟨x, rfl⟩ := (skewZigzagCenterEquiv k G c t).surjective z
  rw [LinearEquiv.symm_apply_apply]
  exact (centerAssembly_repr_vertex k G c t x i).symm

/-- The inverse equivalence reads the chosen volume coefficient. -/
@[simp]
theorem skewZigzagCenterEquiv_symm_apply_snd
    (z : Subalgebra.center k (skewZigzagQuotient k G c)) (i : V) :
    ((skewZigzagCenterEquiv k G c t).symm z).2 i =
      (skewZigzagBasis k G c t).repr z (.inr (.inr i)) := by
  obtain ⟨x, rfl⟩ := (skewZigzagCenterEquiv k G c t).surjective z
  rw [LinearEquiv.symm_apply_apply]
  exact (centerAssembly_repr_volume k G c t x i).symm

/-- A basis of the center of a possibly disconnected skew-zigzag quotient: the component units
and the chosen vertex volumes. -/
noncomputable def skewZigzagDisconnectedCenterBasis :
    Module.Basis (G.ConnectedComponent ⊕ V) k
      (Subalgebra.center k (skewZigzagQuotient k G c)) := by
  letI := Fintype.ofFinite G.ConnectedComponent
  exact ((Pi.basisFun k G.ConnectedComponent).prod (Pi.basisFun k V)).map
    (skewZigzagCenterEquiv k G c t)

open scoped Classical in
/-- A component basis vector is the sum of the idempotents on precisely that component. -/
theorem skewZigzagDisconnectedCenterBasis_inl (C : G.ConnectedComponent) :
    (skewZigzagDisconnectedCenterBasis k G c t (.inl C) : skewZigzagQuotient k G c) =
      ∑ i, if G.connectedComponentMk i = C then
        skewZigzagMk k G c (vertexIdempotent k (vertex G i)) else 0 := by
  classical
  simp [skewZigzagDisconnectedCenterBasis, Module.Basis.map_apply,
    skewZigzagCenterEquiv_apply_coe, Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- A vertex basis vector of the center is its chosen backtrack volume. -/
@[simp]
theorem skewZigzagDisconnectedCenterBasis_inr (i : V) :
    (skewZigzagDisconnectedCenterBasis k G c t (.inr i) : skewZigzagQuotient k G c) =
      skewZigzagVolume k G c (t i) := by
  classical
  simp [skewZigzagDisconnectedCenterBasis, Module.Basis.map_apply,
    skewZigzagCenterEquiv_apply_coe, Pi.basisFun_apply, Pi.single_apply]

/-- A component coefficient can be read at any vertex of that component. -/
@[simp]
theorem skewZigzagDisconnectedCenterBasis_repr_inl
    (z : Subalgebra.center k (skewZigzagQuotient k G c)) (i : V) :
    (skewZigzagDisconnectedCenterBasis k G c t).repr z (.inl (G.connectedComponentMk i)) =
      (skewZigzagBasis k G c t).repr z (.inl i) := by
  simp [skewZigzagDisconnectedCenterBasis, Module.Basis.map_repr]

/-- A volume coefficient in the center basis is the same coefficient in the algebra basis. -/
@[simp]
theorem skewZigzagDisconnectedCenterBasis_repr_inr
    (z : Subalgebra.center k (skewZigzagQuotient k G c)) (i : V) :
    (skewZigzagDisconnectedCenterBasis k G c t).repr z (.inr i) =
      (skewZigzagBasis k G c t).repr z (.inr (.inr i)) := by
  simp [skewZigzagDisconnectedCenterBasis, Module.Basis.map_repr]

/-- The center dimension is the number of vertices plus the number of connected components,
independently of the skew parameter, over every nontrivial commutative coefficient ring. -/
theorem finrank_center_skewZigzagQuotient_of_no_isolated [Nontrivial k]
    [Fintype G.ConnectedComponent]
    (hns : ∀ i : V, ∃ j, G.Adj i j) :
    Module.finrank k (Subalgebra.center k (skewZigzagQuotient k G c)) =
      Fintype.card V + Fintype.card G.ConnectedComponent := by
  let t : ∀ i : V, {j : V // G.Adj i j} := fun i => ⟨(hns i).choose, (hns i).choose_spec⟩
  rw [Module.finrank_eq_card_basis (skewZigzagDisconnectedCenterBasis k G c t),
    Fintype.card_sum, Nat.add_comm]

end TauCeti
