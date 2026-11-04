/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Op

/-!
# The opposite of a join

The covariant involution `SSet.opFunctor` reverses the order of the vertices of every simplex. A
simplex of the join `K ⋆ L` splits into an initial segment in `K` and a final segment in `L`;
reversing its vertices gives a simplex that splits into an initial segment in `Lᵒᵖ` and a final
segment in `Kᵒᵖ`. Hence `(K ⋆ L)ᵒᵖ ≅ Lᵒᵖ ⋆ Kᵒᵖ` (`SSet.join.opIso`), naturally in `K` and `L` and
exchanging the two inclusions. This duality exchanges the two variables of the join, so that
constructions and statements for one factor, such as slices `C_{/p}` built from the joins `X ⋆ K`,
transfer to the other, such as coslices `C_{p/}` built from the joins `K ⋆ X`.

## Main definitions

* `SSet.JoinData.op`: the opposite of join data on `X` for `K ⋆ L`, which are join data on `Xᵒᵖ`
  for `Lᵒᵖ ⋆ Kᵒᵖ`.
* `SSet.join.opIso`: the isomorphism `(K ⋆ L)ᵒᵖ ≅ Lᵒᵖ ⋆ Kᵒᵖ`.

## Main results

* `SSet.joinFiber_op`: the parts of `Xᵒᵖ` over the vertices of `Δ[1]` along the opposite of
  `p : X ⟶ Δ[1]` are the opposites of the parts of `X` over the reversed vertices.
* `SSet.JoinData.op_op`: taking opposite join data is involutive.
* `SSet.join.homEquiv_opFunctor_map_comp_opIso_hom`: under the universal property of the join,
  `SSet.join.opIso` corresponds to taking opposite join data.
* `SSet.join.opFunctor_map_inl_comp_opIso_hom`, `SSet.join.opFunctor_map_inr_comp_opIso_hom`: the
  isomorphism exchanges the inclusions of the two factors.
* `SSet.join.opFunctor_map_map_comp_opIso_hom`: the isomorphism is natural in both factors.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.8.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

variable {X Y K L K' L' : SSet.{u}}

/-- The part of `Xᵒᵖ` over the vertex `e'` of `Δ[1]` along the opposite of `p : X ⟶ Δ[1]` is the
opposite of the part of `X` over the reversed vertex `e`. -/
lemma joinFiber_op (p : X ⟶ Δ[1]) {e e' : Fin 2} (h : e.rev = e') :
    joinFiber (opFunctor.map p ≫ (stdSimplex.opIso _).hom) e' = (joinFiber p e).op := by
  subst h
  ext ⟨n⟩ x
  induction n using SimplexCategory.rec with | _ n
  simp only [mem_joinFiber_iff, Subcomplex.mem_op_obj_iff, NatTrans.comp_app,
    ConcreteCategory.comp_apply, opFunctor_map, stdSimplex.opIso_hom_app_hom_apply,
    stdSimplex.opObjEquiv_apply, Equiv.apply_symm_apply, Fin.rev_inj]
  exact ⟨fun h j ↦ by simpa using h j.rev, fun h j ↦ h j.rev⟩

namespace JoinData

/-- The opposite of join data on `X` for `K ⋆ L`: join data on `Xᵒᵖ` for `Lᵒᵖ ⋆ Kᵒᵖ`, whose map to
`Δ[1]` is the opposite of the original one, with the two vertices exchanged. -/
def op (d : JoinData X K L) : JoinData X.op L.op K.op where
  p := opFunctor.map d.p ≫ (stdSimplex.opIso _).hom
  left := (Subcomplex.eqToIso (joinFiber_op d.p (by decide))).hom ≫ opFunctor.map d.right
  right := (Subcomplex.eqToIso (joinFiber_op d.p (by decide))).hom ≫ opFunctor.map d.left

/-- The map to `Δ[1]` of the opposite join data is the opposite of the original one. -/
@[simp]
lemma op_p (d : JoinData X K L) : d.op.p = opFunctor.map d.p ≫ (stdSimplex.opIso _).hom :=
  (rfl)

/-- Over the vertex `0`, the opposite join data on `Xᵒᵖ` are the opposite of the map to `L` of the
original join data. -/
@[simp]
lemma op_left_app (d : JoinData X K L) {n : SimplexCategoryᵒᵖ} (x : X.op.obj n)
    (hx : x ∈ (joinFiber d.op.p 0).obj n) :
    dsimp% d.op.left.app n ⟨x, hx⟩ = opObjEquiv.symm (d.right.app n ⟨opObjEquiv x,
      by rwa [op_p, joinFiber_op d.p (by decide : (1 : Fin 2).rev = 0)] at hx⟩) :=
  (rfl)

/-- Over the vertex `1`, the opposite join data on `Xᵒᵖ` are the opposite of the map to `K` of the
original join data. -/
@[simp]
lemma op_right_app (d : JoinData X K L) {n : SimplexCategoryᵒᵖ} (x : X.op.obj n)
    (hx : x ∈ (joinFiber d.op.p 1).obj n) :
    dsimp% d.op.right.app n ⟨x, hx⟩ = opObjEquiv.symm (d.left.app n ⟨opObjEquiv x,
      by rwa [op_p, joinFiber_op d.p (by decide : (0 : Fin 2).rev = 1)] at hx⟩) :=
  (rfl)

/-- Taking opposite join data commutes with restriction along a map `g : Y ⟶ X`. -/
@[simp]
lemma op_precomp (d : JoinData X K L) (g : Y ⟶ X) :
    (d.precomp g).op = d.op.precomp (opFunctor.map g) :=
  ext (by simp) (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

/-- Taking opposite join data commutes with composition with maps `f : K ⟶ K'` and `g : L ⟶ L'`,
which exchange their roles. -/
@[simp]
lemma op_postcomp (d : JoinData X K L) (f : K ⟶ K') (g : L ⟶ L') :
    (d.postcomp f g).op = d.op.postcomp (opFunctor.map g) (opFunctor.map f) :=
  ext (by simp) (fun _ _ _ _ ↦ by simp [opFunctor_map]) (fun _ _ _ _ ↦ by simp [opFunctor_map])

/-- Taking opposite join data twice gives back the original join data, through the involution
`Xᵒᵖᵒᵖ ≅ X`. -/
lemma op_op (d : JoinData X K L) :
    d.op.op = (d.precomp (opFunctorCompOpFunctorIso.hom.app X)).postcomp
      (opFunctorCompOpFunctorIso.inv.app K) (opFunctorCompOpFunctorIso.inv.app L) := by
  refine ext ?_ (fun _ _ _ _ ↦ by simp) (fun _ _ _ _ ↦ by simp)
  simpa using opFunctorCompOpFunctorIso.hom.naturality d.p

end JoinData

namespace join

/-- The bijection between the simplices of `(K ⋆ L)ᵒᵖ` and of `Lᵒᵖ ⋆ Kᵒᵖ` underlying
`SSet.join.opIso`: the opposite of the join data of a simplex, transported along `Δ[n] ≅ Δ[n]ᵒᵖ`. -/
private def opObjEquiv' {n : SimplexCategoryᵒᵖ} : (join K L).op.obj n ≃ (join L.op K.op).obj n where
  toFun x := objEquiv.symm ((objEquiv (opObjEquiv x)).op.precomp (stdSimplex.opIso _).inv)
  invFun y := opObjEquiv.symm (objEquiv.symm
    (((objEquiv y).op.precomp (stdSimplex.opIso _).inv).postcomp
      (opFunctorCompOpFunctorIso.hom.app K) (opFunctorCompOpFunctorIso.hom.app L)))
  left_inv x := by
    apply opObjEquiv.injective
    apply objEquiv.injective
    simp only [Equiv.apply_symm_apply, JoinData.op_precomp, JoinData.op_op,
      JoinData.precomp_postcomp, JoinData.precomp_precomp, JoinData.postcomp_postcomp,
      stdSimplex.opIso_inv_comp_opFunctor_map_opIso_inv_assoc, Iso.inv_hom_id_app,
      JoinData.precomp_id, Functor.id_obj, JoinData.postcomp_id]
  right_inv y := by
    apply objEquiv.injective
    simp only [Equiv.apply_symm_apply, JoinData.op_precomp, JoinData.op_op, JoinData.op_postcomp,
      JoinData.precomp_postcomp, JoinData.precomp_precomp, JoinData.postcomp_postcomp,
      stdSimplex.opIso_inv_comp_opFunctor_map_opIso_inv_assoc,
      Iso.inv_hom_id_app, JoinData.precomp_id, Functor.id_obj]
    -- The remaining components are the triangle identity of `SSet.opEquivalence`.
    exact (congr_arg₂ _ (opEquivalence.unit_inverse_comp L)
      (opEquivalence.unit_inverse_comp K)).trans (JoinData.postcomp_id _)

variable (K L) in
/-- **The opposite of a join**: `(K ⋆ L)ᵒᵖ ≅ Lᵒᵖ ⋆ Kᵒᵖ`. A simplex of `(K ⋆ L)ᵒᵖ` is a simplex of
`K ⋆ L` with its vertices read in reverse order, so its initial segment in `K` becomes a final
segment in `Kᵒᵖ`, and its final segment in `L` an initial segment in `Lᵒᵖ`. -/
def opIso : (join K L).op ≅ join L.op K.op :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso opObjEquiv') fun {n m} f ↦ by
    ext x
    apply objEquiv.injective
    simp [opObjEquiv', op_map, JoinData.op_precomp, stdSimplex.map_comp_opIso_inv]

/-- The join data of the simplex of `Lᵒᵖ ⋆ Kᵒᵖ` corresponding to a simplex `x` of `(K ⋆ L)ᵒᵖ` are
the opposite of the join data of `x`, transported along `Δ[n] ≅ Δ[n]ᵒᵖ`. -/
@[simp]
lemma objEquiv_opIso_hom_app {n : SimplexCategoryᵒᵖ} (x : (join K L).op.obj n) :
    objEquiv ((opIso K L).hom.app n x) =
      (objEquiv (opObjEquiv x)).op.precomp (stdSimplex.opIso _).inv := by
  simp [opIso, opObjEquiv']

/-- Under the universal property of the join, the opposite `Xᵒᵖ ⟶ (K ⋆ L)ᵒᵖ ≅ Lᵒᵖ ⋆ Kᵒᵖ` of a map
`G : X ⟶ K ⋆ L` corresponds to the opposite of the join data of `G`. -/
lemma homEquiv_opFunctor_map_comp_opIso_hom (G : X ⟶ join K L) :
    homEquiv (opFunctor.map G ≫ (opIso K L).hom) = (homEquiv G).op := by
  rw [← Equiv.eq_symm_apply]
  ext ⟨n⟩ y
  apply objEquiv.injective
  have hG : objEquiv (G.app _ (opObjEquiv y)) =
      (homEquiv G).precomp (yonedaEquiv.symm (opObjEquiv y)) := by
    rw [← homEquiv_comp, yonedaEquiv_symm_comp, homEquiv_apply, univ_precomp_yonedaEquiv_symm]
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply,
    homEquiv_symm_app, Equiv.apply_symm_apply, opFunctor_map]
  rw [objEquiv_opIso_hom_app, Equiv.apply_symm_apply, hG, JoinData.op_precomp,
    JoinData.precomp_precomp, stdSimplex.opIso_inv_comp_opFunctor_map_yonedaEquiv_symm,
    Equiv.symm_apply_apply]

variable (K L) in
/-- Under the universal property of the join, the isomorphism `(K ⋆ L)ᵒᵖ ≅ Lᵒᵖ ⋆ Kᵒᵖ` corresponds
to the opposite of the tautological join data on `K ⋆ L`. -/
@[simp]
lemma homEquiv_opIso_hom : homEquiv (opIso K L).hom = (univ K L).op := by
  simpa using homEquiv_opFunctor_map_comp_opIso_hom (𝟙 (join K L))

variable (K L) in
/-- The opposite of the inclusion of `K` into `K ⋆ L` is the inclusion of `Kᵒᵖ` into
`Lᵒᵖ ⋆ Kᵒᵖ`. -/
@[reassoc (attr := simp)]
lemma opFunctor_map_inl_comp_opIso_hom :
    opFunctor.map (inl K L) ≫ (opIso K L).hom = inr L.op K.op := by
  apply homEquiv.injective
  rw [homEquiv_opFunctor_map_comp_opIso_hom]
  refine JoinData.ext ?_ (fun _ _ _ hx ↦ by simp at hx) (fun _ _ _ _ ↦ ?_)
  · simp
  · rw [JoinData.op_right_app, homEquiv_inl_left_app, homEquiv_inr_right_app,
      Equiv.symm_apply_apply]

variable (K L) in
/-- The opposite of the inclusion of `L` into `K ⋆ L` is the inclusion of `Lᵒᵖ` into
`Lᵒᵖ ⋆ Kᵒᵖ`. -/
@[reassoc (attr := simp)]
lemma opFunctor_map_inr_comp_opIso_hom :
    opFunctor.map (inr K L) ≫ (opIso K L).hom = inl L.op K.op := by
  apply homEquiv.injective
  rw [homEquiv_opFunctor_map_comp_opIso_hom]
  refine JoinData.ext ?_ (fun _ _ _ _ ↦ ?_) (fun _ _ _ hx ↦ by simp at hx)
  · simp
  · rw [JoinData.op_left_app, homEquiv_inr_right_app, homEquiv_inl_left_app,
      Equiv.symm_apply_apply]

/-- The isomorphism `(K ⋆ L)ᵒᵖ ≅ Lᵒᵖ ⋆ Kᵒᵖ` is natural in `K` and `L`. -/
@[reassoc (attr := simp)]
lemma opFunctor_map_map_comp_opIso_hom (f : K ⟶ K') (g : L ⟶ L') :
    opFunctor.map (map f g) ≫ (opIso K' L').hom =
      (opIso K L).hom ≫ map (opFunctor.map g) (opFunctor.map f) := by
  apply homEquiv.injective
  rw [homEquiv_opFunctor_map_comp_opIso_hom, homEquiv_comp_map, homEquiv_opIso_hom,
    ← JoinData.op_postcomp, ← Category.id_comp (map f g), homEquiv_comp_map, homEquiv_id]

end join

end SSet
