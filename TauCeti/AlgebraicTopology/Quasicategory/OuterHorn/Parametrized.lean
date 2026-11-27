/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.HornFilling
public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Vertex

/-!
# Joyal's theorem on special outer horns, parametrized

Let `C` be a quasicategory. Joyal's theorem `SSet.Quasicategory.hornFilling_zero` fills a horn
`Λ[m + 2, 0] ⟶ C` whose initial edge is an equivalence. This file proves the parametrized form:
families of such horns, parametrized by a simplicial set, can be filled compatibly with a filling
given over a simplicial subset of the parameter space. It is the case over a point of the relative
form: for an inner fibration `p : X ⟶ S`, families of horns `Λ[m + 2, 0] ⟶ X` over a simplex of
`S` whose initial edges are `p`-coCartesian can be filled over that simplex.

By Mathlib's description of the trivial fibrations as the maps lifting against boundary
inclusions (`SSet.rlp_monomorphisms`), it suffices to treat the families parametrized by `Δ[n]`
with given filling over `∂Δ[n]`, that is lifting along
`(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n]) ⟶ Δ[m + 2] ⊗ Δ[n]`. This is lifting along a prism whose
vertical edge `(0, 0) ⟶ (1, 0)` is coCartesian
(`SSet.prodStdSimplex.exists_lift_unionProd_horn_zero`, proved through Mathlib's regular pairing
of Moss). Over a point, the edges of a quasicategory which are coCartesian are its equivalences
(`SSet.Edge.isEquivalence_iff_isCoCartesian`). The case `m = 0` of the absolute prism form, a prism
`Δ[1] ⊗ Δ[n]` with given start and sides, is used for right fibrations in
`TauCeti.AlgebraicTopology.Quasicategory.RightFibration.KanComplex`.

## Main results

* `SSet.prodStdSimplex.exists_ext_unionProd_horn_zero`: a map from
  `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n])` to a quasicategory which is defined on the vertical
  edge `(0, 0) ⟶ (1, 0)` and sends it to an equivalence extends to `Δ[m + 1] ⊗ Δ[n]`.
* `SSet.exists_lift_ihomOver_pre_horn_zero`: for an inner fibration `p : X ⟶ S` and
  `β : Δ[m + 2] ⟶ S`, over the horns whose initial edge is `p`-coCartesian, restriction
  `Fun_S(Δ[m + 2], X) ⟶ Fun_S(Λ[m + 2, 0], X)` of functors over `β` has the right lifting property
  with respect to monomorphisms.
* `SSet.exists_lift_tensor_horn_zero`: families of horns `Λ[m + 2, 0]` with coCartesian initial
  edges, parametrized by a simplicial set, lift along an inner fibration.
* `SSet.Quasicategory.exists_ext_cylinder_boundary`: a cylinder on a simplex extends a given
  start and boundary cylinder when its initial vertical edge is an equivalence.
* `SSet.Quasicategory.exists_lift_pre_horn_zero`: over the horns whose initial edge is an
  equivalence, restriction `Fun(Δ[m + 2], C) ⟶ Fun(Λ[m + 2, 0], C)` has the right lifting property
  with respect to monomorphisms.

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
* J. Lurie, *Kerodon*, proof of Theorem 4.4.4.4.
* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits Simplicial HomotopicalAlgebra
  CartesianMonoidalCategory

namespace SSet

variable {C : SSet.{u}}

namespace prodStdSimplex

open Subcomplex

/-- **Extension along a prism with an invertible initial vertical edge.** Let `C` be a
quasicategory. A map `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ C` extends to
`Δ[m + 1] ⊗ Δ[n]` provided that the vertical edge `(0, 0) ⟶ (1, 0)` lies in its domain and is sent
to an equivalence. The edge lies in `Λ[m + 1, 0] ⊗ Δ[n]` when `1 ≤ m` and in `Δ[m + 1] ⊗ ∂Δ[n]`
when `1 ≤ n`. -/
theorem exists_ext_unionProd_horn_zero [Quasicategory C] {m n : ℕ}
    (a : (unionProd Λ[m + 1, 0] ∂Δ[n] : SSet.{u}) ⟶ C)
    (hmem : (stdSimplex.edge (m + 1) 0 1 (Fin.zero_le _), stdSimplex.const n 0 _) ∈
      (unionProd Λ[m + 1, 0] ∂Δ[n]).obj (Opposite.op ⦋1⦌))
    (ha : (Edge.mk' (a.app _ ⟨_, hmem⟩)).IsEquivalence) :
    ∃ b : Δ[m + 1] ⊗ Δ[n] ⟶ C, (unionProd Λ[m + 1, 0] ∂Δ[n]).ι ≫ b = a := by
  -- Over a point, the equivalences of `C` are its coCartesian edges.
  obtain ⟨b, hb, -⟩ := exists_lift_unionProd_horn_zero (terminal.from C) a (terminal.from _)
    (terminal.hom_ext _ _) hmem
    ((Edge.isEquivalence_iff_isCoCartesian _ _ terminalIsTerminal).1 ha)
  exact ⟨b, hb⟩

end prodStdSimplex

section relative

variable {X S : SSet.{u}} (p : X ⟶ S) {m : ℕ} (β : Δ[m + 2] ⟶ S)

/-- The boundary case of `SSet.exists_lift_ihomOver_pre_horn_zero`, in curried form: a lifting
problem of `∂Δ[n] ⟶ Δ[n]` against restriction `Fun_S(Δ[m + 2], X) ⟶ Fun_S(Λ[m + 2, 0], X)` is a
lifting problem along the prism `(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n])`. -/
private lemma exists_lift_boundary_pre_horn_zero [InnerFibration p] {n : ℕ}
    (t₀ : (∂Δ[n] : SSet.{u}) ⟶ ihomOver p β) (b₀ : Δ[n] ⟶ ihomOver p (Λ[m + 2, 0].ι ≫ β))
    (w₀ : t₀ ≫ ihomOver.pre Λ[m + 2, 0].ι = ∂Δ[n].ι ≫ b₀)
    (hb₀ : ∀ z : Δ[n] _⦋0⦌, (Edge.mk' ((ihomOver.obj₀Equiv (b₀.app _ z)).val.app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsCoCartesian p) :
    ∃ l : Δ[n] ⟶ ihomOver p β, ∂Δ[n].ι ≫ l = t₀ ∧ l ≫ ihomOver.pre Λ[m + 2, 0].ι = b₀ := by
  have hw : Λ[m + 2, 0].ι ▷ _ ≫ (ihomOver.homEquiv t₀).val =
      _ ◁ ∂Δ[n].ι ≫ (ihomOver.homEquiv b₀).val := by
    rw [← ihomOver.homEquiv_comp_pre_coe, w₀, ihomOver.homEquiv_comp_coe]
  have hpush := Subcomplex.unionProd.isPushout Λ[m + 2, 0] ∂Δ[n]
  let a := hpush.desc (ihomOver.homEquiv t₀).val (ihomOver.homEquiv b₀).val hw
  obtain ⟨L, hL₁, hL₂⟩ := prodStdSimplex.exists_lift_unionProd_horn_zero p a (fst _ _ ≫ β)
    (hpush.hom_ext (by simp [a, (ihomOver.homEquiv t₀).property])
      (by simp [a, (ihomOver.homEquiv b₀).property]))
    ((Subcomplex.unionProd.ι₂ _ _).app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp), stdSimplex.const n 0 _)).property (by
      have hv := hb₀ (stdSimplex.obj₀Equiv.symm 0)
      rw [ihomOver.obj₀Equiv_app_coe] at hv
      have h₁ : (lift (𝟙 _) (const (stdSimplex.obj₀Equiv.symm 0))).app _
          (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)) =
          (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp), stdSimplex.const n 0 _) := by
        rw [lift_id_const_app_one, Edge.id_edge, SimplicialObject.σ_def,
          stdSimplex.obj₀Equiv_symm_apply, stdSimplex.map_const]
      have h₂ := hpush.inr_desc (ihomOver.homEquiv t₀).val (ihomOver.homEquiv b₀).val hw
      exact hv.of_edge_eq ((congrArg ((ihomOver.homEquiv b₀).val.app _) h₁).trans
        (congrArg (fun (f : (Λ[m + 2, 0] : SSet.{u}) ⊗ Δ[n] ⟶ X) ↦ f.app _
          (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp), stdSimplex.const n 0 _))
            h₂).symm))
  refine ⟨ihomOver.homEquiv.symm ⟨L, hL₂⟩, ihomOver.homEquiv.injective (Subtype.ext ?_),
    ihomOver.homEquiv.injective (Subtype.ext ?_)⟩
  · rw [ihomOver.homEquiv_comp_coe, Equiv.apply_symm_apply, ← Subcomplex.unionProd.ι₁_ι,
      Category.assoc, hL₁, hpush.inl_desc]
  · rw [ihomOver.homEquiv_comp_pre_coe, Equiv.apply_symm_apply, ← Subcomplex.unionProd.ι₂_ι,
      Category.assoc, hL₁, hpush.inr_desc]

/-- **Lifting along horns with coCartesian initial edges, parametrized.** Let `p : X ⟶ S` be an
inner fibration and `β : Δ[m + 2] ⟶ S`. Over the horns `Λ[m + 2, 0] ⟶ X` over `β` whose initial
edge is `p`-coCartesian, restriction `Fun_S(Δ[m + 2], X) ⟶ Fun_S(Λ[m + 2, 0], X)` of functors over
`β` has the right lifting property with respect to every monomorphism `i : Y ⟶ Z`: a family of
such horns parametrized by `Z`, whose restriction to `Y` is filled over `β`, has a filling over `β`
extending the given one. -/
theorem exists_lift_ihomOver_pre_horn_zero [InnerFibration p] {Y Z : SSet.{u}} (i : Y ⟶ Z)
    [Mono i] (t : Y ⟶ ihomOver p β) (b : Z ⟶ ihomOver p (Λ[m + 2, 0].ι ≫ β))
    (w : t ≫ ihomOver.pre Λ[m + 2, 0].ι = i ≫ b)
    (hb : ∀ z : Z _⦋0⦌, (Edge.mk' ((ihomOver.obj₀Equiv (b.app _ z)).val.app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsCoCartesian p) :
    ∃ l : Z ⟶ ihomOver p β, i ≫ l = t ∧ l ≫ ihomOver.pre Λ[m + 2, 0].ι = b :=
  exists_lift_of_forall_boundary (ihomOver.pre Λ[m + 2, 0].ι)
    (fun v ↦ (Edge.mk' ((ihomOver.obj₀Equiv v).val.app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsCoCartesian p)
    (fun _ t₀ b₀ w₀ hb₀ ↦ exists_lift_boundary_pre_horn_zero p β t₀ b₀ w₀ hb₀) i t b w hb

/-- **Lifting families of horns with coCartesian initial edges.** Let `p : X ⟶ S` be an inner
fibration and `β : Δ[m + 2] ⟶ S`. A family `b : Z ⊗ Λ[m + 2, 0] ⟶ X` of horns over `β`,
parametrized by a simplicial set `Z`, whose initial edges `(z, 0 ⟶ 1)` are all `p`-coCartesian,
extends to a family `Z ⊗ Δ[m + 2] ⟶ X` of simplices over `β`. This is the case of the empty
simplicial subset of `Z` in `SSet.exists_lift_ihomOver_pre_horn_zero`. -/
theorem exists_lift_tensor_horn_zero [InnerFibration p] {Z : SSet.{u}}
    (b : Z ⊗ (Λ[m + 2, 0] : SSet) ⟶ X) (hb : b ≫ p = snd _ _ ≫ Λ[m + 2, 0].ι ≫ β)
    (hZ : ∀ z : Z _⦋0⦌, (Edge.mk' (b.app _
      (Z.σ 0 z, horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsCoCartesian p) :
    ∃ l : Z ⊗ Δ[m + 2] ⟶ X, Z ◁ Λ[m + 2, 0].ι ≫ l = b ∧ l ≫ p = snd _ _ ≫ β := by
  -- By adjunction, this is a lifting problem against the restriction
  -- `Fun_S(Δ[m + 2], X) ⟶ Fun_S(Λ[m + 2, 0], X)` of functors over `β`, along `∅ ⟶ Z`.
  -- The braided family `Λ[m + 2, 0] ⊗ Z ⟶ X`, as a map `Z ⟶ Fun_S(Λ[m + 2, 0], X)`.
  let b' : (Λ[m + 2, 0] : SSet) ⊗ Z ⟶ X := (β_ _ _).hom ≫ b
  have hb' : b' ≫ p = fst _ _ ≫ Λ[m + 2, 0].ι ≫ β := by
    rw [Category.assoc, hb, braiding_hom_snd_assoc]
  obtain ⟨l, -, hl⟩ := exists_lift_ihomOver_pre_horn_zero p β (initial.to Z) (initial.to _)
    (ihomOver.homEquiv.symm ⟨b', hb'⟩) (initial.hom_ext _ _)
    fun z ↦ by
      rw [ihomOver.obj₀Equiv_app_coe, Equiv.apply_symm_apply]
      have hz : (lift (𝟙 _) (const z)).app _ (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)) =
          (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp), Z.σ 0 z) :=
        lift_id_const_app_one z _
      exact (hZ z).of_edge_eq (congrArg (fun q ↦ b.app _ ((β_ (Λ[m + 2, 0] : SSet) Z).hom.app _ q))
        hz.symm)
  refine ⟨(β_ _ _).hom ≫ (ihomOver.homEquiv l).val, ?_, ?_⟩
  · rw [BraidedCategory.braiding_naturality_right_assoc, ← ihomOver.homEquiv_comp_pre_coe, hl,
      Equiv.apply_symm_apply, SymmetricCategory.symmetry_assoc]
  · rw [Category.assoc, (ihomOver.homEquiv l).property, braiding_hom_fst_assoc]

end relative

namespace Quasicategory

open Edge

/-- **Extension along a prism over a boundary with an invertible initial vertical edge**, in
cylinder form. Let `C` be a quasicategory, `g : Δ[n + 1] ⟶ C` and `L : ∂Δ[n + 1] ⊗ Δ[1] ⟶ C` a
homotopy starting at the restriction of `g`. When `L` sends the vertical edge `{0} ⊗ Δ[1]` to an
equivalence, `g` and `L` extend to a homotopy `Δ[n + 1] ⊗ Δ[1] ⟶ C`. This is
`SSet.prodStdSimplex.exists_ext_unionProd_horn_zero` for `Λ[1, 0]`, transported along the
braiding `Δ[1] ⊗ Δ[n + 1] ≅ Δ[n + 1] ⊗ Δ[1]`. -/
theorem exists_ext_cylinder_boundary [Quasicategory C] (g : Δ[n + 1] ⟶ C)
    (L : (∂Δ[n + 1] : SSet.{u}) ⊗ Δ[1] ⟶ C) (hgL : ∂Δ[n + 1].ι ≫ g = ι₀ ≫ L)
    (hL : (Edge.mk' (L.app _
      (boundary.edgeZero n, stdSimplex.edge 1 0 1 (Fin.zero_le _)))).IsEquivalence) :
    ∃ L' : Δ[n + 1] ⊗ Δ[1] ⟶ C, ι₀ ≫ L' = g ∧ ∂Δ[n + 1].ι ▷ Δ[1] ≫ L' = L := by
  have hpush := Subcomplex.unionProd.isPushout Λ[1, 0] ∂Δ[n + 1]
  have hw : Λ[1, 0].ι ▷ (∂Δ[n + 1] : SSet.{u}) ≫ (β_ _ _).hom ≫ L =
      (Λ[1, 0] : SSet.{u}) ◁ ∂Δ[n + 1].ι ≫ snd _ _ ≫ g := by
    rw [BraidedCategory.braiding_naturality_left_assoc, whiskerLeft_horn_one_zero_ι,
      Category.assoc, braiding_hom_fst_assoc, ← hgL, whiskerLeft_snd_assoc]
  let a := hpush.desc ((β_ _ _).hom ≫ L) (snd _ _ ≫ g) hw
  have hmem : (stdSimplex.edge 1 0 1 (Fin.zero_le _), stdSimplex.const (n + 1) 0 _) ∈
      (Subcomplex.unionProd Λ[1, 0] ∂Δ[n + 1]).obj (Opposite.op ⦋1⦌) := by
    rw [← boundary.edgeZero_val n]
    exact ((Subcomplex.unionProd.ι₁ _ _).app _
      (stdSimplex.edge 1 0 1 (Fin.zero_le _), boundary.edgeZero n)).property
  obtain ⟨E, hE⟩ := prodStdSimplex.exists_ext_unionProd_horn_zero a hmem (by
    have he : (Subcomplex.unionProd.ι₁ _ _).app _
        (stdSimplex.edge 1 0 1 (Fin.zero_le _), boundary.edgeZero n) = ⟨_, hmem⟩ :=
      Subtype.ext (Prod.ext rfl (boundary.edgeZero_val n))
    have h := congrArg (fun f ↦ f.app _ (stdSimplex.edge 1 0 1 (Fin.zero_le _),
      boundary.edgeZero n)) (hpush.inl_desc _ _ hw)
    exact (isEquivalence_iff_of_edge_eq (e := Edge.mk' _) (e' := Edge.mk' _)
      ((congrArg (a.app _) he).symm.trans h).symm).1 hL)
  refine ⟨(β_ _ _).hom ≫ E, ?_, ?_⟩
  · -- The start of the cylinder is the image of `Λ[1, 0] ⊗ Δ[n + 1]`.
    have h : ι₀ ≫ (β_ _ _).hom = lift (stdSimplex.isTerminalObj₀.from _ ≫
        horn.ι 0 1 (by decide)) (𝟙 _) ≫ Λ[1, 0].ι ▷ Δ[n + 1] :=
      CartesianMonoidalCategory.hom_ext _ _ (by simp [horn_one_ι_eq_const]) (by simp)
    rw [reassoc_of% h, ← Subcomplex.unionProd.ι₂_ι, Category.assoc, hE, hpush.inr_desc,
      lift_snd_assoc, Category.id_comp]
  · rw [BraidedCategory.braiding_naturality_left_assoc, ← Subcomplex.unionProd.ι₁_ι,
      Category.assoc, hE, hpush.inl_desc, SymmetricCategory.symmetry_assoc]

variable {m : ℕ}

/-- **Joyal's theorem on special outer horns, parametrized.** Let `C` be a quasicategory. Over the
horns `Λ[m + 2, 0] ⟶ C` whose initial edge is an equivalence, restriction
`Fun(Δ[m + 2], C) ⟶ Fun(Λ[m + 2, 0], C)` has the right lifting property with respect to every
monomorphism `i : Y ⟶ Z`: a family of such horns parametrized by `Z`, whose restriction to `Y` is
filled, has a filling extending the given one. -/
theorem exists_lift_pre_horn_zero [Quasicategory C] {Y Z : SSet.{u}} (i : Y ⟶ Z) [Mono i]
    (t : Y ⟶ (ihom Δ[m + 2]).obj C) (b : Z ⟶ (ihom (Λ[m + 2, 0] : SSet.{u})).obj C)
    (w : t ≫ (pre Λ[m + 2, 0].ι).app C = i ≫ b)
    (hb : ∀ z : Z _⦋0⦌, (Edge.mk' ((ihomObj₀Equiv _ C (b.app _ z)).app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsEquivalence) :
    ∃ l : Z ⟶ (ihom Δ[m + 2]).obj C, i ≫ l = t ∧ l ≫ (pre Λ[m + 2, 0].ι).app C = b := by
  -- This is the case over a point of `SSet.exists_lift_ihomOver_pre_horn_zero`: every map lies
  -- over the point, and the equivalences of `C` are its coCartesian edges over the point.
  let t' : Y ⟶ ihomOver (terminal.from C) (terminal.from Δ[m + 2]) :=
    ihomOver.homEquiv.symm ⟨uncurry t, terminal.hom_ext _ _⟩
  let b' : Z ⟶ ihomOver (terminal.from C) (Λ[m + 2, 0].ι ≫ terminal.from Δ[m + 2]) :=
    ihomOver.homEquiv.symm ⟨uncurry b, terminal.hom_ext _ _⟩
  obtain ⟨l, hl₁, hl₂⟩ := exists_lift_ihomOver_pre_horn_zero (terminal.from C) _ i t' b'
    (ihomOver.homEquiv.injective (Subtype.ext (by
      rw [ihomOver.homEquiv_comp_pre_coe, ihomOver.homEquiv_comp_coe, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, ← uncurry_pre_app, w, uncurry_natural_left])))
    fun z ↦ by
      rw [ihomOver.obj₀Equiv_app_coe, Equiv.apply_symm_apply, ← ihomObj₀Equiv_app]
      exact (Edge.isEquivalence_iff_isCoCartesian _ _ terminalIsTerminal).1 (hb z)
  refine ⟨curry (ihomOver.homEquiv l).val, ?_, ?_⟩
  · rw [← curry_natural_left, ← ihomOver.homEquiv_comp_coe, hl₁, Equiv.apply_symm_apply,
      curry_uncurry]
  · rw [curry_pre_app, ← ihomOver.homEquiv_comp_pre_coe, hl₂, Equiv.apply_symm_apply,
      curry_uncurry]

end Quasicategory

end SSet
