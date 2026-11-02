/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The fundamental group of a graph of groups relative to a set of edges

For a graph of groups `𝔸` over a Serre graph `Γ` and a set `T` of darts of `Γ`, the group
`π₁(𝔸, T)` is the quotient of the free product of the vertex groups `A_v` and the free group on
the darts of `Γ` by the relations

* `rev e = e⁻¹` for every dart `e`;
* `e ω_e(c) e⁻¹ = α_e(c)` for every dart `e` and every `c ∈ A_e`;
* `e = 1` for every dart `e ∈ T`.

When `Γ` is connected and `T` is the set of darts of a maximal tree, this is Serre's group
`π₁(𝔸, T)`, one of the two standard models of the fundamental group of the graph of groups; the
other is the group of closed `𝔸`-paths at a base vertex. The construction itself makes sense for
every set of darts, and only the comparison with the path model uses that `T` is a maximal tree.

The group is characterised by its universal property: `TauCeti.GraphOfGroups.π₁Tree.lift` builds a
homomorphism `π₁(𝔸, T) →* H` from homomorphisms `φ_v : A_v →* H` and elements `h_e ∈ H` that
satisfy the three relations, and `TauCeti.GraphOfGroups.π₁Tree.homEquiv` states that every
homomorphism arises in this way from exactly one such family.

## Main definitions

* `TauCeti.GraphOfGroups.π₁Tree`: the group `π₁(𝔸, T)`.
* `TauCeti.GraphOfGroups.π₁Tree.of`: the homomorphism `A_v →* π₁(𝔸, T)`.
* `TauCeti.GraphOfGroups.π₁Tree.edge`: the element of `π₁(𝔸, T)` given by a dart.
* `TauCeti.GraphOfGroups.π₁Tree.lift`: the universal property.

## Main results

* `TauCeti.GraphOfGroups.π₁Tree.homEquiv`: homomorphisms out of `π₁(𝔸, T)` are the families
  `(φ_v, h_e)` satisfying the defining relations.
* `TauCeti.GraphOfGroups.π₁Tree.vertexEquivOfIsEmpty`: over a graph with one vertex and no
  edges, `π₁(𝔸, T)` is the vertex group.
* `TauCeti.GraphOfGroups.π₁Tree.equivFreeGroup`: with trivial vertex groups and `T` closed under
  reversal, `π₁(𝔸, T)` is the free group on the darts of `O \ T` for any orientation `O`. For
  the rose, whose maximal tree is empty, this is the free group on the petals.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.1.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ)

/-- The free product of the vertex groups of `𝔸` with the free group on the darts of the
underlying graph, of which `π₁(𝔸, T)` is a quotient. -/
abbrev π₁TreeCover : Type (max u v w) :=
  Monoid.Coprod (Monoid.CoprodI 𝔸.vertexGroup) (FreeGroup Γ.E)

/-- The defining relators of `π₁(𝔸, T)` in `π₁TreeCover 𝔸`: `rev e * e` for every dart `e`,
`e ω_e(c) e⁻¹ α_e(c)⁻¹` for every dart `e` and `c ∈ A_e`, and `e` for every dart `e ∈ T`. -/
def π₁TreeRels (T : Set Γ.E) : Set 𝔸.π₁TreeCover :=
  Set.range (fun e : Γ.E =>
      Monoid.Coprod.inr (FreeGroup.of (Γ.rev e)) * Monoid.Coprod.inr (FreeGroup.of e)) ∪
    Set.range (fun p : Σ e : Γ.E, 𝔸.edgeGroup (Γ.toGeomEdge e) =>
      Monoid.Coprod.inr (FreeGroup.of p.1) *
          Monoid.Coprod.inl (Monoid.CoprodI.of (𝔸.ω p.1 p.2)) *
          (Monoid.Coprod.inr (FreeGroup.of p.1))⁻¹ *
        (Monoid.Coprod.inl (Monoid.CoprodI.of (𝔸.α p.1 p.2)))⁻¹) ∪
    (fun e => Monoid.Coprod.inr (FreeGroup.of e)) '' T

/-- The fundamental group `π₁(𝔸, T)` of the graph of groups `𝔸` relative to a set `T` of darts:
the free product of the vertex groups and the free group on the darts, modulo `rev e = e⁻¹`,
`e ω_e(c) e⁻¹ = α_e(c)`, and `e = 1` for `e ∈ T`. For a maximal tree `T` of a connected graph
this is Serre's `π₁(𝔸, T)`. -/
def π₁Tree (T : Set Γ.E) : Type (max u v w) :=
  𝔸.π₁TreeCover ⧸ Subgroup.normalClosure (𝔸.π₁TreeRels T)
deriving Group

namespace π₁Tree

variable {𝔸} {T : Set Γ.E}

/-- The quotient map from the free product onto `π₁(𝔸, T)`. -/
def mk : 𝔸.π₁TreeCover →* π₁Tree 𝔸 T :=
  QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk : 𝔸.π₁TreeCover →* π₁Tree 𝔸 T) :=
  QuotientGroup.mk'_surjective _

@[simp] theorem mk_eq_one_iff {r : 𝔸.π₁TreeCover} :
    (mk r : π₁Tree 𝔸 T) = 1 ↔ r ∈ Subgroup.normalClosure (𝔸.π₁TreeRels T) :=
  QuotientGroup.eq_one_iff r

theorem mk_eq_one_of_mem {r : 𝔸.π₁TreeCover} (hr : r ∈ 𝔸.π₁TreeRels T) :
    (mk r : π₁Tree 𝔸 T) = 1 :=
  mk_eq_one_iff.2 (Subgroup.subset_normalClosure hr)

variable (T) in
/-- The homomorphism from the vertex group `A_v` to `π₁(𝔸, T)`. -/
def of (v : Γ.V) : 𝔸.vertexGroup v →* π₁Tree 𝔸 T :=
  mk.comp (Monoid.Coprod.inl.comp Monoid.CoprodI.of)

variable (T) in
/-- The element of `π₁(𝔸, T)` given by a dart `e`. -/
def edge (e : Γ.E) : π₁Tree 𝔸 T :=
  mk (Monoid.Coprod.inr (FreeGroup.of e))

/-- Reversing a dart inverts its element: `rev e = e⁻¹`. -/
@[simp] theorem edge_rev (e : Γ.E) : (edge T (Γ.rev e) : π₁Tree 𝔸 T) = (edge T e)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    simpa only [edge, map_mul] using
      mk_eq_one_of_mem (T := T) (Or.inl (Or.inl ⟨e, rfl⟩))

/-- The defining relation of an edge: `e ω_e(c) e⁻¹ = α_e(c)`. -/
theorem edge_mul_of_ω_mul_edge_inv (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    edge T e * of T (Γ.tgt e) (𝔸.ω e c) * (edge T e)⁻¹ = of T (Γ.src e) (𝔸.α e c) :=
  mul_inv_eq_one.1 <| by
    simpa only [edge, of, MonoidHom.comp_apply, map_mul, map_inv] using
      mk_eq_one_of_mem (T := T) (Or.inl (Or.inr ⟨⟨e, c⟩, rfl⟩))

/-- The defining relation of an edge, in the form `e ω_e(c) = α_e(c) e`. -/
theorem edge_mul_of_ω (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    edge T e * of T (Γ.tgt e) (𝔸.ω e c) = of T (Γ.src e) (𝔸.α e c) * edge T e := by
  rw [← edge_mul_of_ω_mul_edge_inv, inv_mul_cancel_right]

/-- The darts of `T` are trivial in `π₁(𝔸, T)`. -/
@[simp] theorem edge_eq_one {e : Γ.E} (he : e ∈ T) : (edge T e : π₁Tree 𝔸 T) = 1 :=
  mk_eq_one_of_mem (Or.inr ⟨e, he, rfl⟩)

/-- Two homomorphisms out of `π₁(𝔸, T)` agree when they agree on every vertex group and on every
dart. -/
@[ext high]
theorem hom_ext {M : Type*} [Monoid M] {f g : π₁Tree 𝔸 T →* M}
    (hof : ∀ v, f.comp (of T v) = g.comp (of T v)) (hedge : ∀ e, f (edge T e) = g (edge T e)) :
    f = g :=
  (MonoidHom.cancel_right mk_surjective).1 <|
    Monoid.Coprod.hom_ext (Monoid.CoprodI.ext_hom _ _ hof) (FreeGroup.ext_hom _ _ hedge)

variable {H : Type*} [Group H]

/-- The universal property of `π₁(𝔸, T)`: homomorphisms `φ_v : A_v →* H` and elements
`h_e ∈ H` with `h_e = 1` for `e ∈ T`, `h_{rev e} = h_e⁻¹` and `h_e φ(ω_e c) h_e⁻¹ = φ(α_e c)`
define a homomorphism `π₁(𝔸, T) →* H` sending `A_v` by `φ_v` and the dart `e` to `h_e`. -/
def lift (φ : ∀ v, 𝔸.vertexGroup v →* H) (h : Γ.E → H) (hT : ∀ e ∈ T, h e = 1)
    (hrev : ∀ e, h (Γ.rev e) = (h e)⁻¹)
    (hrel : ∀ e c, h e * φ (Γ.tgt e) (𝔸.ω e c) * (h e)⁻¹ = φ (Γ.src e) (𝔸.α e c)) :
    π₁Tree 𝔸 T →* H :=
  QuotientGroup.lift _ (Monoid.Coprod.lift (Monoid.CoprodI.lift φ) (FreeGroup.lift h)) <|
    Subgroup.normalClosure_le_normal <| by
      rintro _ ((⟨e, rfl⟩ | ⟨⟨e, c⟩, rfl⟩) | ⟨e, he, rfl⟩)
      · simp [hrev]
      · simp [hrel]
      · simp [hT e he]

section lift

variable (φ : ∀ v, 𝔸.vertexGroup v →* H) (h : Γ.E → H) (hT : ∀ e ∈ T, h e = 1)
  (hrev : ∀ e, h (Γ.rev e) = (h e)⁻¹)
  (hrel : ∀ e c, h e * φ (Γ.tgt e) (𝔸.ω e c) * (h e)⁻¹ = φ (Γ.src e) (𝔸.α e c))

@[simp] theorem lift_mk (r : 𝔸.π₁TreeCover) :
    lift φ h hT hrev hrel (mk r) =
      Monoid.Coprod.lift (Monoid.CoprodI.lift φ) (FreeGroup.lift h) r :=
  QuotientGroup.lift_mk' ..

@[simp] theorem lift_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    lift φ h hT hrev hrel (of T v a) = φ v a := by
  simp [of]

@[simp] theorem lift_comp_of (v : Γ.V) : (lift φ h hT hrev hrel).comp (of T v) = φ v :=
  MonoidHom.ext (lift_of φ h hT hrev hrel v)

@[simp] theorem lift_edge (e : Γ.E) : lift φ h hT hrev hrel (edge T e) = h e := by
  simp [edge]

end lift

variable (𝔸 T H) in
/-- Homomorphisms `π₁(𝔸, T) →* H` correspond to families of homomorphisms `φ_v : A_v →* H`
together with elements `h_e ∈ H` such that `h_e = 1` for `e ∈ T`, `h_{rev e} = h_e⁻¹` and
`h_e φ(ω_e c) h_e⁻¹ = φ(α_e c)`. -/
def homEquiv :
    (π₁Tree 𝔸 T →* H) ≃
      { p : (∀ v, 𝔸.vertexGroup v →* H) × (Γ.E → H) //
        (∀ e ∈ T, p.2 e = 1) ∧ (∀ e, p.2 (Γ.rev e) = (p.2 e)⁻¹) ∧
          ∀ e c, p.2 e * p.1 (Γ.tgt e) (𝔸.ω e c) * (p.2 e)⁻¹ = p.1 (Γ.src e) (𝔸.α e c) } where
  toFun f := ⟨(fun v => f.comp (of T v), fun e => f (edge T e)),
    fun e he => by simp [edge_eq_one he], fun e => by simp,
    fun e c => by
      simp only [MonoidHom.comp_apply, ← map_inv, ← map_mul, edge_mul_of_ω_mul_edge_inv]⟩
  invFun p := lift p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2
  left_inv f := hom_ext (fun v => lift_comp_of ..) (fun e => lift_edge ..)
  right_inv p := by
    ext
    · simp
    · simp

@[simp] theorem homEquiv_apply_coe (f : π₁Tree 𝔸 T →* H) :
    (homEquiv 𝔸 T H f : (∀ v, 𝔸.vertexGroup v →* H) × (Γ.E → H)) =
      (fun v => f.comp (of T v), fun e => f (edge T e)) :=
  (rfl)

@[simp] theorem homEquiv_symm_apply (p) :
    (homEquiv 𝔸 T H).symm p = lift p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2 :=
  (rfl)

section isEmpty

variable [Unique Γ.V] [IsEmpty Γ.E]

variable (𝔸 T) in
/-- Over a graph with a single vertex and no edges, `π₁(𝔸, T)` is the vertex group. -/
def vertexEquivOfIsEmpty : 𝔸.vertexGroup default ≃* π₁Tree 𝔸 T :=
  MonoidHom.toMulEquiv (of T default)
    (lift (fun v => (MulEquiv.cast (M := 𝔸.vertexGroup) (Subsingleton.elim v default)).toMonoidHom)
      isEmptyElim isEmptyElim isEmptyElim isEmptyElim)
    (MonoidHom.ext fun a => by simp)
    (hom_ext (fun v => by
        obtain rfl := Subsingleton.elim v default
        ext a
        simp)
      isEmptyElim)

@[simp] theorem vertexEquivOfIsEmpty_apply (a : 𝔸.vertexGroup default) :
    vertexEquivOfIsEmpty 𝔸 T a = of T default a :=
  (rfl)

end isEmpty

section trivialVertexGroups

variable [∀ v, Subsingleton (𝔸.vertexGroup v)] {O : Set Γ.E}

open Classical in
/-- The image of a dart in the free group on the darts of `O \ T`: the generator `e` if
`e ∈ O \ T`, its inverse if `rev e ∈ O \ T`, and `1` otherwise. -/
private noncomputable def dartWord (O T : Set Γ.E) (e : Γ.E) : FreeGroup ↥(O \ T) :=
  if h₁ : e ∈ O \ T then FreeGroup.of ⟨e, h₁⟩
  else if h₂ : Γ.rev e ∈ O \ T then (FreeGroup.of ⟨Γ.rev e, h₂⟩)⁻¹ else 1

private theorem dartWord_of_mem {e : Γ.E} (he : e ∈ O \ T) :
    dartWord O T e = FreeGroup.of ⟨e, he⟩ := by
  simp [dartWord, he]

private theorem dartWord_of_rev_mem {e : Γ.E} (he : e ∉ O \ T) (hr : Γ.rev e ∈ O \ T) :
    dartWord O T e = (FreeGroup.of ⟨Γ.rev e, hr⟩)⁻¹ := by
  simp [dartWord, he, hr]

private theorem dartWord_of_notMem {e : Γ.E} (he : e ∉ O \ T) (hr : Γ.rev e ∉ O \ T) :
    dartWord O T e = 1 := by
  simp [dartWord, he, hr]

private theorem dartWord_rev (hO : Γ.IsOrientation O) (e : Γ.E) :
    dartWord O T (Γ.rev e) = (dartWord O T e)⁻¹ := by
  by_cases he : e ∈ O \ T
  · have hr : Γ.rev e ∉ O \ T := fun h =>
      SerreGraph.IsOrientation.rev_notMem_of_mem _ hO e he.1 h.1
    rw [dartWord_of_rev_mem hr (by rwa [Γ.rev_rev]), dartWord_of_mem he]
    congr 2
    exact Subtype.ext (Γ.rev_rev e)
  by_cases hr : Γ.rev e ∈ O \ T
  · rw [dartWord_of_mem hr, dartWord_of_rev_mem he hr, inv_inv]
  · rw [dartWord_of_notMem hr (by rwa [Γ.rev_rev]), dartWord_of_notMem he hr, inv_one]

private theorem dartWord_of_mem_tree (hT : ∀ e ∈ T, Γ.rev e ∈ T) {e : Γ.E} (he : e ∈ T) :
    dartWord O T e = 1 :=
  dartWord_of_notMem (fun h => h.2 he) (fun h => h.2 (hT e he))

variable (𝔸) in
/-- A graph of groups with trivial vertex groups, relative to a set `T` of darts closed under
reversal, has fundamental group free on the darts of `O \ T` for any orientation `O`; the dart
`e ∈ O \ T` corresponds to the generator `e`. When `T` is a maximal tree, `O \ T` is the set of
positively oriented edges outside the tree. For the rose with petals `α`, the maximal tree is
`∅` and the positive darts `{e | e.2 = true}` form an orientation, giving a free group on the
petals. -/
noncomputable def equivFreeGroup (hO : Γ.IsOrientation O)
    (hT : ∀ e ∈ T, Γ.rev e ∈ T) : π₁Tree 𝔸 T ≃* FreeGroup ↥(O \ T) :=
  MonoidHom.toMulEquiv
    (lift (fun _ => 1) (dartWord O T) (fun _ => dartWord_of_mem_tree hT) (dartWord_rev hO)
      (fun _ _ => by simp))
    (FreeGroup.lift fun x => edge T x.1)
    (hom_ext (fun v => MonoidHom.ext fun a => by simp [Subsingleton.elim a 1]) fun e => by
      by_cases he : e ∈ O \ T
      · simp [dartWord_of_mem he]
      by_cases hr : Γ.rev e ∈ O \ T
      · simp [dartWord_of_rev_mem he hr]
      -- Neither `e` nor `rev e` lies in `O \ T`, and one of them lies in `O`, so `e ∈ T`.
      have heT : e ∈ T := by
        by_cases heO : e ∈ O
        · exact not_not.1 fun h => he ⟨heO, h⟩
        · have hrO := (SerreGraph.IsOrientation.mem_rev_iff _ hO e).2 heO
          have := hT _ (not_not.1 fun h => hr ⟨hrO, h⟩)
          rwa [Γ.rev_rev] at this
      simp [edge_eq_one heT])
    (FreeGroup.ext_hom _ _ fun x => by simp [dartWord_of_mem x.2])

@[simp] theorem equivFreeGroup_edge (hO : Γ.IsOrientation O)
    (hT : ∀ e ∈ T, Γ.rev e ∈ T) {e : Γ.E} (he : e ∈ O \ T) :
    equivFreeGroup 𝔸 hO hT (edge T e) = FreeGroup.of ⟨e, he⟩ := by
  simp [equivFreeGroup, dartWord_of_mem he]

@[simp] theorem equivFreeGroup_symm_of (hO : Γ.IsOrientation O)
    (hT : ∀ e ∈ T, Γ.rev e ∈ T) (x : ↥(O \ T)) :
    (equivFreeGroup 𝔸 hO hT).symm (FreeGroup.of x) = edge T x.1 := by
  simp [equivFreeGroup]

end trivialVertexGroups

end π₁Tree

end GraphOfGroups

end TauCeti
