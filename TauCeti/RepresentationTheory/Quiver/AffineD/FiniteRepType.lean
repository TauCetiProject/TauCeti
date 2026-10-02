/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AffineD.Basic
public import TauCeti.RepresentationTheory.Quiver.Subspace.FiniteRepType

/-!
# The extended Dynkin quiver `D̃ₙ` has infinite representation type

The quiver `TauCeti.Quiver.AffineD m`, whose underlying graph is the extended Dynkin diagram
`D̃ₘ₊₄`, has infinitely many finite-dimensional indecomposable representations over every field
(`TauCeti.not_isFiniteRepType_affineD`).

The proof reduces to the four subspace quiver, the case `m = 0`, which is already known to have
infinite representation type (`TauCeti.not_isFiniteRepType_subspace_fin_four`). A representation
`M` of the four subspace quiver is *stretched* along the spine (`TauCeti.affineDStretchRep`): its
centre space is placed at every spine vertex, with the identity on every spine arrow, and its four
outer spaces at the four leaves, each leaf arrow acting as the corresponding arrow of `M`.

Stretching is fully faithful (`TauCeti.fullyFaithfulAffineDStretchFunctor`). A morphism between
stretched representations commutes with the identity maps along the spine, so its components at
all the spine vertices agree; that common component, together with the components at the leaves,
is a morphism of the original representations. Stretching therefore preserves indecomposability
and reflects isomorphism, and it preserves finite-dimensionality, so it embeds the
finite-dimensional indecomposables of the four subspace quiver, up to isomorphism, in those of
`TauCeti.Quiver.AffineD m`.

## Main definitions

* `TauCeti.affineDStretchRep`: a representation of the four subspace quiver, stretched along the
  spine of `TauCeti.Quiver.AffineD m`.
* `TauCeti.affineDStretchFunctor`: stretching, as a functor.

## Main results

* `TauCeti.fullyFaithfulAffineDStretchFunctor`: stretching is fully faithful.
* `TauCeti.IsFiniteRepType.subspace_fin_four_of_affineD`: finite representation type of
  `TauCeti.Quiver.AffineD m` would force it on the four subspace quiver.
* `TauCeti.not_isFiniteRepType_affineD`: `TauCeti.Quiver.AffineD m` has infinite representation
  type over every field.

## Implementation notes

`TauCeti.affineDStretchRep` carries `@[expose]` for the reason recorded on
`TauCeti.subspaceJordanRep`: a functor built by `CategoryTheory.Paths.lift` reveals its vertex
spaces only through its definition, and the components of the stretching functor on morphisms
are typed by them.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

open CategoryTheory

universe u t

variable {k : Type u} [Field k] {m : ℕ}

/-- **A representation of the four subspace quiver, stretched along the spine of
`TauCeti.Quiver.AffineD m`**: the centre space of `M` sits at every spine vertex, with the identity
on every spine arrow, and the outer space indexed by `i` at the leaf indexed by `i`, whose arrow
acts as the arrow of `M` from that outer vertex. -/
@[expose]
noncomputable def affineDStretchRep (m : ℕ)
    (M : QuiverRep.{u, 0, 1, t} k (Quiver.Subspace (Fin 4))) :
    QuiverRep.{u, 0, 0, t} k (Quiver.AffineD m) :=
  Paths.lift
    { obj := fun v ↦ match v with
        | .leaf i => M.obj (Quiver.Subspace.outer i : Paths (Quiver.Subspace (Fin 4)))
        | .spine _ => M.obj (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4)))
      map := fun {a b} e ↦ match a, b, e with
        | .leaf i, .spine _, _ => M.map (Quiver.Subspace.arrow i).toPath
        | .spine _, .spine _, _ => 𝟙 _
        | .leaf _, .leaf _, e => isEmptyElim e
        | .spine _, .leaf _, e => isEmptyElim e }

variable {M N : QuiverRep.{u, 0, 1, t} k (Quiver.Subspace (Fin 4))}

/-- The leaf indexed by `i` of a stretched representation carries the outer space of `M` indexed
by `i`. -/
@[simp]
theorem affineDStretchRep_obj_leaf (i : Fin 4) :
    (affineDStretchRep m M).obj (Quiver.AffineD.leaf i : Paths (Quiver.AffineD m)) =
      M.obj (Quiver.Subspace.outer i : Paths (Quiver.Subspace (Fin 4))) :=
  rfl

/-- Every spine vertex of a stretched representation carries the centre space of `M`. -/
@[simp]
theorem affineDStretchRep_obj_spine (j : Fin (m + 1)) :
    (affineDStretchRep m M).obj (Quiver.AffineD.spine j : Paths (Quiver.AffineD m)) =
      M.obj (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4))) :=
  rfl

/-- The leaf arrow indexed by `i` acts on a stretched representation as the arrow of `M` from the
outer vertex indexed by `i`. -/
@[simp]
theorem affineDStretchRep_map_leafArrow (i : Fin 4) :
    (affineDStretchRep m M).map (Quiver.AffineD.leafArrow m i).toPath =
      M.map (Quiver.Subspace.arrow i).toPath :=
  Paths.lift_toPath _ _

/-- Every spine arrow acts on a stretched representation as the identity. -/
@[simp]
theorem affineDStretchRep_map_spineArrow (j : Fin m) :
    (affineDStretchRep m M).map (Quiver.AffineD.spineArrow j).toPath =
      𝟙 (M.obj (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4)))) :=
  Paths.lift_toPath _ _

/-- **A stretched representation of a finite-dimensional representation is finite-dimensional**:
its vertex spaces are vertex spaces of `M`. -/
theorem isFinDim_affineDStretchRep (hM : IsFinDim k (Quiver.Subspace (Fin 4)) M) :
    IsFinDim k (Quiver.AffineD m) (affineDStretchRep m M) := by
  refine isFinDim_iff.mpr fun v ↦ ?_
  cases v with
  | leaf i => exact isFinDim_iff.mp hM (Quiver.Subspace.outer i : Paths (Quiver.Subspace (Fin 4)))
  | spine _ => exact isFinDim_iff.mp hM (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4)))

/-- The components of the stretch of a morphism: the centre component at every spine vertex, and
the outer component indexed by `i` at the leaf indexed by `i`. -/
private noncomputable def stretchApp (f : M ⟶ N) :
    ∀ v : Quiver.AffineD m, (affineDStretchRep m M).obj v ⟶ (affineDStretchRep m N).obj v
  | .leaf i => f.app (Quiver.Subspace.outer i : Paths (Quiver.Subspace (Fin 4)))
  | .spine _ => f.app (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4)))

/-- The components `stretchApp` commute with the action of every arrow of
`TauCeti.Quiver.AffineD m`: along a leaf arrow by naturality of `f`, and along a spine arrow
because it acts by the identity. -/
private theorem stretchApp_naturality (f : M ⟶ N) {a b : Quiver.AffineD m} (e : a ⟶ b) :
    (affineDStretchRep m M).map e.toPath ≫ stretchApp f b =
      stretchApp f a ≫ (affineDStretchRep m N).map e.toPath := by
  match a, b, e with
  | .leaf i, .spine j, e =>
    obtain rfl : j = Quiver.AffineD.leafTarget m i := e.down
    obtain rfl : e = Quiver.AffineD.leafArrow m i := Subsingleton.elim _ _
    rw [affineDStretchRep_map_leafArrow, affineDStretchRep_map_leafArrow]
    exact f.naturality (Quiver.Subspace.arrow i).toPath
  | .spine _, .spine _, _ =>
    -- Both spine maps are identities, so the square commutes trivially.
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  | .leaf _, .leaf _, e => exact isEmptyElim e
  | .spine _, .leaf _, e => exact isEmptyElim e

variable (k m) in
/-- **Stretching along the spine of `TauCeti.Quiver.AffineD m`, as a functor**: on a morphism it
acts by its centre component at every spine vertex and by its outer components at the leaves. -/
noncomputable def affineDStretchFunctor :
    QuiverRep.{u, 0, 1, t} k (Quiver.Subspace (Fin 4)) ⥤
      QuiverRep.{u, 0, 0, t} k (Quiver.AffineD m) where
  obj M := affineDStretchRep m M
  map f := Paths.liftNatTrans (stretchApp f) (stretchApp_naturality f)
  map_id M := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v <;> rfl
  map_comp f g := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v <;> rfl

/-- The stretching functor sends a representation to its stretch. -/
@[simp]
theorem affineDStretchFunctor_obj : (affineDStretchFunctor k m).obj M = affineDStretchRep m M :=
  (rfl)

/-! ### Full faithfulness -/

/-- The component at the spine vertex indexed by `j` of a morphism of stretched representations,
as a map between the centre spaces. -/
private noncomputable def spineApp (g : affineDStretchRep m M ⟶ affineDStretchRep m N)
    (j : Fin (m + 1)) :
    M.obj (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4))) ⟶
      N.obj (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4))) :=
  g.app (Quiver.AffineD.spine j : Paths (Quiver.AffineD m))

/-- **The spine components of a morphism of stretched representations agree**: naturality along
each spine arrow, which acts by the identity, equates the components at its two ends. -/
private theorem spineApp_eq (g : affineDStretchRep m M ⟶ affineDStretchRep m N)
    (j : Fin (m + 1)) : spineApp g j = spineApp g 0 := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    have h := g.naturality (Quiver.AffineD.spineArrow j).toPath
    rw [affineDStretchRep_map_spineArrow, affineDStretchRep_map_spineArrow] at h
    exact (((Category.id_comp _).symm.trans h).trans (Category.comp_id _)).trans ih

/-- The components of the morphism of representations of the four subspace quiver underlying a
morphism of stretched representations: the common spine component at the centre, and the leaf
components at the outer vertices. -/
private noncomputable def unstretchApp (g : affineDStretchRep m M ⟶ affineDStretchRep m N) :
    ∀ v : Quiver.Subspace (Fin 4), M.obj v ⟶ N.obj v
  | .center => spineApp g 0
  | .outer i => g.app (Quiver.AffineD.leaf i : Paths (Quiver.AffineD m))

/-- The components `unstretchApp` commute with the four arrows: naturality of `g` along a leaf
arrow, with the spine component at its head replaced by the common one. -/
private theorem unstretchApp_naturality (g : affineDStretchRep m M ⟶ affineDStretchRep m N)
    {a b : Quiver.Subspace (Fin 4)} (e : a ⟶ b) :
    M.map e.toPath ≫ unstretchApp g b = unstretchApp g a ≫ N.map e.toPath := by
  match a, b, e with
  | .outer i, .center, e =>
    obtain rfl : e = Quiver.Subspace.arrow i := Subsingleton.elim _ _
    have h := g.naturality (Quiver.AffineD.leafArrow m i).toPath
    rw [affineDStretchRep_map_leafArrow, affineDStretchRep_map_leafArrow] at h
    exact (congrArg (M.map (Quiver.Subspace.arrow i).toPath ≫ ·)
      (spineApp_eq g (Quiver.AffineD.leafTarget m i)).symm).trans h
  | .center, .center, e => exact isEmptyElim e
  | .center, .outer _, e => exact isEmptyElim e
  | .outer _, .outer _, e => exact isEmptyElim e

variable (k m) in
/-- **Stretching along the spine of `TauCeti.Quiver.AffineD m` is fully faithful.** A morphism of
stretched representations has equal components at all the spine vertices, and that common
component together with the leaf components is a morphism of the original representations. -/
noncomputable def fullyFaithfulAffineDStretchFunctor :
    (affineDStretchFunctor.{u, t} k m).FullyFaithful where
  preimage {M N} g := Paths.liftNatTrans (unstretchApp g) (unstretchApp_naturality g)
  map_preimage {M N} g := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v with
    | leaf i => rfl
    | spine j => exact (spineApp_eq g j).symm
  preimage_map {M N} f := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v <;> rfl

/-- **Stretching reflects and preserves isomorphism**: two representations of the four subspace
quiver are isomorphic exactly when their stretches along the spine of `TauCeti.Quiver.AffineD m`
are. -/
@[simp]
theorem nonempty_affineDStretchRep_iso_iff :
    Nonempty (affineDStretchRep m M ≅ affineDStretchRep m N) ↔ Nonempty (M ≅ N) :=
  ⟨fun ⟨e⟩ ↦ ⟨(fullyFaithfulAffineDStretchFunctor k m).preimageIso e⟩,
    fun ⟨e⟩ ↦ ⟨(affineDStretchFunctor k m).mapIso e⟩⟩

/-- **The stretch of an indecomposable representation is indecomposable**: stretching is fully
faithful, so it matches the idempotent endomorphisms of `M` with those of its stretch. -/
theorem indecomposable_affineDStretchRep (hM : Indecomposable M) :
    Indecomposable (affineDStretchRep m M) :=
  (affineDStretchFunctor k m).indecomposable_obj_of_map_bijective hM
    ((fullyFaithfulAffineDStretchFunctor k m).map_bijective M M)

/-! ### Infinite representation type -/

/-- **Finite representation type of `TauCeti.Quiver.AffineD m` would force it on the four subspace
quiver**: stretching carries the finite-dimensional indecomposables of the four subspace quiver
to finite-dimensional indecomposables of `TauCeti.Quiver.AffineD m` and reflects isomorphism
among them. -/
theorem IsFiniteRepType.subspace_fin_four_of_affineD
    (h : IsFiniteRepType.{u, 0, 0, t} k (Quiver.AffineD m)) :
    IsFiniteRepType.{u, 0, 1, t} k (Quiver.Subspace (Fin 4)) :=
  isFiniteRepType_of_map (fun _ ↦ False) (affineDStretchRep m)
    (fun _ hM hM' _ ↦ ⟨isFinDim_affineDStretchRep hM, indecomposable_affineDStretchRep hM'⟩)
    (fun _ _ _ _ _ _ ↦ nonempty_affineDStretchRep_iso_iff.mp) (fun _ _ _ _ h _ ↦ h.elim) h

/-- **The extended Dynkin quiver `D̃ₘ₊₄` has infinite representation type over every field.** The
stretches along its spine of the Jordan block configurations of four subspaces
(`TauCeti.subspaceJordanRep`) are infinitely many pairwise non-isomorphic finite-dimensional
indecomposables. -/
theorem not_isFiniteRepType_affineD (k : Type u) [Field k] (m : ℕ) :
    ¬ IsFiniteRepType.{u, 0, 0, u} k (Quiver.AffineD m) :=
  fun h ↦ not_isFiniteRepType_subspace_fin_four k h.subspace_fin_four_of_affineD

end TauCeti
