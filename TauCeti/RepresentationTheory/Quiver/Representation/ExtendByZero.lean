/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.PathCategory.MorphismProperty
public import Mathlib.Combinatorics.Quiver.Cast
public import TauCeti.Combinatorics.Quiver.Embedding
public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional

/-!
# Extension by zero along an embedding of quivers

An **embedding of quivers** `φ : Q' → Q` (`TauCeti.QuiverEmbedding`) is a prefunctor injective on
vertices and on the arrows between each pair of vertices; it exhibits `Q'` as a subquiver of `Q`,
not necessarily full. A representation `M` of `Q'` then extends by zero to a representation of `Q`
(`TauCeti.QuiverEmbedding.extendByZeroRep`): it carries `M u` at `φ u` and the zero space at every
vertex outside the image, the image of an arrow `a` of `Q'` acts as `a`, and every other arrow of
`Q` acts by zero.

The point of the construction is that it loses nothing: extension by zero is a fully faithful
functor (`TauCeti.QuiverEmbedding.fullyFaithfulExtendByZeroFunctor`). A morphism between two
extensions by zero is determined by its components over the image, and those commute with the
arrows of `Q'` because the image of an arrow of `Q'` is not the image of any other. Hence extension
by zero preserves finite-dimensionality and indecomposability, and it reflects isomorphism. This is
how a representation-theoretic property of a subquiver is transported to the ambient quiver; in
particular a subquiver with infinitely many indecomposables forces the ambient quiver to have
infinitely many, the reduction by which the non-Dynkin half of Gabriel's theorem is proved.

## Main definitions

* `TauCeti.QuiverEmbedding.extendByZeroRep`: the extension by zero of a representation.
* `TauCeti.QuiverEmbedding.extendByZeroFunctor`: extension by zero as a functor.

## Main results

* `TauCeti.QuiverEmbedding.extendByZeroMap_map_apply`: the image of an arrow of `Q'` acts on the
  extension by zero as the arrow itself.
* `TauCeti.QuiverEmbedding.extendByZeroMap_apply_of_not_exists`: an arrow of `Q` that is not in
  the image acts by zero.
* `TauCeti.QuiverEmbedding.fullyFaithfulExtendByZeroFunctor`: extension by zero is fully faithful.
* `TauCeti.QuiverEmbedding.nonempty_extendByZeroRep_iso_iff`,
  `TauCeti.QuiverEmbedding.isFinDim_extendByZeroRep` and
  `TauCeti.QuiverEmbedding.indecomposable_extendByZeroRep`: extension by zero reflects and
  preserves isomorphism, and preserves finite-dimensionality and indecomposability.

## Implementation notes

The space over a vertex `v` of `Q` is the product of the spaces of `M` over the fiber of `φ` at
`v` (`TauCeti.QuiverEmbedding.Fiber`), which has at most one point. This names the space without
choosing a preimage of `v`, and without transporting `M` along an equality of vertices: over
`φ u` the fiber is the single point `⟨u, rfl⟩`, whose component is `M u` on the nose. The price is
a universe: the vertices of `Q'` are in `v'`, so the product is in `max v' t` when the spaces of
`M` are in `t`. For the quivers the theory is applied to, whose vertices form a `Type`, that is
`t` again.

An arrow `α : v ⟶ w` of `Q` acts on the component over `u'` through the arrow of `Q'` over `α`
ending at `u'`, when there is one; that arrow is picked by choice, and it is unique by injectivity,
which is what `TauCeti.QuiverEmbedding.extendByZeroMap_apply_of_cast_eq` records.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w v' w' t

namespace QuiverEmbedding

variable {Q' : Type v'} [Quiver.{w'} Q'] {Q : Type v} [Quiver.{w} Q] (φ : QuiverEmbedding Q' Q)

variable {k : Type u} [Field k]

open Classical in
/-- The action of an arrow `α : v ⟶ w` of `Q` on the extension by zero of `M`: the component over
`u'` is the action of the arrow of `Q'` over `α` ending at `u'`, applied to the component at its
source, if there is such an arrow, and zero otherwise. -/
noncomputable def extendByZeroMap (M : QuiverRep.{u, v', w', t} k Q') {v w : Q} (α : v ⟶ w) :
    (∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) →ₗ[k]
      ∀ u' : φ.Fiber w, QuiverRep.vertexSpace k Q' M u'.1 :=
  LinearMap.pi fun u' ↦
    if h : ∃ (u : φ.Fiber v) (a : u.1 ⟶ u'.1), (φ.map a).cast u.2 u'.2 = α then
      (QuiverRep.mapₗ k Q' M h.choose_spec.choose.toPath).comp (LinearMap.proj h.choose)
    else 0

variable {φ} in
/-- Two arrows of `Q'` over the same arrow of `Q` and with the same target act the same way on the
extension by zero: they have the same source, and then they coincide. -/
private theorem mapₗ_eq_of_cast_eq (M : QuiverRep.{u, v', w', t} k Q') {v w : Q} {α : v ⟶ w}
    {u₁ u₂ : φ.Fiber v} {u' : φ.Fiber w} {a₁ : u₁.1 ⟶ u'.1} {a₂ : u₂.1 ⟶ u'.1}
    (h₁ : (φ.map a₁).cast u₁.2 u'.2 = α) (h₂ : (φ.map a₂).cast u₂.2 u'.2 = α)
    (x : ∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) :
    QuiverRep.mapₗ k Q' M a₁.toPath (x u₁) = QuiverRep.mapₗ k Q' M a₂.toPath (x u₂) := by
  obtain ⟨u, rfl⟩ := u₁
  obtain ⟨u', rfl⟩ := u'
  obtain rfl : u₂ = ⟨u, rfl⟩ := Subsingleton.elim _ _
  simp only [Quiver.Hom.cast_eq_cast, cast_eq] at h₁ h₂
  obtain rfl := φ.map_injective (h₁.trans h₂.symm)
  rfl

/-- On a component over which `α` has a lift `a`, the extension by zero acts by `a`. -/
theorem extendByZeroMap_apply_of_cast_eq (M : QuiverRep.{u, v', w', t} k Q') {v w : Q}
    {α : v ⟶ w} (x : ∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) {u : φ.Fiber v}
    {u' : φ.Fiber w} (a : u.1 ⟶ u'.1) (ha : (φ.map a).cast u.2 u'.2 = α) :
    φ.extendByZeroMap M α x u' = QuiverRep.mapₗ k Q' M a.toPath (x u) := by
  have h : ∃ (u : φ.Fiber v) (a : u.1 ⟶ u'.1), (φ.map a).cast u.2 u'.2 = α := ⟨u, a, ha⟩
  rw [extendByZeroMap, LinearMap.pi_apply, dite_eq_left_of_eq_true (eq_true h),
    LinearMap.comp_apply, LinearMap.proj_apply]
  exact mapₗ_eq_of_cast_eq M h.choose_spec.choose_spec ha x

/-- **The image of an arrow acts on the extension by zero as the arrow itself**, from the component
at its source to the component at its target. -/
@[simp]
theorem extendByZeroMap_map_apply (M : QuiverRep.{u, v', w', t} k Q') {u u' : Q'} (a : u ⟶ u')
    (x : ∀ u'' : φ.Fiber (φ.obj u), QuiverRep.vertexSpace k Q' M u''.1) :
    φ.extendByZeroMap M (φ.map a) x ⟨u', rfl⟩ = QuiverRep.mapₗ k Q' M a.toPath (x ⟨u, rfl⟩) :=
  φ.extendByZeroMap_apply_of_cast_eq M x (u := ⟨u, rfl⟩) (u' := ⟨u', rfl⟩) a
    (Quiver.Hom.cast_rfl_rfl _)

/-- On a component over which `α` has no lift, the extension by zero acts by zero. -/
theorem extendByZeroMap_apply_of_not_exists (M : QuiverRep.{u, v', w', t} k Q') {v w : Q}
    {α : v ⟶ w} (x : ∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) {u' : φ.Fiber w}
    (h : ¬ ∃ (u : φ.Fiber v) (a : u.1 ⟶ u'.1), (φ.map a).cast u.2 u'.2 = α) :
    φ.extendByZeroMap M α x u' = 0 := by
  rw [extendByZeroMap, LinearMap.pi_apply, dite_eq_right_of_eq_false (eq_false h),
    LinearMap.zero_apply]

/-- **The extension by zero** of a representation `M` of `Q'` along an embedding `φ` into `Q`: the
representation of `Q` with `M u` at `φ u` and the zero space at every vertex outside the image,
on which the image of an arrow `a` of `Q'` acts as `a` and every other arrow of `Q` acts by zero.

The space over a vertex `v` is the product of the spaces of `M` over the fiber of `φ` at `v`,
which has at most one point; this names it without choosing a preimage of `v`. -/
-- The object and arrow API below elaborates using the value of this functor at a vertex.
@[expose]
noncomputable def extendByZeroRep (M : QuiverRep.{u, v', w', t} k Q') :
    QuiverRep.{u, v, w, max v' t} k Q :=
  Paths.lift
    { obj := fun v ↦ ModuleCat.of k (∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1)
      map := fun α ↦ ModuleCat.ofHom (φ.extendByZeroMap M α) }

variable (M : QuiverRep.{u, v', w', t} k Q')

/-- The space of the extension by zero over a vertex is the product of the spaces of `M` over the
fiber there. -/
@[simp]
theorem extendByZeroRep_obj (v : Q) :
    (φ.extendByZeroRep M).obj (v : Paths Q) =
      ModuleCat.of k (∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) :=
  rfl

/-- An arrow of `Q` acts on the extension by zero by `TauCeti.QuiverEmbedding.extendByZeroMap`. -/
@[simp]
theorem extendByZeroRep_map_toPath {v w : Q} (α : v ⟶ w) :
    (φ.extendByZeroRep M).map α.toPath = ModuleCat.ofHom (φ.extendByZeroMap M α) :=
  Paths.lift_toPath _ α

variable {M} {N : QuiverRep.{u, v', w', t} k Q'}

/-- The component over a vertex of the extension by zero of a morphism `f`: `f` over the fiber. -/
noncomputable def extendByZeroApp (f : M ⟶ N) (v : Q) :
    (∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) →ₗ[k]
      ∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' N u.1 :=
  LinearMap.piMap fun u ↦ (f.app u.1).hom

/-- The component of the extension by zero of `f` over the point `u` of a fiber is `f` at `u`. -/
@[simp]
theorem extendByZeroApp_apply (f : M ⟶ N) (v : Q)
    (x : ∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) (u : φ.Fiber v) :
    φ.extendByZeroApp f v x u = f.app u.1 (x u) :=
  (rfl)

/-- A morphism of representations commutes with the retyped action of a path. -/
private theorem app_mapₗ (f : M ⟶ N) {u u' : Q'} (p : Quiver.Path u u')
    (z : QuiverRep.vertexSpace k Q' M u) :
    f.app u' (QuiverRep.mapₗ k Q' M p z) = QuiverRep.mapₗ k Q' N p (f.app u z) :=
  ((ModuleCat.comp_apply _ _ z).symm.trans (ConcreteCategory.congr_hom (f.naturality p) z)).trans
    (ModuleCat.comp_apply _ _ z)

/-- The extension by zero of a morphism commutes with the action of every arrow of `Q`: over the
image of an arrow of `Q'` this is naturality of `f`, and elsewhere both sides vanish. -/
theorem extendByZeroMap_comp_extendByZeroApp (f : M ⟶ N) {v w : Q} (α : v ⟶ w) :
    φ.extendByZeroApp f w ∘ₗ φ.extendByZeroMap M α =
      φ.extendByZeroMap N α ∘ₗ φ.extendByZeroApp f v := by
  refine LinearMap.ext fun x ↦ funext fun u' ↦ ?_
  simp only [LinearMap.comp_apply, extendByZeroApp_apply]
  by_cases h : ∃ (u : φ.Fiber v) (a : u.1 ⟶ u'.1), (φ.map a).cast u.2 u'.2 = α
  · obtain ⟨u, a, ha⟩ := h
    rw [φ.extendByZeroMap_apply_of_cast_eq M x a ha,
      φ.extendByZeroMap_apply_of_cast_eq N _ a ha, extendByZeroApp_apply]
    exact app_mapₗ f a.toPath (x u)
  · rw [φ.extendByZeroMap_apply_of_not_exists M x h,
      φ.extendByZeroMap_apply_of_not_exists N _ h]
    exact map_zero _

variable (k) in
/-- **Extension by zero along an embedding of quivers**, as a functor from the representations of
`Q'` to those of `Q`; on a morphism it acts by that morphism over the image and by zero
elsewhere. -/
-- The componentwise map API below elaborates using the objects of this functor.
@[expose]
noncomputable def extendByZeroFunctor :
    QuiverRep.{u, v', w', t} k Q' ⥤ QuiverRep.{u, v, w, max v' t} k Q where
  obj M := φ.extendByZeroRep M
  map f := Paths.liftNatTrans (fun v ↦ ModuleCat.ofHom (φ.extendByZeroApp f v)) fun α ↦ by
    rw [extendByZeroRep_map_toPath, extendByZeroRep_map_toPath]
    exact ModuleCat.hom_ext (φ.extendByZeroMap_comp_extendByZeroApp f α)
  map_id M := by
    refine NatTrans.ext (funext fun v ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    rfl
  map_comp f g := by
    refine NatTrans.ext (funext fun v ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    rfl

/-- The extension by zero functor sends a representation to its extension by zero. -/
@[simp]
theorem extendByZeroFunctor_obj : (φ.extendByZeroFunctor k).obj M = φ.extendByZeroRep M :=
  rfl

-- Not `@[simp]`: `TauCeti.QuiverEmbedding.extendByZeroFunctor_obj` and
-- `TauCeti.QuiverEmbedding.extendByZeroRep_obj` rewrite the objects in the implicit arguments of
-- its left-hand side, so it would not be in simp-normal form (`simpNF`).
/-- The extension by zero of a morphism `f` acts over the point `u` of a fiber as `f` at `u`. -/
theorem extendByZeroFunctor_map_app_apply (f : M ⟶ N) (v : Q)
    (x : ∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) (u : φ.Fiber v) :
    ((φ.extendByZeroFunctor k).map f).app (v : Paths Q) x u = f.app u.1 (x u) :=
  (rfl)

/-- Extension by zero is additive: it acts on morphisms componentwise. -/
instance : (φ.extendByZeroFunctor k : QuiverRep.{u, v', w', t} k Q' ⥤ _).Additive where
  map_add {M N f g} := by
    refine NatTrans.ext (funext fun v ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    rfl

/-! ### Full faithfulness -/

/-- A morphism between extensions by zero commutes with the action of every arrow of `Q`. -/
private theorem app_extendByZeroMap (g : φ.extendByZeroRep M ⟶ φ.extendByZeroRep N) {v w : Q}
    (α : v ⟶ w) (z : ∀ u : φ.Fiber v, QuiverRep.vertexSpace k Q' M u.1) :
    g.app w (φ.extendByZeroMap M α z) = φ.extendByZeroMap N α (g.app v z) := by
  have h := g.naturality α.toPath
  rw [extendByZeroRep_map_toPath, extendByZeroRep_map_toPath] at h
  exact ((ModuleCat.comp_apply (ModuleCat.ofHom (φ.extendByZeroMap M α)) (g.app w) z).symm.trans
    (ConcreteCategory.congr_hom h z)).trans
      (ModuleCat.comp_apply (g.app v) (ModuleCat.ofHom (φ.extendByZeroMap N α)) z)

/-- An element of the product over a fiber is determined by its component at the one point. -/
private theorem single_self {u : Q'} [DecidableEq (φ.Fiber (φ.obj u))]
    {X : φ.Fiber (φ.obj u) → Type*} [∀ u', AddCommMonoid (X u')] (x : ∀ u', X u') :
    Pi.single ⟨u, rfl⟩ (x ⟨u, rfl⟩) = x := by
  refine funext fun u' ↦ ?_
  obtain rfl : u' = ⟨u, rfl⟩ := Subsingleton.elim _ _
  exact Pi.single_eq_same _ _

open Classical in
/-- The component at `u` of the morphism of representations of `Q'` underlying a morphism of
extensions by zero: the component of `g` over `φ u`, read on the one point of the fiber. -/
private noncomputable def preimageApp (g : φ.extendByZeroRep M ⟶ φ.extendByZeroRep N) (u : Q') :
    QuiverRep.vertexSpace k Q' M u →ₗ[k] QuiverRep.vertexSpace k Q' N u :=
  LinearMap.proj (φ := fun u' : φ.Fiber (φ.obj u) ↦ QuiverRep.vertexSpace k Q' N u'.1) ⟨u, rfl⟩ ∘ₗ
    (g.app (φ.obj u)).hom ∘ₗ
      LinearMap.single k (fun u' : φ.Fiber (φ.obj u) ↦ QuiverRep.vertexSpace k Q' M u'.1) ⟨u, rfl⟩

open Classical in
private theorem preimageApp_apply (g : φ.extendByZeroRep M ⟶ φ.extendByZeroRep N) (u : Q')
    (y : QuiverRep.vertexSpace k Q' M u) :
    preimageApp φ g u y = g.app (φ.obj u) (Pi.single ⟨u, rfl⟩ y) ⟨u, rfl⟩ :=
  rfl

/-- The components `TauCeti.QuiverEmbedding.preimageApp` commute with the action of every arrow
of `Q'`, because `g` commutes with the action of its image. -/
private theorem preimageApp_mapₗ (g : φ.extendByZeroRep M ⟶ φ.extendByZeroRep N) {u u' : Q'}
    (a : u ⟶ u') (y : QuiverRep.vertexSpace k Q' M u) :
    preimageApp φ g u' (QuiverRep.mapₗ k Q' M a.toPath y) =
      QuiverRep.mapₗ k Q' N a.toPath (preimageApp φ g u y) := by
  classical
  have hsingle : (Pi.single ⟨u', rfl⟩ (QuiverRep.mapₗ k Q' M a.toPath y) :
      ∀ u'' : φ.Fiber (φ.obj u'), QuiverRep.vertexSpace k Q' M u''.1) =
      φ.extendByZeroMap M (φ.map a) (Pi.single ⟨u, rfl⟩ y) := by
    refine funext fun u'' ↦ ?_
    obtain rfl : u'' = ⟨u', rfl⟩ := Subsingleton.elim _ _
    rw [Pi.single_eq_same, extendByZeroMap_map_apply, Pi.single_eq_same]
  rw [preimageApp_apply, preimageApp_apply, hsingle, app_extendByZeroMap]
  exact φ.extendByZeroMap_map_apply N a _

variable (k) in
/-- **Extension by zero along an embedding of quivers is fully faithful.** A morphism between two
extensions by zero is the extension by zero of its components over the image, which form a morphism
of representations of `Q'` because the embedding is injective on arrows. -/
noncomputable def fullyFaithfulExtendByZeroFunctor :
    (φ.extendByZeroFunctor k : QuiverRep.{u, v', w', t} k Q' ⥤ _).FullyFaithful where
  preimage {M N} g := Paths.liftNatTrans (fun u ↦ ModuleCat.ofHom (preimageApp φ g u)) fun a ↦
    ModuleCat.hom_ext (LinearMap.ext fun y ↦ preimageApp_mapₗ φ g a y)
  map_preimage {M N} g := by
    classical
    refine NatTrans.ext (funext fun v ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    refine funext fun u' ↦ ?_
    obtain ⟨u', rfl⟩ := u'
    exact (preimageApp_apply φ g u' _).trans
      (congrArg (fun z ↦ g.app (φ.obj u') z ⟨u', rfl⟩) (single_self φ x))
  preimage_map {M N} f := by
    classical
    refine NatTrans.ext (funext fun u ↦ ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_))
    exact (preimageApp_apply φ ((φ.extendByZeroFunctor k).map f) u y).trans
      (congrArg (f.app u) (Pi.single_eq_same _ _))

/-! ### What extension by zero preserves -/

variable (M N)

/-- **Extension by zero reflects and preserves isomorphism**: two representations of `Q'` are
isomorphic exactly when their extensions by zero are. -/
@[simp]
theorem nonempty_extendByZeroRep_iso_iff :
    Nonempty (φ.extendByZeroRep M ≅ φ.extendByZeroRep N) ↔ Nonempty (M ≅ N) :=
  ⟨fun ⟨e⟩ ↦ ⟨(φ.fullyFaithfulExtendByZeroFunctor k).preimageIso e⟩,
    fun ⟨e⟩ ↦ ⟨(φ.extendByZeroFunctor k).mapIso e⟩⟩

variable {M N}

/-- **The extension by zero of a finite-dimensional representation is finite-dimensional**: each
of its spaces is a product of at most one space of `M`. -/
theorem isFinDim_extendByZeroRep (hM : IsFinDim k Q' M) :
    IsFinDim k Q (φ.extendByZeroRep M) := by
  refine isFinDim_iff.mpr fun (v : Q) ↦ ?_
  have (u : φ.Fiber v) : Module.Finite k (QuiverRep.vertexSpace k Q' M u.1) :=
    isFinDim_iff.mp hM u.1
  have : Finite (φ.Fiber v) := Finite.of_subsingleton
  exact Module.Finite.pi

/-- **The extension by zero of an indecomposable representation is indecomposable**: extension by
zero is fully faithful, so it matches the idempotent endomorphisms of `M` with those of its
extension. -/
theorem indecomposable_extendByZeroRep (hM : Indecomposable M) :
    Indecomposable (φ.extendByZeroRep M) :=
  (φ.extendByZeroFunctor k).indecomposable_obj_of_map_bijective hM
    ((φ.fullyFaithfulExtendByZeroFunctor k).map_bijective M M)

end QuiverEmbedding

end TauCeti
