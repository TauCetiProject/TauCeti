/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CategoricalEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.InfinityOperad
public import TauCeti.AlgebraicTopology.Quasicategory.Product

/-!
# Symmetric monoidal quasicategories

A symmetric monoidal quasicategory is a coCartesian fibration `p : C^⊗ ⟶ N(Fin_*)` over the nerve
of the category `TauCeti.FinPointed` of finite pointed sets `⟨n⟩ = Fin (n + 1)`, satisfying the
*Segal condition*: for every `n`, the functors `(ρ i)_! : C_⟨n⟩ ⟶ C_⟨1⟩` associated to the inert
projections `ρ i : ⟨n⟩ ⟶ ⟨1⟩` together give a categorical equivalence
`C_⟨n⟩ ⟶ ∏_{i < n} C_⟨1⟩`. The fiber `C = C_⟨1⟩` is the underlying quasicategory, the fiber
`C_⟨n⟩` is a model of `C^n`, and the functor associated to the active map `⟨2⟩ ⟶ ⟨1⟩` is the
tensor product. The fiber `C_⟨0⟩` is contractible, and the functor associated to the map
`⟨0⟩ ⟶ ⟨1⟩` picks out the unit.

The functors `(ρ i)_!` are given by coCartesian transports (`SSet.CoCartesianTransport`), and the
Segal condition asks for transports along the projections whose product is a categorical
equivalence. Associated functors are unique up to equivalence, so this does not depend on the
choice of transports, but that comparison is not proved here.

A symmetric monoidal functor between symmetric monoidal quasicategories `p` and `q` is a map
`C^⊗ ⟶ D^⊗` over `N(Fin_*)` preserving coCartesian edges; a lax symmetric monoidal functor is only
required to preserve the coCartesian edges lying over inert maps, that is, it is a map of
`∞`-operads `SSet.InfinityOperad.Hom p q`.

## Main definitions

* `SSet.segalMap T`: the map `C_⟨n⟩ ⟶ ∏_{i < n} C_⟨1⟩` given by transports `T` along the inert
  projections.
* `SSet.IsSegal p`: the Segal condition.
* `SSet.SymmetricMonoidal p`: the coCartesian fibration `p` over `N(Fin_*)` satisfies the Segal
  condition.
* `SSet.SymmetricMonoidalFunctor p q`: maps over `N(Fin_*)` preserving all coCartesian edges,
  with their identities, composites and underlying functors on the fibers over `⟨1⟩`.
* `SSet.SymmetricMonoidalFunctor.toOperadHom`: the underlying lax symmetric monoidal functor, a
  map of `∞`-operads.

## Main results

* `SSet.symmetricMonoidal_of_isIso`: an isomorphism onto `N(Fin_*)` is symmetric monoidal; for
  instance the identity of `N(Fin_*)`, the terminal symmetric monoidal quasicategory.
* `SSet.not_symmetricMonoidal_of_not_nonempty`: the empty simplicial set over `N(Fin_*)` is not
  symmetric monoidal, since its fiber over `⟨0⟩` is not a point.

## References

* J. Lurie, *Higher Algebra*, Definition 2.0.0.7, Definition 2.1.3.7 and Remark 2.1.3.8.
-/

public section

universe u

open CategoryTheory Limits Simplicial TauCeti

namespace SSet

variable {X Y Z : SSet.{u}}

/-- The Segal map `C_⟨n⟩ ⟶ ∏_{i < n} C_⟨1⟩` of a map `p : C^⊗ ⟶ N(Fin_*)`, given by
coCartesian transports `T i` along the inert projections `ρ i : ⟨n⟩ ⟶ ⟨1⟩`: its components are
the functors `(ρ i)_!` associated to them. -/
noncomputable def segalMap {p : X ⟶ nerve FinPointed.{u}} {n : FinPointed.{u}}
    (T : ∀ i : Fin n.len, CoCartesianTransport p (nerve.edgeMk (FinPointed.ρ i))) :
    (fiber p n.vertex : SSet) ⟶
      ∏ᶜ fun _ : Fin n.len ↦ (fiber p (FinPointed.mk 1).vertex : SSet) :=
  Pi.lift fun i ↦ (T i).functor

@[reassoc (attr := simp)]
lemma segalMap_π {p : X ⟶ nerve FinPointed.{u}} {n : FinPointed.{u}}
    (T : ∀ i : Fin n.len, CoCartesianTransport p (nerve.edgeMk (FinPointed.ρ i)))
    (i : Fin n.len) :
    segalMap T ≫ Pi.π _ i = (T i).functor := by
  simp [segalMap]

/-- The Segal condition on an inner fibration `p : C^⊗ ⟶ N(Fin_*)`: for every `n` there are
coCartesian transports along the inert projections `ρ i : ⟨n⟩ ⟶ ⟨1⟩` whose Segal map
`C_⟨n⟩ ⟶ ∏_{i < n} C_⟨1⟩` is a categorical equivalence. -/
def IsSegal (p : X ⟶ nerve FinPointed.{u}) [InnerFibration p] : Prop :=
  ∀ n : FinPointed.{u},
    ∃ T : ∀ i : Fin n.len, CoCartesianTransport p (nerve.edgeMk (FinPointed.ρ i)),
    QCat.IsCategoricalEquivalence (X := ⟨fiber p n.vertex, inferInstance⟩)
      (Y := ⟨∏ᶜ fun _ : Fin n.len ↦ (fiber p (FinPointed.mk 1).vertex : SSet), inferInstance⟩)
      (ObjectProperty.homMk (segalMap T))

lemma isSegal_iff (p : X ⟶ nerve FinPointed.{u}) [InnerFibration p] :
    IsSegal p ↔ ∀ n : FinPointed.{u},
      ∃ T : ∀ i : Fin n.len, CoCartesianTransport p (nerve.edgeMk (FinPointed.ρ i)),
      QCat.IsCategoricalEquivalence (X := ⟨fiber p n.vertex, inferInstance⟩)
        (Y := ⟨∏ᶜ fun _ : Fin n.len ↦ (fiber p (FinPointed.mk 1).vertex : SSet), inferInstance⟩)
        (ObjectProperty.homMk (segalMap T)) :=
  Iff.rfl

/-- A symmetric monoidal quasicategory: a coCartesian fibration `p : C^⊗ ⟶ N(Fin_*)` satisfying
the Segal condition. Its underlying quasicategory is the fiber `C_⟨1⟩`. -/
class SymmetricMonoidal (p : X ⟶ nerve FinPointed.{u}) : Prop extends CoCartesianFibration p where
  isSegal : IsSegal p

/-- An isomorphism `p : X ⟶ N(Fin_*)` is a symmetric monoidal quasicategory: its fibers are
points, and so are their products. For instance the identity of `N(Fin_*)` is the terminal
symmetric monoidal quasicategory. -/
instance symmetricMonoidal_of_isIso (p : X ⟶ nerve FinPointed.{u}) [IsIso p] :
    SymmetricMonoidal p where
  isSegal n := by
    refine ⟨fun i ↦ .ofIsIso p _, ?_⟩
    let hX := fiber.isTerminalOfIsIso p n.vertex
    let hY : IsTerminal (∏ᶜ fun _ : Fin n.len ↦ (fiber p (FinPointed.mk 1).vertex : SSet)) :=
      IsTerminal.ofUniqueHom (fun _ ↦ Pi.lift fun _ ↦ (fiber.isTerminalOfIsIso p _).from _)
        fun _ _ ↦ Pi.hom_ext _ _ fun _ ↦ (fiber.isTerminalOfIsIso p _).hom_ext _ _
    exact @QCat.IsCategoricalEquivalence.of_isIso ⟨_, inferInstance⟩ ⟨_, inferInstance⟩ _
      ⟨ObjectProperty.homMk (hX.from _), ObjectProperty.hom_ext _ (hX.hom_ext _ _),
        ObjectProperty.hom_ext _ (hY.hom_ext _ _)⟩

/-- A simplicial set without vertices is not a symmetric monoidal quasicategory over any map to
`N(Fin_*)`: its fiber over `⟨0⟩` is empty, while the empty product is a point. -/
lemma not_symmetricMonoidal_of_not_nonempty (hX : ¬ X.Nonempty) (p : X ⟶ nerve FinPointed.{u}) :
    ¬ SymmetricMonoidal p := by
  intro h
  obtain ⟨T, hT⟩ := h.isSegal (.mk 0)
  obtain ⟨e, -⟩ := (QCat.isCategoricalEquivalence_iff_exists_equivalence _).1 hT
  let y : Δ[0] ⟶ ∏ᶜ fun _ : Fin 0 ↦ (fiber p (FinPointed.mk 1).vertex : SSet) :=
    Pi.lift fun i ↦ i.elim0
  exact hX ⟨(fiber p _).ι.app _ (e.inv.hom.app _ (yonedaEquiv y))⟩

/-! ### Symmetric monoidal functors -/

variable (p : X ⟶ nerve FinPointed.{u}) (q : Y ⟶ nerve FinPointed.{u})
  (r : Z ⟶ nerve FinPointed.{u})

/-- A symmetric monoidal functor from `p : C^⊗ ⟶ N(Fin_*)` to `q : D^⊗ ⟶ N(Fin_*)`: a map
`C^⊗ ⟶ D^⊗` over `N(Fin_*)` sending `p`-coCartesian edges to `q`-coCartesian edges. -/
@[ext]
structure SymmetricMonoidalFunctor where
  /-- The underlying map `C^⊗ ⟶ D^⊗`. -/
  hom : X ⟶ Y
  hom_comp : hom ≫ q = p
  isCoCartesian_map {x y : X _⦋0⦌} (f : Edge x y) (hf : f.IsCoCartesian p) :
    (f.map hom).IsCoCartesian q

attribute [reassoc (attr := simp)] SymmetricMonoidalFunctor.hom_comp

namespace SymmetricMonoidalFunctor

/-- The identity symmetric monoidal functor. -/
def id : SymmetricMonoidalFunctor p p where
  hom := 𝟙 X
  hom_comp := Category.id_comp p
  isCoCartesian_map f hf := hf.of_edge_eq (by simp)

@[simp]
lemma id_hom : (id p).hom = 𝟙 X :=
  (rfl)

variable {p q r}

/-- The composite of two symmetric monoidal functors. -/
def comp (F : SymmetricMonoidalFunctor p q) (G : SymmetricMonoidalFunctor q r) :
    SymmetricMonoidalFunctor p r where
  hom := F.hom ≫ G.hom
  hom_comp := by simp
  isCoCartesian_map f hf :=
    (G.isCoCartesian_map _ (F.isCoCartesian_map f hf)).of_edge_eq (by simp)

@[simp]
lemma comp_hom (F : SymmetricMonoidalFunctor p q) (G : SymmetricMonoidalFunctor q r) :
    (F.comp G).hom = F.hom ≫ G.hom :=
  (rfl)

/-- A symmetric monoidal functor is lax symmetric monoidal: it is a map of `∞`-operads. -/
def toOperadHom (F : SymmetricMonoidalFunctor p q) : InfinityOperad.Hom p q where
  hom := F.hom
  hom_comp := F.hom_comp
  isCoCartesian_map f hf _ := F.isCoCartesian_map f hf

@[simp]
lemma toOperadHom_hom (F : SymmetricMonoidalFunctor p q) : F.toOperadHom.hom = F.hom :=
  (rfl)

/-- The underlying functor `C_⟨1⟩ ⟶ D_⟨1⟩` of a symmetric monoidal functor. -/
abbrev underlying (F : SymmetricMonoidalFunctor p q) :
    (fiber p (FinPointed.mk 1).vertex : SSet) ⟶ (fiber q (FinPointed.mk 1).vertex : SSet) :=
  fiber.map F.hom F.hom_comp _

/-- The underlying functor of a composite is the composite of the underlying functors. -/
@[simp]
lemma comp_underlying (F : SymmetricMonoidalFunctor p q) (G : SymmetricMonoidalFunctor q r) :
    (F.comp G).underlying = F.underlying ≫ G.underlying :=
  fiber.map_comp _ _ _ _ _

end SymmetricMonoidalFunctor

end SSet
