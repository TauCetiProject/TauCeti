/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Pointed
public import TauCeti.Topology.Category.BasedTopPair
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Relative homotopy sets of based pairs

Let `X` be a based pair `(X, A, a₀)`, with `A ↪ X` a topological pair and `a₀ ∈ A`. This file
defines the relative homotopy set `π_{n+1}(X, A, a₀)` in the cubical model that Mathlib uses for
`HomotopyGroup`, where `n` is the cardinality of an index type `N`.

A *relative cube* is a continuous map `p : I × I^N → X` that sends the face `{0} × I^N` into
`A`, and the rest of the boundary of the cube — the opposite face `{1} × I^N` and the sides
`I × ∂I^N` — to `a₀`. This is the classical description of relative homotopy classes as maps
`(I^{n+1}, ∂I^{n+1}, J^n) → (X, A, a₀)`; see Hatcher, *Algebraic Topology*, Section 4.1, where
the face mapped to `A` is also the one where the distinguished coordinate vanishes. Two relative
cubes are homotopic when they are joined by a homotopy through relative cubes, which is Mathlib's
`ContinuousMap.HomotopicWith` for the relative-cube predicate. Unlike homotopy of generalized
loops, such a homotopy is not stationary on the face `{0} × I^N`: it may move inside `A` there.

The resulting type `TauCeti.RelHomotopyGroup N X` is pointed by the class of the constant cube.
Its group structure in dimensions at least two is not constructed here; in particular nothing
here makes `π_2(X, A, a₀)` commutative.

A morphism of based pairs acts by postcomposition, functorially, giving the functor
`TauCeti.RelHomotopyGroup.functor N : BasedTopPair ⥤ Pointed`. Restricting a relative cube to
the face `{0} × I^N` gives a generalized loop in `A` based at `a₀`, and hence the boundary map
`π_{n+1}(X, A, a₀) → π_n(A, a₀)`, which is natural in the based pair. Finally, a relative cube
that lies entirely in `A` is trivial, by pushing it towards the face `{1} × I^N` (the easy half of
the compression criterion); in particular `π_{n+1}(X, X, x₀)` is trivial.

## Main declarations

* `TauCeti.RelGenLoop N X`: relative cubes `I × I^N → X` of the based pair `X`.
* `TauCeti.RelGenLoop.mk`: the relative cube given by a continuous map satisfying the face
  conditions.
* `TauCeti.RelGenLoop.Homotopic`: homotopy through relative cubes, characterised by
  `TauCeti.RelGenLoop.homotopic_iff`.
* `TauCeti.RelHomotopyGroup N X`: the relative homotopy set `π_{n+1}(X, A, a₀)`, with
  induced maps `TauCeti.RelHomotopyGroup.map` and the functor
  `TauCeti.RelHomotopyGroup.functor`.
* `TauCeti.RelHomotopyGroup.boundary`: the boundary map
  `π_{n+1}(X, A, a₀) → π_n(A, a₀)`, natural by `TauCeti.RelHomotopyGroup.boundary_map`.
* `TauCeti.RelHomotopyGroup.mk_eq_default_of_mem_range`: a relative cube with values in `A`
  represents the distinguished class.
-/

public section

universe u v

open CategoryTheory
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

variable (N : Type v) (X : BasedTopPair.{u})

/-- The relative cubes of the based pair `X = (X, A, a₀)`: continuous maps `I × I^N → X` sending
the face `{0} × I^N` into `A`, and the face `{1} × I^N` and the sides `I × ∂I^N` to `a₀`. -/
def RelGenLoop : Set C(I × (I^N), X.pair.fst) :=
  {p | (∀ t, p (0, t) ∈ Set.range X.pair.map) ∧
    ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → p (s, t) = X.pair.map X.basepoint}

namespace RelGenLoop

variable {N X} {Y Z : BasedTopPair.{u}}

theorem mem_iff {p : C(I × (I^N), X.pair.fst)} :
    p ∈ RelGenLoop N X ↔ (∀ t, p (0, t) ∈ Set.range X.pair.map) ∧
      ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → p (s, t) = X.pair.map X.basepoint :=
  Iff.rfl

instance instFunLike : FunLike (RelGenLoop N X) (I × (I^N)) X.pair.fst where
  coe p := p.1
  coe_injective _ _ h := Subtype.ext (ContinuousMap.ext (congrFun h))

@[simp]
theorem coe_coe (p : RelGenLoop N X) : ⇑(p : C(I × (I^N), X.pair.fst)) = p :=
  rfl

@[ext]
theorem ext {p q : RelGenLoop N X} (h : ∀ y, p y = q y) : p = q :=
  DFunLike.coe_injective (funext h)

/-- The relative cube given by a continuous map `I × I^N → X` that sends the face `{0} × I^N`
into the subspace, and the face `{1} × I^N` and the sides `I × ∂I^N` to the basepoint. -/
def mk (p : C(I × (I^N), X.pair.fst)) (h₀ : ∀ t, p (0, t) ∈ Set.range X.pair.map)
    (h₁ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → p (s, t) = X.pair.map X.basepoint) :
    RelGenLoop N X :=
  ⟨p, h₀, h₁⟩

@[simp]
theorem coe_mk (p : C(I × (I^N), X.pair.fst)) (h₀ : ∀ t, p (0, t) ∈ Set.range X.pair.map)
    (h₁ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → p (s, t) = X.pair.map X.basepoint) :
    (mk p h₀ h₁ : C(I × (I^N), X.pair.fst)) = p :=
  (rfl)

@[simp]
theorem mk_apply (p : C(I × (I^N), X.pair.fst)) (h₀ : ∀ t, p (0, t) ∈ Set.range X.pair.map)
    (h₁ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → p (s, t) = X.pair.map X.basepoint)
    (y : I × (I^N)) : mk p h₀ h₁ y = p y :=
  (rfl)

/-- A relative cube sends the face `{0} × I^N` into the subspace. -/
theorem apply_zero_mem_range (p : RelGenLoop N X) (t : I^N) :
    p (0, t) ∈ Set.range X.pair.map :=
  p.2.1 t

/-- A relative cube sends the face `{1} × I^N` to the basepoint. -/
@[simp]
theorem apply_one (p : RelGenLoop N X) (t : I^N) : p (1, t) = X.pair.map X.basepoint :=
  p.2.2 1 t (Or.inl rfl)

/-- A relative cube sends the sides `I × ∂I^N` to the basepoint. -/
theorem apply_of_mem_boundary (p : RelGenLoop N X) (s : I) {t : I^N}
    (ht : t ∈ Cube.boundary N) : p (s, t) = X.pair.map X.basepoint :=
  p.2.2 s t (Or.inr ht)

/-- The constant relative cube at the basepoint. -/
def const : RelGenLoop N X :=
  ⟨ContinuousMap.const _ (X.pair.map X.basepoint), fun _ => ⟨_, rfl⟩, fun _ _ _ => rfl⟩

@[simp]
theorem const_apply (y : I × (I^N)) : (const : RelGenLoop N X) y = X.pair.map X.basepoint :=
  (rfl)

instance : Inhabited (RelGenLoop N X) :=
  ⟨const⟩

/-! ### Homotopy through relative cubes -/

/-- Two relative cubes are homotopic if they are joined by a homotopy all of whose stages are
relative cubes. On the face `{0} × I^N` the homotopy may move inside the subspace. -/
def Homotopic (p q : RelGenLoop N X) : Prop :=
  ContinuousMap.HomotopicWith (p : C(I × (I^N), X.pair.fst)) q (· ∈ RelGenLoop N X)

/-- The characteristic property of `Homotopic`: a homotopy through relative cubes is a homotopy
of the underlying continuous maps all of whose stages are relative cubes. -/
theorem homotopic_iff {p q : RelGenLoop N X} :
    Homotopic p q ↔
      ContinuousMap.HomotopicWith (p : C(I × (I^N), X.pair.fst)) q (· ∈ RelGenLoop N X) :=
  Iff.rfl

namespace Homotopic

@[refl]
theorem refl (p : RelGenLoop N X) : Homotopic p p :=
  ContinuousMap.HomotopicWith.refl _ p.2

@[symm]
theorem symm ⦃p q : RelGenLoop N X⦄ (h : Homotopic p q) : Homotopic q p :=
  ContinuousMap.HomotopicWith.symm h

@[trans]
theorem trans ⦃p q r : RelGenLoop N X⦄ (h₀ : Homotopic p q) (h₁ : Homotopic q r) :
    Homotopic p r :=
  ContinuousMap.HomotopicWith.trans h₀ h₁

theorem equiv : Equivalence (@Homotopic N X) :=
  ⟨refl, (symm ·), (trans · ·)⟩

end Homotopic

/-- Homotopy through relative cubes, as a setoid. -/
instance setoid (N : Type v) (X : BasedTopPair.{u}) : Setoid (RelGenLoop N X) :=
  ⟨Homotopic, Homotopic.equiv⟩

/-! ### Functoriality -/

/-- Postcomposing with the ambient component of a morphism of based pairs preserves relative
cubes. -/
theorem comp_mem (f : X ⟶ Y) {p : C(I × (I^N), X.pair.fst)} (hp : p ∈ RelGenLoop N X) :
    (TopPair.Hom.fst f.toTopPairHom).hom.comp p ∈ RelGenLoop N Y := by
  refine ⟨fun t => ?_, fun s t h => ?_⟩
  · obtain ⟨a, ha⟩ := hp.1 t
    exact ⟨TopPair.Hom.snd f.toTopPairHom a, by
      rw [ContinuousMap.comp_apply, ← ha, TopPair.Hom.w_apply]⟩
  · rw [ContinuousMap.comp_apply, hp.2 s t h]
    exact BasedTopPair.Hom.fst_map_basepoint f

/-- A morphism of based pairs sends relative cubes to relative cubes by postcomposition. -/
def map (f : X ⟶ Y) (p : RelGenLoop N X) : RelGenLoop N Y :=
  ⟨(TopPair.Hom.fst f.toTopPairHom).hom.comp p, comp_mem f p.2⟩

@[simp]
theorem map_apply (f : X ⟶ Y) (p : RelGenLoop N X) (y : I × (I^N)) :
    map f p y = TopPair.Hom.fst f.toTopPairHom (p y) :=
  (rfl)

@[simp]
theorem map_id (p : RelGenLoop N X) : map (𝟙 X) p = p := by
  ext y
  simp only [map_apply, TopPair.Hom.fst, BasedTopPair.id_toTopPairHom,
    MorphismProperty.Comma.id_hom, Comma.id_right, TopCat.hom_id, ContinuousMap.id_apply]

@[simp]
theorem map_map (f : X ⟶ Y) (g : Y ⟶ Z) (p : RelGenLoop N X) :
    map g (map f p) = map (f ≫ g) p := by
  ext y
  simp only [map_apply, TopPair.Hom.fst, BasedTopPair.comp_toTopPairHom,
    MorphismProperty.Comma.comp_hom, Comma.comp_right, TopCat.hom_comp, ContinuousMap.comp_apply]

@[simp]
theorem map_const (f : X ⟶ Y) : map f (const : RelGenLoop N X) = const := by
  ext _
  exact BasedTopPair.Hom.fst_map_basepoint f

/-- Postcomposition preserves homotopy through relative cubes. -/
theorem Homotopic.map {p q : RelGenLoop N X} (h : Homotopic p q) (f : X ⟶ Y) :
    Homotopic (RelGenLoop.map f p) (RelGenLoop.map f q) :=
  Nonempty.map (fun F =>
    { toHomotopy :=
        (ContinuousMap.Homotopy.refl (TopPair.Hom.fst f.toTopPairHom).hom).comp F.toHomotopy
      -- Each stage of the composite homotopy is, by definition of `Homotopy.comp`, the
      -- postcomposition of the corresponding stage of `F`.
      prop' r := (RelGenLoop.map f ⟨_, F.prop r⟩).2 }) h

/-! ### The face in the subspace -/

/-- The restriction of a relative cube to the face `{0} × I^N`, as a generalized loop in the
subspace based at the basepoint. -/
noncomputable def boundary (p : RelGenLoop N X) : Ω^ N X.pair.snd X.basepoint :=
  ⟨X.pair.liftSnd ⟨fun t => p (0, t),
      (map_continuous (p : C(I × (I^N), X.pair.fst))).comp (Continuous.prodMk_right 0)⟩
      (apply_zero_mem_range p),
    fun t ht => by
      rw [TopPair.liftSnd_apply_eq_iff]
      exact apply_of_mem_boundary p 0 ht⟩

@[simp]
theorem map_boundary_apply (p : RelGenLoop N X) (t : I^N) :
    X.pair.map (boundary p t) = p (0, t) :=
  TopPair.map_liftSnd _ _ t

theorem boundary_apply_eq_iff (p : RelGenLoop N X) (t : I^N) (a : X.pair.snd) :
    boundary p t = a ↔ p (0, t) = X.pair.map a := by
  rw [← X.pair.isEmbedding_map.injective.eq_iff, map_boundary_apply]

@[simp]
theorem boundary_const : boundary (const : RelGenLoop N X) = GenLoop.const := by
  ext t
  rw [boundary_apply_eq_iff, const_apply, GenLoop.const_apply]

/-- Restricting to the face `{0} × I^N` commutes with the action of morphisms of based pairs. -/
theorem boundary_map (f : X ⟶ Y) (p : RelGenLoop N X) :
    boundary (map f p) =
      GenLoop.map (TopPair.Hom.snd f.toTopPairHom).hom f.map_basepoint (boundary p) := by
  ext t
  rw [boundary_apply_eq_iff, GenLoop.map_apply, map_apply, ← map_boundary_apply p t,
    TopPair.Hom.w_apply]

/-- A homotopy through relative cubes restricts on the face `{0} × I^N` to a homotopy of
generalized loops in the subspace, relative to the cube boundary. -/
theorem Homotopic.boundary {p q : RelGenLoop N X} (h : Homotopic p q) :
    GenLoop.Homotopic (boundary p) (boundary q) :=
  Nonempty.map (fun F =>
    { toContinuousMap := X.pair.liftSnd
        ⟨fun y => F (y.1, (0, y.2)),
          F.continuous.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩
        fun y => by simpa using (mem_iff.1 (F.prop y.1)).1 y.2
      map_zero_left t := by
        rw [ContinuousMap.toFun_eq_coe, TopPair.liftSnd_apply_eq_iff, GenLoop.coe_coe,
          map_boundary_apply, ContinuousMap.coe_mk]
        exact F.apply_zero (0, t)
      map_one_left t := by
        rw [ContinuousMap.toFun_eq_coe, TopPair.liftSnd_apply_eq_iff, GenLoop.coe_coe,
          map_boundary_apply, ContinuousMap.coe_mk]
        exact F.apply_one (0, t)
      prop' r t ht := by
        apply X.pair.isEmbedding_map.injective
        have h := (mem_iff.1 (F.prop r)).2 0 t (Or.inr ht)
        simp only [ContinuousMap.Homotopy.curry_apply,
          ContinuousMap.HomotopyWith.coe_toHomotopy] at h
        simp [apply_of_mem_boundary p 0 ht, h] }) h

/-- A relative cube with all of its values in the subspace is homotopic, through relative cubes,
to the constant cube: push it towards the face `{1} × I^N`. -/
theorem homotopic_const_of_mem_range (p : RelGenLoop N X)
    (hp : ∀ y, p y ∈ Set.range X.pair.map) : Homotopic p const :=
  ⟨{ toFun y := p (max y.2.1 y.1, y.2.2)
     continuous_toFun := (map_continuous (p : C(I × (I^N), X.pair.fst))).comp (by fun_prop)
     map_zero_left y := by simp
     map_one_left y := by simp [max_eq_right unitInterval.le_one']
     prop' r := by
       refine ⟨fun t => hp _, fun s t h => ?_⟩
       rcases h with rfl | ht
       · simp [max_eq_left unitInterval.le_one']
       · exact apply_of_mem_boundary p _ ht }⟩

end RelGenLoop

/-- The relative homotopy set `π_{n+1}(X, A, a₀)` of a based pair `X = (X, A, a₀)`, where `n` is
the cardinality of `N`: relative cubes `I × I^N → X` up to homotopy through relative cubes. -/
def RelHomotopyGroup (N : Type v) (X : BasedTopPair.{u}) : Type (max u v) :=
  Quotient (RelGenLoop.setoid N X)

namespace RelHomotopyGroup

variable {N X} {Y Z : BasedTopPair.{u}}

/-- The class of a relative cube. -/
def mk (p : RelGenLoop N X) : RelHomotopyGroup N X :=
  Quotient.mk _ p

theorem mk_surjective : Function.Surjective (mk : RelGenLoop N X → RelHomotopyGroup N X) :=
  Quotient.mk_surjective

theorem mk_eq_mk {p q : RelGenLoop N X} : mk p = mk q ↔ RelGenLoop.Homotopic p q :=
  Quotient.eq

/-- Lift a function on relative cubes that is invariant under homotopy through relative cubes to
the relative homotopy set. -/
def lift {β : Sort*} (f : RelGenLoop N X → β)
    (hf : ∀ p q, RelGenLoop.Homotopic p q → f p = f q) : RelHomotopyGroup N X → β :=
  Quotient.lift f hf

@[simp]
theorem lift_mk {β : Sort*} (f : RelGenLoop N X → β)
    (hf : ∀ p q, RelGenLoop.Homotopic p q → f p = f q) (p : RelGenLoop N X) :
    lift f hf (mk p) = f p :=
  (rfl)

/-- Lift a function of two relative cubes that is invariant under homotopy through relative cubes
in each argument to a function of two relative homotopy classes. -/
def lift₂ {N' : Type*} {X' : BasedTopPair.{u}} {β : Sort*}
    (f : RelGenLoop N X → RelGenLoop N' X' → β)
    (hf : ∀ p₁ q₁ p₂ q₂, RelGenLoop.Homotopic p₁ p₂ → RelGenLoop.Homotopic q₁ q₂ →
      f p₁ q₁ = f p₂ q₂) :
    RelHomotopyGroup N X → RelHomotopyGroup N' X' → β :=
  Quotient.lift₂ f hf

@[simp]
theorem lift₂_mk {N' : Type*} {X' : BasedTopPair.{u}} {β : Sort*}
    (f : RelGenLoop N X → RelGenLoop N' X' → β)
    (hf : ∀ p₁ q₁ p₂ q₂, RelGenLoop.Homotopic p₁ p₂ → RelGenLoop.Homotopic q₁ q₂ →
      f p₁ q₁ = f p₂ q₂) (p : RelGenLoop N X) (q : RelGenLoop N' X') :
    lift₂ f hf (mk p) (mk q) = f p q :=
  (rfl)

/-- The relative homotopy set is pointed by the class of the constant cube. -/
instance : Inhabited (RelHomotopyGroup N X) :=
  ⟨mk RelGenLoop.const⟩

theorem default_eq : (default : RelHomotopyGroup N X) = mk RelGenLoop.const :=
  (rfl)

/-- The map on relative homotopy sets induced by a morphism of based pairs. -/
def map (f : X ⟶ Y) : RelHomotopyGroup N X → RelHomotopyGroup N Y :=
  Quotient.map (RelGenLoop.map f) fun _ _ h => h.map f

@[simp]
theorem map_mk (f : X ⟶ Y) (p : RelGenLoop N X) : map f (mk p) = mk (RelGenLoop.map f p) :=
  (rfl)

@[simp]
theorem map_id : map (𝟙 X) = (id : RelHomotopyGroup N X → RelHomotopyGroup N X) := by
  funext a
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [map_mk, RelGenLoop.map_id, id_eq]

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map g ∘ map f : RelHomotopyGroup N X → RelHomotopyGroup N Z) := by
  funext a
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [Function.comp_apply, map_mk, map_mk, map_mk, RelGenLoop.map_map]

@[simp]
theorem map_map (f : X ⟶ Y) (g : Y ⟶ Z) (a : RelHomotopyGroup N X) :
    map g (map f a) = map (f ≫ g) a := by
  rw [map_comp, Function.comp_apply]

@[simp]
theorem map_default (f : X ⟶ Y) : map f (default : RelHomotopyGroup N X) = default := by
  rw [default_eq, map_mk, RelGenLoop.map_const, default_eq]

/-- Relative homotopy sets as a functor from based pairs to pointed types. -/
@[expose, simps obj map_toFun]
def functor (N : Type v) : BasedTopPair.{u} ⥤ Pointed.{max u v} where
  obj X := ⟨RelHomotopyGroup N X, default⟩
  map f := ⟨map f, map_default f⟩
  map_id X := Pointed.Hom.ext (map_id (X := X))
  map_comp f g := Pointed.Hom.ext (map_comp f g)

/-- The boundary map `π_{n+1}(X, A, a₀) → π_n(A, a₀)`, restricting a relative cube to the face
that lies in the subspace. -/
noncomputable def boundary : RelHomotopyGroup N X → HomotopyGroup N X.pair.snd X.basepoint :=
  Quotient.map RelGenLoop.boundary fun _ _ h => h.boundary

@[simp]
theorem boundary_mk (p : RelGenLoop N X) :
    boundary (mk p) = (⟦RelGenLoop.boundary p⟧ : HomotopyGroup N X.pair.snd X.basepoint) :=
  (rfl)

@[simp]
theorem boundary_default :
    boundary (default : RelHomotopyGroup N X) =
      (⟦GenLoop.const⟧ : HomotopyGroup N X.pair.snd X.basepoint) := by
  rw [default_eq, boundary_mk, RelGenLoop.boundary_const]

/-- The boundary map is natural in the based pair. -/
theorem boundary_map (f : X ⟶ Y) (a : RelHomotopyGroup N X) :
    boundary (map f a) =
      HomotopyGroup.map (TopPair.Hom.snd f.toTopPairHom).hom f.map_basepoint (boundary a) := by
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [map_mk, boundary_mk, boundary_mk, HomotopyGroup.map_mk, RelGenLoop.boundary_map]

/-- A relative cube with all of its values in the subspace represents the distinguished class. -/
theorem mk_eq_default_of_mem_range (p : RelGenLoop N X)
    (hp : ∀ y, p y ∈ Set.range X.pair.map) : mk p = default :=
  mk_eq_mk.2 (RelGenLoop.homotopic_const_of_mem_range p hp)

/-- If the subspace is all of the space, every relative homotopy class is trivial. -/
theorem subsingleton_of_surjective (h : Function.Surjective X.pair.map) :
    Subsingleton (RelHomotopyGroup N X) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨p, rfl⟩ := mk_surjective a
  obtain ⟨q, rfl⟩ := mk_surjective b
  rw [mk_eq_default_of_mem_range p fun y => h _, mk_eq_default_of_mem_range q fun y => h _]

end RelHomotopyGroup

end TauCeti
