/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.GenLoop.Map

/-!
# Functoriality of homotopy groups

Mathlib defines the quotient `HomotopyGroup N X x` of the generalized loop space, and this file
supplies the map induced by a based continuous map (postcomposition of generalized loops, in
`TauCeti.Topology.Homotopy.GenLoop.Map`) on homotopy classes: it respects identity and composition,
handles constant maps and subsingleton targets, and is a monoid homomorphism in positive
dimensions. In dimension one it is Mathlib's induced map `FundamentalGroup.mapOfEq` of fundamental
groups, read through `HomotopyGroup.pi1EquivFundamentalGroup`, so in particular one is bijective
exactly when the other is. Every homotopy group of a subsingleton space is itself a subsingleton
(`HomotopyGroup.subsingleton_of_subsingleton`).

The covering-map isomorphisms on `π_n` for `n ≥ 2`
(`TauCeti.Topology.Homotopy.HomotopyGroup.Covering`) are stated with it.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace HomotopyGroup

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- In positive dimensions, the class of the constant generalized loop is the identity element.
This is `HomotopyGroup.one_def` oriented towards `1`, so that `1` is the simp normal form for
the constant-map results below. -/
@[simp]
theorem mk_const_eq_one [DecidableEq N] [Nonempty N] :
    (⟦(_root_.GenLoop.const : Ω^ N X x)⟧ : HomotopyGroup N X x) = (1 : HomotopyGroup N X x) :=
  _root_.HomotopyGroup.one_def.symm

/-- The map on homotopy classes induced by a based continuous map. -/
@[expose] def map (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (GenLoop.map f hf) fun _ _ h => GenLoop.map_homotopic h f hf

@[simp]
theorem map_mk (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) :
    map f hf (⟦p⟧ : HomotopyGroup N X x) = ⟦GenLoop.map f hf p⟧ :=
  rfl

/-- A constant continuous map sends every homotopy class to the class of the constant
generalized loop. This statement also covers dimension zero, where the target need not carry
the positive-dimensional group structure. -/
@[simp]
theorem map_continuousMap_const_apply (y : Y) (hy : (ContinuousMap.const X y) x = y)
    (a : HomotopyGroup N X x) :
    map (x := x) (ContinuousMap.const X y) hy a =
      (⟦(_root_.GenLoop.const : Ω^ N Y y)⟧ : HomotopyGroup N Y y) := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [map_mk]
  exact congrArg _ (GenLoop.map_continuousMap_const y p)

/-- Every homotopy group of a subsingleton space is a subsingleton: any two generalized loops
in it are equal. This includes dimension zero. -/
instance subsingleton_of_subsingleton [Subsingleton X] : Subsingleton (HomotopyGroup N X x) :=
  ⟨fun a b ↦ Quotient.inductionOn₂ a b fun f g ↦
    congrArg _ (_root_.GenLoop.ext f g fun _ ↦ Subsingleton.elim _ _)⟩

/-- A based map into a subsingleton space induces the same map as the constant map at the
target basepoint. -/
theorem map_eq_continuousMap_const_of_subsingleton [Subsingleton Y] (f : C(X, Y)) (hf : f x = y) :
    map (N := N) f hf = map (x := x) (ContinuousMap.const X y) rfl := by
  have h : f = ContinuousMap.const X y := Subsingleton.elim _ _
  subst f
  rfl

/-- A based map into a subsingleton space sends every homotopy class to the class of the
constant generalized loop. -/
@[simp]
theorem map_apply_of_subsingleton [Subsingleton Y] (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    map (N := N) f hf a =
      (⟦(_root_.GenLoop.const : Ω^ N Y y)⟧ : HomotopyGroup N Y y) := by
  rw [map_eq_continuousMap_const_of_subsingleton]
  exact map_continuousMap_const_apply y _ a

/-- In positive dimensions, a constant continuous map sends every homotopy class to the
identity.

This is not a `simp` lemma: the positive-dimensional normal form is already reached by
`map_continuousMap_const_apply` followed by `mk_const_eq_one`, so a separate `⟦const⟧`-keyed
`= 1` rule would be redundant. It is kept as an explicit rewrite. -/
theorem map_continuousMap_const_apply_eq_one [DecidableEq N] [Nonempty N]
    (y : Y) (hy : (ContinuousMap.const X y) x = y) (a : HomotopyGroup N X x) :
    map (x := x) (ContinuousMap.const X y) hy a = 1 :=
  (map_continuousMap_const_apply y hy a).trans _root_.HomotopyGroup.one_def.symm

/-- In positive dimensions, a based map into a subsingleton space sends every homotopy class
to the identity.

This is not a `simp` lemma: the positive-dimensional normal form is already reached by
`map_apply_of_subsingleton` followed by `mk_const_eq_one`, so a separate composite `= 1` rule
would be redundant. It is kept as an explicit rewrite. -/
theorem map_apply_eq_one_of_subsingleton [DecidableEq N] [Nonempty N] [Subsingleton Y]
    (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup N X x) :
    map (N := N) f hf a = 1 :=
  (map_apply_of_subsingleton f hf a).trans _root_.HomotopyGroup.one_def.symm

/-- Identity law: the map induced by the identity continuous map is the identity on homotopy
classes. -/
@[simp]
theorem map_id_apply (a : HomotopyGroup N X x) :
    map (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [map_mk, GenLoop.map_id]
    rfl

/-- Composition law: the map induced by a composite continuous map is the composite of the
induced maps on homotopy classes. -/
@[simp]
theorem map_comp_apply (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = map (g.comp f) (by simp [hf, hg]) a := by
  refine Quotient.inductionOn a ?_
  intro p
  simp
  -- both sides are now `⟦GenLoop.map (g.comp f) _ p⟧` and differ only in the basepoint proof
  -- carried by `GenLoop.map`, which is proof-irrelevant.
  rfl

/-- Composition law, as an equality of functions: the composite of the maps induced on homotopy
classes is the map induced by the composite continuous map. -/
@[simp]
theorem map_comp_map (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y) :
    map (N := N) g hg ∘ map f hf = map (g.comp f) (by simp [hf, hg]) :=
  funext (map_comp_apply g hg f hf)

/-- The induced map `HomotopyGroup.map` depends only on the underlying continuous map, not on the
chosen proof of the basepoint equation. -/
theorem map_congr {f₁ f₂ : C(X, Y)} (hfe : f₁ = f₂) (h₁ : f₁ x = y) (h₂ : f₂ x = y)
    (a : HomotopyGroup N X x) :
    map f₁ h₁ a = map f₂ h₂ a := by
  subst hfe
  rfl

/-- Composition law for a commuting triangle: if `g ∘ f = h`, then the composite of the maps
induced by `f` and `g` on homotopy classes is the map induced by `h`. -/
theorem map_comp_map_of_comp_eq {g : C(Y, Z)} {f : C(X, Y)} {h : C(X, Z)} (hgf : g.comp f = h)
    (hg : g y = z) (hf : f x = y) (hh : h x = z) :
    map (N := N) g hg ∘ map f hf = map h hh := by
  subst hgf
  exact map_comp_map g hg f hf

/-- If `g ∘ f` is the identity, then the induced map of `g` undoes the induced map of `f` on
homotopy classes. -/
theorem map_map_of_comp_eq_id (g : C(Y, X)) (f : C(X, Y)) (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X) (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = a := by
  rw [map_comp_apply]
  exact (map_congr hgf _ rfl a).trans (map_id_apply a)

/-- In positive dimensions, the map induced by a based continuous map is a monoid
homomorphism for the standard group structure on homotopy groups. -/
@[expose] def mapHom [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    rw [_root_.HomotopyGroup.one_def, map_mk, GenLoop.map_const]
    exact _root_.HomotopyGroup.one_def.symm
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    simp [_root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N)]
    -- as in `map_comp_apply`, the two sides differ only in the proof-irrelevant basepoint
    -- argument of `GenLoop.map`.
    rfl

@[simp]
theorem mapHom_apply [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    mapHom f hf a = map f hf a :=
  rfl

/-- In positive dimensions, a constant continuous map induces the trivial homomorphism on
homotopy groups.

This is not a `simp` lemma: baking the basepoint proof `rfl` into the statement forces the
target basepoint to be `(ContinuousMap.const X y) x` rather than `y`, so `simp` cannot close
even its own statement. Use it as an explicit rewrite. -/
theorem mapHom_continuousMap_const_eq_one [DecidableEq N] [Nonempty N] (y : Y) :
    mapHom (N := N) (x := x) (ContinuousMap.const X y) rfl = 1 := by
  ext a
  exact map_continuousMap_const_apply_eq_one (x := x) y rfl a

/-- A based map into a subsingleton space induces the trivial homomorphism on every
positive-dimensional homotopy group. -/
@[simp]
theorem mapHom_eq_one_of_subsingleton [DecidableEq N] [Nonempty N] [Subsingleton Y]
    (f : C(X, Y)) (hf : f x = y) : mapHom (N := N) f hf = 1 := by
  ext a
  exact map_apply_eq_one_of_subsingleton f hf a

/-- Identity law for the bundled homomorphism: the induced monoid homomorphism of the identity
continuous map is the identity homomorphism. -/
@[simp]
theorem mapHom_id [DecidableEq N] [Nonempty N] :
    mapHom (ContinuousMap.id X) rfl = MonoidHom.id (HomotopyGroup N X x) :=
  MonoidHom.ext fun a => map_id_apply a

/-- Composition law for the bundled homomorphism: the induced monoid homomorphism of a composite
continuous map is the composite of the induced homomorphisms. -/
@[simp]
theorem mapHom_comp [DecidableEq N] [Nonempty N] (g : C(Y, Z)) (hg : g y = z)
    (f : C(X, Y)) (hf : f x = y) :
    (mapHom g hg).comp (mapHom f hf) = mapHom (N := N) (g.comp f) (by simp [hf, hg]) :=
  MonoidHom.ext fun a => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, mapHom_apply, map_comp_apply]

@[simp]
theorem map_mul [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y)
    (a b : HomotopyGroup N X x) :
    map f hf (a * b) = map f hf a * map f hf b :=
  (mapHom f hf).map_mul a b

@[simp]
theorem map_one [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y) :
    map f hf (1 : HomotopyGroup N X x) = 1 :=
  (mapHom f hf).map_one

/-- In dimension one, the induced map on homotopy groups is the induced map on fundamental groups,
under Mathlib's identification `pi1EquivFundamentalGroup` of `π_1` with the fundamental group. -/
@[simp]
theorem pi1EquivFundamentalGroup_map (f : C(X, Y)) (hf : f x = y) (a : π_ 1 X x) :
    pi1EquivFundamentalGroup (map f hf a) =
      FundamentalGroup.mapOfEq f hf (pi1EquivFundamentalGroup a) := by
  induction a using Quotient.inductionOn with
  | h p =>
  rw [FundamentalGroup.mapOfEq_apply]
  -- Both sides are classes of the loop `t ↦ f (p t)`.
  refine congrArg FundamentalGroup.fromPath
    (congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun t => ?_)))
  simp [genLoopEquivOfUnique, GenLoop.map_apply]

/-- In dimension one, a map induces a bijection on homotopy groups exactly when it induces a
bijection of fundamental groups. -/
theorem bijective_map_iff_bijective_mapOfEq (f : C(X, Y)) (hf : f x = y) :
    Function.Bijective (map (N := Fin 1) f hf) ↔
      Function.Bijective (FundamentalGroup.mapOfEq f hf) := by
  have h : ⇑(FundamentalGroup.mapOfEq f hf) =
      pi1EquivFundamentalGroup ∘ map f hf ∘ pi1EquivFundamentalGroup.symm := by
    funext γ
    simp
  rw [h, Function.Bijective.of_comp_iff' (Equiv.bijective _),
    Function.Bijective.of_comp_iff _ (Equiv.bijective _)]

end HomotopyGroup
