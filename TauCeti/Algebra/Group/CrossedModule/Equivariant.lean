/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.CrossedModule.Basic

/-!
# Group actions on crossed modules

A monoid `G` acting on groups `T` and `H` by group endomorphisms (`MulDistribMulAction`; by
automorphisms when `G` is a group) acts **compatibly** on a crossed module `∂ : T → H` when `∂`
is `G`-equivariant and the action of `H` on `T` is `G`-equivariant:

`∂ (g • x) = g • ∂ x` and `g • (h • x) = (g • h) • (g • x)`.

This is the setting of Galois cohomology with coefficients in a crossed module, where `G` is a
Galois group acting on the points of a crossed module of algebraic groups, such as the map
`G_sc → G` from the simply connected cover of the derived group of a connected reductive group.
The cohomology itself is in
`TauCeti/RepresentationTheory/Homological/ContCohomology/Nonabelian/CrossedModule/H0.lean`.

## Main definitions

* `TauCeti.CrossedModule.IsEquivariant G M`: the actions of `G` on `T` and `H` are compatible with
  the crossed module `M`.

## References

* M. Borovoi, *Abelian Galois cohomology of reductive groups*, Mem. Amer. Math. Soc. 626 (1998),
  §3.
* J.-P. Labesse, *Cohomologie, stabilisation et changement de base*, Astérisque 257 (1999),
  §1.1–1.2.
-/

public section

namespace TauCeti

namespace CrossedModule

variable {T H : Type*} [Group T] [Group H]

/-- The actions of `G` on `T` and on `H` by group endomorphisms are **compatible** with the crossed
module `M : T → H`: the boundary is `G`-equivariant, and so is the action of `H` on `T`. -/
class IsEquivariant (G : Type*) [Monoid G] [MulDistribMulAction G T] [MulDistribMulAction G H]
    (M : CrossedModule T H) : Prop where
  /-- The boundary `∂ : T → H` is `G`-equivariant. -/
  boundary_smul (g : G) (x : T) : M.boundary (g • x) = g • M.boundary x
  /-- The action of `H` on `T` is `G`-equivariant. -/
  smul_act (g : G) (h : H) (x : T) : g • M.act h x = M.act (g • h) (g • x)

attribute [simp] IsEquivariant.boundary_smul IsEquivariant.smul_act

variable {G : Type*} [Monoid G] [MulDistribMulAction G T] [MulDistribMulAction G H]
  (M : CrossedModule T H)

/-- Every action is compatible with a crossed module whose source is trivial. -/
instance isEquivariant_of_subsingleton_left [Subsingleton T] : M.IsEquivariant G where
  boundary_smul g x := by rw [Subsingleton.elim x 1, smul_one, map_one, smul_one]
  smul_act _ _ _ := Subsingleton.elim _ _

/-- Every action is compatible with a crossed module whose target is trivial. -/
instance isEquivariant_of_subsingleton_right [Subsingleton H] : M.IsEquivariant G where
  boundary_smul _ _ := Subsingleton.elim _ _
  smul_act g h x := by
    rw [Subsingleton.elim (g • h) 1, Subsingleton.elim h 1]
    simp

end CrossedModule

end TauCeti
