/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
import TauCeti.LinearAlgebra.Trace.Pi

/-!
# The representation carried by a `k[G]`-module

Mathlib's `Representation.ofModule' M` reads a `k[G]`-module `M` whose `k`-module structure is
already the restriction of its `k[G]`-module structure as a representation of `G` on `M` itself,
rather than on a type synonym.  That is the convenient form -- a left ideal, say, stays a left
ideal -- but nothing is recorded about it, so the general theory of representations, which runs
on the type synonym `ρ.asModule`, cannot be applied to it.

This file records what is needed to pass between the two.  The algebra map of `ofModule' M` is
the given action (`TauCeti.Representation.asAlgebraHom_ofModule'`), so `(ofModule' M).asModule` is
`M` again, with the same `k[G]`-action
(`TauCeti.Representation.ofModule'AsModuleEquiv`).  Consequently `ofModule' M` is irreducible
exactly when `M` is a simple `k[G]`-module
(`TauCeti.Representation.isIrreducible_ofModule'_iff`), which is how a module built by hand -- a
left ideal, for instance -- is recognised as an irreducible representation.  That last statement
is stated here, beside the comparison of modules it is read off from, rather than among the
self-contained criteria of `TauCeti.RepresentationTheory.Irreducible`, which say nothing about
where the representation came from.

Characters are read off in the same spirit: the character of `ofModule'` of a finite product of
`k[G]`-modules is the sum of the characters of the factors
(`TauCeti.Representation.char_ofModule'_pi`), and a factor `ρ.asModule` contributes the character
of `ρ` itself (`Representation.char_ofModule'_asModule`).  Together they compute the
character of a direct sum of representations assembled as a `k[G]`-module.

## Main results

* `TauCeti.Representation.ofModule'_apply`: a group element acts by the corresponding
  group-algebra basis element.
* `TauCeti.Representation.asAlgebraHom_ofModule'`: the algebra map of `ofModule' M` is the action
  of `k[G]` on `M`.
* `TauCeti.Representation.ofModule'AsModuleEquiv`: `(ofModule' M).asModule` is `M` as a
  `k[G]`-module.
* `TauCeti.Representation.isIrreducible_ofModule'_iff`: `ofModule' M` is irreducible exactly when
  `M` is simple.
* `TauCeti.Representation.char_ofModule'_pi`: the character of `ofModule'` of a finite product is
  the sum of the characters of the factors.
* `Representation.char_ofModule'_asModule`: the character of `ofModule' ρ.asModule` is the
  character of `ρ`.
-/

public section

namespace TauCeti

namespace Representation

open scoped MonoidAlgebra

section Semiring

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable (M : Type*) [AddCommMonoid M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]

/-- A group element acts on `Representation.ofModule' M` through the corresponding group-algebra
basis element. -/
@[simp]
theorem ofModule'_apply (g : G) (x : M) :
    _root_.Representation.ofModule' (k := k) (G := G) M g x = MonoidAlgebra.single g (1 : k) • x :=
  rfl

/-- The algebra map of `Representation.ofModule' M` is the action of `k[G]` on `M` that it was
built from. -/
-- Both are the `k[G]`-linear extension of the same map on group elements, and `MonoidAlgebra.lift`
-- says that extension is unique.
theorem asAlgebraHom_ofModule' :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asAlgebraHom = Algebra.lsmul k k M := by
  rw [_root_.Representation.asAlgebraHom_def, _root_.Representation.ofModule']
  exact (MonoidAlgebra.lift k (Module.End k M) G).apply_symm_apply _

@[simp]
theorem asAlgebraHom_ofModule'_apply (r : k[G]) (x : M) :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r x = r • x := by
  rw [asAlgebraHom_ofModule']
  rfl

/-- **The `k[G]`-module underlying `Representation.ofModule' M` is `M` itself.**  The map is the
identity; the content is that the two `k[G]`-actions agree. -/
noncomputable def ofModule'AsModuleEquiv :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asModule ≃ₗ[k[G]] M where
  toFun := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv
  invFun := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.symm
  map_add' := map_add _
  map_smul' r x := by
    rw [RingHom.id_apply, _root_.Representation.asModuleEquiv_map_smul,
      asAlgebraHom_ofModule'_apply]
  left_inv := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.left_inv
  right_inv := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.right_inv

/-- `TauCeti.Representation.ofModule'AsModuleEquiv` is the identity map: its two sides are the
same type, and all it records is that their `k[G]`-actions agree. -/
-- The proof is written `(rfl)` rather than `rfl`: the parenthesised form suppresses the automatic
-- `@[defeq]` tag, which an exported theorem may carry only if the definitions it unfolds are
-- exposed, and there is no reason to expose the body of the equivalence.
@[simp]
theorem ofModule'AsModuleEquiv_apply
    (x : (_root_.Representation.ofModule' (k := k) (G := G) M).asModule) :
    ofModule'AsModuleEquiv M x = x :=
  (rfl)

end Semiring

section Field

variable {k G : Type*} [Field k] [Monoid G]
variable (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]

/-- **`Representation.ofModule' M` is irreducible exactly when `M` is a simple `k[G]`-module.**
This is the form of `Representation.irreducible_iff_isSimpleModule_asModule` that applies to a
module given in advance, with no type synonym in the way. -/
theorem isIrreducible_ofModule'_iff :
    (_root_.Representation.ofModule' (k := k) (G := G) M).IsIrreducible ↔
      IsSimpleModule k[G] M := by
  rw [_root_.Representation.irreducible_iff_isSimpleModule_asModule]
  exact (ofModule'AsModuleEquiv M).isSimpleModule_iff

end Field

section Character

variable {k G : Type*} [Field k] [Monoid G]

/-- **The character of `Representation.ofModule'` of a finite product of `k[G]`-modules is the
sum of the characters of the factors.**  This is the finite-product counterpart of
`Representation.char_prod`, for representations read off a `k[G]`-module; a factor of
the form `ρ.asModule` is then evaluated by `Representation.char_ofModule'_asModule`. -/
-- A group element acts on the product coordinatewise: `(MonoidAlgebra.single g 1 • x) i` is
-- `MonoidAlgebra.single g 1 • x i`, by `ofModule'_apply` and `Pi.smul_apply`, both of which hold
-- by `rfl`.  Rewriting with them instead of `rfl` is measurably slower, so `rfl` is kept.
@[simp]
theorem char_ofModule'_pi {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] [∀ i, Module k[G] (M i)] [∀ i, IsScalarTower k k[G] (M i)]
    [∀ i, FiniteDimensional k (M i)] (g : G) :
    (_root_.Representation.ofModule' (k := k) (G := G) ((i : ι) → M i)).character g =
      ∑ i, (_root_.Representation.ofModule' (k := k) (G := G) (M i)).character g :=
  LinearMap.trace_pi_of_apply_eq_dependent _ _ fun _ _ => rfl

/-- **The character of `Representation.ofModule' ρ.asModule` is the character of `ρ`.**  This
lets a character computed on a `k[G]`-module assembled from `asModule` summands be expressed
through the original representations. -/
-- `ρ.asModuleEquiv` conjugates the action on `ρ.asModule` into `ρ g`, and the trace is invariant
-- under conjugation.  The conjugation identity is proved pointwise with explicit rewrites rather
-- than `simp`, which would leave a goal closed only by identifying `ρ.asModule` with `V`.
@[simp]
theorem _root_.Representation.char_ofModule'_asModule {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : _root_.Representation k G V) (g : G) :
    (_root_.Representation.ofModule' (k := k) (G := G) ρ.asModule).character g = ρ.character g := by
  have h : _root_.Representation.ofModule' (k := k) (G := G) ρ.asModule g =
      ρ.asModuleEquiv.symm.conj (ρ g) := by
    ext x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      _root_.Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply,
      ofModule'_apply, MonoidAlgebra.of_apply]
  rw [_root_.Representation.character, h, LinearMap.trace_conj', _root_.Representation.character]

end Character

end Representation

end TauCeti
