/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Intertwining
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
* `Representation.exists_intertwiningMap_section_of_projective`: a representation with projective
  underlying `k[G]`-module is a retract of a free representation.
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

section Comp

variable {k G H : Type*} [CommSemiring k] [Monoid G] [Monoid H]
variable {M N : Type*} [AddCommMonoid M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
  [Module k[H] M] [AddCommMonoid N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N]
  [Module k[H] N]

/-- **Linear maps over a restricted group algebra are equivariant.** If `k[H]` acts on `M` and
`N` through `f : H →* G`, then a `k[H]`-linear map `M → N` commutes with the action of `f h` in
`Representation.ofModule'`. -/
theorem map_ofModule'_comp (f : H →* G)
    (hM : ∀ (a : k[H]) (x : M), a • x = MonoidAlgebra.mapDomainRingHom k f a • x)
    (hN : ∀ (a : k[H]) (y : N), a • y = MonoidAlgebra.mapDomainRingHom k f a • y)
    (e : M →ₗ[k[H]] N) (h : H) (x : M) :
    e (_root_.Representation.ofModule' (k := k) (G := G) M (f h) x) =
      _root_.Representation.ofModule' (k := k) (G := G) N (f h) (e x) := by
  simp only [ofModule'_apply]
  have := e.map_smul (MonoidAlgebra.single h 1) x
  rwa [hM, hN, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single] at this

end Comp

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
  LinearMap.trace_piMap fun i ↦ _root_.Representation.ofModule' (k := k) (G := G) (M i) g

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

section Projective

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A representation whose underlying `k[G]`-module is projective is a retract, as a representation,
of the free representation on its underlying module: there is an intertwining map out of the free
representation with an intertwining section. -/
theorem _root_.Representation.exists_intertwiningMap_section_of_projective
    (ρ : _root_.Representation k G V) [Module.Projective k[G] ρ.asModule] :
    ∃ (F : _root_.Representation.IntertwiningMap
        (_root_.Representation.ofModule' (k := k) (G := G) (ρ.asModule →₀ k[G])) ρ)
      (S : _root_.Representation.IntertwiningMap ρ
        (_root_.Representation.ofModule' (k := k) (G := G) (ρ.asModule →₀ k[G]))),
      ∀ z, F (S z) = z := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp ‹Module.Projective k[G] ρ.asModule›
  let τ := _root_.Representation.ofModule' (k := k) (G := G) (ρ.asModule →₀ k[G])
  let E : τ.asModule ≃ₗ[k[G]] (ρ.asModule →₀ k[G]) := ofModule'AsModuleEquiv _
  let F : _root_.Representation.IntertwiningMap τ ρ :=
    (_root_.Representation.IntertwiningMap.equivLinearMapAsModule τ ρ).symm
      (Finsupp.linearCombination k[G] id ∘ₗ E.toLinearMap)
  let S : _root_.Representation.IntertwiningMap ρ τ :=
    (_root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ τ).symm
      (E.symm.toLinearMap ∘ₗ s)
  -- Both maps evaluate definitionally through the identifications of `asModule` with the carrier.
  have hF_apply (z : ρ.asModule →₀ k[G]) :
      F z = ρ.asModuleEquiv
        (Finsupp.linearCombination k[G] id (E (τ.asModuleEquiv.symm z))) := rfl
  have hS_apply (z : V) :
      S z = τ.asModuleEquiv (E.symm (s (ρ.asModuleEquiv.symm z))) := rfl
  -- `S` is a section of `F`, because `s` is a section of `Finsupp.linearCombination`.
  refine ⟨F, S, fun z => ?_⟩
  simpa only [hF_apply, hS_apply, LinearEquiv.symm_apply_apply, E.apply_symm_apply,
    LinearEquiv.apply_symm_apply] using congrArg ρ.asModuleEquiv (hs (ρ.asModuleEquiv.symm z))

end Projective

end Representation

end TauCeti
