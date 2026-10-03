/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.RingEquiv

/-!
# Restriction of scalars on `G₀(mod R)` along a finite ring homomorphism

Let `f : R →+* S` be a ring homomorphism making `S` a finitely generated `R`-module. Restriction
of scalars along `f` keeps the underlying abelian group of an `S`-module, so it is exact, and it
sends a finitely generated `S`-module to a finitely generated `R`-module: a finite generating set
of `M` over `S` multiplied by a finite generating set of `S` over `R` generates `M` over `R`. It
therefore induces a homomorphism of exact Grothendieck groups

```text
f^* : G₀(mod S) →+ G₀(mod R),   [M] ↦ [M with scalars restricted along f],
```

contravariantly functorial in `f`. Along a ring isomorphism it is the isomorphism
`RingEquiv.finiteModulesK0Equiv`. The motivating instance is restriction of representations
along a group homomorphism `H →* G` with `G` finite, where `k[G]` is finite over `k[H]`.

The finiteness hypothesis is stated as the finite generation of `S` itself over `R` through `f`.
It is also necessary: restriction of scalars sends the finitely generated `S`-module `S` to a
finitely generated `R`-module only when it holds.

The API is dot notation on the ring homomorphism: use `f.finiteModulesRestrictScalars hf` and
`f.finiteModulesK0Restrict hf`.

The functor on finitely generated modules, `RingHom.finiteModulesRestrictScalars`, is in
`TauCeti.Algebra.Category.ModuleCat.RestrictScalars`.

## Main definitions

* `RingHom.finiteModulesK0Restrict`: the induced homomorphism `G₀(mod S) →+ G₀(mod R)`.

## Main results

* `RingHom.isConflationExact_finiteModulesRestrictScalars`: the restricted functor is
  conflation-exact.
* `RingHom.finiteModulesK0Restrict_of`: the induced homomorphism sends the class of a module to
  the class of its restriction of scalars.
* `RingHom.finiteModulesK0Restrict_id'` and `RingHom.finiteModulesK0Restrict_comp'`: the induced
  homomorphisms are functorial, with `RingHom.finiteModulesK0Restrict_id` and
  `RingHom.finiteModulesK0Restrict_comp` their forms for the literal identity and composite.
* `RingEquiv.finiteModulesK0Restrict_toRingHom`: along a ring isomorphism the induced
  homomorphism is `RingEquiv.finiteModulesK0Equiv`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6,
  for the functoriality of `G₀` along finite ring homomorphisms.
-/

public section

open CategoryTheory CategoryTheory.ObjectProperty TauCeti

universe u

namespace RingHom

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

variable (f : R →+* S)
  (hf : letI := f.toModule; Module.Finite R S)

/-- Restriction of scalars on finitely generated modules is conflation-exact: it sends a short
exact sequence of finitely generated `S`-modules to a short exact sequence of `R`-modules. -/
theorem isConflationExact_finiteModulesRestrictScalars :
    (finiteModulesExactStructure S).IsConflationExact (finiteModulesExactStructure R)
      (f.finiteModulesRestrictScalars hf) where
  map_conflation {X} hX := by
    rw [finiteModulesExactStructure_conflation_iff] at hX ⊢
    have hR := hX.map_of_exact (ModuleCat.restrictScalars.{u} f)
    rw [← ShortComplex.map_comp] at hR ⊢
    exact ShortComplex.shortExact_of_iso
      (X.mapNatIso (f.finiteModulesRestrictScalarsCompιIso hf).symm) hR

/-- **Restriction of scalars on `G₀(mod R)`.** A ring homomorphism `f : R →+* S` making `S` a
finitely generated `R`-module induces `G₀(mod S) →+ G₀(mod R)`, sending the class of a
finitely generated `S`-module to the class of the same module with scalars restricted along
`f`. -/
noncomputable def finiteModulesK0Restrict :
    ExactK0.{u} (finiteModulesExactStructure S) →+ ExactK0.{u} (finiteModulesExactStructure R) :=
  ExactK0.map _ (f.isConflationExact_finiteModulesRestrictScalars hf)

@[simp]
theorem finiteModulesK0Restrict_of (M : FGModuleCat.{u} S) :
    f.finiteModulesK0Restrict hf (ExactK0.of M) =
      ExactK0.of ((f.finiteModulesRestrictScalars hf).obj M) :=
  ExactK0.map_of.{u, u} _ _ M

/-! ### Functoriality in the ring homomorphism

As for `RingEquiv.finiteModulesK0Equiv`, functoriality is proved from the isomorphisms
`ModuleCat.restrictScalarsId'App` and `ModuleCat.restrictScalarsComp'App` between restricted
modules: isomorphic objects have the same class. The primed forms take an equation of ring
homomorphisms, so they apply to ring homomorphisms that are only propositionally an identity or a
composite, such as the maps of monoid algebras induced by an identity or a composite of monoid
homomorphisms. -/

/-- Restriction along a ring endomorphism equal to the identity induces the identity on
`G₀(mod R)`. -/
theorem finiteModulesK0Restrict_id' (f : R →+* R) (h : f = RingHom.id R)
    (hf : letI := f.toModule; Module.Finite R R) :
    f.finiteModulesK0Restrict hf = AddMonoidHom.id _ :=
  ExactK0.hom_ext fun M ↦ by
    simp only [finiteModulesK0Restrict_of, AddMonoidHom.id_apply]
    exact ExactK0.of_congr (ObjectProperty.isoMk _
      ((f.finiteModulesRestrictScalarsCompιIso hf).app M ≪≫
        ModuleCat.restrictScalarsId'App f h M.obj))

/-- Restriction along the identity ring homomorphism induces the identity on `G₀(mod R)`. -/
@[simp]
theorem finiteModulesK0Restrict_id
    (hf : letI := (RingHom.id R).toModule; Module.Finite R R) :
    (RingHom.id R).finiteModulesK0Restrict hf = AddMonoidHom.id _ :=
  finiteModulesK0Restrict_id' _ rfl hf

/-- Restriction along a ring homomorphism equal to a composite `g ∘ f` induces the composite of
the restrictions along `g` and along `f`, in the reverse order. -/
theorem finiteModulesK0Restrict_comp' (g : S →+* T) (gf : R →+* T) (h : gf = g.comp f)
    (hg : letI := g.toModule; Module.Finite S T)
    (hgf : letI := gf.toModule; Module.Finite R T) :
    gf.finiteModulesK0Restrict hgf =
      (f.finiteModulesK0Restrict hf).comp (g.finiteModulesK0Restrict hg) :=
  ExactK0.hom_ext fun M ↦ by
    simp only [finiteModulesK0Restrict_of, AddMonoidHom.comp_apply]
    exact ExactK0.of_congr
      (ObjectProperty.isoMk _ ((gf.finiteModulesRestrictScalarsCompιIso hgf).app M ≪≫
        ModuleCat.restrictScalarsComp'App f g gf h M.obj ≪≫
        (ModuleCat.restrictScalars f).mapIso
          ((g.finiteModulesRestrictScalarsCompιIso hg).app M).symm ≪≫
        ((f.finiteModulesRestrictScalarsCompιIso hf).app _).symm))

/-- Restriction along a composite `g ∘ f` of ring homomorphisms induces the composite of the
restrictions along `g` and along `f`, in the reverse order. -/
@[simp]
theorem finiteModulesK0Restrict_comp (g : S →+* T)
    (hg : letI := g.toModule; Module.Finite S T)
    (hgf : letI := (g.comp f).toModule; Module.Finite R T) :
    (g.comp f).finiteModulesK0Restrict hgf =
      (f.finiteModulesK0Restrict hf).comp (g.finiteModulesK0Restrict hg) :=
  f.finiteModulesK0Restrict_comp' hf g _ rfl hg hgf

end RingHom

namespace RingEquiv

variable {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)

/-- Along a ring isomorphism, restriction of scalars on `G₀(mod S)` is the isomorphism
`RingEquiv.finiteModulesK0Equiv`. -/
theorem finiteModulesK0Restrict_toRingHom
    (hf : letI := e.toRingHom.toModule; Module.Finite R S) :
    e.toRingHom.finiteModulesK0Restrict hf = e.finiteModulesK0Equiv.toAddMonoidHom :=
  ExactK0.hom_ext fun M ↦ by
    simp only [RingHom.finiteModulesK0Restrict_of, AddEquiv.coe_toAddMonoidHom,
      finiteModulesK0Equiv_of]
    exact congrArg ExactK0.of (FullSubcategory.ext (by simp))

end RingEquiv
