/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.MonoidAlgebra.Finite
public import TauCeti.RepresentationTheory.GrothendieckGroup.Finrank

/-!
# Restriction between Grothendieck groups of group algebras

Let `k` be a ring and `φ : H →* G` a homomorphism of monoids with `G` finite. A
`k[G]`-module becomes a `k[H]`-module through the ring homomorphism
`MonoidAlgebra.mapDomainRingHom k φ : k[H] →+* k[G]`. Since `k[G]` is a finitely generated
`k`-module, it is also a finitely generated `k[H]`-module
(`TauCeti.MonoidAlgebra.mapDomainRingHom_moduleFinite_of_finite`), so this restriction of scalars
sends finitely generated modules to finitely generated modules
(`RingHom.finiteModulesK0Restrict`). It does not change the underlying
groups, so it is exact, and it descends to the exact Grothendieck groups:

```text
res φ : G₀(k[G]) →+ G₀(k[H]),   [M] ↦ [M viewed as a k[H]-module through φ].
```

When `k` is commutative, for a representation `ρ` of `G` this is the class of the composite
representation `ρ ∘ φ`, so it is restriction of representations to a subgroup, and inflation from
a quotient. It is contravariantly functorial in `φ` and, over a field with `H` finite too,
preserves the dimension of a class. Neither `H` nor `k` need be finite for the map itself, and
`H` need not be a subgroup: `φ` is an arbitrary monoid homomorphism into a finite monoid.

## Main definitions

* `TauCeti.resK0`: restriction along `φ : H →* G` as a homomorphism of exact Grothendieck
  groups of finitely generated group-algebra modules.

## Main results

* `TauCeti.resK0_of`: the class of a module goes to the class of its restriction of scalars.
* `TauCeti.resK0_of_asModule`: the class of a representation goes to the class of its composite
  with `φ`; in particular `TauCeti.resK0_of_trivial`, the trivial line goes to the trivial line.
* `TauCeti.resK0_id` and `TauCeti.resK0_comp`: restriction is contravariantly functorial.
* `TauCeti.finrankK0_resK0`: restriction preserves the dimension of a class.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.1, for the restriction
  homomorphism `R_k(G) → R_k(H)`.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

universe u

section Ring

variable (k : Type u) [Ring k] {G H K : Type u} [Monoid G] [Monoid H] [Monoid K] [Finite G]

/-- **Restriction on the Grothendieck group of a group algebra.** For a monoid homomorphism
`φ : H →* G` with `G` finite, viewing a finitely generated `k[G]`-module as a `k[H]`-module
through `φ` induces `G₀(k[G]) →+ G₀(k[H])`. When `k` is commutative, on the class of a
representation `ρ` of `G` it is the class of `ρ ∘ φ` (`TauCeti.resK0_of_asModule`). -/
noncomputable def resK0 (φ : H →* G) :
    ExactK0 (finiteModulesExactStructure k[G]) →+ ExactK0 (finiteModulesExactStructure k[H]) :=
  (MonoidAlgebra.mapDomainRingHom k φ).finiteModulesK0Restrict
    (MonoidAlgebra.mapDomainRingHom_moduleFinite_of_finite φ)

/-- Restriction sends the class of a module to the class of the same module with scalars
restricted along `φ`. -/
@[simp]
theorem resK0_of (φ : H →* G) (M : FGModuleCat.{u} k[G]) :
    resK0 k φ (ExactK0.of M) =
      ExactK0.of (((MonoidAlgebra.mapDomainRingHom k φ).finiteModulesRestrictScalars
        (MonoidAlgebra.mapDomainRingHom_moduleFinite_of_finite φ)).obj M) :=
  RingHom.finiteModulesK0Restrict_of _ _ M

/-- Restriction along the identity homomorphism is the identity. -/
@[simp]
theorem resK0_id : resK0 k (MonoidHom.id G) = AddMonoidHom.id _ :=
  RingHom.finiteModulesK0Restrict_id' _ MonoidAlgebra.mapDomainRingHom_id _

/-- **Restriction is contravariantly functorial**: restricting along `ψ ∘ φ` is restricting
along `ψ` and then along `φ`. -/
@[simp]
theorem resK0_comp [Finite K] (φ : H →* G) (ψ : G →* K) :
    resK0 k (ψ.comp φ) = (resK0 k φ).comp (resK0 k ψ) :=
  RingHom.finiteModulesK0Restrict_comp' _ _ _ _ (MonoidAlgebra.mapDomainRingHom_comp ψ φ) _ _

end Ring

section CommRing

variable (k : Type u) [CommRing k] {G H : Type u} [Monoid G] [Monoid H] [Finite G]

/-- **Restriction of the class of a representation.** Restricting the class of the
`k[G]`-module of a representation `ρ` along `φ` gives the class of the `k[H]`-module of the
composite representation `ρ ∘ φ`. -/
-- Priority above `resK0_of`, whose left-hand side this one specializes.
@[simp high]
theorem resK0_of_asModule (φ : H →* G) {V : Type u} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ : Representation k G V) :
    letI : Module.Finite k[G] ρ.asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] ρ.asModule
    letI : Module.Finite k[H] (Representation.asModule (ρ.comp φ)) :=
      Module.Finite.of_restrictScalars_finite k k[H] (Representation.asModule (ρ.comp φ))
    resK0 k φ (ExactK0.of (FGModuleCat.of k[G] ρ.asModule)) =
      ExactK0.of (FGModuleCat.of k[H] (Representation.asModule (ρ.comp φ))) := by
  let : Module.Finite k[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] ρ.asModule
  let : Module.Finite k[H] (Representation.asModule (ρ.comp φ)) :=
    Module.Finite.of_restrictScalars_finite k k[H] (Representation.asModule (ρ.comp φ))
  have hρ : ρ.asAlgebraHom.comp (MonoidAlgebra.mapDomainAlgHom k k φ) =
      (Representation.asAlgebraHom (ρ.comp φ)) :=
    MonoidAlgebra.algHom_ext (fun h ↦ by simp) (Subsingleton.elim _ _)
  rw [resK0_of]
  refine ExactK0.of_congr (ObjectProperty.isoMk _
    ((RingHom.finiteModulesRestrictScalarsCompιIso _ _).app _ ≪≫ LinearEquiv.toModuleIso
      (AddEquiv.toLinearEquiv
        (M := (ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
          (ModuleCat.of k[G] ρ.asModule))
        (M₂ := (Representation.asModule (ρ.comp φ))) (by rfl) fun a x ↦ ?_)))
  -- Both actions of `a : k[H]` on the underlying space `V` are the endomorphism
  -- `ρ.asAlgebraHom (mapDomain φ a) = (ρ ∘ φ).asAlgebraHom a`.
  exact congrArg (fun T : Module.End k V ↦ T x) (AlgHom.congr_fun hρ a)

/-- Restriction sends the class of the trivial line to the class of the trivial line. -/
-- Priority above `resK0_of_asModule`, whose left-hand side this one specializes.
@[simp high + 1]
theorem resK0_of_trivial (φ : H →* G) :
    letI : Module.Finite k[G] (Representation.trivial k G k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    letI : Module.Finite k[H] (Representation.trivial k H k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[H] _
    resK0 k φ (ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule)) =
      ExactK0.of (FGModuleCat.of k[H] (Representation.trivial k H k).asModule) := by
  have h := resK0_of_asModule k φ (Representation.trivial k G k)
  rwa [Representation.trivial, MonoidHom.one_comp] at h

end CommRing

/-- **Restriction preserves dimension.** Over a field, for finite monoids `H` and `G`, the
`k`-dimension of the restriction of a class along `φ : H →* G` is the dimension of the class. -/
@[simp]
theorem finrankK0_resK0 (k : Type u) [Field k] {G H : Type u} [Monoid G] [Monoid H] [Finite G]
    [Finite H] (φ : H →* G) (x : ExactK0 (finiteModulesExactStructure k[G])) :
    finrankK0 k k[H] (resK0 k φ x) = finrankK0 k k[G] x :=
  finrankK0_finiteModulesK0Restrict k k[H] _
    (MonoidAlgebra.mapDomainRingHom_comp_algebraMap (R := k) φ) x

end TauCeti
