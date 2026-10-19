/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.ModuleCat.CoextendScalars

/-!
# Coextension of scalars on `G₀(mod R)` along a finite projective algebra homomorphism

Let `f : R →ₐ[k] S` be a homomorphism of algebras over a commutative ring `k`, with `R` finitely
generated over `k` and `S` finitely generated and projective over `R` through `f`. Coextension of
scalars `M ↦ Hom_R(S, M)` then sends finitely generated `R`-modules to finitely generated
`S`-modules (`AlgHom.isFG_coextendScalars`) and short exact sequences to short exact sequences
(`ModuleCat.coextendScalars_map_shortExact`). It therefore induces a homomorphism of exact
Grothendieck groups

```text
f_! : G₀(mod R) →+ G₀(mod S),   [M] ↦ [Hom_R(S, M)].
```

The motivating instance is coinduction from a subgroup of a finite group, which for a subgroup of
finite index is also induction.

The API is dot notation on the algebra homomorphism: use
`f.finiteModulesK0Coextend hproj hfin`.

## Main definitions

* `AlgHom.finiteModulesK0Coextend`: the induced homomorphism `G₀(mod R) →+ G₀(mod S)`.

## Main results

* `AlgHom.isConflationExact_finiteModulesCoextendScalars`: coextension of scalars on finitely
  generated modules is conflation-exact.
* `AlgHom.finiteModulesK0Coextend_of`: the induced homomorphism sends the class of a module to the
  class of its coextension of scalars.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6,
  for exact functors between categories of modules and the maps they induce on `G₀`.
-/

public section

open CategoryTheory TauCeti

universe u

namespace AlgHom

variable {k : Type*} [CommRing k] {R S : Type u} [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (f : R →ₐ[k] S) [Module.Finite k R]
  (hproj : letI := f.toRingHom.toModule; Module.Projective R S)
  (hfin : letI := f.toRingHom.toModule; Module.Finite R S)

/-- Coextension of scalars on finitely generated modules is conflation-exact: it sends a short
exact sequence of finitely generated `R`-modules to a short exact sequence of `S`-modules. -/
theorem isConflationExact_finiteModulesCoextendScalars :
    (finiteModulesExactStructure R).IsConflationExact (finiteModulesExactStructure S)
      (f.finiteModulesCoextendScalars hproj hfin) where
  map_conflation {X} hX := by
    rw [finiteModulesExactStructure_conflation_iff] at hX ⊢
    have hS := ModuleCat.coextendScalars_map_shortExact.{u} f.toRingHom hproj hX
    rw [← ShortComplex.map_comp] at hS ⊢
    exact ShortComplex.shortExact_of_iso
      (X.mapNatIso (f.finiteModulesCoextendScalarsCompιIso hproj hfin).symm) hS

/-- **Coextension of scalars on `G₀(mod R)`.** A homomorphism `f : R →ₐ[k] S` of algebras over a
commutative ring `k`, with `R` finitely generated over `k` and `S` finitely generated and
projective over `R` through `f`, induces `G₀(mod R) →+ G₀(mod S)`, sending the class of a
finitely generated `R`-module `M` to the class of `Hom_R(S, M)`. -/
noncomputable def finiteModulesK0Coextend :
    ExactK0.{u} (finiteModulesExactStructure R) →+ ExactK0.{u} (finiteModulesExactStructure S) :=
  ExactK0.map _ (f.isConflationExact_finiteModulesCoextendScalars hproj hfin)

@[simp]
theorem finiteModulesK0Coextend_of (M : FGModuleCat.{u} R) :
    f.finiteModulesK0Coextend hproj hfin (ExactK0.of M) =
      ExactK0.of ((f.finiteModulesCoextendScalars hproj hfin).obj M) :=
  ExactK0.map_of.{u, u} _ _ M

end AlgHom
