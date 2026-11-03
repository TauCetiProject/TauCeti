/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.CategoryTheory.Exact.Functor

/-!
# Extension of scalars on `K₀(proj R)`

Let `f : R →+* S` be a homomorphism of possibly noncommutative rings. Extension of scalars
`P ↦ S ⊗_R P` (`TauCeti.BalancedExtension.functor f`) sends finitely generated projective
`R`-modules to finitely generated projective `S`-modules and is additive. Every conflation of
finitely generated projective modules splits, and additive functors preserve split short exact
sequences, so it induces a homomorphism of algebraic `K₀`-groups

```text
f_* : K₀(proj R) →+ K₀(proj S),   [P] ↦ [S ⊗_R P],
```

covariantly functorial in `f`. This is the functoriality of algebraic `K₀` in the ring.

In the stable-idempotent description of `K₀`, a finitely generated projective module is the image
`Rⁿ e` of an idempotent matrix `e` acting on row vectors, and `f_*` applies `f` to the entries of
`e`: the class of `Rⁿ e` is sent to the class of `Sⁿ f(e)`
(`RingHom.finiteProjectiveModulesK0Extend_of_linearEquiv_range`). In particular the class of
`Rⁿ` is sent to the class of `Sⁿ`. This is the form in which pairings of `K₀` with cyclic
cohomology, computed on idempotent matrices, are compared along ring homomorphisms; for instance
the augmentation of a forced unitization `A⁺ → R` induces `K₀(A⁺) → K₀(R)`, whose kernel is the
`K₀`-group of a nonunital algebra `A`.

The API is dot notation on the ring homomorphism: use `f.finiteProjectiveModulesExtendScalars`
and `f.finiteProjectiveModulesK0Extend`.

## Main definitions

* `RingHom.finiteProjectiveModulesK0Extend`: the homomorphism `K₀(proj R) →+ K₀(proj S)`
  induced by the extension-of-scalars functor `RingHom.finiteProjectiveModulesExtendScalars`
  of `TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange`.

## Main results

* `RingHom.isConflationExact_finiteProjectiveModulesExtendScalars`: the functor is
  conflation-exact.
* `RingHom.finiteProjectiveModulesK0Extend_of`: the class of a module is sent to the class of its
  extension of scalars.
* `RingHom.finiteProjectiveModulesK0Extend_id` and `RingHom.finiteProjectiveModulesK0Extend_comp`:
  functoriality in the ring homomorphism.
* `RingHom.finiteProjectiveModulesK0Extend_of_linearEquiv_range`: the class of the image of an
  idempotent matrix `e` is sent to the class of the image of `f(e)`.
* `RingHom.finiteProjectiveModulesK0Extend_of_linearEquiv_pi`: the class of `Rⁿ` is sent to the
  class of `Sⁿ`.

## References

* C. A. Weibel, *The K-book*, Chapter II, §2.8 and Example 2.8.1, pp. 12–13, for the
  functoriality of `K₀` of a ring by extension of scalars.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2, for the description of this map
  on idempotent matrices.
-/

public section

open CategoryTheory TauCeti

universe u

namespace RingHom

variable {R S T : Type u} [Ring R] [Ring S] [Ring T] (f : R →+* S)

/-- Extension of scalars on finitely generated projective modules is conflation-exact: every
conflation of finitely generated projective modules splits, and the additive functor preserves
split short exact sequences. -/
theorem isConflationExact_finiteProjectiveModulesExtendScalars :
    (finiteProjectiveModulesExactStructure R).IsConflationExact
      (finiteProjectiveModulesExactStructure S) f.finiteProjectiveModulesExtendScalars := by
  rw [finiteProjectiveModulesExactStructure_eq_split,
    finiteProjectiveModulesExactStructure_eq_split]
  exact ExactStructure.isConflationExact_split _

/-- **Extension of scalars on `K₀(proj R)`.** A ring homomorphism `f : R →+* S` induces
`K₀(proj R) →+ K₀(proj S)`, sending the class of a finitely generated projective `R`-module `P` to
the class of `S ⊗_R P`. -/
noncomputable def finiteProjectiveModulesK0Extend :
    ExactK0.{u} (finiteProjectiveModulesExactStructure R) →+
      ExactK0.{u} (finiteProjectiveModulesExactStructure S) :=
  ExactK0.map _ f.isConflationExact_finiteProjectiveModulesExtendScalars

@[simp]
theorem finiteProjectiveModulesK0Extend_of (P : (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesK0Extend (ExactK0.of P) =
      (ExactK0.of (f.finiteProjectiveModulesExtendScalars.obj P) :
        ExactK0.{u} (finiteProjectiveModulesExactStructure S)) :=
  ExactK0.map_of.{u, u} _ _ P

/-- The class of a finitely generated projective module `P` is sent to the class of any
finitely generated projective `S`-module isomorphic to `S ⊗_R P`. -/
theorem finiteProjectiveModulesK0Extend_of_linearEquiv
    (P : (finiteProjectiveModules R).FullSubcategory)
    (Q : (finiteProjectiveModules S).FullSubcategory) (θ : BalancedExtension f P.obj ≃ₗ[S] Q.obj) :
    f.finiteProjectiveModulesK0Extend (ExactK0.of P) =
      (ExactK0.of Q : ExactK0.{u} (finiteProjectiveModulesExactStructure S)) := by
  rw [finiteProjectiveModulesK0Extend_of]
  exact ExactK0.of_congr (ObjectProperty.isoMk _
    (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫ θ.toModuleIso))

/-! ### Functoriality in the ring homomorphism

Extension along the identity is the identity and extension along a composite is the composite
of the extensions, up to the natural isomorphisms `TauCeti.BalancedExtension.lid` and
`TauCeti.BalancedExtension.cancelBaseChange`; isomorphic modules have the same class. -/

/-- Extension of scalars along the identity ring homomorphism induces the identity on
`K₀(proj R)`. -/
@[simp]
theorem finiteProjectiveModulesK0Extend_id :
    (RingHom.id R).finiteProjectiveModulesK0Extend = AddMonoidHom.id _ :=
  ExactK0.hom_ext fun P ↦
    (RingHom.id R).finiteProjectiveModulesK0Extend_of_linearEquiv P P
      (BalancedExtension.lid R P.obj)

/-- Extension of scalars along a composite `g ∘ f` induces the composite of the extensions along
`f` and along `g`. -/
@[simp]
theorem finiteProjectiveModulesK0Extend_comp (g : S →+* T) :
    (g.comp f).finiteProjectiveModulesK0Extend =
      g.finiteProjectiveModulesK0Extend.comp f.finiteProjectiveModulesK0Extend :=
  ExactK0.hom_ext fun P ↦ by
    rw [AddMonoidHom.comp_apply, f.finiteProjectiveModulesK0Extend_of,
      g.finiteProjectiveModulesK0Extend_of, (g.comp f).finiteProjectiveModulesK0Extend_of]
    exact ExactK0.of_congr (ObjectProperty.isoMk _
      (eqToIso ((g.comp f).finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫
        (BalancedExtension.cancelBaseChange f g (P := P.obj)).symm.toModuleIso ≪≫
          eqToIso (by
            rw [finiteProjectiveModulesExtendScalars_obj_obj,
              finiteProjectiveModulesExtendScalars_obj_obj])))

/-! ### Idempotent matrices -/

/-- **Extension of scalars on idempotent matrices.** If a finitely generated projective
`R`-module `P` is isomorphic to the image `Rⁿ e` of an idempotent matrix `e`, acting on row
vectors, then its class is sent to the class of any finitely generated projective `S`-module
isomorphic to the image `Sⁿ f(e)` of the matrix `f(e)`. -/
theorem finiteProjectiveModulesK0Extend_of_linearEquiv_range {ι : Type*} [Fintype ι]
    {e : Matrix ι ι R} (he : IsIdempotentElem e) (P : (finiteProjectiveModules R).FullSubcategory)
    (Q : (finiteProjectiveModules S).FullSubcategory)
    (θ : P.obj ≃ₗ[R] LinearMap.range e.vecMulLinear)
    (θ' : Q.obj ≃ₗ[S] LinearMap.range (e.map f).vecMulLinear) :
    f.finiteProjectiveModulesK0Extend (ExactK0.of P) =
      (ExactK0.of Q : ExactK0.{u} (finiteProjectiveModulesExactStructure S)) :=
  f.finiteProjectiveModulesK0Extend_of_linearEquiv P Q
    ((BalancedExtension.congr f θ).trans
      ((BalancedExtension.rangeVecMulLinearEquiv f he).trans θ'.symm))

/-- Extension of scalars sends the class of a free module `Rⁿ` to the class of `Sⁿ`. -/
theorem finiteProjectiveModulesK0Extend_of_linearEquiv_pi {ι : Type*} [_root_.Finite ι]
    (P : (finiteProjectiveModules R).FullSubcategory)
    (Q : (finiteProjectiveModules S).FullSubcategory) (θ : P.obj ≃ₗ[R] (ι → R))
    (θ' : Q.obj ≃ₗ[S] (ι → S)) :
    f.finiteProjectiveModulesK0Extend (ExactK0.of P) =
      (ExactK0.of Q : ExactK0.{u} (finiteProjectiveModulesExactStructure S)) :=
  have := Fintype.ofFinite ι
  f.finiteProjectiveModulesK0Extend_of_linearEquiv P Q
    ((BalancedExtension.congr f θ).trans ((BalancedExtension.piScalarRight f ι).trans θ'.symm))

end RingHom
