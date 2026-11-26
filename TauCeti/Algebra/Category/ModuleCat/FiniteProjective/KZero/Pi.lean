/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Map
public import TauCeti.RingTheory.GrothendieckRing

/-!
# Projective `K₀` of a finite product of rings

Projective `K₀` turns finite products of rings into products of groups:

```text
K₀(Π j, R j) ≃ Π j, K₀(R j)
```

for a finite family of rings `R j`. As for binary products (`TauCeti.KZero.prodEquiv`), the
isomorphism is computed on the idempotent model of `K₀`: the idempotent monoid of the product is
the product of the idempotent monoids (`TauCeti.IdempotentMonoid.piEquiv`), and group completion
commutes with arbitrary products (`Algebra.GrothendieckAddGroup.piEquiv`). It sends the class
`[eRⁿ]` of an idempotent matrix over the product to the classes of its components `e.map (· j)`.
When the index type and the rings live in one universe, its components are the maps of `K₀`
induced by the evaluations `Π j, R j → R j`, that is, extension of scalars along them.

The inverse places a class of `K₀(R j)` in the factor `j`. This component inclusion is an additive
map, not induced by a unital ring homomorphism: it sends the class of an idempotent matrix `e` over
`R j` to the class of the idempotent matrix over the product supported in the factor `j`, whose
image is a module on which the other factors act by zero.

## Main definitions

* `TauCeti.KZero.piEquiv R`: the isomorphism `K₀(Π j, R j) ≃+ Π j, K₀(R j)` for a finite family.

## Main results

* `TauCeti.KZero.piEquiv_toKZero`, `TauCeti.KZero.piEquiv_symm_single_toKZero`: on idempotent
  classes, the isomorphism takes components, and its inverse places a class in one factor by the
  idempotent matrix supported there. `TauCeti.KZero.piEquiv_of_ofIdempotent` and
  `TauCeti.KZero.piEquiv_symm_single_of_ofIdempotent` state the same on the classes
  `SplitK0.of (ofIdempotent e he)`.
* `TauCeti.KZero.piEquiv_of_finiteProjectiveModulesRegular`: `[Π j, R j] ↦ ([R j])ⱼ`.
* `TauCeti.KZero.piEquiv_apply`: the components of the isomorphism are the maps induced by the
  evaluations.

## References

* C. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2, Examples
  2.1.2–2.1.4, p. 69: `K₀` of a finite product of rings is the product of the `K₀` groups.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2, for the idempotent description.
-/

public section

noncomputable section

namespace TauCeti

open _root_.Algebra

universe u w

namespace KZero

/-! ### Projective `K₀` of a finite product -/

section Pi

variable {J : Type w} [Finite J] (R : J → Type u) [∀ j, Ring (R j)]

/-- **`K₀` of a finite product of rings.** `K₀(Π j, R j) ≃+ Π j, K₀(R j)`, sending the class
`[eRⁿ]` of an idempotent matrix `e` over the product to the classes of its components
(`TauCeti.KZero.piEquiv_toKZero`), and the free module of rank one to the family of free modules of
rank one (`TauCeti.KZero.piEquiv_of_finiteProjectiveModulesRegular`). -/
def piEquiv : KZero (∀ j, R j) ≃+ ∀ j, KZero (R j) :=
  (IdempotentMonoid.kZeroEquiv (∀ j, R j)).symm.trans <|
    (GrothendieckAddGroup.congr (IdempotentMonoid.piEquiv R)).trans <|
      GrothendieckAddGroup.piEquiv.trans
        (AddEquiv.piCongrRight (Ns := fun j ↦ KZero (R j)) fun j ↦
          IdempotentMonoid.kZeroEquiv (R j))

variable {R}

/-- `TauCeti.KZero.piEquiv` sends the class of an element `x` of the idempotent monoid of
`Π j, R j` to the classes of its images under the evaluations. -/
@[simp]
theorem piEquiv_toKZero (x : IdempotentMonoid (∀ j, R j)) :
    piEquiv R (IdempotentMonoid.toKZero _ x) =
      fun j ↦ IdempotentMonoid.toKZero (R j)
        (IdempotentMonoid.map (Pi.evalNonUnitalRingHom R j) x) := by
  ext j
  simp only [piEquiv, ← IdempotentMonoid.kZeroEquiv_of, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply, GrothendieckAddGroup.congr_of, GrothendieckAddGroup.piEquiv_of,
    AddEquiv.piCongrRight_apply, IdempotentMonoid.piEquiv_apply]

/-- The inverse of `TauCeti.KZero.piEquiv` places the class of an element `x` of the idempotent
monoid of `R j` in the factor `j` by the element of the idempotent monoid of the product supported
in that factor. -/
@[simp]
theorem piEquiv_symm_single_toKZero [DecidableEq J] (j : J) (x : IdempotentMonoid (R j)) :
    (piEquiv R).symm (Pi.single j (IdempotentMonoid.toKZero (R j) x)) =
      IdempotentMonoid.toKZero _ ((IdempotentMonoid.piEquiv R).symm (Pi.single j x)) := by
  rw [AddEquiv.symm_apply_eq, piEquiv_toKZero]
  ext k
  rw [← IdempotentMonoid.piEquiv_apply, AddEquiv.apply_symm_apply]
  rcases eq_or_ne k j with rfl | hkj
  · simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hkj, map_zero]

/-- `TauCeti.KZero.piEquiv` sends the class of the column range of an idempotent matrix `e` over
`Π j, R j` to the classes of the column ranges of its components. This is
`TauCeti.KZero.piEquiv_toKZero` in the simp normal form `TauCeti.IdempotentMonoid.toKZero_mk`
produces. -/
@[simp]
theorem piEquiv_of_ofIdempotent {ι : Type*} [Fintype ι] {e : Matrix ι ι (∀ j, R j)}
    (he : IsIdempotentElem e) :
    piEquiv R (SplitK0.of.{max w u} (FiniteProjectiveModules.ofIdempotent e he)) =
      fun j ↦ SplitK0.of.{u} (FiniteProjectiveModules.ofIdempotent (e.map (· j))
        (he.matrix_map (Pi.evalNonUnitalRingHom R j))) := by
  simpa only [IdempotentMonoid.toKZero_mk, IdempotentMonoid.map_mk, Pi.coe_evalNonUnitalRingHom]
    using piEquiv_toKZero (IdempotentMonoid.mk e he)

/-- The inverse of `TauCeti.KZero.piEquiv` places the class of the column range of an idempotent
matrix `e` over `R j` in the factor `j` by the matrix over `Π j, R j` supported in that factor.
This is `TauCeti.KZero.piEquiv_symm_single_toKZero` in the simp normal form
`TauCeti.IdempotentMonoid.toKZero_mk` produces. -/
@[simp]
theorem piEquiv_symm_single_of_ofIdempotent [DecidableEq J] {ι : Type*} [Fintype ι] {j : J}
    {e : Matrix ι ι (R j)} (he : IsIdempotentElem e) :
    (piEquiv R).symm (Pi.single j (SplitK0.of.{u} (FiniteProjectiveModules.ofIdempotent e he))) =
      SplitK0.of.{max w u} (FiniteProjectiveModules.ofIdempotent (e.map (Pi.single j))
        (he.matrix_map_piSingle j)) := by
  simpa only [IdempotentMonoid.toKZero_mk, IdempotentMonoid.piEquiv_symm_single_mk] using
    piEquiv_symm_single_toKZero j (IdempotentMonoid.mk e he)

/-- `TauCeti.KZero.piEquiv` sends the class of the free right `Π j, R j`-module of rank one to the
classes of the free modules of rank one over the `R j`. -/
theorem piEquiv_of_finiteProjectiveModulesRegular :
    piEquiv R (SplitK0.of.{max w u} (finiteProjectiveModulesRegular (∀ j, R j)ᵐᵒᵖ)) =
      fun j ↦ SplitK0.of.{u} (finiteProjectiveModulesRegular (R j)ᵐᵒᵖ) := by
  rw [← IdempotentMonoid.toKZero_mk_one, piEquiv_toKZero]
  ext j
  rw [← IdempotentMonoid.toKZero_mk_one, IdempotentMonoid.map_mk]
  congr
  exact Matrix.map_one _ rfl rfl

end Pi

section Components

variable {J : Type u} [Finite J] (R : J → Type u) [∀ j, Ring (R j)]

/-- The components of `TauCeti.KZero.piEquiv` are the maps of `K₀` induced by the evaluations
`Π j, R j → R j`, extension of scalars along them. -/
theorem piEquiv_apply (x : KZero (∀ j, R j)) (j : J) :
    piEquiv R x j = map (Pi.evalRingHom R j) x := by
  have h : (Pi.evalAddMonoidHom (fun j ↦ KZero (R j)) j).comp (piEquiv R).toAddMonoidHom =
      map (Pi.evalRingHom R j) := by
    refine (AddMonoidHom.cancel_right (f := (IdempotentMonoid.kZeroEquiv _).toAddMonoidHom)
      (IdempotentMonoid.kZeroEquiv _).surjective).1 <|
        GrothendieckAddGroup.addHom_ext fun x ↦ ?_
    induction x using IdempotentMonoid.ind with | mk n e he
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, Pi.evalAddMonoidHom_apply]
    rw [map_kZeroEquiv_of_mk, IdempotentMonoid.kZeroEquiv_of, IdempotentMonoid.kZeroEquiv_of,
      piEquiv_toKZero]
    simp only [IdempotentMonoid.map_mk]
    -- The evaluation as a ring homomorphism and as a non-unital one have the same entries.
    exact congrArg _ (IdempotentMonoid.mk_congr_matrix _ _ (by ext; simp))
  exact DFunLike.congr_fun h x

end Components

end KZero

end TauCeti
