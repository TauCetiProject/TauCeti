/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Map
public import TauCeti.RingTheory.GrothendieckRing

import TauCeti.Algebra.Ring.Prod

/-!
# Projective `K₀` of a product of rings

Projective `K₀` turns finite products of rings into products of groups:

```text
K₀(R × S) ≃ K₀(R) × K₀(S).
```

The isomorphism is computed on the idempotent model of `K₀` (`TauCeti.IdempotentMonoid`). A
matrix over `R × S` is a pair of matrices of the same size over `R` and over `S`
(`Matrix.prodEquiv`), it is idempotent exactly when both components are, and two idempotents over
`R × S` are equivalent exactly when their components are
(`Matrix.idempotentEquivalent_prod_iff`). So the idempotent monoid of `R × S` is the product of
those of `R` and `S` (`TauCeti.IdempotentMonoid.prodEquiv`), and passing to group completions
gives the isomorphism of `K₀`. It sends the class `[eRⁿ]` of an idempotent `e` over `R × S` to the
classes of its two components `e.map Prod.fst` and `e.map Prod.snd`. When `R` and `S` live in the
same universe, its two components are the maps of `K₀` induced by the two projections
(`TauCeti.KZero.map`), that is, extension of scalars along `R × S → R` and `R × S → S`. In
particular the free module of rank one goes to the pair of free modules of rank one.

The zero-ring value `K₀(0) = 0`, the empty case of the product formula, is the instance
`TauCeti.FiniteProjectiveModules.subsingleton_splitK0` applied to `Rᵐᵒᵖ`.

## Main definitions

* `TauCeti.KZero.prodEquiv R S`: the isomorphism `K₀(R × S) ≃+ K₀(R) × K₀(S)`.

## Main results

* `TauCeti.KZero.prodEquiv_toKZero`, `TauCeti.KZero.prodEquiv_symm_toKZero_toKZero`: on the
  classes `[eRⁿ]` of idempotents, the isomorphism takes components, and its inverse pairs them.
  `TauCeti.KZero.prodEquiv_of_ofIdempotent` and
  `TauCeti.KZero.prodEquiv_symm_of_ofIdempotent_of_ofIdempotent` state the same on the classes
  `SplitK0.of (ofIdempotent e he)`, the simp normal form of `toKZero _ (mk e he)`.
* `TauCeti.KZero.toAddMonoidHom_prodEquiv`, `TauCeti.KZero.prodEquiv_apply_fst`,
  `TauCeti.KZero.prodEquiv_apply_snd`: the components of the isomorphism are the maps induced by
  the two projections.
* `TauCeti.KZero.prodEquiv_of_finiteProjectiveModulesRegular`: `[R × S] ↦ ([R], [S])`.

## References

* C. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2: `K₀` of a finite
  product of rings is the product of the `K₀` groups.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2, for the idempotent description.
-/

public section

noncomputable section

namespace TauCeti

open _root_.Algebra

universe u v

namespace KZero

/-! ### Projective `K₀` of a product -/

section Prod

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/-- **`K₀` of a product of rings.** `K₀(R × S) ≃+ K₀(R) × K₀(S)`, sending the class `[eRⁿ]` of an
idempotent matrix `e` over `R × S` to the classes of its two components
(`TauCeti.KZero.prodEquiv_toKZero`), and the free module of rank one to the pair of free modules of
rank one (`TauCeti.KZero.prodEquiv_of_finiteProjectiveModulesRegular`). -/
def prodEquiv : KZero (R × S) ≃+ KZero R × KZero S :=
  (IdempotentMonoid.kZeroEquiv (R × S)).symm.trans <|
    (GrothendieckAddGroup.congr (IdempotentMonoid.prodEquiv R S)).trans <|
      GrothendieckAddGroup.prodEquiv.trans
        ((IdempotentMonoid.kZeroEquiv R).prodCongr (IdempotentMonoid.kZeroEquiv S))

variable {R S}

/-- `TauCeti.KZero.prodEquiv` sends the class of an element `x` of the idempotent monoid of
`R × S` to the classes of its images under the two projections. -/
@[simp]
theorem prodEquiv_toKZero (x : IdempotentMonoid (R × S)) :
    prodEquiv R S (IdempotentMonoid.toKZero (R × S) x) =
      (IdempotentMonoid.toKZero R (IdempotentMonoid.map (NonUnitalRingHom.fst R S) x),
        IdempotentMonoid.toKZero S (IdempotentMonoid.map (NonUnitalRingHom.snd R S) x)) := by
  rw [← IdempotentMonoid.kZeroEquiv_of, prodEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply, AddEquiv.trans_apply, GrothendieckAddGroup.congr_of,
    IdempotentMonoid.prodEquiv_apply, AddEquiv.trans_apply, GrothendieckAddGroup.prodEquiv_of]
  -- `AddEquiv.prodCongr` acts componentwise; Mathlib states no apply lemma for it.
  exact Prod.ext (IdempotentMonoid.kZeroEquiv_of _ _) (IdempotentMonoid.kZeroEquiv_of _ _)

/-- The inverse of `TauCeti.KZero.prodEquiv` sends the pair of classes of `x` in the idempotent
monoid of `R` and `y` in that of `S` to the class of the element of the idempotent monoid of
`R × S` with components `x` and `y`. -/
@[simp]
theorem prodEquiv_symm_toKZero_toKZero (x : IdempotentMonoid R) (y : IdempotentMonoid S) :
    (prodEquiv R S).symm (IdempotentMonoid.toKZero R x, IdempotentMonoid.toKZero S y) =
      IdempotentMonoid.toKZero (R × S) ((IdempotentMonoid.prodEquiv R S).symm (x, y)) := by
  have h := (IdempotentMonoid.prodEquiv R S).apply_symm_apply (x, y)
  rw [IdempotentMonoid.prodEquiv_apply, Prod.mk.injEq] at h
  rw [AddEquiv.symm_apply_eq, prodEquiv_toKZero, h.1, h.2]

/-- `TauCeti.KZero.prodEquiv` sends the class of the column range of an idempotent matrix `e` over
`R × S` to the classes of the column ranges of its components. This is
`TauCeti.KZero.prodEquiv_toKZero` in the simp normal form `TauCeti.IdempotentMonoid.toKZero_mk`
produces. -/
@[simp]
theorem prodEquiv_of_ofIdempotent {ι : Type*} [Fintype ι] {e : Matrix ι ι (R × S)}
    (he : IsIdempotentElem e) :
    prodEquiv R S (SplitK0.of.{max u v} (FiniteProjectiveModules.ofIdempotent e he)) =
      (SplitK0.of.{u} (FiniteProjectiveModules.ofIdempotent (e.map Prod.fst)
          (he.matrix_map (NonUnitalRingHom.fst R S))),
        SplitK0.of.{v} (FiniteProjectiveModules.ofIdempotent (e.map Prod.snd)
          (he.matrix_map (NonUnitalRingHom.snd R S)))) := by
  simpa only [IdempotentMonoid.toKZero_mk, IdempotentMonoid.map_mk, NonUnitalRingHom.coe_fst,
    NonUnitalRingHom.coe_snd] using prodEquiv_toKZero (IdempotentMonoid.mk e he)

/-- The inverse of `TauCeti.KZero.prodEquiv` sends the pair of classes of the column ranges of
idempotent matrices `e₁` over `R` and `e₂` over `S` to the class of the column range of the
idempotent matrix over `R × S` with components `e₁` and `e₂`. This is
`TauCeti.KZero.prodEquiv_symm_toKZero_toKZero` in the simp normal form
`TauCeti.IdempotentMonoid.toKZero_mk` produces. -/
@[simp]
theorem prodEquiv_symm_of_ofIdempotent_of_ofIdempotent {ι : Type*} [Fintype ι]
    {e₁ : Matrix ι ι R} {e₂ : Matrix ι ι S} (he₁ : IsIdempotentElem e₁)
    (he₂ : IsIdempotentElem e₂) :
    (prodEquiv R S).symm (SplitK0.of.{u} (FiniteProjectiveModules.ofIdempotent e₁ he₁),
        SplitK0.of.{v} (FiniteProjectiveModules.ofIdempotent e₂ he₂)) =
      SplitK0.of.{max u v} (FiniteProjectiveModules.ofIdempotent
        ((Matrix.prodEquiv ι ι R S).symm (e₁, e₂)) (he₁.matrix_prodEquiv_symm he₂)) := by
  simpa only [IdempotentMonoid.toKZero_mk, IdempotentMonoid.prodEquiv_symm_mk_mk] using
    prodEquiv_symm_toKZero_toKZero (IdempotentMonoid.mk e₁ he₁) (IdempotentMonoid.mk e₂ he₂)

/-- `TauCeti.KZero.prodEquiv` sends the class of the free right `R × S`-module of rank one to the
classes of the free modules of rank one over `R` and over `S`. -/
theorem prodEquiv_of_finiteProjectiveModulesRegular :
    prodEquiv R S (SplitK0.of.{max u v} (finiteProjectiveModulesRegular (R × S)ᵐᵒᵖ)) =
      (SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ),
        SplitK0.of.{v} (finiteProjectiveModulesRegular Sᵐᵒᵖ)) := by
  have h₁ := IdempotentMonoid.kZeroEquiv_of_mk_one (R := R × S) 1
  have hR := IdempotentMonoid.kZeroEquiv_of_mk_one (R := R) 1
  have hS := IdempotentMonoid.kZeroEquiv_of_mk_one (R := S) 1
  rw [one_smul, IdempotentMonoid.kZeroEquiv_of] at h₁ hR hS
  rw [← h₁, ← hR, ← hS, prodEquiv_toKZero, IdempotentMonoid.map_mk, IdempotentMonoid.map_mk]
  congr <;> exact Matrix.map_one _ rfl rfl

end Prod

section Components

variable (R S : Type u) [Ring R] [Ring S]

/-- As an additive map, `TauCeti.KZero.prodEquiv` is the pair of the maps of `K₀` induced by the
two projections `R × S → R` and `R × S → S`, extension of scalars along them. -/
theorem toAddMonoidHom_prodEquiv :
    (prodEquiv R S).toAddMonoidHom =
      (map (RingHom.fst R S)).prod (map (RingHom.snd R S)) := by
  -- On the idempotent model both sides take the two components of an idempotent over `R × S`.
  refine (AddMonoidHom.cancel_right (f := (IdempotentMonoid.kZeroEquiv (R × S)).toAddMonoidHom)
    (IdempotentMonoid.kZeroEquiv (R × S)).surjective).1 <|
      GrothendieckAddGroup.addHom_ext fun x ↦ ?_
  induction x using IdempotentMonoid.ind with | mk n e he =>
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddMonoidHom.prod_apply,
    map_kZeroEquiv_of_mk]
  simp only [IdempotentMonoid.kZeroEquiv_of, prodEquiv_toKZero, IdempotentMonoid.map_mk,
    NonUnitalRingHom.coe_fst, NonUnitalRingHom.coe_snd, RingHom.coe_fst, RingHom.coe_snd]

/-- The first component of `TauCeti.KZero.prodEquiv` is the map of `K₀` induced by the first
projection `R × S → R`, extension of scalars along it. -/
theorem prodEquiv_apply_fst (x : KZero (R × S)) :
    (prodEquiv R S x).1 = map (RingHom.fst R S) x :=
  congrArg Prod.fst (DFunLike.congr_fun (toAddMonoidHom_prodEquiv R S) x)

/-- The second component of `TauCeti.KZero.prodEquiv` is the map of `K₀` induced by the second
projection `R × S → S`, extension of scalars along it. -/
theorem prodEquiv_apply_snd (x : KZero (R × S)) :
    (prodEquiv R S x).2 = map (RingHom.snd R S) x :=
  congrArg Prod.snd (DFunLike.congr_fun (toAddMonoidHom_prodEquiv R S) x)

end Components

end KZero

end TauCeti
