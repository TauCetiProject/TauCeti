/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent
public import TauCeti.RingTheory.GrothendieckRing

/-!
# Projective `K₀` of a product of rings and of the zero ring

Projective `K₀` turns finite products of rings into products of groups:

```text
K₀(R × S) ≃ K₀(R) × K₀(S).
```

The isomorphism is computed on the idempotent model of `K₀` (`TauCeti.IdempotentMonoid`). A
matrix over `R × S` is a pair of matrices of the same size over `R` and over `S`
(`Matrix.prodEquiv`), it is idempotent exactly when both components are, and two idempotents over
`R × S` are equivalent exactly when their components are
(`Matrix.idempotentEquivalent_prod_iff`). Since an idempotent can be padded by zero blocks without
changing its class, every pair of classes over `R` and over `S` comes from one idempotent over
`R × S`. So the idempotent monoid of `R × S` is the product of those of `R` and `S`, and passing
to group completions gives the isomorphism of `K₀`. It sends the class `[eRⁿ]` of an idempotent
`e` over `R × S` to the classes of its two components `e.map Prod.fst` and `e.map Prod.snd`; the
module `e.map Prod.fst` presents is the extension of scalars of `eRⁿ` along the first projection,
and similarly for the second. In particular the free module of rank one goes to the pair of free
modules of rank one.

Over the zero ring every matrix is zero, so the idempotent monoid is trivial and `K₀(0) = 0`; this
is the empty case of the product formula.

## Main definitions

* `TauCeti.IdempotentMonoid.prodEquiv A B`: the isomorphism `V(A × B) ≃+ V(A) × V(B)` of
  idempotent monoids.
* `TauCeti.KZero.prodEquiv R S`: the isomorphism `K₀(R × S) ≃+ K₀(R) × K₀(S)`.

## Main results

* `TauCeti.IdempotentMonoid.prodEquiv_mk`, `TauCeti.IdempotentMonoid.prodEquiv_symm_mk_mk`: the
  idempotent isomorphism takes components, and pairs two idempotents of the same size.
* `TauCeti.KZero.prodEquiv_kZeroEquiv_of_mk`, `TauCeti.KZero.prodEquiv_symm_kZeroEquiv_of_mk`:
  the same formulas on the classes `[eRⁿ]` in `K₀`.
* `TauCeti.KZero.prodEquiv_of_finiteProjectiveModulesRegular`: `[R × S] ↦ ([R], [S])`.
* `TauCeti.KZero.instSubsingleton`: the projective `K₀` of the zero ring is trivial, from the
  instance `Unique (TauCeti.IdempotentMonoid A)` for a trivial `A`.

## References

* C. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2: `K₀` of a finite
  product of rings is the product of the `K₀` groups, and `K₀` of the zero ring vanishes.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2, for the idempotent description.
-/

public section

noncomputable section

namespace TauCeti

open Matrix _root_.Algebra

universe u v

namespace IdempotentMonoid

/-! ### The idempotent monoid of a product -/

section Prod

variable (A B : Type*) [NonUnitalSemiring A] [NonUnitalSemiring B]

/-- Taking the two components of an idempotent matrix over `A × B`, on idempotent monoids. -/
private abbrev prodHom : IdempotentMonoid (A × B) →+ IdempotentMonoid A × IdempotentMonoid B :=
  (map (NonUnitalRingHom.fst A B)).prod (map (NonUnitalRingHom.snd A B))

variable {A B} {ι : Type*} [Fintype ι]

private theorem prodHom_mk_prodEquiv_symm {e₁ : Matrix ι ι A} {e₂ : Matrix ι ι B}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) :
    prodHom A B (mk _ (he₁.matrix_prodEquiv_symm he₂)) = (mk e₁ he₁, mk e₂ he₂) := by
  rw [AddMonoidHom.prod_apply, map_mk, map_mk]
  -- The components of the pair `(e₁, e₂)`, read through `NonUnitalRingHom.fst` and
  -- `NonUnitalRingHom.snd`.
  rfl

private theorem prodHom_injective : Function.Injective (prodHom A B) := by
  intro x y h
  induction x using ind with | mk n e he
  induction y using ind with | mk m f hf
  simp only [AddMonoidHom.prod_apply, map_mk, Prod.mk.injEq, mk_eq_mk_iff,
    NonUnitalRingHom.coe_fst, NonUnitalRingHom.coe_snd] at h
  exact (mk_eq_mk_iff he hf).2 (idempotentEquivalent_prod_iff.2 h)

private theorem prodHom_surjective : Function.Surjective (prodHom A B) := by
  rintro ⟨x, y⟩
  induction x using ind with | mk n e₁ he₁
  induction y using ind with | mk m e₂ he₂
  -- `([e₁], [e₂]) = ([e₁], 0) + (0, [e₂])`, and each summand is the image of a pair with a zero
  -- component of the same size.
  have h₀A : IsIdempotentElem (0 : Matrix (Fin m) (Fin m) A) := .zero
  have h₀B : IsIdempotentElem (0 : Matrix (Fin n) (Fin n) B) := .zero
  refine ⟨mk _ (he₁.matrix_prodEquiv_symm h₀B) + mk _ (h₀A.matrix_prodEquiv_symm he₂), ?_⟩
  rw [map_add, prodHom_mk_prodEquiv_symm he₁ h₀B, prodHom_mk_prodEquiv_symm h₀A he₂, mk_zero,
    mk_zero, Prod.mk_add_mk, add_zero, zero_add]

private theorem prodHom_bijective : Function.Bijective (prodHom A B) :=
  ⟨prodHom_injective, prodHom_surjective⟩

variable (A B) in
/-- **The idempotent monoid of a product.** `V(A × B) ≃+ V(A) × V(B)`, sending the class of an
idempotent matrix over `A × B` to the classes of its two components
(`TauCeti.IdempotentMonoid.prodEquiv_mk`). -/
def prodEquiv : IdempotentMonoid (A × B) ≃+ IdempotentMonoid A × IdempotentMonoid B :=
  AddEquiv.ofBijective (prodHom A B) prodHom_bijective

/-- `TauCeti.IdempotentMonoid.prodEquiv` sends the class of an idempotent matrix `e` over `A × B`
to the classes of its components `e.map Prod.fst` and `e.map Prod.snd`. -/
@[simp]
theorem prodEquiv_mk {e : Matrix ι ι (A × B)} (he : IsIdempotentElem e) :
    prodEquiv A B (mk e he) =
      (mk (e.map Prod.fst) (he.matrix_map (NonUnitalRingHom.fst A B)),
        mk (e.map Prod.snd) (he.matrix_map (NonUnitalRingHom.snd A B))) := by
  rw [prodEquiv, AddEquiv.ofBijective_apply, AddMonoidHom.prod_apply, map_mk, map_mk]
  -- `NonUnitalRingHom.fst A B` and `NonUnitalRingHom.snd A B` are `Prod.fst` and `Prod.snd` as
  -- functions.
  rfl

/-- The inverse of `TauCeti.IdempotentMonoid.prodEquiv` sends the classes of two idempotent
matrices `e₁` over `A` and `e₂` over `B` of the same size to the class of the matrix over `A × B`
with components `e₁` and `e₂`. -/
@[simp]
theorem prodEquiv_symm_mk_mk {e₁ : Matrix ι ι A} {e₂ : Matrix ι ι B} (he₁ : IsIdempotentElem e₁)
    (he₂ : IsIdempotentElem e₂) :
    (prodEquiv A B).symm (mk e₁ he₁, mk e₂ he₂) =
      mk ((Matrix.prodEquiv ι ι A B).symm (e₁, e₂)) (he₁.matrix_prodEquiv_symm he₂) :=
  (prodEquiv A B).symm_apply_eq.2 (prodHom_mk_prodEquiv_symm he₁ he₂).symm

end Prod

end IdempotentMonoid

namespace KZero

/-! ### Projective `K₀` of a product -/

section Prod

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/-- **`K₀` of a product of rings.** `K₀(R × S) ≃+ K₀(R) × K₀(S)`, sending the class `[eRⁿ]` of an
idempotent matrix `e` over `R × S` to the classes of its two components
(`TauCeti.KZero.prodEquiv_kZeroEquiv_of_mk`), and the free module of rank one to the pair of free
modules of rank one (`TauCeti.KZero.prodEquiv_of_finiteProjectiveModulesRegular`). -/
def prodEquiv : KZero (R × S) ≃+ KZero R × KZero S :=
  (IdempotentMonoid.kZeroEquiv (R × S)).symm.trans <|
    ((AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv (AddLocalization.addMonoidOf ⊤)
      (j := IdempotentMonoid.prodEquiv R S) (AddSubmonoid.map_equiv_top _)).trans <|
      GrothendieckAddGroup.prodEquiv.trans
        ((IdempotentMonoid.kZeroEquiv R).prodCongr (IdempotentMonoid.kZeroEquiv S))

variable {R S} {ι : Type*} [Fintype ι]

/-- `TauCeti.KZero.prodEquiv` sends the class `[eRⁿ]` of an idempotent matrix `e` over `R × S`
to the classes of its components `e.map Prod.fst` and `e.map Prod.snd`. -/
theorem prodEquiv_kZeroEquiv_of_mk {e : Matrix ι ι (R × S)} (he : IsIdempotentElem e) :
    prodEquiv R S (IdempotentMonoid.kZeroEquiv (R × S)
        (GrothendieckAddGroup.of (IdempotentMonoid.mk e he))) =
      (IdempotentMonoid.kZeroEquiv R (GrothendieckAddGroup.of
          (IdempotentMonoid.mk (e.map Prod.fst) (he.matrix_map (NonUnitalRingHom.fst R S)))),
        IdempotentMonoid.kZeroEquiv S (GrothendieckAddGroup.of
          (IdempotentMonoid.mk (e.map Prod.snd) (he.matrix_map (NonUnitalRingHom.snd R S))))) := by
  have h : (AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv (AddLocalization.addMonoidOf ⊤)
      (AddSubmonoid.map_equiv_top (IdempotentMonoid.prodEquiv R S))
        (GrothendieckAddGroup.of (IdempotentMonoid.mk e he)) =
          GrothendieckAddGroup.of (IdempotentMonoid.prodEquiv R S (IdempotentMonoid.mk e he)) :=
    AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq _ _ _
  rw [prodEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply, AddEquiv.trans_apply, h,
    IdempotentMonoid.prodEquiv_mk, AddEquiv.trans_apply, GrothendieckAddGroup.prodEquiv_of]
  -- `AddEquiv.prodCongr` acts componentwise.
  rfl

/-- The inverse of `TauCeti.KZero.prodEquiv` sends the classes `[e₁Rⁿ]` and `[e₂Sⁿ]` of two
idempotent matrices of the same size to the class of the idempotent matrix over `R × S` with
components `e₁` and `e₂`. -/
theorem prodEquiv_symm_kZeroEquiv_of_mk {e₁ : Matrix ι ι R} {e₂ : Matrix ι ι S}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) :
    (prodEquiv R S).symm
        (IdempotentMonoid.kZeroEquiv R (GrothendieckAddGroup.of (IdempotentMonoid.mk e₁ he₁)),
          IdempotentMonoid.kZeroEquiv S (GrothendieckAddGroup.of (IdempotentMonoid.mk e₂ he₂))) =
      IdempotentMonoid.kZeroEquiv (R × S) (GrothendieckAddGroup.of
        (IdempotentMonoid.mk _ (he₁.matrix_prodEquiv_symm he₂))) :=
  (prodEquiv R S).symm_apply_eq.2 <| by
    rw [prodEquiv_kZeroEquiv_of_mk]
    -- The components of the pair `(e₁, e₂)` are `e₁` and `e₂`.
    rfl

/-- `TauCeti.KZero.prodEquiv` sends the class of the free right `R × S`-module of rank one to the
classes of the free modules of rank one over `R` and over `S`. -/
theorem prodEquiv_of_finiteProjectiveModulesRegular :
    prodEquiv R S (SplitK0.of.{max u v} (finiteProjectiveModulesRegular (R × S)ᵐᵒᵖ)) =
      (SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ),
        SplitK0.of.{v} (finiteProjectiveModulesRegular Sᵐᵒᵖ)) := by
  have h₁ := IdempotentMonoid.kZeroEquiv_of_mk_one (R := R × S) 1
  rw [one_smul] at h₁
  rw [← h₁, prodEquiv_kZeroEquiv_of_mk]
  have hR := IdempotentMonoid.kZeroEquiv_of_mk_one (R := R) 1
  have hS := IdempotentMonoid.kZeroEquiv_of_mk_one (R := S) 1
  rw [one_smul] at hR hS
  rw [← hR, ← hS]
  congr <;> exact Matrix.map_one _ rfl rfl

end Prod

/-! ### The zero ring -/

/-- **`K₀` of the zero ring vanishes.** Over the zero ring every idempotent matrix is zero, so
the idempotent monoid and its group completion `K₀` are trivial. -/
instance instSubsingleton (R : Type u) [Ring R] [Subsingleton R] : Subsingleton (KZero R) :=
  (IdempotentMonoid.kZeroEquiv R).symm.injective.subsingleton

end KZero

end TauCeti
