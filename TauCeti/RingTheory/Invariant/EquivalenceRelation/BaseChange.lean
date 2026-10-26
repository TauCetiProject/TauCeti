/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Basic
public import TauCeti.RingTheory.IsTensorProduct.EqLocus
public import TauCeti.RingTheory.IsTensorProduct.Pushout

/-!
# Base change of affine equivalence relations and their invariants

Let `s = algebraMap A B` and `t : A →+* B` give two morphisms `Spec B ⇉ Spec A`, and let `R` be a
ring of coefficients on which they agree, `t ∘ (R → A) = s ∘ (R → A)`. Base change along a map
`R → R'` replaces `A` by `A' = R' ⊗[R] A` and `B` by `B' = A' ⊗[A] B`, with first morphism
`A' → B'`; these are expressed by `Algebra.IsPushout R R' A A'` and `Algebra.IsPushout A A' B B'`,
so that localizations are allowed as well as tensor products. The second morphism is the ring
homomorphism `t' : A' →+* B'` which is `t` on `A` and the first morphism on `R'`; it exists by
`Algebra.IsPushout.liftRingHom`, and the results below take any `t'` with these two properties.

This file proves that the relation is preserved, and combines with
`TauCeti.RingTheory.IsTensorProduct.EqLocus`, which shows that its invariants are preserved.

* If `Spec B ⇉ Spec A` is an equivalence relation, so is `Spec B' ⇉ Spec A'`
  (`RingHom.IsSpecEquivRel.of_isPushout`). A point of `Spec B'` is a point of `Spec B` together
  with a compatible point of `Spec R'`, so reflexivity, symmetry and transitivity are inherited.
  When `B` is a finite projective `A`-module, so is `B'` over `A'`
  (`Module.Finite.of_isPushout`, `Module.Projective.of_isPushout`).
* If `R'` is flat over `R`, the invariants commute with base change: the ring of invariants
  `{a' : s' a' = t' a'}` of `A'` is generated over `R'` by the image of the ring of invariants
  `{a : s a = t a}` of `A` (`RingHom.eqLocus_eq_adjoin_of_isPushout`). In particular, if `R` is
  the ring of invariants of `A`, then `R'` is the ring of invariants of `A'`
  (`RingHom.eqLocus_eq_range_of_isPushout`). These hold for any pair of ring homomorphisms, and
  are proved in `TauCeti.RingTheory.IsTensorProduct.EqLocus`.

Base change along the flat maps `C → C_𝔭` from the ring of invariants `C` to its localizations
reduces the construction of the quotient of an affine scheme by a finite locally free equivalence
relation (SGA 3, Exposé V, Théorème 4.1) to the case of a local ring of invariants.

## Main results

* `RingHom.IsSpecEquivRel.of_isPushout`: an equivalence relation remains one after base change.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Finite flat groupoids, affine case*.
-/

public section

open Algebra

universe u

namespace RingHom

section EquivRel

variable {A B A' B' : Type u} {R' : Type*} [CommRing A] [CommRing B] [CommRing R'] [CommRing A']
  [CommRing B'] [Algebra A B] [Algebra R' A'] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] [IsPushout A A' B B']
  {t : A →+* B} {t' : A' →+* B'}

/-- **Base change of an equivalence relation.** If `Spec B ⇉ Spec A`, given by `s = algebraMap A B`
and `t`, is an equivalence relation, then so is its base change `Spec B' ⇉ Spec A'` along any map
`R → R'`, where `A' = R' ⊗[R] A`, `B' = A' ⊗[A] B`, and `t' : A' →+* B'` is `t` on `A` and the first
morphism on `R'`. -/
theorem IsSpecEquivRel.of_isPushout (R : Type*) [CommRing R] [Algebra R A] [Algebra R R']
    [Algebra R A'] [IsScalarTower R R' A'] [IsScalarTower R A A'] [IsPushout R R' A A']
    (h : (algebraMap A B).IsSpecEquivRel t)
    (ht₁ : t'.comp (algebraMap A A') = (algebraMap B B').comp t)
    (ht₂ : t'.comp (algebraMap R' A') = (algebraMap A' B').comp (algebraMap R' A')) :
    (algebraMap A' B').IsSpecEquivRel t' := by
  have ht₁' (a : A) : t' (algebraMap A A' a) = algebraMap B B' (t a) := congr($ht₁ a)
  have ht₂' (r : R') : t' (algebraMap R' A' r) = algebraMap A' B' (algebraMap R' A' r) :=
    congr($ht₂ r)
  have hA (a : A) : algebraMap B B' (algebraMap A B a) = algebraMap A' B' (algebraMap A A' a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  -- a ring homomorphism out of `A' = R' ⊗[R] A` is determined on `A` and on `R'`
  have extA {T : Type u} [CommRing T] {f g : A' →+* T}
      (hfA : ∀ a, f (algebraMap A A' a) = g (algebraMap A A' a))
      (hfR : ∀ r, f (algebraMap R' A' r) = g (algebraMap R' A' r)) : f = g :=
    IsPushout.ringHom_ext (R := R) (RingHom.ext hfR) (RingHom.ext hfA)
  refine ⟨fun T _ x y hs ht ↦ ?_, fun T _ u ↦ ?_, fun T _ x ↦ ?_, fun T _ x y hxy ↦ ?_⟩
  · -- a point of `Spec B' = Spec (A' ⊗[A] B)` is determined by its images in `Spec A'` and
    -- `Spec B`, and the latter is determined by its two images in `Spec A`
    refine IsPushout.ringHom_ext (R := A) hs
      (h.ext (RingHom.ext fun a ↦ ?_) (RingHom.ext fun a ↦ ?_))
    · simpa [hA] using congr($hs (algebraMap A A' a))
    · simpa [ht₁'] using congr($ht (algebraMap A A' a))
  · obtain ⟨z, hzs, hzt⟩ := h.refl (u.comp (algebraMap A A'))
    refine ⟨IsPushout.liftRingHom B' u z hzs.symm, RingHom.ext fun x ↦ by simp,
      extA (fun a ↦ ?_) (fun r ↦ by simp [ht₂'])⟩
    simpa [ht₁'] using congr($hzt a)
  · obtain ⟨z, hzs, hzt⟩ := h.symm (x.comp (algebraMap B B'))
    have hxz : (x.comp t').comp (algebraMap A A') = z.comp (algebraMap A B) :=
      RingHom.ext fun a ↦ by simpa [ht₁'] using congr($hzs a).symm
    refine ⟨IsPushout.liftRingHom B' (x.comp t') z hxz, RingHom.ext fun x ↦ by simp,
      extA (fun a ↦ ?_) (fun r ↦ by simp [ht₂'])⟩
    simpa [ht₁', hA] using congr($hzt a)
  · obtain ⟨z, hzs, hzt⟩ := h.trans (x.comp (algebraMap B B')) (y.comp (algebraMap B B'))
      (RingHom.ext fun a ↦ by simpa [ht₁', hA] using congr($hxy (algebraMap A A' a)))
    have hxz : (x.comp (algebraMap A' B')).comp (algebraMap A A') = z.comp (algebraMap A B) :=
      RingHom.ext fun a ↦ by simpa [hA] using congr($hzs a).symm
    refine ⟨IsPushout.liftRingHom B' (x.comp (algebraMap A' B')) z hxz,
      RingHom.ext fun x ↦ by simp, extA (fun a ↦ ?_) (fun r ↦ ?_)⟩
    · simpa [ht₁'] using congr($hzt a)
    · simpa [ht₂'] using congr($hxy (algebraMap R' A' r))

end EquivRel

end RingHom
