/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Dynamic Levi subgroups are cocharacter centralizers

The dynamic Levi of a cocharacter is the scheme-theoretic centralizer of that cocharacter.
Its defining Hopf ideal, obtained by intersecting the two opposite dynamic parabolics,
agrees with the coefficient ideal defining the centralizer of the multiplicative group.
The equality retains the full closed subgroup scheme structure, including infinitesimals.

The comparison uses all commutative value algebras, including nonreduced ones, and requires
neither an injective cocharacter nor smoothness or finite type. Centralizer calculations can
therefore be used for the represented dynamic Levi without comparing their defining equations
again.

The Laurent and group-algebra presentations of the multiplicative group are identified by
Mathlib's `AddMonoidAlgebra.toMultiplicativeBialgEquiv`. The two central inputs are the
universal-point criterion for the centralizer and the generic-conjugation definition of
the dynamic Levi.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open WithConv

namespace BialgHom

open TauCeti TauCeti.Cocharacter

universe u v w

variable {R : Type u} {H : Type v} {A : Type w} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing A] [Algebra R A]

/-- Killing the scheme-theoretic centralizer ideal of a cocharacter is equivalent to
membership in its dynamic Levi, including over nonreduced value algebras. -/
theorem centralizerHopfIdeal_toMultiplicative_comp_le_ker_iff
    (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] A)) :
    (centralizerHopfIdeal
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)).toIdeal ≤
        RingHom.ker g.ofConv ↔ g ∈ levi A l := by
  let e := AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ
  constructor
  · intro hg
    let t : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] LaurentPolynomial A) :=
      toConv ((laurentEval (R := R) (LaurentPolynomial.genericUnit A)).comp
        e.symm.toAlgEquiv.toAlgHom)
    have ht : mapDomain (e.toBialgHom.comp l) t = genericPoint A l := by
      rw [genericPoint_eq_pointsHom, pointsHom_apply]
      ext h
      simp [t, mapDomain_apply]
    have hc := commute_mapValue_mapDomain_of_centralizerHopfIdeal_le_ker
      (e.toBialgHom.comp l) hg
      (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) t
    have hconst : AlgHom.mapValue (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) g =
        Cocharacter.constPoint A g := by
      rw [constPoint_apply, AlgHom.mapValue_apply]
    rw [ht, hconst] at hc
    rw [mem_levi_iff, conjugate_apply]
    exact (mul_inv_eq_iff_eq_mul).mpr hc.symm.eq
  · intro hg
    rw [centralizerHopfIdeal_le_ker_iff]
    intro B _ _ φ t
    have hvalue : mapDomain (e.toBialgHom.comp l) t =
        pointsHom B l (laurentEvalEquiv.symm (t.ofConv.comp e.toAlgEquiv.toAlgHom)) := by
      rw [pointsHom_apply, laurentEval_laurentEvalEquiv_symm]
      ext h
      simp [mapDomain_apply]
    rw [hvalue]
    exact commute_pointsHom_of_mem_levi l (levi_le_comap φ hg) _

/-- **Dynamic Levi subgroups are scheme-theoretic centralizers.** The intersection of the
opposite dynamic parabolics is cut out by the centralizer ideal of the cocharacter.
No injectivity, finite-type or smoothness hypothesis on the cocharacter or group is needed. -/
theorem leviDefiningHopfIdeal_eq_centralizerHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) :
    leviDefiningHopfIdeal l = centralizerHopfIdeal
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l) := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
    (H := _root_.CommHopfAlgCat.of R H)
  intro A
  ext g
  rw [quotientPointsSubgroup_leviDefiningHopfIdeal,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  rw [← centralizerHopfIdeal_toMultiplicative_comp_le_ker_iff]
  exact ⟨fun h x hx ↦ h (HopfIdeal.mem_toIdeal.mp hx),
    fun h x hx ↦ h x (HopfIdeal.mem_toIdeal.mpr hx)⟩

end BialgHom
