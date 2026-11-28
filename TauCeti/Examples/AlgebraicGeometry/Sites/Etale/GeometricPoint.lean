/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Frobenius
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Functoriality
import TauCeti.CategoryTheory.Aut.Basic
import TauCeti.FieldTheory.Galois.Complex

/-!
# Worked examples of geometric points and stalk Frobenius

This file collects concrete calculations illustrating the general theory of geometric points,
Galois actions on stalks, and the stalk Frobenius:

* **The complex point of `Spec ℝ`**: the automorphism group of `ofOver (𝟙 (Spec (.of ℝ))) ℂ` is
  `Gal(ℂ/ℝ)` (`ofOverComplexRealAutMulEquiv`), and complex conjugation acts on the two-element
  stalk of `Spec ℂ ⟶ Spec ℝ` as a fixed-point-free involution.
* **The quadratic extension `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`**: the stalk at `kbar` has cardinality `2`
  and `stalkGeometricFrobenius` exchanges its two points, coinciding with
  `stalkArithmeticFrobenius`.
* **Fifth roots of unity `μ_5` over `Spec 𝔽_2`**: the stalk at `kbar` is `rootsOfUnity 5 kbar`,
  `stalkGeometricFrobenius` acts by `ζ ↦ ζ ^ 3` (since `3 · 2 ≡ 1 [MOD 5]`),
  `stalkArithmeticFrobenius` acts by `ζ ↦ ζ ^ 2`, and the two automorphisms are distinct on this
  stalk.
* **The imperfect function field `𝔽_p(t)`**: by `isIso_algClosureToSepClosure_ratFunc_iff`, the
  morphism `algClosureToSepClosure` from `Spec (AlgebraicClosure (RatFunc (ZMod p)))` to
  `Spec (SeparableClosure (RatFunc (ZMod p)))` is not an isomorphism in `GeometricPoint`
  (`not_isIso_algClosureToSepClosure_ratFunc_zmod`); see `isIso_toPointFunctor_map` for why
  every morphism induces an isomorphism of points and stalks.
-/

public section

universe u

open CategoryTheory Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

section ComplexReal

/-- The automorphism group of the geometric point `Spec ℂ ⟶ Spec ℝ` is `Gal(ℂ/ℝ)` (with opposite
multiplication, since `Spec (σ * τ) = Spec σ ≫ Spec τ`). -/
noncomputable def ofOverComplexRealAutMulEquiv :
    Gal(ℂ/ℝ) ≃* (Aut (ofOver (𝟙 (Spec (.of ℝ))) ℂ))ᵐᵒᵖ :=
  ofOverAutMulEquiv (𝟙 (Spec (.of ℝ))) ℂ

/-- The stalk of `FiniteEtaleScheme.toSheaf` of `Spec ℂ ⟶ Spec ℝ` at `Spec ℂ` has two elements. -/
theorem natCard_specComplex_stalk :
    Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of ℝ))) ℂ).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
          ((FiniteEtaleScheme.spec (.of ℝ)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt ℝ ℂ))))) =
      2 :=
  (natCard_toSheafSpecStalk_fieldExt_eq_finrank ℝ ℂ ℂ).trans Complex.finrank_real_complex

/-- Complex conjugation has no fixed points on the stalk of `Spec ℂ ⟶ Spec ℝ` at `Spec ℂ`
(by `TauCeti.conjAe_ne_one`). -/
theorem conjAe_specComplex_stalk_ne_self
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of ℝ))) ℂ).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
        ((FiniteEtaleScheme.spec (.of ℝ)).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt ℝ ℂ))))) :
    (ofOverGaloisStalkAction (𝟙 (Spec (.of ℝ))) ℂ Complex.conjAe).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
          ((FiniteEtaleScheme.spec (.of ℝ)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt ℝ ℂ)))) z ≠
      z := by
  let B := CommAlgCat.FiniteEtale.ofSeparableFieldExt ℝ ℂ
  intro h
  let φ : ℂ →ₐ[ℝ] ℂ := toSheafSpecStalkEquiv ℝ ℂ B z
  have hφ : Complex.conjAe.toAlgHom.comp φ = (AlgHom.id ℝ ℂ).comp φ :=
    (toSheafSpecStalkEquiv_ofOverGaloisStalkAction ℝ ℂ B Complex.conjAe z).symm.trans
      ((congrArg (toSheafSpecStalkEquiv ℝ ℂ B) h).trans (AlgHom.id_comp φ).symm)
  have hsurj : Function.Surjective φ :=
    φ.toLinearMap.surjective_of_injective φ.toRingHom.injective
  have hconj : (Complex.conjAe : Gal(ℂ/ℝ)) = 1 :=
    (AlgEquiv.coe_toAlgHom_injective
      (((AlgHom.cancel_right hsurj).mp hφ).trans AlgEquiv.refl_toAlgHom.symm)).trans
      AlgEquiv.aut_one.symm
  exact TauCeti.conjAe_ne_one hconj

/-- Complex conjugation acts as an involution on the stalk of `Spec ℂ ⟶ Spec ℝ` at `Spec ℂ`. -/
theorem conjAe_specComplex_stalk_involutive :
    Function.Involutive
      ((ofOverGaloisStalkAction (𝟙 (Spec (.of ℝ))) ℂ Complex.conjAe).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
          ((FiniteEtaleScheme.spec (.of ℝ)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt ℝ ℂ))))) := by
  intro z
  rw [← ofOverGaloisStalkAction_mul_app_apply]
  have hsq : Complex.conjAe * Complex.conjAe = 1 := by
    ext x
    simp
  rw [hsq, map_one, Aut.functor_one_asIso_hom_app_apply]

end ComplexReal

section QuadraticFiniteField

variable (p : ℕ) [Fact p.Prime]
variable (kbar : Type) [Field kbar] [Algebra (ZMod p) kbar] [IsSepClosed kbar]

/-- For the quadratic extension `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`, the stalk at `kbar` has two elements. -/
theorem natCard_galoisField_two_stalk :
    Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod p)))) kbar).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt (ZMod p) (GaloisField p 2)))))) =
      2 :=
  (natCard_toSheafSpecStalk_fieldExt_eq_finrank (ZMod p) (GaloisField p 2) kbar).trans
    (GaloisField.finrank p (by decide))

/-- On the two-element stalk of `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`, `stalkGeometricFrobenius` has no fixed
points. -/
theorem stalkGeometricFrobenius_galoisField_two_ne_self
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod p)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
        ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt (ZMod p) (GaloisField p 2)))))) :
    (stalkGeometricFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt (ZMod p) (GaloisField p 2))))) z ≠
      z :=
  stalkGeometricFrobenius_ne_self_of_one_lt_finrank (ZMod p) (GaloisField p 2) kbar
    (by rw [GaloisField.finrank p (by decide)]; decide) z

/-- On the two-element stalk of `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`, `stalkGeometricFrobenius` is an
involution. -/
theorem stalkGeometricFrobenius_galoisField_two_involutive :
    Function.Involutive ((stalkGeometricFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
        ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt (ZMod p) (GaloisField p 2)))))) :=
  stalkGeometricFrobenius_involutive_of_finrank_eq_two (ZMod p) (GaloisField p 2) kbar
    (GaloisField.finrank p (by decide))

/-- On the two-element stalk of `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`, `stalkGeometricFrobenius` coincides with
`stalkArithmeticFrobenius`. -/
theorem stalkGeometricFrobenius_eq_stalkArithmeticFrobenius_galoisField_two
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod p)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
        ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
          (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt (ZMod p) (GaloisField p 2)))))) :
    (stalkGeometricFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt (ZMod p) (GaloisField p 2))))) z =
      (stalkArithmeticFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt (ZMod p) (GaloisField p 2))))) z :=
  stalkGeometricFrobenius_eq_stalkArithmeticFrobenius_of_finrank_eq_two
    (ZMod p) (GaloisField p 2) kbar (GaloisField.finrank p (by decide)) z

end QuadraticFiniteField

section FifthRootsOverF2

variable (kbar : Type) [Field kbar] [Algebra (ZMod 2) kbar] [IsSepClosed kbar]

/-- **Stalk Frobenius on `μ_5` over `Spec 𝔽_2`.** Under the identification of the stalk of the
degree-`5` Kummer cover over `1` with `rootsOfUnity 5 kbar`, `stalkGeometricFrobenius` acts by
`ζ ↦ ζ ^ 3`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkGeometricFrobenius_zmod_two_five
    (hn : IsUnit (5 : CommRingCat.of (ZMod 2)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod 2)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
        (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn))) :
    kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        hn (map_one _)
        ((stalkGeometricFrobenius (𝟙 (Spec (.of (ZMod 2)))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
            (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn)) z) =
      (kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        hn (map_one _) z) ^ 3 :=
  kummerCoverStalkEquivRootsOfUnity_stalkGeometricFrobenius_of_mul_modEq (ZMod 2) kbar
    (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn (map_one _)
    (by rw [Nat.card_zmod]; decide) z

/-- On the stalk `rootsOfUnity 5 kbar` of `μ_5` over `Spec 𝔽_2`, `stalkArithmeticFrobenius` acts
by `ζ ↦ ζ ^ 2`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkArithmeticFrobenius_zmod_two_five
    (hn : IsUnit (5 : CommRingCat.of (ZMod 2)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod 2)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
        (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn))) :
    kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        hn (map_one _)
        ((stalkArithmeticFrobenius (𝟙 (Spec (.of (ZMod 2)))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
            (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn)) z) =
      (kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        hn (map_one _) z) ^ 2 := by
  simpa [Nat.card_zmod] using
    kummerCoverStalkEquivRootsOfUnity_stalkArithmeticFrobenius (ZMod 2) kbar
      (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn (map_one _) z

/-- On `μ_5` over `Spec 𝔽_2`, `stalkGeometricFrobenius` (`ζ ↦ ζ ^ 3`) and `stalkArithmeticFrobenius`
(`ζ ↦ ζ ^ 2`) are distinct automorphisms of the stalk. -/
theorem stalkGeometricFrobenius_ne_stalkArithmeticFrobenius_zmod_two_five
    (hn : IsUnit (5 : CommRingCat.of (ZMod 2))) :
    (stalkGeometricFrobenius (𝟙 (Spec (.of (ZMod 2)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
          (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn)) ≠
      (stalkArithmeticFrobenius (𝟙 (Spec (.of (ZMod 2)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
          (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn)) := by
  intro heq
  let e := kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
    hn (map_one _)
  have hone (ζ : rootsOfUnity 5 kbar) : ζ = 1 := by
    have h32 : ζ ^ 3 = ζ ^ 2 := by
      have hstep := congrArg e (congrArg (fun g ↦ g (e.symm ζ)) heq)
      rw [kummerCoverStalkEquivRootsOfUnity_stalkGeometricFrobenius_zmod_two_five,
        kummerCoverStalkEquivRootsOfUnity_stalkArithmeticFrobenius_zmod_two_five,
        Equiv.apply_symm_apply] at hstep
      exact hstep
    have hmul : ζ ^ 2 * ζ = ζ ^ 2 * 1 := by
      calc ζ ^ 2 * ζ = ζ ^ (2 + 1) := (pow_succ ζ 2).symm
        _ = ζ ^ 3 := by norm_num
        _ = ζ ^ 2 * 1 := by rw [h32, mul_one]
    exact mul_left_cancel hmul
  let _ : Unique (rootsOfUnity 5 kbar) := ⟨⟨1⟩, hone⟩
  have hcard : Nat.card (rootsOfUnity 5 kbar) = 5 :=
    (Nat.card_congr e.symm).trans
      (natCard_kummerCoverStalk (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5 hn)
  rw [Nat.card_unique] at hcard
  exact absurd hcard (by decide)

end FifthRootsOverF2

section ImperfectFunctionField

/-- For `k = 𝔽_p(t)`, the morphism `Spec (AlgebraicClosure k) ⟶ Spec (SeparableClosure k)` over
`Spec k` is not an isomorphism in `GeometricPoint (Spec (.of (RatFunc (ZMod p))))` (though by
`isIso_toPointFunctor_map` its image under `toPointFunctor` is an isomorphism). -/
theorem not_isIso_algClosureToSepClosure_ratFunc_zmod (p : ℕ) [Fact p.Prime] :
    ¬ IsIso (algClosureToSepClosure (𝟙 (Spec (.of (RatFunc (ZMod p)))))) := by
  rw [isIso_algClosureToSepClosure_ratFunc_iff]
  intro h
  exact (Fact.out : p.Prime).ne_zero (CharP.eq (ZMod p) inferInstance (CharP.ofCharZero (ZMod p)))

end ImperfectFunctionField

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
