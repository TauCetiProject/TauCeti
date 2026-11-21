/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Frobenius
public import TauCeti.FieldTheory.RatFunc.PowerTower

/-!
# Worked examples of geometric points and stalk Frobenius

This file collects concrete calculations illustrating the general theory of geometric points,
Galois actions on stalks, and the stalk Frobenius:

* **The complex point of `Spec ℝ`**: the automorphism group of `ofOver (𝟙 (Spec (.of ℝ))) ℂ` is
  `Gal(ℂ/ℝ)` (`galComplexRealMulEquivAutOp`), and complex conjugation acts on the two-element stalk
  of `Spec ℂ ⟶ Spec ℝ` as a fixed-point-free involution.
* **The quadratic extension `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`**: the stalk at `kbar` has cardinality `2`
  and `stalkFrobenius` exchanges its two points, coinciding with `stalkArithmeticFrobenius`.
* **Fifth roots of unity `μ_5` over `Spec 𝔽_2`**: the stalk at `kbar` is `rootsOfUnity 5 kbar`,
  `stalkFrobenius` acts by `ζ ↦ ζ ^ 3` (since `3 · 2 ≡ 1 [MOD 5]`), `stalkArithmeticFrobenius`
  acts by `ζ ↦ ζ ^ 2`, and the two automorphisms are distinct on this stalk.
* **Rational function fields `K(X)`**: the morphism `ofSepToAlgClosure` from
  `Spec (AlgebraicClosure (RatFunc K))` to `Spec (SeparableClosure (RatFunc K))` is an isomorphism
  in `GeometricPoint` if and only if `CharZero K` (in particular, it is not an isomorphism for
  `𝔽_p(t)`), yet always induces an isomorphism of points and stalks via `isIso_toPointFunctor_map`.
-/

public section

universe u

open CategoryTheory Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

section ComplexReal

/-- The automorphism group of the geometric point `Spec ℂ ⟶ Spec ℝ` is `Gal(ℂ/ℝ)` (with opposite
multiplication, since `Spec (σ * τ) = Spec σ ≫ Spec τ`). -/
noncomputable def galComplexRealMulEquivAutOp :
    Gal(ℂ/ℝ) ≃* (Aut (ofOver (𝟙 (Spec (.of ℝ))) ℂ))ᵐᵒᵖ :=
  galMulEquivAutOp (𝟙 (Spec (.of ℝ))) ℂ

/-- The stalk of `FiniteEtaleScheme.toSheaf` of `Spec ℂ ⟶ Spec ℝ` at `Spec ℂ` has two elements. -/
theorem natCard_specComplex_stalk :
    Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of ℝ))) ℂ).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
          ((FiniteEtaleScheme.spec (.of ℝ)).obj (op (finiteEtaleOfSeparableFieldExt ℝ ℂ))))) =
      2 :=
  (natCard_toSheafSpecStalk_fieldExt_eq_finrank ℝ ℂ ℂ).trans Complex.finrank_real_complex

/-- Complex conjugation has no fixed points on the stalk of `Spec ℂ ⟶ Spec ℝ` at `Spec ℂ`. -/
theorem conjAe_specComplex_stalk_ne_self
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of ℝ))) ℂ).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
        ((FiniteEtaleScheme.spec (.of ℝ)).obj (op (finiteEtaleOfSeparableFieldExt ℝ ℂ))))) :
    (galStalkAut (𝟙 (Spec (.of ℝ))) ℂ Complex.conjAe).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
          ((FiniteEtaleScheme.spec (.of ℝ)).obj (op (finiteEtaleOfSeparableFieldExt ℝ ℂ)))) z ≠
      z := by
  let B := finiteEtaleOfSeparableFieldExt ℝ ℂ
  intro h
  let φ : ℂ →ₐ[ℝ] ℂ := toSheafSpecStalkEquiv ℝ ℂ B z
  have hφ : φ = Complex.conjAe.toAlgHom.comp φ :=
    (congrArg (toSheafSpecStalkEquiv ℝ ℂ B) h).symm.trans
      (toSheafSpecStalkEquiv_galStalkAut ℝ ℂ B Complex.conjAe z)
  have hv := DFunLike.congr_fun hφ Complex.I
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Complex.conjAe_coe] at hv
  rcases Complex.real_algHom_eq_id_or_conj φ with hid | hconj
  · have hI : Complex.I = -Complex.I := by simpa [hid, Complex.conj_I] using hv
    exact absurd (congrArg Complex.im hI) (by norm_num)
  · have hI : -Complex.I = Complex.I := by simpa [hconj, Complex.conj_I] using hv
    exact absurd (congrArg Complex.im hI) (by norm_num)

/-- Complex conjugation acts as an involution on the stalk of `Spec ℂ ⟶ Spec ℝ` at `Spec ℂ`. -/
theorem conjAe_specComplex_stalk_involutive
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of ℝ))) ℂ).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
        ((FiniteEtaleScheme.spec (.of ℝ)).obj (op (finiteEtaleOfSeparableFieldExt ℝ ℂ))))) :
    (galStalkAut (𝟙 (Spec (.of ℝ))) ℂ Complex.conjAe).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
          ((FiniteEtaleScheme.spec (.of ℝ)).obj (op (finiteEtaleOfSeparableFieldExt ℝ ℂ))))
        ((galStalkAut (𝟙 (Spec (.of ℝ))) ℂ Complex.conjAe).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of ℝ))).obj
            ((FiniteEtaleScheme.spec (.of ℝ)).obj (op (finiteEtaleOfSeparableFieldExt ℝ ℂ)))) z) =
      z := by
  rw [← galStalkAut_mul_app_apply]
  have hsq : Complex.conjAe * Complex.conjAe = 1 := by
    ext x
    simp
  rw [hsq, map_one]
  rfl

end ComplexReal

section QuadraticFiniteField

variable (p : ℕ) [Fact p.Prime]
variable (kbar : Type) [Field kbar] [Algebra (ZMod p) kbar] [IsSepClosed kbar]

/-- For the quadratic extension `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`, the stalk at `kbar` has two elements. -/
theorem natCard_galoisField_two_stalk :
    Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod p)))) kbar).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2)))))) =
      2 :=
  (natCard_toSheafSpecStalk_fieldExt_eq_finrank (ZMod p) (GaloisField p 2) kbar).trans
    (GaloisField.finrank p (by decide))

variable [Algebra.IsAlgebraic (ZMod p) kbar]

/-- On the two-element stalk of `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`, `stalkFrobenius` has no fixed points. -/
theorem stalkFrobenius_galoisField_two_ne_self
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod p)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
        ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
          (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2)))))) :
    (stalkFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2))))) z ≠ z :=
  stalkFrobenius_ne_self_of_one_lt_finrank (ZMod p) (GaloisField p 2) kbar
    (by rw [GaloisField.finrank p (by decide)]; decide) z

/-- On the two-element stalk of `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`, `stalkFrobenius` is an involution. -/
theorem stalkFrobenius_galoisField_two_involutive
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod p)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
        ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
          (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2)))))) :
    (stalkFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2)))))
        ((stalkFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
            ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
              (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2))))) z) = z :=
  stalkFrobenius_involutive_of_finrank_eq_two (ZMod p) (GaloisField p 2) kbar
    (GaloisField.finrank p (by decide)) z

/-- On the two-element stalk of `Spec 𝔽_{p²} ⟶ Spec 𝔽_p`, `stalkFrobenius` coincides with
`stalkArithmeticFrobenius`. -/
theorem stalkFrobenius_eq_stalkArithmeticFrobenius_galoisField_two
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod p)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
        ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
          (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2)))))) :
    (stalkFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2))))) z =
      (stalkArithmeticFrobenius (𝟙 (Spec (.of (ZMod p)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod p)))).obj
          ((FiniteEtaleScheme.spec (.of (ZMod p))).obj
            (op (finiteEtaleOfSeparableFieldExt (ZMod p) (GaloisField p 2))))) z :=
  stalkFrobenius_eq_stalkArithmeticFrobenius_of_finrank_eq_two (ZMod p) (GaloisField p 2) kbar
    (GaloisField.finrank p (by decide)) z

end QuadraticFiniteField

section FifthRootsOverF2

variable (kbar : Type) [Field kbar] [Algebra (ZMod 2) kbar] [Algebra.IsAlgebraic (ZMod 2) kbar]
  [IsSepClosed kbar]

/-- `5` is a unit in `ZMod 2`. -/
theorem isUnit_five_zmod_two : IsUnit (5 : CommRingCat.of (ZMod 2)) :=
  isUnit_iff_ne_zero.mpr (by decide)

/-- **Stalk Frobenius on `μ_5` over `Spec 𝔽_2`.** Under the identification of the stalk of the
degree-`5` Kummer cover over `1` with `rootsOfUnity 5 kbar`, `stalkFrobenius` acts by
`ζ ↦ ζ ^ 3`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkFrobenius_zmod_two_five
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod 2)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
        (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5 isUnit_five_zmod_two))) :
    kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        isUnit_five_zmod_two (map_one _)
        ((stalkFrobenius (𝟙 (Spec (.of (ZMod 2)))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
            (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5
              isUnit_five_zmod_two)) z) =
      (kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        isUnit_five_zmod_two (map_one _) z) ^ 3 :=
  kummerCoverStalkEquivRootsOfUnity_stalkFrobenius_of_mul_modEq (ZMod 2) kbar
    (1 : (CommRingCat.of (ZMod 2))ˣ) 5 isUnit_five_zmod_two (map_one _)
    (by rw [Nat.card_zmod]; decide) z

/-- On the stalk `rootsOfUnity 5 kbar` of `μ_5` over `Spec 𝔽_2`, `stalkArithmeticFrobenius` acts
by `ζ ↦ ζ ^ 2`. -/
theorem kummerCoverStalkEquivRootsOfUnity_stalkArithmeticFrobenius_zmod_two_five
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of (ZMod 2)))) kbar).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
        (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5 isUnit_five_zmod_two))) :
    kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        isUnit_five_zmod_two (map_one _)
        ((stalkArithmeticFrobenius (𝟙 (Spec (.of (ZMod 2)))) kbar).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
            (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5
              isUnit_five_zmod_two)) z) =
      (kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        isUnit_five_zmod_two (map_one _) z) ^ 2 := by
  simpa [Nat.card_zmod] using
    kummerCoverStalkEquivRootsOfUnity_stalkArithmeticFrobenius (ZMod 2) kbar
      (1 : (CommRingCat.of (ZMod 2))ˣ) 5 isUnit_five_zmod_two (map_one _) z

/-- On `μ_5` over `Spec 𝔽_2`, `stalkFrobenius` (`ζ ↦ ζ ^ 3`) and `stalkArithmeticFrobenius`
(`ζ ↦ ζ ^ 2`) are distinct automorphisms of the stalk. -/
theorem stalkFrobenius_ne_stalkArithmeticFrobenius_zmod_two_five :
    (stalkFrobenius (𝟙 (Spec (.of (ZMod 2)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
          (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5
            isUnit_five_zmod_two)) ≠
      (stalkArithmeticFrobenius (𝟙 (Spec (.of (ZMod 2)))) kbar).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of (ZMod 2)))).obj
          (FiniteEtaleScheme.kummerCover (1 : (CommRingCat.of (ZMod 2))ˣ) 5
            isUnit_five_zmod_two)) := by
  intro heq
  let e := kummerCoverStalkEquivRootsOfUnity (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
    isUnit_five_zmod_two (map_one _)
  have hone (ζ : rootsOfUnity 5 kbar) : ζ = 1 := by
    have h32 : ζ ^ 3 = ζ ^ 2 := by
      have hstep := congrArg e (congrArg (fun g ↦ g (e.symm ζ)) heq)
      rw [kummerCoverStalkEquivRootsOfUnity_stalkFrobenius_zmod_two_five,
        kummerCoverStalkEquivRootsOfUnity_stalkArithmeticFrobenius_zmod_two_five,
        Equiv.apply_symm_apply] at hstep
      exact hstep
    exact mul_left_cancel (a := ζ ^ 2) (by rw [← pow_succ, mul_one, h32])
  let _ : Unique (rootsOfUnity 5 kbar) := ⟨⟨1⟩, hone⟩
  have hcard : Nat.card (rootsOfUnity 5 kbar) = 5 :=
    (Nat.card_congr e.symm).trans
      (natCard_kummerCoverStalk (ZMod 2) kbar (1 : (CommRingCat.of (ZMod 2))ˣ) 5
        isUnit_five_zmod_two)
  rw [Nat.card_unique] at hcard
  exact absurd hcard (by decide)

end FifthRootsOverF2

section ImperfectFunctionField

/-- For any field `K` and any `a : Spec (.of (RatFunc K)) ⟶ S`, the morphism `ofSepToAlgClosure a`
is an isomorphism in `GeometricPoint S` if and only if `K` has characteristic zero (whereas
`(toPointFunctor S).map (ofSepToAlgClosure a)` is always an isomorphism by
`isIso_toPointFunctor_map`). -/
theorem isIso_ofSepToAlgClosure_ratFunc_iff {S : Scheme.{u}} {K : Type u} [Field K]
    (a : Spec (.of (RatFunc K)) ⟶ S) :
    IsIso (ofSepToAlgClosure a) ↔ CharZero K :=
  (isIso_ofSepToAlgClosure_iff_perfectField a).trans (TauCeti.RatFunc.perfectField_iff_charZero K)

/-- For `k = 𝔽_p(t)`, the morphism `Spec (AlgebraicClosure k) ⟶ Spec (SeparableClosure k)` over
`Spec k` is not an isomorphism in `GeometricPoint (Spec (.of (RatFunc (ZMod p))))`, while it
induces an isomorphism of points and stalks. -/
theorem not_isIso_ofSepToAlgClosure_ratFunc_zmod (p : ℕ) [Fact p.Prime] :
    ¬ IsIso (ofSepToAlgClosure (𝟙 (Spec (.of (RatFunc (ZMod p)))))) := by
  rw [isIso_ofSepToAlgClosure_ratFunc_iff]
  intro h
  exact (Fact.out : p.Prime).ne_zero (CharP.eq (ZMod p) inferInstance (CharP.ofCharZero (ZMod p)))

end ImperfectFunctionField

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
