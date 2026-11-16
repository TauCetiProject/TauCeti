/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.FixedPoints
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.RingTheory.Smooth.FixedPoints
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import TauCeti.Algebra.MonoidAlgebra.Smooth
import TauCeti.Algebra.Polynomial.Laurent.Smooth
import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Edixhoven's smoothness theorem for fixed points of affine group schemes

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let
`ρ : Θ →* CategoryTheory.Aut H` be an action of a finite group `Θ` on `H` by Hopf-algebra
automorphisms (contravariantly, a `Θ`-action on `Spec H` by group-scheme automorphisms).
The underlying ideal of the fixed-point Hopf ideal
`TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom)` is precisely the
algebraic fixed-point ideal `TauCeti.fixedPointIdeal ((autToAlgAut H).comp ρ)`
(`TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal_toIdeal_eq_fixedPointIdeal`).

Combining this identification with Edixhoven's affine fixed-point theorem
(`TauCeti.formallySmooth_quotient_fixedPointIdeal`, `TauCeti.smooth_quotient_fixedPointIdeal`)
yields **Edixhoven's smoothness theorem for affine group schemes**: if `|Θ|` is invertible in `R`
and `Spec H` is formally smooth (respectively, smooth) over `R`, then the fixed-point closed
subgroup scheme `Spec (H ⧸ fixedPointsHopfIdeal ...)` is formally smooth (respectively, smooth)
over `R`, with no Noetherian or field hypothesis
(`TauCeti.CommHopfAlgCat.formallySmooth_quotient_fixedPointsHopfIdeal`,
`TauCeti.CommHopfAlgCat.smooth_quotient_fixedPointsHopfIdeal`,
`TauCeti.FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointsHopfIdeal`, and
`TauCeti.FiniteTypeCommHopfAlgCat.smooth_fixedPoints`).

As a concrete example demonstrating both the theorem and the sharpness of its hypotheses, we
define the `ℤ/2ℤ`-action by inversion (`TauCeti.CommHopfAlgCat.inversionAction`) on any
commutative cocommutative Hopf algebra and specialize it to the multiplicative group `𝔾ₘ`:
its fixed-point subgroup scheme is canonically isomorphic to `μ₂` over every commutative ring `R`
(`TauCeti.CommHopfAlgCat.quotientFixedPointsInversionMultiplicativeGroupIso`). Hence it is smooth
over `R` if and only if `2` is a unit in `R`
(`TauCeti.CommHopfAlgCat.smooth_quotient_fixedPoints_inversion_multiplicativeGroup_iff`),
and has disconnected spectrum whenever `R` is nontrivial with `2` a unit (see
`not_connectedSpace_quotient_fixedPoints_inversion_multiplicativeGroup`),
illustrating why fixed points of a tame finite group on a connected smooth group need not remain
connected.

## Main declarations

* `TauCeti.CommHopfAlgCat.autToAlgAut`: the homomorphism from `CategoryTheory.Aut H` to
  `H ≃ₐ[R] H`.
* `TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal_toIdeal_eq_fixedPointIdeal`: the Hopf-ideal
  fixed-point ideal has the same underlying ideal as `TauCeti.fixedPointIdeal`.
* `TauCeti.CommHopfAlgCat.formallySmooth_quotient_fixedPointsHopfIdeal` and
  `TauCeti.CommHopfAlgCat.smooth_quotient_fixedPointsHopfIdeal`: Edixhoven's formal smoothness and
  smoothness theorems for `CommHopfAlgCat`.
* `TauCeti.FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointsHopfIdeal` and
  `TauCeti.FiniteTypeCommHopfAlgCat.smooth_fixedPoints`: Edixhoven's smoothness theorem for
  finite-type affine group schemes.
* `TauCeti.CommHopfAlgCat.inversionAction`: the `ℤ/2ℤ`-action by the antipode on a commutative
  cocommutative Hopf algebra.
* `TauCeti.CommHopfAlgCat.quotientFixedPointsInversionMultiplicativeGroupIso`: the fixed-point
  subgroup of inversion on `𝔾ₘ` is `μ₂`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions
  3.1 and 3.4, pp. 293–295.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom
open CategoryTheory
open scoped LaurentPolynomial

namespace TauCeti

universe u v w x

namespace CommHopfAlgCat

section General

variable {R : Type u} [CommRing R]

/-- Forget the coalgebra structure on an automorphism of a commutative Hopf algebra, yielding a
monoid homomorphism `CategoryTheory.Aut H →* (H ≃ₐ[R] H)`. -/
noncomputable def autToAlgAut (H : _root_.CommHopfAlgCat.{v} R) :
    CategoryTheory.Aut H →* (H ≃ₐ[R] H) where
  toFun e := (_root_.CommHopfAlgCat.ofIso e.asIso).toAlgEquiv
  map_one' := by
    ext x
    rfl
  map_mul' e₁ e₂ := by
    ext x
    rfl

/-- `autToAlgAut H e` acts on `H` as the underlying bialgebra homomorphism of `e`. -/
@[simp]
theorem autToAlgAut_apply (H : _root_.CommHopfAlgCat.{v} R) (e : CategoryTheory.Aut H) (x : H) :
    autToAlgAut H e x = e.asIso.hom.hom x :=
  (rfl)

variable {H : _root_.CommHopfAlgCat.{v} R} {Θ : Type w}

/-- The underlying ideal of `fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom)` coincides with the
algebraic fixed-point ideal `TauCeti.fixedPointIdeal ((autToAlgAut H).comp ρ)`. -/
theorem fixedPointsHopfIdeal_toIdeal_eq_fixedPointIdeal [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) :
    (fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom)).toIdeal =
      TauCeti.fixedPointIdeal ((autToAlgAut H).comp ρ) := by
  rw [fixedPointsHopfIdeal_toIdeal, TauCeti.fixedPointIdeal_eq_iSup]
  refine iSup_congr fun θ ↦ ?_
  rw [HopfIdeal.equalizerIdeal_eq_span]
  rfl

/-- If `H` is of finite type over `R` and `Θ` is a finite monoid acting on `H` by Hopf-algebra
automorphisms, then the underlying ideal of the fixed-point Hopf ideal is finitely generated, over
any base ring `R`. -/
theorem fixedPointsHopfIdeal_toIdeal_fg [Algebra.FiniteType R H] [Monoid Θ] [Finite Θ]
    (ρ : Θ →* CategoryTheory.Aut H) :
    (fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom)).toIdeal.FG := by
  rw [fixedPointsHopfIdeal_toIdeal_eq_fixedPointIdeal]
  exact TauCeti.fixedPointIdeal_fg ((autToAlgAut H).comp ρ)

/-- **Edixhoven's formal smoothness theorem for affine group schemes**: if `H` is formally smooth
over `R` and `Θ` is a finite group of order invertible in `R` acting on `H` by Hopf-algebra
automorphisms, then the fixed-point quotient `quotient H (fixedPointsHopfIdeal ...)` is formally
smooth over `R`. -/
theorem formallySmooth_quotient_fixedPointsHopfIdeal [Algebra.FormallySmooth R H]
    [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    Algebra.FormallySmooth R (quotient H (fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom))) := by
  have _ : Algebra.FormallySmooth R (H ⧸ TauCeti.fixedPointIdeal ((autToAlgAut H).comp ρ)) :=
    TauCeti.formallySmooth_quotient_fixedPointIdeal ((autToAlgAut H).comp ρ) hΘ
  exact Algebra.FormallySmooth.of_equiv
    (Ideal.quotientEquivAlgOfEq R (fixedPointsHopfIdeal_toIdeal_eq_fixedPointIdeal ρ)).symm

/-- **Edixhoven's smoothness theorem for affine group schemes**: if `H` is smooth over `R` and `Θ`
is a finite group of order invertible in `R` acting on `H` by Hopf-algebra automorphisms, then the
fixed-point quotient `quotient H (fixedPointsHopfIdeal ...)` is smooth over `R`. -/
theorem smooth_quotient_fixedPointsHopfIdeal [Algebra.Smooth R H]
    [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    Algebra.Smooth R (quotient H (fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom))) := by
  have _ : Algebra.Smooth R (H ⧸ TauCeti.fixedPointIdeal ((autToAlgAut H).comp ρ)) :=
    TauCeti.smooth_quotient_fixedPointIdeal ((autToAlgAut H).comp ρ) hΘ
  exact Algebra.Smooth.of_equiv
    (Ideal.quotientEquivAlgOfEq R (fixedPointsHopfIdeal_toIdeal_eq_fixedPointIdeal ρ)).symm

/-- Object-property form of `smooth_quotient_fixedPointsHopfIdeal`. -/
theorem smoothCommHopfAlgProperty_quotient_fixedPointsHopfIdeal
    (H : _root_.CommHopfAlgCat.{v} R) (hH : smoothCommHopfAlgProperty R H)
    [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R
      (quotient H (fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom))) := by
  let _ : Algebra.Smooth R H := (smoothCommHopfAlgProperty_iff H).mp hH
  exact (smoothCommHopfAlgProperty_iff _).mpr (smooth_quotient_fixedPointsHopfIdeal ρ hΘ)

end General

section Inversion

variable {R : Type u} [CommRing R]

/-- The `ℤ/2ℤ`-action by the antipode on a commutative cocommutative Hopf algebra `H`.
Contravariantly, this is the inversion involution `g ↦ g⁻¹` on a commutative affine group scheme.
-/
noncomputable def inversionAction (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    Multiplicative (ZMod 2) →* CategoryTheory.Aut H :=
  let antipodeHom : H ⟶ H := _root_.CommHopfAlgCat.ofHom (HopfAlgebra.antipodeBialgHom (R := R))
  have hcomp : antipodeHom ≫ antipodeHom = 𝟙 H := by
    ext x
    simp [antipodeHom]
  let antipodeAut : CategoryTheory.Aut H :=
    CategoryTheory.Aut.of ⟨antipodeHom, antipodeHom, hcomp, hcomp⟩
  (zmodMonoidHomEquiv 2 (CategoryTheory.Aut H)).symm ⟨antipodeAut, by
    rw [sq]
    ext x
    simp [antipodeAut, antipodeHom]⟩

/-- The generator of `ℤ/2ℤ` acts via `inversionAction H` by the antipode. -/
@[simp]
theorem inversionAction_ofAdd_one (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    (inversionAction H (Multiplicative.ofAdd (1 : ZMod 2))).asIso.hom =
      _root_.CommHopfAlgCat.ofHom (HopfAlgebra.antipodeBialgHom (R := R) (A := H)) := by
  rw [inversionAction, zmodMonoidHomEquiv_symm_apply_ofAdd_one]

/-- The inversion fixed points of `𝔾ₘ = Spec R[T; T⁻¹]` are canonically isomorphic to
`μ₂ = Spec R[ℤ/2ℤ]` over every commutative ring `R`. -/
noncomputable def quotientFixedPointsInversionMultiplicativeGroupIso (R : Type u) [CommRing R] :
    quotient (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
      (fixedPointsHopfIdeal fun θ ↦
        (inversionAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom) ≅
      _root_.CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative (ZMod 2))) :=
  let Gm := _root_.CommHopfAlgCat.of R R[T;T⁻¹]
  let Mu2 := _root_.CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative (ZMod 2)))
  let g : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)
  have hg_sq : g * g = 1 := by decide
  have hcases : ∀ θ : Multiplicative (ZMod 2), θ = 1 ∨ θ = g := by decide
  let ζ : (MonoidAlgebra R (Multiplicative (ZMod 2)))ˣ :=
    { val := MonoidAlgebra.single g (1 : R)
      inv := MonoidAlgebra.single g (1 : R)
      val_inv := by rw [MonoidAlgebra.single_mul_single, hg_sq, mul_one, MonoidAlgebra.one_def]
      inv_val := by rw [MonoidAlgebra.single_mul_single, hg_sq, mul_one, MonoidAlgebra.one_def] }
  let toMu2Alg : R[T;T⁻¹] →ₐ[R] MonoidAlgebra R (Multiplicative (ZMod 2)) := laurentEval ζ
  let toMu2 : Gm ⟶ Mu2 := _root_.CommHopfAlgCat.ofHom <|
    BialgHom.ofAlgHom toMu2Alg
      (by
        exact (laurentEval_unique (1 : Rˣ) _ (by simp [toMu2Alg, ζ])).trans
          (laurentEval_unique (1 : Rˣ) _ (by simp)).symm)
      (by
        have hζu : IsUnit (ζ.val ⊗ₜ[R] ζ.val) :=
          ⟨⟨ζ.val ⊗ₜ[R] ζ.val, ζ.inv ⊗ₜ[R] ζ.inv,
            by simp [Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.one_def],
            by simp [Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.one_def]⟩, rfl⟩
        have h1 : ((Bialgebra.comulAlgHom R (MonoidAlgebra R (Multiplicative (ZMod 2)))).comp
            toMu2Alg) = laurentEval hζu.unit := by
          apply laurentEval_unique
          simp [toMu2Alg, ζ]
        have h2 : ((Algebra.TensorProduct.map toMu2Alg toMu2Alg).comp
            (Bialgebra.comulAlgHom R R[T;T⁻¹])) = laurentEval hζu.unit := by
          apply laurentEval_unique
          simp [toMu2Alg, ζ, LaurentPolynomial.comul_T]
        exact h2.trans h1.symm)
  have htoMu2_inv :
      ∀ θ : Multiplicative (ZMod 2), (inversionAction Gm θ).asIso.hom ≫ toMu2 = toMu2 := by
    intro θ
    rcases hcases θ with rfl | rfl
    · simp
    · apply _root_.CommHopfAlgCat.hom_ext
      apply BialgHom.coe_toAlgHom_injective
      have h1 : (toMu2Alg.comp (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹])).toAlgHom) =
          laurentEval ζ := by
        apply laurentEval_unique
        simp [toMu2Alg, LaurentPolynomial.antipode_T, ζ]
      have h2 : ((inversionAction Gm g).asIso.hom ≫ toMu2).hom.toAlgHom =
          toMu2Alg.comp (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹])).toAlgHom := by
        rw [inversionAction_ofAdd_one]
        rfl
      exact h2.trans h1
  let I := fixedPointsHopfIdeal fun θ ↦ (inversionAction Gm θ).asIso.hom
  let hom : quotient Gm I ⟶ Mu2 := liftFixedPoints toMu2 htoMu2_inv
  let q : Gm ⟶ quotient Gm I := mkQuotient Gm I
  let t : quotient Gm I := q.hom (LaurentPolynomial.T 1)
  have ht_sq : t * t = 1 := by
    have hinv : q.hom (LaurentPolynomial.T (-1)) = t := by
      have hq := congrArg (fun m : Gm ⟶ quotient Gm I ↦ m.hom (LaurentPolynomial.T 1))
        (comp_mkQuotient_fixedPointsHopfIdeal (fun θ ↦ (inversionAction Gm θ).asIso.hom) g)
      rw [inversionAction_ofAdd_one] at hq
      have hanti :
          (_root_.CommHopfAlgCat.ofHom
            (HopfAlgebra.antipodeBialgHom (R := R) (A := Gm))).hom (LaurentPolynomial.T 1) =
            LaurentPolynomial.T (-1) :=
        (HopfAlgebra.antipodeBialgHom_apply _).trans (LaurentPolynomial.antipode_T 1)
      rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply, hanti] at hq
      exact hq
    calc t * t
      _ = q.hom (LaurentPolynomial.T (-1)) * q.hom (LaurentPolynomial.T 1) := by rw [hinv]
      _ = q.hom (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) := (map_mul q.hom _ _).symm
      _ = 1 := by rw [← LaurentPolynomial.T_add]; simp
  let tUnit : (quotient Gm I)ˣ := ⟨t, t, ht_sq, ht_sq⟩
  let φ : Multiplicative (ZMod 2) →* quotient Gm I :=
    (Units.coeHom (quotient Gm I)).comp
      ((zmodMonoidHomEquiv 2 (quotient Gm I)ˣ).symm ⟨tUnit, by
        ext
        simpa [sq, tUnit] using ht_sq⟩)
  have hφ_g : φ g = t := by
    dsimp only [φ, g]
    rw [MonoidHom.comp_apply, zmodMonoidHomEquiv_symm_apply_ofAdd_one]
    rfl
  let invAlg : MonoidAlgebra R (Multiplicative (ZMod 2)) →ₐ[R] quotient Gm I :=
    MonoidAlgebra.lift R (quotient Gm I) (Multiplicative (ZMod 2)) φ
  have hgl : ∀ θ : Multiplicative (ZMod 2), IsGroupLikeElem R (φ θ) := by
    intro θ
    rcases hcases θ with rfl | rfl
    · simp [isGroupLikeElem_iff, Algebra.TensorProduct.one_def]
    · have hT : IsGroupLikeElem R (LaurentPolynomial.T 1 : R[T;T⁻¹]) :=
        MultiplicativeGroup.groupLikeT_val R ▸
          (MultiplicativeGroup.groupLikeT R).isGroupLikeElem_val
      rw [hφ_g]
      exact hT.map q.hom
  let inv : Mu2 ⟶ quotient Gm I := _root_.CommHopfAlgCat.ofHom <|
    BialgHom.ofAlgHom invAlg
      (by
        refine MonoidAlgebra.algHom_ext (fun θ ↦ ?_) (Subsingleton.elim _ _)
        simp [invAlg, (hgl θ).counit_eq_one])
      (by
        refine MonoidAlgebra.algHom_ext (fun θ ↦ ?_) (Subsingleton.elim _ _)
        simp [invAlg, (hgl θ).comul_eq_tmul_self])
  { hom := hom
    inv := inv
    hom_inv_id := by
      apply mkQuotient_hom_ext
      rw [Category.comp_id, ← Category.assoc, mkQuotient_comp_liftFixedPoints]
      apply _root_.CommHopfAlgCat.hom_ext
      apply BialgHom.coe_toAlgHom_injective
      have h1 : (toMu2 ≫ inv).hom.toAlgHom = laurentEval tUnit := by
        apply laurentEval_unique
        calc (toMu2 ≫ inv).hom.toAlgHom (LaurentPolynomial.T 1)
          _ = invAlg (toMu2Alg (LaurentPolynomial.T 1)) := rfl
          _ = invAlg (MonoidAlgebra.single g (1 : R)) := by rw [laurentEval_T, zpow_one]
          _ = (1 : R) • φ g := MonoidAlgebra.lift_single φ g (1 : R)
          _ = tUnit.val := by rw [one_smul, hφ_g]
      have h2 : q.hom.toAlgHom = laurentEval tUnit := by
        apply laurentEval_unique
        simp [t, tUnit]
      exact h1.trans h2.symm
    inv_hom_id := by
      apply _root_.CommHopfAlgCat.hom_ext
      apply BialgHom.coe_toAlgHom_injective
      refine MonoidAlgebra.algHom_ext (fun θ ↦ ?_) (Subsingleton.elim _ _)
      rcases hcases θ with rfl | rfl
      · simp [inv, invAlg, ← MonoidAlgebra.one_def]
      · have hhom_t : hom.hom t = MonoidAlgebra.single g (1 : R) := by
          have h := congrArg (fun m : Gm ⟶ Mu2 ↦ m.hom (LaurentPolynomial.T 1))
            (mkQuotient_comp_liftFixedPoints toMu2 htoMu2_inv)
          rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at h
          exact h.trans ((laurentEval_T ζ 1).trans (by simp [ζ]))
        simpa [inv, invAlg, MonoidAlgebra.lift_single, hφ_g] using hhom_t }

/-- When `2` is a unit in `R`, the fixed-point quotient of inversion on `𝔾ₘ` is smooth over `R`.
-/
theorem smooth_quotient_fixedPoints_inversion_multiplicativeGroup (R : Type u) [CommRing R]
    (h2 : IsUnit (2 : R)) :
    Algebra.Smooth R
      (quotient (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (fixedPointsHopfIdeal fun θ ↦
          (inversionAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom)) := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2))).trans
      (Nat.card_zmod 2)
  exact smooth_quotient_fixedPointsHopfIdeal
    (inversionAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]))
    (by simpa only [hcard, Nat.cast_ofNat] using h2)

/-- **Sharpness of the tameness hypothesis**: over any commutative ring `R`, the fixed-point
quotient of inversion on `𝔾ₘ` (which is `μ₂`) is smooth over `R` if and only if `2` is a unit in
`R`. -/
theorem smooth_quotient_fixedPoints_inversion_multiplicativeGroup_iff
    (R : Type u) [CommRing R] :
    Algebra.Smooth R
      (quotient (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (fixedPointsHopfIdeal fun θ ↦
          (inversionAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom)) ↔
      IsUnit (2 : R) := by
  refine ⟨fun hs ↦ ?_, smooth_quotient_fixedPoints_inversion_multiplicativeGroup R⟩
  by_contra h2
  have hne : Ideal.span {(2 : R)} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ : m.IsMaximal := hm
  let k := R ⧸ m
  let _ : Field k := Ideal.Quotient.field m
  have _ : Algebra.Smooth R (MonoidAlgebra R (Multiplicative (ZMod 2))) :=
    Algebra.Smooth.of_equiv
      (_root_.CommHopfAlgCat.ofIso
        (quotientFixedPointsInversionMultiplicativeGroupIso R)).toAlgEquiv
  have hmu2 : Algebra.Smooth k (MonoidAlgebra k (Multiplicative (ZMod 2))) :=
    Algebra.Smooth.of_equiv
      (MonoidAlgebra.scalarTensorEquiv (R := R) (A := k) (M := Multiplicative (ZMod 2)))
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2))).trans
      (Nat.card_zmod 2)
  have hu : IsUnit (2 : k) := by
    have h := (MonoidAlgebra.smooth_iff_isUnit_card k (Multiplicative (ZMod 2))).mp hmu2
    simpa only [hcard, Nat.cast_ofNat] using h
  have h0 : (2 : k) = 0 := by
    rw [← map_ofNat (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
    exact hle (Ideal.subset_span (Set.mem_singleton _))
  exact hu.ne_zero h0

/-- **Disconnectedness of tame fixed points**: over any nontrivial commutative ring `R` in which
`2` is a unit, the fixed-point quotient of inversion on the connected smooth group `𝔾ₘ` has
disconnected spectrum (it is `μ₂`, which splits via the nontrivial idempotent `(1 + g) / 2`). -/
theorem not_connectedSpace_quotient_fixedPoints_inversion_multiplicativeGroup
    (R : Type u) [CommRing R] [Nontrivial R] (h2 : IsUnit (2 : R)) :
    ¬ ConnectedSpace (PrimeSpectrum
      (quotient (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (fixedPointsHopfIdeal fun θ ↦
          (inversionAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom))) := by
  intro hconn
  let _ : ConnectedSpace _ := hconn
  let g : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)
  have hg_ne : g ≠ 1 := by decide
  have hg_sq : g * g = 1 := by decide
  let e : MonoidAlgebra R (Multiplicative (ZMod 2)) :=
    (↑h2.unit⁻¹ : R) • (1 + MonoidAlgebra.single g (1 : R))
  have h2inv : (↑h2.unit⁻¹ : R) * (2 : R) = 1 :=
    calc (↑h2.unit⁻¹ : R) * 2
      _ = ↑h2.unit⁻¹ * ↑h2.unit := by rw [h2.unit_spec]
      _ = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have he_idem : IsIdempotentElem e := by
    have hmul : (1 + MonoidAlgebra.single g (1 : R)) * (1 + MonoidAlgebra.single g (1 : R)) =
        (2 : R) • (1 + MonoidAlgebra.single g (1 : R)) := by
      simp only [add_mul, mul_add, one_mul, mul_one, MonoidAlgebra.single_mul_single, hg_sq,
        ← MonoidAlgebra.one_def, two_smul]
      abel
    rw [IsIdempotentElem]
    dsimp only [e]
    rw [smul_mul_smul_comm, hmul, smul_smul, mul_assoc, h2inv, mul_one]
  have he_ne_zero : e ≠ 0 := by
    intro h0
    have hcoeff := congrArg (fun x : MonoidAlgebra R (Multiplicative (ZMod 2)) ↦ x.coeff 1) h0
    simp [e, hg_ne.symm] at hcoeff
  have he_ne_one : e ≠ 1 := by
    intro h1
    have hcoeff := congrArg (fun x : MonoidAlgebra R (Multiplicative (ZMod 2)) ↦ x.coeff g) h1
    simp [e, MonoidAlgebra.one_def, hg_ne.symm] at hcoeff
  let eqv :=
    (_root_.CommHopfAlgCat.ofIso (quotientFixedPointsInversionMultiplicativeGroupIso R)).toAlgEquiv
  have hback : IsIdempotentElem (eqv.symm e) := he_idem.map eqv.symm.toRingHom
  rcases hback.eq_zero_or_eq_one_of_preconnectedSpace with h0 | h1
  · exact he_ne_zero (eqv.symm.injective (h0.trans (map_zero eqv.symm).symm))
  · exact he_ne_one (eqv.symm.injective (h1.trans (map_one eqv.symm).symm))

end Inversion

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- **Edixhoven's smoothness theorem for finite-type affine group schemes** (canonical quotient
form): if `H` is a smooth finite-type commutative Hopf algebra over `R` and `Θ` is a finite group
of order invertible in `R` acting on `H` by automorphisms, then the fixed-point quotient
`quotient H (fixedPointsHopfIdeal ...)` is smooth over `R`. -/
theorem smoothCommHopfAlgProperty_quotient_fixedPointsHopfIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, v} R) (hH : smoothCommHopfAlgProperty R H.obj)
    {Θ : Type w} [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R
      (quotient H (fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom))).obj := by
  let ρ' : Θ →* CategoryTheory.Aut H.obj :=
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).mapAut H).comp ρ
  exact CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointsHopfIdeal H.obj hH ρ' hΘ

/-- **Edixhoven's smoothness theorem for finite-type affine group schemes**: fixed points of a
finite group of invertible order acting on a smooth finite-type affine group scheme are represented
by a smooth closed subgroup scheme (Edixhoven, Props. 3.1 and 3.4, pp. 293–295). -/
theorem smooth_fixedPoints
    (H : FiniteTypeCommHopfAlgCat.{u, v} R) (hH : smoothCommHopfAlgProperty R H.obj)
    (Θ : Type w) [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : R)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} R) (f : H ⟶ H'),
      smoothCommHopfAlgProperty R H'.obj ∧ Function.Surjective f.hom.hom ∧
      ∀ (A : Type x) [CommRing A] [Algebra R A],
        Set.range (BialgHom.mapDomain (A := A) (f.hom.hom : (H : Type v) →ₐc[R] H')) =
          {g | ∀ θ : Θ,
            BialgHom.mapDomain (A := A) ((ρ θ).asIso.hom.hom.hom : (H : Type v) →ₐc[R] H) g = g} :=
  ⟨quotient H (fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom)),
    mkQuotient H (fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom)),
    smoothCommHopfAlgProperty_quotient_fixedPointsHopfIdeal H hH ρ hΘ,
    CommHopfAlgCat.mkQuotient_surjective H.obj _,
    fun A _ _ ↦ range_mapDomain_mkQuotient_fixedPointsHopfIdeal (fun θ ↦ (ρ θ).asIso.hom) A⟩

end FiniteTypeCommHopfAlgCat

end TauCeti
