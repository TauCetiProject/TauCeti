/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Coprime
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Devissage
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Formula
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Induced
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.ModularInduction

/-!
# Tate's local Euler characteristic formula

For a finite smooth discrete Galois module over a finite compatible extension `F` of `ℚ_p`,
Tate's formula identifies the local Euler characteristic with the normalized absolute value
of the coefficient order. Its cardinality form is
`#H¹ = #H⁰ · #H² · p ^ ([F : ℚ_p] v_p(#A))`; for `𝔽_p` coefficients this becomes
`dim H¹ = dim H⁰ + dim H² + [F : ℚ_p] dim A`.

The formula follows by dévissage to prime coefficients and modular Artin induction, followed
by Shapiro's lemma and the formula for a quotient of order prime to the coefficient prime.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
  (7.3.1)–(7.3.4).
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory

variable (p : ℕ) [Fact p.Prime]
  (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- **Tate's local Euler characteristic formula.** The Euler characteristic of a finite smooth
discrete Galois module equals the normalized absolute value of its order. -/
theorem localEulerCharacteristic_eq_localCardNorm (n : ℕ) [NeZero n]
    (A : GalRep n F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] :
    localEulerCharacteristic
      (have := FinitePadicExtension.charZero F p; Nat.cast_ne_zero.2 (NeZero.ne n)) A =
        localCardNorm p A := by
  have := FinitePadicExtension.charZero F p
  refine localEulerCharacteristic_eq_localCardNorm_of_forall_prime p (fun ℓ _ B _ _ ↦ ?_) n A
  have := (Fact.out : IsSmoothDiscrete (ZMod ℓ) B).discreteTopology
  refine localEulerCharacteristic_eq_localCardNorm_of_indFDRep p F ℓ (fun V C hC D ↦ ?_) B
  let L := shapiroField F V C
  let σ := shapiroFieldEmbedding F V C
  have hσ := range_absoluteGaloisGroupExtend_shapiroFieldEmbedding F V C
  -- Install the compatible local-field structures on the fixed field, without giving its
  -- algebraic closure an ambient topology or valuation.
  let _ := finiteIntermediateFieldValuativeRel F (AlgebraicClosure F) L
  let _ := finiteIntermediateFieldTopology F (AlgebraicClosure F) L
  have := finiteIntermediateField_isNonarchimedeanLocalField F (AlgebraicClosure F) L
  have := finiteIntermediateField_valuativeExtension F (AlgebraicClosure F) L
  have : Module.Finite ℚ_[p] L := Module.Finite.trans F L
  have : ValuativeExtension ℚ_[p] L := ValuativeExtension.trans ℚ_[p] F L
  let D' := (forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj D
  have : Finite D' := Module.finite_of_finite (ZMod ℓ)
  let E := shapiroGalRep σ ℓ hσ D'
  let f : Field.absoluteGaloisGroup L →* C :=
    ((QuotientGroup.mk' V.toSubgroup).subgroupComap C).comp
      (absoluteGaloisGroupExtendEquiv F L σ hσ : Field.absoluteGaloisGroup L →* _)
  have hf : Continuous f :=
    ((QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _).comp
      (absoluteGaloisGroupExtendEquiv F L σ hσ).continuous_toFun
  -- This open kernel acts trivially, and its index divides the order of the coprime group C.
  let N : OpenNormalSubgroup (Field.absoluteGaloisGroup L) :=
    ⟨⟨f.ker, hf.isOpen_preimage _ (isOpen_discrete _)⟩, inferInstance⟩
  have hN : N.toSubgroup.index.Coprime ℓ := by
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hC.2).symm.of_dvd_left
      (Subgroup.index_ker f ▸ f.range.card_subgroup_dvd_card)
  have hE := localEulerCharacteristic_eq_localCardNorm_of_index_coprime p E N hN
    (fun g hg x ↦ (shapiroGalRepLinearEquiv σ ℓ hσ D').injective (by
      rw [shapiroGalRepLinearEquiv_ρ_apply]
      have hfg : f g = 1 := hg
      exact (congrArg (fun c ↦ D'.ρ c ((shapiroGalRepLinearEquiv σ ℓ hσ D') x))
        hfg).trans (by simp)))
  -- Compare the small induced carrier with Mathlib induction, then transport both invariants
  -- through Shapiro to the coprime formula over L.
  let e := eqToIso (fdGalRepOfQuotient_obj ℓ F V (indFDRep D)) ≪≫
    (galRepOfQuotient ℓ F V).mapIso (indFDRepForgetIso D)
  exact (localEulerCharacteristic_congr _ e).trans
    ((localEulerCharacteristic_galRepOfQuotient_ind σ ℓ hσ D'
      (Nat.cast_ne_zero.2 (NeZero.ne ℓ))).trans
      (hE.trans ((localCardNorm_galRepOfQuotient_ind σ ℓ hσ D' p).symm.trans
        (localCardNorm_congr p e).symm)))

/-- **Cardinality form of Tate's local Euler characteristic formula.** For a finite smooth
discrete module, `#H¹ = #H⁰ · #H² · p ^ ([F : ℚ_p] v_p(#A))`. -/
theorem eulerCharacteristic_mixed (n : ℕ) (hn : n ≠ 0)
    (A : GalRep n F) (hA : Finite A.V) [Fact (IsSmoothDiscrete (ZMod n) A)] :
    Nat.card (continuousCohomology 1 A) =
      Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
      p ^ (Module.finrank ℚ_[p] F * padicValNat p (Nat.card A.V)) := by
  have := FinitePadicExtension.charZero F p
  have : NeZero n := ⟨hn⟩
  exact natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm
    p n A (localEulerCharacteristic_eq_localCardNorm p F n A)

/-- **Dimension form of Tate's local Euler characteristic formula.** For a finite smooth
discrete `𝔽_p`-module, `dim H¹ = dim H⁰ + dim H² + [F : ℚ_p] dim A`. -/
theorem eulerCharacteristic_finrank_fp (A : GalRep p F) (hA : Finite A.V)
    [Fact (IsSmoothDiscrete (ZMod p) A)] :
    Module.finrank (ZMod p) (continuousCohomology 1 A) =
      Module.finrank (ZMod p) (continuousCohomology 0 A) +
        Module.finrank (ZMod p) (continuousCohomology 2 A) +
        Module.finrank ℚ_[p] F * Module.finrank (ZMod p) A.V := by
  have := FinitePadicExtension.charZero F p
  exact finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm
    p A (localEulerCharacteristic_eq_localCardNorm p F p A)

end TauCeti.ClassFieldTheory
