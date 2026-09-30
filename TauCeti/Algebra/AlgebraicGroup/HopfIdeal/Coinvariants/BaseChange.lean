/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flat base change of coinvariant algebras

For a closed subgroup `N` of an affine group `G`, the algebra of functions invariant under
right translation by `N` commutes with flat extension of scalars. No normality, finite-type,
or smoothness assumption is needed. This compares the candidate coordinate algebra of `G/N`
with the corresponding candidate after extending the ground field.

The proof uses Mathlib's `AlgHom.tensorEqualizerEquiv`, together with the quotient base-change
isomorphism and the formula for comultiplication on a scalar extension.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
variable {H : _root_.CommHopfAlgCat.{v} R}

noncomputable section

/-- Compare the targets of the original and base-changed coinvariance equations. -/
private def coinvariantsTensorComparison (I : HopfIdeal R H) :
    (S ⊗[R] H) ⊗[S] ((S ⊗[R] H) ⧸ (baseChangeHopfIdeal (K := S) I).toIdeal) ≃ₐ[S]
      S ⊗[R] (H ⊗[R] (H ⧸ I.toIdeal)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : (S ⊗[R] H) ≃ₐ[S] (S ⊗[R] H))
    (_root_.CommHopfAlgCat.ofIso (quotientBaseChangeIso (K := S) I)).toAlgEquiv).trans
    (TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv R S H (H ⧸ I.toIdeal)).symm

private theorem coinvariantsTensorComparison_tmul_mk (I : HopfIdeal R H)
    (s t : S) (x y : H) :
    coinvariantsTensorComparison I
        ((s ⊗ₜ[R] x) ⊗ₜ[S] Ideal.Quotient.mk (baseChangeHopfIdeal (K := S) I).toIdeal
          (t ⊗ₜ[R] y)) =
      (s * t) ⊗ₜ[R] (x ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal y) := by
  simp only [coinvariantsTensorComparison, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, BialgEquiv.coe_toAlgEquiv]
  rw [_root_.CommHopfAlgCat.ofIso_apply (quotientBaseChangeIso (K := S) I)]
  rw [quotientBaseChangeIso_hom_apply, baseChangeMap_apply_tmul, mkQuotient_apply]
  exact TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv_symm_tmul R S H
    (H ⧸ I.toIdeal) s t x (Ideal.Quotient.mk I.toIdeal y)

/-- Transport the base-changed coaction across the quotient and tensor comparisons. -/
private theorem coinvariantsTensorComparison_map_comul (I : HopfIdeal R H) (z : S ⊗[R] H) :
    coinvariantsTensorComparison I
        (Algebra.TensorProduct.map (AlgHom.id S (S ⊗[R] H))
          (Ideal.Quotient.mkₐ S (baseChangeHopfIdeal (K := S) I).toIdeal)
          (Coalgebra.comul (R := S) z)) =
      Algebra.TensorProduct.map (AlgHom.id S S)
        ((Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)).comp
          (Bialgebra.comulAlgHom R H)) z := by
  induction z with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s h =>
    simp only [TauCeti.Coalgebra.baseChange_comul_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul x y =>
      simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk]
      exact (coinvariantsTensorComparison_tmul_mk I s 1 x y).trans (by rw [mul_one])

private theorem coinvariantsTensorComparison_tmul_one (I : HopfIdeal R H) (z : S ⊗[R] H) :
    coinvariantsTensorComparison I
        (z ⊗ₜ[S] (1 : (S ⊗[R] H) ⧸ (baseChangeHopfIdeal (K := S) I).toIdeal)) =
      Algebra.TensorProduct.map (AlgHom.id S S)
        (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] (H ⧸ I.toIdeal)) z := by
  induction z with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul s h =>
    have he := coinvariantsTensorComparison_tmul_mk I s 1 h 1
    simpa only [← Algebra.TensorProduct.one_def, map_one, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeLeft_apply] using he

/-- The base-changed coinvariance equation is the scalar extension of the original equalizer. -/
private theorem coinvariants_baseChange_eq_equalizer (I : HopfIdeal R H) :
    (baseChangeHopfIdeal (K := S) I).coinvariants =
      AlgHom.equalizer
        (Algebra.TensorProduct.map (AlgHom.id S S)
          ((Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)).comp
            (Bialgebra.comulAlgHom R H)))
        (Algebra.TensorProduct.map (AlgHom.id S S)
          (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] (H ⧸ I.toIdeal))) := by
  ext z
  rw [HopfIdeal.mem_coinvariants_iff, AlgHom.mem_equalizer,
    ← (coinvariantsTensorComparison (S := S) I).injective.eq_iff,
    coinvariantsTensorComparison_map_comul, coinvariantsTensorComparison_tmul_one]

/-- Flat scalar extension commutes with taking functions invariant under a closed subgroup:
`S ⊗[R] H^{co H/I} ≃ (S ⊗[R] H)^{co (S ⊗[R] H)/I_S}`. -/
def coinvariantsBaseChangeEquiv [Module.Flat R S] (I : HopfIdeal R H) :
    S ⊗[R] I.coinvariants ≃ₐ[S] (baseChangeHopfIdeal (K := S) I).coinvariants :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (Subalgebra.equivOfEq _ _ (HopfIdeal.coinvariants_eq_equalizer I))).trans <|
  (AlgHom.tensorEqualizerEquiv S S
    ((Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)).comp
      (Bialgebra.comulAlgHom R H)) Algebra.TensorProduct.includeLeft).trans
    (Subalgebra.equivOfEq _ _ (coinvariants_baseChange_eq_equalizer I).symm)

/-- The comparison sends a tensor of invariant functions to the same tensor in the ambient
coordinate algebra. -/
@[simp]
theorem coe_coinvariantsBaseChangeEquiv [Module.Flat R S] (I : HopfIdeal R H)
    (z : S ⊗[R] I.coinvariants) :
    (coinvariantsBaseChangeEquiv I z : S ⊗[R] H) =
      Algebra.TensorProduct.map (AlgHom.id S S) I.coinvariants.val z := by
  induction z with
  | add x y hx hy => simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (· + ·) hx hy
  | tmul s h =>
    simp [coinvariantsBaseChangeEquiv, Subalgebra.equivOfEq_apply,
      AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]

/-- Including the inverse image of an invariant function recovers that function in the
ambient scalar-extended coordinate algebra. -/
@[simp]
theorem map_coinvariantsBaseChangeEquiv_symm [Module.Flat R S] (I : HopfIdeal R H)
    (z : (baseChangeHopfIdeal (K := S) I).coinvariants) :
    Algebra.TensorProduct.map (AlgHom.id S S) I.coinvariants.val
        ((coinvariantsBaseChangeEquiv I).symm z) = (z : S ⊗[R] H) := by
  rw [← coe_coinvariantsBaseChangeEquiv I, AlgEquiv.apply_symm_apply]

/-- As subalgebras of the scalar-extended coordinate ring, coinvariants commute with flat
base change. -/
@[simp]
theorem coinvariants_baseChangeHopfIdeal [Module.Flat R S] (I : HopfIdeal R H) :
    (baseChangeHopfIdeal (K := S) I).coinvariants = I.coinvariants.baseChange S := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (coinvariantsBaseChangeEquiv (S := S) I).surjective ⟨z, hz⟩
    exact ⟨x, (coe_coinvariantsBaseChangeEquiv I x).symm.trans (congrArg Subtype.val hx)⟩
  · rintro ⟨x, rfl⟩
    exact (coe_coinvariantsBaseChangeEquiv I x) ▸ (coinvariantsBaseChangeEquiv I x).property

end

end TauCeti.CommHopfAlgCat
