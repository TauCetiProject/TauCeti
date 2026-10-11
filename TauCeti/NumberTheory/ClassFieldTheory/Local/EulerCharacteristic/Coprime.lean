/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.DegreeTwo
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Kummer.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Kummer.Invariants
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Shapiro
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Invariants

/-!
# Tate's local Euler characteristic formula, prime-to-`ℓ` case

Let `F/ℚ_p` be finite, `ℓ` a prime, and `A` a finite smooth discrete `ZMod ℓ`-representation of
`G_F` on which an open normal subgroup of index prime to `ℓ` acts trivially. This file proves
Tate's formula `χ_F(A) = φ_F(A)` for such `A`
(`localEulerCharacteristic_eq_localCardNorm_of_index_coprime`):

```text
#H⁰(F, A) · #H²(F, A) / #H¹(F, A) = ‖#A‖_F.
```

This is the case of the formula to which the modular Artin theorem and Shapiro's lemma reduce the
general one (`localEulerCharacteristic_eq_localCardNorm_of_indFDRep`).

Shrink the subgroup to an open normal `W` that also fixes `μ_ℓ`, with index still prime to `ℓ`
(`exists_openNormalSubgroup_le_muNRep_ρ_eq_self_of_coprime`), and write `A`, and `μ_ℓ` as `M`, as
inflations of representations of `G = G_F ⧸ W`. Then, by the coprime index,

* `dim H⁰(F, A) = dim Aᴳ` (`finrank_continuousCohomology_zero_fdGalRepOfQuotient`);
* `dim H¹(F, A) = dim (H¹(W, 𝔽_ℓ) ⊗ A)ᴳ`
  (`finrank_continuousCohomology_one_fdGalRepOfQuotient`);
* `dim H²(F, A) = dim (M^∨ ⊗ A)ᴳ` (`finrank_continuousCohomology_two_fdGalRepOfQuotient`).

Equivariant Kummer theory computes the middle term at the fixed field `L` of `W`:
`dim (H¹(W, 𝔽_ℓ) ⊗ A)ᴳ = dim (M^∨ ⊗ A)ᴳ + dim Aᴳ + [ℓ = p] [F : ℚ_p] dim A`
(`finrank_invariants_kummerH1FiniteRepresentation_tprod_of_isUnit` and
`finrank_invariants_kummerH1FiniteRepresentation_tprod_of_finitePadicExtension`, stated for
`Gal(L/F)` and read here through `G ≃* Gal(L/F)`). Comparing with `‖ℓ‖_F`, which is `1` for
`ℓ ≠ p` and `p^{-[F : ℚ_p]}` for `ℓ = p`, gives `χ_F(A) = φ_F(A)`.

## Main results

* `TauCeti.ClassFieldTheory.finrank_continuousCohomology_zero_fdGalRepOfQuotient`:
  `dim H⁰(F, A) = dim Aᴳ` for an inflated representation.
* `TauCeti.ClassFieldTheory.finrank_continuousCohomology_one_fdGalRepOfQuotient`:
  `dim H¹(F, A) = dim (H¹(W, 𝔽_ℓ) ⊗ A)ᴳ` for an inflated representation, `W` of index prime to
  `ℓ`.
* `TauCeti.ClassFieldTheory.localEulerCharacteristic_eq_localCardNorm_of_index_coprime`:
  `χ_F(A) = φ_F(A)` when an open normal subgroup of index prime to `ℓ` acts trivially on `A`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
* The statement and the outline of its proof are adapted from split 6 of the pull-request split
  plan in `LOOKAHEAD.md` on the Tau Ceti lookahead branch
  `lookahead/ClassFieldTheory/euler-characteristic-mixed` of `roed-math/TauCeti`, commit
  `217e838c7c3ccfe5f1c3874537459b0527c37625`.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology Module

attribute [local instance] trivialZModAction

local instance {n : ℕ} {H : Type*} [Monoid H] [TopologicalSpace H] :
    ContinuousSMul H (ZMod n) := ⟨continuous_snd⟩

section Transport

variable {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L]
  [Normal F L] (σ : L →ₐ[F] SeparableClosure F)
  {W : OpenNormalSubgroup (Field.absoluteGaloisGroup F)}
  (hW : (absoluteGaloisGroupExtend F L σ).range = W.toSubgroup) (n : ℕ)

/-- The finite-layer conjugation representation on `H¹(Gal(Fˢ/σ(L)), ℤ/n)`, read through
`G_F ⧸ W ≃* Gal(L/F)`, is the conjugation representation on `H¹(W, ℤ/n)`. -/
private def kummerH1FiniteRepresentationEquiv :
    Representation.Equiv ((kummerH1FiniteRepresentation σ n).comp
        (absoluteGaloisGroupExtendQuotientEquiv F L σ hW).toMonoidHom)
      (h1ConjRepresentation (p := n) (G := Field.absoluteGaloisGroup F) (N := W.toSubgroup)) :=
  .mk ((restrictSubgroupH1Equiv σ n hW).toLinearEquiv (ZMod.map_smul _)) fun q ↦ by
    induction q using QuotientGroup.induction_on with | H g => ?_
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, absoluteGaloisGroupExtendQuotientEquiv_mk,
      kummerH1FiniteRepresentation_restrictNormalHom, AddEquiv.coe_toLinearEquiv,
      h1ConjRepresentation_quotient_mk_apply, explicitConj1_apply_eq_smul]
    exact restrictSubgroupH1Equiv_smul σ n hW g x

/-- The finite-layer roots-of-unity representation, read through `G_F ⧸ W ≃* Gal(L/F)`, is a
representation `M` of `G_F ⧸ W` inflating to `μₙ`. -/
private def kummerCoeffFiniteRepresentationEquiv (hn : IsUnit (n : F))
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ W.toSubgroup)}
    (e : (fdGalRepOfQuotient n F W).obj M ≅ muNRep n F) :
    Representation.Equiv ((kummerCoeffFiniteRepresentation σ n
        (smul_kummerCoeff_eq_self_of_mem_fixingSubgroup σ hn hW e)).comp
      (absoluteGaloisGroupExtendQuotientEquiv F L σ hW).toMonoidHom) M.ρ :=
  let e' := eqToIso (fdGalRepOfQuotient_obj n F W M).symm ≪≫ e
  Representation.Equiv.symm <| Representation.Equiv.mk (((
      { toFun := fun x ↦ e'.hom.hom x
        invFun := fun x ↦ e'.inv.hom x
        left_inv := e'.hom_inv_id_apply
        right_inv := e'.inv_hom_id_apply
        map_add' := map_add e'.hom.hom } : M ≃+ (muNRep n F).V).trans
        (kummerCoeffEquivMuNRep n F).symm).toLinearEquiv (ZMod.map_smul _)) fun q ↦ by
    induction q using QuotientGroup.induction_on with | H g => ?_
    refine LinearMap.ext fun m ↦ (kummerCoeffEquivMuNRep n F).injective ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      AddEquiv.coe_toLinearEquiv, AddEquiv.trans_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, absoluteGaloisGroupExtendQuotientEquiv_mk,
      kummerCoeffFiniteRepresentation_restrictNormalHom, kummerCoeffEquivMuNRep_smul,
      AddEquiv.apply_symm_apply]
    -- The inflated action of `g` is that of its class on the underlying representation of `M`.
    exact (congrArg e'.hom.hom ((galRepOfQuotient_ρ_apply n F W _ g m).trans
      (LinearMap.congr_fun (DFunLike.congr_fun (FDRep.forget₂_ρ M) _) m)).symm).trans
        (TopRep.hom_comm_apply e'.hom g m)

end Transport

section Arithmetic

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharZero F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- `χ_F = φ_F` from the dimension count `dim H¹ = dim H⁰ + dim H² + c dim A`, when
`‖ℓ‖_F = ℓ⁻ᶜ`. -/
private theorem localEulerCharacteristic_eq_localCardNorm_of_finrank {ℓ : ℕ} [Fact ℓ.Prime]
    (A : GalRep ℓ F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod ℓ) A)] (c : ℕ)
    (hc : padicNorm p ℓ ^ Module.finrank ℚ_[p] F = ((ℓ : ℚ) ^ c)⁻¹)
    (h : finrank (ZMod ℓ) (continuousCohomology 1 A) =
      finrank (ZMod ℓ) (continuousCohomology 0 A) + finrank (ZMod ℓ) (continuousCohomology 2 A) +
        c * finrank (ZMod ℓ) A.V) :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne ℓ)) A = localCardNorm p A := by
  have hℓ : (ℓ : F) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne ℓ)
  have : Finite (continuousCohomology 0 A) := finite_H hℓ A Fact.out (by omega)
  have : Finite (continuousCohomology 1 A) := finite_H hℓ A Fact.out (by omega)
  have : Finite (continuousCohomology 2 A) := finite_H hℓ A Fact.out (by omega)
  have : Module.Finite (ZMod ℓ) A.V := Module.Finite.of_finite
  have : Module.Finite (ZMod ℓ) (continuousCohomology 0 A) := Module.Finite.of_finite
  have : Module.Finite (ZMod ℓ) (continuousCohomology 1 A) := Module.Finite.of_finite
  have : Module.Finite (ZMod ℓ) (continuousCohomology 2 A) := Module.Finite.of_finite
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne ℓ)
  apply Subtype.ext
  apply Units.ext
  simp only [localEulerCharacteristic_coe, localCardNorm_coe]
  rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := continuousCohomology 0 A),
    Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := continuousCohomology 1 A),
    Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := continuousCohomology 2 A),
    Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := A.V), Nat.card_zmod, h]
  push_cast
  rw [IsAbsoluteValue.abv_pow (padicNorm p), pow_right_comm, hc, inv_pow, ← pow_mul, pow_add,
    pow_add]
  field_simp

end Arithmetic

section Inflation

variable {F : Type} [Field F] {W : OpenNormalSubgroup (Field.absoluteGaloisGroup F)} {ℓ : ℕ}

/-- **`dim H⁰(F, A) = dim Aᴳ` for an inflated representation**: `H⁰` is the module of invariants
(`ContinuousCohomology.zeroIso`), and an element is fixed by `G_F` exactly when it is fixed by
its quotient `G = G_F ⧸ W`. -/
theorem finrank_continuousCohomology_zero_fdGalRepOfQuotient [Fact ℓ.Prime]
    (A : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ W.toSubgroup)) :
    finrank (ZMod ℓ) (continuousCohomology 0 ((fdGalRepOfQuotient ℓ F W).obj A)) =
      finrank (ZMod ℓ) (Representation.invariants A.ρ) := by
  have hcard : Nat.card (continuousCohomology 0 ((fdGalRepOfQuotient ℓ F W).obj A)) =
      Nat.card (Representation.invariants A.ρ) := by
    rw [fdGalRepOfQuotient_obj]
    refine Nat.card_congr ((ContinuousCohomology.zeroIso _).toContinuousLinearEquiv.toEquiv.trans
      (Equiv.subtypeEquivRight fun x ↦ ?_))
    -- The inflated action of `g` is that of its class, and every class lifts to `G_F`.
    have hρ (g : Field.absoluteGaloisGroup F) :
        ((galRepOfQuotient ℓ F W).obj ((forget₂ (FDRep (ZMod ℓ) _) (Rep (ZMod ℓ) _)).obj A)).ρ g x =
          A.ρ g x :=
      (galRepOfQuotient_ρ_apply ℓ F W _ g x).trans
        (LinearMap.congr_fun (DFunLike.congr_fun (FDRep.forget₂_ρ A) _) x)
    simp only [ContRepresentation.mem_invariants, hρ]
    exact ⟨fun h q ↦ QuotientGroup.induction_on q h, fun h g ↦ h g⟩
  have : Finite (Representation.invariants A.ρ) := Module.finite_of_finite (ZMod ℓ)
  have : Finite (continuousCohomology 0 ((fdGalRepOfQuotient ℓ F W).obj A)) :=
    Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have : Module.Finite (ZMod ℓ) (continuousCohomology 0 ((fdGalRepOfQuotient ℓ F W).obj A)) :=
    Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ),
    Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := Representation.invariants A.ρ),
    Nat.card_zmod] at hcard
  exact Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le hcard

/-- **`dim H¹(F, A) = dim (H¹(W, 𝔽_ℓ) ⊗ A)ᴳ` for an inflated representation**, when the index of
`W` is prime to `ℓ`: restriction to `W` identifies `H¹(F, A)` with the `G`-invariants of
`H¹(W, A) = H¹(W, 𝔽_ℓ) ⊗ A` (`finrank_H1_eq_finrank_representationInvariants`), `G = G_F ⧸ W`
acting on `H¹(W, 𝔽_ℓ)` by conjugation. -/
theorem finrank_continuousCohomology_one_fdGalRepOfQuotient [Fact ℓ.Prime]
    (hW : W.toSubgroup.index.Coprime ℓ)
    (A : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ W.toSubgroup)) :
    finrank (ZMod ℓ) (continuousCohomology 1 ((fdGalRepOfQuotient ℓ F W).obj A)) =
      finrank (ZMod ℓ) (Representation.invariants
        (V := TensorProduct (ZMod ℓ) (H1 W.toSubgroup (ZMod ℓ)) A)
        ((h1ConjRepresentation (p := ℓ) (G := Field.absoluteGaloisGroup F)
          (N := W.toSubgroup)).tprod A.ρ)) := by
  have hℓ : ℓ.Prime := Fact.out
  have : W.toSubgroup.FiniteIndex :=
    ⟨fun h ↦ hℓ.one_lt.ne' (Nat.coprime_zero_left ℓ |>.1 (h ▸ hW))⟩
  rw [fdGalRepOfQuotient_obj]
  let X := (galRepOfQuotient ℓ F W).obj
    ((forget₂ (FDRep (ZMod ℓ) _) (Rep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ W.toSubgroup))).obj A)
  let _ := TopRep.distribMulAction X
  have : ContinuousSMul (Field.absoluteGaloisGroup F) X.V :=
    (isSmoothDiscrete_galRepOfQuotient ℓ F W _).continuousSMul
  have : Finite X.V := Module.finite_of_finite (ZMod ℓ) (M := A)
  -- The inflated action of `g` is that of its class on the underlying representation of `A`.
  have hρ (g : Field.absoluteGaloisGroup F) (a : X.V) : A.ρ g a = g • a :=
    ((galRepOfQuotient_ρ_apply ℓ F W _ g a).trans
      (LinearMap.congr_fun (DFunLike.congr_fun (FDRep.forget₂_ρ A) _) a)).symm
  have : Module.Finite (ZMod ℓ) X.V := Module.Finite.of_finite
  let ρ : Representation (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ W.toSubgroup) X.V := A.ρ
  have h1 := finrank_H1_eq_finrank_representationInvariants (A := X.V) (p := ℓ)
    (fun n a ↦ galRepOfQuotient_ρ_eq_self ℓ F W _ n.2 a) W.isOpen hW ρ hρ
  calc finrank (ZMod ℓ) (continuousCohomology 1 X)
      _ = finrank (ZMod ℓ) (H1 (Field.absoluteGaloisGroup F) X.V) :=
        ((TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete X).toLinearEquiv
          (ZMod.map_smul _)).finrank_eq.symm
      _ = _ := h1
      -- `ρ` is `A.ρ` read on the same underlying module.
      _ = _ := rfl

end Inflation

section Count

variable {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L]
  [Normal F L] (σ : L →ₐ[F] SeparableClosure F)
  {W : OpenNormalSubgroup (Field.absoluteGaloisGroup F)}
  (hW : (absoluteGaloisGroupExtend F L σ).range = W.toSubgroup) {ℓ : ℕ} [Fact ℓ.Prime]
  (hℓ : IsUnit (ℓ : F)) {M : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ W.toSubgroup)}
  (e : (fdGalRepOfQuotient ℓ F W).obj M ≅ muNRep ℓ F)

/-- A count of first-cohomology invariants at the finite Galois layer `Gal(L/F)` gives the same
count for the quotient `G_F ⧸ W`, through `G_F ⧸ W ≃* Gal(L/F)`. -/
private theorem finrank_invariants_h1ConjRepresentation_tprod_of_forall (c : ℕ)
    (h : ∀ A' : FDRep (ZMod ℓ) Gal(L/F),
      finrank (ZMod ℓ) (Representation.invariants
          (V := TensorProduct (ZMod ℓ) (H1 σ.fieldRange.fixingSubgroup (ZMod ℓ)) A')
          ((kummerH1FiniteRepresentation σ ℓ).tprod A'.ρ)) =
        finrank (ZMod ℓ) (Representation.invariants
            (V := TensorProduct (ZMod ℓ) (Module.Dual (ZMod ℓ) (KummerCoeff F ℓ)) A')
            ((kummerCoeffFiniteRepresentation σ ℓ
              (smul_kummerCoeff_eq_self_of_mem_fixingSubgroup σ hℓ hW e)).dual.tprod A'.ρ)) +
          finrank (ZMod ℓ) (Representation.invariants A'.ρ) + c * finrank (ZMod ℓ) A')
    (A : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ W.toSubgroup)) :
    finrank (ZMod ℓ) (Representation.invariants
        (V := TensorProduct (ZMod ℓ) (H1 W.toSubgroup (ZMod ℓ)) A)
        ((h1ConjRepresentation (p := ℓ) (G := Field.absoluteGaloisGroup F)
          (N := W.toSubgroup)).tprod A.ρ)) =
      finrank (ZMod ℓ) (Representation.invariants
          (V := TensorProduct (ZMod ℓ) (Module.Dual (ZMod ℓ) M) A)
          ((Representation.dual M.ρ).tprod A.ρ)) +
        finrank (ZMod ℓ) (Representation.invariants A.ρ) + c * finrank (ZMod ℓ) A := by
  let φ := absoluteGaloisGroupExtendQuotientEquiv F L σ hW
  let A' : FDRep (ZMod ℓ) Gal(L/F) := FDRep.of (A.ρ.comp φ.symm.toMonoidHom)
  let eA : Representation.Equiv (A'.ρ.comp φ.toMonoidHom) A.ρ :=
    .mk (LinearEquiv.refl _ _) fun g ↦ by ext; simp [A']
  -- The dual of a restriction is the restriction of the dual, `φ` being a homomorphism.
  let eμ : Representation.Equiv ((kummerCoeffFiniteRepresentation σ ℓ
      (smul_kummerCoeff_eq_self_of_mem_fixingSubgroup σ hℓ hW e)).dual.comp φ.toMonoidHom)
        (Representation.dual M.ρ) :=
    (Representation.Equiv.mk (LinearEquiv.refl _ _) fun g ↦ by
      ext; simp [Representation.dual_apply, φ]).trans
      (kummerCoeffFiniteRepresentationEquiv σ hW ℓ hℓ e).dual
  have hH := Representation.finrank_invariants_tprod_of_comp φ.surjective
    (kummerH1FiniteRepresentationEquiv σ hW ℓ) eA
  have hμ := Representation.finrank_invariants_tprod_of_comp φ.surjective eμ eA
  have hA : Representation.invariants A'.ρ = Representation.invariants A.ρ :=
    Representation.invariants_comp_of_surjective A.ρ φ.symm.toMonoidHom φ.symm.surjective
  rw [← hH, h A', hμ, hA]

end Count

section Main

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharZero F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- `χ_F = φ_F` for the inflation of a representation of `G_F ⧸ W`, when `W` has index prime to
`ℓ` and fixes `μ_ℓ`. -/
private theorem localEulerCharacteristic_fdGalRepOfQuotient_eq_localCardNorm {ℓ : ℕ}
    [Fact ℓ.Prime] {W : OpenNormalSubgroup (Field.absoluteGaloisGroup F)}
    (hW : W.toSubgroup.index.Coprime ℓ)
    (hWμ : ∀ g ∈ W, ∀ x : (muNRep ℓ F).V, (muNRep ℓ F).ρ g x = x)
    (A : FDRep (ZMod ℓ) (Field.absoluteGaloisGroup F ⧸ W.toSubgroup)) :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne ℓ))
        ((fdGalRepOfQuotient ℓ F W).obj A) =
      localCardNorm p ((fdGalRepOfQuotient ℓ F W).obj A) := by
  have hℓ : IsUnit (ℓ : F) := (Nat.cast_ne_zero.2 (NeZero.ne ℓ)).isUnit
  obtain ⟨M, ⟨e⟩⟩ := exists_fdGalRepOfQuotient_iso_muNRep hℓ hWμ
  -- The fixed field `L` of `W`: a finite Galois extension of `F` with `G_L = W`.
  let L := shapiroField F W ⊥
  let σ := shapiroFieldEmbedding F W ⊥
  have hσ : (absoluteGaloisGroupExtend F L σ).range = W.toSubgroup := by
    rw [range_absoluteGaloisGroupExtend_shapiroFieldEmbedding, MonoidHom.comap_bot,
      QuotientGroup.ker_mk']
  let _ : ValuativeRel L := finiteIntermediateFieldValuativeRel F (AlgebraicClosure F) L
  let _ : TopologicalSpace L := finiteIntermediateFieldTopology F (AlgebraicClosure F) L
  have : IsNonarchimedeanLocalField L :=
    finiteIntermediateField_isNonarchimedeanLocalField F (AlgebraicClosure F) L
  have : ValuativeExtension F L :=
    finiteIntermediateField_valuativeExtension F (AlgebraicClosure F) L
  -- `L` is a finite extension of `ℚ_p` (`FinitePadicExtension.ofInstances`).
  have : Module.Finite ℚ_[p] L := Module.Finite.trans F L
  have : ValuativeExtension ℚ_[p] L := ValuativeExtension.trans ℚ_[p] F L
  have : IsGalois F L := by
    refine (InfiniteGalois.normal_iff_isGalois L).1 ?_
    rw [fixingSubgroup_shapiroField, shapiroOpenSubgroup_toSubgroup, MonoidHom.comap_bot,
      QuotientGroup.ker_mk']
    exact W.isNormal'
  have : NeZero (Nat.card Gal(L/F) : ZMod ℓ) := by
    refine ⟨?_⟩
    rw [IsGalois.card_aut_eq_finrank, finrank_shapiroField, Subgroup.index_bot,
      ← Subgroup.index_eq_card, Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hW.symm
  have hdim : finrank (ZMod ℓ) ((fdGalRepOfQuotient ℓ F W).obj A).V = finrank (ZMod ℓ) A := by
    -- Inflation does not change the underlying module (`galRepOfQuotient_obj_V`).
    rw [fdGalRepOfQuotient_obj]
    rfl
  -- The three cohomological dimensions, as invariant dimensions of representations of `G_F ⧸ W`.
  have h0 := finrank_continuousCohomology_zero_fdGalRepOfQuotient A
  have h1 := finrank_continuousCohomology_one_fdGalRepOfQuotient hW A
  have h2 := finrank_continuousCohomology_two_fdGalRepOfQuotient hℓ hW e A
  -- The Kummer count at `L`, at the residue characteristic and away from it.
  by_cases hℓp : ℓ = p
  · subst hℓp
    have hk := finrank_invariants_h1ConjRepresentation_tprod_of_forall σ hσ hℓ e
      (finrank ℚ_[ℓ] F) (fun A' ↦
        finrank_invariants_kummerH1FiniteRepresentation_tprod_of_finitePadicExtension σ _ A') A
    refine localEulerCharacteristic_eq_localCardNorm_of_finrank ℓ _ (finrank ℚ_[ℓ] F)
      (by simp [inv_pow]) ?_
    rw [h0, h1, h2, hk, hdim]
    ring
  · have hℓL : IsUnit (ℓ : 𝒪[L]) := by
      have : CharZero L := FinitePadicExtension.charZero L p
      refine (natCastValuation_eq_zero_iff L ℓ (Nat.cast_ne_zero.2 (NeZero.ne ℓ))).1 ?_
      rw [natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat L p ℓ (NeZero.ne ℓ),
        padicValNat_primes (Ne.symm hℓp), mul_zero]
    have hk := finrank_invariants_h1ConjRepresentation_tprod_of_forall σ hσ hℓ e 0 (fun A' ↦
      by simpa using finrank_invariants_kummerH1FiniteRepresentation_tprod_of_isUnit σ _ hℓL A') A
    refine localEulerCharacteristic_eq_localCardNorm_of_finrank p _ 0
      (by simp [padicNorm.padicNorm_of_prime_of_ne (Ne.symm hℓp)]) ?_
    rw [h0, h1, h2, hk, hdim]
    ring

/-- **Tate's local Euler characteristic formula, prime-to-`ℓ` case.** Let `F/ℚ_p` be finite and
`ℓ` a prime. If an open normal subgroup of `G_F` of index prime to `ℓ` acts trivially on a finite
smooth discrete `ZMod ℓ`-representation `A`, then `χ_F(A) = φ_F(A)`, that is
`#H⁰(F, A) · #H²(F, A) / #H¹(F, A) = ‖#A‖_F`. -/
theorem localEulerCharacteristic_eq_localCardNorm_of_index_coprime {ℓ : ℕ} [Fact ℓ.Prime]
    (A : GalRep ℓ F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod ℓ) A)]
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroup F)) (hN : N.toSubgroup.index.Coprime ℓ)
    (hA : ∀ g ∈ N, ∀ x : A.V, A.ρ g x = x) :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne ℓ)) A = localCardNorm p A := by
  have hℓ : IsUnit (ℓ : F) := (Nat.cast_ne_zero.2 (NeZero.ne ℓ)).isUnit
  -- Shrink `N` so that it also fixes `μ_ℓ`, keeping its index prime to `ℓ`.
  obtain ⟨W, hWN, hWμ, hW, -⟩ := exists_openNormalSubgroup_le_muNRep_ρ_eq_self_of_coprime hℓ N hN
  have := (Fact.out : IsSmoothDiscrete (ZMod ℓ) A).discreteTopology
  obtain ⟨B, ⟨eB⟩⟩ := exists_galRepOfQuotient_iso_of_trivial ℓ F W A fun g hg ↦ hA g (hWN hg)
  have : Finite B.V := Finite.of_equiv _ ((forget (GalRep ℓ F)).mapIso eB).toEquiv.symm
  have : Module.Finite (ZMod ℓ) B.V := Module.Finite.of_finite
  have h := localEulerCharacteristic_fdGalRepOfQuotient_eq_localCardNorm p hW hWμ (FDRep.of B.ρ)
  let e : (fdGalRepOfQuotient ℓ F W).obj (FDRep.of B.ρ) ≅ A :=
    eqToIso (fdGalRepOfQuotient_obj_of ℓ F W B) ≪≫ eB
  exact (localEulerCharacteristic_congr _ e).symm.trans (h.trans (localCardNorm_congr p e))

end Main

end TauCeti.ClassFieldTheory
