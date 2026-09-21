/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GL2.Cuspidal.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Complex
import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity
import TauCeti.FieldTheory.Finite.FrobeniusFixed
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# Irreducibility of the cuspidal character of `GL₂(𝔽_q)`

The cuspidal virtual character attached to a character `θ` of the multiplicative group of a
quadratic extension is the difference of two induced characters.  This file computes the three
pairings between those induced characters.  When `θ` is not fixed by the `q`-power map, their
self-pairings are `q` and `q - 1`, while their mutual pairing is `q - 1`.  Bilinearity therefore
gives norm `1` for the difference.

Since the difference is already known to be a virtual character, the norm-one criterion identifies
it, up to sign, with an irreducible character.  Its positive value `q - 1` at the identity rules out
the negative sign.  The resulting representation is the cuspidal representation of `GL₂(𝔽_q)`.

## Main results

* `TauCeti.characterPairing_GL2CuspidalVirtualCharacter_self`: the cuspidal virtual character has
  norm `1` for `θ^q ≠ θ` and a nontrivial additive character.
* `TauCeti.GL2CuspidalVirtualCharacter_mem_irreducibleCharacters`: the virtual character is an
  irreducible character.
* `TauCeti.GL2Cuspidal`: the corresponding irreducible representation, using Mathlib's canonical
  primitive additive character internally.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F] [Finite F]
variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

private theorem card_gl2_ne_zero : (Nat.card (GL (Fin 2) F) : ℂ) ≠ 0 := by
  exact_mod_cast Nat.card_pos.ne'

private theorem card_scalarUnipotent_ne_zero :
    (Nat.card (GL2ScalarUnipotent F) : ℂ) ≠ 0 := by
  exact_mod_cast Nat.card_pos.ne'

variable [Fintype F] [DecidableEq F]

/-- **The scalar--unipotent induction has character norm `q`** when its additive character is
nontrivial. -/
theorem characterPairing_GL2ScalarUnipotentInduction_self (mu : Fˣ →* ℂˣ)
    {psi : AddChar F ℂ} (hpsi : psi ≠ 1) :
    ClassFunction.characterPairing
        (ClassFunction.ofFDRep (GL2ScalarUnipotentInduction F mu psi))
        (ClassFunction.ofFDRep (GL2ScalarUnipotentInduction F mu psi)) =
      Fintype.card F := by
  classical
  let hG : IsUnit (Nat.card (GL (Fin 2) F) : ℂ) :=
    isUnit_iff_ne_zero.mpr card_gl2_ne_zero
  rw [GL2ScalarUnipotentInduction_def]
  rw [← ClassFunction.ind_ofFDRep, characterPairing_ind hG]
  rw [ClassFunction.characterPairing_apply]
  simp only [ClassFunction.ind_ofFDRep, ClassFunction.comap_subtype_ofFDRep,
    ClassFunction.ofFDRep_apply, character_resFDRep]
  have hterm (a : Fˣ) (t : Multiplicative F) :
      (GL2ScalarUnipotentRep F mu psi).character
          (GL2ScalarUnipotent.mulEquiv F (a, t)) *
        (indFDRep (GL2ScalarUnipotentRep F mu psi)).character
          (((GL2ScalarUnipotent.mulEquiv F (a, t) : GL2ScalarUnipotent F) :
            GL (Fin 2) F)⁻¹) =
        if t = 1 then (Fintype.card F ^ 2 - 1 : ℂ) else -psi (Multiplicative.toAdd t) := by
    rw [character_GL2ScalarUnipotentRep, GL2ScalarUnipotent.linearChar_mulEquiv]
    have hinv :
        (((GL2ScalarUnipotent.mulEquiv F (a, t) : GL2ScalarUnipotent F) :
            GL (Fin 2) F)⁻¹) =
          ((GL2ScalarUnipotent.mulEquiv F (a⁻¹, t⁻¹) : GL2ScalarUnipotent F) :
            GL (Fin 2) F) := by
      rw [← Subgroup.coe_inv, ← map_inv]
      rfl
    rw [hinv, GL2ScalarUnipotent.coe_mulEquiv_apply_eq_jordanGL]
    rw [← GL2ScalarUnipotentInduction_def]
    split_ifs with ht
    · subst t
      have ht_one : Multiplicative.toAdd (1 : Multiplicative F) = 0 := rfl
      rw [inv_one, ht_one, mul_zero,
        jordanGL_zero,
        character_GL2ScalarUnipotentInduction_scalar]
      simp only [map_one, map_inv, Units.val_inv_eq_inv_val]
      have hmu : (mu a : ℂ) ≠ 0 := Units.ne_zero _
      field_simp [hmu]
      simp only [mul_one]
      ring
    · have ht0 : Multiplicative.toAdd t⁻¹ ≠ 0 := by
        simpa using ht
      rw [character_GL2ScalarUnipotentInduction_jordanGL _ _ hpsi a⁻¹
        (mul_ne_zero a⁻¹.ne_zero ht0)]
      simp only [map_inv, Units.val_inv_eq_inv_val, Units.val_mul,
        MonoidHom.coe_toHomUnits, AddChar.toMonoidHom_apply]
      field_simp
  rw [← (GL2ScalarUnipotent.mulEquiv F).toEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subgroup.coe_inv]
  simp_rw [hterm]
  have hsumpsi : ∑ t : Multiplicative F, psi (Multiplicative.toAdd t) = 0 := by
    rw [Multiplicative.toAdd.sum_comp]
    exact AddChar.sum_eq_zero_of_ne_one hpsi
  have herase :
      ∑ t ∈ (Finset.univ.erase (1 : Multiplicative F)), psi (Multiplicative.toAdd t) = -1 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Multiplicative F))
      (fun t => psi (Multiplicative.toAdd t)) (Finset.mem_univ 1)
    rw [hsumpsi] at hsplit
    simpa using eq_neg_of_add_eq_zero_left hsplit
  have hinner :
      ∑ t : Multiplicative F,
          (if t = 1 then (Fintype.card F ^ 2 - 1 : ℂ) else -psi (Multiplicative.toAdd t)) =
        (Fintype.card F : ℂ) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Multiplicative F))]
    rw [ite_eq_left rfl]
    have hrest :
        ∑ t ∈ Finset.univ.erase (1 : Multiplicative F),
            (if t = 1 then (Fintype.card F ^ 2 - 1 : ℂ) else -psi (Multiplicative.toAdd t)) =
          ∑ t ∈ Finset.univ.erase (1 : Multiplicative F), -psi (Multiplicative.toAdd t) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [ite_eq_right (Finset.ne_of_mem_erase ht)]
    rw [hrest, Finset.sum_neg_distrib, herase, neg_neg]
    ring
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [natCard_gl2ScalarUnipotent, Nat.card_eq_fintype_card, Fintype.card_units]
  push_cast [Fintype.one_lt_card.le]
  have hq : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩).ne'
  have hq1 : (Fintype.card F : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast Fintype.one_lt_card.ne')
  field_simp [hq, hq1]

/-- **The elliptic induction has character norm `q - 1`** when `θ` is not fixed by the
`q`-power map. -/
theorem characterPairing_GL2EllipticInduction_self (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    ClassFunction.characterPairing
        (ClassFunction.ofFDRep (GL2EllipticInduction F E hE theta))
        (ClassFunction.ofFDRep (GL2EllipticInduction F E hE theta)) =
      Fintype.card F - 1 := by
  classical
  let _ : Finite E :=
    Finite.of_injective (nonSplitTorusBasis F E hE).repr
      (nonSplitTorusBasis F E hE).repr.injective
  let _ : Fintype E := Fintype.ofFinite E
  let hG : IsUnit (Nat.card (GL (Fin 2) F) : ℂ) :=
    isUnit_iff_ne_zero.mpr card_gl2_ne_zero
  rw [GL2EllipticInduction_def]
  rw [← ClassFunction.ind_ofFDRep, characterPairing_ind hG]
  rw [ClassFunction.characterPairing_apply]
  simp only [ClassFunction.ind_ofFDRep, ClassFunction.comap_subtype_ofFDRep,
    ClassFunction.ofFDRep_apply, character_resFDRep]
  have hterm (u : Eˣ) :
      (GL2NonSplitTorusRep F E hE theta).character
          (GL2NonSplitTorus.unitsEquiv hE u) *
        (indFDRep (GL2NonSplitTorusRep F E hE theta)).character
          (((GL2NonSplitTorus.unitsEquiv hE u : GL2NonSplitTorus F E hE) :
            GL (Fin 2) F)⁻¹) =
        if (u : E) ∈ Set.range (algebraMap F E) then
          ((Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1))
        else 1 + ((theta * (theta.comp (powMonoidHom (Nat.card F)))⁻¹) u : ℂ) := by
    rw [character_GL2NonSplitTorusRep, MulEquiv.symm_apply_apply]
    have hinv :
        (((GL2NonSplitTorus.unitsEquiv hE u : GL2NonSplitTorus F E hE) :
            GL (Fin 2) F)⁻¹) = GL2NonSplitTorusHom F E hE u⁻¹ := by
      rw [← Subgroup.coe_inv, ← map_inv]
      exact GL2NonSplitTorus.coe_unitsEquiv_apply hE u⁻¹
    rw [hinv, ← GL2EllipticInduction_def]
    split_ifs with hu
    · obtain ⟨a, rfl⟩ := (Units.coe_mem_range_algebraMap_iff _).mp hu
      rw [map_inv, GL2NonSplitTorus.gl2NonSplitTorusHom_map_algebraMap,
        ← map_inv, character_GL2EllipticInduction_scalar]
      simp only [map_inv, Units.val_inv_eq_inv_val]
      field_simp
      rw [Nat.card_eq_fintype_card]
    · have huinv : ((u⁻¹ : Eˣ) : E) ∉ Set.range (algebraMap F E) := by
        simpa only [Units.coe_inv_mem_range_algebraMap_iff] using hu
      rw [character_GL2EllipticInduction_gl2NonSplitTorusHom _ _ _ _ huinv]
      simp [mul_add, inv_pow]
  rw [← (GL2NonSplitTorus.unitsEquiv hE).toEquiv.sum_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subgroup.coe_inv]
  simp_rw [hterm]
  let delta : Eˣ →* ℂˣ := theta * (theta.comp (powMonoidHom (Nat.card F)))⁻¹
  have hdelta : delta ≠ 1 := by
    intro hd
    apply htheta
    ext u
    have hu := DFunLike.congr_fun hd u
    dsimp only [delta] at hu
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.one_apply, mul_inv_eq_one] at hu
    exact congrArg Units.val hu.symm
  have hcoedelta : (Units.coeHom ℂ).comp delta ≠ 1 := by
    intro hd
    apply hdelta
    ext u
    exact DFunLike.congr_fun hd u
  have hsumdelta : ∑ u : Eˣ, (delta u : ℂ) = 0 :=
    sum_hom_units_eq_zero ((Units.coeHom ℂ).comp delta) hcoedelta
  let p : Eˣ → Prop := fun u => (u : E) ∈ Set.range (algebraMap F E)
  let f : Fˣ → {u : Eˣ // p u} := fun a =>
    ⟨Units.map (algebraMap F E : F →* E) a, a, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Units.ext
      have hab' := congrArg (fun u : {u : Eˣ // p u} => ((u : Eˣ) : E)) hab
      exact (algebraMap F E).injective hab'
    · rintro ⟨u, hu⟩
      obtain ⟨a, ha⟩ := (Units.coe_mem_range_algebraMap_iff u).mp hu
      exact ⟨a, Subtype.ext ha⟩
  let e : Fˣ ≃ {u : Eˣ // p u} := Equiv.ofBijective f hf
  have hcardBase : (Finset.univ.filter p).card = Fintype.card F - 1 := by
    rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_units]
  have hrewrite (u : Eˣ) :
      (if p u then (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1)
        else 1 + (delta u : ℂ)) =
        1 + (delta u : ℂ) +
          if p u then (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1) - 2
          else 0 := by
    split_ifs with hu
    · have hpow : u ^ Fintype.card F = u := by
        apply Units.ext
        exact (FiniteField.pow_card_eq_self_iff_mem_range_algebraMap (u : E)).mpr hu
      have hdelta_one : delta u = 1 := by
        dsimp only [delta]
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
        rw [MonoidHom.comp_apply, powMonoidHom_apply, Nat.card_eq_fintype_card, hpow]
      rw [hdelta_one]
      norm_num
    · ring
  -- Unfold the pairing after naming its summand predicate and character quotient above.
  change (Nat.card (GL2NonSplitTorus F E hE) : ℂ)⁻¹ *
    (∑ u : Eˣ, if p u then (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1)
      else 1 + (delta u : ℂ)) = _
  simp_rw [hrewrite]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hsumdelta, add_zero]
  have hcorrection :
      ∑ u : Eˣ,
          (if p u then
            (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1) - 2 else 0) =
        (Fintype.card F - 1 : ℂ) *
          ((Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1) - 2) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcardBase]
    push_cast [Fintype.one_lt_card.le]
    rfl
  rw [hcorrection, GL2NonSplitTorus.natCard_eq hE, Nat.card_eq_fintype_card]
  have hcardE : Fintype.card E = Fintype.card F ^ 2 := by
    rw [Fintype.card_congr (nonSplitTorusBasis F E hE).equivFun.toEquiv, Fintype.card_fun,
      Fintype.card_fin]
  rw [Fintype.card_units, hcardE]
  have hq2 : 1 ≤ Fintype.card F ^ 2 := by
    nlinarith [Fintype.one_lt_card (α := F)]
  push_cast [Fintype.one_lt_card.le, hq2]
  have hq1 : (Fintype.card F : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast Fintype.one_lt_card.ne')
  have hqplus : (Fintype.card F : ℂ) + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    have hrpos : 0 < (Fintype.card F : ℝ) + 1 := by positivity
    linarith
  have hfactor : -1 + (Fintype.card F : ℂ) ^ 2 =
      ((Fintype.card F : ℂ) - 1) * ((Fintype.card F : ℂ) + 1) := by
    ring
  have hdenom : -1 + (Fintype.card F : ℂ) ^ 2 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hq1 hqplus
  have hdenom' : (Fintype.card F : ℂ) ^ 2 - 1 ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hdenom
  field_simp [hdenom']
  ring

/-- **The mutual pairing of the scalar--unipotent and elliptic inductions is `q - 1`.** Only
the scalar elements of the scalar--unipotent subgroup contribute, because the elliptic induction
vanishes on nontrivial Jordan blocks. -/
theorem characterPairing_GL2ScalarUnipotentInduction_GL2EllipticInduction
    (theta : Eˣ →* ℂˣ) (psi : AddChar F ℂ) :
    ClassFunction.characterPairing
        (ClassFunction.ofFDRep
          (GL2ScalarUnipotentInduction F
            (theta.comp (Units.map (algebraMap F E : F →* E))) psi))
        (ClassFunction.ofFDRep (GL2EllipticInduction F E hE theta)) =
      Fintype.card F - 1 := by
  classical
  let hG : IsUnit (Nat.card (GL (Fin 2) F) : ℂ) :=
    isUnit_iff_ne_zero.mpr card_gl2_ne_zero
  rw [GL2ScalarUnipotentInduction_def]
  rw [← ClassFunction.ind_ofFDRep, characterPairing_ind hG]
  rw [ClassFunction.characterPairing_apply]
  simp only [ClassFunction.comap_subtype_ofFDRep,
    ClassFunction.ofFDRep_apply, character_resFDRep]
  have hterm (a : Fˣ) (t : Multiplicative F) :
      (GL2ScalarUnipotentRep F
          (theta.comp (Units.map (algebraMap F E : F →* E))) psi).character
          (GL2ScalarUnipotent.mulEquiv F (a, t)) *
        (GL2EllipticInduction F E hE theta).character
          (((GL2ScalarUnipotent.mulEquiv F (a, t) : GL2ScalarUnipotent F) :
            GL (Fin 2) F)⁻¹) =
        if t = 1 then (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1) else 0 := by
    rw [character_GL2ScalarUnipotentRep, GL2ScalarUnipotent.linearChar_mulEquiv]
    have hinv :
        (((GL2ScalarUnipotent.mulEquiv F (a, t) : GL2ScalarUnipotent F) :
            GL (Fin 2) F)⁻¹) =
          ((GL2ScalarUnipotent.mulEquiv F (a⁻¹, t⁻¹) : GL2ScalarUnipotent F) :
            GL (Fin 2) F) := by
      rw [← Subgroup.coe_inv, ← map_inv]
      rfl
    rw [hinv, GL2ScalarUnipotent.coe_mulEquiv_apply_eq_jordanGL]
    split_ifs with ht
    · subst t
      have ht_one : Multiplicative.toAdd (1 : Multiplicative F) = 0 := rfl
      rw [inv_one, ht_one, mul_zero,
        jordanGL_zero, character_GL2EllipticInduction_scalar]
      simp only [MonoidHom.comp_apply, map_one, map_inv, Units.val_inv_eq_inv_val]
      have htheta : (theta ((Units.map (algebraMap F E : F →* E)) a) : ℂ) ≠ 0 :=
        Units.ne_zero _
      field_simp [htheta]
      simp only [mul_one]
      rw [Nat.card_eq_fintype_card]
    · have ht0 : Multiplicative.toAdd t⁻¹ ≠ 0 := by
        simpa using ht
      rw [character_GL2EllipticInduction_jordanGL _ _ _ _ a⁻¹
        (mul_ne_zero a⁻¹.ne_zero ht0), mul_zero]
  rw [← (GL2ScalarUnipotent.mulEquiv F).toEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subgroup.coe_inv]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [natCard_gl2ScalarUnipotent, Nat.card_eq_fintype_card, Fintype.card_units]
  push_cast [Fintype.one_lt_card.le]
  have hq : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩).ne'
  have hq1 : (Fintype.card F : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast Fintype.one_lt_card.ne')
  field_simp [hq, hq1]

/-- **The cuspidal virtual character has norm one in general position.** -/
@[simp]
theorem characterPairing_GL2CuspidalVirtualCharacter_self (theta : Eˣ →* ℂˣ)
    {psi : AddChar F ℂ} (hpsi : psi ≠ 1)
    (htheta : theta.comp (powMonoidHom (Fintype.card F)) ≠ theta) :
    ClassFunction.characterPairing (GL2CuspidalVirtualCharacter F E hE theta psi)
      (GL2CuspidalVirtualCharacter F E hE theta psi) = 1 := by
  rw [GL2CuspidalVirtualCharacter_def]
  simp only [map_sub, LinearMap.sub_apply]
  have hcross : ClassFunction.characterPairing
      (ClassFunction.ofFDRep (GL2EllipticInduction F E hE theta))
      (ClassFunction.ofFDRep
        (GL2ScalarUnipotentInduction F
          (theta.comp (Units.map (algebraMap F E : F →* E))) psi)) =
        Fintype.card F - 1 := by
    rw [ClassFunction.characterPairing_symm]
    exact characterPairing_GL2ScalarUnipotentInduction_GL2EllipticInduction hE theta psi
  rw [characterPairing_GL2ScalarUnipotentInduction_self
      (theta.comp (Units.map (algebraMap F E : F →* E))) hpsi,
    characterPairing_GL2ScalarUnipotentInduction_GL2EllipticInduction hE theta psi,
    hcross, characterPairing_GL2EllipticInduction_self hE theta (by
      simpa only [Nat.card_eq_fintype_card] using htheta)]
  ring

omit [DecidableEq F] in
/-- **The cuspidal virtual character is an irreducible character in general position.** The
norm-one criterion gives an irreducible character up to sign, and its degree `q - 1 > 0` fixes the
positive sign. -/
theorem GL2CuspidalVirtualCharacter_mem_irreducibleCharacters (theta : Eˣ →* ℂˣ)
    {psi : AddChar F ℂ} (hpsi : psi ≠ 1)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (GL2CuspidalVirtualCharacter F E hE theta psi).1 ∈
      irreducibleCharacters ℂ (GL (Fin 2) F) := by
  classical
  let _ : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero card_gl2_ne_zero
  obtain ⟨i, hi⟩ := exists_eq_irreducibleCharacter_or_neg
    (GL2CuspidalVirtualCharacter_mem_virtualCharacters hE theta psi)
    (characterPairing_GL2CuspidalVirtualCharacter_self hE theta hpsi (by
      simpa only [Nat.card_eq_fintype_card] using htheta))
  rcases hi with hi | hi
  · rw [hi]
    exact irreducibleCharacter_mem ℂ i
  · exfalso
    have hval := congrFun hi (1 : GL (Fin 2) F)
    rw [GL2CuspidalVirtualCharacter_apply_one, Pi.neg_apply, irreducibleCharacter_one] at hval
    have hsum :
        (((Fintype.card F - 1) + characterDegree ℂ i : ℕ) : ℂ) = 0 := by
      push_cast [Fintype.one_lt_card.le]
      linear_combination hval
    rw [Nat.cast_eq_zero] at hsum
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have hdeg := characterDegree_pos ℂ i
    omega

omit [DecidableEq F] in
private theorem exists_gl2Cuspidal (theta : Eˣ →* ℂˣ) (psi : AddChar F ℂ)
    (hpsi : psi ≠ 1) (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    ∃ (n : ℕ) (rho : Representation ℂ (GL (Fin 2) F) (Fin n → ℂ)),
      rho.IsIrreducible ∧
        rho.character = (GL2CuspidalVirtualCharacter F E hE theta psi).1 :=
  mem_irreducibleCharacters_iff.mp
    (GL2CuspidalVirtualCharacter_mem_irreducibleCharacters hE theta hpsi htheta)

omit [DecidableEq F] in
private noncomputable def gl2CuspidalDimension (theta : Eˣ →* ℂˣ) (psi : AddChar F ℂ)
    (hpsi : psi ≠ 1) (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) : ℕ :=
  (exists_gl2Cuspidal hE theta psi hpsi htheta).choose

omit [DecidableEq F] in
private noncomputable def gl2CuspidalRepresentation (theta : Eˣ →* ℂˣ)
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    Representation ℂ (GL (Fin 2) F) (Fin (gl2CuspidalDimension hE theta psi hpsi htheta) → ℂ) :=
  (exists_gl2Cuspidal hE theta psi hpsi htheta).choose_spec.choose

omit [DecidableEq F] in
private theorem gl2CuspidalRepresentation_spec (theta : Eˣ →* ℂˣ) (psi : AddChar F ℂ)
    (hpsi : psi ≠ 1) (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (gl2CuspidalRepresentation hE theta psi hpsi htheta).IsIrreducible ∧
      (gl2CuspidalRepresentation hE theta psi hpsi htheta).character =
        (GL2CuspidalVirtualCharacter F E hE theta psi).1 :=
  (exists_gl2Cuspidal hE theta psi hpsi htheta).choose_spec.choose_spec

omit [Fintype F] [DecidableEq F] in
/-- Mathlib's primitive complex additive character on a finite field is nontrivial. -/
private theorem primitiveChar_to_Complex_ne_one :
    AddChar.FiniteField.primitiveChar_to_Complex F ≠ 1 := by
  have hprimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  simpa only [AddChar.mulShift_one] using hprimitive (one_ne_zero : (1 : F) ≠ 0)

omit [DecidableEq F] in
/-- Passing the chosen cuspidal representation through `FDRep.of` preserves its character. -/
private theorem character_fdRepOf_gl2CuspidalRepresentation (theta : Eˣ →* ℂˣ)
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (FDRep.of (gl2CuspidalRepresentation hE theta psi hpsi htheta)).character =
      (GL2CuspidalVirtualCharacter F E hE theta psi).1 := by
  exact (gl2CuspidalRepresentation_spec hE theta psi hpsi htheta).2

omit [DecidableEq F] in
/-- **The cuspidal representation of `GL₂(𝔽_q)` attached to a general-position character
`θ : Eˣ → ℂˣ`.** The auxiliary additive character is Mathlib's canonical primitive complex
character of `F`, so it does not appear in the public cuspidal datum. -/
noncomputable def GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) : FDRep ℂ (GL (Fin 2) F) :=
  FDRep.of (gl2CuspidalRepresentation hE theta
    (AddChar.FiniteField.primitiveChar_to_Complex F)
    (primitiveChar_to_Complex_ne_one (F := F)) htheta)

omit [DecidableEq F] in
/-- The character of `TauCeti.GL2Cuspidal` is the cuspidal virtual character from which it was
constructed. -/
@[simp]
theorem character_GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (GL2Cuspidal hE theta htheta).character =
      (GL2CuspidalVirtualCharacter F E hE theta
        (AddChar.FiniteField.primitiveChar_to_Complex F)).1 := by
  exact character_fdRepOf_gl2CuspidalRepresentation hE theta
    (AddChar.FiniteField.primitiveChar_to_Complex F)
    (primitiveChar_to_Complex_ne_one (F := F)) htheta

omit [DecidableEq F] in
/-- The cuspidal representation has degree `q - 1`. -/
@[simp]
theorem finrank_GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    Module.finrank ℂ (GL2Cuspidal hE theta htheta) = Fintype.card F - 1 := by
  have hchar := congrFun (character_GL2Cuspidal hE theta htheta)
    (1 : GL (Fin 2) F)
  rw [FDRep.char_one, GL2CuspidalVirtualCharacter_apply_one] at hchar
  apply Nat.cast_injective (R := ℂ)
  push_cast [Fintype.one_lt_card.le]
  exact hchar

omit [DecidableEq F] in
/-- The character of the cuspidal representation has value `q - 1` at the identity. -/
theorem character_one_GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (GL2Cuspidal hE theta htheta).character 1 = (Fintype.card F : ℂ) - 1 := by
  rw [character_GL2Cuspidal, GL2CuspidalVirtualCharacter_apply_one]

omit [DecidableEq F] in
/-- The cuspidal representation attached to a general-position character is simple. -/
theorem simple_GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    CategoryTheory.Simple (GL2Cuspidal hE theta htheta) := by
  let _ : Representation.IsIrreducible (GL2Cuspidal hE theta htheta).ρ := by
    rw [GL2Cuspidal, FDRep.of_ρ']
    exact (gl2CuspidalRepresentation_spec hE theta
      (AddChar.FiniteField.primitiveChar_to_Complex F)
      (primitiveChar_to_Complex_ne_one (F := F)) htheta).1
  exact FDRep.simple_of_isIrreducible _

end TauCeti
