/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2CuspidalVirtualCharacter` and its four values are the subject of this file.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Cuspidal.Basic
-- Non-public: Frobenius reciprocity for class functions turns each pairing with an induced
-- character into a sum over the inducing subgroup.
import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity
-- Non-public: the `q`-power map fixes the units coming from `F`.
import TauCeti.FieldTheory.Finite.FrobeniusFixed
-- Non-public: lifting a unit of `E` lying in `F` to a unit of `F`.
import TauCeti.Algebra.GroupWithZero.Units.Basic
-- Non-public: a nontrivial additive character of a finite field sums to zero.
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
-- Non-public: a nontrivial character of a finite group into a domain sums to zero.
import Mathlib.RingTheory.IntegralDomain
-- Non-public: the fundamental theorem of algebra supplies the `IsAlgClosed ℂ` instance of the
-- norm-`1` classification of virtual characters.
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The cuspidal characters of `GL₂(𝔽_q)` are irreducible

Let `F` be a finite field with `q` elements, `E/F` a degree-`2` extension, `θ` a character of `Eˣ`
with `θ^q ≠ θ` and `ψ` a nontrivial additive character of `F`.  This file proves that the cuspidal
virtual character

`χ_θ = χ(Ind_{Z U}^{GL₂(F)} (θ|_{Fˣ} ⊗ ψ)) - χ(Ind_{Eˣ}^{GL₂(F)} θ)`

of `TauCeti/RepresentationTheory/CharacterTable/GL2/Cuspidal/Basic.lean` has norm `1`, and hence,
having positive degree `q - 1`, is the character of an irreducible representation of `GL₂(F)`.
Classically, this character belongs to the cuspidal (discrete series) family attached to `θ`.

## The norm computation

Pairing `χ_θ` with itself splits along its two induced terms, and Frobenius reciprocity turns each
pairing with an induced character into an average over the inducing subgroup, where the four
values of `χ_θ` are known.

* On the scalar--unipotent subgroup `Z U ≃ Fˣ × F`, an element `(a, y)` is a scalar if `y = 0` and
  a nontrivial Jordan block otherwise, so `χ_θ` takes the values `(q - 1) θ(a)` and `-θ(a)` there.
  Against the inducing character `θ(a) ψ(y)` the summand is `q - 1` at `y = 0` and `-ψ(-y)`
  otherwise; `ψ` sums to zero over `F`, so each `a` contributes `q`, and the average is
  `(q - 1) q / |Z U| = 1`.
* On the non-split torus `Eˣ`, an element `u` is a scalar if it comes from `Fˣ` and elliptic
  otherwise, where `χ_θ` takes the value `-(θ(u) + θ(u^q))`.  Against the inducing character `θ`
  the summand is `q - 1` on `Fˣ` and `-(1 + θ(u^q) θ(u)⁻¹)` off it.  The character
  `u ↦ θ(u^q) θ(u)⁻¹` of `Eˣ` is trivial on `Fˣ` and nontrivial exactly when `θ^q ≠ θ`, in which
  case it sums to zero over `Eˣ`; the total is then `(q - 1)² - q (q - 1) + (q - 1) = 0`.

So `⟨χ_θ, χ_θ⟩ = 1 - 0 = 1`.  A virtual character of norm `1` is `±` an irreducible character, and
the sign is fixed by the degree `q - 1`, a natural number
(`TauCeti.mem_irreducibleCharacters_of_characterPairing_self_eq_one`).

## Main results

* `TauCeti.characterPairing_GL2ScalarUnipotentInduction_GL2CuspidalVirtualCharacter`: the cuspidal
  virtual character occurs once in the Gelfand-Graev term.
* `TauCeti.characterPairing_GL2EllipticInduction_GL2CuspidalVirtualCharacter`: for `θ^q ≠ θ` it is
  orthogonal to the character induced from the non-split torus.
* `TauCeti.characterPairing_GL2CuspidalVirtualCharacter_self`: for `θ^q ≠ θ` it has norm `1`.
* `TauCeti.GL2CuspidalVirtualCharacter_mem_irreducibleCharacters`: **for `θ^q ≠ θ` the cuspidal
  virtual character is an irreducible character of `GL₂(F)`.**

## Implementation notes

The pairing theorems carry a `[DecidableEq F]` hypothesis, as
`TauCeti.characterPairing_GL2Steinberg_self` does: the character pairing needs the finite type of
`GL₂(F)`.  The irreducibility theorem, whose statement does not mention the pairing, supplies it
classically in its proof.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F] {E : Type*} [Field E] [Algebra F E]
  (hE : Module.finrank F E = 2)

/-! ### The two sums over the inducing subgroups -/

/-- **The cuspidal virtual character against the Gelfand-Graev line, summed over `Z U`.**  In the
coordinates `(a, y) ∈ Fˣ × F` the summand is `q - 1` at `y = 0` and `-ψ(-y)` otherwise, so each
`a` contributes `q`. -/
private theorem sum_GL2CuspidalVirtualCharacter_mul_GL2ScalarUnipotentRep
    [Fintype (GL2ScalarUnipotent F)] (θ : Eˣ →* ℂˣ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ s : GL2ScalarUnipotent F, (GL2CuspidalVirtualCharacter F E hE θ ψ).1 s *
        (GL2ScalarUnipotentRep F (θ.comp (Units.map (algebraMap F E : F →* E))) ψ).character s⁻¹ =
      ((Fintype.card F : ℂ) - 1) * Fintype.card F := by
  classical
  set μ : Fˣ →* ℂˣ := θ.comp (Units.map (algebraMap F E : F →* E)) with hμ
  have hterm : ∀ (a : Fˣ) (y : F),
      (GL2CuspidalVirtualCharacter F E hE θ ψ).1
          (GL2ScalarUnipotent.mulEquiv F (a, Multiplicative.ofAdd y)) *
        (GL2ScalarUnipotentRep F μ ψ).character
          (GL2ScalarUnipotent.mulEquiv F (a, Multiplicative.ofAdd y))⁻¹ =
      (if y = 0 then (Fintype.card F : ℂ) else 0) - ψ (-y) := by
    intro a y
    have hμa : (μ a : ℂ) ≠ 0 := Units.ne_zero _
    have hψy : ψ y ≠ 0 := (ψ.val_isUnit y).ne_zero
    rw [character_GL2ScalarUnipotentRep, map_inv, GL2ScalarUnipotent.linearChar_mulEquiv,
      GL2ScalarUnipotent.coe_mulEquiv_apply_eq_jordanGL]
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, MonoidHom.coe_toHomUnits,
      AddChar.toMonoidHom_apply, toAdd_ofAdd, AddChar.map_neg_eq_inv]
    by_cases hy : y = 0
    · subst hy
      simp only [mul_zero, jordanGL_zero, GL2CuspidalVirtualCharacter_apply_scalar, ↓reduceIte,
        AddChar.map_zero_eq_one, inv_one, hμ, MonoidHom.comp_apply]
      field_simp
    · simp only [GL2CuspidalVirtualCharacter_apply_jordanGL _ _ hψ a (mul_ne_zero a.ne_zero hy),
        hy, ↓reduceIte, hμ, MonoidHom.comp_apply]
      field_simp
      ring
  rw [← Equiv.sum_comp (GL2ScalarUnipotent.mulEquiv F).toEquiv, Fintype.sum_prod_type]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  have hψsum : ∑ y : F, ψ (-y) = 0 := by
    have h := Equiv.sum_comp (Equiv.neg F) ψ
    simp only [Equiv.neg_apply] at h
    rw [h, AddChar.sum_eq_zero_of_ne_one hψ]
  have hinner : ∀ a : Fˣ, ∑ t : Multiplicative F,
      (GL2CuspidalVirtualCharacter F E hE θ ψ).1 (GL2ScalarUnipotent.mulEquiv F (a, t)) *
        (GL2ScalarUnipotentRep F μ ψ).character (GL2ScalarUnipotent.mulEquiv F (a, t))⁻¹ =
      (Fintype.card F : ℂ) := by
    intro a
    rw [← Equiv.sum_comp Multiplicative.ofAdd]
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      hψsum, sub_zero]
  rw [Finset.sum_congr rfl fun a _ => hinner a, Finset.sum_const, Finset.card_univ,
    Fintype.card_units, nsmul_eq_mul, Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-- **The cuspidal virtual character against `θ`, summed over the non-split torus.**  The summand
is `q - 1` on the units coming from `Fˣ` and `-(1 + θ(u^q) θ(u)⁻¹)` off them; for `θ^q ≠ θ` the
character `u ↦ θ(u^q) θ(u)⁻¹` is nontrivial and the total vanishes. -/
private theorem sum_GL2CuspidalVirtualCharacter_mul_GL2NonSplitTorusRep
    [Fintype (GL2NonSplitTorus F E hE)] {θ : Eˣ →* ℂˣ}
    (hθ : θ.comp (powMonoidHom (Fintype.card F)) ≠ θ) (ψ : AddChar F ℂ) :
    ∑ s : GL2NonSplitTorus F E hE, (GL2CuspidalVirtualCharacter F E hE θ ψ).1 s *
        (GL2NonSplitTorusRep F E hE θ).character s⁻¹ = 0 := by
  classical
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  have : Finite E := Module.finite_of_finite F
  have : Fintype E := Fintype.ofFinite E
  set φ : Eˣ →* ℂˣ := θ.comp (powMonoidHom (Nat.card F)) / θ with hφ
  have hterm : ∀ u : Eˣ,
      (GL2CuspidalVirtualCharacter F E hE θ ψ).1 (GL2NonSplitTorus.unitsEquiv hE u) *
        (GL2NonSplitTorusRep F E hE θ).character (GL2NonSplitTorus.unitsEquiv hE u)⁻¹ =
      (if (u : E) ∈ Set.range (algebraMap F E) then (Fintype.card F : ℂ) + 1 else 0) - 1 -
        (φ u : ℂ) := by
    intro u
    have hθu : (θ u : ℂ) ≠ 0 := Units.ne_zero _
    rw [character_GL2NonSplitTorusRep, ← map_inv, MulEquiv.symm_apply_apply, map_inv,
      Units.val_inv_eq_inv_val, GL2NonSplitTorus.coe_unitsEquiv_apply]
    by_cases hu : (u : E) ∈ Set.range (algebraMap F E)
    · obtain ⟨a, rfl⟩ := (mem_range_iff_exists_units_map_eq (algebraMap F E) u).mp hu
      simp only [hu, ↓reduceIte, hφ, MonoidHom.div_apply, MonoidHom.comp_apply, powMonoidHom_apply,
        FiniteField.units_map_algebraMap_pow_natCard, div_self', Units.val_one,
        GL2NonSplitTorus.gl2NonSplitTorusHom_map_algebraMap,
        GL2CuspidalVirtualCharacter_apply_scalar]
      field_simp
      ring
    · simp only [hu, ↓reduceIte, GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ _ hu,
        hφ, MonoidHom.div_apply, MonoidHom.comp_apply, powMonoidHom_apply,
        Units.val_div_eq_div_val, Nat.card_eq_fintype_card]
      field_simp
      ring
  -- the character `u ↦ θ(u^q) θ(u)⁻¹` is nontrivial, so it sums to zero over `Eˣ`
  have hφne : (Units.coeHom ℂ).comp φ ≠ 1 := by
    intro h
    refine hθ ?_
    rw [← MonoidHom.comp_one (Units.coeHom ℂ)] at h
    have h1 : φ = 1 := (MonoidHom.cancel_left Units.coeHom_injective).mp h
    refine MonoidHom.ext fun u => ?_
    have hu := DFunLike.congr_fun h1 u
    rw [hφ, MonoidHom.div_apply, MonoidHom.one_apply, div_eq_one,
      Nat.card_eq_fintype_card] at hu
    exact hu
  have hφsum : ∑ u : Eˣ, (φ u : ℂ) = 0 := sum_hom_units_eq_zero _ hφne
  -- the units of `E` coming from `F` are the image of `Fˣ`
  have hfilter : (Finset.univ.filter fun u : Eˣ => (u : E) ∈ Set.range (algebraMap F E)) =
      Finset.univ.map ⟨Units.map (algebraMap F E : F →* E),
        Units.map_injective (algebraMap F E).injective⟩ := by
    calc
      _ = Finset.univ.filter (fun u : Eˣ =>
            u ∈ Set.range (Units.map (algebraMap F E : F →* E))) := by
          apply Finset.filter_congr
          intro u _
          exact mem_range_iff_exists_units_map_eq (algebraMap F E) u
      _ = Finset.univ.image (Units.map (algebraMap F E : F →* E)) :=
        Finset.univ_filter_mem_range _
      _ = _ := by
        simpa only [Function.Embedding.coeFn_mk] using
          (Finset.map_eq_image
            ⟨Units.map (algebraMap F E : F →* E),
              Units.map_injective (algebraMap F E).injective⟩ Finset.univ).symm
  have hcardE : ((Fintype.card E - 1 : ℕ) : ℂ) = (Fintype.card F : ℂ) ^ 2 - 1 := by
    rw [← Fintype.card_units, ← Nat.card_eq_fintype_card,
      Nat.card_congr (GL2NonSplitTorus.unitsEquiv hE).toEquiv, GL2NonSplitTorus.natCard_eq,
      Nat.card_eq_fintype_card,
      Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos)]
    push_cast
    ring
  rw [← Equiv.sum_comp (GL2NonSplitTorus.unitsEquiv hE).toEquiv]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hfilter, Finset.card_map,
    Finset.card_univ, Fintype.card_units, hφsum, nsmul_eq_mul, mul_one, hcardE]
  rw [Nat.cast_sub Fintype.card_pos]
  push_cast
  ring

/-! ### The norm of the cuspidal virtual character -/

section Pairing

variable [DecidableEq F]

/-- **The cuspidal virtual character occurs once in the Gelfand-Graev term**: its pairing with the
character induced from `Z U` by `(a, t) ↦ θ(a) ψ(t)` is `1`, for every nontrivial `ψ`. -/
@[simp]
theorem characterPairing_GL2ScalarUnipotentInduction_GL2CuspidalVirtualCharacter
    (θ : Eˣ →* ℂˣ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ClassFunction.characterPairing
        (ClassFunction.ofFDRep
          (GL2ScalarUnipotentInduction F (θ.comp (Units.map (algebraMap F E : F →* E))) ψ))
        (GL2CuspidalVirtualCharacter F E hE θ ψ) = 1 := by
  classical
  have hG : IsUnit (Nat.card (GL (Fin 2) F) : ℂ) :=
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne').isUnit
  rw [GL2ScalarUnipotentInduction_def, ← ClassFunction.ind_ofFDRep, characterPairing_ind hG,
    ClassFunction.characterPairing_symm, ClassFunction.characterPairing_apply]
  simp only [ClassFunction.comap_apply, Subgroup.coe_subtype, ClassFunction.ofFDRep_apply]
  rw [sum_GL2CuspidalVirtualCharacter_mul_GL2ScalarUnipotentRep hE θ hψ,
    natCard_gl2ScalarUnipotent, Nat.card_eq_fintype_card, Nat.cast_mul,
    Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hq : ((Fintype.card F : ℂ) - 1) * Fintype.card F ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast Fintype.one_lt_card.ne'))
      (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
  exact inv_mul_cancel₀ hq

/-- **For `θ^q ≠ θ` the cuspidal virtual character is orthogonal to the elliptic induction**
`Ind_{Eˣ}^{GL₂(F)} θ`. -/
@[simp]
theorem characterPairing_GL2EllipticInduction_GL2CuspidalVirtualCharacter {θ : Eˣ →* ℂˣ}
    (hθ : θ.comp (powMonoidHom (Fintype.card F)) ≠ θ) (ψ : AddChar F ℂ) :
    ClassFunction.characterPairing (ClassFunction.ofFDRep (GL2EllipticInduction F E hE θ))
        (GL2CuspidalVirtualCharacter F E hE θ ψ) = 0 := by
  classical
  have hG : IsUnit (Nat.card (GL (Fin 2) F) : ℂ) :=
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne').isUnit
  rw [GL2EllipticInduction_def, ← ClassFunction.ind_ofFDRep, characterPairing_ind hG,
    ClassFunction.characterPairing_symm, ClassFunction.characterPairing_apply]
  simp only [ClassFunction.comap_apply, Subgroup.coe_subtype, ClassFunction.ofFDRep_apply]
  rw [sum_GL2CuspidalVirtualCharacter_mul_GL2NonSplitTorusRep hE hθ ψ, mul_zero]

/-- **For `θ^q ≠ θ` and `ψ` nontrivial the cuspidal virtual character has norm `1`**: it pairs to
`1` with the Gelfand-Graev term and to `0` with the elliptic induction. -/
@[simp]
theorem characterPairing_GL2CuspidalVirtualCharacter_self {θ : Eˣ →* ℂˣ}
    (hθ : θ.comp (powMonoidHom (Fintype.card F)) ≠ θ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ClassFunction.characterPairing (GL2CuspidalVirtualCharacter F E hE θ ψ)
        (GL2CuspidalVirtualCharacter F E hE θ ψ) = 1 := by
  nth_rewrite 1 [GL2CuspidalVirtualCharacter_def]
  rw [map_sub, LinearMap.sub_apply,
    characterPairing_GL2ScalarUnipotentInduction_GL2CuspidalVirtualCharacter hE θ hψ,
    characterPairing_GL2EllipticInduction_GL2CuspidalVirtualCharacter hE hθ ψ, sub_zero]

end Pairing

/-- **The cuspidal characters of `GL₂(𝔽_q)` are irreducible**: for a character `θ` of `Eˣ` with
`θ^q ≠ θ` and a nontrivial additive character `ψ`, the cuspidal virtual character is the character
of an irreducible complex representation of `GL₂(F)`, of degree `q - 1`
(`TauCeti.GL2CuspidalVirtualCharacter_apply_one`). -/
theorem GL2CuspidalVirtualCharacter_mem_irreducibleCharacters {θ : Eˣ →* ℂˣ}
    (hθ : θ.comp (powMonoidHom (Fintype.card F)) ≠ θ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1 ∈ irreducibleCharacters ℂ (GL (Fin 2) F) := by
  classical
  let : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine mem_irreducibleCharacters_of_characterPairing_self_eq_one
    (GL2CuspidalVirtualCharacter_mem_virtualCharacters hE θ ψ)
    (characterPairing_GL2CuspidalVirtualCharacter_self hE hθ hψ) (n := Fintype.card F - 1) ?_
  rw [GL2CuspidalVirtualCharacter_apply_one, Nat.cast_sub Fintype.card_pos, Nat.cast_one]

end TauCeti
