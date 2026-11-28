/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.FieldTheory.RatFunc.LeadingCoeff
public import TauCeti.RingTheory.MilnorK.Residue

/-!
# The leading-coefficient specialization of `K_*ᴹ(F(t))`

Let `F` be a field. The place at infinity `P_∞` of the rational function field `F(t)` has order
`ord_∞ f = -deg f`, uniformizer `t⁻¹` and residue field `F`. The specialization of Milnor
K-theory at `P_∞` with respect to `t⁻¹`, read through the identification of the residue field
with `F`, is a ring homomorphism

`λ : K_*ᴹ(F(t)) → K_*ᴹ(F)`, `λ{f₁, …, fₙ} = {lc f₁, …, lc fₙ}`,

where `lc f` is the leading coefficient `RatFunc.leadingCoeffHom f`, the quotient of the leading
coefficients of the numerator and denominator of `f`. Indeed the unit part of `f` relative to
`t⁻¹` is `f t^{-deg f}`, a function of degree `0` whose value at infinity is `lc f`.

Since `λ` sends the symbol of constants `{c₁, …, cₙ}` to itself, it retracts the map
`K_*ᴹ(F) → K_*ᴹ(F(t))` induced by the inclusion of constants. So this map is a split injection,
in every degree since both maps preserve degrees. This splitting is the first step of the
computation of `K_nᴹ(F(t))` by the Bass–Tate (Milnor) exact sequence.

The specialization depends on the uniformizer: with `c t⁻¹` in place of `t⁻¹` the degree-one
class `{t}` would specialize to `{c}` rather than to `0`.

## Main definitions

* `TauCeti.MilnorK.leadingCoeffSpecialization F`: the ring homomorphism
  `λ : K_*ᴹ(F(t)) → K_*ᴹ(F)`.

## Main results

* `TauCeti.MilnorK.map_comp_leadingCoeffSpecialization`: the specialization
  `Valuation.milnorSpecialization` at the place at infinity with respect to `t⁻¹` is `λ` followed
  by the inclusion of `F` in the residue field at infinity.
* `TauCeti.MilnorK.leadingCoeffSpecialization_ofUnit`,
  `TauCeti.MilnorK.leadingCoeffSpecialization_symbol`: `λ{f₁, …, fₙ} = {lc f₁, …, lc fₙ}`.
* `TauCeti.MilnorK.leadingCoeffSpecialization_map_C`: `λ` retracts
  `K_*ᴹ(F) → K_*ᴹ(F(t))`, which is therefore injective
  (`TauCeti.MilnorK.map_ratFunc_C_injective`), and `λ` is surjective
  (`TauCeti.MilnorK.leadingCoeffSpecialization_surjective`).
* `TauCeti.MilnorK.leadingCoeffSpecialization_mem_degree`: `λ` preserves degrees.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Example III.7.3.2 and Example III.6.1.2.
* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), 318–344, §2.
-/

public section

open TauCeti.Place

namespace TauCeti.MilnorK

variable (F : Type*) [Field F]

/-- The order of `t⁻¹` at the place at infinity of `F(t)` is one. -/
private theorem ord_infty_inv_mk0_X :
    (infty F).valuation.ord (((Units.mk0 RatFunc.X RatFunc.X_ne_zero)⁻¹ : (RatFunc F)ˣ) :
      RatFunc F) = 1 := by
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, Place.ord_valuation, ord_infty_inv_X]

/-- The identification of the residue field at infinity, in the form on which the residue
constructions for the valuation of `P_∞` take values, with `F`. -/
private noncomputable def inftyResidueFieldToConst :
    IsLocalRing.ResidueField (infty F).valuation.valuationSubring →+* F :=
  ((inftyResidueFieldEquiv F).symm : (infty F).ResidueField →+* F).comp
    ((infty F).residueFieldEquivValuationSubring.symm :
      IsLocalRing.ResidueField (infty F).valuation.valuationSubring →+* (infty F).ResidueField)

/-- The **leading-coefficient specialization** `λ : K_*ᴹ(F(t)) → K_*ᴹ(F)`: the ring homomorphism
with `λ{f₁, …, fₙ} = {lc f₁, …, lc fₙ}` (`TauCeti.MilnorK.leadingCoeffSpecialization_symbol`),
where `lc` is the leading coefficient `RatFunc.leadingCoeffHom`. It is the specialization of
Milnor K-theory at the place at infinity of `F(t)` with respect to the uniformizer `t⁻¹`, read
through the identification of the residue field at infinity with `F`
(`TauCeti.MilnorK.map_comp_leadingCoeffSpecialization`), and it retracts the map induced by the
inclusion of constants (`TauCeti.MilnorK.leadingCoeffSpecialization_map_C`). -/
noncomputable def leadingCoeffSpecialization : MilnorK (RatFunc F) →+* MilnorK F :=
  (map (inftyResidueFieldToConst F)).comp
    ((infty F).valuation.milnorSpecialization _ (ord_infty_inv_mk0_X F))

variable {F}

/-- The reduced unit part at infinity of `f`, relative to `t⁻¹`, is the leading coefficient of
`f`: the unit part is `f t^{-deg f}`, a function of degree `0` with the same leading
coefficient. -/
private theorem inftyResidueFieldToConst_unitPartResidue (f : (RatFunc F)ˣ) :
    inftyResidueFieldToConst F
        ((infty F).valuation.unitPartResidue _ (ord_infty_inv_mk0_X F) f) =
      RatFunc.leadingCoeffHom (f : RatFunc F) := by
  set u := (infty F).valuation.unitPart _ (ord_infty_inv_mk0_X F) f
  have hu : ((u : (RatFunc F)ˣ) : RatFunc F).intDegree = 0 := by
    have h := ((infty F).valuation.mem_unitGroup_iff_ord_eq_zero _).1 u.property
    rwa [Place.ord_valuation, ord_infty, neg_eq_zero] at h
  have hlc : RatFunc.leadingCoeffHom ((u : (RatFunc F)ˣ) : RatFunc F) =
      RatFunc.leadingCoeffHom (f : RatFunc F) := by
    simp [u, Units.val_zpow_eq_zpow_val]
  have hmem : ((u : (RatFunc F)ˣ) : RatFunc F) ∈ (infty F).integers :=
    (infty F).mem_integers_iff_ord_nonneg.2 (by rw [ord_infty, hu, neg_zero])
  rw [Valuation.coe_unitPartResidue_eq_residue _ _ _
    (x := ⟨_, (Valuation.mem_valuationSubring_iff _ _).2 ((infty F).mem_integers_iff.1 hmem)⟩) rfl]
  simpa [inftyResidueFieldToConst, residue_infty_eq_algebraMap_leadingCoeff (x := ⟨_, hmem⟩) hu,
    ← inftyResidueFieldEquiv_apply, RatFunc.leadingCoeffHom_apply] using hlc

/-- `λ{f} = {lc f}`. -/
@[simp]
theorem leadingCoeffSpecialization_ofUnit (f : (RatFunc F)ˣ) :
    leadingCoeffSpecialization F (ofUnit f) =
      ofUnit (Units.map (RatFunc.leadingCoeffHom (K := F) : RatFunc F →* F) f) := by
  rw [leadingCoeffSpecialization, RingHom.comp_apply, Valuation.milnorSpecialization_ofUnit,
    map_ofUnit]
  congr 1
  ext
  exact inftyResidueFieldToConst_unitPartResidue f

/-- `λ{f₁, …, fₙ} = {lc f₁, …, lc fₙ}`. -/
@[simp]
theorem leadingCoeffSpecialization_symbol (l : List (RatFunc F)ˣ) :
    leadingCoeffSpecialization F (symbol l) =
      symbol (l.map (Units.map (RatFunc.leadingCoeffHom (K := F) : RatFunc F →* F))) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [symbol_cons, ih]

/-- The leading-coefficient specialization retracts the map `K_*ᴹ(F) → K_*ᴹ(F(t))` induced by
the inclusion of constants. -/
theorem leadingCoeffSpecialization_comp_map_C :
    (leadingCoeffSpecialization F).comp (map (RatFunc.C : F →+* RatFunc F)) = RingHom.id _ :=
  ringHom_ext fun c ↦ by
    rw [RingHom.comp_apply, map_ofUnit, leadingCoeffSpecialization_ofUnit, RingHom.id_apply]
    congr 1
    ext
    simp

/-- `λ` is the identity on the image of `K_*ᴹ(F)`: `λ (map C x) = x`. -/
@[simp]
theorem leadingCoeffSpecialization_map_C (x : MilnorK F) :
    leadingCoeffSpecialization F (map (RatFunc.C : F →+* RatFunc F) x) = x :=
  RingHom.congr_fun leadingCoeffSpecialization_comp_map_C x

/-- The specialization at the place at infinity with respect to the uniformizer `t⁻¹` is the
leading-coefficient specialization followed by the inclusion of `F` in the residue field at
infinity. -/
theorem map_comp_leadingCoeffSpecialization {t : (RatFunc F)ˣ}
    (ht : (infty F).valuation.ord (t : RatFunc F) = 1) (htX : (t : RatFunc F) = RatFunc.X⁻¹) :
    (map (((infty F).residueFieldEquivValuationSubring : (infty F).ResidueField →+* _).comp
      (algebraMap F (infty F).ResidueField))).comp (leadingCoeffSpecialization F) =
        (infty F).valuation.milnorSpecialization t ht := by
  obtain rfl : t = (Units.mk0 RatFunc.X RatFunc.X_ne_zero)⁻¹ :=
    Units.ext (by rw [htX, Units.val_inv_eq_inv_val, Units.val_mk0])
  have h : (((infty F).residueFieldEquivValuationSubring : (infty F).ResidueField →+* _).comp
      (algebraMap F (infty F).ResidueField)).comp (inftyResidueFieldToConst F) = RingHom.id _ := by
    ext y
    simp [inftyResidueFieldToConst, ← inftyResidueFieldEquiv_apply]
  rw [leadingCoeffSpecialization, ← RingHom.comp_assoc, ← map_comp, h, map_id, RingHom.id_comp]

/-- **`K_*ᴹ(F)` embeds in `K_*ᴹ(F(t))`**: the map induced by the inclusion of constants is a
split injection, split by `TauCeti.MilnorK.leadingCoeffSpecialization`. -/
theorem map_ratFunc_C_injective :
    Function.Injective (map (RatFunc.C : F →+* RatFunc F)) :=
  Function.LeftInverse.injective leadingCoeffSpecialization_map_C

/-- The leading-coefficient specialization is surjective, with section the map induced by the
inclusion of constants. -/
theorem leadingCoeffSpecialization_surjective :
    Function.Surjective (leadingCoeffSpecialization F) :=
  Function.LeftInverse.surjective leadingCoeffSpecialization_map_C

/-- The leading-coefficient specialization preserves degrees. -/
theorem leadingCoeffSpecialization_mem_degree {n : ℕ} {x : MilnorK (RatFunc F)}
    (hx : x ∈ degree (RatFunc F) n) : leadingCoeffSpecialization F x ∈ degree F n :=
  map_mem_degree _ (Valuation.milnorSpecialization_mem_degree _ _ _ hx)

end TauCeti.MilnorK
