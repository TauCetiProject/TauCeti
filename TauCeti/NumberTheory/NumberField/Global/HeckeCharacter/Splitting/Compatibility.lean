/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.NumberTheory.NumberField.CMType.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
import TauCeti.NumberTheory.NumberField.CMField.IntegralAdeleNorm
import TauCeti.NumberTheory.NumberField.CMField.IntegralNormOne
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.CM
import TauCeti.NumberTheory.QuadraticForm.Global.IdeleCharacter
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula

/-!
# Compatibility of the archimedean phase with CM idele norms

To prescribe an unramified splitting character, the archimedean phase must be trivial on
products of principal ideles and CM idele norms whose finite parts are integral units.
Dividing the principal element by a suitable global unit makes it real without changing its
phase. An integral norm then cancels the finite part, and Hilbert reciprocity makes the
product of the real signs trivial.

See O. T. O'Meara, *Introduction to Quadratic Forms*, §71, for Hilbert reciprocity, and
`New.Cohomology.υ_star_eq_inv_and_apply_eq` in
`grh/src/Lib/ClassField/Global/CMSplittingCharacters.lean` of lsernau/grh-lean (revision `72fead1`)
for the application to splitting characters.
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField NumberField.InfinitePlace
  TauCeti.GlobalNumberFields TauCeti.NumberField.QuadraticForm
open TauCeti (hilbertSymbol hilbertSymbol_one_left hilbertSymbol_productFormula
  hilbertSymbol_completion_eq_unitAtRealPlace hilbertSymbol_unitAtRealPlace_eq_neg_one_iff
  hilbertSymbol_unitAtRealPlace_eq_one_iff)
open scoped NumberField

namespace TauCeti.CMType

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

local notation "F" => maximalRealSubfield E
local notation "A" => FiniteAdeleRing (𝓞 E) E

/-- At a real place of the base, the phase of the principal factor is its local quadratic
symbol against a negative element. -/
private theorem phase_algebraMap_eq_hilbertSymbol (Φ : CMType E) (a b : Fˣ)
    (hneg : ∀ v : {v : InfinitePlace F // v.IsReal}, embedding_of_isReal v.property (b : F) < 0)
    (w : InfinitePlace E) :
    Φ.embedding w (algebraMap F E (a : F)) / ‖Φ.embedding w (algebraMap F E (a : F))‖ =
      ((hilbertSymbol ((equivInfinitePlace E w).ideleInfiniteCoord
        (IdeleGroup.unitEmbedding (𝓞 F) F a))
        (Units.map (algebraMap F (equivInfinitePlace E w).Completion).toMonoidHom b) : ℤ) : ℂ) := by
  let v := equivInfinitePlace E w
  have hvreal : v.IsReal := IsTotallyReal.isReal v
  let t := embedding_of_isReal hvreal (a : F)
  have he : Φ.embedding w (algebraMap F E (a : F)) = (t : ℂ) := by
    have hv : InfinitePlace.mk ((Φ.embedding w).comp (algebraMap F E)) = v := by
      simpa only [← comap_mk, Φ.mk_embedding] using (equivInfinitePlace_apply E w).symm
    rw [embedding_of_isReal_apply, ← hv,
      embedding_mk_eq_of_isReal (isReal_of_mk_isReal (hv ▸ hvreal))]
    rfl
  rw [he, Complex.norm_real, ← Complex.ofReal_div, ideleInfiniteCoord_unitEmbedding,
    hilbertSymbol_completion_eq_unitAtRealPlace ⟨v, hvreal⟩]
  have ht : t ≠ 0 := (map_ne_zero (embedding_of_isReal hvreal)).2 a.ne_zero
  rcases lt_or_gt_of_ne ht with ht' | ht'
  · rw [(hilbertSymbol_unitAtRealPlace_eq_neg_one_iff ⟨v, hvreal⟩ a b).2
      ⟨ht', hneg ⟨v, hvreal⟩⟩, Real.norm_eq_abs, abs_of_neg ht']
    simp [ht]
  · rw [(hilbertSymbol_unitAtRealPlace_eq_one_iff ⟨v, hvreal⟩ a b).2 (Or.inl ht'),
      Real.norm_eq_abs, abs_of_pos ht', div_self ht]
    norm_num

/-- If the finite principal idele of `a ∈ E⁺ˣ` is the inverse of a finite CM idele norm,
the product of the phases of `a` at any CM type of `E` is one. -/
theorem prod_phase_eq_one_of_finite_norm (Φ : CMType E) (a : Fˣ) (z : Aˣ)
    (hz : algebraMap E A (algebraMap F E (a : F)) * (z : A) * star (z : A) = 1) :
    ∏ w : InfinitePlace E, Φ.embedding w (algebraMap F E (a : F)) /
      ‖Φ.embedding w (algebraMap F E (a : F))‖ = 1 := by
  classical
  obtain ⟨b, hsq, hneg⟩ := TauCeti.NumberField.IsCMField.exists_isSquare_algebraMap_and_neg (K := E)
  let y := IdeleGroup.ofFiniteIdele (𝓞 E) E z
  let x := IdeleGroup.unitEmbedding (𝓞 F) F a * ideleNormMap F E y
  have hx' : (IdeleGroup.toFiniteIdele (𝓞 E) E (ideleExtension F E x) : A) = 1 := by
    simpa only [x, y, map_mul, Units.val_mul, ideleExtension_unitEmbedding,
      IdeleGroup.toFiniteIdele_unitEmbedding, FiniteAdeleRing.unitEmbedding,
      Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      IdeleGroup.coe_toFiniteIdele_ideleExtension_ideleNormMap,
      IdeleGroup.toFiniteIdele_ofFiniteIdele, mul_assoc] using hz
  have hx (v : HeightOneSpectrum (𝓞 F)) : v.ideleFiniteCoord x = 1 := by
    obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 F) (𝓞 E) v
    apply Units.ext
    apply (HeightOneSpectrum.adicCompletionExtension F E (w.under (𝓞 F)) w).injective
    have hh := congrArg (fun c : A ↦ c w) hx'
    rw [IdeleGroup.coe_toFiniteIdele, ← HeightOneSpectrum.coe_ideleFiniteCoord,
      ideleFiniteCoord_ideleExtension,
      Units.coe_map, FiniteAdeleRing.one_apply] at hh
    simpa using hh
  have hchar : ideleHilbertCharacter b x = 1 := by
    simp [x, ideleHilbertCharacter_unitEmbedding, hilbertSymbol_productFormula,
      ideleHilbertCharacter_ideleNormMap hsq]
  let χ (v : InfinitePlace F) : ℤˣ := hilbertSymbol
    (v.ideleInfiniteCoord (IdeleGroup.unitEmbedding (𝓞 F) F a))
    (Units.map (algebraMap F v.Completion).toMonoidHom b)
  rw [ideleHilbertCharacter_apply] at hchar
  simp only [hx, hilbertSymbol_one_left, finprod_one, mul_one] at hchar
  have hprod : ∏ v : InfinitePlace F, χ v = 1 := by
    simpa only [χ, x, hilbertSymbol_ideleInfiniteCoord_unitEmbedding_mul_ideleNormMap hsq,
      ideleInfiniteCoord_unitEmbedding] using hchar
  simp_rw [Φ.phase_algebraMap_eq_hilbertSymbol a b hneg]
  let f := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
  calc
    _ = ∏ v : InfinitePlace F, f (χ v) := (equivInfinitePlace E).prod_comp (f ∘ χ)
    _ = 1 := by rw [← map_prod, hprod, map_one]

open FiniteAdeleRing in
/-- Dividing an integral finite product by its conjugate cancels the norm factor, so the
quotient of the principal factors is an integral norm-one element. -/
private theorem isOfFinOrder_div_complexConj_of_mul_norm_mem_integralUnits (a : Eˣ) (z : Aˣ)
    (hu : unitEmbedding (𝓞 E) E a * (z * star z) ∈ integralUnits (𝓞 E) E) :
    IsOfFinOrder ((a : E) / complexConj E (a : E)) := by
  let u := unitEmbedding (𝓞 E) E a * (z * star z)
  have hc : star u ∈ integralUnits (𝓞 E) E := by
    simpa only [mem_integralUnits_iff_val_mem_and_inv_mem, Units.coe_star,
      Units.coe_star_inv, star_mem_integralAdeles_iff] using hu
  have he : ((u / star u : Aˣ) : A) = algebraMap E A ((a : E) / complexConj E (a : E)) := by
    have hs : star (unitEmbedding (𝓞 E) E a) =
        unitEmbedding (𝓞 E) E (Units.map (complexConj E).toMonoidHom a) := by
      apply Units.ext
      simp
    have h : u / star u = unitEmbedding (𝓞 E) E (a / Units.map (complexConj E).toMonoidHom a) := by
      dsimp only [u]
      rw [star_mul, star_mul, star_star, hs, mul_comm (z * star z),
        mul_div_mul_right_eq_div, map_div]
    rw [h, unitEmbedding_apply, Units.val_div_eq_div_val, Units.coe_map]
    rfl
  have hint := (mem_integralUnits_iff_val_mem_and_inv_mem.mp
    ((integralUnits (𝓞 E) E).div_mem hu hc)).1
  rw [he] at hint
  obtain ⟨c, hc⟩ := (algebraMap_mem_integralAdeles_iff _).mp hint
  exact NumberField.IsCMField.isOfFinOrder_iff_isIntegral_and_mul_complexConj_eq_one.mpr
    ⟨hc ▸ RingOfIntegers.isIntegral_coe c,
      div_complexConj_mul_complexConj_div_complexConj_eq_one a⟩

open FiniteAdeleRing in
/-- When the finite product of a real principal idele and a CM idele norm is an integral unit,
it can be made exactly one by correcting the norm by an integral unit. -/
private theorem prod_phase_eq_one_of_finite_norm_mem_integralUnits (Φ : CMType E)
    {ζ₄ ζ₇ : E} (h₄ : IsPrimitiveRoot ζ₄ 4) (h₇ : IsPrimitiveRoot ζ₇ 7)
    (a : Fˣ) (z : Aˣ)
    (hu : unitEmbedding (𝓞 E) E (Units.map (algebraMap F E).toMonoidHom a) *
      (z * star z) ∈ integralUnits (𝓞 E) E) :
    ∏ w : InfinitePlace E, Φ.embedding w (algebraMap F E (a : F)) /
      ‖Φ.embedding w (algebraMap F E (a : F))‖ = 1 := by
  let u := unitEmbedding (𝓞 E) E (Units.map (algebraMap F E).toMonoidHom a) * (z * star z)
  have hstar : star u = u := by
    apply Units.ext
    simp only [u, Units.coe_star, Units.val_mul, unitEmbedding_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, star_mul, star_star,
      ← coe_finiteAdeleConj E, finiteAdeleConj_algebraMap, AlgEquiv.commutes]
    ac_rfl
  rw [← range_units_map_val_eq_integralUnits] at hu
  let f := Units.map (integralAdeles (𝓞 E) E).val.toRingHom.toMonoidHom
  obtain ⟨u₀, hu₀ : f u₀ = u⟩ := hu
  have hf (v : (integralAdeles (𝓞 E) E)ˣ) : f (star v) = star (f v) := by
    apply Units.ext
    exact coe_star_integralAdeles (v : integralAdeles (𝓞 E) E)
  have hfix : star u₀ = u₀ := by
    have hf_inj : Function.Injective f := Units.map_injective
      (f := (integralAdeles (𝓞 E) E).val.toRingHom.toMonoidHom) Subtype.val_injective
    apply hf_inj
    rw [← hu₀] at hstar
    exact (hf u₀).trans hstar
  obtain ⟨v, hv⟩ := exists_star_mul_self_eq_of_isPrimitiveRoot h₄ h₇ u₀ hfix
  have hv' : star (f v) * f v = u := by
    simpa only [map_mul, hf, hu₀] using congrArg f hv
  apply Φ.prod_phase_eq_one_of_finite_norm a (z / f v)
  have hone : unitEmbedding (𝓞 E) E (Units.map (algebraMap F E).toMonoidHom a) *
      (z / f v) * star (z / f v) = 1 := by
    rw [star_div, mul_assoc, div_mul_div_comm, mul_comm (f v), hv', ← mul_div_assoc]
    exact div_self' u
  simpa only [Units.val_mul, Units.coe_star, unitEmbedding_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Units.val_one] using
      congrArg (fun t : Aˣ ↦ (t : A)) hone

open FiniteAdeleRing in
/-- The archimedean phase is trivial on the intersection of the integral-finite ideles with
products of a principal idele and a CM norm. The root-of-unity condition makes it possible
to replace the principal element by a real one without changing its phase. -/
theorem prod_phase_eq_one_of_principal_mul_norm_integral (Φ : CMType E)
    {ζ₄ ζ₇ : E} (h₄ : IsPrimitiveRoot ζ₄ 4) (h₇ : IsPrimitiveRoot ζ₇ 7)
    (hroots : ∀ x : E, IsOfFinOrder x → ∃ δ : (𝓞 E)ˣ,
      (δ : E) / complexConj E (δ : E) = x ∧ ∏ w : InfinitePlace E, Φ.embedding w (δ : E) = 1)
    (a : Eˣ) (z : Aˣ)
    (hu : unitEmbedding (𝓞 E) E a * (z * star z) ∈ integralUnits (𝓞 E) E) :
    ∏ w : InfinitePlace E, Φ.embedding w (a : E) / ‖Φ.embedding w (a : E)‖ = 1 := by
  obtain ⟨δ, hδ, hΦ⟩ := hroots _ (isOfFinOrder_div_complexConj_of_mul_norm_mem_integralUnits a z hu)
  let δ' : Eˣ := Units.map (algebraMap (𝓞 E) E).toMonoidHom δ
  have hδ₀ : (δ : E) ≠ 0 := δ'.ne_zero
  have ha₀ : complexConj E (a : E) ≠ 0 := (map_ne_zero (complexConj E)).2 a.ne_zero
  have hd₀ : complexConj E (δ : E) ≠ 0 := (map_ne_zero (complexConj E)).2 hδ₀
  have hfix : complexConj E ((a / δ' : Eˣ) : E) = (a / δ' : Eˣ) := by
    simp only [Units.val_div_eq_div_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, δ', map_div₀]
    exact (div_eq_div_iff hd₀ hδ₀).mpr (mul_comm _ _ |>.trans ((div_eq_div_iff hd₀ ha₀).mp hδ))
  let b : Fˣ := Units.mk0 ⟨(a / δ' : Eˣ), (complexConj_eq_self_iff E _).mp hfix⟩
    (fun h ↦ (a / δ').ne_zero (congrArg Subtype.val h))
  have hb : Units.map (algebraMap F E).toMonoidHom b = a / δ' := Units.ext rfl
  have hmem : unitEmbedding (𝓞 E) E (Units.map (algebraMap F E).toMonoidHom b) *
      (z * star z) ∈ integralUnits (𝓞 E) E := by
    rw [hb, map_div, div_mul_eq_mul_div]
    exact (integralUnits (𝓞 E) E).div_mem hu
      (unitEmbedding_map_algebraMap_mem_integralUnits δ)
  have hphase := Φ.prod_phase_eq_one_of_finite_norm_mem_integralUnits h₄ h₇ b z hmem
  have hbδ : a = δ' * Units.map (algebraMap F E).toMonoidHom b := by rw [hb, mul_div_cancel]
  rw [hbδ]
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, δ', map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm,
    Finset.prod_mul_distrib, hphase, mul_one]
  rw [Finset.prod_div_distrib, ← Complex.ofReal_prod, ← norm_prod, hΦ]
  simp

end TauCeti.CMType
