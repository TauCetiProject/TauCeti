/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.InfinitePlace
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Archimedean

/-!
# Weights on norm-one ideles relative to a CM type

The CM type chooses a complex embedding above each infinite place. Changing the embedding
conjugates the circle coordinate, or equivalently negates its exponent. Ideles with trivial
finite part detect all exponents, so finite residue factors cannot hide a change in weight.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.GlobalNumberFields

/-- Two weights that give the same character on the norm-one ideles with trivial finite
part are equal. -/
theorem eq_of_normOneWeightCharacter_eq_on_trivialFinite {E : Type*} [Field E]
    [NumberField E] [IsCMField E] {e f : InfinitePlace E → ℤ}
    (h : ∀ x : (ideleNormMap (maximalRealSubfield E) E).toMonoidHom.ker,
      IdeleGroup.toFiniteIdele (𝓞 E) E x.val = 1 →
        normOneWeightCharacter e x = normOneWeightCharacter f x) : e = f := by
  classical
  funext w
  by_contra hne
  let d : ℤ := e w - f w
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
  let z := Circle.exp (Real.pi / (d : ℝ))
  obtain ⟨x, hx, hc⟩ := exists_normOneCircleCoord_eq (Pi.mulSingle w z)
  have heq := h x hx
  simp only [normOneWeightCharacter_apply, hc, Pi.mulSingle_apply] at heq
  have hw : z ^ e w = z ^ f w := by
    simpa using heq
  have hd' : z ^ d = 1 := by
    simp [d, zpow_sub, hw]
  apply Circle.exp_pi_ne_one
  calc
    Circle.exp Real.pi = Circle.exp ((d : ℝ) * (Real.pi / (d : ℝ))) := by
      rw [mul_div_cancel₀ _ hd]
    _ = z ^ d := Circle.exp_intCast_mul _ _
    _ = 1 := hd'

end TauCeti.GlobalNumberFields

namespace TauCeti.CMType

open GlobalNumberFields NumberField.InfinitePlace.Completion

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

local notation "U" => MonoidHom.ker
  (ContinuousMonoidHom.toMonoidHom (ideleNormMap (maximalRealSubfield E) E))

/-- The weight character using the embeddings of `Φ` rather than the default representatives
of the infinite places. Conjugation on a circle coordinate negates its exponent. -/
noncomputable def normOneWeightCharacter (Φ : CMType E) (e : InfinitePlace E → ℤ) : U →ₜ* Circle :=
  open scoped Classical in
  GlobalNumberFields.normOneWeightCharacter (fun w ↦ if w.embedding ∈ Φ then e w else -e w)

/-- The complex value of the weight character is the product of the powers of the coordinates
read through the completion embeddings of the CM type. -/
theorem coe_normOneWeightCharacter_apply (Φ : CMType E) (e : InfinitePlace E → ℤ) (x : U) :
    (Φ.normOneWeightCharacter e x : ℂ) =
      ∏ w, Φ.completionEmbedding w (w.ideleInfiniteCoord x.val : w.Completion) ^ e w := by
  unfold normOneWeightCharacter
  rw [GlobalNumberFields.normOneWeightCharacter_apply]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun w _ ↦ ?_)
  by_cases hw : w.embedding ∈ Φ
  · rw [ite_eq_left hw, Φ.completionEmbedding_of_mem hw]
    exact (map_zpow Circle.coeHom _ _).trans
      (congrArg (· ^ e w) (coe_normOneCircleCoord w x))
  · rw [ite_eq_right hw, Φ.completionEmbedding_of_notMem hw, RingHom.comp_apply]
    rw [zpow_neg, ← inv_zpow]
    exact (map_zpow Circle.coeHom _ _).trans (congrArg (· ^ e w)
      ((Circle.coe_inv_eq_conj (w.normOneCircleCoord x)).trans
        (congrArg (starRingEnd ℂ) (coe_normOneCircleCoord w x))))

/-- For a fixed CM type, equality on the ideles with trivial finite part implies equality of
weights. -/
theorem eq_of_normOneWeightCharacter_eq_on_trivialFinite (Φ : CMType E)
    {e f : InfinitePlace E → ℤ} (h : ∀ x : U,
      IdeleGroup.toFiniteIdele (𝓞 E) E x.val = 1 →
        Φ.normOneWeightCharacter e x = Φ.normOneWeightCharacter f x) : e = f := by
  unfold normOneWeightCharacter at h
  have hw := GlobalNumberFields.eq_of_normOneWeightCharacter_eq_on_trivialFinite h
  funext w
  by_cases hm : w.embedding ∈ Φ <;> simpa [hm] using congrFun hw w

end TauCeti.CMType
