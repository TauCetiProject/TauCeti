/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.ComplexTrace
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Torsion in principal Bianchi congruence subgroups

If an integral matrix `A` of determinant one reduces to the identity modulo `I`, then
`det (1 - A) = 2 - tr A` lies in `I²`. If its projective class is nontrivial of finite order,
every complex embedding sends this determinant into the open real interval `(0, 4)`.
The determinant bound `Matrix.det_mem_pow_card` and the product formula
`NumberField.prod_norm_embedding_eq_abs_norm` then give `0 < N(I) < 2 ^ [K : ℚ]`.

Over a quadratic field this leaves only the ideal norms `1`, `2`, and `3`. Since the absolute
norm of an ideal belongs to the ideal, the principal congruence subgroup in `PSL(2, ℂ)` is
torsion-free whenever the level contains neither `2` nor `3`.
-/

public section

open NumberField TauCeti.SpecialLinear
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {K : Type*} [Field K] [NumberField K]

/-- All complex embeddings send the trace defect `2 - tr A` of a lift of nontrivial projective
torsion into `(0, 4)`. Its absolute field norm is consequently positive and less than
`4 ^ [K : ℚ]`. -/
theorem natAbs_norm_two_sub_trace_mem_Ioo_of_isOfFinOrder_mk {A : SL(2, 𝓞 K)}
    (hfin : IsOfFinOrder (A : PSL(2, 𝓞 K))) (hne : (A : PSL(2, 𝓞 K)) ≠ 1) :
    (Algebra.norm ℤ (2 - A.val.trace)).natAbs ∈ Set.Ioo 0 (4 ^ Module.finrank ℚ K) := by
  let x : 𝓞 K := 2 - A.val.trace
  have hx (σ : K →+* ℂ) : ‖σ (x : K)‖ ∈ Set.Ioo 0 4 := by
    let f := σ.comp (algebraMap (𝓞 K) K)
    have hf := projectiveMap_injective 2 (f := f) (σ.injective.comp RingOfIntegers.coe_injective)
    have hσ := (projectiveMap 2 f).isOfFinOrder hfin
    have hσ' := (hf.ne hne : projectiveMap 2 f (A : PSL(2, 𝓞 K)) ≠ projectiveMap 2 f 1)
    rw [projectiveMap_mk] at hσ
    rw [projectiveMap_mk, map_one] at hσ'
    obtain ⟨t, ht, he⟩ := ProjectiveSpecialLinearGroup.trace_mem_ofReal_image_Ioo_of_isOfFinOrder_mk
      hσ hσ'
    rw [map_apply_coe, ← AddMonoidHom.map_trace] at he
    have he' : σ (x : K) = ((2 - t : ℝ) : ℂ) := by
      simp only [x, map_sub, map_ofNat, Complex.ofReal_sub, Complex.ofReal_ofNat]
      simpa [f] using congrArg ((2 : ℂ) - ·) he.symm
    rw [he', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.2)]
    exact ⟨sub_pos.mpr ht.2, by linarith [ht.1]⟩
  have hprod : ∏ σ : K →+* ℂ, ‖σ (x : K)‖ < ∏ _σ : K →+* ℂ, (4 : ℝ) :=
    Finset.prod_lt_prod_of_nonempty₀ (fun σ _ ↦ (hx σ).1) (fun σ _ ↦ (hx σ).2)
      Finset.univ_nonempty
  have hpos := Finset.prod_pos (s := Finset.univ) fun σ _ ↦ (hx σ).1
  rw [prod_norm_embedding_eq_abs_norm, ← Algebra.coe_norm_int, Rat.cast_intCast,
    ← Int.cast_abs] at hpos hprod
  simp only [Finset.prod_const, Finset.card_univ, Embeddings.card] at hprod
  rw [Int.abs_eq_natAbs] at hpos hprod
  exact ⟨by exact_mod_cast hpos, by exact_mod_cast hprod⟩

/-- A nonidentity torsion class represented by a matrix congruent to the identity modulo `I`
forces the absolute ideal norm of `I` to lie strictly between zero and `2 ^ [K : ℚ]`. -/
theorem absNorm_mem_Ioo_of_isOfFinOrder_mk {I : Ideal (𝓞 K)} {A : SL(2, 𝓞 K)}
    (hA : A ∈ (map (Ideal.Quotient.mk I)).ker) (hfin : IsOfFinOrder (A : PSL(2, 𝓞 K)))
    (hne : (A : PSL(2, 𝓞 K)) ≠ 1) :
    I.absNorm ∈ Set.Ioo 0 (2 ^ Module.finrank ℚ K) := by
  have hentries (i j : Fin 2) : (1 - A.val) i j ∈ I := by
    rw [Matrix.sub_apply, ← neg_sub]
    exact I.neg_mem (mem_ker_map_quotientMk_iff.mp hA i j)
  have hdet := (1 - A.val).det_mem_pow_card hentries
  simp only [det_one_sub_eq_two_sub_trace_of_det_eq_one A.det_coe, Fintype.card_fin] at hdet
  have hd := Ideal.absNorm_dvd_norm_of_mem hdet
  rw [map_pow] at hd
  have hd' := Int.natAbs_dvd_natAbs.mpr hd
  simp only [Int.natAbs_natCast] at hd'
  have ht := natAbs_norm_two_sub_trace_mem_Ioo_of_isOfFinOrder_mk hfin hne
  refine ⟨Nat.pos_of_ne_zero (fun h ↦ ?_), ?_⟩
  · simp [h, ht.1.ne'] at hd'
  · have hlt := (Nat.le_of_dvd ht.1 hd').trans_lt ht.2
    apply (Nat.pow_lt_pow_iff_left (n := 2) (by decide)).mp
    simpa only [pow_right_comm (2 : ℕ) _ 2, Nat.reducePow] using hlt

/-- Over any number field of degree at most two, the complex projective image of the principal
congruence subgroup is torsion-free if the level contains neither `2` nor `3`. -/
theorem isMulTorsionFree_map_ker_of_finrank_le_two (ι : K →+* ℂ) (hK : Module.finrank ℚ K ≤ 2)
    {I : Ideal (𝓞 K)} (h₂ : (2 : 𝓞 K) ∉ I) (h₃ : (3 : 𝓞 K) ∉ I) :
    IsMulTorsionFree ((map (n := Fin 2) (Ideal.Quotient.mk I)).ker.map
      ((QuotientGroup.mk' (Subgroup.center SL(2, ℂ))).comp
        (map (ι.comp (algebraMap (𝓞 K) K))))) := by
  apply IsMulTorsionFree.of_not_isOfFinOrder
  rintro ⟨g, A, hA, rfl⟩ hne hfin
  let f := ι.comp (algebraMap (𝓞 K) K)
  have hf := projectiveMap_injective 2 (f := f) (ι.injective.comp RingOfIntegers.coe_injective)
  have ht : IsOfFinOrder (projectiveMap 2 f (A : PSL(2, 𝓞 K))) := by
    rw [projectiveMap_mk]
    exact Submonoid.isOfFinOrder_coe.2 hfin
  have hA' : (A : PSL(2, 𝓞 K)) ≠ 1 := by
    intro h
    apply hne
    apply Subtype.ext
    simpa only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, OneMemClass.coe_one,
      projectiveMap_mk, map_one] using congrArg (projectiveMap 2 f) h
  obtain ⟨hpos, hlt⟩ := absNorm_mem_Ioo_of_isOfFinOrder_mk hA (hf.isOfFinOrder_iff.mp ht) hA'
  have hb : I.absNorm < 4 := hlt.trans_le (Nat.pow_le_pow_right (by decide) hK)
  have hm := I.absNorm_mem
  interval_cases h : I.absNorm
  · exact h₂ (by simp [Ideal.absNorm_eq_one_iff.mp h])
  · exact h₂ (by simpa [h] using hm)
  · exact h₃ (by simpa [h] using hm)

end Matrix.SpecialLinearGroup
