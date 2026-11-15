/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Generation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Perfectness and projective simplicity of the standard special unitary group

Let `σ` be an involution of a field `K` and let `Q_r = typeAGraphConjugator r K` (`r ≥ 2`). Under
the trace, skew-trace, and (for even `r`) norm hypotheses, together with `r ≠ 2` or existence of
`t ∉ {0, 1}` fixed by `σ`, unitary transvections generate `Q_r.specialIsometryGroup σ` and are
permuted transitively by conjugation. Expressing every unitary transvection along `e₀` as a
Heisenberg commutator (`3 ≤ r`) or torus-transvection commutator (`r = 2`) proves perfectness of
`Q_r.specialIsometryGroup σ` and Iwasawa simplicity of its central quotient.

## Main results

* `TauCeti.commutator_specialIsometryGroup_typeAGraphConjugator`: `Q_r.specialIsometryGroup σ` is
  perfect for `2 ≤ r` when `r ≠ 2` or `{t | σ(t) = t}` has at least three elements.
* `TauCeti.isSimpleGroup_quotient_center_typeAGraphConjugator`: the central quotient of
  `Q_r.specialIsometryGroup σ` is simple under the same hypotheses.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, 3rd ed., Springer (1971), Chapter II, §5.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), §10.6 and §11.5.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization commutatorElement

namespace TauCeti

section Field

variable {K : Type*} [Field K] {σ : K →+* K}

private abbrev stdUnitMat (R : Type*) [Ring R] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  typeAGraphConjugator r R

private theorem unitaryTransvection_single_zero_param_eq_zero (hσ : Function.Involutive σ) {r : ℕ}
    (h0r : (0 : Fin (r + 1)) ≠ Fin.last r) {g : (stdUnitMat K r).specialIsometryGroup σ} {a : K}
    (hg : g.1.1 = (stdUnitMat K r).unitaryTransvection σ (Pi.single 0 1) a) :
    a + (-1 : K) ^ r * σ a = 0 := by
  simpa [Function.comp_def, ← Pi.zero_def] using
    siegelTransvection_single_zero_scalar_eq_zero hσ h0r (w := 0) (by simp) (c := a)
      (by rwa [siegelTransvection_zero_eq_unitaryTransvection])

private theorem exists_siegelTransvection_zero_and_coe_inv (hσ : Function.Involutive σ) {r : ℕ}
    (h0r : (0 : Fin (r + 1)) ≠ Fin.last r) {w : Fin (r + 1) → K}
    (hw : (σ ∘ w) ⬝ᵥ (stdUnitMat K r *ᵥ w) = 0)
    (he0w : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w) = 0) :
    ∃ g : (stdUnitMat K r).specialIsometryGroup σ,
      g.1.1 = (stdUnitMat K r).siegelTransvection σ ((-1 : K) ^ r) (Pi.single 0 1) w 0 ∧
      (g⁻¹).1.1 = (stdUnitMat K r).siegelTransvection σ ((-1 : K) ^ r) (Pi.single 0 1) (-w) 0 := by
  have he0 := comp_single_dotProduct_typeAGraphConjugator_mulVec_single (σ := σ) (i := 0)
    (by rwa [Fin.rev_zero])
  obtain ⟨g₀, hg₀, hcoe⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ
    (transpose_map_typeAGraphConjugator σ r) he0 he0w (c := 0) (by simp [hw])
  refine ⟨⟨g₀, hg₀⟩, hcoe, ?_⟩
  simpa [hw] using coe_inv_eq_siegelTransvection_neg hσ h0r (g := ⟨g₀, hg₀⟩) he0w hcoe

private theorem exists_commutator_coe_eq_unitaryTransvection_of_isotropic
    (hσ : Function.Involutive σ) {r : ℕ} (h0r : (0 : Fin (r + 1)) ≠ Fin.last r)
    {w₁ w₂ : Fin (r + 1) → K} (hw₁ : (σ ∘ w₁) ⬝ᵥ (stdUnitMat K r *ᵥ w₁) = 0)
    (hw₂ : (σ ∘ w₂) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = 0)
    (he0w₁ : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w₁) = 0)
    (he0w₂ : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = 0) :
    ∃ g₁ g₂ : (stdUnitMat K r).specialIsometryGroup σ,
      (⁅g₁, g₂⁆).1.1 = (stdUnitMat K r).unitaryTransvection σ (Pi.single 0 1)
        (σ ((σ ∘ w₁) ⬝ᵥ (stdUnitMat K r *ᵥ w₂)) -
          (-1 : K) ^ r * ((σ ∘ w₁) ⬝ᵥ (stdUnitMat K r *ᵥ w₂))) := by
  have hQ := transpose_map_typeAGraphConjugator σ r
  have he0 := comp_single_dotProduct_typeAGraphConjugator_mulVec_single (σ := σ) (i := 0)
    (by rwa [Fin.rev_zero])
  have hw₁e0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp he0w₁
  have hw₂e0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp he0w₂
  obtain ⟨g₁, hg₁, hg₁i⟩ := exists_siegelTransvection_zero_and_coe_inv hσ h0r hw₁ he0w₁
  obtain ⟨g₂, hg₂, hg₂i⟩ := exists_siegelTransvection_zero_and_coe_inv hσ h0r hw₂ he0w₂
  refine ⟨g₁, g₂, ?_⟩
  change g₁.1.1 * g₂.1.1 * (g₁⁻¹).1.1 * (g₂⁻¹).1.1 = _
  rw [hg₁, hg₂, hg₁i, hg₂i, Matrix.mul_assoc (_ * _),
    siegelTransvection_mul_siegelTransvection he0 he0w₂ hw₁e0,
    siegelTransvection_mul_siegelTransvection he0 (by simp [mulVec_neg, he0w₂])
      (by rw [show σ ∘ (-w₁) = -(σ ∘ w₁) from funext fun _ ↦ map_neg σ _, neg_dotProduct,
        hw₁e0, neg_zero]),
    siegelTransvection_mul_siegelTransvection he0
      (by simp [mulVec_neg, mulVec_add, he0w₁, he0w₂])
      (by rw [comp_add_dotProduct_mulVec, hw₁e0, hw₂e0, add_zero]),
    show w₁ + w₂ + (-w₁ + -w₂) = 0 by abel, siegelTransvection_zero_eq_unitaryTransvection]
  congr 1
  simp only [show (-w₁ + -w₂) = -(w₁ + w₂) by abel, show σ ∘ (-w₁) = -(σ ∘ w₁) from
    funext fun _ ↦ map_neg σ _, mulVec_neg, dotProduct_neg, neg_dotProduct,
    comp_add_dotProduct_mulVec, mulVec_add, dotProduct_add, hw₁, hw₂]
  linear_combination -(apply_comp_dotProduct_mulVec hσ hQ w₁ w₂)

private theorem unitaryTransvection_single_zero_mem_commutator_of_three_le
    (hσ : Function.Involutive σ) (htr : ∀ s : K, σ s = s → ∃ t : K, t + σ t = s) {r : ℕ}
    (hr : 3 ≤ r) {g : (stdUnitMat K r).specialIsometryGroup σ} {a : K}
    (hg : g.1.1 = (stdUnitMat K r).unitaryTransvection σ (Pi.single 0 1) a) :
    g ∈ commutator ((stdUnitMat K r).specialIsometryGroup σ) := by
  have h0r : (0 : Fin (r + 1)) ≠ Fin.last r := by simp [Fin.ext_iff]; omega
  have ha := unitaryTransvection_single_zero_param_eq_zero hσ h0r hg
  have hσa : σ a = (-1 : K) ^ (r + 1) * a := by
    have hsq : ((-1 : K) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [pow_succ, mul_neg_one]; linear_combination (-1 : K) ^ r * ha - σ a * hsq
  obtain ⟨t, ht⟩ := exists_add_neg_one_pow_mul_apply_eq htr (r + 1) hσa
  let i₁ : Fin (r + 1) := ⟨1, by omega⟩
  let j₁ : Fin (r + 1) := i₁.rev
  let w₁ : Fin (r + 1) → K := (-t) • Pi.single i₁ 1
  let w₂ : Fin (r + 1) → K := Pi.single j₁ 1
  have hi₁j₁ : i₁ ≠ j₁ := by simp [i₁, j₁, Fin.ext_iff, Fin.rev]; omega
  have hw₁ : (σ ∘ w₁) ⬝ᵥ (stdUnitMat K r *ᵥ w₁) = 0 := by
    rw [TauCeti.map_comp_smul, smul_dotProduct, mulVec_smul, dotProduct_smul,
      comp_single_dotProduct_typeAGraphConjugator_mulVec_single hi₁j₁, smul_zero, smul_zero]
  have hw₂ : (σ ∘ w₂) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = 0 :=
    comp_single_dotProduct_typeAGraphConjugator_mulVec_single (by simpa [j₁] using hi₁j₁.symm)
  have he0w₁ : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w₁) = 0 := by
    rw [comp_single_zero_dotProduct_typeAGraphConjugator_mulVec]; simp [w₁, i₁, Fin.ext_iff]; omega
  have he0w₂ : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = 0 := by
    rw [comp_single_zero_dotProduct_typeAGraphConjugator_mulVec]
    simp [w₂, j₁, i₁, Fin.ext_iff, Fin.rev]; omega
  obtain ⟨g₁, g₂, hcomm⟩ :=
    exists_commutator_coe_eq_unitaryTransvection_of_isotropic hσ h0r hw₁ hw₂ he0w₁ he0w₂
  have hpair : (σ ∘ w₁) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = σ t := by
    have hc : σ ∘ Pi.single i₁ (1 : K) = Pi.single i₁ 1 := funext fun m ↦ by
      by_cases hm : m = i₁ <;> simp [hm]
    rw [show w₁ = (-t) • Pi.single i₁ 1 from rfl, TauCeti.map_comp_smul, smul_dotProduct, hc,
      single_one_dotProduct, coe_typeAGraphConjugator_mulVec]
    simp [w₂, i₁, j₁]
  have hge : g = ⁅g₁, g₂⁆ := Subtype.ext <| Subtype.ext <| by
    rw [hg, hcomm, hpair, hσ t]; congr 1; rw [pow_succ] at ht; linear_combination -ht
  exact hge ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_top g₁) (Subgroup.mem_top g₂)

private theorem exists_diag_three_mulVec_single_zero (hσ : Function.Involutive σ) {u : K}
    (hu0 : u ≠ 0) :
    ∃ D : (stdUnitMat K 2).specialIsometryGroup σ, D.1.1 *ᵥ Pi.single 0 1 = u • Pi.single 0 1 := by
  have hσu0 : σ u ≠ 0 := (map_ne_zero σ).mpr hu0
  let d : Fin 3 → K := ![u, σ u * u⁻¹, (σ u)⁻¹]
  have hdetD : (diagonal d).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; field_simp
  have hisoD : ((diagonal d).map σ)ᵀ * stdUnitMat K 2 * diagonal d = stdUnitMat K 2 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, stdUnitMat, coe_typeAGraphConjugator_two, d,
        hσ u, hu0, hσu0]
    field_simp
  refine ⟨⟨⟨diagonal d, hdetD⟩, mem_specialIsometryGroup_iff.mpr hisoD⟩, ?_⟩
  ext i; fin_cases i <;> simp [mulVec_diagonal, d]

private theorem unitaryTransvection_single_zero_mem_commutator_two (hσ : Function.Involutive σ)
    {t u : K} (ht : σ t = t) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hu : σ u * u = t)
    {g : (stdUnitMat K 2).specialIsometryGroup σ} {a : K}
    (hg : g.1.1 = (stdUnitMat K 2).unitaryTransvection σ (Pi.single 0 1) a) :
    g ∈ commutator ((stdUnitMat K 2).specialIsometryGroup σ) := by
  have hQ := transpose_map_typeAGraphConjugator σ 2
  have h02 : (0 : Fin 3) ≠ Fin.last 2 := by decide
  have he0 := comp_single_dotProduct_typeAGraphConjugator_mulVec_single (σ := σ) (i := (0 : Fin 3))
    (by decide)
  have ha := unitaryTransvection_single_zero_param_eq_zero hσ h02 hg
  have htsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  obtain ⟨D, hDe0⟩ := exists_diag_three_mulVec_single_zero hσ (right_ne_zero_of_mul (hu ▸ ht0))
  let b : K := (t - 1)⁻¹ * a
  have hb : b + (-1 : K) ^ 2 * σ b = 0 := by
    simp only [b, map_mul, map_inv₀, map_sub, ht, map_one]; linear_combination (t - 1)⁻¹ * ha
  obtain ⟨h₀, hh₀, hcoe⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ he0 hb
  let h : (stdUnitMat K 2).specialIsometryGroup σ := ⟨h₀, hh₀⟩
  have hhi : (h⁻¹).1.1 = (stdUnitMat K 2).unitaryTransvection σ (Pi.single 0 1) (-b) := by
    simpa [Function.comp_def, ← Pi.zero_def, siegelTransvection_zero_eq_unitaryTransvection] using
      coe_inv_eq_siegelTransvection_neg hσ h02 (g := h) (w := 0) (by simp) (c := b)
        (by rwa [siegelTransvection_zero_eq_unitaryTransvection])
  have hmat : g.1.1 = (⁅D, h⁆).1.1 := by
    change g.1.1 = D.1.1 * h.1.1 * (D.1⁻¹ : Matrix.SpecialLinearGroup _ K).1 * (h⁻¹).1.1
    rw [hcoe, coe_mul_unitaryTransvection_mul_coe_inv D.2, hDe0, unitaryTransvection_smul, hhi,
      unitaryTransvection_mul_unitaryTransvection he0, hg]
    congr 1
    calc a = b * (t - 1) := by dsimp only [b]; rw [mul_right_comm, inv_mul_cancel₀ htsub, one_mul]
      _ = b * u * σ u + -b := by linear_combination -b * hu
  exact Subtype.ext (Subtype.ext hmat) ▸
    Subgroup.commutator_mem_commutator (Subgroup.mem_top D) (Subgroup.mem_top h)

private def isotropicPointZero (σ : K →+* K) {r : ℕ} (h0r : (0 : Fin (r + 1)) ≠ Fin.last r) :
    (stdUnitMat K r).isotropicPoints σ :=
  let he0_ne : (Pi.single 0 1 : Fin (r + 1) → K) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  ⟨Projectivization.mk K (Pi.single 0 1) he0_ne,
    (mk_mem_isotropicPoints_iff he0_ne).mpr
      (comp_single_dotProduct_typeAGraphConjugator_mulVec_single (by rwa [Fin.rev_zero]))⟩

/-- **Perfectness of the standard special unitary group.** -/
theorem commutator_specialIsometryGroup_typeAGraphConjugator
    (hσ : Function.Involutive σ) (htr : ∀ s : K, σ s = s → ∃ t : K, t + σ t = s)
    (hadm : ∃ d ≠ (0 : K), d + σ d = 0) {r : ℕ} (hr : 2 ≤ r)
    (hnorm : Even r → ∀ s : K, σ s = s → ∃ b : K, σ b * b = s)
    (hfield : r ≠ 2 ∨ ∃ t : K, σ t = t ∧ t ≠ 0 ∧ t ≠ 1) :
    commutator ((typeAGraphConjugator r K :
      Matrix (Fin (r + 1)) (Fin (r + 1)) K).specialIsometryGroup σ) = ⊤ := by
  have := isPretransitive_isotropicPoints hσ (transpose_map_typeAGraphConjugator σ r)
    (isUnits_det_units _).ne_zero (fun _ ↦ exists_add_neg_one_pow_mul_apply_eq htr r)
    (exists_ne_zero_add_neg_one_pow_mul_apply_eq_zero hadm r)
  have h0r : (0 : Fin (r + 1)) ≠ Fin.last r := by simp [Fin.ext_iff]; omega
  let p₀ := isotropicPointZero σ h0r
  rw [eq_top_iff, ← iSup_unitaryTransvectionSubgroup_typeAGraphConjugator hσ htr hadm
    (fun he _ ↦ hnorm he) hfield]
  refine iSup_unitaryTransvectionSubgroup_le_of_normal p₀ fun g hg ↦ ?_
  obtain ⟨a, hga⟩ := (mem_unitaryTransvectionSubgroup_mk_iff
    (Pi.single_ne_zero_iff.mpr one_ne_zero) p₀.2).mp hg
  rcases eq_or_lt_of_le hr with rfl | hr3
  · obtain ⟨t, ht, ht0, ht1⟩ := hfield.resolve_left (by decide)
    obtain ⟨u, hu⟩ := hnorm even_two t ht
    exact unitaryTransvection_single_zero_mem_commutator_two hσ ht ht0 ht1 hu hga
  · exact unitaryTransvection_single_zero_mem_commutator_of_three_le hσ htr hr3 hga

/-- **Simplicity of the standard projective special unitary group.** -/
theorem isSimpleGroup_quotient_center_typeAGraphConjugator
    (hσ : Function.Involutive σ) (htr : ∀ s : K, σ s = s → ∃ t : K, t + σ t = s)
    (hadm : ∃ d ≠ (0 : K), d + σ d = 0) {r : ℕ} (hr : 2 ≤ r)
    (hnorm : Even r → ∀ s : K, σ s = s → ∃ b : K, σ b * b = s)
    (hfield : r ≠ 2 ∨ ∃ t : K, σ t = t ∧ t ≠ 0 ∧ t ≠ 1) :
    IsSimpleGroup ((typeAGraphConjugator r K :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K).specialIsometryGroup σ ⧸
      Subgroup.center ((typeAGraphConjugator r K :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K).specialIsometryGroup σ)) := by
  have : Nonempty ((stdUnitMat K r).isotropicPoints σ) :=
    ⟨isotropicPointZero σ (by simp [Fin.ext_iff]; omega)⟩
  exact isSimpleGroup_quotient_center_specialIsometryGroup hσ
    (transpose_map_typeAGraphConjugator σ r) (isUnits_det_units _).ne_zero
    (fun _ ↦ exists_add_neg_one_pow_mul_apply_eq htr r)
    (exists_ne_zero_add_neg_one_pow_mul_apply_eq_zero hadm r)
    (iSup_unitaryTransvectionSubgroup_typeAGraphConjugator hσ htr hadm (fun he _ ↦ hnorm he) hfield)
    (commutator_specialIsometryGroup_typeAGraphConjugator hσ htr hadm hr hnorm hfield)

end Field

end TauCeti
