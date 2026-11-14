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

Let `σ` be an involution of a field `K` and let `Q_r = typeAGraphConjugator r K` be the `(r + 1)` by
`(r + 1)` signed anti-diagonal Gram matrix (`r ≥ 2`). Assume that `t ↦ t + σ(t)` is onto
`{s | σ(s) = s}`, `d + σ(d) = 0` has a nonzero solution, `b ↦ σ(b) * b` is onto `{s | σ(s) = s}`
when `r` is even, and that either `r ≠ 2` or `{t : K | σ(t) = t}` has at least three elements
(excluding `SU₃(2)`).

By `TauCeti.iSup_unitaryTransvectionSubgroup_typeAGraphConjugator`, the unitary transvection
subgroups generate `Q_r.specialIsometryGroup σ`, and by `Matrix.isPretransitive_isotropicPoints`
conjugation permutes them transitively. To prove that `Q_r.specialIsometryGroup σ` is perfect, it
therefore suffices (`Matrix.iSup_unitaryTransvectionSubgroup_le_of_normal`) to express every
unitary transvection `τ_{e₀, a}` (`a + (-1) ^ r * σ(a) = 0`) at `[e₀]` as a commutator:

* When `3 ≤ r`, the orthogonal complement `{e₀, e_r}^⊥` contains the isotropic pair `(e₁, e_{r-1})`
  with `B(e₁, e_{r-1}) = -1`. In the Heisenberg group of Siegel transformations along `e₀`, the
  commutator of `S(e₀, b • e₁, 0)` and `S(e₀, e_{r-1}, 0)` is the unitary transvection
  `τ_{e₀, -b + (-1) ^ r * σ(b)}`, and surjectivity of the twisted trace supplies `b` for every
  admissible `a`.
* When `r = 2`, picking `t ∈ K \ {0, 1}` with `σ(t) = t` and `u ∈ K` with `σ(u) * u = t`, the
  diagonal special isometry `diag(u, σ(u) * u⁻¹, σ(u)⁻¹)` rescales `e₀` by `u`, so its commutator
  with `τ_{e₀, (t - 1)⁻¹ * a}` is `τ_{e₀, a}`.

Combining perfectness and transvection generation with
`Matrix.isSimpleGroup_quotient_center_specialIsometryGroup` proves Iwasawa's theorem for the
standard projective special unitary group `Q_r.specialIsometryGroup σ ⧸ Subgroup.center _`.

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

private theorem comp_single_zero_dotProduct_stdUnitMat_mulVec {r : ℕ} (v : Fin (r + 1) → K) :
    (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ v) = v (Fin.last r) := by
  have hc : σ ∘ Pi.single (0 : Fin (r + 1)) (1 : K) = Pi.single 0 1 := funext fun j ↦ by
    by_cases hj : j = 0 <;> simp [hj]
  rw [hc, single_one_dotProduct, coe_typeAGraphConjugator_mulVec]
  simp [Fin.rev_zero]

/-- Every unitary transvection `τ_{e₀, a}` in `Q_r.specialIsometryGroup σ` (`0 < r`) satisfies
`a + (-1) ^ r * σ(a) = 0`. -/
private theorem unitaryTransvection_single_zero_param_eq_zero (hσ : Function.Involutive σ) {r : ℕ}
    (h0r : (0 : Fin (r + 1)) ≠ Fin.last r) {g : (stdUnitMat K r).specialIsometryGroup σ} {a : K}
    (hg : ((g : Matrix.SpecialLinearGroup (Fin (r + 1)) K) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K) =
      (stdUnitMat K r).unitaryTransvection σ (Pi.single 0 1) a) :
    a + (-1 : K) ^ r * σ a = 0 := by
  have he0 := comp_single_dotProduct_typeAGraphConjugator_mulVec_single (σ := σ) (i := 0)
    (by rwa [Fin.rev_zero])
  have hiso := mem_specialIsometryGroup_iff.mp g.2
  rw [hg, transpose_map_unitaryTransvection_mul_mul hσ (transpose_map_typeAGraphConjugator σ r)
    he0] at hiso
  have hentry := congrArg (fun M ↦ M (Fin.last r) (Fin.last r)) (add_eq_left.mp hiso)
  have hQe0 : (stdUnitMat K r *ᵥ Pi.single 0 1) (Fin.last r) = (-1 : K) ^ r := by
    rw [coe_typeAGraphConjugator_mulVec]; simp [Fin.rev_last]
  have he0Q : ((σ ∘ Pi.single (0 : Fin (r + 1)) 1) ᵥ* stdUnitMat K r) (Fin.last r) = 1 := by
    have hc : σ ∘ Pi.single (0 : Fin (r + 1)) (1 : K) = Pi.single 0 1 := funext fun j ↦ by
      by_cases hj : j = 0 <;> simp [hj]
    rw [hc, single_one_vecMul]; simp [typeAGraphConjugator_apply, Fin.rev_zero]
  simp only [Matrix.smul_apply, vecMulVec_apply, hQe0, he0Q, mul_one, smul_eq_mul] at hentry
  exact (mul_eq_zero.mp hentry).resolve_right (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero))

/-- For an isotropic `w` orthogonal to `e₀`, `S(e₀, w, 0)` belongs to `Q_r.specialIsometryGroup σ`
and its inverse has matrix `S(e₀, -w, 0)`. -/
private theorem exists_siegelTransvection_zero_and_coe_inv (hσ : Function.Involutive σ) {r : ℕ}
    (h0r : (0 : Fin (r + 1)) ≠ Fin.last r) {w : Fin (r + 1) → K}
    (hw : (σ ∘ w) ⬝ᵥ (stdUnitMat K r *ᵥ w) = 0)
    (he0w : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w) = 0) :
    ∃ g : (stdUnitMat K r).specialIsometryGroup σ,
      ((g : Matrix.SpecialLinearGroup (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) =
        (stdUnitMat K r).siegelTransvection σ ((-1 : K) ^ r) (Pi.single 0 1) w 0 ∧
      (((g⁻¹ : (stdUnitMat K r).specialIsometryGroup σ) :
          Matrix.SpecialLinearGroup (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) =
        (stdUnitMat K r).siegelTransvection σ ((-1 : K) ^ r) (Pi.single 0 1) (-w) 0 := by
  have hQ := transpose_map_typeAGraphConjugator σ r
  have he0 := comp_single_dotProduct_typeAGraphConjugator_mulVec_single (σ := σ) (i := 0)
    (by rwa [Fin.rev_zero])
  have hwe0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp he0w
  obtain ⟨g₀, hg₀, hcoe⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ he0
    he0w (c := 0) (by simp [hw])
  let g : (stdUnitMat K r).specialIsometryGroup σ := ⟨g₀, hg₀⟩
  have h1 := siegelTransvection_mul_siegelTransvection_neg_eq_one (Q := stdUnitMat K r) (σ := σ)
    (ε := (-1 : K) ^ r) he0 he0w hwe0 0
  simp only [neg_zero, hw, mul_zero, sub_zero] at h1
  have h2 : ((g : Matrix.SpecialLinearGroup (Fin (r + 1)) K) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) K) *
      (((g⁻¹ : (stdUnitMat K r).specialIsometryGroup σ) :
        Matrix.SpecialLinearGroup (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Matrix.SpecialLinearGroup.coe_one]
  exact ⟨g, hcoe, (inv_eq_right_inv h2).symm.trans (inv_eq_right_inv (hcoe ▸ h1))⟩

/-- Heisenberg commutator of two isotropic Siegel transformations `S(e₀, w₁, 0)` and
`S(e₀, w₂, 0)`. -/
private theorem exists_commutator_coe_eq_unitaryTransvection_of_isotropic
    (hσ : Function.Involutive σ) {r : ℕ} (h0r : (0 : Fin (r + 1)) ≠ Fin.last r)
    {w₁ w₂ : Fin (r + 1) → K} (hw₁ : (σ ∘ w₁) ⬝ᵥ (stdUnitMat K r *ᵥ w₁) = 0)
    (hw₂ : (σ ∘ w₂) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = 0)
    (he0w₁ : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w₁) = 0)
    (he0w₂ : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = 0) :
    ∃ g₁ g₂ : (stdUnitMat K r).specialIsometryGroup σ,
      (((⁅g₁, g₂⁆ : (stdUnitMat K r).specialIsometryGroup σ) :
          Matrix.SpecialLinearGroup (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) =
        (stdUnitMat K r).unitaryTransvection σ (Pi.single 0 1)
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
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hg₁, hg₂, hg₁i, hg₂i, Matrix.mul_assoc (_ * _),
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

/-- When `3 ≤ r`, every unitary transvection along `e₀` is a Heisenberg commutator of two Siegel
transformations supported on `e₁` and `e_{r-1}`. -/
private theorem unitaryTransvection_single_zero_mem_commutator_of_three_le
    (hσ : Function.Involutive σ) (htr : ∀ s : K, σ s = s → ∃ t : K, t + σ t = s) {r : ℕ}
    (hr : 3 ≤ r) {g : (stdUnitMat K r).specialIsometryGroup σ} {a : K}
    (hg : ((g : Matrix.SpecialLinearGroup (Fin (r + 1)) K) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K) =
      (stdUnitMat K r).unitaryTransvection σ (Pi.single 0 1) a) :
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
    rw [comp_single_zero_dotProduct_stdUnitMat_mulVec]; simp [w₁, i₁, Fin.ext_iff]; omega
  have he0w₂ : (σ ∘ Pi.single 0 1) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = 0 := by
    rw [comp_single_zero_dotProduct_stdUnitMat_mulVec]; simp [w₂, j₁, i₁, Fin.ext_iff, Fin.rev]
    omega
  obtain ⟨g₁, g₂, hcomm⟩ :=
    exists_commutator_coe_eq_unitaryTransvection_of_isotropic hσ h0r hw₁ hw₂ he0w₁ he0w₂
  have hpair : (σ ∘ w₁) ⬝ᵥ (stdUnitMat K r *ᵥ w₂) = σ t := by
    have hc : σ ∘ Pi.single i₁ (1 : K) = Pi.single i₁ 1 := funext fun m ↦ by
      by_cases hm : m = i₁ <;> simp [hm]
    rw [show w₁ = (-t) • Pi.single i₁ 1 from rfl, TauCeti.map_comp_smul, smul_dotProduct, hc,
      single_one_dotProduct, coe_typeAGraphConjugator_mulVec]
    simp [w₂, i₁, j₁]
  have hge : g = ⁅g₁, g₂⁆ := Subtype.ext (Subtype.ext <| by
    rw [hg, hcomm, hpair, hσ t]
    congr 1; rw [pow_succ] at ht; linear_combination -ht)
  exact hge ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_top g₁) (Subgroup.mem_top g₂)

/-- The diagonal special isometry `diag(u, σ(u) * u⁻¹, σ(u)⁻¹)` in `SU₃` rescaling `e₀` by `u`. -/
private theorem exists_diag_three_mulVec_single_zero (hσ : Function.Involutive σ) {u : K}
    (hu0 : u ≠ 0) :
    ∃ D : (stdUnitMat K 2).specialIsometryGroup σ,
      ((D : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 =
        u • Pi.single 0 1 := by
  have hσu0 : σ u ≠ 0 := (map_ne_zero σ).mpr hu0
  let d : Fin 3 → K := ![u, σ u * u⁻¹, (σ u)⁻¹]
  have hdetD : (diagonal d).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
  have hisoD : ((diagonal d).map σ)ᵀ * stdUnitMat K 2 * diagonal d = stdUnitMat K 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, stdUnitMat, coe_typeAGraphConjugator_two, d,
        hσ u, hu0, hσu0]
    field_simp
  refine ⟨⟨⟨diagonal d, hdetD⟩, mem_specialIsometryGroup_iff.mpr hisoD⟩, ?_⟩
  ext i; fin_cases i <;> simp [mulVec_diagonal, d]

/-- When `r = 2` and `{t | σ(t) = t}` contains `t ∉ {0, 1}` with `σ(u) * u = t`, every unitary
transvection along `e₀` is a torus-transvection commutator. -/
private theorem unitaryTransvection_single_zero_mem_commutator_two (hσ : Function.Involutive σ)
    {t u : K} (ht : σ t = t) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hu : σ u * u = t)
    {g : (stdUnitMat K 2).specialIsometryGroup σ} {a : K}
    (hg : ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (stdUnitMat K 2).unitaryTransvection σ (Pi.single 0 1) a) :
    g ∈ commutator ((stdUnitMat K 2).specialIsometryGroup σ) := by
  have hQ := transpose_map_typeAGraphConjugator σ 2
  have he0 := comp_single_dotProduct_typeAGraphConjugator_mulVec_single (σ := σ) (i := (0 : Fin 3))
    (by decide)
  have ha := unitaryTransvection_single_zero_param_eq_zero hσ (by decide) hg
  have htsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  obtain ⟨D, hDe0⟩ := exists_diag_three_mulVec_single_zero hσ (right_ne_zero_of_mul (hu ▸ ht0))
  let b : K := (t - 1)⁻¹ * a
  have hb : b + (-1 : K) ^ 2 * σ b = 0 := by
    simp only [b, map_mul, map_inv₀, map_sub, ht, map_one]
    linear_combination (t - 1)⁻¹ * ha
  obtain ⟨h₀, hh₀, hcoe⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ he0 hb
  let h : (stdUnitMat K 2).specialIsometryGroup σ := ⟨h₀, hh₀⟩
  have hhi : (((h⁻¹ : (stdUnitMat K 2).specialIsometryGroup σ) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (stdUnitMat K 2).unitaryTransvection σ (Pi.single 0 1) (-b) := by
    have h1 : (stdUnitMat K 2).unitaryTransvection σ (Pi.single 0 1) b *
        (stdUnitMat K 2).unitaryTransvection σ (Pi.single 0 1) (-b) = 1 := by
      rw [unitaryTransvection_mul_unitaryTransvection he0, add_neg_cancel, unitaryTransvection_zero]
    have h2 : ((h : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((h⁻¹ : (stdUnitMat K 2).specialIsometryGroup σ) : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        Matrix.SpecialLinearGroup.coe_one]
    exact (inv_eq_right_inv h2).symm.trans (inv_eq_right_inv (hcoe ▸ h1))
  have hmat : ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((⁅D, h⁆ : (stdUnitMat K 2).specialIsometryGroup σ) :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hcoe, Subgroup.coe_inv,
      coe_mul_unitaryTransvection_mul_coe_inv D.2, hDe0, unitaryTransvection_smul, hhi,
      unitaryTransvection_mul_unitaryTransvection he0, hg]
    congr 1
    calc a = b * (t - 1) := by dsimp only [b]; rw [mul_right_comm, inv_mul_cancel₀ htsub, one_mul]
      _ = b * u * σ u + -b := by linear_combination -b * hu
  exact Subtype.ext (Subtype.ext hmat) ▸
    Subgroup.commutator_mem_commutator (Subgroup.mem_top D) (Subgroup.mem_top h)

/-- **Perfectness of the standard special unitary group.** Let `σ` be an involution of a field `K`
such that `t ↦ t + σ(t)` is onto `{s | σ(s) = s}`, `d + σ(d) = 0` has a nonzero solution, and,
when `r` is even, `b ↦ σ(b) * b` is onto `{s | σ(s) = s}`. For `2 ≤ r`, assuming `r ≠ 2` or that
`{t : K | σ(t) = t}` has at least three elements (excluding `SU₃(2)`), the special unitary group
`(typeAGraphConjugator r K).specialIsometryGroup σ` is perfect. -/
theorem commutator_specialIsometryGroup_typeAGraphConjugator
    (hσ : Function.Involutive σ) (htr : ∀ s : K, σ s = s → ∃ t : K, t + σ t = s)
    (hadm : ∃ d ≠ (0 : K), d + σ d = 0) {r : ℕ} (hr : 2 ≤ r)
    (hnorm : Even r → ∀ s : K, σ s = s → ∃ b : K, σ b * b = s)
    (hfield : r ≠ 2 ∨ ∃ t : K, σ t = t ∧ t ≠ 0 ∧ t ≠ 1) :
    commutator ((typeAGraphConjugator r K :
      Matrix (Fin (r + 1)) (Fin (r + 1)) K).specialIsometryGroup σ) = ⊤ := by
  have hQ := transpose_map_typeAGraphConjugator σ r
  have hdet : (stdUnitMat K r).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).mp (typeAGraphConjugator r K).isUnit).ne_zero
  have := isPretransitive_isotropicPoints hσ hQ hdet
    (fun _ ↦ exists_add_neg_one_pow_mul_apply_eq htr r)
    (exists_ne_zero_add_neg_one_pow_mul_apply_eq_zero hadm r)
  have h0r : (0 : Fin (r + 1)) ≠ Fin.last r := by simp [Fin.ext_iff]; omega
  have he0 := comp_single_dotProduct_typeAGraphConjugator_mulVec_single (σ := σ) (i := 0)
    (by rwa [Fin.rev_zero])
  have he0_ne : (Pi.single 0 1 : Fin (r + 1) → K) ≠ 0 :=
    fun h ↦ (one_ne_zero (α := K)) (by simpa using congrFun h 0)
  let p₀ : (stdUnitMat K r).isotropicPoints σ :=
    ⟨Projectivization.mk K (Pi.single 0 1) he0_ne, (mk_mem_isotropicPoints_iff he0_ne).mpr he0⟩
  rw [eq_top_iff, ← iSup_unitaryTransvectionSubgroup_typeAGraphConjugator hσ htr hadm
    (fun he _ ↦ hnorm he) hfield]
  refine iSup_unitaryTransvectionSubgroup_le_of_normal p₀ fun g hg ↦ ?_
  obtain ⟨a, hga⟩ := (mem_unitaryTransvectionSubgroup_mk_iff he0_ne p₀.2).mp hg
  rcases eq_or_lt_of_le hr with rfl | hr3
  · obtain ⟨t, ht, ht0, ht1⟩ := hfield.resolve_left (by decide)
    obtain ⟨u, hu⟩ := hnorm even_two t ht
    exact unitaryTransvection_single_zero_mem_commutator_two hσ ht ht0 ht1 hu hga
  · exact unitaryTransvection_single_zero_mem_commutator_of_three_le hσ htr hr3 hga

/-- **Simplicity of the standard projective special unitary group.** Under the hypotheses of
`TauCeti.commutator_specialIsometryGroup_typeAGraphConjugator`, the central quotient of
`(typeAGraphConjugator r K).specialIsometryGroup σ` is simple. -/
theorem isSimpleGroup_quotient_center_typeAGraphConjugator
    (hσ : Function.Involutive σ) (htr : ∀ s : K, σ s = s → ∃ t : K, t + σ t = s)
    (hadm : ∃ d ≠ (0 : K), d + σ d = 0) {r : ℕ} (hr : 2 ≤ r)
    (hnorm : Even r → ∀ s : K, σ s = s → ∃ b : K, σ b * b = s)
    (hfield : r ≠ 2 ∨ ∃ t : K, σ t = t ∧ t ≠ 0 ∧ t ≠ 1) :
    IsSimpleGroup ((typeAGraphConjugator r K :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K).specialIsometryGroup σ ⧸
      Subgroup.center ((typeAGraphConjugator r K :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K).specialIsometryGroup σ)) := by
  have h0r : (0 : Fin (r + 1)) ≠ Fin.last r := by simp [Fin.ext_iff]; omega
  have he0 := comp_single_dotProduct_typeAGraphConjugator_mulVec_single (σ := σ) (i := 0)
    (by rwa [Fin.rev_zero])
  have he0_ne : (Pi.single 0 1 : Fin (r + 1) → K) ≠ 0 :=
    fun h ↦ (one_ne_zero (α := K)) (by simpa using congrFun h 0)
  have : Nonempty ((stdUnitMat K r).isotropicPoints σ) :=
    ⟨⟨Projectivization.mk K (Pi.single 0 1) he0_ne, (mk_mem_isotropicPoints_iff he0_ne).mpr he0⟩⟩
  exact isSimpleGroup_quotient_center_specialIsometryGroup hσ
    (transpose_map_typeAGraphConjugator σ r)
    ((isUnit_iff_isUnit_det _).mp (typeAGraphConjugator r K).isUnit).ne_zero
    (fun _ ↦ exists_add_neg_one_pow_mul_apply_eq htr r)
    (exists_ne_zero_add_neg_one_pow_mul_apply_eq_zero hadm r)
    (iSup_unitaryTransvectionSubgroup_typeAGraphConjugator hσ htr hadm (fun he _ ↦ hnorm he) hfield)
    (commutator_specialIsometryGroup_typeAGraphConjugator hσ htr hadm hr hnorm hfield)

end Field

end TauCeti
