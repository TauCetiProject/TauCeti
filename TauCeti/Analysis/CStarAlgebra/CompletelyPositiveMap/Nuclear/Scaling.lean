/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Matrix
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear

/-!
# Nuclearity does not depend on the scaling

A completely positive map `φ` is nuclear (`CompletelyPositiveMap.IsNuclear`) when it is a
nonnegative multiple `c • ψ` of a nuclear contraction `ψ`. For a unital domain `A` the scaling
can always be taken to be `‖φ‖ = ‖φ 1‖`: a nuclear map with `‖φ 1‖ ≤ 1` is itself a nuclear
contraction (`CompletelyPositiveMap.IsNuclear.isNuclearContraction`), and so `φ` is nuclear
exactly when its normalization `‖φ 1‖⁻¹ • φ` is a nuclear contraction
(`CompletelyPositiveMap.isNuclear_iff_isNuclearContraction_inv_nnnorm_map_one_smul`).

The approximants of `c • ψ` are composites `c • β ∘ α` through matrix algebras, but `c • β` may
have norm up to `c`. By the Choi–Effros factorization
(`CompletelyPositiveMap.exists_unital_eq_sqrt_mul_mul_sqrt`), `α = h α' h` with `h = α(1)^{1/2}`
and `α'` unital. Then `β' = c • β(h · h)` satisfies `β' ∘ α' = c • β ∘ α`, and, as a completely
positive map on a unital algebra, has norm `‖β' 1‖ = ‖c • β (α 1)‖`, close to `‖φ 1‖ ≤ 1`; a
slight rescaling of `β'` gives the required contractions.

## References

* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences 122, Springer (2006), IV.3.1.4.
-/

public section

open scoped CStarAlgebra ComplexOrder NNReal

namespace CompletelyPositiveMap

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The choice of tolerance `δ = ε / (2 (c + 1) (c M + 1))` in the approximation step. -/
private theorem mul_div_mul_lt {c M ε : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (hε : 0 < ε) :
    c * (ε / (2 * (c + 1) * (c * M + 1))) * (c * M) + c * (ε / (2 * (c + 1) * (c * M + 1))) <
      ε := by
  calc _ = c * (ε / (2 * (c + 1) * (c * M + 1))) * (c * M + 1) := by ring
    _ ≤ (c + 1) * (ε / (2 * (c + 1) * (c * M + 1))) * (c * M + 1) := by gcongr; linarith
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- One approximation step: for a nuclear contraction `ψ`, a scalar `c` with `‖c • ψ 1‖ ≤ 1`, a
finite set `F` and `ε > 0`, the map `c • ψ` is approximated on `F` within `ε` by a composite of
completely positive contractions through a matrix algebra. -/
private theorem exists_approx [Nontrivial A] {ψ : A →CP B} (hψ : ψ.IsNuclearContraction)
    (c : ℝ≥0) (h1 : ‖(c • ψ) 1‖ ≤ 1) (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (α : A →CP CStarMatrix (Fin n) (Fin n) ℂ)
      (β : CStarMatrix (Fin n) (Fin n) ℂ →CP B),
      (∀ a, ‖α a‖ ≤ ‖a‖) ∧ (∀ x, ‖β x‖ ≤ ‖x‖) ∧ ∀ a ∈ F, ‖β (α a) - (c • ψ) a‖ < ε := by
  classical
  set M : ℝ := ∑ a ∈ F, ‖a‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun a _ ↦ norm_nonneg a
  have haM {a : A} (ha : a ∈ F) : ‖a‖ ≤ M :=
    Finset.single_le_sum (f := fun a ↦ ‖a‖) (fun a _ ↦ norm_nonneg a) ha
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  set δ : ℝ := ε / (2 * (c + 1) * (c * M + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨n, α, β, hα, hβ, hF⟩ := isNuclearContraction_iff.mp hψ (insert 1 F) δ hδ
  obtain ⟨α', hα'1, hα'⟩ := exists_unital_eq_sqrt_mul_mul_sqrt α
  set h := CFC.sqrt (α 1)
  have hh : star h = h := (CFC.sqrt_nonneg (α 1)).isSelfAdjoint.star_eq
  set β' : CStarMatrix (Fin n) (Fin n) ℂ →CP B := c • β.comp (conj h)
  have hβ'α' (a : A) : β' (α' a) = (c : ℝ) • β (α a) := by
    simp [β', hα' a, hh, NNReal.smul_def]
  have hβ'1 : ‖β' 1‖ ≤ 1 + c * δ := by
    have e1 : β' 1 = (c • ψ) 1 + (c : ℝ) • (β (α 1) - ψ 1) := by
      rw [show (1 : CStarMatrix (Fin n) (Fin n) ℂ) = α' 1 from hα'1.symm, hβ'α']
      simp [NNReal.smul_def, smul_sub]
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add h1 ?_)
    rw [norm_smul_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hF 1 (Finset.mem_insert_self 1 F)).le hc
  -- rescale `β'` by `t = (1 + c δ)⁻¹`
  have hcδ : 0 ≤ (c : ℝ) * δ := by positivity
  set t : ℝ≥0 := ⟨(1 + c * δ)⁻¹, by positivity⟩
  have ht (y : B) : t • y = (1 + (c : ℝ) * δ)⁻¹ • y := NNReal.smul_def t y
  refine ⟨n, α', t • β', fun a ↦ ?_, fun x ↦ ?_, fun a ha ↦ ?_⟩
  · exact (CompletelyPositiveMapClass.norm_map_one_le_one_iff α').1
      (hα'1 ▸ CStarRing.norm_one_le) a
  · refine (CompletelyPositiveMapClass.norm_map_one_le_one_iff (t • β')).1 ?_ x
    rw [smul_apply, ht, norm_smul_of_nonneg (by positivity)]
    exact inv_mul_le_one_of_le₀ hβ'1 (by positivity)
  have hX : ‖(c : ℝ) • β (α a)‖ ≤ c * M := by
    rw [norm_smul_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (((hβ _).trans (hα a)).trans (haM ha)) hc
  have hXY : ‖(c : ℝ) • β (α a) - (c • ψ) a‖ ≤ c * δ := by
    rw [smul_apply, NNReal.smul_def, ← smul_sub, norm_smul_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hF a (Finset.mem_insert_of_mem ha)).le hc
  calc ‖(t • β') (α' a) - (c • ψ) a‖
      ≤ ‖((1 + (c : ℝ) * δ)⁻¹ - 1) • ((c : ℝ) • β (α a))‖ +
          ‖(c : ℝ) • β (α a) - (c • ψ) a‖ := by
        rw [smul_apply, hβ'α', ht, sub_smul, one_smul]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ c * δ * (c * M) + c * δ := by
        rw [norm_smul, Real.norm_eq_abs, abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by linarith)))]
        exact add_le_add (mul_le_mul (by field_simp; nlinarith) hX (norm_nonneg _) hcδ) hXY
    _ < ε := mul_div_mul_lt hc hM hε

/-- **Independence of the scaling.** On a unital C⋆-algebra, a nuclear completely positive map
`φ` with `‖φ 1‖ ≤ 1` (equivalently, a nuclear map that is itself contractive) is a nuclear
contraction: its approximants through matrix algebras can be taken to be completely positive
contractions. -/
theorem IsNuclear.isNuclearContraction {φ : A →CP B} (hφ : φ.IsNuclear) (h1 : ‖φ 1‖ ≤ 1) :
    φ.IsNuclearContraction := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : φ = 0 := ext fun a ↦ by rw [Subsingleton.elim a 0, map_zero, zero_apply]
    exact this ▸ isNuclearContraction_zero
  obtain ⟨c, ψ, hψ, rfl⟩ := isNuclear_iff.mp hφ
  exact isNuclearContraction_iff.mpr fun F ε hε ↦ exists_approx hψ c h1 F hε

/-- On a unital C⋆-algebra, a nuclear completely positive map is a nuclear contraction exactly
when `‖φ 1‖ ≤ 1`. -/
theorem isNuclearContraction_iff_isNuclear_and_norm_map_one_le_one {φ : A →CP B} :
    φ.IsNuclearContraction ↔ φ.IsNuclear ∧ ‖φ 1‖ ≤ 1 := by
  refine ⟨fun h ↦ ⟨h.isNuclear, ?_⟩, fun h ↦ h.1.isNuclearContraction h.2⟩
  exact (h.norm_apply_le 1).trans CStarRing.norm_one_le

/-- **Normalization.** On a unital C⋆-algebra, a completely positive map `φ` is nuclear exactly
when its normalization `‖φ 1‖⁻¹ • φ` is a nuclear contraction. (When `φ 1 = 0`, `φ = 0` and the
normalization is `0`.) -/
theorem isNuclear_iff_isNuclearContraction_inv_nnnorm_map_one_smul {φ : A →CP B} :
    φ.IsNuclear ↔ (‖φ 1‖₊⁻¹ • φ).IsNuclearContraction := by
  refine ⟨fun h ↦ (h.smul _).isNuclearContraction ?_, fun h ↦ ?_⟩
  · rw [smul_apply, NNReal.smul_def, norm_smul_of_nonneg (by positivity), NNReal.coe_inv,
      coe_nnNorm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
  · rcases eq_or_ne ‖φ 1‖₊ 0 with h0 | h0
    · have h := (φ.isNPositive 2).eq_zero_of_map_one_eq_zero two_pos (nnNorm_eq_zero.mp h0)
      have : φ = 0 := ext fun a ↦ LinearMap.congr_fun h a
      exact this ▸ isNuclearContraction_zero.isNuclear
    · refine isNuclear_iff.mpr ⟨‖φ 1‖₊, _, h, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

end CompletelyPositiveMap
