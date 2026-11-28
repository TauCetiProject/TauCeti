/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Basic
import TauCeti.Analysis.Fourier.Torus.UnitCube
import TauCeti.Analysis.InnerProductSpace.WeakSolution
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The inverse of the Cauchy–Riemann operator on a nontrivial flat line over a torus

Let `ω₁, ω₂ ∈ ℂ` be linearly independent over `ℝ`, and consider the flat Hermitian line over the
torus `ℂ / (ℤ ω₁ + ℤ ω₂)` with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂`, as in
`TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Basic`. Its sections are the functions `u : ℂ → ℂ`
with `u (z + ω₁) = exp (2πiθ₁) u z` and `u (z + ω₂) = exp (2πiθ₂) u z`, and a section is
determined by its values `u (s ω₁ + t ω₂)` in lattice coordinates `(s, t) ∈ [0, 1]²`. The
square-integrable sections are therefore the elements of `L²([0, 1]²)`.

The operators `∂bar` and `-∂` are formally adjoint on sections of a unitary flat line: for `C¹`
sections `u` and `φ` with the same twists,

`∫ ∂bar u · conj φ = -∫ u · conj (∂φ)`

over the fundamental domain in lattice coordinates
(`TauCeti.setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv`).
Accordingly a square-integrable section `y` is a *weak solution* of `∂bar y = f`, for `f` in
`L²([0, 1]²)`, if `∫ y · conj (∂φ) = -∫ f · conj φ` for every `C²` section `φ`; a `C¹` section
`y` with `∂bar y = f` is one.

When the holonomy is nontrivial, the coercivity estimate
`C ∫ |φ|² ≤ ∫ |∂φ|²` of `TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq`,
with `C = π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²) > 0`, bounds the formal adjoint below. This
gives a bounded operator `Q` on `L²([0, 1]²)` of norm at most `C^(-1/2)` such that `Q f` is a weak
solution of `∂bar y = f` for every `f`
(`TauCeti.exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq`), chosen as
`TauCeti.flatLineCRInverse`. Since the
twisted exponentials `exp (2πi ((k₁ + θ₁) s + (k₂ + θ₂) t))`, `k ∈ ℤ²`, are smooth sections whose
`∂` is a nonzero multiple of themselves, and span a dense subspace of `L²([0, 1]²)`
(`TauCeti.UnitAddTorus.ae_eq_zero_of_forall_setIntegral_cexp_mul_eq_zero`), the weak kernel of
`∂bar` is zero (`TauCeti.eq_zero_of_forall_setIntegral_mul_conj_wirtingerDeriv_eq_zero`): weak
solutions are unique. So `∂bar` is invertible on square-integrable sections of every flat line with
nontrivial holonomy, in the weak sense, and `Q` is its inverse.

The inverse gains one derivative. For a `C²` section `u` of a unitary flat line, the energies of
`∂u` and `∂bar u` agree,

`∫ |∂u|² = ∫ |∂bar u|²`

(`TauCeti.setIntegral_norm_wirtingerDeriv_sq_eq_setIntegral_norm_conjWirtingerDeriv_sq`), by
integrating by parts twice and commuting `∂` with `∂bar`. So the rule `∂bar u ↦ ∂u` extends to a
contraction `TauCeti.flatLineBeurling` of `L²([0, 1]²)`, the Beurling transform of the flat line.
When the holonomy is nontrivial, the `∂bar u` are dense in `L²([0, 1]²)`, because the twisted
exponentials are eigenfunctions of `∂bar` with nonzero eigenvalues; the Beurling transform is then
an isometry (`TauCeti.norm_flatLineBeurling_apply`) and it computes the weak `∂`-derivative of the
inverse, `∂ (Q f) = flatLineBeurling f`
(`TauCeti.setIntegral_flatLineCRInverse_mul_conj_conjWirtingerDeriv`). Hence `Q f` lies in `H¹`:
along every direction `v ∈ ℂ` it has the weak derivative `v • flatLineBeurling f + conj v • f`
(`TauCeti.setIntegral_flatLineCRInverse_mul_conj_fderiv`), of norm at most `2 ‖v‖ ‖f‖`
(`TauCeti.norm_smul_flatLineBeurling_add_smul_le`). The directions `ω₁` and `ω₂` give the weak
derivatives in lattice coordinates.

If the holonomy has infinite image, every power of the line and every pullback to a finite cover
of the torus has nontrivial holonomy
(`TauCeti.notMem_range_intCast_or_notMem_range_intCast_of_irrational`), on a lattice whose basis
is again linearly independent (`TauCeti.im_conj_intCast_mul_add_mul_intCast_mul_add_ne_zero`), so
`∂bar` is invertible on all of them. These are the leading-order inverses in Taubes's construction
of Seiberg–Witten solutions near a square-zero pseudoholomorphic torus whose normal line is flat
with irrational holonomy, where the leading operator acts on the divisor bundle
`N ⊕ N² ⊕ ⋯ ⊕ Nᵐ` of the normal line `N`.

## Main definitions

* `TauCeti.flatLineCRInverse`: the inverse of `∂bar` on square-integrable sections of a flat line
  with nontrivial holonomy.
* `TauCeti.flatLineBeurling`: the Beurling transform `∂bar u ↦ ∂u` of a flat line.

## Main results

* `TauCeti.setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv`:
  integration by parts for sections of a unitary flat line.
* `TauCeti.exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq`: the bounded weak
  inverse of `∂bar` on a flat line with nontrivial holonomy.
* `TauCeti.eq_zero_of_forall_setIntegral_mul_conj_wirtingerDeriv_eq_zero`: uniqueness of weak
  solutions.
* `TauCeti.norm_flatLineCRInverse_le`, `TauCeti.flatLineCRInverse_apply_eq_iff`: the inverse of
  `∂bar` is bounded and sends `f` to the unique weak solution of `∂bar y = f`.
* `TauCeti.flatLineCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv`: it inverts `∂bar` on `C¹`
  sections.
* `TauCeti.setIntegral_norm_wirtingerDeriv_sq_eq_setIntegral_norm_conjWirtingerDeriv_sq`: the
  energy identity `∫ |∂u|² = ∫ |∂bar u|²` for `C²` sections.
* `TauCeti.flatLineBeurling_ae_eq_of_ae_eq_conjWirtingerDeriv`, `TauCeti.norm_flatLineBeurling_le`,
  `TauCeti.norm_flatLineBeurling_apply`: the Beurling transform sends `∂bar u` to `∂u`, is a
  contraction, and is an isometry on a nontrivial flat line.
* `TauCeti.setIntegral_flatLineCRInverse_mul_conj_conjWirtingerDeriv`,
  `TauCeti.setIntegral_flatLineCRInverse_mul_conj_fderiv`,
  `TauCeti.norm_smul_flatLineBeurling_add_smul_le`: the inverse of `∂bar` maps `L²` into `H¹`.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2 (the Beurling transform and the `L²` Calderón–Zygmund identity).
-/

public section

open Complex ComplexConjugate MeasureTheory Set
open scoped Real

namespace TauCeti

variable {u φ : ℂ → ℂ} {ω₁ ω₂ χ₁ χ₂ : ℂ} {θ₁ θ₂ : ℝ}

section IntegrationByParts

/-- Pointwise, with `D = Im (conj ω₁ ω₂)`, `2 i D (∂bar u conj φ + u conj ∂φ)` is the combination
`ω₂ F₁ - ω₁ F₂` of the derivatives `F_j = Du ω_j conj φ + u conj (Dφ ω_j)` of `u conj φ` along
the lattice vectors. -/
private theorem two_mul_I_mul_im_mul_conjWirtingerDeriv_mul_conj_add (z : ℂ) :
    (2 * I * (conj ω₁ * ω₂).im : ℂ) *
        (conjWirtingerDeriv u z 1 * conj (φ z) + u z * conj (wirtingerDeriv φ z 1)) =
      ω₂ * (fderiv ℝ u z ω₁ * conj (φ z) + u z * conj (fderiv ℝ φ z ω₁)) -
        ω₁ * (fderiv ℝ u z ω₂ * conj (φ z) + u z * conj (fderiv ℝ φ z ω₂)) := by
  have hu := smul_conjWirtingerDeriv_apply_one_eq_sub u ω₁ ω₂ z
  have hφ := congrArg conj (smul_wirtingerDeriv_apply_one_eq_sub φ ω₁ ω₂ z)
  simp only [smul_eq_mul, map_mul, map_sub, map_ofNat, conj_conj, conj_I, conj_ofReal] at hu hφ
  linear_combination conj (φ z) * hu - u z * hφ

/-- **`∂bar` and `-∂` are formally adjoint on a unitary flat line.** Let `ω₁, ω₂` be linearly
independent over `ℝ`, and let `u` and `φ` be `C¹` functions twisted by the same unit complex numbers
`χ₁`, `χ₂` along `ω₁`, `ω₂`, that is, sections of the same flat Hermitian line over the torus
`ℂ / (ℤ ω₁ + ℤ ω₂)`. Then, over the fundamental domain in lattice coordinates,
`∫ ∂bar u · conj φ = -∫ u · conj (∂φ)`. -/
theorem setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv
    (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 1 φ) (hω : (conj ω₁ * ω₂).im ≠ 0) (hχ₁ : ‖χ₁‖ = 1)
    (hχ₂ : ‖χ₂‖ = 1) (hu₁ : ∀ z, u (z + ω₁) = χ₁ * u z) (hu₂ : ∀ z, u (z + ω₂) = χ₂ * u z)
    (hφ₁ : ∀ z, φ (z + ω₁) = χ₁ * φ z) (hφ₂ : ∀ z, φ (z + ω₂) = χ₂ * φ z) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1 * conj (φ (p.1 * ω₁ + p.2 * ω₂)) =
      -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        u (p.1 * ω₁ + p.2 * ω₂) * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) := by
  have hcont {g : ℂ → ℂ} (hg : Continuous g) :
      IntegrableOn (fun p : ℝ × ℝ ↦ g (p.1 * ω₁ + p.2 * ω₂)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (hg.comp continuous_ofReal_fst_mul_add_ofReal_snd_mul).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hint₁ := setIntegral_fderiv_mul_conj_add_mul_conj_fderiv_eq_zero (ω₂ := ω₂) hu hφ hχ₁ hu₁
    hφ₁
  have hint₂ := setIntegral_fderiv_mul_conj_add_mul_conj_fderiv_eq_zero (ω₂ := ω₁) hu hφ hχ₂ hu₂
    hφ₂
  rw [setIntegral_comp_ofReal_fst_mul_add_ofReal_snd_mul_swap (fun z ↦
    fderiv ℝ u z ω₂ * conj (φ z) + u z * conj (fderiv ℝ φ z ω₂))] at hint₂
  -- The integral of `∂bar u conj φ + u conj ∂φ` is `(2 i D)⁻¹ (ω₂ ∫ F₁ - ω₁ ∫ F₂) = 0`.
  have h := integral_sub
    ((hcont (continuous_fderiv_mul_conj_add_mul_conj_fderiv hu hφ ω₁)).const_mul ω₂)
    ((hcont (continuous_fderiv_mul_conj_add_mul_conj_fderiv hu hφ ω₂)).const_mul ω₁)
  simp only [← two_mul_I_mul_im_mul_conjWirtingerDeriv_mul_conj_add, integral_const_mul, hint₁,
    hint₂, mul_zero, sub_zero, mul_eq_zero, mul_ne_zero two_ne_zero I_ne_zero,
    ofReal_eq_zero, hω, false_or] at h
  rw [eq_neg_iff_add_eq_zero, ← integral_add
    (hcont (g := fun z ↦ conjWirtingerDeriv u z 1 * conj (φ z))
      ((hu.continuous_conjWirtingerDeriv_apply 1).mul (continuous_conj.comp hφ.continuous)))
    (hcont (g := fun z ↦ u z * conj (wirtingerDeriv φ z 1))
      (hu.continuous.mul (continuous_conj.comp (hφ.continuous_wirtingerDeriv_apply 1))))]
  exact h

end IntegrationByParts

section WeakInverse

/-- A continuous function read in lattice coordinates is square integrable over the fundamental
domain. -/
private theorem memLp_comp_latticeCoord {g : ℂ → ℂ} (hg : Continuous g) :
    MemLp (fun p : ℝ × ℝ ↦ g (p.1 * ω₁ + p.2 * ω₂)) 2
      ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
  (hg.comp continuous_ofReal_fst_mul_add_ofReal_snd_mul).continuousOn
    |>.memLp_restrict_of_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
      (measurableSet_Icc.prod measurableSet_Icc) subset_rfl 2

/-- The inclusion of the test sections into `L²` of the fundamental domain. -/
private noncomputable def sectionToLp (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) :
    flatLineSections 2 ω₁ ω₂ θ₁ θ₂ →ₗ[ℂ]
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) where
  toFun u := (memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂)
    (contDiff_of_mem_flatLineSections u.property).continuous).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ by simp)
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ by simp)

private theorem sectionToLp_apply (u : flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    sectionToLp ω₁ ω₂ θ₁ θ₂ u =
      (memLp_comp_latticeCoord (contDiff_of_mem_flatLineSections u.property).continuous).toLp
        (fun p : ℝ × ℝ ↦ (u : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂)) :=
  rfl

/-- The Wirtinger derivative `∂` on test sections, with values in `L²` of the fundamental
domain. -/
private noncomputable def wirtingerToLp (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) :
    flatLineSections 2 ω₁ ω₂ θ₁ θ₂ →ₗ[ℂ]
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) where
  toFun u := (memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂)
    (ContDiff.continuous_wirtingerDeriv_apply
      ((contDiff_of_mem_flatLineSections u.property).of_le one_le_two) 1)).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ ?_)
    simp [wirtingerDeriv_add
      ((contDiff_of_mem_flatLineSections u.property).differentiable two_ne_zero _)
      ((contDiff_of_mem_flatLineSections v.property).differentiable two_ne_zero _)]
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ by simp [wirtingerDeriv_const_smul])

private theorem wirtingerToLp_apply (u : flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    wirtingerToLp ω₁ ω₂ θ₁ θ₂ u = (memLp_comp_latticeCoord
      (ContDiff.continuous_wirtingerDeriv_apply
        ((contDiff_of_mem_flatLineSections u.property).of_le one_le_two) 1)).toLp
      (fun p : ℝ × ℝ ↦ wirtingerDeriv (u : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂) 1) :=
  rfl

/-- The coercivity estimate of `∂` in `L²` of the fundamental domain. -/
private theorem sqrt_mul_norm_sectionToLp_le (hω : (conj ω₁ * ω₂).im ≠ 0)
    (u : flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    √(π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2)) *
        ‖sectionToLp ω₁ ω₂ θ₁ θ₂ u‖ ≤ ‖wirtingerToLp ω₁ ω₂ θ₁ θ₂ u‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [mul_pow, Real.sq_sqrt (by positivity), sectionToLp_apply, wirtingerToLp_apply,
    MemLp.norm_toLp_sq, MemLp.norm_toLp_sq]
  obtain ⟨hu, hu₁, hu₂⟩ := mem_flatLineSections.1 u.property
  exact mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq hu hω hu₁ hu₂

/-- **The bounded weak inverse of `∂bar` on a flat line with nontrivial holonomy.** Let
`ω₁, ω₂` be linearly independent over `ℝ`, and let `θ₁` or `θ₂` not be an integer, so that the
flat line with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂` is nontrivial. Then there is
a bounded operator `Q` on `L²([0, 1]²)`, the square-integrable sections in lattice coordinates,
with `‖Q‖ ≤ C^(-1/2)` for `C = π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²)`, such that `Q f` is a
weak solution of `∂bar y = f` for every `f`: `∫ Q f · conj (∂φ) = -∫ f · conj φ` for every `C²`
section `φ`. -/
theorem exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq
    (hω : (conj ω₁ * ω₂).im ≠ 0) (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) :
    ∃ Q : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) →L[ℂ]
        Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)),
      ‖Q‖ ≤ (√(π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2)))⁻¹ ∧
      ∀ f, ∀ φ ∈ flatLineSections 2 ω₁ ω₂ θ₁ θ₂,
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            Q f p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
          -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  have hne (h : ω₁ = 0 ∨ ω₂ = 0) : False := by rcases h with h | h <;> simp [h] at hω
  have hC := pi_sq_div_two_mul_sq_abs_sub_round_div_add_pos hθ (fun h ↦ hne (.inl h))
    (fun h ↦ hne (.inr h))
  obtain ⟨Q, hQn, -, hQ⟩ := LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le
    (-wirtingerToLp ω₁ ω₂ θ₁ θ₂) (sectionToLp ω₁ ω₂ θ₁ θ₂) (Real.sqrt_pos.2 hC)
    fun u ↦ by rw [LinearMap.neg_apply, norm_neg]; exact sqrt_mul_norm_sectionToLp_le hω u
  refine ⟨Q, hQn, fun f φ hφ ↦ ?_⟩
  have h := hQ f ⟨φ, hφ⟩
  rw [LinearMap.neg_apply, inner_neg_right, wirtingerToLp_apply, sectionToLp_apply,
    L2.inner_toLp, L2.inner_toLp] at h
  have h' := congrArg conj h
  rw [map_neg, ← integral_conj, ← integral_conj] at h'
  simp only [RCLike.inner_apply, map_mul, conj_conj] at h'
  simp only [mul_comm (Q f _), mul_comm (f _)]
  linear_combination -h'

end WeakInverse

section Uniqueness

/-- The coefficient `a` of the twisted exponential with `Im (a ω₁) = π c₁` and
`Im (a ω₂) = π c₂`. -/
private noncomputable def dualCoeff (ω₁ ω₂ : ℂ) (c₁ c₂ : ℝ) : ℂ :=
  ((π / (conj ω₁ * ω₂).im : ℝ) : ℂ) * (c₂ * conj ω₁ - c₁ * conj ω₂)

private theorem im_dualCoeff_mul (hω : (conj ω₁ * ω₂).im ≠ 0) (c₁ c₂ : ℝ) :
    (dualCoeff ω₁ ω₂ c₁ c₂ * ω₁).im = π * c₁ ∧ (dualCoeff ω₁ ω₂ c₁ c₂ * ω₂).im = π * c₂ := by
  have h₁ : ((c₂ * conj ω₁ - c₁ * conj ω₂ : ℂ) * ω₁).im = c₁ * (conj ω₁ * ω₂).im := by
    simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im]
    ring
  have h₂ : ((c₂ * conj ω₁ - c₁ * conj ω₂ : ℂ) * ω₂).im = c₂ * (conj ω₁ * ω₂).im := by
    simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im]
    ring
  rw [dualCoeff, mul_assoc, mul_assoc, im_ofReal_mul, im_ofReal_mul, h₁, h₂]
  constructor <;> field_simp

/-- In lattice coordinates the twisted exponential is `exp (2πi (c₁ s + c₂ t))`. -/
private theorem cexp_dualCoeff_mul_sub_conj_mul_conj_latticeCoord (hω : (conj ω₁ * ω₂).im ≠ 0)
    (c₁ c₂ : ℝ) (p : ℝ × ℝ) :
    cexp (dualCoeff ω₁ ω₂ c₁ c₂ * (p.1 * ω₁ + p.2 * ω₂) -
        conj (dualCoeff ω₁ ω₂ c₁ c₂) * conj (p.1 * ω₁ + p.2 * ω₂)) =
      cexp (2 * π * I * (c₁ * p.1 + c₂ * p.2)) := by
  obtain ⟨h₁, h₂⟩ := im_dualCoeff_mul hω c₁ c₂
  have him : (dualCoeff ω₁ ω₂ c₁ c₂ * (p.1 * ω₁ + p.2 * ω₂)).im =
      p.1 * (π * c₁) + p.2 * (π * c₂) := by
    rw [← h₁, ← h₂, mul_add, add_im, mul_left_comm, mul_left_comm _ (p.2 : ℂ), im_ofReal_mul,
      im_ofReal_mul]
  rw [← map_mul, sub_conj, him]
  push_cast
  ring_nf

/-- The twisted exponential `exp (a z - conj a conj z)`, with coefficient
`a = dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂)`, is a smooth section of the flat line with holonomy
`exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂`. -/
private theorem cexp_dualCoeff_mem_flatLineSections (hω : (conj ω₁ * ω₂).im ≠ 0) (k₁ k₂ : ℤ) :
    (fun z ↦ cexp (dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂) * z -
      conj (dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂)) * conj z)) ∈
        flatLineSections 2 ω₁ ω₂ θ₁ θ₂ := by
  obtain ⟨ha₁, ha₂⟩ := im_dualCoeff_mul hω (k₁ + θ₁) (k₂ + θ₂)
  exact mem_flatLineSections.2 ⟨contDiff_cexp_mul_sub_conj_mul_conj _,
    cexp_mul_add_sub_conj_mul_conj_add_of_im_mul_eq _ ha₁,
    cexp_mul_add_sub_conj_mul_conj_add_of_im_mul_eq _ ha₂⟩

/-- On a flat line with nontrivial holonomy the coefficient of every twisted exponential is
nonzero. -/
private theorem dualCoeff_ne_zero (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) (k₁ k₂ : ℤ) :
    dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂) ≠ 0 := by
  obtain ⟨ha₁, ha₂⟩ := im_dualCoeff_mul hω (k₁ + θ₁) (k₂ + θ₂)
  intro h0
  simp only [h0, zero_mul, zero_im, eq_comm (a := (0 : ℝ)), mul_eq_zero, Real.pi_ne_zero,
    false_or] at ha₁ ha₂
  rcases hθ with h | h
  · exact h ⟨-k₁, by push_cast; linarith⟩
  · exact h ⟨-k₂, by push_cast; linarith⟩

/-- **Completeness of the twisted exponentials.** A square-integrable section in lattice
coordinates which is orthogonal to every twisted exponential section of the flat line is zero. -/
private theorem eq_zero_of_forall_setIntegral_mul_conj_cexp_dualCoeff_eq_zero
    (hω : (conj ω₁ * ω₂).im ≠ 0)
    {y : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))}
    (hy : ∀ k₁ k₂ : ℤ, ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      y p * conj (cexp (dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂) * (p.1 * ω₁ + p.2 * ω₂) -
        conj (dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂)) * conj (p.1 * ω₁ + p.2 * ω₂))) = 0) :
    y = 0 := by
  -- Untwisted by `exp (-2πi (θ₁ s + θ₂ t))`, the section `y` becomes a function with vanishing
  -- Fourier coefficients.
  have hg : MemLp (fun p : ℝ × ℝ ↦ cexp (((-(2 * π * (θ₁ * p.1 + θ₂ * p.2)) : ℝ) : ℂ) * I) * y p)
      2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (Lp.memLp y).of_le ((by fun_prop : Continuous fun p : ℝ × ℝ ↦
      cexp (((-(2 * π * (θ₁ * p.1 + θ₂ * p.2)) : ℝ) : ℂ) * I)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable y))
      (ae_of_all _ fun p ↦ by simp only [norm_mul, norm_exp_ofReal_mul_I, one_mul, le_refl])
  have hzero := UnitAddTorus.ae_eq_zero_of_forall_setIntegral_cexp_mul_eq_zero hg fun k₁ k₂ ↦ by
    rw [← hy k₁ k₂]
    refine integral_congr_ae (ae_of_all _ fun p ↦ ?_)
    dsimp only
    rw [cexp_dualCoeff_mul_sub_conj_mul_conj_latticeCoord hω, ← exp_conj, ← mul_assoc,
      ← Complex.exp_add, mul_comm]
    congr 2
    simp only [map_mul, map_add, conj_ofReal, conj_I, map_ofNat]
    push_cast
    ring
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hzero] with p hp
  exact (mul_eq_zero.1 hp).resolve_left (Complex.exp_ne_zero _)

/-- **Uniqueness of weak solutions of `∂bar y = f` on a flat line with nontrivial holonomy.** Let
`ω₁, ω₂` be linearly independent over `ℝ`, and let `θ₁` or `θ₂` not be an integer. If `y` is a
square-integrable section in lattice coordinates which is a weak solution of `∂bar y = 0`, that is,
`∫ y · conj (∂φ) = 0` for every `C²` section `φ` of the flat line with holonomy `exp (2πiθ₁)`,
`exp (2πiθ₂)` along `ω₁`, `ω₂`, then `y = 0`. -/
theorem eq_zero_of_forall_setIntegral_mul_conj_wirtingerDeriv_eq_zero
    (hω : (conj ω₁ * ω₂).im ≠ 0) (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    {y : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))}
    (hy : ∀ φ ∈ flatLineSections 2 ω₁ ω₂ θ₁ θ₂,
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        y p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) = 0) :
    y = 0 := by
  refine eq_zero_of_forall_setIntegral_mul_conj_cexp_dualCoeff_eq_zero (θ₁ := θ₁) (θ₂ := θ₂) hω
    fun k₁ k₂ ↦ ?_
  -- The twisted exponential `e` with coefficient `a ≠ 0` satisfies `∂e = a e`.
  have h := hy _ (cexp_dualCoeff_mem_flatLineSections hω k₁ k₂)
  simpa only [wirtingerDeriv_cexp_mul_sub_conj_mul_conj, map_mul, mul_left_comm (y _) (conj _),
    integral_const_mul, mul_eq_zero, map_eq_zero, dualCoeff_ne_zero hω hθ, false_or] using h

end Uniqueness

section Inverse

/-- Against a continuous section read in lattice coordinates, the integral over the fundamental
domain is an `L²` inner product. -/
private theorem setIntegral_mul_conj_comp_latticeCoord_eq_inner {g : ℂ → ℂ} (hg : Continuous g)
    (y : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, y p * conj (g (p.1 * ω₁ + p.2 * ω₂)) =
      inner ℂ ((memLp_comp_latticeCoord hg).toLp fun p : ℝ × ℝ ↦ g (p.1 * ω₁ + p.2 * ω₂)) y := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_comp_latticeCoord hg).coeFn_toLp] with p hp
  rw [hp, RCLike.inner_apply, mul_comm]

open scoped Classical in
/-- **The inverse of `∂bar` on a flat line over a torus.** When `ω₁, ω₂` are linearly independent
over `ℝ` and `θ₁` or `θ₂` is not an integer, this is the bounded operator on `L²([0, 1]²)`, the
square-integrable sections in lattice coordinates of the flat line with holonomy `exp (2πiθ₁)`,
`exp (2πiθ₂)` along `ω₁`, `ω₂`, sending `f` to the unique weak solution of `∂bar y = f`
(`TauCeti.flatLineCRInverse_apply_eq_iff`). Otherwise it is `0`. -/
noncomputable def flatLineCRInverse (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) :
    Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
  if h : (conj ω₁ * ω₂).im ≠ 0 ∧ (θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) then
    (exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq h.1 h.2).choose
  else 0

/-- For a degenerate lattice or trivial holonomy, `flatLineCRInverse ω₁ ω₂ θ₁ θ₂` is `0`. -/
theorem flatLineCRInverse_of_not
    (h : ¬((conj ω₁ * ω₂).im ≠ 0 ∧ (θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)))) :
    flatLineCRInverse ω₁ ω₂ θ₁ θ₂ = 0 := by
  rw [flatLineCRInverse, dite_eq_right_of_eq_false (eq_false h)]

/-- On the trivial flat line, with integer `θ₁, θ₂`, `flatLineCRInverse ω₁ ω₂ θ₁ θ₂` is `0`. -/
@[simp]
theorem flatLineCRInverse_intCast (k₁ k₂ : ℤ) : flatLineCRInverse ω₁ ω₂ k₁ k₂ = 0 :=
  flatLineCRInverse_of_not fun h ↦ h.2.elim (· ⟨k₁, rfl⟩) (· ⟨k₂, rfl⟩)

/-- The inverse of `∂bar` on a flat line with nontrivial holonomy has norm at most `C^(-1/2)`, for
`C = π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²)`. -/
theorem norm_flatLineCRInverse_le (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) :
    ‖flatLineCRInverse ω₁ ω₂ θ₁ θ₂‖ ≤
      (√(π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2)))⁻¹ := by
  rw [flatLineCRInverse, dite_eq_left_of_eq_true (eq_true ⟨hω, hθ⟩)]
  exact (exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq hω hθ).choose_spec.1

/-- On a flat line with nontrivial holonomy, `flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f` is a weak solution of
`∂bar y = f`: `∫ y · conj (∂φ) = -∫ f · conj φ` for every `C²` section `φ`. -/
theorem setIntegral_flatLineCRInverse_mul_conj_wirtingerDeriv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hφ : φ ∈ flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
      -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  rw [flatLineCRInverse, dite_eq_left_of_eq_true (eq_true ⟨hω, hθ⟩)]
  exact (exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq hω hθ).choose_spec.2
    f φ hφ

/-- **Characterization of the inverse of `∂bar`.** On a flat line with nontrivial holonomy,
`flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f = y` exactly when `y` is a weak solution of `∂bar y = f`, that is,
`∫ y · conj (∂φ) = -∫ f · conj φ` for every `C²` section `φ`. -/
theorem flatLineCRInverse_apply_eq_iff (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    {f y : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))} :
    flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f = y ↔ ∀ φ ∈ flatLineSections 2 ω₁ ω₂ θ₁ θ₂,
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          y p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
        -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl φ hφ
    exact setIntegral_flatLineCRInverse_mul_conj_wirtingerDeriv hω hθ f hφ
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_setIntegral_mul_conj_wirtingerDeriv_eq_zero hω hθ
    fun φ hφ ↦ ?_
  have hg :=
    ((contDiff_of_mem_flatLineSections hφ).of_le one_le_two).continuous_wirtingerDeriv_apply 1
  rw [setIntegral_mul_conj_comp_latticeCoord_eq_inner hg, inner_sub_right,
    ← setIntegral_mul_conj_comp_latticeCoord_eq_inner hg,
    ← setIntegral_mul_conj_comp_latticeCoord_eq_inner hg,
    setIntegral_flatLineCRInverse_mul_conj_wirtingerDeriv hω hθ f hφ, h φ hφ,
    sub_self]

/-- **The inverse of `∂bar` inverts `∂bar` on `C¹` sections.** On a flat line with nontrivial
holonomy, if `u` is a `C¹` section and `f` represents `∂bar u` in lattice coordinates, then
`flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f` represents `u`. -/
theorem flatLineCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) (hu : ContDiff ℝ 1 u)
    (hu₁ : ∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z)
    (hu₂ : ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z)
    {f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))}
    (hf : f =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)]
      fun p ↦ conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1) :
    flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f =ᵐ[(volume : Measure (ℝ × ℝ)).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)] fun p ↦ u (p.1 * ω₁ + p.2 * ω₂) := by
  have hmem := memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂) hu.continuous
  rw [(flatLineCRInverse_apply_eq_iff hω hθ).2 fun φ hφ ↦ ?_]
  · exact hmem.coeFn_toLp
  have h₁ : ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      hmem.toLp _ p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          u (p.1 * ω₁ + p.2 * ω₂) * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) :=
    integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with p hp; rw [hp])
  have h₂ : ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1 * conj (φ (p.1 * ω₁ + p.2 * ω₂)) :=
    integral_congr_ae (by filter_upwards [hf] with p hp; rw [hp])
  obtain ⟨hφ, hφ₁, hφ₂⟩ := mem_flatLineSections.1 hφ
  rw [h₁, h₂, setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv hu
    (hφ.of_le one_le_two) hω (norm_exp_two_pi_mul_ofReal_mul_I θ₁)
    (norm_exp_two_pi_mul_ofReal_mul_I θ₂) hu₁ hu₂ hφ₁ hφ₂, neg_neg]

end Inverse

section Regularity

/-- Integration by parts in the form `∫ u · conj (∂bar φ) = -∫ ∂u · conj φ`, the complex conjugate
of `TauCeti.setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv`
with `u` and `φ` exchanged. -/
private theorem setIntegral_mul_conj_conjWirtingerDeriv_eq_neg (hu : ContDiff ℝ 1 u)
    (hφ : ContDiff ℝ 1 φ) (hω : (conj ω₁ * ω₂).im ≠ 0) (hχ₁ : ‖χ₁‖ = 1) (hχ₂ : ‖χ₂‖ = 1)
    (hu₁ : ∀ z, u (z + ω₁) = χ₁ * u z) (hu₂ : ∀ z, u (z + ω₂) = χ₂ * u z)
    (hφ₁ : ∀ z, φ (z + ω₁) = χ₁ * φ z) (hφ₂ : ∀ z, φ (z + ω₂) = χ₂ * φ z) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        u (p.1 * ω₁ + p.2 * ω₂) * conj (conjWirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
      -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        wirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1 * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  have h := congrArg conj
    (setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv hφ hu hω
      hχ₁ hχ₂ hφ₁ hφ₂ hu₁ hu₂)
  rw [← integral_conj, map_neg, ← integral_conj] at h
  simpa only [map_mul, conj_conj, mul_comm] using h

/-- **The `∂` and `∂bar` energies of a section agree.** Let `ω₁, ω₂` be linearly independent over
`ℝ`, and let `u` be a `C²` function twisted by unit complex numbers `χ₁`, `χ₂` along `ω₁`, `ω₂`,
that is, a section of a unitary flat line over the torus `ℂ / (ℤ ω₁ + ℤ ω₂)`. Then
`∫ |∂u|² = ∫ |∂bar u|²` over the fundamental domain in lattice coordinates. -/
theorem setIntegral_norm_wirtingerDeriv_sq_eq_setIntegral_norm_conjWirtingerDeriv_sq
    (hu : ContDiff ℝ 2 u) (hω : (conj ω₁ * ω₂).im ≠ 0) (hχ₁ : ‖χ₁‖ = 1) (hχ₂ : ‖χ₂‖ = 1)
    (h₁ : ∀ z, u (z + ω₁) = χ₁ * u z) (h₂ : ∀ z, u (z + ω₂) = χ₂ * u z) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖wirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1‖ ^ 2 =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ‖conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1‖ ^ 2 := by
  have hd : ContDiff ℝ 1 fun z ↦ wirtingerDeriv u z 1 :=
    contDiff_iff_contDiffAt.2 fun z ↦ hu.contDiffAt.wirtingerDeriv_apply (by norm_num) 1
  have hdb : ContDiff ℝ 1 fun z ↦ conjWirtingerDeriv u z 1 :=
    contDiff_iff_contDiffAt.2 fun z ↦ hu.contDiffAt.conjWirtingerDeriv_apply (by norm_num) 1
  -- Integrating by parts, `∫ ∂u conj ∂u = -∫ ∂bar ∂u conj u` and
  -- `∫ ∂bar u conj ∂bar u = -∫ u conj (∂ ∂bar u)`, and `∂ ∂bar u = ∂bar ∂u`.
  have hA := setIntegral_mul_conj_conjWirtingerDeriv_eq_neg (hu.of_le one_le_two) hd hω hχ₁ hχ₂
    h₁ h₂ (wirtingerDeriv_add_apply_one_eq_mul h₁) (wirtingerDeriv_add_apply_one_eq_mul h₂)
  have hB := setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv
    (hu.of_le one_le_two) hdb hω hχ₁ hχ₂ h₁ h₂ (conjWirtingerDeriv_add_apply_one_eq_mul h₁)
    (conjWirtingerDeriv_add_apply_one_eq_mul h₂)
  simp only [wirtingerDeriv_conjWirtingerDeriv_comm hu.contDiffAt] at hB
  have key : ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1 *
        conj (conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1) =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        wirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1 *
          conj (wirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1) := by
    rw [hB, hA, neg_neg]
  simp only [mul_conj', ← ofReal_pow, integral_complex_ofReal] at key
  exact (ofReal_injective key).symm

/-- The conjugate Wirtinger derivative `∂bar` on test sections, with values in `L²` of the
fundamental domain. -/
private noncomputable def conjWirtingerToLp (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) :
    flatLineSections 2 ω₁ ω₂ θ₁ θ₂ →ₗ[ℂ]
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) where
  toFun u := (memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂)
    (ContDiff.continuous_conjWirtingerDeriv_apply
      ((contDiff_of_mem_flatLineSections u.property).of_le one_le_two) 1)).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ ?_)
    simp [conjWirtingerDeriv_add
      ((contDiff_of_mem_flatLineSections u.property).differentiable two_ne_zero _)
      ((contDiff_of_mem_flatLineSections v.property).differentiable two_ne_zero _)]
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ by simp [conjWirtingerDeriv_const_smul])

private theorem conjWirtingerToLp_apply (u : flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ u = (memLp_comp_latticeCoord
      (ContDiff.continuous_conjWirtingerDeriv_apply
        ((contDiff_of_mem_flatLineSections u.property).of_le one_le_two) 1)).toLp
      (fun p : ℝ × ℝ ↦ conjWirtingerDeriv (u : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂) 1) :=
  rfl

/-- The energy identity in `L²`: `‖∂u‖ = ‖∂bar u‖` for every test section `u`. -/
private theorem norm_wirtingerToLp (hω : (conj ω₁ * ω₂).im ≠ 0)
    (u : flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    ‖wirtingerToLp ω₁ ω₂ θ₁ θ₂ u‖ = ‖conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ u‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [wirtingerToLp_apply, conjWirtingerToLp_apply, MemLp.norm_toLp_sq, MemLp.norm_toLp_sq]
  obtain ⟨hu, hu₁, hu₂⟩ := mem_flatLineSections.1 u.property
  exact setIntegral_norm_wirtingerDeriv_sq_eq_setIntegral_norm_conjWirtingerDeriv_sq hu hω
    (norm_exp_two_pi_mul_ofReal_mul_I θ₁) (norm_exp_two_pi_mul_ofReal_mul_I θ₂) hu₁ hu₂

/-- On a flat line with nontrivial holonomy, the `∂bar` of the test sections are dense in
`L²`: the twisted exponentials are eigenfunctions of `∂bar` with nonzero eigenvalues, and they
are complete. -/
private theorem topologicalClosure_range_conjWirtingerToLp (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) :
    (LinearMap.range (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  refine eq_zero_of_forall_setIntegral_mul_conj_cexp_dualCoeff_eq_zero (θ₁ := θ₁) (θ₂ := θ₂) hω
    fun k₁ k₂ ↦ ?_
  have hmem := cexp_dualCoeff_mem_flatLineSections (θ₁ := θ₁) (θ₂ := θ₂) hω k₁ k₂
  have h : ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, y p * conj (conjWirtingerDeriv
      (fun z ↦ cexp (dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂) * z -
        conj (dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂)) * conj z)) (p.1 * ω₁ + p.2 * ω₂) 1) = 0 := by
    rw [setIntegral_mul_conj_comp_latticeCoord_eq_inner
      (ContDiff.continuous_conjWirtingerDeriv_apply
        ((contDiff_of_mem_flatLineSections hmem).of_le one_le_two) 1)]
    exact (Submodule.mem_orthogonal _ y).1 hy _
      (LinearMap.mem_range_self (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂) ⟨_, hmem⟩)
  -- The twisted exponential `e` with coefficient `a ≠ 0` satisfies `∂bar e = -conj a e`.
  simpa only [conjWirtingerDeriv_cexp_mul_sub_conj_mul_conj, map_mul, map_neg, conj_conj,
    neg_mul, mul_neg, integral_neg, neg_eq_zero, mul_left_comm (y _) (dualCoeff _ _ _ _),
    integral_const_mul, mul_eq_zero, dualCoeff_ne_zero hω hθ, false_or] using h

/-- The bound `‖∂u‖ ≤ ‖∂bar u‖` through which `∂bar u ↦ ∂u` is a bounded operator. -/
private theorem exists_norm_wirtingerToLp_le (hω : (conj ω₁ * ω₂).im ≠ 0) :
    ∃ C, ∀ u, ‖wirtingerToLp ω₁ ω₂ θ₁ θ₂ u‖ ≤ C * ‖conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ u‖ :=
  ⟨1, fun u ↦ by rw [one_mul, norm_wirtingerToLp hω]⟩

/-- **The Beurling transform of a flat line over a torus.** The bounded operator on
`L²([0, 1]²)`, the square-integrable sections in lattice coordinates of the flat line with
holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂`, which sends `∂bar u` to `∂u` for every
`C²` section `u` (`TauCeti.flatLineBeurling_ae_eq_of_ae_eq_conjWirtingerDeriv`) when `ω₁, ω₂`
are linearly independent over `ℝ`, and is then a contraction (`TauCeti.norm_flatLineBeurling_le`).
It is defined as the canonical factor (`ContinuousLinearMap.factorThru`) of `∂` through `∂bar` on
test sections. On a flat line with nontrivial holonomy it is an isometry
(`TauCeti.norm_flatLineBeurling_apply`) and it is the weak `∂`-derivative of the inverse of `∂bar`
(`TauCeti.setIntegral_flatLineCRInverse_mul_conj_conjWirtingerDeriv`). -/
noncomputable def flatLineBeurling (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) :
    Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
  ((wirtingerToLp ω₁ ω₂ θ₁ θ₂).compLeftInverse (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂)).factorThru
    (LinearMap.range (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂)).subtypeL

private theorem flatLineBeurling_conjWirtingerToLp (hω : (conj ω₁ * ω₂).im ≠ 0)
    (u : flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    flatLineBeurling ω₁ ω₂ θ₁ θ₂ (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ u) =
      wirtingerToLp ω₁ ω₂ θ₁ θ₂ u :=
  ContinuousLinearMap.factorThru_compLeftInverse_apply (exists_norm_wirtingerToLp_le hω) u

/-- **The Beurling transform sends `∂bar u` to `∂u`.** If `ω₁, ω₂` are linearly independent over
`ℝ`, `u` is a `C²` section of the flat line with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along
`ω₁`, `ω₂`, and `f` represents `∂bar u` in lattice coordinates, then
`flatLineBeurling ω₁ ω₂ θ₁ θ₂ f` represents `∂u`. -/
theorem flatLineBeurling_ae_eq_of_ae_eq_conjWirtingerDeriv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hu : ContDiff ℝ 2 u) (hu₁ : ∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z)
    (hu₂ : ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z)
    {f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))}
    (hf : f =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)]
      fun p ↦ conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1) :
    flatLineBeurling ω₁ ω₂ θ₁ θ₂ f =ᵐ[(volume : Measure (ℝ × ℝ)).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)] fun p ↦ wirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1 := by
  have hf' : f = conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ ⟨u, mem_flatLineSections.2 ⟨hu, hu₁, hu₂⟩⟩ :=
    Lp.ext (hf.trans (by rw [conjWirtingerToLp_apply]; exact (MemLp.coeFn_toLp _).symm))
  rw [hf', flatLineBeurling_conjWirtingerToLp hω, wirtingerToLp_apply]
  exact MemLp.coeFn_toLp _

/-- If `ω₁, ω₂` are linearly independent over `ℝ`, the Beurling transform of a flat line is a
contraction. -/
theorem norm_flatLineBeurling_le (hω : (conj ω₁ * ω₂).im ≠ 0) :
    ‖flatLineBeurling ω₁ ω₂ θ₁ θ₂‖ ≤ 1 :=
  ContinuousLinearMap.norm_factorThru_le zero_le_one
    (LinearMap.norm_compLeftInverse_apply_le fun u ↦ by rw [one_mul, norm_wirtingerToLp hω])

/-- **The Beurling transform of a nontrivial flat line is an isometry.** If `ω₁, ω₂` are linearly
independent over `ℝ` and `θ₁` or `θ₂` is not an integer, then
`‖flatLineBeurling ω₁ ω₂ θ₁ θ₂ f‖ = ‖f‖` for every square-integrable section `f`. -/
theorem norm_flatLineBeurling_apply (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) :
    ‖flatLineBeurling ω₁ ω₂ θ₁ θ₂ f‖ = ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_wirtingerToLp_le (θ₁ := θ₁) (θ₂ := θ₂) hω
  refine ContinuousLinearMap.norm_factorThru_apply (fun x ↦ ?_) ?_
  · obtain ⟨_, u, rfl⟩ := x
    rw [LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨C, hC⟩ u _ rfl, norm_wirtingerToLp hω,
      Submodule.coe_subtypeL, Submodule.coe_subtype]
  · rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype,
      topologicalClosure_range_conjWirtingerToLp hω hθ]
    exact Submodule.mem_top

/-- The weak derivative `v • flatLineBeurling f + conj v • f` of the inverse of `∂bar` along a
direction `v` (`TauCeti.setIntegral_flatLineCRInverse_mul_conj_fderiv`) has norm at most
`2 ‖v‖ ‖f‖`, when `ω₁, ω₂` are linearly independent over `ℝ`. -/
theorem norm_smul_flatLineBeurling_add_smul_le (hω : (conj ω₁ * ω₂).im ≠ 0)
    (f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) (v : ℂ) :
    ‖v • flatLineBeurling ω₁ ω₂ θ₁ θ₂ f + conj v • f‖ ≤ 2 * ‖v‖ * ‖f‖ :=
  ContinuousLinearMap.norm_smul_apply_add_conj_smul_le (norm_flatLineBeurling_le hω) v f

/-- Integration by parts for test sections in inner product form:
`⟪∂bar φ, u⟫ + ⟪φ, ∂u⟫ = 0`. -/
private theorem inner_conjWirtingerToLp_add_inner_wirtingerToLp (hω : (conj ω₁ * ω₂).im ≠ 0)
    (u φ : flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    inner ℂ (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ φ) (sectionToLp ω₁ ω₂ θ₁ θ₂ u) +
      inner ℂ (sectionToLp ω₁ ω₂ θ₁ θ₂ φ) (wirtingerToLp ω₁ ω₂ θ₁ θ₂ u) = 0 := by
  obtain ⟨hu, hu₁, hu₂⟩ := mem_flatLineSections.1 u.property
  obtain ⟨hφ, hφ₁, hφ₂⟩ := mem_flatLineSections.1 φ.property
  have e₁ : inner ℂ (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ φ) (sectionToLp ω₁ ω₂ θ₁ θ₂ u) =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (u : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂) *
        conj (conjWirtingerDeriv (φ : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂) 1) := by
    refine (setIntegral_mul_conj_comp_latticeCoord_eq_inner
      ((hφ.of_le one_le_two).continuous_conjWirtingerDeriv_apply 1) _).symm.trans
        (integral_congr_ae ?_)
    filter_upwards [(memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂
        := ω₂) hu.continuous).coeFn_toLp]
      with p hp
    rw [sectionToLp_apply, hp]
  have e₂ : inner ℂ (sectionToLp ω₁ ω₂ θ₁ θ₂ φ) (wirtingerToLp ω₁ ω₂ θ₁ θ₂ u) =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, wirtingerDeriv (u : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂) 1 *
        conj ((φ : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂)) := by
    refine (setIntegral_mul_conj_comp_latticeCoord_eq_inner hφ.continuous _).symm.trans
      (integral_congr_ae ?_)
    filter_upwards [(memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂)
      ((hu.of_le one_le_two).continuous_wirtingerDeriv_apply 1)).coeFn_toLp] with p hp
    rw [wirtingerToLp_apply, hp]
  rw [e₁, e₂, add_eq_zero_iff_eq_neg]
  exact setIntegral_mul_conj_conjWirtingerDeriv_eq_neg (hu.of_le one_le_two)
    (hφ.of_le one_le_two) hω (norm_exp_two_pi_mul_ofReal_mul_I θ₁)
    (norm_exp_two_pi_mul_ofReal_mul_I θ₂) hu₁ hu₂ hφ₁ hφ₂

/-- The weak equation `∂ (Q f) = flatLineBeurling f` for the inverse `Q` of `∂bar`, in inner
product form. -/
private theorem inner_conjWirtingerToLp_flatLineCRInverse (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (φ : flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    inner ℂ (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ φ) (flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f) =
      -inner ℂ (sectionToLp ω₁ ω₂ θ₁ θ₂ φ) (flatLineBeurling ω₁ ω₂ θ₁ θ₂ f) := by
  rw [← add_eq_zero_iff_eq_neg]
  -- Both sides are continuous in `f`, so it suffices to take `f = ∂bar u` for a test section `u`,
  -- which is dense; there `Q f = u` and `flatLineBeurling f = ∂u`.
  let F := (innerSL ℂ (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ φ)).comp (flatLineCRInverse ω₁ ω₂ θ₁ θ₂) +
    (innerSL ℂ (sectionToLp ω₁ ω₂ θ₁ θ₂ φ)).comp (flatLineBeurling ω₁ ω₂ θ₁ θ₂)
  suffices hF : LinearMap.range (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂) ≤
      LinearMap.ker (F : _ →ₗ[ℂ] ℂ) by
    have hle := (LinearMap.range (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂)).topologicalClosure_minimal hF
      F.isClosed_ker
    rw [topologicalClosure_range_conjWirtingerToLp hω hθ] at hle
    exact hle (Submodule.mem_top (x := f))
  rintro _ ⟨u, rfl⟩
  obtain ⟨hu, hu₁, hu₂⟩ := mem_flatLineSections.1 u.property
  have hQ : flatLineCRInverse ω₁ ω₂ θ₁ θ₂ (conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ u) =
      sectionToLp ω₁ ω₂ θ₁ θ₂ u := by
    refine Lp.ext ((flatLineCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv hω hθ
      (hu.of_le one_le_two) hu₁ hu₂ ?_).trans ?_)
    · rw [conjWirtingerToLp_apply]
      exact MemLp.coeFn_toLp _
    · rw [sectionToLp_apply]
      exact (MemLp.coeFn_toLp _).symm
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hQ, flatLineBeurling_conjWirtingerToLp hω, innerSL_apply_apply,
    innerSL_apply_apply]
  exact inner_conjWirtingerToLp_add_inner_wirtingerToLp hω u φ

/-- **The `∂`-derivative of the inverse of `∂bar`.** Let `ω₁, ω₂` be linearly independent over `ℝ`
and let `θ₁` or `θ₂` not be an integer. For every square-integrable section `f`, the section
`flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f` has weak derivative `∂ (Q f) = flatLineBeurling ω₁ ω₂ θ₁ θ₂ f`:
`∫ Q f · conj (∂bar φ) = -∫ flatLineBeurling f · conj φ` for every `C²` section `φ`. Together
with the weak equation `∂bar (Q f) = f`, both Wirtinger derivatives of `Q f` are square
integrable, with `‖∂ (Q f)‖ = ‖∂bar (Q f)‖ = ‖f‖` (`TauCeti.norm_flatLineBeurling_apply`). -/
theorem setIntegral_flatLineCRInverse_mul_conj_conjWirtingerDeriv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hφ : φ ∈ flatLineSections 2 ω₁ ω₂ θ₁ θ₂) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f p * conj (conjWirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
      -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        flatLineBeurling ω₁ ω₂ θ₁ θ₂ f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  have hc := contDiff_of_mem_flatLineSections hφ
  rw [setIntegral_mul_conj_comp_latticeCoord_eq_inner
      ((hc.of_le one_le_two).continuous_conjWirtingerDeriv_apply 1),
    setIntegral_mul_conj_comp_latticeCoord_eq_inner hc.continuous]
  exact inner_conjWirtingerToLp_flatLineCRInverse hω hθ f ⟨φ, hφ⟩

/-- **The inverse of `∂bar` gains one derivative.** Let `ω₁, ω₂` be linearly independent over `ℝ`
and let `θ₁` or `θ₂` not be an integer. For every square-integrable section `f` and every
direction `v ∈ ℂ`, the section `Q f = flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f` has the square-integrable
weak derivative `v • flatLineBeurling ω₁ ω₂ θ₁ θ₂ f + conj v • f` along `v`: for every `C²`
section `φ`, `∫ Q f · conj (Dφ v) = -∫ (v • flatLineBeurling f + conj v • f) · conj φ`. Its norm
is at most `2 ‖v‖ ‖f‖` (`TauCeti.norm_smul_flatLineBeurling_add_smul_le`). For `v = ω₁` and
`v = ω₂` these are the weak derivatives of `Q f` in the lattice coordinates `s` and `t`, so `Q f`
lies in `H¹`. -/
theorem setIntegral_flatLineCRInverse_mul_conj_fderiv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hφ : φ ∈ flatLineSections 2 ω₁ ω₂ θ₁ θ₂) (v : ℂ) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f p * conj (fderiv ℝ φ (p.1 * ω₁ + p.2 * ω₂) v) =
      -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        (v • flatLineBeurling ω₁ ω₂ θ₁ θ₂ f + conj v • f) p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  have hc := contDiff_of_mem_flatLineSections hφ
  have hcont := (hc.continuous_fderiv two_ne_zero).clm_apply (continuous_const (y := v))
  have hD : (memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂) hcont).toLp _ =
      v • wirtingerToLp ω₁ ω₂ θ₁ θ₂ ⟨φ, hφ⟩ + conj v • conjWirtingerToLp ω₁ ω₂ θ₁ θ₂ ⟨φ, hφ⟩ := by
    rw [wirtingerToLp_apply, conjWirtingerToLp_apply, ← MemLp.toLp_const_smul,
      ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ ?_)
    simp [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv]
  have hw : inner ℂ (wirtingerToLp ω₁ ω₂ θ₁ θ₂ ⟨φ, hφ⟩) (flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f) =
      -inner ℂ (sectionToLp ω₁ ω₂ θ₁ θ₂ ⟨φ, hφ⟩) f := by
    have h := setIntegral_flatLineCRInverse_mul_conj_wirtingerDeriv hω hθ f hφ
    rw [setIntegral_mul_conj_comp_latticeCoord_eq_inner
        ((hc.of_le one_le_two).continuous_wirtingerDeriv_apply 1),
      setIntegral_mul_conj_comp_latticeCoord_eq_inner hc.continuous] at h
    exact h
  have hs : (memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂) hc.continuous).toLp _ =
      sectionToLp ω₁ ω₂ θ₁ θ₂ ⟨φ, hφ⟩ :=
    (sectionToLp_apply ⟨φ, hφ⟩).symm
  rw [setIntegral_mul_conj_comp_latticeCoord_eq_inner hcont, hD,
    setIntegral_mul_conj_comp_latticeCoord_eq_inner hc.continuous, hs, inner_add_left,
    inner_smul_left, inner_smul_left, hw, inner_conjWirtingerToLp_flatLineCRInverse hω hθ f,
    inner_add_right, inner_smul_right, inner_smul_right, conj_conj]
  ring

end Regularity

end TauCeti
