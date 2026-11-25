/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.InfiniteDimensional
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.RingTheory.Polynomial.Basic

/-!
# `W^{k,p}` on the closed disc is infinite-dimensional

On the closed unit disc `Complex.UnitClosedDisc` with the trivial bundle of a nonzero fibre `F`, the
sections `z ↦ P(re z) v`, for real polynomials `P` and a fixed `v ≠ 0`, are linearly independent:
a polynomial vanishing on `[-1, 1]` is zero. So the `Cᵏ` sections are infinite-dimensional
(`TauCeti.not_finiteDimensional_contMDiffSection_unitClosedDisc`), and so is the bordered Sobolev
space `W^{k,p}` for every finite bundle atlas, every order `k` and `1 ≤ p ≤ ∞`
(`TauCeti.BorderedSobolevSection.not_finiteDimensional_unitClosedDisc`). Its identity is not a
compact operator (`TauCeti.BorderedSobolevSection.not_isCompactOperator_id_unitClosedDisc`).

## Main results

* `TauCeti.not_finiteDimensional_contMDiffSection_unitClosedDisc`: the `Cᵏ` sections of the trivial
  bundle over the closed disc are infinite-dimensional.
* `TauCeti.BorderedSobolevSection.not_finiteDimensional_unitClosedDisc`,
  `TauCeti.BorderedSobolevSection.not_isCompactOperator_id_unitClosedDisc`: `W^{k,p}` on the
  closed disc is infinite-dimensional, and its identity is not compact.
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ENNReal ContDiff Complex.UnitDisc

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The section `z ↦ P(re z) v` of the trivial bundle over the closed disc, for a real polynomial
`P`. -/
private def polySection (k : ℕ) (v : F) (P : Polynomial ℝ) :
    Cₛ^k⟮closedUpperHalfPlaneModel; F, Bundle.Trivial 𝕔𝔻 F⟯ :=
  ⟨fun z ↦ P.eval (z : ℂ).re • v, fun x ↦ (contMDiffAt_section_iff x).2 (by
    have hre : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, ℝ) k fun z : 𝕔𝔻 ↦ (z : ℂ).re :=
      Complex.reCLM.contDiff.contMDiff.comp Complex.UnitClosedDisc.contMDiff_coe
    have hP : ContDiff ℝ k fun t : ℝ ↦ P.eval t := by
      simpa using Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) P k
    exact (hP.contMDiff.comp hre).smul contMDiff_const x)⟩

private theorem polySection_apply (k : ℕ) (v : F) (P : Polynomial ℝ) (z : 𝕔𝔻) :
    polySection k v P z = P.eval (z : ℂ).re • v :=
  rfl

/-- **The `Cᵏ` sections over the closed disc are infinite-dimensional.** For a nonzero fibre `F`,
the sections `z ↦ P(re z) v` for real polynomials `P` and a fixed `v ≠ 0` are linearly
independent. -/
theorem not_finiteDimensional_contMDiffSection_unitClosedDisc [Nontrivial F] (k : ℕ) :
    ¬ FiniteDimensional ℝ Cₛ^k⟮closedUpperHalfPlaneModel; F, Bundle.Trivial 𝕔𝔻 F⟯ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  let L : Polynomial ℝ →ₗ[ℝ] Cₛ^k⟮closedUpperHalfPlaneModel; F, Bundle.Trivial 𝕔𝔻 F⟯ :=
    { toFun := polySection k v
      map_add' := fun P Q ↦ ContMDiffSection.ext fun z ↦ by
        simp [polySection_apply, add_smul]
      map_smul' := fun c P ↦ ContMDiffSection.ext fun z ↦ by
        simp [polySection_apply, smul_smul] }
  intro hfin
  -- A polynomial is determined by its values on `[-1, 1]`.
  refine Polynomial.not_finite (R := ℝ) (FiniteDimensional.of_injective L fun P Q hPQ ↦
    Polynomial.eq_of_infinite_eval_eq P Q ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono
      fun t ht ↦ ?_))
  have ht' : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ht
  have h := congrArg (fun s : Cₛ^k⟮closedUpperHalfPlaneModel; F, Bundle.Trivial 𝕔𝔻 F⟯ ↦
    s (Complex.UnitClosedDisc.mk t ht')) hPQ
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, polySection_apply, Complex.UnitClosedDisc.coe_mk,
    Complex.ofReal_re] at h
  exact (smul_left_injective ℝ hv).eq_iff.1 h

namespace BorderedSobolevSection

variable [Nontrivial F] [FiniteDimensional ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **`W^{k,p}` on the closed disc is infinite-dimensional.** For the trivial bundle over the
closed unit disc with a nonzero finite-dimensional fibre and every finite bundle atlas, the Sobolev
space of sections is infinite-dimensional. -/
theorem not_finiteDimensional_unitClosedDisc
    (A : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F)) :
    ¬ FiniteDimensional ℝ (BorderedSobolevSection A p k) :=
  not_finiteDimensional A (not_finiteDimensional_contMDiffSection_unitClosedDisc k)

/-- **`W^{k,p} → W^{k,p}` is not compact on the closed disc.** For the trivial bundle over the
closed unit disc with a nonzero finite-dimensional fibre, every finite bundle atlas, every order `k`
and `1 ≤ p ≤ ∞`, the identity of the Sobolev space of sections is not a compact operator. -/
theorem not_isCompactOperator_id_unitClosedDisc
    (A : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F)) :
    ¬ IsCompactOperator (id : BorderedSobolevSection A p k → BorderedSobolevSection A p k) :=
  not_isCompactOperator_id A (not_finiteDimensional_contMDiffSection_unitClosedDisc k)

end BorderedSobolevSection

end TauCeti
