/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Regularity
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import TauCeti.Analysis.Matrix.EuclideanLin.MeanOscillation
import TauCeti.Analysis.PDE.DirichletProblem.HomogeneousSobolev
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# Whole-space `W^{1,p}` estimates for coefficients of small BMO norm, `1 < p < 2`

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants
`0 < λ ≤ Λ`, neither symmetric nor continuous in general, whose field of operators `a(x)` has small
BMO seminorm (`TauCeti.bmoSeminorm`): its mean oscillation is at most `δ` on every ball. Let `u` be
a finite-energy weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` on `ℝ^{n+1}`,

that is an element of the homogeneous Sobolev space `D^{1,2}(ℝ^{n+1})` (`TauCeti.D1p0`), recorded
by its gradient field, with `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`. Such a
solution exists and is unique for every `G ∈ L²`
(`TauCeti.PDE.existsUnique_forall_integral_matrixBilinearForm_eq_integral_inner`). This file proves,
for `1 < p < 2` and every `G ∈ L² ∩ Lᵖ`, the `W^{1,p}` estimate

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`,

with `C` and the threshold `δ` depending only on `n`, `p`, `λ` and `Λ`, and the membership
`∇u ∈ Lᵖ` as a conclusion
(`TauCeti.PDE.exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le_of_lt_two`).

For `2 < p < ∞` and every `G ∈ Lᵖ` the same estimate is the whole-space regularity theorem
`TauCeti.PDE.exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le`, which extends the interior
regularity theorem by exhausting the space with balls. At `p = 2` the estimate is the energy
estimate `λ ‖∇u‖_{L²} ≤ ‖G‖_{L²}`
(`TauCeti.PDE.mul_norm_le_of_forall_integral_matrixBilinearForm_eq_integral_inner`), which needs no
smallness of the oscillation. Together these give the whole range `1 < p < ∞`.

The a priori estimate
`TauCeti.PDE.exists_eLpNorm_le_of_forall_integral_matrixBilinearForm_eq_of_setAverage_le` covers
`2 < p < ∞` for solutions already known to have `∇u ∈ Lᵖ`. Krylov's sharp function method behind
it works with the `L²` mean oscillation of `∇u` and does not reach `p < 2`; that range is reached
here by duality.

## The argument

For `1 < p < 2` let `p' > 2` be the Hölder conjugate exponent, and let `Φ` be bounded and vanish
off a set of finite measure. The adjoint problem `-∂ᵢ((aᵀ)ⁱʲ ∂ⱼv) = -div Φ` has a finite-energy
solution `v`. The transposed coefficients are uniformly elliptic with the same constants and their
BMO seminorm is at most twice that of `a`, since transposition is the adjoint of operators, an
isometry (`TauCeti.bmoSeminorm_toEuclideanCLM_conjTranspose_le`). So the whole-space regularity
theorem for `p' > 2` gives `‖∇v‖_{L^{p'}} ≤ C ‖Φ‖_{L^{p'}}`. Testing the equation of `v` with `u`
and that of `u` with `v` gives `∫ ⟨∇u, Φ⟩ = ∫ ⟨G, ∇v⟩`
(`TauCeti.PDE.integral_inner_eq_integral_inner_of_forall_transpose`), which Hölder's inequality
bounds by `C ‖G‖_{Lᵖ} ‖Φ‖_{L^{p'}}`. Norming `∇u` by such `Φ`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`) gives the
estimate. The hypothesis `G ∈ L²` makes the pairing `∫ ⟨G, ∇v⟩` the limit of the pairings with
test gradients.

## Main declarations

* `TauCeti.PDE.exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le_of_lt_two`:
  the whole-space `W^{1,p}` regularity and estimate, `1 < p < 2`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.8.
* G. Di Fazio, *Lᵖ estimates for divergence form elliptic equations with discontinuous
  coefficients*, Boll. Un. Mat. Ital. A (7) **10** (1996), 409–420, Theorem 2.1.
* P. Auscher, M. Qafsaoui, *Observations on `W^{1,p}` estimates for divergence elliptic equations
  with VMO coefficients*, Boll. Un. Mat. Ital. B (8) **5** (2002), 487–509, Theorem 1.1.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace Matrix
open scoped ENNReal NNReal Distributions Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Whole-space `W^{1,p}` estimate for coefficients of small BMO norm, `1 < p < 2`.** Let
`1 < p < 2` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ`
and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`,
uniformly elliptic with constants `λ, Λ`, whose field of operators `a(x)` has BMO seminorm at most
`δ`. Let `u` be an element of the homogeneous Sobolev space `D^{1,2}_0(ℝ^{n+1})`
(`TauCeti.D1p0`), recorded by its gradient field, which solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly,
that is `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`, with `G ∈ L² ∩ Lᵖ`. Then
`∇u ∈ Lᵖ` and

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`.

The hypothesis `G ∈ L²` is what lets the equation of `u` be tested with the adjoint solution `v`,
making `∫ ⟨G, ∇v⟩` the limit of the pairings with test gradients; the constant does not depend on
`‖G‖_{L²}`. The coefficients need not be symmetric or continuous. -/
theorem exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le_of_lt_two
    {p : ℝ≥0∞} (hp : 1 < p) (hp2 : p < 2) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume ≤ ENNReal.ofReal δ →
        ∀ (u : D1p0 volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            ∫ x, matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)
                ((u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) x) =
              ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp G 2 volume → MemLp G p volume →
          MemLp (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) p volume ∧
            eLpNorm (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
                (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
                  Set (EuclideanSpace ℝ (Fin (n + 1)))))) p volume ≤
              C * eLpNorm G p volume := by
  -- The Hölder conjugate exponent `q = 1 + (p - 1)⁻¹` lies in `(2, ∞)`.
  set q := ENNReal.conjExponent p
  have : p.HolderConjugate q := .conjExponent hp.le
  have hq2 : 2 < q := by
    have h1 : p - 1 < 1 := by
      rw [ENNReal.sub_lt_iff_lt_right ENNReal.one_ne_top hp.le]
      simpa [one_add_one_eq_two] using hp2
    exact one_add_one_eq_two.symm.trans_lt
      (ENNReal.add_lt_add_left ENNReal.one_ne_top (ENNReal.one_lt_inv.2 h1))
  obtain ⟨C, δ, hδ, hreg⟩ := exists_memLp_gradient_and_eLpNorm_le_of_bmoSeminorm_le (n := n) hq2
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp).ne lam Lam
  refine ⟨C, δ / 2, half_pos hδ, fun {a} ha hell hbmo u G hu hG2 hGp => ?_⟩
  have haT : AEStronglyMeasurable (fun x => (a x)ᵀ) volume :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable ha
  -- Transposing the coefficients at most doubles the BMO seminorm.
  have hbmoT : bmoSeminorm (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ) volume ≤ ENNReal.ofReal δ := by
    simp_rw [← conjTranspose_eq_transpose_of_trivial]
    refine (bmoSeminorm_toEuclideanCLM_conjTranspose_le ha).trans
      ((mul_le_mul_right hbmo 2).trans_eq ?_)
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]; ring_nf
  have hg2 : MemLp (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))))) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (u : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
          Set (EuclideanSpace ℝ (Fin (n + 1))))))
  -- Norm `∇u` by bounded test fields `Φ` vanishing off a set of finite measure.
  have hle := hg2.aestronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℝ)
    (q := p) (q' := q) (C := C * eLpNorm G p volume) fun Φ s hs hΦs hΦ => by
    have hΦ2 : MemLp Φ 2 volume := hΦ.mono_exponent_of_measure_support_ne_top hΦs hs le_top
    -- The finite-energy solution `v` of the adjoint problem `-∂ᵢ((aᵀ)ⁱʲ ∂ⱼv) = -div Φ` has
    -- `‖∇v‖_{L^q} ≤ C ‖Φ‖_{L^q}`, and `∫ ⟨∇u, Φ⟩ = ∫ ⟨G, ∇v⟩`.
    obtain ⟨v, hv, -⟩ := existsUnique_forall_integral_matrixBilinearForm_eq_integral_inner
      (Omega := ⊤) (by rw [Opens.coe_top]; exact hell.transpose) haT.restrict (hΦ2.restrict _)
    obtain ⟨-, hvq⟩ := hreg haT hell.transpose hbmoT
      v Φ (fun ψ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hv ψ)
      (hΦ.mono_exponent_of_measure_support_ne_top hΦs hs le_top)
    have hpair := integral_inner_eq_integral_inner_of_forall_transpose ha.restrict
      (fun x _ => hell.opNorm_matrixBilinearForm_le (mem_univ x)) (hG2.restrict _)
      (hΦ2.restrict _) (fun ψ => by simpa only [Opens.coe_top, Measure.restrict_univ] using hu ψ)
      hv
    simp only [Opens.coe_top, Measure.restrict_univ] at hpair
    rw [hpair]
    calc _ ≤ eLpNorm G p volume * eLpNorm _ q volume := enorm_integral_inner_le
      _ ≤ eLpNorm G p volume * (C * eLpNorm Φ q volume) := by gcongr
      _ = C * eLpNorm G p volume * eLpNorm Φ q volume := by ring
  exact ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hGp.eLpNorm_lt_top), hle⟩

end PDE

end TauCeti
