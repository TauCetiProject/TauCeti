/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.ErrorTransform
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Rat
public import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import TauCeti.Analysis.LaplaceTransform.Meromorphic
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Rational.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.RiemannHypotheses.HalfPlane
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# One-sided Chebyshev bounds and zeros of Dedekind zeta

Landau's theorem applied to `ψ_K(x) - x` converts a lower bound of order `x ^ θ` into
zero-freeness to the right of `θ`. An upper bound instead allows a rightmost real zero:
the Laplace transform of the error has residue `-m / ρ` at a zero `ρ` of multiplicity `m`.
For the rational field the real exception is impossible, so either one-sided bound at
all exponents greater than `1 / 2` implies the Riemann hypothesis.

This is the classical oscillation argument for `ψ(x) - x`: a one-sided bound makes the Laplace
transform of the error a transform of a function of constant sign, and Landau's theorem places its
first singularity on the real axis.

## References

* E. Landau, *Über einen Satz von Tschebyschef*, Math. Ann. **61** (1905).
* A. E. Ingham, *The Distribution of Prime Numbers*, Cambridge Tracts in Mathematics and
  Mathematical Physics **30**, Cambridge University Press, 1932, Chapter V.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Cambridge Studies in Advanced Mathematics **97**, Cambridge University Press, 2007, Chapter 15.
-/

public section

open Filter MeasureTheory Set
open scoped ComplexOrder

namespace TauCeti

open LFunctions

/-- The Riemann hypothesis follows from bounds `P C (1 / 2 + ε)`, one for each `ε > 0`, as soon as
each bound `P C σ` with `σ > 1 / 2` excludes zeros of `ζ_ℚ` to the right of `σ`. -/
private lemma riemannHypothesis_of_forall_exponent {P : ℝ → ℝ → Prop}
    (h : ∀ ε > (0 : ℝ), ∃ C : ℝ, P C (1 / 2 + ε))
    (hP : ∀ σ > (1 / 2 : ℝ), ∀ C, P C σ → ZeroFreeRightOf σ (dedekindZetaC ℚ)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_zeroFreeRightOf, ← zeroFreeRightOf_dedekindZetaC_rat_iff,
    zeroFreeRightOf_iff_forall_gt]
  intro σ hσ
  obtain ⟨C, hC⟩ := h (σ - 1 / 2) (sub_pos.mpr hσ)
  rw [add_sub_cancel] at hC
  exact hP σ hσ C hC

variable (K : Type*) [Field K] [NumberField K]

/-- An eventual lower bound for `ψ_K(x) - x` by `-C * x ^ θ` excludes zeros of `ζ_K` in
`Re s > θ`. -/
theorem zeroFreeRightOf_dedekindZetaC_of_eventually_neg_rpow_le_primePsi_sub {θ C : ℝ}
    (hθ : 0 ≤ θ) (h : ∀ᶠ x in atTop, -(C * x ^ θ) ≤ primePsi K univ x - x) :
    ZeroFreeRightOf θ (dedekindZetaC K) := by
  obtain ⟨u₀, hg⟩ := exists_ae_le_exp_of_eventually_le_rpow
    (f := fun x ↦ -(primePsi K univ x - x)) (h.mono fun _ hx ↦ neg_le.mp hx)
  have hF : MeromorphicOn (fun s ↦ -primePsiErrorTransform K s) {s | θ < s.re} :=
    (meromorphicNFOn_primePsiErrorTransform K).meromorphicOn.neg.mono_set (subset_univ _)
  have hL (s : ℂ) (hs : 1 < s.re) : HasLaplace
      (fun u ↦ ((-(primePsi K univ (Real.exp u) - Real.exp u) : ℝ) : ℂ)) s
      (-primePsiErrorTransform K s) := by
    refine (hasLaplace_primePsi_sub_exp K hs).neg.congr_ae (.of_forall fun u ↦ ?_)
    simp only [Pi.neg_apply, Complex.ofReal_neg]
  have hsign (β : ℝ) (hβ : β ∈ Ioc θ 1)
      (hp : meromorphicOrderAt (fun s ↦ -primePsiErrorTransform K s) (β : ℂ) < 0) :
      0 ≤ (meromorphicTrailingCoeffAt (fun s ↦ -primePsiErrorTransform K s) (β : ℂ)).re := by
    rw [← meromorphicOrderAt_fun_neg] at hp
    rw [meromorphicTrailingCoeffAt_fun_neg, Complex.neg_re]
    exact neg_nonneg.mpr (re_meromorphicTrailingCoeffAt_primePsiErrorTransform_neg K
      (hθ.trans_lt hβ.1) hp).le
  have hn := (hasLaplace_toMeromorphicNFOn_of_ae_le_exp hg hF hL hsign).1
  refine
    (zeroFreeRightOf_dedekindZetaC_iff_forall_meromorphicOrderAt_primePsiErrorTransform_nonneg
      K hθ).mpr fun s hs ↦ ?_
  simpa only [← meromorphicOrderAt_fun_neg] using hn s hs

/-- Under an eventual upper bound for `ψ_K(x) - x` by `C * x ^ θ`, either `ζ_K` has no zero
in `Re s > θ`, or it has a real zero in `(θ, 1)` whose real part bounds those of all zeros. -/
theorem zeroFreeRightOf_or_exists_rightmost_real_zero_of_eventually_primePsi_sub_le_rpow
    {θ C : ℝ} (hθ : 0 ≤ θ) (h : ∀ᶠ x in atTop, primePsi K univ x - x ≤ C * x ^ θ) :
    ZeroFreeRightOf θ (dedekindZetaC K) ∨
      ∃ β ∈ Ioo θ 1, 0 < meromorphicOrderAt (dedekindZetaC K) (β : ℂ) ∧
        ZeroFreeRightOf β (dedekindZetaC K) := by
  obtain ⟨u₀, hg⟩ := exists_ae_le_exp_of_eventually_le_rpow (f := fun x ↦ primePsi K univ x - x) h
  rcases hasLaplace_toMeromorphicNFOn_or_exists_rightmost_real_pole_of_ae_le_exp hg
      ((meromorphicNFOn_primePsiErrorTransform K).meromorphicOn.mono_set (subset_univ _))
      (fun _ hs ↦ hasLaplace_primePsi_sub_exp K hs) with ⟨hn, -⟩ | ⟨β, hβ, hβ₁, hp, -, -, hn, -⟩
  · exact .inl
      ((zeroFreeRightOf_dedekindZetaC_iff_forall_meromorphicOrderAt_primePsiErrorTransform_nonneg
        K hθ).mpr hn)
  have hβne : β ≠ 1 := by
    rintro rfl
    exact hp.not_ge (by simpa using
      (analyticAt_primePsiErrorTransform_one K).meromorphicOrderAt_nonneg)
  have hβ₀ := hθ.trans_lt hβ
  exact .inr ⟨β, ⟨hβ, hβ₁.lt_of_ne hβne⟩,
    (meromorphicOrderAt_primePsiErrorTransform_neg_iff K
      (Complex.ofReal_ne_zero.mpr hβ₀.ne')).mp hp,
    (zeroFreeRightOf_dedekindZetaC_iff_forall_meromorphicOrderAt_primePsiErrorTransform_nonneg
      K hβ₀.le).mpr hn⟩

/-- An eventual upper bound for `ψ_K(x) - x` by `C * x ^ θ` excludes zeros in `Re s > θ`
if `ζ_K` has no real zeros in `(θ, 1)`. -/
theorem zeroFreeRightOf_dedekindZetaC_of_eventually_primePsi_sub_le_rpow {θ C : ℝ}
    (hθ : 0 ≤ θ) (h : ∀ᶠ x in atTop, primePsi K univ x - x ≤ C * x ^ θ)
    (hreal : ∀ β ∈ Ioo θ 1, meromorphicOrderAt (dedekindZetaC K) (β : ℂ) ≤ 0) :
    ZeroFreeRightOf θ (dedekindZetaC K) := by
  rcases zeroFreeRightOf_or_exists_rightmost_real_zero_of_eventually_primePsi_sub_le_rpow K hθ h
    with hz | ⟨β, hβ, hz, -⟩
  · exact hz
  · exact (hz.not_ge (hreal β hβ)).elim

/-- The Riemann hypothesis follows from eventual lower bounds for `ψ(x) - x` of order
`x ^ (1 / 2 + ε)` for every `ε > 0`. -/
theorem riemannHypothesis_of_eventually_neg_rpow_le_psi_sub
    (h : ∀ ε > (0 : ℝ), ∃ C : ℝ,
      ∀ᶠ x in atTop, -(C * x ^ (1 / 2 + ε)) ≤ Chebyshev.psi x - x) : RiemannHypothesis :=
  riemannHypothesis_of_forall_exponent
    (P := fun C θ ↦ ∀ᶠ x in atTop, -(C * x ^ θ) ≤ Chebyshev.psi x - x) h fun σ hσ _ hC ↦
      zeroFreeRightOf_dedekindZetaC_of_eventually_neg_rpow_le_primePsi_sub ℚ (by linarith)
        (by simpa only [primePsi_rat_univ] using hC)

/-- The Riemann hypothesis follows from eventual upper bounds for `ψ(x) - x` of order
`x ^ (1 / 2 + ε)` for every `ε > 0`. -/
theorem riemannHypothesis_of_eventually_psi_sub_le_rpow
    (h : ∀ ε > (0 : ℝ), ∃ C : ℝ,
      ∀ᶠ x in atTop, Chebyshev.psi x - x ≤ C * x ^ (1 / 2 + ε)) : RiemannHypothesis := by
  refine riemannHypothesis_of_forall_exponent
    (P := fun C θ ↦ ∀ᶠ x in atTop, Chebyshev.psi x - x ≤ C * x ^ θ) h fun σ hσ _ hC ↦ ?_
  refine zeroFreeRightOf_dedekindZetaC_of_eventually_primePsi_sub_le_rpow ℚ (by linarith)
    (by simpa only [primePsi_rat_univ] using hC) fun β hβ ↦ ?_
  rw [meromorphicOrderAt_congr (dedekindZetaC_rat_eventuallyEq_riemannZeta β)]
  exact not_lt.mp fun hz ↦ (riemannZeta_lt_zero (by linarith [hβ.1]) hβ.2).ne
    (meromorphicOrderAt_riemannZeta_pos_iff.mp hz)

end TauCeti
