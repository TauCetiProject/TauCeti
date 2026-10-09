/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Basic
public import TauCeti.Analysis.Analytic.LaurentConjugation

/-!
# Conjugation-compatible Laurent forms of nonmonic roots

The Laurent forms extracted from an analytic splitting of integral normalization
respect a conjugation action on the original roots: conjugate labels have equal
integer exponents and conjugate analytic units. The unit identity holds across
the exceptional hyperplane, even when the original roots have poles there.

Root branches, their analytic scaled extensions, and the action on labels are
inputs. Neither Laurent exponents nor unit symmetry are assumed. This permits
the root-covering and conjugation arguments to be used independently of the
extraction of Laurent units. No simplicity assumption is needed for this step.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method
for CAD construction*, J. Symbolic Comput. 92 (2019), §4, Corollary 4.2.
-/

public section

open Filter Polynomial Topology ComplexConjugate

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Laurent forms of nonmonic roots can be chosen compatibly with conjugation.
The parameter map is continuous at and fixes the central parameter; the
distinguished coordinate is conjugated. Labels related by `σ` have the same
Laurent exponent, and their unit germs satisfy the corresponding conjugation
identity on the full neighborhood. The root equations themselves are required
only off the hyperplane, where poles are allowed. -/
theorem exists_root_eq_zpow_mul_unit_conj {d a c : ℕ} (hd : 0 < d)
    {P : E × ℂ → Polynomial ℂ} {r s : Fin d → E × ℂ → ℂ} {x₀ : E}
    {u v : E × ℂ → ℂ} (hs : ∀ i, AnalyticAt ℂ (s i) (x₀, 0))
    (hu : AnalyticAt ℂ u (x₀, 0)) (hu0 : u (x₀, 0) ≠ 0)
    (hv : AnalyticAt ℂ v (x₀, 0)) (hv0 : v (x₀, 0) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), (P p).coeff d = p.2 ^ c * v p)
    (hconst : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), (P p).coeff 0 = p.2 ^ a * u p)
    (hscale : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i, (P p).coeff d * r i p = s i p)
    {τ : E → E} (hτ : ContinuousAt τ x₀) (hτ0 : τ x₀ = x₀) {σ : Fin d → Fin d}
    (hσ : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i, r (σ i) p = conj (r i (τ p.1, conj p.2))) :
    ∃ e : Fin d → ℤ, ∃ w : Fin d → E × ℂ → ℂ,
      (∀ i, AnalyticAt ℂ (w i) (x₀, 0)) ∧
      (∀ i, w i (x₀, 0) ≠ 0) ∧ (∀ i, e (σ i) = e i) ∧
      ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), (∀ i, w i p ≠ 0) ∧
        (∀ i, w (σ i) p = conj (w i (τ p.1, conj p.2))) ∧
        (p.2 ≠ 0 → ∀ i, r i p = p.2 ^ e i * w i p) := by
  obtain ⟨m, w, hw, hw0, hform⟩ := exists_root_eq_zpow_mul_unit hd hs hu hu0 hv hv0
    hnorm (by simpa using hlead) (by simpa using hconst) hscale
  let e : Fin d → ℤ := fun i ↦ (m i : ℤ) - c
  have hform' : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)),
      (∀ i, w i p ≠ 0) ∧ (p.2 ≠ 0 → ∀ i, r i p = p.2 ^ e i * w i p) := by
    simpa only [sub_zero] using hform
  let T : E × ℂ → E × ℂ := fun p ↦ (τ p.1, conj p.2)
  have hT : ContinuousAt T (x₀, 0) := (hτ.comp continuousAt_fst).prodMk
    (Complex.continuous_conj.continuousAt.comp continuousAt_snd)
  have hT0 : T (x₀, 0) = (x₀, 0) := by simp [T, hτ0]
  have hTt : Tendsto T (𝓝 (x₀, (0 : ℂ))) (𝓝 (x₀, (0 : ℂ))) := by
    simpa only [hT0] using hT.tendsto
  have hconj (i : Fin d) : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      p.2 ^ e (σ i) * w (σ i) p =
        conj ((conj p.2) ^ e i * w i (τ p.1, conj p.2)) := by
    filter_upwards [hform', hTt.eventually hform', hσ]
      with p hp hTp hsp hp0
    have hTp0 : (T p).2 ≠ 0 := by simpa [T] using hp0
    rw [← hp.2 hp0 (σ i), hsp hp0 i, hTp.2 hTp0 i]
  have hcompat (i : Fin d) : e (σ i) = e i ∧
      ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), w (σ i) p = conj (w i (τ p.1, conj p.2)) :=
    ((hw (σ i)).restrictScalars (𝕜 := ℝ)).laurent_eq_of_conj (hw0 (σ i))
      ((hw i).restrictScalars (𝕜 := ℝ)) (hw0 i) hτ hτ0 (hconj i)
  have hall : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)),
      ∀ i, w (σ i) p = conj (w i (τ p.1, conj p.2)) := by
    rw [eventually_all]
    exact fun i ↦ (hcompat i).2
  refine ⟨e, w, hw, hw0, fun i ↦ (hcompat i).1, ?_⟩
  filter_upwards [hform', hall] with p hp hwp
  exact ⟨hp.1, hwp, hp.2⟩

end TauCeti
