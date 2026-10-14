/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference.Nonmonic
public import TauCeti.Analysis.Analytic.LaurentConjugation

/-!
# Conjugation-compatible Laurent forms of root differences

For a nonmonic polynomial family, root branches related by conjugation have Laurent
differences whose exponents agree and whose analytic units are conjugate. This combines
the difference factorization with the conjugation action, including when the original
roots have poles at the distinguished hyperplane.

The root branches and their analytic scaled extensions are inputs. The result is a
reusable step for retaining conjugation symmetry when root-difference forms are assembled
from a labelled splitting.

## Reference

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Polynomial Topology ComplexConjugate

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Laurent forms of pairwise differences of nonmonic roots can be chosen compatibly
with conjugation. The permutation acts on the labels, and the parameter map acts
on the base; corresponding differences have the same integer exponent and conjugate
analytic unit. The root and difference equations are required only off the hyperplane. -/
theorem exists_root_sub_eq_zpow_mul_unit_conj {d a c : ℕ}
    {P : E × ℂ → ℂ[X]} {r s : Fin d → E × ℂ → ℂ} {x₀ : E}
    {u v : E × ℂ → ℂ}
    (hs : ∀ i, AnalyticAt ℂ (s i) (x₀, 0))
    (hu : AnalyticAt ℂ u (x₀, 0)) (hu0 : u (x₀, 0) ≠ 0)
    (hv : AnalyticAt ℂ v (x₀, 0)) (hv0 : v (x₀, 0) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).coeff d = p.2 ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).discr = p.2 ^ a * u p)
    (hscale : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i, (P p).coeff d * r i p = s i p)
    {τ : E → E} (hτ : ContinuousAt τ x₀) (hτ0 : τ x₀ = x₀)
    (σ : Equiv.Perm (Fin d))
    (hσ : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i, r (σ i) p = conj (r i (τ p.1, conj p.2))) :
    ∃ e : Fin d → Fin d → ℤ, ∃ w : Fin d → Fin d → E × ℂ → ℂ,
      (∀ i j, i ≠ j → AnalyticAt ℂ (w i j) (x₀, 0)) ∧
      (∀ i j, i ≠ j → w i j (x₀, 0) ≠ 0) ∧
      (∀ i j, i ≠ j → e (σ i) (σ j) = e i j) ∧
      ∀ i j, i ≠ j → ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)),
        w i j p ≠ 0 ∧ (p.2 ≠ 0 →
          r i p - r j p = p.2 ^ e i j * w i j p) ∧
          w (σ i) (σ j) p = conj (w i j (τ p.1, conj p.2)) := by
  -- Choose a Laurent form for each off-diagonal pair and pad the diagonal.
  let hpair (i j : Fin d) (hij : i ≠ j) :=
    exists_root_sub_eq_zpow_mul_unit hs hu hu0 hv hv0 hnorm
      (by filter_upwards [hlead] with p hp hp0; simpa using hp hp0)
      (by filter_upwards [hdiscr] with p hp hp0; simpa using hp hp0)
      (by filter_upwards [hscale] with p hp hp0; exact ⟨hp hp0 i, hp hp0 j⟩) hij
  choose e₀ w₀ hw hw0 hform using hpair
  let e : Fin d → Fin d → ℤ := fun i j ↦ if hij : i ≠ j then e₀ i j hij else 0
  let w : Fin d → Fin d → E × ℂ → ℂ := fun i j ↦
    if hij : i ≠ j then w₀ i j hij else fun _ ↦ 0
  let T : E × ℂ → E × ℂ := fun p ↦ (τ p.1, conj p.2)
  have hTt : Tendsto T (𝓝 (x₀, (0 : ℂ))) (𝓝 (x₀, (0 : ℂ))) := by
    simpa only [T, Prod.map_def, hτ0, map_zero] using hτ.tendsto.prodMap_nhds
      (Complex.continuous_conj.tendsto (0 : ℂ))
  -- Compare the two forms for each pair using conjugation of the roots.
  have hcompat (i j : Fin d) (hij : i ≠ j) (hσij : σ i ≠ σ j) :
      e₀ (σ i) (σ j) hσij = e₀ i j hij ∧
        ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)),
          w₀ (σ i) (σ j) hσij p =
            conj (w₀ i j hij (T p)) := by
    have hrelation : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
        p.2 ^ e₀ (σ i) (σ j) hσij *
            w₀ (σ i) (σ j) hσij p =
          conj ((conj p.2) ^ e₀ i j hij * w₀ i j hij (T p)) := by
      filter_upwards [hform (σ i) (σ j) hσij,
        hTt.eventually (hform i j hij), hσ] with p hp hTp hsigma hp0
      have hTp0 : (T p).2 ≠ 0 := by simpa [T] using hp0
      have h1 : r (σ i) p - r (σ j) p = p.2 ^
          e₀ (σ i) (σ j) hσij *
            w₀ (σ i) (σ j) hσij p := by
        simpa only [sub_zero] using hp.2 hp0
      have h2 : r i (T p) - r j (T p) = (T p).2 ^ e₀ i j hij * w₀ i j hij (T p) := by
        simpa only [sub_zero] using hTp.2 hTp0
      calc
        _ = r (σ i) p - r (σ j) p := h1.symm
        _ = conj (r i (T p) - r j (T p)) := by
          rw [hsigma hp0 i, hsigma hp0 j]
          exact (map_sub (starRingEnd ℂ) (r i (T p)) (r j (T p))).symm
        _ = conj ((T p).2 ^ e₀ i j hij * w₀ i j hij (T p)) :=
          congrArg conj h2
        _ = _ := by simp [T, map_mul, map_zpow₀]
    exact (hw (σ i) (σ j) hσij).restrictScalars (𝕜 := ℝ) |>.laurent_eq_of_conj
      (hw0 (σ i) (σ j) hσij) ((hw i j hij).restrictScalars (𝕜 := ℝ)) (hw0 i j hij)
      hτ hτ0 hrelation
  -- Assemble the paired forms into the indexed result.
  refine ⟨e, w, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simpa [w, hij] using hw i j hij
  · intro i j hij
    simpa [w, hij] using hw0 i j hij
  · intro i j hij
    simpa [e, hij] using
      (hcompat i j hij (σ.injective.ne hij)).1
  · intro i j hij
    have hcomp := (hcompat i j hij (σ.injective.ne hij)).2
    filter_upwards [hcomp, hform i j hij] with p hp hf
    refine ⟨?_, ?_, ?_⟩
    · simpa [w, hij] using hf.1
    · simpa [e, w, hij, sub_zero] using hf.2
    · simpa [w, e, hij, sub_zero, T] using hp

end TauCeti
