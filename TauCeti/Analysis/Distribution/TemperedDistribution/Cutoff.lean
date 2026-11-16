/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.ComplexPairing
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv

/-!
# Cut-off distributions as tempered distributions

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real normed space
`E`, and `φ` a complex test function on `Ω`. The product `φ T` is a compactly supported
distribution, and it extends to the tempered distribution

`Distribution.cutoffTempered T φ : ψ ↦ T (φ ψ)`

on all of `E`: the product of `φ` with a Schwartz function `ψ` is a test function on `Ω`, and
since `T` has finite order on the support of `φ`, the pairing `T (φ ψ)` is bounded by finitely
many Schwartz seminorms of `ψ`. This is the passage from distributions on open sets to the
Fourier analysis of tempered distributions, and in particular to Mathlib's Bessel-potential
spaces `H^s`: `φ T ∈ H^s` is a statement about `Distribution.cutoffTempered T φ`.

The extension is unique: a tempered distribution is determined by its values on real compactly
supported Schwartz functions (`TemperedDistribution.ext_real`), on which it must be `T (φ ψ)`. It
only depends on the cutoff near the support of `T`.

## Main declarations

* `Distribution.cutoffTempered T φ`: the tempered distribution `φ T`.
* `Distribution.cutoffTempered_def`, `Distribution.cutoffTempered_apply`: its value `T (φ ψ)` on
  a Schwartz function `ψ`.
* `Distribution.eq_cutoffTempered_of_forall`: uniqueness of the extension.
* `Distribution.cutoffTempered_congr`: independence of the cutoff near the support of `T`.
* `Distribution.smulLeftCLM_cutoffTempered`: multiplying `φ T` by a function `g` of temperate
  growth gives `(g φ) T`.
* `Distribution.cutoffTempered_smulLeftCLM`: `φ (g T) = (g φ) T` for a smooth real function `g`.
* `Distribution.cutoffTempered_iteratedLineDerivOp`: if `φ = 1` on the support of `χ`, then
  `χ ∂^m T = χ ∂^m (φ T)`. Together with the previous two lemmas, this computes the cut-off
  `χ P T` of a differential operator `P` with smooth coefficients applied to `T` as a differential
  operator applied to the tempered distribution `φ T`; this is
  `Distribution.cutoffTempered_sum_smul_smulLeftCLM_iteratedLineDerivOp`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.3 (the order of a
  compactly supported distribution) and §7.1 (compactly supported distributions are tempered).
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology SchwartzMap ContDiff LineDeriv

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

/-! ### The tempered distribution `φ T` -/

section Cutoff

/-- Since `T` has finite order on the support of `φ`, the pairing `T (φ ψ)` is bounded by finitely
many Schwartz seminorms of `ψ`. -/
private theorem exists_norm_complexPairing_bilinLeftCLM_le (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ ψ : 𝓢(E, ℂ),
      ‖T.complexPairing (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) φ)‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ E ℂ) ψ := by
  let K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport⟩
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_complexPairing_le (K := K) φ.tsupport_subset
  -- `φ` as a test function supported in `K`, to which the Leibniz bound applies.
  let φK : 𝓓_{K}(E, ℂ) := .of_support_subset φ.contDiff (subset_tsupport φ)
  set A := ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K N φK
  set s : Finset (ℕ × ℕ) := (Finset.range (N + 1)).image fun j ↦ (0, j)
  refine ⟨s, C * (2 ^ N * A), by positivity, fun ψ ↦ ?_⟩
  set S := s.sup (schwartzSeminormFamily ℂ E ℂ) ψ
  have hψ (j : ℕ) (hj : j ≤ N) (x : E) : ‖iteratedFDeriv ℝ j ψ x‖ ≤ S :=
    (ψ.norm_iteratedFDeriv_le_seminorm ℂ j x).trans (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily ℂ E ℂ) (x := ψ) (Finset.mem_image_of_mem
        (fun j ↦ ((0 : ℕ), j)) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))))
  have hφK : ⇑(ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) φK) =
      bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) φ := by
    ext x
    simp [φK]
  have hsupp : tsupport (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) φ) ⊆ K := by
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']
    exact tsupport_mul_subset_left
  refine (hT _ hsupp (2 ^ N * A * S) (by positivity) fun i hi x ↦ ?_).trans_eq (by ring)
  rw [← hφK]
  exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
    (ContDiffMapSupportedIn.seminorm_bilinLeftCLM_mul_le φK (ψ.smooth ⊤) hψ hi)

/-- **The tempered distribution `φ T`.** For a complex distribution `T` on `Ω` and a complex test
function `φ` on `Ω`, the compactly supported distribution `φ T`, extended to the tempered
distribution `ψ ↦ T (φ ψ)` on all of `E`. -/
def cutoffTempered (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) : 𝓢'(E, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ <|
    SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
      (fun ψ ↦ T.complexPairing (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) φ))
      (fun ψ ψ' ↦ by
        rw [← map_add]
        congr 1
        ext x
        simp [mul_add])
      (fun a ψ ↦ by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        ext x
        simp [mul_left_comm])
      (exists_norm_complexPairing_bilinLeftCLM_le T φ)

/-- The defining equation of `Distribution.cutoffTempered`: the value of `φ T` on a Schwartz
function `ψ` is `T` paired with the product `φ ψ`. -/
theorem cutoffTempered_def (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (ψ : 𝓢(E, ℂ)) :
    T.cutoffTempered φ ψ =
      T.complexPairing (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) φ) :=
  -- Mathlib has no evaluation lemma for `SchwartzMap.mkCLMtoNormedSpace`; it evaluates by
  -- definition, as in Mathlib's own evaluation lemmas for maps built with it.
  (rfl)

/-- The value of `φ T` on a Schwartz function `ψ` is the pairing of `T` with any test function
equal to `φ ψ`. -/
theorem cutoffTempered_apply (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) {ψ : 𝓢(E, ℂ)} {χ : 𝓓(Ω, ℂ)}
    (hχ : ∀ x, χ x = φ x * ψ x) : T.cutoffTempered φ ψ = T.complexPairing χ := by
  rw [cutoffTempered_def]
  congr 1
  ext x
  simp [hχ]

/-- **Uniqueness of the extension.** A tempered distribution which takes the value `T (φ ψ)` on
every real compactly supported Schwartz function `ψ` is `φ T`. -/
theorem eq_cutoffTempered_of_forall [FiniteDimensional ℝ E] (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ))
    {S : 𝓢'(E, ℂ)}
    (hS : ∀ (ψ : 𝓢(E, ℝ)) (χ : 𝓓(Ω, ℂ)), HasCompactSupport ψ → (∀ x, χ x = φ x * ψ x) →
      S (ψ.postcompCLM Complex.ofRealCLM) = T.complexPairing χ) :
    S = T.cutoffTempered φ :=
  TemperedDistribution.ext_real fun ψ hψ ↦ by
    rw [hS ψ (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
      ((ψ.postcompCLM Complex.ofRealCLM).smooth ⊤) φ) hψ fun x ↦ by simp, cutoffTempered_def]

/-- **Cutoff independence.** The tempered distribution `φ T` only depends on the germ of `φ` along
the support of `T`. -/
theorem cutoffTempered_congr [FiniteDimensional ℝ E] (T : 𝓓'(Ω, ℂ)) {φ φ' : 𝓓(Ω, ℂ)}
    (h : (φ : E → ℂ) =ᶠ[𝓝ˢ (dsupport T)] φ') : T.cutoffTempered φ = T.cutoffTempered φ' := by
  ext ψ
  rw [cutoffTempered_def, cutoffTempered_def]
  exact T.complexPairing_eq_of_eventuallyEq (h.mono fun x hx ↦ by
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', hx])

/-- The tempered distribution `φ T` is additive in `T`. -/
@[simp]
theorem cutoffTempered_add (T S : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (T + S).cutoffTempered φ = T.cutoffTempered φ + S.cutoffTempered φ := by
  ext ψ
  simp only [add_apply, cutoffTempered_def, complexPairing_add]

/-- The tempered distribution `φ T` is complex-linear in `T`. -/
@[simp]
theorem cutoffTempered_smul (c : ℂ) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (c • T).cutoffTempered φ = c • T.cutoffTempered φ := by
  ext ψ
  simp only [smul_apply, cutoffTempered_def, complexPairing_smul, smul_eq_mul]

/-- The tempered distribution `φ T` is additive in the cutoff `φ`. -/
@[simp]
theorem cutoffTempered_add_cutoff (T : 𝓓'(Ω, ℂ)) (φ φ' : 𝓓(Ω, ℂ)) :
    T.cutoffTempered (φ + φ') = T.cutoffTempered φ + T.cutoffTempered φ' := by
  ext ψ
  simp only [add_apply, cutoffTempered_def, map_add]

/-- The tempered distribution `φ T` is complex-linear in the cutoff `φ`. -/
@[simp]
theorem cutoffTempered_smul_cutoff (T : 𝓓'(Ω, ℂ)) (c : ℂ) (φ : 𝓓(Ω, ℂ)) :
    T.cutoffTempered (c • φ) = c • T.cutoffTempered φ := by
  ext ψ
  simp only [smul_apply, cutoffTempered_def, map_smul, smul_eq_mul]

/-- Multiplying the tempered distribution `φ T` by a function `g` of temperate growth gives the
tempered distribution `θ T` of any test function `θ` equal to `g φ`. -/
theorem smulLeftCLM_cutoffTempered (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {θ : 𝓓(Ω, ℂ)} (hθ : ∀ x, θ x = g x * φ x) :
    TemperedDistribution.smulLeftCLM ℂ g (T.cutoffTempered φ) = T.cutoffTempered θ := by
  ext ψ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, cutoffTempered_def T θ,
    cutoffTempered_apply T φ fun x ↦ ?_]
  simp [hθ, hg, mul_left_comm, mul_assoc]

/-- The cut-off of the product `g T` of a distribution with a smooth real function is the
cut-off of `T` by the test function `g φ`. -/
theorem cutoffTempered_smulLeftCLM {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ))
    (φ : 𝓓(Ω, ℂ)) :
    (Distribution.smulLeftCLM hg T).cutoffTempered φ =
      T.cutoffTempered (TestFunction.smulLeftCLM hg φ) := by
  ext ψ
  rw [cutoffTempered_def, complexPairing_smulLeftCLM, cutoffTempered_def]
  congr 1
  ext x
  simp [TestFunction.smulLeftCLM_apply, mul_assoc]

/-- **Cut-offs commute with derivatives where the inner cutoff is one.** If `φ = 1` on the
support of `χ`, then the cut-off `χ ∂^m T` of an iterated derivative of `T` is `χ` times the
iterated derivative of the tempered distribution `φ T`. -/
theorem cutoffTempered_iteratedLineDerivOp (T : 𝓓'(Ω, ℂ)) {φ χ : 𝓓(Ω, ℂ)}
    (hφ : EqOn φ 1 (tsupport χ)) {k : ℕ} (m : Fin k → E) :
    (∂^{m} T).cutoffTempered χ =
      TemperedDistribution.smulLeftCLM ℂ χ (∂^{m} (T.cutoffTempered φ)) := by
  have hχ : (χ : E → ℂ).HasTemperateGrowth := χ.hasCompactSupport.hasTemperateGrowth χ.contDiff
  ext ψ
  set θ := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) χ
  set f := SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) ψ
  have hθf : ⇑(∂^{m ∘ Fin.rev} θ) = ⇑(∂^{m ∘ Fin.rev} f) :=
    TestFunction.coe_iteratedLineDerivOp_of_coe_eq (funext fun x ↦ by simp [θ, f, hχ]) _
  have hf : tsupport f ⊆ tsupport χ := by
    simpa [f, SchwartzMap.smulLeftCLM_apply hχ] using tsupport_mul_subset_left
  rw [cutoffTempered_def, complexPairing_iteratedLineDerivOp,
    TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.iteratedLineDerivOp_apply_apply,
    cutoffTempered_apply T φ (χ := ∂^{m ∘ Fin.rev} θ) fun x ↦ ?_, smul_eq_mul]
  by_cases hx : x ∈ tsupport χ
  · rw [hφ hx, Pi.one_apply, one_mul, hθf]
  · rw [hθf, image_eq_zero_of_notMem_tsupport fun h ↦ hx
      (hf (SchwartzMap.tsupport_iteratedLineDerivOp_subset _ f h)), mul_zero]

/-- **The cut-off of a differential operator.** If `φ = 1` on the support of `χ`, the cut-off by
`χ` of `P T = ∑ i ∈ t, c i g i ∂^{m i} T`, with smooth real coefficients `g i`, is the
differential operator with the compactly supported coefficients `c i g i χ` applied to the
tempered distribution `φ T`. -/
theorem cutoffTempered_sum_smul_smulLeftCLM_iteratedLineDerivOp (T : 𝓓'(Ω, ℂ)) {φ χ : 𝓓(Ω, ℂ)}
    (hφ : EqOn φ 1 (tsupport χ)) {ι : Type*} (t : Finset ι) (c : ι → ℂ) {g : ι → E → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {n : ι → ℕ} (m : ∀ i, Fin (n i) → E) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered χ =
      ∑ i ∈ t, TemperedDistribution.smulLeftCLM ℂ ⇑(c i • TestFunction.smulLeftCLM (hg i) χ)
        (∂^{m i} (T.cutoffTempered φ)) := by
  let L : 𝓓'(Ω, ℂ) →+ 𝓢'(E, ℂ) :=
    AddMonoidHom.mk' (fun S ↦ S.cutoffTempered χ) fun S S' ↦ cutoffTempered_add S S' χ
  refine (map_sum L _ t).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  set θ := TestFunction.smulLeftCLM (hg i) χ
  have hθ : (θ : E → ℂ).HasTemperateGrowth := θ.hasCompactSupport.hasTemperateGrowth θ.contDiff
  have hφθ : EqOn φ 1 (tsupport θ) :=
    hφ.mono ((TestFunction.tsupport_smulLeftCLM_subset _ _).trans inter_subset_right)
  simp only [L, AddMonoidHom.mk'_apply, cutoffTempered_smul, cutoffTempered_smulLeftCLM,
    FunLike.coe_smul, TemperedDistribution.smulLeftCLM_smul hθ, _root_.smul_apply]
  exact congrArg (c i • ·) (cutoffTempered_iteratedLineDerivOp T hφθ (m i))

end Cutoff

end Distribution
