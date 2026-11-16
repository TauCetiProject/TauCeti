/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

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

Near the points where `φ = 1`, the tempered distribution `φ T` is `T`: if `φ = 1` on the support of
a test function `χ` and `g` is a smooth real function, then `χ g ∂^m (φ T)` is the tempered
distribution `χ (g ∂^m T)`. This identifies the action of a differential operator on `φ T` near
such points with the cut-off of its action on `T`.

## Main declarations

* `Distribution.cutoffTempered T φ`: the tempered distribution `φ T`.
* `Distribution.cutoffTempered_def`, `Distribution.cutoffTempered_apply`: its value `T (φ ψ)` on
  a Schwartz function `ψ`.
* `Distribution.eq_cutoffTempered_of_forall`: uniqueness of the extension.
* `Distribution.cutoffTempered_congr`: independence of the cutoff near the support of `T`.
* `Distribution.smulLeftCLM_cutoffTempered`: if `φ = 1` on the support of `ψ`, then
  `ψ (φ T) = ψ T`.
* `Distribution.smulLeftCLM_iteratedLineDerivOp_cutoffTempered`: where `φ = 1`, derivatives and
  products of `φ T` are those of `T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.3 (the order of a
  compactly supported distribution) and §7.1 (compactly supported distributions are tempered).
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology SchwartzMap ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

namespace Distribution

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

/-- The cut-off of a finite sum of distributions is the sum of their cut-offs. -/
@[simp]
theorem cutoffTempered_sum {ι : Type*} (s : Finset ι) (T : ι → 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (∑ i ∈ s, T i).cutoffTempered φ = ∑ i ∈ s, (T i).cutoffTempered φ :=
  map_sum (AddMonoidHom.mk' (cutoffTempered · φ) fun T S ↦ cutoffTempered_add T S φ) T s

/-- **Locality of the cut-off.** If `φ = 1` on the support of a test function `ψ`, then the
product `ψ (φ T)` is the cut-off `ψ T`. -/
theorem smulLeftCLM_cutoffTempered {T : 𝓓'(Ω, ℂ)} {φ ψ : 𝓓(Ω, ℂ)}
    (hφ : ∀ x ∈ tsupport ψ, φ x = 1) :
    TemperedDistribution.smulLeftCLM ℂ (ψ : E → ℂ) (T.cutoffTempered φ) = T.cutoffTempered ψ := by
  have hψ : (ψ : E → ℂ).HasTemperateGrowth := ψ.hasCompactSupport.hasTemperateGrowth ψ.contDiff
  ext f
  rw [TemperedDistribution.smulLeftCLM_apply_apply, cutoffTempered_def]
  refine cutoffTempered_apply T φ fun x ↦ ?_
  simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
    SchwartzMap.smulLeftCLM_apply_apply hψ, smul_eq_mul]
  by_cases hx : x ∈ tsupport ψ
  · rw [hφ x hx, one_mul]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end Cutoff

/-! ### Derivatives where the cutoff is `1` -/

section LineDeriv

open LineDeriv

/-- On Schwartz functions supported where `φ = 1`, the derivatives of `φ T` are those of `T`. -/
private theorem iteratedLineDerivOp_cutoffTempered_apply {T : 𝓓'(Ω, ℂ)} {φ : 𝓓(Ω, ℂ)}
    {W : Set E} (hφ : ∀ x ∈ W, φ x = 1) {k : ℕ} (m : Fin k → E) {f : 𝓢(E, ℂ)}
    (hf : tsupport f ⊆ W) {χ : 𝓓(Ω, ℂ)} (hχ : ∀ x, χ x = f x) :
    ∂^{m} (T.cutoffTempered φ) f = (∂^{m} T).complexPairing χ := by
  induction k generalizing f χ with
  | zero =>
    refine cutoffTempered_apply T φ fun x ↦ ?_
    by_cases hx : x ∈ W
    · rw [hχ, hφ x hx, one_mul]
    · rw [hχ, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hf h), mul_zero]
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left,
      TemperedDistribution.lineDerivOp_apply_apply, map_neg, complexPairing_lineDerivOp,
      ih _ ((SchwartzMap.tsupport_lineDerivOp_subset _ f).trans hf) fun x ↦ ?_]
    rw [TestFunction.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      show (χ : E → ℂ) = f from funext hχ]

/-- **Locality of the cut-off.** If `φ = 1` on the support of a test function `χ`, then for a
smooth real function `g` and an iterated derivative `∂^m`, the tempered distribution
`χ g ∂^m (φ T)` is the cut-off `χ (g ∂^m T)`. Near the points where `φ = 1`, a differential
operator acts on `φ T` as it acts on `T`. -/
theorem smulLeftCLM_iteratedLineDerivOp_cutoffTempered {T : 𝓓'(Ω, ℂ)} {φ χ : 𝓓(Ω, ℂ)}
    (hφ : ∀ x ∈ tsupport χ, φ x = 1) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) {k : ℕ}
    (m : Fin k → E) :
    TemperedDistribution.smulLeftCLM ℂ (fun x ↦ χ x * g x) (∂^{m} (T.cutoffTempered φ)) =
      (smulLeftCLM hg (∂^{m} T)).cutoffTempered χ := by
  have hht : (fun x ↦ χ x * (g x : ℂ)).HasTemperateGrowth :=
    χ.hasTemperateGrowth_mul (ofRealCLM.contDiff.comp hg)
  ext f
  rw [TemperedDistribution.smulLeftCLM_apply_apply, cutoffTempered_def,
    complexPairing_smulLeftCLM]
  refine iteratedLineDerivOp_cutoffTempered_apply hφ m ?_ fun x ↦ ?_
  · rw [show ⇑(SchwartzMap.smulLeftCLM ℂ (fun x ↦ χ x * (g x : ℂ)) f) =
        fun x ↦ χ x * g x * f x from
      funext fun x ↦ SchwartzMap.smulLeftCLM_apply_apply hht f x]
    exact tsupport_mul_subset_left.trans tsupport_mul_subset_left
  · rw [SchwartzMap.smulLeftCLM_apply_apply hht, TestFunction.smulLeftCLM_apply,
      bilinLeftCLM_apply]
    simp only [ContinuousLinearMap.mul_apply', real_smul, smul_eq_mul]
    ring

end LineDeriv

end Distribution
