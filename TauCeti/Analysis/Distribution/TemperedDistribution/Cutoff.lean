/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
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

## Main declarations

* `Distribution.cutoffTempered T φ`: the tempered distribution `φ T`.
* `Distribution.cutoffTempered_def`, `Distribution.cutoffTempered_apply`: its value `T (φ ψ)` on
  a Schwartz function `ψ`.
* `Distribution.eq_cutoffTempered_of_forall`: uniqueness of the extension.
* `Distribution.cutoffTempered_congr`: independence of the cutoff near the support of `T`.
* `Distribution.smulLeftCLM_iteratedLineDerivOp_cutoffTempered`: if `χ = 1` near the support of
  `ψ`, then `ψ g ∂^{w} (χ T) = ψ (g ∂^{w} T)` for every smooth real `g`, so that a differential
  operator applied to `χ T` and cut off by `ψ` is the cut-off by `ψ` of the operator applied to
  `T`; `Distribution.smulLeftCLM_cutoffTempered` is the case `ψ (χ T) = ψ T`.

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

/-- The tempered distribution `φ T` vanishes for `T = 0`. -/
@[simp]
theorem cutoffTempered_zero (φ : 𝓓(Ω, ℂ)) : (0 : 𝓓'(Ω, ℂ)).cutoffTempered φ = 0 := by
  ext ψ
  simp [cutoffTempered_def, complexPairing_apply]

/-- The tempered distribution `φ T` is additive in `T`, for finite sums. -/
theorem cutoffTempered_sum {ι : Type*} (s : Finset ι) (T : ι → 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (∑ i ∈ s, T i).cutoffTempered φ = ∑ i ∈ s, (T i).cutoffTempered φ :=
  map_sum (⟨⟨fun S ↦ S.cutoffTempered φ, cutoffTempered_zero φ⟩,
    fun S S' ↦ cutoffTempered_add S S' φ⟩ : 𝓓'(Ω, ℂ) →+ 𝓢'(E, ℂ)) T s

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

end Cutoff

/-! ### Differential operators and cutoffs -/

section LineDeriv

/-- A test function and a Schwartz function with the same values have the same iterated
directional derivatives. -/
private theorem iteratedLineDerivOp_apply_eq {φ : 𝓓(Ω, ℂ)} {h : 𝓢(E, ℂ)}
    (hφh : ∀ x, φ x = h x) {j : ℕ} (w : Fin j → E) (x : E) : (∂^{w} φ) x = (∂^{w} h) x := by
  induction j generalizing x with
  | zero => simpa using hφh x
  | succ j ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left,
      TestFunction.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have h' : (⇑(∂^{Fin.tail w} φ) : E → ℂ) = ⇑(∂^{Fin.tail w} h) := funext (ih _)
    rw [h']

/-- **Cutting off commutes with differential operators near the cutoff.** Let `χ` be a test
function equal to `1` near the support of a test function `ψ`. For a smooth real function `g`,
multiplying the derivative `∂^{w} (χ T)` of the tempered distribution `χ T` by `ψ g` gives the
cut-off `ψ (g ∂^{w} T)` of the distribution `g ∂^{w} T`. -/
theorem smulLeftCLM_iteratedLineDerivOp_cutoffTempered [FiniteDimensional ℝ E] (T : 𝓓'(Ω, ℂ))
    {χ ψ : 𝓓(Ω, ℂ)} (hχ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), χ x = 1) {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    {j : ℕ} (w : Fin j → E) :
    TemperedDistribution.smulLeftCLM ℂ (fun x ↦ ψ x * g x) (∂^{w} (T.cutoffTempered χ)) =
      (smulLeftCLM hg (∂^{w} T)).cutoffTempered ψ := by
  have hψg : (fun x ↦ ψ x * (g x : ℂ)).HasTemperateGrowth :=
    HasCompactSupport.hasTemperateGrowth ψ.hasCompactSupport.mul_right
      (ψ.contDiff.mul (Complex.ofRealCLM.contDiff.comp hg))
  refine eq_cutoffTempered_of_forall _ _ fun f χ' _ hχ' ↦ ?_
  set H := SchwartzMap.smulLeftCLM ℂ (fun x ↦ ψ x * (g x : ℂ)) (f.postcompCLM Complex.ofRealCLM)
  have hH : ⇑H = fun x ↦ (ψ x * (g x : ℂ)) • (f x : ℂ) := by
    ext x
    simp [H, SchwartzMap.smulLeftCLM_apply_apply hψg]
  have hHψ : tsupport H ⊆ tsupport ψ := by
    rw [hH]
    exact (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left)
  set θ : 𝓓(Ω, ℂ) := ∂^{w ∘ Fin.rev} (TestFunction.smulLeftCLM hg χ')
  have hθ (x : E) : θ x = χ x * (∂^{w ∘ Fin.rev} H) x := by
    rw [iteratedLineDerivOp_apply_eq (h := H) (fun y ↦ ?_)]
    · by_cases hx : x ∈ tsupport ψ
      · rw [hχ.self_of_nhdsSet x hx, one_mul]
      · rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
          image_eq_zero_of_notMem_tsupport (f := iteratedFDeriv ℝ j H)
            (fun h ↦ hx (hHψ (tsupport_iteratedFDeriv_subset _ h))),
          zero_apply, mul_zero]
    · simp [hH, hχ']
      ring
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.iteratedLineDerivOp_apply_apply, cutoffTempered_apply T χ hθ,
    complexPairing_smulLeftCLM, complexPairing_iteratedLineDerivOp, smul_eq_mul]

/-- **Cutting off twice.** If the test function `χ` is equal to `1` near the support of the test
function `ψ`, then `ψ (χ T) = ψ T`. -/
theorem smulLeftCLM_cutoffTempered [FiniteDimensional ℝ E] (T : 𝓓'(Ω, ℂ)) {χ ψ : 𝓓(Ω, ℂ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), χ x = 1) :
    TemperedDistribution.smulLeftCLM ℂ ψ (T.cutoffTempered χ) = T.cutoffTempered ψ := by
  simpa using smulLeftCLM_iteratedLineDerivOp_cutoffTempered T hχ (contDiff_const (c := (1 : ℝ)))
    Fin.elim0

end LineDeriv

end Distribution
