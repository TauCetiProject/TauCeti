/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
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

Cutting off commutes with the operations of differential operators up to derivatives of the
cutoff: multiplication by a smooth function moves into the cutoff, derivatives obey the Leibniz
rule `∂_v (φ T) = (∂_v φ) T + φ ∂_v T`, and where a second cutoff `χ` equals one, the derivatives
of `χ T` are those of `T`. These identities let a differential operator acting on a distribution
on `Ω` be replaced by one acting on the tempered distribution `χ T`.

## Main declarations

* `Distribution.cutoffTempered T φ`: the tempered distribution `φ T`.
* `Distribution.cutoffTempered_def`, `Distribution.cutoffTempered_apply`: its value `T (φ ψ)` on
  a Schwartz function `ψ`.
* `Distribution.eq_cutoffTempered_of_forall`: uniqueness of the extension.
* `Distribution.cutoffTempered_apply_congr`: `φ T` only sees the values of a Schwartz function on
  `tsupport φ`.
* `Distribution.cutoffTempered_congr`: independence of the cutoff near the support of `T`.
* `Distribution.cutoffTempered_zero`, `Distribution.cutoffTempered_add`,
  `Distribution.cutoffTempered_smul`, `Distribution.cutoffTempered_sum`: `φ T` is linear in `T`.
* `Distribution.cutoffTempered_smulLeftCLM`: `φ (g T) = (g φ) T` for a smooth real `g`.
* `Distribution.lineDerivOp_cutoffTempered`: the Leibniz rule for `φ T`.
* `Distribution.smulLeftCLM_cutoffTempered`,
  `Distribution.smulLeftCLM_iteratedLineDerivOp_cutoffTempered`: if `χ = 1` on the support of
  `φ`, then `φ (χ T) = φ T` and `φ ∂^m (χ T) = φ ∂^m T`.
* `Distribution.cutoffTempered_toDistribution`: for a tempered distribution `u`, restricted to `Ω`
  by `TemperedDistribution.toDistribution`, the tempered distribution `φ u` is the product of `u`
  with `φ`.
* `Distribution.isVanishingOn_sub_toDistribution_cutoffTempered`: `χ T` agrees with `T` where
  `χ = 1`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.3 (the order of a
  compactly supported distribution) and §7.1 (compactly supported distributions are tempered).
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology SchwartzMap ContDiff

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

/-- **Locality of the cut-off.** The tempered distribution `φ T` only depends on the values of a
Schwartz function on `tsupport φ`. -/
theorem cutoffTempered_apply_congr (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) {ψ ψ' : 𝓢(E, ℂ)}
    (h : EqOn ψ ψ' (tsupport φ)) : T.cutoffTempered φ ψ = T.cutoffTempered φ ψ' := by
  rw [cutoffTempered_def, cutoffTempered_def]
  congr 1
  ext x
  simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']
  by_cases hx : x ∈ tsupport φ
  · rw [h hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

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
theorem cutoffTempered_congr (T : 𝓓'(Ω, ℂ)) {φ φ' : 𝓓(Ω, ℂ)}
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

/-- The cutoff of the zero distribution is zero. -/
@[simp]
theorem cutoffTempered_zero (φ : 𝓓(Ω, ℂ)) : (0 : 𝓓'(Ω, ℂ)).cutoffTempered φ = 0 := by
  ext ψ
  simp [cutoffTempered_def, complexPairing_apply]

/-- The tempered distribution `φ T` is additive in `T` over finite sums. -/
@[simp]
theorem cutoffTempered_sum {ι : Type*} (s : Finset ι) (T : ι → 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (∑ i ∈ s, T i).cutoffTempered φ = ∑ i ∈ s, (T i).cutoffTempered φ :=
  map_sum (AddMonoidHom.mk' (fun S : 𝓓'(Ω, ℂ) ↦ S.cutoffTempered φ)
    fun S S' ↦ cutoffTempered_add S S' φ) T s

/-- The tempered distribution `φ T` is additive in the cutoff `φ`. -/
@[simp]
theorem cutoffTempered_add_cutoff (T : 𝓓'(Ω, ℂ)) (φ φ' : 𝓓(Ω, ℂ)) :
    T.cutoffTempered (φ + φ') = T.cutoffTempered φ + T.cutoffTempered φ' := by
  ext ψ
  simp only [add_apply, cutoffTempered_def, map_add]

/-- The tempered distribution `φ T` is additive in the cutoff `φ`, over finite sums. -/
@[simp]
theorem cutoffTempered_sum_cutoff {ι : Type*} (T : 𝓓'(Ω, ℂ)) (s : Finset ι) (φ : ι → 𝓓(Ω, ℂ)) :
    T.cutoffTempered (∑ i ∈ s, φ i) = ∑ i ∈ s, T.cutoffTempered (φ i) :=
  map_sum (AddMonoidHom.mk' T.cutoffTempered T.cutoffTempered_add_cutoff) φ s

/-- The tempered distribution `φ T` is complex-linear in the cutoff `φ`. -/
@[simp]
theorem cutoffTempered_smul_cutoff (T : 𝓓'(Ω, ℂ)) (c : ℂ) (φ : 𝓓(Ω, ℂ)) :
    T.cutoffTempered (c • φ) = c • T.cutoffTempered φ := by
  ext ψ
  simp only [smul_apply, cutoffTempered_def, map_smul, smul_eq_mul]

end Cutoff

section Operations

open LineDeriv
open scoped LineDeriv

/-- Multiplying `T` by a smooth real function `g` before cutting off by `φ` is cutting `T` off by
the test function `g φ`. -/
@[simp]
theorem cutoffTempered_smulLeftCLM {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ))
    (φ : 𝓓(Ω, ℂ)) :
    (smulLeftCLM hg T).cutoffTempered φ = T.cutoffTempered (TestFunction.smulLeftCLM hg φ) := by
  ext ψ
  rw [cutoffTempered_def, complexPairing_smulLeftCLM, cutoffTempered_def]
  congr 1
  ext x
  simp [mul_assoc]

/-- **The Leibniz rule for `φ T`**: `∂_v (φ T) = (∂_v φ) T + φ ∂_v T`. -/
theorem lineDerivOp_cutoffTempered (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (v : E) :
    ∂_{v} (T.cutoffTempered φ) = T.cutoffTempered (∂_{v} φ) + (∂_{v} T).cutoffTempered φ := by
  ext ψ
  -- The Leibniz rule for the test function `φ ψ`.
  have hprod : ∂_{v} (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) φ) =
      bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) (∂_{v} φ) +
        bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ((∂_{v} ψ).smooth ⊤) φ := by
    ext x
    have hφ : DifferentiableAt ℝ φ x := (φ.contDiff.differentiable (by simp)).differentiableAt
    simp only [TestFunction.lineDerivOp_apply_eq_fderiv, add_apply, bilinLeftCLM_apply,
      ContinuousLinearMap.mul_apply', SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [← Pi.mul_def, fderiv_mul hφ ψ.differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hneg : bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ((-∂_{v} ψ).smooth ⊤) φ =
      -bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ((∂_{v} ψ).smooth ⊤) φ := by
    ext x
    simp
  rw [TemperedDistribution.lineDerivOp_apply_apply, add_apply, cutoffTempered_def,
    cutoffTempered_def, cutoffTempered_def, complexPairing_lineDerivOp, hprod, hneg, map_add,
    map_neg]
  ring

/-- **Cutting off a cut-off distribution.** If `χ = 1` on the support of `φ`, then
`φ (χ T) = φ T`. -/
theorem smulLeftCLM_cutoffTempered (T : 𝓓'(Ω, ℂ)) {χ φ : 𝓓(Ω, ℂ)}
    (h : ∀ x ∈ tsupport φ, χ x = 1) :
    TemperedDistribution.smulLeftCLM ℂ (φ : E → ℂ) (T.cutoffTempered χ) = T.cutoffTempered φ := by
  ext ψ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, cutoffTempered_def, cutoffTempered_def]
  congr 1
  ext x
  simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
    SchwartzMap.smulLeftCLM_apply (φ.hasCompactSupport.hasTemperateGrowth φ.contDiff),
    smul_eq_mul]
  by_cases hx : x ∈ tsupport φ
  · rw [h x hx]
    ring
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **Derivatives of a cut-off distribution where the cutoff is one.** If `χ = 1` on the support
of `φ`, then cutting the derivative `∂^m (χ T)` off by `φ` gives `φ ∂^m T`. -/
theorem smulLeftCLM_iteratedLineDerivOp_cutoffTempered (T : 𝓓'(Ω, ℂ)) {χ φ : 𝓓(Ω, ℂ)}
    (h : ∀ x ∈ tsupport φ, χ x = 1) {k : ℕ} (m : Fin k → E) :
    TemperedDistribution.smulLeftCLM ℂ (φ : E → ℂ) (∂^{m} (T.cutoffTempered χ)) =
      (∂^{m} T).cutoffTempered φ := by
  induction k generalizing φ with
  | zero => exact smulLeftCLM_cutoffTempered T h
  | succ k ih =>
    -- `φ ∂_v R = ∂_v (φ R) - (∂_v φ) R`, and both cutoffs `φ` and `∂_v φ` are supported where
    -- `χ = 1`.
    set v := m 0
    set R := ∂^{Fin.tail m} (T.cutoffTempered χ)
    have hfd : (fun x ↦ fderiv ℝ φ x v) = ⇑(∂_{v} φ : 𝓓(Ω, ℂ)) :=
      (TestFunction.coe_lineDerivOp_eq_fderiv φ v).symm
    have hL : TemperedDistribution.smulLeftCLM ℂ (φ : E → ℂ) (∂_{v} R) =
        ∂_{v} (TemperedDistribution.smulLeftCLM ℂ (φ : E → ℂ) R) -
          TemperedDistribution.smulLeftCLM ℂ ⇑(∂_{v} φ : 𝓓(Ω, ℂ)) R := by
      rw [TemperedDistribution.lineDerivOp_smulLeftCLM
        (φ.hasCompactSupport.hasTemperateGrowth φ.contDiff), hfd]
      abel
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, hL, ih h,
      ih fun x hx ↦ h x (TestFunction.tsupport_lineDerivOp_subset φ v hx),
      lineDerivOp_cutoffTempered]
    abel

end Operations

/-! ### Restrictions of tempered distributions -/

section ToDistribution

/-- The complex-linear extension of the restriction of a tempered distribution `u` to `Ω` is `u`
itself on complex test functions. -/
@[simp]
theorem complexPairing_toDistribution (u : 𝓢'(E, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (TemperedDistribution.toDistribution Ω u).complexPairing φ = u (toSchwartzMapCLM ℝ φ) := by
  rw [complexPairing_apply, TemperedDistribution.toDistribution_apply,
    TemperedDistribution.toDistribution_apply, ← smul_eq_mul,
    ← map_smul, ← map_add]
  congr 1
  ext x
  simpa [postcompCLM_apply, mul_comm] using re_add_im (φ x)

/-- **Cutting off a tempered distribution.** For a tempered distribution `u` restricted to `Ω`
and a test function `φ` on `Ω`, the tempered distribution `φ u` of `Distribution.cutoffTempered`
is the product of `u` with `φ`. -/
@[simp]
theorem cutoffTempered_toDistribution (u : 𝓢'(E, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (TemperedDistribution.toDistribution Ω u).cutoffTempered φ =
      TemperedDistribution.smulLeftCLM ℂ (φ : E → ℂ) u := by
  ext ψ
  rw [cutoffTempered_def, complexPairing_toDistribution,
    TemperedDistribution.smulLeftCLM_apply_apply]
  congr 1
  ext x
  simp [SchwartzMap.smulLeftCLM_apply_apply (φ.hasCompactSupport.hasTemperateGrowth φ.contDiff)]

/-- **A distribution agrees with its cut-off where the cutoff is one.** If `χ = 1` on a set `V`,
then `T` and the restriction to `Ω` of the tempered distribution `χ T` agree on the test functions
supported in `V`. -/
theorem isVanishingOn_sub_toDistribution_cutoffTempered (T : 𝓓'(Ω, ℂ)) {χ : 𝓓(Ω, ℂ)} {V : Set E}
    (hχ : ∀ x ∈ V, χ x = 1) :
    IsVanishingOn ⇑(T - TemperedDistribution.toDistribution Ω (T.cutoffTempered χ)) V := by
  intro φ hφ
  rw [sub_apply, TemperedDistribution.toDistribution_apply, sub_eq_zero,
    ← complexPairing_postcompCLM_ofRealCLM T φ, cutoffTempered_apply T χ fun x ↦ ?_]
  by_cases hx : x ∈ tsupport φ
  · simp [hχ x (hφ hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end ToDistribution

end Distribution
