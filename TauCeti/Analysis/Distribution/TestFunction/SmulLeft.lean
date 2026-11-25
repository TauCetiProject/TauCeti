/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Distribution.TestFunction.Basic

/-!
# Smooth multiplication of test forms and the Leibniz rule for currents

For an open set `Ω` of a real normed space `E`, a smooth function `f : E → ℝ` acts on test
functions on `Ω` by pointwise multiplication, and a smooth covector field `α : E → E →L[ℝ] ℝ`
acts on test `k`-forms by the wedge product `ω ↦ α ∧ ω`, with values in test `(k + 1)`-forms.
Both are continuous linear maps for the LF topology, built from Mathlib's
`TestFunction.bilinLeftCLM`. They do not enlarge supports and commute with extension of test
functions to a larger open set. In a finite-dimensional space, multiplication by a function that
is `C^n` on `Ω` only, with no condition off `Ω`, is also a continuous linear map: on the tests
supported in a compact `K ⊆ Ω` it is multiplication by a globally `C^n` function equal to it near
`K`.

The exterior derivative satisfies the Leibniz rule `d (f ω) = df ∧ ω + f dω` on test forms.
Transposing, for a current `T` (a continuous linear functional on test `(k + 1)`-forms), the
current `fT = T ∘ (f ·)` has boundary
`∂(fT) = f ∂T - T ⌞ df`, where `∂T = T ∘ d` and `(T ⌞ df) ω = T (df ∧ ω)`.

The wedge `α ∧ ω` with a one-form is the alternatization of `v ↦ α v • ω`, the operation through
which Mathlib's `extDeriv` is defined, so that it lands in degree `k + 1` like the exterior
derivative. `ContinuousAlternatingMap.alternatizeUncurryFin_smulRight_apply` identifies it with
the paired wedge `ContinuousAlternatingMap.pairedWedge` of the one-form `α` with `ω`.

## Main declarations

* `TestFunction.smulLeftCLM`: multiplication `φ ↦ f φ` of test functions by a smooth function.
* `TestFunction.smulLeftCLMOfContDiffOn`: multiplication `φ ↦ g φ` of test functions on `Ω` by a
  function `C^n` on `Ω` only, which depends only on the values of the multiplier on `Ω`
  (`TestFunction.smulLeftCLMOfContDiffOn_congr`).
* `TestFunction.norm_iteratedFDeriv_smulLeftCLM_le`: the Leibniz bound for `a Ψ` when the
  derivatives of `a` are only controlled on a set containing the support of `Ψ`.
* `TestFunction.exists_mul_eq_of_forall_ne_zero`: a test function divided by a smooth function
  that does not vanish near its support is a test function, with derivative bounds.
* `TestFunction.hasTemperateGrowth_mul`: the product `χ f` of a complex test function with a
  smooth function has temperate growth.
* `TestFunction.exists_coe_eq_clm_apply_of_tsupport_inter_subset`: the pairing `x ↦ A x (φ x)`
  of a test function on `Ω'` with a smooth operator field is a test function on any open `Ω`
  containing `tsupport A ∩ Ω'`.
* `TestFunction.oneFormWedgeCLM`: the wedge `ω ↦ α ∧ ω` of test forms with a smooth one-form.
* `TestFunction.norm_oneFormWedgeCLM_apply_le`: the pointwise bound
  `‖(α ∧ ω) x‖ ≤ (k + 1) ‖α x‖ ‖ω x‖`, with its extended-norm form
  `TestFunction.enorm_oneFormWedgeCLM_apply_le`.
* `TestFunction.extDerivCLM_smulLeftCLM`: the Leibniz rule `d (f ω) = df ∧ ω + f dω`.
* `ContinuousLinearMap.comp_smulLeftCLM_comp_extDerivCLM`: the boundary of a smooth multiple of
  a current, `∂(fT) = f ∂T - T ⌞ df`.
* `ContDiffMapSupportedIn.seminorm_bilinLeftCLM_mul_le`: the Leibniz bound
  `N_i(χ g) ≤ 2 ^ k N_k(χ) M` for the product of a complex smooth function `χ` supported in a
  compact set with a smooth function `g` whose derivatives of order at most `k` are bounded by `M`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6.
-/

public section

namespace TestFunction

open TopologicalSpace ContinuousAlternatingMap
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω Ω' : Opens E} {n : ℕ∞} {k : ℕ}

section SmulLeft

variable {f g : E → ℝ}

/-- Multiplication of test functions on `Ω` by a `C^n` real function `f`, as a continuous linear
map `φ ↦ f φ`. -/
noncomputable def smulLeftCLM (hf : ContDiff ℝ n f) : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F) :=
  bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ).flip hf

@[simp]
theorem smulLeftCLM_apply (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω, F)) (x : E) :
    smulLeftCLM hf φ x = f x • φ x := by
  simp [smulLeftCLM]

/-- A smooth multiple of a test function, as a function, is the pointwise product. -/
theorem coe_smulLeftCLM (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω, F)) :
    (smulLeftCLM hf φ : E → F) = f • ⇑φ :=
  funext (smulLeftCLM_apply hf φ)

/-- Multiplying by a smooth function does not enlarge the support of a test function. -/
theorem tsupport_smulLeftCLM_subset (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω, F)) :
    tsupport (smulLeftCLM hf φ : E → F) ⊆ tsupport f ∩ tsupport φ :=
  tsupport_subset_inter_of_apply_eq_smul (smulLeftCLM_apply hf φ)

/-- Multiplying by a smooth function does not enlarge the support of a test function: the support
of `f φ` lies in that of `φ`. -/
theorem tsupport_smulLeftCLM_subset_right (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω, F)) :
    tsupport (smulLeftCLM hf φ : E → F) ⊆ tsupport φ :=
  (tsupport_smulLeftCLM_subset hf φ).trans Set.inter_subset_right

/-- Multiplication by a smooth function is additive in the multiplier. -/
theorem smulLeftCLM_add (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    (smulLeftCLM (hf.add hg) : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F)) =
      smulLeftCLM hf + smulLeftCLM hg := by
  ext φ x
  simp [add_smul]

/-- Multiplication by a smooth function is homogeneous in the multiplier. -/
theorem smulLeftCLM_smul (hf : ContDiff ℝ n f) (c : ℝ) :
    (smulLeftCLM (hf.const_smul c) : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F)) = c • smulLeftCLM hf := by
  ext φ x
  simp [smul_smul]

/-- Multiplying by two smooth functions in turn is multiplying by their product. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (φ : 𝓓^{n}(Ω, F)) :
    smulLeftCLM hf (smulLeftCLM hg φ) = smulLeftCLM (hf.mul hg) φ := by
  ext x
  simp [smul_smul]

/-- Multiplication by a smooth function commutes with extending test functions from `Ω'` to
`Ω`. -/
@[simp]
theorem smulLeftCLM_monoCLM (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω', F)) :
    smulLeftCLM hf (monoCLM ℝ φ : 𝓓^{n}(Ω, F)) = monoCLM ℝ (smulLeftCLM hf φ) := by
  ext x
  by_cases h : Ω' ≤ Ω <;> simp [monoCLM_apply, h]

open scoped ContDiff in
/-- The product of a complex test function with a smooth function has temperate growth: it is
smooth with compact support. Such products are the multipliers that localize a differential
operator near the support of the test function. -/
theorem hasTemperateGrowth_mul (χ : 𝓓(Ω, ℂ)) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    (fun x ↦ χ x * f x).HasTemperateGrowth :=
  χ.hasCompactSupport.mul_right.hasTemperateGrowth (χ.contDiff.mul hf)

end SmulLeft

section Bounds

open Set
open scoped ContDiff

/-- **Dividing a test function by a smooth function.** Let `φ` be a test function supported in
`K`, and let `p` be smooth and nonvanishing on an open set `W ⊇ K`. Then `φ / p` is a test function
`Ψ` supported in `K` with `p Ψ = φ`. If the derivatives of order at most `n` of `p⁻¹` are bounded
by `Q ≥ 0` on `K` and those of `φ` by `B`, then those of `Ψ` are bounded by `2 ^ n Q B`. -/
theorem exists_mul_eq_of_forall_ne_zero (φ : 𝓓(Ω, ℂ)) {K W : Set E} (hW : IsOpen W)
    (hKW : K ⊆ W) (hφK : tsupport φ ⊆ K) {p : E → ℂ} (hp : ContDiffOn ℝ ∞ p W)
    (hpW : ∀ y ∈ W, p y ≠ 0) {n : ℕ} {Q B : ℝ} (hQ0 : 0 ≤ Q)
    (hQ : ∀ i ≤ n, ∀ y ∈ K, ‖iteratedFDeriv ℝ i (fun z ↦ (p z)⁻¹) y‖ ≤ Q)
    (hB : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) :
    ∃ Ψ : 𝓓(Ω, ℂ), tsupport Ψ ⊆ K ∧ (∀ y, p y * Ψ y = φ y) ∧
      ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i Ψ y‖ ≤ 2 ^ n * Q * B := by
  have hinv : ContDiffOn ℝ ∞ (fun y ↦ (p y)⁻¹) W := hp.inv hpW
  have hcd : ContDiff ℝ ∞ (fun y ↦ (p y)⁻¹ * φ y) :=
    (ContinuousLinearMap.mul ℝ ℂ).contDiff_of_tsupport_subset_right hinv φ.contDiff.contDiffOn
      hW (hφK.trans hKW)
  have hts : tsupport (fun y ↦ (p y)⁻¹ * φ y) ⊆ tsupport φ := tsupport_mul_subset_right
  refine ⟨⟨fun y ↦ (p y)⁻¹ * φ y, hcd, φ.hasCompactSupport.mono' (subset_tsupport _ |>.trans hts),
    hts.trans φ.tsupport_subset⟩, hts.trans hφK, fun y ↦ ?_, fun i hi y ↦ ?_⟩
  · by_cases hy : y ∈ W
    · exact mul_inv_cancel_left₀ (hpW y hy) (φ y)
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (hKW (hφK h))]
  · refine (TauCeti.norm_iteratedFDeriv_mul_le_of_tsupport_subset hW hKW hinv φ.contDiff hφK
      (by exact_mod_cast le_top) hQ0
      (fun l hl z hz ↦ hQ l (hl.trans hi) z hz) (fun l hl z ↦ hB l (hl.trans hi) z) y).trans ?_
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) y)
    gcongr
    exact one_le_two

/-- The derivatives of order at most `n` of a smooth multiple `a Ψ` of a test function supported in
`K` are bounded by `2 ^ n G B`, if those of `a` are bounded by `G ≥ 0` on `K` and those of `Ψ` by
`B`. -/
theorem norm_iteratedFDeriv_smulLeftCLM_le {a : E → ℝ} (ha : ContDiff ℝ ∞ a)
    (Ψ : 𝓓(Ω, ℂ)) {K : Set E} (hΨK : tsupport Ψ ⊆ K) {n : ℕ} {G B : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ l ≤ n, ∀ y ∈ K, ‖iteratedFDeriv ℝ l (fun z ↦ (a z : ℂ)) y‖ ≤ G)
    (hB : ∀ l ≤ n, ∀ y, ‖iteratedFDeriv ℝ l Ψ y‖ ≤ B) :
    ∀ l ≤ n, ∀ y, ‖iteratedFDeriv ℝ l (smulLeftCLM ha Ψ) y‖ ≤ 2 ^ n * G * B := by
  intro l hl y
  have hcoe : ⇑(smulLeftCLM ha Ψ) = fun z ↦ (a z : ℂ) * Ψ z := by
    ext z
    simp [Complex.real_smul]
  rw [hcoe]
  refine (TauCeti.norm_iteratedFDeriv_mul_le_of_tsupport_subset isOpen_univ (subset_univ K)
    (Complex.ofRealCLM.contDiff.comp ha).contDiffOn Ψ.contDiff hΨK (by exact_mod_cast le_top) hG0
    (fun l' hl' z hz ↦ hG l' (hl'.trans hl) z hz) (fun l' hl' z ↦ hB l' (hl'.trans hl) z)
    y).trans ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) y)
  gcongr
  exact one_le_two

end Bounds

section SmulLeftOfContDiffOn

open Set

variable [FiniteDimensional ℝ E] {f g : E → ℝ}

/-- A globally `C^n` function that agrees with `g` near the compact set `K ⊆ Ω`. -/
private noncomputable def extendOn (hg : ContDiffOn ℝ n g Ω) {K : Compacts E}
    (hK : (K : Set E) ⊆ Ω) : E → ℝ :=
  (hg.exists_contDiff_eventuallyEq_on_isCompact K.isCompact Ω.isOpen hK).choose

private theorem contDiff_extendOn (hg : ContDiffOn ℝ n g Ω) {K : Compacts E}
    (hK : (K : Set E) ⊆ Ω) : ContDiff ℝ n (extendOn hg hK) :=
  (hg.exists_contDiff_eventuallyEq_on_isCompact K.isCompact Ω.isOpen hK).choose_spec.1

private theorem extendOn_eventuallyEq (hg : ContDiffOn ℝ n g Ω) {K : Compacts E}
    (hK : (K : Set E) ⊆ Ω) {x : E} (hx : x ∈ (K : Set E)) : extendOn hg hK =ᶠ[nhds x] g := by
  obtain ⟨-, -, -, -, h⟩ :=
    (hg.exists_contDiff_eventuallyEq_on_isCompact K.isCompact Ω.isOpen hK).choose_spec
  exact h x hx

/-- **Multiplication by a function `C^n` on `Ω`**, `φ ↦ g φ`, as a continuous linear map on the
`C^n` test functions on `Ω`. Nothing is required of `g` off `Ω`; when `g` is `C^n` on all of `E`
this is `TestFunction.smulLeftCLM` (`TestFunction.smulLeftCLMOfContDiffOn_eq_smulLeftCLM`). On the
tests supported in a compact `K ⊆ Ω` it is multiplication by a globally `C^n` function that agrees
with `g` near `K`. -/
noncomputable def smulLeftCLMOfContDiffOn (hg : ContDiffOn ℝ n g Ω) :
    𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F) :=
  TestFunction.limitCLM ℝ (fun φ ↦ (exists_coe_eq_smul_of_contDiffOn hg φ).choose)
    (fun K hK ↦ smulLeftCLM (contDiff_extendOn hg hK) ∘L ofSupportedInCLM ℝ hK)
    (fun K hK φ ↦ by
      ext x
      rw [ContinuousLinearMap.comp_apply, smulLeftCLM_apply,
        (exists_coe_eq_smul_of_contDiffOn hg _).choose_spec, coe_ofSupportedInCLM]
      by_cases hx : x ∈ (K : Set E)
      · rw [(extendOn_eventuallyEq hg hK hx).eq_of_nhds, coe_ofSupportedIn]
      · simp [φ.zero_on_compl hx])

@[simp]
theorem smulLeftCLMOfContDiffOn_apply (hg : ContDiffOn ℝ n g Ω) (φ : 𝓓^{n}(Ω, F)) (x : E) :
    smulLeftCLMOfContDiffOn hg φ x = g x • φ x := by
  rw [smulLeftCLMOfContDiffOn, limitCLM_apply, (exists_coe_eq_smul_of_contDiffOn hg φ).choose_spec]

/-- A multiple of a test function by a function `C^n` on `Ω`, as a function, is the pointwise
product. -/
theorem coe_smulLeftCLMOfContDiffOn (hg : ContDiffOn ℝ n g Ω) (φ : 𝓓^{n}(Ω, F)) :
    (smulLeftCLMOfContDiffOn hg φ : E → F) = g • ⇑φ :=
  funext (smulLeftCLMOfContDiffOn_apply hg φ)

/-- Multiplying by a function `C^n` on `Ω` does not enlarge the support of a test function. -/
theorem tsupport_smulLeftCLMOfContDiffOn_subset (hg : ContDiffOn ℝ n g Ω) (φ : 𝓓^{n}(Ω, F)) :
    tsupport (smulLeftCLMOfContDiffOn hg φ : E → F) ⊆ tsupport g ∩ tsupport φ :=
  tsupport_subset_inter_of_apply_eq_smul (smulLeftCLMOfContDiffOn_apply hg φ)

/-- For a function `C^n` on all of `E`, multiplication by it is `TestFunction.smulLeftCLM`. -/
theorem smulLeftCLMOfContDiffOn_eq_smulLeftCLM (hg : ContDiff ℝ n g) :
    (smulLeftCLMOfContDiffOn hg.contDiffOn : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F)) = smulLeftCLM hg := by
  ext φ x
  simp

/-- Multiplication by a function `C^n` on `Ω` depends only on the values of the multiplier on
`Ω`. -/
theorem smulLeftCLMOfContDiffOn_congr (hf : ContDiffOn ℝ n f Ω) (hg : ContDiffOn ℝ n g Ω)
    (hfg : EqOn f g Ω) :
    (smulLeftCLMOfContDiffOn hf : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F)) = smulLeftCLMOfContDiffOn hg := by
  ext φ x
  by_cases hx : x ∈ (Ω : Set E)
  · simp [hfg hx]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)]

/-- Multiplication by a function `C^n` on `Ω` is additive in the multiplier. -/
theorem smulLeftCLMOfContDiffOn_add (hf : ContDiffOn ℝ n f Ω) (hg : ContDiffOn ℝ n g Ω) :
    (smulLeftCLMOfContDiffOn (hf.add hg) : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F)) =
      smulLeftCLMOfContDiffOn hf + smulLeftCLMOfContDiffOn hg := by
  ext φ x
  simp [add_smul]

/-- Multiplication by a function `C^n` on `Ω` is homogeneous in the multiplier. -/
theorem smulLeftCLMOfContDiffOn_smul (hf : ContDiffOn ℝ n f Ω) (c : ℝ) :
    (smulLeftCLMOfContDiffOn (hf.const_smul c) : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F)) =
      c • smulLeftCLMOfContDiffOn hf := by
  ext φ x
  simp [smul_smul]

/-- Multiplying by two functions `C^n` on `Ω` in turn is multiplying by their product. -/
@[simp]
theorem smulLeftCLMOfContDiffOn_smulLeftCLMOfContDiffOn (hf : ContDiffOn ℝ n f Ω)
    (hg : ContDiffOn ℝ n g Ω) (φ : 𝓓^{n}(Ω, F)) :
    smulLeftCLMOfContDiffOn hf (smulLeftCLMOfContDiffOn hg φ) =
      smulLeftCLMOfContDiffOn (hf.mul hg) φ := by
  ext x
  simp [smul_smul]

/-- Multiplication by a function `C^n` on `Ω` commutes with extending test functions from
`Ω' ≤ Ω` to `Ω`. -/
@[simp]
theorem smulLeftCLMOfContDiffOn_monoCLM (hg : ContDiffOn ℝ n g Ω) (h : Ω' ≤ Ω)
    (φ : 𝓓^{n}(Ω', F)) :
    smulLeftCLMOfContDiffOn hg (monoCLM ℝ φ : 𝓓^{n}(Ω, F)) =
      monoCLM ℝ (smulLeftCLMOfContDiffOn (hg.mono h) φ) := by
  ext x
  simp [monoCLM_apply, h]

end SmulLeftOfContDiffOn

section ClmApply

open Function Set
open scoped ContDiff

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Pairing a test function with a `C^n` operator field from a smaller open set.** If
`A : E → F →L[ℝ] G` is `C^n` with `tsupport A ∩ Ω' ⊆ Ω` and `φ` is a `C^n` test function on `Ω'`,
then `x ↦ A x (φ x)` is a `C^n` test function on `Ω`, whether or not `Ω' ≤ Ω`. This covers a
scalar multiple `f φ` (take `A x = f x • id`) and the pairing `Df φ` with a derivative. -/
theorem exists_coe_eq_clm_apply_of_tsupport_inter_subset {A : E → F →L[ℝ] G}
    (hA : ContDiff ℝ n A) (h : tsupport A ∩ Ω' ⊆ Ω) (φ : 𝓓^{n}(Ω', F)) :
    ∃ ψ : 𝓓^{n}(Ω, G), ⇑ψ = fun x => A x (φ x) := by
  have hsupp : support (fun x => A x (φ x)) ⊆ support A ∩ support φ :=
    fun x hx => ⟨fun h0 => hx (by simp [h0]), fun h0 => hx (by simp [h0])⟩
  exact ⟨⟨fun x => A x (φ x), hA.clm_apply φ.contDiff,
    φ.hasCompactSupport.mono fun x hx => (hsupp hx).2,
    (closure_mono hsupp |>.trans (closure_inter_subset_inter_closure _ _)).trans
      ((inter_subset_inter_right _ φ.tsupport_subset).trans h)⟩, rfl⟩

end ClmApply

section OneFormWedge

variable {α : E → E →L[ℝ] ℝ}

/-- The wedge `α ∧ ω` of a test `k`-form `ω` on `Ω` with a `C^n` one-form `α`, as a continuous
linear map into test `(k + 1)`-forms. Pointwise, `α ∧ ω` is the alternatization of
`v ↦ α v • ω`, see `TestFunction.oneFormWedgeCLM_apply`. -/
noncomputable def oneFormWedgeCLM (hα : ContDiff ℝ n α) :
    𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓^{n}(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) :=
  bilinLeftCLM
    ((ContinuousLinearMap.compL ℝ (E →L[ℝ] ℝ) _ _ (alternatizeUncurryFinCLM ℝ E F)) ∘L
      (ContinuousLinearMap.smulRightL ℝ ℝ ℝ E (E [⋀^Fin k]→L[ℝ] F)).flip) hα

@[simp]
theorem oneFormWedgeCLM_apply (hα : ContDiff ℝ n α) (ω : 𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F)) (x : E) :
    oneFormWedgeCLM hα ω x = alternatizeUncurryFin ((α x).smulRight (ω x)) := by
  simp [oneFormWedgeCLM]

/-- Pointwise, the wedge `α ∧ ω` is bounded in operator norm by `(k + 1) ‖α x‖ ‖ω x‖`. -/
theorem norm_oneFormWedgeCLM_apply_le (hα : ContDiff ℝ n α) (ω : 𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F))
    (x : E) : ‖oneFormWedgeCLM hα ω x‖ ≤ (k + 1) * ‖α x‖ * ‖ω x‖ := by
  rw [oneFormWedgeCLM_apply, mul_assoc, ← ContinuousLinearMap.norm_smulRight_apply]
  exact norm_alternatizeUncurryFin_le _

/-- The pointwise bound `‖(α ∧ ω) x‖ₑ ≤ (k + 1) ‖α x‖ₑ ‖ω x‖ₑ` in extended norms. -/
theorem enorm_oneFormWedgeCLM_apply_le (hα : ContDiff ℝ n α)
    (ω : 𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F)) (x : E) :
    ‖oneFormWedgeCLM hα ω x‖ₑ ≤ (k + 1) * ‖α x‖ₑ * ‖ω x‖ₑ := by
  simp only [eNorm_eq_nnNorm]
  exact_mod_cast norm_oneFormWedgeCLM_apply_le hα ω x

/-- The wedge with a smooth one-form does not enlarge the support of a test form. -/
theorem tsupport_oneFormWedgeCLM_subset (hα : ContDiff ℝ n α)
    (ω : 𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    tsupport (oneFormWedgeCLM hα ω : E → E [⋀^Fin (k + 1)]→L[ℝ] F) ⊆ tsupport α ∩ tsupport ω := by
  have h₀ : alternatizeUncurryFin (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) = 0 :=
    map_zero (alternatizeUncurryFinCLM ℝ E F)
  refine Set.subset_inter (closure_mono fun x hx ↦ ?_) (closure_mono fun x hx ↦ ?_) <;>
    contrapose hx <;> simp [Function.notMem_support.1 hx, h₀]

/-- The wedge with a smooth one-form commutes with extending test forms from `Ω'` to `Ω`. -/
@[simp]
theorem oneFormWedgeCLM_monoCLM (hα : ContDiff ℝ n α) (ω : 𝓓^{n}(Ω', E [⋀^Fin k]→L[ℝ] F)) :
    oneFormWedgeCLM hα (monoCLM ℝ ω : 𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F)) =
      monoCLM ℝ (oneFormWedgeCLM hα ω) := by
  have h₀ : alternatizeUncurryFin (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) = 0 :=
    map_zero (alternatizeUncurryFinCLM ℝ E F)
  ext x : 1
  by_cases h : Ω' ≤ Ω <;> simp [monoCLM_apply, h, h₀]

end OneFormWedge

section Leibniz

variable {f : E → ℝ}

/-- **The Leibniz rule** for test forms: `d (f ω) = df ∧ ω + f dω` for a smooth function `f`. -/
theorem extDerivCLM_smulLeftCLM (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    extDerivCLM (smulLeftCLM hf ω) =
      oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hf).2 ω + smulLeftCLM hf (extDerivCLM ω) := by
  ext x : 1
  rw [extDerivCLM_apply, coe_smulLeftCLM,
    TauCeti.extDeriv_function_smul (hf.differentiable (by simp) x)
      (ω.contDiff.differentiable (by simp) x)]
  simp [add_comm]

end Leibniz

end TestFunction

namespace ContinuousLinearMap

open TestFunction
open scoped Distributions

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] {Ω : TopologicalSpace.Opens E} {k : ℕ} {f : E → ℝ}

/-- **The boundary of a smooth multiple of a current**: for a continuous linear functional `T` on
test `(k + 1)`-forms and a smooth function `f`, `∂(fT) = f ∂T - T ⌞ df`. Here `fT = T ∘ (f ·)`,
the boundary is `∂T = T ∘ d`, and `(T ⌞ df) ω = T (df ∧ ω)`. -/
theorem comp_smulLeftCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (T ∘L smulLeftCLM hf) ∘L extDerivCLM =
      (T ∘L extDerivCLM) ∘L smulLeftCLM hf -
        T ∘L oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hf).2 := by
  ext ω
  simp [extDerivCLM_smulLeftCLM hf ω]

end ContinuousLinearMap

namespace ContDiffMapSupportedIn

open TopologicalSpace
open scoped ContDiff Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Compacts E}

/-- The `C^i` seminorms, `i ≤ k`, of `χ g` are bounded by `2 ^ k N_k(χ) M` when `M` bounds the
derivatives of `g` of order at most `k`. -/
theorem seminorm_bilinLeftCLM_mul_le (χ : 𝓓_{K}(E, ℂ)) {g : E → ℂ} (hg : ContDiff ℝ ∞ g)
    {k : ℕ} {M : ℝ} (hM : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ M) {i : ℕ} (hi : i ≤ k) :
    N[ℂ]_{K, i} (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hg χ) ≤
      2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le k) 0)
  refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (by positivity) i _).2 fun x _ ↦ ?_
  rw [bilinLeftCLM_apply]
  simp only [ContinuousLinearMap.mul_apply']
  refine (norm_iteratedFDeriv_mul_le χ.contDiff hg x (mod_cast le_top)).trans ?_
  calc _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * M := by
        gcongr with j hj
        · exact (norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
            (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2
              ((Finset.mem_range_succ_iff.1 hj).trans hi)))
        · exact hM _ ((Nat.sub_le i j).trans hi) x
    _ = 2 ^ i * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * M := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ _ := by gcongr; exact one_le_two

end ContDiffMapSupportedIn
