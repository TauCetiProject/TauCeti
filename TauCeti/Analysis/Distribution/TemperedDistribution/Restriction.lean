/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.SchwartzMap
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Tempered distributions as distributions, and compactly supported distributions as tempered ones

Mathlib has two carriers for generalized functions on a real normed space `E`: the distributions
`𝓓'(Ω, F)` on an open set `Ω`, continuous `ℝ`-linear maps on *real* test functions with the
topology of compact convergence, and the tempered distributions `𝓢'(E, F)`, continuous
`ℂ`-linear maps on *complex* Schwartz functions with the topology of pointwise convergence.
This file relates the two.

**Restriction.** Every test function is a Schwartz function (`TestFunction.toSchwartzMapCLM`), so
a tempered distribution `u` restricts to the distribution
`TemperedDistribution.toDistribution Ω u : φ ↦ u φ` on real test functions on `Ω`. On complex
test functions its complex-linear extension `Distribution.complexPairing` is again `u`
(`TemperedDistribution.complexPairing_toDistribution`): the real-test convention of `𝓓'` and the
complex-test convention of `𝓢'` agree. Restriction commutes with derivatives, sends an `Lᵖ`
function to the distribution of the same function, and is injective on the whole space, since
test functions are dense in Schwartz space. It is only a linear map: the source and target carry
the topologies of pointwise and of compact convergence, which are not identified here.

**Extension.** Conversely, let `T : 𝓓'(Ω, ℂ)` have compact support `dsupport T ⊆ Ω`. For a
Schwartz function `f` and a test function `χ` equal to one near the support of `T`, `χ f` is a
test function on `Ω` (`SchwartzMap.cutoffCLM`), and
`Distribution.toTemperedDistribution T f = T (χ f)`
does not depend on `χ` (`Distribution.toTemperedDistribution_apply_of_eventuallyEq`). This is a
tempered distribution whose restriction to `Ω` is `T`
(`Distribution.toDistribution_toTemperedDistribution`) and which vanishes on Schwartz functions
vanishing near the support of `T` (`Distribution.toTemperedDistribution_apply_eq_zero`), and it
is the only tempered distribution with these two properties
(`Distribution.eq_toTemperedDistribution`). On the whole space it is the unique tempered
distribution restricting to `T` (`Distribution.toTemperedDistribution_eq_iff`). The extension is
additive and homogeneous on distributions with compact support in `Ω`, and commutes with
derivatives.

## Main declarations

* `TemperedDistribution.toDistribution`: restriction of tempered distributions to `Ω`.
* `TemperedDistribution.complexPairing_toDistribution`: compatibility of the test conventions.
* `TemperedDistribution.toDistribution_lineDerivOp`,
  `MeasureTheory.Lp.toDistribution_toTemperedDistribution`: derivatives and `Lᵖ` functions.
* `TemperedDistribution.toDistribution_injective`: restriction to the whole space is injective.
* `Distribution.toTemperedDistribution`: the tempered extension of a compactly supported
  distribution, with `Distribution.toTemperedDistribution_apply_of_eventuallyEq`,
  `Distribution.toTemperedDistribution_eq_of_eventuallyEq`,
  `Distribution.toTemperedDistribution_apply_eq_zero`,
  `Distribution.toDistribution_toTemperedDistribution`, `Distribution.eq_toTemperedDistribution`
  and `Distribution.toTemperedDistribution_eq_iff`.
* `Distribution.toTemperedDistribution_zero`, `Distribution.toTemperedDistribution_add`,
  `Distribution.toTemperedDistribution_smul`, `Distribution.toTemperedDistribution_lineDerivOp`:
  linearity of the tempered extension and compatibility with derivatives.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.3 and §7.1.
-/

public section

noncomputable section

open Set Filter TopologicalSpace Function Complex
open scoped Distributions SchwartzMap Topology LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace TemperedDistribution

section Restriction

variable [NormedAddCommGroup F] [NormedSpace ℂ F] (Ω : Opens E)

/-- A real test function on `Ω` as a complex Schwartz function on `E`. -/
private def ofRealToSchwartzMapCLM : 𝓓(Ω, ℝ) →L[ℝ] 𝓢(E, ℂ) :=
  TestFunction.toSchwartzMapCLM ℝ ∘L TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM

private theorem ofRealToSchwartzMapCLM_apply (φ : 𝓓(Ω, ℝ)) (x : E) :
    ofRealToSchwartzMapCLM Ω φ x = φ x := by
  simp [ofRealToSchwartzMapCLM]

/-- The **restriction** of a tempered distribution `u` to the open set `Ω`: the distribution
`φ ↦ u φ` on real test functions on `Ω`, viewed as complex Schwartz functions on the whole space.
-/
def toDistribution : 𝓢'(E, F) →ₗ[ℂ] 𝓓'(Ω, F) where
  toFun u :=
    { toFun φ := u (ofRealToSchwartzMapCLM Ω φ)
      map_add' φ ψ := by rw [map_add, map_add]
      map_smul' c φ := by
        rw [map_smul, RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
          RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
      cont := (map_continuous u).comp (ofRealToSchwartzMapCLM Ω).continuous }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem toDistribution_apply (u : 𝓢'(E, F)) (φ : 𝓓(Ω, ℝ)) :
    toDistribution Ω u φ =
      u (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM φ)) :=
  (rfl)

/-- **The test conventions agree.** The complex-linear extension of the restriction of a tempered
distribution `u`, evaluated on a complex test function `φ`, is `u φ`. -/
@[simp]
theorem complexPairing_toDistribution (u : 𝓢'(E, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    (toDistribution Ω u).complexPairing φ = u (TestFunction.toSchwartzMapCLM ℂ φ) := by
  rw [Distribution.complexPairing_apply, toDistribution_apply, toDistribution_apply,
    ← smul_eq_mul, ← map_smul, ← map_add]
  congr 1
  ext x
  simp [mul_comm I, re_add_im]

/-- Restriction commutes with directional derivatives. -/
theorem toDistribution_lineDerivOp (u : 𝓢'(E, F)) (v : E) :
    toDistribution Ω (∂_{v} u) = ∂_{v} (toDistribution Ω u) := by
  ext φ
  have h : TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM (∂_{v} φ) =
      ∂_{v} (TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM φ) := by
    simp only [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_postcompCLM]
  rw [Distribution.lineDerivOp_apply_apply, toDistribution_apply, toDistribution_apply,
    lineDerivOp_apply_apply]
  simp only [map_neg, h, TestFunction.toSchwartzMapCLM_lineDerivOp]

/-- **Restriction to the whole space is injective**: a tempered distribution is determined by its
values on test functions. -/
theorem toDistribution_injective [FiniteDimensional ℝ E] :
    Injective (toDistribution (⊤ : Opens E) : 𝓢'(E, F) → 𝓓'(⊤, F)) := by
  intro u v h
  refine TemperedDistribution.ext_real fun φ hφ ↦ ?_
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, φ.smooth ⊤, hφ, subset_univ _⟩
  have hψ : TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM ψ) =
      φ.postcompCLM ofRealCLM := by
    ext x
    simp [ψ]
  rw [← hψ, ← toDistribution_apply, ← toDistribution_apply, h]

/-- The restriction of the tempered distribution of an `Lᵖ` function is the distribution of the
same function. -/
theorem _root_.MeasureTheory.Lp.toDistribution_toTemperedDistribution [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E} [μ.HasTemperateGrowth]
    [MeasureTheory.IsLocallyFiniteMeasure μ] {p : ENNReal} [Fact (1 ≤ p)]
    (f : MeasureTheory.Lp F p μ) :
    toDistribution Ω (f : 𝓢'(E, F)) = Distribution.ofFun Ω f μ ⊤ := by
  ext φ
  rw [toDistribution_apply, MeasureTheory.Lp.toTemperedDistribution_apply,
    Distribution.ofFun_apply
      (((MeasureTheory.Lp.memLp f).locallyIntegrable Fact.out).locallyIntegrableOn _)]
  simp

end Restriction

end TemperedDistribution

namespace Distribution

variable {Ω : Opens E}

/-- Multiplication by a test function `χ`, from complex Schwartz functions to complex test
functions on `Ω`. -/
private def cutoff (χ : 𝓓(Ω, ℝ)) : 𝓢(E, ℂ) →L[ℂ] 𝓓(Ω, ℂ) :=
  SchwartzMap.cutoffCLM ℂ χ.contDiff χ.hasCompactSupport χ.tsupport_subset

private theorem cutoff_apply (χ : 𝓓(Ω, ℝ)) (f : 𝓢(E, ℂ)) (x : E) :
    cutoff χ f x = χ x • f x :=
  SchwartzMap.cutoffCLM_apply _ _ _ f x

variable [FiniteDimensional ℝ E]

open Classical in
/-- The **tempered extension** of a complex distribution `T` with compact support in `Ω`: the
tempered distribution `f ↦ T (χ f)`, where `χ` is a test function equal to one on a neighbourhood
of the support of `T`. It does not depend on `χ`
(`Distribution.toTemperedDistribution_apply_of_eventuallyEq`), and it restricts to `T` on `Ω`
(`Distribution.toDistribution_toTemperedDistribution`). It is zero if no such `χ` exists, which
does not happen when the support is a compact subset of `Ω`. -/
def toTemperedDistribution (T : 𝓓'(Ω, ℂ)) : 𝓢'(E, ℂ) :=
  if h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 then
    ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ (T.complexPairing ∘L cutoff h.choose)
  else 0

/-- **Independence of the cutoff.** The tempered extension of `T` is `f ↦ T (χ f)` for every test
function `χ` equal to one on a neighbourhood of the support of `T`. -/
theorem toTemperedDistribution_apply_of_eventuallyEq (T : 𝓓'(Ω, ℂ)) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g : 𝓓(Ω, ℂ)} {f : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = χ x * f x) : T.toTemperedDistribution f = T.complexPairing g := by
  have h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 := ⟨χ, hχ⟩
  have hT : T.toTemperedDistribution f = T.complexPairing (cutoff h.choose f) := by
    rw [toTemperedDistribution, dite_eq_left h]
    -- `toPointwiseConvergenceCLM` is the identity on the underlying continuous linear map, but
    -- rewriting with its `_apply` lemma leaves a term that is not type-correct, so we apply
    -- `comp_apply` up to this identification.
    exact ContinuousLinearMap.comp_apply _ _ _
  rw [hT]
  refine complexPairing_eq_of_eventuallyEq T ?_
  filter_upwards [h.choose_spec, hχ] with x h₁ h₂
  rw [cutoff_apply, hg, h₁, h₂, ofReal_one, one_mul, one_smul]

/-- The tempered extension of `T` is `f ↦ T (χ f)` for the cutoff by `χ`. -/
private theorem toTemperedDistribution_apply_cutoff (T : 𝓓'(Ω, ℂ)) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (f : 𝓢(E, ℂ)) :
    T.toTemperedDistribution f = T.complexPairing (cutoff χ f) :=
  toTemperedDistribution_apply_of_eventuallyEq T hχ fun x ↦ by rw [cutoff_apply, real_smul]

/-- The tempered extension of `T` depends only on the germ of the Schwartz function along the
support of `T`. -/
theorem toTemperedDistribution_eq_of_eventuallyEq (T : 𝓓'(Ω, ℂ)) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) {f g : 𝓢(E, ℂ)} (h : (f : E → ℂ) =ᶠ[𝓝ˢ (dsupport T)] g) :
    T.toTemperedDistribution f = T.toTemperedDistribution g := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTΩ
  rw [toTemperedDistribution_apply_cutoff T hχ, toTemperedDistribution_apply_cutoff T hχ]
  refine complexPairing_eq_of_eventuallyEq T ?_
  filter_upwards [h] with x hx
  rw [cutoff_apply, cutoff_apply, hx]

/-- The tempered extension of `T` vanishes on every Schwartz function vanishing near the support
of `T`. -/
theorem toTemperedDistribution_apply_eq_zero (T : 𝓓'(Ω, ℂ)) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) {f : 𝓢(E, ℂ)} (hf : ∀ᶠ x in 𝓝ˢ (dsupport T), f x = 0) :
    T.toTemperedDistribution f = 0 := by
  rw [toTemperedDistribution_eq_of_eventuallyEq T hT hTΩ (g := 0) hf, map_zero]

/-- The tempered extension of the zero distribution is zero. -/
@[simp]
theorem toTemperedDistribution_zero : (0 : 𝓓'(Ω, ℂ)).toTemperedDistribution = 0 := by
  have h0 : dsupport (0 : 𝓓'(Ω, ℂ)) = ∅ := (dsupport_eq_empty_iff _).2 rfl
  ext f
  rw [toTemperedDistribution_apply_cutoff 0 (χ := 0) (by rw [h0]; simp)]
  simp [complexPairing_apply]

/-- The tempered extension is additive on distributions with compact support in `Ω`. -/
theorem toTemperedDistribution_add (S T : 𝓓'(Ω, ℂ)) (hS : IsCompact (dsupport S))
    (hSΩ : dsupport S ⊆ Ω) (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    (S + T).toTemperedDistribution = S.toTemperedDistribution + T.toTemperedDistribution := by
  obtain ⟨χ, hχ, -⟩ :=
    TestFunction.exists_eventually_eq_one (n := ⊤) (hS.union hT) (union_subset hSΩ hTΩ)
  have hST : dsupport (S + T) ⊆ dsupport S ∪ dsupport T := dsupport_add_subset ⇑S ⇑T
  ext f
  rw [add_apply,
    toTemperedDistribution_apply_cutoff _ (hχ.filter_mono (nhdsSet_mono hST)),
    toTemperedDistribution_apply_cutoff S (hχ.filter_mono (nhdsSet_mono subset_union_left)),
    toTemperedDistribution_apply_cutoff T (hχ.filter_mono (nhdsSet_mono subset_union_right)),
    complexPairing_add]

/-- The tempered extension is homogeneous. -/
theorem toTemperedDistribution_smul (c : ℂ) (T : 𝓓'(Ω, ℂ)) :
    (c • T).toTemperedDistribution = c • T.toTemperedDistribution := by
  have hcT : ∀ (c : ℂ) (T : 𝓓'(Ω, ℂ)), dsupport (c • T) ⊆ dsupport T := fun c T ↦
    dsupport_subset_dsupport fun _ _ h φ hφ ↦ by simp [h φ hφ]
  ext f
  rw [smul_apply, smul_eq_mul]
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨χ, hχ⟩ := h
    rw [toTemperedDistribution_apply_cutoff _ (hχ.filter_mono (nhdsSet_mono (hcT c T))),
      toTemperedDistribution_apply_cutoff T hχ, complexPairing_smul]
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : (0 : ℂ) • T = 0 := by
      ext φ
      simp
    rw [h0, toTemperedDistribution_zero, zero_mul, zero_apply]
  -- For `c ≠ 0` neither `T` nor `c • T` admits a cutoff, so both sides are zero.
  have h' : ¬∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport (c • T)), χ x = 1 := by
    refine fun ⟨χ, hχ⟩ ↦ h ⟨χ, hχ.filter_mono (nhdsSet_mono ?_)⟩
    simpa [smul_smul, inv_mul_cancel₀ hc] using hcT c⁻¹ (c • T)
  rw [toTemperedDistribution, dite_eq_right h', toTemperedDistribution, dite_eq_right h,
    zero_apply, mul_zero]

/-- The tempered extension of a distribution with compact support in `Ω` commutes with directional
derivatives. -/
theorem toTemperedDistribution_lineDerivOp (T : 𝓓'(Ω, ℂ)) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) (v : E) :
    (∂_{v} T).toTemperedDistribution = ∂_{v} T.toTemperedDistribution := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTΩ
  ext f
  rw [toTemperedDistribution_apply_cutoff _
      (hχ.filter_mono (nhdsSet_mono (dsupport_lineDerivOp_subset v))),
    complexPairing_lineDerivOp, TemperedDistribution.lineDerivOp_apply_apply,
    toTemperedDistribution_apply_cutoff T hχ, map_neg, map_neg, neg_inj]
  refine complexPairing_eq_of_eventuallyEq T ?_
  -- Near the support of `T`, the cutoff `χ f` agrees with `f` on a neighbourhood.
  filter_upwards [hχ.eventually_nhdsSet] with x hx
  have h : (cutoff χ f : E → ℂ) =ᶠ[𝓝 x] f :=
    hx.mono fun y hy ↦ by rw [cutoff_apply, hy, one_smul]
  rw [TestFunction.lineDerivOp_apply_eq_fderiv, h.fderiv_eq, cutoff_apply, hx.self_of_nhds,
    one_smul, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- **The tempered extension restricts to `T`.** -/
@[simp]
theorem toDistribution_toTemperedDistribution (T : 𝓓'(Ω, ℂ)) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) :
    TemperedDistribution.toDistribution Ω T.toTemperedDistribution = T := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTΩ
  ext φ
  set f := TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM φ)
  rw [TemperedDistribution.toDistribution_apply,
    toTemperedDistribution_apply_cutoff T hχ, ← complexPairing_postcompCLM_ofRealCLM]
  refine complexPairing_eq_of_eventuallyEq T ?_
  filter_upwards [hχ] with x hx
  simp [cutoff_apply, hx]

/-- **Uniqueness of the tempered extension.** A tempered distribution whose restriction to `Ω` is
`T` and which vanishes on every Schwartz function vanishing near the support of `T` is the
tempered extension of `T`. -/
theorem eq_toTemperedDistribution (T : 𝓓'(Ω, ℂ)) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) {u : 𝓢'(E, ℂ)} (hu : TemperedDistribution.toDistribution Ω u = T)
    (hu₀ : ∀ f : 𝓢(E, ℂ), (∀ᶠ x in 𝓝ˢ (dsupport T), f x = 0) → u f = 0) :
    u = T.toTemperedDistribution := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTΩ
  ext f
  -- Split `f` into the Schwartz function `χ f` and a remainder vanishing near the support of `T`.
  set g := TestFunction.toSchwartzMapCLM ℂ (cutoff χ f)
  have hsplit : u f = u g + u (f - g) := by rw [← map_add, add_sub_cancel]
  rw [toTemperedDistribution_apply_cutoff T hχ, ← hu,
    TemperedDistribution.complexPairing_toDistribution, hsplit, hu₀ (f - g) ?_, add_zero]
  filter_upwards [hχ] with x hx
  simp [g, cutoff_apply, hx]

/-- On the whole space, the tempered extension of a compactly supported distribution `T` is the
unique tempered distribution whose restriction is `T`. -/
theorem toTemperedDistribution_eq_iff (T : 𝓓'((⊤ : Opens E), ℂ)) (hT : IsCompact (dsupport T))
    (u : 𝓢'(E, ℂ)) :
    T.toTemperedDistribution = u ↔ TemperedDistribution.toDistribution ⊤ u = T := by
  refine ⟨fun h ↦ h ▸ toDistribution_toTemperedDistribution T hT (subset_univ _), fun h ↦ ?_⟩
  refine TemperedDistribution.toDistribution_injective ?_
  rw [h, toDistribution_toTemperedDistribution T hT (subset_univ _)]

end Distribution
