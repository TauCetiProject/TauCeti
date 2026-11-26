/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Compactly supported distributions as tempered distributions

Let `T : 𝓓'(Ω, ℂ)` be a complex distribution whose support is a compact subset of the open set
`Ω`. For a complex test function `χ` on `Ω` equal to one on a neighbourhood of the support of `T`,
the tempered distribution `Distribution.cutoffTempered T χ : f ↦ T (χ f)` does not depend on `χ`
(`Distribution.cutoffTempered_congr`). This file names it without reference to a cutoff:
`Distribution.toTemperedDistribution T` is the **tempered extension** of `T`, and
`Distribution.toTemperedDistribution_eq_cutoffTempered` evaluates it with any such cutoff.

The tempered extension restricts to `T` on `Ω`
(`Distribution.toDistribution_toTemperedDistribution`) and vanishes on Schwartz functions
vanishing near the support of `T` (`Distribution.toTemperedDistribution_apply_eq_zero`), and it
is the only tempered distribution with these two properties
(`Distribution.eq_toTemperedDistribution`). On the whole space it is the unique tempered
distribution restricting to `T`
(`Distribution.toTemperedDistribution_eq_iff_toDistribution_top_eq`). The extension is linear on
distributions with compact support in `Ω`, and commutes with derivatives.

## Main declarations

* `Distribution.toTemperedDistribution`: the tempered extension of a compactly supported
  distribution.
* `Distribution.toTemperedDistribution_eq_cutoffTempered`: independence of the cutoff.
* `Distribution.toTemperedDistribution_apply_eq_of_eventuallyEq`,
  `Distribution.toTemperedDistribution_apply_eq_zero`: the extension only sees the germ of a
  Schwartz function along the support of `T`.
* `Distribution.toDistribution_toTemperedDistribution`: the extension restricts to `T`.
* `Distribution.eq_toTemperedDistribution`,
  `Distribution.toTemperedDistribution_eq_iff_toDistribution_top_eq`: uniqueness.
* `Distribution.toTemperedDistribution_zero`, `Distribution.toTemperedDistribution_add`,
  `Distribution.toTemperedDistribution_smul`, `Distribution.toTemperedDistribution_neg`,
  `Distribution.toTemperedDistribution_sub`, `Distribution.toTemperedDistribution_lineDerivOp`:
  linearity of the tempered extension and compatibility with derivatives.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.3 and §7.1.
-/

public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Distributions SchwartzMap Topology LineDeriv

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

open Classical in
/-- The **tempered extension** of a complex distribution `T` with compact support in `Ω`: the
tempered distribution `χ T : f ↦ T (χ f)` of `Distribution.cutoffTempered`, for a test function
`χ` equal to one on a neighbourhood of the support of `T`. It does not depend on `χ`
(`Distribution.toTemperedDistribution_eq_cutoffTempered`), and it restricts to `T` on `Ω`
(`Distribution.toDistribution_toTemperedDistribution`). It is zero if no such `χ` exists
(`Distribution.toTemperedDistribution_of_not_exists`), which does not happen when `E` is
finite-dimensional and the support is a compact subset of `Ω`. -/
def toTemperedDistribution (T : 𝓓'(Ω, ℂ)) : 𝓢'(E, ℂ) :=
  if h : ∃ χ : 𝓓(Ω, ℂ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 then T.cutoffTempered h.choose else 0

/-- **Independence of the cutoff.** The tempered extension of `T` is `χ T` for every test function
`χ` equal to one on a neighbourhood of the support of `T`. -/
theorem toTemperedDistribution_eq_cutoffTempered (T : 𝓓'(Ω, ℂ)) {χ : 𝓓(Ω, ℂ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) : T.toTemperedDistribution = T.cutoffTempered χ := by
  have h : ∃ χ : 𝓓(Ω, ℂ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 := ⟨χ, hχ⟩
  rw [toTemperedDistribution, dite_eq_left h]
  exact T.cutoffTempered_congr ((h.choose_spec.and hχ).mono fun x hx ↦ hx.1.trans hx.2.symm)

/-- The tempered extension of `T` is zero when no test function on `Ω` is equal to one on a
neighbourhood of the support of `T`. -/
@[simp]
theorem toTemperedDistribution_of_not_exists (T : 𝓓'(Ω, ℂ))
    (h : ¬∃ χ : 𝓓(Ω, ℂ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) : T.toTemperedDistribution = 0 :=
  dite_eq_right h

/-- The tempered extension of `T` depends only on the germ of the Schwartz function along the
support of `T`. -/
theorem toTemperedDistribution_apply_eq_of_eventuallyEq (T : 𝓓'(Ω, ℂ)) {f g : 𝓢(E, ℂ)}
    (h : (f : E → ℂ) =ᶠ[𝓝ˢ (dsupport T)] g) :
    T.toTemperedDistribution f = T.toTemperedDistribution g := by
  by_cases hT : ∃ χ : 𝓓(Ω, ℂ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨χ, hχ⟩ := hT
    rw [toTemperedDistribution_eq_cutoffTempered T hχ, cutoffTempered_def, cutoffTempered_def]
    refine complexPairing_eq_of_eventuallyEq T ?_
    filter_upwards [h] with x hx
    simp only [TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', hx]
  · rw [toTemperedDistribution_of_not_exists T hT, zero_apply, zero_apply]

/-- The tempered extension of `T` vanishes on every Schwartz function vanishing near the support
of `T`. -/
theorem toTemperedDistribution_apply_eq_zero (T : 𝓓'(Ω, ℂ)) {f : 𝓢(E, ℂ)}
    (hf : ∀ᶠ x in 𝓝ˢ (dsupport T), f x = 0) : T.toTemperedDistribution f = 0 := by
  rw [toTemperedDistribution_apply_eq_of_eventuallyEq T (g := 0) hf, map_zero]

/-- The tempered extension of the zero distribution is zero. -/
@[simp]
theorem toTemperedDistribution_zero : (0 : 𝓓'(Ω, ℂ)).toTemperedDistribution = 0 := by
  rw [toTemperedDistribution]
  split_ifs
  · exact cutoffTempered_zero _
  · rfl

/-- The tempered extension is homogeneous. -/
@[simp]
theorem toTemperedDistribution_smul (c : ℂ) (T : 𝓓'(Ω, ℂ)) :
    (c • T).toTemperedDistribution = c • T.toTemperedDistribution := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul ℂ T, toTemperedDistribution_zero]
    exact (zero_smul ℂ T.toTemperedDistribution).symm
  have hcT : dsupport ⇑(c • T) = dsupport ⇑T := dsupport_smul_of_ne_zero hc ⇑T
  -- Both extensions are defined by the same cutoff condition, hence with the same cutoff.
  rw [toTemperedDistribution, toTemperedDistribution, hcT]
  split_ifs
  · exact cutoffTempered_smul c T _
  · exact (smul_zero (A := 𝓢'(E, ℂ)) c).symm

/-- The tempered extension commutes with negation. -/
@[simp]
theorem toTemperedDistribution_neg (T : 𝓓'(Ω, ℂ)) :
    (-T).toTemperedDistribution = -T.toTemperedDistribution := by
  rw [← neg_one_smul ℂ T, toTemperedDistribution_smul]
  exact neg_one_smul ℂ T.toTemperedDistribution

variable [FiniteDimensional ℝ E]

/-- The tempered extension is additive on distributions with compact support in `Ω`. -/
theorem toTemperedDistribution_add (S T : 𝓓'(Ω, ℂ)) (hS : IsCompact (dsupport S))
    (hSΩ : dsupport S ⊆ Ω) (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    (S + T).toTemperedDistribution = S.toTemperedDistribution + T.toTemperedDistribution := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    (hS.union hT) Ω.isOpen (union_subset hSΩ hTΩ) subset_rfl
  have hST : dsupport (S + T) ⊆ dsupport S ∪ dsupport T := dsupport_add_subset ⇑S ⇑T
  rw [toTemperedDistribution_eq_cutoffTempered _ (hχ.filter_mono (nhdsSet_mono hST)),
    toTemperedDistribution_eq_cutoffTempered S (hχ.filter_mono (nhdsSet_mono subset_union_left)),
    toTemperedDistribution_eq_cutoffTempered T (hχ.filter_mono (nhdsSet_mono subset_union_right)),
    cutoffTempered_add]

/-- The tempered extension is subtractive on distributions with compact support in `Ω`. -/
theorem toTemperedDistribution_sub (S T : 𝓓'(Ω, ℂ)) (hS : IsCompact (dsupport S))
    (hSΩ : dsupport S ⊆ Ω) (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    (S - T).toTemperedDistribution = S.toTemperedDistribution - T.toTemperedDistribution := by
  have hnT : dsupport ⇑(-T) = dsupport ⇑T := dsupport_neg ⇑T
  rw [sub_eq_add_neg, toTemperedDistribution_add S (-T) hS hSΩ (hnT ▸ hT) (hnT ▸ hTΩ),
    toTemperedDistribution_neg, ← sub_eq_add_neg]

/-- The tempered extension of a distribution with compact support in `Ω` commutes with directional
derivatives. -/
theorem toTemperedDistribution_lineDerivOp (T : 𝓓'(Ω, ℂ)) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) (v : E) :
    (∂_{v} T).toTemperedDistribution = ∂_{v} T.toTemperedDistribution := by
  obtain ⟨χ, hχ, -⟩ :=
    TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) hT Ω.isOpen hTΩ subset_rfl
  -- The derivative of `χ` vanishes near the support of `T`, where `χ` is constant.
  have hχ' : ((∂_{v} χ : 𝓓(Ω, ℂ)) : E → ℂ) =ᶠ[𝓝ˢ (dsupport T)] (0 : 𝓓(Ω, ℂ)) := by
    filter_upwards [hχ.eventually_nhdsSet] with x hx
    have h1 : (χ : E → ℂ) =ᶠ[𝓝 x] fun _ ↦ 1 := hx
    rw [TestFunction.lineDerivOp_apply_eq_fderiv, h1.fderiv_eq]
    simp
  have h0 : T.cutoffTempered 0 = 0 := by
    ext ψ
    simp [cutoffTempered_def]
  rw [toTemperedDistribution_eq_cutoffTempered _
      (hχ.filter_mono (nhdsSet_mono (dsupport_lineDerivOp_subset v))),
    toTemperedDistribution_eq_cutoffTempered T hχ, lineDerivOp_cutoffTempered,
    cutoffTempered_congr T hχ', h0, zero_add]

/-- **The tempered extension restricts to `T`.** -/
@[simp]
theorem toDistribution_toTemperedDistribution (T : 𝓓'(Ω, ℂ)) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) :
    TemperedDistribution.toDistribution Ω T.toTemperedDistribution = T := by
  obtain ⟨χ, hχ, -⟩ :=
    TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) hT Ω.isOpen hTΩ subset_rfl
  ext φ
  rw [TemperedDistribution.toDistribution_apply, toTemperedDistribution_eq_cutoffTempered T hχ,
    cutoffTempered_def, ← complexPairing_postcompCLM_ofRealCLM]
  refine complexPairing_eq_of_eventuallyEq T ?_
  filter_upwards [hχ] with x hx
  simp [hx]

/-- **Uniqueness of the tempered extension.** A tempered distribution whose restriction to `Ω` is
`T` and which vanishes on every Schwartz function vanishing near the support of `T` is the
tempered extension of `T`. -/
theorem eq_toTemperedDistribution (T : 𝓓'(Ω, ℂ)) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) {u : 𝓢'(E, ℂ)} (hu : TemperedDistribution.toDistribution Ω u = T)
    (hu₀ : ∀ f : 𝓢(E, ℂ), (∀ᶠ x in 𝓝ˢ (dsupport T), f x = 0) → u f = 0) :
    u = T.toTemperedDistribution := by
  obtain ⟨χ, hχ, -⟩ :=
    TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) hT Ω.isOpen hTΩ subset_rfl
  rw [toTemperedDistribution_eq_cutoffTempered T hχ]
  ext f
  -- Split `f` into the Schwartz function `χ f` and a remainder vanishing near the support of `T`.
  set g := TestFunction.toSchwartzMapCLM ℝ
    (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (f.smooth ⊤) χ)
  have hsplit : u f = u g + u (f - g) := by rw [← map_add, add_sub_cancel]
  rw [cutoffTempered_def, ← hu, complexPairing_toDistribution, hsplit, hu₀ (f - g) ?_, add_zero]
  filter_upwards [hχ] with x hx
  simp [g, hx]

/-- On the whole space, the tempered extension of a compactly supported distribution `T` is the
unique tempered distribution whose restriction is `T`. -/
theorem toTemperedDistribution_eq_iff_toDistribution_top_eq (T : 𝓓'((⊤ : Opens E), ℂ))
    (hT : IsCompact (dsupport T)) (u : 𝓢'(E, ℂ)) :
    T.toTemperedDistribution = u ↔ TemperedDistribution.toDistribution ⊤ u = T := by
  refine ⟨fun h ↦ h ▸ toDistribution_toTemperedDistribution T hT (subset_univ _), fun h ↦ ?_⟩
  refine TemperedDistribution.toDistribution_injective ?_
  rw [h, toDistribution_toTemperedDistribution T hT (subset_univ _)]

end Distribution
