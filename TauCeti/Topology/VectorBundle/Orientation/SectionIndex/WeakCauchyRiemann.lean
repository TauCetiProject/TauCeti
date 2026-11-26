/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.DifferentialInequality
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Holomorphic

/-!
# The zero count for sections solving a weak Cauchy–Riemann inequality

Let `s` be a continuous section of an oriented real plane bundle `E → M` with fibre `ℂ`, over an
oriented surface `M` charted on `ℂ`. Read near a point `z` in a linear trivialization `e` and a
chart `φ`, the section becomes a function `f y = (e (s (φ⁻¹ y))).2` of `y ∈ ℂ`. Suppose that, on
an open set `Ω ∋ φ z`, `f` has a weak conjugate Wirtinger derivative `G = \bar∂ f` with

`‖\bar∂ f‖ ≤ g ‖f‖` almost everywhere on `Ω`,

for a function `g ∈ Lᵖ_loc(Ω)`, `p > 2`. This is what a section in the kernel of a real
Cauchy–Riemann operator whose zeroth-order term is only `Lᵖ` looks like in a holomorphic chart and
a complex frame: there the operator reads `\bar∂ + Z` with `Z ∈ Lᵖ_loc`, and a kernel element
satisfies `‖\bar∂ f‖ = ‖Z f‖ ≤ ‖Z‖ ‖f‖`. The statements here take the inequality in coordinates as
their hypothesis.

By the scalar similarity principle for weak inequalities
(`TauCeti.exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le`), near `φ z` the
function `f` is `v * σ` with `v` continuous and nonzero at `φ z` and `σ` analytic at `φ z`. So the
zeros of `s` count as those of a holomorphic section, through the statements of
`TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Holomorphic`: the local index at an
isolated zero is positive, on a compact surface the number of zeros is at most the Euler number
`⟨e(E), [M]⟩`, and on a connected compact surface a section which does not vanish identically has
finitely many zeros, so a section vanishing at more than `⟨e(E), [M]⟩` points vanishes
identically. This extends the statements of
`TauCeti.Topology.VectorBundle.Orientation.SectionIndex.CauchyRiemann`, for `C¹` sections and
locally bounded `g`, to weak solutions and `Lᵖ` bounds.

## Main results

* `Bundle.Trivialization.eventually_eq_zero_or_eventually_ne_zero_of_hasWeakConjWirtingerDerivOn`:
  near a point the section vanishes identically or has no other zero.
* `TauCeti.VectorBundleOrientation.sectionIndex_pos_of_hasWeakConjWirtingerDerivOn`: the local
  index at an isolated zero is positive.
* `TauCeti.finite_setOf_section_eq_zero_of_hasWeakConjWirtingerDerivOn`: on a connected compact
  surface, a section which is not identically zero has finitely many zeros.
* `ncard_le_evalFundamentalClass_eulerClass_of_hasWeakConjWirtingerDerivOn`,
  `evalFundamentalClass_eulerClass_nonneg_of_hasWeakConjWirtingerDerivOn` and
  `eq_zero_of_evalFundamentalClass_eulerClass_lt_ncard_of_hasWeakConjWirtingerDerivOn`, in the
  namespace `TauCeti.VectorBundleOrientation`: the zero count, the nonnegativity of the Euler
  number, and vanishing at more points than the Euler number.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52 (2012), Theorem 2.3.5 (the similarity principle) and the proof of
  Theorem C.1.10 (iii) (the zeros of a section in the kernel of a real Cauchy–Riemann operator on a
  line bundle are isolated, of positive order, and counted by the first Chern number).
-/

public section

noncomputable section

open Bundle CategoryTheory Filter MeasureTheory Module Set Topology TopologicalSpace
open scoped ENNReal

namespace Bundle.Trivialization

open TauCeti

variable {M : Type} [TopologicalSpace M] {E : M → Type} [TopologicalSpace (TotalSpace ℂ E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)] (e : Trivialization ℂ (π ℂ E))
  [e.IsLinear ℝ] (φ : OpenPartialHomeomorph M ℂ) {z : M} {s : ∀ x, E x}

/-- **A section solving a weak Cauchy–Riemann inequality vanishes near a point or has no other
zero near it.** Let `e` be a linear trivialization of a real plane bundle `E` with fibre `ℂ` and
`φ` a chart of `M` with values in `ℂ`, both defined at `z`. If the section `s`, read in these
coordinates as `f y = (e (s (φ⁻¹ y))).2`, is continuous on an open set `Ω ∋ φ z` with weak
conjugate Wirtinger derivative `G` there and `‖G‖ ≤ g ‖f‖` almost everywhere on `Ω`, for
`g ∈ Lᵖ_loc(Ω)` and `p > 2`, then either `s` vanishes on a neighbourhood of `z`, or `s` does not
vanish on a punctured neighbourhood of `z`. -/
theorem eventually_eq_zero_or_eventually_ne_zero_of_hasWeakConjWirtingerDerivOn
    (hze : z ∈ e.baseSet) (hzφ : z ∈ φ.source) {p : ℝ≥0∞} (hp : 2 < p) {Ω : Opens ℂ}
    (hzΩ : φ z ∈ Ω) {g : ℂ → ℝ} (hg : MemLpLoc p Ω g) {G : ℂ → ℂ}
    (hf : ContinuousOn (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) Ω)
    (hG : HasWeakConjWirtingerDerivOn volume Ω
      (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) G)
    (hle : ∀ᵐ y ∂volume.restrict Ω,
      ‖G y‖ ≤ g y * ‖(e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2‖) :
    (∀ᶠ x in 𝓝 z, s x = 0) ∨ ∀ᶠ x in 𝓝[≠] z, s x ≠ 0 := by
  obtain ⟨v, σ, hv, hv₀, hσ, hfac⟩ :=
    exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le hp hg hf hG hle hzΩ
  exact e.eventually_eq_zero_or_eventually_ne_zero_of_eventually_eq_mul φ hze hzφ hv hv₀ hσ hfac

end Bundle.Trivialization

namespace TauCeti

section Finite

variable {M : Type} [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M] {E : M → Type}
  [TopologicalSpace (TotalSpace ℂ E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  {s : ∀ x, E x}

/-- **Unique continuation for sections solving a weak Cauchy–Riemann inequality.** Let `M` be a
connected compact space and `s` a section of a real plane bundle `E → M` with fibre `ℂ`. Suppose
that around every point `z` there are a chart `φ z` and a linear trivialization `e z` in which `s`,
read as `f y = (e z (s ((φ z)⁻¹ y))).2`, is continuous on an open set `Ω z ∋ φ z z` with weak
conjugate Wirtinger derivative `G z` there and `‖G z‖ ≤ g z ‖f‖` almost everywhere on `Ω z`, for
`g z ∈ Lᵖ_loc(Ω z)` and `p > 2`. If `s` does not vanish identically, it has finitely many
zeros. -/
theorem finite_setOf_section_eq_zero_of_hasWeakConjWirtingerDerivOn
    (φ : M → OpenPartialHomeomorph M ℂ)
    (e : M → Trivialization ℂ (π ℂ E)) [∀ z, (e z).IsLinear ℝ] (hzφ : ∀ z, z ∈ (φ z).source)
    (hze : ∀ z, z ∈ (e z).baseSet) {p : ℝ≥0∞} (hp : 2 < p) (Ω : M → Opens ℂ)
    (hzΩ : ∀ z, φ z z ∈ Ω z) (g : M → ℂ → ℝ) (hg : ∀ z, MemLpLoc p (Ω z) (g z))
    (G : M → ℂ → ℂ)
    (hf : ∀ z, ContinuousOn
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (Ω z))
    (hG : ∀ z, HasWeakConjWirtingerDerivOn volume (Ω z)
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (G z))
    (hle : ∀ z, ∀ᵐ y ∂volume.restrict (Ω z),
      ‖G z y‖ ≤ g z y * ‖(e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2‖)
    (hne : ∃ x, s x ≠ 0) : {x | s x = 0}.Finite :=
  finite_setOf_section_eq_zero_of_eventually_eq_mul φ e hzφ hze
    (fun z ↦ exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le hp (hg z) (hf z)
      (hG z) (hle z) (hzΩ z)) hne

end Finite

namespace VectorBundleOrientation

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] {E : M → Type}
  [TopologicalSpace (TotalSpace ℂ E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle ℂ E] [VectorBundle ℝ ℂ E]
  (o : VectorBundleOrientation ℂ E (Fin (1 + 1))) (hF : finrank ℝ ℂ = 1 + 1)
  (oM : HomologicalOrientation M ℂ (1 + 1)) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' ℂ x (s x))

/-- **The local index of a section at an isolated zero solving a weak Cauchy–Riemann inequality is
positive.** Let `e` be a linear trivialization of a real plane bundle `E` with fibre `ℂ` and `φ` a
chart of `M` with values in `ℂ`, both defined at `z`, oriented compatibly with `E` and `M` near `z`
as in `TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`. If the section, read
in these coordinates as `f y = (e (s (φ⁻¹ y))).2`, is continuous on an open set `Ω ∋ φ z` with
weak conjugate Wirtinger derivative `G` there and `‖G‖ ≤ g ‖f‖` almost everywhere on `Ω`, for
`g ∈ Lᵖ_loc(Ω)` and `p > 2`, and `z` is an isolated zero of `s`, then the local index of `s` at
`z` is positive. -/
theorem sectionIndex_pos_of_hasWeakConjWirtingerDerivOn (e : Trivialization ℂ (π ℂ E))
    [e.IsLinear ℝ] (φ : OpenPartialHomeomorph M ℂ) {z : M}
    (hze : z ∈ e.baseSet) (hzφ : z ∈ φ.source) {ω : Orientation ℝ ℂ (Fin (1 + 1))}
    (ho : ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ e.baseSet, e.mapOrientation (Fin (1 + 1)) hx (o x) = ω)
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, ℂ)) (S := {⟨z, hzφ⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.property hzφ (sub_eq_zero.1 hx))) (1 + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ⟩
          (1 + 1)).symm (oM z)).val =
      (ω.localOrientation hF).val)
    {p : ℝ≥0∞} (hp : 2 < p) {Ω : Opens ℂ} (hzΩ : φ z ∈ Ω) {g : ℂ → ℝ} (hg : MemLpLoc p Ω g)
    {G : ℂ → ℂ}
    (hf : ContinuousOn (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) Ω)
    (hG : HasWeakConjWirtingerDerivOn volume Ω
      (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) G)
    (hle : ∀ᵐ y ∂volume.restrict Ω,
      ‖G y‖ ≤ g y * ‖(e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2‖)
    (hsz : s z = 0) (hiso : ∀ᶠ x in 𝓝[≠] z, s x ≠ 0) :
    0 < o.sectionIndex hF oM hs z := by
  obtain ⟨v, σ, hv, hv₀, hσ, hfac⟩ :=
    exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le hp hg hf hG hle hzΩ
  exact o.sectionIndex_pos_of_eventually_eq_mul hF oM hs e φ hze hzφ ho hφ hv hv₀ hσ hfac hsz hiso

section CompactSpace

variable [CompactSpace M] (φ : M → OpenPartialHomeomorph M ℂ) (e : M → Trivialization ℂ (π ℂ E))
  [∀ z, (e z).IsLinear ℝ] (ω : M → Orientation ℝ ℂ (Fin (1 + 1)))
  (hzφ : ∀ z, s z = 0 → z ∈ (φ z).source) {p : ℝ≥0∞} (Ω : M → Opens ℂ) (g : M → ℂ → ℝ)
  (G : M → ℂ → ℂ)

include hs in
/-- **The zero count for sections solving a weak Cauchy–Riemann inequality.** Let `M` be a
compact surface with orientation `oM`, and let `s` be a continuous section with finitely many zeros
of an oriented real plane bundle `E → M` with fibre `ℂ`. Suppose that at each zero `z` there are a
chart `φ z` and a linear trivialization `e z`, oriented compatibly with `E` and `M` near `z` as in
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`, in which `s`, read as
`f y = (e z (s ((φ z)⁻¹ y))).2`, is continuous on an open set `Ω z ∋ φ z z` with weak conjugate
Wirtinger derivative `G z` there and `‖G z‖ ≤ g z ‖f‖` almost everywhere on `Ω z`, for
`g z ∈ Lᵖ_loc(Ω z)` and `p > 2`. Then the number of zeros of `s` is at most the Euler class of `E`
evaluated on the fundamental class of `M`. -/
theorem ncard_le_evalFundamentalClass_eulerClass_of_hasWeakConjWirtingerDerivOn
    (hZ : {x | s x = 0}.Finite) (hze : ∀ z, s z = 0 → z ∈ (e z).baseSet)
    (ho : ∀ z, s z = 0 → ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ (e z).baseSet,
      (e z).mapOrientation (Fin (1 + 1)) hx (o x) = ω z)
    (hφ : ∀ z (hz : s z = 0), localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (φ z).source ↦ φ z x - φ z z,
          (φ z).continuousOn.domRestrict.sub continuous_const⟩ : C((φ z).source, ℂ))
        (S := {⟨z, hzφ z hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((φ z).injOn x.property (hzφ z hz) (sub_eq_zero.1 hx))) (1 + 1)
        (((φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ z hz⟩
          (1 + 1)).symm (oM z)).val =
      ((ω z).localOrientation hF).val)
    (hp : 2 < p) (hzΩ : ∀ z, s z = 0 → φ z z ∈ Ω z)
    (hg : ∀ z, s z = 0 → MemLpLoc p (Ω z) (g z))
    (hf : ∀ z, s z = 0 → ContinuousOn
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (Ω z))
    (hG : ∀ z, s z = 0 → HasWeakConjWirtingerDerivOn volume (Ω z)
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (G z))
    (hle : ∀ z, s z = 0 → ∀ᵐ y ∂volume.restrict (Ω z),
      ‖G z y‖ ≤ g z y * ‖(e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2‖) :
    ({x | s x = 0}.ncard : ℤ) ≤ (oM.evalFundamentalClass hF (ModuleCat.of ℤ (ULift.{0} ℤ))
      (ContinuousMap.id M) (o.eulerClass hF)).down :=
  o.ncard_le_evalFundamentalClass_eulerClass_of_eventually_eq_mul hF oM hs φ e ω hzφ hZ hze ho hφ
    fun z hz ↦ exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le hp (hg z hz)
      (hf z hz) (hG z hz) (hle z hz) (hzΩ z hz)

include hs in
/-- **The Euler number of a plane bundle with a section solving a weak Cauchy–Riemann inequality
is nonnegative.** Under the hypotheses of
`ncard_le_evalFundamentalClass_eulerClass_of_hasWeakConjWirtingerDerivOn`, which include that the
section has finitely many zeros, the Euler class of `E` evaluated on the fundamental class of `M`
is nonnegative. -/
theorem evalFundamentalClass_eulerClass_nonneg_of_hasWeakConjWirtingerDerivOn
    (hZ : {x | s x = 0}.Finite) (hze : ∀ z, s z = 0 → z ∈ (e z).baseSet)
    (ho : ∀ z, s z = 0 → ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ (e z).baseSet,
      (e z).mapOrientation (Fin (1 + 1)) hx (o x) = ω z)
    (hφ : ∀ z (hz : s z = 0), localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (φ z).source ↦ φ z x - φ z z,
          (φ z).continuousOn.domRestrict.sub continuous_const⟩ : C((φ z).source, ℂ))
        (S := {⟨z, hzφ z hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((φ z).injOn x.property (hzφ z hz) (sub_eq_zero.1 hx))) (1 + 1)
        (((φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ z hz⟩
          (1 + 1)).symm (oM z)).val =
      ((ω z).localOrientation hF).val)
    (hp : 2 < p) (hzΩ : ∀ z, s z = 0 → φ z z ∈ Ω z)
    (hg : ∀ z, s z = 0 → MemLpLoc p (Ω z) (g z))
    (hf : ∀ z, s z = 0 → ContinuousOn
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (Ω z))
    (hG : ∀ z, s z = 0 → HasWeakConjWirtingerDerivOn volume (Ω z)
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (G z))
    (hle : ∀ z, s z = 0 → ∀ᵐ y ∂volume.restrict (Ω z),
      ‖G z y‖ ≤ g z y * ‖(e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2‖) :
    0 ≤ (oM.evalFundamentalClass hF (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (o.eulerClass hF)).down :=
  o.evalFundamentalClass_eulerClass_nonneg_of_eventually_eq_mul hF oM hs φ e ω hzφ hZ hze ho hφ
    fun z hz ↦ exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le hp (hg z hz)
      (hf z hz) (hG z hz) (hle z hz) (hzΩ z hz)

end CompactSpace

section ConnectedSpace

variable [CompactSpace M] [ConnectedSpace M] (φ : M → OpenPartialHomeomorph M ℂ)
  (e : M → Trivialization ℂ (π ℂ E)) [∀ z, (e z).IsLinear ℝ] (ω : M → Orientation ℝ ℂ (Fin (1 + 1)))
  (hzφ : ∀ z, z ∈ (φ z).source) {p : ℝ≥0∞} (Ω : M → Opens ℂ) (g : M → ℂ → ℝ) (G : M → ℂ → ℂ)

include hs in
/-- **A section solving a weak Cauchy–Riemann inequality and vanishing at more points than the
Euler number vanishes identically.** Let `M` be a connected compact surface with orientation `oM`,
and let `s` be a continuous section of an oriented real plane bundle `E → M` with fibre `ℂ`.
Suppose that around every point `z` there are a chart `φ z` and a linear trivialization `e z`,
oriented compatibly with `E` and `M` near `z`, in which `s`, read as
`f y = (e z (s ((φ z)⁻¹ y))).2`, is continuous on an open set `Ω z ∋ φ z z` with weak conjugate
Wirtinger derivative `G z` there and `‖G z‖ ≤ g z ‖f‖` almost everywhere on `Ω z`, for
`g z ∈ Lᵖ_loc(Ω z)` and `p > 2`. If `s` vanishes on a finite set `S` with more elements than the
Euler class of `E` evaluated on the fundamental class of `M`, then `s` vanishes identically. -/
theorem eq_zero_of_evalFundamentalClass_eulerClass_lt_ncard_of_hasWeakConjWirtingerDerivOn
    (hze : ∀ z, z ∈ (e z).baseSet)
    (ho : ∀ z, ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ (e z).baseSet,
      (e z).mapOrientation (Fin (1 + 1)) hx (o x) = ω z)
    (hφ : ∀ z, localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (φ z).source ↦ φ z x - φ z z,
          (φ z).continuousOn.domRestrict.sub continuous_const⟩ : C((φ z).source, ℂ))
        (S := {⟨z, hzφ z⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((φ z).injOn x.property (hzφ z) (sub_eq_zero.1 hx))) (1 + 1)
        (((φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ z⟩
          (1 + 1)).symm (oM z)).val =
      ((ω z).localOrientation hF).val)
    (hp : 2 < p) (hzΩ : ∀ z, φ z z ∈ Ω z) (hg : ∀ z, MemLpLoc p (Ω z) (g z))
    (hf : ∀ z, ContinuousOn
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (Ω z))
    (hG : ∀ z, HasWeakConjWirtingerDerivOn volume (Ω z)
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (G z))
    (hle : ∀ z, ∀ᵐ y ∂volume.restrict (Ω z),
      ‖G z y‖ ≤ g z y * ‖(e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2‖)
    {S : Set M} (hS : ∀ x ∈ S, s x = 0)
    (hlt : (oM.evalFundamentalClass hF (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (o.eulerClass hF)).down < S.ncard) (x : M) : s x = 0 :=
  o.eq_zero_of_evalFundamentalClass_eulerClass_lt_ncard_of_eventually_eq_mul hF oM hs φ e ω hzφ hze
    ho hφ (fun z ↦ exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le hp (hg z)
      (hf z) (hG z) (hle z) (hzΩ z)) hS hlt x

end ConnectedSpace

end VectorBundleOrientation

end TauCeti
