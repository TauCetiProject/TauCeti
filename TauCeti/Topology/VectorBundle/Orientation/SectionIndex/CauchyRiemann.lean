/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Holomorphic

/-!
# The zero count for sections solving a Cauchy–Riemann inequality

Let `s` be a continuous section of an oriented real plane bundle `E → M` with fibre `ℂ`, over an
oriented surface `M` charted on `ℂ`. Read near a point `z` in a linear trivialization `e` and a
chart `φ`, the section becomes a function `f y = (e (s (φ⁻¹ y))).2` of `y ∈ ℂ`. Suppose that `f` is
of class `C¹` on an open set `Ω ∋ φ z` and satisfies the Cauchy–Riemann inequality

`‖\bar∂ f‖ ≤ K ‖f‖`

on `Ω`, for a locally bounded function `K`. This is what a section in the kernel of a real
Cauchy–Riemann operator `D` on a complex line bundle looks like in a holomorphic chart and a
complex frame: there `D` reads as `\bar∂ + Z` with a bounded real-linear zeroth-order term `Z`
(`TauCeti.FiniteBundleAtlas.chartZeroOrder`), so `‖\bar∂ f‖ = ‖Z f‖ ≤ ‖Z‖ ‖f‖`. The statements here
take the inequality in coordinates as their hypothesis; reading it off a bundle operator is not done
in this file. The section need not be holomorphic, but its zeros behave as if it were:

* **Positive local indices.** By the similarity principle (here in the scalar form
  `TauCeti.exists_eventually_eq_mul_of_norm_conjWirtingerDeriv_le`), near `φ z` the function `f`
  is `v * σ` for a function `v` continuous and nonzero at `φ z` and a function `σ` analytic at
  `φ z`. So, in oriented coordinates, the local index of `s` at `z` is the order of vanishing of
  `σ` at `φ z` (`sectionIndex_eq_analyticOrderNatAt_of_eventually_eq_mul` in the namespace
  `TauCeti.VectorBundleOrientation`), which is nonnegative, and positive at an isolated zero
  (`TauCeti.VectorBundleOrientation.sectionIndex_pos_of_norm_conjWirtingerDeriv_le`). The factor `v`
  is a complex number: a real-linear factor could reverse orientations, as complex conjugation,
  of local index `-1`, does.
* **The zero count.** On a compact surface, a section with finitely many zeros, each satisfying the
  inequality in oriented coordinates, has at most `⟨e(E), [M]⟩` zeros
  (`ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le` in the namespace
  `TauCeti.VectorBundleOrientation`): the Euler number is the sum of their local indices, each at
  least `1`. In particular the Euler number is nonnegative.
* **Unique continuation.** On a connected compact surface, a section satisfying the inequality in
  coordinates around every point either vanishes identically or has finitely many zeros
  (`TauCeti.finite_setOf_section_eq_zero_of_norm_conjWirtingerDeriv_le`): near each point it
  vanishes identically or has no other zero, by the similarity principle, and the set of points
  near which it vanishes is open and closed
  (`TauCeti.finite_setOf_eq_zero_of_forall_eventually`).

Together: a section satisfying the inequality everywhere which vanishes at more than `⟨e(E), [M]⟩`
points vanishes identically
(`TauCeti.VectorBundleOrientation.eq_zero_of_evalFundamentalClass_eulerClass_lt_ncard`). So, for
sections satisfying the inequality in coordinates everywhere, evaluation at `⟨e(E), [M]⟩ + 1`
distinct points is injective, and there are no nonzero such sections when `⟨e(E), [M]⟩ < 0`. This
file does not identify the Euler class with the first Chern class, nor derive the inequality from a
bundle operator. Once both are done, this becomes the statement that evaluating the kernel of a
real Cauchy–Riemann operator on a complex line bundle `L` of degree `d = c₁(L)[M]` at `d + 1`
distinct points is injective, and that this kernel is zero when `d < 0`: the inputs of automatic
transversality for line bundles.

## Main results

* `Bundle.Trivialization.eventually_eq_zero_or_eventually_ne_zero_of_norm_conjWirtingerDeriv_le`:
  a section satisfying the inequality near `z` vanishes near `z` or has no zero near `z` other than
  `z`.
* `TauCeti.VectorBundleOrientation.sectionIndex_nonneg_of_norm_conjWirtingerDeriv_le` and
  `TauCeti.VectorBundleOrientation.sectionIndex_pos_of_norm_conjWirtingerDeriv_le`: its local index
  is nonnegative, and positive at an isolated zero.
* `ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le` and
  `evalFundamentalClass_eulerClass_nonneg_of_norm_conjWirtingerDeriv_le`, in the namespace
  `TauCeti.VectorBundleOrientation`: the number of zeros is at most the Euler number, which is
  therefore nonnegative.
* `TauCeti.finite_setOf_section_eq_zero_of_norm_conjWirtingerDeriv_le`: on a connected compact
  surface, a section which is not identically zero has finitely many zeros, by
  `TauCeti.finite_setOf_eq_zero_of_forall_eventually`, which needs only that near every point the
  section vanishes identically or has no other zero.
* `TauCeti.VectorBundleOrientation.eq_zero_of_evalFundamentalClass_eulerClass_lt_ncard`: a section
  vanishing at more points than the Euler number vanishes identically.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52 (2012), Theorem 2.3.5 (the similarity principle) and the proof of
  Theorem C.1.10 (iii) (the zeros of a section in the kernel of a real Cauchy–Riemann operator on a
  line bundle are isolated, of positive order, and counted by the first Chern number).
* H. Hofer, V. Lizan, J.-C. Sikorav, *On genericity for holomorphic curves in four-dimensional
  almost-complex manifolds*, J. Geom. Anal. 7 (1997), 149–159 (automatic transversality from the
  zero count).
-/

public section

noncomputable section

open Bundle CategoryTheory Filter Module Set Topology

namespace Bundle.Trivialization

open TauCeti

variable {M : Type} [TopologicalSpace M] {E : M → Type} [TopologicalSpace (TotalSpace ℂ E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)] (e : Trivialization ℂ (π ℂ E))
  [e.IsLinear ℝ] (φ : OpenPartialHomeomorph M ℂ) {z : M} {s : ∀ x, E x}

/-- **A section solving a Cauchy–Riemann inequality vanishes near a point or has no other zero near
it.** Let `e` be a linear trivialization of a real plane bundle `E` with fibre `ℂ` and `φ` a chart
of `M` with values in `ℂ`, both defined at `z`. If the section `s`, read in these coordinates as
`f y = (e (s (φ⁻¹ y))).2`, is of class `C¹` on an open set `Ω ∋ φ z` and satisfies
`‖\bar∂ f‖ ≤ K ‖f‖` there, for a locally bounded `K`, then either `s` vanishes on a neighbourhood of
`z`, or `s` does not vanish on a punctured neighbourhood of `z`. -/
theorem eventually_eq_zero_or_eventually_ne_zero_of_norm_conjWirtingerDeriv_le
    (hze : z ∈ e.baseSet) (hzφ : z ∈ φ.source) {Ω : Set ℂ} (hΩ : IsOpen Ω) (hzΩ : φ z ∈ Ω)
    (hf : ContDiffOn ℝ 1 (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) Ω)
    {K : ℂ → ℝ} (hK : ∀ y ∈ Ω, ∃ B, ∀ᶠ w in 𝓝 y, K w ≤ B)
    (hfK : ∀ y ∈ Ω, ‖conjWirtingerDeriv
        (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) y‖ ≤
      K y * ‖(e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2‖) :
    (∀ᶠ x in 𝓝 z, s x = 0) ∨ ∀ᶠ x in 𝓝[≠] z, s x ≠ 0 := by
  obtain ⟨v, σ, hv, hv₀, hσ, hfac⟩ :=
    exists_eventually_eq_mul_of_norm_conjWirtingerDeriv_le hΩ hf hK hfK hzΩ
  exact e.eventually_eq_zero_or_eventually_ne_zero_of_eventually_eq_mul φ hze hzφ hv hv₀ hσ hfac

end Bundle.Trivialization

namespace TauCeti

section Finite

/-- **A function which vanishes identically or has no other zero near each point has finitely many
zeros.** Let `M` be a connected compact space and `s` a dependent function on `M` with values in
types with a zero, such as a section of a bundle. If near every point `x` either `s` vanishes
identically, or `s` has no zero other than possibly `x`, and `s` does not vanish identically, then
`s` has finitely many zeros. -/
theorem finite_setOf_eq_zero_of_forall_eventually {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [ConnectedSpace M] {E : M → Type*} [∀ x, Zero (E x)] {s : ∀ x, E x}
    (hdich : ∀ x, (∀ᶠ y in 𝓝 x, s y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, s y ≠ 0) (hne : ∃ x, s x ≠ 0) :
    {x | s x = 0}.Finite := by
  -- The set `A` of points near which `s` vanishes is open, and closed: near a point outside `A`,
  -- `s` vanishes at most at that point.
  set A := {x | ∀ᶠ y in 𝓝 x, s y = 0}
  have hAc : IsOpen Aᶜ := isOpen_iff_mem_nhds.2 fun x hx ↦ by
    have h := eventually_nhdsWithin_iff.1 ((hdich x).resolve_left hx)
    filter_upwards [h] with y hy hyA
    by_cases hyx : y = x
    · exact hx (hyx ▸ hyA)
    · exact hy hyx hyA.self_of_nhds
  -- Since `M` is connected and `s` does not vanish identically, `A` is empty.
  have hA : A = ∅ := by
    refine (isClopen_iff.1 ⟨isOpen_compl_iff.1 hAc, isOpen_setOfPred_eventually_nhds⟩).resolve_right
      fun hA ↦ ?_
    obtain ⟨x, hx⟩ := hne
    exact hx (hA ▸ mem_univ x : x ∈ A).self_of_nhds
  -- So the zeros of `s` are isolated, and a codiscrete subset of a compact space is cofinite.
  have h : {y | s y ≠ 0} ∈ codiscrete M := mem_codiscrete_iff_forall_mem_nhdsNE.2 fun x ↦
    (hdich x).resolve_left (show x ∉ A by rw [hA]; exact notMem_empty x)
  simpa [compl_ofPred] using cofinite_le_codiscrete h

variable {M : Type} [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M] {E : M → Type}
  [TopologicalSpace (TotalSpace ℂ E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  {s : ∀ x, E x}

/-- **Unique continuation for sections solving a Cauchy–Riemann inequality.** Let `M` be a
connected compact space and `s` a section of a real plane bundle `E → M` with fibre `ℂ`. Suppose
that around every point `z` there are a chart `φ z` and a linear trivialization `e z` in which `s`,
read as `f y = (e z (s ((φ z)⁻¹ y))).2`, is of class `C¹` on an open set `Ω z ∋ φ z z` and
satisfies `‖\bar∂ f‖ ≤ K z ‖f‖` there, for a locally bounded `K z`. If `s` does not vanish
identically, it has finitely many zeros. -/
theorem finite_setOf_section_eq_zero_of_norm_conjWirtingerDeriv_le
    (φ : M → OpenPartialHomeomorph M ℂ)
    (e : M → Trivialization ℂ (π ℂ E)) [∀ z, (e z).IsLinear ℝ] (hzφ : ∀ z, z ∈ (φ z).source)
    (hze : ∀ z, z ∈ (e z).baseSet) (Ω : M → Set ℂ) (hΩ : ∀ z, IsOpen (Ω z))
    (hzΩ : ∀ z, φ z z ∈ Ω z)
    (hf : ∀ z, ContDiffOn ℝ 1
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (Ω z))
    (K : M → ℂ → ℝ) (hK : ∀ z, ∀ y ∈ Ω z, ∃ B, ∀ᶠ w in 𝓝 y, K z w ≤ B)
    (hfK : ∀ z, ∀ y ∈ Ω z, ‖conjWirtingerDeriv
        (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) y‖ ≤
      K z y * ‖(e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2‖)
    (hne : ∃ x, s x ≠ 0) : {x | s x = 0}.Finite :=
  finite_setOf_eq_zero_of_forall_eventually (fun x ↦
    (e x).eventually_eq_zero_or_eventually_ne_zero_of_norm_conjWirtingerDeriv_le (φ x) (hze x)
      (hzφ x) (hΩ x) (hzΩ x) (hf x) (hK x) (hfK x)) hne

end Finite

namespace VectorBundleOrientation

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] {E : M → Type}
  [TopologicalSpace (TotalSpace ℂ E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle ℂ E] [VectorBundle ℝ ℂ E]
  (o : VectorBundleOrientation ℂ E (Fin (1 + 1))) (hF : finrank ℝ ℂ = 1 + 1)
  (oM : HomologicalOrientation M ℂ (1 + 1)) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' ℂ x (s x))

section Local

variable (e : Trivialization ℂ (π ℂ E)) [e.IsLinear ℝ]

/-- **The local index of a section solving a Cauchy–Riemann inequality is nonnegative.** Let `e` be
a linear trivialization of a real plane bundle `E` with fibre `ℂ` and `φ` a chart of `M` with
values in `ℂ`, both defined at `z`, oriented compatibly with `E` and `M` near `z` as in
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`. If the section, read in these
coordinates as `f y = (e (s (φ⁻¹ y))).2`, is of class `C¹` on an open set `Ω ∋ φ z` and satisfies
`‖\bar∂ f‖ ≤ K ‖f‖` there, for a locally bounded `K`, then the local index of `s` at `z` is
nonnegative: it is the order of vanishing of the holomorphic factor of `f`. -/
theorem sectionIndex_nonneg_of_norm_conjWirtingerDeriv_le (φ : OpenPartialHomeomorph M ℂ) {z : M}
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
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hzΩ : φ z ∈ Ω)
    (hf : ContDiffOn ℝ 1 (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) Ω)
    {K : ℂ → ℝ} (hK : ∀ y ∈ Ω, ∃ B, ∀ᶠ w in 𝓝 y, K w ≤ B)
    (hfK : ∀ y ∈ Ω, ‖conjWirtingerDeriv
        (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) y‖ ≤
      K y * ‖(e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2‖) :
    0 ≤ o.sectionIndex hF oM hs z := by
  obtain ⟨v, σ, hv, hv₀, hσ, hfac⟩ :=
    exists_eventually_eq_mul_of_norm_conjWirtingerDeriv_le hΩ hf hK hfK hzΩ
  rw [o.sectionIndex_eq_analyticOrderNatAt_of_eventually_eq_mul hF oM hs e φ hze hzφ ho hφ hv hv₀
    hσ hfac]
  exact Nat.cast_nonneg _

/-- **The local index of a section at an isolated zero solving a Cauchy–Riemann inequality is
positive.** Under the hypotheses of
`TauCeti.VectorBundleOrientation.sectionIndex_nonneg_of_norm_conjWirtingerDeriv_le`, if `z` is an
isolated zero of `s`, the local index of `s` at `z` is positive. -/
theorem sectionIndex_pos_of_norm_conjWirtingerDeriv_le (φ : OpenPartialHomeomorph M ℂ) {z : M}
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
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hzΩ : φ z ∈ Ω)
    (hf : ContDiffOn ℝ 1 (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) Ω)
    {K : ℂ → ℝ} (hK : ∀ y ∈ Ω, ∃ B, ∀ᶠ w in 𝓝 y, K w ≤ B)
    (hfK : ∀ y ∈ Ω, ‖conjWirtingerDeriv
        (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) y‖ ≤
      K y * ‖(e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2‖)
    (hsz : s z = 0) (hiso : ∀ᶠ x in 𝓝[≠] z, s x ≠ 0) :
    0 < o.sectionIndex hF oM hs z := by
  obtain ⟨v, σ, hv, hv₀, hσ, hfac⟩ :=
    exists_eventually_eq_mul_of_norm_conjWirtingerDeriv_le hΩ hf hK hfK hzΩ
  exact o.sectionIndex_pos_of_eventually_eq_mul hF oM hs e φ hze hzφ ho hφ hv hv₀ hσ hfac hsz hiso

end Local

section CompactSpace

variable [CompactSpace M] (φ : M → OpenPartialHomeomorph M ℂ) (e : M → Trivialization ℂ (π ℂ E))
  [∀ z, (e z).IsLinear ℝ] (ω : M → Orientation ℝ ℂ (Fin (1 + 1)))
  (hzφ : ∀ z, s z = 0 → z ∈ (φ z).source) (Ω : M → Set ℂ) (K : M → ℂ → ℝ)

include hs in
/-- **The zero count.** Let `M` be a compact surface with orientation `oM`, and let `s` be a
continuous section with finitely many zeros of an oriented real plane bundle `E → M` with fibre
`ℂ`. Suppose that at each zero `z` there are a chart `φ z` and a linear trivialization `e z`,
oriented compatibly with `E` and `M` near `z` as in
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`, in which `s`, read as
`f y = (e z (s ((φ z)⁻¹ y))).2`, is of class `C¹` on an open set `Ω z ∋ φ z z` and satisfies
`‖\bar∂ f‖ ≤ K z ‖f‖` there, for a locally bounded `K z`. Then the number of zeros of `s` is at most
the Euler class of `E` evaluated on the fundamental class of `M`: the Euler number is the sum of
the local indices of the zeros, each a positive integer. -/
theorem ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le
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
    (hΩ : ∀ z, s z = 0 → IsOpen (Ω z)) (hzΩ : ∀ z, s z = 0 → φ z z ∈ Ω z)
    (hf : ∀ z, s z = 0 → ContDiffOn ℝ 1
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (Ω z))
    (hK : ∀ z, s z = 0 → ∀ y ∈ Ω z, ∃ B, ∀ᶠ w in 𝓝 y, K z w ≤ B)
    (hfK : ∀ z, s z = 0 → ∀ y ∈ Ω z, ‖conjWirtingerDeriv
        (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) y‖ ≤
      K z y * ‖(e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2‖) :
    ({x | s x = 0}.ncard : ℤ) ≤ (oM.evalFundamentalClass hF (ModuleCat.of ℤ (ULift.{0} ℤ))
      (ContinuousMap.id M) (o.eulerClass hF)).down := by
  rw [o.evalFundamentalClass_eulerClass_eq_sum_sectionIndex hF oM hs hF hZ,
    ncard_eq_toFinset_card _ hZ, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun z hz ↦ ?_
  have hz0 : s z = 0 := hZ.mem_toFinset.1 hz
  -- A zero of a section with finitely many zeros is isolated.
  have hiso : ∀ᶠ x in 𝓝[≠] z, s x ≠ 0 := by
    have hcl : IsClosed ({x | s x = 0} \ {z}) := (hZ.subset sdiff_subset).isClosed
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (hcl.isOpen_compl.mem_nhds fun h ↦ h.2 rfl), self_mem_nhdsWithin] with x hx hxz h0
    exact hx ⟨h0, hxz⟩
  have := o.sectionIndex_pos_of_norm_conjWirtingerDeriv_le hF oM hs (e z) (φ z) (hze z hz0)
    (hzφ z hz0) (ho z hz0) (hφ z hz0) (hΩ z hz0) (hzΩ z hz0) (hf z hz0) (hK z hz0) (hfK z hz0)
    hz0 hiso
  omega

include hs in
/-- **The Euler number of a plane bundle with a section solving a Cauchy–Riemann inequality is
nonnegative.** Under the hypotheses of
`ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le`, which include that the
section has finitely many zeros, the Euler class of `E` evaluated on the fundamental class of `M`
is nonnegative. -/
theorem evalFundamentalClass_eulerClass_nonneg_of_norm_conjWirtingerDeriv_le
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
    (hΩ : ∀ z, s z = 0 → IsOpen (Ω z)) (hzΩ : ∀ z, s z = 0 → φ z z ∈ Ω z)
    (hf : ∀ z, s z = 0 → ContDiffOn ℝ 1
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (Ω z))
    (hK : ∀ z, s z = 0 → ∀ y ∈ Ω z, ∃ B, ∀ᶠ w in 𝓝 y, K z w ≤ B)
    (hfK : ∀ z, s z = 0 → ∀ y ∈ Ω z, ‖conjWirtingerDeriv
        (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) y‖ ≤
      K z y * ‖(e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2‖) :
    0 ≤ (oM.evalFundamentalClass hF (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (o.eulerClass hF)).down :=
  (Nat.cast_nonneg _).trans
    (o.ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le hF oM hs φ e ω hzφ Ω
      K hZ hze ho hφ hΩ hzΩ hf hK hfK)

end CompactSpace

section ConnectedSpace

variable [CompactSpace M] [ConnectedSpace M] (φ : M → OpenPartialHomeomorph M ℂ)
  (e : M → Trivialization ℂ (π ℂ E)) [∀ z, (e z).IsLinear ℝ] (ω : M → Orientation ℝ ℂ (Fin (1 + 1)))
  (hzφ : ∀ z, z ∈ (φ z).source) (Ω : M → Set ℂ) (K : M → ℂ → ℝ)

include hs in
/-- **A section solving a Cauchy–Riemann inequality and vanishing at more points than the Euler
number vanishes identically.** Let `M` be a connected compact surface with orientation `oM`, and
let `s` be a continuous section of an oriented real plane bundle `E → M` with fibre `ℂ`. Suppose
that around every point `z` there are a chart `φ z` and a linear trivialization `e z`, oriented
compatibly with `E` and `M` near `z` as in
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`, in which `s`, read as
`f y = (e z (s ((φ z)⁻¹ y))).2`, is of class `C¹` on an open set `Ω z ∋ φ z z` and satisfies
`‖\bar∂ f‖ ≤ K z ‖f‖` there, for a locally bounded `K z`. If `s` vanishes on a set `S` with more
elements than the Euler class of `E` evaluated on the fundamental class of `M`, then `s` vanishes
identically. -/
theorem eq_zero_of_evalFundamentalClass_eulerClass_lt_ncard (hze : ∀ z, z ∈ (e z).baseSet)
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
    (hΩ : ∀ z, IsOpen (Ω z)) (hzΩ : ∀ z, φ z z ∈ Ω z)
    (hf : ∀ z, ContDiffOn ℝ 1
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (Ω z))
    (hK : ∀ z, ∀ y ∈ Ω z, ∃ B, ∀ᶠ w in 𝓝 y, K z w ≤ B)
    (hfK : ∀ z, ∀ y ∈ Ω z, ‖conjWirtingerDeriv
        (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) y‖ ≤
      K z y * ‖(e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2‖)
    {S : Set M} (hS : ∀ x ∈ S, s x = 0)
    (hlt : (oM.evalFundamentalClass hF (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (o.eulerClass hF)).down < S.ncard) (x : M) : s x = 0 := by
  by_contra hx
  have hZ := finite_setOf_section_eq_zero_of_norm_conjWirtingerDeriv_le φ e hzφ hze Ω hΩ hzΩ hf K
    hK hfK ⟨x, hx⟩
  have hle := o.ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le hF oM hs φ e
    ω (fun z _ ↦ hzφ z) Ω K hZ (fun z _ ↦ hze z) (fun z _ ↦ ho z) (fun z _ ↦ hφ z)
    (fun z _ ↦ hΩ z) (fun z _ ↦ hzΩ z) (fun z _ ↦ hf z) (fun z _ ↦ hK z) (fun z _ ↦ hfK z)
  have hSZ : S.ncard ≤ {x | s x = 0}.ncard := ncard_le_ncard hS hZ
  omega

end ConnectedSpace

end VectorBundleOrientation

end TauCeti
