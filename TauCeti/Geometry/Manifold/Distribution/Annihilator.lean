/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse

/-!
# Annihilating covectors of distributions and the involutivity criterion

A tangent vector outside a smooth distribution is detected by a smooth covector field defined near
the base point, vanishing nowhere there and annihilating the distribution there. The covectors are
sections of the existing bundle of continuous linear maps from the tangent bundle to the scalar
field. In particular a smooth hyperplane distribution is locally the kernel of a nowhere-zero
smooth covector field. No global coorientation is assumed: the section is constructed only on a
neighborhood of the chosen point.

In tangent-bundle coordinates, a local frame gives an injective operator `A`. A fixed left
inverse `P` of its value at the chosen point gives the nearby left inverse `(P A)⁻¹ P`.
The projection `1 - A (P A)⁻¹ P` then turns a covector annihilating the frame at the chosen point
into a smooth covector field annihilating the frame nearby. Nonvanishing is open, and for a
hyperplane field the rank of the distribution makes its inclusion in the kernel an equality.

On a Hausdorff manifold a bump function extends these local one-forms to global smooth one-forms
annihilating the distribution everywhere. Together with the invariant formula
`dα(V, W) = V(α W) - W(α V) - α [V, W]`, this gives the dual description of involutivity: a
smooth distribution `D` is involutive exactly when `dα` vanishes on `D` for every smooth one-form
`α` annihilating `D` (`TauCeti.isInvolutiveDistribution_iff_forall_mextDeriv`).

## Main results

* `TauCeti.IsContMDiffDistribution.exists_local_annihilator_apply_ne_zero`: a vector outside a
  `C^n` distribution is detected by a local `C^n` covector field annihilating the distribution.
* `TauCeti.IsContMDiffDistribution.exists_local_annihilator`: a `C^n` hyperplane distribution is
  locally the kernel of a nowhere-zero `C^n` covector field.
* `TauCeti.IsContMDiffDistribution.exists_roughForm_apply_ne_zero` and
  `TauCeti.IsContMDiffDistribution.exists_roughForm_ker_eq`: the same statements for local
  real one-forms.
* `TauCeti.IsContMDiffDistribution.exists_isSmoothForm_apply_ne_zero`: on a Hausdorff manifold,
  a vector outside a smooth distribution is detected by a global smooth one-form annihilating it.
* `TauCeti.IsInvolutiveDistribution.mextDeriv_apply_eq_zero`: for an involutive `C¹` distribution,
  the exterior derivative of a one-form annihilating it near a point vanishes on it there.
* `TauCeti.isInvolutiveDistribution_iff_forall_mextDeriv`: a smooth distribution on a Hausdorff
  manifold is involutive exactly when the exterior derivative of every smooth one-form
  annihilating it vanishes on it.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 19 (local defining
  forms for distributions, and the characterization of involutivity by annihilating one-forms).
* H. Geiges, *An Introduction to Contact Topology*, Section 1.1 (local contact forms).
-/

public section

noncomputable section

open Bundle Set Filter Function Module VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

section Annihilator

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {k : ℕ} {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

/-- A tangent vector `u` outside a `C^n` distribution `D` is detected by a covector field which,
on an open neighborhood of the base point, is `C^n`, vanishes nowhere and annihilates `D`. The
covector is a section of the usual hom bundle; its regularity, nonvanishing and annihilation are
asserted only on the open neighborhood, not outside it. -/
theorem IsContMDiffDistribution.exists_local_annihilator_apply_ne_zero
    (hD : IsContMDiffDistribution I n k D) {x : M} {u : TangentSpace I x} (hu : u ∉ D x) :
    ∃ (U : Set M) (α : Π y : M, TangentSpace I y →L[𝕜] 𝕜),
      IsOpen U ∧ x ∈ U ∧
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
        (fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) y (α y)) U ∧
      α x u ≠ 0 ∧ ∀ y ∈ U, α y ≠ 0 ∧ D y ≤ LinearMap.ker (α y).toLinearMap := by
  classical
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  -- Read a local frame in one fixed tangent-bundle trivialization.
  obtain ⟨V, hV, hxV, X, hX⟩ := isContMDiffDistribution_iff.mp hD x
  let e := trivializationAt E (TangentSpace I) x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  let A := IsSubbundleFrameOn.trivOperator 𝕜 E X x
  have hA := hX.contMDiffOn_trivOperator x
  have hAx := hX.isSubbundleFrameOn.injective_trivOperator hxV
  obtain ⟨p, hp⟩ := (A x).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hAx)
  let P := p.toContinuousLinearMap
  have hP : LeftInverse P (A x) := fun v ↦ LinearMap.congr_fun hp v
  -- Read in the trivialization, `u` lies outside the range of the frame operator at `x`.
  have hux : (e ⟨x, u⟩).2 ∉ LinearMap.range (A x).toLinearMap := by
    rintro ⟨c, hc⟩
    apply hu
    have h : (e ⟨x, ∑ i, c i • X i x⟩).2 = (e ⟨x, u⟩).2 := by
      rw [← IsSubbundleFrameOn.trivOperator_apply hxe]
      exact hc
    have h' := (e.continuousLinearEquivAt 𝕜 x hxe).injective
      (by simpa [Trivialization.continuousLinearEquivAt_apply] using h)
    rw [← h', ← hX.span_eq hxV]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨a, ha, haA⟩ := Submodule.exists_le_ker_of_notMem hux
  let a' := a.toContinuousLinearMap
  have ha'A : a' ∘L A x = 0 := by
    ext c
    exact haA (LinearMap.mem_range_self _ c)
  have ha' : a' ≠ 0 := fun hz ↦ ha (by simpa [a'] using congr($hz (e ⟨x, u⟩).2))
  -- Project the covector `a` at x to the annihilators of the nearby frame images.
  obtain ⟨U, hU, hxU, hUS, hc, hUc⟩ :=
    hA.exists_isOpen_contMDiffOn_sub_comp_inverse_comp (hV.inter e.open_baseSet) ⟨hxV, hxe⟩ hP
      ha' ha'A
  let c : M → E →L[𝕜] 𝕜 := fun y ↦ a' - a' ∘L A y ∘L (P ∘L A y).inverse ∘L P
  have hcx : c x = a' := by
    dsimp only [c]
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, ha'A]
    simp
  let α : Π y : M, TangentSpace I y →L[𝕜] 𝕜 :=
    fun y ↦ c y ∘L e.continuousLinearMapAt 𝕜 y
  refine ⟨U, α, hU, hxU, ?_, ?_, ?_⟩
  -- The cotangent-bundle coordinates of α are exactly the smooth covectors c.
  · exact CotangentBundle.contMDiffOn_mk_comp_continuousLinearMapAt x
      (U := U) (c := c) (fun _ hy ↦ (hUS hy).2) hc
  · have heval : α x u = c x (e ⟨x, u⟩).2 :=
      congrArg (c x) (e.continuousLinearMapAt_apply_of_mem 𝕜 hxe u)
    rw [heval, hcx]
    simpa [a'] using ha
  · intro y hy
    have hcy : c y ≠ 0 := (hUc y hy).2
    have hαy : α y ≠ 0 := by
      intro hz
      apply hcy
      ext v
      have := congrArg (fun f : TangentSpace I y →L[𝕜] 𝕜 ↦ f (e.symmL 𝕜 y v)) hz
      simpa [α, e.continuousLinearMapAt_symmL (hUS hy).2] using this
    refine ⟨hαy, ?_⟩
    -- The frame spans `D y` and is annihilated by `α y`.
    rw [← hX.span_eq (hUS hy).1]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hzero : c y ∘L A y = 0 :=
      a'.sub_comp_inverse_comp_comp_eq_zero (A y) P (hUc y hy).1
    have hAi := IsSubbundleFrameOn.trivOperator_apply (𝕜 := 𝕜) (X := X) (hUS hy).2
      (Pi.single i (1 : 𝕜))
    have heval : α y (X i y) = c y (e ⟨y, X i y⟩).2 :=
      congrArg (c y) (e.continuousLinearMapAt_apply_of_mem 𝕜 (hUS hy).2 (X i y))
    have hzeroi : α y (X i y) = 0 := by
      rw [heval]
      simpa [A, hAi, e] using
        congrArg (fun f : (Fin k → 𝕜) →L[𝕜] 𝕜 ↦ f (Pi.single i 1)) hzero
    exact hzeroi

/-- A `C^n` hyperplane distribution is locally the kernel of a nowhere-zero `C^n` covector
field. The covector is a section of the usual hom bundle; its regularity and nonvanishing
are asserted only on the open neighborhood, not outside it. -/
theorem IsContMDiffDistribution.exists_local_annihilator
    (hD : IsContMDiffDistribution I n k D) (hk : k + 1 = finrank 𝕜 E) (x : M) :
    ∃ (U : Set M) (α : Π y : M, TangentSpace I y →L[𝕜] 𝕜),
      IsOpen U ∧ x ∈ U ∧
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
        (fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) y (α y)) U ∧
      ∀ y ∈ U, α y ≠ 0 ∧ LinearMap.ker (α y).toLinearMap = D y := by
  -- A hyperplane is a proper subspace, so some tangent vector lies outside it.
  obtain ⟨u, -, hu⟩ := IsConcreteLE.exists_of_lt
    (Submodule.lt_top_of_finrank_lt_finrank (s := D x)
      (by rw [hD.finrank_eq x, finrank_tangentSpace]; omega))
  obtain ⟨U, α, hU, hxU, hα, -, hαD⟩ := hD.exists_local_annihilator_apply_ne_zero hu
  -- Annihilation gives inclusion; codimension one upgrades it to equality.
  exact ⟨U, α, hU, hxU, hα, fun y hy ↦ ⟨(hαD y hy).1,
    Module.Dual.ker_eq_of_le_of_finrank_add_one (α y).toLinearMap
      (fun hz ↦ (hαD y hy).1 (ContinuousLinearMap.coe_injective hz)) (hαD y hy).2
      (by rw [hD.finrank_eq y, finrank_tangentSpace, hk])⟩⟩

end Annihilator

/-! ### Local defining one-forms -/

section RoughForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- **A vector outside a distribution is detected by a local annihilating one-form.** For a
tangent vector `u` outside a `C^n` distribution `D`, the base point has an open neighbourhood `U`
carrying a one-form `α` of class `C^n` on `U` which vanishes nowhere on `U`, annihilates `D` on
`U`, and does not vanish on `u`. -/
theorem IsContMDiffDistribution.exists_roughForm_apply_ne_zero
    (hD : IsContMDiffDistribution I n k D) {x : M} {u : TangentSpace I x} (hu : u ∉ D x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ α : RoughForm I M ℝ 1,
      ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U ∧
      α x ![u] ≠ 0 ∧ ∀ y ∈ U, α y ≠ 0 ∧ D y ≤ α.ker y := by
  obtain ⟨U, a, hU, hxU, ha, hau, haD⟩ := hD.exists_local_annihilator_apply_ne_zero hu
  -- The covector field `a` is the one-form `α`, with the same kernel and regularity.
  let α : RoughForm I M ℝ 1 :=
    fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) ℝ (0 : Fin 1) (a y)
  have hαa (y : M) (v : TangentSpace I y) : α y ![v] = a y v := by simp [α]
  refine ⟨U, hU, hxU, α, fun y hy ↦ ?_, by rwa [hαa], fun y hy ↦ ⟨fun h ↦ (haD y hy).1 <|
    ContinuousLinearMap.ext fun v ↦ by simpa [hαa] using congr($h ![v]), fun v hv ↦ ?_⟩⟩
  · exact ((contMDiffAt_ofSubsingleton_iff (V := Bundle.Trivial M ℝ)).2
      ((ha y hy).contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt
  · rw [RoughForm.mem_ker, hαa]
    exact (haD y hy).2 hv

/-- **A hyperplane field is locally the kernel of a one-form.** Every point of a `C^n` distribution
`D` of rank `k` with `k + 1 = dim E` has an open neighbourhood `U` on which `D` is the kernel of a
one-form `α` of class `C^n` on `U` which vanishes nowhere on `U`. No coorientation is assumed: the
form is only defined near the chosen point. -/
theorem IsContMDiffDistribution.exists_roughForm_ker_eq
    (hD : IsContMDiffDistribution I n k D) (hk : k + 1 = finrank ℝ E) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ α : RoughForm I M ℝ 1,
      ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U ∧
      ∀ y ∈ U, α y ≠ 0 ∧ α.ker y = D y := by
  obtain ⟨u, -, hu⟩ := IsConcreteLE.exists_of_lt
    (Submodule.lt_top_of_finrank_lt_finrank (s := D x)
      (by rw [hD.finrank_eq x, finrank_tangentSpace]; omega))
  obtain ⟨U, hU, hxU, α, hα, -, hαD⟩ := hD.exists_roughForm_apply_ne_zero hu
  refine ⟨U, hU, hxU, α, hα, fun y hy ↦ ⟨(hαD y hy).1, ?_⟩⟩
  -- Annihilation gives inclusion; codimension one upgrades it to equality.
  have hne : α.eval y ≠ 0 := fun h ↦ (hαD y hy).1 <|
    RoughForm.ker_eq_top_iff.mp (by rw [RoughForm.ker_eq_ker_eval, h, LinearMap.ker_zero])
  rw [RoughForm.ker_eq_ker_eval]
  exact Module.Dual.ker_eq_of_le_of_finrank_add_one (α.eval y) hne
    (by rw [← RoughForm.ker_eq_ker_eval]; exact (hαD y hy).2)
    (by rw [hD.finrank_eq y, finrank_tangentSpace, hk])

end RoughForm

/-! ### Global annihilating one-forms and involutivity -/

section Involutive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- **A vector outside a distribution is detected by a global annihilating one-form.** On a
Hausdorff manifold, for a tangent vector `u` outside a smooth distribution `D`, some smooth
one-form annihilates `D` at every point and does not vanish on `u`. -/
theorem IsContMDiffDistribution.exists_isSmoothForm_apply_ne_zero [T2Space M] [IsManifold I ∞ M]
    (hD : IsContMDiffDistribution I ∞ k D) {x : M} {u : TangentSpace I x} (hu : u ∉ D x) :
    ∃ α : RoughForm I M ℝ 1, IsSmoothForm I ∞ α ∧ α x ![u] ≠ 0 ∧ ∀ y, D y ≤ α.ker y := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  obtain ⟨U, hU, hxU, α, hα, hαu, hαD⟩ := hD.exists_roughForm_apply_ne_zero hu
  obtain ⟨ρ, -, hρU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hU.mem_nhds hxU)
  refine ⟨fun y ↦ ρ y • α y, ?_, by simpa [ρ.eventuallyEq_one.eq_of_nhds] using hαu,
    fun y v hv ↦ ?_⟩
  · rw [isSmoothForm_def]
    exact ρ.contMDiff.contMDiffOn.smul_section_of_tsupport hU hρU hα
  · -- Outside `U` the bump function vanishes; inside `U` the form `α` annihilates `D`.
    rw [RoughForm.mem_ker]
    by_cases hy : y ∈ U
    · simp [RoughForm.mem_ker.mp ((hαD y hy).2 hv)]
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (hρU h)]

section Local

variable {n : ℕ∞ω} [IsManifold I 1 M]

omit [FiniteDimensional ℝ E] in
/-- **Involutive distributions are annihilated by the exterior derivatives of their annihilators.**
If a `C^n` distribution `D`, with `n ≠ 0`, is involutive and a one-form `α` differentiable at `x`
annihilates `D` near `x`, then `dα_x (v, w) = 0` for all `v` and `w` in `D x`. No
finite-dimensionality is needed. -/
theorem IsInvolutiveDistribution.mextDeriv_apply_eq_zero (hDi : IsInvolutiveDistribution I D)
    (hD : IsContMDiffDistribution I n k D) (hn : n ≠ 0) {α : RoughForm I M ℝ 1} {x : M}
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hαD : ∀ᶠ y in 𝓝 x, D y ≤ α.ker y) {v w : TangentSpace I x} (hv : v ∈ D x)
    (hw : w ∈ D x) : mextDeriv α x ![v, w] = 0 := by
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.mp hD x
  let V := hX.extend hxU ⟨v, hv⟩
  let W := hX.extend hxU ⟨w, hw⟩
  have hVU := (hX.contMDiffOn_extend hxU ⟨v, hv⟩).mdifferentiableOn hn
  have hWU := (hX.contMDiffOn_extend hxU ⟨w, hw⟩).mdifferentiableOn hn
  have hVD (y : M) (hy : y ∈ U) : V y ∈ D y := hX.extend_mem hxU _ hy
  have hWD (y : M) (hy : y ∈ U) : W y ∈ D y := hX.extend_mem hxU _ hy
  have hUx : U ∈ 𝓝 x := hU.mem_nhds hxU
  have hVα : ∀ᶠ y in 𝓝 x, V y ∈ α.ker y := by
    filter_upwards [hαD, hUx] with y hy hyU using hy (hVD y hyU)
  have hWα : ∀ᶠ y in 𝓝 x, W y ∈ α.ker y := by
    filter_upwards [hαD, hUx] with y hy hyU using hy (hWD y hyU)
  have h := RoughForm.apply_mlieBracket_eq_neg_mextDeriv hα
    ((hVU x hxU).mdifferentiableAt hUx) ((hWU x hxU).mdifferentiableAt hUx) hVα hWα
  -- The bracket is tangent to `D`, hence annihilated by `α`.
  have hbr : α x ![mlieBracket I V W x] = 0 :=
    RoughForm.mem_ker.mp (hαD.self_of_nhds (hDi.mlieBracket_mem hU hVU hWU hVD hWD hxU))
  rwa [hbr, eq_comm, neg_eq_zero, hX.extend_apply_self, hX.extend_apply_self] at h

end Local

/-- **Involutivity through annihilating one-forms.** A smooth distribution `D` on a Hausdorff
manifold is involutive exactly when, for every smooth one-form `α` annihilating `D`, the
exterior derivative `dα` vanishes on pairs of vectors of `D`. -/
theorem isInvolutiveDistribution_iff_forall_mextDeriv [T2Space M] [IsManifold I ∞ M]
    (hD : IsContMDiffDistribution I ∞ k D) :
    IsInvolutiveDistribution I D ↔ ∀ α : RoughForm I M ℝ 1, IsSmoothForm I ∞ α →
      (∀ x, D x ≤ α.ker x) → ∀ x, ∀ v ∈ D x, ∀ w ∈ D x, mextDeriv α x ![v, w] = 0 := by
  refine ⟨fun hDi α hα hαD x v hv w hw ↦ hDi.mextDeriv_apply_eq_zero hD (by simp)
    (hα.contMDiff.mdifferentiableAt (by simp)) (Eventually.of_forall hαD) hv hw, fun h ↦ ?_⟩
  rw [isInvolutiveDistribution_iff]
  intro U hU V W hV hW hVD hWD x hx
  by_contra hbr
  -- A global annihilating form not vanishing on the bracket contradicts the invariant formula.
  obtain ⟨α, hα, hαbr, hαD⟩ := hD.exists_isSmoothForm_apply_ne_zero hbr
  have hUx : U ∈ 𝓝 x := hU.mem_nhds hx
  have hVα : ∀ᶠ y in 𝓝 x, V y ∈ α.ker y := by
    filter_upwards [hUx] with y hy using hαD y (hVD y hy)
  have hWα : ∀ᶠ y in 𝓝 x, W y ∈ α.ker y := by
    filter_upwards [hUx] with y hy using hαD y (hWD y hy)
  rw [RoughForm.apply_mlieBracket_eq_neg_mextDeriv (hα.contMDiff.mdifferentiableAt (by simp))
    ((hV x hx).mdifferentiableAt hUx) ((hW x hx).mdifferentiableAt hUx) hVα hWα,
    h α hα hαD x (V x) (hVD x hx) (W x) (hWD x hx), neg_zero] at hαbr
  exact hαbr rfl

end Involutive

end TauCeti
