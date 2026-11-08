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
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse

/-!
# Local defining covectors for hyperplane distributions

A smooth hyperplane distribution is locally the kernel of a nowhere-zero smooth covector field.
The covectors are sections of the existing bundle of continuous linear maps from the tangent
bundle to the scalar field. No global coorientation is assumed: the section is constructed only
on a neighborhood of the chosen point.

In tangent-bundle coordinates, a local frame gives an injective operator `A`. A fixed left
inverse `P` of its value at the chosen point gives the nearby left inverse `(P A)⁻¹ P`.
The projection `1 - A (P A)⁻¹ P` then produces a smooth annihilating covector. Nonvanishing is
open, and the rank of the distribution makes its inclusion in the kernel an equality.

This is the local defining-form construction for hyperplane fields, including noncoorientable
contact structures. Over `ℝ`, the covector field is the same as a local one-form whose kernel is
the hyperplane field (`TauCeti.IsContMDiffDistribution.exists_roughForm_ker_eq`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 19 (local defining
  forms for distributions).
* H. Geiges, *An Introduction to Contact Topology*, Section 1.1 (local contact forms).
-/

public section

noncomputable section

open Bundle Set Filter Function Module
open scoped Manifold ContDiff Topology

namespace TauCeti

section Annihilator

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {k : ℕ} {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

omit [CompleteSpace 𝕜] [IsManifold I (n + 1) M] in
/-- At a point of a frame domain, a nonzero covector killing the frame operator pulls back along
the trivialization to a nonzero covector whose kernel is the distribution. -/
private theorem ker_comp_continuousLinearMapAt_eq
    (hD : IsContMDiffDistribution I n k D) (hk : k + 1 = finrank 𝕜 E) {x y : M}
    {V : Set M} {X : Fin k → Π y : M, TangentSpace I y} (hX : IsDistributionFrameOn I n D X V)
    (hyV : y ∈ V) (hye : y ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    {c : E →L[𝕜] 𝕜} (hc : c ≠ 0) (hzero : c ∘L IsSubbundleFrameOn.trivOperator 𝕜 E X x y = 0) :
    c ∘L (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 y ≠ 0 ∧
      LinearMap.ker
        (c ∘L (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 y).toLinearMap =
          D y := by
  set e := trivializationAt E (TangentSpace I) x
  have hαy : c ∘L e.continuousLinearMapAt 𝕜 y ≠ 0 := by
    intro hz
    apply hc
    ext v
    have := congrArg (fun f : TangentSpace I y →L[𝕜] 𝕜 ↦ f (e.symmL 𝕜 y v)) hz
    simpa [e.continuousLinearMapAt_symmL hye] using this
  refine ⟨hαy, ?_⟩
  -- Annihilation gives inclusion; codimension one upgrades it to equality.
  have hle : D y ≤ LinearMap.ker (c ∘L e.continuousLinearMapAt 𝕜 y).toLinearMap := by
    rw [← hX.span_eq hyV]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hAi := IsSubbundleFrameOn.trivOperator_apply (𝕜 := 𝕜) (X := X) hye
      (Pi.single i (1 : 𝕜))
    have heval : (c ∘L e.continuousLinearMapAt 𝕜 y) (X i y) = c (e ⟨y, X i y⟩).2 :=
      congrArg c (e.continuousLinearMapAt_apply_of_mem 𝕜 hye (X i y))
    rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, heval]
    simpa [hAi, e] using congrArg (fun f : (Fin k → 𝕜) →L[𝕜] 𝕜 ↦ f (Pi.single i 1)) hzero
  exact Module.Dual.ker_eq_of_le_of_finrank_add_one _
    (fun hz ↦ hαy (ContinuousLinearMap.coe_injective hz)) hle
    (by rw [hD.finrank_eq y, finrank_tangentSpace, hk])

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
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  -- Read a local frame in one fixed tangent-bundle trivialization.
  obtain ⟨V, hV, hxV, X, hX⟩ := isContMDiffDistribution_iff.mp hD x
  let e := trivializationAt E (TangentSpace I) x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  let A := IsSubbundleFrameOn.trivOperator 𝕜 E X x
  have hA := hX.contMDiffOn_trivOperator x
  obtain ⟨P, a, hP, ha, haA⟩ := ContinuousLinearMap.exists_leftInverse_ne_zero_comp_eq_zero _
    (hX.isSubbundleFrameOn.injective_trivOperator hxV)
    (by rw [Module.finrank_pi, Fintype.card_fin]; omega)
  obtain ⟨W, hW, hxW, hWS, hc, hWc⟩ := hA.exists_isOpen_contMDiffOn_sub_comp_inverse_comp
    (hV.inter e.open_baseSet) ⟨hxV, hxe⟩ hP ha haA
  refine ⟨W,
    fun y ↦ (a - a ∘L A y ∘L (P ∘L A y).inverse ∘L P) ∘L e.continuousLinearMapAt 𝕜 y, hW,
    hxW, ?_, fun y hy ↦ ?_⟩
  -- The cotangent-bundle coordinates of α are exactly the smooth covectors c.
  · exact CotangentBundle.contMDiffOn_mk_comp_continuousLinearMapAt x
      (U := W) (fun _ hy ↦ (hWS hy).2) hc
  · exact ker_comp_continuousLinearMapAt_eq hD hk hX (hWS hy).1 (hWS hy).2 (hWc y hy).2
      (a.sub_comp_inverse_comp_comp_eq_zero (A y) P (hWc y hy).1)

end Annihilator

/-! ### Local defining one-forms -/

section RoughForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

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
  obtain ⟨U, a, hU, hxU, ha, haD⟩ := hD.exists_local_annihilator hk x
  -- The covector field `a` is the one-form `α`, with the same kernel and regularity.
  let α : RoughForm I M ℝ 1 :=
    fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) ℝ (0 : Fin 1) (a y)
  refine ⟨U, hU, hxU, α, fun y hy ↦ ?_, fun y hy ↦ ⟨fun h ↦ (haD y hy).1 <|
    ContinuousLinearMap.ext fun v ↦ by simpa [α] using congr($h ![v]), ?_⟩⟩
  · exact ((contMDiffAt_ofSubsingleton_iff (V := Bundle.Trivial M ℝ)).2
      ((ha y hy).contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt
  · ext v
    rw [← (haD y hy).2, RoughForm.mem_ker]
    simp [α]

end RoughForm

end TauCeti
