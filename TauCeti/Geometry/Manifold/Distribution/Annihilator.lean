/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.IsManifold.Basic

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
contact structures. Over `ℝ`, the covector field is a one-form: a `C^n` hyperplane field is locally
the kernel of a nonzero `C^n` one-form
(`TauCeti.IsContMDiffDistribution.exists_roughForm_ker_eq`).

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

section Covector

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  {k : ℕ} {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

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
  have hrank : finrank 𝕜 (LinearMap.range (A x).toLinearMap) = k := by
    rw [LinearMap.finrank_range_of_inj hAx, Module.finrank_pi, Fintype.card_fin]
  have hlt : LinearMap.range (A x).toLinearMap < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro h
    have := congrArg (fun S : Submodule 𝕜 E ↦ finrank 𝕜 S) h
    rw [hrank, finrank_top, ← hk] at this
    omega
  obtain ⟨a, ha, haA⟩ := (LinearMap.range (A x).toLinearMap).exists_le_ker_of_lt_top hlt
  let a' := a.toContinuousLinearMap
  have ha'A : a' ∘L A x = 0 := by
    ext c
    exact haA (LinearMap.mem_range_self _ c)
  -- The compressed frame is the identity at x, hence invertible on a neighborhood.
  let Q : M → (Fin k → 𝕜) →L[𝕜] Fin k → 𝕜 := fun y ↦ P ∘L A y
  have hQ : ContMDiffOn I 𝓘(𝕜, (Fin k → 𝕜) →L[𝕜] Fin k → 𝕜) n Q
      (V ∩ e.baseSet) := contMDiffOn_const.clm_comp hA
  have hQx : Q x = 1 := ContinuousLinearMap.ext hP
  -- Project a nonzero annihilator at x to the annihilators of the nearby frame images.
  let c : M → E →L[𝕜] 𝕜 := fun y ↦ a' - a' ∘L A y ∘L (Q y).inverse ∘L P
  have hcx : c x = a' := by
    dsimp only [c]
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, ha'A]
    simp
  have hcn : c x ≠ 0 := by
    rw [hcx]
    exact fun hz ↦ ha (congrArg ContinuousLinearMap.toLinearMap hz)
  have hQunit : ∀ᶠ y in 𝓝 x, (Q y).IsInvertible := by
    have hi : (Q x).IsInvertible := by
      rw [hQx]
      exact ⟨ContinuousLinearEquiv.refl 𝕜 _, rfl⟩
    exact (hQ.continuousOn.continuousAt
      ((hV.inter e.open_baseSet).mem_nhds ⟨hxV, hxe⟩)).tendsto.eventually hi.eventually_nhds
  obtain ⟨W, hWQ, hW, hxW⟩ := eventually_nhds_iff.mp hQunit
  have hc : ContMDiffOn I 𝓘(𝕜, E →L[𝕜] 𝕜) n c (V ∩ e.baseSet ∩ W) := by
    apply contMDiffOn_const.sub
    exact ((contMDiffOn_const.clm_comp (hA.mono inter_subset_left)).clm_comp
      (fun y hy ↦ (hWQ y hy.2).contDiffAt_map_inverse.comp_contMDiffWithinAt
        ((hQ y hy.1).mono inter_subset_left))).clm_comp contMDiffOn_const
  have hcn' : ∀ᶠ y in 𝓝 x, c y ≠ 0 :=
    (hc.continuousOn.continuousAt
      (((hV.inter e.open_baseSet).inter hW).mem_nhds ⟨⟨hxV, hxe⟩, hxW⟩)).eventually_ne hcn
  obtain ⟨Z, hZc, hZ, hxZ⟩ := eventually_nhds_iff.mp hcn'
  let U := V ∩ e.baseSet ∩ W ∩ Z
  let α : Π y : M, TangentSpace I y →L[𝕜] 𝕜 :=
    fun y ↦ c y ∘L e.continuousLinearMapAt 𝕜 y
  refine ⟨U, α, ((hV.inter e.open_baseSet).inter hW).inter hZ,
    ⟨⟨⟨hxV, hxe⟩, hxW⟩, hxZ⟩, ?_, ?_⟩
  -- The cotangent-bundle coordinates of α are exactly the smooth covectors c.
  · exact CotangentBundle.contMDiffOn_mk_comp_continuousLinearMapAt x
      (U := U) (c := c) (fun _ hy ↦ hy.1.1.2)
      (hc.mono inter_subset_left)
  · intro y hy
    have hcy : c y ≠ 0 := hZc y hy.2
    have hαy : α y ≠ 0 := by
      intro hz
      apply hcy
      ext v
      have := congrArg (fun f : TangentSpace I y →L[𝕜] 𝕜 ↦ f (e.symmL 𝕜 y v)) hz
      simpa [α, e.continuousLinearMapAt_symmL hy.1.1.2] using this
    refine ⟨hαy, ?_⟩
    -- Annihilation gives inclusion; codimension one upgrades it to equality.
    have hle : D y ≤ LinearMap.ker (α y).toLinearMap := by
      rw [← hX.span_eq hy.1.1.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hzero : c y ∘L A y = 0 :=
        a'.sub_comp_inverse_comp_comp_eq_zero (A y) P (hWQ y hy.1.2)
      have hAi := IsSubbundleFrameOn.trivOperator_apply (𝕜 := 𝕜) (X := X) hy.1.1.2
        (Pi.single i (1 : 𝕜))
      have heval : α y (X i y) = c y (e ⟨y, X i y⟩).2 :=
        congrArg (c y) (e.continuousLinearMapAt_apply_of_mem 𝕜 hy.1.1.2 (X i y))
      have hzeroi : α y (X i y) = 0 := by
        rw [heval]
        simpa [A, hAi, e] using
          congrArg (fun f : (Fin k → 𝕜) →L[𝕜] 𝕜 ↦ f (Pi.single i 1)) hzero
      exact hzeroi
    exact Module.Dual.ker_eq_of_le_of_finrank_add_one (α y).toLinearMap
      (fun hz ↦ hαy (ContinuousLinearMap.coe_injective hz)) hle
      (by rw [hD.finrank_eq y, finrank_tangentSpace, hk])


end Covector

/-! ### Local defining one-forms -/

section RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {n : ℕ∞ω} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- **A hyperplane field is locally the kernel of a one-form.** Every point of a `C^n` distribution
`D` of rank `dim E - 1` has an open neighbourhood `U` on which `D` is the kernel of a one-form `α`,
nonzero and of class `C^n` on `U`. No contact condition is needed. -/
theorem IsContMDiffDistribution.exists_roughForm_ker_eq [IsManifold I (n + 1) M] {k : ℕ}
    (hD : IsContMDiffDistribution I n k D) (hk : k + 1 = finrank ℝ E) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ α : RoughForm I M ℝ 1,
      ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U ∧
      ∀ y ∈ U, α y ≠ 0 ∧ α.ker y = D y := by
  obtain ⟨U, a, hU, hxU, ha, haD⟩ := hD.exists_local_annihilator hk x
  -- The covector field `a` is the one-form `α`, with the same kernel and regularity.
  let α : RoughForm I M ℝ 1 :=
    fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) ℝ (0 : Fin 1) (a y)
  refine ⟨U, hU, hxU, α, fun y hy ↦ ?_, fun y hy ↦ ⟨fun h ↦ (haD y hy).1 ?_, ?_⟩⟩
  · exact ((contMDiffAt_ofSubsingleton_iff (V := Bundle.Trivial M ℝ)).2
      ((ha y hy).contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt
  · exact ContinuousLinearMap.ext fun v ↦ by simpa [α] using congr($h ![v])
  · ext v
    rw [← (haD y hy).2, RoughForm.mem_ker]
    simp [α]

end RoughForm

end TauCeti
