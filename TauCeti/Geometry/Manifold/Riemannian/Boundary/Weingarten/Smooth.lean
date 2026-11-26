/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Weingarten.Basic
import TauCeti.Geometry.Manifold.Boundary.Derivative
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt

/-!
# Smoothness of the Weingarten map and the mean curvature of the boundary

Let `M` be a Riemannian manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, on a
`C^(k + 2)` manifold with a `C^(k + 1)` metric. The second fundamental form `II` of the boundary is
then a `C^k` section of the bundle of bilinear forms on `T∂M`
(`TauCeti.contMDiffAt_boundarySecondFundamentalForm_apply`). This file shows that the same holds for
the quantities built from `II` and the induced metric `h`:

* the Weingarten map `S` is a `C^k` section of the bundle of endomorphisms of `T∂M`: it carries a
  tangent field `U` of the boundary manifold that is `C^k` at `q₀` to the field `q ↦ S_q (U q)`,
  again `C^k` at `q₀` (`TauCeti.contMDiffAt_boundaryWeingarten_apply`);
* the mean curvature `H` is a `C^k` function on `∂M` (`TauCeti.contMDiffAt_boundaryMeanCurvature`).

Near every point the boundary carries tangent fields `e₁, …, eₙ` that are `C^k` and orthonormal
for `h`. They are obtained by applying Gram–Schmidt to the images under `dι` of a local frame of
`T∂M`, as vector fields of `M` along the inclusion `ι : ∂M → M`
(`ContMDiffAt.gramSchmidtNormed_bundle`), and reading the result back in `T∂M`
(`TauCeti.contMDiffAt_of_mfderiv_subtypeVal_boundary`). In such a frame
`S_q u = ∑ᵢ II_q(u, eᵢ) eᵢ` (`TauCeti.boundaryWeingarten_apply_eq_sum`) and
`n H = ∑ᵢ II_q(eᵢ, eᵢ)` (`TauCeti.sum_boundarySecondFundamentalForm_eq_mul_boundaryMeanCurvature`),
whose terms are `C^k`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
-/

public section

noncomputable section

open Bundle Filter InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  {k m l : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) m M]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) l (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)]

omit [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
/-- **Local orthonormal frames of the boundary.** Near every point `q₀` of the boundary there are
tangent fields `e₁, …, eₙ` of the boundary manifold, `C^k` at `q₀` and orthonormal for the induced
metric at every point near `q₀`, on a `C^(k + 1)` manifold with a `C^k` metric. -/
theorem exists_contMDiffAt_boundaryInducedForm_orthonormal (hm : k + 1 ≤ m) (hl : k ≤ l)
    (q₀ : (𝓡∂ (n + 1)).boundary M) :
    ∃ e : Fin n → (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
      (∀ i, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
        (T% (e i)) q₀) ∧
      ∀ᶠ q in 𝓝 q₀, ∀ i j, boundaryInducedForm q (e i q) (e j q) = if i = j then 1 else 0 := by
  have : IsManifold (𝓡∂ (n + 1)) (k + 1) M := .of_le hm
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1) ((𝓡∂ (n + 1)).boundary M) :=
    isManifold_boundary M
  have : ContMDiffVectorBundle k (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : (𝓡∂ (n + 1)).boundary M → Type _)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) :=
    TangentBundle.contMDiffVectorBundle
  have : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := .of_le hl
  -- A local frame `(bᵢ)` of `T∂M` at `q₀`, pushed forward to `M` along `ι`.
  set t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : (𝓡∂ (n + 1)).boundary M → Type _) q₀
  set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hq₀ : q₀ ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' q₀
  have hframe := t.isLocalFrameOn_localFrame_baseSet 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k b
  set E : Fin n → (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (q : M) :=
    fun i q ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q (t.localFrame b i q)
  have hι : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) (k + 1)
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) :=
    (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M).contMDiff
  have hE (i : Fin n) : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((𝓡∂ (n + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) k
      (fun q : (𝓡∂ (n + 1)).boundary M ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin (n + 1))) (q : M) (E i q)) q₀ :=
    ContMDiffAt.mfderiv_apply_sectionAlong hι.contMDiffAt
      ((hframe.contMDiffOn i).contMDiffAt (t.open_baseSet.mem_nhds hq₀)) le_rfl
  have hli {q : (𝓡∂ (n + 1)).boundary M} (hq : q ∈ t.baseSet) :
      LinearIndependent ℝ fun i ↦ E i q :=
    (hframe.linearIndependent hq).map' _
      (LinearMap.ker_eq_bot.2 (injective_mfderiv_subtypeVal_boundary q))
  -- Gram–Schmidt in `T_qM` keeps the fields `C^k` along `ι` and tangent to the boundary.
  set F : Fin n → (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (q : M) :=
    fun j q ↦ gramSchmidtNormed ℝ (fun i ↦ E i q) j
  have hmem (j : Fin n) (q : (𝓡∂ (n + 1)).boundary M) : F j q ∈ boundaryTangentSpace q := by
    have h : F j q ∈ Submodule.span ℝ (Set.range fun i ↦ F i q) :=
      Submodule.subset_span (Set.mem_range_self j)
    rw [span_gramSchmidtNormed_range, span_gramSchmidt] at h
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨i, rfl⟩
    exact mfderiv_subtypeVal_mem_boundaryTangentSpace q _
  refine ⟨fun j q ↦ (boundaryTangentEquiv q).symm ⟨F j q, hmem j q⟩, fun j ↦ ?_, ?_⟩
  · refine contMDiffAt_of_mfderiv_subtypeVal_boundary ?_
    simp only [← coe_boundaryTangentEquiv_apply, LinearEquiv.apply_symm_apply]
    exact ContMDiffAt.gramSchmidtNormed_bundle j (fun i _ ↦ hE i) ((hli hq₀).linearIndepOn _)
  · filter_upwards [t.open_baseSet.mem_nhds hq₀] with q hq i j
    rw [boundaryInducedForm_eq_inner_boundaryTangentEquiv, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, Submodule.coe_inner]
    exact orthonormal_iff_ite.1 (gramSchmidtNormed_orthonormal (hli hq)) i j

/-- **The Weingarten map of the boundary is a `C^k` section** of the bundle of endomorphisms of
`T∂M`, on a `C^(k + 2)` manifold with a `C^(k + 1)` metric: it carries a tangent field `U` of the
boundary manifold that is `C^k` at `q₀` to the field `q ↦ S_q (U q)`, again `C^k` at `q₀`. -/
theorem contMDiffAt_boundaryWeingarten_apply (hm : k + 2 ≤ m) (hl : k + 1 ≤ l)
    {U : (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    {q₀ : (𝓡∂ (n + 1)).boundary M}
    (hU : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% U) q₀) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% (fun q ↦ boundaryWeingarten q (U q))) q₀ := by
  have hm1 : k + 1 ≤ m := (add_le_add_right (by norm_num : (1 : ℕ∞ω) ≤ 2) k).trans hm
  obtain ⟨e, he, hon⟩ :=
    exists_contMDiffAt_boundaryInducedForm_orthonormal hm1 (le_self_add.trans hl) q₀
  -- `S_q (U q) = ∑ᵢ II_q(U q, eᵢ q) eᵢ q` near `q₀`.
  have hsum := ContMDiffAt.sum_section (s := Finset.univ) (t := fun i q ↦
    boundarySecondFundamentalForm q (U q) (e i q) • e i q) fun i _ ↦
      (contMDiffAt_boundarySecondFundamentalForm_apply hm hl hU (he i)).smul_section (he i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hon] with q hq
  rw [boundaryWeingarten_apply_eq_sum q (fun i ↦ e i q) hq]

/-- **The Weingarten map of the boundary is a `C^k` section**: for a `C^k` tangent field `U` of the
boundary manifold, `q ↦ S_q (U q)` is `C^k`, on a `C^(k + 2)` manifold with a `C^(k + 1)`
metric. -/
theorem contMDiff_boundaryWeingarten_apply (hm : k + 2 ≤ m) (hl : k + 1 ≤ l)
    {U : (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    (hU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% U)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% (fun q ↦ boundaryWeingarten q (U q))) := fun q₀ ↦
  contMDiffAt_boundaryWeingarten_apply hm hl (hU q₀)

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)]

/-- **The mean curvature of the boundary is `C^k`** at every point, on a `C^(k + 2)` manifold with
a `C^(k + 1)` metric. -/
theorem contMDiffAt_boundaryMeanCurvature (hm : k + 2 ≤ m) (hl : k + 1 ≤ l)
    (q₀ : (𝓡∂ (n + 1)).boundary M) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k
      (boundaryMeanCurvature (n := n) (M := M)) q₀ := by
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
    isManifold_boundary M
  have hm1 : k + 1 ≤ m := (add_le_add_right (by norm_num : (1 : ℕ∞ω) ≤ 2) k).trans hm
  obtain ⟨e, he, hon⟩ :=
    exists_contMDiffAt_boundaryInducedForm_orthonormal hm1 (le_self_add.trans hl) q₀
  -- `n H(q) = ∑ᵢ II_q(eᵢ q, eᵢ q)` near `q₀`.
  have hsum : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k
      (fun q ↦ (n : ℝ)⁻¹ * ∑ i, boundarySecondFundamentalForm q (e i q) (e i q)) q₀ :=
    contMDiffAt_const.mul (contMDiffAt_finsetSum fun i _ ↦
      contMDiffAt_boundarySecondFundamentalForm_apply hm hl (he i) (he i))
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hon] with q hq
  rw [sum_boundarySecondFundamentalForm_eq_mul_boundaryMeanCurvature q (fun i ↦ e i q) hq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [boundaryMeanCurvature_def]
  · rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hn)]

/-- **The mean curvature of the boundary is a `C^k` function**, on a `C^(k + 2)` manifold with a
`C^(k + 1)` metric. -/
theorem contMDiff_boundaryMeanCurvature (hm : k + 2 ≤ m) (hl : k + 1 ≤ l) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k (boundaryMeanCurvature (n := n) (M := M)) :=
  contMDiffAt_boundaryMeanCurvature hm hl

end TauCeti
