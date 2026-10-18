/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Analysis.Normed.Module.Alternating.Bilinear
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap

/-!
# Smooth differential two-forms on manifolds

The generic smooth differential-form carrier already records the alternating map in each tangent
fibre. This module supplies the degree-two view used by the symplectic API: `SmoothTwoForm` is
the scalar degree-two specialization, and its bilinear, evaluation, and constant-form operations
are derived from `SmoothForm`.

The old independent structure has deliberately disappeared. Keeping the specialization name
lets the symplectic modules state their degree-two hypotheses while sharing the generic form
operations and their smoothness proofs.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth real differential two-form is the generic smooth scalar form in degree two. -/
abbrev SmoothTwoForm (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  SmoothForm I M ℝ 2

namespace SmoothTwoForm

variable {form form' : SmoothTwoForm I M}

section Evaluation

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Evaluating a smooth degree-two form on two smooth tangent fields along a smooth map gives a
smooth scalar function. -/
lemma contMDiff_apply {n : ℕ∞ω} [ENat.LEInfty n] (form : SmoothTwoForm I M)
    {b : N → M}
    {V W : ∀ y : N, TangentSpace I (b y)}
    (hV : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (V y)))
    (hW : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (W y))) :
    ContMDiff I' 𝓘(ℝ) n (fun y ↦ SmoothForm.eval₂ form (b y) (V y) (W y)) := by
  have hb : ContMDiff I' I n b := fun y ↦ by
    have hy := hV y
    rw [← contMDiffWithinAt_univ] at hy ⊢
    exact (contMDiffWithinAt_totalSpace.mp hy).1
  have hform := (form.toContMDiffSection.contMDiff.of_le ENat.LEInfty.out).comp hb
  have hform' : ContMDiff I' (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun y ↦ Bundle.TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) (b y)
        (form.toContMDiffSection (b y))) := by
    convert hform using 1
    funext y
    rfl
  intro y₀
  let e := trivializationAt E (TangentSpace I) (b y₀)
  have he : b y₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (b y₀)
  have hV' := (e.contMDiffAt_iff (f := fun y ↦ TotalSpace.mk' E (b y) (V y))
    (FiberBundle.mem_trivializationAt_proj_source (x := ⟨b y₀, V y₀⟩))).mp (hV y₀)
  have hW' := (e.contMDiffAt_iff (f := fun y ↦ TotalSpace.mk' E (b y) (W y))
    (FiberBundle.mem_trivializationAt_proj_source (x := ⟨b y₀, W y₀⟩))).mp (hW y₀)
  have hf := (contMDiffAt_continuousAlternatingMap_bundle (IM := I') (IB := I) (n := n)
    (f := fun y : N ↦
      (Bundle.TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) (b y)
        (form.toContMDiffSection (b y))))
    ).mp (hform' y₀)
  have happly := (hf.2.continuousAlternatingMap_apply
    (f := fun i : Fin 2 ↦ Fin.cases
      (fun y ↦ (e ⟨b y, V y⟩).2)
      (fun _ ↦ fun y ↦ (e ⟨b y, W y⟩).2) i)
    (fun i ↦ by
    fin_cases i
    · exact hV'.2
    · exact hW'.2))
  refine happly.congr_of_eventuallyEq ?_
  filter_upwards [(hb y₀).continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with y hy
  change SmoothForm.eval₂ form (b y) (V y) (W y) =
    ContinuousAlternatingMap.inCoordinates E ℝ
      (B₁ := M) (B₂ := M) (E₁ := TangentSpace I) (E₂ := Bundle.Trivial M ℝ)
      (b y₀) (b y) (b y₀) (b y)
      ((SmoothForm.toContMDiffSection form) (b y)) _
  rw [ContinuousAlternatingMap.inCoordinates_eq (F₁ := E) (F₂ := ℝ)
    (B₁ := M) (B₂ := M) (E₁ := TangentSpace I) (E₂ := Bundle.Trivial M ℝ)
    hy (by simp)]
  have hVvec : (trivializationAt E (TangentSpace I) (b y₀)).symm (b y)
      (e ⟨b y, V y⟩).2 = V y := by
    rw [← e.symmL_apply (R := ℝ) hy]
    simpa [e.coe_linearMapAt_of_mem (R := ℝ) hy] using
      (e.symmL_continuousLinearMapAt (R := ℝ) hy (V y))
  have hWvec : (trivializationAt E (TangentSpace I) (b y₀)).symm (b y)
      (e ⟨b y, W y⟩).2 = W y := by
    rw [← e.symmL_apply (R := ℝ) hy]
    simpa [e.coe_linearMapAt_of_mem (R := ℝ) hy] using
      (e.symmL_continuousLinearMapAt (R := ℝ) hy (W y))
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, SmoothForm.eval₂_apply]
  simp only [Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearEquivAt_trivialization, ContinuousLinearEquiv.coe_refl,
    SmoothForm.toContMDiffSection_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_symm_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, ContinuousLinearMap.coe_id',
    Function.comp_apply, id_eq]
  congr 1
  funext i
  fin_cases i
  · simpa [Function.comp_apply] using hVvec.symm
  · convert hWvec.symm using 1 <;> rfl

end Evaluation

/-- A continuous alternating bilinear form defines a constant smooth two-form on its model space. -/
def const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (_hB : ∀ v, B v v = 0) :
    SmoothTwoForm (modelWithCornersSelf ℝ V) V := by
  let A := (2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ V ℝ B
  let A' : ∀ x : V, TangentSpace (modelWithCornersSelf ℝ V) x [⋀^Fin 2]→L[ℝ] ℝ :=
    fun x ↦ A.compContinuousLinearMap (NormedSpace.fromTangentSpace x).toContinuousLinearMap
  exact ⟨A', by
    apply (mem_smoothForms (I := modelWithCornersSelf ℝ V) (M := V)
      (F := ℝ) (k := 2) (φ := A')).2
    change IsSmoothBundleForm (I := modelWithCornersSelf ℝ V) (F := ℝ)
      (V := Bundle.Trivial V ℝ) ∞ A'
    rw [isSmoothBundleForm_def]
    intro x
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨?_, ?_⟩
    · simpa only [Function.id_def] using (contMDiffAt_id : ContMDiffAt (modelWithCornersSelf ℝ V)
          (modelWithCornersSelf ℝ V) ∞ id x)
    · change ContMDiffAt (modelWithCornersSelf ℝ V)
        (𝓘(ℝ, V [⋀^Fin 2]→L[ℝ] ℝ)) ∞
        (fun y => ContinuousAlternatingMap.inCoordinates V ℝ
          (E₁ := TangentSpace (modelWithCornersSelf ℝ V))
          (E₂ := Bundle.Trivial V ℝ) x y x y (A' y)) x
      have hcoord : (fun y : V =>
          ContinuousAlternatingMap.inCoordinates V ℝ
            (E₁ := TangentSpace (modelWithCornersSelf ℝ V))
            (E₂ := Bundle.Trivial V ℝ) x y x y (A' y)) = fun _ => A := by
        funext y
        ext v
        simp only [A', ContinuousAlternatingMap.inCoordinates,
          Bundle.Trivial.eq_trivialization V ℝ
            (trivializationAt ℝ (Trivial V ℝ) x),
          Bundle.Trivial.continuousLinearMapAt_trivialization,
          TangentBundle.symmL_model_space,
          ]
        rfl
      rw [hcoord]
      exact contMDiffAt_const⟩

theorem const_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (x : V)
    (v w : TangentSpace (modelWithCornersSelf ℝ V) x) :
    SmoothForm.eval₂ (const B hB) x v w =
      B (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) := by
  rw [SmoothForm.eval₂_apply]
  dsimp [const]
  rw [ContinuousAlternatingMap.alternatizeBilinCLM_apply]
  have hneg := LinearMap.IsAlt.neg (show LinearMap.IsAlt B.toBilinForm from fun v ↦ by
    simpa only [ContinuousLinearMap.toBilinForm_apply] using hB v)
    (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w)
  simp only [Function.comp_apply]
  have hneg' : -B (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) =
      B (NormedSpace.fromTangentSpace x w) (NormedSpace.fromTangentSpace x v) := by
    simpa only [ContinuousLinearMap.toBilinForm_apply] using hneg
  change 2⁻¹ * (B (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) -
      B (NormedSpace.fromTangentSpace x w) (NormedSpace.fromTangentSpace x v)) = _
  rw [← hneg']
  ring

theorem const_model_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (x v w : V) :
    SmoothForm.eval₂ (const B hB) x ((NormedSpace.fromTangentSpace x).symm v)
      ((NormedSpace.fromTangentSpace x).symm w) = B v w := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (const_apply B hB x ((NormedSpace.fromTangentSpace x).symm v)
      ((NormedSpace.fromTangentSpace x).symm w))


end SmoothTwoForm

end TauCeti

end
