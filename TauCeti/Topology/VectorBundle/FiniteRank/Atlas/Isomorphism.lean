/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Category
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix

/-!
# Fibrewise continuity and isomorphism criterion for variable-rank bundle atlases

Each fibre `A.Fiber x` embeds into the glued total space `TotalSpace Unit A.Fiber` of a
`TauCeti.FiniteRankAtlas` (`TauCeti.FiniteRankAtlas.isEmbedding_totalSpaceMk`), so every morphism
`f : A ⟶ D` in `FiniteRankAtlas 𝕜 X` is automatically continuous on each fibre
(`TauCeti.FiniteRankAtlas.Hom.continuousLinearMap`).

For every nontrivially normed field `𝕜` (without assuming `CompleteSpace 𝕜`),
`TauCeti.FiniteRankAtlas.isIso_iff_bijective` shows that a morphism `f : A ⟶ D` is a categorical
isomorphism if and only if it is bijective on every fibre. Fibrewise bijectivity first forces
`A.rank = D.rank` (`TauCeti.FiniteRankAtlas.rank_eq_of_bijective`); on each clopen rank stratum,
Cramer's rule (`continuousAt_matrix_inv`) in the preferred coordinate trivializations then shows
that the fibrewise inverse is continuous on the glued total space, without any completeness,
compactness, or separation assumption.
-/

public section

open Bundle CategoryTheory Set Topology VectorBundleCore
open scoped Matrix

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section FiberEmbedding

variable (A : FiniteRankAtlas 𝕜 X)

/-- Inclusion of a single fibre into the glued total space is a topological embedding. -/
theorem isEmbedding_totalSpaceMk (x : X) :
    IsEmbedding (TotalSpace.mk' Unit x : A.Fiber x → TotalSpace Unit A.Fiber) := by
  have h : (TotalSpace.mk' Unit x : A.Fiber x → TotalSpace Unit A.Fiber) =
      fun v ↦ A.totalSpaceHomeomorph
        ⟨A.rank x, TotalSpace.mk' (Fin (A.rank x) → 𝕜) ⟨x, rfl⟩ v⟩ :=
    funext fun v ↦ (A.totalSpaceHomeomorph_apply ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩).symm
  rw [h]
  exact A.totalSpaceHomeomorph.isEmbedding.comp
    (IsEmbedding.sigmaMk.comp
      (FiberBundle.totalSpaceMk_isEmbedding (Fin (A.rank x) → 𝕜)
        (A.charts (A.rank x)).Fiber ⟨x, rfl⟩))

@[continuity, fun_prop]
theorem continuous_totalSpaceMk (x : X) :
    Continuous (TotalSpace.mk' Unit x : A.Fiber x → TotalSpace Unit A.Fiber) :=
  (A.isEmbedding_totalSpaceMk x).continuous

end FiberEmbedding

namespace Hom

variable {A D : FiniteRankAtlas 𝕜 X}

/-- Every atlas morphism is continuous on each fibre, without assuming `CompleteSpace 𝕜`. -/
theorem continuous_fiberMap (f : Hom A D) (x : X) : Continuous (f.fiberMap x) := by
  rw [(D.isEmbedding_totalSpaceMk x).isInducing.continuous_iff]
  exact f.continuous_totalSpaceMap.comp (A.continuous_totalSpaceMk x)

/-- The continuous linear map induced by an atlas morphism on the fibre over `x`. -/
def continuousLinearMap (f : Hom A D) (x : X) : A.Fiber x →L[𝕜] D.Fiber x :=
  ⟨f.fiberMap x, f.continuous_fiberMap x⟩

@[simp]
theorem coe_continuousLinearMap (f : Hom A D) (x : X) :
    (f.continuousLinearMap x : A.Fiber x →ₗ[𝕜] D.Fiber x) = f.fiberMap x := (rfl)

@[simp]
theorem continuousLinearMap_apply (f : Hom A D) (x : X) (v : A.Fiber x) :
    f.continuousLinearMap x v = f.fiberMap x v := (rfl)

end Hom

section Isomorphism

variable {A D : FiniteRankAtlas 𝕜 X}

/-- A morphism that is bijective on every fibre forces the source and target atlases to have the
same locally constant rank. -/
theorem rank_eq_of_bijective (f : A ⟶ D) (hf : ∀ x, Function.Bijective (f.fiberMap x)) :
    A.rank = D.rank := by
  ext x
  calc
    A.rank x = Module.finrank 𝕜 (A.Fiber x) := (Module.finrank_fin_fun 𝕜).symm
    _ = Module.finrank 𝕜 (D.Fiber x) := (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).finrank_eq
    _ = D.rank x := Module.finrank_fin_fun 𝕜

private theorem mem_baseSet_self {S : Type*} [TopologicalSpace S] {n : ℕ}
    (c : VectorBundleCore 𝕜 S (Fin n → 𝕜) S) (hc : ∀ s, c.indexAt s = s) (s : S) :
    s ∈ c.baseSet s := by
  have h := c.mem_baseSet_at s
  rwa [hc s] at h

private def chartMatrix {S : Type*} [TopologicalSpace S] {n : ℕ}
    (c₁ c₂ : VectorBundleCore 𝕜 S (Fin n → 𝕜) S)
    (L : S → ((Fin n → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜))) (s₀ s : S) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  LinearMap.toMatrix' <|
    (c₂.coordChange s s₀ s).toLinearMap.comp
      ((L s).toLinearMap.comp (c₁.coordChange s₀ s s).toLinearMap)

private theorem continuousAt_chartMatrix {S : Type*} [TopologicalSpace S] {n : ℕ}
    (c₁ c₂ : VectorBundleCore 𝕜 S (Fin n → 𝕜) S)
    (h₁ : ∀ s, c₁.indexAt s = s) (h₂ : ∀ s, c₂.indexAt s = s)
    (L : S → ((Fin n → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜)))
    (hF : Continuous (fun p : c₁.TotalSpace ↦ (⟨p.proj, L p.proj p.2⟩ : c₂.TotalSpace)))
    (s₀ : S) :
    ContinuousAt (chartMatrix c₁ c₂ L s₀) s₀ := by
  refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
  let e₁ := (c₁.localTriv s₀).toOpenPartialHomeomorph
  let e₂ := (c₂.localTriv s₀).toOpenPartialHomeomorph
  let F : c₁.TotalSpace → c₂.TotalSpace := fun p ↦ ⟨p.proj, L p.proj p.2⟩
  have hs₁ : (s₀, Pi.single j (1 : 𝕜)) ∈ e₁.target := by
    rw [c₁.mem_localTriv_target]
    exact mem_baseSet_self c₁ h₁ s₀
  have hsymm : ContinuousAt (fun s : S ↦ e₁.symm (s, Pi.single j (1 : 𝕜))) s₀ :=
    ContinuousAt.comp (g := e₁.symm) (e₁.continuousAt_symm hs₁)
      (continuous_id.prodMk continuous_const).continuousAt
  have hs₂ : F (e₁.symm (s₀, Pi.single j (1 : 𝕜))) ∈ e₂.source := by
    rw [c₂.mem_localTriv_source]
    exact mem_baseSet_self c₂ h₂ s₀
  have htriv : ContinuousAt
      (fun s : S ↦ (e₂ (F (e₁.symm (s, Pi.single j (1 : 𝕜))))).2 i) s₀ :=
    (continuous_apply i).continuousAt.comp <| continuous_snd.continuousAt.comp <|
      ContinuousAt.comp (g := e₂) (e₂.continuousAt hs₂)
        (ContinuousAt.comp (g := F) hF.continuousAt hsymm)
  refine htriv.congr (Filter.Eventually.of_forall fun s ↦ ?_)
  simp only [e₁, e₂, F, chartMatrix, LinearMap.toMatrix'_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe, Trivialization.coe_coe, localTriv_symm_fst,
    localTriv_apply, h₁ s, h₂ s]

private theorem chartMatrix_mul_eq_one {S : Type*} [TopologicalSpace S] {n : ℕ}
    (c₁ c₂ : VectorBundleCore 𝕜 S (Fin n → 𝕜) S)
    (h₁ : ∀ s, c₁.indexAt s = s) (h₂ : ∀ s, c₂.indexAt s = s)
    (L : S → ((Fin n → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜))) {s₀ s : S}
    (hs₁ : s ∈ c₁.baseSet s₀) (hs₂ : s ∈ c₂.baseSet s₀) :
    chartMatrix c₁ c₂ L s₀ s *
      LinearMap.toMatrix' ((c₁.coordChange s s₀ s).toLinearMap.comp
        (((L s).symm).toLinearMap.comp (c₂.coordChange s₀ s s).toLinearMap)) = 1 := by
  rw [chartMatrix, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  ext v
  have hs₁_self : s ∈ c₁.baseSet s := mem_baseSet_self c₁ h₁ s
  have hs₂_self : s ∈ c₂.baseSet s := mem_baseSet_self c₂ h₂ s
  simp only [LinearMap.comp_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe,
    LinearEquiv.coe_coe]
  rw [c₁.coordChange_comp s s₀ s s ⟨⟨hs₁_self, hs₁⟩, hs₁_self⟩, c₁.coordChange_self s s hs₁_self,
    LinearEquiv.apply_symm_apply, c₂.coordChange_comp s₀ s s₀ s ⟨⟨hs₂, hs₂_self⟩, hs₂⟩,
    c₂.coordChange_self s₀ s hs₂]

private theorem localTriv_symm_chartMatrix_inv {S : Type*} [TopologicalSpace S] {n : ℕ}
    (c₁ c₂ : VectorBundleCore 𝕜 S (Fin n → 𝕜) S)
    (h₁ : ∀ s, c₁.indexAt s = s) (h₂ : ∀ s, c₂.indexAt s = s)
    (L : S → ((Fin n → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜))) {s₀ : S} {q : c₂.TotalSpace}
    (hq₁ : q.proj ∈ c₁.baseSet s₀) (hq₂ : q.proj ∈ c₂.baseSet s₀) :
    (c₁.localTriv s₀).toOpenPartialHomeomorph.symm
      (q.proj, (chartMatrix c₁ c₂ L s₀ q.proj)⁻¹ *ᵥ ((c₂.localTriv s₀) q).2) =
      (⟨q.proj, (L q.proj).symm q.2⟩ : c₁.TotalSpace) := by
  have hinv := Matrix.inv_eq_right_inv (chartMatrix_mul_eq_one c₁ c₂ h₁ h₂ L hq₁ hq₂)
  have hq₁_self : q.proj ∈ c₁.baseSet q.proj := mem_baseSet_self c₁ h₁ q.proj
  have hq₂_self : q.proj ∈ c₂.baseSet q.proj := mem_baseSet_self c₂ h₂ q.proj
  have hw₂ : (c₂.coordChange s₀ q.proj q.proj) ((c₂.coordChange q.proj s₀ q.proj) q.snd) =
      q.snd :=
    (c₂.coordChange_comp q.proj s₀ q.proj q.proj ⟨⟨hq₂_self, hq₂⟩, hq₂_self⟩ q.snd).trans
      (c₂.coordChange_self q.proj q.proj hq₂_self q.snd)
  have hw₁ (u : Fin n → 𝕜) :
      (c₁.coordChange s₀ q.proj q.proj) ((c₁.coordChange q.proj s₀ q.proj) u) = u :=
    (c₁.coordChange_comp q.proj s₀ q.proj q.proj ⟨⟨hq₁_self, hq₁⟩, hq₁_self⟩ u).trans
      (c₁.coordChange_self q.proj q.proj hq₁_self u)
  ext : 1
  · rfl
  · refine heq_of_eq ?_
    simp only [localTriv_symm_fst, localTriv_apply, h₁ q.proj, h₂ q.proj, hinv,
      LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearEquiv.coe_coe]
    exact (hw₁ _).trans (congrArg (L q.proj).symm hw₂)

private theorem continuous_core_inv {S : Type*} [TopologicalSpace S] {n : ℕ}
    (c₁ c₂ : VectorBundleCore 𝕜 S (Fin n → 𝕜) S)
    (h₁ : ∀ s, c₁.indexAt s = s) (h₂ : ∀ s, c₂.indexAt s = s)
    (L : S → ((Fin n → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜)))
    (hF : Continuous (fun p : c₁.TotalSpace ↦ (⟨p.proj, L p.proj p.2⟩ : c₂.TotalSpace))) :
    Continuous (fun q : c₂.TotalSpace ↦ (⟨q.proj, (L q.proj).symm q.2⟩ : c₁.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  let s₀ := q₀.proj
  let e₁ := (c₁.localTriv s₀).toOpenPartialHomeomorph
  let e₂ := (c₂.localTriv s₀).toOpenPartialHomeomorph
  have hs₀₁ : s₀ ∈ c₁.baseSet s₀ := mem_baseSet_self c₁ h₁ s₀
  have hs₀₂ : s₀ ∈ c₂.baseSet s₀ := mem_baseSet_self c₂ h₂ s₀
  have hdet : (chartMatrix c₁ c₂ L s₀ s₀).det ≠ 0 := fun h0 ↦ by
    have hmul := congrArg Matrix.det (chartMatrix_mul_eq_one c₁ c₂ h₁ h₂ L hs₀₁ hs₀₂)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hmul
    exact zero_ne_one hmul
  have hrinv : ContinuousAt Ring.inverse (chartMatrix c₁ c₂ L s₀ s₀).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet
  have hMinv_s : ContinuousAt (fun s : S ↦ (chartMatrix c₁ c₂ L s₀ s)⁻¹) s₀ :=
    (continuousAt_matrix_inv _ hrinv).comp (continuousAt_chartMatrix c₁ c₂ h₁ h₂ L hF s₀)
  have hMinv : ContinuousAt (fun q : c₂.TotalSpace ↦ (chartMatrix c₁ c₂ L s₀ q.proj)⁻¹) q₀ :=
    ContinuousAt.comp (g := fun s : S ↦ (chartMatrix c₁ c₂ L s₀ s)⁻¹) hMinv_s
      c₂.continuous_proj.continuousAt
  have hq₀_src : q₀ ∈ e₂.source := by rw [c₂.mem_localTriv_source]; exact hs₀₂
  have hvec : ContinuousAt
      (fun q : c₂.TotalSpace ↦ (chartMatrix c₁ c₂ L s₀ q.proj)⁻¹ *ᵥ (e₂ q).2) q₀ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).continuousAt.comp
      (hMinv.prodMk <| continuous_snd.continuousAt.comp (e₂.continuousAt hq₀_src))
  have htgt : (q₀.proj, (chartMatrix c₁ c₂ L s₀ q₀.proj)⁻¹ *ᵥ (e₂ q₀).2) ∈ e₁.target := by
    rw [c₁.mem_localTriv_target]; exact hs₀₁
  have hloc : ContinuousAt (fun q : c₂.TotalSpace ↦
      e₁.symm (q.proj, (chartMatrix c₁ c₂ L s₀ q.proj)⁻¹ *ᵥ (e₂ q).2)) q₀ :=
    ContinuousAt.comp (g := e₁.symm) (e₁.continuousAt_symm htgt)
      (c₂.continuous_proj.continuousAt.prodMk hvec)
  have hU : c₂.proj ⁻¹' (c₁.baseSet s₀ ∩ c₂.baseSet s₀) ∈ 𝓝 q₀ :=
    ((c₁.isOpen_baseSet s₀).inter (c₂.isOpen_baseSet s₀) |>.preimage c₂.continuous_proj).mem_nhds
      ⟨hs₀₁, hs₀₂⟩
  exact hloc.congr (Filter.eventually_of_mem hU fun q ⟨hq₁, hq₂⟩ ↦
    localTriv_symm_chartMatrix_inv c₁ c₂ h₁ h₂ L hq₁ hq₂)

private theorem continuous_inv_of_bijective_same_rank (r : LocallyConstant X ℕ)
    (cA cD : ∀ n : ℕ, VectorBundleCore 𝕜 {x : X // r x = n} (Fin n → 𝕜) {x : X // r x = n})
    (hA : ∀ n x, (cA n).indexAt x = x) (hD : ∀ n x, (cD n).indexAt x = x)
    (f : (⟨r, cA, hA⟩ : FiniteRankAtlas 𝕜 X) ⟶ ⟨r, cD, hD⟩)
    (hf : ∀ x, Function.Bijective (f.fiberMap x)) :
    let A' : FiniteRankAtlas 𝕜 X := ⟨r, cA, hA⟩
    let D' : FiniteRankAtlas 𝕜 X := ⟨r, cD, hD⟩
    Continuous (fun p : TotalSpace Unit D'.Fiber ↦
      (⟨p.proj, (LinearEquiv.ofBijective (f.fiberMap p.proj) (hf p.proj)).symm p.2⟩ :
        TotalSpace Unit A'.Fiber)) := by
  let A' : FiniteRankAtlas 𝕜 X := ⟨r, cA, hA⟩
  let D' : FiniteRankAtlas 𝕜 X := ⟨r, cD, hD⟩
  refine (A'.continuous_mk_iff_rankStrata D'.continuous_proj _).2 fun n ↦ ?_
  let eCoord (s : {x : X // r x = n}) : (Fin (r s.1) → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜) :=
    LinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜) (finCongr s.2)
  let L (s : {x : X // r x = n}) : (Fin n → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜) :=
    (eCoord s).symm.trans ((LinearEquiv.ofBijective (f.fiberMap s.1) (hf s.1)).trans (eCoord s))
  have hF : Continuous
      (fun p : (cA n).TotalSpace ↦ (⟨p.proj, L p.proj p.2⟩ : (cD n).TotalSpace)) := by
    apply (IsEmbedding.sigmaMk (σ := fun m ↦ (cD m).TotalSpace)).continuous_iff.2
    refine (D'.totalSpaceHomeomorph.symm.continuous.comp
      (f.continuous_totalSpaceMap.comp
        (A'.totalSpaceHomeomorph.continuous.comp continuous_sigmaMk))).congr ?_
    rintro ⟨⟨x, hx⟩, v⟩
    cases hx
    exact (congrArg (fun q : TotalSpace Unit A'.Fiber ↦
      D'.totalSpaceHomeomorph.symm ⟨q.proj, f.fiberMap q.proj q.2⟩)
      (A'.totalSpaceHomeomorph_apply ⟨r x, ⟨⟨x, rfl⟩, v⟩⟩)).trans
      (D'.totalSpaceHomeomorph_symm_apply ⟨x, f.fiberMap x v⟩)
  have htoChart : Continuous (fun q : {q : TotalSpace Unit D'.Fiber // r q.proj = n} ↦
      (⟨⟨q.1.proj, q.2⟩, fun i ↦ q.1.2 (Fin.cast q.2.symm i)⟩ : (cD n).TotalSpace)) := by
    apply (IsEmbedding.sigmaMk (σ := fun m ↦ (cD m).TotalSpace)).continuous_iff.2
    refine (D'.totalSpaceHomeomorph.symm.continuous.comp continuous_subtype_val).congr ?_
    rintro ⟨⟨x, v⟩, hx⟩
    cases hx
    exact D'.totalSpaceHomeomorph_symm_apply ⟨x, v⟩
  refine ((continuous_core_inv (cA n) (cD n) (hA n) (hD n) L hF).comp htoChart).congr ?_
  rintro ⟨⟨x, v⟩, hx⟩
  cases hx
  rfl

private theorem continuous_inv_of_bijective (f : A ⟶ D)
    (hf : ∀ x, Function.Bijective (f.fiberMap x)) :
    Continuous (fun p : TotalSpace Unit D.Fiber ↦
      (⟨p.proj, (LinearEquiv.ofBijective (f.fiberMap p.proj) (hf p.proj)).symm p.2⟩ :
        TotalSpace Unit A.Fiber)) := by
  have hr : A.rank = D.rank := rank_eq_of_bijective f hf
  rcases A with ⟨r, cA, hA⟩
  rcases D with ⟨rD, cD, hD⟩
  change r = rD at hr
  subst hr
  exact continuous_inv_of_bijective_same_rank r cA cD hA hD f hf

/-- Over any nontrivially normed field, an atlas morphism that is bijective on every fibre upgrades
to an isomorphism in `FiniteRankAtlas 𝕜 X`. -/
noncomputable def isoOfBijective (f : A ⟶ D) (hf : ∀ x, Function.Bijective (f.fiberMap x)) :
    A ≅ D :=
  isoMk (fun x ↦ LinearEquiv.ofBijective (f.fiberMap x) (hf x))
    (f.continuous_totalSpaceMap.congr fun _ ↦ rfl) (continuous_inv_of_bijective f hf)

@[simp]
theorem isoOfBijective_hom (f : A ⟶ D) (hf : ∀ x, Function.Bijective (f.fiberMap x)) :
    (isoOfBijective f hf).hom = f := by
  apply hom_ext
  intro x
  rw [isoOfBijective, fiberMap_isoMk_hom]
  rfl

@[simp]
theorem fiberMap_isoOfBijective_inv (f : A ⟶ D) (hf : ∀ x, Function.Bijective (f.fiberMap x))
    (x : X) :
    (isoOfBijective f hf).inv.fiberMap x =
      (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).symm.toLinearMap := by
  rw [isoOfBijective, fiberMap_isoMk_inv]

/-- Over any nontrivially normed field, a morphism of variable-rank bundle atlases is an
isomorphism if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective (f : A ⟶ D) :
    IsIso f ↔ ∀ x, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun hf x ↦ ?_, fun hf ↦ ?_⟩
  · exact ((fiberFunctor x).mapIso (asIso f)).toLinearEquiv.bijective
  · rw [← isoOfBijective_hom f hf]
    infer_instance

end Isomorphism

end TauCeti.FiniteRankAtlas
