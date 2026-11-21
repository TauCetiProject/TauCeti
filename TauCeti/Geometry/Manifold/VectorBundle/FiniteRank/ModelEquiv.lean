/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.ModelEquiv
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth and holomorphic cores from a coordinate equivalence of the model fibre

This file lifts the coordinate-model constructions of
`TauCeti.Topology.VectorBundle.FiniteRank.ModelEquiv` to `C^n` (and in particular holomorphic, for
`𝕜 = ℂ` and `n = ∞`) vector bundles over a charted space `B`:

* `TauCeti.FiniteRankBundleCore.isContMDiff_ofBundleEquiv`: if `V` is a `C^n` vector bundle with
  model fibre `F` and `e : F ≃L[𝕜] (Fin r → 𝕜)`, then `ofBundleEquiv e V` is a `C^n` finite-rank
  core;
* `TauCeti.FiniteRankBundleCore.ofBundleEquivTotalSpaceDiffeomorph`: the reconstructed total space
  of `ofBundleEquiv e V` is `C^n` diffeomorphic to `TotalSpace F V` over the identity of the base,
  without smoothness or completeness hypotheses;
* `TauCeti.FiniteRankBundleCore.ofBundleEquivChangeDiffeomorph`: changing the coordinate
  equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of core total spaces commuting with
  `ofBundleEquivTotalSpaceDiffeomorph`;
* `TauCeti.FiniteRankBundleCore.ofBundleEquivDualTotalSpaceDiffeomorph` and
  `TauCeti.FiniteRankBundleCore.ofBundleEquivDualChangeDiffeomorph`: over a complete scalar field,
  the dual core `(ofBundleEquiv e V).dual` is `C^n` diffeomorphic to Mathlib's dual bundle
  `fun x ↦ V x →L[𝕜] 𝕜`, compatibly with changes of coordinate equivalence.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle CategoryTheory FiberBundle Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A pair of mutually inverse core morphisms with constant fibre maps `L` and `L'` where `L`
intertwines all point-to-chart transitions induces a `C^n` diffeomorphism of total spaces without
smoothness hypotheses. -/
noncomputable def toDiffeomorphOfConstFiberMap {A D : FiniteRankBundleCore 𝕜 B}
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (f : A ⟶ D) (g : D ⟶ A) (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 D)
    (L : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (L' : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜))
    (hf : ∀ x, f.fiberMap x = L) (hg : ∀ x, g.fiberMap x = L')
    (hL : ∀ x b v, D.core.coordChange x b x (L v) = L (A.core.coordChange x b x v)) :
    A.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin D.rank → 𝕜)⟯ D.core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv f g hfg hgf
    (contMDiff_totalSpaceMap_of_coordChange (I := I) (n := n) f L fun x b v ↦ by
      rw [hf]; exact hL x b v)
    (contMDiff_totalSpaceMap_of_coordChange (I := I) (n := n) g L' fun x b v ↦ by
      have h1 : L'.comp L = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
        rw [← hf x, ← hg x, ← fiberMap_comp, hfg, fiberMap_id]
      have h2 : L.comp L' = ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜) := by
        rw [← hf x, ← hg x, ← fiberMap_comp, hgf, fiberMap_id]
      have h1' := congrArg (fun S ↦ S (A.core.coordChange x b x (L' v))) h1
      have h2' := congrArg (fun S ↦ S v) h2
      dsimp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1' h2'
      rw [hg, ← h1', ← hL x b (L' v), h2'])

theorem coe_toDiffeomorphOfConstFiberMap {A D : FiniteRankBundleCore 𝕜 B}
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (f : A ⟶ D) (g : D ⟶ A) (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 D)
    (L : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (L' : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜))
    (hf : ∀ x, f.fiberMap x = L) (hg : ∀ x, g.fiberMap x = L')
    (hL : ∀ x b v, D.core.coordChange x b x (L v) = L (A.core.coordChange x b x v)) :
    ⇑(toDiffeomorphOfConstFiberMap I n f g hfg hgf L L' hf hg hL) = f.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv ..

theorem coe_toDiffeomorphOfConstFiberMap_symm {A D : FiniteRankBundleCore 𝕜 B}
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (f : A ⟶ D) (g : D ⟶ A) (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 D)
    (L : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (L' : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜))
    (hf : ∀ x, f.fiberMap x = L) (hg : ∀ x, g.fiberMap x = L')
    (hL : ∀ x b v, D.core.coordChange x b x (L v) = L (A.core.coordChange x b x v)) :
    ⇑(toDiffeomorphOfConstFiberMap I n f g hfg hgf L L' hf hg hL).symm = g.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm ..

section OfBundleEquiv

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- If `V` is a `C^n` vector bundle with model fibre `F` and `e : F ≃L[𝕜] (Fin r → 𝕜)`, then
`ofBundleEquiv e V` is a `C^n` finite-rank core. -/
instance isContMDiff_ofBundleEquiv [ContMDiffVectorBundle n F V I] :
    (ofBundleEquiv e V).core.IsContMDiff I n where
  contMDiffOn_coordChange i j :=
    (e.arrowCongr e).contDiff.contMDiff.comp_contMDiffOn
      (ContMDiffVectorBundle.contMDiffOn_coordChangeL (IB := I) (n := n)
        (trivializationAt F V i) (trivializationAt F V j))

/-- The total-space identification between `(ofBundleEquiv e V).core.TotalSpace` and
`TotalSpace F V` is a `C^n` diffeomorphism over the identity of the base, fibrewise `𝕜`-linear via
`ofBundleEquivFiberEquiv`. No smoothness or completeness hypothesis is required. -/
noncomputable def ofBundleEquivTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv e V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofBundleEquiv e V).rank → 𝕜),
      I.prod 𝓘(𝕜, F)⟯ TotalSpace F V where
  toFun p := ⟨p.proj, ofBundleEquivFiberEquiv e V p.proj p.2⟩
  invFun p := ⟨p.proj, (ofBundleEquivFiberEquiv e V p.proj).symm p.2⟩
  left_inv p := by dsimp only; rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by dsimp only; rw [ContinuousLinearEquiv.apply_symm_apply]
  contMDiff_toFun p₀ := by
    rw [Bundle.contMDiffAt_totalSpace_iff]
    refine ⟨(contMDiff_proj (ofBundleEquiv e V).core.Fiber).contMDiffAt, ?_⟩
    have hU := ((ofBundleEquiv e V).core.localTriv p₀.proj).open_source.mem_nhds <|
      ((ofBundleEquiv e V).core.mem_localTriv_source p₀.proj p₀).2
        (mem_baseSet_trivializationAt F V p₀.proj)
    refine (e.symm.contDiff.comp_contMDiffAt
      ((ofBundleEquiv e V).contMDiffAt_localTriv_snd (I := I) (n := n) p₀)).congr_of_eventuallyEq ?_
    filter_upwards [hU] with q hq
    exact trivializationAt_ofBundleEquivFiberEquiv_snd e V p₀.proj
      (((ofBundleEquiv e V).core.mem_localTriv_source p₀.proj q).1 hq) q.2
  contMDiff_invFun p₀ := by
    rw [Bundle.contMDiffAt_totalSpace_iff, (ofBundleEquiv e V).trivializationAt_core]
    refine ⟨(contMDiff_proj V).contMDiffAt, ?_⟩
    have hU := (trivializationAt F V p₀.proj).open_source.mem_nhds
      (FiberBundle.mem_trivializationAt_proj_source (x := p₀))
    refine (e.contDiff.comp_contMDiffAt
      (p₀.contMDiffAt_trivializationAt_snd (IB := I) (n := n))).congr_of_eventuallyEq ?_
    filter_upwards [hU] with q hq
    have hq' := trivializationAt_ofBundleEquivFiberEquiv_snd e V p₀.proj
      ((trivializationAt F V p₀.proj).mem_source.1 hq)
      ((ofBundleEquivFiberEquiv e V q.proj).symm q.2)
    rw [show (⟨q.proj, ofBundleEquivFiberEquiv e V q.proj
        ((ofBundleEquivFiberEquiv e V q.proj).symm q.2)⟩ : TotalSpace F V) = q by
      rw [ContinuousLinearEquiv.apply_symm_apply]] at hq'
    exact ((congrArg e hq').trans (e.apply_symm_apply _)).symm

@[simp]
theorem ofBundleEquivTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleEquivTotalSpaceDiffeomorph e V I n).toHomeomorph =
      ofBundleEquivTotalSpaceHomeomorph e V :=
  Homeomorph.ext fun p ↦ (ofBundleEquivTotalSpaceHomeomorph_apply e V p).symm

@[simp]
theorem ofBundleEquivTotalSpaceDiffeomorph_apply
    (p : (ofBundleEquiv e V).core.TotalSpace) :
    ofBundleEquivTotalSpaceDiffeomorph e V I n p =
      ⟨p.proj, ofBundleEquivFiberEquiv e V p.proj p.2⟩ := (rfl)

@[simp]
theorem ofBundleEquivTotalSpaceDiffeomorph_symm_apply (p : TotalSpace F V) :
    (ofBundleEquivTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofBundleEquivFiberEquiv e V p.proj).symm p.2⟩ := (rfl)

end OfBundleEquiv

section ChangeEquiv

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of core
total spaces over the identity of the base, with fibre map `e₂ ∘ e₁⁻¹`. -/
noncomputable def ofBundleEquivChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv e₁ V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofBundleEquiv e₁ V).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv e₂ V).rank → 𝕜)⟯ (ofBundleEquiv e₂ V).core.TotalSpace :=
  toDiffeomorphOfConstFiberMap I n
    (ofBundleEquivChangeIso e₁ e₂ V).hom (ofBundleEquivChangeIso e₁ e₂ V).inv
    (ofBundleEquivChangeIso e₁ e₂ V).hom_inv_id (ofBundleEquivChangeIso e₁ e₂ V).inv_hom_id
    (e₁.symm.trans e₂).toContinuousLinearMap (e₂.symm.trans e₁).toContinuousLinearMap
    (fiberMap_ofBundleEquivChangeIso_hom e₁ e₂ V) (fiberMap_ofBundleEquivChangeIso_inv e₁ e₂ V)
    fun _ _ v ↦ congrArg e₂ <|
      (congrArg _ (e₂.symm_apply_apply (e₁.symm v))).trans (e₁.symm_apply_apply _).symm

@[simp]
theorem ofBundleEquivChangeDiffeomorph_apply (p : (ofBundleEquiv e₁ V).core.TotalSpace) :
    ofBundleEquivChangeDiffeomorph e₁ e₂ V I n p = ⟨p.proj, e₂ (e₁.symm p.2)⟩ :=
  (congrFun (coe_toDiffeomorphOfConstFiberMap ..) p).trans <|
    (congrArg (fun f ↦ f p)
        (CoordinateHom.totalSpaceMap_def (ofBundleEquivChangeIso e₁ e₂ V).hom)).trans <|
      congrArg (TotalSpace.mk' (Fin r₂ → 𝕜) p.proj) <|
        congrArg (fun S : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜) ↦ S p.2)
          (fiberMap_ofBundleEquivChangeIso_hom e₁ e₂ V p.proj)

@[simp]
theorem ofBundleEquivChangeDiffeomorph_symm_apply (p : (ofBundleEquiv e₂ V).core.TotalSpace) :
    (ofBundleEquivChangeDiffeomorph e₁ e₂ V I n).symm p = ⟨p.proj, e₁ (e₂.symm p.2)⟩ :=
  (congrFun (coe_toDiffeomorphOfConstFiberMap_symm ..) p).trans <|
    (congrArg (fun f ↦ f p)
        (CoordinateHom.totalSpaceMap_def (ofBundleEquivChangeIso e₁ e₂ V).inv)).trans <|
      congrArg (TotalSpace.mk' (Fin r₁ → 𝕜) p.proj) <|
        congrArg (fun S : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜) ↦ S p.2)
          (fiberMap_ofBundleEquivChangeIso_inv e₁ e₂ V p.proj)

/-- Changing the coordinate equivalence commutes with `ofBundleEquivTotalSpaceDiffeomorph`. -/
theorem ofBundleEquivTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundleEquiv e₁ V).core.TotalSpace) :
    ofBundleEquivTotalSpaceDiffeomorph e₂ V I n (ofBundleEquivChangeDiffeomorph e₁ e₂ V I n p) =
      ofBundleEquivTotalSpaceDiffeomorph e₁ V I n p := by
  rw [ofBundleEquivChangeDiffeomorph_apply, ofBundleEquivTotalSpaceDiffeomorph_apply,
    ofBundleEquivTotalSpaceDiffeomorph_apply]
  have h := ofBundleEquivFiberEquiv_changeIso e₁ e₂ V p.proj p.2
  rw [fiberMap_ofBundleEquivChangeIso_hom] at h
  exact congrArg (TotalSpace.mk' F p.proj) h

end ChangeEquiv

section DualBundle

variable [CompleteSpace 𝕜] {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Reading dual-core coordinates as functionals on `V` is `C^n` on total spaces. -/
theorem contMDiff_ofBundleEquivDualFiberEquiv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofBundleEquiv e V).dual.rank → 𝕜))
      (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun p : (ofBundleEquiv e V).dual.core.TotalSpace ↦
        TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] 𝕜) p.proj
          (ofBundleEquivDualFiberEquiv e V p.proj p.2)) := by
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hU := ((ofBundleEquiv e V).dual.core.localTriv p.proj).open_source.mem_nhds <|
    ((ofBundleEquiv e V).dual.core.mem_localTriv_source p.proj p).2
      (mem_baseSet_trivializationAt F V p.proj)
  let L : (Fin (ofBundleEquiv e V).dual.rank → 𝕜) →L[𝕜] (F →L[𝕜] 𝕜) :=
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
  refine (L.contDiff.comp_contMDiffAt
    ((ofBundleEquiv e V).dual.contMDiffAt_localTriv_snd (I := I) (n := n) p)).congr_of_eventuallyEq
      ?_
  filter_upwards [hU] with q hq
  exact (ofBundleEquivDualFiberEquiv_inCoordinates e V p.proj
    (((ofBundleEquiv e V).dual.core.mem_localTriv_source p.proj q).1 hq) q.2).trans
    (ContinuousLinearMap.ext fun _ ↦ rfl)

/-- The reconstructed total space of `(ofBundleEquiv e V).dual` is `C^n` diffeomorphic to Mathlib's
dual bundle `fun x ↦ V x →L[𝕜] 𝕜`, over the identity of the base and fibrewise `𝕜`-linear via
`ofBundleEquivDualFiberEquiv`. No smoothness assumption on `V` is required. -/
noncomputable def ofBundleEquivDualTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv e V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv e V).dual.rank → 𝕜), I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)⟯
      TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜) :=
  bundleDiffeomorph (ofBundleEquivDualFiberEquiv e V)
    (contMDiff_ofBundleEquivDualFiberEquiv (I := I) (n := n) e V)

@[simp]
theorem ofBundleEquivDualTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleEquivDualTotalSpaceDiffeomorph e V I n).toHomeomorph =
      ofBundleEquivDualTotalSpaceHomeomorph e V :=
  Homeomorph.ext fun p ↦
    (bundleDiffeomorph_apply _ _ p).trans (ofBundleEquivDualTotalSpaceHomeomorph_apply e V p).symm

@[simp]
theorem ofBundleEquivDualTotalSpaceDiffeomorph_apply
    (p : (ofBundleEquiv e V).dual.core.TotalSpace) :
    ofBundleEquivDualTotalSpaceDiffeomorph e V I n p =
      ⟨p.proj, ofBundleEquivDualFiberEquiv e V p.proj p.2⟩ :=
  bundleDiffeomorph_apply _ _ p

@[simp]
theorem ofBundleEquivDualTotalSpaceDiffeomorph_symm_apply
    (p : TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜)) :
    (ofBundleEquivDualTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofBundleEquivDualFiberEquiv e V p.proj).symm p.2⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end DualBundle

section DualChange

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

private theorem dualMap_changeIso_comp :
    (dualMap (ofBundleEquivChangeIso e₁ e₂ V).hom) ≫
        (dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom) =
      𝟙 (ofBundleEquiv e₂ V).dual := by
  rw [← dualMap_comp]
  have h : (ofBundleEquivChangeIso e₂ e₁ V).hom ≫ (ofBundleEquivChangeIso e₁ e₂ V).hom =
      𝟙 (ofBundleEquiv e₂ V) := hom_ext fun x ↦
    (fiberMap_comp _ _ x).trans <|
      (congrArg₂ ContinuousLinearMap.comp
        (fiberMap_ofBundleEquivChangeIso_hom e₁ e₂ V x)
        (fiberMap_ofBundleEquivChangeIso_hom e₂ e₁ V x)).trans <|
      (show (e₁.symm.trans e₂).toContinuousLinearMap.comp
            (e₂.symm.trans e₁).toContinuousLinearMap =
          ContinuousLinearMap.id 𝕜 (Fin r₂ → 𝕜) from
        ContinuousLinearMap.ext fun v ↦
          (congrArg e₂ (e₁.symm_apply_apply (e₂.symm v))).trans
            (e₂.apply_symm_apply v)).trans (fiberMap_id (ofBundleEquiv e₂ V) x).symm
  rw [h, dualMap_id]

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of dual
core total spaces, given by the dual morphism `dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom`. -/
noncomputable def ofBundleEquivDualChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv e₁ V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv e₁ V).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv e₂ V).dual.rank → 𝕜)⟯
      (ofBundleEquiv e₂ V).dual.core.TotalSpace :=
  toDiffeomorphOfConstFiberMap I n
    (dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom) (dualMap (ofBundleEquivChangeIso e₁ e₂ V).hom)
    (dualMap_changeIso_comp e₂ e₁ V) (dualMap_changeIso_comp e₁ e₂ V)
    (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose
    (e₁.symm.trans e₂).toContinuousLinearMap.piTranspose
    (fun x ↦ (fiberMap_dualMap _ x).trans (congrArg ContinuousLinearMap.piTranspose
      (fiberMap_ofBundleEquivChangeIso_hom e₂ e₁ V x)))
    (fun x ↦ (fiberMap_dualMap _ x).trans (congrArg ContinuousLinearMap.piTranspose
      (fiberMap_ofBundleEquivChangeIso_hom e₁ e₂ V x)))
    fun x b v ↦ by
      let T₁ : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜) := (ofBundleEquiv e₁ V).core.coordChange b x x
      let T₂ : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜) := (ofBundleEquiv e₂ V).core.coordChange b x x
      have hcomp : T₂.piTranspose.comp (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose =
          (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose.comp T₁.piTranspose := by
        rw [← ContinuousLinearMap.piTranspose_comp, ← ContinuousLinearMap.piTranspose_comp]
        congr 1; ext u
        simp only [T₁, T₂, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.trans_apply, coordChange_ofBundleEquiv,
          ContinuousLinearEquiv.symm_apply_apply]
      exact congrArg (fun S : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜) ↦ S v) hcomp

@[simp]
theorem ofBundleEquivDualChangeDiffeomorph_apply
    (p : (ofBundleEquiv e₁ V).dual.core.TotalSpace) :
    ofBundleEquivDualChangeDiffeomorph e₁ e₂ V I n p =
      (dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom).totalSpaceMap p :=
  congrFun (coe_toDiffeomorphOfConstFiberMap ..) p

@[simp]
theorem ofBundleEquivDualChangeDiffeomorph_symm_apply
    (p : (ofBundleEquiv e₂ V).dual.core.TotalSpace) :
    (ofBundleEquivDualChangeDiffeomorph e₁ e₂ V I n).symm p =
      (dualMap (ofBundleEquivChangeIso e₁ e₂ V).hom).totalSpaceMap p :=
  congrFun (coe_toDiffeomorphOfConstFiberMap_symm ..) p

end DualChange

section DualChangeCompat

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence commutes with `ofBundleEquivDualTotalSpaceDiffeomorph`. -/
theorem ofBundleEquivDualTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundleEquiv e₁ V).dual.core.TotalSpace) :
    ofBundleEquivDualTotalSpaceDiffeomorph e₂ V I n
        (ofBundleEquivDualChangeDiffeomorph e₁ e₂ V I n p) =
      ofBundleEquivDualTotalSpaceDiffeomorph e₁ V I n p := by
  rw [ofBundleEquivDualChangeDiffeomorph_apply, ofBundleEquivDualTotalSpaceDiffeomorph_apply,
    ofBundleEquivDualTotalSpaceDiffeomorph_apply, CoordinateHom.totalSpaceMap_def]
  exact congrArg (TotalSpace.mk' (F →L[𝕜] 𝕜) p.proj)
    (ofBundleEquivDualFiberEquiv_dualMap_changeIso e₁ e₂ V p.proj p.2)

end DualChangeCompat

end TauCeti.FiniteRankBundleCore
