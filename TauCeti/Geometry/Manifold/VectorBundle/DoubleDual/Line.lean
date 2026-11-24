/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.DoubleDual

/-!
# Double duality with values in a line bundle

For a finite-rank vector bundle `V` and a line bundle `L`, evaluation identifies `V` with
`Hom(Hom(V, L), L)`. In the induced Hom frames the two occurrences of the line transition
cancel, and evaluation is the ordinary scalar double-dual map on the model fibre. The
identification and its inverse are smooth. Taking `L` to be the density line gives the fibre
identification used for testing distributional sections of a density-valued dual.
-/

public noncomputable section

open Bundle FiberBundle
open scoped Topology ContDiff Manifold

namespace TauCeti

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (V L : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module 𝕜 (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace 𝕜 L)] [FiberBundle 𝕜 L] [VectorBundle 𝕜 𝕜 L]
  [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul 𝕜 (L x)]

/-- Evaluation identifies a finite-dimensional fibre with its double dual taken with values
in a line. Transporting `bundleDoubleDualEquiv` through a local frame of the line gives this
identification without a global nonvanishing section. -/
def bundleLineDoubleDualEquiv (x : B) : V x ≃L[𝕜] ((V x →L[𝕜] L x) →L[𝕜] L x) :=
  let d := (trivializationAt 𝕜 L x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt 𝕜 L x)
  (bundleDoubleDualEquiv (F := F) V x).trans
    (((ContinuousLinearEquiv.refl 𝕜 (V x)).arrowCongr d.symm).arrowCongr d.symm)

/-- The line-valued double-dual equivalence evaluates a line-valued functional on the vector. -/
@[simp]
theorem bundleLineDoubleDualEquiv_apply (x : B) (v : V x) (φ : V x →L[𝕜] L x) :
    bundleLineDoubleDualEquiv (F := F) V L x v φ = φ v := by
  simp [bundleLineDoubleDualEquiv,
    (trivializationAt 𝕜 L x).symm_apply_apply_mk (mem_baseSet_trivializationAt 𝕜 L x)]

/-- A line-valued functional on the inverse image evaluates by the original double-dual element. -/
@[simp]
theorem apply_bundleLineDoubleDualEquiv_symm (x : B)
    (Φ : (V x →L[𝕜] L x) →L[𝕜] L x) (φ : V x →L[𝕜] L x) :
    φ ((bundleLineDoubleDualEquiv (F := F) V L x).symm Φ) = Φ φ := by
  rw [← bundleLineDoubleDualEquiv_apply (F := F) V L x,
    ContinuousLinearEquiv.apply_symm_apply]

attribute [local instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle Bundle.ContinuousLinearMap.vectorBundle

section Frames

variable {V L} (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  (d : Trivialization 𝕜 (π 𝕜 L)) [MemTrivializationAtlas d]

/-- In any pair of vector and line frames, the line-valued identification is ordinary
double-dual evaluation in the induced Hom frames. -/
theorem bundleLineDoubleDualEquiv_inFrame {x : B} (hx : x ∈ e.baseSet ∩ d.baseSet)
    (v : V x) :
    (((e.continuousLinearMap (RingHom.id 𝕜) d).continuousLinearMap (RingHom.id 𝕜) d)
      ⟨x, bundleLineDoubleDualEquiv (F := F) V L x v⟩).2 =
        NormedSpace.inclusionInDoubleDual 𝕜 F (e ⟨x, v⟩).2 := by
  have hxd : x ∈ (e.continuousLinearMap (RingHom.id 𝕜) d).baseSet ∩ d.baseSet :=
    ⟨hx, hx.2⟩
  rw [Trivialization.apply_eq_prod_continuousLinearEquivAt 𝕜 _ x hxd,
    Trivialization.apply_eq_prod_continuousLinearEquivAt 𝕜 e x hx.1]
  simp only [Trivialization.continuousLinearEquivAt_continuousLinearMap _ _ hxd,
    Trivialization.continuousLinearEquivAt_continuousLinearMap _ _ hx]
  ext φ
  simp [NormedSpace.dual_def, d.apply_mk_symm hx.2]

/-- Applying scalar double-dual evaluation to the frame coordinates of the inverse
identification recovers the original coordinates in the induced Hom frame. -/
theorem bundleLineDoubleDualEquiv_symm_inFrame {x : B} (hx : x ∈ e.baseSet ∩ d.baseSet)
    (Φ : (V x →L[𝕜] L x) →L[𝕜] L x) :
    NormedSpace.inclusionInDoubleDual 𝕜 F
      (e ⟨x, (bundleLineDoubleDualEquiv (F := F) V L x).symm Φ⟩).2 =
        (((e.continuousLinearMap (RingHom.id 𝕜) d).continuousLinearMap (RingHom.id 𝕜) d)
          ⟨x, Φ⟩).2 := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (bundleLineDoubleDualEquiv_inFrame e d hx
      ((bundleLineDoubleDualEquiv (F := F) V L x).symm Φ)).symm

end Frames

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [ChartedSpace H B] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

/-- Evaluation into the line-valued double dual is smooth on total spaces. -/
theorem contMDiff_bundleLineDoubleDualEquiv :
    ContMDiff (I.prod 𝓘(𝕜, F))
      (I.prod 𝓘(𝕜, (F →L[𝕜] 𝕜) →L[𝕜] 𝕜)) n
      (fun p : TotalSpace F V ↦
        TotalSpace.mk' ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜)
          (E := fun x ↦ (V x →L[𝕜] L x) →L[𝕜] L x) p.proj
          (bundleLineDoubleDualEquiv (F := F) V L p.proj p.snd)) := by
  refine contMDiff_bundleMap_of_constant_coordinates (IB := I) (E₁ := V)
    (E₂ := fun x ↦ (V x →L[𝕜] L x) →L[𝕜] L x)
    (fun x v ↦ bundleLineDoubleDualEquiv (F := F) V L x v)
    (NormedSpace.inclusionInDoubleDual 𝕜 F) ?_
  intro a x hx v
  -- The preferred Hom frame is built from the preferred frames of its domain and codomain.
  exact bundleLineDoubleDualEquiv_inFrame (trivializationAt F V a) (trivializationAt 𝕜 L a)
    ⟨hx.1, hx.2.2⟩ v

/-- A finite-rank bundle and its line-valued double dual have diffeomorphic total spaces
via fibrewise evaluation. -/
def bundleLineDoubleDualDiffeomorph :
    TotalSpace F V ≃ₘ^n⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, (F →L[𝕜] 𝕜) →L[𝕜] 𝕜)⟯
      TotalSpace ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜) (fun x ↦ (V x →L[𝕜] L x) →L[𝕜] L x) :=
  bundleDiffeomorph (bundleLineDoubleDualEquiv (F := F) V L)
    (contMDiff_bundleLineDoubleDualEquiv V L)

/-- The total-space identification acts by fibrewise evaluation. -/
@[simp]
theorem bundleLineDoubleDualDiffeomorph_apply (p : TotalSpace F V) :
    bundleLineDoubleDualDiffeomorph V L (I := I) (n := n) p =
      ⟨p.proj, bundleLineDoubleDualEquiv (F := F) V L p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

/-- The inverse total-space identification acts by the inverse fibre equivalence. -/
@[simp]
theorem bundleLineDoubleDualDiffeomorph_symm_apply
    (p : TotalSpace ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜) (fun x ↦ (V x →L[𝕜] L x) →L[𝕜] L x)) :
    (bundleLineDoubleDualDiffeomorph (F := F) V L (I := I) (n := n)).symm p =
      ⟨p.proj, (bundleLineDoubleDualEquiv (F := F) V L p.proj).symm p.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end TauCeti
