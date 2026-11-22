/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# The Hessian fibre metric on the negative normal bundle

Let `i : S → M` be a nondegenerate critical submanifold of a function `f` on a boundaryless
finite-dimensional manifold, with constant Morse index `r`. For any `C^k` fibre metric `g` on the
normal bundle of `i`, the negative normal spaces form a `C^k` rank-`r` subbundle `ν⁻` of the normal
bundle (`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace`),
on which `-½ Hessₛ` is symmetric and positive definite.

This file equips `ν⁻` with the continuous Riemannian metric `-½ Hessₛ`
(`negativeNormalHessianMetric`), whose squared norm is `‖v‖² = -½ Hessₛ(v, v)`
(`norm_sq_eq_of_negativeNormalHessianMetric`), and shows that rescaling by `√ε` sends the unit
disc bundle `D(ν⁻)` continuously and injectively onto the negative disc bundle `D_ε`
(`rescale_negativeDiscBundle`).

## Main definitions and results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `negativeNormalHessianMetric`: the continuous Riemannian metric `-½ Hess` on the negative normal
  bundle `ν⁻`.
* `negativeNormalHessianMetric_inner_apply`: evaluating `negativeNormalHessianMetric` gives
  `-½ Hessₛ(u, v)`.
* `norm_sq_eq_of_negativeNormalHessianMetric`: the squared norm in `negativeNormalHessianMetric` is
  `-½ Hessₛ(v, v)`.
* `rescale_negativeDiscBundle`: rescaling by `√ε` sends `D(ν⁻)` continuously and injectively
  onto `D_ε`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.1 and 15.4.
-/

public section

noncomputable section

open Bundle Module Set Topology
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

section HessianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold J (k + 1) S]

/-- On each fibre of the negative normal bundle, `-½ Hessₛ` as a continuous bilinear form, built
by transferring the algebraic bilinear form through a local trivialization into the finite-rank
model fibre `Fin r → ℝ`. -/
private def negativeNormalHessianBilin (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (s : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    h.negativeNormalSpace hn g.toRiemannianMetric s →L[ℝ]
      h.negativeNormalSpace hn g.toRiemannianMetric s →L[ℝ] ℝ :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  letI := hV.fiberBundle
  letI := hV.vectorBundle
  let e := (trivializationAt (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
    s).continuousLinearEquivAt ℝ s (mem_baseSet_trivializationAt _ _ s)
  let V := h.negativeNormalSpace hn g.toRiemannianMetric s
  letI : IsNormableSpace ℝ V := e.isNormableSpace
  let B : (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ :=
    ((-(2⁻¹ : ℝ) • (h.normalHessian hn s).compl₁₂ V.subtype V.subtype).compl₁₂
      e.symm.toLinearMap e.symm.toLinearMap).toContinuousBilinearMap
  B.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap

private theorem negativeNormalHessianBilin_apply (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (s : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∀ u v : h.negativeNormalSpace hn g.toRiemannianMetric s,
      h.negativeNormalHessianBilin hn hk hf hdim g hr s u v =
        -(2⁻¹ * h.normalHessian hn s u v) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  intro u v
  let e := (trivializationAt (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
    s).continuousLinearEquivAt ℝ s (mem_baseSet_trivializationAt _ _ s)
  have h1 : e.symm.toLinearMap (e u) = u := e.symm_apply_apply u
  have h2 : e.symm.toLinearMap (e v) = v := e.symm_apply_apply v
  simp only [negativeNormalHessianBilin, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe, LinearMap.toContinuousBilinearMap_apply,
    LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul, Submodule.coe_subtype, neg_mul]
  rw [h1, h2]

/-- `-½ Hess` varies continuously as a section of the bilinear-form bundle of `ν⁻`. -/
private theorem continuous_negativeNormalHessianBilin (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    letI := hV.vectorBundle
    Continuous fun s ↦ TotalSpace.mk' ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ) s
      (h.negativeNormalHessianBilin hn hk hf hdim g hr s) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  refine continuous_iff_continuousAt.2 fun s₀ ↦ ?_
  let V : S → Type _ := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  set eV := trivializationAt (Fin r → ℝ) V s₀
  set eN := i.normalSpaceTrivialization hn hdim s₀
  have hs₀V : s₀ ∈ eV.baseSet := mem_baseSet_trivializationAt _ _ s₀
  have hs₀N : s₀ ∈ eN.baseSet := by
    have hmem := mem_baseSet_trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀
    rwa [i.normalSpaceFiberBundle_trivializationAt hn hdim s₀] at hmem
  -- Express the normal Hessian in the normal-bundle trivialization at `s₀`.
  obtain ⟨Q, hQ, hQe⟩ :=
    h.toIsCriticalSubmanifold.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn
      (le_self_add.trans hk) hf hdim s₀
  rw [Trivialization.continuousAt_section_iff (F := (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ)
    (E := fun s ↦ V s →L[ℝ] V s →L[ℝ] ℝ) (trivializationAt _ _ s₀)
    (mem_baseSet_trivializationAt _ _ s₀)]
  refine continuousAt_clm_apply.2 fun u ↦ continuousAt_clm_apply.2 fun v ↦ ?_
  have hcoord (w : Fin r → ℝ) :
      ContinuousAt (fun s ↦ (eN ⟨s, (eV.symm s w : i.NormalSpace s hn)⟩).2) s₀ :=
    eV.continuousAt_symm_subbundle eN (isEmbedding_totalSpace_subbundle P (Fin r → ℝ) _).continuous
      hs₀V hs₀N w
  have hQcont : ContinuousAt Q s₀ := hQ.continuousOn.continuousAt (eN.open_baseSet.mem_nhds hs₀N)
  have hval : ContinuousAt (fun s ↦ -(2⁻¹ * Q s (eN ⟨s, (eV.symm s u : i.NormalSpace s hn)⟩).2
      (eN ⟨s, (eV.symm s v : i.NormalSpace s hn)⟩).2)) s₀ :=
    (continuousAt_const.mul ((hQcont.clm_apply (hcoord u)).clm_apply (hcoord v))).neg
  refine hval.congr ?_
  filter_upwards [eV.open_baseSet.mem_nhds hs₀V, eN.open_baseSet.mem_nhds hs₀N] with s hsV hsN
  have hsymm (w : Fin r → ℝ) :
      eN.symm s (eN ⟨s, (eV.symm s w : i.NormalSpace s hn)⟩).2 =
        (eV.symm s w : i.NormalSpace s hn) :=
    eN.symm_proj_apply ⟨s, (eV.symm s w : i.NormalSpace s hn)⟩ hsN
  have hQeq : h.normalHessian hn s (eV.symm s u : i.NormalSpace s hn)
      (eV.symm s v : i.NormalSpace s hn) =
      Q s (eN ⟨s, (eV.symm s u : i.NormalSpace s hn)⟩).2
        (eN ⟨s, (eV.symm s v : i.NormalSpace s hn)⟩).2 := by
    have h1 : h.normalHessian hn s (eN.symm s (eN ⟨s, (eV.symm s u : i.NormalSpace s hn)⟩).2)
        (eN.symm s (eN ⟨s, (eV.symm s v : i.NormalSpace s hn)⟩).2) =
        Q s (eN ⟨s, (eV.symm s u : i.NormalSpace s hn)⟩).2
          (eN ⟨s, (eV.symm s v : i.NormalSpace s hn)⟩).2 :=
      (hQe s hsN _ _).1
    rwa [hsymm u, hsymm v] at h1
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hsV hsV (by simp),
    negativeNormalHessianBilin_apply, hQeq, Trivialization.linearMapAt_def_of_mem _ (by simp)]
  rfl

/-- **The Hessian fibre metric on the negative normal bundle.** On the negative normal subbundle
`ν⁻` of a Morse–Bott critical submanifold `i : S → M` of constant index `r`, the symmetric
bilinear form `-½ Hessₛ` is positive definite and varies continuously along `S`, equipping `ν⁻`
with a continuous Riemannian metric whose squared norm is `-½ Hessₛ(v, v)`. -/
def negativeNormalHessianMetric (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    letI := hV.vectorBundle
    ContinuousRiemannianMetric (Fin r → ℝ)
      (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  letI := hV.fiberBundle
  letI := hV.vectorBundle
  { inner := h.negativeNormalHessianBilin hn hk hf hdim g hr
    symm := fun s u v ↦ by
      simp only [negativeNormalHessianBilin_apply]
      rw [(h.isSymm_normalHessian hn s).eq]
    pos := fun s u hu ↦ by
      rw [negativeNormalHessianBilin_apply]
      have hneg := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g.toRiemannianMetric
        u.property (Subtype.coe_ne_coe.mpr hu)
      linarith
    isVonNBounded := fun s ↦ by
      let e := (trivializationAt (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) s).continuousLinearEquivAt ℝ s
        (mem_baseSet_trivializationAt _ _ s)
      let : IsNormableSpace ℝ (h.negativeNormalSpace hn g.toRiemannianMetric s) := e.isNormableSpace
      let c := (h.negativeNormalHessianBilin hn hk hf hdim g hr s).bilinearComp
        e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap
      have hc : Bornology.IsVonNBounded ℝ {v : Fin r → ℝ | c v v < 1} :=
        c.isVonNBounded_setOf_lt_one_of_pos fun v hv ↦ by
          simp only [c, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
            negativeNormalHessianBilin_apply]
          have hneg := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn
            g.toRiemannianMetric (e.symm v).property
            (Subtype.coe_ne_coe.mpr (e.symm.map_ne_zero_iff.mpr hv))
          linarith
      exact Bornology.IsVonNBounded.subset
        (s₂ := e.symm.toContinuousLinearMap '' {v : Fin r → ℝ | c v v < 1})
        (fun v hv ↦ ⟨e v, by simpa [c] using hv, by simp⟩)
        (hc.image e.symm.toContinuousLinearMap)
    continuous := h.continuous_negativeNormalHessianBilin hn hk hf hdim g hr }

/-- Evaluating the Hessian fibre metric on the negative normal bundle gives `-½ Hessₛ(u, v)`. -/
@[simp]
theorem negativeNormalHessianMetric_inner_apply (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (s : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    letI := hV.vectorBundle
    ∀ u v : h.negativeNormalSpace hn g.toRiemannianMetric s,
      (h.negativeNormalHessianMetric hn hk hf hdim g hr).inner s u v =
        -(2⁻¹ * h.normalHessian hn s u v) :=
  h.negativeNormalHessianBilin_apply hn hk hf hdim g hr s

/-- In the Hessian fibre metric on the negative normal bundle, the squared norm of a negative
normal vector `v` is `-½ Hessₛ(v, v)`. -/
@[simp]
theorem norm_sq_eq_of_negativeNormalHessianMetric (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (s : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    letI := hV.vectorBundle
    letI ν : S → Type _ := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
    letI : RiemannianBundle ν :=
      ⟨(h.negativeNormalHessianMetric hn hk hf hdim g hr).toRiemannianMetric⟩
    letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
    ∀ v : ν s, ‖v‖ ^ 2 = -(2⁻¹ * h.normalHessian hn s v v) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let ν : S → Type _ := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn hk hf hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  intro v
  rw [← real_inner_self_eq_norm_sq]
  exact h.negativeNormalHessianMetric_inner_apply hn hk hf hdim g hr s v v

end HessianMetric

section Rescale

universe u

variable {E : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} {S : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold J (k + 1) S]

/-- Rescaling vectors in the negative normal bundle `ν⁻` by `√ε` sends the unit disc bundle
`D(ν⁻)` for the Hessian fibre metric continuously and injectively onto the negative disc bundle
`D_ε`, with `-½ Hess(√ε • v, √ε • v) = ε ‖v‖²`. -/
theorem rescale_negativeDiscBundle (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) {ε : ℝ} (hε : 0 < ε) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
    letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
      subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
    letI : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
    letI : RiemannianBundle ν :=
      ⟨(h.negativeNormalHessianMetric hn hk hf hdim g hr).toRiemannianMetric⟩
    letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
    let scale : TotalSpace (Fin r → ℝ) ν → TotalSpace P (fun s ↦ i.NormalSpace s hn) :=
      fun v ↦ TotalSpace.mk' P v.proj (Real.sqrt ε • v.snd.val)
    Continuous scale ∧ Function.Injective scale ∧
      (∀ v, -(2⁻¹ * h.normalHessian hn (scale v).proj (scale v).snd (scale v).snd) =
        ε * ‖v.snd‖ ^ 2) ∧
      scale '' discBundle (Fin r → ℝ) ν = h.negativeDiscBundle hn P g.toRiemannianMetric ε := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn hk hf hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  have hsq : Real.sqrt ε ≠ 0 := Real.sqrt_ne_zero'.mpr hε
  let scale : TotalSpace (Fin r → ℝ) ν → TotalSpace P (fun s ↦ i.NormalSpace s hn) :=
    fun v ↦ TotalSpace.mk' P v.proj (Real.sqrt ε • v.snd.val)
  have hcont : Continuous scale :=
    (Continuous.smul_totalSpace continuous_const continuous_id).comp
      (isEmbedding_totalSpace_subbundle P (Fin r → ℝ)
        (h.negativeNormalSpace hn g.toRiemannianMetric)).continuous
  have hinj : Function.Injective scale := by
    intro ⟨s₁, v₁⟩ ⟨s₂, v₂⟩ hEq
    obtain rfl : s₁ = s₂ := congrArg TotalSpace.proj hEq
    dsimp only [scale, TotalSpace.mk'] at hEq
    have h2 : Real.sqrt ε • v₁.val = Real.sqrt ε • v₂.val :=
      (TotalSpace.mk_inj (E := fun s ↦ i.NormalSpace s hn)).mp hEq
    exact congrArg (TotalSpace.mk s₁) (Subtype.ext (smul_right_injective _ hsq h2))
  have hhess (v : TotalSpace (Fin r → ℝ) ν) :
      -(2⁻¹ * h.normalHessian hn (scale v).proj (scale v).snd (scale v).snd) = ε * ‖v.snd‖ ^ 2 := by
    have hnorm := h.norm_sq_eq_of_negativeNormalHessianMetric hn hk hf hdim g hr v.proj v.snd
    simp only [scale, TotalSpace.mk', map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hnorm]
    have : Real.sqrt ε * (Real.sqrt ε * h.normalHessian hn v.proj v.snd.val v.snd.val) =
        Real.sqrt ε ^ 2 * h.normalHessian hn v.proj v.snd.val v.snd.val := by ring
    rw [this, Real.sq_sqrt hε.le]
    ring
  refine ⟨hcont, hinj, hhess, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine (IsCriticalSubmanifold.mem_negativeDiscBundle hn).2
      ⟨Submodule.smul_mem _ _ v.snd.property, ?_⟩
    rw [hhess v]
    have hle : ‖v.snd‖ ^ 2 ≤ 1 := by nlinarith [mem_discBundle.1 hv, norm_nonneg v.snd]
    nlinarith
  · intro x hx
    obtain ⟨hxmem, hxle⟩ := (IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx
    let v : TotalSpace (Fin r → ℝ) ν :=
      ⟨x.proj, ⟨(Real.sqrt ε)⁻¹ • x.snd, Submodule.smul_mem _ _ hxmem⟩⟩
    have hsv : scale v = x := by
      cases x
      simp [scale, v, TotalSpace.mk', smul_inv_smul₀ hsq]
    refine ⟨v, mem_discBundle.2 ?_, hsv⟩
    have hsqle : ε * ‖v.snd‖ ^ 2 ≤ ε := by
      rw [← hhess v, hsv]
      exact hxle
    have hle1 : ‖v.snd‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg v.snd]

end Rescale

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
