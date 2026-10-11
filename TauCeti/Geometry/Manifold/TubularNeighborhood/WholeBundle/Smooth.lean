/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Radial.Basic
public import TauCeti.Geometry.Manifold.TubularNeighborhood.WholeBundle.Noncompact
public import TauCeti.Geometry.Manifold.TubularNeighborhood.SmoothRadius

/-!
# Smooth embeddings of whole Euclidean normal bundles

Radial compression followed by normal addition gives a smooth parametrization of an
open neighbourhood of an embedded submanifold by its entire normal bundle. The radius
may vary over a noncompact core, and the image can lie in any prescribed open neighbourhood.
The map agrees with the core embedding on the zero section.

The results establish smoothness and the open embedding property of the forward map.
Smoothness of its inverse requires local normal coordinates, independently of radial
compression. Install `normalFiberBundle` locally to use the smooth normal-bundle atlas.

The fibre formula and its smoothness reuse Mathlib's `OpenPartialHomeomorph.univUnitBall`;
the topological inverse is supplied by `normalBundleHomeomorphTubeOfRadius`.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

noncomputable section

open Set Function Bundle Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {V E H M F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- Compress each normal fibre to radius `r` and then add it to the core point.
For a tubular radius this parametrizes the normal tube using the entire normal bundle. -/
def normalBundleTubularMapOfRadius (f : M → V) (r : M → ℝ)
    (p : TotalSpace F (fun x => normalSubspace I f x)) : V :=
  f p.proj + ((normalBundleRadialMap f (r p.proj) p).2 : V)

/-- The ambient formula for the whole-normal-bundle tubular map. -/
@[simp] theorem normalBundleTubularMapOfRadius_apply (f : M → V) (r : M → ℝ)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    normalBundleTubularMapOfRadius f r p =
      f p.proj + r p.proj • OpenPartialHomeomorph.univUnitBall (p.2 : V) := by
  simp [normalBundleTubularMapOfRadius]

/-- If normal addition embeds the variable-radius tube openly, radial compression
makes the whole-normal-bundle tubular map an open embedding. Only continuity of the positive
radius is needed; the core map need not be smooth. -/
theorem isOpenEmbedding_normalBundleTubularMapOfRadius (f : M → V)
    {r : M → ℝ} (hr : Continuous r) (hrpos : ∀ x, 0 < r x)
    (hemb : IsOpenEmbedding ((normalTubeOfRadius I f r).domRestrict
      fun p : M × V => f p.1 + p.2)) :
    IsOpenEmbedding (normalBundleTubularMapOfRadius (I := I) (F := F) f r) := by
  -- The model-fibre parameter is phantom; both topologies are induced from `M × V`.
  let k : TotalSpace F (fun x => normalSubspace I f x) ≃ₜ
      TotalSpace V (fun x => normalSubspace I f x) :=
    { toFun := fun p => ⟨p.proj, p.2⟩
      invFun := fun p => ⟨p.proj, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (isEmbedding_totalSpace_normalSubspace f).isInducing.continuous_iff.mpr
        (isEmbedding_totalSpace_normalSubspace (F := F) f).continuous
      continuous_invFun :=
        (isEmbedding_totalSpace_normalSubspace (F := F) f).isInducing.continuous_iff.mpr
          (isEmbedding_totalSpace_normalSubspace (F := V) f).continuous }
  let h := k.trans (normalBundleHomeomorphTubeOfRadius (I := I) f ⟨r, hr⟩ hrpos)
  have hk (p : TotalSpace F (fun x => normalSubspace I f x)) :
      k p = ⟨p.proj, p.2⟩ := rfl
  convert hemb.comp h.isOpenEmbedding using 1
  funext p
  simp only [Function.comp_apply, h, Homeomorph.trans_apply, Set.domRestrict,
    normalBundleHomeomorphTubeOfRadius_apply_fst,
    normalBundleHomeomorphTubeOfRadius_apply_snd, normalBundleTubularMapOfRadius_apply]
  simp only [hk, ContinuousMap.coe_mk,
    OpenPartialHomeomorph.univUnitBall_apply]
  -- Evaluate the locally constructed map between the two phantom model-fibre parameters.
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [I.Boundaryless] {n : ℕ∞} [IsManifold I (n + 1) M] {f : M → V}

/-- A `C^(n+1)` immersion and a `C^n` radius give a `C^n` tubular map
on the entire normal bundle. Positivity is unnecessary for this regularity statement. -/
theorem contMDiff_normalBundleTubularMapOfRadius
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {r : M → ℝ} (hr : ContMDiff I 𝓘(ℝ) n r) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) n
      (normalBundleTubularMapOfRadius (I := I) (F := F) f r) := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  have hb := Bundle.contMDiff_proj (IB := I) (F := F) (n := n)
    (fun x => normalSubspace I f x)
  have hv := OpenPartialHomeomorph.contDiff_univUnitBall.contMDiff.comp
    (contMDiff_normalBundle_snd hf himm hdim)
  convert ((hf.of_le (by simp)).comp hb).add ((hr.comp hb).smul hv) using 1
  funext p
  exact normalBundleTubularMapOfRadius_apply f r p

omit [IsManifold I (n + 1) M] in
/-- A smooth Euclidean embedding of a boundaryless manifold has a smooth
open embedding of its entire normal bundle into any prescribed open neighbourhood of its
image. The embedding agrees with the core on the zero section. -/
theorem exists_contMDiff_isOpenEmbedding_wholeNormalBundle_subset
    [IsManifold I ∞ M]
    (hf : ContMDiff I 𝓘(ℝ, V) ∞ f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    letI := normalFiberBundle (hf.of_le (by simp)) himm hdim
    ∃ Φ : TotalSpace F (fun x => normalSubspace I f x) → V,
      ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) ∞ Φ ∧ IsOpenEmbedding Φ ∧
      (∀ x, Φ (zeroSection F (fun x => normalSubspace I f x) x) = f x) ∧ range Φ ⊆ O := by
  let := normalFiberBundle (hf.of_le (by simp)) himm hdim
  have : SecondCountableTopology M := hind.secondCountableTopology
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨r, hrpos, hemb, hOdisc⟩ :=
    exists_isOpenEmbedding_normalTubeOfRadius_contMDiff_subset (hf.of_le (by simp))
      himm hind hO hfO
  have hf' : ContMDiff I 𝓘(ℝ, V) (↑(⊤ : ℕ∞) + 1) f := by simpa using hf
  have : IsManifold I (↑(⊤ : ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  refine ⟨normalBundleTubularMapOfRadius (F := F) f r,
    contMDiff_normalBundleTubularMapOfRadius hf' himm hdim r.contMDiff,
    isOpenEmbedding_normalBundleTubularMapOfRadius f r.contMDiff.continuous hrpos hemb,
    (fun x => by simp [zeroSection]), ?_⟩
  rintro _ ⟨p, rfl⟩
  have hu : ‖OpenPartialHomeomorph.univUnitBall (p.2 : V)‖ < 1 :=
    mem_ball_zero_iff.mp
      (OpenPartialHomeomorph.univUnitBall.map_source (mem_univ (p.2 : V)))
  have hv : ‖r p.proj • OpenPartialHomeomorph.univUnitBall (p.2 : V)‖ < r p.proj := by
    rw [norm_smul, Real.norm_of_nonneg (hrpos p.proj).le]
    exact (mul_lt_mul_of_pos_left hu (hrpos p.proj)).trans_eq (mul_one _)
  rw [normalBundleTubularMapOfRadius_apply]
  exact hOdisc _ _ hv.le

end TauCeti
