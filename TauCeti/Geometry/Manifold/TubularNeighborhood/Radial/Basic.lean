/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.SmoothMap
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth radial coordinates on the normal bundle

Radial compression identifies the entire normal bundle of a Euclidean immersion with
the open bundle of normal balls of any positive fixed radius. This identification is a
partial diffeomorphism on the total space, with source the whole bundle. It fixes the
zero section and preserves base points. Composing it with smooth tubular coordinates
therefore gives tubular coordinates parametrized by the whole normal bundle.

Install `normalFiberBundle` locally as in `SmoothMap.lean`; its projected normal-coordinate
atlas is used in both directions. No compactness,
injectivity of the core map, or normal framing is required. A `C^(n+1)` immersion gives
`C^n` radial coordinates, including `n = ∞`.

The fibre maps reuse Mathlib's `OpenPartialHomeomorph.univUnitBall` and its smoothness
theorems, by Yury Kudryashov and Oliver Nash.
This construction adapts the radial fibre formula of Tau Ceti's prior topological
formalization `TauCeti.normalBundleHomeomorphTube` in
`TauCeti/Geometry/Manifold/TubularNeighborhood/WholeBundle.lean` to the smooth normal bundle.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.24
(tubular neighbourhoods).
-/

public section

noncomputable section

open Set Function Bundle Metric
open scoped Manifold ContDiff

namespace TauCeti

variable {V E H M F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- Scale the unit-ball radial compression in each normal fibre by `ε`, keeping its base point.
When `0 < ε`, its image in each fibre is the open ball of radius `ε`, and the inverse on
that ball is `normalBundleRadialInverse`. -/
def normalBundleRadialMap (f : M → V) (ε : ℝ)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    TotalSpace F (fun x => normalSubspace I f x) :=
  ⟨p.proj, ε • OpenPartialHomeomorph.univUnitBall p.2⟩

/-- Radial expansion in each normal fibre. Compression undoes this expansion on the
open normal ball of positive radius `ε`. -/
def normalBundleRadialInverse (f : M → V) (ε : ℝ)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    TotalSpace F (fun x => normalSubspace I f x) :=
  ⟨p.proj, OpenPartialHomeomorph.univUnitBall.symm (ε⁻¹ • p.2)⟩

/-- Radial compression preserves the base point. -/
@[simp] theorem normalBundleRadialMap_proj (f : M → V) (ε : ℝ)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    (normalBundleRadialMap f ε p).proj = p.proj := (rfl)

/-- Radial expansion preserves the base point. -/
@[simp] theorem normalBundleRadialInverse_proj (f : M → V) (ε : ℝ)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    (normalBundleRadialInverse f ε p).proj = p.proj := (rfl)

/-- Compression in ambient normal-vector coordinates. -/
@[simp] theorem normalBundleRadialMap_snd (f : M → V) (ε : ℝ)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    ((normalBundleRadialMap f ε p).2 : V) =
      ε • OpenPartialHomeomorph.univUnitBall (p.2 : V) := by
  simp [normalBundleRadialMap, OpenPartialHomeomorph.univUnitBall_apply]

/-- Expansion in ambient normal-vector coordinates. -/
@[simp] theorem normalBundleRadialInverse_snd (f : M → V) (ε : ℝ)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    ((normalBundleRadialInverse f ε p).2 : V) =
      OpenPartialHomeomorph.univUnitBall.symm (ε⁻¹ • (p.2 : V)) := by
  simp [normalBundleRadialInverse, OpenPartialHomeomorph.univUnitBall_symm_apply]

/-- Compression fixes the zero section. -/
@[simp] theorem normalBundleRadialMap_zeroSection (f : M → V) (ε : ℝ) (x : M) :
    normalBundleRadialMap f ε (zeroSection F (fun x => normalSubspace I f x) x) =
      zeroSection F (fun x => normalSubspace I f x) x := by
  dsimp [normalBundleRadialMap, zeroSection]
  congr 1
  rw [OpenPartialHomeomorph.univUnitBall_apply_zero, smul_zero]

/-- Expansion fixes the zero section. -/
@[simp] theorem normalBundleRadialInverse_zeroSection (f : M → V) (ε : ℝ) (x : M) :
    normalBundleRadialInverse f ε (zeroSection F (fun x => normalSubspace I f x) x) =
      zeroSection F (fun x => normalSubspace I f x) x := by
  dsimp [normalBundleRadialInverse, zeroSection]
  congr 1
  rw [smul_zero, OpenPartialHomeomorph.univUnitBall_symm_apply_zero]

/-- Expansion undoes compression everywhere for a nonzero radius. -/
@[simp] theorem normalBundleRadialInverse_map (f : M → V) {ε : ℝ} (hε : ε ≠ 0)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    normalBundleRadialInverse f ε (normalBundleRadialMap f ε p) = p := by
  rcases p with ⟨x, v⟩
  dsimp [normalBundleRadialMap, normalBundleRadialInverse]
  congr 1
  simp only [smul_smul, inv_mul_cancel₀ hε, one_smul]
  exact OpenPartialHomeomorph.univUnitBall.left_inv (mem_univ v)

/-- Compression undoes expansion on the open normal ball of positive radius. -/
@[simp] theorem normalBundleRadialMap_inverse (f : M → V) {ε : ℝ} (hε : 0 < ε)
    (p : TotalSpace F (fun x => normalSubspace I f x)) (hp : ‖(p.2 : V)‖ < ε) :
    normalBundleRadialMap f ε (normalBundleRadialInverse f ε p) = p := by
  rcases p with ⟨x, v⟩
  have hv : ε⁻¹ • v ∈ ball (0 : normalSubspace I f x) 1 := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le]
    exact (inv_mul_lt_iff₀ hε).mpr (by simpa using hp)
  dsimp [normalBundleRadialMap, normalBundleRadialInverse]
  congr 1
  rw [OpenPartialHomeomorph.univUnitBall.right_inv hv]
  simp [smul_smul, hε.ne']

section Smooth

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [I.Boundaryless] {n : ℕ∞} [IsManifold I (n + 1) M] {f : M → V}

/-- Radial compression is `C^n` on the entire smooth normal bundle. -/
theorem contMDiff_normalBundleRadialMap
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (ε : ℝ) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
      (normalBundleRadialMap (I := I) (F := F) f ε) := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  rw [contMDiff_normalBundle_iff hf himm hdim]
  refine ⟨?_, ?_⟩
  · simpa only [normalBundleRadialMap_proj] using
      (Bundle.contMDiff_proj (IB := I) (n := n) (fun x => normalSubspace I f x))
  · simpa only [normalBundleRadialMap_snd, Function.comp_def] using
      ((OpenPartialHomeomorph.contDiff_univUnitBall.const_smul ε).contMDiff.comp
        (contMDiff_normalBundle_snd hf himm hdim))

/-- Radial expansion is `C^n` on the open normal ball bundle of positive radius. -/
theorem contMDiffOn_normalBundleRadialInverse
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {ε : ℝ} (hε : 0 < ε) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
      (normalBundleRadialInverse (I := I) (F := F) f ε) {p | ‖(p.2 : V)‖ < ε} := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  rw [contMDiffOn_normalBundle_iff hf himm hdim]
  refine ⟨?_, ?_⟩
  · simpa only [normalBundleRadialInverse_proj] using
      (Bundle.contMDiff_proj (IB := I) (n := n) (fun x => normalSubspace I f x)).contMDiffOn
  · have hscale := (contDiff_id.const_smul ε⁻¹).contMDiff.comp
      (contMDiff_normalBundle_snd hf himm hdim)
    have hball : MapsTo (fun p : TotalSpace F (fun x => normalSubspace I f x) =>
        ε⁻¹ • (p.2 : V)) {p | ‖(p.2 : V)‖ < ε} (ball (0 : V) 1) := by
      intro p hp
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le]
      exact (inv_mul_lt_iff₀ hε).mpr (by simpa using hp)
    simpa only [normalBundleRadialInverse_snd, Function.comp_def, id_eq] using
      OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.contMDiffOn.comp
        hscale.contMDiffOn hball

/-- The whole smooth normal bundle is diffeomorphic, by radial compression, to its
open ball bundle of any positive fixed radius. The source is the entire total space. -/
def normalBundleRadialPartialDiffeomorph
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {ε : ℝ} (hε : 0 < ε) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    PartialDiffeomorph (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F))
      (TotalSpace F (fun x => normalSubspace I f x))
      (TotalSpace F (fun x => normalSubspace I f x)) n := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  exact
    { toFun := normalBundleRadialMap f ε
      invFun := normalBundleRadialInverse f ε
      source := univ
      target := {p | ‖(p.2 : V)‖ < ε}
      map_source' := fun p _ => by
        rw [mem_ofPred_eq, normalBundleRadialMap_snd, norm_smul,
          Real.norm_of_nonneg hε.le]
        have h := OpenPartialHomeomorph.univUnitBall.map_source (mem_univ (p.2 : V))
        exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp h) hε).trans_eq (mul_one ε)
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun p _ => normalBundleRadialInverse_map f hε.ne' p
      right_inv' := fun p hp => normalBundleRadialMap_inverse f hε p hp
      open_source := isOpen_univ
      open_target := isOpen_lt
        ((contMDiff_normalBundle_snd hf himm hdim).continuous.norm) continuous_const
      contMDiffOn_toFun := (contMDiff_normalBundleRadialMap hf himm hdim ε).contMDiffOn
      contMDiffOn_invFun := contMDiffOn_normalBundleRadialInverse hf himm hdim hε }

/-- The radial diffeomorphism is defined on the entire normal bundle. -/
@[simp] theorem normalBundleRadialPartialDiffeomorph_source
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {ε : ℝ} (hε : 0 < ε) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    (normalBundleRadialPartialDiffeomorph hf himm hdim hε).source = univ := (rfl)

/-- The target consists exactly of normal vectors of norm less than the radius. -/
@[simp] theorem normalBundleRadialPartialDiffeomorph_target
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {ε : ℝ} (hε : 0 < ε) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    (normalBundleRadialPartialDiffeomorph hf himm hdim hε).target =
      {p | ‖(p.2 : V)‖ < ε} := (rfl)

/-- The radial diffeomorphism acts by fibrewise compression. -/
@[simp] theorem normalBundleRadialPartialDiffeomorph_apply
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {ε : ℝ} (hε : 0 < ε)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    normalBundleRadialPartialDiffeomorph hf himm hdim hε p =
      normalBundleRadialMap f ε p := (rfl)

/-- The inverse radial diffeomorphism acts by fibrewise expansion. -/
@[simp] theorem normalBundleRadialPartialDiffeomorph_symm_apply
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {ε : ℝ} (hε : 0 < ε)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    (normalBundleRadialPartialDiffeomorph hf himm hdim hε).toPartialEquiv.symm p =
      normalBundleRadialInverse f ε p := (rfl)

end Smooth

end TauCeti
