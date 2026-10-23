/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Noncompact
public import TauCeti.Geometry.Manifold.TubularNeighborhood.WholeBundle.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Whole normal bundles over noncompact Euclidean submanifolds

The noncompact Euclidean tubular-neighborhood theorem supplies a positive continuous radius on
which the normal addition map is an open embedding.  This file radially compresses every normal
fibre into that variable-radius tube, extending the bounded result to the whole normal bundle.
The construction is topological; a smooth vector-bundle structure and smoothness of the inverse
remain separate parts of the tubular-neighbourhood theorem.

The radial formulas are the variable-radius analogue of `normalBundleHomeomorphTube`.  They use
no compactness and preserve the zero section, so the resulting whole-bundle embedding can be used
by the `IsTubularNeighborhood` interface.

The construction follows Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.24.
-/

public section

noncomputable section

open Set Function Topology Bundle Metric
open scoped Manifold ContMDiff Set.Notation

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Radially compressing each normal fibre by its positive continuous radius identifies the whole
normal bundle with the corresponding variable-radius open tube. -/
def normalBundleHomeomorphTubeOfRadius (f : M → V) (r : C(M, ℝ))
    (hr : ∀ x, 0 < r x) :
    TotalSpace V (fun x : M => normalSubspace I f x) ≃ₜ normalTubeOfRadius I f r where
  toFun p :=
    ⟨(p.proj, r p.proj • ((Homeomorph.unitBall p.2 : normalSubspace I f p.proj) : V)),
      mem_normalTubeOfRadius.mpr ⟨(normalSubspace I f p.proj).smul_mem (r p.proj)
        (Homeomorph.unitBall p.2).1.2, by
          rw [norm_smul, Real.norm_of_nonneg (hr p.proj).le]
          exact (mul_lt_mul_of_pos_left
            (mem_ball_zero_iff.mp (Homeomorph.unitBall p.2).2) (hr p.proj)).trans_eq
              (mul_one (r p.proj))⟩⟩
  invFun q :=
    ⟨q.1.1, Homeomorph.unitBall.symm
      ⟨(r q.1.1)⁻¹ • (⟨q.1.2, (mem_normalTubeOfRadius.mp q.2).1⟩ :
          normalSubspace I f q.1.1), by
        rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (hr q.1.1).le]
        exact (inv_mul_lt_iff₀ (hr q.1.1)).mpr (by simpa using (mem_normalTubeOfRadius.mp q.2).2)⟩⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    dsimp only
    congr 1
    rw [← Homeomorph.symm_apply_apply Homeomorph.unitBall v]
    congr 1
    apply Subtype.ext
    simp [smul_smul, (hr x).ne']
  right_inv q := by
    apply Subtype.ext
    dsimp only
    apply Prod.ext
    · rfl
    · simp [smul_smul, (hr q.1.1).ne']
  continuous_toFun := by
    have hι := isEmbedding_totalSpace_normalSubspace (I := I) (F := V) f
    have hv := hι.continuous.snd
    have ha : Continuous fun p : TotalSpace V (fun x : M => normalSubspace I f x) =>
        (Real.sqrt (1 + ‖(p.2 : V)‖ ^ 2))⁻¹ :=
      ((continuous_const.add (hv.norm.pow 2)).sqrt).inv₀
        (fun p => Real.sqrt_ne_zero'.mpr (by simpa using zero_lt_one_add_norm_sq (p.2 : V)))
    have hrp : Continuous fun p : TotalSpace V (fun x : M => normalSubspace I f x) => r p.proj :=
      r.continuous.comp hι.continuous.fst
    apply Continuous.subtype_mk
    convert hι.continuous.fst.prodMk (hrp.smul (ha.smul hv)) using 1
    funext p
    dsimp only
    simp [Homeomorph.unitBall_apply_coe, OpenPartialHomeomorph.univUnitBall_apply]
  continuous_invFun := by
    have hι := isEmbedding_totalSpace_normalSubspace (I := I) (F := V) f
    have hrq : Continuous fun q : normalTubeOfRadius I f r => (r q.1.1)⁻¹ :=
      (r.continuous.comp (continuous_fst.comp continuous_subtype_val)).inv₀
        (fun q => (hr q.1.1).ne')
    have hv : Continuous fun q : normalTubeOfRadius I f r =>
        (r q.1.1)⁻¹ • q.1.2 :=
      hrq.smul (continuous_snd.comp continuous_subtype_val)
    let k : normalTubeOfRadius I f r → ball (0 : V) 1 := fun q =>
      ⟨(r q.1.1)⁻¹ • q.1.2, by
        rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (hr q.1.1).le]
        exact (inv_mul_lt_iff₀ (hr q.1.1)).mpr (by simpa using (mem_normalTubeOfRadius.mp q.2).2)⟩
    have hk : Continuous k := hv.subtype_mk _
    apply hι.isInducing.continuous_iff.mpr
    convert (continuous_fst.comp continuous_subtype_val).prodMk
      (Homeomorph.unitBall.symm.continuous.comp hk) using 1
    funext q
    apply Prod.ext
    · rfl
    · let y : ball (0 : normalSubspace I f q.1.1) 1 :=
        ⟨(r q.1.1)⁻¹ • ⟨q.1.2, (mem_normalTubeOfRadius.mp q.2).1⟩, by
          rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (hr q.1.1).le]
          exact (inv_mul_lt_iff₀ (hr q.1.1)).mpr (by simpa using (mem_normalTubeOfRadius.mp q.2).2)⟩
      have hS : Homeomorph.unitBall.symm y =
          (Real.sqrt (1 - ‖y.1‖ ^ 2))⁻¹ • y.1 := Homeomorph.unitBall_symm_apply_coe y
      have hV : Homeomorph.unitBall.symm (k q) =
          (Real.sqrt (1 - ‖(k q).1‖ ^ 2))⁻¹ • (k q).1 :=
        Homeomorph.unitBall_symm_apply_coe (k q)
      simpa only [k, y, Function.comp_apply, Submodule.coe_smul, Submodule.norm_coe]
        using congrArg ((↑) : normalSubspace I f q.1.1 → V) hS |>.trans hV.symm

@[simp]
theorem normalBundleHomeomorphTubeOfRadius_apply_fst (f : M → V) (r : C(M, ℝ))
    (hr : ∀ x, 0 < r x) (p : TotalSpace V (fun x : M => normalSubspace I f x)) :
    (normalBundleHomeomorphTubeOfRadius f r hr p).1.1 = p.proj := by
  simp [normalBundleHomeomorphTubeOfRadius]

@[simp]
theorem normalBundleHomeomorphTubeOfRadius_symm_apply_proj (f : M → V) (r : C(M, ℝ))
    (hr : ∀ x, 0 < r x) (q : normalTubeOfRadius I f r) :
    ((normalBundleHomeomorphTubeOfRadius f r hr).symm q).proj = q.1.1 := by
  simp [normalBundleHomeomorphTubeOfRadius]

@[simp]
theorem normalBundleHomeomorphTubeOfRadius_apply_snd (f : M → V) (r : C(M, ℝ))
    (hr : ∀ x, 0 < r x) (p : TotalSpace V (fun x : M => normalSubspace I f x)) :
    (normalBundleHomeomorphTubeOfRadius f r hr p).1.2 =
      r p.proj • (Real.sqrt (1 + ‖(p.2 : V)‖ ^ 2))⁻¹ • (p.2 : V) := by
  simp [normalBundleHomeomorphTubeOfRadius, Homeomorph.unitBall_apply_coe,
    OpenPartialHomeomorph.univUnitBall_apply]

@[simp]
theorem normalBundleHomeomorphTubeOfRadius_symm_apply_snd (f : M → V) (r : C(M, ℝ))
    (hr : ∀ x, 0 < r x) (q : normalTubeOfRadius I f r) :
    (((normalBundleHomeomorphTubeOfRadius f r hr).symm q).2 : V) =
      (Real.sqrt (1 - ‖(r q.1.1)⁻¹ • q.1.2‖ ^ 2))⁻¹ •
        ((r q.1.1)⁻¹ • q.1.2) := by
  let y : ball (0 : normalSubspace I f q.1.1) 1 :=
    ⟨(r q.1.1)⁻¹ • ⟨q.1.2, (mem_normalTubeOfRadius.mp q.2).1⟩, by
      rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (hr q.1.1).le]
      exact (inv_mul_lt_iff₀ (hr q.1.1)).mpr (by simpa using (mem_normalTubeOfRadius.mp q.2).2)⟩
  have hy : Homeomorph.unitBall.symm y =
      (Real.sqrt (1 - ‖y.1‖ ^ 2))⁻¹ • y.1 := Homeomorph.unitBall_symm_apply_coe y
  have hinv :
      (((normalBundleHomeomorphTubeOfRadius f r hr).symm q).2 : V) =
        ((Homeomorph.unitBall.symm y : normalSubspace I f q.1.1) : V) := by
    -- The inverse is defined with this dependent subtype; expose that definition explicitly.
    dsimp [normalBundleHomeomorphTubeOfRadius, y]
  simpa only [y, ← Submodule.norm_coe, Submodule.coe_smul, Subtype.coe_mk]
    using hinv.trans (congrArg ((↑) : normalSubspace I f q.1.1 → V) hy)

@[simp]
theorem normalBundleHomeomorphTubeOfRadius_zeroSection (f : M → V) (r : C(M, ℝ))
    (hr : ∀ x, 0 < r x) (x : M) :
    normalBundleHomeomorphTubeOfRadius f r hr (zeroSection V (fun x => normalSubspace I f x) x) =
      ⟨(x, 0), mem_normalTubeOfRadius.mpr
        ⟨(normalSubspace I f x).zero_mem, by simpa using hr x⟩⟩ := by
  apply Subtype.ext
  simp [normalBundleHomeomorphTubeOfRadius, zeroSection]

/-- The noncompact whole-bundle tubular embedding, packaged for the tubular-neighbourhood API. -/
theorem exists_isTubularNeighborhood_wholeNormalBundle [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] {f : M → V}
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f) :
    ∃ Φ : TotalSpace V (fun x : M => normalSubspace I f x) → V,
      IsTubularNeighborhood f Set.univ (Set.univ.domRestrict Φ) := by
  obtain ⟨r, hr, hemb⟩ := exists_isOpenEmbedding_normalTubeOfRadius hf himm hind
  let e := normalBundleHomeomorphTubeOfRadius (I := I) f r hr
  let Φ : TotalSpace V (fun x : M => normalSubspace I f x) → V :=
    fun p => f (e p).1.1 + (e p).1.2
  have hΦ : IsOpenEmbedding Φ := by
    have he : IsOpenEmbedding (fun p : TotalSpace V (fun x : M => normalSubspace I f x) =>
        (normalTubeOfRadius I f r).domRestrict (fun q : M × V => f q.1 + q.2) (e p)) :=
      hemb.comp e.isOpenEmbedding
    simpa only [Φ, Set.domRestrict, Function.comp_apply, e] using he
  let hι := isEmbedding_totalSpace_normalSubspace (I := I) (F := V) f
  have hzero : IsEmbedding (zeroSection V (fun x : M => normalSubspace I f x)) := by
    apply hι.of_comp_iff.mp
    convert (isEmbedding_prodMkLeft (0 : V) :
      IsEmbedding (fun x : M => (x, (0 : V)))) using 1
    funext x
    rfl
  have hmap : Φ ∘ zeroSection V (fun x : M => normalSubspace I f x) = f := by
    funext x
    dsimp [Φ]
    rw [normalBundleHomeomorphTubeOfRadius_zeroSection]
    simp
  refine ⟨Φ, ?_⟩
  refine ⟨isOpen_univ, fun x => mem_univ _, ?_,
    hΦ.comp isOpen_univ.isOpenEmbedding_subtypeVal,
    ?_, ?_, ?_⟩
  · intro x
    simpa using starConvex_univ (𝕜 := ℝ) (0 : normalSubspace I f x)
  · rw [← hmap]
    exact hΦ.isEmbedding.comp hzero
  · intro x
    exact congrFun hmap x
  · apply hι.isInducing.continuous_iff.mpr
    have hp : Continuous fun p : Icc (0 : ℝ) 1 ×
        (Set.univ : Set (TotalSpace V (fun x : M => normalSubspace I f x))) =>
          (p.2.1.proj, (p.2.1.2 : V)) :=
      hι.continuous.comp (continuous_subtype_val.comp continuous_snd)
    exact hp.fst.prodMk ((continuous_subtype_val.comp continuous_fst).smul hp.snd)

/-- A noncompact Euclidean immersion inducing the source topology has an open embedding of its
whole normal bundle. -/
theorem exists_isOpenEmbedding_wholeNormalBundle [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] {f : M → V}
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f) :
    ∃ Φ : TotalSpace V (fun x : M => normalSubspace I f x) → V, IsOpenEmbedding Φ := by
  obtain ⟨Φ, hΦ⟩ := exists_isTubularNeighborhood_wholeNormalBundle hf himm hind
  refine ⟨Φ, ?_⟩
  have hcomp := hΦ.isOpenEmbedding.comp (Homeomorph.Set.univ _).symm.isOpenEmbedding
  convert hcomp using 1
  ext p
  rfl

end TauCeti
