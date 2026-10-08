/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Tubular neighbourhoods parametrized by the whole normal bundle

For a compact embedded submanifold of a Euclidean space, the whole normal bundle is
homeomorphic to an open neighbourhood of the submanifold, inside any prescribed open
neighbourhood. The normal vectors need not be globally bounded: each fibre is compressed
radially into a ball before applying the normal map. The compression fixes the zero section
and preserves the base point.

`normalBundleHomeomorphTube` supplies the fibrewise reparametrization, with the subspace
topology on the normal bundle inherited from `M × V`. The existence theorem
`exists_isOpenEmbedding_normalBundle_subset` combines it with the bounded-radius tubular
neighbourhood theorem. This is the topological whole-bundle form; it does not assert a
smooth vector-bundle structure or smoothness of the resulting embedding.

The radial compression reuses Mathlib's `Homeomorph.unitBall`, by Yury Kudryashov and
Oliver Nash. No trivialization or framing of the normal bundle is chosen.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public section

noncomputable section

open Set Function Topology Bundle Metric
open scoped Manifold ContDiff Set.Notation

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Radially compressing each normal fibre identifies the whole normal bundle with its
open tube of radius `ε`. It preserves the base point and fixes the zero section. -/
def normalBundleHomeomorphTube (f : M → V) {ε : ℝ} (hε : 0 < ε) :
    TotalSpace V (fun x : M => normalSubspace I f x) ≃ₜ normalTube I f ε where
  toFun p := ⟨(p.proj, ε • ((Homeomorph.unitBall p.2 : normalSubspace I f p.proj) : V)),
    mem_normalTube.mpr ⟨(normalSubspace I f p.proj).smul_mem ε (Homeomorph.unitBall p.2).1.2, by
      rw [norm_smul, Real.norm_of_nonneg hε.le]
      exact (mul_lt_mul_of_pos_left
        (mem_ball_zero_iff.mp (Homeomorph.unitBall p.2).2) hε).trans_eq (mul_one ε)⟩⟩
  invFun q := ⟨q.1.1, Homeomorph.unitBall.symm
    ⟨ε⁻¹ • (⟨q.1.2, (mem_normalTube.mp q.2).1⟩ : normalSubspace I f q.1.1), by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le]
      exact (inv_mul_lt_iff₀ hε).mpr (by simpa using (mem_normalTube.mp q.2).2)⟩⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    dsimp only
    congr 1
    rw [← Homeomorph.symm_apply_apply Homeomorph.unitBall v]
    congr 1
    apply Subtype.ext
    simp [smul_smul, hε.ne']
  right_inv q := by
    apply Subtype.ext
    dsimp only
    apply Prod.ext
    · rfl
    · simp [hε.ne', smul_smul]
  continuous_toFun := by
    have hι := isEmbedding_totalSpace_normalSubspace (I := I) (F := V) f
    have hv := hι.continuous.snd
    have ha : Continuous fun p : TotalSpace V (fun x : M => normalSubspace I f x) =>
        (Real.sqrt (1 + ‖(p.2 : V)‖ ^ 2))⁻¹ :=
      ((continuous_const.add (hv.norm.pow 2)).sqrt).inv₀
        (fun p => Real.sqrt_ne_zero'.mpr (by simpa using zero_lt_one_add_norm_sq (p.2 : V)))
    apply Continuous.subtype_mk
    convert hι.continuous.fst.prodMk ((continuous_const (y := ε)).smul (ha.smul hv)) using 1
    funext p
    dsimp only
    simp [Homeomorph.unitBall_apply_coe, OpenPartialHomeomorph.univUnitBall_apply]
  continuous_invFun := by
    have hv : Continuous fun q : normalTube I f ε => ε⁻¹ • q.1.2 :=
      continuous_const.smul (continuous_snd.comp continuous_subtype_val)
    let k : normalTube I f ε → ball (0 : V) 1 := fun q => ⟨ε⁻¹ • q.1.2, by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le]
      exact (inv_mul_lt_iff₀ hε).mpr (by simpa using (mem_normalTube.mp q.2).2)⟩
    have hk : Continuous k := hv.subtype_mk _
    apply (isEmbedding_totalSpace_normalSubspace (I := I) (F := V) f).isInducing.continuous_iff.mpr
    convert (continuous_fst.comp continuous_subtype_val).prodMk
      (Homeomorph.unitBall.symm.continuous.comp hk) using 1
    funext q
    apply Prod.ext
    · rfl
    · let y : ball (0 : normalSubspace I f q.1.1) 1 :=
        ⟨ε⁻¹ • ⟨q.1.2, (mem_normalTube.mp q.2).1⟩, by
          rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le]
          exact (inv_mul_lt_iff₀ hε).mpr (by simpa using (mem_normalTube.mp q.2).2)⟩
      -- Compose the explicit inverse formulas before rewriting: their intermediate subtypes
      -- use the source and target of the partial homeomorphism, rather than `univ` and `ball`.
      have hS : Homeomorph.unitBall.symm y = (Real.sqrt (1 - ‖y.1‖ ^ 2))⁻¹ • y.1 :=
        (Homeomorph.unitBall_symm_apply y).trans
          ((OpenPartialHomeomorph.toHomeomorphSourceTarget_symm_apply_coe
            (OpenPartialHomeomorph.univUnitBall (E := normalSubspace I f q.1.1)) y).trans
            (OpenPartialHomeomorph.univUnitBall_symm_apply y.1))
      have hV : Homeomorph.unitBall.symm (k q) =
          (Real.sqrt (1 - ‖(k q).1‖ ^ 2))⁻¹ • (k q).1 :=
        (Homeomorph.unitBall_symm_apply (k q)).trans
          ((OpenPartialHomeomorph.toHomeomorphSourceTarget_symm_apply_coe
            (OpenPartialHomeomorph.univUnitBall (E := V)) (k q)).trans
            (OpenPartialHomeomorph.univUnitBall_symm_apply (k q).1))
      simpa only [k, y, Function.comp_apply, Submodule.coe_smul, Submodule.norm_coe]
        using congrArg ((↑) : normalSubspace I f q.1.1 → V) hS |>.trans hV.symm

/-- The radial compression leaves the base point unchanged. -/
@[simp]
theorem normalBundleHomeomorphTube_apply_fst (f : M → V) {ε : ℝ} (hε : 0 < ε)
    (p : TotalSpace V (fun x : M => normalSubspace I f x)) :
    (normalBundleHomeomorphTube f hε p).1.1 = p.proj := (rfl)

/-- The inverse radial compression also leaves the base point unchanged. -/
@[simp]
theorem normalBundleHomeomorphTube_symm_apply_proj (f : M → V) {ε : ℝ} (hε : 0 < ε)
    (q : normalTube I f ε) :
    ((normalBundleHomeomorphTube f hε).symm q).proj = q.1.1 := (rfl)

/-- The fibre coordinate of radial compression, read in the ambient Euclidean space. -/
@[simp]
theorem normalBundleHomeomorphTube_apply_snd (f : M → V) {ε : ℝ} (hε : 0 < ε)
    (p : TotalSpace V (fun x : M => normalSubspace I f x)) :
    (normalBundleHomeomorphTube f hε p).1.2 =
      ε • (Real.sqrt (1 + ‖(p.2 : V)‖ ^ 2))⁻¹ • (p.2 : V) := by
  simp [normalBundleHomeomorphTube, Homeomorph.unitBall_apply_coe,
    OpenPartialHomeomorph.univUnitBall_apply]

/-- The fibre coordinate of inverse radial compression, read in the ambient Euclidean space. -/
@[simp]
theorem normalBundleHomeomorphTube_symm_apply_snd (f : M → V) {ε : ℝ} (hε : 0 < ε)
    (q : normalTube I f ε) :
    (((normalBundleHomeomorphTube f hε).symm q).2 : V) =
      (Real.sqrt (1 - ‖ε⁻¹ • q.1.2‖ ^ 2))⁻¹ • (ε⁻¹ • q.1.2) := by
  let y : ball (0 : normalSubspace I f q.1.1) 1 :=
    ⟨ε⁻¹ • ⟨q.1.2, (mem_normalTube.mp q.2).1⟩, by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le]
      exact (inv_mul_lt_iff₀ hε).mpr (by simpa using (mem_normalTube.mp q.2).2)⟩
  -- Compose the inverse formulas before coercing: the partial homeomorphism uses
  -- its source subtype, whereas `unitBall.symm` returns a vector in the normal subspace.
  have hy : Homeomorph.unitBall.symm y = (Real.sqrt (1 - ‖y.1‖ ^ 2))⁻¹ • y.1 :=
    (Homeomorph.unitBall_symm_apply y).trans
      ((OpenPartialHomeomorph.toHomeomorphSourceTarget_symm_apply_coe
        (OpenPartialHomeomorph.univUnitBall (E := normalSubspace I f q.1.1)) y).trans
        (OpenPartialHomeomorph.univUnitBall_symm_apply y.1))
  -- The inverse fibre is definitionally `unitBall.symm y`; naming its subtype input
  -- lets the explicit Mathlib formula apply without unfolding the partial homeomorphism.
  change ((Homeomorph.unitBall.symm y : normalSubspace I f q.1.1) : V) = _
  simpa only [y, ← Submodule.norm_coe, Submodule.coe_smul, Subtype.coe_mk]
    using congrArg ((↑) : normalSubspace I f q.1.1 → V) hy

/-- The zero section is carried to the zero vectors of the bounded normal tube. -/
@[simp]
theorem normalBundleHomeomorphTube_zeroSection (f : M → V) {ε : ℝ} (hε : 0 < ε)
    (x : M) :
    normalBundleHomeomorphTube f hε (zeroSection V (fun x => normalSubspace I f x) x) =
      ⟨(x, 0), mem_normalTube.mpr ⟨(normalSubspace I f x).zero_mem, by simpa using hε⟩⟩ := by
  apply Subtype.ext
  simp [normalBundleHomeomorphTube, zeroSection]

/-- **The whole normal bundle form of the tubular neighbourhood theorem.** A compact `C²`
embedded submanifold of a Euclidean space has an open tubular embedding of its entire normal
bundle inside any given open neighbourhood of its image. The embedding fixes the core. -/
theorem exists_isOpenEmbedding_normalBundle_subset [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompactSpace M]
    {f : M → V} (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hinj : Injective f)
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ Φ : TotalSpace V (fun x : M => normalSubspace I f x) → V,
      IsOpenEmbedding Φ ∧
        (∀ x, Φ (zeroSection V (fun x => normalSubspace I f x) x) = f x) ∧ range Φ ⊆ O := by
  obtain ⟨ε, hε, hemb⟩ := exists_isOpenEmbedding_normalTube hf himm hinj
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_range hf.continuous).exists_thickening_subset_open hO hfO
  let r := min ε δ
  have hr : 0 < r := lt_min hε hδ
  have hsub : normalTube I f r ⊆ normalTube I f ε := fun p hp =>
    mem_normalTube.mpr ⟨(mem_normalTube.mp hp).1,
      (mem_normalTube.mp hp).2.trans_le (min_le_left ε δ)⟩
  have hrel : IsOpen ((normalTube I f ε) ↓∩ normalTube I f r) := by
    have heq : ((normalTube I f ε) ↓∩ normalTube I f r) =
        {p : normalTube I f ε | ‖p.1.2‖ < r} := by
      ext p
      simp only [mem_preimage, mem_normalTube, mem_ofPred_eq,
        (mem_normalTube.mp p.2).1, true_and]
    rw [heq]
    exact isOpen_lt ((continuous_snd.comp continuous_subtype_val).norm) continuous_const
  have hrEmb := hemb.comp (IsOpenEmbedding.inclusion hsub hrel)
  let e := normalBundleHomeomorphTube (I := I) f hr
  let Φ : TotalSpace V (fun x : M => normalSubspace I f x) → V :=
    fun p => f (e p).1.1 + (e p).1.2
  refine ⟨Φ, hrEmb.comp e.isOpenEmbedding, ?_, ?_⟩
  · intro x
    simp [Φ, e]
  · rintro _ ⟨p, rfl⟩
    apply hδO
    refine mem_thickening_iff.mpr ⟨f (e p).1.1, mem_range_self _, ?_⟩
    simpa [Φ, dist_eq_norm] using
      (mem_normalTube.mp (e p).2).2.trans_le (min_le_right ε δ)

/-- The whole-bundle tubular embedding inside a prescribed open neighbourhood, packaged in the
`IsTubularNeighborhood` interface with domain the entire normal bundle. -/
theorem exists_isTubularNeighborhood_wholeNormalBundle_subset [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompactSpace M]
    {f : M → V} (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hinj : Injective f)
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ Φ : TotalSpace V (fun x : M => normalSubspace I f x) → V,
      IsTubularNeighborhood f univ (univ.domRestrict Φ) ∧ range Φ ⊆ O := by
  obtain ⟨Φ, hΦ, hzero, hΦO⟩ := exists_isOpenEmbedding_normalBundle_subset hf himm hinj hO hfO
  refine ⟨Φ, ⟨isOpen_univ, fun _ => mem_univ _, ?_,
    hΦ.comp isOpen_univ.isOpenEmbedding_subtypeVal,
    (hf.continuous.isClosedEmbedding hinj).isEmbedding, hzero, ?_⟩, hΦO⟩
  · intro x
    simpa using starConvex_univ (𝕜 := ℝ) (0 : normalSubspace I f x)
  · have hι := isEmbedding_totalSpace_normalSubspace (I := I) (F := V) f
    apply hι.isInducing.continuous_iff.mpr
    have hp : Continuous fun p : Icc (0 : ℝ) 1 ×
        (univ : Set (TotalSpace V (fun x : M => normalSubspace I f x))) =>
          (p.2.1.proj, (p.2.1.2 : V)) :=
      hι.continuous.comp (continuous_subtype_val.comp continuous_snd)
    exact hp.fst.prodMk ((continuous_subtype_val.comp continuous_fst).smul hp.snd)

end TauCeti
