/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Manifold
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# Smoothness, submersions, and smooth embeddings on iterated fibre products

For a `C^n` submersion `π : Y → M` (`1 ≤ n`) between finite-dimensional boundaryless manifolds,
this file establishes the smoothness and regularity of the Čech-nerve structure maps on the
iterated fibre products `Y^[k + 1] := TauCeti.IteratedFiberProduct π (k + 1)` equipped with
`TauCeti.iteratedFiberProductChartedSpace`:
* all coordinate projections, base projections, small diagonals, reindexing maps, face maps,
  and degeneracy maps are `C^n`;
* reindexing along an injection (in particular every face map `face i`), every coordinate
  projection `coord i`, and the common base projection `baseProj` are `C^n` submersions
  (`TauCeti.IteratedFiberProduct.isSubmersion_reindex`, `isSubmersion_face`,
  `isSubmersion_coord`, `isSubmersion_baseProj`);
* reindexing along a surjection (in particular every degeneracy `degeneracy i`) and the small
  diagonal `diag` are `C^n` smooth embeddings
  (`TauCeti.IteratedFiberProduct.isSmoothEmbedding_reindex`, `isSmoothEmbedding_degeneracy`,
  `isSmoothEmbedding_diag`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 4.26 (submersion theorem) and Theorem 6.30 (transverse fibre products).
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416.
-/

public section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti

namespace IteratedFiberProduct

section StructureMaps

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} {π : Y → M}
  [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
  (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- Every coordinate projection `Y^[k + 1] → Y` is `C^n`. -/
theorem contMDiff_coord {k : ℕ} (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY n
      (coord (π := π) i) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  exact ((contMDiff_apply (i := i)).comp
    (isSmoothEmbedding_coe_iteratedFiberProduct hn hπ k).contMDiff).congr fun y ↦
      coord_apply i y

/-- The common base projection `Y^[k + 1] → M` is `C^n`. -/
theorem contMDiff_baseProj (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IM n
      (baseProj (π := π) (k := k)) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  exact (hπ.contMDiff.comp (contMDiff_coord hn hπ 0)).congr fun y ↦ by
    rw [baseProj_def]; simp

/-- The small diagonal `Y → Y^[k + 1]` is `C^n`. -/
theorem contMDiff_diag (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff IY 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (diag (π := π) (k + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  exact (contMDiff_iteratedFiberProduct_iff hn hπ).2 fun _ ↦
    contMDiff_id.congr fun y ↦ by simp

/-- Reindexing along any map `α : Fin (m + 1) → Fin (k + 1)` is `C^n`. -/
theorem contMDiff_reindex {m k : ℕ} (α : Fin (m + 1) → Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
      (reindex (π := π) α) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  let := iteratedFiberProductChartedSpace hn hπ m
  exact (contMDiff_iteratedFiberProduct_iff hn hπ).2 fun i ↦
    (contMDiff_coord hn hπ (α i)).congr fun y ↦ by simp

/-- Every face map `Y^[k + 2] → Y^[k + 1]` is `C^n`. -/
theorem contMDiff_face {k : ℕ} (i : Fin (k + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    ContMDiff
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (face (π := π) i) := by
  rw [face_eq_reindex]
  exact contMDiff_reindex hn hπ i.succAbove

/-- Every degeneracy map `Y^[k + 1] → Y^[k + 2]` is `C^n`. -/
theorem contMDiff_degeneracy {k : ℕ} (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    ContMDiff
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ) n
      (degeneracy (π := π) i) := by
  rw [degeneracy_eq_reindex]
  exact contMDiff_reindex hn hπ i.predAbove

/-- The `a`-th coordinate differential of a reindexed tangent vector `d(reindex α) ξ` equals the
`α a`-th coordinate differential of `ξ`. -/
theorem mfderiv_coord_reindex {m k : ℕ} (α : Fin (m + 1) → Fin (k + 1)) (a : Fin (m + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ m
    ∀ ξ : TangentSpace 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) y,
      mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY
          (coord a) (y.reindex α)
          (mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
            𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) (reindex α) y ξ) =
        mfderiv 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY
          (coord (α a)) y ξ := by
  let := iteratedFiberProductChartedSpace hn hπ k
  let := iteratedFiberProductChartedSpace hn hπ m
  intro ξ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let Kk := 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
  let Km := 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
  have hcomp := mfderiv_comp (I := Kk) (I' := Km) (I'' := IY) y
    ((contMDiff_coord hn hπ a (y.reindex α)).mdifferentiableAt hn0)
    ((contMDiff_reindex hn hπ α y).mdifferentiableAt hn0)
  have hcoord_eq : coord (π := π) a ∘ reindex α = coord (α a) := funext fun _ ↦ by simp
  exact ((DFunLike.congr_fun hcomp ξ).symm).trans
    (congrArg (fun g ↦ (mfderiv Kk IY g y ξ : EY)) hcoord_eq)

/-- **Reindexing along an injective index map is a submersion.** Given any injection
`α : Fin (m + 1) → Fin (k + 1)`, the induced projection `Y^[k + 1] → Y^[m + 1]` is a `C^n`
submersion. In particular every face map and every subset projection is a submersion. -/
theorem isSubmersion_reindex {m k : ℕ} {α : Fin (m + 1) → Fin (k + 1)} (hα : Injective α) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
      (reindex (π := π) α) := by
  classical
  let := iteratedFiberProductChartedSpace hn hπ k
  let := iteratedFiberProductChartedSpace hn hπ m
  have := isManifold_iteratedFiberProduct hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ m
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let Km := 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
  refine ((contMDiff_reindex hn hπ α).isSubmersionOfComplement_of_surjective_mfderiv hn
    ?_).isSubmersion
  intro y η
  let w : Fin (m + 1) → EY :=
    mfderiv Km (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) Subtype.val (y.reindex α) η
  have hw := (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ m (y.reindex α) w).1 ⟨η, rfl⟩
  have hre (a : Fin (m + 1)) (u : EY) :
      (mfderiv IY IM π ((y.reindex α).1 a) u : EM) = mfderiv IY IM π (y.1 (α a)) u :=
    congrArg (fun x ↦ (mfderiv IY IM π x u : EM)) (by simp)
  let u₀ : TangentSpace IM y.baseProj :=
    tangentSpaceCast IM (π (y.1 (α 0))) y.baseProj (mfderiv IY IM π (y.1 (α 0)) (w 0))
  let v : Fin (k + 1) → EY := fun i ↦
    if h : ∃ a : Fin (m + 1), α a = i then w h.choose
    else (hπ.surjective_mfderiv hn0 (y.1 i) (tangentSpaceCast IM y.baseProj (π (y.1 i)) u₀)).choose
  have hv_α (a : Fin (m + 1)) : v (α a) = w a := by
    have h : ∃ b : Fin (m + 1), α b = α a := ⟨a, rfl⟩
    simp only [v, h, ↓reduceDIte]; exact congrArg w (hα h.choose_spec)
  have hdv (i : Fin (k + 1)) :
      mfderiv IY IM π (y.1 i) (v i) = tangentSpaceCast IM y.baseProj (π (y.1 i)) u₀ := by
    by_cases h : ∃ a : Fin (m + 1), α a = i
    · obtain ⟨a, rfl⟩ := h
      rw [hv_α a]
      exact (hre a (w a)).symm.trans ((hw a 0).trans (hre 0 (w 0)))
    · simp only [v, h, ↓reduceDIte]
      exact (hπ.surjective_mfderiv hn0 (y.1 i) _).choose_spec
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_eq_of_iteratedFiberProduct hn hπ k y v fun i j ↦ by
    rw [hdv i, hdv j]; rfl
  refine ⟨ξ, sub_eq_zero.1 (eq_zero_of_mfderiv_iteratedFiberProduct hn hπ m (y.reindex α) _
    fun a ↦ ?_)⟩
  rw [map_sub, sub_eq_zero, mfderiv_coord_reindex hn hπ α a y ξ, hξ (α a), hv_α a,
    mfderiv_coord_apply hn hπ a (y.reindex α) η]

/-- Every face map `Y^[k + 2] → Y^[k + 1]` of the Čech nerve is a `C^n` submersion. -/
theorem isSubmersion_face {k : ℕ} (i : Fin (k + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (face (π := π) i) := by
  rw [face_eq_reindex]
  exact isSubmersion_reindex hn hπ Fin.succAbove_right_injective

/-- Every coordinate projection `Y^[k + 1] → Y` is a `C^n` submersion. -/
theorem isSubmersion_coord {k : ℕ} (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IY n
      (coord (π := π) i) := by
  classical
  let := iteratedFiberProductChartedSpace hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_coord hn hπ i).isSubmersionOfComplement_of_surjective_mfderiv hn
    ?_).isSubmersion
  intro y v₀
  let u₀ := mfderiv IY IM π (y.1 i) v₀
  let v : Fin (k + 1) → EY := fun j ↦
    if j = i then v₀
    else (hπ.surjective_mfderiv hn0 (y.1 j)
      (tangentSpaceCast IM (π (y.1 i)) (π (y.1 j)) u₀)).choose
  have hdv (j : Fin (k + 1)) : mfderiv IY IM π (y.1 j) (v j) =
      tangentSpaceCast IM (π (y.1 i)) (π (y.1 j)) u₀ := by
    by_cases h : j = i
    · subst h; simp only [v, ↓reduceIte]; rfl
    · simp only [v, h, ↓reduceIte]
      exact (hπ.surjective_mfderiv hn0 (y.1 j) _).choose_spec
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_eq_of_iteratedFiberProduct hn hπ k y v fun j₁ j₂ ↦ by
    rw [hdv j₁, hdv j₂]; rfl
  exact ⟨ξ, by rw [hξ i]; simp [v]⟩

/-- The common base projection `Y^[k + 1] → M` is a `C^n` submersion. -/
theorem isSubmersion_baseProj (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) IM n
      (baseProj (π := π) (k := k)) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let Kk := 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
  refine ((contMDiff_baseProj hn hπ k).isSubmersionOfComplement_of_surjective_mfderiv hn
    ?_).isSubmersion
  intro y
  have hcomp : baseProj (π := π) (k := k) = π ∘ coord 0 :=
    funext fun z ↦ by rw [baseProj_def]; simp
  have hmf : (mfderiv Kk IM (baseProj (π := π) (k := k)) y : TangentSpace Kk y → EM) =
      (mfderiv Kk IM (π ∘ coord 0) y : TangentSpace Kk y → EM) :=
    funext fun ξ ↦ congrArg (fun g : IteratedFiberProduct π (k + 1) → M ↦
      (mfderiv Kk IM g y ξ : EM)) hcomp
  have hpi : MDifferentiableAt IY IM π (coord 0 y) := (hπ.contMDiff _).mdifferentiableAt hn0
  rw [hmf, mfderiv_comp y hpi ((contMDiff_coord hn hπ 0 y).mdifferentiableAt hn0),
    ContinuousLinearMap.coe_comp]
  exact (hπ.surjective_mfderiv hn0 (coord 0 y)).comp
    ((isSubmersion_coord hn hπ (0 : Fin (k + 1))).surjective_mfderiv hn0 y)

/-- **Reindexing along a surjective index map is a smooth embedding.** Given any surjection
`α : Fin (m + 1) → Fin (k + 1)`, the induced map `Y^[k + 1] → Y^[m + 1]` has a global `C^n`
left inverse and is therefore a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_reindex {m k : ℕ} {α : Fin (m + 1) → Fin (k + 1)} (hα : Surjective α) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
      (reindex (π := π) α) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  let := iteratedFiberProductChartedSpace hn hπ m
  have := isManifold_iteratedFiberProduct hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ m
  let β : Fin (k + 1) → Fin (m + 1) := surjInv hα
  have hleft : LeftInverse (reindex (π := π) β) (reindex α) := fun y ↦ by
    apply Subtype.ext
    funext i
    simpa only [coe_reindex, comp_apply] using congrArg y.1 (surjInv_eq hα i)
  exact (contMDiff_reindex hn hπ α).isSmoothEmbedding_of_leftInverse hn
    ((contMDiff_reindex hn hπ β).of_le hn) hleft

/-- Every diagonal degeneracy `Y^[k + 1] → Y^[k + 2]` of the Čech nerve is a `C^n` smooth
embedding. -/
theorem isSmoothEmbedding_degeneracy {k : ℕ} (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ) n
      (degeneracy (π := π) i) := by
  rw [degeneracy_eq_reindex]
  exact isSmoothEmbedding_reindex hn hπ i.predAbove_surjective

/-- The small diagonal `Y → Y^[k + 1]` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_diag (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    Manifold.IsSmoothEmbedding IY
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) n
      (diag (π := π) (k + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ k
  have := isManifold_iteratedFiberProduct hn hπ k
  exact (contMDiff_diag hn hπ k).isSmoothEmbedding_of_leftInverse hn
    ((contMDiff_coord hn hπ 0).of_le hn) (fun _ ↦ by simp)

end StructureMaps

end IteratedFiberProduct

end TauCeti
