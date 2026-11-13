/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.Fourier.Hardy.Basic
public import TauCeti.Analysis.InnerProductSpace.Amplification
public import TauCeti.Analysis.Normed.Lp.Interchange
public import TauCeti.MeasureTheory.Function.Lp.PiLp
import Mathlib.LinearAlgebra.Matrix.StdBasis
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.Topology.Algebra.Module.Span

/-!
# Block boundary Hardy space and matrix symbols

This file sets up the ambient `L²` orthogonal splitting and scalar matrix-entry maps that supply
the compression and entrywise reduction for block Toeplitz and block Hankel operators. For block
size `r`, `TauCeti.BlockHardySpace r` is `PiLp 2 (fun _ : Fin r ↦ HardySpace)`. Under
`MeasureTheory.Lp.piLpEquiv` and `LinearIsometryEquiv.subspacePiLp`, `TauCeti.blockHardyEquiv` and
`TauCeti.blockHardyOrthogonalEquiv` identify `BlockHardySpace r` and
`PiLp 2 (fun _ : Fin r ↦ ↥hardySubmoduleᗮ)` unitarily with `TauCeti.blockHardySubmodule r` and
`(blockHardySubmodule r)ᗮ` in `Lp (EuclideanSpace ℂ (Fin r)) 2 haarAddCircle`. Combining
`hardyBasis.repr` with `lp.piLpEquiv` gives `TauCeti.blockHardyRepr`, and the `(ℕ × Fin r)` Fourier
modes form `TauCeti.blockHardyBasis`. On `TauCeti.BlockSymbol r`, `TauCeti.blockSymbolEntry` and
`TauCeti.blockSymbolSingle` extract and insert scalar `L∞` matrix entries compatibly with algebra
operations, scalar `L∞` `•`, `ContinuousMap.toLp`, `star`, and `fourierCoeff`.

References: A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators* (2nd ed., §2.9);
J. B. Conway, *A Course in Functional Analysis* (2nd ed.); E. Park, *Toeplitz operators*.
-/

public noncomputable section

open AddCircle ContinuousLinearMap MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- The `r`-block boundary Hardy Hilbert space `PiLp 2 (fun _ : Fin r ↦ HardySpace)`. -/
abbrev BlockHardySpace (r : ℕ) := PiLp 2 (fun _ : Fin r ↦ HardySpace)

/-- Vector-valued circle Fourier mode concentrated in coordinate `i : Fin r` at frequency `n`. -/
def blockFourierMode (r : ℕ) (n : ℤ) (i : Fin r) :
    Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)) :=
  (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))).symm
    (PiLp.single 2 i (fourierBasis (T := 1) n))

/-- Coordinatewise evaluation of `blockFourierMode` under `Lp.piLpEquiv`. -/
@[simp] theorem piLpEquiv_blockFourierMode (r : ℕ) (n : ℤ) (i j : Fin r) :
    Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) (blockFourierMode r n i) j =
      if j = i then fourierBasis (T := 1) n else 0 := by simp [blockFourierMode, PiLp.single_apply]

/-- `Lp.piLpSingleLI` sends `fourierBasis n` in slot `i` to `blockFourierMode r n i`. -/
theorem piLpSingleLI_fourierBasis (r : ℕ) (n : ℤ) (i : Fin r) :
    Lp.piLpSingleLI 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) i (fourierBasis (T := 1) n) =
      blockFourierMode r n i := by rw [Lp.piLpSingleLI_eq_symm_single, blockFourierMode]

/-- Almost-everywhere pointwise evaluation of `blockFourierMode`. -/
theorem coeFn_blockFourierMode (r : ℕ) (n : ℤ) (i : Fin r) :
    blockFourierMode r n i =ᵐ[haarAddCircle (T := 1)]
      fun x ↦ EuclideanSpace.single i (fourier n x) := by
  filter_upwards [Lp.coeFn_piLpEquiv_symm_single (p := 2) (𝕜 := ℂ) (E := fun _ : Fin r ↦ ℂ) i
    (fourierBasis (T := 1) n), coeFn_fourierLp (T := 1) 2 n] with x hx hn
  rw [blockFourierMode, hx, coe_fourierBasis, hn, EuclideanSpace.single]

/-- `fourierCoeff (blockFourierMode r n i) k` is `single i 1` at `n` and `0` elsewhere. -/
@[simp] theorem fourierCoeff_blockFourierMode (r : ℕ) (n k : ℤ) (i : Fin r) :
    fourierCoeff (blockFourierMode r n i) k =
      if k = n then EuclideanSpace.single i 1 else 0 := by
  ext j; rw [fourierCoeff_piLp_apply, piLpEquiv_blockFourierMode]
  rcases eq_or_ne j i with rfl | hji
  · rw [ite_eq_left rfl, coe_fourierBasis, fourierCoeff_fourierLp]
    rcases eq_or_ne k n with rfl | hkn <;> simp [*, EuclideanSpace.single]
  · rw [ite_eq_right hji, fourierCoeff_congr_ae (Lp.coeFn_zero _ _ _)]
    rcases eq_or_ne k n with rfl | hkn <;> simp [*, fourierCoeff, EuclideanSpace.single]

/-- Closed subspace of vector-valued circle `L²` spanned by nonnegative vector Fourier modes. -/
def blockHardySubmodule (r : ℕ) :
    Submodule ℂ (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) :=
  (span ℂ (Set.range fun p : ℕ × Fin r ↦ blockFourierMode r (p.1 : ℤ) p.2)).topologicalClosure

/-- `blockHardySubmodule r` is the closed span of the nonnegative vector Fourier modes. -/
theorem blockHardySubmodule_def (r : ℕ) : blockHardySubmodule r =
    (span ℂ (Set.range fun p : ℕ × Fin r ↦ blockFourierMode r (p.1 : ℤ) p.2)).topologicalClosure :=
  (rfl)

/-- `blockHardySubmodule r` is closed in vector-valued circle `L²`. -/
theorem isClosed_blockHardySubmodule (r : ℕ) :
    IsClosed (blockHardySubmodule r :
      Set (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))) :=
  isClosed_topologicalClosure _

instance (r : ℕ) : CompleteSpace ↥(blockHardySubmodule r) :=
  (isClosed_blockHardySubmodule r).completeSpace_coe

/-- Every nonnegative vector Fourier mode belongs to `blockHardySubmodule r`. -/
theorem blockFourierMode_mem_blockHardySubmodule (r : ℕ) (n : ℕ) (i : Fin r) :
    blockFourierMode r (n : ℤ) i ∈ blockHardySubmodule r :=
  le_topologicalClosure _ (subset_span ⟨(n, i), rfl⟩)

/-- Membership in `blockHardySubmodule r` is coordinatewise membership in `hardySubmodule`. -/
theorem mem_blockHardySubmodule_iff_piLpEquiv {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) :
    f ∈ blockHardySubmodule r ↔ ∀ i : Fin r,
      Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) f i ∈ hardySubmodule := by
  set e := Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))
  refine ⟨fun hf i ↦ ?_, fun hf ↦ ?_⟩
  · let proj_i := PiLp.proj 2 (fun _ : Fin r ↦ Lp ℂ 2 (haarAddCircle (T := 1))) i ∘L
      e.toLinearIsometry.toContinuousLinearMap
    refine proj_i.continuous.apply_mem_of_mem_topologicalClosure_span isClosed_hardySubmodule ?_ hf
    rintro _ ⟨⟨n, j⟩, rfl⟩
    simp only [coe_coe, proj_i, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, PiLp.proj_apply, e, piLpEquiv_blockFourierMode]
    split_ifs; · exact fourierBasis_mem_hardySubmodule n
    exact hardySubmodule.zero_mem
  · rw [Lp.eq_sum_piLpSingleLI (𝕜 := ℂ) f]; refine (blockHardySubmodule r).sum_mem fun i _ ↦ ?_
    refine (Lp.piLpSingleLI 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) i).continuous
      |>.apply_mem_of_mem_topologicalClosure_span (isClosed_blockHardySubmodule r) ?_
        (hardySubmodule_def ▸ hf i)
    rintro _ ⟨n, rfl⟩; rw [LinearIsometry.coe_toLinearMap, piLpSingleLI_fourierBasis]
    exact blockFourierMode_mem_blockHardySubmodule r n i

/-- `f` lies in `blockHardySubmodule r` iff all negative Fourier coefficients vanish. -/
theorem mem_blockHardySubmodule_iff {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) :
    f ∈ blockHardySubmodule r ↔ ∀ n : ℤ, n < 0 → fourierCoeff f n = 0 := by
  rw [mem_blockHardySubmodule_iff_piLpEquiv]
  simp_rw [mem_hardySubmodule_iff, PiLp.ext_iff, PiLp.zero_apply, fourierCoeff_piLp_apply]
  exact ⟨fun h n hn i ↦ h i n hn, fun h i n hn ↦ h n hn i⟩

/-- The span of all vector Fourier modes is dense in vector-valued circle `L²`. -/
theorem dense_span_blockFourierMode (r : ℕ) :
    Dense (span ℂ (Set.range fun p : ℤ × Fin r ↦ blockFourierMode r p.1 p.2) :
      Set (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))) := by
  rw [dense_iff_topologicalClosure_eq_top, eq_top_iff]; intro f _
  rw [Lp.eq_sum_piLpSingleLI (𝕜 := ℂ) f]; refine Submodule.sum_mem _ fun i _ ↦ ?_
  refine (Lp.piLpSingleLI 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) i).continuous
    |>.apply_mem_of_mem_topologicalClosure_span (isClosed_topologicalClosure _) ?_
      ((fourierBasis (T := 1)).dense_span.symm ▸ mem_top)
  rintro _ ⟨n, rfl⟩; rw [LinearIsometry.coe_toLinearMap, piLpSingleLI_fourierBasis]
  exact le_topologicalClosure _ (subset_span ⟨(n, i), rfl⟩)

/-- High Fourier modes shift any vector trigonometric polynomial into `blockHardySubmodule r`. -/
theorem eventually_fourierLp_smul_mem_blockHardySubmodule {r : ℕ}
    {g : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))}
    (hg : g ∈ span ℂ (Set.range fun p : ℤ × Fin r ↦ blockFourierMode r p.1 p.2)) :
    ∀ᶠ N : ℤ in Filter.atTop,
      (fourierLp (T := 1) ∞ N • g : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) ∈
        blockHardySubmodule r := by
  have hcoord (i : Fin r) : Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) g i ∈
      span ℂ (Set.range (fourierBasis (T := 1))) := by
    induction hg using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨⟨n, j⟩, rfl⟩ := hx; rw [piLpEquiv_blockFourierMode]
      split_ifs; · exact subset_span ⟨n, rfl⟩
      exact zero_mem _
    | zero => simp
    | add _ _ _ _ hx hy => rw [map_add, PiLp.add_apply]; exact add_mem hx hy
    | smul c _ _ hx => rw [map_smul, PiLp.smul_apply]; exact smul_mem _ c hx
  filter_upwards [Filter.eventually_all.mpr fun i ↦
    eventually_fourierLp_smul_mem_hardySubmodule (hcoord i)] with N hN
  exact (mem_blockHardySubmodule_iff_piLpEquiv _).mpr fun i ↦ by
    rw [Lp.piLpEquiv_lpSMul]; exact hN i

/-- Unitary equivalence between `blockHardySubmodule r` and `BlockHardySpace r`. -/
def blockHardyEquiv (r : ℕ) : ↥(blockHardySubmodule r) ≃ₗᵢ[ℂ] BlockHardySpace r :=
  (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))).subspacePiLp
    (blockHardySubmodule r) (fun _ ↦ hardySubmodule) fun f ↦
    mem_blockHardySubmodule_iff_piLpEquiv f

/-- Coordinatewise evaluation of `blockHardyEquiv r` in circle `L²`. -/
@[simp] theorem coe_blockHardyEquiv_apply {r : ℕ} (f : ↥(blockHardySubmodule r)) (i : Fin r) :
    (blockHardyEquiv r f i : Lp ℂ 2 (haarAddCircle (T := 1))) =
      Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) f.1 i := by
  rw [blockHardyEquiv]; exact LinearIsometryEquiv.coe_subspacePiLp_apply _ _ _ _ f i

/-- Coordinatewise evaluation of `(blockHardyEquiv r).symm` under `Lp.piLpEquiv`. -/
@[simp] theorem piLpEquiv_coe_blockHardyEquiv_symm {r : ℕ} (g : BlockHardySpace r) (i : Fin r) :
    Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))
      ((blockHardyEquiv r).symm g : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) i =
      (g i : Lp ℂ 2 (haarAddCircle (T := 1))) := by
  rw [blockHardyEquiv]; exact LinearIsometryEquiv.apply_coe_subspacePiLp_symm _ _ _ _ g i

/-- Embedding a single-coordinate block Hardy vector into ambient vector `L²`. -/
theorem coe_blockHardyEquiv_symm_single {r : ℕ} (j : Fin r) (h : HardySpace) :
    ((blockHardyEquiv r).symm (PiLp.single 2 j h) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) =
      (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))).symm
        (PiLp.single 2 j (h : Lp ℂ 2 (haarAddCircle (T := 1)))) :=
  LinearIsometryEquiv.coe_subspacePiLp_symm_single _ (blockHardySubmodule r)
    (fun _ ↦ hardySubmodule) _ j h

/-- Orthogonal projection onto `blockHardySubmodule r` acts coordinatewise as Hardy projection. -/
@[simp] theorem blockHardyEquiv_orthogonalProjectionOnto {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) (i : Fin r) :
    blockHardyEquiv r ((blockHardySubmodule r).orthogonalProjectionOnto f) i =
      hardySubmodule.orthogonalProjectionOnto
        (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) f i) := by
  set e := Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))
  let p : BlockHardySpace r := WithLp.toLp 2 fun j ↦ hardySubmodule.orthogonalProjectionOnto (e f j)
  suffices h : (blockHardySubmodule r).orthogonalProjectionOnto f = (blockHardyEquiv r).symm p by
    rw [h, LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply]
  refine ext_inner_left ℂ fun w ↦ ?_
  rw [inner_orthogonalProjectionOnto_eq_of_mem_left,
    ← (blockHardySubmodule r).subtypeₗᵢ.inner_map_map, coe_subtypeₗᵢ, subtype_apply, subtype_apply,
    ← e.inner_map_map, PiLp.inner_apply, ← e.inner_map_map, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_; rw [piLpEquiv_coe_blockHardyEquiv_symm]
  exact (inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨e w.1 j, (mem_blockHardySubmodule_iff_piLpEquiv w.1).mp w.2 j⟩ (e f j)).symm

/-- Ambient `starProjection` onto `blockHardySubmodule r` acts coordinatewise. -/
@[simp] theorem piLpEquiv_blockHardySubmodule_starProjection {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) (i : Fin r) :
    Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))
      ((blockHardySubmodule r).starProjection f) i =
      hardySubmodule.starProjection
        (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) f i) := by
  rw [← coe_orthogonalProjectionOnto_apply, ← coe_orthogonalProjectionOnto_apply,
    ← coe_blockHardyEquiv_apply, blockHardyEquiv_orthogonalProjectionOnto]

/-- Orthogonal projection onto `blockHardySubmodule r` zeroes negative Fourier modes. -/
@[simp] theorem fourierCoeff_blockHardySubmodule_starProjection {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) (n : ℤ) :
    fourierCoeff ((blockHardySubmodule r).starProjection f) n =
      if 0 ≤ n then fourierCoeff f n else 0 := by
  ext i; rw [fourierCoeff_piLp_apply, piLpEquiv_blockHardySubmodule_starProjection,
    fourierCoeff_hardySubmodule_starProjection]
  split_ifs <;> simp [fourierCoeff_piLp_apply]

/-- Membership in `(blockHardySubmodule r)ᗮ` is coordinatewise membership in `hardySubmoduleᗮ`. -/
theorem mem_blockHardySubmodule_orthogonal_iff_piLpEquiv {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) :
    f ∈ (blockHardySubmodule r)ᗮ ↔ ∀ i : Fin r,
      Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) f i ∈ hardySubmoduleᗮ := by
  rw [← orthogonalProjectionOnto_eq_zero_iff, ← (blockHardyEquiv r).map_eq_zero_iff, PiLp.ext_iff]
  exact forall_congr' fun i ↦ by
    rw [PiLp.zero_apply, blockHardyEquiv_orthogonalProjectionOnto,
      orthogonalProjectionOnto_eq_zero_iff]

/-- `(blockHardySubmodule r)ᗮ` consists of vector `L²` functions with zero nonnegative modes. -/
theorem mem_blockHardySubmodule_orthogonal_iff {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) :
    f ∈ (blockHardySubmodule r)ᗮ ↔ ∀ n : ℕ, fourierCoeff f (n : ℤ) = 0 := by
  rw [mem_blockHardySubmodule_orthogonal_iff_piLpEquiv]
  simp_rw [mem_hardySubmodule_orthogonal_iff, PiLp.ext_iff, PiLp.zero_apply,
    fourierCoeff_piLp_apply]
  exact ⟨fun h n i ↦ h i n, fun h i n ↦ h n i⟩

/-- Every strictly negative vector Fourier mode belongs to `(blockHardySubmodule r)ᗮ`. -/
theorem blockFourierMode_mem_blockHardySubmodule_orthogonal (r : ℕ) (n : ℕ) (i : Fin r) :
    blockFourierMode r (-(n : ℤ) - 1) i ∈ (blockHardySubmodule r)ᗮ := by
  rw [mem_blockHardySubmodule_orthogonal_iff]; intro m
  rw [fourierCoeff_blockFourierMode, ite_eq_right (by omega)]

/-- Unitary equivalence `↥(blockHardySubmodule r)ᗮ ≃ₗᵢ[ℂ] PiLp 2 (fun _ ↦ ↥hardySubmoduleᗮ)`. -/
def blockHardyOrthogonalEquiv (r : ℕ) :
    ↥(blockHardySubmodule r)ᗮ ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Fin r ↦ ↥hardySubmoduleᗮ) :=
  (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))).subspacePiLp
    (blockHardySubmodule r)ᗮ (fun _ ↦ hardySubmoduleᗮ) fun f ↦
    mem_blockHardySubmodule_orthogonal_iff_piLpEquiv f

/-- Coordinatewise evaluation of `blockHardyOrthogonalEquiv r` in circle `L²`. -/
@[simp] theorem coe_blockHardyOrthogonalEquiv_apply {r : ℕ} (f : ↥(blockHardySubmodule r)ᗮ)
    (i : Fin r) : (blockHardyOrthogonalEquiv r f i : Lp ℂ 2 (haarAddCircle (T := 1))) =
      Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) f.1 i := by
  rw [blockHardyOrthogonalEquiv]; exact LinearIsometryEquiv.coe_subspacePiLp_apply _ _ _ _ f i

/-- Coordinatewise evaluation of `(blockHardyOrthogonalEquiv r).symm` under `Lp.piLpEquiv`. -/
@[simp] theorem piLpEquiv_coe_blockHardyOrthogonalEquiv_symm {r : ℕ}
    (g : PiLp 2 (fun _ : Fin r ↦ ↥hardySubmoduleᗮ)) (i : Fin r) :
    Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))
      ((blockHardyOrthogonalEquiv r).symm g :
        Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) i =
      (g i : Lp ℂ 2 (haarAddCircle (T := 1))) := by
  rw [blockHardyOrthogonalEquiv]; exact LinearIsometryEquiv.apply_coe_subspacePiLp_symm _ _ _ _ g i

/-- Embedding a single-coordinate vector in `PiLp 2 (fun _ ↦ ↥hardySubmoduleᗮ)` into vector `L²`. -/
theorem coe_blockHardyOrthogonalEquiv_symm_single {r : ℕ} (j : Fin r) (h : ↥hardySubmoduleᗮ) :
    ((blockHardyOrthogonalEquiv r).symm (PiLp.single 2 j h) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) =
      (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))).symm
        (PiLp.single 2 j (h : Lp ℂ 2 (haarAddCircle (T := 1)))) :=
  LinearIsometryEquiv.coe_subspacePiLp_symm_single _ (blockHardySubmodule r)ᗮ
    (fun _ ↦ hardySubmoduleᗮ) _ j h

/-- `blockHardyOrthogonalEquiv r` sends `blockFourierMode r (-n - 1) i` to `single 2 i e_{-n-1}`. -/
@[simp] theorem blockHardyOrthogonalEquiv_blockFourierMode (r : ℕ) (n : ℕ) (i : Fin r) :
    blockHardyOrthogonalEquiv r ⟨blockFourierMode r (-(n : ℤ) - 1) i,
      blockFourierMode_mem_blockHardySubmodule_orthogonal r n i⟩ =
      PiLp.single 2 i (negativeHardyBasis n) :=
  (blockHardyOrthogonalEquiv r).symm.injective <| Subtype.ext <| by
    rw [LinearIsometryEquiv.symm_apply_apply, Subtype.coe_mk,
      coe_blockHardyOrthogonalEquiv_symm_single, coe_negativeHardyBasis, blockFourierMode]

/-- Orthogonal projection onto `(blockHardySubmodule r)ᗮ` acts coordinatewise. -/
@[simp] theorem blockHardyOrthogonalEquiv_orthogonalProjectionOnto {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) (i : Fin r) :
    blockHardyOrthogonalEquiv r ((blockHardySubmodule r)ᗮ.orthogonalProjectionOnto f) i =
      hardySubmoduleᗮ.orthogonalProjectionOnto
        (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1)) f i) := Subtype.ext <| by
  rw [coe_blockHardyOrthogonalEquiv_apply, coe_orthogonalProjectionOnto_apply,
    coe_orthogonalProjectionOnto_apply, starProjection_orthogonal_val,
    starProjection_orthogonal_val, map_sub, PiLp.sub_apply,
    piLpEquiv_blockHardySubmodule_starProjection]

/-- Isometric Fourier-sequence representation of `BlockHardySpace r` in vector-valued `ℓ²`. -/
def blockHardyRepr (r : ℕ) : BlockHardySpace r ≃ₗᵢ[ℂ] lp (fun _ : ℕ ↦ EuclideanSpace ℂ (Fin r)) 2 :=
  (LinearIsometryEquiv.piLpCongrRight 2 fun _ : Fin r ↦ hardyBasis.repr).trans
    (lp.piLpEquiv 2 ℂ (fun _ : ℕ ↦ fun _ : Fin r ↦ ℂ)).symm

/-- Coordinatewise evaluation of `blockHardyRepr r`. -/
@[simp] theorem blockHardyRepr_apply {r : ℕ} (f : BlockHardySpace r) (n : ℕ) (i : Fin r) :
    blockHardyRepr r f n i = hardyBasis.repr (f i) n := by simp [blockHardyRepr]

/-- Coordinatewise evaluation of `(blockHardyRepr r).symm`. -/
@[simp] theorem blockHardyRepr_symm_apply {r : ℕ} (c : lp (fun _ : ℕ ↦ EuclideanSpace ℂ (Fin r)) 2)
    (i : Fin r) : (blockHardyRepr r).symm c i =
      hardyBasis.repr.symm (lp.piLpEquiv 2 ℂ (fun _ : ℕ ↦ fun _ : Fin r ↦ ℂ) c i) := by
  simp [blockHardyRepr]

/-- Under `blockHardyEquiv r`, `blockHardyRepr r` extracts nonnegative vector Fourier modes. -/
theorem blockHardyRepr_blockHardyEquiv_eq_fourierCoeff {r : ℕ} (f : ↥(blockHardySubmodule r))
    (n : ℕ) : blockHardyRepr r (blockHardyEquiv r f) n =
      fourierCoeff (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) (n : ℤ) :=
  PiLp.ext fun i ↦ by
    rw [blockHardyRepr_apply, hardyBasis_repr, coe_blockHardyEquiv_apply, fourierCoeff_piLp_apply]

/-- The `(ℕ × Fin r)`-indexed Fourier Hilbert basis of `BlockHardySpace r`. -/
def blockHardyBasis (r : ℕ) : HilbertBasis (ℕ × Fin r) ℂ (BlockHardySpace r) :=
  HilbertBasis.mkOfOrthogonalEqBot (v := fun p : ℕ × Fin r ↦ PiLp.single 2 p.2 (hardyBasis p.1))
    (by
      rw [orthonormal_iff_ite]; rintro ⟨m, i⟩ ⟨n, j⟩
      rw [PiLp.inner_apply, Finset.sum_eq_single i (fun k _ hki ↦ by simp [hki]) (by simp)]
      rcases eq_or_ne i j with rfl | hij <;>
        simp [*, orthonormal_iff_ite.mp hardyBasis.orthonormal])
    (by
      refine le_antisymm (fun x hx ↦ ?_) bot_le; ext i : 1; apply hardyBasis.repr.injective; ext n
      simp only [PiLp.zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply,
        HilbertBasis.repr_apply_apply]
      have hmem := (mem_orthogonal _ _).mp hx (PiLp.single 2 i (hardyBasis n))
        (subset_span ⟨(n, i), rfl⟩)
      rw [PiLp.inner_apply, Finset.sum_eq_single i (fun k _ hki ↦ by simp [hki]) (by simp)] at hmem
      simpa using hmem)

/-- Evaluation of `blockHardyBasis r` at `(n, i)` as `PiLp.single 2 i (hardyBasis n)`. -/
@[simp] theorem blockHardyBasis_apply (r : ℕ) (p : ℕ × Fin r) :
    blockHardyBasis r p = PiLp.single 2 p.2 (hardyBasis p.1) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) p

/-- Coordinate representation in `blockHardyBasis r` evaluates coordinatewise via `hardyBasis`. -/
@[simp] theorem blockHardyBasis_repr {r : ℕ} (f : BlockHardySpace r) (p : ℕ × Fin r) :
    (blockHardyBasis r).repr f p = hardyBasis.repr (f p.2) p.1 := by
  rw [HilbertBasis.repr_apply_apply, blockHardyBasis_apply, PiLp.inner_apply,
    Finset.sum_eq_single p.2 (fun k _ hkp ↦ by simp [hkp]) (by simp), PiLp.single_eq_same,
    ← HilbertBasis.repr_apply_apply]

/-- `(blockHardyEquiv r).symm` sends `blockHardyBasis r p` to `blockFourierMode r p.1 p.2`. -/
theorem coe_blockHardyEquiv_symm_blockHardyBasis (r : ℕ) (p : ℕ × Fin r) :
    ((blockHardyEquiv r).symm (blockHardyBasis r p) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) =
      blockFourierMode r (p.1 : ℤ) p.2 := by
  rw [blockHardyBasis_apply, coe_blockHardyEquiv_symm_single, coe_hardyBasis, blockFourierMode]

/-- `blockHardyEquiv r` sends `blockFourierMode r n i` to `blockHardyBasis r (n, i)`. -/
@[simp] theorem blockHardyEquiv_blockFourierMode (r : ℕ) (n : ℕ) (i : Fin r) :
    blockHardyEquiv r ⟨blockFourierMode r (n : ℤ) i,
      blockFourierMode_mem_blockHardySubmodule r n i⟩ = blockHardyBasis r (n, i) :=
  (blockHardyEquiv r).symm.injective <| Subtype.ext <| by
    rw [LinearIsometryEquiv.symm_apply_apply, coe_blockHardyEquiv_symm_blockHardyBasis]

/-- `blockHardyRepr r` sends `PiLp.single 2 i (hardyBasis n)` to `lp.single 2 n (single i 1)`. -/
@[simp] theorem blockHardyRepr_single_hardyBasis {r : ℕ} (i : Fin r) (n : ℕ) :
    blockHardyRepr r (PiLp.single 2 i (hardyBasis n)) =
      lp.single 2 n (EuclideanSpace.single i 1) := by
  ext m j; rw [blockHardyRepr_apply, lp.single_apply]
  rcases eq_or_ne m n with rfl | hmn <;> rcases eq_or_ne j i with rfl | hji <;>
    simp [*, HilbertBasis.repr_self, lp.single_apply, EuclideanSpace.single]

/-- `blockHardyRepr r` sends `blockHardyBasis r p` to `lp.single 2 p.1 (single p.2 1)`. -/
theorem blockHardyRepr_blockHardyBasis (r : ℕ) (p : ℕ × Fin r) :
    blockHardyRepr r (blockHardyBasis r p) = lp.single 2 p.1 (EuclideanSpace.single p.2 1) := by
  rw [blockHardyBasis_apply, blockHardyRepr_single_hardyBasis]

/-- `(blockHardyRepr r).symm` sends `lp.single 2 n (single i 1)` to `blockHardyBasis r (n, i)`. -/
@[simp] theorem blockHardyRepr_symm_single {r : ℕ} (n : ℕ) (i : Fin r) :
    (blockHardyRepr r).symm (lp.single 2 n (EuclideanSpace.single i 1)) =
      blockHardyBasis r (n, i) :=
  (blockHardyRepr r).symm_apply_eq.mpr (blockHardyRepr_blockHardyBasis r (n, i)).symm

/-- Matrix elements in `blockHardyBasis r` are Hardy-basis matrix elements of `T.piLpEntry`. -/
theorem inner_blockHardyBasis_apply {r : ℕ} (T : BlockHardySpace r →L[ℂ] BlockHardySpace r)
    (m n : ℕ) (i j : Fin r) :
    ⟪blockHardyBasis r (m, i), T (blockHardyBasis r (n, j))⟫_ℂ =
      ⟪hardyBasis m, T.piLpEntry i j (hardyBasis n)⟫_ℂ := by
  rw [blockHardyBasis_apply, blockHardyBasis_apply, PiLp.inner_apply,
    Finset.sum_eq_single i (fun k _ hki ↦ by simp [hki]) (by simp)]; simp

/-! ### Operator-normed matrix symbols on the unit circle -/

/-- Essentially bounded `(r × r)` operator-normed matrix symbols on the unit circle. -/
abbrev BlockSymbol (r : ℕ) :=
  Lp (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞ (haarAddCircle (T := 1))

/-- Extract the `(i, j)` scalar `L∞` entry of a block symbol `A : BlockSymbol r`. -/
def blockSymbolEntry (r : ℕ) (i j : Fin r) : BlockSymbol r →L[ℂ] Lp ℂ ∞ (haarAddCircle (T := 1)) :=
  (EuclideanSpace.proj i ∘L apply ℂ (EuclideanSpace ℂ (Fin r)) (EuclideanSpace.single j 1)).compLpL
    ∞ (haarAddCircle (T := 1))

/-- Insert a scalar `L∞` symbol into the `(i, j)` matrix-unit entry of `BlockSymbol r`. -/
def blockSymbolSingle (r : ℕ) (i j : Fin r) : Lp ℂ ∞ (haarAddCircle (T := 1)) →L[ℂ] BlockSymbol r :=
  (toSpanSingleton ℂ (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (Matrix.single i j 1))).compLpL
    ∞ (haarAddCircle (T := 1))

/-- Almost-everywhere evaluation of `blockSymbolEntry r i j A`. -/
theorem blockSymbolEntry_ae {r : ℕ} (i j : Fin r) (A : BlockSymbol r) :
    blockSymbolEntry r i j A =ᵐ[haarAddCircle (T := 1)]
      fun x ↦ A x (EuclideanSpace.single j 1) i := by
  filter_upwards [(EuclideanSpace.proj i ∘L
    apply ℂ (EuclideanSpace ℂ (Fin r)) (EuclideanSpace.single j 1)).coeFn_compLpL A] with x hx
  simpa only [blockSymbolEntry, comp_apply, apply_apply, PiLp.proj_apply] using hx

/-- Almost-everywhere evaluation of `blockSymbolSingle r i j a`. -/
theorem blockSymbolSingle_ae {r : ℕ} (i j : Fin r) (a : Lp ℂ ∞ (haarAddCircle (T := 1))) :
    blockSymbolSingle r i j a =ᵐ[haarAddCircle (T := 1)]
      fun x ↦ Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (Matrix.single i j (a x)) := by
  filter_upwards [(toSpanSingleton ℂ (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ)
    (Matrix.single i j 1))).coeFn_compLpL a] with x hx
  rw [blockSymbolSingle, hx, toSpanSingleton_apply, ← map_smul, Matrix.smul_single, smul_eq_mul,
    mul_one]

/-- Extracting entry `(i, j)` of `blockSymbolSingle r k l a` gives `a` at `(k, l)` and `0` else. -/
@[simp] theorem blockSymbolEntry_blockSymbolSingle {r : ℕ} (i j k l : Fin r)
    (a : Lp ℂ ∞ (haarAddCircle (T := 1))) :
    blockSymbolEntry r i j (blockSymbolSingle r k l a) = if i = k ∧ j = l then a else 0 := by
  by_cases h : i = k ∧ j = l
  · rcases h with ⟨rfl, rfl⟩; rw [ite_eq_left ⟨rfl, rfl⟩]; apply Lp.ext
    filter_upwards [blockSymbolEntry_ae i j (blockSymbolSingle r i j a),
      blockSymbolSingle_ae i j a] with x h₁ h₂
    simp [h₁, h₂, EuclideanSpace.single]
  · rw [ite_eq_right h]; apply Lp.ext
    filter_upwards [blockSymbolEntry_ae i j (blockSymbolSingle r k l a), blockSymbolSingle_ae k l a,
      Lp.coeFn_zero ℂ ∞ (haarAddCircle (T := 1))] with x h₁ h₂ h₀
    rw [h₁, h₂, h₀]
    simp [show ¬(k = i ∧ l = j) from fun ⟨hki, hlj⟩ ↦ h ⟨hki.symm, hlj.symm⟩, EuclideanSpace.single]

/-- Extracting entry `(i, j)` from a sum of `blockSymbolSingle` entries recovers `a i j`. -/
theorem blockSymbolEntry_sum_blockSymbolSingle {r : ℕ}
    (a : Fin r → Fin r → Lp ℂ ∞ (haarAddCircle (T := 1))) (i j : Fin r) :
    blockSymbolEntry r i j (∑ k : Fin r, ∑ l : Fin r, blockSymbolSingle r k l (a k l)) = a i j := by
  have hmap (f : Fin r → BlockSymbol r) :
      blockSymbolEntry r i j (∑ x, f x) = ∑ x, blockSymbolEntry r i j (f x) :=
    map_sum (blockSymbolEntry r i j).toLinearMap.toAddMonoidHom f Finset.univ
  simp_rw [hmap, blockSymbolEntry_blockSymbolSingle, and_comm (a := i = _), ite_and]; simp

/-- Every block symbol is the finite sum of its scalar matrix entries along the matrix units. -/
theorem eq_sum_blockSymbolSingle {r : ℕ} (A : BlockSymbol r) :
    A = ∑ i : Fin r, ∑ j : Fin r, blockSymbolSingle r i j (blockSymbolEntry r i j A) := by
  let b := (Matrix.stdBasis ℂ (Fin r) (Fin r)).map
    (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv
  have hb (i j : Fin r) :
      b (i, j) = Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (Matrix.single i j 1) := by
    simp [b, Matrix.stdBasis_eq_single]
  have hcoord (i j : Fin r) : (b.coord (i, j)).toContinuousLinearMap =
      EuclideanSpace.proj i ∘L apply ℂ (EuclideanSpace ℂ (Fin r)) (EuclideanSpace.single j 1) :=
    coe_injective <| b.ext fun ⟨k, l⟩ ↦ by
      simp only [coe_coe, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
        Module.Basis.repr_self]
      simp [hb, Finsupp.single_apply, Matrix.single_apply, Prod.mk.injEq, EuclideanSpace.single]
  simpa only [Fintype.sum_prod_type, hb, hcoord, blockSymbolSingle, blockSymbolEntry] using
    eq_sum_basis_compLpL b A

/-- Two block symbols are equal if and only if all of their scalar matrix entries agree. -/
theorem blockSymbol_ext_iff {r : ℕ} {A B : BlockSymbol r} :
    A = B ↔ ∀ i j : Fin r, blockSymbolEntry r i j A = blockSymbolEntry r i j B :=
  ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ by
    rw [eq_sum_blockSymbolSingle A, eq_sum_blockSymbolSingle B]; simp_rw [h]⟩

/-- Matrix-unit product rule `E_{i,j}(a) * E_{k,l}(b) = δ_{j,k} E_{i,l}(a * b)` on symbols. -/
@[simp] theorem blockSymbolSingle_mul_blockSymbolSingle {r : ℕ} (i j k l : Fin r)
    (a b : Lp ℂ ∞ (haarAddCircle (T := 1))) :
    blockSymbolSingle r i j a * blockSymbolSingle r k l b =
      if j = k then blockSymbolSingle r i l (a * b) else 0 := by
  rcases eq_or_ne j k with rfl | hjk
  · rw [ite_eq_left rfl]; apply Lp.ext
    filter_upwards [Lp.coeFn_mul (blockSymbolSingle r i j a) (blockSymbolSingle r j l b),
      blockSymbolSingle_ae i j a, blockSymbolSingle_ae j l b, blockSymbolSingle_ae i l (a * b),
      Lp.coeFn_mul a b] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.mul_apply, h₂, h₃, h₄, h₅, Pi.mul_apply, ← map_mul, Matrix.single_mul_single_same]
  · rw [ite_eq_right hjk]; apply Lp.ext
    filter_upwards [Lp.coeFn_mul (blockSymbolSingle r i j a) (blockSymbolSingle r k l b),
      blockSymbolSingle_ae i j a, blockSymbolSingle_ae k l b,
      Lp.coeFn_zero (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
        (haarAddCircle (T := 1))] with x h₁ h₂ h₃ h₀
    rw [h₁, Pi.mul_apply, h₂, h₃, h₀, Pi.zero_apply, ← map_mul]; simp [hjk]

/-- The `(i, j)` scalar entry of `A * B` is the matrix product sum of their scalar entries. -/
theorem blockSymbolEntry_mul {r : ℕ} (A B : BlockSymbol r) (i j : Fin r) :
    blockSymbolEntry r i j (A * B) =
      ∑ k : Fin r, blockSymbolEntry r i k A * blockSymbolEntry r k j B := Lp.ext <| by
  filter_upwards [blockSymbolEntry_ae i j (A * B), Lp.coeFn_mul A B,
    Lp.coeFn_fun_finsetSum Finset.univ fun k ↦ blockSymbolEntry r i k A * blockSymbolEntry r k j B,
    ae_all_iff.mpr fun k ↦ (Lp.coeFn_mul (blockSymbolEntry r i k A) (blockSymbolEntry r k j B)).and
      ((blockSymbolEntry_ae i k A).and (blockSymbolEntry_ae k j B))] with x h₁ h₂ hsum hk
  rw [h₁, h₂, Pi.mul_apply, mul_apply_eq_comp, hsum]
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin r) ℂ).sum_repr (B x (EuclideanSpace.single j 1))]
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, map_sum, WithLp.ofLp_sum,
    Finset.sum_apply, map_smul, PiLp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [(hk k).1, Pi.mul_apply, (hk k).2.1, (hk k).2.2, mul_comm]

/-- Scalar `(i, j)` entry of a constant operator-valued circle symbol. -/
@[simp] theorem blockSymbolEntry_const {r : ℕ}
    (M : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) (i j : Fin r) :
    blockSymbolEntry r i j (Lp.const ∞ (haarAddCircle (T := 1)) M) =
      Lp.const ∞ (haarAddCircle (T := 1)) (M (EuclideanSpace.single j 1) i) := Lp.ext <| by
  filter_upwards [blockSymbolEntry_ae i j (Lp.const ∞ (haarAddCircle (T := 1)) M),
    Lp.coeFn_const ∞ (haarAddCircle (T := 1)) M,
    Lp.coeFn_const ∞ (haarAddCircle (T := 1)) (M (EuclideanSpace.single j 1) i)] with x h₁ h₂ h₃
  simp only [h₁, h₂, h₃, Function.const_apply]

/-- Scalar `(i, j)` entry of `algebraMap ℂ (BlockSymbol r) c`. -/
@[simp] theorem blockSymbolEntry_algebraMap {r : ℕ} (c : ℂ) (i j : Fin r) :
    blockSymbolEntry r i j ((algebraMap ℂ (BlockSymbol r) : ℂ →+* BlockSymbol r) c) =
      if i = j then algebraMap ℂ (Lp ℂ ∞ (haarAddCircle (T := 1))) c else 0 := by
  rw [Lp.algebraMap_eq_const, blockSymbolEntry_const, Algebra.algebraMap_eq_smul_one]
  rcases eq_or_ne i j with rfl | hij <;> simp [*, Lp.algebraMap_eq_const, EuclideanSpace.single]

/-- Scalar `(i, j)` entry of `1 : BlockSymbol r` is `1` on the diagonal and `0` off it. -/
@[simp] theorem blockSymbolEntry_one {r : ℕ} (i j : Fin r) :
    blockSymbolEntry r i j (1 : BlockSymbol r) = if i = j then 1 else 0 := by
  simpa using blockSymbolEntry_algebraMap (r := r) 1 i j

/-- Scalar `L∞` action on `BlockSymbol r` acts by multiplication on every matrix entry. -/
theorem blockSymbolEntry_lpSMul {r : ℕ} (a : Lp ℂ ∞ (haarAddCircle (T := 1)))
    (A : BlockSymbol r) (i j : Fin r) :
    blockSymbolEntry r i j (a • A : BlockSymbol r) = a * blockSymbolEntry r i j A := Lp.ext <| by
  filter_upwards [blockSymbolEntry_ae i j (a • A : BlockSymbol r), Lp.coeFn_lpSMul (r := ∞) a A,
    Lp.coeFn_mul a (blockSymbolEntry r i j A), blockSymbolEntry_ae i j A] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply', smul_apply, PiLp.smul_apply, smul_eq_mul, h₃, Pi.mul_apply, h₄]

/-- Scalar `L∞` action on `blockSymbolSingle r i j b` multiplies its scalar entry by `a`. -/
@[simp] theorem blockSymbolSingle_lpSMul {r : ℕ} (i j : Fin r)
    (a b : Lp ℂ ∞ (haarAddCircle (T := 1))) :
    (a • blockSymbolSingle r i j b : BlockSymbol r) = blockSymbolSingle r i j (a * b) := by
  rw [blockSymbol_ext_iff]; intro k l
  rw [blockSymbolEntry_lpSMul, blockSymbolEntry_blockSymbolSingle,
    blockSymbolEntry_blockSymbolSingle]; split_ifs <;> simp

/-- Scalar `(i, j)` entry of `a • (1 : BlockSymbol r)` is `a` on the diagonal and `0` off it. -/
theorem blockSymbolEntry_smul_one {r : ℕ} (a : Lp ℂ ∞ (haarAddCircle (T := 1))) (i j : Fin r) :
    blockSymbolEntry r i j (a • (1 : BlockSymbol r) : BlockSymbol r) = if i = j then a else 0 := by
  rw [blockSymbolEntry_lpSMul, blockSymbolEntry_one]; split_ifs <;> simp

/-- Extracting the `(i, j)` scalar entry commutes with `ContinuousMap.toLp ∞`. -/
@[simp] theorem blockSymbolEntry_toLp {r : ℕ}
    (F : C(UnitAddCircle, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) (i j : Fin r) :
    blockSymbolEntry r i j (ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ F) =
      ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ
        ⟨fun x ↦ F x (EuclideanSpace.single j 1) i, by fun_prop⟩ := Lp.ext <| by
  filter_upwards [blockSymbolEntry_ae i j (ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ F),
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (haarAddCircle (T := 1)) F,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (haarAddCircle (T := 1))
      ⟨fun x ↦ F x (EuclideanSpace.single j 1) i, by fun_prop⟩] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]; simp

/-- Entry `(i, j)` of `star A` is `star` of entry `(j, i)` of `A`. -/
@[simp] theorem blockSymbolEntry_star {r : ℕ} (A : BlockSymbol r) (i j : Fin r) :
    blockSymbolEntry r i j (star A) = star (blockSymbolEntry r j i A) := Lp.ext <| by
  filter_upwards [blockSymbolEntry_ae i j (star A), Lp.coeFn_star A,
    Lp.coeFn_star (blockSymbolEntry r j i A), blockSymbolEntry_ae j i A] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.star_apply, Pi.star_apply, h₄, star_eq_adjoint]
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, RCLike.star_def] using
    adjoint_inner_right (A x) (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j (1 : ℂ))

/-- `star` on `blockSymbolSingle r i j a` transposes `(i, j)` to `(j, i)` and conjugates `a`. -/
@[simp] theorem star_blockSymbolSingle {r : ℕ} (i j : Fin r) (a : Lp ℂ ∞ (haarAddCircle (T := 1))) :
    star (blockSymbolSingle r i j a) = blockSymbolSingle r j i (star a) := by
  rw [blockSymbol_ext_iff]; intro k l
  rw [blockSymbolEntry_star, blockSymbolEntry_blockSymbolSingle, blockSymbolEntry_blockSymbolSingle]
  by_cases hkl : k = j ∧ l = i
  · rcases hkl with ⟨rfl, rfl⟩; simp
  · simp [hkl, show ¬(l = i ∧ k = j) from fun ⟨hli, hkj⟩ ↦ hkl ⟨hkj, hli⟩]

/-- Scalar `(i, j)` Fourier coefficient of `A` equals entry `(i, j)` of `fourierCoeff A n`. -/
theorem fourierCoeff_blockSymbolEntry {r : ℕ} (A : BlockSymbol r) (i j : Fin r) (n : ℤ) :
    fourierCoeff (blockSymbolEntry r i j A) n = fourierCoeff A n (EuclideanSpace.single j 1) i := by
  let entry : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) →L[ℂ] ℂ :=
    EuclideanSpace.proj i ∘L apply ℂ (EuclideanSpace ℂ (Fin r)) (EuclideanSpace.single j 1)
  have hae : blockSymbolEntry r i j A =ᵐ[haarAddCircle (T := 1)] fun x ↦ entry (A x) :=
    (blockSymbolEntry_ae i j A).mono fun x hx ↦ by simp [hx, entry]
  rw [fourierCoeff_congr_ae hae, entry.fourierCoeff_comp ((Lp.memLp A).integrable le_top) n]
  simp [entry]

/-- `fourierCoeff (blockSymbolSingle r i j a) n` is `Matrix.single i j (fourierCoeff a n)`. -/
theorem fourierCoeff_blockSymbolSingle {r : ℕ} (i j : Fin r) (a : Lp ℂ ∞ (haarAddCircle (T := 1)))
    (n : ℤ) : fourierCoeff (blockSymbolSingle r i j a) n =
      Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (Matrix.single i j (fourierCoeff a n)) := by
  let ins : ℂ →L[ℂ] EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
    toSpanSingleton ℂ (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (Matrix.single i j 1))
  rw [blockSymbolSingle, fourierCoeff_congr_ae (ins.coeFn_compLpL a),
    ins.fourierCoeff_comp ((Lp.memLp a).integrable le_top) n]
  simp [ins, ← map_smul, Matrix.smul_single]

/-- Standard-basis matrix element form of `fourierCoeff_blockSymbolEntry`. -/
theorem inner_single_fourierCoeff_blockSymbol {r : ℕ} (A : BlockSymbol r) (i j : Fin r) (n : ℤ) :
    ⟪EuclideanSpace.single i (1 : ℂ), fourierCoeff A n (EuclideanSpace.single j (1 : ℂ))⟫_ℂ =
      fourierCoeff (blockSymbolEntry r i j A) n := by
  rw [fourierCoeff_blockSymbolEntry, EuclideanSpace.inner_single_left, map_one, one_mul]

end TauCeti
