/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FormalMultilinearSeries

/-!
# Homogeneity and one-variable formal multilinear series

The `n`-th term of a formal multilinear series, evaluated on the diagonal, is homogeneous of
degree `n`: its value at `c • x` is `c ^ n` times its value at `x`
(`FormalMultilinearSeries.apply_smul`).

For a sequence `c : ℕ → E` in a topological `𝕜`-module, `TauCeti.mkPiRingSeries 𝕜 c` is the
one-variable formal multilinear series whose `n`-th term sends `v : Fin n → 𝕜` to
`(∏ i, v i) • c n`. Over a nontrivially normed field this is inverse to
`FormalMultilinearSeries.coeff` (`TauCeti.coeff_mkPiRingSeries`,
`FormalMultilinearSeries.eq_mkPiRingSeries_coeff`). Composing a one-variable series on the left
with a continuous linear map applies that map to each coefficient
(`ContinuousLinearMap.coeff_compFormalMultilinearSeries`).
-/

public section

section Homogeneity

variable {𝕜 E F : Type*} [CommSemiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]

/-- The `n`-th term of a formal multilinear series, evaluated on the diagonal, is homogeneous of
degree `n`. -/
theorem FormalMultilinearSeries.apply_smul (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (c : 𝕜)
    (x : E) : (p n fun _ ↦ c • x) = c ^ n • p n fun _ ↦ x := by
  simpa using (p n).map_smul_univ (fun _ ↦ c) fun _ ↦ x

end Homogeneity

section Coeff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Every coefficient of the zero one-variable formal multilinear series is zero. -/
@[simp]
theorem FormalMultilinearSeries.coeff_zero (n : ℕ) :
    (0 : FormalMultilinearSeries 𝕜 𝕜 E).coeff n = 0 := by
  rw [FormalMultilinearSeries.coeff]
  simp

/-- Composing a one-variable formal multilinear series on the left with a continuous linear map
applies that map to each coefficient. -/
@[simp]
theorem ContinuousLinearMap.coeff_compFormalMultilinearSeries
    (g : E →L[𝕜] F) (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :
    (g.compFormalMultilinearSeries p).coeff n = g (p.coeff n) := by
  rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff,
    ContinuousLinearMap.compFormalMultilinearSeries_apply']

end Coeff

namespace TauCeti

section TopologicalModule

variable {𝕜 E F : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

variable (𝕜) in
/-- The one-variable formal multilinear series with coefficient sequence `c : ℕ → E`, sending
`v : Fin n → 𝕜` in degree `n` to `(∏ i, v i) • c n`. -/
def mkPiRingSeries (c : ℕ → E) : FormalMultilinearSeries 𝕜 𝕜 E :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (c n)

/-- Degree-`n` unfolding of `TauCeti.mkPiRingSeries`. -/
theorem mkPiRingSeries_def (c : ℕ → E) (n : ℕ) :
    mkPiRingSeries 𝕜 c n = ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (c n) :=
  (rfl)

/-- Evaluating `mkPiRingSeries 𝕜 c` in degree `n` multiplies the coordinates and scales `c n`. -/
@[simp]
theorem mkPiRingSeries_apply_pi (c : ℕ → E) (n : ℕ) (v : Fin n → 𝕜) :
    mkPiRingSeries 𝕜 c n v = (∏ i, v i) • c n := by
  simp [mkPiRingSeries_def]

/-- Evaluating `mkPiRingSeries 𝕜 c` on the constant tuple `(z, …, z)` gives `z ^ n • c n`. -/
theorem mkPiRingSeries_apply (c : ℕ → E) (n : ℕ) (z : 𝕜) :
    mkPiRingSeries 𝕜 c n (fun _ ↦ z) = z ^ n • c n := by
  simp

/-- The series associated to the zero coefficient sequence is zero. -/
@[simp]
theorem mkPiRingSeries_zero : mkPiRingSeries 𝕜 (0 : ℕ → E) = 0 := by
  ext1 n
  exact ContinuousMultilinearMap.mkPiRing_zero

variable (𝕜) in
/-- Constructing a one-variable formal multilinear series from its coefficient sequence is
injective. -/
theorem mkPiRingSeries_injective : Function.Injective (mkPiRingSeries 𝕜 (E := E)) := by
  intro c d h
  ext n
  exact ContinuousMultilinearMap.mkPiRing_eq_iff.mp (congrFun h n)

/-- Two `mkPiRingSeries` agree if and only if their coefficient sequences agree. -/
@[simp]
theorem mkPiRingSeries_inj {c d : ℕ → E} :
    mkPiRingSeries 𝕜 c = mkPiRingSeries 𝕜 d ↔ c = d :=
  (mkPiRingSeries_injective 𝕜).eq_iff

/-- `mkPiRingSeries 𝕜 c` vanishes if and only if `c = 0`. -/
@[simp]
theorem mkPiRingSeries_eq_zero {c : ℕ → E} :
    mkPiRingSeries 𝕜 c = 0 ↔ c = 0 := by
  rw [← mkPiRingSeries_zero (𝕜 := 𝕜), mkPiRingSeries_inj]

/-- `mkPiRingSeries` commutes with pointwise addition of coefficient sequences. -/
theorem mkPiRingSeries_add (a b : ℕ → E) :
    mkPiRingSeries 𝕜 (a + b) = mkPiRingSeries 𝕜 a + mkPiRingSeries 𝕜 b := by
  ext1 n
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp [smul_add]

/-- `mkPiRingSeries` commutes with scalar multiplication by scalars commuting with `𝕜`. -/
theorem mkPiRingSeries_smul {R : Type*} [Semiring R] [Module R E] [ContinuousConstSMul R E]
    [SMulCommClass 𝕜 R E] (r : R) (c : ℕ → E) :
    mkPiRingSeries 𝕜 (r • c) = r • mkPiRingSeries 𝕜 c := by
  ext1 n
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp [smul_comm _ r]

/-- Composing `mkPiRingSeries 𝕜 c` on the left with a continuous linear map `g` composes `g` with
the coefficient sequence `c`. -/
@[simp]
theorem _root_.ContinuousLinearMap.compFormalMultilinearSeries_mkPiRingSeries
    (g : E →L[𝕜] F) (c : ℕ → E) :
    g.compFormalMultilinearSeries (mkPiRingSeries 𝕜 c) = mkPiRingSeries 𝕜 (g ∘ c) := by
  ext1 n
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp

end TopologicalModule

section TopologicalAddGroup

variable {𝕜 E : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- `mkPiRingSeries` commutes with negation of coefficient sequences. -/
theorem mkPiRingSeries_neg (c : ℕ → E) :
    mkPiRingSeries 𝕜 (-c) = -mkPiRingSeries 𝕜 c := by
  ext1 n
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp

/-- `mkPiRingSeries` commutes with subtraction of coefficient sequences. -/
theorem mkPiRingSeries_sub (a b : ℕ → E) :
    mkPiRingSeries 𝕜 (a - b) = mkPiRingSeries 𝕜 a - mkPiRingSeries 𝕜 b := by
  ext1 n
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp [smul_sub]

end TopologicalAddGroup

section Normed

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The `n`-th coefficient of `mkPiRingSeries 𝕜 c` is `c n`. -/
@[simp]
theorem coeff_mkPiRingSeries (c : ℕ → E) (n : ℕ) :
    (mkPiRingSeries 𝕜 c).coeff n = c n := by
  rw [FormalMultilinearSeries.coeff, mkPiRingSeries_apply_pi]
  simp

/-- The operator norm of the `n`-th term of `mkPiRingSeries 𝕜 c` is `‖c n‖`. -/
theorem norm_mkPiRingSeries (c : ℕ → E) (n : ℕ) :
    ‖mkPiRingSeries 𝕜 c n‖ = ‖c n‖ :=
  ContinuousMultilinearMap.norm_mkPiRing (c n)

/-- Every one-variable formal multilinear series over a nontrivially normed field is recovered
from its coefficient sequence via `TauCeti.mkPiRingSeries`. -/
theorem _root_.FormalMultilinearSeries.eq_mkPiRingSeries_coeff
    (p : FormalMultilinearSeries 𝕜 𝕜 E) :
    p = mkPiRingSeries 𝕜 p.coeff := by
  ext1 n
  exact (p.mkPiRing_coeff_eq n).symm

end Normed

end TauCeti

end
