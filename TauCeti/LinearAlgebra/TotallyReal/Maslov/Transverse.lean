/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Symmetric
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Euclidean
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Path
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Prod
public import TauCeti.Topology.Algebra.Matrix.Symmetric

/-!
# The Maslov index of paths with endpoints transverse to `ℝⁿ`

For a real `n × n` matrix `S`, the real subspace `{S y + i y | y ∈ ℝⁿ}` of `ℂⁿ`
(`Matrix.lagrangianChart`, in `TauCeti.LinearAlgebra.TotallyReal.Euclidean`) is the image of `ℝⁿ`
under the complex matrix `S + i`. It meets `ℝⁿ` only in `0`, it determines `S`, and for symmetric
`S` it is Lagrangian for the standard symplectic form `Im ⟪·, ·⟫` of `ℂⁿ`. For a scalar matrix it
is a rotation of `ℝⁿ` (`Matrix.lagrangianChart_smul_one`), whose Maslov phase is computed in
`Matrix.maslovPhase_realImage_smul_one` (in `TauCeti.LinearAlgebra.TotallyReal.Maslov.Euclidean`).
The symmetric matrices form a convex set, so these chart subspaces form a contractible cell; paths
of symmetric matrices are handled in `TauCeti.Topology.Algebra.Matrix.Symmetric`.

A continuous path `S t` of symmetric matrices gives a path of maximal totally real subspaces
(`TauCeti.TotallyRealPath.ofLagrangianChart`). Any two such paths with the same endpoints have
relative Maslov index zero (`TauCeti.TotallyRealPath.relativeMaslovIndex_ofLagrangianChart`): the
straight-line homotopy between them stays in the chart.

This makes the following definition independent of choices. Let `Λ` be a path of maximal totally
real subspaces of `ℂⁿ` from `S₀ + i` to `S₁ + i` (meaning the chart subspaces of the symmetric
matrices `S₀` and `S₁`). Its **Maslov index relative to `ℝⁿ`**
(`TauCeti.TotallyRealPath.transverseMaslovIndex`) is the relative Maslov index of `Λ` against the
chart path of the segment from `S₀` to `S₁`; every other chart path with these endpoints gives the
same value. It has the following properties, which are the axioms of the Robbin–Salamon Maslov
index for paths relative to the Lagrangian `ℝⁿ`, restricted to endpoints of this form, with the
convention that a positive crossing counts `+1`:

* **zero:** a path in the chart, which stays transverse to `ℝⁿ`, has index zero
  (`TauCeti.TotallyRealPath.transverseMaslovIndex_ofLagrangianChart`);
* **catenation:** the index is additive under catenation
  (`TauCeti.TotallyRealPath.transverseMaslovIndex_trans`), and reversal negates it
  (`TauCeti.TotallyRealPath.transverseMaslovIndex_symm`);
* **homotopy:** homotopies with fixed endpoints, given by two-parameter frames, preserve it
  (`TauCeti.TotallyRealPath.transverseMaslovIndex_eq_of_homotopy`);
* **normalization:** the rotation `t ↦ e^{iπ(2t - 1)/4} ℝⁿ`, which crosses `ℝⁿ` once in the
  positive direction, from the chart subspace of `-1` to that of `1`, has index `n`
  (`TauCeti.TotallyRealPath.transverseMaslovIndex_rotation`); for `n = 1` this is the
  normalization axiom;
* **naturality:** a real orthogonal change of coordinates `O`, which preserves `ℝⁿ` and moves the
  chart subspace of `S` to that of `O S Oᵀ`, does not change the index
  (`TauCeti.TotallyRealPath.transverseMaslovIndex_eq_of_orthogonal`);
* **direct sum:** the direct sum `Λ ⊕ Λ'` of paths in `ℂⁿ` and `ℂᵐ`
  (`TauCeti.TotallyRealPath.sum`), a path in `ℂ^{n ⊕ m}` between the chart subspaces of
  block-diagonal matrices, has index the sum of the two indices
  (`TauCeti.TotallyRealPath.transverseMaslovIndex_sum`), as is the relative index of two direct
  sums (`TauCeti.TotallyRealPath.relativeMaslovIndex_sum`).

For a loop based at a chart subspace it is the Maslov index of the loop
(`TauCeti.TotallyRealLoop.transverseMaslovIndex_toTotallyRealPath`).

The crossing-form formula for the index and its extension to endpoints that are not transverse
are not treated here.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the axioms of the Maslov index for paths, including naturality and the direct
  sum).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.3 (the Lagrangian Grassmannian, the open cell of Lagrangians transverse
  to a fixed one as symmetric matrices, and the Maslov index of paths).
-/

public section

open Module Real
open scoped ComplexConjugate unitInterval

noncomputable section

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

open Matrix

namespace TotallyRealPath

/-- The path `t ↦ {S t y + i y | y ∈ ℝⁿ}` of the chart subspaces of a path `S` of symmetric real
matrices. It is a path of Lagrangian subspaces transverse to `ℝⁿ`. -/
def ofLagrangianChart {S₀ S₁ : Matrix n n ℝ} (S : Path S₀ S₁) (hS : ∀ t, (S t).IsSymm) :
    TotallyRealPath (EuclideanSpace ℂ n) where
  toFun t := (S t).lagrangianChart
  exists_frame := ⟨realSubspace n, isMaximalTotallyReal_realSubspace,
    fun t ↦ lagrangianChartCLE (hS t), continuous_lagrangianChartCLE S.continuous hS,
    fun t ↦ (map_lagrangianChartCLE (hS t)).symm⟩

@[simp]
theorem ofLagrangianChart_apply {S₀ S₁ : Matrix n n ℝ} (S : Path S₀ S₁)
    (hS : ∀ t, (S t).IsSymm) (t : I) : ofLagrangianChart S hS t = (S t).lagrangianChart :=
  (rfl)

/-- The chart path of a constant path of matrices is the constant path at its chart subspace. -/
@[simp]
theorem ofLagrangianChart_refl {S₀ : Matrix n n ℝ} (hS : ∀ t, (Path.refl S₀ t).IsSymm) :
    ofLagrangianChart (Path.refl S₀) hS =
      (TotallyRealLoop.const (E := EuclideanSpace ℂ n)
        (isMaximalTotallyReal_lagrangianChart (hS 0))).toTotallyRealPath :=
  ext fun t ↦ (ofLagrangianChart_apply _ _ t).trans (by simp)

/-- Reversing a chart path is the chart path of the reversed path of matrices. -/
@[simp]
theorem ofLagrangianChart_symm {S₀ S₁ : Matrix n n ℝ} (S : Path S₀ S₁)
    (hS : ∀ t, (S t).IsSymm) :
    (ofLagrangianChart S hS).symm =
      ofLagrangianChart S.symm (isSymm_path_symm hS) :=
  ext fun t ↦ by
    rw [symm_apply, ofLagrangianChart_apply, ofLagrangianChart_apply, Path.symm_apply,
      Function.comp_apply]

/-- Catenating chart paths gives the chart path of the catenated path of matrices. -/
@[simp]
theorem ofLagrangianChart_trans {S₀ S₁ S₂ : Matrix n n ℝ} (S : Path S₀ S₁) (T : Path S₁ S₂)
    (hS : ∀ t, (S t).IsSymm) (hT : ∀ t, (T t).IsSymm) :
    (ofLagrangianChart S hS).trans (ofLagrangianChart T hT) (by simp) =
      ofLagrangianChart (S.trans T) (isSymm_path_trans hS hT) := by
  ext1 t
  rw [trans_apply, ofLagrangianChart_apply, Path.trans_apply]
  split_ifs <;> rw [ofLagrangianChart_apply]

/-- **Paths in the chart have relative Maslov index zero.** Two chart paths of paths of symmetric
matrices with the same endpoints are joined by the straight-line homotopy of the matrices, which
stays in the chart; so their relative Maslov index vanishes. -/
theorem relativeMaslovIndex_ofLagrangianChart {S₀ S₁ : Matrix n n ℝ} (S T : Path S₀ S₁)
    (hS : ∀ t, (S t).IsSymm) (hT : ∀ t, (T t).IsSymm) :
    relativeMaslovIndex (ofLagrangianChart S hS) (ofLagrangianChart T hT) (by simp) (by simp) =
      0 := by
  -- The straight-line homotopy `H (s, t) = (1 - s) S t + s T t` of symmetric matrices.
  let H (p : I × I) : Matrix n n ℝ := AffineMap.lineMap (S p.2) (T p.2) (p.1 : ℝ)
  have hH (p : I × I) : (H p).IsSymm := by
    simp only [H, AffineMap.lineMap_apply_module]
    exact ((hS p.2).smul _).add ((hT p.2).smul _)
  have hHc : Continuous H := by
    simp only [H, AffineMap.lineMap_apply_module]
    fun_prop
  let A (p : I × I) := lagrangianChartCLE (hH p)
  let B (p : I × I) := lagrangianChartCLE (hT p.2)
  have h := relativeMaslovIndex_eq_of_homotopy (ofLagrangianChart S hS) (ofLagrangianChart T hT)
    (ofLagrangianChart T hT) (ofLagrangianChart T hT) isMaximalTotallyReal_realSubspace A B
    (continuous_lagrangianChartCLE hHc hH)
    (continuous_lagrangianChartCLE (T.continuous.comp continuous_snd) fun p ↦ hT p.2)
    (fun t ↦ by simp [A, H])
    (fun t ↦ by simp [B])
    (fun t ↦ by simp [A, H])
    (fun t ↦ by simp [B])
    (fun s ↦ by simp [A, B, H])
    (fun s ↦ by simp [A, B, H])
  exact h.trans (relativeMaslovIndex_self _)

/-- The **Maslov index relative to `ℝⁿ`** of a path `Λ` of maximal totally real subspaces of `ℂⁿ`
from the chart subspace `{S₀ y + i y}` of a symmetric matrix `S₀` to the chart subspace of a
symmetric matrix `S₁`; these endpoints are Lagrangian and transverse to `ℝⁿ`. It is the relative
Maslov index of `Λ` against the chart path of the segment from `S₀` to `S₁`, and any other path of
symmetric matrices from `S₀` to `S₁` gives the same value
(`TauCeti.TotallyRealPath.transverseMaslovIndex_eq_relativeMaslovIndex`). It satisfies the axioms
of the Robbin–Salamon index relative to `ℝⁿ` for such endpoints: zero, catenation, homotopy and
normalization. -/
def transverseMaslovIndex (Λ : TotallyRealPath (EuclideanSpace ℂ n)) {S₀ S₁ : Matrix n n ℝ}
    (hS₀ : S₀.IsSymm) (hS₁ : S₁.IsSymm) (h₀ : Λ 0 = S₀.lagrangianChart)
    (h₁ : Λ 1 = S₁.lagrangianChart) : ℤ :=
  relativeMaslovIndex Λ (ofLagrangianChart (Path.segment S₀ S₁) (isSymm_segment hS₀ hS₁))
    (by simpa using h₀) (by simpa using h₁)

/-- The Maslov index relative to `ℝⁿ` may be computed against the chart path of any path of
symmetric matrices with the same endpoints. -/
theorem transverseMaslovIndex_eq_relativeMaslovIndex (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    {S₀ S₁ : Matrix n n ℝ} (S : Path S₀ S₁) (hS : ∀ t, (S t).IsSymm)
    (h₀ : Λ 0 = S₀.lagrangianChart) (h₁ : Λ 1 = S₁.lagrangianChart) :
    Λ.transverseMaslovIndex (by simpa using hS 0) (by simpa using hS 1) h₀ h₁ =
      relativeMaslovIndex Λ (ofLagrangianChart S hS) (by simpa using h₀) (by simpa using h₁) := by
  rw [transverseMaslovIndex, ← relativeMaslovIndex_add Λ (ofLagrangianChart S hS) _
    (by simpa using h₀) (by simpa using h₁) (by simp) (by simp),
    relativeMaslovIndex_ofLagrangianChart, add_zero]

/-- **Zero axiom.** A path of chart subspaces of symmetric matrices, which stays transverse to
`ℝⁿ`, has Maslov index zero relative to `ℝⁿ`. -/
@[simp]
theorem transverseMaslovIndex_ofLagrangianChart {S₀ S₁ : Matrix n n ℝ} (S : Path S₀ S₁)
    (hS : ∀ t, (S t).IsSymm) :
    (ofLagrangianChart S hS).transverseMaslovIndex (S₀ := S₀) (S₁ := S₁) (by simpa using hS 0)
      (by simpa using hS 1) (by simp) (by simp) = 0 := by
  rw [transverseMaslovIndex_eq_relativeMaslovIndex _ S hS, relativeMaslovIndex_self]

/-- **Catenation axiom.** The Maslov index relative to `ℝⁿ` is additive under catenation of paths
whose common point is a chart subspace. -/
theorem transverseMaslovIndex_trans (Λ₁ Λ₂ : TotallyRealPath (EuclideanSpace ℂ n))
    (h : Λ₁ 1 = Λ₂ 0) {S₀ S₁ S₂ : Matrix n n ℝ} (hS₀ : S₀.IsSymm) (hS₁ : S₁.IsSymm)
    (hS₂ : S₂.IsSymm) (h₀ : Λ₁ 0 = S₀.lagrangianChart) (h₁ : Λ₁ 1 = S₁.lagrangianChart)
    (h₂ : Λ₂ 1 = S₂.lagrangianChart) :
    (Λ₁.trans Λ₂ h).transverseMaslovIndex hS₀ hS₂ (by simpa using h₀) (by simpa using h₂) =
      Λ₁.transverseMaslovIndex hS₀ hS₁ h₀ h₁ +
        Λ₂.transverseMaslovIndex hS₁ hS₂ (h.symm.trans h₁) h₂ := by
  have hseg := ofLagrangianChart_trans (Path.segment S₀ S₁) (Path.segment S₁ S₂)
    (isSymm_segment hS₀ hS₁) (isSymm_segment hS₁ hS₂)
  rw [transverseMaslovIndex_eq_relativeMaslovIndex _ _
    (isSymm_path_trans (isSymm_segment hS₀ hS₁) (isSymm_segment hS₁ hS₂))]
  exact (relativeMaslovIndex_congr_right hseg.symm _ _).trans
    (relativeMaslovIndex_trans Λ₁ Λ₂ _ _ h (by simp) (by simpa using h₀) (by simpa using h₁)
      (by simpa using h₂))

/-- **Reversal.** Reversing a path negates its Maslov index relative to `ℝⁿ`. -/
theorem transverseMaslovIndex_symm (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    {S₀ S₁ : Matrix n n ℝ} (hS₀ : S₀.IsSymm) (hS₁ : S₁.IsSymm) (h₀ : Λ 0 = S₀.lagrangianChart)
    (h₁ : Λ 1 = S₁.lagrangianChart) :
    Λ.symm.transverseMaslovIndex hS₁ hS₀ (by simpa using h₁) (by simpa using h₀) =
      -Λ.transverseMaslovIndex hS₀ hS₁ h₀ h₁ := by
  rw [transverseMaslovIndex_eq_relativeMaslovIndex _ (Path.segment S₀ S₁).symm
    (isSymm_path_symm (isSymm_segment hS₀ hS₁))]
  exact (relativeMaslovIndex_congr_right (ofLagrangianChart_symm _ _).symm _ _).trans
    (relativeMaslovIndex_symm _ _ _ _)

/-- **Homotopy axiom.** Two paths joined by a homotopy of paths whose endpoints stay at fixed chart
subspaces have the same Maslov index relative to `ℝⁿ`. The homotopy is given by a continuous
two-parameter family of complex-linear automorphisms moving `ℝⁿ`. -/
theorem transverseMaslovIndex_eq_of_homotopy (Λ₀ Λ₁ : TotallyRealPath (EuclideanSpace ℂ n))
    {S₀ S₁ : Matrix n n ℝ} (hS₀ : S₀.IsSymm) (hS₁ : S₁.IsSymm)
    (A : I × I → EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n)
    (hA : Continuous fun p ↦ (A p : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))
    (hΛ₀ : ∀ t, Λ₀ t = (realSubspace n).map (((A (0, t)).toLinearEquiv :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ))
    (hΛ₁ : ∀ t, Λ₁ t = (realSubspace n).map (((A (1, t)).toLinearEquiv :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ))
    (hA₀ : ∀ s, (realSubspace n).map (((A (s, 0)).toLinearEquiv :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) = S₀.lagrangianChart)
    (hA₁ : ∀ s, (realSubspace n).map (((A (s, 1)).toLinearEquiv :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) = S₁.lagrangianChart) :
    Λ₀.transverseMaslovIndex hS₀ hS₁ (by rw [hΛ₀, hA₀]) (by rw [hΛ₀, hA₁]) =
      Λ₁.transverseMaslovIndex hS₀ hS₁ (by rw [hΛ₁, hA₀]) (by rw [hΛ₁, hA₁]) := by
  -- Compare both paths with the chart path of the segment, held fixed during the homotopy.
  let B (p : I × I) := lagrangianChartCLE (isSymm_segment hS₀ hS₁ p.2)
  let Γ := ofLagrangianChart (Path.segment S₀ S₁) (isSymm_segment hS₀ hS₁)
  rw [transverseMaslovIndex, transverseMaslovIndex]
  exact relativeMaslovIndex_eq_of_homotopy Λ₀ Γ Λ₁ Γ isMaximalTotallyReal_realSubspace A B hA
    (continuous_lagrangianChartCLE ((Path.segment S₀ S₁).continuous.comp continuous_snd)
      fun p ↦ isSymm_segment hS₀ hS₁ p.2)
    hΛ₀ (fun t ↦ by simp [B, Γ]) hΛ₁
    (fun t ↦ by simp [B, Γ])
    (fun s ↦ by simp [B, hA₀])
    (fun s ↦ by simp [B, hA₁])

/-! ### Normalization -/

/-- **Normalization.** The rotation `t ↦ e^{iπ(2t - 1)/4} ℝⁿ` from the chart subspace of `-1` to
that of `1` crosses `ℝⁿ` once, at `t = 1/2`, in the positive direction; its Maslov index relative to
`ℝⁿ` is `n`. For `n = 1` this is the normalization axiom of Robbin and Salamon. -/
theorem transverseMaslovIndex_rotation (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    (hΛ : ∀ t : I, Λ t =
      (Complex.exp ((π * (2 * t - 1) / 4 : ℝ) * Complex.I) • (1 : Matrix n n ℂ)).realImage) :
    Λ.transverseMaslovIndex isSymm_one.neg isSymm_one
      (by rw [hΛ, lagrangianChart_neg_one]; norm_num [neg_div])
      (by rw [hΛ, lagrangianChart_one]; norm_num) = Fintype.card n := by
  set k := Fintype.card n
  set c := 2 * k * (π * (2 * (0 : ℝ) - 1) / 4)
  have hL₀ := Λ.isMaximalTotallyReal 0
  -- Relative to `Λ 0 = e^{-iπ/4} ℝⁿ`, the phase of `e^{iθ} ℝⁿ` is `e^{i (2kθ - c)}`.
  have key {X : Submodule ℝ (EuclideanSpace ℂ n)}
      (hX : IsMaximalTotallyReal
        ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ) X) (θ : ℝ)
      (hXθ : X = (Complex.exp (θ * Complex.I) • (1 : Matrix n n ℂ)).realImage) :
      hL₀.maslovPhase hX = Complex.exp ((2 * k * θ - c : ℝ) * Complex.I) := by
    have hmax (φ : ℝ) := isMaximalTotallyReal_realImage_smul_one (n := n)
      (Complex.exp_ne_zero (φ * Complex.I))
    rw [← isMaximalTotallyReal_realSubspace.maslovPhase_div_maslovPhase hL₀ hX,
      isMaximalTotallyReal_realSubspace.maslovPhase_congr hX (hmax θ) hXθ,
      isMaximalTotallyReal_realSubspace.maslovPhase_congr hL₀ (hmax _) (hΛ 0),
      maslovPhase_realImage_exp_smul_one, maslovPhase_realImage_exp_smul_one, ← Complex.exp_sub]
    congr 1
    simp only [c, k]
    push_cast
    ring
  -- The segment from `-1` to `1` consists of the scalar matrices `(2t - 1) • 1`.
  have hseg (t : I) :
      Path.segment (-1 : Matrix n n ℝ) 1 t = ((2 * t - 1 : ℝ)) • (1 : Matrix n n ℝ) := by
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    module
  refine relativeMaslovIndex_eq_of_angle_lifts _ _ _ _
    (θΛ := fun t ↦ 2 * k * (π * (2 * t - 1) / 4) - c)
    (θΓ := fun t ↦ 2 * k * (π / 2 - arctan (2 * t - 1)) - c) (by fun_prop) (by fun_prop)
    (fun t ↦ Circle.ext ?_) (fun t ↦ Circle.ext ?_) ?_
  · rw [Circle.coe_exp, maslovPhasePath_apply, key _ _ (hΛ t)]
  · rw [Circle.coe_exp, maslovPhasePath_apply, key _ _ (by
      rw [ofLagrangianChart_apply, hseg, lagrangianChart_smul_one])]
  · simp only [Set.Icc.coe_one, Set.Icc.coe_zero]
    norm_num [arctan_one, arctan_neg]
    ring

/-! ### Naturality and direct sums -/

/-- **Naturality.** A real orthogonal change of coordinates `O` of `ℂⁿ` preserves `ℝⁿ` and carries
the chart subspace of `S` to that of `O S Oᵀ`
(`Matrix.lagrangianChart_mul_mul_transpose`). If `Γ` is the image of `Λ` under `O`, then the
Maslov index of `Γ` relative to `ℝⁿ`, between the conjugated endpoints, is that of `Λ`. -/
theorem transverseMaslovIndex_eq_of_orthogonal (Λ Γ : TotallyRealPath (EuclideanSpace ℂ n))
    {O : Matrix n n ℝ} (hO : O ∈ orthogonalGroup n ℝ)
    (hΓ : ∀ t, Γ t = (Λ t).map (((toEuclideanCLM (𝕜 := ℂ) (O.map ((↑) : ℝ → ℂ)) :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ))
    {S₀ S₁ : Matrix n n ℝ} (hS₀ : S₀.IsSymm) (hS₁ : S₁.IsSymm) (h₀ : Λ 0 = S₀.lagrangianChart)
    (h₁ : Λ 1 = S₁.lagrangianChart) :
    Γ.transverseMaslovIndex (hS₀.mul_mul_transpose O) (hS₁.mul_mul_transpose O)
      (by rw [hΓ, h₀, lagrangianChart_mul_mul_transpose hO])
      (by rw [hΓ, h₁, lagrangianChart_mul_mul_transpose hO]) =
      Λ.transverseMaslovIndex hS₀ hS₁ h₀ h₁ := by
  -- The complex matrix of `O` as an automorphism of `ℂⁿ`.
  have hdet : (O.map ((↑) : ℝ → ℂ)).det ≠ 0 := by
    rw [det_map_ofReal, Complex.ofReal_ne_zero]
    exact (isUnit_det_of_left_inverse ((mem_orthogonalGroup_iff' n ℝ).1 hO)).ne_zero
  set D := (O.map ((↑) : ℝ → ℂ)).toEuclideanCLE hdet
  have hD (L : Submodule ℝ (EuclideanSpace ℂ n)) :
      L.map ((D.toLinearEquiv : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) =
        L.map (((toEuclideanCLM (𝕜 := ℂ) (O.map ((↑) : ℝ → ℂ)) :
          EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
            EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) := by
    congr 1
    ext x
    simp [D]
  have hΓD : Γ = Λ.mapEquiv D := ext fun t ↦ by rw [hΓ, mapEquiv_apply, hD]
  -- The image under `O` of the chart path of the segment from `S₀` to `S₁` is the chart path of
  -- the segment from `O S₀ Oᵀ` to `O S₁ Oᵀ`.
  have hseg : ofLagrangianChart (Path.segment (O * S₀ * Oᵀ) (O * S₁ * Oᵀ))
      (isSymm_segment (hS₀.mul_mul_transpose O) (hS₁.mul_mul_transpose O)) =
      (ofLagrangianChart (Path.segment S₀ S₁) (isSymm_segment hS₀ hS₁)).mapEquiv D := by
    ext1 t
    rw [mapEquiv_apply, ofLagrangianChart_apply, ofLagrangianChart_apply, hD,
      ← lagrangianChart_mul_mul_transpose hO]
    congr 1
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  subst hΓD
  rw [transverseMaslovIndex, transverseMaslovIndex]
  exact (relativeMaslovIndex_congr_right hseg _ _).trans (relativeMaslovIndex_mapEquiv _ _ _ _ _)

section Sum

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
/-- The **direct sum** `Λ ⊕ Λ'` of paths of maximal totally real subspaces of `ℂⁿ` and `ℂᵐ`, as a
path in `ℂ^{n ⊕ m}`: the product path, transported along `ℂⁿ × ℂᵐ ≃ ℂ^{n ⊕ m}`. -/
noncomputable def sum (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    (Λ' : TotallyRealPath (EuclideanSpace ℂ m)) :
    TotallyRealPath (EuclideanSpace ℂ (n ⊕ m)) :=
  (Λ.prod Λ').mapEquiv (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := n) (κ := m)).symm

omit [DecidableEq n] [DecidableEq m] in
@[simp]
theorem sum_apply (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    (Λ' : TotallyRealPath (EuclideanSpace ℂ m)) (t : I) :
    Λ.sum Λ' t = ((Λ t).prod (Λ' t)).map
      (((EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := n) (κ := m)).symm.toLinearEquiv :
        (EuclideanSpace ℂ n × EuclideanSpace ℂ m) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ m)).restrictScalars
          ℝ) := by
  rw [sum, mapEquiv_apply, prod_apply]

omit [DecidableEq n] [DecidableEq m] in
/-- The relative Maslov index is additive under the direct sum of paths in `ℂⁿ` and `ℂᵐ`:
`μ(Λ ⊕ Λ', Γ ⊕ Γ') = μ(Λ, Γ) + μ(Λ', Γ')`. -/
@[simp]
theorem relativeMaslovIndex_sum (Λ Γ : TotallyRealPath (EuclideanSpace ℂ n))
    (Λ' Γ' : TotallyRealPath (EuclideanSpace ℂ m)) (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1)
    (h₀' : Λ' 0 = Γ' 0) (h₁' : Λ' 1 = Γ' 1) :
    relativeMaslovIndex (Λ.sum Λ') (Γ.sum Γ') (by simp [h₀, h₀']) (by simp [h₁, h₁']) =
      relativeMaslovIndex Λ Γ h₀ h₁ + relativeMaslovIndex Λ' Γ' h₀' h₁' :=
  (relativeMaslovIndex_mapEquiv _ _ _ _ _).trans (relativeMaslovIndex_prod _ _ _ _ _ _ _ _)

/-- **Direct-sum axiom.** The Maslov index relative to `ℝ^{n ⊕ m}` of the direct sum of paths
between chart subspaces is the sum of their Maslov indices relative to `ℝⁿ` and `ℝᵐ`; the endpoints
of the direct sum are the chart subspaces of the block-diagonal matrices
(`Matrix.lagrangianChart_fromBlocks_zero`). -/
theorem transverseMaslovIndex_sum (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    (Λ' : TotallyRealPath (EuclideanSpace ℂ m)) {S₀ S₁ : Matrix n n ℝ} {T₀ T₁ : Matrix m m ℝ}
    (hS₀ : S₀.IsSymm) (hS₁ : S₁.IsSymm) (hT₀ : T₀.IsSymm) (hT₁ : T₁.IsSymm)
    (h₀ : Λ 0 = S₀.lagrangianChart) (h₁ : Λ 1 = S₁.lagrangianChart)
    (h₀' : Λ' 0 = T₀.lagrangianChart) (h₁' : Λ' 1 = T₁.lagrangianChart) :
    (Λ.sum Λ').transverseMaslovIndex (S₀ := fromBlocks S₀ 0 0 T₀) (S₁ := fromBlocks S₁ 0 0 T₁)
      (hS₀.fromBlocks (by simp) hT₀) (hS₁.fromBlocks (by simp) hT₁)
      (by rw [sum_apply, h₀, h₀', lagrangianChart_fromBlocks_zero])
      (by rw [sum_apply, h₁, h₁', lagrangianChart_fromBlocks_zero]) =
      Λ.transverseMaslovIndex hS₀ hS₁ h₀ h₁ + Λ'.transverseMaslovIndex hT₀ hT₁ h₀' h₁' := by
  -- The chart path of the segment of block-diagonal matrices is the direct sum of the chart paths
  -- of the segments of the blocks.
  have hseg : ofLagrangianChart (Path.segment (fromBlocks S₀ 0 0 T₀) (fromBlocks S₁ 0 0 T₁))
      (isSymm_segment (hS₀.fromBlocks (by simp) hT₀) (hS₁.fromBlocks (by simp) hT₁)) =
      (ofLagrangianChart (Path.segment S₀ S₁) (isSymm_segment hS₀ hS₁)).sum
        (ofLagrangianChart (Path.segment T₀ T₁) (isSymm_segment hT₀ hT₁)) := by
    ext1 t
    rw [sum_apply, ofLagrangianChart_apply, ofLagrangianChart_apply, ofLagrangianChart_apply,
      ← lagrangianChart_fromBlocks_zero]
    congr 1
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, fromBlocks_smul,
      fromBlocks_add, smul_zero, add_zero]
  rw [transverseMaslovIndex, transverseMaslovIndex, transverseMaslovIndex]
  exact (relativeMaslovIndex_congr_right hseg _ _).trans (relativeMaslovIndex_sum _ _ _ _ _ _ _ _)

end Sum

end TotallyRealPath

namespace TotallyRealLoop

/-- **Loops.** For a loop based at the chart subspace of a symmetric matrix, the Maslov index
relative to `ℝⁿ` is the Maslov index of the loop. -/
theorem transverseMaslovIndex_toTotallyRealPath (Λ : TotallyRealLoop (EuclideanSpace ℂ n))
    {S₀ : Matrix n n ℝ} (hS₀ : S₀.IsSymm) (h₀ : Λ 0 = S₀.lagrangianChart) :
    Λ.toTotallyRealPath.transverseMaslovIndex hS₀ hS₀ (by simpa using h₀)
      (by rw [toTotallyRealPath_apply, ← Λ.toFun_zero_eq_toFun_one]; exact h₀) =
      Λ.maslovIndex := by
  rw [TotallyRealPath.transverseMaslovIndex_eq_relativeMaslovIndex _ (Path.refl S₀) fun _ ↦ hS₀]
  refine (TotallyRealPath.relativeMaslovIndex_congr_right
    (TotallyRealPath.ofLagrangianChart_refl _) _ _).trans ?_
  rw [relativeMaslovIndex_toTotallyRealPath Λ _ (by simpa using h₀), maslovIndex_const, sub_zero]

end TotallyRealLoop

end TauCeti
