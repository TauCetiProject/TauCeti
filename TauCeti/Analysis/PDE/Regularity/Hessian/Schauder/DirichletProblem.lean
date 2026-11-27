/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.C2HolderBoundary.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Operator
import TauCeti.Analysis.Convex.Segment
import TauCeti.Analysis.Holder.C2HolderBoundary.Extension
import TauCeti.Analysis.Holder.Coefficient
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.BoundedDomain
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Dirichlet problem in `C^{2,α}(Ω)` by the method of continuity

Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary Ω α`), and let

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u`

have coefficients in the bounded `α`-Hölder functions on `Ω`, with `a` uniformly elliptic,
`λ ‖ξ‖² ≤ ξᵀ a ξ` with `0 < λ`, and `c ≤ 0`. This file studies the Dirichlet problem

`L u = f` in `Ω`,  `u = φ` on `∂Ω`

in the Hölder space `C^{2,α}(Ω)` (`TauCeti.CkHolderSpaceOn 2 α Ω ℝ`), with `L` the operator
`TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL` and the zero boundary condition expressed by the
submodule `TauCeti.CkHolderSpaceOn.vanishingOnFrontierSubmodule`.

* **The a priori estimate.** There is `C`, depending only on `Ω`, `α`, `λ` and a bound `K` on the
  norms of the coefficients, with `‖u‖_{C^{2,α}(Ω)} ≤ C ‖L u‖_{C^{0,α}(Ω)}` for every `u`
  vanishing on `∂Ω`
  (`TauCeti.CkHolderSpaceOn.exists_norm_le_mul_norm_nonDivergenceOperatorL`). This is
  Gilbarg–Trudinger's Theorem 6.6 for zero boundary values, in the norms of the Banach spaces
  on which `L` acts.
* **The method of continuity.** For two such operators, the Dirichlet problem with zero boundary
  values is solvable for every `f` for one of them exactly when it is for the other
  (`TauCeti.CkHolderSpaceOn.surjOn_nonDivergenceOperatorL_iff`). In particular it is solvable
  for `L` exactly when it is solvable for the Laplacian
  (`TauCeti.CkHolderSpaceOn.surjOn_nonDivergenceOperatorL_iff_surjOn_laplacianL`); this is
  Gilbarg–Trudinger's Theorem 6.8. When it is, the solution is unique, also for arbitrary boundary
  values `φ ∈ C^{2,α}(Ω)`
  (`existsUnique_sub_mem_vanishingOnFrontierSubmodule_and_nonDivergenceOperatorL_eq`).

Together with Kellogg's theorem, that Poisson's equation `Δu = f`, `u = 0` on `∂Ω`, has a solution
in `C^{2,α}(Ω)` for every `f ∈ C^{0,α}(Ω)` (Gilbarg–Trudinger, Lemma 6.18 and Theorem 6.14), this
gives the unique solvability of the Dirichlet problem for every such `L`.

## The argument

* **The a priori estimate.** An element `u` of `C^{2,α}(Ω)` is the restriction of a function `g`
  that is `C²` on the whole space (`TauCeti.CkHolderSpaceOn.exists_contDiff_eq`, which uses the
  `C^{2,α}` boundary). Since `u` vanishes on `∂Ω`, so does `g`, and `D²g` is `α`-Hölder on
  `closure Ω` by continuity. The coefficients extend to `closure Ω` with the same Hölder constants
  and bounds (`TauCeti.HolderSpace.exists_holderOnWith_closure_and_norm_le`), and ellipticity
  passes to the closure by continuity. The global Schauder estimate for a nonpositive potential
  (`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos`, in
  the `TauCeti.PDE` namespace) then bounds `|g|`, `‖Dg‖`, `‖D²g‖` and the Hölder constant of `D²g`
  on `closure Ω` by a multiple of the `C^{0,α}(Ω)` norm of `L u`, and these four quantities bound
  the norm of `u` (`TauCeti.CkHolderSpaceOn.norm_le_sum_add_of_apply_eq`).
* **The method of continuity.** Along the segment `t ↦ (1 - t) L₀ + t L₁`, `t ∈ [0, 1]`, the
  operator is that of the segment of coefficients
  (`TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_lineMap`), and these coefficients stay
  uniformly elliptic with the same `λ`, keep `c ≤ 0`, and have norms bounded independently of `t`.
  So the a priori estimate is uniform along the segment, and the method of continuity
  (`ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`) on the Banach space of
  elements of `C^{2,α}(Ω)` vanishing on `∂Ω` transports surjectivity from one end to the other.
  The Laplacian is the operator with `a = I` and `b = c = 0`
  (`TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_eq_laplacianL`).
* **Boundary values.** Uniqueness is the maximum principle
  (`TauCeti.CkHolderSpaceOn.injOn_nonDivergenceOperatorL`); for boundary values `φ` the solution
  is `φ + w` with `w` the solution with zero boundary values and datum `f - L φ`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity), Theorem 6.6 (the global Schauder estimate) and
  Theorem 6.8 (its use for the Dirichlet problem).
-/

public section

noncomputable section

namespace TauCeti.CkHolderSpaceOn

open Set TopologicalSpace
open scoped NNReal

variable {n : ℕ} {α : ℝ≥0} {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### Coefficients on the closure -/

/-- The principal coefficients on the closure: a matrix of bounded `α`-Hölder functions on `Ω`
with norms at most `K` and ellipticity constant `λ` on `Ω` agrees on `Ω` with a matrix field whose
entries are `α`-Hölder with constant `K` and bounded by `K` on `closure Ω`, and which has
ellipticity constant `λ` on `closure Ω`. -/
private theorem exists_coeff_closure (hα₀ : 0 < α) {K : ℝ≥0}
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ} (hak : ∀ i j, ‖a i j‖ ≤ K) {lam : ℝ}
    (ha : ∀ (x : Ω) (ξ : E), lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ) :
    ∃ A : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, (∀ (x : Ω) i j, A x i j = a i j x) ∧
      (∀ i j, HolderOnWith K α (fun z ↦ A z i j) (closure (Ω : Set E))) ∧
      (∀ z ∈ closure (Ω : Set E), ∀ i j, |A z i j| ≤ K) ∧
      ∀ z ∈ closure (Ω : Set E), ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (A z).toQuadraticForm' ξ := by
  choose g hg hgH hgM using fun i j ↦
    (a i j).exists_holderOnWith_closure_and_norm_le (s := (Ω : Set E)) hα₀ (hak i j)
  refine ⟨fun z ↦ Matrix.of fun i j ↦ g i j z, fun x i j ↦ hg i j x, hgH,
    fun z hz i j ↦ (Real.norm_eq_abs _).symm.trans_le (hgM i j z hz), fun z hz ξ ↦ ?_⟩
  -- The quadratic form at `ξ` is continuous on `closure Ω`, and at least `λ ‖ξ‖²` on `Ω`.
  have hc : ContinuousOn (fun z ↦ (Matrix.of fun i j ↦ g i j z).toQuadraticForm' ξ)
      (closure (Ω : Set E)) := by
    have hgc (i j) : ContinuousOn (g i j) (closure (Ω : Set E)) := (hgH i j).continuousOn hα₀
    simp only [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Matrix.of_apply]
    fun_prop
  refine ContinuousWithinAt.closure_le hz continuousWithinAt_const ((hc z hz).mono subset_closure)
    fun y hy ↦ ?_
  have h := ha ⟨y, hy⟩ ξ
  simp only [← hg _ _ ⟨y, hy⟩] at h
  exact h

/-- The drift on the closure: bounded `α`-Hölder functions `bⁱ` on `Ω` with norms at most `K`
give a vector field `∑ᵢ bⁱ eᵢ` that is `α`-Hölder on `Ω` with constant `(n + 1) K` and bounded by
`(n + 1) K` there. -/
private theorem exists_drift (hα₀ : 0 < α) {K : ℝ≥0} {b : Fin (n + 1) → HolderSpace α Ω ℝ}
    (hbk : ∀ i, ‖b i‖ ≤ K) :
    ∃ B : E → E, (∀ x : Ω, B x = ∑ i, b i x • EuclideanSpace.single i (1 : ℝ)) ∧
      HolderOnWith ((n + 1) * K) α B Ω ∧ ∀ z ∈ (Ω : Set E), ‖B z‖ ≤ (n + 1) * K := by
  choose g hg hgH _ using fun i ↦
    (b i).exists_holderOnWith_closure_and_norm_le (s := (Ω : Set E)) hα₀ (hbk i)
  refine ⟨fun z ↦ ∑ i, g i z • EuclideanSpace.single i (1 : ℝ), fun x ↦ by simp only [hg], ?_,
    fun z hz ↦ ?_⟩
  · have hiso (i : Fin (n + 1)) : Isometry fun r : ℝ ↦ r • EuclideanSpace.single i (1 : ℝ) :=
      Isometry.of_dist_eq fun x y ↦ by simp [dist_eq_norm, ← sub_smul, norm_smul]
    simpa using HolderOnWith.fintype_sum fun i ↦
      (hiso i).comp_holderOnWith ((hgH i).mono subset_closure)
  · have h := HolderSpace.norm_sum_apply_smul_single_le_sum_norm b ⟨z, hz⟩
    simp only [← hg] at h
    refine h.trans ((Finset.sum_le_sum fun i _ ↦ hbk i).trans_eq ?_)
    simp

/-! ### Representatives up to the boundary -/

/-- An element of `C^{2,α}(Ω)` vanishing on `∂Ω`, for `Ω` bounded with `C^{2,α}` boundary, is the
restriction to `Ω` of a function `g` that is `C²` on the whole space, vanishes on `∂Ω`, and has
`D²g` `α`-Hölder on `closure Ω`. -/
private theorem exists_contDiff_eq_of_mem_vanishingOnFrontierSubmodule (hα₀ : 0 < α)
    (hb : Bornology.IsBounded (Ω : Set E)) (hbdry : (Ω : Set E).HasC2HolderBoundary α)
    {u : CkHolderSpaceOn 2 α Ω ℝ} (hu : u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ (∀ x : Ω, g x = u x) ∧ (∀ z ∈ frontier (Ω : Set E), g z = 0) ∧
      ∃ V : ℝ≥0, HolderOnWith V α (_root_.iteratedFDeriv ℝ 2 g) (closure (Ω : Set E)) := by
  obtain ⟨g, hg, hgu⟩ := u.exists_contDiff_eq hbdry hb hα₀
  refine ⟨g, hg, hgu, fun z hz ↦ ?_, _, (u.holderOnWith_iteratedFDeriv hgu).of_subset_closure
    subset_rfl fun z _ ↦
      ((hg.continuous_iteratedFDeriv (by norm_num)).continuousAt).continuousWithinAt⟩
  -- `g` is continuous and agrees with `u` on `Ω`, so it has the boundary values of `u`.
  have hext : EqOn g u.extend (closure (Ω : Set E)) :=
    EqOn.of_subset_closure (fun y hy ↦ (hgu ⟨y, hy⟩).trans (u.extend_apply ⟨y, hy⟩).symm)
      hg.continuous.continuousOn (continuousOn_extend_closure hu) subset_closure subset_rfl
  rw [hext (frontier_subset_closure hz), u.extend_apply_of_mem_frontier hz]

/-! ### The a priori estimate -/

/-- **The a priori estimate for the Dirichlet problem in `C^{2,α}(Ω)`.** Let `0 < α < 1`, let
`Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary, and let `0 < λ` and `K` be given.
There is a constant `C ≥ 0` such that for all coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded
`α`-Hölder functions on `Ω` with `λ ‖ξ‖² ≤ ξᵀ a ξ` and `c ≤ 0` on `Ω` and with norms at most `K`,
and for every `u ∈ C^{2,α}(Ω)` vanishing on `∂Ω`,

`‖u‖_{C^{2,α}(Ω)} ≤ C ‖L u‖_{C^{0,α}(Ω)}`,  `L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u`.

This is Gilbarg–Trudinger's Theorem 6.6 for zero boundary values, with `sup |u|` bounded by the
maximum principle. The sign condition `c ≤ 0` cannot be dropped: `u = sin x` on `(0, π)` vanishes
on the boundary and solves `u'' + u = 0`. -/
theorem exists_norm_le_mul_norm_nonDivergenceOperatorL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E))
    (hbdry : (Ω : Set E).HasC2HolderBoundary α) {lam : ℝ} (hlam : 0 < lam) (K : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ)
      (b : Fin (n + 1) → HolderSpace α Ω ℝ) (c : HolderSpace α Ω ℝ),
      (∀ (x : Ω) (ξ : E), lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ) →
      (∀ x : Ω, c x ≤ 0) → (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        ‖u‖ ≤ C * ‖nonDivergenceOperatorL hΩ hb hα₁.le a b c u‖ := by
  obtain ⟨C, hC⟩ :=
    PDE.exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos
      hα₀ hα₁ hb hbdry (∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), (K : ℝ)) K K ((n + 1) * K + K)
      hlam
  refine ⟨8 * C, by positivity, fun a b c ha hc0 hak hbk hck u hu ↦ ?_⟩
  obtain ⟨A, hA, hAH, hAM, hAell⟩ := exists_coeff_closure hα₀ hak ha
  obtain ⟨B, hB, hBH, hBM⟩ := exists_drift hα₀ hbk
  obtain ⟨c', hc', hcH, hcM⟩ :=
    c.exists_holderOnWith_closure_and_norm_le (s := (Ω : Set E)) hα₀ hck
  obtain ⟨g, hg, hgu, hg0, V, hV⟩ :=
    exists_contDiff_eq_of_mem_vanishingOnFrontierSubmodule hα₀ hb hbdry hu
  set f := nonDivergenceOperatorL hΩ hb hα₁.le a b c u
  have hK : (K : ℝ) ≤ (n + 1) * K + K := le_add_of_nonneg_left (by positivity)
  -- On `Ω`, the operator applied to `g` is `L u`.
  have hLu (x : Ω) : ∑ i, ∑ j, A x i j • fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ g x (B x) + c' x * g x = f x := by
    rw [nonDivergenceOperatorL_apply hΩ hb hα₁.le u hgu, hB, hc', map_sum]
    simp only [hA, smul_eq_mul, map_smul]
  -- The global Schauder estimate for `g` with the extended coefficients.
  obtain ⟨h0, hH, h1, h2⟩ := hC (a := A) (b := B) (c := c') (fun z hz ξ ↦ hAell z hz ξ)
    (fun z hz ξ ↦ Matrix.toQuadraticForm'_le_of_forall_abs_le (hAM z hz) ξ) hAH hAM
    (hBH.mono_const (by exact_mod_cast le_add_of_nonneg_right K.coe_nonneg))
    (fun z hz ↦ (hBM z hz).trans (le_add_of_nonneg_right K.coe_nonneg))
    ((hcH.mono subset_closure).mono_const (by exact_mod_cast hK))
    (fun z hz ↦ ((Real.norm_eq_abs _).symm.trans_le (hcM z (subset_closure hz))).trans hK)
    (fun z hz ↦ (hc' ⟨z, hz⟩).trans_le (hc0 ⟨z, hz⟩)) (U := univ) (u := g) (K := ‖f‖₊)
    (F := ‖f‖₊) isOpen_univ (subset_univ _) hg.contDiffOn hg0 hV
    ((f.holderOnWith_of_apply_eq fun x ↦ (hLu x).symm))
    (fun z hz ↦ (congrArg abs (hLu ⟨z, hz⟩)).trans_le
      ((HolderSpace.abs_apply_le_norm f _).trans_eq (coe_nnNorm f).symm))
  -- The four bounds on `closure Ω` bound the norm of `u`.
  have hf : (↑(C * (‖f‖₊ + ‖f‖₊)) : ℝ) = 2 * C * ‖f‖ := by push_cast; ring
  have hCf : (↑(C * ‖f‖₊) : ℝ) ≤ 2 * C * ‖f‖ := by
    push_cast
    nlinarith [C.coe_nonneg, norm_nonneg f]
  have hN (i : Fin 3) (z : E) (hz : z ∈ (Ω : Set E)) :
      ‖_root_.iteratedFDeriv ℝ i g z‖ ≤ 2 * C * ‖f‖ := by
    fin_cases i
    · simpa [_root_.norm_iteratedFDeriv_zero] using (h0 z (subset_closure hz)).trans hCf
    · simpa [_root_.norm_iteratedFDeriv_one] using (h1 z (subset_closure hz)).trans_eq hf
    · simpa using (h2 z (subset_closure hz)).trans_eq hf
  refine (norm_le_sum_add_of_apply_eq hgu (fun _ ↦ by positivity) hN
    (hH.mono subset_closure)).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hf]
  ring

/-! ### The method of continuity -/

/-- The segment between two operators restricted to the elements vanishing on `∂Ω` is the
operator of the segment of coefficients, restricted. -/
private theorem lineMap_comp_subtypeL (hΩ : (Ω : Set E).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1)
    (a₀ a₁ : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ)
    (b₀ b₁ : Fin (n + 1) → HolderSpace α Ω ℝ) (c₀ c₁ : HolderSpace α Ω ℝ) (t : ℝ) :
    AffineMap.lineMap ((nonDivergenceOperatorL hΩ hb hα a₀ b₀ c₀).comp
        (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL)
      ((nonDivergenceOperatorL hΩ hb hα a₁ b₁ c₁).comp
        (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL) t =
    (nonDivergenceOperatorL hΩ hb hα (AffineMap.lineMap a₀ a₁ t) (AffineMap.lineMap b₀ b₁ t)
      (AffineMap.lineMap c₀ c₁ t)).comp (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL := by
  rw [nonDivergenceOperatorL_lineMap]
  ext u
  simp [AffineMap.lineMap_apply_module]

/-- **The method of continuity for the Dirichlet problem in `C^{2,α}(Ω)`.** Let `0 < α < 1` and
let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary. For two operators
`L₀, L₁` of the form `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼ + ∑ᵢ bⁱ ∂ᵢ + c` with coefficients in the bounded `α`-Hölder
functions on `Ω`, both with ellipticity constant `λ > 0` and with `c ≤ 0`, the Dirichlet problem
`L₀ u = f` in `Ω`, `u = 0` on `∂Ω`, has a solution `u ∈ C^{2,α}(Ω)` for every `f ∈ C^{0,α}(Ω)`
if and only if the same holds for `L₁` (Gilbarg–Trudinger, Theorem 5.2 and the proof of
Theorem 6.8). -/
theorem surjOn_nonDivergenceOperatorL_iff (hα₀ : 0 < α) (hα₁ : α < 1)
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E))
    (hbdry : (Ω : Set E).HasC2HolderBoundary α) {lam : ℝ} (hlam : 0 < lam)
    {a₀ a₁ : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ}
    {b₀ b₁ : Fin (n + 1) → HolderSpace α Ω ℝ} {c₀ c₁ : HolderSpace α Ω ℝ}
    (ha₀ : ∀ (x : Ω) (ξ : E), lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a₀ i j x).toQuadraticForm' ξ)
    (ha₁ : ∀ (x : Ω) (ξ : E), lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a₁ i j x).toQuadraticForm' ξ)
    (hc₀ : ∀ x : Ω, c₀ x ≤ 0) (hc₁ : ∀ x : Ω, c₁ x ≤ 0) :
    SurjOn (nonDivergenceOperatorL hΩ hb hα₁.le a₀ b₀ c₀)
        (vanishingOnFrontierSubmodule 2 α Ω ℝ) univ ↔
      SurjOn (nonDivergenceOperatorL hΩ hb hα₁.le a₁ b₁ c₁)
        (vanishingOnFrontierSubmodule 2 α Ω ℝ) univ := by
  -- One bound `K` on the norms of all the coefficients.
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, ∀ f ∈ insert c₀ (insert c₁ (range b₀ ∪ range b₁ ∪
      range (Function.uncurry a₀) ∪ range (Function.uncurry a₁))), ‖f‖ ≤ K := by
    obtain ⟨K, hK⟩ := (((((finite_range b₀).union (finite_range b₁)).union
      (finite_range (Function.uncurry a₀))).union (finite_range (Function.uncurry a₁))).insert
      c₁).insert c₀ |>.isBounded.exists_norm_le
    exact ⟨K.toNNReal, fun f hf ↦ (hK f hf).trans (Real.le_coe_toNNReal K)⟩
  obtain ⟨C, -, hC⟩ := exists_norm_le_mul_norm_nonDivergenceOperatorL hα₀ hα₁ hΩ hb hbdry hlam K
  -- The method of continuity on the Banach space of elements vanishing on `∂Ω`.
  rw [surjOn_iff_surjective, surjOn_iff_surjective]
  refine ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap (C := C)
    (L₀ := (nonDivergenceOperatorL hΩ hb hα₁.le a₀ b₀ c₀).comp
      (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL)
    (L₁ := (nonDivergenceOperatorL hΩ hb hα₁.le a₁ b₁ c₁).comp
      (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL) fun t ht u ↦ ?_
  rw [lineMap_comp_subtypeL]
  -- The closed ball of radius `K` is convex, so it contains the segments of coefficients.
  refine hC _ _ _ (fun x ξ ↦ ?_) (fun x ↦ ?_)
    (fun i j ↦ norm_lineMap_le_of_norm_le (hK _ (by simp)) (hK _ (by simp)) ht)
    (fun i ↦ norm_lineMap_le_of_norm_le (hK _ (by simp)) (hK _ (by simp)) ht)
    (norm_lineMap_le_of_norm_le (hK _ (by simp)) (hK _ (by simp)) ht) u u.property
  · -- Ellipticity is preserved by convex combinations.
    have hmat : (Matrix.of fun i j ↦ AffineMap.lineMap (a₀ i j) (a₁ i j) t x) =
        (1 - t) • (Matrix.of fun i j ↦ a₀ i j x) + t • Matrix.of fun i j ↦ a₁ i j x := by
      ext i j
      simp [AffineMap.lineMap_apply_module, HolderSpace.add_apply, HolderSpace.smul_apply]
    simp only [hmat, Matrix.toQuadraticForm'_add, Matrix.toQuadraticForm'_smul,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    nlinarith [ha₀ x ξ, ha₁ x ξ, ht.1, ht.2]
  · -- So is the sign of the potential.
    simp only [AffineMap.lineMap_apply_module, HolderSpace.add_apply, HolderSpace.smul_apply,
      smul_eq_mul]
    nlinarith [hc₀ x, hc₁ x, ht.1, ht.2]

/-- **Gilbarg–Trudinger, Theorem 6.8.** Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be a bounded open set
with `C^{2,α}` boundary, and let `L = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼ + ∑ᵢ bⁱ ∂ᵢ + c` have coefficients in the
bounded `α`-Hölder functions on `Ω`, with `a` uniformly elliptic and `c ≤ 0`. Then the Dirichlet
problem `L u = f` in `Ω`, `u = 0` on `∂Ω`, has a solution `u ∈ C^{2,α}(Ω)` for every
`f ∈ C^{0,α}(Ω)` if and only if Poisson's equation `Δu = f`, `u = 0` on `∂Ω`, does. -/
theorem surjOn_nonDivergenceOperatorL_iff_surjOn_laplacianL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E))
    (hbdry : (Ω : Set E).HasC2HolderBoundary α) {lam : ℝ} (hlam : 0 < lam)
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ} (b : Fin (n + 1) → HolderSpace α Ω ℝ)
    {c : HolderSpace α Ω ℝ}
    (ha : ∀ (x : Ω) (ξ : E), lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x : Ω, c x ≤ 0) :
    SurjOn (nonDivergenceOperatorL hΩ hb hα₁.le a b c)
        (vanishingOnFrontierSubmodule 2 α Ω ℝ) univ ↔
      SurjOn (laplacianL α Ω ℝ) (vanishingOnFrontierSubmodule 2 α Ω ℝ) univ := by
  rw [← nonDivergenceOperatorL_eq_laplacianL hΩ hb hα₁.le]
  have hmin : 0 < min 1 lam := lt_min one_pos hlam
  refine surjOn_nonDivergenceOperatorL_iff hα₀ hα₁ hΩ hb hbdry hmin
    (fun x ξ ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (ha x ξ))
    (fun x ξ ↦ ?_) hc fun _ ↦ le_rfl
  have hone : (Matrix.of fun i j ↦
      (if i = j then (1 : HolderSpace α Ω ℝ) else 0) x) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    ext i j
    rw [Matrix.of_apply, Matrix.one_apply]
    split_ifs with h <;> simp [HolderSpace.one_apply, HolderSpace.zero_apply]
  rw [hone, PDE.toQuadraticForm'_one]
  exact mul_le_of_le_one_left (sq_nonneg _) (min_le_left _ _)

/-- **Existence and uniqueness with boundary values.** Under the hypotheses of
`TauCeti.CkHolderSpaceOn.surjOn_nonDivergenceOperatorL_iff_surjOn_laplacianL`, if Poisson's
equation `Δu = f`, `u = 0` on `∂Ω`, has a solution `u ∈ C^{2,α}(Ω)` for every `f ∈ C^{0,α}(Ω)`,
then for every boundary datum `φ ∈ C^{2,α}(Ω)` and every `f ∈ C^{0,α}(Ω)` there is exactly one
`u ∈ C^{2,α}(Ω)` with `L u = f` in `Ω` and `u - φ` vanishing on `∂Ω` (Gilbarg–Trudinger,
Theorem 6.8). -/
theorem existsUnique_sub_mem_vanishingOnFrontierSubmodule_and_nonDivergenceOperatorL_eq
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E))
    (hbdry : (Ω : Set E).HasC2HolderBoundary α) {lam : ℝ} (hlam : 0 < lam)
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ} (b : Fin (n + 1) → HolderSpace α Ω ℝ)
    {c : HolderSpace α Ω ℝ}
    (ha : ∀ (x : Ω) (ξ : E), lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x : Ω, c x ≤ 0)
    (hΔ : SurjOn (laplacianL α Ω ℝ) (vanishingOnFrontierSubmodule 2 α Ω ℝ) univ)
    (φ : CkHolderSpaceOn 2 α Ω ℝ) (f : HolderSpace α Ω ℝ) :
    ∃! u : CkHolderSpaceOn 2 α Ω ℝ, u - φ ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ ∧
      nonDivergenceOperatorL hΩ hb hα₁.le a b c u = f := by
  set L := nonDivergenceOperatorL hΩ hb hα₁.le a b c
  obtain ⟨w, hw, hLw⟩ := (surjOn_nonDivergenceOperatorL_iff_surjOn_laplacianL hα₀ hα₁ hΩ hb hbdry
    hlam b ha hc).2 hΔ (mem_univ (f - L φ))
  refine ⟨w + φ, ⟨by rwa [add_sub_cancel_right], by rw [map_add, hLw, sub_add_cancel]⟩,
    fun v ⟨hv, hLv⟩ ↦ ?_⟩
  have h := injOn_nonDivergenceOperatorL hΩ hb hα₁.le (b := b) hlam ha hc hv hw
    (by rw [map_sub, hLv, hLw])
  rw [← h, sub_add_cancel]

end TauCeti.CkHolderSpaceOn
