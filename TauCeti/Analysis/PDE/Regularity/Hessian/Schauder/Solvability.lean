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
import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.BoundedDomain
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Dirichlet problem in `C^{2,α}(Ω)` by the method of continuity

Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary`). For coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded `α`-Hölder functions
on `Ω`, with `a` uniformly elliptic and `c ≤ 0`, consider the operator

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u`

from `C^{2,α}(Ω)` to `C^{0,α}(Ω)` (`TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL`), and the closed
subspace `X ⊆ C^{2,α}(Ω)` of the elements vanishing on `∂Ω`
(`TauCeti.CkHolderSpaceOn.vanishingOnFrontierSubmodule`). This file proves Gilbarg–Trudinger's
Theorem 6.8 for this setting.

* **The a priori estimate on `X`.** There is a constant `C`, depending only on `Ω`, `α`, the
  ellipticity constant `λ` and a bound `K` on the norms of the coefficients, such that
  `‖u‖_{C^{2,α}(Ω)} ≤ C ‖L u‖_{C^{0,α}(Ω)}` for every `u ∈ X`
  (`TauCeti.CkHolderSpaceOn.exists_norm_le_mul_norm_nonDivergenceOperatorL`).
* **The method of continuity.** `L` maps `X` onto `C^{0,α}(Ω)` if and only if the Laplacian does
  (`TauCeti.CkHolderSpaceOn.surjective_nonDivergenceOperatorL_comp_subtypeL_iff`), and then `L` is
  an isomorphism of Banach spaces from `X` onto `C^{0,α}(Ω)`
  (`TauCeti.CkHolderSpaceOn.isInvertible_nonDivergenceOperatorL_comp_subtypeL`). More generally,
  for two such operators `L₀` and `L₁` the Dirichlet problem `L₀ u = f`, `u ∈ X`, is solvable for
  every `f ∈ C^{0,α}(Ω)` if and only if the one for `L₁` is
  (`TauCeti.CkHolderSpaceOn.forall_exists_nonDivergenceOperatorL_eq_iff`), with the case `L₀ = Δ`
  stated as `TauCeti.CkHolderSpaceOn.forall_exists_nonDivergenceOperatorL_eq_iff_laplacianL`.
* **Boundary values.** In that case, for every `f ∈ C^{0,α}(Ω)` and every `φ ∈ C^{2,α}(Ω)` the
  Dirichlet problem `L u = f` in `Ω`, `u = φ` on `∂Ω`, has exactly one solution `u ∈ C^{2,α}(Ω)`
  (`existsUnique_sub_mem_vanishingOnFrontierSubmodule_and_nonDivergenceOperatorL_eq`, in the
  `TauCeti.CkHolderSpaceOn` namespace). The boundary condition is `u - φ ∈ X`: since elements of
  `C^{2,α}(Ω)` are functions on `Ω`, `u - φ` tends to `0` at every frontier point.

The solvability of the Dirichlet problem for the Laplacian on `X` is Kellogg's theorem
(Gilbarg–Trudinger, Theorem 6.14 for `L = Δ`). With it the last two statements give the unique
solvability of the Dirichlet problem for `L` in `C^{2,α}(Ω)`.

## The argument

* **The a priori estimate.** An element `u ∈ X` is the restriction of a function `w` that is `C²`
  on the whole space, vanishes on `∂Ω` and has `D²w` `α`-Hölder on `closure Ω`
  (`TauCeti.CkHolderSpaceOn.exists_contDiff_eq_of_mem_vanishingOnFrontierSubmodule`). The
  coefficients extend from `Ω` to `α`-Hölder functions on `closure Ω` with the same norms
  (`TauCeti.HolderSpace.exists_holderOnWith_closure_and_norm_le`), and ellipticity passes to
  `closure Ω` by continuity. The global Schauder estimate with the maximum principle
  (`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos`, in
  the `TauCeti.PDE` namespace) then bounds `|w|`, `‖Dw‖`, `‖D²w‖` and the Hölder constant of `D²w`
  on `closure Ω` by a multiple of the `C^{0,α}(Ω)` norm of `L u`, with a constant depending only on
  the bounds on the coefficients.
* **The method of continuity.** Along the segment `L_t = (1 - t) Δ + t L`, `t ∈ [0, 1]`, the
  operator `L_t` has the coefficients `(1 - t) I + t a`, `t b` and `t c`
  (`TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_lineMap`). They are elliptic with constant
  `min 1 λ`, bounded in norm by `1 + K`, and `t c ≤ 0`, so the a priori estimate holds along the
  whole segment with one constant, and `L_0 = Δ` and `L_1 = L` are surjective together
  (`ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`). Between two operators `L₀` and
  `L₁` the coefficients along the segment are convex combinations of theirs, elliptic with constant
  `min λ₀ λ₁` and bounded by a common bound on all the coefficient norms.
* **Boundary values.** For `φ ∈ C^{2,α}(Ω)`, `u = φ + v` with `v ∈ X` solving `L v = f - L φ`.
  Uniqueness is the maximum principle on `X`
  (`TauCeti.CkHolderSpaceOn.injOn_nonDivergenceOperatorL`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity), Theorem 6.6 (the global Schauder estimate) and
  Theorem 6.8 (solvability for `L` from solvability for `Δ`).
-/

public section

noncomputable section

namespace TauCeti.CkHolderSpaceOn

open Set Filter Topology TopologicalSpace
open scoped NNReal

variable {n : ℕ} {α : ℝ≥0} {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Ellipticity passes to `closure Ω` for continuous extensions of the coefficients. -/
private theorem mul_norm_sq_le_toQuadraticForm'_of_mem_closure
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ}
    {A : Fin (n + 1) → Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hAeq : ∀ i j z (hz : z ∈ Ω), A i j z = a i j ⟨z, hz⟩)
    (hA : ∀ i j, ContinuousOn (A i j) (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {lam : ℝ} (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (ξ : EuclideanSpace ℝ (Fin (n + 1))) :
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ A i j z).toQuadraticForm' ξ := by
  refine le_on_closure (f := fun _ ↦ lam * ‖ξ‖ ^ 2)
    (g := fun z ↦ (Matrix.of fun i j ↦ A i j z).toQuadraticForm' ξ) (fun y hy ↦ ?_)
    continuousOn_const ?_ hz
  · have hAy : (Matrix.of fun i j ↦ A i j y) = Matrix.of fun i j ↦ a i j ⟨y, hy⟩ := by
      ext i j
      exact hAeq i j y hy
    rw [hAy]
    exact ha ⟨y, hy⟩ ξ
  -- The quadratic form is a polynomial in the entries.
  simp only [Matrix.toQuadraticForm'_apply]
  exact (continuous_const.dotProduct
    (continuous_id.matrix_mulVec continuous_const)).comp_continuousOn
      (continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ hA i j)

variable (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E')
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))

/-- **The a priori estimate of the Dirichlet problem in `C^{2,α}(Ω)`.** Let `0 < α < 1`, let
`Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary, and let `0 < λ` and `K` be given.
There is a constant `C` such that for all coefficients `aⁱʲ`, `bⁱ`, `c` in `C^{0,α}(Ω)` with
`λ ‖ξ‖² ≤ ξᵀ a ξ` on `Ω`, norms at most `K` and `c ≤ 0`, every `u ∈ C^{2,α}(Ω)` vanishing on `∂Ω`
satisfies `‖u‖_{C^{2,α}(Ω)} ≤ C ‖L u‖_{C^{0,α}(Ω)}`, where
`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u`. The constant depends only on `Ω`, `α`, `λ` and `K`
(Gilbarg–Trudinger, Theorem 6.6, with `sup |u|` bounded by the maximum principle). -/
theorem exists_norm_le_mul_norm_nonDivergenceOperatorL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α) {lam : ℝ}
    (hlam : 0 < lam) (K : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ)
      (b : Fin (n + 1) → HolderSpace α Ω ℝ) (c : HolderSpace α Ω ℝ),
      (∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K → (∀ x, c x ≤ 0) →
      ∀ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        ‖u‖ ≤ C * ‖nonDivergenceOperatorL hΩ hb hα₁.le a b c u‖ := by
  set B : ℝ≥0 := (n + 1) * K
  have hKB : K ≤ B := le_mul_of_one_le_left K.property (by simp)
  obtain ⟨C, hC⟩ :=
    PDE.exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos
      hα₀ hα₁ hb hbdry (∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), (K : ℝ)) K K B hlam
  refine ⟨8 * C, by positivity, fun a b c ha hak hbk hck hc u hu ↦ ?_⟩
  -- The coefficients, extended to `α`-Hölder functions on `closure Ω`.
  have hext (f : HolderSpace α Ω ℝ) := HolderSpace.exists_holderOnWith_closure_and_norm_le hα₀ f
  choose A hAeq hAH hAbd using fun i j ↦ hext (a i j)
  choose Bc hBeq hBH _ using fun i ↦ hext (b i)
  obtain ⟨Cc, hCeq, hCH, hCbd⟩ := hext c
  have hAK (i j) {z} (hz : z ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
      |A i j z| ≤ K := ((Real.norm_eq_abs _).symm.trans_le (hAbd i j z hz)).trans (hak i j)
  -- The drift as a vector field, `α`-Hölder on `Ω` and bounded there by `B`.
  set bv := fun z ↦ ∑ i, Bc i z • EuclideanSpace.single i (1 : ℝ)
  have hbvH : HolderOnWith B α bv Ω := (HolderOnWith.sum (s := Finset.univ) fun i _ ↦
    (((hBH i).mono subset_closure).mono_const (by exact_mod_cast hbk i)).smul_const
      (EuclideanSpace.single i (1 : ℝ))).mono_const (by simp [B])
  have hbvB (z) (hz : z ∈ Ω) : ‖bv z‖ ≤ B := by
    simpa [bv, hBeq _ ⟨z, hz⟩, B] using le_trans
      (HolderSpace.norm_sum_apply_smul_single_le_sum_norm b _) (Finset.sum_le_sum fun i _ ↦ hbk i)
  obtain ⟨w, hw, hwu, hw0, hwH⟩ :=
    exists_contDiff_eq_of_mem_vanishingOnFrontierSubmodule hbdry hb hα₀ hu
  -- On `Ω` the operator of the global estimate is `L u`.
  have hLu (z) (hz : z ∈ Ω) :
      ∑ i, ∑ j, (Matrix.of fun i j ↦ A i j z) i j • fderiv ℝ (fderiv ℝ w) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ w z (bv z) +
        Cc z * w z = nonDivergenceOperatorL hΩ hb hα₁.le a b c u ⟨z, hz⟩ := by
    rw [nonDivergenceOperatorL_apply hΩ hb hα₁.le u hwu]
    simp [hAeq _ _ ⟨z, hz⟩, hCeq ⟨z, hz⟩, bv, hBeq _ ⟨z, hz⟩]
  obtain ⟨h0, h2, h1, h2'⟩ := hC (a := fun z ↦ Matrix.of fun i j ↦ A i j z) (b := bv) (c := Cc)
    (fun z hz ↦ mul_norm_sq_le_toQuadraticForm'_of_mem_closure (fun i j z hz ↦ hAeq i j ⟨z, hz⟩)
      (fun i j ↦ (hAH i j).continuousOn hα₀) ha hz)
    (fun z hz ξ ↦ Matrix.toQuadraticForm'_le_of_forall_abs_le (fun i j ↦ hAK i j hz) ξ)
    (fun i j ↦ (hAH i j).mono_const (by exact_mod_cast hak i j)) (fun z hz i j ↦ hAK i j hz)
    hbvH hbvB
    (((hCH.mono subset_closure).mono_const (by exact_mod_cast hck)).mono_const hKB)
    (fun z hz ↦ by simpa using ((hCbd z (subset_closure hz)).trans hck).trans (mod_cast hKB))
    (fun z hz ↦ hCeq ⟨z, hz⟩ ▸ hc ⟨z, hz⟩) isOpen_univ (subset_univ _) hw.contDiffOn hw0 hwH
    (K := ‖nonDivergenceOperatorL hΩ hb hα₁.le a b c u‖₊)
    (F := ‖nonDivergenceOperatorL hΩ hb hα₁.le a b c u‖₊)
    (HolderSpace.holderOnWith_of_apply_eq (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (nonDivergenceOperatorL hΩ hb hα₁.le a b c u) fun x ↦ (hLu x.val x.property).symm)
    (fun z hz ↦ (hLu z hz).symm ▸ HolderSpace.abs_apply_le_norm _ _)
  -- Read the norm of `u` off the bounds on `w` and its derivatives.
  refine (norm_le_of_forall_norm_iteratedFDeriv_le hwu (fun i hi x ↦ ?_)
    (h2.mono subset_closure)).trans_eq (by push_cast; ring)
  interval_cases i
  · simpa using (h0 x (subset_closure x.property)).trans (by push_cast; gcongr; simp)
  · simpa [norm_iteratedFDeriv_one] using h1 x (subset_closure x.property)
  · exact_mod_cast h2' x (subset_closure x.property)

/-! ### The method of continuity -/

section MethodOfContinuity

variable (hα₁ : α < 1)

/-- **The a priori estimate along the segment from the Laplacian.** For elliptic `a` and `c ≤ 0`
there is `C` with `‖u‖ ≤ C ‖((1 - t) Δ + t L) u‖` for every `u ∈ C^{2,α}(Ω)` vanishing on `∂Ω` and
every `t ∈ [0, 1]`. -/
private theorem exists_forall_norm_le_lineMap (hα₀ : 0 < α)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α)
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ} {b : Fin (n + 1) → HolderSpace α Ω ℝ}
    {c : HolderSpace α Ω ℝ} {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x, c x ≤ 0) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : vanishingOnFrontierSubmodule 2 α Ω ℝ,
      ‖x‖ ≤ C * ‖AffineMap.lineMap
        (laplacianL α Ω ℝ ∘L (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL)
        (nonDivergenceOperatorL hΩ hb hα₁.le a b c ∘L
          (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL) t x‖ := by
  -- One bound `K` for all the coefficient norms: the norm of the triple of coefficients.
  set K : ℝ≥0 := ‖(a, b, c)‖₊
  have hak (i j) : ‖a i j‖ ≤ K :=
    (norm_le_pi_norm (a i) j).trans ((norm_le_pi_norm a i).trans (norm_fst_le (a, b, c)))
  have hbk (i) : ‖b i‖ ≤ K :=
    (norm_le_pi_norm b i).trans ((norm_fst_le (b, c)).trans (norm_snd_le (a, b, c)))
  have hck : ‖c‖ ≤ K := (norm_snd_le (b, c)).trans (norm_snd_le (a, b, c))
  obtain ⟨C, -, hC⟩ := exists_norm_le_mul_norm_nonDivergenceOperatorL hΩ hb hα₀ hα₁ hbdry
    (lt_min one_pos hlam) (1 + K)
  refine ⟨C, fun t ht x ↦ ?_⟩
  -- The closed ball of radius `1 + K` is convex, so it contains the segments of coefficients.
  have hball {y z : HolderSpace α Ω ℝ} (hy : ‖y‖ ≤ 1 + K) (hz : ‖z‖ ≤ 1 + K) :
      ‖AffineMap.lineMap y z t‖ ≤ 1 + K :=
    norm_lineMap_le_of_norm_le hy hz ht
  have hK : (K : ℝ) ≤ 1 + K := le_add_of_nonneg_left zero_le_one
  have h0 : ‖(0 : HolderSpace α Ω ℝ)‖ ≤ 1 + K := by
    rw [norm_zero]
    positivity
  have hcomp : AffineMap.lineMap
      (laplacianL α Ω ℝ ∘L (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL)
      (nonDivergenceOperatorL hΩ hb hα₁.le a b c ∘L
        (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL) t =
      nonDivergenceOperatorL hΩ hb hα₁.le
        (AffineMap.lineMap
          (fun i j ↦ HolderSpace.const ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j)) a t)
        (AffineMap.lineMap 0 b t) (AffineMap.lineMap 0 c t) ∘L
          (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL := by
    rw [nonDivergenceOperatorL_lineMap, nonDivergenceOperatorL_eq_laplacianL]
    ext1 y
    simp [AffineMap.lineMap_apply_module]
  rw [hcomp]
  refine hC _ _ _ (fun y ξ ↦ ?_) (fun i j ↦ ?_) (fun i ↦ ?_) ?_ (fun y ↦ ?_) x x.property
  · rw [HolderSpace.of_lineMap_const_apply]
    exact Matrix.min_one_mul_norm_sq_le_toQuadraticForm'_lineMap ht (ha y ξ)
  · push_cast
    refine hball ((HolderSpace.norm_const_le _).trans ?_) ((hak i j).trans hK)
    rw [Matrix.one_apply]
    split_ifs <;> simp [hK.trans' K.property]
  · push_cast
    exact hball h0 ((hbk i).trans hK)
  · push_cast
    exact hball h0 (hck.trans hK)
  · simp only [AffineMap.lineMap_apply_module, smul_zero, zero_add, HolderSpace.smul_apply,
      smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ht.1 (hc y)

/-- **The method of continuity for the Dirichlet problem** (Gilbarg–Trudinger, Theorem 6.8). Let
`0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary, and let
`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u` have coefficients in `C^{0,α}(Ω)` with `a` uniformly
elliptic and `c ≤ 0`. Then `L` maps the elements of `C^{2,α}(Ω)` vanishing on `∂Ω` onto
`C^{0,α}(Ω)` if and only if the Laplacian does. -/
theorem surjective_nonDivergenceOperatorL_comp_subtypeL_iff (hα₀ : 0 < α)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α)
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ} {b : Fin (n + 1) → HolderSpace α Ω ℝ}
    {c : HolderSpace α Ω ℝ} {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x, c x ≤ 0) :
    Function.Surjective (nonDivergenceOperatorL hΩ hb hα₁.le a b c ∘L
        (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL) ↔
      Function.Surjective
        (laplacianL α Ω ℝ ∘L (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL) := by
  obtain ⟨C, hC⟩ := exists_forall_norm_le_lineMap hΩ hb hα₁ hα₀ hbdry (b := b) hlam ha hc
  exact (ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap hC).symm

/-- **The Dirichlet problem for `L` is well posed when it is for the Laplacian.** Under the
hypotheses of `TauCeti.CkHolderSpaceOn.surjective_nonDivergenceOperatorL_comp_subtypeL_iff`, if the
Laplacian maps the elements of `C^{2,α}(Ω)` vanishing on `∂Ω` onto `C^{0,α}(Ω)`, then `L` is an
isomorphism of Banach spaces from these elements onto `C^{0,α}(Ω)`. -/
theorem isInvertible_nonDivergenceOperatorL_comp_subtypeL (hα₀ : 0 < α)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α)
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ} {b : Fin (n + 1) → HolderSpace α Ω ℝ}
    {c : HolderSpace α Ω ℝ} {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x, c x ≤ 0)
    (hΔ : Function.Surjective
      (laplacianL α Ω ℝ ∘L (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL)) :
    (nonDivergenceOperatorL hΩ hb hα₁.le a b c ∘L
      (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL).IsInvertible := by
  obtain ⟨C, hC⟩ := exists_forall_norm_le_lineMap hΩ hb hα₁ hα₀ hbdry (b := b) hlam ha hc
  have h := isPreconnected_Icc.isInvertible_of_forall_norm_le
    AffineMap.lineMap_continuous.continuousOn hC (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one) (by rwa [AffineMap.lineMap_apply_zero])
  rwa [AffineMap.lineMap_apply_one] at h

/-- **The Dirichlet problem with boundary values in `C^{2,α}(Ω)`.** Under the hypotheses of
`TauCeti.CkHolderSpaceOn.isInvertible_nonDivergenceOperatorL_comp_subtypeL`, for every
`f ∈ C^{0,α}(Ω)` and every `φ ∈ C^{2,α}(Ω)` there is exactly one `u ∈ C^{2,α}(Ω)` with
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u = f` in `Ω` and `u = φ` on `∂Ω`, in the sense that `u - φ` vanishes
on `∂Ω`. -/
theorem existsUnique_sub_mem_vanishingOnFrontierSubmodule_and_nonDivergenceOperatorL_eq
    (hα₀ : 0 < α) (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α)
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ} {b : Fin (n + 1) → HolderSpace α Ω ℝ}
    {c : HolderSpace α Ω ℝ} {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x, c x ≤ 0)
    (hΔ : Function.Surjective
      (laplacianL α Ω ℝ ∘L (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL))
    (f : HolderSpace α Ω ℝ) (φ : CkHolderSpaceOn 2 α Ω ℝ) :
    ∃! u : CkHolderSpaceOn 2 α Ω ℝ, u - φ ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ ∧
      nonDivergenceOperatorL hΩ hb hα₁.le a b c u = f := by
  obtain ⟨v, hv⟩ := (surjective_nonDivergenceOperatorL_comp_subtypeL_iff hΩ hb hα₁ hα₀ hbdry hlam ha
    hc).2 hΔ (f - nonDivergenceOperatorL hΩ hb hα₁.le a b c φ)
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at hv
  refine ⟨v + φ, ⟨by rw [add_sub_cancel_right]; exact v.property,
    by rw [map_add, hv, sub_add_cancel]⟩,
    fun u ⟨hu, hLu⟩ ↦ ?_⟩
  -- Uniqueness is the maximum principle on the elements vanishing on `∂Ω`.
  have h := injOn_nonDivergenceOperatorL hΩ hb hα₁.le (b := b) hlam ha hc hu v.property
    (by rw [map_sub, hLu, hv])
  rw [← h, sub_add_cancel]

/-- **The method of continuity between two operators.** Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be a
bounded open set with `C^{2,α}` boundary, and let `L₀ u = ∑ᵢⱼ a₀ⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ b₀ⁱ ∂ᵢu + c₀ u` and
`L₁ u = ∑ᵢⱼ a₁ⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ b₁ⁱ ∂ᵢu + c₁ u` have coefficients in the bounded `α`-Hölder functions
on `Ω`, with `a₀` and `a₁` uniformly elliptic with constants `λ₀ > 0` and `λ₁ > 0` and
`c₀, c₁ ≤ 0`. Then the Dirichlet problem `L₀ u = f` in `Ω`, `u = 0` on `∂Ω`, has a solution
`u ∈ C^{2,α}(Ω)` for every `f ∈ C^{0,α}(Ω)` if and only if the Dirichlet problem for `L₁` does
(Gilbarg–Trudinger, Theorems 5.2 and 6.8). -/
theorem forall_exists_nonDivergenceOperatorL_eq_iff (hα₀ : 0 < α)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α) {lam₀ lam₁ : ℝ}
    (hlam₀ : 0 < lam₀) (hlam₁ : 0 < lam₁) {a₀ a₁ : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ}
    {b₀ b₁ : Fin (n + 1) → HolderSpace α Ω ℝ} {c₀ c₁ : HolderSpace α Ω ℝ}
    (ha₀ : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam₀ * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a₀ i j x).toQuadraticForm' ξ)
    (ha₁ : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam₁ * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a₁ i j x).toQuadraticForm' ξ)
    (hc₀ : ∀ x : Ω, c₀ x ≤ 0) (hc₁ : ∀ x : Ω, c₁ x ≤ 0) :
    (∀ f : HolderSpace α Ω ℝ, ∃ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        nonDivergenceOperatorL hΩ hb hα₁.le a₀ b₀ c₀ u = f) ↔
      ∀ f : HolderSpace α Ω ℝ, ∃ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        nonDivergenceOperatorL hΩ hb hα₁.le a₁ b₁ c₁ u = f := by
  set V := vanishingOnFrontierSubmodule 2 α Ω ℝ
  -- A common bound `M` on the norms of all the coefficients.
  set S : Set (HolderSpace α Ω ℝ) :=
    range (Function.uncurry a₀) ∪ range (Function.uncurry a₁) ∪ range b₀ ∪ range b₁ ∪ {c₀, c₁}
  obtain ⟨M, hM⟩ : BddAbove (norm '' S) :=
    ((((((finite_range _).union (finite_range _)).union (finite_range _)).union
      (finite_range _)).union (toFinite _)).image _).bddAbove
  have hS {f} (hf : f ∈ S) : ‖f‖ ≤ M := hM (mem_image_of_mem _ hf)
  have hM0 : 0 ≤ M := (norm_nonneg c₀).trans (hS (by simp [S]))
  obtain ⟨C, -, hC⟩ := exists_norm_le_mul_norm_nonDivergenceOperatorL hΩ hb hα₀ hα₁ hbdry
    (lt_min hlam₀ hlam₁) ⟨M, hM0⟩
  -- The convex combinations of the coefficients satisfy the same bounds.
  have hnorm {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {f₀ f₁ : HolderSpace α Ω ℝ} (h₀ : f₀ ∈ S)
      (h₁ : f₁ ∈ S) : ‖AffineMap.lineMap f₀ f₁ t‖ ≤ M :=
    norm_lineMap_le_of_norm_le (hS h₀) (hS h₁) ht
  -- The operators restricted to the elements vanishing on `∂Ω`.
  set T : (Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ) → (Fin (n + 1) → HolderSpace α Ω ℝ) →
      HolderSpace α Ω ℝ → V →L[ℝ] HolderSpace α Ω ℝ :=
    fun a b c ↦ nonDivergenceOperatorL hΩ hb hα₁.le a b c ∘L V.subtypeL
  have hsurj (a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ)
      (b : Fin (n + 1) → HolderSpace α Ω ℝ) (c : HolderSpace α Ω ℝ) :
      Function.Surjective (T a b c) ↔
        ∀ f, ∃ u ∈ V, nonDivergenceOperatorL hΩ hb hα₁.le a b c u = f :=
    ⟨fun h f ↦ let ⟨u, hu⟩ := h f; ⟨u, u.property, hu⟩,
      fun h f ↦ let ⟨u, hu, huf⟩ := h f; ⟨⟨u, hu⟩, huf⟩⟩
  rw [← hsurj, ← hsurj]
  refine ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap (C := C) fun t ht u ↦ ?_
  -- Along the segment, the operators are those of the convex combinations of the coefficients.
  have hT : AffineMap.lineMap (T a₀ b₀ c₀) (T a₁ b₁ c₁) t u =
      nonDivergenceOperatorL hΩ hb hα₁.le (AffineMap.lineMap a₀ a₁ t) (AffineMap.lineMap b₀ b₁ t)
        (AffineMap.lineMap c₀ c₁ t) u := by
    rw [nonDivergenceOperatorL_lineMap]
    simp only [T, AffineMap.lineMap_apply_module, _root_.add_apply,
      _root_.smul_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [hT, ← Submodule.norm_coe]
  refine hC _ _ _ (fun x ξ ↦ ?_) (fun i j ↦ hnorm ht (by simp [S]) (by simp [S]))
    (fun i ↦ hnorm ht (by simp [S]) (by simp [S])) (hnorm ht (by simp [S]) (by simp [S]))
    (fun x ↦ ?_) u u.property
  · -- The matrix is the convex combination of the two matrices, and so is its quadratic form.
    have hA : (Matrix.of fun i j ↦ AffineMap.lineMap (a₀ i j) (a₁ i j) t x) =
        (1 - t) • (Matrix.of fun i j ↦ a₀ i j x) + t • Matrix.of fun i j ↦ a₁ i j x := by
      ext i j
      simp [AffineMap.lineMap_apply_module, HolderSpace.add_apply, HolderSpace.smul_apply]
    rw [hA, Matrix.toQuadraticForm'_add, Matrix.toQuadraticForm'_smul,
      Matrix.toQuadraticForm'_smul]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    nlinarith [(mul_le_mul_of_nonneg_right (min_le_left lam₀ lam₁) (sq_nonneg ‖ξ‖)).trans
      (ha₀ x ξ), (mul_le_mul_of_nonneg_right (min_le_right lam₀ lam₁) (sq_nonneg ‖ξ‖)).trans
      (ha₁ x ξ), ht.1, ht.2]
  · simp only [AffineMap.lineMap_apply_module, HolderSpace.add_apply, HolderSpace.smul_apply,
      smul_eq_mul]
    nlinarith [hc₀ x, hc₁ x, ht.1, ht.2]

/-- **Reduction of the Dirichlet problem to Poisson's equation.** Let `0 < α < 1`, let
`Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary, and let
`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u` have coefficients in the bounded `α`-Hölder functions on
`Ω`, with `a` uniformly elliptic and `c ≤ 0`. Then the Dirichlet problem `L u = f` in `Ω`, `u = 0`
on `∂Ω`, has a solution `u ∈ C^{2,α}(Ω)` for every `f ∈ C^{0,α}(Ω)` if and only if the Dirichlet
problem for Poisson's equation `Δu = f` does (Gilbarg–Trudinger, Theorem 6.8, for zero boundary
values). The solution is unique (`TauCeti.CkHolderSpaceOn.injOn_nonDivergenceOperatorL`). -/
theorem forall_exists_nonDivergenceOperatorL_eq_iff_laplacianL (hα₀ : 0 < α)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α) {lam : ℝ}
    (hlam : 0 < lam) {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ}
    {b : Fin (n + 1) → HolderSpace α Ω ℝ} {c : HolderSpace α Ω ℝ}
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x : Ω, c x ≤ 0) :
    (∀ f : HolderSpace α Ω ℝ, ∃ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        nonDivergenceOperatorL hΩ hb hα₁.le a b c u = f) ↔
      ∀ f : HolderSpace α Ω ℝ, ∃ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        laplacianL α Ω ℝ u = f := by
  rw [← nonDivergenceOperatorL_eq_laplacianL hΩ hb hα₁.le]
  refine forall_exists_nonDivergenceOperatorL_eq_iff hΩ hb hα₁ hα₀ hbdry hlam one_pos ha
    (fun x ξ ↦ ?_) hc fun _ ↦ le_rfl
  -- The identity matrix has quadratic form `‖ξ‖²`.
  have hI : (Matrix.of fun i j ↦
      HolderSpace.const (α := α) ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j) x) = 1 := by
    ext i j
    simp [HolderSpace.const_apply]
  rw [hI, PDE.toQuadraticForm'_one, one_mul]

end MethodOfContinuity

end TauCeti.CkHolderSpaceOn
