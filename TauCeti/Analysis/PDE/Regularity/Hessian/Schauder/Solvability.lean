/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.C2HolderBoundary.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Operator
import TauCeti.Analysis.Holder.C2HolderBoundary.Extension
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
  (`TauCeti.CkHolderSpaceOn.isInvertible_nonDivergenceOperatorL_comp_subtypeL`).
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
  on the whole space (`TauCeti.CkHolderSpaceOn.exists_contDiff_eq`, the extension lemma for
  `C^{2,α}` domains), and `w` vanishes on `∂Ω`, where it is the limit of `u`. The coefficients
  extend from `Ω` to `α`-Hölder functions on `closure Ω` with the same norms
  (`TauCeti.HolderSpace.exists_holderOnWith_closure`), and ellipticity passes to `closure Ω` by
  continuity. The global Schauder estimate with the maximum principle
  (`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos`, in
  the `TauCeti.PDE` namespace) then bounds `|w|`, `‖Dw‖`, `‖D²w‖` and the Hölder constant of `D²w`
  on `closure Ω` by a multiple of the `C^{0,α}(Ω)` norm of `L u`, with a constant depending only on
  the bounds on the coefficients.
* **The method of continuity.** Along the segment `L_t = (1 - t) Δ + t L`, `t ∈ [0, 1]`, the
  operator `L_t` has the coefficients `(1 - t) I + t a`, `t b` and `t c`
  (`TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_lineMap`). They are elliptic with constant
  `min 1 λ`, bounded in norm by `1 + K`, and `t c ≤ 0`, so the a priori estimate holds along the
  whole segment with one constant, and `L_0 = Δ` and `L_1 = L` are surjective together
  (`ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`).
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

/-- An element of `C^{0,α}(Ω)`, `α > 0`, agrees on `Ω` with a function on `ℝ^{n+1}` that is
`α`-Hölder on `closure Ω` with constant its norm and bounded there by its norm. -/
private theorem exists_holderOnWith_closure_and_abs_le (hα₀ : 0 < α) (f : HolderSpace α Ω ℝ) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, (∀ z (hz : z ∈ Ω), g z = f ⟨z, hz⟩) ∧
      HolderOnWith ‖f‖₊ α g (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) ∧
      ∀ z ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), |g z| ≤ ‖f‖ := by
  obtain ⟨g, hg, hgH⟩ := HolderSpace.exists_holderOnWith_closure
    (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) hα₀ f
  refine ⟨g, fun z hz ↦ hg ⟨z, hz⟩, hgH, fun z hz ↦ ?_⟩
  -- The bound passes from `Ω` to its closure by continuity.
  refine le_on_closure (f := fun z ↦ |g z|) (g := fun _ ↦ ‖f‖) (fun y hy ↦ ?_)
    (hgH.continuousOn hα₀).abs continuousOn_const hz
  rw [hg ⟨y, hy⟩]
  exact HolderSpace.abs_apply_le_norm f _

/-- An element `u` of `C^{2,α}(Ω)` vanishing on `∂Ω`, for a bounded `Ω` with `C^{2,α}` boundary and
`α > 0`, is the restriction of a function `w` that is `C²` on the whole space, vanishes on `∂Ω`, and
has `D²w` `α`-Hölder on `closure Ω`. -/
private theorem exists_contDiff_eq_and_holderOnWith_closure (hα₀ : 0 < α)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {u : CkHolderSpaceOn 2 α Ω ℝ} (hu : u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ) :
    ∃ w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ 2 w ∧ (∀ x : Ω, w x = u x) ∧
      (∀ z ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), w z = 0) ∧
      ∃ V : ℝ≥0, HolderOnWith V α (_root_.iteratedFDeriv ℝ 2 w)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  obtain ⟨w, hw, hwu⟩ := exists_contDiff_eq hbdry hb hα₀ u
  refine ⟨w, hw, hwu, fun z hz ↦ ?_, _, (u.holderOnWith_iteratedFDeriv hwu).of_subset_closure
    subset_rfl fun _ _ ↦ (hw.continuous_iteratedFDeriv le_rfl).continuousWithinAt⟩
  -- At a frontier point, `w z` is the limit of `u`, which is `0`.
  have : (𝓝[(Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hz)
  refine tendsto_nhds_unique (hw.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((mem_vanishingOnFrontierSubmodule_iff.1 hu z hz).congr'
      (eventually_nhdsWithin_of_forall fun y hy ↦ ?_))
  rw [u.extend_apply_of_mem hy, hwu ⟨y, hy⟩]

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

/-- An element `u` of `C^{2,α}(Ω)` agreeing on `Ω` with a function `w` whose value, first and second
derivatives are bounded by `N` on `Ω`, and whose second derivative is `α`-Hölder on `Ω` with
constant `N`, has norm at most `4 N`. -/
private theorem norm_le_of_forall_norm_iteratedFDeriv_le {u : CkHolderSpaceOn 2 α Ω ℝ}
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hwu : ∀ x : Ω, w x = u x) {N : ℝ≥0}
    (h0 : ∀ x : Ω, |w x| ≤ N) (h1 : ∀ x : Ω, ‖fderiv ℝ w x‖ ≤ N)
    (h2 : ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ 2 w x‖ ≤ N)
    (hH : HolderOnWith N α (_root_.iteratedFDeriv ℝ 2 w) Ω) : ‖u‖ ≤ 4 * N := by
  have he : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).domRestrict (_root_.iteratedFDeriv ℝ 2 w) =
      (u.iteratedFDeriv (Fin.last 2) : Ω → EuclideanSpace ℝ (Fin (n + 1)) [×2]→L[ℝ] ℝ) :=
    funext fun x ↦ u.iteratedFDeriv_eq hwu (Fin.last 2) x
  have h := hH.holderWith
  rw [he] at h
  refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith (M := fun _ ↦ (N : ℝ))
    (fun _ ↦ N.property) (fun i x ↦ ?_) h).trans_eq ?_
  · rw [← u.iteratedFDeriv_eq hwu i x]
    fin_cases i
    · simpa [_root_.norm_iteratedFDeriv_zero] using h0 x
    · simpa [norm_iteratedFDeriv_one] using h1 x
    · exact h2 x
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

/-- A drift `∑ᵢ bⁱ eᵢ` whose components are `α`-Hölder on `s` with constants `Cᵢ` and bounded there
by `Cᵢ` is `α`-Hölder on `s` with constant `∑ᵢ Cᵢ` and bounded there by `∑ᵢ Cᵢ`. -/
private theorem holderOnWith_sum_smul_single_and_norm_le {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {Bc : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {C : Fin (n + 1) → ℝ≥0}
    (hH : ∀ i, HolderOnWith (C i) α (Bc i) s) (hB : ∀ i, ∀ z ∈ s, |Bc i z| ≤ C i) :
    HolderOnWith (∑ i, C i) α (fun z ↦ ∑ i, Bc i z • EuclideanSpace.single i (1 : ℝ)) s ∧
      ∀ z ∈ s, ‖∑ i, Bc i z • EuclideanSpace.single i (1 : ℝ)‖ ≤ ∑ i, (C i : ℝ) := by
  refine ⟨HolderOnWith.sum (s := Finset.univ) fun i _ ↦ HolderOnWith.of_dist_le
    (f := fun z ↦ Bc i z • EuclideanSpace.single i (1 : ℝ)) fun x hx y hy ↦ ?_,
    fun z hz ↦ (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)⟩
  · rw [dist_eq_norm, ← sub_smul, norm_smul, PiLp.norm_single, norm_one, mul_one, ← dist_eq_norm]
    exact (hH i).dist_le hx hy
  · rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    exact hB i z hz

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
  choose A hAeq hAH hAbd using fun i j ↦ exists_holderOnWith_closure_and_abs_le hα₀ (a i j)
  choose Bc hBeq hBH hBbd using fun i ↦ exists_holderOnWith_closure_and_abs_le hα₀ (b i)
  obtain ⟨Cc, hCeq, hCH, hCbd⟩ := exists_holderOnWith_closure_and_abs_le hα₀ c
  have hAK (i j) {z} (hz : z ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
      |A i j z| ≤ K := (hAbd i j z hz).trans (hak i j)
  -- The drift as a vector field, `α`-Hölder on `Ω` and bounded there by `B`.
  set bv : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun z ↦ ∑ i, Bc i z • EuclideanSpace.single i (1 : ℝ)
  obtain ⟨hbvH, hbvB⟩ := holderOnWith_sum_smul_single_and_norm_le (C := fun _ ↦ K)
    (fun i ↦ ((hBH i).mono subset_closure).mono_const (by exact_mod_cast hbk i))
    (fun i z hz ↦ (hBbd i z (subset_closure hz)).trans (hbk i))
  obtain ⟨w, hw, hwu, hw0, V, hwH⟩ := exists_contDiff_eq_and_holderOnWith_closure hα₀ hbdry hb hu
  -- On `Ω` the operator of the global estimate is `L u`.
  have hLu (z) (hz : z ∈ Ω) :
      ∑ i, ∑ j, (Matrix.of fun i j ↦ A i j z) i j • fderiv ℝ (fderiv ℝ w) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ w z (bv z) +
        Cc z * w z = nonDivergenceOperatorL hΩ hb hα₁.le a b c u ⟨z, hz⟩ := by
    rw [nonDivergenceOperatorL_apply hΩ hb hα₁.le u hwu]
    simp only [Matrix.of_apply, hAeq _ _ z hz, hCeq z hz, bv, map_sum, map_smul, smul_eq_mul,
      hBeq _ z hz]
  obtain ⟨h0, h2, h1, h2'⟩ := hC (a := fun z ↦ Matrix.of fun i j ↦ A i j z) (b := bv) (c := Cc)
    (fun z hz ↦ mul_norm_sq_le_toQuadraticForm'_of_mem_closure hAeq
      (fun i j ↦ (hAH i j).continuousOn hα₀) ha hz)
    (fun z hz ξ ↦ Matrix.toQuadraticForm'_le_of_forall_abs_le (fun i j ↦ hAK i j hz) ξ)
    (fun i j ↦ (hAH i j).mono_const (by exact_mod_cast hak i j)) (fun z hz i j ↦ hAK i j hz)
    (hbvH.mono_const (by simp [B])) (fun z hz ↦ (hbvB z hz).trans_eq (by simp [B]))
    (((hCH.mono subset_closure).mono_const (by exact_mod_cast hck)).mono_const hKB)
    (fun z hz ↦ ((hCbd z (subset_closure hz)).trans hck).trans (by exact_mod_cast hKB))
    (fun z hz ↦ hCeq z hz ▸ hc ⟨z, hz⟩) isOpen_univ (subset_univ _) hw.contDiffOn hw0 hwH
    (K := ‖nonDivergenceOperatorL hΩ hb hα₁.le a b c u‖₊)
    (F := ‖nonDivergenceOperatorL hΩ hb hα₁.le a b c u‖₊)
    (HolderSpace.holderOnWith_of_apply_eq (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (nonDivergenceOperatorL hΩ hb hα₁.le a b c u) fun x ↦ (hLu x.val x.property).symm)
    (fun z hz ↦ (hLu z hz).symm ▸ HolderSpace.abs_apply_le_norm _ _)
  -- Read the norm of `u` off the bounds on `w` and its derivatives.
  refine (norm_le_of_forall_norm_iteratedFDeriv_le hwu
    (fun x ↦ (h0 x (subset_closure x.property)).trans ?_)
    (fun x ↦ by exact_mod_cast h1 x (subset_closure x.property))
    (fun x ↦ by exact_mod_cast h2' x (subset_closure x.property))
    (h2.mono subset_closure)).trans_eq (by push_cast; ring)
  push_cast
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) C.property

/-! ### The method of continuity -/

section MethodOfContinuity

variable (hα₁ : α < 1)

/-- The coefficients of the Laplacian: the identity matrix. -/
private abbrev laplacianCoeff : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Along the segment from the identity to `a`, the matrix of coefficients at `x` is
`(1 - t) 1 + t a(x)`. -/
private theorem of_lineMap_laplacianCoeff_apply (a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ)
    (t : ℝ) (x : Ω) :
    (Matrix.of fun i j ↦ AffineMap.lineMap laplacianCoeff a t i j x) =
      AffineMap.lineMap (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Matrix.of fun i j ↦ a i j x)
        t := by
  ext i j
  simp only [AffineMap.lineMap_apply_module, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    HolderSpace.add_apply, HolderSpace.smul_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply]
  split_ifs <;> simp [HolderSpace.one_apply, HolderSpace.zero_apply]

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
    mem_closedBall_zero_iff.1 ((convex_closedBall 0 _).lineMap_mem
      (mem_closedBall_zero_iff.2 hy) (mem_closedBall_zero_iff.2 hz) ht)
  have hK : (K : ℝ) ≤ 1 + K := le_add_of_nonneg_left zero_le_one
  have h0 : ‖(0 : HolderSpace α Ω ℝ)‖ ≤ 1 + K := by
    rw [norm_zero]
    positivity
  have hcomp : AffineMap.lineMap
      (laplacianL α Ω ℝ ∘L (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL)
      (nonDivergenceOperatorL hΩ hb hα₁.le a b c ∘L
        (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL) t =
      nonDivergenceOperatorL hΩ hb hα₁.le (AffineMap.lineMap laplacianCoeff a t)
        (AffineMap.lineMap 0 b t) (AffineMap.lineMap 0 c t) ∘L
          (vanishingOnFrontierSubmodule 2 α Ω ℝ).subtypeL := by
    rw [nonDivergenceOperatorL_lineMap, nonDivergenceOperatorL_eq_laplacianL]
    ext1 y
    simp [AffineMap.lineMap_apply_module]
  rw [hcomp]
  refine hC _ _ _ (fun y ξ ↦ ?_) (fun i j ↦ ?_) (fun i ↦ ?_) ?_ (fun y ↦ ?_) x x.property
  · rw [of_lineMap_laplacianCoeff_apply]
    exact Matrix.min_one_mul_norm_sq_le_toQuadraticForm'_lineMap ht (ha y ξ)
  · push_cast
    refine hball ?_ ((hak i j).trans hK)
    by_cases hij : i = j
    · simp only [laplacianCoeff, hij, ite_true]
      -- The unit of `C^{0,α}(Ω)` is the constant function `1`.
      exact (HolderSpace.norm_const_le (1 : ℝ)).trans (by simp)
    · simpa [laplacianCoeff, hij] using h0
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

end MethodOfContinuity

end TauCeti.CkHolderSpaceOn
