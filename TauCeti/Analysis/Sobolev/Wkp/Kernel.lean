/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import TauCeti.Analysis.Sobolev.Wkp.Classical
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.IteratedGradient.Multilinear
import TauCeti.Analysis.MvPolynomial.Poincare
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic

/-!
# Polynomial kernel of the top weak derivative on `W^{m+1,p}(Ω)`

On a preconnected open subset `Ω` of `EuclideanSpace ℝ ι`, an element `u ∈ W^{m+1,p}(Ω)` has
vanishing top weak derivative (`Wkp.iteratedGradient m u = 0`) if and only if its value agrees
almost everywhere on `Ω` with a polynomial function of total degree at most `m`
(`TauCeti.polynomialsDegLE ι m`). Neither boundedness nor boundary regularity of `Ω` is required,
and every exponent `1 ≤ p ≤ ∞` is covered.

The reverse direction holds on arbitrary open sets: a polynomial of total degree at most `m` is
smooth and its `(m + 1)`-st classical Fréchet derivative vanishes identically
(`TauCeti.iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE`), so
`Wkp.iteratedGradient_ae_eq_of_contDiffOn` identifies the top weak derivative with `0`.

The forward direction argues by induction on `m` along three basis-free steps followed by the
Euclidean polynomial Poincaré lemma:

1. Commutativity of mixed weak derivatives passes directional differentiation through
   `Wkp.iteratedGradient` (`TauCeti.Wkp.hasWeakLineDerivOn_iteratedGradient`), identifying
   `Wkp.iteratedGradient j (Wkp.lineDerivL v (j + 1) u)` with evaluation of the outermost slot of
   `Wkp.iteratedGradient (j + 1) u` at `v` (`TauCeti.Wkp.iteratedGradient_lineDerivL`).
2. When `Wkp.iteratedGradient (m + 1) u = 0`, each coordinate directional derivative
   `d i = Wkp.lineDerivL (single i 1) (m + 1) u` therefore has vanishing `m`-th iterated gradient,
   and by the induction hypothesis agrees almost everywhere on `Ω` with a polynomial
   `q i ∈ polynomialsDegLE ι m`. Mixed weak-derivative symmetry and open-set rigidity
   (`TauCeti.eq_of_mem_polynomialsDegLE_of_ae_eq_isOpen`) upgrade `∂_j q_i = ∂_i q_j` from almost
   everywhere on `Ω` to all of `EuclideanSpace ℝ ι`, so
   `TauCeti.exists_mem_polynomialsDegLE_gradient_eq` produces `Q ∈ polynomialsDegLE ι (m + 1)`
   whose classical gradient agrees almost everywhere on `Ω` with the weak gradient of `u`.
3. Subtracting `Q` locally on compactly contained balls and gluing local constants on the
   preconnected domain (`TauCeti.W1p.exists_value_ae_eq_add_const_of_gradient_ae_eq`) expresses
   `u` almost everywhere as `Q + c`.

## Main declarations

* `TauCeti.iteratedGradientChain_eq_zero_of_mem_polynomialsDegLE`: every classical iterated
  gradient field of order exceeding `m` vanishes on `polynomialsDegLE ι m`.
* `TauCeti.Wkp.iteratedGradient_eq_zero_of_ae_eq_mem_polynomialsDegLE`: a Sobolev function
  represented almost everywhere by a polynomial of degree at most `m ≤ k` has vanishing `(k + 1)`-st
  weak derivative.
* `TauCeti.Wkp.exists_mem_polynomialsDegLE_value_ae_eq_of_iteratedGradient_eq_zero`: on a
  preconnected domain, vanishing of `Wkp.iteratedGradient m u` implies almost-everywhere agreement
  with a polynomial in `polynomialsDegLE ι m`.
* `TauCeti.Wkp.iteratedGradient_eq_zero_iff`, `TauCeti.Wkp.norm_iteratedGradient_eq_zero_iff`:
  characterizations of the kernel of the top weak derivative and its `Lᵖ` seminorm.

## References

* J. Deny, J.-L. Lions, *Les espaces du type de Beppo Levi*, Ann. Inst. Fourier 5 (1954),
  305–370, Chapitre I, §2, Théorème 2.1.
* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer (2008), §4.3.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace Topology

/-! ### Polynomial kernel of the top weak derivative on `EuclideanSpace ℝ ι` -/

section Euclidean

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every classical iterated-gradient field of order exceeding `m` vanishes on
`polynomialsDegLE ι m`. -/
theorem iteratedGradientChain_eq_zero_of_mem_polynomialsDegLE {m k : ℕ} (hmk : m ≤ k)
    {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m) :
    iteratedGradientChain q k = 0 := by
  funext x
  rw [Pi.zero_apply, ← norm_eq_zero, norm_iteratedGradientChain,
    iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE (Nat.lt_succ_of_le hmk) hq, Pi.zero_apply,
    norm_zero]

/-- If `u ∈ W^{k+1,p}(Ω)` agrees almost everywhere on `Ω` with a polynomial of total degree at most
`m ≤ k`, then its `(k + 1)`-st weak derivative `Wkp.iteratedGradient k u` vanishes. -/
theorem Wkp.iteratedGradient_eq_zero_of_ae_eq_mem_polynomialsDegLE {m k : ℕ} (hmk : m ≤ k)
    {u : Wkp mu Omega p (k + 1)} {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m)
    (hu : (Wkp.value (k + 1) u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q) :
    Wkp.iteratedGradient k u = 0 := by
  have hcont : ContDiffOn ℝ (k + 1) q Omega :=
    (contDiff_of_mem_polynomialsDegLE hq).contDiffOn
  apply Lp.ext
  refine (Wkp.iteratedGradient_ae_eq_of_contDiffOn k u hcont hu).trans ?_
  rw [iteratedGradientChain_eq_zero_of_mem_polynomialsDegLE hmk hq]
  exact (Lp.coeFn_zero _ _ _).symm

/-- Symmetry of coordinate polynomial representatives of `Wkp.lineDerivL` on a nonempty open
domain: if `Wkp.lineDerivL (single i 1) (m + 1) u` agrees almost everywhere on `Ω` with
`q i ∈ polynomialsDegLE ι m`, then `∂_j (q i) = ∂_i (q j)` everywhere on `EuclideanSpace ℝ ι`. -/
private theorem fderiv_single_comm_of_lineDerivL_ae_eq [DecidableEq ι] {m : ℕ}
    (hOne : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (u : Wkp mu Omega p (m + 2)) {q : ι → EuclideanSpace ℝ ι → ℝ}
    (hq : ∀ i, q i ∈ polynomialsDegLE ι m)
    (hdq : ∀ i, (Wkp.value (m + 1) (Wkp.lineDerivL (EuclideanSpace.single i 1) (m + 1) u) :
      EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q i)
    (i j : ι) (x : EuclideanSpace ℝ ι) :
    fderiv ℝ (q i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (q j) x (EuclideanSpace.single i 1) := by
  set ei := EuclideanSpace.single (𝕜 := ℝ) i 1
  set ej := EuclideanSpace.single (𝕜 := ℝ) j 1
  have hqi_weak : HasWeakLineDerivOn mu Omega
      (Wkp.value (m + 1) (Wkp.lineDerivL ei (m + 1) u))
      (fun y ↦ fderiv ℝ (q i) y ej) ej :=
    (((contDiff_of_mem_polynomialsDegLE (n := 1) (hq i)).contDiffOn.hasWeakFDerivOn_fderiv
      ).hasWeakLineDerivOn ej).congr_ae (hdq i).symm
  have hqj_weak : HasWeakLineDerivOn mu Omega
      (Wkp.value (m + 1) (Wkp.lineDerivL ej (m + 1) u))
      (fun y ↦ fderiv ℝ (q j) y ei) ei :=
    (((contDiff_of_mem_polynomialsDegLE (n := 1) (hq j)).contDiffOn.hasWeakFDerivOn_fderiv
      ).hasWeakLineDerivOn ei).congr_ae (hdq j).symm
  have hcomm := (Wkp.hasWeakLineDerivOn_lineDerivL ei (m + 1) u).comm hqi_weak
    (Wkp.hasWeakLineDerivOn_lineDerivL ej (m + 1) u)
  have hae := hcomm.ae_eq hqj_weak
  exact congrFun (eq_of_mem_polynomialsDegLE_of_ae_eq_isOpen
    (fderiv_apply_mem_polynomialsDegLE (hq i) ej)
    (fderiv_apply_mem_polynomialsDegLE (hq j) ei)
    Omega.isOpen hOne hae) x

/-- Inductive step of `Wkp.exists_mem_polynomialsDegLE_value_ae_eq_of_iteratedGradient_eq_zero`:
integrate polynomial coordinate weak derivatives on a nonempty preconnected open set. -/
private theorem exists_mem_polynomialsDegLE_succ_of_lineDerivL_ae_eq [DecidableEq ι] {m : ℕ}
    (hOmega : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hOne : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (u : Wkp mu Omega p (m + 2)) {q : ι → EuclideanSpace ℝ ι → ℝ}
    (hq : ∀ i, q i ∈ polynomialsDegLE ι m)
    (hdq : ∀ i, (Wkp.value (m + 1) (Wkp.lineDerivL (EuclideanSpace.single i 1) (m + 1) u) :
      EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q i) :
    ∃ P ∈ polynomialsDegLE ι (m + 1),
      (Wkp.value (m + 2) u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] P := by
  obtain ⟨Q, hQdeg, -, -, hQgrad⟩ := exists_mem_polynomialsDegLE_gradient_eq hq
    (fderiv_single_comm_of_lineDerivL_ae_eq hOne u hq hdq)
  set u₁ : W1p mu Omega p := Wkp.firstOrder (m + 1) u
  have hcoord : ∀ i : ι,
      (fun x ↦ ⟪W1p.gradient u₁ x, EuclideanSpace.single i 1⟫_ℝ) =ᵐ[mu.restrict Omega] q i := by
    intro i
    set ei := EuclideanSpace.single (𝕜 := ℝ) i 1
    have hw1 : HasWeakLineDerivOn mu Omega (Wkp.value (m + 2) u)
        (fun x ↦ ⟪W1p.gradient u₁ x, ei⟫_ℝ) ei := by
      simpa only [u₁, Wkp.value_firstOrder, innerSL_apply_apply] using
        (W1p.hasWeakFDerivOn u₁).hasWeakLineDerivOn ei
    exact (hw1.ae_eq (Wkp.hasWeakLineDerivOn_lineDerivL ei (m + 1) u)).trans (hdq i)
  have hgrad : (W1p.gradient u₁ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) =ᵐ[mu.restrict Omega]
      ∇ Q := by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    rw [hQgrad x]
    simpa only [EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun ι ℝ).sum_repr' (W1p.gradient u₁ x)).symm.trans
        (Finset.sum_congr rfl fun i _ ↦ by
          rw [EuclideanSpace.basisFun_apply, real_inner_comm, hx i])
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_add_const_of_gradient_ae_eq hOmega
    (contDiff_of_mem_polynomialsDegLE (n := 1) hQdeg).contDiffOn hgrad
  refine ⟨fun x ↦ Q x + c,
    Submodule.add_mem _ hQdeg (const_mem_polynomialsDegLE ι (m + 1) c), ?_⟩
  simpa only [u₁, Wkp.value_firstOrder] using hc

/-- **Polynomial kernel of the top weak derivative (forward direction).** On a preconnected open
subset `Ω` of `EuclideanSpace ℝ ι`, if `u ∈ W^{m+1,p}(Ω)` has `Wkp.iteratedGradient m u = 0`, then
`Wkp.value (m + 1) u` agrees almost everywhere on `Ω` with a polynomial of total degree at most
`m`. -/
theorem Wkp.exists_mem_polynomialsDegLE_value_ae_eq_of_iteratedGradient_eq_zero
    (hOmega : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι))) {m : ℕ}
    {u : Wkp mu Omega p (m + 1)} (hu : Wkp.iteratedGradient m u = 0) :
    ∃ q ∈ polynomialsDegLE ι m,
      (Wkp.value (m + 1) u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q := by
  classical
  induction m with
  | zero =>
      rw [Wkp.iteratedGradient_zero u] at hu
      obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero hOmega hu
      refine ⟨fun _ ↦ c, const_mem_polynomialsDegLE ι 0 c, ?_⟩
      rw [Wkp.value_one u]
      exact hc
  | succ m ih =>
      rcases (Omega : Set (EuclideanSpace ℝ ι)).eq_empty_or_nonempty with hempty | hne
      · refine ⟨0, Submodule.zero_mem _, ?_⟩
        have hbot : ae (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) = ⊥ := by simp [hempty]
        exact Eventually.filter_mono hbot.le eventually_bot
      · have hd (i : ι) : ∃ q ∈ polynomialsDegLE ι m,
            (Wkp.value (m + 1) (Wkp.lineDerivL (EuclideanSpace.single i 1) (m + 1) u) :
              EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q :=
          ih (Wkp.iteratedGradient_lineDerivL_eq_zero_of_eq_zero _ hu)
        choose q hq hdq using hd
        exact exists_mem_polynomialsDegLE_succ_of_lineDerivL_ae_eq hOmega hne u hq hdq

/-- **Characterization of the kernel of the top weak derivative.** On a preconnected open subset
`Ω` of `EuclideanSpace ℝ ι`, the highest weak derivative `Wkp.iteratedGradient m u` of
`u ∈ W^{m+1,p}(Ω)` vanishes if and only if `u` agrees almost everywhere on `Ω` with a polynomial of
total degree at most `m`. -/
theorem Wkp.iteratedGradient_eq_zero_iff
    (hOmega : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι))) {m : ℕ}
    (u : Wkp mu Omega p (m + 1)) :
    Wkp.iteratedGradient m u = 0 ↔
      ∃ q ∈ polynomialsDegLE ι m,
        (Wkp.value (m + 1) u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q :=
  ⟨Wkp.exists_mem_polynomialsDegLE_value_ae_eq_of_iteratedGradient_eq_zero hOmega,
    fun ⟨_, hq, hu⟩ ↦ Wkp.iteratedGradient_eq_zero_of_ae_eq_mem_polynomialsDegLE le_rfl hq hu⟩

/-- **Characterization of the kernel of the top weak-derivative seminorm.** On a preconnected open
subset `Ω` of `EuclideanSpace ℝ ι`, `‖Wkp.iteratedGradient m u‖ = 0` if and only if `u` agrees
almost everywhere on `Ω` with a polynomial of total degree at most `m`. -/
theorem Wkp.norm_iteratedGradient_eq_zero_iff
    (hOmega : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι))) {m : ℕ}
    (u : Wkp mu Omega p (m + 1)) :
    ‖Wkp.iteratedGradient m u‖ = 0 ↔
      ∃ q ∈ polynomialsDegLE ι m,
        (Wkp.value (m + 1) u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] q := by
  rw [norm_eq_zero, Wkp.iteratedGradient_eq_zero_iff hOmega]

end Euclidean

/-! ### Edge cases and sharpness of `IsPreconnected` -/

-- On zero-dimensional Euclidean space `ℝ⁰`, every subset is subsingleton hence preconnected, and
-- every positive-order Sobolev function has vanishing top weak derivative.
example {mu : Measure (EuclideanSpace ℝ (Fin 0))} [mu.IsAddHaarMeasure]
    {Omega : Opens (EuclideanSpace ℝ (Fin 0))} {p : ℝ≥0∞} [Fact (1 ≤ p)] (m : ℕ)
    (u : Wkp mu Omega p (m + 1)) :
    Wkp.iteratedGradient m u = 0 := by
  have hsub : (Omega : Set (EuclideanSpace ℝ (Fin 0))).Subsingleton :=
    Set.subsingleton_of_subsingleton
  rw [Wkp.iteratedGradient_eq_zero_iff hsub.isPreconnected]
  have : Unique (EuclideanSpace ℝ (Fin 0)) := inferInstance
  rcases (Omega : Set (EuclideanSpace ℝ (Fin 0))).eq_empty_or_nonempty with hempty | ⟨x₀, _⟩
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    have hbot : ae (mu.restrict (Omega : Set (EuclideanSpace ℝ (Fin 0)))) = ⊥ := by simp [hempty]
    exact Eventually.filter_mono hbot.le eventually_bot
  · refine ⟨fun _ ↦ Wkp.value (m + 1) u x₀, const_mem_polynomialsDegLE (Fin 0) m _, ?_⟩
    exact ae_of_all _ fun x ↦ congrArg (Wkp.value (m + 1) u) (Subsingleton.elim x x₀)

-- Degree sharpness at higher order: on the unit ball `B(0, 1) ⊆ ℝ¹`, `x ↦ (x 0) ^ 2` represents
-- an element `v ∈ W^{3,2}(B(0, 1))` with `Wkp.iteratedGradient 2 v = 0` whose `W^{2,2}` projection
-- has `Wkp.iteratedGradient 1 (Wkp.lowerOrder 2 v) ≠ 0`.
example :
    let Omega : Opens (EuclideanSpace ℝ (Fin 1)) := ⟨ball 0 1, isOpen_ball⟩
    ∃ v : Wkp volume Omega 2 3,
      Wkp.iteratedGradient 2 v = 0 ∧ Wkp.iteratedGradient 1 (Wkp.lowerOrder 2 v) ≠ 0 := by
  intro Omega
  set P : MvPolynomial (Fin 1) ℝ := MvPolynomial.X 0 * MvPolynomial.X 0
  set g : EuclideanSpace ℝ (Fin 1) → ℝ := polynomialEvalₗ (Fin 1) P
  have hg2 : g ∈ polynomialsDegLE (Fin 1) 2 := by
    rw [polynomialEvalₗ_mem_polynomialsDegLE_iff]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X])
  have hg1 : g ∉ polynomialsDegLE (Fin 1) 1 := by
    intro hmem
    set e₀ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
    obtain ⟨c, hc⟩ := (mem_polynomialsDegLE_zero_iff (Fin 1)).mp
      (fderiv_apply_mem_polynomialsDegLE hmem e₀)
    have h0 : fderiv ℝ g 0 e₀ = c := congrFun hc 0
    have h1 : fderiv ℝ g e₀ e₀ = c := congrFun hc e₀
    simp [g, P, e₀] at h0 h1
    linarith
  obtain ⟨v, hv⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := Omega) (p := 2) 3 isOpen_univ (contDiff_of_mem_polynomialsDegLE hg2).contDiffOn
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) ball_subset_closedBall (subset_univ _)
  refine ⟨v, Wkp.iteratedGradient_eq_zero_of_ae_eq_mem_polynomialsDegLE le_rfl hg2 hv, fun h1 ↦ ?_⟩
  obtain ⟨q, hq, hvq⟩ :=
    (Wkp.iteratedGradient_eq_zero_iff (convex_ball (0 : EuclideanSpace ℝ (Fin 1)) 1).isPreconnected
      (Wkp.lowerOrder 2 v)).1 h1
  have hval : (Wkp.value 2 (Wkp.lowerOrder 2 v) : EuclideanSpace ℝ (Fin 1) → ℝ) =ᵐ[
      volume.restrict Omega] g := by simpa only [Wkp.value_succ] using hv
  have hgq : g = q := eq_of_mem_polynomialsDegLE_of_ae_eq_isOpen hg2 hq isOpen_ball
    (nonempty_ball.2 zero_lt_one) (hval.symm.trans hvq)
  exact hg1 (hgq ▸ hq)

-- `IsPreconnected` cannot be omitted in `Wkp.iteratedGradient_eq_zero_iff`: on the disconnected
-- open set `Ω = B(-2 e₀, 1) ∪ B(2 e₀, 1) ⊆ ℝ¹`, the locally constant function equal to `0` on the
-- negative half-line and `1` on the positive half-line defines an element of `W^{1,2}(Ω)` with
-- vanishing weak gradient that agrees almost everywhere with no single polynomial in
-- `polynomialsDegLE (Fin 1) 0`.
example :
    ∃ (Omega : Opens (EuclideanSpace ℝ (Fin 1))) (u : Wkp volume Omega 2 1),
      Wkp.iteratedGradient 0 u = 0 ∧
        ¬ ∃ q ∈ polynomialsDegLE (Fin 1) 0,
          (Wkp.value 1 u : EuclideanSpace ℝ (Fin 1) → ℝ) =ᵐ[volume.restrict Omega] q := by
  let c₀ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (-2)
  let c₁ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 2
  let Omega : Opens (EuclideanSpace ℝ (Fin 1)) :=
    ⟨ball c₀ 1 ∪ ball c₁ 1, isOpen_ball.union isOpen_ball⟩
  let Uneg : Set (EuclideanSpace ℝ (Fin 1)) := {x | x 0 < 0}
  let Upos : Set (EuclideanSpace ℝ (Fin 1)) := {x | 0 < x 0}
  have hUneg : IsOpen Uneg := isOpen_lt (PiLp.continuous_apply 2 _ 0) continuous_const
  have hUpos : IsOpen Upos := isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)
  let f : EuclideanSpace ℝ (Fin 1) → ℝ := fun x ↦ if 0 < x 0 then 1 else 0
  have hf_neg : ∀ x ∈ Uneg, f =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := fun x hx ↦ by
    filter_upwards [hUneg.mem_nhds hx] with y hy
    have hy0 : ¬ 0 < y 0 := not_lt.2 (le_of_lt hy)
    simp [f, hy0]
  have hf_pos : ∀ x ∈ Upos, f =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := fun x hx ↦ by
    filter_upwards [hUpos.mem_nhds hx] with y hy
    have hy0 : 0 < y 0 := hy
    simp [f, hy0]
  have hf_diff : ContDiffOn ℝ 1 f (Uneg ∪ Upos) := by
    rintro x (hx | hx)
    · exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (hf_neg x hx)).contDiffWithinAt
    · exact ((contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
        (hf_pos x hx)).contDiffWithinAt
  have hΩK : (Omega : Set (EuclideanSpace ℝ (Fin 1))) ⊆ closedBall c₀ 1 ∪ closedBall c₁ 1 :=
    union_subset_union ball_subset_closedBall ball_subset_closedBall
  have hB₀ : closedBall c₀ 1 ⊆ Uneg := fun x hx ↦ by
    have hle : |x 0 - (-2)| ≤ 1 := by
      have h1 : ‖(x - c₀) 0‖ ≤ ‖x - c₀‖ := PiLp.norm_apply_le (x - c₀) 0
      have h2 : ‖x - c₀‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hx
      simpa [c₀, Real.norm_eq_abs] using h1.trans h2
    have hlt : x 0 < 0 := by linarith [(abs_le.mp hle).2]
    exact hlt
  have hB₁ : closedBall c₁ 1 ⊆ Upos := fun x hx ↦ by
    have hle : |x 0 - 2| ≤ 1 := by
      have h1 : ‖(x - c₁) 0‖ ≤ ‖x - c₁‖ := PiLp.norm_apply_le (x - c₁) 0
      have h2 : ‖x - c₁‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hx
      simpa [c₁, Real.norm_eq_abs] using h1.trans h2
    have hlt : 0 < x 0 := by linarith [(abs_le.mp hle).1]
    exact hlt
  have hKU : closedBall c₀ 1 ∪ closedBall c₁ 1 ⊆ Uneg ∪ Upos := union_subset_union hB₀ hB₁
  obtain ⟨u₁, hu₁val, hu₁grad⟩ :=
    W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Omega)
      (p := 2) (hUneg.union hUpos) hf_diff
      ((isCompact_closedBall c₀ 1).union (isCompact_closedBall c₁ 1)) hΩK hKU
  let u : Wkp volume Omega 2 1 := u₁
  refine ⟨Omega, u, ?_, ?_⟩
  · rw [Wkp.iteratedGradient_zero u]
    apply Lp.ext
    refine hu₁grad.trans ?_
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet,
      Lp.coeFn_zero (EuclideanSpace ℝ (Fin 1)) 2
        (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 1))))] with x hx h0
    rw [h0]
    apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1))).injective
    rcases hKU (hΩK hx) with hx' | hx'
    · simp [toDual_gradient, (hf_neg x hx').fderiv_eq]
    · simp [toDual_gradient, (hf_pos x hx').fderiv_eq]
  · rintro ⟨q, hq, huq⟩
    obtain ⟨c, rfl⟩ := (mem_polynomialsDegLE_zero_iff (Fin 1)).mp hq
    rw [Wkp.value_one u] at huq
    have hfq : f =ᵐ[volume.restrict Omega] fun _ ↦ c := hu₁val.symm.trans huq
    have hc0 : (0 : ℝ) = c := by
      have hae0 : (fun _ : EuclideanSpace ℝ (Fin 1) ↦ (0 : ℝ)) =ᵐ[volume.restrict (ball c₀ 1)]
          fun _ ↦ c := by
        filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
          ae_restrict_of_ae_restrict_of_subset subset_union_left hfq] with x hx hfx
        have hx0 : ¬ 0 < x 0 := not_lt.2 (le_of_lt (hB₀ (ball_subset_closedBall hx)))
        simpa [f, hx0] using hfx
      exact Measure.eqOn_open_of_ae_eq hae0 isOpen_ball continuousOn_const continuousOn_const
        (mem_ball_self zero_lt_one)
    have hc1 : (1 : ℝ) = c := by
      have hae1 : (fun _ : EuclideanSpace ℝ (Fin 1) ↦ (1 : ℝ)) =ᵐ[volume.restrict (ball c₁ 1)]
          fun _ ↦ c := by
        filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
          ae_restrict_of_ae_restrict_of_subset subset_union_right hfq] with x hx hfx
        have hx1 : 0 < x 0 := hB₁ (ball_subset_closedBall hx)
        simpa [f, hx1] using hfx
      exact Measure.eqOn_open_of_ae_eq hae1 isOpen_ball continuousOn_const continuousOn_const
        (mem_ball_self zero_lt_one)
    linarith

end TauCeti
