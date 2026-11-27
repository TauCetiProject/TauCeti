/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Piecewise
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Piecewise
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FirstVariation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration

/-!
# Second variation of energy for piecewise smooth variations

Let `F : ℝ → ℝ → M` be a continuous piecewise `C³` two-parameter family on a nondecreasing
partition `τ₀ ≤ τ₁ ≤ ⋯ ≤ τ_{n+1}`, witnessed by smooth extensions `G i` which are `C³` on
`{0} × [τ_i, τ_{i+1}]` and agree with `F` on `[τ_i, τ_{i+1}]` for all variation parameters near `0`.
Near `s = 0` the energy of `F s` is the sum of the piece energies of `G i s`, and each piece energy
is differentiable near `s = 0` (`TauCeti.Manifold.eventually_differentiableAt_energy`), so `d/ds E`
is locally the sum of the piece derivatives. Differentiating a second time at `s = 0` using
`TauCeti.Manifold.hasDerivAt_deriv_energy` on each piece gives:

* the sum of the piece index forms `I(V_i, V_i)`;
* the outer boundary transverse-acceleration pairings `⟪A_n(τ_{n+1}), γ'_n(τ_{n+1})⟫` and
  `-⟪A_0(τ_0), γ'_0(τ_0)⟫`;
* at each interior vertex `τ_{j+1}`, the jump `⟪A_j(τ_{j+1}), γ'_j(τ_{j+1})⟫ -
  ⟪A_{j+1}(τ_{j+1}), γ'_{j+1}(τ_{j+1})⟫` of the transverse acceleration of the moving vertex paired
  with the incoming minus outgoing velocity;
* minus the sum of the bulk longitudinal-acceleration integrals `∫_{τ_i}^{τ_{i+1}} ⟪A_i, D_t γ'_i⟫`.

When `F` is the exponential variation `(s, t) ↦ exp_(γ t) (s • V t)` of a curve `γ` along a
continuous piecewise `C³` tangent field `V` on `[a, b]` (`IsPiecewiseContMDiffOn` or a bundled
`PiecewiseContMDiffSectionAlong`), each transverse curve is geodesic near `s = 0` and therefore has
vanishing covariant acceleration at `s = 0` (including at the partition vertices), so all outer,
corner, and bulk transverse-acceleration terms vanish, while
`TauCeti.Manifold.sum_indexForm_adjacent_intervals` combines the piece index forms into the single
unrestricted `TauCeti.Manifold.indexForm I γ V V`.
Along a geodesic `γ` on `(a, b)` with cancelling outer first-variation pairings, any continuous
piecewise `C³` field `V` with `I(V, V) < 0` therefore strictly decreases the energy of
`exp_(γ ·) (s • V ·)` for small `s ≠ 0` — the broken-field shortening principle of Morse index
theory.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise`: **second variation of energy** for a
  continuous piecewise `C³` family, including all outer and interior corner transverse-acceleration
  terms.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints`: specialization to
  stationary outer endpoints.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn` and
  `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn_of_fixed_endpoints`:
  specializations to broken-geodesic central curves with free or stationary outer endpoints.
* `hasDerivAt_deriv_energy_exponentialVariation_of_isPiecewiseContMDiffOn` and
  `PiecewiseContMDiffSectionAlong.hasDerivAt_deriv_energy_exponentialVariation` (in
  `TauCeti.Manifold`): second variation of energy along the exponential variation of a continuous
  piecewise `C³` field equals `I(V, V)`.
* `indexForm_nonneg_of_isLocalMin_energy_exponentialVariation_of_isPiecewiseContMDiffOn`,
  `PiecewiseContMDiffSectionAlong.indexForm_nonneg_of_isLocalMin_energy_exponentialVariation`,
  `eventually_energy_exponentialVariation_lt_of_indexForm_neg_of_isPiecewiseContMDiffOn`, and
  `PiecewiseContMDiffSectionAlong.eventually_energy_exponentialVariation_lt_of_indexForm_neg`
  (in `TauCeti.Manifold`): local-minimum nonnegativity and strict energy shortening for piecewise
  `C³` fields.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §13 and §15 (broken variations and the index theorem).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 10
  (where the length counterpart of the second variation formula and piecewise smooth vector fields
  are developed).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 9, §2 and Chapter 10, §2.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Piecewise smooth two-parameter families -/

/-- **Second variation of energy for a continuous piecewise `C³` family.** At each interior vertex
`τ_{j+1}` the corner contribution is the pairing of the incoming extension's transverse acceleration
with its incoming velocity minus the corresponding outgoing pairing; since adjacent extensions agree
along the moving vertex near `s = 0`, both transverse accelerations represent the acceleration of
that vertex. -/
theorem hasDerivAt_deriv_energy_piecewise {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ))) :
    let A := fun (i : Fin (n + 1)) t ↦
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (curveVelocity I (G i 0) t)
    HasDerivAt (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      ((∑ i : Fin (n + 1), indexForm I (G i 0) (variationField I (G i))
          (variationField I (G i)) (τ i.castSucc) (τ i.succ)) +
        A (Fin.last n) (τ (Fin.last (n + 1))) - A 0 (τ 0) +
        (∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc))) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
            (acceleration (leviCivitaConnection I M) (G i 0) t)) 0 := by
  intro A
  have hGu (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ uIcc (τ i.castSucc) (τ i.succ)) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t) :=
    hG i t (by simpa only [uIcc_of_le (hτ (Fin.castSucc_le_succ i))] using ht)
  -- Near `s = 0`, `E(F s)` is the sum of `E(G i s)` and each `s ↦ E(G i s)` is differentiable.
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  have heq := eventually_energy_eq_sum_of_piecewise τ hτ
    (fun i t ht ↦ (hG i t ht).of_le (by norm_num)) hFG
  refine (TauCeti.hasDerivAt_deriv_sum_of_eventuallyEq heq
    (fun i _ ↦ eventually_differentiableAt_energy (u := 0) fun t ht ↦
      (hGu i t ht).of_le (by norm_num))
    (fun i _ ↦ hasDerivAt_deriv_energy (I := I) (F := G i) (a := τ i.castSucc) (b := τ i.succ)
      (hGu i))).congr_deriv ?_
  have hboundary := Fin.sum_univ_sub_eq_boundary_add_sum_jump (fun i j ↦ A i (τ j))
  dsimp only [A] at hboundary ⊢
  simp only [add_sub_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib, hboundary]; ring

/-- **Second variation of energy for a piecewise `C³` family with fixed outer endpoints.**
Stationary outer endpoints kill the two outer transverse-acceleration pairings while retaining all
interior corner jump terms. -/
theorem hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (ha : ∀ᶠ s in 𝓝 0, F s (τ 0) = F 0 (τ 0))
    (hb : ∀ᶠ s in 𝓝 0, F s (τ (Fin.last (n + 1))) = F 0 (τ (Fin.last (n + 1)))) :
    let A := fun (i : Fin (n + 1)) t ↦
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (curveVelocity I (G i 0) t)
    HasDerivAt (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      ((∑ i : Fin (n + 1), indexForm I (G i 0) (variationField I (G i))
          (variationField I (G i)) (τ i.castSucc) (τ i.succ)) +
        (∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc))) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
            (acceleration (leviCivitaConnection I M) (G i 0) t)) 0 := by
  intro A
  refine (hasDerivAt_deriv_energy_piecewise τ hτ hG hFG).congr_deriv ?_
  dsimp only [A]
  rw [acceleration_eq_zero_of_eventuallyEq_const (leviCivitaConnection I M)
      (eventually_eq_left_of_piecewise hτ hFG ha),
    acceleration_eq_zero_of_eventuallyEq_const (leviCivitaConnection I M)
      (eventually_eq_right_of_piecewise hτ hFG hb),
    inner_zero_left, inner_zero_left]; ring

/-- **Second variation of energy of a broken geodesic.** When each smooth extension's central curve
`G i 0` is a geodesic on the open subinterval `(τ_i, τ_{i+1})`, the bulk longitudinal-acceleration
integrals vanish, leaving the sum of piece index forms, the outer endpoint transverse-acceleration
pairings, and the interior corner jumps. -/
theorem hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hγ : ∀ i : Fin (n + 1), IsGeodesicCurveOn I (G i 0) (Ioo (τ i.castSucc) (τ i.succ))) :
    let A := fun (i : Fin (n + 1)) t ↦
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (curveVelocity I (G i 0) t)
    HasDerivAt (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      ((∑ i : Fin (n + 1), indexForm I (G i 0) (variationField I (G i))
          (variationField I (G i)) (τ i.castSucc) (τ i.succ)) +
        A (Fin.last n) (τ (Fin.last (n + 1))) - A 0 (τ 0) +
        ∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc))) 0 := by
  intro A
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  refine (hasDerivAt_deriv_energy_piecewise τ hτ hG hFG).congr_deriv ?_
  rw [Finset.sum_eq_zero fun i _ ↦ (hγ i).integral_inner_acceleration_eq_zero
    (by rw [uIoo_of_le (hτ (Fin.castSucc_le_succ i))]) _, sub_zero]

/-- **Second variation of energy of a broken geodesic with fixed outer endpoints.** When each smooth
extension's central curve `G i 0` is a geodesic on `(τ_i, τ_{i+1})` and the outer endpoints are
stationary, only the sum of piece index forms and the interior corner transverse-acceleration jumps
remain. -/
theorem hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn_of_fixed_endpoints {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hγ : ∀ i : Fin (n + 1), IsGeodesicCurveOn I (G i 0) (Ioo (τ i.castSucc) (τ i.succ)))
    (ha : ∀ᶠ s in 𝓝 0, F s (τ 0) = F 0 (τ 0))
    (hb : ∀ᶠ s in 𝓝 0, F s (τ (Fin.last (n + 1))) = F 0 (τ (Fin.last (n + 1)))) :
    let A := fun (i : Fin (n + 1)) t ↦
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (curveVelocity I (G i 0) t)
    HasDerivAt (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      ((∑ i : Fin (n + 1), indexForm I (G i 0) (variationField I (G i))
          (variationField I (G i)) (τ i.castSucc) (τ i.succ)) +
        ∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc))) 0 := by
  intro A
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  refine (hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints τ hτ hG hFG ha hb).congr_deriv ?_
  rw [Finset.sum_eq_zero fun i _ ↦ (hγ i).integral_inner_acceleration_eq_zero
    (by rw [uIoo_of_le (hτ (Fin.castSucc_le_succ i))]) _, sub_zero]

/-! ### Exponential variations along continuous piecewise smooth fields -/

section PiecewiseExponential

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- **Second variation of energy along a piecewise `C³` exponential variation.** Let `V` be a
continuous piecewise `C³` tangent field along `γ` on `[a, b]` (`IsPiecewiseContMDiffOn`). Then
`d²/ds² E(exp_(γ ·) (s • V ·)) |₀ = I(V, V)`, where `I(V, V)` is the single unrestricted
`TauCeti.Manifold.indexForm` over `[a, b]`. -/
theorem hasDerivAt_deriv_energy_exponentialVariation_of_isPiecewiseContMDiffOn {a b : ℝ}
    (hV : IsPiecewiseContMDiffOn I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) a b) :
    HasDerivAt (deriv fun s ↦ energy I (exponentialVariation I γ V s) a b)
      (indexForm I γ V V a b) 0 := by
  obtain ⟨n, τ, hτa, hτb, hτ, hpieces⟩ := hV.exists_partition
  have hpi (i : Fin (n + 1)) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc (τ i.castSucc) (τ i.succ)) := by
    rw [uIcc_of_le (hτ i).le]; exact hpieces i
  have heq := eventually_energy_exponentialVariation_eq_sum τ
    (Fin.strictMono_iff_lt_succ.mpr hτ).monotone fun i ↦ (hpieces i).of_le (by norm_num)
  rw [hτa, hτb] at heq
  refine (TauCeti.hasDerivAt_deriv_sum_of_eventuallyEq heq
    (fun i _ ↦
      eventually_differentiableAt_energy_exponentialVariation ((hpi i).of_le (by norm_num)))
    (fun i _ ↦ hasDerivAt_deriv_energy_exponentialVariation (hpi i))).congr_deriv ?_
  rw [sum_indexForm_adjacent_intervals τ fun i ↦ intervalIntegrable_indexFormIntegrand
    ((hpi i).of_le (by norm_num)) ((hpi i).of_le (by norm_num)), hτa, hτb]

/-- **Second variation of energy along a bundled piecewise smooth section.** Specialization of
`hasDerivAt_deriv_energy_exponentialVariation_of_isPiecewiseContMDiffOn` to a bundled section
`W : PiecewiseContMDiffSectionAlong hγp` (`3 ≤ n`) extended by zero outside `[a, b]`. -/
theorem PiecewiseContMDiffSectionAlong.hasDerivAt_deriv_energy_exponentialVariation
    {n : ℕ∞ω} {a b : ℝ} {hγp : IsPiecewiseContMDiffOn I n γ a b} (hn : 3 ≤ n)
    (W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγp) :
    HasDerivAt (deriv fun s ↦ energy I (exponentialVariation I γ W.extendByZero s) a b)
      (indexForm I γ W.extendByZero W.extendByZero a b) 0 :=
  hasDerivAt_deriv_energy_exponentialVariation_of_isPiecewiseContMDiffOn
    (W.isPiecewiseContMDiffOn_extendByZero.of_le hn)

/-- **Nonnegativity of the index form on piecewise `C³` fields at a local minimum of the energy.**
If `V` is continuous piecewise `C³` along `γ` on `[a, b]` and `s ↦ E(exp_(γ ·) (s • V ·))` has a
local minimum at `s = 0`, then `0 ≤ I(V, V)`. -/
theorem indexForm_nonneg_of_isLocalMin_energy_exponentialVariation_of_isPiecewiseContMDiffOn
    {a b : ℝ} (hV : IsPiecewiseContMDiffOn I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) a b)
    (hmin : IsLocalMin (fun s ↦ energy I (exponentialVariation I γ V s) a b) 0) :
    0 ≤ indexForm I γ V V a b := by
  obtain ⟨n, τ, hτa, hτb, hτ, hpieces⟩ := hV.exists_partition
  have hpi (i : Fin (n + 1)) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc (τ i.castSucc) (τ i.succ)) := by
    rw [uIcc_of_le (hτ i).le]; exact hpieces i
  have heq := eventually_energy_exponentialVariation_eq_sum τ
    (Fin.strictMono_iff_lt_succ.mpr hτ).monotone fun i ↦ (hpieces i).of_le (by norm_num)
  rw [hτa, hτb] at heq
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin (((HasDerivAt.fun_sum (u := Finset.univ)
    fun i _ ↦ hasDerivAt_energy_exponentialVariation (I := I) (γ := γ) (V := V)
      ((hpi i).of_le (by norm_num))).congr_of_eventuallyEq heq).continuousAt) hmin
  rwa [(hasDerivAt_deriv_energy_exponentialVariation_of_isPiecewiseContMDiffOn hV).deriv] at hnn

/-- **Nonnegativity of the index form on a bundled piecewise smooth section at a local minimum of
the energy.** Specialization of
`indexForm_nonneg_of_isLocalMin_energy_exponentialVariation_of_isPiecewiseContMDiffOn` to a bundled
section `W : PiecewiseContMDiffSectionAlong hγp` (`3 ≤ n`). -/
theorem PiecewiseContMDiffSectionAlong.indexForm_nonneg_of_isLocalMin_energy_exponentialVariation
    {n : ℕ∞ω} {a b : ℝ} {hγp : IsPiecewiseContMDiffOn I n γ a b} (hn : 3 ≤ n)
    (W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγp)
    (hmin : IsLocalMin (fun s ↦ energy I (exponentialVariation I γ W.extendByZero s) a b) 0) :
    0 ≤ indexForm I γ W.extendByZero W.extendByZero a b :=
  indexForm_nonneg_of_isLocalMin_energy_exponentialVariation_of_isPiecewiseContMDiffOn
    (W.isPiecewiseContMDiffOn_extendByZero.of_le hn) hmin

/-- **Broken-field energy shortening along a geodesic.** Let `γ` be a geodesic on `(a, b)` and `V`
a continuous piecewise `C³` field along `γ` on `[a, b]` whose outer endpoint pairings satisfy
`⟪V(b), γ'_[a,b](b)⟫ = ⟪V(a), γ'_[a,b](a)⟫` (for instance `V(a) = 0` and `V(b) = 0`). If
`I(V, V) < 0`, then `E(exp_(γ ·) (s • V ·)) < E(γ)` for all sufficiently small `s ≠ 0`. -/
theorem eventually_energy_exponentialVariation_lt_of_indexForm_neg_of_isPiecewiseContMDiffOn
    {a b : ℝ} (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hV : IsPiecewiseContMDiffOn I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) a b)
    (hbdry : inner ℝ (V b) (curveVelocityWithin I γ (Icc a b) b) =
      inner ℝ (V a) (curveVelocityWithin I γ (Icc a b) a))
    (hneg : indexForm I γ V V a b < 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ), energy I (exponentialVariation I γ V s) a b < energy I γ a b := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hd₁ := hasDerivAt_energy_exponentialVariation_of_isPiecewiseContMDiffOn
    (fun t ht ↦ (hγ.mdifferentiableOn t ht).mdifferentiableAt (isOpen_Ioo.mem_nhds ht))
    (hV.of_le (by norm_num))
  have hd₁_zero : deriv (fun s ↦ energy I (exponentialVariation I γ V s) a b) 0 = 0 := by
    rw [hd₁.deriv, hγ.integral_inner_acceleration_eq_zero (by rw [uIoo_of_le hV.lt.le]),
      hbdry, sub_self, sub_zero]
  have hneg' : deriv (deriv fun s ↦ energy I (exponentialVariation I γ V s) a b) 0 < 0 := by
    rwa [(hasDerivAt_deriv_energy_exponentialVariation_of_isPiecewiseContMDiffOn hV).deriv]
  simpa only [exponentialVariation_zero] using TauCeti.eventually_gt_of_deriv_deriv_neg
    hneg' hd₁_zero hd₁.continuousAt

/-- **Broken-field energy shortening along a geodesic for a bundled piecewise smooth section.**
Specialization of
`eventually_energy_exponentialVariation_lt_of_indexForm_neg_of_isPiecewiseContMDiffOn` to a bundled
section `W : PiecewiseContMDiffSectionAlong hγp` (`3 ≤ n`). -/
theorem PiecewiseContMDiffSectionAlong.eventually_energy_exponentialVariation_lt_of_indexForm_neg
    {n : ℕ∞ω} {a b : ℝ} {hγp : IsPiecewiseContMDiffOn I n γ a b} (hn : 3 ≤ n)
    (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    (W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγp)
    (hbdry : inner ℝ (W.val ⟨b, hγp.lt.le, le_rfl⟩) (curveVelocityWithin I γ (Icc a b) b) =
      inner ℝ (W.val ⟨a, le_rfl, hγp.lt.le⟩) (curveVelocityWithin I γ (Icc a b) a))
    (hneg : indexForm I γ W.extendByZero W.extendByZero a b < 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      energy I (exponentialVariation I γ W.extendByZero s) a b < energy I γ a b := by
  refine eventually_energy_exponentialVariation_lt_of_indexForm_neg_of_isPiecewiseContMDiffOn
    hγ (W.isPiecewiseContMDiffOn_extendByZero.of_le hn) ?_ hneg
  simpa only [W.extendByZero_apply_of_mem ⟨hγp.lt.le, le_rfl⟩,
    W.extendByZero_apply_of_mem ⟨le_rfl, hγp.lt.le⟩] using hbdry

end PiecewiseExponential

end TauCeti.Manifold

end
