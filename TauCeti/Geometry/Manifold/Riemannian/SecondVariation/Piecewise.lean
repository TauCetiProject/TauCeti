/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Piecewise
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
import TauCeti.Analysis.Calculus.DerivativeTest

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
* the outer boundary transverse-acceleration pairings `⟪A_{n}(τ_{n+1}), γ'_{n}(τ_{n+1})⟫` and
  `-⟪A_0(τ_0), γ'_0(τ_0)⟫`;
* at each interior vertex `τ_{j+1}`, the jump `⟪A_j(τ_{j+1}), γ'_j(τ_{j+1})⟫ -
  ⟪A_{j+1}(τ_{j+1}), γ'_{j+1}(τ_{j+1})⟫` of the transverse acceleration of the moving vertex paired
  with the incoming minus outgoing velocity;
* minus the sum of the bulk longitudinal-acceleration integrals `∫_{τ_i}^{τ_{i+1}} ⟪A_i, D_t γ'_i⟫`.

When `F` is the exponential variation `(s, t) ↦ exp_(γ t) (s • V t)` of a curve `γ` along a
continuous piecewise `C³` tangent field `V`, every transverse curve is a geodesic, so all outer,
corner, and bulk transverse-acceleration terms vanish, while
`TauCeti.Manifold.sum_indexForm_adjacent_intervals` combines the piece index forms into the single
unrestricted `TauCeti.Manifold.indexForm I γ V V`. Along a smooth geodesic `γ` with cancelling outer
first-variation pairings, any continuous piecewise `C³` field `V` with `I(V, V) < 0` therefore
strictly decreases the energy of `exp_(γ ·) (s • V ·)` for small `s ≠ 0` — the broken-field
shortening principle of Morse index theory.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise`: **second variation of energy** for a
  continuous piecewise `C³` family, including all outer and interior corner transverse-acceleration
  terms.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints`: specialization to
  stationary outer endpoints.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn`: specialization to
  broken-geodesic central curves with stationary outer endpoints.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_exponentialVariation_piecewise`: second variation of
  energy along the exponential variation of a continuous piecewise `C³` field equals `I(V, V)`.
* `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_exponentialVariation_piecewise` and
  `TauCeti.Manifold.eventually_energy_exponentialVariation_lt_of_piecewise_indexForm_neg`:
  local-minimum nonnegativity and strict energy shortening for piecewise `C³` fields.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §13 and §15 (broken variations and the index theorem).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10, Theorem 10.4 and Theorem 10.18 (piecewise smooth vector fields and index form).
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
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    hasDerivAt_deriv_energy (I := I) (F := G i) (a := τ i.castSucc) (b := τ i.succ) (hGu i)
  -- Near `s = 0`, `E(F s)` is the sum of `E(G i s)` and each `s ↦ E(G i s)` is differentiable.
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  have heq := eventually_energy_eq_sum_of_piecewise τ hτ
    (fun i t ht ↦ (hG i t ht).of_le (by norm_num)) hFG
  have hdiff : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      DifferentiableAt ℝ (fun q ↦ energy I (G i q) (τ i.castSucc) (τ i.succ)) s :=
    Filter.eventually_all.mpr fun i ↦ eventually_differentiableAt_energy (u := 0)
      fun t ht ↦ (hGu i t ht).of_le (by norm_num)
  have hdeq : (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1)))) =ᶠ[𝓝 0]
      fun s ↦ ∑ i : Fin (n + 1), deriv (fun q ↦ energy I (G i q) (τ i.castSucc) (τ i.succ)) s := by
    filter_upwards [heq.deriv, hdiff] with s hs hds
    rw [hs, (HasDerivAt.fun_sum fun i _ ↦ (hds i).hasDerivAt).deriv]
  -- Telescope the piece boundary pairings into outer endpoints plus interior corner jumps.
  have hboundary : ∑ i : Fin (n + 1), (A i (τ i.succ) - A i (τ i.castSucc)) =
      A (Fin.last n) (τ (Fin.last (n + 1))) - A 0 (τ 0) +
        ∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc)) := by
    rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (fun i ↦ A i (τ i.succ)),
      Fin.sum_univ_succ (fun i ↦ A i (τ i.castSucc)), Finset.sum_sub_distrib]
    simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero]
    ring
  refine (hd.congr_of_eventuallyEq hdeq).congr_deriv ?_
  have hsplit : ∑ x : Fin (n + 1),
      (indexForm I (G x 0) (variationField I (G x)) (variationField I (G x))
          (τ x.castSucc) (τ x.succ) + A x (τ x.succ) - A x (τ x.castSucc) -
        ∫ t in τ x.castSucc..τ x.succ,
          inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G x s t) 0)
            (acceleration (leviCivitaConnection I M) (G x 0) t)) =
      (∑ x : Fin (n + 1), indexForm I (G x 0) (variationField I (G x))
          (variationField I (G x)) (τ x.castSucc) (τ x.succ)) +
        (∑ x : Fin (n + 1), (A x (τ x.succ) - A x (τ x.castSucc))) -
        ∑ x : Fin (n + 1), ∫ t in τ x.castSucc..τ x.succ,
          inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G x s t) 0)
            (acceleration (leviCivitaConnection I M) (G x 0) t) := by
    simp only [add_sub_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  dsimp only [A] at hboundary hsplit ⊢
  rw [hsplit, hboundary]
  ring

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
  have hleft : τ 0 ∈ Icc (τ (0 : Fin (n + 1)).castSucc) (τ (0 : Fin (n + 1)).succ) :=
    ⟨le_rfl, hτ (Fin.zero_le _)⟩
  have hright : τ (Fin.last (n + 1)) ∈
      Icc (τ (Fin.last n).castSucc) (τ (Fin.last n).succ) :=
    ⟨hτ (Fin.le_last _), le_rfl⟩
  have haG : (fun s ↦ G 0 s (τ 0)) =ᶠ[𝓝 0] fun _ ↦ G 0 0 (τ 0) := by
    filter_upwards [hFG, ha] with s hs hs0
    rw [← hs 0 hleft, hs0, hFG.self_of_nhds 0 hleft]
  have hbG : (fun s ↦ G (Fin.last n) s (τ (Fin.last (n + 1)))) =ᶠ[𝓝 0]
      fun _ ↦ G (Fin.last n) 0 (τ (Fin.last (n + 1))) := by
    filter_upwards [hFG, hb] with s hs hs0
    rw [← hs (Fin.last n) hright, hs0, hFG.self_of_nhds (Fin.last n) hright]
  have ha0 : acceleration (leviCivitaConnection I M) (fun s ↦ G 0 s (τ 0)) 0 = 0 :=
    (haG.acceleration_eq (leviCivitaConnection I M)).trans (acceleration_const _ _ 0)
  have hb0 : acceleration (leviCivitaConnection I M)
      (fun s ↦ G (Fin.last n) s (τ (Fin.last (n + 1)))) 0 = 0 :=
    (hbG.acceleration_eq (leviCivitaConnection I M)).trans (acceleration_const _ _ 0)
  refine (hasDerivAt_deriv_energy_piecewise τ hτ hG hFG).congr_deriv ?_
  dsimp only [A]
  rw [ha0, hb0, inner_zero_left, inner_zero_left]
  ring

/-- **Second variation of energy of a broken geodesic with fixed outer endpoints.** When each smooth
extension's central curve `G i 0` is a geodesic on the open subinterval `(τ_i, τ_{i+1})` and the
outer endpoints are stationary, only the sum of piece index forms and the interior corner
transverse-acceleration jumps remain. -/
theorem hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
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
  refine (hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints τ hτ hG hFG ha hb).congr_deriv ?_
  have hbulk : ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (acceleration (leviCivitaConnection I M) (G i 0) t) = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIoo_of_le (hτ (Fin.castSucc_le_succ i))] at ht
    rw [← accelerationWithin_of_mem_nhds _ (G i 0) (isOpen_Ioo.mem_nhds ht),
      (hγ i).accelerationWithin_eq_zero t ht, inner_zero_right]
  rw [hbulk, sub_zero]

/-! ### Exponential variations along continuous piecewise smooth fields -/

section PiecewiseExponential

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- **First variation of energy along a piecewise `C²` exponential variation of a smooth curve.**
Let `V` be a continuous piecewise `C²` field along `γ` on a monotone partition `τ`, witnessed by
fields `W i` with `C²` lifts on `[τ_i, τ_{i+1}]` agreeing with `V` on each closed piece. Because
the central curve `γ` has no corners, all interior vertex jumps cancel automatically and
`d/ds E(exp_(γ ·) (s • V ·)) |₀ =
  ⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∑_i ∫_{τ_i}^{τ_{i+1}} ⟪W_i, D_t γ'⟫`. -/
theorem hasDerivAt_energy_exponentialVariation_piecewise {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {W : Fin (n + 1) → ∀ t, TangentSpace I (γ t)}
    (hW : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (W i r)) t)
    (hVW : ∀ i : Fin (n + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ), V t = W i t) :
    HasDerivAt (fun s ↦ energy I (exponentialVariation I γ V s) (τ 0) (τ (Fin.last (n + 1))))
      (inner ℝ (V (τ (Fin.last (n + 1)))) (curveVelocity I γ (τ (Fin.last (n + 1)))) -
        inner ℝ (V (τ 0)) (curveVelocity I γ (τ 0)) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (W i t) (acceleration (leviCivitaConnection I M) γ t)) 0 := by
  have hWu (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ uIcc (τ i.castSucc) (τ i.succ)) :
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (W i r)) t :=
    hW i t (by simpa only [uIcc_of_le (hτ (Fin.castSucc_le_succ i))] using ht)
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    hasDerivAt_energy_exponentialVariation (I := I) (γ := γ) (V := W i)
      (a := τ i.castSucc) (b := τ i.succ) (hWu i)
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  have heq := eventually_energy_eq_sum_of_piecewise τ hτ
    (F := exponentialVariation I γ V) (G := fun i ↦ exponentialVariation I γ (W i))
    (fun i t ht ↦ (contMDiffAt_exponentialVariation_zero γ (W i) (hW i t ht)).of_le (by norm_num))
    (Eventually.of_forall fun s i t ht ↦ by simp only [exponentialVariation_apply, hVW i t ht])
  -- Each endpoint of piece `i` evaluates `W i` to `V`, so the boundary sum telescopes cleanly.
  have hleft (i : Fin (n + 1)) : W i (τ i.castSucc) = V (τ i.castSucc) :=
    (hVW i _ ⟨le_rfl, hτ (Fin.castSucc_le_succ i)⟩).symm
  have hright (i : Fin (n + 1)) : W i (τ i.succ) = V (τ i.succ) :=
    (hVW i _ ⟨hτ (Fin.castSucc_le_succ i), le_rfl⟩).symm
  let B : ℝ → ℝ := fun t ↦ inner ℝ (V t) (curveVelocity I γ t)
  have htele : ∑ i : Fin (n + 1), (B (τ i.succ) - B (τ i.castSucc)) =
      B (τ (Fin.last (n + 1))) - B (τ 0) := by
    rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (fun i ↦ B (τ i.succ)),
      Fin.sum_univ_succ (fun i ↦ B (τ i.castSucc))]
    simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero]
    ring
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  have hsum : ∑ i : Fin (n + 1),
      (inner ℝ (W i (τ i.succ)) (curveVelocity I γ (τ i.succ)) -
        inner ℝ (W i (τ i.castSucc)) (curveVelocity I γ (τ i.castSucc)) -
        ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (W i t) (acceleration (leviCivitaConnection I M) γ t)) =
      (∑ i : Fin (n + 1), (B (τ i.succ) - B (τ i.castSucc))) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (W i t) (acceleration (leviCivitaConnection I M) γ t) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hright i, hleft i]
  rw [hsum, htele]

/-- **Second variation of energy along a piecewise `C³` exponential variation.** Let `V` be a
continuous piecewise `C³` tangent field along `γ` on a monotone partition `τ`, witnessed by fields
`W i` with `C³` lifts on `[τ_i, τ_{i+1}]` agreeing with `V` on `[τ_i, τ_{i+1}]`. Then
`d²/ds² E(exp_(γ ·) (s • V ·)) |₀ = I(V, V)`, where `I(V, V)` is the single unrestricted
`TauCeti.Manifold.indexForm` over `[τ₀, τ_{n+1}]`. -/
theorem hasDerivAt_deriv_energy_exponentialVariation_piecewise {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {W : Fin (n + 1) → ∀ t, TangentSpace I (γ t)}
    (hW : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (W i r)) t)
    (hVW : ∀ i : Fin (n + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ), V t = W i t) :
    HasDerivAt
      (deriv fun s ↦ energy I (exponentialVariation I γ V s) (τ 0) (τ (Fin.last (n + 1))))
      (indexForm I γ V V (τ 0) (τ (Fin.last (n + 1)))) 0 := by
  let G : Fin (n + 1) → ℝ → ℝ → M := fun i ↦ exponentialVariation I γ (W i)
  have hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t) :=
    fun i t ht ↦ contMDiffAt_exponentialVariation_zero γ (W i) (hW i t ht)
  have hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (exponentialVariation I γ V s) (G i s) (Icc (τ i.castSucc) (τ i.succ)) :=
    Eventually.of_forall fun s i t ht ↦ by simp [G, hVW i t ht]
  refine (hasDerivAt_deriv_energy_piecewise τ hτ hG hFG).congr_deriv ?_
  -- Every transverse curve of `G i` is a geodesic, so all transverse-acceleration terms vanish.
  simp only [G, acceleration_exponentialVariation_zero, inner_zero_left, sub_self,
    Finset.sum_const_zero, intervalIntegral.integral_zero, add_zero, sub_zero]
  -- On each piece, `G i 0 = γ` and `variationField I (G i) = W i` agrees with `V` on the interior.
  have hpiece (i : Fin (n + 1)) :
      indexForm I (exponentialVariation I γ (W i) 0)
          (variationField I (exponentialVariation I γ (W i)))
          (variationField I (exponentialVariation I γ (W i))) (τ i.castSucc) (τ i.succ) =
        indexForm I γ V V (τ i.castSucc) (τ i.succ) := by
    refine indexForm_congr (fun t _ ↦ congrFun (exponentialVariation_zero γ (W i)) t)
      (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · rw [uIoo_of_le (hτ (Fin.castSucc_le_succ i))] at ht
      exact (heq_of_eq (variationField_exponentialVariation γ (W i) t)).trans
        (heq_of_eq (hVW i t (Ioo_subset_Icc_self ht)).symm)
    · rw [uIoo_of_le (hτ (Fin.castSucc_le_succ i))] at ht
      exact (heq_of_eq (variationField_exponentialVariation γ (W i) t)).trans
        (heq_of_eq (hVW i t (Ioo_subset_Icc_self ht)).symm)
  -- Each piece integrand agrees on the open subinterval with the smooth `W i` integrand, hence is
  -- integrable, so `sum_indexForm_adjacent_intervals` reassembles the full index form.
  have hint (i : Fin (n + 1)) :
      IntervalIntegrable (indexFormIntegrand I γ V V) volume (τ i.castSucc) (τ i.succ) := by
    have hWi : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
        (fun r ↦ TotalSpace.mk' E (γ r) (W i r)) (uIcc (τ i.castSucc) (τ i.succ)) := by
      intro t ht
      rw [uIcc_of_le (hτ (Fin.castSucc_le_succ i))] at ht
      exact ((hW i t ht).of_le (by norm_num)).contMDiffWithinAt
    refine (intervalIntegrable_indexFormIntegrand hWi hWi).congr_uIoo fun t ht ↦ ?_
    rw [uIoo_of_le (hτ (Fin.castSucc_le_succ i))] at ht
    have hnear : ∀ᶠ r in 𝓝 t, HEq (W i r) (V r) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
      exact heq_of_eq (hVW i r (Ioo_subset_Icc_self hr)).symm
    exact indexFormIntegrand_congr Filter.EventuallyEq.rfl hnear hnear
  rw [Finset.sum_congr rfl fun i _ ↦ hpiece i, sum_indexForm_adjacent_intervals τ hint]

/-- **Nonnegativity of the index form on piecewise `C³` fields at a local minimum of the energy.**
If `s ↦ E(exp_(γ ·) (s • V ·))` has a local minimum at `s = 0` for a continuous piecewise `C³`
field `V` along `γ`, then `0 ≤ I(V, V)`. -/
theorem indexForm_nonneg_of_isLocalMin_energy_exponentialVariation_piecewise {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : Monotone τ) {W : Fin (n + 1) → ∀ t, TangentSpace I (γ t)}
    (hW : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (W i r)) t)
    (hVW : ∀ i : Fin (n + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ), V t = W i t)
    (hmin : IsLocalMin
      (fun s ↦ energy I (exponentialVariation I γ V s) (τ 0) (τ (Fin.last (n + 1)))) 0) :
    0 ≤ indexForm I γ V V (τ 0) (τ (Fin.last (n + 1))) := by
  have hcont : ContinuousAt
      (fun s ↦ energy I (exponentialVariation I γ V s) (τ 0) (τ (Fin.last (n + 1)))) 0 :=
    (hasDerivAt_energy_exponentialVariation_piecewise τ hτ
      (fun i t ht ↦ (hW i t ht).of_le (by norm_num)) hVW).continuousAt
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rwa [(hasDerivAt_deriv_energy_exponentialVariation_piecewise τ hτ hW hVW).deriv] at hnn

/-- **Broken-field energy shortening along a geodesic.** Let `γ` be a geodesic on
`Ioo (τ 0) (τ (Fin.last (n + 1)))` and `V` a continuous piecewise `C³` field along `γ` on a
monotone partition `τ` whose outer endpoint pairings satisfy
`⟪V(τ_{n+1}), γ'(τ_{n+1})⟫ = ⟪V(τ₀), γ'(τ₀)⟫` (for instance `V(τ₀) = 0` and `V(τ_{n+1}) = 0`).
If `I(V, V) < 0`, then `E(exp_(γ ·) (s • V ·)) < E(γ)` for all sufficiently small `s ≠ 0`. -/
theorem eventually_energy_exponentialVariation_lt_of_piecewise_indexForm_neg {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : Monotone τ)
    (hγ : IsGeodesicCurveOn I γ (Ioo (τ 0) (τ (Fin.last (n + 1)))))
    {W : Fin (n + 1) → ∀ t, TangentSpace I (γ t)}
    (hW : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (W i r)) t)
    (hVW : ∀ i : Fin (n + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ), V t = W i t)
    (hbdry : inner ℝ (V (τ (Fin.last (n + 1)))) (curveVelocity I γ (τ (Fin.last (n + 1)))) =
      inner ℝ (V (τ 0)) (curveVelocity I γ (τ 0)))
    (hneg : indexForm I γ V V (τ 0) (τ (Fin.last (n + 1))) < 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      energy I (exponentialVariation I γ V s) (τ 0) (τ (Fin.last (n + 1))) <
        energy I γ (τ 0) (τ (Fin.last (n + 1))) := by
  have hd₁ := hasDerivAt_energy_exponentialVariation_piecewise τ hτ
    (fun i t ht ↦ (hW i t ht).of_le (by norm_num)) hVW
  have hbulk : ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
      inner ℝ (W i t) (acceleration (leviCivitaConnection I M) γ t) = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIoo_of_le (hτ (Fin.castSucc_le_succ i))] at ht
    have ht' : t ∈ Ioo (τ 0) (τ (Fin.last (n + 1))) :=
      ⟨lt_of_le_of_lt (hτ (Fin.zero_le _)) ht.1, lt_of_lt_of_le ht.2 (hτ (Fin.le_last _))⟩
    rw [← accelerationWithin_of_mem_nhds _ γ (isOpen_Ioo.mem_nhds ht'),
      hγ.accelerationWithin_eq_zero t ht', inner_zero_right]
  have hd₁_zero :
      deriv (fun s ↦ energy I (exponentialVariation I γ V s) (τ 0) (τ (Fin.last (n + 1)))) 0 =
        0 := by
    rw [hd₁.deriv, hbulk, hbdry, sub_self, sub_zero]
  have hd₂ := hasDerivAt_deriv_energy_exponentialVariation_piecewise τ hτ hW hVW
  simpa only [exponentialVariation_zero] using
    TauCeti.eventually_gt_of_deriv_deriv_neg (hd₂.deriv.symm ▸ hneg) hd₁_zero hd₁.continuousAt

end PiecewiseExponential

end TauCeti.Manifold

end
