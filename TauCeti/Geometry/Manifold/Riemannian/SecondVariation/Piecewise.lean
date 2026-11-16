/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Piecewise
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic

/-!
# Second variation of energy for curves with corners

A continuous piecewise smooth variation is represented, as in
`TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Piecewise`, by an assembled family `F` and
finitely many smooth extensions `G i` on the closed intervals of a nondecreasing partition `τ`,
matching `F` on each closed piece for variation parameters near `0`.

Near `s = 0` the first derivative of the energy of `F s` is the sum of the first derivatives of the
piece energies (`TauCeti.Manifold.eventually_deriv_energy_eq_sum_of_piecewise`), and the global
index form `indexForm I (F 0) (variationField I F) (variationField I F) (τ 0) (τ (Fin.last n))` is
the sum of the piece index forms (`TauCeti.Manifold.indexForm_eq_sum_of_piecewise`). Differentiating
a second time gives the piecewise second variation of energy
(`TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise`): the global index form, the outer endpoint
transverse-acceleration pairings, the pairings of the transverse vertex acceleration with the
interior corner velocity jump (incoming minus outgoing piece velocity), minus the piece
geodesic-acceleration integrals.

When the partition is strictly increasing and the central curve `F 0` is a smooth geodesic on the
open interval `(τ 0, τ (Fin.last (n + 1)))`, `F 0` is differentiable at every interior vertex, so
the incoming and outgoing velocities at each interior vertex agree and all interior corner
velocity-jump pairings cancel alongside the bulk geodesic-acceleration integrals
(`TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn`). Under fixed outer
endpoints (or periodic boundary conditions on a closed geodesic), the Hessian of energy along a
piecewise smooth variation of a geodesic reduces to the single global index form, which is therefore
nonnegative at any local minimum of energy
(`TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_piecewise_of_fixed_endpoints` and
`TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_piecewise_of_periodic`).

## Main results

* `TauCeti.Manifold.intervalIntegrable_indexFormIntegrand_of_piecewise` and
  `TauCeti.Manifold.indexForm_eq_sum_of_piecewise`: integrability and partition additivity of the
  index form of a piecewise smooth variation.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise` and
  `TauCeti.Manifold.deriv_deriv_energy_piecewise`: the second variation of energy including outer
  endpoint, interior corner velocity-jump, and bulk acceleration terms.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints` and
  `TauCeti.Manifold.deriv_deriv_energy_piecewise_of_fixed_endpoints`: elimination of outer endpoint
  acceleration terms for stationary outer endpoints.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn`,
  `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints_of_isGeodesicCurveOn`,
  `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_piecewise_of_fixed_endpoints`,
  `TauCeti.Manifold.hasDerivAt_deriv_energy_piecewise_of_periodic`, and
  `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_piecewise_of_periodic`: cancellation of
  interior corner and bulk acceleration terms for piecewise smooth variations of a smooth geodesic.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§12–13.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2 (piecewise smooth variations
  of energy) and Ch. 10, §2 (index form on piecewise smooth fields).
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- On each piece `[τ i.castSucc, τ i.succ]` of a piecewise `C²` variation,
`indexFormIntegrand I (F 0) (variationField I F) (variationField I F)` is interval integrable. -/
theorem intervalIntegrable_indexFormIntegrand_of_piecewise {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin n → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin n,
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ))) (i : Fin n) :
    IntervalIntegrable (indexFormIntegrand I (F 0) (variationField I F) (variationField I F))
      volume (τ i.castSucc) (τ i.succ) := by
  have hi := hτ (Fin.castSucc_le_succ i)
  have hsub : uIoo (τ i.castSucc) (τ i.succ) ⊆ Icc (τ i.castSucc) (τ i.succ) :=
    uIoo_of_le hi ▸ Ioo_subset_Icc_self
  have hVl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (G i 0 r) (variationField I (G i) r))
      (uIcc (τ i.castSucc) (τ i.succ)) := fun t ht ↦
    ((hG i t (uIcc_of_le hi ▸ ht)).contMDiffAt_variationField (m := 1)
      (by norm_num)).contMDiffWithinAt
  have hVheq : ∀ t ∈ uIoo (τ i.castSucc) (τ i.succ),
      HEq (variationField I F t) (variationField I (G i) t) := fun t ht ↦
    heq_variationField_of_eventuallyEq (hFG.mono fun s hs ↦ hs i (hsub ht))
  exact intervalIntegrable_indexFormIntegrand_of_eqOn_uIoo ((hFG.self_of_nhds i).mono hsub)
    hVheq hVheq hVl hVl

/-- **Partition additivity of the index form for a piecewise `C²` variation.** The global index form
of `variationField I F` on `[τ 0, τ (Fin.last n)]` equals the sum of the index forms of the smooth
piece extensions `G i`. -/
theorem indexForm_eq_sum_of_piecewise {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin n → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin n,
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ))) :
    indexForm I (F 0) (variationField I F) (variationField I F) (τ 0) (τ (Fin.last n)) =
      ∑ i : Fin n, indexForm I (G i 0) (variationField I (G i)) (variationField I (G i))
        (τ i.castSucc) (τ i.succ) := by
  have hsub (i : Fin n) : uIoo (τ i.castSucc) (τ i.succ) ⊆ Icc (τ i.castSucc) (τ i.succ) :=
    uIoo_of_le (hτ (Fin.castSucc_le_succ i)) ▸ Ioo_subset_Icc_self
  have hVl (i : Fin n) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (G i 0 r) (variationField I (G i) r))
      (uIcc (τ i.castSucc) (τ i.succ)) := fun t ht ↦
    ((hG i t (uIcc_of_le (hτ (Fin.castSucc_le_succ i)) ▸ ht)).contMDiffAt_variationField
      (m := 1) (by norm_num)).contMDiffWithinAt
  have hVheq (i : Fin n) (t : ℝ) (ht : t ∈ uIoo (τ i.castSucc) (τ i.succ)) :
      HEq (variationField I F t) (variationField I (G i) t) :=
    heq_variationField_of_eventuallyEq (hFG.mono fun s hs ↦ hs i (hsub i ht))
  exact indexForm_eq_sum_of_eqOn_uIoo τ (fun i ↦ (hFG.self_of_nhds i).mono (hsub i))
    hVheq hVheq hVl hVl

/-- **The second variation of energy for a continuous piecewise smooth variation**, including outer
endpoint, interior corner, and bulk acceleration terms. At each interior vertex `τ_{j+1}`, the
corner term is the pairing of the transverse vertex acceleration with the incoming piece velocity
minus its pairing with the outgoing piece velocity. -/
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
      (indexForm I (F 0) (variationField I F) (variationField I F) (τ 0) (τ (Fin.last (n + 1))) +
        (A (Fin.last n) (τ (Fin.last (n + 1))) - A 0 (τ 0)) +
        ∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc)) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
            (acceleration (leviCivitaConnection I M) (G i 0) t)) 0 := by
  intro A
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    hasDerivAt_deriv_energy (I := I) (F := G i) (a := τ i.castSucc) (b := τ i.succ) fun t ht ↦
      hG i t (by simpa only [uIcc_of_le (hτ (Fin.castSucc_le_succ i))] using ht)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have heq := eventually_deriv_energy_eq_sum_of_piecewise τ hτ
    (fun i t ht ↦ (hG i t ht).of_le (by norm_num)) hFG
  have hI := indexForm_eq_sum_of_piecewise τ hτ (fun i t ht ↦ (hG i t ht).of_le (by norm_num)) hFG
  have hboundary := Fin.sum_univ_sub_eq_add_sum_castSucc_sub_succ
    (fun i ↦ A i (τ i.castSucc)) (fun i ↦ A i (τ i.succ))
  simp only [Fin.succ_last, Fin.castSucc_zero, Fin.succ_castSucc] at hboundary
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [hI, add_assoc (∑ i : Fin (n + 1), _), ← hboundary]
  simp only [A, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **The second variation of energy for a piecewise smooth variation**, written as an iterated
`deriv`. -/
theorem deriv_deriv_energy_piecewise {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ))) :
    let A := fun (i : Fin (n + 1)) t ↦
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (curveVelocity I (G i 0) t)
    deriv (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1)))) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F) (τ 0) (τ (Fin.last (n + 1))) +
        (A (Fin.last n) (τ (Fin.last (n + 1))) - A 0 (τ 0)) +
        ∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc)) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
            (acceleration (leviCivitaConnection I M) (G i 0) t) :=
  (hasDerivAt_deriv_energy_piecewise τ hτ hG hFG).deriv

omit [T2Space M] in
/-- For a piecewise family with stationary outer endpoints near `s = 0`, the transverse
accelerations of the first and last piece extensions at the outer endpoints vanish. -/
private theorem acceleration_piecewise_outer_eq_zero {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (ha : ∀ᶠ s in 𝓝 0, F s (τ 0) = F 0 (τ 0))
    (hb : ∀ᶠ s in 𝓝 0, F s (τ (Fin.last (n + 1))) = F 0 (τ (Fin.last (n + 1)))) :
    acceleration (leviCivitaConnection I M) (fun s ↦ G 0 s (τ 0)) 0 = 0 ∧
      acceleration (leviCivitaConnection I M)
        (fun s ↦ G (Fin.last n) s (τ (Fin.last (n + 1)))) 0 = 0 :=
  ⟨(((eventuallyEq_piecewise_left τ hτ hFG).trans ha).acceleration_eq _).trans
      (acceleration_const _ _ 0),
    (((eventuallyEq_piecewise_right τ hτ hFG).trans hb).acceleration_eq _).trans
      (acceleration_const _ _ 0)⟩

/-- For stationary outer endpoints, the outer endpoint acceleration pairings vanish in the
piecewise second variation of energy; interior corner terms remain if the central curve has
velocity jumps at interior vertices. -/
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
      (indexForm I (F 0) (variationField I F) (variationField I F) (τ 0) (τ (Fin.last (n + 1))) +
        ∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc)) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
            (acceleration (leviCivitaConnection I M) (G i 0) t)) 0 := by
  obtain ⟨ha0, hb0⟩ := acceleration_piecewise_outer_eq_zero (I := I) τ hτ hFG ha hb
  simpa only [ha0, hb0, inner_zero_left, sub_zero, add_zero] using
    hasDerivAt_deriv_energy_piecewise τ hτ hG hFG

/-- Iterated-`deriv` form of `hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints`. -/
theorem deriv_deriv_energy_piecewise_of_fixed_endpoints {n : ℕ} (τ : Fin (n + 2) → ℝ)
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
    deriv (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1)))) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F) (τ 0) (τ (Fin.last (n + 1))) +
        ∑ j : Fin n, (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc)) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
            (acceleration (leviCivitaConnection I M) (G i 0) t) :=
  (hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints τ hτ hG hFG ha hb).deriv

/-! ### Piecewise smooth variations of a smooth geodesic -/

omit [T2Space M] in
/-- When `τ` is strictly increasing and the central curve `F 0` is differentiable on the open
interval `(τ 0, τ (Fin.last (n + 1)))`, the incoming and outgoing velocities of `G j.castSucc 0`
and `G j.succ 0` at every interior vertex agree with `curveVelocity I (F 0)`, so every interior
corner velocity-jump term vanishes. -/
private theorem corner_acceleration_sub_eq_zero_of_isGeodesicCurveOn {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : StrictMono τ) {F : ℝ → ℝ → M}
    {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1))))) (j : Fin n) :
    inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G j.castSucc s (τ j.succ.castSucc)) 0)
        (curveVelocity I (G j.castSucc 0) (τ j.succ.castSucc)) -
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G j.succ s (τ j.succ.castSucc)) 0)
        (curveVelocity I (G j.succ 0) (τ j.succ.castSucc)) = 0 := by
  set c := τ j.succ.castSucc
  have hc_Ioo : c ∈ Ioo (τ 0) (τ (Fin.last (n + 1))) :=
    ⟨hτ (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos j)),
      hτ (Fin.castSucc_lt_succ.trans_le (Fin.le_last _))⟩
  have hL_mem : c ∈ Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ) := by
    rw [Fin.succ_castSucc]
    exact ⟨(hτ Fin.castSucc_lt_succ).le, le_rfl⟩
  have hR_mem : c ∈ Icc (τ j.succ.castSucc) (τ j.succ.succ) :=
    ⟨le_rfl, (hτ Fin.castSucc_lt_succ).le⟩
  have hF_diff : MDifferentiableAt 𝓘(ℝ, ℝ) I (F 0) c :=
    (hgeo.mdifferentiableOn c hc_Ioo).mdifferentiableAt (isOpen_Ioo.mem_nhds hc_Ioo)
  have hG_diff (i : Fin (n + 1)) (hc : c ∈ Icc (τ i.castSucc) (τ i.succ)) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I (G i 0) c :=
    ((hG i c hc).comp c (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt).mdifferentiableAt
      (by norm_num)
  have hvelL := curveVelocityLift_eq_of_eqOn_Icc (hτ Fin.castSucc_lt_succ) hL_mem
    (hFG.self_of_nhds j.castSucc) hF_diff (hG_diff j.castSucc hL_mem)
  have hvelR := curveVelocityLift_eq_of_eqOn_Icc (hτ Fin.castSucc_lt_succ) hR_mem
    (hFG.self_of_nhds j.succ) hF_diff (hG_diff j.succ hR_mem)
  have hjoin : (fun s ↦ G j.castSucc s c) =ᶠ[𝓝 0] fun s ↦ G j.succ s c :=
    hFG.mono fun s hs ↦ (hs j.castSucc hL_mem).symm.trans (hs j.succ hR_mem)
  have hacc := hjoin.totalSpaceMk_acceleration_eq (leviCivitaConnection I M)
  have hvel : TotalSpace.mk' E (G j.castSucc 0 c) (curveVelocity I (G j.castSucc 0) c) =
      TotalSpace.mk' E (G j.succ 0 c) (curveVelocity I (G j.succ 0) c) := by
    simpa only [curveVelocityLift_apply] using hvelL.symm.trans hvelR
  rw [sub_eq_zero]
  exact TauCeti.inner_eq_of_totalSpaceMk_eq (𝕜 := ℝ) hacc hvel

/-- **The second variation of energy for a piecewise smooth variation of a smooth geodesic.** When
`τ` is strictly increasing and `F 0` is a geodesic on `(τ 0, τ (Fin.last (n + 1)))`, all interior
corner terms and bulk geodesic-acceleration integrals vanish, leaving only the global index form and
the outer endpoint acceleration pairings. -/
theorem hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : StrictMono τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1))))) :
    let A := fun (i : Fin (n + 1)) t ↦
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (curveVelocity I (G i 0) t)
    HasDerivAt (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      (indexForm I (F 0) (variationField I F) (variationField I F) (τ 0) (τ (Fin.last (n + 1))) +
        A (Fin.last n) (τ (Fin.last (n + 1))) - A 0 (τ 0)) 0 := by
  intro A
  have hcorner : ∑ j : Fin n,
      (A j.castSucc (τ j.succ.castSucc) - A j.succ (τ j.succ.castSucc)) = 0 :=
    Finset.sum_eq_zero fun j _ ↦
      corner_acceleration_sub_eq_zero_of_isGeodesicCurveOn τ hτ hG hFG hgeo j
  have hzero {x y : M} {u v : TangentSpace I x}
      (h : TotalSpace.mk' E x v = TotalSpace.mk' E y 0) : inner ℝ u v = 0 := by
    obtain ⟨rfl, hv⟩ := TotalSpace.ext_iff.mp h
    have hv' : v = 0 := eq_of_heq hv
    rw [hv', inner_zero_right]
  have hbulk : ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (acceleration (leviCivitaConnection I M) (G i 0) t) = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIoo_of_le (hτ.monotone (Fin.castSucc_le_succ i))] at ht
    have ht_Ioo : t ∈ Ioo (τ 0) (τ (Fin.last (n + 1))) :=
      ⟨(hτ.monotone (Fin.zero_le _)).trans_lt ht.1, ht.2.trans_le (hτ.monotone (Fin.le_last _))⟩
    have hEq : G i 0 =ᶠ[𝓝 t] F 0 :=
      eventually_of_mem (isOpen_Ioo.mem_nhds ht)
        ((hFG.self_of_nhds i).symm.mono Ioo_subset_Icc_self)
    have hnhds : Ioo (τ 0) (τ (Fin.last (n + 1))) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht_Ioo
    have h0 : acceleration (leviCivitaConnection I M) (F 0) t = 0 := by
      rw [← accelerationWithin_of_mem_nhds _ _ hnhds, hgeo.accelerationWithin_eq_zero t ht_Ioo]
    exact hzero ((hEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M)).trans (by rw [h0]))
  refine (hasDerivAt_deriv_energy_piecewise τ hτ.monotone hG hFG).congr_deriv ?_
  dsimp only [A] at hcorner ⊢
  rw [hcorner, hbulk]
  ring

/-- Iterated-`deriv` form of `hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn`. -/
theorem deriv_deriv_energy_piecewise_of_isGeodesicCurveOn {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : StrictMono τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1))))) :
    let A := fun (i : Fin (n + 1)) t ↦
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ G i s t) 0)
        (curveVelocity I (G i 0) t)
    deriv (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1)))) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F) (τ 0) (τ (Fin.last (n + 1))) +
        A (Fin.last n) (τ (Fin.last (n + 1))) - A 0 (τ 0) :=
  (hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn τ hτ hG hFG hgeo).deriv

/-- **Fixed-endpoint second variation of energy for a piecewise smooth variation of a geodesic.**
When `F 0` is a smooth geodesic on `(τ 0, τ (Fin.last (n + 1)))` and the outer endpoints are
stationary, the Hessian of energy at `s = 0` is the single global index form `I(V, V)`. -/
theorem hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints_of_isGeodesicCurveOn {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : StrictMono τ) {F : ℝ → ℝ → M}
    {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1)))))
    (ha : ∀ᶠ s in 𝓝 0, F s (τ 0) = F 0 (τ 0))
    (hb : ∀ᶠ s in 𝓝 0, F s (τ (Fin.last (n + 1))) = F 0 (τ (Fin.last (n + 1)))) :
    HasDerivAt (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      (indexForm I (F 0) (variationField I F) (variationField I F)
        (τ 0) (τ (Fin.last (n + 1)))) 0 := by
  obtain ⟨ha0, hb0⟩ := acceleration_piecewise_outer_eq_zero (I := I) τ hτ.monotone hFG ha hb
  simpa only [ha0, hb0, inner_zero_left, add_zero, sub_zero] using
    hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn τ hτ hG hFG hgeo

/-- Iterated-`deriv` form of
`hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints_of_isGeodesicCurveOn`. -/
theorem deriv_deriv_energy_piecewise_of_fixed_endpoints_of_isGeodesicCurveOn {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : StrictMono τ) {F : ℝ → ℝ → M}
    {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1)))))
    (ha : ∀ᶠ s in 𝓝 0, F s (τ 0) = F 0 (τ 0))
    (hb : ∀ᶠ s in 𝓝 0, F s (τ (Fin.last (n + 1))) = F 0 (τ (Fin.last (n + 1)))) :
    deriv (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1)))) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F)
        (τ 0) (τ (Fin.last (n + 1))) :=
  (hasDerivAt_deriv_energy_piecewise_of_fixed_endpoints_of_isGeodesicCurveOn
    τ hτ hG hFG hgeo ha hb).deriv

/-- **Nonnegativity of the index form for a fixed-endpoint piecewise smooth variation at a local
minimum of energy.** If a smooth geodesic `F 0` on `(τ 0, τ (Fin.last (n + 1)))` locally minimizes
energy along a fixed-endpoint piecewise `C³` variation `F`, then the global index form is
nonnegative. -/
theorem indexForm_nonneg_of_isLocalMin_energy_piecewise_of_fixed_endpoints {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : StrictMono τ) {F : ℝ → ℝ → M}
    {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1)))))
    (ha : ∀ᶠ s in 𝓝 0, F s (τ 0) = F 0 (τ 0))
    (hb : ∀ᶠ s in 𝓝 0, F s (τ (Fin.last (n + 1))) = F 0 (τ (Fin.last (n + 1))))
    (hmin : IsLocalMin (fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1)))) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F)
      (τ 0) (τ (Fin.last (n + 1))) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  rw [← deriv_deriv_energy_piecewise_of_fixed_endpoints_of_isGeodesicCurveOn
    τ hτ hG hFG hgeo ha hb]
  exact TauCeti.deriv_deriv_nonneg_of_isLocalMin
    (hasDerivAt_energy_piecewise τ hτ.monotone (fun i t ht ↦ (hG i t ht).of_le (by norm_num))
      hFG).continuousAt hmin

/-- **Periodic piecewise smooth second variation of energy on a closed geodesic.** When `F s`
closes up at the outer endpoints near `s = 0` and the initial velocity of the first piece agrees in
the tangent bundle with the terminal velocity of the last piece, the outer endpoint acceleration
pairings cancel and the Hessian of energy is the global index form `I(V, V)`. -/
theorem hasDerivAt_deriv_energy_piecewise_of_periodic {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : StrictMono τ) {F : ℝ → ℝ → M}
    {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1)))))
    (hper : ∀ᶠ s in 𝓝 0, F s (τ 0) = F s (τ (Fin.last (n + 1))))
    (hvel : curveVelocityLift I (G 0 0) (τ 0) =
      curveVelocityLift I (G (Fin.last n) 0) (τ (Fin.last (n + 1)))) :
    HasDerivAt (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      (indexForm I (F 0) (variationField I F) (variationField I F)
        (τ 0) (τ (Fin.last (n + 1)))) 0 := by
  have hperG : (fun s ↦ G 0 s (τ 0)) =ᶠ[𝓝 0]
      fun s ↦ G (Fin.last n) s (τ (Fin.last (n + 1))) :=
    ((eventuallyEq_piecewise_left τ hτ.monotone hFG).trans hper).trans
      (eventuallyEq_piecewise_right τ hτ.monotone hFG).symm
  have hacc := hperG.totalSpaceMk_acceleration_eq (leviCivitaConnection I M)
  have hvel' : TotalSpace.mk' E (G 0 0 (τ 0)) (curveVelocity I (G 0 0) (τ 0)) =
      TotalSpace.mk' E (G (Fin.last n) 0 (τ (Fin.last (n + 1))))
        (curveVelocity I (G (Fin.last n) 0) (τ (Fin.last (n + 1)))) := by
    simpa only [curveVelocityLift_apply] using hvel
  have hinner := TauCeti.inner_eq_of_totalSpaceMk_eq (𝕜 := ℝ) hacc hvel'
  refine (hasDerivAt_deriv_energy_piecewise_of_isGeodesicCurveOn τ hτ hG hFG hgeo).congr_deriv ?_
  dsimp only
  rw [hinner, add_sub_cancel_right]

/-- Iterated-`deriv` form of `hasDerivAt_deriv_energy_piecewise_of_periodic`. -/
theorem deriv_deriv_energy_piecewise_of_periodic {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : StrictMono τ) {F : ℝ → ℝ → M}
    {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1)))))
    (hper : ∀ᶠ s in 𝓝 0, F s (τ 0) = F s (τ (Fin.last (n + 1))))
    (hvel : curveVelocityLift I (G 0 0) (τ 0) =
      curveVelocityLift I (G (Fin.last n) 0) (τ (Fin.last (n + 1)))) :
    deriv (deriv fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1)))) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F)
        (τ 0) (τ (Fin.last (n + 1))) :=
  (hasDerivAt_deriv_energy_piecewise_of_periodic τ hτ hG hFG hgeo hper hvel).deriv

/-- **Nonnegativity of the index form for a periodic piecewise smooth variation at a local minimum
of energy.** If a smooth geodesic `F 0` on `(τ 0, τ (Fin.last (n + 1)))` with matching endpoint
velocities locally minimizes energy along a periodic piecewise `C³` variation `F`, then the global
index form is nonnegative. -/
theorem indexForm_nonneg_of_isLocalMin_energy_piecewise_of_periodic {n : ℕ}
    (τ : Fin (n + 2) → ℝ) (hτ : StrictMono τ) {F : ℝ → ℝ → M}
    {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo (τ 0) (τ (Fin.last (n + 1)))))
    (hper : ∀ᶠ s in 𝓝 0, F s (τ 0) = F s (τ (Fin.last (n + 1))))
    (hvel : curveVelocityLift I (G 0 0) (τ 0) =
      curveVelocityLift I (G (Fin.last n) 0) (τ (Fin.last (n + 1))))
    (hmin : IsLocalMin (fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1)))) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F)
      (τ 0) (τ (Fin.last (n + 1))) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  rw [← deriv_deriv_energy_piecewise_of_periodic τ hτ hG hFG hgeo hper hvel]
  exact TauCeti.deriv_deriv_nonneg_of_isLocalMin
    (hasDerivAt_energy_piecewise τ hτ.monotone (fun i t ht ↦ (hG i t ht).of_le (by norm_num))
      hFG).continuousAt hmin

end TauCeti.Manifold

end
