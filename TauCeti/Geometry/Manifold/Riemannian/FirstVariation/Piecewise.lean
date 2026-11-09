/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic

/-!
# First variation of energy for curves with corners

A continuous piecewise smooth variation is represented by a family `F` and finitely many smooth
extensions `G i`, one on each closed interval of a nondecreasing partition. The extensions agree
with `F` on their respective pieces for all variation parameters near zero. Consequently adjacent
extensions agree at every moving vertex, while their longitudinal velocities may differ.

The energy is the existing `TauCeti.Manifold.energy` of the assembled curve. It is locally the
sum of the piece energies, even though the unrestricted velocity at a corner may take a junk
value. Summing the smooth first-variation formula gives the endpoint terms, the bulk acceleration
integrals, and at each interior vertex the incoming boundary pairing minus the outgoing one.
Since both transverse velocities are the velocity of the same moving vertex, this is the usual
pairing of the variation field with the incoming-minus-outgoing velocity jump. Keeping the two
pairings separate avoids transports between propositionally equal tangent fibres.

The partition and its extensions are witnesses, not part of a new curve or energy carrier.
In particular the resulting derivative is independent of these choices. The fixed-endpoint
formula retains all interior corner terms; stationary endpoints do not make them vanish.

## References

* J. Milnor, *Morse Theory*, Princeton University Press (1963), §12, the first variation of
  energy for piecewise smooth curves.
* M. P. do Carmo, *Riemannian Geometry*, Chapter 9, §2.

The proof uses `TauCeti.Manifold.hasDerivAt_energy` on each smooth extension.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section EnergySum

variable [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Near the central parameter, the energy of a piecewise smooth family is the sum of the
energies of its smooth extensions. Matching is required on each closed piece, so the same
hypotheses also identify the moving vertices of adjacent pieces. -/
theorem eventually_energy_eq_sum_of_piecewise {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin n → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 1 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin n,
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ))) :
    (fun s ↦ energy I (F s) (τ 0) (τ (Fin.last n))) =ᶠ[𝓝 0]
      fun s ↦ ∑ i : Fin n, energy I (G i s) (τ i.castSucc) (τ i.succ) := by
  have hint (i : Fin n) : ∀ᶠ s in 𝓝 0,
      IntervalIntegrable (fun t ↦ ‖curveVelocity I (G i s) t‖ ^ 2) volume
        (τ i.castSucc) (τ i.succ) := by
    have hi := hτ (Fin.castSucc_le_succ i)
    obtain ⟨U, V, hUo, hVo, h0U, hV, hUV⟩ :=
      TauCeti.exists_isOpen_prod_contMDiffOn
        (K := uIcc (τ i.castSucc) (τ i.succ)) isCompact_uIcc (by simp)
        (fun t ht ↦ hG i t (by simpa only [uIcc_of_le hi] using ht))
    filter_upwards [hUo.mem_nhds h0U] with s hs
    have hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (G i s) V :=
      hUV.comp (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right s)).contMDiffOn
        (fun t ht ↦ ⟨hs, ht⟩)
    have hn : ContinuousOn (fun t ↦ ‖curveVelocity I (G i s) t‖) V :=
      (hc.continuousOn_norm_mfderiv (by norm_num) hVo (1 : ℝ)).congr
        (fun t _ ↦ congrArg norm (curveVelocity_apply (I := I) (γ := G i s) (t := t)))
    exact ((hn.pow 2).mono hV).intervalIntegrable
  have hsub (i : Fin n) : uIoo (τ i.castSucc) (τ i.succ) ⊆
      Icc (τ i.castSucc) (τ i.succ) := by
    rw [uIoo_of_le (hτ (Fin.castSucc_le_succ i))]
    exact Ioo_subset_Icc_self
  filter_upwards [hFG, Filter.eventually_all.mpr hint] with s hs hint
  have hnorm (i : Fin n) : EqOn (fun t ↦ ‖curveVelocity I (F s) t‖ ^ 2)
      (fun t ↦ ‖curveVelocity I (G i s) t‖ ^ 2) (uIoo (τ i.castSucc) (τ i.succ)) := by
    intro t ht
    have heq : F s =ᶠ[𝓝 t] G i s :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
        ((hs i).mono (hsub i))
    exact congrArg (· ^ 2) (heq.norm_curveVelocity_eq (I := I))
  have hintF (i : Fin n) : IntervalIntegrable (fun t ↦ ‖curveVelocity I (F s) t‖ ^ 2)
      volume (τ i.castSucc) (τ i.succ) :=
    (intervalIntegrable_congr_uIoo (hnorm i)).2 (hint i)
  rw [← sum_energy_adjacent_intervals (F s) τ hintF]
  exact Finset.sum_congr rfl fun i _ ↦ energy_congr ((hs i).mono (hsub i))

end EnergySum

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The first variation of energy for a continuous piecewise smooth family, including all
corner terms. At an interior vertex the scalar jump is the pairing with the incoming velocity
minus the pairing with the outgoing velocity. The two smooth extensions give the same moving
vertex by `hFG`; their tangent velocities along the pieces need not agree. -/
theorem hasDerivAt_energy_piecewise {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ))) :
    let B := fun (i : Fin (n + 1)) t ↦
      inner ℝ (variationField I (G i) t) (curveVelocity I (G i 0) t)
    HasDerivAt (fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      (B (Fin.last n) (τ (Fin.last (n + 1))) - B 0 (τ 0) +
        ∑ j : Fin n, (B j.castSucc (τ j.succ.castSucc) - B j.succ (τ j.succ.castSucc)) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (variationField I (G i) t)
            (acceleration (leviCivitaConnection I M) (G i 0) t)) 0 := by
  intro B
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    hasDerivAt_energy (I := I) (F := G i)
      (a := τ i.castSucc) (b := τ i.succ) (fun t ht ↦
      hG i t (by simpa only [uIcc_of_le (hτ (Fin.castSucc_le_succ i))] using ht)))
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)
  have heq := eventually_energy_eq_sum_of_piecewise τ hτ
    (fun i t ht ↦ (hG i t ht).of_le (by norm_num)) hFG
  have hboundary : ∑ i : Fin (n + 1), (B i (τ i.succ) - B i (τ i.castSucc)) =
      B (Fin.last n) (τ (Fin.last (n + 1))) - B 0 (τ 0) +
        ∑ j : Fin n, (B j.castSucc (τ j.succ.castSucc) - B j.succ (τ j.succ.castSucc)) := by
    rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (fun i ↦ B i (τ i.succ)),
      Fin.sum_univ_succ (fun i ↦ B i (τ i.castSucc)), Finset.sum_sub_distrib]
    simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero]
    ring
  convert hd.congr_of_eventuallyEq heq using 1
  rw [← hboundary]
  simp only [B, Finset.sum_sub_distrib]

/-- For stationary outer endpoints the first variation consists of the interior velocity-jump
terms and the bulk acceleration integrals. No stationarity is imposed on interior vertices. -/
theorem hasDerivAt_energy_piecewise_of_fixed_endpoints {n : ℕ} (τ : Fin (n + 2) → ℝ)
    (hτ : Monotone τ) {F : ℝ → ℝ → M} {G : Fin (n + 1) → ℝ → ℝ → M}
    (hG : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ G i z.1 z.2) (0, t))
    (hFG : ∀ᶠ s in 𝓝 0, ∀ i : Fin (n + 1),
      EqOn (F s) (G i s) (Icc (τ i.castSucc) (τ i.succ)))
    (ha : ∀ᶠ s in 𝓝 0, F s (τ 0) = F 0 (τ 0))
    (hb : ∀ᶠ s in 𝓝 0, F s (τ (Fin.last (n + 1))) = F 0 (τ (Fin.last (n + 1)))) :
    let B := fun (i : Fin (n + 1)) t ↦
      inner ℝ (variationField I (G i) t) (curveVelocity I (G i 0) t)
    HasDerivAt (fun s ↦ energy I (F s) (τ 0) (τ (Fin.last (n + 1))))
      ((∑ j : Fin n, (B j.castSucc (τ j.succ.castSucc) - B j.succ (τ j.succ.castSucc))) -
        ∑ i : Fin (n + 1), ∫ t in τ i.castSucc..τ i.succ,
          inner ℝ (variationField I (G i) t)
            (acceleration (leviCivitaConnection I M) (G i 0) t)) 0 := by
  have hleft : τ 0 ∈ Icc (τ (0 : Fin (n + 1)).castSucc) (τ (0 : Fin (n + 1)).succ) :=
    ⟨le_rfl, hτ (Fin.zero_le _)⟩
  have hright : τ (Fin.last (n + 1)) ∈
      Icc (τ (Fin.last n).castSucc) (τ (Fin.last n).succ) :=
    ⟨hτ (Fin.le_last _), le_rfl⟩
  have haG : ∀ᶠ s in 𝓝 0, G 0 s (τ 0) = G 0 0 (τ 0) := by
    filter_upwards [hFG, ha] with s hs hs0
    rw [← hs 0 hleft, hs0, hFG.self_of_nhds 0 hleft]
  have hbG : ∀ᶠ s in 𝓝 0,
      G (Fin.last n) s (τ (Fin.last (n + 1))) =
        G (Fin.last n) 0 (τ (Fin.last (n + 1))) := by
    filter_upwards [hFG, hb] with s hs hs0
    rw [← hs (Fin.last n) hright, hs0, hFG.self_of_nhds (Fin.last n) hright]
  have h := hasDerivAt_energy_piecewise τ hτ hG hFG
  simpa only [variationField_eq_zero haG, variationField_eq_zero hbG, inner_zero_left,
    sub_zero, zero_add, sub_self] using h

end TauCeti.Manifold
