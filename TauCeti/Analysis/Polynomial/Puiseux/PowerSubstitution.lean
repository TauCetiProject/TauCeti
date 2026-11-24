/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SimpleRoots.Covering
public import TauCeti.Topology.Covering.PowerSubstitution
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Limit

/-!
# Continuous roots after a power substitution

A continuous monic family of degree `d` over a simply connected, locally path connected parameter
space and a punctured disc, separable at every point, splits into `d` pointwise distinct continuous
linear factors after the substitution `(w, t) ↦ (w, t ^ n)`, provided `d ! ∣ n` and the
substituted disc fits inside the original disc.

Over a disc rather than a punctured disc, with roots allowed to collide at the centre only, the
continuous roots extend across the centre
(`TauCeti.Polynomial.exists_continuousOn_prod_X_sub_C_add_pow`). After the substitution
`y = c + ζ ^ n` the family splits into `d` linear factors, continuous on the whole disc, distinct
off the centre, and listing at `ζ = 0` the roots of the central member with their multiplicities.
Each root function converges at the centre to a root of the central member
(`TauCeti.Polynomial.exists_isRoot_tendsto_of_continuousOn`), and the factorization passes to the
limit (`TauCeti.Polynomial.eq_prod_X_sub_C_of_continuousAt`, in
`TauCeti.Topology.Algebra.Polynomial.Basic`).

The analytic version, with ambient root functions on an open simply connected domain, is
`TauCeti.Polynomial.exists_analyticOnNhd_eq_prod_X_sub_C_powerSubstitution` in
`TauCeti.Analysis.Polynomial.Puiseux.Branches`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

noncomputable section

open Function Filter Metric Polynomial Set Topology

namespace TauCeti.Polynomial

/-- A continuous family of degree `d`, separable over a punctured disc, has `d` pointwise
distinct continuous root functions after a power substitution of exponent divisible by `d !`.
The parameter space can be any simply connected, locally path connected space. -/
theorem exists_continuousMap_isRoot_powerSubstitution
    {U : Type*} [TopologicalSpace U] [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    {d n : ℕ} {R R' : ℝ} {F : U × ↥(ball (0 : ℂ) R \ {0}) → ℂ[X]}
    (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hdeg : ∀ b, (F b).natDegree = d) (hsep : ∀ b, (F b).Separable)
    (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n) :
    ∃ r : Fin d → C(U × ↥(ball (0 : ℂ) R' \ {0}), ℂ), ∀ b,
      Injective (fun i => r i b) ∧ ∀ i, (F (powerSubstitution U hn hR b)).IsRoot (r i b) := by
  classical
  obtain hempty | ⟨⟨a⟩⟩ := isEmpty_or_nonempty (U × ↥(ball (0 : ℂ) R' \ {0}))
  · let := hempty
    exact ⟨fun _ => 0, fun b => isEmptyElim b⟩
  let B := U × ↥(ball (0 : ℂ) R \ {0})
  let Z := {q : B × ℂ // (F q.1).IsRoot q.2}
  let p : Z → B := fun q => q.val.1
  let q := powerSubstitution U hn hR
  -- Lift all points of one fibre, then use their root coordinates as the global labels.
  have hp : IsCoveringMap p := isCoveringMap_fst_isRoot hF hdeg hsep
  let : Finite (p ⁻¹' {q a}) := finite_preimage_fst_isRoot (hsep _).ne_zero
  have hcard : Nat.card (p ⁻¹' {q a}) = d := natCard_preimage_fst_isRoot (hdeg _) (hsep _)
  obtain ⟨L, hL, hinj⟩ := hp.exists_continuousMap_lifts_powerSubstitution hn hR a
    (by rwa [hcard])
  let := Fintype.ofFinite (p ⁻¹' {q a})
  let e : Fin d ≃ p ⁻¹' {q a} :=
    (Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])).symm
  let r : Fin d → C(U × ↥(ball (0 : ℂ) R' \ {0}), ℂ) := fun i =>
    ⟨fun b => (L (e i) b).val.2,
      ((continuous_snd : Continuous (Prod.snd : B × ℂ → ℂ)).comp
        (continuous_subtypeVal : Continuous (Subtype.val : Z → B × ℂ))).comp (L (e i)).continuous⟩
  have hbase : ∀ i b, p (L (e i) b) = q b := fun i b => congrFun (hL (e i)).2 b
  refine ⟨r, fun b => ⟨?_, fun i => (hbase i b) ▸ (L (e i) b).property⟩⟩
  intro i j hij
  apply e.injective
  apply hinj b
  exact Subtype.ext (Prod.ext ((hbase i b).trans (hbase j b).symm) hij)

/-- A continuous monic family of degree `d`, separable over a punctured disc, splits into `d`
pointwise distinct continuous linear factors after a power substitution of exponent divisible by
`d !`. The parameter space can be any simply connected, locally path connected space. -/
theorem exists_continuousMap_prod_X_sub_C_powerSubstitution
    {U : Type*} [TopologicalSpace U] [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    {d n : ℕ} {R R' : ℝ} {F : U × ↥(ball (0 : ℂ) R \ {0}) → ℂ[X]}
    (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hmonic : ∀ b, (F b).Monic) (hdeg : ∀ b, (F b).natDegree = d)
    (hsep : ∀ b, (F b).Separable) (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n) :
    ∃ r : Fin d → C(U × ↥(ball (0 : ℂ) R' \ {0}), ℂ), ∀ b,
      Injective (fun i => r i b) ∧
      F (powerSubstitution U hn hR b) = ∏ i, (X - C (r i b)) := by
  obtain ⟨r, hr⟩ := exists_continuousMap_isRoot_powerSubstitution hF hdeg hsep hn hR hdvd
  exact ⟨r, fun b => ⟨(hr b).1, (Sym.toMonic_ofFn_eq_of_forall_isRoot (hmonic _) (hdeg _)
    (hr b).1 (hr b).2).symm.trans (Sym.toMonic_ofFn _)⟩⟩

/-- The punctured-disc stage of `TauCeti.Polynomial.exists_continuousOn_prod_X_sub_C_add_pow`:
after the substitution `y = c + ζ ^ n` the family splits over the punctured disc into linear
factors with continuous, pairwise distinct roots. -/
private theorem exists_continuousOn_prod_X_sub_C_add_pow_of_ne {F : ℂ → ℂ[X]} {c : ℂ} {d n : ℕ}
    {R R' : ℝ} (hF : ∀ i ≤ d, ContinuousOn (fun y => (F y).coeff i) (ball c R))
    (hmonic : ∀ y ∈ ball c R, (F y).Monic) (hdeg : ∀ y ∈ ball c R, (F y).natDegree = d)
    (hsep : ∀ y ∈ ball c R, y ≠ c → (F y).Separable) (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (hdvd : d.factorial ∣ n) :
    ∃ v : Fin d → ℂ → ℂ, (∀ i, ContinuousOn (v i) (ball 0 R' \ {0})) ∧
      (∀ ζ ∈ ball (0 : ℂ) R' \ {0}, F (c + ζ ^ n) = ∏ i, (X - C (v i ζ))) ∧
      ∀ ζ ∈ ball (0 : ℂ) R' \ {0}, Injective fun i => v i ζ := by
  classical
  have hmem : ∀ w ∈ ball (0 : ℂ) R, c + w ∈ ball c R := fun w hw => by
    simpa [mem_ball_iff_norm] using hw
  -- over the punctured disc the roots are the continuous roots of the power substitution
  obtain ⟨r, hr⟩ := exists_continuousMap_prod_X_sub_C_powerSubstitution (U := Unit)
    (F := fun b => F (c + (b.snd : ℂ)))
    (fun i hi => (hF i hi).comp_continuous (by fun_prop) fun b => hmem _ b.snd.property.left)
    (fun b => hmonic _ (hmem _ b.snd.property.left)) (fun b => hdeg _ (hmem _ b.snd.property.left))
    (fun b => hsep _ (hmem _ b.snd.property.left) (by simpa using b.snd.property.right)) hn hR hdvd
  set v : Fin d → ℂ → ℂ := fun i ζ =>
    if h : ζ ∈ ball (0 : ℂ) R' \ {0} then r i ((), ⟨ζ, h⟩) else 0 with hv
  have hv_apply (i : Fin d) {ζ : ℂ} (h : ζ ∈ ball (0 : ℂ) R' \ {0}) :
      v i ζ = r i ((), ⟨ζ, h⟩) := by
    simp only [hv]
    exact dite_eq_left_of_eq_true (eq_true h)
  have hvc (i : Fin d) : ContinuousOn (v i) (ball 0 R' \ {0}) := by
    have h : (ball (0 : ℂ) R' \ {0}).domRestrict (v i) = fun x => r i ((), x) :=
      funext fun x => hv_apply i x.property
    rw [continuousOn_iff_continuous_domRestrict, h]
    fun_prop
  have hvF : ∀ ζ ∈ ball (0 : ℂ) R' \ {0}, F (c + ζ ^ n) = ∏ i, (X - C (v i ζ)) := fun ζ hζ => by
    simpa [hv_apply _ hζ] using (hr ((), ⟨ζ, hζ⟩)).2
  have hvinj : ∀ ζ ∈ ball (0 : ℂ) R' \ {0}, Injective fun i => v i ζ := fun ζ hζ => by
    simpa [hv_apply _ hζ] using (hr ((), ⟨ζ, hζ⟩)).1
  exact ⟨v, hvc, hvF, hvinj⟩

/-- **Continuous root branches through a collision.** Let `F y` be monic polynomials of degree
`d` for `y` in the disc `ball c R`, with coefficients continuous on the disc and separable except
possibly at the centre `c`. After the substitution `y = c + ζ ^ n`, with `d ! ∣ n` and the disc
`ball 0 R'` mapped into `ball c R`, the family splits on the whole disc `ball 0 R'` into `d`
linear factors `X - u_i(ζ)` with continuous roots `u_i`, pairwise distinct for `ζ ≠ 0`. At `ζ = 0`
the `u_i(0)` are the roots of `F c` with their multiplicities. -/
theorem exists_continuousOn_prod_X_sub_C_add_pow {F : ℂ → ℂ[X]} {c : ℂ} {d n : ℕ} {R R' : ℝ}
    (hF : ∀ i ≤ d, ContinuousOn (fun y => (F y).coeff i) (ball c R))
    (hmonic : ∀ y ∈ ball c R, (F y).Monic) (hdeg : ∀ y ∈ ball c R, (F y).natDegree = d)
    (hsep : ∀ y ∈ ball c R, y ≠ c → (F y).Separable) (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (hdvd : d.factorial ∣ n) :
    ∃ u : Fin d → ℂ → ℂ, (∀ i, ContinuousOn (u i) (ball 0 R')) ∧
      (∀ ζ ∈ ball (0 : ℂ) R', F (c + ζ ^ n) = ∏ i, (X - C (u i ζ))) ∧
      ∀ ζ ∈ ball (0 : ℂ) R', ζ ≠ 0 → Injective fun i => u i ζ := by
  classical
  obtain ⟨v, hvc, hvF, hvinj⟩ :=
    exists_continuousOn_prod_X_sub_C_add_pow_of_ne hF hmonic hdeg hsep hn hR hdvd
  rcases le_or_gt R' 0 with hR' | hR'
  · exact ⟨v, fun i => by simp [ball_eq_empty.2 hR'], by simp [ball_eq_empty.2 hR'],
      by simp [ball_eq_empty.2 hR']⟩
  -- the substituted family `F (c + ζ ^ n)` near `ζ = 0`
  have hpow : ∀ ζ ∈ ball (0 : ℂ) R', c + ζ ^ n ∈ ball c R := fun ζ hζ => by
    simpa [mem_ball_iff_norm] using mapsTo_pow_ball_zero hn hR hζ
  have hG : ∀ i ≤ d, ContinuousAt (fun ζ : ℂ => (F (c + ζ ^ n)).coeff i) 0 := fun i hi =>
    ((hF i hi).continuousAt (isOpen_ball.mem_nhds (hpow 0 (mem_ball_self hR')))).comp_of_eq
      (f := fun ζ : ℂ => c + ζ ^ n) (by fun_prop) rfl
  have hGdeg : ∀ᶠ ζ in 𝓝 (0 : ℂ), (F (c + ζ ^ n)).degree = d :=
    eventually_of_mem (ball_mem_nhds 0 hR') fun ζ hζ => by
      rw [degree_eq_natDegree (hmonic _ (hpow ζ hζ)).ne_zero, hdeg _ (hpow ζ hζ)]
  -- each root converges at the centre; extend it by its limit
  have hlim (i : Fin d) : ∃ w, Tendsto (v i) (𝓝[≠] 0) (𝓝 w) := by
    obtain ⟨w, -, hw⟩ := exists_isRoot_tendsto_of_continuousOn
      (by simp [Complex.rank_real_complex]) hG hGdeg hR' (hvc i) fun ζ hζ => by
        rw [IsRoot, hvF ζ hζ, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    exact ⟨w, hw⟩
  choose w hw using hlim
  set u : Fin d → ℂ → ℂ := fun i => update (v i) 0 (w i)
  have hu (i : Fin d) {ζ : ℂ} (hζ : ζ ≠ 0) : u i ζ = v i ζ := update_of_ne hζ _ _
  have huc (i : Fin d) : ContinuousOn (u i) (ball 0 R') := by
    intro ζ hζ
    rcases eq_or_ne ζ 0 with rfl | hζ0
    · exact (continuousAt_update_same.2 (hw i)).continuousWithinAt
    · have hv : ContinuousAt (v i) ζ :=
        (hvc i).continuousAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hζ, hζ0⟩)
      exact (hv.congr (eventually_of_mem (isOpen_ne.mem_nhds hζ0) fun z hz =>
        (hu i hz).symm)).continuousWithinAt
  refine ⟨u, huc, fun ζ hζ => ?_, fun ζ hζ hζ0 => by simpa only [hu _ hζ0] using hvinj ζ ⟨hζ, hζ0⟩⟩
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · -- at the centre, the factorization holds in the limit
    refine eq_prod_X_sub_C_of_continuousAt (F := fun ζ : ℂ => F (c + ζ ^ n)) hG
      (hGdeg.mono fun ζ hζ => natDegree_le_of_degree_le hζ.le)
      (fun i => (huc i).continuousAt (ball_mem_nhds 0 hR')) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds 0 hR')] with ζ hζ0 hζ
    rw [hvF ζ ⟨hζ, hζ0⟩]
    simp only [hu _ hζ0]
  · simpa only [hu _ hζ0] using hvF ζ ⟨hζ, hζ0⟩

end TauCeti.Polynomial
