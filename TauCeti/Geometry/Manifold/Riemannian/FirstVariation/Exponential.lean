/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length
public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Piecewise
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.Variation
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Piecewise
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# First variation of energy and length along exponential variations

For a curve `γ` in a smooth Riemannian manifold and a tangent field `V` along `γ` whose lift to
the tangent bundle is `C²` on the closed interval `uIcc a b` (or continuous piecewise `C²` on
`Icc a b`), the exponential variation `TauCeti.Manifold.exponentialVariation I γ V` realizes `V` as
the variation field of a family of curves whose energy and length can be differentiated at `s = 0`.
Because `TauCeti.Manifold.exists_contMDiffAt_exponentialVariation_eqOn` extends any closed-interval
`C^k` section lift to a two-sided `C^k` lift having the same exponential variation on `uIcc a b`,
all statements below require only closed-interval (`ContMDiffOn`) or piecewise
(`IsPiecewiseContMDiffOn` / `PiecewiseContMDiffSectionAlong`) regularity, with endpoint velocities
read within the closed interval via `curveVelocityWithin`.

## Main results

* `TauCeti.Manifold.eventually_pathELength_exponentialVariation_ne_top`: curves of a `C¹`
  exponential variation have finite Riemannian length near `s = 0`.
* `TauCeti.Manifold.hasDerivAt_energy_exponentialVariation`: first variation of energy along an
  exponential variation for a field with a `C²` lift on `uIcc a b`.
* `TauCeti.Manifold.hasDerivAt_energy_exponentialVariation_of_isPiecewiseContMDiffOn` and
  `TauCeti.Manifold.PiecewiseContMDiffSectionAlong.hasDerivAt_energy_exponentialVariation`:
  first variation of energy along an exponential variation of an unbroken curve for a continuous
  piecewise `C²` field.
* `TauCeti.Manifold.hasDerivAt_toReal_pathELength_exponentialVariation`: first variation of length
  along an exponential variation of a constant-speed curve.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 9, §2.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §12 (first variation of energy for smooth and piecewise smooth curves).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 6 (the first variation formula for length).
-/

public noncomputable section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- For a field `V` along `γ` whose tangent-bundle lift is `C¹` on `uIcc a b`, the curves
`exp_(γ ·) (s • V ·)` have finite Riemannian length between `a` and `b` for all `s` near `0`. -/
theorem eventually_pathELength_exponentialVariation_ne_top {a b : ℝ}
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc a b)) :
    ∀ᶠ s in 𝓝 (0 : ℝ), Manifold.pathELength I (exponentialVariation I γ V s) a b ≠ ⊤ := by
  obtain ⟨γ', V', hV', -, hExp⟩ := exists_contMDiffAt_exponentialVariation_eqOn γ V hV
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hfin := eventually_pathELength_ne_top (I := I) (a := a) (b := b)
    (F := exponentialVariation I γ' V') fun t ht ↦
      contMDiffAt_exponentialVariation_zero γ' V' (hV' t ht)
  filter_upwards [hfin] with s hs
  rwa [← Manifold.pathELength_congr ((hExp s).mono Icc_subset_uIcc)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Transfer the endpoint pairing `⟪V'(t), γ''(t)⟫` of a two-sided `C^1` extension `(γ', V')` on
a nondegenerate closed interval `uIcc a b` to `⟪V(t), γ'_{uIcc a b}(t)⟫`. -/
private theorem inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq
    {γ' : ℝ → M} {V' : ∀ t, TangentSpace I (γ' t)} {a b t : ℝ} (hab : a ≠ b) (ht : t ∈ uIcc a b)
    (hV' : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ' r) (V' r)) t)
    (hEq : ∀ r ∈ uIcc a b, TotalSpace.mk' E (γ' r) (V' r) = TotalSpace.mk' E (γ r) (V r)) :
    ⟪V' t, curveVelocity I γ' t⟫_ℝ = ⟪V t, curveVelocityWithin I γ (uIcc a b) t⟫_ℝ := by
  have hγ't : MDifferentiableAt 𝓘(ℝ, ℝ) I γ' t :=
    ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp t hV').mdifferentiableAt one_ne_zero
  have hγEq : EqOn γ' γ (uIcc a b) := fun r hr ↦ congrArg TotalSpace.proj (hEq r hr)
  have hvel_eq : curveVelocity I γ' t = curveVelocityWithin I γ' (uIcc a b) t := by
    rw [← curveVelocityWithin_univ]
    exact (curveVelocityWithin_subset (subset_univ _) (uniqueDiffOn_uIcc hab t ht)
      hγ't.mdifferentiableWithinAt).symm
  have hvel_lift := (eventuallyEq_of_mem self_mem_nhdsWithin hγEq).curveVelocityLiftWithin_eq
    (I := I) (hγEq ht)
  rw [curveVelocityLiftWithin_apply, curveVelocityLiftWithin_apply] at hvel_lift
  rw [hvel_eq]
  exact TauCeti.inner_eq_of_totalSpaceMk_eq (hEq t ht) hvel_lift

omit [I.Boundaryless] [T2Space M] in
/-- Transfer the bulk acceleration integral `∫_a^b ⟪V', D_t γ''⟫` across two pairs `(γ', V')` and
`(γ, V)` whose tangent-bundle lifts agree on `uIcc a b`. -/
private theorem integral_inner_acceleration_eq_of_totalSpaceMk_eq
    {γ' : ℝ → M} {V' : ∀ t, TangentSpace I (γ' t)} {a b : ℝ}
    (hEq : ∀ r ∈ uIcc a b, TotalSpace.mk' E (γ' r) (V' r) = TotalSpace.mk' E (γ r) (V r)) :
    ∫ t in a..b, ⟪V' t, acceleration (leviCivitaConnection I M) γ' t⟫_ℝ =
      ∫ t in a..b, ⟪V t, acceleration (leviCivitaConnection I M) γ t⟫_ℝ := by
  have hγEq : EqOn γ' γ (uIcc a b) := fun r hr ↦ congrArg TotalSpace.proj (hEq r hr)
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  have hnear : γ' =ᶠ[𝓝 t] γ :=
    eventuallyEq_of_mem (mem_of_superset (isOpen_Ioo.mem_nhds ht) uIoo_subset_uIcc_self) hγEq
  exact TauCeti.inner_eq_of_totalSpaceMk_eq (hEq t (uIoo_subset_uIcc_self ht))
    (hnear.totalSpaceMk_acceleration_eq (leviCivitaConnection I M))

/-- **First variation of energy along an exponential variation.** Let `V` be a tangent field along
`γ` whose tangent-bundle lift is `C²` on `uIcc a b`. Then the energy of `exp_(γ ·) (s • V ·)`
between `a` and `b` has derivative
`⟪V(b), γ'_{uIcc a b}(b)⟫ - ⟪V(a), γ'_{uIcc a b}(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt` at `s = 0`. -/
theorem hasDerivAt_energy_exponentialVariation {a b : ℝ}
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc a b)) :
    HasDerivAt (fun s ↦ energy I (exponentialVariation I γ V s) a b)
      (inner ℝ (V b) (curveVelocityWithin I γ (uIcc a b) b) -
        inner ℝ (V a) (curveVelocityWithin I γ (uIcc a b) a) -
        ∫ t in a..b, inner ℝ (V t) (acceleration (leviCivitaConnection I M) γ t)) 0 := by
  rcases eq_or_ne a b with rfl | hab
  · simp only [energy_def, intervalIntegral.integral_same, zero_div, sub_self]
    exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  obtain ⟨γ', V', hV', hEq, hExp⟩ := exists_contMDiffAt_exponentialVariation_eqOn γ V hV
  have hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ' V' z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t ht)
  have hderiv' : HasDerivAt (fun s ↦ energy I (exponentialVariation I γ' V' s) a b)
      (inner ℝ (V' b) (curveVelocity I γ' b) - inner ℝ (V' a) (curveVelocity I γ' a) -
        ∫ t in a..b, inner ℝ (V' t) (acceleration (leviCivitaConnection I M) γ' t)) 0 := by
    have h0 : exponentialVariation I γ' V' 0 = γ' := exponentialVariation_zero γ' V'
    have hVF : ∀ t, HEq (variationField I (exponentialVariation I γ' V') t) (V' t) :=
      fun t ↦ heq_of_eq (variationField_exponentialVariation γ' V' t)
    generalize exponentialVariation I γ' V' = G at hF h0 hVF ⊢
    subst h0
    simpa only [funext fun t ↦ eq_of_heq (hVF t)] using hasDerivAt_energy hF
  have henergy : (fun s ↦ energy I (exponentialVariation I γ V s) a b) =
      fun s ↦ energy I (exponentialVariation I γ' V' s) a b :=
    funext fun s ↦ (energy_congr ((hExp s).mono uIoo_subset_uIcc_self)).symm
  rw [henergy]
  refine hderiv'.congr_deriv ?_
  rw [inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq hab right_mem_uIcc
      ((hV' b right_mem_uIcc).of_le one_le_two) hEq,
    inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq hab left_mem_uIcc
      ((hV' a left_mem_uIcc).of_le one_le_two) hEq,
    integral_inner_acceleration_eq_of_totalSpaceMk_eq hEq]

/-- **First variation of energy along a piecewise `C²` exponential variation of an unbroken curve.**
Let `V` be a continuous piecewise `C²` field along `γ` on `[a, b]` (`IsPiecewiseContMDiffOn`), and
assume `γ` is differentiable at every interior point of `(a, b)` so that adjacent piece velocities
agree at every corner of `V`. Then all interior corner pairings cancel and
`d/ds E(exp_(γ ·) (s • V ·)) |₀ =
  ⟪V(b), γ'_[a,b](b)⟫ - ⟪V(a), γ'_[a,b](a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`. -/
theorem hasDerivAt_energy_exponentialVariation_of_isPiecewiseContMDiffOn {a b : ℝ}
    (hγ : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : IsPiecewiseContMDiffOn I.tangent 2
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) a b) :
    HasDerivAt (fun s ↦ energy I (exponentialVariation I γ V s) a b)
      (inner ℝ (V b) (curveVelocityWithin I γ (Icc a b) b) -
        inner ℝ (V a) (curveVelocityWithin I γ (Icc a b) a) -
        ∫ t in a..b, inner ℝ (V t) (acceleration (leviCivitaConnection I M) γ t)) 0 := by
  obtain ⟨n, τ, hτa, hτb, hτ, hpieces⟩ := hV.exists_partition
  have hτ_strict : StrictMono τ := Fin.strictMono_iff_lt_succ.mpr hτ
  have hτ_mono : Monotone τ := hτ_strict.monotone
  have hpi (i : Fin (n + 1)) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc (τ i.castSucc) (τ i.succ)) := by
    rw [uIcc_of_le (hτ i).le]
    exact hpieces i
  -- Extend each closed piece to a two-sided `C²` section lift to sum energies and check
  -- integrability of `⟪V, D_t γ'⟫` on each piece.
  choose γi Vi hVi hEqi hExpi using
    fun i : Fin (n + 1) ↦ exists_contMDiffAt_exponentialVariation_eqOn γ V (hpi i)
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  have heq : (fun s ↦ energy I (exponentialVariation I γ V s) a b) =ᶠ[𝓝 0]
      fun s ↦ ∑ i : Fin (n + 1),
        energy I (exponentialVariation I γ V s) (τ i.castSucc) (τ i.succ) := by
    have hsum := eventually_energy_eq_sum_of_piecewise τ hτ_mono
      (F := exponentialVariation I γ V) (G := fun i ↦ exponentialVariation I (γi i) (Vi i))
      (fun i t ht ↦ (contMDiffAt_exponentialVariation_zero (γi i) (Vi i)
        (hVi i t (by rwa [uIcc_of_le (hτ i).le]))).of_le (by norm_num))
      (Eventually.of_forall fun s i t ht ↦
        (hExpi i s (by rwa [uIcc_of_le (hτ i).le])).symm)
    rw [hτa, hτb] at hsum
    filter_upwards [hsum] with s hs
    rw [hs]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact energy_congr ((hExpi i s).mono uIoo_subset_uIcc_self)
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    hasDerivAt_energy_exponentialVariation (I := I) (γ := γ) (V := V) (hpi i)
  -- Match each piece endpoint velocity to `curveVelocityWithin I γ (Icc a b)`.
  have hvel_left (i : Fin (n + 1)) :
      curveVelocityWithin I γ (uIcc (τ i.castSucc) (τ i.succ)) (τ i.castSucc) =
        curveVelocityWithin I γ (Icc a b) (τ i.castSucc) := by
    rw [uIcc_of_le (hτ i).le]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [Fin.castSucc_zero, hτa]
      have hset : Icc a (τ (0 : Fin (n + 1)).succ) =ᶠ[𝓝 a] Icc a b := by
        filter_upwards [Iio_mem_nhds (by simpa only [Fin.castSucc_zero, hτa] using hτ 0)] with t ht
        have htb : t ≤ b := ht.le.trans (hτb ▸ hτ_mono (Fin.le_last _))
        exact ⟨fun h ↦ ⟨h.1, htb⟩, fun h ↦ ⟨h.1, ht.le⟩⟩
      simp only [curveVelocityWithin_apply, mfderivWithin_congr_set hset]
    · have h0lt : (0 : Fin (n + 2)) < i.castSucc :=
        Fin.pos_iff_ne_zero.mpr fun h ↦ hi (Fin.ext (by simpa using congrArg Fin.val h))
      have hmem : τ i.castSucc ∈ Ioo a b :=
        ⟨hτa ▸ hτ_strict h0lt, hτb ▸ hτ_strict (Fin.castSucc_lt_last i)⟩
      rw [curveVelocityWithin_subset (subset_univ _)
          (uniqueDiffOn_Icc (hτ i) _ ⟨le_rfl, (hτ i).le⟩)
          (hγ _ hmem).mdifferentiableWithinAt,
        curveVelocityWithin_univ, curveVelocityWithin_of_mem_nhds (Icc_mem_nhds hmem.1 hmem.2)]
  have hvel_right (i : Fin (n + 1)) :
      curveVelocityWithin I γ (uIcc (τ i.castSucc) (τ i.succ)) (τ i.succ) =
        curveVelocityWithin I γ (Icc a b) (τ i.succ) := by
    rw [uIcc_of_le (hτ i).le]
    rcases eq_or_ne i (Fin.last n) with rfl | hi
    · rw [Fin.succ_last, hτb]
      have hset : Icc (τ (Fin.last n).castSucc) b =ᶠ[𝓝 b] Icc a b := by
        filter_upwards [Ioi_mem_nhds
          (by simpa only [Fin.succ_last, hτb] using hτ (Fin.last n))] with t ht
        have hat : a ≤ t := (hτa ▸ hτ_mono (Fin.zero_le (Fin.last n).castSucc)).trans ht.le
        exact ⟨fun h ↦ ⟨hat, h.2⟩, fun h ↦ ⟨ht.le, h.2⟩⟩
      simp only [curveVelocityWithin_apply, mfderivWithin_congr_set hset]
    · have hlt_last : i.succ < Fin.last (n + 1) := by
        rw [Fin.lt_def, Fin.val_succ, Fin.val_last]
        have : i.val < n :=
          lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) (by simpa [Fin.ext_iff] using hi)
        omega
      have hmem : τ i.succ ∈ Ioo a b :=
        ⟨hτa ▸ hτ_strict (Fin.succ_pos i), hτb ▸ hτ_strict hlt_last⟩
      rw [curveVelocityWithin_subset (subset_univ _)
          (uniqueDiffOn_Icc (hτ i) _ ⟨(hτ i).le, le_rfl⟩)
          (hγ _ hmem).mdifferentiableWithinAt,
        curveVelocityWithin_univ, curveVelocityWithin_of_mem_nhds (Icc_mem_nhds hmem.1 hmem.2)]
  -- Each piece acceleration integrand is interval integrable by comparison with `(γi i, Vi i)`.
  have hint (i : Fin (n + 1)) : IntervalIntegrable
      (fun t ↦ inner ℝ (V t) (acceleration (leviCivitaConnection I M) γ t)) volume
      (τ i.castSucc) (τ i.succ) := by
    have hcont : ContinuousOn (fun t ↦ inner ℝ (Vi i t)
        (acceleration (leviCivitaConnection I M) (γi i) t)) (uIcc (τ i.castSucc) (τ i.succ)) := by
      intro t ht
      have hc := continuousAt_inner_variationField_acceleration
        (contMDiffAt_exponentialVariation_zero (γi i) (Vi i) (hVi i t ht))
      have heq_f : (fun r ↦ inner ℝ (variationField I (exponentialVariation I (γi i) (Vi i)) r)
          (acceleration (leviCivitaConnection I M) (exponentialVariation I (γi i) (Vi i) 0) r)) =
          fun r ↦ inner ℝ (Vi i r) (acceleration (leviCivitaConnection I M) (γi i) r) :=
        funext fun r ↦ TauCeti.inner_eq_of_totalSpaceMk_eq
          (TotalSpace.ext (congrFun (exponentialVariation_zero (γi i) (Vi i)) r)
            (heq_of_eq (variationField_exponentialVariation (γi i) (Vi i) r)))
          ((EventuallyEq.of_eq
            (exponentialVariation_zero (γi i) (Vi i))).totalSpaceMk_acceleration_eq
            (leviCivitaConnection I M))
      rw [heq_f] at hc
      exact hc.continuousWithinAt
    refine hcont.intervalIntegrable.congr_uIoo fun t ht ↦ ?_
    have hγEq : EqOn (γi i) γ (uIcc (τ i.castSucc) (τ i.succ)) :=
      fun r hr ↦ congrArg TotalSpace.proj (hEqi i r hr)
    have hnear : γi i =ᶠ[𝓝 t] γ :=
      eventuallyEq_of_mem (mem_of_superset (isOpen_Ioo.mem_nhds ht) uIoo_subset_uIcc_self) hγEq
    exact TauCeti.inner_eq_of_totalSpaceMk_eq (hEqi i t (uIoo_subset_uIcc_self ht))
      (hnear.totalSpaceMk_acceleration_eq (leviCivitaConnection I M))
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  have hsum_int := TauCeti.intervalIntegral.sum_integral_adjacent_intervals_fin τ hint
  rw [hτa, hτb] at hsum_int
  have htele := Fin.sum_univ_succ_sub_castSucc
    (fun k ↦ inner ℝ (V (τ k)) (curveVelocityWithin I γ (Icc a b) (τ k)))
  rw [hτa, hτb] at htele
  simp only [hvel_left, hvel_right, Finset.sum_sub_distrib, htele, hsum_int]

/-- **First variation of energy along a bundled piecewise smooth section.** Specialization of
`hasDerivAt_energy_exponentialVariation_of_isPiecewiseContMDiffOn` to a bundled section
`W : PiecewiseContMDiffSectionAlong hγp` (`2 ≤ n`) extended by zero outside `[a, b]`. -/
theorem PiecewiseContMDiffSectionAlong.hasDerivAt_energy_exponentialVariation
    {n : ℕ∞ω} {a b : ℝ} {hγp : IsPiecewiseContMDiffOn I n γ a b} (hn : 2 ≤ n)
    (hγ : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγp) :
    HasDerivAt (fun s ↦ energy I (exponentialVariation I γ W.extendByZero s) a b)
      (inner ℝ (W.val ⟨b, hγp.lt.le, le_rfl⟩) (curveVelocityWithin I γ (Icc a b) b) -
        inner ℝ (W.val ⟨a, le_rfl, hγp.lt.le⟩) (curveVelocityWithin I γ (Icc a b) a) -
        ∫ t in a..b, inner ℝ (W.extendByZero t)
          (acceleration (leviCivitaConnection I M) γ t)) 0 := by
  simpa only [W.extendByZero_apply_of_mem ⟨hγp.lt.le, le_rfl⟩,
    W.extendByZero_apply_of_mem ⟨le_rfl, hγp.lt.le⟩] using
    hasDerivAt_energy_exponentialVariation_of_isPiecewiseContMDiffOn hγ
      (W.isPiecewiseContMDiffOn_extendByZero.of_le hn)

/-- **First variation of length along an exponential variation.** Let `a ≤ b`, let `γ` have
constant speed `C > 0` on `(a, b)`, and let `V` be a tangent field along `γ` whose tangent-bundle
lift is `C²` on `[a, b]`. Then
`d/ds L(exp_(γ ·) (s • V ·)) |₀ =
  (⟪V(b), γ'_[a,b](b)⟫ - ⟪V(a), γ'_[a,b](a)⟫ - ∫_a^b ⟪V, D_t γ'⟫ dt) / C`. -/
theorem hasDerivAt_toReal_pathELength_exponentialVariation {a b : ℝ} (hab : a ≤ b)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (Icc a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = C) :
    HasDerivAt (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      ((⟪V b, curveVelocityWithin I γ (Icc a b) b⟫_ℝ -
        ⟪V a, curveVelocityWithin I γ (Icc a b) a⟫_ℝ -
        ∫ t in a..b, ⟪V t, acceleration (leviCivitaConnection I M) γ t⟫_ℝ) / C) 0 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp only [Manifold.pathELength_self, ENNReal.toReal_zero, intervalIntegral.integral_same,
      sub_self, zero_div]
    exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hVu : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc a b) := by
    rwa [uIcc_of_le hab]
  obtain ⟨γ', V', hV', hEq, hExp⟩ := exists_contMDiffAt_exponentialVariation_eqOn γ V hVu
  have hγEq : EqOn γ' γ (Icc a b) := fun r hr ↦
    congrArg TotalSpace.proj (hEq r (by rwa [uIcc_of_le hab]))
  have hspeed' : ∀ t ∈ Icc a b, ‖curveVelocity I γ' t‖ = C := by
    have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    exact norm_curveVelocity_eq_Icc_of_Ioo hlt
      (fun t ht ↦ (contMDiff_proj (TangentSpace I)).contMDiffAt.comp t
        ((hV' t (by rwa [uIcc_of_le hab])).of_le one_le_two))
      fun t ht ↦ by
        rw [(eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2) hγEq).norm_curveVelocity_eq, hspeed t ht]
  have hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ' V' z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t (by rwa [uIcc_of_le hab]))
  have hderiv' : HasDerivAt
      (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ' V' s) a b).toReal)
      ((⟪V' b, curveVelocity I γ' b⟫_ℝ - ⟪V' a, curveVelocity I γ' a⟫_ℝ -
        ∫ t in a..b, ⟪V' t, acceleration (leviCivitaConnection I M) γ' t⟫_ℝ) / C) 0 := by
    have h0 : exponentialVariation I γ' V' 0 = γ' := exponentialVariation_zero γ' V'
    have hVF : ∀ t, HEq (variationField I (exponentialVariation I γ' V') t) (V' t) :=
      fun t ↦ heq_of_eq (variationField_exponentialVariation γ' V' t)
    generalize exponentialVariation I γ' V' = G at hF h0 hVF ⊢
    subst h0
    simpa only [funext fun t ↦ eq_of_heq (hVF t)] using
      hasDerivAt_toReal_pathELength hab hF hC hspeed'
  have hlen : (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal) =
      fun s ↦ (Manifold.pathELength I (exponentialVariation I γ' V' s) a b).toReal :=
    funext fun s ↦ congrArg ENNReal.toReal
      (Manifold.pathELength_congr ((hExp s).mono (by rw [uIcc_of_le hab]))).symm
  rw [hlen]
  refine hderiv'.congr_deriv ?_
  have hb := inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq
    hlt.ne right_mem_uIcc ((hV' b right_mem_uIcc).of_le one_le_two) hEq
  have ha := inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq
    hlt.ne left_mem_uIcc ((hV' a left_mem_uIcc).of_le one_le_two) hEq
  rw [uIcc_of_le hab] at hb ha
  rw [hb, ha, integral_inner_acceleration_eq_of_totalSpaceMk_eq hEq]

end TauCeti.Manifold
