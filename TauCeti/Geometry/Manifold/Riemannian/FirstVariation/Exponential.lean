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

For a curve `γ` in a smooth boundaryless Riemannian manifold and a tangent field `V` along `γ`
whose lift to the tangent bundle is `C²` on the closed interval `uIcc a b` (or continuous
piecewise `C²` on `Icc a b`), the exponential variation
`TauCeti.Manifold.exponentialVariation I γ V` realizes `V` as the variation field of a family of
curves whose energy can be differentiated at `s = 0`. When `a ≤ b` and `γ` also has constant
positive speed `C > 0` on `(a, b)`,
`TauCeti.Manifold.hasDerivAt_toReal_pathELength_exponentialVariation` differentiates its length
at `s = 0` for any field with a `C²` lift on `[a, b]`. In a boundaryless manifold, because
`TauCeti.Manifold.exists_contMDiffAt_exponentialVariation_eqOn` extends any finite-order
closed-interval `C^k` (`k : ℕ`) section lift to a two-sided `C^k` lift having the same exponential
variation on `uIcc a b`, the smooth formulas require only closed-interval (`ContMDiffOn`)
regularity, and piecewise regularity (`IsPiecewiseContMDiffOn` / `PiecewiseContMDiffSectionAlong`)
suffices to decompose the energy near `s = 0` into piece energies. Obtaining the corner-free
piecewise first variation of energy additionally requires `γ` to be differentiable at every
interior point of `(a, b)` so that the corner pairings cancel, with outer endpoint velocities read
within the closed interval via `curveVelocityWithin`.

## Main results

* `TauCeti.Manifold.eventually_pathELength_exponentialVariation_ne_top`: curves of a `C¹`
  exponential variation have finite Riemannian length near `s = 0`.
* `TauCeti.Manifold.eventually_differentiableAt_energy_exponentialVariation`: energy of a `C²`
  exponential variation is differentiable near `s = 0`.
* `TauCeti.Manifold.hasDerivAt_energy_exponentialVariation`: first variation of energy along an
  exponential variation for a field with a `C²` lift on `uIcc a b`.
* `TauCeti.Manifold.eventually_energy_exponentialVariation_eq_sum`: along a piecewise `C¹`
  partition, the energy of an exponential variation eventually equals the sum of piece energies.
* `TauCeti.Manifold.hasDerivAt_energy_exponentialVariation_of_isPiecewiseContMDiffOn` and
  `TauCeti.Manifold.PiecewiseContMDiffSectionAlong.hasDerivAt_energy_exponentialVariation`:
  first variation of energy along an exponential variation of an unbroken curve for a continuous
  piecewise `C²` field.
* `TauCeti.Manifold.hasDerivAt_toReal_pathELength_exponentialVariation`: first variation of length
  along an exponential variation of a constant-speed curve (`C > 0` on `(a, b)`).

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

omit [I.Boundaryless] [T2Space M] in
/-- Two exponential variations agreeing on `uIcc a b` for every parameter `s` have equal energy
functions `s ↦ energy I (exponentialVariation I _ _ s) a b`. -/
theorem energy_exponentialVariation_eq_of_eqOn {γ' : ℝ → M} {V' : ∀ t, TangentSpace I (γ' t)}
    {a b : ℝ}
    (hExp : ∀ s, EqOn (exponentialVariation I γ' V' s) (exponentialVariation I γ V s) (uIcc a b)) :
    (fun s ↦ energy I (exponentialVariation I γ V s) a b) =
      fun s ↦ energy I (exponentialVariation I γ' V' s) a b :=
  funext fun s ↦ (energy_congr ((hExp s).mono uIoo_subset_uIcc_self)).symm

omit [I.Boundaryless] [T2Space M] in
/-- Two exponential variations agreeing on `uIcc a b` for every parameter `s` have equal extended
Riemannian length functions `s ↦ Manifold.pathELength I (exponentialVariation I _ _ s) a b`. -/
theorem pathELength_exponentialVariation_eq_of_eqOn {γ' : ℝ → M} {V' : ∀ t, TangentSpace I (γ' t)}
    {a b : ℝ}
    (hExp : ∀ s, EqOn (exponentialVariation I γ' V' s) (exponentialVariation I γ V s) (uIcc a b)) :
    (fun s ↦ Manifold.pathELength I (exponentialVariation I γ V s) a b) =
      fun s ↦ Manifold.pathELength I (exponentialVariation I γ' V' s) a b :=
  funext fun s ↦ (Manifold.pathELength_congr ((hExp s).mono Icc_subset_uIcc)).symm

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
  rwa [congrFun (pathELength_exponentialVariation_eq_of_eqOn hExp) s]

/-- For a field `V` along `γ` whose tangent-bundle lift is `C²` on `uIcc a b`, the energy of the
exponential variation `exp_(γ ·) (s • V ·)` between `a` and `b` is differentiable at every `s`
near `0`. -/
theorem eventually_differentiableAt_energy_exponentialVariation {a b : ℝ}
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc a b)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (fun q ↦ energy I (exponentialVariation I γ V q) a b) s := by
  obtain ⟨γ', V', hV', -, hExp⟩ := exists_contMDiffAt_exponentialVariation_eqOn γ V hV
  rw [energy_exponentialVariation_eq_of_eqOn hExp]
  exact eventually_differentiableAt_energy (I := I) (F := exponentialVariation I γ' V') (a := a)
    (b := b) (u := 0) fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t ht)

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
  simp only [curveVelocityLiftWithin_apply] at hvel_lift
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
  · simpa only [energy_def, intervalIntegral.integral_same, zero_div, sub_self] using
      hasDerivAt_const (0 : ℝ) (0 : ℝ)
  obtain ⟨γ', V', hV', hEq, hExp⟩ := exists_contMDiffAt_exponentialVariation_eqOn γ V hV
  have hderiv' : HasDerivAt (fun s ↦ energy I (exponentialVariation I γ' V' s) a b)
      (inner ℝ (V' b) (curveVelocity I γ' b) - inner ℝ (V' a) (curveVelocity I γ' a) -
        ∫ t in a..b, inner ℝ (V' t) (acceleration (leviCivitaConnection I M) γ' t)) 0 := by
    have h := hasDerivAt_energy fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t ht)
    rwa [variationField_exponentialVariation_eq, exponentialVariation_zero] at h
  rw [energy_exponentialVariation_eq_of_eqOn hExp]
  refine hderiv'.congr_deriv ?_
  rw [inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq hab right_mem_uIcc
      ((hV' b right_mem_uIcc).of_le one_le_two) hEq,
    inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq hab left_mem_uIcc
      ((hV' a left_mem_uIcc).of_le one_le_two) hEq,
    integral_inner_acceleration_eq_of_totalSpaceMk_eq hEq]

/-- Along any nondecreasing partition `τ` whose closed subintervals carry a `C¹` tangent-bundle
lift of `V`, the energy of `exp_(γ ·) (s • V ·)` agrees near `s = 0` with the sum of its piece
energies. -/
theorem eventually_energy_exponentialVariation_eq_sum {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hτ : Monotone τ)
    (hpieces : ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (Icc (τ i.castSucc) (τ i.succ))) :
    (fun s ↦ energy I (exponentialVariation I γ V s) (τ 0) (τ (Fin.last n))) =ᶠ[𝓝 0]
      fun s ↦ ∑ i : Fin n,
        energy I (exponentialVariation I γ V s) (τ i.castSucc) (τ i.succ) := by
  have hpi (i : Fin n) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc (τ i.castSucc) (τ i.succ)) := by
    rw [uIcc_of_le (hτ (Fin.castSucc_le_succ i))]; exact hpieces i
  choose γi Vi hVi _ hExpi using
    fun i : Fin n ↦ exists_contMDiffAt_exponentialVariation_eqOn γ V (hpi i)
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  have hsum := eventually_energy_eq_sum_of_piecewise τ hτ
    (F := exponentialVariation I γ V) (G := fun i ↦ exponentialVariation I (γi i) (Vi i))
    (fun i t ht ↦ contMDiffAt_exponentialVariation_zero (γi i) (Vi i)
      (hVi i t (by rwa [uIcc_of_le (hτ (Fin.castSucc_le_succ i))])))
    (Eventually.of_forall fun s i t ht ↦
      (hExpi i s (by rwa [uIcc_of_le (hτ (Fin.castSucc_le_succ i))])).symm)
  filter_upwards [hsum] with s hs
  exact hs.trans (Finset.sum_congr rfl fun i _ ↦
    energy_congr ((hExpi i s).mono uIoo_subset_uIcc_self))

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
  have hτ_mono : Monotone τ := (Fin.strictMono_iff_lt_succ.mpr hτ).monotone
  have hpi (i : Fin (n + 1)) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc (τ i.castSucc) (τ i.succ)) := by
    rw [uIcc_of_le (hτ i).le]; exact hpieces i
  have heq := eventually_energy_exponentialVariation_eq_sum τ hτ_mono
    fun i ↦ (hpieces i).of_le one_le_two
  rw [hτa, hτb] at heq
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    hasDerivAt_energy_exponentialVariation (I := I) (γ := γ) (V := V) (hpi i)
  have hvel (i : Fin (n + 1)) {x : ℝ} (hx : x = τ i.castSucc ∨ x = τ i.succ) :
      curveVelocityWithin I γ (uIcc (τ i.castSucc) (τ i.succ)) x =
        curveVelocityWithin I γ (Icc a b) x := by
    rw [uIcc_of_le (hτ i).le]
    exact curveVelocityWithin_Icc_eq_of_subset (hτ i) (hτa ▸ hτ_mono (Fin.zero_le _))
      (hτb ▸ hτ_mono (Fin.le_last _)) (by rcases hx with rfl | rfl <;> simp [(hτ i).le]) hγ
  choose γi Vi hVi hEqi _ using
    fun i : Fin (n + 1) ↦ exists_contMDiffAt_exponentialVariation_eqOn γ V (hpi i)
  have hint (i : Fin (n + 1)) : IntervalIntegrable
      (fun t ↦ inner ℝ (V t) (acceleration (leviCivitaConnection I M) γ t)) volume
      (τ i.castSucc) (τ i.succ) := by
    have hcont : ContinuousOn (fun t ↦ inner ℝ (Vi i t)
        (acceleration (leviCivitaConnection I M) (γi i) t)) (uIcc (τ i.castSucc) (τ i.succ)) :=
      fun t ht ↦ ((continuousAt_inner_variationField_acceleration
        (contMDiffAt_exponentialVariation_zero (γi i) (Vi i) (hVi i t ht))).congr
          (Eventually.of_forall fun r ↦ TauCeti.inner_eq_of_totalSpaceMk_eq
            (TotalSpace.ext (congrFun (exponentialVariation_zero (γi i) (Vi i)) r)
              (heq_of_eq (variationField_exponentialVariation (γi i) (Vi i) r)))
            ((EventuallyEq.of_eq (exponentialVariation_zero (γi i)
              (Vi i))).totalSpaceMk_acceleration_eq (leviCivitaConnection I M)))).continuousWithinAt
    refine hcont.intervalIntegrable.congr_uIoo fun t ht ↦ ?_
    have hnear : γi i =ᶠ[𝓝 t] γ := eventuallyEq_of_mem
      (mem_of_superset (isOpen_Ioo.mem_nhds ht) uIoo_subset_uIcc_self)
      fun r hr ↦ congrArg TotalSpace.proj (hEqi i r hr)
    exact TauCeti.inner_eq_of_totalSpaceMk_eq (hEqi i t (uIoo_subset_uIcc_self ht))
      (hnear.totalSpaceMk_acceleration_eq (leviCivitaConnection I M))
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  have hsum_int := TauCeti.intervalIntegral.sum_integral_adjacent_intervals_fin τ hint
  have htele := Fin.sum_univ_succ_sub_castSucc
    (fun k ↦ inner ℝ (V (τ k)) (curveVelocityWithin I γ (Icc a b) (τ k)))
  rw [hτa, hτb] at hsum_int htele
  simp only [hvel _ (Or.inl rfl), hvel _ (Or.inr rfl), Finset.sum_sub_distrib, htele, hsum_int]

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
  · simpa only [Manifold.pathELength_self, ENNReal.toReal_zero, intervalIntegral.integral_same,
      sub_self, zero_div] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  obtain ⟨γ', V', hV', hEq, hExp⟩ :=
    exists_contMDiffAt_exponentialVariation_eqOn γ V (by rwa [uIcc_of_le hab])
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hspeed' := norm_curveVelocity_eq_Icc_of_totalSpaceMk_eq one_le_two hlt hV' hEq hspeed
  have hderiv' : HasDerivAt
      (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ' V' s) a b).toReal)
      ((⟪V' b, curveVelocity I γ' b⟫_ℝ - ⟪V' a, curveVelocity I γ' a⟫_ℝ -
        ∫ t in a..b, ⟪V' t, acceleration (leviCivitaConnection I M) γ' t⟫_ℝ) / C) 0 := by
    have h := hasDerivAt_toReal_pathELength hab
      (fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t (by rwa [uIcc_of_le hab])))
      hC (fun t ht ↦ by rw [exponentialVariation_zero]; exact hspeed' t ht)
    rwa [variationField_exponentialVariation_eq, exponentialVariation_zero] at h
  rw [congrArg (fun f s ↦ (f s).toReal) (pathELength_exponentialVariation_eq_of_eqOn hExp)]
  refine hderiv'.congr_deriv ?_
  have hb := inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq
    hlt.ne right_mem_uIcc ((hV' b right_mem_uIcc).of_le one_le_two) hEq
  have ha := inner_curveVelocity_eq_inner_curveVelocityWithin_of_totalSpaceMk_eq
    hlt.ne left_mem_uIcc ((hV' a left_mem_uIcc).of_le one_le_two) hEq
  rw [uIcc_of_le hab] at hb ha
  rw [hb, ha, integral_inner_acceleration_eq_of_totalSpaceMk_eq hEq]

end TauCeti.Manifold
