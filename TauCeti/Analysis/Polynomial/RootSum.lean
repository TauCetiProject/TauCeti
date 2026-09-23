/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Analysis.Polynomial.SymmetricPower
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Units
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Holomorphic functions summed over the roots of a polynomial

Let `g` be holomorphic near the roots of a monic complex polynomial `P₀`. This file proves that the
sum `∑ g(z)` over the roots `z` of a monic polynomial `P`, counted with multiplicity, depends
analytically on the coefficients of `P` near those of `P₀`, **with no assumption that the roots of
`P₀` are distinct**. By Newton's identities the same then holds for the elementary symmetric
functions of the values `g(z)`, that is, for the coefficients of `∏ (X - g(z))`.

Read through the elementary symmetric chart `TauCeti.Sym.coeffEquiv`, which identifies `Sym^n ℂ`
with `Fin n → ℂ`, this says that a holomorphic change of coordinate `φ` acts analytically on
elementary symmetric coordinates everywhere, including along the diagonal where points collide:
`TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm_of_analyticAt`. This is what makes the
transition maps of the elementary symmetric atlas on the symmetric power of a Riemann surface
holomorphic (Ozsváth--Szabó, [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1). At
tuples of distinct points the same conclusion is
`TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm`, obtained there from the implicit function
theorem, which is unavailable once roots collide.

## The argument

Around each distinct root `w` of `P₀` choose a small circle `C(w, r)`, the closed discs being
pairwise disjoint and inside the region where `g` is holomorphic. By the argument principle weighted
by `g` (Ahlfors, *Complex Analysis*, Ch. 4, §5.2),

`(2πi)⁻¹ ∮_{C(w, r)} g(t) P'(t) / P(t) dt = ∑_{z root of P, |z - w| < r} g(z)`,

and for `P` near `P₀` every root of `P` lies in one of the discs, by continuity of the roots
(`TauCeti.Sym.coeffHomeomorph`). Summing over `w` expresses `∑ g(z)` as a finite sum of contour
integrals. Each of these is analytic in the coefficients `c` of `P`: restricted to the circle, `P`
and `P'` are affine functions of `c` with values in the Banach algebra `C(sphere w r, ℂ)`, `P₀` is
a unit there since it does not vanish on the circle, inversion is analytic on the units of a
Banach algebra (`analyticAt_inverse`), and integration over the circle is a continuous linear
functional on `C(sphere w r, ℂ)`.

## Main results

* `Polynomial.circleIntegral_mul_derivative_div_eval`: the argument principle for a polynomial,
  weighted by a holomorphic function.
* `TauCeti.Polynomial.analyticAt_circleIntegral_mul_derivative_div_monicOfCoeff`: such a contour
  integral depends analytically on the coefficients of a monic polynomial not vanishing on the
  circle.
* `TauCeti.analyticAt_esymm_of_forall_analyticAt_sum_map_pow`: analyticity passes from the power
  sums of a family of multisets to its elementary symmetric functions.
* `TauCeti.Sym.analyticAt_sum_map_coeffEquiv_symm`: **sums of a holomorphic function over the
  roots are analytic in the coefficients**, colliding roots included.
* `TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm_of_analyticAt`: **a holomorphic
  coordinate change acts analytically on elementary symmetric coordinates**, colliding points
  included.
-/

public section

open Complex Filter Metric Polynomial Real Topology

namespace TauCeti

namespace Polynomial

section Linear

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

/-- The image of the monic polynomial with lower coefficients `c` under a linear map depends
analytically on `c`: it is affine in `c`. -/
private theorem analyticAt_linearMap_monicOfCoeff (Λ : 𝕜[X] →ₗ[𝕜] F) (c₀ : Fin n → 𝕜) :
    AnalyticAt 𝕜 (fun c => Λ (monicOfCoeff c)) c₀ := by
  have h : (fun c : Fin n → 𝕜 => Λ (monicOfCoeff c)) =
      fun c => Λ (X ^ n) + ∑ i : Fin n, c i • Λ (monomial (i : ℕ) 1) := by
    funext c
    have hp : monicOfCoeff c = X ^ n + ∑ i : Fin n, c i • monomial (i : ℕ) (1 : 𝕜) :=
      Polynomial.funext fun z => by
        simp [eval_monicOfCoeff, eval_finsetSum, smul_monomial]
    simp [hp, map_sum, map_smul]
  rw [h]
  exact analyticAt_const.add (Finset.univ.analyticAt_fun_sum fun i _ =>
    ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).analyticAt c₀).smul
      analyticAt_const)

end Linear

section Circle

variable {w : ℂ} {r : ℝ}

/-- The circle `C(w, r)` as a continuous map into the sphere it parametrizes. -/
private noncomputable def sphereCircleMap (w : ℂ) {r : ℝ} (hr : 0 ≤ r) : C(ℝ, sphere w r) :=
  ⟨fun θ => ⟨circleMap w r θ, circleMap_mem_sphere w hr θ⟩,
    (continuous_circleMap w r).subtype_mk _⟩

private theorem coe_sphereCircleMap (hr : 0 ≤ r) (θ : ℝ) :
    (sphereCircleMap w hr θ : ℂ) = circleMap w r θ :=
  rfl

/-- Integration over the circle `C(w, r)`, as a continuous linear functional on the continuous
functions on the sphere. -/
private noncomputable def sphereIntegral (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    C(sphere w r, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ θ in 0..2 * π, circleMap 0 r θ * I * f (sphereCircleMap w hr θ)
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, mul_add]
        exact intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _)
          ((by fun_prop : Continuous _).intervalIntegrable _ _)
      map_smul' := fun a f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ a]
        exact intervalIntegral.integral_const_mul a _ }
    (r * (2 * π)) fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc _ ≤ r * ‖f‖ * |2 * π - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => by
              rw [norm_mul, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_nonneg hr]
              exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) hr
        _ = r * (2 * π) * ‖f‖ := by
            rw [sub_zero, abs_of_pos two_pi_pos]
            ring

/-- `sphereIntegral` computes the circle integral of any function agreeing with its argument on the
sphere. -/
private theorem sphereIntegral_apply (hr : 0 ≤ r) {f : C(sphere w r, ℂ)} {F : ℂ → ℂ}
    (hF : ∀ t : sphere w r, f t = F t) : sphereIntegral w hr f = ∮ t in C(w, r), F t := by
  simp only [sphereIntegral, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    circleIntegral, deriv_circleMap, smul_eq_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [hF, coe_sphereCircleMap]

variable {n : ℕ}

/-- **Contour integrals against the logarithmic derivative of a monic polynomial depend
analytically on its coefficients.** If the monic polynomial with lower coefficients `c₀` does not
vanish on the circle `C(w, r)`, and `g` is continuous there, then
`c ↦ ∮_{C(w, r)} g(t) P_c'(t) / P_c(t) dt`, where `P_c` is the monic polynomial with lower
coefficients `c`, is analytic at `c₀`. -/
theorem analyticAt_circleIntegral_mul_derivative_div_monicOfCoeff {g : ℂ → ℂ} (hr : 0 ≤ r)
    (hg : ContinuousOn g (sphere w r)) {c₀ : Fin n → ℂ}
    (hc₀ : ∀ t ∈ sphere w r, (monicOfCoeff c₀).eval t ≠ 0) :
    AnalyticAt ℂ (fun c => ∮ t in C(w, r),
      g t * ((monicOfCoeff c).derivative.eval t / (monicOfCoeff c).eval t)) c₀ := by
  -- Restricted to the sphere, `P_c` and `P_c'` are affine in `c`, with values in the Banach
  -- algebra `C(sphere w r, ℂ)`, where `P_{c₀}` is a unit.
  let Λ : ℂ[X] →ₗ[ℂ] C(sphere w r, ℂ) := (toContinuousMapOnAlgHom (sphere w r)).toLinearMap
  let B : (Fin n → ℂ) → C(sphere w r, ℂ) := fun c => Λ (monicOfCoeff c)
  let D : (Fin n → ℂ) → C(sphere w r, ℂ) := fun c => (Λ ∘ₗ derivative) (monicOfCoeff c)
  let G : C(sphere w r, ℂ) := ⟨fun t => g t, continuousOn_iff_continuous_domRestrict.1 hg⟩
  have hB : AnalyticAt ℂ B c₀ := analyticAt_linearMap_monicOfCoeff Λ c₀
  have hD : AnalyticAt ℂ D c₀ := analyticAt_linearMap_monicOfCoeff _ c₀
  have hunit : IsUnit (B c₀) :=
    (ContinuousMap.isUnit_iff_forall_ne_zero _).2 fun t => by simpa [B, Λ] using hc₀ t t.2
  have hinv : AnalyticAt ℂ (fun c => Ring.inverse (B c)) c₀ := by
    have h := analyticAt_inverse (𝕜 := ℂ) hunit.unit
    rw [hunit.unit_spec] at h
    exact h.comp hB
  refine ((sphereIntegral w hr).analyticAt _ |>.comp
    (analyticAt_const (v := G) |>.mul (hD.mul hinv))).congr ?_
  -- Near `c₀`, `B c` is still a unit, and its inverse is computed pointwise.
  filter_upwards [hB.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit)] with c hc
  refine sphereIntegral_apply hr fun t => ?_
  have hinvt : Ring.inverse (B c) t = (B c t)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← ContinuousMap.mul_apply, Ring.inverse_mul_cancel _ hc, ContinuousMap.one_apply]
  rw [Pi.mul_apply, Pi.mul_apply, ContinuousMap.mul_apply, ContinuousMap.mul_apply, hinvt]
  have hG : G t = g t := rfl
  simp [hG, D, B, Λ, div_eq_mul_inv]

end Circle

end Polynomial

section Trace

variable {w : ℂ} {r : ℝ} {g : ℂ → ℂ}

open scoped Classical in
/-- The Cauchy integral formula, summed over a multiset of points off the circle `C(w, r)`: the
points inside contribute `2πi g(z)`, those outside nothing. -/
private theorem circleIntegral_sum_map_inv_sub_mul (hr : 0 < r) (hg : DiffContOnCl ℂ g (ball w r))
    (m : Multiset ℂ) (hm : ∀ z ∈ m, z ∉ sphere w r) :
    CircleIntegrable (fun t => (m.map fun z => (t - z)⁻¹ * g t).sum) w r ∧
      ∮ t in C(w, r), (m.map fun z => (t - z)⁻¹ * g t).sum =
        2 * π * I * ((m.filter (· ∈ ball w r)).map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [circleIntegrable_const, circleIntegral]
  | cons z m ih =>
    obtain ⟨hint, heq⟩ := ih fun y hy => hm y (Multiset.mem_cons_of_mem hy)
    have hz : z ∉ sphere w r := hm z (Multiset.mem_cons_self z m)
    have hgc : ContinuousOn g (sphere w r) :=
      hg.continuousOn.mono (closure_ball w hr.ne' ▸ sphere_subset_closedBall)
    have hzint : CircleIntegrable (fun t => (t - z)⁻¹ * g t) w r :=
      ((continuousOn_id.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.2 (ne_of_mem_of_not_mem ht hz))).mul hgc |>.circleIntegrable hr.le
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons]
    refine ⟨hzint.add hint, ?_⟩
    rw [circleIntegral.integral_add hzint hint, heq]
    by_cases hzb : z ∈ ball w r
    · have hcauchy := hg.circleIntegral_sub_inv_smul hzb
      simp only [smul_eq_mul] at hcauchy
      simp [hzb, hcauchy, mul_add]
    · have hzc : z ∉ closedBall w r := by
        rw [← ball_union_sphere]
        exact fun h => h.elim hzb hz
      have hdiff : DiffContOnCl ℂ (fun t => (t - z)⁻¹) (ball w r) := by
        refine DifferentiableOn.diffContOnCl ?_
        rw [closure_ball w hr.ne']
        exact (differentiableOn_id.sub_const z).inv fun t ht =>
          sub_ne_zero.2 (ne_of_mem_of_not_mem ht hzc)
      have hzero := DiffContOnCl.circleIntegral_eq_zero hr.le (hdiff.smul hg)
      simp only [smul_eq_mul] at hzero
      simp [hzb, hzero]

open scoped Classical in
/-- **The argument principle for a polynomial, weighted by a holomorphic function.** If `g` is
holomorphic on the disc `ball w r` and continuous up to its boundary, and no root of `p` lies on the
circle `C(w, r)`, then integrating `g` against the logarithmic derivative `p' / p` over the circle
gives `2πi` times the sum of the values of `g` at the roots of `p` inside, counted with
multiplicity. -/
theorem _root_.Polynomial.circleIntegral_mul_derivative_div_eval (p : ℂ[X]) (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (ball w r)) (hp : ∀ z ∈ p.roots, z ∉ sphere w r) :
    ∮ t in C(w, r), g t * (p.derivative.eval t / p.eval t) =
      2 * π * I * ((p.roots.filter (· ∈ ball w r)).map g).sum := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [circleIntegral]
  rw [← (circleIntegral_sum_map_inv_sub_mul hr hg p.roots hp).2]
  refine circleIntegral.integral_congr hr.le fun t ht => ?_
  have hpt : p.eval t ≠ 0 := fun h => hp t ((mem_roots hp0).2 h) ht
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpt, ← Multiset.sum_map_mul_left]
  simp [mul_comm]

end Trace

section Esymm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- If every power sum of positive degree of a family of multisets depends analytically on the
parameter, then so does every elementary symmetric function, by Newton's identities. -/
theorem analyticAt_esymm_of_forall_analyticAt_sum_map_pow {m : E → Multiset 𝕜} {x₀ : E}
    (h : ∀ j, 0 < j → AnalyticAt 𝕜 (fun x => ((m x).map (· ^ j)).sum) x₀) (k : ℕ) :
    AnalyticAt 𝕜 (fun x => (m x).esymm k) x₀ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [Multiset.esymm] using analyticAt_const
    have hrec : (fun x => (m x).esymm k) = fun x => (k : 𝕜)⁻¹ * ((-1) ^ (k + 1) *
        ∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1) ^ a.1 * (m x).esymm a.1 * ((m x).map (· ^ a.2)).sum) := by
      funext x
      rw [← Multiset.mul_esymm_eq_sum, inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hk.ne')]
    rw [hrec]
    refine analyticAt_const.mul <| analyticAt_const.mul <|
      Finset.analyticAt_fun_sum _ fun a ha => ?_
    obtain ⟨ha, hak⟩ := Finset.mem_filter.1 ha
    have ha2 : 0 < a.2 := by
      have := Finset.mem_antidiagonal.1 ha
      omega
    exact (analyticAt_const.mul (ih a.1 hak)).mul (h a.2 ha2)

end Esymm

namespace Sym

section Separated

variable {T : Finset ℂ} {r : ℝ}

/-- Around finitely many points, discs of a small enough radius lie in any prescribed common
neighbourhood and are pairwise far apart. -/
private theorem exists_pos_closedBall_subset_and_lt_dist {U : Set ℂ} (hU : ∀ w ∈ T, U ∈ 𝓝 w) :
    ∃ r > 0, (∀ w ∈ T, closedBall w r ⊆ U) ∧ ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' := by
  have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, closedBall w r ⊆ U :=
    (eventually_all_finset T).2 fun w hw => eventually_closedBall_subset (hU w hw)
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w' := by
    refine (eventually_all_finset T).2 fun w _ => (eventually_all_finset T).2 fun w' _ => ?_
    have hlim : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) :=
      (by fun_prop : Continuous fun r : ℝ => 2 * r).tendsto' 0 0 (mul_zero 2)
    by_cases hww : w = w'
    · exact Eventually.of_forall fun _ h => absurd hww h
    · exact (hlim.eventually (gt_mem_nhds (dist_pos.2 hww))).mono fun _ h _ => h
  obtain ⟨r, ⟨h1r, h2r⟩, hr⟩ :=
    (((h1.and h2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists
      (f := 𝓝[>] (0 : ℝ))
  exact ⟨r, hr, h1r, h2r⟩

variable (hsep : ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → 2 * r < dist w w')
include hsep

/-- A point of one of the separated discs lies on none of their boundary circles. -/
private theorem notMem_sphere_of_mem_ball {z w w' : ℂ} (hw : w ∈ T) (hw' : w' ∈ T)
    (hz : z ∈ ball w' r) : z ∉ sphere w r := by
  intro hzs
  rw [mem_sphere] at hzs
  rw [mem_ball] at hz
  rcases eq_or_ne w w' with rfl | hww
  · exact hz.ne hzs
  · have := hsep w hw w' hw' hww
    have := dist_triangle_left w w' z
    linarith

/-- A point lies in at most one of the separated discs. -/
private theorem eq_of_mem_ball_of_mem_ball {z w w' : ℂ} (hw : w ∈ T) (hw' : w' ∈ T)
    (hzw : z ∈ ball w r) (hzw' : z ∈ ball w' r) : w = w' := by
  by_contra hww
  have := hsep w hw w' hw' hww
  have := dist_triangle_left w w' z
  rw [mem_ball] at hzw hzw'
  linarith

open scoped Classical in
/-- A sum over a multiset of points of the separated discs splits as a sum over the discs. -/
private theorem sum_sum_map_filter_mem_ball (g : ℂ → ℂ) {m : Multiset ℂ}
    (hm : ∀ z ∈ m, ∃ w ∈ T, z ∈ ball w r) :
    ∑ w ∈ T, ((m.filter (· ∈ ball w r)).map g).sum = (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons z m ih =>
    obtain ⟨w₀, hw₀, hzw₀⟩ := hm z (Multiset.mem_cons_self z m)
    simp only [Multiset.filter_cons, Multiset.map_add, Multiset.sum_add, Finset.sum_add_distrib,
      Multiset.map_cons, Multiset.sum_cons]
    rw [ih fun y hy => hm y (Multiset.mem_cons_of_mem hy),
      Finset.sum_eq_single_of_mem w₀ hw₀ fun w hw hne => ?_]
    · simp [hzw₀]
    · have hzw : z ∉ ball w r := fun h => hne (eq_of_mem_ball_of_mem_ball hsep hw hw₀ h hzw₀)
      simp [hzw]

end Separated

variable {n : ℕ}

/-- **Sums of a holomorphic function over the roots depend analytically on the coefficients.**
If `g` is holomorphic at every point of the unordered tuple with elementary symmetric coordinates
`c₀`, then `c ↦ ∑ g(z)`, the sum running over the points `z` of the tuple with coordinates `c`,
counted with multiplicity, is analytic at `c₀`. No distinctness is assumed: the points of the tuple
may collide. -/
theorem analyticAt_sum_map_coeffEquiv_symm {g : ℂ → ℂ} {c₀ : Fin n → ℂ}
    (hg : ∀ z ∈ (coeffEquiv ℂ n).symm c₀, AnalyticAt ℂ g z) :
    AnalyticAt ℂ (fun c => (((coeffEquiv ℂ n).symm c : Multiset ℂ).map g).sum) c₀ := by
  classical
  set T := ((coeffEquiv ℂ n).symm c₀ : Multiset ℂ).toFinset
  have hmemT : ∀ z, z ∈ T ↔ z ∈ (coeffEquiv ℂ n).symm c₀ := fun z =>
    Multiset.mem_toFinset.trans _root_.Sym.mem_coe
  -- Separated discs `ball w r` about the distinct points `w` of the tuple, on whose closures `g`
  -- is holomorphic.
  obtain ⟨r, hr, hrU, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist (T := T)
    (U := {z | AnalyticAt ℂ g z}) fun w hw =>
      (isOpen_analyticAt ℂ g).mem_nhds (hg w ((hmemT w).1 hw))
  have hgd : ∀ w ∈ T, DifferentiableOn ℂ g (closedBall w r) := fun w hw z hz =>
    (hrU w hw hz).differentiableAt.differentiableWithinAt
  set V := ⋃ w ∈ T, ball w r
  have hV : ∀ z ∈ V, ∃ w ∈ T, z ∈ ball w r := fun z hz => by simpa [V] using hz
  -- Near `c₀`, every point of the tuple lies in one of the discs.
  have hN : ∀ᶠ c in 𝓝 c₀, ∀ z ∈ (coeffEquiv ℂ n).symm c, z ∈ V := by
    have hcont : ContinuousAt (fun c => (coeffEquiv ℂ n).symm c) c₀ := by
      have h : (fun c => (coeffEquiv ℂ n).symm c) = (coeffHomeomorph ℂ n).symm :=
        funext fun c => (coeffHomeomorph_symm_apply ℂ n c).symm
      rw [h]
      exact (coeffHomeomorph ℂ n).symm.continuous.continuousAt
    refine hcont.preimage_mem_nhds ((isOpen_setOf_forall_mem (n := n) ?_).mem_nhds
      fun z hz => ?_)
    · exact isOpen_biUnion fun _ _ => isOpen_ball
    · exact Set.mem_iUnion₂.2 ⟨z, (hmemT z).2 hz, mem_ball_self hr⟩
  -- There, the sum over the tuple is a sum of contour integrals, one about each disc.
  have hsum : ∀ᶠ c in 𝓝 c₀, ∑ w ∈ T, (2 * π * I)⁻¹ * ∮ t in C(w, r),
      g t * ((Polynomial.monicOfCoeff c).derivative.eval t / (Polynomial.monicOfCoeff c).eval t) =
      (((coeffEquiv ℂ n).symm c : Multiset ℂ).map g).sum := by
    filter_upwards [hN] with c hc
    have hc' : ∀ z ∈ (Polynomial.monicOfCoeff c).roots, z ∈ V := fun z hz =>
      hc z (by rwa [← _root_.Sym.mem_coe, coeffEquiv_symm_apply])
    rw [coeffEquiv_symm_apply, ← sum_sum_map_filter_mem_ball hsep g fun z hz => hV z (hc' z hz)]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hgw : DiffContOnCl ℂ g (ball w r) :=
      ((hgd w hw).mono (closure_ball w hr.ne').subset).diffContOnCl
    rw [Polynomial.circleIntegral_mul_derivative_div_eval _ hr hgw fun z hz => by
        obtain ⟨w', hw', hzw'⟩ := hV z (hc' z hz)
        exact notMem_sphere_of_mem_ball hsep hw hw' hzw',
      inv_mul_cancel_left₀ two_pi_I_ne_zero]
  -- Each contour integral is analytic in the coefficients.
  refine AnalyticAt.congr (Finset.analyticAt_fun_sum T fun w hw => analyticAt_const.mul
    (Polynomial.analyticAt_circleIntegral_mul_derivative_div_monicOfCoeff hr.le
      ((hgd w hw).mono sphere_subset_closedBall).continuousOn fun t ht h0 => ?_)) hsum
  have ht0 : t ∈ T := by
    rw [hmemT, ← _root_.Sym.mem_coe, coeffEquiv_symm_apply,
      mem_roots (Polynomial.monic_monicOfCoeff c₀).ne_zero]
    exact h0
  exact notMem_sphere_of_mem_ball hsep hw ht0 (mem_ball_self hr) ht

/-- **A holomorphic coordinate change acts analytically on elementary symmetric coordinates, also
where points collide.** A map `φ` of `ℂ` induces a map of coefficient tuples, sending the lower
coefficients of a monic polynomial to those of the monic polynomial whose roots are the `φ`-images
of its roots. This induced map is analytic at every coefficient tuple `c₀` at each of whose roots
`φ` is analytic, whether or not those roots are distinct.

Read on the symmetric power of a Riemann surface, `φ` is a change of holomorphic coordinate, and
this is the holomorphy of the corresponding transition map of elementary symmetric charts. -/
theorem analyticAt_coeffEquiv_map_coeffEquiv_symm_of_analyticAt {φ : ℂ → ℂ} {c₀ : Fin n → ℂ}
    (hφ : ∀ z ∈ (coeffEquiv ℂ n).symm c₀, AnalyticAt ℂ φ z) :
    AnalyticAt ℂ (fun c => coeffEquiv ℂ n (_root_.Sym.map φ ((coeffEquiv ℂ n).symm c))) c₀ := by
  have hpow (j : ℕ) (_ : 0 < j) : AnalyticAt ℂ
      (fun c => (((((coeffEquiv ℂ n).symm c : Multiset ℂ)).map φ).map (· ^ j)).sum) c₀ := by
    simpa only [Multiset.map_map, Function.comp_def] using
      analyticAt_sum_map_coeffEquiv_symm fun z hz => (hφ z hz).fun_pow j
  refine AnalyticAt.pi fun i => ?_
  simp only [coeffEquiv_apply, _root_.Sym.coe_map]
  exact analyticAt_const.mul (analyticAt_esymm_of_forall_analyticAt_sum_map_pow hpow _)

end Sym

end TauCeti
