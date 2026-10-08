/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.DirectionalOrder
public import TauCeti.Analysis.Analytic.Complexification.Basic
public import TauCeti.Topology.Algebra.MvPolynomial.Nonvanishing
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Complex preparation of constant real polynomial order

Suppose a real polynomial has constant finite ambient order along a real parametrization.
For any analytic complexification of that parametrization, there is a real affine direction
in which the complex polynomial slices have the same constant order. Evaluation on these
slices is therefore a power of the distinguished coordinate times a complex analytic unit.
The directions can be chosen from an open dense set, with a shared complexification and
a possibly smaller polydisc for each direction. This permits choosing finitely many
preparable slices that also detect ambient order on root sections.
In particular, the real constant-order hypothesis suffices to prepare a discriminant for
complex analytic root splitting; constant order on complex points is a conclusion.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  Sections 2–3.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), §4, Lemma 4.4 and Theorem 4.1.
* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser (2002), Chapter 2.
-/

public section

open Filter Topology

namespace MvPolynomial

variable {σ ι : Type*} [Fintype ι]

/-- A real direction detecting the finite ambient order at the central point also detects
the complex slice order locally along any analytic complexification. -/
theorem eventually_analyticOrderAt_complex_eval_add_smul_eq_of_coeff_ne_zero
    (p : MvPolynomial σ ℝ) (v : σ → ℝ)
    {φ : (ι → ℝ) → σ → ℝ} {Φ : (ι → ℂ) → σ → ℂ}
    {a : ι → ℝ} {m : ℕ}
    (hΦ : ∀ i, AnalyticAt ℂ (fun z ↦ Φ z i) (fun j ↦ (a j : ℂ)))
    (hreal : ∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ))
    (hm : ∀ᶠ x in 𝓝 a, p.orderAt (φ x) = m)
    (hv : (aeval (fun i ↦ Polynomial.C (φ a i) + Polynomial.C (v i) * Polynomial.X)
      p).coeff m ≠ 0) :
    ∀ᶠ z in 𝓝 (fun j ↦ (a j : ℂ)),
      analyticOrderAt (fun t : ℂ ↦
        eval (Φ z + t • (fun i ↦ (v i : ℂ))) (p.map Complex.ofRealHom)) 0 = m := by
  let L (z : ι → ℂ) := aeval
    (fun i ↦ Polynomial.C (Φ z i) + Polynomial.C (v i : ℂ) * Polynomial.X)
    (p.map Complex.ofRealHom)
  have hcoeff (k : ℕ) : AnalyticAt ℂ (fun z ↦ (L z).coeff k)
      (fun j ↦ (a j : ℂ)) :=
    (p.map Complex.ofRealHom).analyticAt_coeff_aeval_C_add_C_mul_X
      (φ := Φ) (ψ := fun _ i ↦ (v i : ℂ)) hΦ
      (fun _ ↦ analyticAt_const) k
  have hmap (x : ι → ℝ) (hx : Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ)) :
      L (fun j ↦ (x j : ℂ)) =
        (aeval (fun i ↦ Polynomial.C (φ x i) + Polynomial.C (v i) * Polynomial.X)
          p).map Complex.ofRealHom := by
    dsimp only [L]
    rw [hx, aeval_def, eval₂_map, ← Polynomial.coe_mapRingHom, map_aeval]
    have hc : (algebraMap ℂ (Polynomial ℂ)).comp Complex.ofRealHom =
        (Polynomial.mapRingHom Complex.ofRealHom).comp (algebraMap ℝ (Polynomial ℝ)) := by
      ext r
      simp
    simp only [hc, coe_eval₂Hom, Polynomial.coe_mapRingHom, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Complex.ofRealHom_eq_coe]
  have hzero (k : Fin m) : ∀ᶠ z in 𝓝 (fun j ↦ (a j : ℂ)), (L z).coeff k = 0 := by
    apply (hcoeff k).eventually_eq_zero_of_eventually_real
    filter_upwards [hreal, hm] with x hx hmx
    rw [hmap x hx, Polynomial.coeff_map]
    have hz := p.coeff_aeval_C_add_C_mul_X_eq_zero (φ x) v
      (m := k) (by simp [hmx])
    simp only [hz, map_zero]
  have hne : (L (fun j ↦ (a j : ℂ))).coeff m ≠ 0 := by
    rw [hmap a hreal.self_of_nhds, Polynomial.coeff_map]
    simpa only [Complex.ofRealHom_eq_coe, Complex.ofReal_ne_zero] using
      hv
  filter_upwards [(hcoeff m).continuousAt.eventually_ne hne,
    Filter.eventually_all.2 hzero] with z hz hzz
  have hnz : L z ≠ 0 := fun h ↦ hz (by simp [h])
  have hord : (L z).natTrailingDegree = m := by
    refine le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hz)
      (Polynomial.le_natTrailingDegree hnz fun k hk ↦ ?_)
    exact hzz ⟨k, hk⟩
  have heval := (p.map Complex.ofRealHom).eval_aeval_C_add_C_mul_X
    (Φ z) (fun i ↦ (v i : ℂ))
  rw [← _root_.funext heval, Polynomial.analyticOrderAt_eval_zero,
    Polynomial.trailingDegree_eq_natTrailingDegree hnz, hord]

/-- Constant real ambient polynomial order gives constant complex slice order along a
real direction, for any analytic complexification of the parametrization. -/
theorem exists_eventually_analyticOrderAt_complex_eval_add_smul_eq
    (p : MvPolynomial σ ℝ) {φ : (ι → ℝ) → σ → ℝ} {Φ : (ι → ℂ) → σ → ℂ}
    {a : ι → ℝ} {m : ℕ}
    (hΦ : ∀ i, AnalyticAt ℂ (fun z ↦ Φ z i) (fun j ↦ (a j : ℂ)))
    (hreal : ∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ))
    (hm : ∀ᶠ x in 𝓝 a, p.orderAt (φ x) = m) :
    ∃ v : σ → ℝ, ∀ᶠ z in 𝓝 (fun j ↦ (a j : ℂ)),
      analyticOrderAt (fun t : ℂ ↦
        eval (Φ z + t • (fun i ↦ (v i : ℂ))) (p.map Complex.ofRealHom)) 0 = m := by
  obtain ⟨v, hn, hv⟩ := p.exists_natTrailingDegree_aeval_C_add_C_mul_X_eq
    (φ a) hm.self_of_nhds
  refine ⟨v, p.eventually_analyticOrderAt_complex_eval_add_smul_eq_of_coeff_ne_zero
    v hΦ hreal hm ?_⟩
  rw [← hv]
  exact Polynomial.coeff_natTrailingDegree_ne_zero.2 hn

/-- A specified real direction detecting the central ambient order gives a complex
power-times-unit factorization along an analytic complexification of the parametrization. -/
theorem exists_analyticAt_complex_eval_add_smul_eq_pow_mul_of_coeff_ne_zero
    (p : MvPolynomial σ ℝ) (v : σ → ℝ)
    {φ : (ι → ℝ) → σ → ℝ} {Φ : (ι → ℂ) → σ → ℂ}
    {a : ι → ℝ} {m : ℕ}
    (hΦ : ∀ i, AnalyticAt ℂ (fun z ↦ Φ z i) (fun j ↦ (a j : ℂ)))
    (hreal : ∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ))
    (hm : ∀ᶠ x in 𝓝 a, p.orderAt (φ x) = m)
    (hv : (aeval (fun i ↦ Polynomial.C (φ a i) + Polynomial.C (v i) * Polynomial.X)
      p).coeff m ≠ 0) :
    ∃ u : (ι → ℂ) × ℂ → ℂ,
      AnalyticAt ℂ u ((fun j ↦ (a j : ℂ)), 0) ∧
      u ((fun j ↦ (a j : ℂ)), 0) ≠ 0 ∧
      ∀ᶠ z in 𝓝 ((fun j ↦ (a j : ℂ)), 0),
        eval (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))) (p.map Complex.ofRealHom) =
          z.2 ^ m * u z := by
  have horder := p.eventually_analyticOrderAt_complex_eval_add_smul_eq_of_coeff_ne_zero
    v hΦ hreal hm hv
  have hG : AnalyticAt ℂ (fun z : (ι → ℂ) × ℂ ↦
      eval (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))) (p.map Complex.ofRealHom))
      ((fun j ↦ (a j : ℂ)), 0) := by
    have hf : AnalyticAt ℂ (fun z : (ι → ℂ) × ℂ ↦ z.1)
        ((fun j ↦ (a j : ℂ)), 0) := analyticAt_fst
    have hs : AnalyticAt ℂ (fun z : (ι → ℂ) × ℂ ↦ z.2)
        ((fun j ↦ (a j : ℂ)), 0) := analyticAt_snd
    have hGa : AnalyticAt ℂ (fun z : (ι → ℂ) × ℂ ↦
        aeval (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))) (p.map Complex.ofRealHom))
        ((fun j ↦ (a j : ℂ)), 0) := by
      apply AnalyticAt.aeval_mvPolynomial
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact ((hΦ i).comp hf).fun_add (hs.fun_mul (analyticAt_const (v := (v i : ℂ))))
    simpa only [aeval_eq_eval] using hGa
  obtain ⟨u, hu, hu0, heq⟩ := hG.eventually_analyticOrderAt_eq_natCast_iff.1 horder
  exact ⟨u, hu, hu0, by simpa only [sub_zero, smul_eq_mul] using heq⟩

/-- Constant finite real order gives a complex power-times-unit factorization along
some real direction, for any analytic complexification of the parametrization. -/
theorem exists_analyticAt_complex_eval_add_smul_eq_pow_mul
    (p : MvPolynomial σ ℝ) {φ : (ι → ℝ) → σ → ℝ} {Φ : (ι → ℂ) → σ → ℂ}
    {a : ι → ℝ} {m : ℕ}
    (hΦ : ∀ i, AnalyticAt ℂ (fun z ↦ Φ z i) (fun j ↦ (a j : ℂ)))
    (hreal : ∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ))
    (hm : ∀ᶠ x in 𝓝 a, p.orderAt (φ x) = m) :
    ∃ v : σ → ℝ, ∃ u : (ι → ℂ) × ℂ → ℂ,
      AnalyticAt ℂ u ((fun j ↦ (a j : ℂ)), 0) ∧
      u ((fun j ↦ (a j : ℂ)), 0) ≠ 0 ∧
      ∀ᶠ z in 𝓝 ((fun j ↦ (a j : ℂ)), 0),
        eval (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))) (p.map Complex.ofRealHom) =
          z.2 ^ m * u z := by
  obtain ⟨v, hn, hv⟩ := p.exists_natTrailingDegree_aeval_C_add_C_mul_X_eq
    (φ a) hm.self_of_nhds
  refine ⟨v, p.exists_analyticAt_complex_eval_add_smul_eq_pow_mul_of_coeff_ne_zero
    v hΦ hreal hm ?_⟩
  rw [← hv]
  exact Polynomial.coeff_natTrailingDegree_ne_zero.2 hn

/-- Constant finite ambient order along a real analytic parametrization admits one
conjugation-compatible complexification and an open dense set of real directions. Every
such direction gives a power-times-unit factorization on a sufficiently small polydisc.
The complexification is shared; the radius and unit may depend on the direction. -/
theorem exists_complexification_dense_open_directions_eval_add_smul_eq_pow_mul [Fintype σ]
    (p : MvPolynomial σ ℝ) {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ} {m : ℕ}
    (hφ : AnalyticAt ℝ φ a) (hm : ∀ᶠ x in 𝓝 a, p.orderAt (φ x) = m) :
    ∃ ρ > (0 : ℝ), ∃ Φ : (ι → ℂ) → σ → ℂ, ∃ V : Set (σ → ℝ),
      IsOpen V ∧ Dense V ∧
      AnalyticOnNhd ℂ Φ (Metric.ball (fun j ↦ (a j : ℂ)) ρ) ∧
      (∀ x ∈ Metric.ball a ρ, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ)) ∧
      (∀ z, Φ (star z) = star (Φ z)) ∧
      ∀ v ∈ V, ∃ r > (0 : ℝ), r ≤ ρ ∧ ∃ u : (ι → ℂ) × ℂ → ℂ,
        AnalyticOnNhd ℂ u
          (Metric.ball (fun j ↦ (a j : ℂ)) r ×ˢ Metric.ball 0 r) ∧
        ∀ z ∈ Metric.ball (fun j ↦ (a j : ℂ)) r ×ˢ Metric.ball 0 r,
          u z ≠ 0 ∧
            eval (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))) (p.map Complex.ofRealHom) =
              z.2 ^ m * u z := by
  obtain ⟨ρ, hρ, Φ, hΦ, hreal, hstar⟩ := hφ.exists_complexification_pi
  let H := homogeneousComponent m (taylor (φ a) p)
  have hH : H ≠ 0 :=
    p.homogeneousComponent_ne_zero_of_orderAt_eq (φ a) hm.self_of_nhds
  let V := {v : σ → ℝ | eval v H ≠ 0}
  have hV : IsOpen V := isOpen_ne.preimage H.continuous_eval
  refine ⟨ρ, hρ, Φ, V, hV, H.dense_setOf_eval_ne_zero hH, hΦ, hreal, hstar, ?_⟩
  intro v hv
  have hc : (aeval (fun i ↦ Polynomial.C (φ a i) + Polynomial.C (v i) * Polynomial.X)
      p).coeff m ≠ 0 := by
    simpa only [V, Set.mem_ofPred_eq, H, coeff_aeval_C_add_C_mul_X] using hv
  have hΦa := hΦ _ (Metric.mem_ball_self hρ)
  have hreal' : ∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ) :=
    Filter.Eventually.mono (Metric.ball_mem_nhds a hρ) hreal
  obtain ⟨u, hu, hu0, heq⟩ :=
    p.exists_analyticAt_complex_eval_add_smul_eq_pow_mul_of_coeff_ne_zero
      v (analyticAt_pi_iff.1 hΦa) hreal' hm hc
  obtain ⟨s, hs, hsu⟩ := Metric.eventually_nhds_iff.1
    (hu.eventually_analyticAt.and ((hu.continuousAt.eventually_ne hu0).and heq))
  have hlocal : ∀ z ∈ Metric.ball (fun j ↦ (a j : ℂ)) (min ρ s) ×ˢ
      Metric.ball 0 (min ρ s), AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
        eval (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))) (p.map Complex.ofRealHom) =
          z.2 ^ m * u z := by
    intro z hz
    have hz' := Metric.ball_subset_ball (min_le_right ρ s)
      (ball_prod_same (fun j ↦ (a j : ℂ)) (0 : ℂ) (min ρ s) ▸ hz)
    exact hsu (by simpa only [Metric.mem_ball, dist_comm] using hz')
  exact ⟨min ρ s, lt_min hρ hs, min_le_left _ _, u,
    fun z hz ↦ (hlocal z hz).1, fun z hz ↦ (hlocal z hz).2⟩

end MvPolynomial
