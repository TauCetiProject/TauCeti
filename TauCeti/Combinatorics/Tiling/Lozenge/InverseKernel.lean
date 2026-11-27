/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Integrable
public import TauCeti.Combinatorics.Tiling.Lozenge.Lattice
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The kernel `G_w` inverts the Kasteleyn matrix of the plane

For liquid type weights `w = (w₁, w₂, w₃)`, the kernel
`G_w(d) = (4π²)⁻¹ ∫∫_{[0,2π]²} e^{i(d₁θ + d₂φ)} / P_w(θ, φ) dθ dφ` (`TauCeti.lozengeKernel`)
satisfies `w₃ G_w(d) + w₂ G_w(d + e₁) + w₁ G_w(d − e₂) = [d = 0]`
(`TauCeti.IsLiquidWeights.lozengeKernel_three_term`, and
`TauCeti.lozengeKernel_three_term_of_integrableOn` whenever `1 / P_w` is integrable on the torus
and `P_w ≠ 0` almost everywhere on it): the three terms combine the integrands
into `e^{i(d₁θ + d₂φ)} P_w / P_w`, which is `e^{i(d₁θ + d₂φ)}` off the zeros of `P_w`, a countable
and hence null set, and the Fourier integral of that exponential over the torus is `4π² [d = 0]`.

The Kasteleyn matrix of the plane has an entry `w_k` at `(W(u), B(v'))` when the two faces share
an edge of direction `k`, and `0` otherwise. The white face `W(u)` meets the black faces across
its three edges `W(u).edge k` (`TauCeti.TriFace.edge`), and the black face `B(v'')` the white
faces across its three edges. So the three-term identity says that
`K⁻¹_∞(B(v'), W(v)) = G_w(v' − v)` is a two-sided inverse of the Kasteleyn matrix:
`Σ_{v'} K(W(u), B(v')) G_w(v' − v) = [u = v]` (`TauCeti.IsLiquidWeights.sum_edge_lozengeKernel`)
and `Σ_u G_w(v' − u) K(W(u), B(v'')) = [v' = v'']`
(`TauCeti.IsLiquidWeights.sum_lozengeKernel_edge`), each sum running over the three edges of
the fixed face.

The orthogonality relation used is `∫∫_{(0,2π]²} e^{i(d₁θ + d₂φ)} dθ dφ = 4π² [d = 0]`
(`TauCeti.setIntegral_cexp_intCast_mul_add_intCast_mul_mul_I`).

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Theorem 4.11.
* R. Kenyon, *Local statistics of lattice dimers*, Ann. Inst. H. Poincaré Probab. Statist. 33
  (1997).
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009),
  Section 6.1.
* R. Kenyon, A. Okounkov, S. Sheffield, *Dimers and amoebae*, Ann. of Math. 163 (2006),
  Theorem 4.3.
-/

public section

noncomputable section

open Complex Set MeasureTheory

namespace TauCeti

variable {w₁ w₂ w₃ : ℝ}

/-- For liquid weights `P_w` is almost everywhere nonzero on `ℝ²`: its zeros form a countable
set. -/
theorem IsLiquidWeights.ae_lozengeCharFun_ne_zero (hw : IsLiquidWeights w₁ w₂ w₃) :
    ∀ᵐ p : ℝ × ℝ, lozengeCharFun w₁ w₂ w₃ p.1 p.2 ≠ 0 := by
  set θ₀ := lozengeZeroAngleFst w₁ w₂ w₃
  set φ₀ := lozengeZeroAngleSnd w₁ w₂ w₃
  have hsub : {p : ℝ × ℝ | lozengeCharFun w₁ w₂ w₃ p.1 p.2 = 0} ⊆
      range fun x : ℤ × ℤ × Bool =>
        if x.2.2 then (2 * x.1 * Real.pi + θ₀, 2 * x.2.1 * Real.pi + φ₀)
        else (2 * x.1 * Real.pi - θ₀, 2 * x.2.1 * Real.pi - φ₀) := by
    rintro ⟨θ, φ⟩ hp
    obtain ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (lozengeCharFun_eq_zero_iff hw).1 hp
    · exact ⟨(m, n, true), rfl⟩
    · exact ⟨(m, n, false), rfl⟩
  exact ((countable_range _).mono hsub).ae_notMem ((volume : Measure ℝ).prod volume)

/-- Off the zeros of `P_w`, the integrands of `G_w(d)`, `G_w(d + e₁)` and `G_w(d − e₂)` combine
with the weights `w₃`, `w₂`, `w₁` into `e^{i(d₁θ + d₂φ)}`. -/
private theorem lozengeKernel_integrand_three_term (d : ℤ × ℤ) {p : ℝ × ℝ}
    (hp : lozengeCharFun w₁ w₂ w₃ p.1 p.2 ≠ 0) :
    (w₃ : ℂ) * (exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2) +
        w₂ * (exp (((d + (1, 0)).1 * p.1 + (d + (1, 0)).2 * p.2 : ℝ) * I) /
          lozengeCharFun w₁ w₂ w₃ p.1 p.2) +
        w₁ * (exp (((d - (0, 1)).1 * p.1 + (d - (0, 1)).2 * p.2 : ℝ) * I) /
          lozengeCharFun w₁ w₂ w₃ p.1 p.2) =
      exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) := by
  set E := exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I)
  have e1 : exp (((d + (1, 0)).1 * p.1 + (d + (1, 0)).2 * p.2 : ℝ) * I) = E * exp (p.1 * I) := by
    rw [← exp_add]; congr 1; simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring
  have e2 : exp (((d - (0, 1)).1 * p.1 + (d - (0, 1)).2 * p.2 : ℝ) * I) =
      E * exp (-(p.2 * I)) := by
    rw [← exp_add]; congr 1; simp only [Prod.fst_sub, Prod.snd_sub]; push_cast; ring
  rw [e1, e2, ← div_mul_cancel₀ E hp]
  rw [lozengeCharFun_def] at hp ⊢
  field_simp

/-- Whenever `1 / P_w` is integrable on the torus, a combination `a G_w(d₀) + b G_w(d₁) + c G_w(d₂)`
is `(4π²)⁻¹` times the integral of the same combination of the integrands. -/
private theorem lozengeKernel_linear_combination
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)))
    (a b c : ℂ) (d₀ d₁ d₂ : ℤ × ℤ) :
    a * lozengeKernel w₁ w₂ w₃ d₀ + b * lozengeKernel w₁ w₂ w₃ d₁ +
        c * lozengeKernel w₁ w₂ w₃ d₂ =
      ((4 * Real.pi ^ 2)⁻¹ : ℝ) • ∫ p in Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi),
        (a * (exp ((d₀.1 * p.1 + d₀.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2) +
          b * (exp ((d₁.1 * p.1 + d₁.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2) +
          c * (exp ((d₂.1 * p.1 + d₂.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2)) := by
  have hint := integrableOn_lozengeKernel_integrand_of_integrableOn hP
  rw [integral_add (((hint d₀).const_mul a).fun_add ((hint d₁).const_mul b))
      ((hint d₂).const_mul c), integral_add ((hint d₀).const_mul a) ((hint d₁).const_mul b),
    integral_const_mul, integral_const_mul, integral_const_mul]
  simp only [lozengeKernel_def, real_smul]
  ring

/-- **The three-term identity**, for any type weights for which `1 / P_w` is integrable on the
torus and `P_w` is almost everywhere nonzero there: liquid weights, but also the frozen weights
`(1, 1, 3)`, where `P_w` does not vanish. For `d ∈ ℤ²`,
`w₃ G_w(d) + w₂ G_w(d + e₁) + w₁ G_w(d − e₂) = [d = 0]`. -/
theorem lozengeKernel_three_term_of_integrableOn
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)))
    (hP₀ : ∀ᵐ p ∂volume.restrict (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)),
      lozengeCharFun w₁ w₂ w₃ p.1 p.2 ≠ 0) (d : ℤ × ℤ) :
    (w₃ : ℂ) * lozengeKernel w₁ w₂ w₃ d + w₂ * lozengeKernel w₁ w₂ w₃ (d + (1, 0)) +
        w₁ * lozengeKernel w₁ w₂ w₃ (d - (0, 1)) =
      if d = 0 then 1 else 0 := by
  rw [lozengeKernel_linear_combination hP,
    integral_congr_ae (hP₀.mono fun p hp => lozengeKernel_integrand_three_term d hp),
    setIntegral_cexp_intCast_mul_add_intCast_mul_mul_I]
  split_ifs
  · rw [real_smul]
    push_cast
    field_simp
  · exact smul_zero _

/-- **The three-term identity.** For liquid weights and `d ∈ ℤ²`,
`w₃ G_w(d) + w₂ G_w(d + e₁) + w₁ G_w(d − e₂) = [d = 0]`. -/
theorem IsLiquidWeights.lozengeKernel_three_term (hw : IsLiquidWeights w₁ w₂ w₃) (d : ℤ × ℤ) :
    (w₃ : ℂ) * lozengeKernel w₁ w₂ w₃ d + w₂ * lozengeKernel w₁ w₂ w₃ (d + (1, 0)) +
        w₁ * lozengeKernel w₁ w₂ w₃ (d - (0, 1)) =
      if d = 0 then 1 else 0 :=
  lozengeKernel_three_term_of_integrableOn hw.integrableOn_inv_lozengeCharFun
    (ae_restrict_of_ae hw.ae_lozengeCharFun_ne_zero) d

/-- **`G_w` is a right inverse of the Kasteleyn matrix.** For liquid weights, summing
`K(W(u), B(v')) G_w(v' − v)` over the three black faces `B(v')` adjacent to `W(u)`, across the
edges `W(u).edge k` of weight `w_k`, gives `[u = v]`. -/
theorem IsLiquidWeights.sum_edge_lozengeKernel (hw : IsLiquidWeights w₁ w₂ w₃)
    (u v : ℤ × ℤ) :
    ∑ k : Fin 3, (![w₁, w₂, w₃] k : ℂ) *
        lozengeKernel w₁ w₂ w₃ ((TriFace.edge ⟨u, true⟩ k).blackFace.v - v) =
      if u = v then 1 else 0 := by
  have h := hw.lozengeKernel_three_term (u - v)
  simp only [sub_eq_zero] at h
  simp only [Fin.sum_univ_three, TriFace.edge_mk_true, TriEdge.blackFace_mk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_ne_one, one_ne_zero,
    Fin.reduceEq, ↓reduceIte]
  rw [sub_right_comm u (0, 1) v, add_sub_right_comm u (1, 0) v]
  linear_combination h

/-- **`G_w` is a left inverse of the Kasteleyn matrix.** For liquid weights, summing
`G_w(v' − u) K(W(u), B(v''))` over the three white faces `W(u)` adjacent to `B(v'')`, across the
edges `B(v'').edge k` of weight `w_k`, gives `[v' = v'']`. -/
theorem IsLiquidWeights.sum_lozengeKernel_edge (hw : IsLiquidWeights w₁ w₂ w₃)
    (v' v'' : ℤ × ℤ) :
    ∑ k : Fin 3, lozengeKernel w₁ w₂ w₃ (v' - (TriFace.edge ⟨v'', false⟩ k).whiteFace.v) *
        (![w₁, w₂, w₃] k : ℂ) =
      if v' = v'' then 1 else 0 := by
  have h := hw.lozengeKernel_three_term (v' - v'')
  simp only [sub_eq_zero] at h
  simp only [Fin.sum_univ_three, TriFace.edge_mk_false, TriEdge.whiteFace_mk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_ne_one, one_ne_zero,
    Fin.reduceEq, ↓reduceIte]
  rw [sub_add_eq_sub_sub v' v'' (0, 1), sub_sub_eq_add_sub, add_sub_right_comm v' (1, 0) v'']
  linear_combination h

end TauCeti
