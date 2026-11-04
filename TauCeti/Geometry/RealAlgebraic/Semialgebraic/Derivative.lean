/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import TauCeti.ModelTheory.Order

/-!
# Directional derivatives of semialgebraic functions

A differentiable semialgebraic scalar function on an open semialgebraic domain has
semialgebraic directional derivatives, including at points where a polynomial relation
for the function has a multiple root. No regularity of that relation is required.

The derivative graph is described by the epsilon-delta condition for the right-hand
limit of difference quotients. Introducing the two function values as quantified
variables makes this a formula of ordered rings. Tarski–Seidenberg then applies.
This also supplies the semialgebraic graph needed to differentiate Nash germs.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Section 2.2 (semialgebraic functions).
-/

public section

open Filter MvPolynomial Set Topology

namespace TauCeti

variable {σ : Type*} {f : (σ → ℝ) → ℝ} {s : Set (σ → ℝ)}

-- The particular ordered-ring formula used below. Its auxiliary value variables
-- let us substitute the graph of f without introducing function symbols.
private theorem isSemialgebraic_setOf_derivative_estimate
    (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) (v : σ → ℝ) :
    IsSemialgebraic {z : σ ⊕ Unit → ℝ | ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t a b : ℝ, 0 < t → t < δ → z ∘ Sum.inl ∈ s → f (z ∘ Sum.inl) = a →
        (z ∘ Sum.inl) + t • v ∈ s → f ((z ∘ Sum.inl) + t • v) = b →
          -ε * t < b - a - t * z (.inr ()) ∧ b - a - t * z (.inr ()) < ε * t} := by
  -- Coordinates are, successively, (x, candidate derivative), epsilon, delta,
  -- and the triple (positive increment, lower function value, upper function value).
  let xP : σ → MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ :=
    fun i ↦ X (.inl (.inl (.inl (.inl i))))
  let dP : MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ :=
    X (.inl (.inl (.inl (.inr ()))))
  let eP : MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ :=
    X (.inl (.inl (.inr ())))
  let rP : MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ :=
    X (.inl (.inr ()))
  let tP : MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ := X (.inr 0)
  let aP : MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ := X (.inr 1)
  let bP : MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ := X (.inr 2)
  let yP := fun i ↦ xP i + tP * C (v i)
  let R := {z : (((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3 → ℝ |
    (0 < eval z tP ∧ eval z tP < eval z rP ∧
      (fun i ↦ eval z (xP i)) ∈ s ∧ f (fun i ↦ eval z (xP i)) = eval z aP ∧
      (fun i ↦ eval z (yP i)) ∈ s ∧ f (fun i ↦ eval z (yP i)) = eval z bP) →
    eval z (-eP * tP) < eval z (bP - aP - tP * dP) ∧
      eval z (bP - aP - tP * dP) < eval z (eP * tP)}
  have hG (p : σ → MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ)
      (q : MvPolynomial ((((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Fin 3) ℝ) :
      IsSemialgebraic {z | (fun i ↦ eval z (p i)) ∈ s ∧
        f (fun i ↦ eval z (p i)) = eval z q} := by
    convert hf.graph.preimage_eval (Sum.elim p (fun _ : Unit ↦ q)) using 1
    ext z
    rw [mem_preimage, mem_preimage_sumArrowEquivProdArrow_scalar_graphOn]
    rfl
  have hG₀ := hG xP aP
  have hG₁ := hG yP bP
  have hR : IsSemialgebraic R := by
    convert (((isSemialgebraic_eval_pos tP).inter (isSemialgebraic_eval_lt tP rP)).inter
      (hG₀.inter hG₁)).compl.union
        ((isSemialgebraic_eval_lt (-eP * tP) (bP - aP - tP * dP)).inter
          (isSemialgebraic_eval_lt (bP - aP - tP * dP) (eP * tP))) using 1
    ext z
    simp only [R, mem_ofPred_eq, mem_union, mem_compl_iff, mem_inter_iff]
    tauto
  -- Eliminate the value/increment triple, then delta, then epsilon.
  let := FirstOrder.Ring.compatibleRingOfRing ℝ
  let := FirstOrder.Language.orderStructure ℝ
  have hAll := hR.definable.forall_of_finite.isSemialgebraic
  have hDelta := ((isSemialgebraic_eval_pos
    (X (.inr ()) : MvPolynomial (((σ ⊕ Unit) ⊕ Unit) ⊕ Unit) ℝ)).inter hAll).definable
    |>.exists_of_finite.isSemialgebraic
  have hEps := ((isSemialgebraic_eval_pos
    (X (.inr ()) : MvPolynomial ((σ ⊕ Unit) ⊕ Unit) ℝ)).compl.union hDelta).definable
    |>.forall_of_finite.isSemialgebraic
  -- Convert finite coordinate blocks back to the scalar quantifiers of the estimate.
  convert hEps using 1
  ext z
  simp only [R, xP, yP, dP, eP, rP, tP, aP, bP, mem_ofPred_eq, mem_union,
    mem_compl_iff, eval_X, mem_inter_iff, eval_add, eval_mul, eval_C, map_sub, map_neg,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h ε
    by_cases hε : 0 < ε ()
    · obtain ⟨δ, hδ, hbound⟩ := h (ε ()) hε
      refine Or.inr ⟨fun _ ↦ δ, hδ, fun w hw ↦ ?_⟩
      obtain ⟨ht, htδ, hx, ha, hy, hb⟩ := hw
      exact hbound (w 0) (w 1) (w 2) ht htδ hx ha hy hb
    · exact Or.inl hε
  · intro h ε hε
    obtain ⟨δ, hδ, hbound⟩ := (h (fun _ ↦ ε)).resolve_left (not_not.mpr hε)
    refine ⟨δ (), hδ, fun t a b ht htδ hx ha hy hb ↦ ?_⟩
    exact hbound ![t, a, b] ⟨ht, htδ, hx, ha, hy, hb⟩

/-- A differentiable semialgebraic function on an open domain has a semialgebraic
scalar directional derivative in each fixed direction. -/
theorem IsSemialgebraicOn.fderiv_apply [Finite σ]
    (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) (hs : IsOpen s)
    (hd : DifferentiableOn ℝ f s) (v : σ → ℝ) :
    IsSemialgebraicOn (fun x (_ : Unit) ↦ fderiv ℝ f x v) s := by
  let := Fintype.ofFinite σ
  refine isSemialgebraicOn_def.mpr ⟨hf.isSemialgebraic, ?_⟩
  convert (hf.isSemialgebraic.preimage_comp Sum.inl).inter
    (isSemialgebraic_setOf_derivative_estimate hf v) using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_scalar_graphOn]
  simp only [mem_inter_iff, mem_preimage]
  refine and_congr_right fun hx ↦ ?_
  let x := z ∘ Sum.inl
  let d := z (.inr ())
  have hder := ((hd x hx).differentiableAt (hs.mem_nhds hx)).hasFDerivAt.hasLineDerivAt v
  constructor
  · -- A derivative satisfies the quantified estimate for all small positive increments.
    intro heq ε hε
    have hlim := hder.tendsto_slope_zero_right
    obtain ⟨δ, hδ, hbound⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε hε
    refine ⟨δ, hδ, fun t a b ht htδ _ ha _ hb ↦ ?_⟩
    have hval := hbound (mem_Ioi.mpr ht) (by simpa [Real.dist_eq, abs_of_pos ht] using htδ)
    have hquot : |(b - a) / t - d| < ε := by
      simpa [Real.dist_eq, smul_eq_mul, div_eq_inv_mul, ha, hb, heq, x, d] using hval
    have hid : (b - a) / t - d = (b - a - t * d) / t := by
      field_simp
    rw [hid] at hquot
    obtain ⟨hl, hu⟩ := abs_lt.mp hquot
    exact ⟨(lt_div_iff₀ ht).mp hl, (div_lt_iff₀ ht).mp hu⟩
  · -- Openness prevents vacuous limits: the displaced points eventually stay in s.
    -- The estimate then determines the derivative by uniqueness of the right-hand limit.
    intro h
    have hlim : Tendsto (fun t : ℝ ↦ t⁻¹ • (f (x + t • v) - f x))
        (𝓝[>] (0 : ℝ)) (𝓝 d) := by
      refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
      obtain ⟨δ, hδ, hbound⟩ := h ε hε
      have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ :=
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
      have hU : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ s := by
        have hc : ContinuousAt (fun t : ℝ ↦ x + t • v) 0 := by fun_prop
        exact nhdsWithin_le_nhds (hc.preimage_mem_nhds (by simpa using hs.mem_nhds hx))
      filter_upwards [self_mem_nhdsWithin, hsmall, hU] with t ht htδ htU
      have ht : 0 < t := ht
      obtain ⟨hl, hu⟩ := hbound t (f x) (f (x + t • v)) ht htδ hx rfl htU rfl
      have hquot : |(f (x + t • v) - f x - t * d) / t| < ε :=
        abs_lt.mpr ⟨(lt_div_iff₀ ht).mpr hl, (div_lt_iff₀ ht).mpr hu⟩
      have hid : (f (x + t • v) - f x - t * d) / t =
          t⁻¹ * (f (x + t • v) - f x) - d := by
        field_simp
      simpa [Real.dist_eq, smul_eq_mul, hid] using hquot
    exact tendsto_nhds_unique hder.tendsto_slope_zero_right hlim

end TauCeti
