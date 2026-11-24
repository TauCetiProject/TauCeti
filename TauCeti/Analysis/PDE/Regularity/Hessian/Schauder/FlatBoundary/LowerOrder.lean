/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.HalfBall
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.LowerOrder
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.InnerProductSpace.HalfSpace

/-!
# Schauder estimates on small half-balls at a flat boundary with lower-order terms

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, with closure
`closure H = {x | c₀ ≤ ⟪x, ν⟫}`, and let `0 < α < 1`. This file extends the Schauder estimate on
small half-balls at the flat boundary `∂H`, in the `TauCeti.PDE` namespace
`exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_halfSpace`,
from `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` to the general second-order operator in non-divergence form

`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + b · ∇u + c u`,

with a drift `b` and a potential `c` that are `α`-Hölder and bounded on `B_R ∩ H`, where
`B_R = ball x₀ R`. The drift term is written `fderiv ℝ u x (b x)`, as in the interior estimate with
lower-order terms, in the `TauCeti.PDE` namespace
`exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul`.
No sign condition on `c` is needed.

**The estimate** is, in the `TauCeti.PDE` namespace,
`exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul_of_halfSpace`.
If `R` is small compared with the Hölder modulus of the principal coefficients, then for every
`ρ < R` and every bound `B` on the Hölder constants and the sizes of `b` and `c` there is `C`,
independent of the solution, such that every `u` which is `C²` near `B_R ∩ closure H`, vanishes on
`B_R ∩ ∂H` and has `α`-Hölder Hessian on `B_R ∩ closure H` satisfies

`[D²u]_{α; closedBall x₀ ρ ∩ closure H} ≤ C ([L u]_{α; B_R ∩ H} + N)`,

where `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on `B_R ∩ closure H`. The smallness condition on `R`
involves only the principal part, and `C` does not depend on the centre `x₀`, the half-space or
the coefficients beyond their bounds.

Flattening a curved boundary portion by a change of variables of order two turns an operator
without lower-order terms into one with a drift, built from the second derivatives of the chart,
so this is the form of the half-ball estimate that the boundary estimate on curved domains needs.

## The argument

As in the interior, the lower-order part is moved to the right side: `u` solves
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = L u - b · ∇u - c u` on `B_R ∩ H`. The set `B_R ∩ closure H` is convex and lies
in `B_R`, so the bounds `N` on `‖Du‖` and `‖D²u‖` make `u` and `Du` Lipschitz there, hence
`α`-Hölder with constant `N (2R)^{1-α}` (`Convex.holderOnWith_of_norm_fderiv_le`,
`Convex.holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le`). The Hölder constant of
`b · ∇u + c u` on `B_R ∩ H` is then a multiple of `N`
(`TauCeti.PDE.holderOnWith_fderiv_apply_add_mul`), and the half-ball estimate for the principal
part applies.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2, Lemma 6.5 (the boundary estimate for operators with lower-order terms on
  half-balls).
-/

public section

noncomputable section

open Metric Set
open scoped InnerProductSpace NNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **The Schauder estimate on small half-balls at a flat boundary, with lower-order terms.** Let
`0 < α < 1`. There is `C₀ > 0`, depending only on the dimension and `α`, with the following
property. Let `0 < λ`, `Λ`, `L`, `M` and `R` be given, put `κ = C₀ (Λ / λ)^(1 + (n+1)/4 + α/2)`,
and assume the scale condition

`2 κ (n+1)² (1 + 2ᵅ) L Rᵅ ≤ λ`.

Then for every `ρ < R` and every `B` there is `C`, depending only on `n`, `α`, `λ`, `Λ`, `L`, `M`,
`B`, `R` and `ρ`, with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}`, `ν ≠ 0`, and let
`x₀ ∈ closure H`. Let `a` be `α`-Hölder entrywise with constant `L` on `closedBall x₀ R ∩ closure H`
and bounded entrywise by `M` on `B_R ∩ H`, and suppose `a x₀` has ellipticity bounds `λ, Λ`. Let
the drift `b` and the potential `c` be `α`-Hölder with constant `B` and bounded by `B` on
`B_R ∩ H`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + b · ∇u + c u`. Let `u` be `C²` on an open set containing
`B_R ∩ closure H`, vanishing on `B_R ∩ ∂H`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on
`B_R ∩ closure H` and with `D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on
`B_R ∩ H` with constant `K`, then `D²u` is `α`-Hölder on `closedBall x₀ ρ ∩ closure H` with
constant `C (K + N)`.

The scale condition does not involve `b` or `c`, and `C` does not depend on the centre `x₀`, the
half-space or the coefficients beyond the bounds `λ`, `Λ`, `L`, `M` and `B`. -/
theorem
    exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul_of_halfSpace
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {lam Lam : ℝ} {L M : ℝ≥0} {R : ℝ}, 0 < lam →
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((1 + 2 ^ (α : ℝ)) * L * R ^ (α : ℝ)) ≤ lam →
      ∀ {ρ : ℝ}, ρ < R → ∀ B : ℝ≥0, ∃ C : ℝ≥0,
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ} {x₀ ν : E}
        {c₀ : ℝ}, ν ≠ 0 → c₀ ≤ ⟪x₀, ν⟫_ℝ →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ})) →
      (∀ x ∈ ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}, ∀ i j, |a x i j| ≤ M) →
      HolderOnWith B α b (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) →
      (∀ x ∈ ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}, ‖b x‖ ≤ B) →
      HolderOnWith B α c (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) →
      (∀ x ∈ ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}, |c x| ≤ B) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U →
        ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U → ContDiffOn ℝ 2 u U →
        (∀ x ∈ ball x₀ R, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
        (∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, |u x| ≤ N) →
        (∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x) +
            c x * u x) (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u)
          (closedBall x₀ ρ ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}) := by
  obtain ⟨C₀, hC₀, hHB⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_halfSpace
      hα hα1 (n := n)
  refine ⟨C₀, hC₀, fun {lam Lam L M R} hlam hsmall {ρ} hρR B => ?_⟩
  obtain ⟨C, hC⟩ := hHB hlam hsmall hρR (L := L) (M := M)
  -- `δ = (2R)^{1-α}` converts Lipschitz bounds on `B_R ∩ closure H` into Hölder bounds, and the
  -- Hölder constant of `b · ∇u + c u` is `N P`.
  set δ : ℝ≥0 := (2 * R).toNNReal ^ ((1 : ℝ) - α)
  set P : ℝ≥0 := B + B * δ + (B * δ + B)
  refine ⟨C * (1 + P), fun {a b c x₀ ν c₀} hν hx₀ hEll hEll' hL hM hLb hBb hLc hBc
    {U u N K V} hU hBU hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  -- On the convex set `B_R ∩ closure H`, `u` and `Du` are `α`-Hölder with constant `N δ`.
  set s : Set E := ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  have hsc : Convex ℝ s := (convex_ball x₀ R).inter (TauCeti.convex_setOf_le_inner ν c₀)
  have hu2 (x : E) (hx : x ∈ s) : ContDiffAt ℝ 2 u x := hu.contDiffAt (hU.mem_nhds (hBU hx))
  have hHu : HolderOnWith (N * δ) α u s := hsc.holderOnWith_of_norm_fderiv_le hα1.le
    inter_subset_left (fun x hx => (hu2 x hx).differentiableAt two_ne_zero) hN1
  have hHDu : HolderOnWith (N * δ) α (fderiv ℝ u) s :=
    hsc.holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le hα1.le inter_subset_left hu2 hN2
  -- The principal part `L u - (b · ∇u + c u)` is `α`-Hölder on `B_R ∩ H` with constant `K + N P`.
  have hos : ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ} ⊆ s :=
    inter_subset_inter_right _ fun _ hx => mem_ofPred.2 (mem_ofPred.1 hx).le
  have hlow := holderOnWith_fderiv_apply_add_mul (hHu.mono hos) (hHDu.mono hos)
    (fun x hx => hN0 x (hos hx)) (fun x hx => hN1 x (hos hx)) hLb hBb hLc
    (fun x hx => by simpa only [Real.norm_eq_abs] using hBc x hx)
  have hprin : HolderOnWith (K + N * P) α (fun x => ∑ i, ∑ j, a x i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) := by
    have h := hK.sub hlow
    simp only [Pi.sub_def, add_sub_add_right_eq_sub, add_sub_cancel_right] at h
    exact h.mono_const (le_of_eq (by ring))
  exact (hC hν hx₀ hEll hEll' hL hM hU hBU hu hu0 hN0 hN1 hN2 hV hprin).mono_const
    (mul_add_mul_add_le_mul_one_add_mul_add zero_le zero_le zero_le)

end TauCeti.PDE
