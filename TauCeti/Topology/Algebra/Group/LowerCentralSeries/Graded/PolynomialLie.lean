/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AEval
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.LieRing
import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Pow

/-!
# The graded Lie algebra of the lower `p`-series over `𝔽_p[π]`, for odd `p`

For odd `p` the `p`-power operator `π : gr_k(G) → gr_{k+1}(G)` on the graded pieces of the lower
`p`-series is additive in every degree, including degree zero
(`TauCeti.gradedPow_add_zero_of_odd`), and it commutes with the graded bracket in every degree
(`TauCeti.gradedPow_gradedBracket_left_of_odd`, `TauCeti.gradedPow_gradedBracket_right_of_odd`).
Assembled over all degrees, `π` is therefore a `ZMod p`-linear endomorphism of degree one of the
graded Lie algebra `⨁ k, gr_k(G)` that commutes with every inner derivation:

  `π ⁅x, y⁆ = ⁅π x, y⁆ = ⁅x, π y⁆`.

So `⨁ k, gr_k(G)` is a Lie algebra over the polynomial ring `𝔽_p[π]`, with the indeterminate
acting by `π`. The `𝔽_p[π]`-module is Mathlib's `Module.AEval'` of the endomorphism `π`, the
`R[X]`-module attached to an `R`-linear endomorphism, and the Lie algebra structure is the general
one of `TauCeti.Module.AEval'.lieAlgebra` for an endomorphism commuting with inner derivations.

For `p = 2` none of this holds: `π` fails to be additive in degree zero, with defect the bracket
(`TauCeti.gradedPow_add_zero_of_two`), and the defect is nonzero for a free pro-`2` group of rank
two (`TauCeti.gradedPow_freeProP_two_not_additive`). This is why the dyadic Demushkin relators need
separate treatment.

## Main definitions

* `TauCeti.gradedPowLinearMap`: `π : gr_k(G) →ₗ[ZMod p] gr_{k+1}(G)`, for odd `p`.
* `TauCeti.gradedPowEnd`: `π` on the direct sum `⨁ k, gr_k(G)`, of degree one.
* The `LieAlgebra (ZMod p)[X]` instance on `Module.AEval' (gradedPowEnd p G hp)`.

## Main results

* `TauCeti.gradedPowEnd_of`: `π` sends a homogeneous element of degree `k` to its `p`-power class,
  of degree `k + 1`.
* `TauCeti.gradedPowEnd_lie_left`, `TauCeti.gradedPowEnd_lie_right`: `π` commutes with the bracket.
* `TauCeti.aeval_gradedPowEnd_lie_right`: so does every polynomial in `π`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1,
  Propositions 1 and 2.
* M. Lazard, *Sur les groupes nilpotents et les anneaux de Lie*, Ann. Sci. École Norm. Sup. 71
  (1954).
-/

public section

open DirectSum Polynomial

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The operator `π` as a linear map -/

variable (p G) in
/-- **The `p`-power operator `π : gr_k(G) → gr_{k+1}(G)` as a `ZMod p`-linear map**, for odd `p`.
It is additive in degree zero by `TauCeti.gradedPow_add_zero_of_odd` and above degree zero by
`TauCeti.gradedPow_add_of_one_le`, and commutes with scalars in every degree. -/
def gradedPowLinearMap (hp : Odd p) (k : ℕ) :
    gradedPiece p G k →ₗ[ZMod p] gradedPiece p G (k + 1) where
  toFun := gradedPow p G k
  map_add' x y := by
    rcases k with _ | k
    · exact gradedPow_add_zero_of_odd hp x y
    · exact gradedPow_add_of_one_le (by omega) x y
  map_smul' := gradedPow_smul

@[simp]
theorem gradedPowLinearMap_apply (hp : Odd p) {k : ℕ} (x : gradedPiece p G k) :
    gradedPowLinearMap p G hp k x = gradedPow p G k x :=
  (rfl)

variable (p G) in
/-- **The `p`-power operator `π` on the graded Lie algebra** `⨁ k, gr_k(G)`, for odd `p`: the
`ZMod p`-linear endomorphism of degree one which on `gr_k(G)` is
`TauCeti.gradedPowLinearMap p G hp k` (`TauCeti.gradedPowEnd_of`). -/
def gradedPowEnd (hp : Odd p) : Module.End (ZMod p) (⨁ k, gradedPiece p G k) :=
  toModule (ZMod p) ℕ _ fun k => lof (ZMod p) ℕ (gradedPiece p G) (k + 1) ∘ₗ
    gradedPowLinearMap p G hp k

/-- **`π` has degree one**: it sends a homogeneous element of degree `k` to its `p`-power class,
of degree `k + 1`. -/
@[simp]
theorem gradedPowEnd_of (hp : Odd p) {k : ℕ} (x : gradedPiece p G k) :
    gradedPowEnd p G hp (of (gradedPiece p G) k x) =
      of (gradedPiece p G) (k + 1) (gradedPow p G k x) := by
  rw [gradedPowEnd, ← lof_eq_of (ZMod p), toModule_lof, LinearMap.comp_apply,
    gradedPowLinearMap_apply, lof_eq_of]

/-! ### `π` against the bracket -/

/-- **`π` commutes with the bracket on the left**, for odd `p`: `π ⁅x, y⁆ = ⁅π x, y⁆` on
`⨁ k, gr_k(G)`. On homogeneous elements this is `TauCeti.gradedPow_gradedBracket_left_of_odd`. -/
theorem gradedPowEnd_lie_left (hp : Odd p) (x y : ⨁ k, gradedPiece p G k) :
    gradedPowEnd p G hp ⁅x, y⁆ = ⁅gradedPowEnd p G hp x, y⁆ := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_lie, map_zero]
  | add x x' hx hx' => simp only [add_lie, map_add, hx, hx']
  | of j a =>
    induction y using DirectSum.induction_on with
    | zero => simp only [lie_zero, map_zero]
    | add y y' hy hy' => simp only [lie_add, map_add, hy, hy']
    | of k b =>
      rw [of_lie_of, gradedPowEnd_of, gradedPowEnd_of, of_lie_of,
        gradedPow_gradedBracket_left_of_odd hp, of_gradedCast]

/-- **`π` commutes with the bracket on the right**, for odd `p`: `π ⁅x, y⁆ = ⁅x, π y⁆` on
`⨁ k, gr_k(G)`. On homogeneous elements this is `TauCeti.gradedPow_gradedBracket_right_of_odd`. -/
theorem gradedPowEnd_lie_right (hp : Odd p) (x y : ⨁ k, gradedPiece p G k) :
    gradedPowEnd p G hp ⁅x, y⁆ = ⁅x, gradedPowEnd p G hp y⁆ := by
  rw [← lie_skew, map_neg, gradedPowEnd_lie_left, lie_skew]

/-- **Every polynomial in `π` commutes with the bracket**, for odd `p`:
`f(π) ⁅x, y⁆ = ⁅x, f(π) y⁆` for `f ∈ 𝔽_p[X]`. This is the `𝔽_p[π]`-bilinearity of the bracket. -/
theorem aeval_gradedPowEnd_lie_right (hp : Odd p) (f : (ZMod p)[X])
    (x y : ⨁ k, gradedPiece p G k) :
    aeval (gradedPowEnd p G hp) f ⁅x, y⁆ = ⁅x, aeval (gradedPowEnd p G hp) f y⁆ :=
  Module.End.aeval_lie_right_of_lie_right (gradedPowEnd_lie_right hp) f x y

/-! ### The `𝔽_p[π]`-Lie algebra -/

/-- **The graded Lie algebra over `𝔽_p[π]`**, for odd `p`: on `Module.AEval' (gradedPowEnd p G hp)`,
where the indeterminate `X` acts by `π` (`Module.AEval'.X_smul_of`), the bracket of the graded Lie
ring is `𝔽_p[π]`-bilinear, because `π` commutes with the bracket
(`TauCeti.gradedPowEnd_lie_right`). -/
noncomputable instance (hp : Odd p) :
    LieAlgebra (ZMod p)[X] (Module.AEval' (gradedPowEnd p G hp)) :=
  Module.AEval'.lieAlgebra (gradedPowEnd_lie_right hp)

end TauCeti
