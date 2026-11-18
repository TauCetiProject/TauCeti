/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative
public import TauCeti.Algebra.Vertex.FormalDistribution
public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Nonnegative residue products of fields

For fields `A(z)` and `B(w)`, their nonnegative residue product is
`Res_z (z - w)ⁿ [A(z), B(w)]`, for `n : ℕ`. Its coefficients are finite sums of
commutators. They define a native `VertexOperator` without any locality assumption:
on each vector, truncation follows from truncation of `B` on that vector and on the
finitely many vectors obtained by applying `A[[i]]`, for `0 ≤ i ≤ n`.

The construction is bilinear. If the fields are local of order `N`, all products
with index at least `N` vanish. These are the singular products used in the
operator product expansion; negative residue products involve normal ordering
and are not constructed here.

For local fields the residue products are the coefficients of the delta expansion of
the commutator, which gives the commutator formula
`[A₍ₘ₎, B₍ₙ₎] = ∑_{j < N} (m choose j) (A₍ⱼ₎B)₍ₘ₊ₙ₋ⱼ₎`. Residue products of translation
covariant fields are translation covariant, and by Dong's lemma a residue product of two
fields is local with every field local with both. These are the closure properties used to
identify the fields of a vertex algebra with residue products.

## Main results

* `VertexOperator.IsLocalOfOrder.lie_ncoeff_eq_sum`: the commutator formula for local fields.
* `VertexOperator.lie_ncoeff_nonnegResidueProduct`: residue products preserve translation
  covariance.
* `VertexOperator.isLocalOfOrder_nonnegResidueProduct`: Dong's lemma for nonnegative residue
  products.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.3 (the delta expansion of a local
  commutator) and Chapter 3 (Dong's lemma, whose proof is followed here).
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2 and Chapter 3.
-/

public section

noncomputable section

open Finset Filter

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem bddBelow_support_nonnegResidueProduct (n : ℕ) (A B : VertexOperator R V)
    (v : V) :
    BddBelow (Function.support fun k : ℤ ↦
      (∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[-k - 1 + ij.2]] -
          B[[-k - 1 + ij.2]] * A[[(ij.1 : ℤ)]])) v) := by
  have hB (w : V) : ∀ᶠ (m : ℤ) in atTop, (B[[m]]) w = 0 := by
    refine (eventually_ge_atTop (-((HahnModule.of R).symm (B w)).order)).mono ?_
    intro m hm
    exact ncoeff_eq_zero_of_lt_order B m w (by omega)
  have h : ∀ᶠ (m : ℤ) in atTop, ∀ ij ∈ antidiagonal n,
      (B[[m + ij.2]]) v = 0 ∧ (B[[m + ij.2]]) ((A[[(ij.1 : ℤ)]]) v) = 0 := by
    rw [eventually_all_finset]
    intro ij _
    exact (tendsto_atTop_add_const_right atTop (ij.2 : ℤ) tendsto_id).eventually
      ((hB v).and (hB ((A[[(ij.1 : ℤ)]]) v)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨-N, fun k hk ↦ ?_⟩
  by_contra! hlt
  apply hk
  simp only [LinearMap.sum_apply]
  apply sum_eq_zero
  intro ij hij
  obtain ⟨h₁, h₂⟩ := hN (-k - 1) (by omega) ij hij
  simp [h₁, h₂]

/-- The bilinear nonnegative residue product
`(A, B) ↦ Res_z (z - w)ⁿ [A(z), B(w)]`. -/
def nonnegResidueProduct (n : ℕ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A :=
    { toFun := fun B ↦ of_coeff (fun k ↦
        ∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[-k - 1 + ij.2]] -
            B[[-k - 1 + ij.2]] * A[[(ij.1 : ℤ)]]))
        (bddBelow_support_nonnegResidueProduct n A B)
      map_add' := by
        intro B C
        apply ext_ncoeff
        intro m
        simp only [ncoeff_of_coeff, map_add, Pi.add_apply]
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro ij _
        simp only [mul_add, add_mul, ← sub_add_sub_comm, smul_add]
      map_smul' := by
        intro r B
        apply ext_ncoeff
        intro m
        simp [← smul_sub, smul_comm, smul_sum] }
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro C
    apply ext_ncoeff
    intro m
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ncoeff_of_coeff, map_add,
      LinearMap.add_apply, Pi.add_apply]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro ij _
    simp only [mul_add, add_mul, ← sub_add_sub_comm, smul_add]
  map_smul' := by
    intro r A
    apply LinearMap.ext
    intro B
    apply ext_ncoeff
    intro m
    simp [← smul_sub, smul_comm, smul_sum]

/-- The coefficients of a nonnegative residue product are the finite binomial
commutator sums. -/
@[simp]
theorem ncoeff_nonnegResidueProduct (n : ℕ) (A B : VertexOperator R V) (m : ℤ) :
    (nonnegResidueProduct n A B)[[m]] =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]]) := by
  simp [nonnegResidueProduct]

/-- Locality kills every nonnegative residue product at or above its order bound. -/
theorem IsLocalOfOrder.nonnegResidueProduct_eq_zero {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) {n : ℕ} (hn : N ≤ n) :
    nonnegResidueProduct n A B = 0 := by
  apply ext_ncoeff
  intro m
  simpa using isLocalOfOrder_iff.mp (h.mono hn) 0 m

/-! ### Residue products as residues of distributions -/

open TauCeti TauCeti.FormalDistribution

/-- The coefficients of `Res_z (z - w)ⁿ [A(z), B(w)]` are those of the residue product. -/
theorem residue_mulSub_pow_commutatorDistribution (n : ℕ) (A B : VertexOperator R V) (m : ℤ) :
    residue ((mulSub ^ n) (A.commutatorDistribution B)) m = (nonnegResidueProduct n A B)[[m]] := by
  rw [residue_apply, mulSub_pow_apply, ncoeff_nonnegResidueProduct]
  simp only [commutatorDistribution_apply, zero_add]

/-- **The commutator formula** for local fields:
`[A₍ₘ₎, B₍ₙ₎] = ∑_{j < N} (m choose j) (A₍ⱼ₎B)₍ₘ₊ₙ₋ⱼ₎`, the coefficient form of the operator
product expansion `[A(z), B(w)] = ∑_{j < N} (A₍ⱼ₎B)(w) ∂_w^(j) δ(z,w)`. -/
theorem IsLocalOfOrder.lie_ncoeff_eq_sum {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (m n : ℤ) :
    ⁅A[[m]], B[[n]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (nonnegResidueProduct j A B)[[m + n - j]] := by
  rw [Ring.lie_def, ← commutatorDistribution_apply, h.commutatorDistribution_eq_sum_deltaTerm,
    Finset.sum_apply, Finset.sum_apply]
  simp only [deltaTerm_apply, residue_mulSub_pow_commutatorDistribution]

/-- **Translation covariance of residue products.** If `[T, A₍ₖ₎] = (∂A)₍ₖ₎` and
`[T, B₍ₖ₎] = (∂B)₍ₖ₎` for all `k`, the same holds for every residue product `A₍ₙ₎B`. -/
theorem lie_ncoeff_nonnegResidueProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ k : ℤ, ⁅T, A[[k]]⁆ = (derivative A)[[k]])
    (hB : ∀ k : ℤ, ⁅T, B[[k]]⁆ = (derivative B)[[k]]) (n : ℕ) (k : ℤ) :
    ⁅T, (nonnegResidueProduct n A B)[[k]]⁆ = (derivative (nonnegResidueProduct n A B))[[k]] := by
  -- Commuting with `T` is the total derivative `∂_z + ∂_w` of the commutator distribution,
  -- which commutes with `(z - w)ⁿ` and whose residue in `z` is `∂_w` of the residue.
  set c := A.commutatorDistribution B
  let g : Module.End R V →+ Module.End R V := AddMonoidHom.mk' (fun X ↦ ⁅T, X⁆) fun X Y ↦ by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  have hT : (fun i j ↦ g (c i j)) = totalDerivative c := by
    funext i j
    have hAi := hA i
    have hBj := hB j
    simp only [Ring.lie_def, ncoeff_derivative] at hAi hBj
    have key : T * (A[[i]] * B[[j]] - B[[j]] * A[[i]]) - (A[[i]] * B[[j]] - B[[j]] * A[[i]]) * T =
        (T * A[[i]] - A[[i]] * T) * B[[j]] + A[[i]] * (T * B[[j]] - B[[j]] * T) -
          ((T * B[[j]] - B[[j]] * T) * A[[i]] + B[[j]] * (T * A[[i]] - A[[i]] * T)) := by
      noncomm_ring
    simp only [g, c, AddMonoidHom.mk'_apply, commutatorDistribution_apply, totalDerivative_apply,
      Ring.lie_def, key, hAi, hBj, smul_mul_assoc, mul_smul_comm]
    module
  rw [ncoeff_derivative, ← residue_mulSub_pow_commutatorDistribution,
    ← residue_mulSub_pow_commutatorDistribution, ← residue_totalDerivative]
  calc ⁅T, residue ((mulSub ^ n) c) k⁆ = residue ((mulSub ^ n) (fun i j ↦ g (c i j))) k := by
        rw [mulSub_pow_map]
        simp only [residue_apply, g, AddMonoidHom.mk'_apply]
    _ = residue (totalDerivative ((mulSub ^ n) c)) k := by
        rw [hT]
        exact congrArg (fun d ↦ residue d k)
          (DFunLike.congr_fun (commute_mulSub_totalDerivative.pow_left n).eq c)

/-! ### Dong's lemma -/

/-- **Dong's lemma** for nonnegative residue products: if `A`, `B` and `C` are pairwise local,
then `A₍ₙ₎B` is local with `C`, with order at most `N_AB - n + N_AC + N_BC - 1`. -/
theorem isLocalOfOrder_nonnegResidueProduct {A B C : VertexOperator R V} {Nab Nac Nbc : ℕ}
    (hab : A.IsLocalOfOrder B Nab) (hac : A.IsLocalOfOrder C Nac)
    (hbc : B.IsLocalOfOrder C Nbc) (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (Nab - n + Nac + Nbc - 1) := by
  -- Right and left commutators with a fixed endomorphism, as additive maps.
  let adR : Module.End R V → Module.End R V →+ Module.End R V :=
    fun Y ↦ AddMonoidHom.mulRight Y - AddMonoidHom.mulLeft Y
  let adL : Module.End R V → Module.End R V →+ Module.End R V :=
    fun Y ↦ AddMonoidHom.mulLeft Y - AddMonoidHom.mulRight Y
  -- The three-variable distribution `[[A(z), B(w)], C(x)]`, split by the Jacobi identity
  -- as `[A(z), [B(w), C(x)]] + [[A(z), C(x)], B(w)]`.
  let t : ℤ → ℤ → ℤ → Module.End R V :=
    fun i j k ↦ adR (C[[k]]) (A.commutatorDistribution B i j)
  let u : ℤ → ℤ → ℤ → Module.End R V :=
    fun i j k ↦ adL (A[[i]]) (B.commutatorDistribution C j k)
  let w : ℤ → ℤ → ℤ → Module.End R V :=
    fun i j k ↦ adR (B[[j]]) (A.commutatorDistribution C i k)
  have htuw : t = u + w := by
    ext i j k : 3
    simp only [t, u, w, adR, adL, commutatorDistribution_apply, Pi.add_apply,
      AddMonoidHom.sub_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    noncomm_ring
  -- The commutator of `A₍ₙ₎B` with `C` is the slice of `(z - w)ⁿ t` at `z`-index `0`.
  have hP : (nonnegResidueProduct n A B).commutatorDistribution C = (mulSub₁₂ ^ n) t 0 := by
    ext p q : 2
    rw [mulSub₁₂_pow_map, commutatorDistribution_apply,
      ← residue_mulSub_pow_commutatorDistribution]
    simp [adR]
  -- `(z - w)^Nab` kills `t`, while `(z - x)^Nac (w - x)^Nbc` kills each of `u` and `w`.
  have ha : (mulSub₁₂ ^ (Nab - n)) ((mulSub₁₂ ^ n) t) = 0 := by
    rw [← Function.comp_apply (f := ⇑(mulSub₁₂ ^ (Nab - n))), ← AddMonoid.End.coe_mul,
      ← pow_add, mulSub₁₂_pow_map,
      (isLocalOfOrder_iff_mulSub_pow_eq_zero A B _).mp (hab.mono (by omega))]
    funext i j k
    simp
  have hu : (mulSub₂₃ ^ Nbc) u = 0 := by
    rw [mulSub₂₃_pow_map, (isLocalOfOrder_iff_mulSub_pow_eq_zero B C _).mp hbc]
    funext i j k
    simp
  have hw : (mulSub₁₃ ^ Nac) w = 0 := by
    rw [mulSub₁₃_pow_map, (isLocalOfOrder_iff_mulSub_pow_eq_zero A C _).mp hac]
    funext i j k
    simp
  have hbd : (mulSub₁₃ ^ Nac) ((mulSub₂₃ ^ Nbc) ((mulSub₁₂ ^ n) t)) = 0 := by
    rw [← mulSub₁₂_pow_apply_mulSub₂₃_pow, ← mulSub₁₂_pow_apply_mulSub₁₃_pow, htuw, map_add,
      map_add, hu, mulSub₁₃_pow_apply_mulSub₂₃_pow, hw]
    simp
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero, hP, ← mulSub₂₃_pow_apply,
    mulSub₂₃_pow_eq_zero ha hbd, Pi.zero_apply]

end VertexOperator
