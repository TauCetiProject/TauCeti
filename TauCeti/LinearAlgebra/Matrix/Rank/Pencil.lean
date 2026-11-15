/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Rank bounds along a pencil

A *pencil* is an affine line `t ↦ A + t • B` of matrices or linear maps. Each minor of `A + t • B`
is a polynomial in `t`, so the condition `rank (A + t • B) ≤ p` either holds for every `t` or
fails for all but finitely many `t`: a polynomial with infinitely many roots is zero. This is the
one-parameter case of the Zariski closedness of rank bounds in
`TauCeti.LinearAlgebra.Matrix.Rank.Closed`, stated over any field and without coordinates on the
source.

Dividing `f + t • g` by `t` and letting `t → ∞` turns a bound on the pencil into a bound on its
direction `g`. Algebraically, the bound for infinitely many `t` passes to the reversed pencil
`g + s • f`, where it then holds at `s = 0`. The same argument tolerates a fixed summand `W` that
is not rescaled: a bound on `range (f + t • g) ⊔ W` for infinitely many `t` bounds
`range g ⊔ W`. This is the linear-algebraic heart of the Lefschetz–Whitehead rank estimate,
Lemma 2 of Łojasiewicz's triangulation of semianalytic sets, where `W` is spanned by the
derivative in the line parameter.

## Main results

* `Matrix.rank_add_smul_le_of_infinite`: a rank bound on a matrix pencil holding at infinitely
  many parameters holds at every parameter.
* `LinearMap.finrank_range_add_smul_le_of_infinite`: the same for a pencil of linear maps into a
  finite-dimensional space.
* `LinearMap.finrank_range_sup_le_of_infinite`: a bound on `range (f + t • g) ⊔ W` at infinitely
  many `t` bounds `range g ⊔ W`.
* `LinearMap.finrank_range_lt_of_infinite`: if moreover `v ∉ range g`, then a bound `p` on
  `range (f + t • g) ⊔ K ∙ v` at infinitely many `t` forces `finrank (range g) < p`.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) 18
  (1964), 449–474, §2, Lemma 2.
-/

public section

open Module Polynomial

namespace Matrix

variable {m n K : Type*} [Finite m] [Fintype n] [Field K]

/-- **Rank bounds along a matrix pencil.** If `rank (A + t • B) ≤ p` for infinitely many scalars
`t`, then it holds for every `t`: each `(p + 1) × (p + 1)` minor of `A + t • B` is a polynomial
in `t` with infinitely many roots, hence zero. -/
theorem rank_add_smul_le_of_infinite {A B : Matrix m n K} {p : ℕ}
    (h : {t : K | (A + t • B).rank ≤ p}.Infinite) (t : K) : (A + t • B).rank ≤ p := by
  rw [rank_le_iff_forall_det_submatrix_eq_zero]
  intro r c
  -- The minor at `(r, c)` as a polynomial in the parameter.
  let P : K[X] := ((A.map C + (X : K[X]) • B.map C).submatrix r c).det
  have hP (s : K) : P.eval s = ((A + s • B).submatrix r c).det := by
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [mul_comm s]
  have hP0 : P = 0 := eq_zero_of_infinite_isRoot P <| h.mono fun s hs ↦ by
    rw [Set.mem_ofPred_eq, IsRoot.def, hP]
    exact rank_le_iff_forall_det_submatrix_eq_zero.1 hs r c
  rw [← hP, hP0, eval_zero]

end Matrix

namespace LinearMap

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [FiniteDimensional K N]

/-- **Rank bounds along a pencil of linear maps.** If `finrank (range (f + t • g)) ≤ p` for
infinitely many scalars `t`, then it holds for every `t`. The source need not be
finite-dimensional: both maps factor through the quotient by `ker f ⊓ ker g`, which embeds into
`N × N`. -/
theorem finrank_range_add_smul_le_of_infinite {f g : M →ₗ[K] N} {p : ℕ}
    (h : {t : K | finrank K (range (f + t • g)) ≤ p}.Infinite) (t : K) :
    finrank K (range (f + t • g)) ≤ p := by
  -- Factor the pencil through the finite-dimensional quotient `Q = M ⧸ (ker f ⊓ ker g)`.
  set k := ker f ⊓ ker g
  let f' := k.liftQ f inf_le_left
  let g' := k.liftQ g inf_le_right
  have : FiniteDimensional K (M ⧸ k) :=
    Module.Finite.of_injective (k.liftQ (f.prod g) (ker_prod f g).ge)
      (ker_eq_bot.1 (k.ker_liftQ_eq_bot' _ (ker_prod f g).symm))
  have hrange (s : K) : range (f + s • g) = range (f' + s • g') := by
    have hcomp : (f' + s • g') ∘ₗ k.mkQ = f + s • g := by
      rw [add_comp, smul_comp, Submodule.liftQ_mkQ, Submodule.liftQ_mkQ]
    rw [← hcomp, range_comp_of_range_eq_top _ (Submodule.range_mkQ k)]
  -- In bases of `Q` and `N`, the matrix of `f' + s • g'` is a matrix pencil.
  let bQ := Module.finBasis K (M ⧸ k)
  let bN := Module.finBasis K N
  have hrank (s : K) : finrank K (range (f + s • g)) =
      (toMatrix bQ bN f' + s • toMatrix bQ bN g').rank := by
    rw [hrange, ← map_smul, ← map_add, rank_toMatrix]
  simp only [hrank] at h ⊢
  exact Matrix.rank_add_smul_le_of_infinite h t

/-- **Rank bounds pass to the direction of a pencil.** If `range (f + t • g) ⊔ W` has dimension at
most `p` for infinitely many scalars `t`, then so does `range g ⊔ W`. For `t ≠ 0` the range of
`f + t • g` is that of `g + t⁻¹ • f`, so the reversed pencil `g + s • f` satisfies the bound at
infinitely many `s` and hence at `s = 0`. -/
theorem finrank_range_sup_le_of_infinite {f g : M →ₗ[K] N} {W : Submodule K N} {p : ℕ}
    (h : {t : K | finrank K ↥(range (f + t • g) ⊔ W) ≤ p}.Infinite) :
    finrank K ↥(range g ⊔ W) ≤ p := by
  -- The reversed pencil `g + s • f`, with `W` adjoined as the range of a second summand.
  let F₀ : M × W →ₗ[K] N := g.coprod W.subtype
  let F₁ : M × W →ₗ[K] N := f.coprod 0
  have hrange (s : K) : range (F₀ + s • F₁) = range (g + s • f) ⊔ W := by
    have : F₀ + s • F₁ = (g + s • f).coprod W.subtype := by
      ext <;> simp [F₀, F₁]
    rw [this, range_coprod, Submodule.range_subtype]
  have hinf : {s : K | finrank K (range (F₀ + s • F₁)) ≤ p}.Infinite := by
    refine ((h.sdiff (Set.finite_singleton 0)).image inv_injective.injOn).mono ?_
    rintro - ⟨t, ⟨ht, ht0⟩, rfl⟩
    have ht0 : t ≠ 0 := ht0
    have hft : f + t • g = t • (g + t⁻¹ • f) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ ht0, one_smul, add_comm]
    rwa [Set.mem_ofPred_eq, hrange, ← range_smul _ t ht0, ← hft]
  have h0 := finrank_range_add_smul_le_of_infinite hinf 0
  rwa [hrange, zero_smul, add_zero] at h0

/-- **The rank drop of a transverse direction.** If `v ∉ range g` and `range (f + t • g) ⊔ K ∙ v`
has dimension at most `p` for infinitely many scalars `t`, then `finrank (range g) < p`. -/
theorem finrank_range_lt_of_infinite {f g : M →ₗ[K] N} {v : N} (hv : v ∉ range g) {p : ℕ}
    (h : {t : K | finrank K ↥(range (f + t • g) ⊔ K ∙ v) ≤ p}.Infinite) :
    finrank K (range g) < p := by
  have := finrank_range_sup_le_of_infinite h
  rw [Submodule.finrank_sup_span_singleton hv] at this
  omega

end LinearMap
