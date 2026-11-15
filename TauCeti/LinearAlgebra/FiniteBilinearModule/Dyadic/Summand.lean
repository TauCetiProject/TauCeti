/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Classification
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo.Classification
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Splitting

/-!
# A dyadic generator splits off every nondegenerate module of even order

Let `A` be a nondegenerate finite quadratic module of even order. This file finds a nonzero
subgroup `H ≤ A` whose restricted form is one of Nikulin's dyadic generators: a cyclic module
`q_θ^{(2)}(2^{k+1})` with `θ` odd, or one of the rank-two modules `u^{(2)}(2^{k+1})` and
`v^{(2)}(2^{k+1})`. Each of these is nondegenerate, so `H` splits off `A` orthogonally through
`TauCeti.FiniteQuadraticModule.restrictProdOrthogonalComplementIsometry`.

Take `x` and `y`, both killed by `2^{k+1}`, with `2^k b(x, y) ≠ 0`; they exist by
`TauCeti.FiniteBilinearModule.exists_nsmul_pairing_ne_zero_of_dvd_card`. If `2^k b(x, x) ≠ 0`,
then `b(x, x)` has the same order `2^{k+1}` as `x`, so `⟨x⟩` is a nondegenerate cyclic summand,
and likewise for `y`. Otherwise both self-pairings are killed by `2^k`, so `q(x)` and `q(y)` are
killed by `2^{k+1}` because `2q(w) = b(w, w)`, and `⟨x, y⟩` is a rank-two block `u` or `v`. Unlike
at an odd prime, `x + y` does not help in the last case: `b(x + y, x + y)` differs from
`b(x, x) + b(y, y)` by `2b(x, y)`, which `2^k` kills.

## Main declaration

* `TauCeti.FiniteQuadraticModule.exists_dyadic_summand`: a nondegenerate finite quadratic module
  of even order has a nonzero subgroup isometric to `q_θ^{(2)}(2^{k+1})` with `θ` odd, to
  `u^{(2)}(2^{k+1})`, or to `v^{(2)}(2^{k+1})`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.1.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

open AddSubgroup

namespace TauCeti.FiniteQuadraticModule

variable {A : FiniteQuadraticModule}

/-- If `2^{k+1}` kills `z` but not `2^k b(z, z)`, then `⟨z⟩` is a nonzero subgroup isometric to
`q_θ^{(2)}(2^{k+1})` for an odd `θ`. -/
private theorem exists_dyadicCyclic_isometry_restrict_zmultiples {k : ℕ} {z : A}
    (hz : 2 ^ (k + 1) • z = 0) (hzz : 2 ^ k • A.toFiniteBilinearModule.pairing z z ≠ 0) :
    zmultiples z ≠ ⊥ ∧ ∃ θ : ℤ, Odd θ ∧
      Nonempty (Isometry (dyadicCyclic (k + 1) θ) (A.restrict (zmultiples z))) := by
  obtain ⟨horder, hnd⟩ :=
    A.toFiniteBilinearModule.addOrderOf_eq_and_isNondegenerate_of_pairing hz hzz
  have hnd' : (A.restrict (zmultiples z)).IsNondegenerate := by
    rwa [IsNondegenerate, restrict_toFiniteBilinearModule]
  have : IsAddCyclic (A.restrict (zmultiples z)) := inferInstanceAs (IsAddCyclic (zmultiples z))
  refine ⟨?_, exists_dyadicCyclic_isometry _ ((Nat.card_zmultiples z).trans horder) hnd'⟩
  rw [Ne, zmultiples_eq_bot]
  rintro rfl
  rw [addOrderOf_zero] at horder
  exact (Nat.one_lt_two_pow k.succ_ne_zero).ne horder

/-- If `2^k b(w, w) = 0`, then `2^{k+1} q(w) = 0`, since `2q(w) = b(w, w)`. -/
private theorem two_pow_succ_nsmul_quadratic_eq_zero {k : ℕ} {w : A}
    (hw : 2 ^ k • A.toFiniteBilinearModule.pairing w w = 0) :
    2 ^ (k + 1) • A.quadratic w = 0 := by
  rw [pow_succ, mul_nsmul', ← QuadraticMap.polar_self, polar_eq_pairing, hw]

/-- **A dyadic generator splits off.** A nondegenerate finite quadratic module of even order has a
nonzero subgroup `H` whose restricted form is isometric to one of Nikulin's dyadic generators:
`q_θ^{(2)}(2^{k+1})` with `θ` odd, `u^{(2)}(2^{k+1})`, or `v^{(2)}(2^{k+1})`. All three are
nondegenerate, so `H` is an orthogonal summand of `A`. -/
theorem exists_dyadic_summand (hA : A.IsNondegenerate) (h2 : 2 ∣ Nat.card A) :
    ∃ (H : AddSubgroup A) (k : ℕ), H ≠ ⊥ ∧
      ((∃ θ : ℤ, Odd θ ∧ Nonempty (Isometry (dyadicCyclic (k + 1) θ) (A.restrict H))) ∨
        Nonempty (Isometry (dyadicU (k + 1)) (A.restrict H)) ∨
        Nonempty (Isometry (dyadicV (k + 1)) (A.restrict H))) := by
  obtain ⟨x, y, k, hx, hy, hxy⟩ :=
    A.toFiniteBilinearModule.exists_nsmul_pairing_ne_zero_of_dvd_card (p := 2) hA h2
  -- An element with `2^k b(w, w) ≠ 0` generates a cyclic summand.
  by_cases hxx : 2 ^ k • A.toFiniteBilinearModule.pairing x x = 0
  swap
  · obtain ⟨hne, h⟩ := exists_dyadicCyclic_isometry_restrict_zmultiples hx hxx
    exact ⟨_, k, hne, Or.inl h⟩
  by_cases hyy : 2 ^ k • A.toFiniteBilinearModule.pairing y y = 0
  swap
  · obtain ⟨hne, h⟩ := exists_dyadicCyclic_isometry_restrict_zmultiples hy hyy
    exact ⟨_, k, hne, Or.inl h⟩
  -- Otherwise `x` and `y` span a rank-two block, which contains `x ≠ 0`.
  refine ⟨zmultiples x ⊔ zmultiples y, k, fun h ↦ hxy ?_, Or.inr
    (nonempty_isometry_dyadicU_or_dyadicV_restrict_zmultiples_sup hx hy
      (two_pow_succ_nsmul_quadratic_eq_zero hxx) (two_pow_succ_nsmul_quadratic_eq_zero hyy) hxy)⟩
  have hx0 : x ∈ zmultiples x ⊔ zmultiples y := mem_sup_left (mem_zmultiples x)
  rw [h, mem_bot] at hx0
  rw [hx0, FiniteBilinearModule.pairing_zero_left, nsmul_zero]

end TauCeti.FiniteQuadraticModule
