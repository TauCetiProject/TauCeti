/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Classification
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo.Classification
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Splitting
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Dyadic summands of finite quadratic modules

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

The file also defines and characterizes `TauCeti.FiniteQuadraticModule.HasCyclicTwoSummand`, the
existence of an orthogonal summand `q_θ^{(2)}(2)` (`θ` odd): a module has such a summand exactly
when it contains an element `x` with `2 • x = 0` and `q(x) + q(x) ≠ 0`.

## Main declarations

* `TauCeti.FiniteQuadraticModule.exists_dyadic_summand`: a nondegenerate finite quadratic module
  of even order has a nonzero subgroup isometric to `q_θ^{(2)}(2^{k+1})` with `θ` odd, to
  `u^{(2)}(2^{k+1})`, or to `v^{(2)}(2^{k+1})`.
* `TauCeti.FiniteQuadraticModule.HasCyclicTwoSummand`: existence of an orthogonal summand
  `q_θ^{(2)}(2)` (`θ` odd).

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.1 and Theorems 1.9.1, 1.10.1(4).
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

open AddSubgroup

namespace TauCeti.FiniteQuadraticModule

universe u v

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

/-! ## Cyclic order-two dyadic summands -/

/-- Existence of a cyclic order-two dyadic orthogonal summand `q_θ^{(2)}(2)` (`θ` odd): this is
the dyadic alternative in Nikulin, Theorem 1.10.1(4), and the obstruction to uniqueness of the
minimal `2`-adic lattice realization in Nikulin, Theorem 1.9.1. -/
def HasCyclicTwoSummand (A : FiniteQuadraticModule.{u}) : Prop :=
  ∃ (θ : ℤ) (A' : FiniteQuadraticModule.{0}),
    Odd θ ∧ Nonempty (A.Isometry ((dyadicCyclic 1 θ).prod A'))

/-- Unfolding lemma for `HasCyclicTwoSummand`: `A` splits off a cyclic dyadic summand
`q_θ^{(2)}(2)` for some odd integer `θ`. -/
theorem hasCyclicTwoSummand_def (A : FiniteQuadraticModule.{u}) :
    HasCyclicTwoSummand A ↔
      ∃ (θ : ℤ) (A' : FiniteQuadraticModule.{0}),
        Odd θ ∧ Nonempty (A.Isometry ((dyadicCyclic 1 θ).prod A')) :=
  Iff.rfl

/-- `HasCyclicTwoSummand` is invariant under quadratic isometry. -/
theorem Isometry.hasCyclicTwoSummand_iff {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : A.Isometry B) :
    HasCyclicTwoSummand A ↔ HasCyclicTwoSummand B :=
  ⟨fun ⟨θ, A', hθ, ⟨g⟩⟩ ↦ ⟨θ, A', hθ, ⟨f.symm.trans g⟩⟩,
    fun ⟨θ, A', hθ, ⟨g⟩⟩ ↦ ⟨θ, A', hθ, ⟨f.trans g⟩⟩⟩

/-- A finite quadratic module has a cyclic order-two dyadic summand if and only if it contains an
element `x` with `2 • x = 0` and `q(x) + q(x) ≠ 0`. -/
theorem hasCyclicTwoSummand_iff_exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
    (A : FiniteQuadraticModule.{u}) :
    HasCyclicTwoSummand A ↔ ∃ x : A, 2 • x = 0 ∧ A.quadratic x + A.quadratic x ≠ 0 := by
  constructor
  · rintro ⟨θ, A', hθ, ⟨f⟩⟩
    -- The carrier of `dyadicCyclic 1 θ` is definitionally `ZMod (2 ^ 1)`.
    let e : dyadicCyclic 1 θ := (1 : ZMod (2 ^ 1))
    have h2e : (2 : ℕ) • e = 0 := by
      rw [← pow_one 2, ← natCard_dyadicCyclic 1 θ]
      exact card_nsmul_eq_zero'
    have h2 : (2 : ℕ) • (e, (0 : A')) = 0 := Prod.ext h2e (nsmul_zero 2)
    refine ⟨f.symm (e, 0), by rw [← map_nsmul, h2, map_zero], ?_⟩
    rw [f.symm.map_app, prod_quadratic, map_zero, add_zero]
    exact dyadicCyclic_one_quadratic_add_self_ne_zero hθ
  · rintro ⟨x, hx, hq⟩
    have hpair : A.toFiniteBilinearModule.pairing x x = -(A.quadratic x + A.quadratic x) := by
      rw [← A.polar_eq_pairing, QuadraticMap.polar, ← two_nsmul, hx, map_zero]
      abel
    have hpair0 : A.toFiniteBilinearModule.pairing x x ≠ 0 := by
      rw [hpair]
      exact neg_ne_zero.mpr hq
    -- Since `2 • x = 0` and `b(x, x) ≠ 0`, `x` has order `2` and generates a nondegenerate cyclic
    -- subgroup `H`.
    have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
    have hx2 : (2 ^ (0 + 1)) • x = 0 := by simpa using hx
    have hpair0' : (2 ^ 0) • A.toFiniteBilinearModule.pairing x x ≠ 0 := by simpa using hpair0
    obtain ⟨hordx, hHndB⟩ :=
      A.toFiniteBilinearModule.addOrderOf_eq_and_isNondegenerate_of_pairing hx2 hpair0'
    let H := AddSubgroup.zmultiples x
    have hHnd : (A.restrict H).IsNondegenerate := by
      rw [IsNondegenerate, restrict_toFiniteBilinearModule]
      exact hHndB
    -- The carrier of `A.restrict H` is definitionally `H`.
    have hcardH : Nat.card (A.restrict H) = 2 ^ 1 :=
      show Nat.card H = 2 ^ 1 by rw [Nat.card_zmultiples x, hordx]
    have _ : IsAddCyclic (A.restrict H) := inferInstanceAs (IsAddCyclic H)
    obtain ⟨θ, hθ, ⟨fH⟩⟩ := exists_dyadicCyclic_isometry (A.restrict H) (k := 1) hcardH hHnd
    -- Shrink the orthogonal complement to `Type 0`, since `HasCyclicTwoSummand` quantifies over
    -- `FiniteQuadraticModule.{0}`.
    let B := A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)
    exact ⟨θ, B.shrink, hθ,
      ⟨((fH.prod B.shrinkIsometry).trans (A.restrictProdOrthogonalComplementIsometry hHnd)).symm⟩⟩

/-- A module with a cyclic order-two dyadic summand has an element `x` with `2 • x = 0` and
`q(x) + q(x) ≠ 0`. -/
theorem HasCyclicTwoSummand.exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
    {A : FiniteQuadraticModule.{u}} (hA : HasCyclicTwoSummand A) :
    ∃ x : A, 2 • x = 0 ∧ A.quadratic x + A.quadratic x ≠ 0 :=
  (hasCyclicTwoSummand_iff_exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero A).mp hA

/-- An orthogonal direct sum has a cyclic order-two dyadic summand if and only if at least one of
its factors does. -/
@[simp]
theorem hasCyclicTwoSummand_prod (A : FiniteQuadraticModule.{u})
    (B : FiniteQuadraticModule.{v}) :
    HasCyclicTwoSummand (A.prod B) ↔ HasCyclicTwoSummand A ∨ HasCyclicTwoSummand B := by
  rw [hasCyclicTwoSummand_iff_exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero,
    hasCyclicTwoSummand_iff_exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero,
    hasCyclicTwoSummand_iff_exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero]
  constructor
  · rintro ⟨⟨a, b⟩, hx2, hq⟩
    have h2 := Prod.ext_iff.mp hx2
    rw [prod_quadratic, add_add_add_comm] at hq
    by_contra! hnot
    exact hq (by rw [hnot.1 a h2.1, hnot.2 b h2.2, add_zero])
  · rintro (⟨a, ha2, haq⟩ | ⟨b, hb2, hbq⟩)
    · refine ⟨(a, 0), Prod.ext ha2 (nsmul_zero 2), ?_⟩
      simpa [prod_quadratic] using haq
    · refine ⟨(0, b), Prod.ext (nsmul_zero 2) hb2, ?_⟩
      simpa [prod_quadratic] using hbq

/-- Every nondegenerate `q_θ^{(2)}(2)` (`θ` odd) has a cyclic order-two dyadic summand. -/
@[simp]
theorem hasCyclicTwoSummand_dyadicCyclic_one {θ : ℤ} (hθ : Odd θ) :
    HasCyclicTwoSummand (dyadicCyclic 1 θ) :=
  ⟨θ, ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ))), hθ,
    ⟨(QuadraticMap.IsometryEquiv.prodUnique (dyadicCyclic 1 θ).quadratic
      (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ)))).symm⟩⟩

/-- For every `k`, `u^{(2)}(2^k)` has no cyclic order-two dyadic summand. -/
@[simp]
theorem not_hasCyclicTwoSummand_dyadicU (k : ℕ) : ¬ HasCyclicTwoSummand (dyadicU k) := by
  intro h
  obtain ⟨⟨a, b⟩, hx2, hq⟩ := h.exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
  have ha : a + a = 0 := congrArg Prod.fst ((two_nsmul _).symm.trans (hx2 : (2 : ℕ) • (a, b) = 0))
  exact hq (by rw [dyadicU_quadratic (k := k) (a, b), ← map_add, ← add_mul, ha, zero_mul, map_zero])

/-- For every `k`, `v^{(2)}(2^k)` has no cyclic order-two dyadic summand. -/
@[simp]
theorem not_hasCyclicTwoSummand_dyadicV (k : ℕ) : ¬ HasCyclicTwoSummand (dyadicV k) := by
  intro h
  obtain ⟨⟨a, b⟩, hx2, hq⟩ := h.exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
  have h2 := Prod.mk.inj ((two_nsmul (a, b)).symm.trans (hx2 : (2 : ℕ) • (a, b) = 0))
  have hsum : (a ^ 2 + a * b + b ^ 2) + (a ^ 2 + a * b + b ^ 2) = 0 := by
    linear_combination (a + b) * h2.1 + b * h2.2
  exact hq (by rw [dyadicV_quadratic (k := k) (a, b), ← map_add, hsum, map_zero])

end TauCeti.FiniteQuadraticModule
