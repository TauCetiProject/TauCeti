/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import TauCeti.Algebra.TypeAHeckeAlgebra.Embedding
public import TauCeti.Algebra.TypeAHeckeAlgebra.CosetBasis
public import TauCeti.Algebra.TypeAHeckeAlgebra.Reverse

/-!
# Prefix and shifted-tail inclusions of finite Hecke algebras

The map `tailIncl : Hₙ → Hₙ₊₁` adds an uncrossed first strand, sending `T i` to
`T (i + 1)`. It differs from `strandIncl`, which adds the last strand. The positive
cycle word `strandCycle q n = T 0 * ⋯ * T (n - 1)` is a unit of `Hₙ₊₁`, and
conjugation by it carries the prefix inclusion to the shifted-tail inclusion.
Consequently the two restrictions of any representation are intertwined by an
invertible operator. This comparison keeps the actual generator labels, as needed
when a tensor representation distinguishes its first site from its tail.

The proof uses the descending coset-word identity
`InfiniteTypeAHeckeAlgebra.cosetRep_mul_T_succ` and the linear word-reversal
anti-involution. No semisimplicity or restriction on the unit parameter is needed.

## References

* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] (q : Rˣ)

/-- The positive cycle word on `n + 1` strands, as a unit:
`T 0 * T 1 * ⋯ * T (n - 1)`. For `n = 0` it is the empty product. -/
def strandCycle : (n : ℕ) → (TypeAHeckeAlgebra R q (n + 1))ˣ
  | 0 => 1
  | n + 1 => Units.map (strandIncl R q (n + 1)).toMonoidHom (strandCycle n) *
      unitT q (Fin.last n)

/-- The positive cycle on one strand is the empty word. -/
@[simp]
theorem strandCycle_zero : strandCycle q 0 = 1 := (rfl)

/-- Adding a last crossing extends the positive cycle word. -/
theorem strandCycle_succ (n : ℕ) :
    (strandCycle q (n + 1) : TypeAHeckeAlgebra R q (n + 2)) =
      strandIncl R q (n + 1) (strandCycle q n) * T q (Fin.last n) := by
  simp [strandCycle]

/-- The positive cycle word is the reversal of the descending coset representative in the
infinite Hecke algebra. -/
@[simp]
theorem toInfinite_strandCycle (n : ℕ) :
    toInfinite R q (n + 1) (strandCycle q n) =
      InfiniteTypeAHeckeAlgebra.reverse q (InfiniteTypeAHeckeAlgebra.cosetRep q n 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [strandCycle_succ, map_mul, toInfinite_strandIncl, ih,
      InfiniteTypeAHeckeAlgebra.cosetRep_succ (Nat.zero_le n)]
    simp

/-- The positive cycle intertwines a prefix generator with the corresponding tail generator.
Here `i` counts crossings from zero. -/
theorem strandCycle_mul_T {n : ℕ} (i : Fin n) :
    (strandCycle q (n + 1) : TypeAHeckeAlgebra R q (n + 2)) * T q i.castSucc =
      T (n := n + 2) q i.succ * (strandCycle q (n + 1) :
        TypeAHeckeAlgebra R q (n + 2)) := by
  apply toInfinite_injective R q (n + 2)
  have hi : (i : ℕ) + 2 ≤ n + 1 := by omega
  have h := congrArg (InfiniteTypeAHeckeAlgebra.reverse q)
    (InfiniteTypeAHeckeAlgebra.cosetRep_mul_T_succ (q := q) (Nat.zero_le (i : ℕ)) hi)
  simpa using h.symm

/-- Conjugation by the positive cycle word. This is an algebra automorphism of the full stage,
not an identification of its two differently labelled subalgebras. -/
def strandCycleConj (n : ℕ) :
    TypeAHeckeAlgebra R q (n + 1) ≃ₐ[R] TypeAHeckeAlgebra R q (n + 1) :=
  MulSemiringAction.toAlgAut (ConjAct (TypeAHeckeAlgebra R q (n + 1))ˣ) R _
    (ConjAct.toConjAct (strandCycle q n))

/-- The cycle automorphism is conjugation by the displayed positive word. -/
theorem strandCycleConj_apply (n : ℕ) (x : TypeAHeckeAlgebra R q (n + 1)) :
    strandCycleConj q n x = strandCycle q n * x * (↑(strandCycle q n)⁻¹ :
      TypeAHeckeAlgebra R q (n + 1)) := by
  simp [strandCycleConj, ConjAct.units_smul_def]

/-- On all prefix elements, conjugation by the positive cycle is exactly the shifted-tail
inclusion. This includes zero and one strands. -/
@[simp]
theorem strandCycleConj_strandIncl (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    strandCycleConj q n (strandIncl R q n x) = tailIncl q n x := by
  have h : (strandCycleConj q n).toAlgHom.comp (strandIncl R q n) = tailIncl q n := by
    apply hom_ext
    intro i
    obtain _ | n := n
    · exact Fin.elim0 i
    · rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        strandIncl_T_castSucc, strandCycleConj_apply, strandCycle_mul_T]
      simp only [mul_assoc, Units.mul_inv, mul_one, tailIncl_T]
      congr 1
  exact AlgHom.congr_fun h x

/-- The prefix-to-tail intertwining identity, without inverse factors. -/
theorem strandCycle_mul_strandIncl (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    (strandCycle q n : TypeAHeckeAlgebra R q (n + 1)) * strandIncl R q n x =
      tailIncl q n x * strandCycle q n := by
  rw [← strandCycleConj_strandIncl, strandCycleConj_apply]
  simp [mul_assoc]

/-- The shifted-tail map is injective for every commutative coefficient ring and unit
parameter. -/
theorem tailIncl_injective (n : ℕ) : Function.Injective (tailIncl q n) := by
  intro x y h
  apply strandIncl_injective R q n
  apply (strandCycleConj q n).injective
  simpa using h

/-- The cycle automorphism carries the prefix subalgebra onto the shifted-tail subalgebra. -/
theorem range_strandIncl_map_strandCycleConj (n : ℕ) :
    (strandIncl R q n).range.map (strandCycleConj q n).toAlgHom = (tailIncl q n).range := by
  rw [← AlgHom.range_comp]
  congr 1
  exact hom_ext fun i ↦ strandCycleConj_strandIncl q n (T q i)

end TauCeti.TypeAHeckeAlgebra
