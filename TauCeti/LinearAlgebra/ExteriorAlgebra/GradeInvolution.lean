/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Grade involution and graded commutativity on an exterior algebra

Independently of any basis or contraction, the grade involution `CliffordAlgebra.involute` acts on
the `n`-th exterior power `⋀[R]^n M` by `(-1) ^ n` (and in particular on `ExteriorAlgebra.ιMulti`),
and every vector `ι R m` graded-commutes with every multivector `x` via
`ι R m * x = involute x * ι R m` (and by `(-1) ^ n` on homogeneous elements of degree `n`).
-/

public section

open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The grade involution acts on the `n`-th exterior power by `(-1) ^ n`.** -/
theorem involute_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    involute (Q := (0 : QuadraticForm R M)) x = (-1 : R) ^ n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x _ ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, ih, involute_ι, mul_smul_comm, neg_mul, smul_neg, pow_succ', mul_smul,
      neg_one_smul]

/-- **The grade involution acts on an exterior monomial by the parity of its degree.** The
monomial is the product of its `n` generators, each of which the involution negates. -/
@[simp]
theorem involute_ιMulti {n : ℕ} (v : Fin n → M) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (ExteriorAlgebra.ιMulti R n v) =
      (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n v := by
  -- Every exterior monomial is the product of the list of its generators.
  have h : ExteriorAlgebra.ιMulti R n v =
      ((List.ofFn v).map (CliffordAlgebra.ι (0 : QuadraticForm R M))).prod := by
    rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
    rfl
  rw [h, CliffordAlgebra.involute_prod_map_ι, List.length_ofFn]

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **A vector graded-commutes with every multivector**: moving `ι R m` past `x` applies the grade
involution to `x`. -/
theorem ι_mul_eq_involute_mul (m : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R m * x =
      involute (Q := (0 : QuadraticForm R M)) x * ExteriorAlgebra.ι R m := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι v =>
    rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero]
    exact ExteriorAlgebra.ι_add_mul_swap m v
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, map_mul, mul_assoc]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]

/-- A vector graded-commutes with an element of the `n`-th exterior power with the sign
`(-1) ^ n`. -/
theorem ι_mul_eq_neg_one_pow_smul_mul {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M)
    (m : M) : ExteriorAlgebra.ι R m * x = (-1 : R) ^ n • (x * ExteriorAlgebra.ι R m) := by
  rw [ι_mul_eq_involute_mul, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower hx,
    smul_mul_assoc]

/-- An element of an even exterior power commutes with every vector, in the form
`x * ι m + involute (ι m) * x = 0` required of the degree-one part of a twisted derivation by
`ExteriorAlgebra.liftTwistedDerivation`. -/
theorem mul_ι_add_involute_ι_mul_of_mem_exteriorPower {n : ℕ} (hn : Even n)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) (m : M) :
    x * ExteriorAlgebra.ι R m +
      involute (Q := (0 : QuadraticForm R M)) (ExteriorAlgebra.ι R m) * x = 0 := by
  rw [involute_ι, neg_mul, ι_mul_eq_neg_one_pow_smul_mul hx, hn.neg_one_pow, one_smul,
    add_neg_cancel]

end ExteriorAlgebra
