/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple
import TauCeti.LinearAlgebra.End.FiniteOrder

/-!
# Finite-order points of affine groups

A point annihilated by a power prime to the characteristic of its value field is semisimple:
each of its actions is annihilated by the separable polynomial `X ^ n - 1`.
Consequently a unipotent point of such order is the identity. In characteristic zero this
excludes every nonidentity torsion unipotent point, and applies in particular to the image of
a unipotent point in a finite constant quotient.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* The operator criterion is `Module.End.isSemisimple_of_pow_eq_one`.
-/

public section

namespace TauCeti.HopfAlgebra

universe u v w

variable {k : Type u} {H : Type v} {K : Type w}
variable [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H]
variable [Field K] [Algebra k K]

/-- A point whose `n`-th power is the identity is semisimple if `n` is nonzero in its
value field. Neither finite type nor reducedness is needed. -/
theorem isSemisimplePoint_of_pow_eq_one {g : WithConv (H →ₐ[k] K)} {n : ℕ}
    (hn : (n : K) ≠ 0) (hg : g ^ n = 1) : IsSemisimplePoint g := by
  rw [isSemisimplePoint_iff_forall_isSemisimple_endOfPoint]
  intro M
  apply Module.End.isSemisimple_of_pow_eq_one hn
  simpa only [map_pow, map_one, Comodule.pointsRepresentation_apply] using
    congrArg (Comodule.pointsRepresentation (R := k) (H := H) (A := K) M) hg

/-- Over a characteristic-zero value field, every finite-order point is semisimple. -/
theorem isSemisimplePoint_of_isOfFinOrder [CharZero K]
    {g : WithConv (H →ₐ[k] K)} (hg : IsOfFinOrder g) : IsSemisimplePoint g :=
  isSemisimplePoint_of_pow_eq_one (Nat.cast_ne_zero.mpr hg.orderOf_pos.ne')
    (pow_orderOf_eq_one g)

end TauCeti.HopfAlgebra

namespace TauCeti.HopfAlgebra.IsUnipotentPoint

universe u

variable {k H K : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
variable [Field K] [Algebra k K]

/-- A unipotent point whose `n`-th power is the identity is trivial when `n` is nonzero in
the value field. -/
theorem eq_one_of_pow_eq_one [PerfectField K]
    {g : WithConv (H →ₐ[k] K)} (hg : IsUnipotentPoint g)
    {n : ℕ} (hn : (n : K) ≠ 0) (hpow : g ^ n = 1) : g = 1 :=
  (isSemisimplePoint_of_pow_eq_one hn hpow).eq_one_of_isUnipotent hg

/-- A unipotent point of finite order over a characteristic-zero value field is the identity. -/
theorem eq_one_of_isOfFinOrder [CharZero K] {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotentPoint g) (hfin : IsOfFinOrder g) : g = 1 :=
  (isSemisimplePoint_of_isOfFinOrder hfin).eq_one_of_isUnipotent hg

end TauCeti.HopfAlgebra.IsUnipotentPoint
