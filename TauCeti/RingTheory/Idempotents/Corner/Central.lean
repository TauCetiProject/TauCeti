/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CentralIdempotent
public import TauCeti.RingTheory.Idempotents.Corner.Basic
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# The corner of an idempotent primitive in the centre

Let `b` be a primitive idempotent of the centre of an `R`-algebra `A`. Then the corner `bAb`,
which is the two-sided ideal `bA` since `b` is central, has no central idempotents besides `0` and
`1`. A central idempotent `z` of `bA` commutes with every `x ∈ A` through the compression `b x`,
so it is a central idempotent of `A` with `b z = z b = z`; primitivity of `b` in the centre leaves
only `z = 0` and `z = b`.

## Main results

* `TauCeti.IsPrimitiveIdempotent.centralIdempotents_corner_subset`: the corner of an idempotent
  primitive in the centre has no central idempotents besides `0` and `1`.
-/

public section

namespace TauCeti

namespace IsPrimitiveIdempotent

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] {b : Subalgebra.center R A}

/-- **The corner of an idempotent primitive in the centre has no nontrivial central
idempotents.** If `b` is a primitive idempotent of the centre of `A`, a central idempotent `z` of
the corner `bA` is a central idempotent of `A` with `b z = z`, so `z` is `0` or `b`. The
idempotence of `b` in `A`, which indexes the corner, is the argument `he`. -/
theorem centralIdempotents_corner_subset (hb : IsPrimitiveIdempotent b)
    (he : IsIdempotentElem (b : A)) : centralIdempotents he.Corner ⊆ {0, 1} := by
  intro z hz
  have hc : IsMulCentral (b : A) := Set.mem_center_iff.mp b.property
  have hbz : (b : A) * z.val = z.val := he.mul_corner_val z
  have hzb : z.val * (b : A) = z.val := he.corner_val_mul z
  -- `z` commutes with every `x ∈ A`, through the compression `b x`.
  have hzc (x : A) : x * z.val = z.val * x := by
    have h := congrArg Subtype.val
      (mul_comm_of_mem_centralIdempotents hz (he.compressAlgHom R hc x))
    rw [IsIdempotentElem.Corner.val_mul, IsIdempotentElem.Corner.val_mul,
      IsIdempotentElem.val_compressAlgHom] at h
    calc x * z.val = b * x * z.val := by rw [(hc.comm x).eq, mul_assoc, hbz]
      _ = z.val * x := by rw [← h, ← mul_assoc, hzb]
  let f : Subalgebra.center R A := ⟨z.val, Subalgebra.mem_center_iff.2 hzc⟩
  have hzz : z.val * z.val = z.val :=
    congrArg Subtype.val (isIdempotentElem_of_mem_centralIdempotents hz).eq
  -- The unit of the corner is `b`, so `f = b` in the centre gives `z = 1` in the corner.
  rcases hb.eq_zero_or_eq (f := f) (Subtype.ext hzz) (Subtype.ext hbz) (Subtype.ext hzb) with h | h
  · refine Or.inl (Subtype.ext ?_)
    rw [IsIdempotentElem.Corner.val_zero]
    simpa [f] using congrArg Subtype.val h
  · refine Or.inr (Subtype.ext ?_)
    rw [IsIdempotentElem.Corner.val_one]
    simpa [f] using congrArg Subtype.val h

end IsPrimitiveIdempotent

end TauCeti
