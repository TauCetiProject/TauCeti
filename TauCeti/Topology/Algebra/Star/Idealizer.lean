/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.StarSubalgebra
public import TauCeti.Algebra.Star.Idealizer

/-!
# Closedness of the idealizer of a closed nonunital `⋆`-subalgebra

In a semitopological `⋆`-algebra `A`, the idealizer `S.idealizer` of any closed nonunital
`⋆`-subalgebra `S` is closed, as an intersection of preimages of `S` under left and right
multiplication. When `A` is a unital C⋆-algebra, Mathlib's `StarSubalgebra.cstarAlgebra` instance
then automatically equips `S.idealizer` with a unital C⋆-algebra structure.
-/

public section

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A] [TopologicalSpace A] [IsSemitopologicalSemiring A]

/-- The idealizer of a closed nonunital `⋆`-subalgebra in a semitopological `⋆`-algebra is
closed. -/
instance isClosed_idealizer (S : NonUnitalStarSubalgebra R A) [hS : IsClosed (S : Set A)] :
    IsClosed (S.idealizer : Set A) := by
  have heq : (S.idealizer : Set A) =
      ⋂ x : S, (· * (x : A)) ⁻¹' (S : Set A) ∩ ((x : A) * ·) ⁻¹' (S : Set A) := by
    ext a
    simp [Set.mem_iInter, Subtype.forall]
  rw [heq]
  exact isClosed_iInter fun x =>
    (hS.preimage (continuous_mul_const (x : A))).inter (hS.preimage (continuous_const_mul (x : A)))

end NonUnitalStarSubalgebra
