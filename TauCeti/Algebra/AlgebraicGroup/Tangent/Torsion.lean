/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.KilledByRank
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Convolution

/-!
# The rank annihilates the cotangent space of a finite flat commutative group

Deligne's theorem says that a finite flat commutative group scheme of constant rank `n` is
killed by `n`. Since convolution induces addition on cotangent spaces, its cotangent space at
the identity is also killed by `n`. This gives an annihilator for the module of invariant
differentials over an arbitrary commutative base ring, without assuming it is a field or
that `n` is invertible.

The general criterion `nsmul_cotangentSpace_eq_zero_of_convPow_id_eq_one` only requires a
commutative bialgebra whose universal point has trivial `n`-th convolution power. The rank results
reuse Deligne's theorem on points, in both the free and constant-stalk-rank forms.

## References

* J. Tate and F. Oort, *Group schemes of prime order*, Ann. Sci. École Norm. Sup. (4) 3 (1970),
  1–21, §1, especially Deligne's theorem on p. 4:
  https://www.numdam.org/item/ASENS_1970_4_3_1_1_0/.
-/

public section

open WithConv

namespace TauCeti.Bialgebra

section Bialgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

/-- If the universal point of a commutative bialgebra has trivial `n`-th convolution power,
then `n` annihilates its cotangent space at the identity. -/
theorem nsmul_cotangentSpace_eq_zero_of_convPow_id_eq_one {n : ℕ}
    (hn : toConv (_root_.AlgHom.id R A) ^ n = 1) (x : CotangentSpace R A) : n • x = 0 := by
  obtain ⟨a, rfl⟩ := cotangentMap_surjective R A x
  have h := cotangentMap_convPow (toConv (_root_.AlgHom.id R A)) (fun _ ↦ rfl) n a
  rw [hn] at h
  simpa [Algebra.algebraMap_eq_smul_one] using h.symm

end Bialgebra

section Hopf

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A]

/-- The rank of a free commutative and cocommutative Hopf algebra annihilates its cotangent
space at the identity. For an infinite free module, `Module.finrank` is zero. -/
theorem finrank_smul_cotangentSpace_eq_zero [Module.Free R A] (x : CotangentSpace R A) :
    (Module.finrank R A : R) • x = 0 := by
  simpa only [Nat.cast_smul_eq_nsmul] using
    nsmul_cotangentSpace_eq_zero_of_convPow_id_eq_one
      (TauCeti.AlgHom.convPow_finrank_eq_one (toConv (_root_.AlgHom.id R A))) x

/-- The constant stalk rank of a finite flat commutative and cocommutative Hopf algebra
annihilates its cotangent space at the identity. -/
theorem smul_cotangentSpace_eq_zero_of_rankAtStalk [Module.Finite R A] [Module.Flat R A] {n : ℕ}
    (hn : ∀ p, Module.rankAtStalk (R := R) A p = n) (x : CotangentSpace R A) :
    (n : R) • x = 0 := by
  simpa only [Nat.cast_smul_eq_nsmul] using
    nsmul_cotangentSpace_eq_zero_of_convPow_id_eq_one
      (TauCeti.AlgHom.convPow_eq_one_of_rankAtStalk hn (toConv (_root_.AlgHom.id R A))) x

end Hopf

end TauCeti.Bialgebra
