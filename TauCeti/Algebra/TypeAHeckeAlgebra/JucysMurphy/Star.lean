/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Finite
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star

/-!
# Self-adjoint Jucys–Murphy elements

For a star-fixed parameter, both the normalized and the additive Jucys–Murphy elements are
self-adjoint, in the infinite algebra and in every finite presentation. Together with their
pairwise commutation, this gives the algebraic input for joint orthogonal spectral
decompositions in real-parameter Hecke modules.

The additive assertion holds also at `q² = 1`; it does not follow by division by `q² - 1`.
These results use the involution fixing `T_i`, not the distinct unit-circle involution
sending `T_i` to its inverse. No assertion about positivity of a trace is made here.

## References

* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ}
variable [hq : Fact (IsSelfAdjoint (q : R))]

/-- Normalized Jucys–Murphy elements are self-adjoint for a star-fixed parameter. -/
theorem isSelfAdjoint_jucysMurphy (k : ℕ) : IsSelfAdjoint (jucysMurphy q k) := by
  induction k with
  | zero => rw [jucysMurphy_zero]; exact IsSelfAdjoint.one _
  | succ k ih =>
    rw [jucysMurphy_succ]
    exact ih.conjugate_self (star_T k)

/-- The real-parameter involution fixes every normalized Jucys–Murphy element. -/
@[simp]
theorem star_jucysMurphy (k : ℕ) : star (jucysMurphy q k) = jucysMurphy q k :=
  (isSelfAdjoint_jucysMurphy k).star_eq

/-- Additive Jucys–Murphy elements are self-adjoint, including at `q² = 1`. -/
theorem isSelfAdjoint_additiveJucysMurphy (k : ℕ) :
    IsSelfAdjoint (additiveJucysMurphy q k) := by
  have hqinv : IsSelfAdjoint (↑q⁻¹ : R) := by
    simpa only [Ring.inverse_unit] using hq.out.ringInverse
  induction k with
  | zero => rw [additiveJucysMurphy_zero]; exact IsSelfAdjoint.zero _
  | succ k ih =>
    rw [additiveJucysMurphy_succ]
    exact (ih.conjugate_self (star_T k)).add (hqinv.smul (star_T k))

/-- The real-parameter involution fixes every additive Jucys–Murphy element. -/
@[simp]
theorem star_additiveJucysMurphy (k : ℕ) :
    star (additiveJucysMurphy q k) = additiveJucysMurphy q k :=
  (isSelfAdjoint_additiveJucysMurphy k).star_eq

end TauCeti.InfiniteTypeAHeckeAlgebra

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} {n : ℕ}
variable [Fact (IsSelfAdjoint (q : R))]

/-- The real-parameter involution fixes the finite normalized Jucys–Murphy elements. -/
@[simp]
theorem star_jucysMurphy (i : Fin n) : star (jucysMurphy q i) = jucysMurphy q i := by
  apply toInfinite_injective R q n
  simp

/-- Finite normalized Jucys–Murphy elements are self-adjoint for a star-fixed parameter. -/
theorem isSelfAdjoint_jucysMurphy (i : Fin n) : IsSelfAdjoint (jucysMurphy q i) :=
  star_jucysMurphy i

/-- The real-parameter involution fixes the finite additive Jucys–Murphy elements. -/
@[simp]
theorem star_additiveJucysMurphy (i : Fin n) :
    star (additiveJucysMurphy q i) = additiveJucysMurphy q i := by
  apply toInfinite_injective R q n
  simp

/-- Finite additive Jucys–Murphy elements are self-adjoint, including at `q² = 1`. -/
theorem isSelfAdjoint_additiveJucysMurphy (i : Fin n) :
    IsSelfAdjoint (additiveJucysMurphy q i) :=
  star_additiveJucysMurphy i

end TauCeti.TypeAHeckeAlgebra
