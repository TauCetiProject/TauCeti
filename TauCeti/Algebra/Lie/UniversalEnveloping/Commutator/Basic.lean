/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator

/-!
# Integral exponential relations from Lie brackets

These lemmas transport Lie brackets to integral exponentials in a representation, assuming only
stability under the divided powers of the individual vectors. Both Kostant root subgroups and
the pinned Chevalley root subgroups use this common transport.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L V : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (M : AddSubgroup V)
variable {A : Type*} [CommRing A] [Algebra ℤ A]

noncomputable section

/-- Integral exponentials of Lie-commuting vectors commute after scalar extension. -/
theorem commute_baseChangeExp_of_lie_eq_zero {x y : L} (hxy : ⁅x, y⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (u v : A) :
    Commute (baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx u)
      (baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy v) :=
  commute_baseChangeExp M (commute_of_lie_eq_zero ρ hxy) hMx hMy u v

/-- The single-term integral exponential relation, with its integer structure constant absorbed
into the parameter. Only the three vectors' divided powers need preserve the lattice. -/
theorem baseChangeExp_mul_baseChangeExp_of_lie_eq {x y z : L} {c : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : ⁅x, z⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hx : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)))
    (hy : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)))
    (hz : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)))
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) • v ∈ M)
    (u v : A) :
    baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx u *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy v =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy v *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz ((c : A) * (u * v)) *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx u := by
  have hcM := fun n => Associative.dividedPower_zsmul_smul_mem c _ M (hMz n)
  rw [← baseChangeExp_zsmul c M hMz hcM hz]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M
    (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy)
    ((commute_of_lie_eq_zero ρ hxz).smul_right c)
    ((commute_of_lie_eq_zero ρ hyz).smul_right c) hx hy hMx hMy hcM u v

end

end TauCeti.UniversalEnvelopingAlgebra
