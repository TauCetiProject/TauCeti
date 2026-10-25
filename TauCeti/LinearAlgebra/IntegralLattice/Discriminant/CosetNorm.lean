/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Signature

/-!
# Norms of the vectors in a discriminant class

A discriminant class `c ∈ A_L = Lᵛ / L` is a coset of `L` inside the dual lattice, and its norms
are the values `⟨y, y⟩` for `y ∈ Lᵛ` with `y + L = c`.  For an even lattice these norms all agree
modulo `2`: translating `y` by `l ∈ L` adds `2⟨y, l⟩ + ⟨l, l⟩`, and both terms are even integers.
Equivalently, the half-norm `q_L(c) = ⟨y, y⟩ / 2 mod ℤ` is well defined.

When the form is moreover positive semidefinite, the norms of a class are nonnegative, so a
representative of norm less than `2` is already shortest in its class: every other norm differs
from it by an even integer and cannot drop below zero.  This determines the minimum norms `4/3`
and `3/2` of the minuscule classes of `E₆` and `E₇`.

## Main declarations

* `TauCeti.IntegralLattice.IsEven.exists_form_self_eq_add_two_mul`: two dual vectors in one
  discriminant class of an even lattice have norms differing by an even integer.
* `TauCeti.IntegralLattice.IsPosSemidef.isLeast_form_self_zero`: the zero class of a positive
  semidefinite lattice has minimum norm `0`.
* `TauCeti.IntegralLattice.IsPosSemidef.isLeast_form_self_of_form_self_lt_two`: in an even
  positive semidefinite lattice, a dual vector of norm less than `2` has the least norm in its
  discriminant class.
* `TauCeti.IntegralLattice.Isometry.setOf_form_self_discriminantGroupEquiv`: an isometry of
  lattices carries each discriminant class to a class with the same norms, so coset minima
  computed in one model of a lattice transfer to every isometric model
  (`TauCeti.IntegralLattice.Isometry.isLeast_form_self_iff_of_discriminantGroupEquiv_eq`).

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §§6--8.
-/

public section

namespace TauCeti

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- **The norms in a discriminant class of an even lattice agree modulo `2`**: if two dual vectors
`x` and `y` have the same discriminant class, then `⟨y, y⟩ = ⟨x, x⟩ + 2k` for an integer `k`. -/
theorem IsEven.exists_form_self_eq_add_two_mul (hL : L.IsEven) {x y : L.dualCarrier}
    (h : (Submodule.Quotient.mk x : L.DiscriminantGroup) = Submodule.Quotient.mk y) :
    ∃ k : ℤ, L.form y y = L.form x x + 2 * k := by
  have hq := congrArg (L.discriminantQuadraticMap hL) h
  rw [discriminantQuadraticMap_mk, discriminantQuadraticMap_mk, ← sub_eq_zero,
    ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at hq
  obtain ⟨k, hk⟩ := hq
  rw [zsmul_eq_mul, mul_one] at hk
  exact ⟨-k, by push_cast; linarith⟩

/-- **The zero discriminant class of a positive semidefinite lattice has minimum norm `0`**,
attained by the zero vector. -/
theorem IsPosSemidef.isLeast_form_self_zero (hP : L.IsPosSemidef) :
    IsLeast {q : ℚ | ∃ y : L.dualCarrier,
      (Submodule.Quotient.mk y : L.DiscriminantGroup) = 0 ∧ L.form y y = q} 0 := by
  refine ⟨⟨0, Submodule.Quotient.mk_zero _, by simp⟩, ?_⟩
  rintro q ⟨y, -, rfl⟩
  exact L.isPosSemidef_iff.mp hP y

/-- **A dual vector of norm less than `2` is shortest in its discriminant class.**  In an even
positive semidefinite lattice the norms of the class `c = x + L` are the numbers
`⟨x, x⟩ + 2k ≥ 0` with `k : ℤ`; when `⟨x, x⟩ < 2` this forces `k ≥ 0`, so `⟨x, x⟩` is the least
norm of a dual vector in `c`. -/
theorem IsPosSemidef.isLeast_form_self_of_form_self_lt_two (hP : L.IsPosSemidef)
    (hL : L.IsEven) {x : L.dualCarrier} {c : L.DiscriminantGroup}
    (hx : Submodule.Quotient.mk x = c) (hlt : L.form x x < 2) :
    IsLeast {q : ℚ | ∃ y : L.dualCarrier, Submodule.Quotient.mk y = c ∧ L.form y y = q}
      (L.form x x) := by
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro q ⟨y, hy, rfl⟩
  obtain ⟨k, hk⟩ := hL.exists_form_self_eq_add_two_mul (hx.trans hy.symm)
  have hy0 := L.isPosSemidef_iff.mp hP y
  have hk1 : (-1 : ℤ) < k := by
    have : (-1 : ℚ) < k := by linarith
    exact_mod_cast this
  have hk0 : (0 : ℚ) ≤ k := by exact_mod_cast (show (0 : ℤ) ≤ k by omega)
  linarith

/-- **Isometries preserve the norms of a discriminant class**: the dual vectors in the class
`e.discriminantGroupEquiv c` have exactly the norms of the dual vectors in `c`. -/
theorem Isometry.setOf_form_self_discriminantGroupEquiv {W : Type v} [AddCommGroup W]
    [Module ℚ W] {M : IntegralLattice W} (e : Isometry L M) (c : L.DiscriminantGroup) :
    {q : ℚ | ∃ y : M.dualCarrier,
      Submodule.Quotient.mk y = e.discriminantGroupEquiv c ∧ M.form y y = q} =
      {q : ℚ | ∃ x : L.dualCarrier, Submodule.Quotient.mk x = c ∧ L.form x x = q} := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e.dualCarrierEquiv.symm y, e.discriminantGroupEquiv.injective ?_, ?_⟩
    · rw [discriminantGroupEquiv_mk, LinearEquiv.apply_symm_apply, hy]
    · rw [← e.map_app, ← coe_dualCarrierEquiv_apply, LinearEquiv.apply_symm_apply]
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨e.dualCarrierEquiv x, (discriminantGroupEquiv_mk e x).symm,
      by rw [coe_dualCarrierEquiv_apply, e.map_app]⟩

/-- **Coset minima transfer along isometries**: if an isometry `e` carries the class `c` to `d`,
then `r` is the least norm of a dual vector in `d` exactly when it is the least norm in `c`. -/
theorem Isometry.isLeast_form_self_iff_of_discriminantGroupEquiv_eq {W : Type v}
    [AddCommGroup W] [Module ℚ W] {M : IntegralLattice W} (e : Isometry L M)
    {c : L.DiscriminantGroup} {d : M.DiscriminantGroup} (h : e.discriminantGroupEquiv c = d)
    {r : ℚ} :
    IsLeast {q : ℚ | ∃ y : M.dualCarrier, Submodule.Quotient.mk y = d ∧ M.form y y = q} r ↔
      IsLeast {q : ℚ | ∃ x : L.dualCarrier, Submodule.Quotient.mk x = c ∧ L.form x x = q} r := by
  rw [← h, e.setOf_form_self_discriminantGroupEquiv]

end IntegralLattice

end TauCeti
