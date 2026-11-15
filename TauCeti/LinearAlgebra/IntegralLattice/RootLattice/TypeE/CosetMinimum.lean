/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.CosetNorm
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic

/-!
# Minimum norms of the discriminant classes of `E₆`, `E₇` and `E₈`

The least norm of a dual vector in each discriminant class of the exceptional root lattices is

```text
E₆ :  [0] ↦ 0,   [1] ↦ 4/3,   [2] ↦ 4/3,
E₇ :  [0] ↦ 0,   [1] ↦ 3/2,
E₈ :  [0] ↦ 0,
```

where the labels are those of `typeE₆DiscriminantGroupEquiv : ZMod 3 ≃+ A_{E₆}` and
`typeE₇DiscriminantGroupEquiv : ZMod 2 ≃+ A_{E₇}`, so `[1]` is the class of the minuscule weight
`ϖ₁` (resp. `ϖ₇`) and `[2]` that of `-ϖ₁`.  These are the shortest norms of the Conway--Sloane
glue labels of an `E₆` or `E₇` component.

The minimum of each nonzero class is attained by `ϖ₁`, `-ϖ₁` or `ϖ₇`.  Since the lattices are
even, every norm in the class of `ϖ` is `⟨ϖ, ϖ⟩ + 2k` for an integer `k`, and since they are
positive definite that norm is nonnegative; as `⟨ϖ₁, ϖ₁⟩ = 4/3` and `⟨ϖ₇, ϖ₇⟩ = 3/2` are both less
than `2`, this forces `k ≥ 0`.  The argument is
`TauCeti.IntegralLattice.IsPosSemidef.isLeast_form_self_of_form_self_lt_two`.

## Main declarations

* `TauCeti.IntegralLattice.isLeast_form_self_typeE₆MinusculeWeightClass`: the class of `ϖ₁` has
  minimum norm `4/3`, attained by `ϖ₁`.
* `TauCeti.IntegralLattice.isLeast_form_self_typeE₆DiscriminantGroupEquiv`: the minimum norm of
  every labelled class of `E₆`.
* `TauCeti.IntegralLattice.isLeast_form_self_typeE₇MinusculeWeightClass`: the class of `ϖ₇` has
  minimum norm `3/2`, attained by `ϖ₇`.
* `TauCeti.IntegralLattice.isLeast_form_self_typeE₇DiscriminantGroupEquiv`: the minimum norm of
  every labelled class of `E₇`.
* `TauCeti.IntegralLattice.isLeast_form_self_typeE₈RootLattice`: the unique class of the unimodular
  lattice `E₈` has minimum norm `0`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.2 and
  §8.3 (the dual lattices `E₇*` and `E₆*`), and Chapter 16, §1.
-/

public section

namespace TauCeti

namespace IntegralLattice

/-! ## Type `E₆` -/

/-- **The minimum norm of the class of `ϖ₁` in `E₆` is `4/3`**: it is attained by the minuscule
weight `ϖ₁` and bounds the norm of every dual vector in its class. -/
theorem isLeast_form_self_typeE₆MinusculeWeightClass :
    IsLeast {q : ℚ | ∃ x : typeE₆RootLattice.dualCarrier,
      Submodule.Quotient.mk x = typeE₆MinusculeWeightClass ∧ typeE₆RootLattice.form x x = q}
      (4 / 3) := by
  have h := isPosDef_typeE₆RootLattice.isPosSemidef.isLeast_form_self_of_form_self_lt_two
    isEven_typeE₆RootLattice mk_typeE₆MinusculeWeightDual (by norm_num)
  rwa [coe_typeE₆MinusculeWeightDual, form_typeE₆MinusculeWeight_self] at h

/-- **The minimum norm of the class of `-ϖ₁` in `E₆` is `4/3`**: it is attained by `-ϖ₁` and
bounds the norm of every dual vector in its class. -/
theorem isLeast_form_self_neg_typeE₆MinusculeWeightClass :
    IsLeast {q : ℚ | ∃ x : typeE₆RootLattice.dualCarrier,
      Submodule.Quotient.mk x = -typeE₆MinusculeWeightClass ∧ typeE₆RootLattice.form x x = q}
      (4 / 3) := by
  have hform : typeE₆RootLattice.form ↑(-typeE₆MinusculeWeightDual)
      ↑(-typeE₆MinusculeWeightDual) = 4 / 3 := by
    simp
  have h := isPosDef_typeE₆RootLattice.isPosSemidef.isLeast_form_self_of_form_self_lt_two
    isEven_typeE₆RootLattice (x := -typeE₆MinusculeWeightDual)
    (by rw [Submodule.Quotient.mk_neg, mk_typeE₆MinusculeWeightDual]) (by rw [hform]; norm_num)
  rwa [hform] at h

/-- **The minimum norm of each discriminant class of `E₆`.**  The class labelled `a : ZMod 3`
has minimum norm `0` when `a = 0` and `4/3` otherwise. -/
theorem isLeast_form_self_typeE₆DiscriminantGroupEquiv (a : ZMod 3) :
    IsLeast {q : ℚ | ∃ x : typeE₆RootLattice.dualCarrier,
      Submodule.Quotient.mk x = typeE₆DiscriminantGroupEquiv a ∧ typeE₆RootLattice.form x x = q}
      (if a = 0 then 0 else 4 / 3) := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = -1 := by revert a; decide
  · rw [ite_eq_left rfl, map_zero]
    exact isPosDef_typeE₆RootLattice.isPosSemidef.isLeast_form_self_zero
  · rw [ite_eq_right one_ne_zero, typeE₆DiscriminantGroupEquiv_apply_one]
    exact isLeast_form_self_typeE₆MinusculeWeightClass
  · rw [ite_eq_right (by decide), map_neg, typeE₆DiscriminantGroupEquiv_apply_one]
    exact isLeast_form_self_neg_typeE₆MinusculeWeightClass

/-! ## Type `E₇` -/

/-- **The minimum norm of the class of `ϖ₇` in `E₇` is `3/2`**: it is attained by the minuscule
weight `ϖ₇` and bounds the norm of every dual vector in its class. -/
theorem isLeast_form_self_typeE₇MinusculeWeightClass :
    IsLeast {q : ℚ | ∃ x : typeE₇RootLattice.dualCarrier,
      Submodule.Quotient.mk x = typeE₇MinusculeWeightClass ∧ typeE₇RootLattice.form x x = q}
      (3 / 2) := by
  have h := isPosDef_typeE₇RootLattice.isPosSemidef.isLeast_form_self_of_form_self_lt_two
    isEven_typeE₇RootLattice mk_typeE₇MinusculeWeightDual (by norm_num)
  rwa [coe_typeE₇MinusculeWeightDual, form_typeE₇MinusculeWeight_self] at h

/-- **The minimum norm of each discriminant class of `E₇`.**  The class labelled `a : ZMod 2`
has minimum norm `0` when `a = 0` and `3/2` otherwise. -/
theorem isLeast_form_self_typeE₇DiscriminantGroupEquiv (a : ZMod 2) :
    IsLeast {q : ℚ | ∃ x : typeE₇RootLattice.dualCarrier,
      Submodule.Quotient.mk x = typeE₇DiscriminantGroupEquiv a ∧ typeE₇RootLattice.form x x = q}
      (if a = 0 then 0 else 3 / 2) := by
  obtain rfl | rfl : a = 0 ∨ a = 1 := by revert a; decide
  · rw [ite_eq_left rfl, map_zero]
    exact isPosDef_typeE₇RootLattice.isPosSemidef.isLeast_form_self_zero
  · rw [ite_eq_right one_ne_zero, typeE₇DiscriminantGroupEquiv_apply_one]
    exact isLeast_form_self_typeE₇MinusculeWeightClass

/-! ## Type `E₈` -/

/-- **The discriminant class of `E₈` has minimum norm `0`.**  The lattice is unimodular, so every
class is the zero class, minimized by the zero vector. -/
theorem isLeast_form_self_typeE₈RootLattice (c : typeE₈RootLattice.DiscriminantGroup) :
    IsLeast {q : ℚ | ∃ x : typeE₈RootLattice.dualCarrier,
      Submodule.Quotient.mk x = c ∧ typeE₈RootLattice.form x x = q} 0 := by
  rw [Subsingleton.elim c 0]
  exact isPosDef_typeE₈RootLattice.isPosSemidef.isLeast_form_self_zero

end IntegralLattice

end TauCeti
