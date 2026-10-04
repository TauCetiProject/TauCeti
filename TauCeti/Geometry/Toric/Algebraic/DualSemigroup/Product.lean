/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Prod
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic

/-!
# Dual semigroups of product cones

An integral character on a product lattice is nonnegative on a product cone precisely when
its restrictions to the two factors are nonnegative. Consequently the dual semigroup of a
product cone is canonically the product of the two dual semigroups. This identification uses
restriction of characters and their coproduct, with no bases or regularity hypotheses, and
supplies the character identification for products of affine toric schemes.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.2.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
  (σ : PointedCone ℝ V) (τ : PointedCone ℝ V')

/-- A character is nonnegative on a product cone exactly when its restrictions to both
factors are nonnegative. -/
-- Give the product rule precedence over the general `mem_dualSemigroup` expansion.
@[simp high]
theorem mem_dualSemigroup_prod (m : N × N' →+ ℤ) :
    m ∈ dualSemigroup (hi.prod hi') (σ.prod τ) ↔
      m.comp (AddMonoidHom.inl N N') ∈ dualSemigroup hi σ ∧
        m.comp (AddMonoidHom.inr N N') ∈ dualSemigroup hi' τ := by
  have hsplit := hi.realCharacter_coprod hi'
    (m.comp (AddMonoidHom.inl N N')) (m.comp (AddMonoidHom.inr N N'))
  rw [AddMonoidHom.coprod_unique] at hsplit
  simp only [mem_dualSemigroup]
  constructor
  · intro hm
    constructor
    · intro x hx
      have h := hm (x := (x, 0)) ⟨hx, τ.zero_mem⟩
      simpa [hsplit] using h
    · intro y hy
      have h := hm (x := (0, y)) ⟨σ.zero_mem, hy⟩
      simpa [hsplit] using h
  · rintro ⟨hm, hm'⟩ ⟨x, y⟩ ⟨hx, hy⟩
    simpa [hsplit] using add_nonneg (hm hx) (hm' hy)

/-- Restriction to the two factors identifies the dual semigroup of a product cone with
the product of the factor dual semigroups. The inverse takes the coproduct of characters. -/
noncomputable def dualSemigroupProdEquiv :
    dualSemigroup (hi.prod hi') (σ.prod τ) ≃+
      dualSemigroup hi σ × dualSemigroup hi' τ :=
  let e := (AddMonoidHom.coprodEquiv (M := N) (N := N') (P := ℤ)).symm
  ({ e.toEquiv.subtypeEquiv (fun m ↦ by
        simpa only [e, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
          AddMonoidHom.coprodEquiv_symm_apply, AddSubmonoid.mem_prod] using
          mem_dualSemigroup_prod hi hi' σ τ m) with
      map_add' := fun m n ↦ Subtype.ext (map_add e (m : N × N' →+ ℤ) n) } :
    dualSemigroup (hi.prod hi') (σ.prod τ) ≃+
      (dualSemigroup hi σ).prod (dualSemigroup hi' τ)).trans
    (AddSubmonoid.prodEquiv _ _)

/-- The first component of the product equivalence evaluates a character on the first factor. -/
@[simp]
theorem dualSemigroupProdEquiv_fst_apply
    (m : dualSemigroup (hi.prod hi') (σ.prod τ)) (n : N) :
    ((dualSemigroupProdEquiv hi hi' σ τ m).1 : N →+ ℤ) n =
      (m : N × N' →+ ℤ) (n, 0) :=
  (congrArg (fun p : (N →+ ℤ) × (N' →+ ℤ) ↦ p.1 n)
    (AddMonoidHom.coprodEquiv_symm_apply (m : N × N' →+ ℤ)))

/-- The second component of the product equivalence evaluates a character on the second factor. -/
@[simp]
theorem dualSemigroupProdEquiv_snd_apply
    (m : dualSemigroup (hi.prod hi') (σ.prod τ)) (n : N') :
    ((dualSemigroupProdEquiv hi hi' σ τ m).2 : N' →+ ℤ) n =
      (m : N × N' →+ ℤ) (0, n) :=
  (congrArg (fun p : (N →+ ℤ) × (N' →+ ℤ) ↦ p.2 n)
    (AddMonoidHom.coprodEquiv_symm_apply (m : N × N' →+ ℤ)))

/-- The inverse product equivalence sums the values of the two factor characters. -/
@[simp]
theorem dualSemigroupProdEquiv_symm_apply
    (m : dualSemigroup hi σ × dualSemigroup hi' τ) (n : N × N') :
    ((dualSemigroupProdEquiv hi hi' σ τ).symm m : N × N' →+ ℤ) n =
      (m.1 : N →+ ℤ) n.1 + (m.2 : N' →+ ℤ) n.2 :=
  (AddMonoidHom.coprodEquiv_apply ((m.1 : N →+ ℤ), (m.2 : N' →+ ℤ)) n)

end TauCeti.Toric
