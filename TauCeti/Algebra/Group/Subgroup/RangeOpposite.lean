/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Anti-automorphisms of the range of a homomorphism

If `σ : G →* Gᵐᵒᵖ` is an anti-homomorphism, such as the transpose of invertible matrices, and
`κ : G →* C` has kernel stable under `σ`, then `κ g ↦ κ (σ g)` is a well-defined
anti-endomorphism of the range of `κ`. When `σ` is involutive, so is the induced map, which is
then an anti-automorphism of the range. It is defined only on that range: nothing is asserted
about elements of `C` outside it.

This is the image anti-isomorphism used with transposition in Bass–Milnor–Serre's extension
argument for Mennicke symbols.

## Main definitions

* `MonoidHom.rangeOpHom`: the anti-endomorphism of the range of `κ` induced by an
  anti-homomorphism of `G` that stabilizes the kernel of `κ`.
* `MonoidHom.rangeOpMulEquiv`: the same map as an anti-automorphism of the range, when the
  anti-homomorphism of `G` is involutive.

## Main results

* `MonoidHom.rangeOpHom_rangeRestrict`, `MonoidHom.rangeOpMulEquiv_rangeRestrict`: the defining
  formula of the induced map.
* `MonoidHom.rangeOpHom_rangeOpHom`, `MonoidHom.rangeOpMulEquiv_rangeOpMulEquiv`: the induced map
  is involutive.
* `MonoidHom.rangeOpMulEquiv_symm_apply`: the inverse of the anti-automorphism is the map itself.

## References

* H. Bass, J. Milnor, J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §9.
-/

public section

namespace MonoidHom

variable {G C F : Type*} [Group G] [Group C] [FunLike F G Gᵐᵒᵖ] [MonoidHomClass F G Gᵐᵒᵖ]
  (κ : G →* C) (σ : F)

/-- If the kernel of `κ` is stable under an anti-homomorphism `σ : G → Gᵐᵒᵖ`, then
`κ g ↦ κ (σ g)` is well defined on the range of `κ`, and is an anti-homomorphism from the range
to itself. -/
noncomputable def rangeOpHom (hker : ∀ g, κ g = 1 → κ (σ g).unop = 1) :
    κ.range →* κ.rangeᵐᵒᵖ :=
  κ.rangeRestrict.liftOfSurjective κ.rangeRestrict_surjective
    ⟨{ toFun g := MulOpposite.op (κ.rangeRestrict (σ g).unop)
       map_one' := by simp
       map_mul' g h := by simp [← MulOpposite.op_mul] },
      fun g hg ↦ by
        rw [ker_rangeRestrict, mem_ker] at hg
        simpa [Subtype.ext_iff] using hker g hg⟩

variable {κ σ}

@[simp]
theorem rangeOpHom_rangeRestrict (hker : ∀ g, κ g = 1 → κ (σ g).unop = 1) (g : G) :
    κ.rangeOpHom σ hker (κ.rangeRestrict g) = MulOpposite.op (κ.rangeRestrict (σ g).unop) :=
  liftOfRightInverse_comp_apply _ _ _ _ g

/-- The anti-endomorphism of the range induced by an involutive anti-homomorphism is
involutive. -/
@[simp]
theorem rangeOpHom_rangeOpHom (hσ : ∀ g, (σ (σ g).unop).unop = g)
    (hker : ∀ g, κ g = 1 → κ (σ g).unop = 1) (x : κ.range) :
    (κ.rangeOpHom σ hker (κ.rangeOpHom σ hker x).unop).unop = x := by
  obtain ⟨g, rfl⟩ := κ.rangeRestrict_surjective x
  simp [hσ]

variable (κ σ)

/-- Let `σ` be an involutive anti-homomorphism of `G`, such as the transpose of invertible
matrices, and suppose that the kernel of `κ` is stable under `σ`. Then `κ g ↦ κ (σ g)` is a
well-defined involutive anti-automorphism of the range of `κ`. -/
noncomputable def rangeOpMulEquiv (hσ : ∀ g, (σ (σ g).unop).unop = g)
    (hker : ∀ g, κ g = 1 → κ (σ g).unop = 1) : κ.range ≃* κ.rangeᵐᵒᵖ :=
  { κ.rangeOpHom σ hker with
    invFun y := (κ.rangeOpHom σ hker y.unop).unop
    left_inv := rangeOpHom_rangeOpHom hσ hker
    right_inv y := congrArg MulOpposite.op (rangeOpHom_rangeOpHom hσ hker y.unop) }

variable {κ σ}

@[simp]
theorem rangeOpMulEquiv_rangeRestrict (hσ : ∀ g, (σ (σ g).unop).unop = g)
    (hker : ∀ g, κ g = 1 → κ (σ g).unop = 1) (g : G) :
    κ.rangeOpMulEquiv σ hσ hker (κ.rangeRestrict g) =
      MulOpposite.op (κ.rangeRestrict (σ g).unop) :=
  rangeOpHom_rangeRestrict hker g

/-- The anti-automorphism of the range induced by an involutive anti-homomorphism is itself
involutive. -/
@[simp]
theorem rangeOpMulEquiv_rangeOpMulEquiv (hσ : ∀ g, (σ (σ g).unop).unop = g)
    (hker : ∀ g, κ g = 1 → κ (σ g).unop = 1) (x : κ.range) :
    (κ.rangeOpMulEquiv σ hσ hker (κ.rangeOpMulEquiv σ hσ hker x).unop).unop = x :=
  rangeOpHom_rangeOpHom hσ hker x

/-- The inverse of the anti-automorphism of the range induced by an involutive anti-homomorphism
is the anti-automorphism itself. -/
@[simp]
theorem rangeOpMulEquiv_symm_apply (hσ : ∀ g, (σ (σ g).unop).unop = g)
    (hker : ∀ g, κ g = 1 → κ (σ g).unop = 1) (y : κ.rangeᵐᵒᵖ) :
    (κ.rangeOpMulEquiv σ hσ hker).symm y = (κ.rangeOpMulEquiv σ hσ hker y.unop).unop := by
  rw [MulEquiv.symm_apply_eq]
  exact congrArg MulOpposite.op (rangeOpMulEquiv_rangeOpMulEquiv hσ hker y.unop).symm

end MonoidHom
