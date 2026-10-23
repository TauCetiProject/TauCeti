/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation

/-!
# Left translations on the coinvariant algebra

Functions invariant under right translation by a closed subgroup remain invariant after
left translation by an ambient rational point. Thus left translations act on the spectrum
of the coinvariant algebra, compatibly with the map from the ambient group. No normality
of the subgroup is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7 and 12.
-/

public section

open WithConv

namespace TauCeti.HopfIdeal

universe u v

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R}
  (I : HopfIdeal R H)

/-- Left translation preserves functions invariant under right translation by a subgroup. -/
theorem leftTranslationAlgEquiv_mem_coinvariants (g : WithConv (H →ₐ[R] R))
    {x : H} (hx : x ∈ I.coinvariants) :
    HopfAlgebra.leftTranslationAlgEquiv g x ∈ I.coinvariants := by
  rw [mem_coinvariants_iff_forall_mul]
  intro A a n hn
  have heval (a : WithConv (H →ₐ[R] A)) :
      a.ofConv (HopfAlgebra.leftTranslationAlgEquiv g x) =
        (AlgHom.mapValue (Algebra.ofId R A) g * a).ofConv x := by
    exact congrArg (fun f : WithConv (H →ₐ[R] A) ↦ f.ofConv x)
      (HopfAlgebra.toConv_comp_leftTranslationAlgEquiv g a)
  rw [heval, heval, ← mul_assoc]
  exact ofConv_mul_apply_of_mem_coinvariants hx _ hn

/-- The automorphism of the coinvariant algebra induced by an ambient left translation. -/
noncomputable def coinvariantsLeftTranslation (g : WithConv (H →ₐ[R] R)) :
    I.coinvariants ≃ₐ[R] I.coinvariants where
  toFun x := ⟨HopfAlgebra.leftTranslationAlgEquiv g x,
    I.leftTranslationAlgEquiv_mem_coinvariants g x.2⟩
  invFun x := ⟨HopfAlgebra.leftTranslationAlgEquiv g⁻¹ x,
    I.leftTranslationAlgEquiv_mem_coinvariants g⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    simp [HopfAlgebra.leftTranslationAlgEquiv_inv]
  right_inv x := by
    apply Subtype.ext
    simp [HopfAlgebra.leftTranslationAlgEquiv_inv]
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext (AlgEquiv.commutes _ r)

/-- The inclusion of coinvariants intertwines the two left translations. -/
@[simp]
theorem coe_coinvariantsLeftTranslation (g : WithConv (H →ₐ[R] R))
    (x : I.coinvariants) :
    (I.coinvariantsLeftTranslation g x : H) = HopfAlgebra.leftTranslationAlgEquiv g x :=
  (rfl)

/-- The inverse restricted translation is left translation by the inverse point. -/
@[simp]
theorem coe_coinvariantsLeftTranslation_symm (g : WithConv (H →ₐ[R] R))
    (x : I.coinvariants) :
    ((I.coinvariantsLeftTranslation g).symm x : H) =
      HopfAlgebra.leftTranslationAlgEquiv g⁻¹ x :=
  (rfl)

/-- Left translation by the identity point fixes the coinvariant algebra. -/
@[simp]
theorem coinvariantsLeftTranslation_one :
    I.coinvariantsLeftTranslation (1 : WithConv (H →ₐ[R] R)) = 1 := by
  ext x
  simp

/-- Pullback on coinvariants reverses the order of convolution products. -/
@[simp]
theorem coinvariantsLeftTranslation_mul (g h : WithConv (H →ₐ[R] R)) :
    I.coinvariantsLeftTranslation (g * h) =
      I.coinvariantsLeftTranslation h * I.coinvariantsLeftTranslation g := by
  ext x
  simp

/-- Translation by the inverse point inverts the automorphism of coinvariants. -/
@[simp]
theorem coinvariantsLeftTranslation_inv (g : WithConv (H →ₐ[R] R)) :
    I.coinvariantsLeftTranslation g⁻¹ = (I.coinvariantsLeftTranslation g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← coinvariantsLeftTranslation_mul, mul_inv_cancel, coinvariantsLeftTranslation_one]

/-- Pulling a restricted point back by a coinvariant left translation multiplies the
original point on the left before restricting it. -/
theorem comp_coinvariantsLeftTranslation (g : WithConv (H →ₐ[R] R))
    {A : Type*} [CommRing A] [Algebra R A] (a : WithConv (H →ₐ[R] A)) :
    (a.ofConv.comp I.coinvariants.val).comp (I.coinvariantsLeftTranslation g).toAlgHom =
      (AlgHom.mapValue (Algebra.ofId R A) g * a).ofConv.comp I.coinvariants.val := by
  ext x
  exact congrArg (fun f : WithConv (H →ₐ[R] A) ↦ f.ofConv x)
    (HopfAlgebra.toConv_comp_leftTranslationAlgEquiv g a)

end TauCeti.HopfIdeal
