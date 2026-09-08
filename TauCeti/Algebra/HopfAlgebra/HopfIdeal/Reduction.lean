/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic

/-!
# Reduction of commutative Hopf algebras

Let `H` be a commutative Hopf algebra over a reduced commutative ring. Its nilradical is
automatically stable under the counit and antipode. It is stable under comultiplication provided
the tensor square of the reduced algebra is reduced: the image of a nilpotent element under
comultiplication is nilpotent, hence vanishes in that tensor square. Thus reducedness of this
tensor square is a sufficient hypothesis for packaging the nilradical as a Hopf ideal.

The tensor-square hypothesis ensures that reduction commutes with the product used by the
comultiplication. It holds, in particular, for finite-type algebras over a perfect field once the
standard geometric-reducedness theorem is available. Keeping it explicit here separates the
Hopf-algebra argument from that commutative-algebra input.

## Main declarations

* `TauCeti.HopfIdeal.reduction`: the nilradical, packaged as a Hopf ideal.
* `TauCeti.HopfIdeal.reduction_toIdeal`: its underlying ideal is the nilradical.
* `TauCeti.HopfIdeal.mem_reduction`: membership is nilpotence.
* `TauCeti.HopfIdeal.reduction_le_of_isReduced_quotient`: its minimality among Hopf ideals with
  reduced quotient.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
* J. S. Milne, *Algebraic Groups* (2017), §1.f.
-/

public section

open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v

variable (R : Type u) [CommRing R] [IsReduced R]
variable (H : Type v) [CommRing H] [HopfAlgebra R H]

private theorem nilradical_counit_eq_zero {x : H} (hx : x ∈ nilradical H) :
    Coalgebra.counit (R := R) x = 0 := by
  rw [mem_nilradical] at hx
  exact isNilpotent_iff_eq_zero.mp (hx.map (Bialgebra.counitAlgHom R H))

omit [IsReduced R] in
private theorem nilradical_antipode_mem {x : H} (hx : x ∈ nilradical H) :
    HopfAlgebra.antipode R x ∈ nilradical H := by
  rw [mem_nilradical] at hx ⊢
  simpa only [HopfAlgebra.antipodeAlgHom_apply] using
    hx.map (HopfAlgebra.antipodeAlgHom R H)

omit [IsReduced R] in
private theorem nilradical_comul_mem
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    {x : H} (hx : x ∈ nilradical H) :
    Coalgebra.comul (R := R) x ∈
      leftTensorIdeal (R := R) (H := H) (nilradical H) ⊔
        rightTensorIdeal (R := R) (H := H) (nilradical H) := by
  let q : H →ₐ[R] H ⧸ nilradical H := Ideal.Quotient.mkₐ R (nilradical H)
  have hnil : IsNilpotent (Coalgebra.comul (R := R) x) :=
    (mem_nilradical.mp hx).map (Bialgebra.comulAlgHom R H)
  have hzero : Algebra.TensorProduct.map q q (Coalgebra.comul (R := R) x) = 0 :=
    isNilpotent_iff_eq_zero.mp (hnil.map (Algebra.TensorProduct.map q q))
  have hker : RingHom.ker (Algebra.TensorProduct.map q q).toRingHom =
      leftTensorIdeal (R := R) (H := H) (nilradical H) ⊔
        rightTensorIdeal (R := R) (H := H) (nilradical H) := by
    have hqker : RingHom.ker q = nilradical H := Ideal.Quotient.mkₐ_ker R (nilradical H)
    simpa only [AlgHom.ker_coe, AlgHom.toRingHom_eq_coe, hqker] using
        HopfIdeal.ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal q q
          (Ideal.Quotient.mkₐ_surjective R (nilradical H))
          (Ideal.Quotient.mkₐ_surjective R (nilradical H))
  rw [← hker, RingHom.mem_ker]
  exact hzero

/-- The nilradical of a commutative Hopf algebra, as a Hopf ideal.

Assuming the tensor square of the reduced algebra is reduced, the comultiplication descends: a
nilpotent element maps to a nilpotent element of that tensor square and therefore to zero. -/
noncomputable def reduction
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] : HopfIdeal R H :=
  ofIdeal (nilradical H)
    (fun {x} hx ↦ nilradical_comul_mem R H (x := x) hx)
    (fun {x} hx ↦ nilradical_counit_eq_zero R H (x := x) hx)
    (fun {x} hx ↦ nilradical_antipode_mem R H (x := x) hx)

/-- The underlying ideal of the reduction Hopf ideal is the nilradical. -/
@[simp]
theorem reduction_toIdeal
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] :
    (reduction R H).toIdeal = nilradical H := by
  rw [reduction, toIdeal_carrier, ofIdeal_carrier]

/-- Membership in the reduction Hopf ideal is nilpotence. -/
@[simp]
theorem mem_reduction
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] {x : H} :
    x ∈ reduction R H ↔ IsNilpotent x := by
  rw [← mem_toIdeal, reduction_toIdeal, mem_nilradical]

/-- The reduction is contained in every Hopf ideal whose quotient is reduced. -/
theorem reduction_le_of_isReduced_quotient
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    (I : HopfIdeal R H) [IsReduced (H ⧸ I.toIdeal)] :
    reduction R H ≤ I := by
  rw [← toIdeal_le_toIdeal, reduction_toIdeal, nilradical]
  exact ((Ideal.isRadical_iff_quotient_reduced I.toIdeal).mpr inferInstance).radical_le_iff.mpr
    bot_le

end TauCeti.HopfIdeal
