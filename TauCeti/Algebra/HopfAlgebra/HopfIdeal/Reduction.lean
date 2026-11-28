/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic
public import TauCeti.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reduction of commutative Hopf algebras

Let `H` be a commutative Hopf algebra over a reduced commutative ring. Its nilradical is
automatically stable under the counit and antipode. It is stable under comultiplication provided
the tensor square of the reduced algebra is reduced: the image of a nilpotent element under
comultiplication is nilpotent, hence vanishes in that tensor square. Thus reducedness of this
tensor square is a sufficient hypothesis for packaging the nilradical as a Hopf ideal.

The tensor-square hypothesis ensures that reduction commutes with the product used by the
comultiplication. It holds, in particular, for finite-type algebras over a perfect field by
geometric reducedness. Keeping it explicit here separates the Hopf-algebra argument from that
commutative-algebra input.

## Main declarations

* `TauCeti.HopfIdeal.reduction`: the nilradical, packaged as a Hopf ideal.
* `TauCeti.HopfIdeal.reduction_toIdeal`: its underlying ideal is the nilradical.
* `TauCeti.HopfIdeal.mem_reduction`: membership is nilpotence.
* `TauCeti.HopfIdeal.isReduced_quotient_reduction`: the quotient is reduced.
* `TauCeti.HopfIdeal.reduction_le_of_isReduced_quotient`: its minimality among Hopf ideals with
  reduced quotient.
* `TauCeti.HopfIdeal.map_eq_zero_of_mem_reduction`: any ring homomorphism into a reduced semiring
  kills the reduction ideal.
* `TauCeti.HopfIdeal.reductionBialgHom`, `TauCeti.HopfIdeal.reductionBialgHom_comp_mkBialgHom`,
  `TauCeti.HopfIdeal.reductionBialgHom_id`, and `TauCeti.HopfIdeal.reductionBialgHom_comp`:
  functoriality of the reduced quotient for bialgebra morphisms.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
* J. S. Milne, *Algebraic Groups* (2017), §1.f.
-/

public section

open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v w x

variable (R : Type u) [CommRing R] [IsReduced R]
variable (H : Type v) [CommRing H] [HopfAlgebra R H]

/-- The nilradical of a commutative Hopf algebra, as a Hopf ideal.

Assuming the tensor square of the reduced algebra is reduced, the comultiplication descends: a
nilpotent element maps to a nilpotent element of that tensor square and therefore to zero. -/
noncomputable def reduction
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] : HopfIdeal R H :=
  ofIdeal (nilradical H)
    (fun {x} hx ↦ by
      let q : H →ₐ[R] H ⧸ nilradical H := Ideal.Quotient.mkₐ R (nilradical H)
      have hker := AlgHom.ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal q q
        (Ideal.Quotient.mkₐ_surjective R (nilradical H))
        (Ideal.Quotient.mkₐ_surjective R (nilradical H))
      simp only [AlgHom.ker_coe, q, Ideal.Quotient.mkₐ_ker] at hker
      rw [← hker, RingHom.mem_ker]
      exact (((mem_nilradical.mp hx).map (Bialgebra.comulAlgHom R H)).map
        (Algebra.TensorProduct.map q q)).eq_zero)
    (fun {_} hx ↦ ((mem_nilradical.mp hx).map (Bialgebra.counitAlgHom R H)).eq_zero)
    (fun {_} hx ↦ mem_nilradical.mpr
      ((mem_nilradical.mp hx).map (HopfAlgebra.antipodeAlgHom R H)))

/-- The underlying ideal of the reduction Hopf ideal is the nilradical. -/
@[simp]
theorem reduction_toIdeal
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] :
    (reduction R H).toIdeal = nilradical H :=
  (toIdeal_carrier _).trans (ofIdeal_carrier _ _ _ _)

/-- Membership in the reduction Hopf ideal is nilpotence. -/
@[simp]
theorem mem_reduction
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] {x : H} :
    x ∈ reduction R H ↔ IsNilpotent x := by
  rw [← mem_toIdeal, reduction_toIdeal, mem_nilradical]

/-- The quotient by the reduction Hopf ideal is reduced. -/
instance isReduced_quotient_reduction
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] :
    IsReduced (H ⧸ (reduction R H).toIdeal) := by
  rw [reduction_toIdeal]
  infer_instance

/-- The reduction is contained in every Hopf ideal whose quotient is reduced. -/
theorem reduction_le_of_isReduced_quotient
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    (I : HopfIdeal R H) [IsReduced (H ⧸ I.toIdeal)] :
    reduction R H ≤ I := by
  rw [← toIdeal_le_toIdeal, reduction_toIdeal, nilradical]
  exact ((Ideal.isRadical_iff_quotient_reduced I.toIdeal).mpr inferInstance).radical_le_iff.mpr
    bot_le

/-- Any ring homomorphism from `H` into a reduced semiring kills `(reduction R H).toIdeal`. -/
theorem map_eq_zero_of_mem_reduction {R : Type u} [CommRing R] [IsReduced R]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    {A : Type*} [Semiring A] [IsReduced A]
    (f : H →+* A) {x : H} (hx : x ∈ (reduction R H).toIdeal) :
    f x = 0 :=
  (((mem_reduction R H).mp (mem_toIdeal.mp hx)).map f).eq_zero

/-- A bialgebra morphism `φ : H →ₐc[R] H'` descends to a bialgebra morphism between the reduced
quotients `H ⧸ (reduction R H).toIdeal` and `H' ⧸ (reduction R H').toIdeal`, because it maps
nilpotent elements to nilpotent elements. -/
noncomputable def reductionBialgHom {R : Type u} [CommRing R] [IsReduced R]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    [IsReduced ((H' ⧸ nilradical H') ⊗[R] (H' ⧸ nilradical H'))]
    (φ : H →ₐc[R] H') :
    H ⧸ (reduction R H).toIdeal →ₐc[R] H' ⧸ (reduction R H').toIdeal :=
  let q := Bialgebra.Quotient.mkBialgHom (reduction R H').toIdeal
  Bialgebra.Quotient.liftBialgHom (reduction R H).toIdeal (q.comp φ) fun _ hx =>
    map_eq_zero_of_mem_reduction (q.comp φ).toAlgHom.toRingHom hx

/-- The reduced morphism commutes with the quotient bialgebra homomorphisms. -/
@[simp]
theorem reductionBialgHom_comp_mkBialgHom {R : Type u} [CommRing R] [IsReduced R]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    [IsReduced ((H' ⧸ nilradical H') ⊗[R] (H' ⧸ nilradical H'))]
    (φ : H →ₐc[R] H') :
    (reductionBialgHom φ).comp (Bialgebra.Quotient.mkBialgHom (reduction R H).toIdeal) =
      (Bialgebra.Quotient.mkBialgHom (reduction R H').toIdeal).comp φ :=
  Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom _ _ _

/-- The reduced morphism of the identity bialgebra homomorphism is the identity. -/
@[simp]
theorem reductionBialgHom_id {R : Type u} [CommRing R] [IsReduced R]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] :
    reductionBialgHom (BialgHom.id R H) = BialgHom.id R (H ⧸ (reduction R H).toIdeal) := by
  apply Bialgebra.Quotient.bialgHom_ext
  rw [reductionBialgHom_comp_mkBialgHom, BialgHom.comp_id, BialgHom.id_comp]

/-- Composition of reduced morphisms agrees with the reduced morphism of the composite. -/
@[simp]
theorem reductionBialgHom_comp {R : Type u} [CommRing R] [IsReduced R]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    [IsReduced ((H' ⧸ nilradical H') ⊗[R] (H' ⧸ nilradical H'))]
    {H'' : Type x} [CommRing H''] [HopfAlgebra R H'']
    [IsReduced ((H'' ⧸ nilradical H'') ⊗[R] (H'' ⧸ nilradical H''))]
    (ψ : H' →ₐc[R] H'') (φ : H →ₐc[R] H') :
    (reductionBialgHom ψ).comp (reductionBialgHom φ) = reductionBialgHom (ψ.comp φ) := by
  apply Bialgebra.Quotient.bialgHom_ext
  calc
    ((reductionBialgHom ψ).comp (reductionBialgHom φ)).comp
        (Bialgebra.Quotient.mkBialgHom (reduction R H).toIdeal)
      = (reductionBialgHom ψ).comp
          ((reductionBialgHom φ).comp (Bialgebra.Quotient.mkBialgHom (reduction R H).toIdeal)) :=
        BialgHom.comp_assoc _ _ _
    _ = (reductionBialgHom ψ).comp
          ((Bialgebra.Quotient.mkBialgHom (reduction R H').toIdeal).comp φ) := by
        rw [reductionBialgHom_comp_mkBialgHom]
    _ = ((reductionBialgHom ψ).comp
          (Bialgebra.Quotient.mkBialgHom (reduction R H').toIdeal)).comp φ :=
        (BialgHom.comp_assoc _ _ _).symm
    _ = ((Bialgebra.Quotient.mkBialgHom (reduction R H'').toIdeal).comp ψ).comp φ := by
        rw [reductionBialgHom_comp_mkBialgHom]
    _ = (Bialgebra.Quotient.mkBialgHom (reduction R H'').toIdeal).comp (ψ.comp φ) :=
        BialgHom.comp_assoc _ _ _
    _ = (reductionBialgHom (ψ.comp φ)).comp
          (Bialgebra.Quotient.mkBialgHom (reduction R H).toIdeal) :=
        (reductionBialgHom_comp_mkBialgHom (ψ.comp φ)).symm

end TauCeti.HopfIdeal
