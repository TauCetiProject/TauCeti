/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# A pointwise criterion for an ideal to be a Hopf ideal

If the points annihilating an ideal form a subgroup over every value algebra, then that
ideal is a Hopf ideal. Multiplication can be tested on the two universal quotient-valued
points over the tensor square of the quotient. Inversion can be tested on the universal
quotient-valued point, and the identity detects the counit condition.

This criterion turns equations representing a subgroup functor into a closed subgroup
scheme without separately calculating the comultiplication of each equation.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- An ideal cutting out subgroups over every value algebra is a Hopf ideal. The subgroup
family need not be given separate naturality data: its equations already imply naturality. -/
noncomputable def ofIdealOfPointsSubgroup (I : Ideal H)
    (S : ∀ A : CommAlgCat.{v} R, Subgroup (WithConv (H →ₐ[R] A)))
    (hS : ∀ (A : CommAlgCat.{v} R) (g : WithConv (H →ₐ[R] A)),
      g ∈ S A ↔ I ≤ RingHom.ker g.ofConv) : HopfIdeal R H := by
  let Q := H ⧸ I
  let q : H →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  have hqker : RingHom.ker q = I := by
    rw [← RingHom.ker_coe_toRingHom]
    exact Ideal.Quotient.mkₐ_ker R I
  have hq : I ≤ RingHom.ker q := hqker.symm.le
  have hcomul {x : H} (hx : x ∈ I) :
      Coalgebra.comul (R := R) x ∈ leftTensorIdeal R H I ⊔
        rightTensorIdeal R H I := by
    let A := CommAlgCat.of R (Q ⊗[R] Q)
    let g : WithConv (H →ₐ[R] A) :=
      toConv ((Algebra.TensorProduct.includeLeft : Q →ₐ[R] Q ⊗[R] Q).comp q)
    let h : WithConv (H →ₐ[R] A) :=
      toConv ((Algebra.TensorProduct.includeRight : Q →ₐ[R] Q ⊗[R] Q).comp q)
    have hg : g ∈ S A := (hS A g).mpr fun y hy ↦ by
      simp only [g, AlgHom.comp_apply, RingHom.mem_ker]
      rw [RingHom.mem_ker.mp (hq hy), map_zero]
    have hh : h ∈ S A := (hS A h).mpr fun y hy ↦ by
      simp only [h, AlgHom.comp_apply, RingHom.mem_ker]
      rw [RingHom.mem_ker.mp (hq hy), map_zero]
    have hzero := RingHom.mem_ker.mp ((hS A (g * h)).mp ((S A).mul_mem hg hh) hx)
    have hmap : Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ .all ..) =
        Algebra.TensorProduct.map q q := by
      dsimp [g, h, A]
      ext a <;> simp
    rw [AlgHom.convMul_apply, hmap] at hzero
    have hker := ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal q q
      (Ideal.Quotient.mkₐ_surjective R I) (Ideal.Quotient.mkₐ_surjective R I)
    rw [hqker] at hker
    exact hker ▸ RingHom.mem_ker.mpr hzero
  have hcounit {x : H} (hx : x ∈ I) : Coalgebra.counit (R := R) x = 0 := by
    have hz := RingHom.mem_ker.mp ((hS (CommAlgCat.of R H) 1).mp
      ((S (CommAlgCat.of R H)).one_mem) hx)
    have hc := congrArg (Bialgebra.counitAlgHom R H) hz
    simpa only [AlgHom.convOne_apply, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, map_zero] using hc
  have hantipode {x : H} (hx : x ∈ I) : HopfAlgebra.antipode R x ∈ I := by
    have hg : toConv q ∈ S (CommAlgCat.of R Q) :=
      (hS _ _).mpr hq
    have hz := RingHom.mem_ker.mp ((hS _ _).mp ((S _).inv_mem hg) hx)
    rw [WithConv.convInv_apply] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact ofIdeal I (fun _ hx ↦ hcomul hx) (fun _ hx ↦ hcounit hx)
    (fun _ hx ↦ hantipode hx)

/-- The pointwise construction leaves the defining ideal unchanged. -/
@[simp]
theorem ofIdealOfPointsSubgroup_toIdeal (I : Ideal H) (S hS) :
    (ofIdealOfPointsSubgroup (R := R) I S hS).toIdeal = I := (rfl)

end TauCeti.HopfIdeal
