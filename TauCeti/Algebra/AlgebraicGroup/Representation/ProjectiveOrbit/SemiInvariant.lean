/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.SubgroupWeights
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Semi-invariant projective orbit coordinates

If a vector transforms through a character of a closed subgroup, its homogeneous orbit
coordinates of degree `n` transform through the `n`th power of that character. Consequently
homogeneous fractions of degree zero are invariant under right multiplication by the subgroup.
These are the local coordinate identities needed to descend projective orbit morphisms to
homogeneous quotients. They apply to nonreduced subgroups and value algebras.

## Main results

* `HopfIdeal.convMul_apply_orbitCoordinates_of_mem_weightSpace`: homogeneous orbit coordinates
  transform by the corresponding power of the subgroup character.
* `HopfIdeal.isUnit_convMul_apply_orbitCoordinates_iff`: right subgroup translation preserves
  membership in a standard projective chart.
* `HopfIdeal.awayLift_convMul_apply_orbitCoordinates_eq`: the two translated points give the same
  map on the chart, including its nilpotent functions.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open HomogeneousLocalization WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v w x

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Degree-`n` homogeneous orbit coordinates of a subgroup weight vector are right
semi-invariants of character `χⁿ`. -/
theorem map_comul_orbitCoordinates_of_mem_weightSpace
    (I : HopfIdeal R H) (χ : GroupLike R (H ⧸ I.toIdeal))
    {m : M} (hm : m ∈ I.weightSpace M χ) {n : ℕ}
    {s : SymmetricAlgebra R (Module.Dual R M)}
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n) :
    ((Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)).comp
        (Bialgebra.comulAlgHom R H)) (Comodule.orbitCoordinates (H := H) m s) =
      Comodule.orbitCoordinates (H := H) m s ⊗ₜ[R] (χ.val ^ n) := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap a => simp
  | add x y i _ _ ihx ihy => simp only [map_add, ihx, ihy, TensorProduct.add_tmul]
  | mem_mul x hx i y _ ih =>
      obtain ⟨φ, rfl⟩ := hx
      have hχ := I.map_comul_matrixCoefficient_of_mem_weightSpace χ hm φ
      simp only [map_mul, Comodule.orbitCoordinates_ι, ih, pow_succ]
      rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
        ← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
        TensorProduct.AlgebraTensorModule.map_eq, AlgHom.toLinearMap_id, hχ]
      simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

section Points

variable {A : Type x} [CommSemiring A] [Algebra R A]

/-- Right multiplication by a subgroup point rescales a homogeneous orbit coordinate of
degree `n` by the `n`th power of the value of the subgroup character. -/
theorem convMul_apply_orbitCoordinates_of_mem_weightSpace
    (I : HopfIdeal R H) (χ : GroupLike R (H ⧸ I.toIdeal))
    {m : M} (hm : m ∈ I.weightSpace M χ)
    (g : WithConv (H →ₐ[R] A)) (h : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A))
    {n : ℕ} {s : SymmetricAlgebra R (Module.Dual R M)}
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n) :
    (g * toConv (h.ofConv.comp (Ideal.Quotient.mkₐ R I.toIdeal))).ofConv
        (Comodule.orbitCoordinates (H := H) m s) =
      h.ofConv χ.val ^ n * g.ofConv (Comodule.orbitCoordinates (H := H) m s) := by
  rw [AlgHom.convMul_apply]
  have he : (Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ .all _ _)).comp
      (Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)) =
      Algebra.TensorProduct.lift g.ofConv
        (h.ofConv.comp (Ideal.Quotient.mkₐ R I.toIdeal)) (fun _ _ ↦ .all _ _) := by
    ext <;> simp
  rw [← he, AlgHom.comp_apply]
  have hsemi := I.map_comul_orbitCoordinates_of_mem_weightSpace χ hm hs
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at hsemi
  rw [hsemi]
  simp [Algebra.TensorProduct.lift_tmul, mul_comm]

/-- A right subgroup translate lies in the same standard projective chart as the original
point: its homogeneous coordinate is a unit exactly when the original coordinate is. -/
theorem isUnit_convMul_apply_orbitCoordinates_iff
    (I : HopfIdeal R H) (χ : GroupLike R (H ⧸ I.toIdeal))
    {m : M} (hm : m ∈ I.weightSpace M χ)
    (g : WithConv (H →ₐ[R] A)) (h : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A))
    {n : ℕ} {s : SymmetricAlgebra R (Module.Dual R M)}
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n) :
    IsUnit ((g * toConv (h.ofConv.comp (Ideal.Quotient.mkₐ R I.toIdeal))).ofConv
        (Comodule.orbitCoordinates (H := H) m s)) ↔
      IsUnit (g.ofConv (Comodule.orbitCoordinates (H := H) m s)) := by
  rw [I.convMul_apply_orbitCoordinates_of_mem_weightSpace χ hm g h hs, IsUnit.mul_iff]
  exact and_iff_right ((χ.2.isUnit.map h.ofConv).pow n)

end Points

section Charts

variable {A : Type x} [CommRing A] [Algebra R A]

/-- The maps on a homogeneous affine chart defined by a group point and its right subgroup
translate agree. This is equality of ring maps, including on nilpotent functions. -/
theorem awayLift_convMul_apply_orbitCoordinates_eq
    (I : HopfIdeal R H) (χ : GroupLike R (H ⧸ I.toIdeal))
    {m : M} (hm : m ∈ I.weightSpace M χ)
    (g : WithConv (H →ₐ[R] A)) (h : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A))
    {d : ℕ} {s : SymmetricAlgebra R (Module.Dual R M)}
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) d)
    (hg : IsUnit (g.ofConv (Comodule.orbitCoordinates (H := H) m s))) :
    Away.lift (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))
        (((g * toConv (h.ofConv.comp (Ideal.Quotient.mkₐ R I.toIdeal))).ofConv).comp
          (Comodule.orbitCoordinates (H := H) m)).toRingHom
        ((I.isUnit_convMul_apply_orbitCoordinates_iff χ hm g h hs).mpr hg) =
      Away.lift (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))
        (g.ofConv.comp (Comodule.orbitCoordinates (H := H) m)).toRingHom hg := by
  apply Away.lift_eq_of_forall_mem _ _
    (Units.map h.ofConv.toMonoidHom (_root_.GroupLike.toUnits R χ)) _ hs
  intro n a ha
  simpa [_root_.GroupLike.toUnits] using
    I.convMul_apply_orbitCoordinates_of_mem_weightSpace χ hm g h ha

end Charts

end TauCeti.HopfIdeal
