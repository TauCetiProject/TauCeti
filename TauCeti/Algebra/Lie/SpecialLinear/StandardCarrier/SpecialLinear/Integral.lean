/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Smooth.Flat
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.AllRootSubgroups.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.SpecialLinear

/-!
# Integral comparison of the type A carrier with the special linear group

The full-weight type `A_r` Kostant carrier has exactly the determinant-one defining ideal
already over `ℤ`. To descend the known equality over an algebraic closure of `ℚ`, we use
flatness of the smooth special-linear coordinate algebra. No flatness assumption on the
Kostant carrier is needed.

The resulting coordinate Hopf isomorphism preserves every pair-indexed root map and transfers
smoothness to the integral carrier. These are the inputs for its stored pinning in
`StandardCarrier.SpecialLinear.Pinning`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.SlStd

noncomputable section

attribute [local instance high] Algebra.toModule

variable (r : ℕ)

/-- The full-weight type `A_r` carrier is cut out by the determinant-one equation over `ℤ`,
including rank zero. -/
theorem definingIdeal_eq_specialLinearDefiningHopfIdeal :
    definingIdeal r = SpecialLinear.definingHopfIdeal ℤ (r + 1) := by
  apply le_antisymm
  · let K := AlgebraicClosure ℚ
    apply (CommHopfAlgCat.baseChangeHopfIdeal_le_iff (K := K)
      (by exact Int.cast_injective)).mp
    rw [← HopfIdeal.toIdeal_le_toIdeal, CommHopfAlgCat.baseChangeHopfIdeal_toIdeal,
      Ideal.map_le_iff_le_comap]
    intro f hf
    have hmem :
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ K (r + 1)).hom.hom
            ((1 : K) ⊗ₜ[ℤ] f) ∈ baseChangeDefiningIdeal r K := by
      rw [baseChangeDefiningIdeal_def]
      exact UniversalEnvelopingAlgebra.map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem
        (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) K (1 : K) hf
    rw [baseChangeDefiningIdeal_eq_specialLinearDefiningHopfIdeal] at hmem
    have hzero : (SpecialLinear.coordinateMap K (r + 1)).hom
        ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ K (r + 1)).hom.hom
          ((1 : K) ⊗ₜ[ℤ] f)) = 0 :=
      (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).2 hmem
    have ht : (1 : K) ⊗ₜ[ℤ] (SpecialLinear.coordinateMap ℤ (r + 1)).hom f = 0 := by
      apply (ConcreteCategory.bijective_of_isIso
        (SpecialLinear.coordinateHopfAlgebraBaseChangeIso ℤ K (r + 1)).hom).1
      exact (SpecialLinear.coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap
        ℤ K (r + 1) 1 f).trans (hzero.trans (map_zero _).symm)
    exact (CommHopfAlgCat.mem_baseChangeHopfIdeal_iff _ _).2 <| by
      simpa only [Algebra.TensorProduct.includeRight_apply] using
        (CommHopfAlgCat.baseChangeMap_apply_tmul (K := K)
          (SpecialLinear.coordinateMap ℤ (r + 1)) 1 f).trans ht
  · exact specialLinearDefiningHopfIdeal_le_kostantToralDefiningIdeal r

/-- The integral carrier--special-linear isomorphism induced by equality of defining ideals. -/
def coordinateSpecialLinearIso :
    coordinateHopfAlgebra r ≅ SpecialLinear.coordinateHopfAlgebra ℤ (r + 1) :=
  eqToIso (congrArg (CommHopfAlgCat.quotient
    (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)))
      (definingIdeal_eq_specialLinearDefiningHopfIdeal r))

/-- The integral comparison identifies the two quotient maps from the general-linear algebra. -/
@[simp]
theorem mkQuotient_comp_coordinateSpecialLinearIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r) ≫ (coordinateSpecialLinearIso r).hom =
      SpecialLinear.coordinateMap ℤ (r + 1) := by
  exact CommHopfAlgCat.mkQuotient_comp_eqToHom
    (definingIdeal_eq_specialLinearDefiningHopfIdeal r).symm

/-- Every elementary root map retains its additive parameter under the integral comparison. -/
@[simp]
theorem coordinateSpecialLinearIso_hom_comp_rootSubgroupCoordinateMap
    {i j : Fin (r + 1)} (hij : i ≠ j) :
    (coordinateSpecialLinearIso r).hom ≫ SpecialLinear.rootSubgroupCoordinateMap hij =
      rootSubgroupCoordinateMapOfPair r hij := by
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [← Category.assoc, mkQuotient_comp_coordinateSpecialLinearIso_hom,
    SpecialLinear.coordinateMap_comp_rootSubgroupCoordinateMap,
    mkQuotient_comp_rootSubgroupCoordinateMapOfPair]

instance : Algebra.Smooth ℤ (coordinateHopfAlgebra r) :=
  Algebra.Smooth.of_equiv
    (_root_.CommHopfAlgCat.ofIso (coordinateSpecialLinearIso r).symm).toAlgEquiv

end

end TauCeti.SlStd
