/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import TauCeti.Algebra.DualNumber.Automorphism
public import TauCeti.LinearAlgebra.CliffordAlgebra.GeneratorAutomorphisms

/-!
# Vector-preserving automorphisms for the zero form

The vector stabilizer `CliffordAlgebra.vectorStabilizer Q`, the group of algebra automorphisms of
`CliffordAlgebra Q` that map the vectors onto themselves, is the image of the orthogonal group of
`Q` (`CliffordAlgebra.orthogonalGroupEquivVectorStabilizer`), with no nondegeneracy hypothesis on
`Q`. This file works out the degenerate extreme, the zero form, where the Clifford algebra is the
exterior algebra.

* Every linear automorphism of `M` is an isometry of the zero form, so the vector stabilizer of
  `ExteriorAlgebra R M` is a copy of the group of linear automorphisms of `M`, acting through the
  exterior algebra functor `ExteriorAlgebra.map`
  (`ExteriorAlgebra.linearEquivEquivVectorStabilizer`).
* When `M` is subsingleton, the Clifford algebra is `R`: the identity is its only automorphism,
  and it lies in the vector stabilizer (`CliffordAlgebra.vectorStabilizer_eq_top_of_subsingleton`).
* On the line `M = R` the Clifford algebra of the zero form is the dual numbers `R[ε]`, and over a
  reduced ring every automorphism of `R[ε]` is `ε ↦ u • ε` for a unit `u`
  (`DualNumber.mapEquivMulEquiv`). So every automorphism preserves the vectors
  (`CliffordAlgebra.vectorStabilizer_zero_line_eq_top`), and the isometry attached to `ε ↦ u • ε`
  is the multiplication by `u`
  (`CliffordAlgebra.autCongr_dualNumberEquiv_linearEquivEquivVectorStabilizer`).

In higher rank the vector stabilizer of the exterior algebra is in general a proper subgroup of
all automorphisms: for instance, on `⋀(R²)` the assignment `e₁ ↦ e₁ + e₁ ∧ e₂`, `e₂ ↦ e₂`
extends to an automorphism that moves the vector `e₁` out of `R²`.

## Main definitions

* `ExteriorAlgebra.linearEquivEquivVectorStabilizer`: the group isomorphism from the linear
  automorphisms of `M` onto the vector stabilizer of `ExteriorAlgebra R M`.

## Main results

* `ExteriorAlgebra.toAlgHom_linearEquivEquivVectorStabilizer_apply`: the automorphism attached to
  `f` is `ExteriorAlgebra.map f`.
* `CliffordAlgebra.vectorStabilizer_eq_top_of_subsingleton`: the case `M = 0`.
* `CliffordAlgebra.vectorStabilizer_zero_line_eq_top`: on a line over a reduced ring, every
  automorphism of the Clifford algebra of the zero form preserves the vectors.
* `CliffordAlgebra.autCongr_dualNumberEquiv_linearEquivEquivVectorStabilizer`: read on the dual
  numbers, the automorphism attached to a linear automorphism `e` of `R` is
  `TrivSqZeroExt.mapEquiv e`.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.3 and Theorem 1.4.
-/

public section

open CliffordAlgebra TrivSqZeroExt

universe u v

/-! ### The zero form: the exterior algebra -/

namespace ExteriorAlgebra

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {M : Type v} [AddCommGroup M]
  [Module R M]

variable (R M) in
/-- **The vector stabilizer of the exterior algebra.** Every linear automorphism `f` of `M` is an
isometry of the zero form, so it induces an automorphism of `ExteriorAlgebra R M` that maps the
vectors onto themselves, namely `ExteriorAlgebra.map f`
(`ExteriorAlgebra.toAlgHom_linearEquivEquivVectorStabilizer_apply`). Every automorphism of the
exterior algebra that maps the vectors onto themselves arises from exactly one `f`, and
composition of automorphisms corresponds to composition of linear maps. -/
noncomputable def linearEquivEquivVectorStabilizer :
    (M ≃ₗ[R] M) ≃* vectorStabilizer (0 : QuadraticForm R M) :=
  -- Every linear automorphism of `M` preserves the zero form.
  ((MulEquiv.subgroupCongr (eq_top_iff.mpr fun _ _ ↦
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun _ ↦ rfl)).trans
    Subgroup.topEquiv).symm.trans (orthogonalGroupEquivVectorStabilizer 0)

/-- On generators, the automorphism attached to `f` applies `f`. -/
@[simp]
theorem linearEquivEquivVectorStabilizer_apply_ι (f : M ≃ₗ[R] M) (m : M) :
    (linearEquivEquivVectorStabilizer R M f :
      ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) (ι R m) = ι R (f m) := by
  rw [linearEquivEquivVectorStabilizer, MulEquiv.trans_apply,
    orthogonalGroupEquivVectorStabilizer_apply_ι]
  simp

/-- **The vector stabilizer acts through the exterior algebra functor**: the automorphism attached
to a linear automorphism `f` of `M` is `ExteriorAlgebra.map f`. -/
@[simp]
theorem toAlgHom_linearEquivEquivVectorStabilizer_apply (f : M ≃ₗ[R] M) :
    ((linearEquivEquivVectorStabilizer R M f : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) :
      ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M) = map (f : M →ₗ[R] M) :=
  hom_ext <| LinearMap.ext fun m ↦ by
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
      linearEquivEquivVectorStabilizer_apply_ι, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      map_apply_ι, LinearEquiv.coe_coe]

/-- The linear automorphism underlying `φ` in the vector stabilizer of the exterior algebra is
characterized by its action on generators. -/
@[simp]
theorem ι_linearEquivEquivVectorStabilizer_symm_apply
    (φ : vectorStabilizer (0 : QuadraticForm R M)) (m : M) :
    ι R ((linearEquivEquivVectorStabilizer R M).symm φ m) =
      (φ : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) (ι R m) := by
  conv_rhs => rw [← (linearEquivEquivVectorStabilizer R M).apply_symm_apply φ,
    linearEquivEquivVectorStabilizer_apply_ι]

end ExteriorAlgebra

namespace CliffordAlgebra

/-! ### The zero module -/

section Subsingleton

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Subsingleton M]
  (Q : QuadraticForm R M)

/-- When `M` is subsingleton, an algebra map out of `CliffordAlgebra Q` is determined by its
values on generators, all of which are `0`. -/
instance subsingleton_algHom_of_subsingleton {A : Type*} [Semiring A] [Algebra R A] :
    Subsingleton (CliffordAlgebra Q →ₐ[R] A) :=
  ⟨fun _ _ ↦ hom_ext <| Subsingleton.elim _ _⟩

/-- When `M` is subsingleton, the identity is the only automorphism of `CliffordAlgebra Q`. -/
instance subsingleton_algEquiv_of_subsingleton :
    Subsingleton (CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q) :=
  AlgEquiv.coe_toAlgHom_injective.subsingleton

/-- **The case `M = 0`.** When `M` is subsingleton, the only automorphism of `CliffordAlgebra Q`
is the identity, and it maps the vectors onto themselves. -/
theorem vectorStabilizer_eq_top_of_subsingleton : vectorStabilizer Q = ⊤ :=
  Subsingleton.elim _ _

end Subsingleton

/-! ### The zero form on a line: the dual numbers -/

section DualNumber

variable {R : Type u} [CommRing R]

/-- On generators, the identification `CliffordAlgebraDualNumber.equiv` of the Clifford algebra of
the zero form on `R` with the dual numbers is `r ↦ inr r`. -/
private theorem dualNumberEquiv_ι (r : R) :
    CliffordAlgebraDualNumber.equiv (ι (0 : QuadraticForm R R) r) = inr r := by
  rw [CliffordAlgebraDualNumber.equiv_ι, DualNumber.inr_eq_smul_eps]

/-- Transporting `TrivSqZeroExt.mapEquiv e` from the dual numbers to the Clifford algebra of the
zero form on `R` gives the automorphism induced by `e`. -/
private theorem autCongr_symm_mapEquiv (e : R ≃ₗ[R] R) :
    CliffordAlgebraDualNumber.equiv.autCongr.symm (mapEquiv e) =
      equivOfIsometry { e with map_app' := fun _ ↦ rfl } := by
  refine algEquiv_ext_ι fun r ↦ CliffordAlgebraDualNumber.equiv.injective ?_
  rw [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.symm_symm, AlgEquiv.trans_apply,
    AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, dualNumberEquiv_ι, coe_mapEquiv, map_inr,
    equivOfIsometry_apply, map_apply_ι, dualNumberEquiv_ι]
  simp [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- **The zero form on a line.** Over a reduced ring, every algebra automorphism of the Clifford
algebra of the zero form on `R`, which is the dual numbers `R[ε]`, maps the vectors `R • ε` onto
themselves: such an automorphism is `ε ↦ u • ε` for a unit `u` (`DualNumber.mapEquivMulEquiv`). -/
theorem vectorStabilizer_zero_line_eq_top [IsReduced R] :
    vectorStabilizer (0 : QuadraticForm R R) = ⊤ := by
  refine eq_top_iff.mpr fun φ _ ↦ mem_vectorStabilizer_iff.mpr ?_
  obtain ⟨e, he⟩ := DualNumber.exists_mapEquiv_eq (CliffordAlgebraDualNumber.equiv.autCongr φ)
  rw [← CliffordAlgebraDualNumber.equiv.autCongr.symm_apply_apply φ, ← he, autCongr_symm_mapEquiv]
  exact ι_range_map_equivOfIsometry _

/-- **The correspondence on the dual numbers.** Read on the dual numbers through
`CliffordAlgebraDualNumber.equiv`, the vector-preserving automorphism attached to a linear
automorphism `e` of `R` is `TrivSqZeroExt.mapEquiv e`; for the multiplication by a unit `u` this
is `ε ↦ u • ε`. Together with `CliffordAlgebra.vectorStabilizer_zero_line_eq_top` this identifies
the isometry group `GL₁(R)` of the zero form with all automorphisms of `R[ε]`, by `u ↦ u`. -/
theorem autCongr_dualNumberEquiv_linearEquivEquivVectorStabilizer [Invertible (2 : R)]
    (e : R ≃ₗ[R] R) :
    CliffordAlgebraDualNumber.equiv.autCongr
        (ExteriorAlgebra.linearEquivEquivVectorStabilizer R R e :
          CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] CliffordAlgebra (0 : QuadraticForm R R)) =
      mapEquiv e := by
  rw [← MulEquiv.eq_symm_apply, autCongr_symm_mapEquiv]
  refine algEquiv_ext_ι fun r ↦ ?_
  rw [ExteriorAlgebra.linearEquivEquivVectorStabilizer_apply_ι, equivOfIsometry_apply,
    map_apply_ι]
  simp [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

end DualNumber

end CliffordAlgebra
