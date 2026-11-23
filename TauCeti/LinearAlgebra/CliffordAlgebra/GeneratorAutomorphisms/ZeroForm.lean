/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DualNumber.Automorphism
public import TauCeti.LinearAlgebra.CliffordAlgebra.GeneratorAutomorphisms.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero

/-!
# Vector-preserving automorphisms for the zero form

The vector stabilizer `CliffordAlgebra.vectorStabilizer Q` is the group of algebra automorphisms of
`CliffordAlgebra Q` that map the vectors onto themselves. When `2` is invertible in `R`, it is the
image of the orthogonal group of `Q` (`CliffordAlgebra.orthogonalGroupEquivVectorStabilizer`),
with no nondegeneracy hypothesis on `Q`. This file works out the degenerate extreme, the zero form,
where the Clifford algebra is the exterior algebra; there the invertibility of `2` is not needed.

* Over every commutative ring, every linear automorphism of `M` is an isometry of the zero form,
  and the vector stabilizer of `ExteriorAlgebra R M` is a copy of the group of linear
  automorphisms of `M`, acting through the exterior algebra functor `ExteriorAlgebra.map`
  (`TauCeti.ExteriorAlgebra.linearEquivEquivVectorStabilizer`).
* When `M` is subsingleton, the Clifford algebra is `R`: the identity is its only automorphism,
  and it lies in the vector stabilizer
  (`TauCeti.CliffordAlgebra.vectorStabilizer_eq_top_of_subsingleton`).
* On the line `M = R` the Clifford algebra of the zero form is the dual numbers `R[ε]`. If `R` has
  no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`, for instance if `R` is reduced or `2` is
  invertible in `R`, then every automorphism of `R[ε]` is `ε ↦ u • ε` for a unit `u`
  (`TauCeti.DualNumber.mapEquivMulEquiv`). So every automorphism preserves the vectors
  (`TauCeti.CliffordAlgebra.vectorStabilizer_zero_line_eq_top`). Over every commutative ring, the
  automorphism attached to the multiplication by `u` is `ε ↦ u • ε`
  (`TauCeti.CliffordAlgebra.autCongr_dualNumberEquiv_linearEquivEquivVectorStabilizer`).

In higher rank the vector stabilizer of the exterior algebra is in general a proper subgroup of
all automorphisms: for instance, on `⋀(R²)` the assignment `e₁ ↦ e₁ + e₁ ∧ e₂`, `e₂ ↦ e₂`
extends to an automorphism that moves the vector `e₁` out of `R²`.

## Main definitions

* `TauCeti.ExteriorAlgebra.linearEquivEquivVectorStabilizer`: the group isomorphism from the
  linear automorphisms of `M` onto the vector stabilizer of `ExteriorAlgebra R M`.

## Main results

* `TauCeti.ExteriorAlgebra.toAlgHom_linearEquivEquivVectorStabilizer_apply`: the automorphism
  attached to `f` is `ExteriorAlgebra.map f`.
* `TauCeti.CliffordAlgebra.vectorStabilizer_eq_top_of_subsingleton`: the case `M = 0`.
* `TauCeti.CliffordAlgebra.vectorStabilizer_zero_line_eq_top`: on a line, if `R` has no nonzero
  `a` with `a ^ 2 = 0` and `2 * a = 0`, every automorphism of the Clifford algebra of the zero form
  preserves the vectors.
* `TauCeti.CliffordAlgebra.autCongr_dualNumberEquiv_linearEquivEquivVectorStabilizer`: read on the
  dual numbers, the automorphism attached to a linear automorphism `e` of `R` is
  `TauCeti.TrivSqZeroExt.mapEquiv e`.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.3 and Theorem 1.4.
-/

public section

open TrivSqZeroExt

universe u v

/-! ### The zero form: the exterior algebra -/

namespace TauCeti.ExteriorAlgebra

open _root_.ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The linear automorphism of `M` underlying `φ`: the restriction of `φ` to the vectors,
transported along `ExteriorAlgebra.ι`, which has the left inverse `ExteriorAlgebra.ιInv`. -/
private noncomputable def vectorStabilizerLinearEquiv
    (φ : CliffordAlgebra.vectorStabilizer (0 : QuadraticForm R M)) : M ≃ₗ[R] M :=
  (LinearEquiv.ofLeftInverse ι_leftInverse).trans <|
    ((φ : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M).toLinearEquiv.ofSubmodules _ _ <| by
      rw [AlgEquiv.toLinearEquiv_toLinearMap]
      exact CliffordAlgebra.mem_vectorStabilizer_iff.mp φ.property).trans
    (LinearEquiv.ofLeftInverse ι_leftInverse).symm

private theorem ι_vectorStabilizerLinearEquiv
    (φ : CliffordAlgebra.vectorStabilizer (0 : QuadraticForm R M)) (m : M) :
    ι R (vectorStabilizerLinearEquiv φ m) =
      (φ : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) (ι R m) := by
  rw [vectorStabilizerLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    ← LinearEquiv.ofLeftInverse_apply ι_leftInverse, LinearEquiv.apply_symm_apply,
    LinearEquiv.ofSubmodules_apply, LinearEquiv.ofLeftInverse_apply,
    AlgEquiv.toLinearEquiv_apply]

variable (R M) in
/-- **The vector stabilizer of the exterior algebra.** Every linear automorphism `f` of `M` is an
isometry of the zero form, so it induces an automorphism of `ExteriorAlgebra R M` that maps the
vectors onto themselves, namely `ExteriorAlgebra.map f`
(`TauCeti.ExteriorAlgebra.toAlgHom_linearEquivEquivVectorStabilizer_apply`). Every automorphism of
the exterior algebra that maps the vectors onto themselves arises from exactly one `f`, and
composition of automorphisms corresponds to composition of linear maps. No hypothesis on `R` is
needed: since `ExteriorAlgebra.ι` is injective over every commutative ring, `f` is read off on
generators. -/
noncomputable def linearEquivEquivVectorStabilizer :
    (M ≃ₗ[R] M) ≃* CliffordAlgebra.vectorStabilizer (0 : QuadraticForm R M) where
  -- Every linear automorphism of `M` preserves the zero form.
  toFun f := ⟨CliffordAlgebra.equivOfIsometry { f with map_app' := fun _ ↦ rfl },
    CliffordAlgebra.mem_vectorStabilizer_iff.mpr (CliffordAlgebra.ι_range_map_equivOfIsometry _)⟩
  invFun := vectorStabilizerLinearEquiv
  left_inv f := LinearEquiv.ext fun m ↦ (ι_inj R _ _).mp <| by
    simp [ι_vectorStabilizerLinearEquiv, CliffordAlgebra.equivOfIsometry_apply,
      ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
  right_inv φ := Subtype.ext <| CliffordAlgebra.algEquiv_ext_ι fun m ↦ by
    simp [ι_vectorStabilizerLinearEquiv, CliffordAlgebra.equivOfIsometry_apply,
      ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
  map_mul' f g := Subtype.ext <| CliffordAlgebra.algEquiv_ext_ι fun m ↦ by
    simp [CliffordAlgebra.equivOfIsometry_apply,
      ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- On generators, the automorphism attached to `f` applies `f`. -/
@[simp]
theorem linearEquivEquivVectorStabilizer_apply_ι (f : M ≃ₗ[R] M) (m : M) :
    (linearEquivEquivVectorStabilizer R M f :
      ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) (ι R m) = ι R (f m) := by
  simp [linearEquivEquivVectorStabilizer, CliffordAlgebra.equivOfIsometry_apply,
    ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- **The vector stabilizer acts through the exterior algebra functor**: the automorphism attached
to a linear automorphism `f` of `M` is `ExteriorAlgebra.map f`. -/
@[simp]
theorem toAlgHom_linearEquivEquivVectorStabilizer_apply (f : M ≃ₗ[R] M) :
    ((linearEquivEquivVectorStabilizer R M f : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) :
      ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M) = map (f : M →ₗ[R] M) :=
  hom_ext <| LinearMap.ext fun m ↦ by simp

/-- The linear automorphism underlying `φ` in the vector stabilizer of the exterior algebra is
characterized by its action on generators. -/
@[simp]
theorem ι_linearEquivEquivVectorStabilizer_symm_apply
    (φ : CliffordAlgebra.vectorStabilizer (0 : QuadraticForm R M)) (m : M) :
    ι R ((linearEquivEquivVectorStabilizer R M).symm φ m) =
      (φ : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) (ι R m) :=
  ι_vectorStabilizerLinearEquiv φ m

end TauCeti.ExteriorAlgebra

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

/-! ### The zero module -/

/-- **The case `M = 0`.** When `M` is subsingleton, the only automorphism of `CliffordAlgebra Q`
is the identity, and it maps the vectors onto themselves. -/
theorem vectorStabilizer_eq_top_of_subsingleton {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Subsingleton M] (Q : QuadraticForm R M) :
    vectorStabilizer Q = ⊤ :=
  Subsingleton.elim _ _

/-! ### The zero form on a line: the dual numbers -/

section DualNumber

variable {R : Type u} [CommRing R]

/-- Transporting `TauCeti.TrivSqZeroExt.mapEquiv e` from the dual numbers to the Clifford algebra
of the zero form on `R` gives the automorphism induced by `e`. -/
private theorem autCongr_symm_mapEquiv (e : R ≃ₗ[R] R) :
    CliffordAlgebraDualNumber.equiv.autCongr.symm (TrivSqZeroExt.mapEquiv e) =
      equivOfIsometry { e with map_app' := fun _ ↦ rfl } := by
  refine algEquiv_ext_ι fun r ↦ CliffordAlgebraDualNumber.equiv.injective ?_
  simp [equivOfIsometry_apply, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    ← DualNumber.inr_eq_smul_eps]

/-- **The zero form on a line.** If `R` has no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`, for
instance if `R` is reduced or `2` is invertible in `R`, then every algebra automorphism of the
Clifford algebra of the zero form on `R`, which is the dual numbers `R[ε]`, maps the vectors
`R • ε` onto themselves: such an automorphism is `ε ↦ u • ε` for a unit `u`
(`TauCeti.DualNumber.mapEquivMulEquiv`). -/
theorem vectorStabilizer_zero_line_eq_top (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0) :
    vectorStabilizer (0 : QuadraticForm R R) = ⊤ := by
  refine eq_top_iff.mpr fun φ _ ↦ mem_vectorStabilizer_iff.mpr ?_
  obtain ⟨e, he⟩ :=
    DualNumber.exists_mapEquiv_eq hR (CliffordAlgebraDualNumber.equiv.autCongr φ)
  rw [← CliffordAlgebraDualNumber.equiv.autCongr.symm_apply_apply φ, ← he, autCongr_symm_mapEquiv]
  exact ι_range_map_equivOfIsometry _

/-- **The correspondence on the dual numbers.** Read on the dual numbers through
`CliffordAlgebraDualNumber.equiv`, the vector-preserving automorphism attached to a linear
automorphism `e` of `R` is `TauCeti.TrivSqZeroExt.mapEquiv e`; for the multiplication by a unit
`u` this is `ε ↦ u • ε`. This holds over every commutative ring. If moreover `R` has no nonzero
`a` with `a ^ 2 = 0` and `2 * a = 0`, for instance if `R` is reduced or `2` is invertible in `R`,
then together with `TauCeti.CliffordAlgebra.vectorStabilizer_zero_line_eq_top` this identifies the
isometry group `GL₁(R)` of the zero form with all automorphisms of `R[ε]`, by `u ↦ u`. -/
theorem autCongr_dualNumberEquiv_linearEquivEquivVectorStabilizer (e : R ≃ₗ[R] R) :
    CliffordAlgebraDualNumber.equiv.autCongr
        (ExteriorAlgebra.linearEquivEquivVectorStabilizer R R e :
          CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] CliffordAlgebra (0 : QuadraticForm R R)) =
      TrivSqZeroExt.mapEquiv e := by
  rw [← MulEquiv.eq_symm_apply, autCongr_symm_mapEquiv]
  refine algEquiv_ext_ι fun r ↦ ?_
  simp [equivOfIsometry_apply, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

end DualNumber

end TauCeti.CliffordAlgebra
