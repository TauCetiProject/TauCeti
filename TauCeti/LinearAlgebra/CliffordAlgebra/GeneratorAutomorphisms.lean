/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Clifford automorphisms that preserve the vectors

An isometry `f` of quadratic forms induces the algebra equivalence
`CliffordAlgebra.equivOfIsometry f`, which maps the vectors `LinearMap.range (ι Q₁)` onto the
vectors `LinearMap.range (ι Q₂)`. This file proves the converse: an algebra equivalence of
Clifford algebras that maps the vectors onto the vectors is induced by a unique isometry. The
isometry is read off on generators through `CliffordAlgebra.ιRangeEquiv`, and the generator
square `ι v * ι v = Q v` forces it to preserve the forms. No hypothesis on the forms is needed,
only that `2` is invertible: degenerate forms, and the exterior algebra of the zero form, are
included.

For a single form `Q`, the algebra automorphisms that map the vectors onto themselves form a
subgroup `CliffordAlgebra.vectorStabilizer Q` of all algebra automorphisms (the stabilizer of the
vectors under the pointwise action), and `equivOfIsometry` identifies it with the orthogonal
group of `Q`.

The condition can be read on the degree filtration `CliffordAlgebra.filtration`: when `2` is
invertible and `R` is reduced, preserving the vectors is equivalent to preserving its first step
`R ⊕ M` (`CliffordAlgebra.filtration_one_map_eq_iff`, in the vector API), and so, by
`CliffordAlgebra.forall_filtration_map_eq_iff`, to preserving every step.

## Main definitions

* `CliffordAlgebra.isometryEquivOfιRangeMap`: the isometry underlying an algebra equivalence
  that maps the vectors onto the vectors.
* `CliffordAlgebra.vectorStabilizer`: the group of algebra automorphisms of `CliffordAlgebra Q`
  that map the vectors onto themselves.
* `CliffordAlgebra.orthogonalGroupEquivVectorStabilizer`: the group isomorphism from the
  orthogonal group of `Q` onto `vectorStabilizer Q`, given by `equivOfIsometry`.

## Main results

* `CliffordAlgebra.ι_range_map_eq_iff_existsUnique`: an algebra equivalence maps the vectors onto
  the vectors if and only if it is `equivOfIsometry f` for a unique isometry `f`.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.3 and Theorem 1.4.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open QuadraticMap
open scoped Pointwise

universe u v w

namespace CliffordAlgebra

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-! ### The vector stabilizer -/

section VectorStabilizer

variable (Q : QuadraticForm R M₁)

/-- The algebra automorphisms of `CliffordAlgebra Q` that map the vectors
`LinearMap.range (ι Q)` onto themselves: the stabilizer of the vectors under the pointwise action
of the automorphism group on submodules.

When `2` is invertible, `CliffordAlgebra.orthogonalGroupEquivVectorStabilizer` identifies these
with the automorphisms `equivOfIsometry f` induced by the isometries of `Q`. -/
def vectorStabilizer : Subgroup (CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q) :=
  MulAction.stabilizer _ (LinearMap.range (ι Q))

variable {Q} in
/-- An automorphism lies in the vector stabilizer when it maps the vectors onto themselves. -/
@[simp]
theorem mem_vectorStabilizer_iff {φ : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q} :
    φ ∈ vectorStabilizer Q ↔
      (LinearMap.range (ι Q)).map φ.toLinearMap = LinearMap.range (ι Q) := by
  rw [vectorStabilizer, MulAction.mem_stabilizer_iff, Submodule.pointwise_smul_def]
  -- The pointwise action applies `φ` through its scalar action, `AlgEquiv.smul_def`.
  exact Iff.of_eq <| congrArg (fun g ↦ Submodule.map g (LinearMap.range (ι Q)) = _) <|
    LinearMap.ext fun x ↦ AlgEquiv.smul_def φ x

end VectorStabilizer

variable [Invertible (2 : R)]

/-! ### The isometry underlying a vector-preserving equivalence -/

/-- The restriction of `φ` to the vectors, transported along `CliffordAlgebra.ιRangeEquiv`. -/
private noncomputable def ιRangeMapLinearEquiv
    (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) : M₁ ≃ₗ[R] M₂ :=
  (ιRangeEquiv Q₁).trans <|
    (φ.toLinearEquiv.ofSubmodules _ _ (by rw [AlgEquiv.toLinearEquiv_toLinearMap, h])).trans
      (ιRangeEquiv Q₂).symm

private theorem ι_ιRangeMapLinearEquiv (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) (v : M₁) :
    ι Q₂ (ιRangeMapLinearEquiv φ h v) = φ (ι Q₁ v) := by
  rw [ιRangeMapLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    ι_ιRangeEquiv_symm_apply, LinearEquiv.ofSubmodules_apply, coe_ιRangeEquiv_apply,
    AlgEquiv.toLinearEquiv_apply]

private theorem map_app_ιRangeMapLinearEquiv
    (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) (v : M₁) :
    Q₂ (ιRangeMapLinearEquiv φ h v) = Q₁ v := by
  -- Both scalars are the square of the same element `φ (ι Q₁ v)`.
  apply algebraMap_injective Q₂
  rw [← ι_sq_scalar, ι_ιRangeMapLinearEquiv, ← map_mul, ι_sq_scalar, AlgEquiv.commutes]

/-- An algebra equivalence of Clifford algebras that maps the vectors of `Q₁` onto the vectors of
`Q₂` restricts to an isometry from `Q₁` to `Q₂`: the vector `f v` is characterized by
`ι Q₂ (f v) = φ (ι Q₁ v)` (`CliffordAlgebra.ι_isometryEquivOfιRangeMap`).

The linear equivalence is the restriction of `φ` to the vectors, transported along
`CliffordAlgebra.ιRangeEquiv`; the generator squares show that it preserves the forms. -/
noncomputable def isometryEquivOfιRangeMap (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) :
    Q₁.IsometryEquiv Q₂ where
  toLinearEquiv := ιRangeMapLinearEquiv φ h
  map_app' := map_app_ιRangeMapLinearEquiv φ h

/-- **The defining equation** of `CliffordAlgebra.isometryEquivOfιRangeMap`: on generators it is
the algebra equivalence it comes from. -/
@[simp]
theorem ι_isometryEquivOfιRangeMap (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) (v : M₁) :
    ι Q₂ (isometryEquivOfιRangeMap φ h v) = φ (ι Q₁ v) :=
  ι_ιRangeMapLinearEquiv φ h v

/-- An algebra equivalence that maps the vectors onto the vectors is induced by the isometry it
restricts to. -/
@[simp]
theorem equivOfIsometry_isometryEquivOfιRangeMap
    (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) :
    equivOfIsometry (isometryEquivOfιRangeMap φ h) = φ :=
  algEquiv_ext_ι fun v ↦ by
    rw [equivOfIsometry_apply, map_apply_ι, IsometryEquiv.toIsometry_apply,
      ι_isometryEquivOfιRangeMap]

/-- The isometry underlying `equivOfIsometry e` is `e`. -/
@[simp]
theorem isometryEquivOfιRangeMap_equivOfIsometry (e : Q₁.IsometryEquiv Q₂) :
    isometryEquivOfιRangeMap (equivOfIsometry e) (ι_range_map_equivOfIsometry e) = e :=
  DFunLike.ext _ _ fun v ↦ ι_injective Q₂ <| by
    rw [ι_isometryEquivOfιRangeMap, equivOfIsometry_apply, map_apply_ι,
      IsometryEquiv.toIsometry_apply]

/-- **The isometry criterion for Clifford algebra equivalences.** An algebra equivalence
`CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂` maps the vectors of `Q₁` onto the vectors of `Q₂`
if and only if it is `equivOfIsometry f` for a unique isometry `f`. No hypothesis on the forms is
needed: they may be degenerate, or zero. -/
theorem ι_range_map_eq_iff_existsUnique (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂) :
    (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂) ↔
      ∃! f : Q₁.IsometryEquiv Q₂, equivOfIsometry f = φ := by
  refine ⟨fun h ↦ ⟨isometryEquivOfιRangeMap φ h,
    equivOfIsometry_isometryEquivOfιRangeMap φ h, fun f hf ↦ ?_⟩, ?_⟩
  · rw [← equivOfIsometry_inj, hf, equivOfIsometry_isometryEquivOfιRangeMap]
  · rintro ⟨f, rfl, -⟩
    exact ι_range_map_equivOfIsometry f

/-! ### The vector stabilizer and the orthogonal group -/

variable (Q : QuadraticForm R M₁)

/-- **The vector stabilizer is the orthogonal group.** The automorphism `equivOfIsometry f`
induced by an orthogonal automorphism `f` of `Q` maps the vectors onto themselves, and every
automorphism that does arises from exactly one `f`; composition of automorphisms corresponds to
composition of isometries. -/
noncomputable def orthogonalGroupEquivVectorStabilizer :
    TauCeti.QuadraticMap.orthogonalGroup Q ≃* vectorStabilizer Q where
  toFun f := ⟨equivOfIsometry (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q f),
    mem_vectorStabilizer_iff.mpr (ι_range_map_equivOfIsometry _)⟩
  invFun φ := (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q).symm
    (isometryEquivOfιRangeMap φ.val (mem_vectorStabilizer_iff.mp φ.property))
  left_inv f := by simp only [isometryEquivOfιRangeMap_equivOfIsometry, Equiv.symm_apply_apply]
  right_inv φ := Subtype.ext <| by
    simp only [Equiv.apply_symm_apply, equivOfIsometry_isometryEquivOfιRangeMap]
  map_mul' f g := Subtype.ext <| algEquiv_ext_ι fun v ↦ by
    simp [equivOfIsometry_apply]

/-- The automorphism attached to an orthogonal automorphism `f` is `equivOfIsometry f`. -/
@[simp]
theorem coe_orthogonalGroupEquivVectorStabilizer_apply
    (f : TauCeti.QuadraticMap.orthogonalGroup Q) :
    (orthogonalGroupEquivVectorStabilizer Q f : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q) =
      equivOfIsometry (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q f) := by
  rw [orthogonalGroupEquivVectorStabilizer, MulEquiv.coe_mk, Equiv.coe_fn_mk]

/-- On generators, `orthogonalGroupEquivVectorStabilizer Q f` applies `f`. -/
theorem orthogonalGroupEquivVectorStabilizer_apply_ι
    (f : TauCeti.QuadraticMap.orthogonalGroup Q) (v : M₁) :
    (orthogonalGroupEquivVectorStabilizer Q f : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q)
      (ι Q v) = ι Q ((f : M₁ ≃ₗ[R] M₁) v) := by
  simp [equivOfIsometry_apply]

/-- The orthogonal automorphism underlying `φ ∈ vectorStabilizer Q` is characterized by its
action on generators. -/
@[simp]
theorem ι_orthogonalGroupEquivVectorStabilizer_symm_apply (φ : vectorStabilizer Q) (v : M₁) :
    ι Q (((orthogonalGroupEquivVectorStabilizer Q).symm φ : M₁ ≃ₗ[R] M₁) v) =
      (φ : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q) (ι Q v) := by
  simp only [orthogonalGroupEquivVectorStabilizer, MulEquiv.symm_mk, MulEquiv.coe_mk,
    Equiv.coe_fn_symm_mk, TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv_symm,
    ι_isometryEquivOfιRangeMap]

/-- The vector stabilizer consists of the automorphisms `equivOfIsometry f`. -/
theorem mem_vectorStabilizer_iff_exists {φ : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q} :
    φ ∈ vectorStabilizer Q ↔ ∃ f : Q.IsometryEquiv Q, equivOfIsometry f = φ := by
  rw [mem_vectorStabilizer_iff, ι_range_map_eq_iff_existsUnique]
  exact ⟨ExistsUnique.exists, fun ⟨f, hf⟩ ↦ ⟨f, hf, fun g hg ↦ equivOfIsometry_injective
    (hg.trans hf.symm)⟩⟩

end CliffordAlgebra
