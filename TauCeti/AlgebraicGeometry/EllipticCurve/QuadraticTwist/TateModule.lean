/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.RepresentationTheory.Invariants

/-!
# Tate modules of quadratic twists

The point isomorphism of a quadratic twist induces a linear isomorphism of Tate modules.
It intertwines the Galois actions up to the quadratic character, over any field and in
characteristic two as well. The isomorphism and its inverse are continuous for the
inverse-limit topologies.

On a subgroup fixing the quadratic extension, the character is trivial and the two
restricted representations are equivalent. In particular an unramified quadratic twist
over a nonarchimedean local field preserves the inertia representation and its invariant
module. This allows inertia computations for split multiplicative reduction to be
transported to nonsplit multiplicative reduction.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, X.2 and X.5.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.6.
-/

public section

noncomputable section

open TauCeti
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M] [DecidableEq M]
  (W : WeierstrassCurve K) (ℓ : ℕ) [Fact ℓ.Prime]

variable (L M)

/-- The Tate-module isomorphism induced by the point isomorphism of a quadratic twist.
No ellipticity, closure, or invertibility hypothesis on `ℓ` is needed. -/
def quadraticTwistTateModuleEquiv :
    TateModule ℓ ((W.quadraticTwist L)⁄M).toAffine.Point ≃ₗ[ℤ_[ℓ]]
      TateModule ℓ (W⁄M).toAffine.Point :=
  TateModule.mapLinearEquiv (W.quadraticTwistPointEquiv L M)

/-- The twist isomorphism applies the point isomorphism at each torsion level. -/
@[simp]
theorem coe_proj_quadraticTwistTateModuleEquiv
    (x : TateModule ℓ ((W.quadraticTwist L)⁄M).toAffine.Point) (n : ℕ) :
    (TateModule.proj n (W.quadraticTwistTateModuleEquiv L M ℓ x) : (W⁄M).toAffine.Point) =
      W.quadraticTwistPointEquiv L M (TateModule.proj n x) := by
  simp [quadraticTwistTateModuleEquiv]

/-- The inverse twist isomorphism applies the inverse point isomorphism at each level. -/
@[simp]
theorem coe_proj_quadraticTwistTateModuleEquiv_symm
    (x : TateModule ℓ (W⁄M).toAffine.Point) (n : ℕ) :
    (TateModule.proj n ((W.quadraticTwistTateModuleEquiv L M ℓ).symm x) :
      ((W.quadraticTwist L)⁄M).toAffine.Point) =
        (W.quadraticTwistPointEquiv L M).symm (TateModule.proj n x) := by
  simp [quadraticTwistTateModuleEquiv]

/-- The twist isomorphism is continuous for the inverse-limit topologies. -/
theorem continuous_quadraticTwistTateModuleEquiv :
    Continuous (W.quadraticTwistTateModuleEquiv L M ℓ) :=
  (TateModule.continuous_map (p := ℓ)
    (W.quadraticTwistPointEquiv L M).toAddMonoidHom).congr fun x ↦
      (TateModule.mapLinearEquiv_apply _ x).symm

/-- The inverse twist isomorphism is continuous for the inverse-limit topologies. -/
theorem continuous_quadraticTwistTateModuleEquiv_symm :
    Continuous (W.quadraticTwistTateModuleEquiv L M ℓ).symm := by
  rw [quadraticTwistTateModuleEquiv, TateModule.mapLinearEquiv_symm]
  exact (TateModule.continuous_map (p := ℓ)
    (W.quadraticTwistPointEquiv L M).symm.toAddMonoidHom).congr fun x ↦
      (TateModule.mapLinearEquiv_apply _ x).symm

/-- The Galois action on the Tate module of a quadratic twist is the original action
multiplied by the quadratic character. The character acts by integer scalars. -/
theorem quadraticTwistTateModuleEquiv_galois (σ : M ≃ₐ[K] M)
    (x : TateModule ℓ ((W.quadraticTwist L)⁄M).toAffine.Point) :
    W.quadraticTwistTateModuleEquiv L M ℓ
        ((W.quadraticTwist L).tateModuleGaloisRepresentation ℓ σ x) =
      (Algebra.IsQuadraticExtension.quadraticCharacter K L (σ.restrictNormal L) : ℤ) •
        W.tateModuleGaloisRepresentation ℓ σ (W.quadraticTwistTateModuleEquiv L M ℓ x) := by
  apply TateModule.ext
  intro n
  apply Subtype.ext
  simp only [coe_proj_quadraticTwistTateModuleEquiv,
    coe_proj_tateModuleGaloisRepresentation, map_zsmul, AddSubgroup.coe_zsmul]
  exact W.quadraticTwistPointEquiv_map_eq_quadraticCharacter_smul_map L M σ _

variable {L M}

/-- On a subgroup fixing the quadratic extension, the twist gives equivalent
Tate-module representations. -/
def quadraticTwistTateModuleRepresentationEquiv (H : Subgroup (M ≃ₐ[K] M))
    (hH : ∀ σ ∈ H, σ.restrictNormal L = 1) :
    Representation.Equiv
      ((W.quadraticTwist L).tateModuleGaloisRepresentation ℓ |>.comp H.subtype)
      (W.tateModuleGaloisRepresentation ℓ |>.comp H.subtype) :=
  .mk (W.quadraticTwistTateModuleEquiv L M ℓ) fun σ ↦ by
    apply LinearMap.ext
    intro x
    simpa [hH σ σ.2] using W.quadraticTwistTateModuleEquiv_galois L M ℓ σ x

/-- The restricted representation equivalence has the original twist isomorphism as
its underlying map. -/
@[simp]
theorem quadraticTwistTateModuleRepresentationEquiv_apply (H : Subgroup (M ≃ₐ[K] M))
    (hH : ∀ σ ∈ H, σ.restrictNormal L = 1)
    (x : TateModule ℓ ((W.quadraticTwist L)⁄M).toAffine.Point) :
    W.quadraticTwistTateModuleRepresentationEquiv ℓ H hH x =
      W.quadraticTwistTateModuleEquiv L M ℓ x :=
  (rfl)

end WeierstrassCurve

namespace WeierstrassCurve

open ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K)
  (L : IntermediateField K (AlgebraicClosure K))
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [IsUnramified K L] [DecidableEq (AlgebraicClosure K)]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- An unramified quadratic twist preserves the inertia representation on the Tate module.
This applies also at residue characteristic two, and does not require `ℓ` to be invertible. -/
def quadraticTwistTateModuleInertiaEquiv :
    Representation.Equiv
      ((W.quadraticTwist L).tateModuleGaloisRepresentation ℓ |>.comp
        (inertiaSubgroup K).subtype)
      (W.tateModuleGaloisRepresentation ℓ |>.comp (inertiaSubgroup K).subtype) :=
  W.quadraticTwistTateModuleRepresentationEquiv ℓ (inertiaSubgroup K) fun σ hσ ↦ by
    rw [AlgEquiv.restrictNormal_eq_one_iff]
    exact (IntermediateField.mem_fixingSubgroup_iff L σ).mp
      ((inertiaSubgroup_le_fixingSubgroup_iff L).mpr inferInstance hσ)

/-- The inertia equivalence for an unramified quadratic twist uses the same twist map. -/
@[simp]
theorem quadraticTwistTateModuleInertiaEquiv_apply
    (x : TateModule ℓ ((W.quadraticTwist L)⁄(AlgebraicClosure K)).toAffine.Point) :
    W.quadraticTwistTateModuleInertiaEquiv L ℓ x =
      W.quadraticTwistTateModuleEquiv L (AlgebraicClosure K) ℓ x :=
  (rfl)

/-- An unramified quadratic twist preserves the rank of the inertia-invariant Tate module.
This is the invariant rank entering the tame conductor computation. -/
theorem finrank_inertiaInvariants_quadraticTwist :
    Module.finrank ℤ_[ℓ] (Representation.invariants
      ((W.quadraticTwist L).tateModuleGaloisRepresentation ℓ |>.comp
        (inertiaSubgroup K).subtype)) =
    Module.finrank ℤ_[ℓ] (Representation.invariants
      (W.tateModuleGaloisRepresentation ℓ |>.comp (inertiaSubgroup K).subtype)) :=
  (W.quadraticTwistTateModuleInertiaEquiv L ℓ).invariantsLinearEquiv.finrank_eq

end WeierstrassCurve
