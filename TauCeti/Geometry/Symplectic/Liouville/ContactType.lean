/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.Transverse
public import TauCeti.Geometry.Symplectic.Liouville.VectorField

/-!
# Hypersurfaces of contact type

Let `ω` be a two-form on a manifold `M` and let `ι : S → M` be a map, typically the inclusion of
an embedded hypersurface. The hypersurface is of **contact type** when some Liouville vector field
(`L_Z ω = ω`) defined near it is transverse to it, and of **restricted contact type** when such a
field exists on all of `M`. These are the hypersurfaces whose characteristic foliations are
preserved, up to conjugation, by the flow of `Z`, which is how existence of closed characteristics
on them is deduced from almost existence.

For a closed `ω`, a Liouville vector field `Z` is the same as a primitive `α = ι_Z ω` of `ω`
(`TauCeti.isLiouvilleVectorField_iff_mextDeriv_interior_eq`), and when `ω` is nondegenerate the
primitive determines the field. The definitions below keep the primitive explicit:

* `TauCeti.IsContactType J ω α ι`: on some open neighbourhood `U` of the image of `ι`, `dα = ω`, and
  some vector field `Z`, smooth on `U` and satisfying `ι_Z ω = α` on `U`, is transverse along `ι`;
* `TauCeti.IsRestrictedContactType J ω α ι`: `dα = ω` on `M`, and some smooth vector field `Z` on
  `M` with `ι_Z ω = α` is transverse along `ι`.

The primitive is part of the data because a Liouville vector field need not be the Liouville field
of a given primitive: on the plane, `x ∂_x + ∂_y` is a Liouville vector field of `d(x dy)` whose
primitive is `x dy - dx`, not `x dy` (`Prod.curryLeft_extDeriv_realPlaneXDy_ne`).

A hypersurface of restricted contact type is of contact type, with the same primitive
(`TauCeti.IsRestrictedContactType.isContactType`). For a closed `C¹` form `ω`, a hypersurface is of
restricted contact type for some primitive exactly when some smooth Liouville vector field of `ω`
is transverse along it (`TauCeti.exists_isRestrictedContactType_iff`), which is the definition of
McDuff and Salamon. The basic example is the unit cosphere bundle of a Riemannian manifold, with
the primitive `-λ` of the canonical symplectic form of the cotangent bundle
(`TauCeti.CotangentBundle.isRestrictedContactType_cosphereBundle`).

## Main definitions

* `TauCeti.IsContactType`: contact type, with an explicit primitive near the hypersurface.
* `TauCeti.IsRestrictedContactType`: restricted contact type, with an explicit global primitive.

## Main results

* `TauCeti.IsRestrictedContactType.isContactType`: restricted contact type implies contact type.
* `TauCeti.exists_isRestrictedContactType_iff`: the characterization by transverse Liouville vector
  fields.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type).
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 4.
-/

public section

open Bundle Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {ω : RoughForm I M ℝ 2} {α : RoughForm I M ℝ 1} {ι : S → M}

variable (J) in
/-- A map `ι : S → M`, typically an embedded hypersurface, is **of contact type** for the two-form
`ω`, with primitive `α`, when on some open neighbourhood `U` of the image of `ι` the one-form `α` is
a primitive of `ω`, `dα = ω`, and some vector field `Z`, smooth on `U` and satisfying `ι_Z ω = α`
on `U`, is transverse along `ι`. When `ω` is smooth, such a `Z` is a Liouville vector field of
`ω` on `U`. -/
def IsContactType (ω : RoughForm I M ℝ 2) (α : RoughForm I M ℝ 1) (ι : S → M) : Prop :=
  ∃ U : Set M, IsOpen U ∧ range ι ⊆ U ∧ (∀ x ∈ U, mextDeriv α x = ω x) ∧
    ∃ Z : (x : M) → TangentSpace I x, ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U ∧
      (∀ x ∈ U, ω.interior Z x = α x) ∧ IsTransverseAlong J Z ι

variable (J) in
/-- A map `ι : S → M`, typically an embedded hypersurface, is **of restricted contact type** for
the two-form `ω`, with primitive `α`, when `α` is a primitive of `ω` on all of `M`, `dα = ω`, and
some smooth vector field `Z` on `M` with `ι_Z ω = α` is transverse along `ι`. For a closed
`C¹` form `ω`, such a `Z` is a Liouville vector field of `ω`
(`TauCeti.exists_isRestrictedContactType_iff`). -/
def IsRestrictedContactType (ω : RoughForm I M ℝ 2) (α : RoughForm I M ℝ 1) (ι : S → M) : Prop :=
  mextDeriv α = ω ∧ ∃ Z : (x : M) → TangentSpace I x, ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z) ∧
    ω.interior Z = α ∧ IsTransverseAlong J Z ι

/-- The defining characterization of contact type. -/
theorem isContactType_iff :
    IsContactType J ω α ι ↔ ∃ U : Set M, IsOpen U ∧ range ι ⊆ U ∧
      (∀ x ∈ U, mextDeriv α x = ω x) ∧ ∃ Z : (x : M) → TangentSpace I x,
        ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U ∧ (∀ x ∈ U, ω.interior Z x = α x) ∧
          IsTransverseAlong J Z ι :=
  Iff.rfl

/-- The defining characterization of restricted contact type. -/
theorem isRestrictedContactType_iff :
    IsRestrictedContactType J ω α ι ↔ mextDeriv α = ω ∧ ∃ Z : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z) ∧ ω.interior Z = α ∧ IsTransverseAlong J Z ι :=
  Iff.rfl

namespace IsRestrictedContactType

/-- The primitive of a hypersurface of restricted contact type is a primitive: `dα = ω`. -/
theorem mextDeriv_eq (h : IsRestrictedContactType J ω α ι) : mextDeriv α = ω :=
  h.1

/-- **Restricted contact type implies contact type**, with the same primitive: take the whole
manifold as the neighbourhood of the hypersurface. -/
theorem isContactType (h : IsRestrictedContactType J ω α ι) : IsContactType J ω α ι := by
  obtain ⟨hα, Z, hZ, hZα, hZι⟩ := h
  exact ⟨univ, isOpen_univ, subset_univ _, fun x _ ↦ congrFun hα x, Z, hZ.contMDiffOn,
    fun x _ ↦ congrFun hZα x, hZι⟩

end IsRestrictedContactType

/-- **Restricted contact type through Liouville vector fields.** For a closed `C¹` two-form `ω`,
a map `ι` is of restricted contact type for some primitive of `ω` exactly when some smooth
Liouville vector field `Z` of `ω` on `M` is transverse along `ι`; the primitive is then
`ι_Z ω`. -/
theorem exists_isRestrictedContactType_iff (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0) :
    (∃ α, IsRestrictedContactType J ω α ι) ↔
      ∃ Z : (x : M) → TangentSpace I x, ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z) ∧
        IsLiouvilleVectorField ω Z ∧ IsTransverseAlong J Z ι := by
  have hω' := hω.contMDiff.mdifferentiable one_ne_zero
  constructor
  · rintro ⟨α, hdα, Z, hZ, hZα, hZι⟩
    refine ⟨Z, hZ, ?_, hZι⟩
    rw [isLiouvilleVectorField_iff_mextDeriv_interior_eq hω' (hZ.mdifferentiable (by simp)) hdω,
      hZα, hdα]
  · rintro ⟨Z, hZ, hZω, hZι⟩
    exact ⟨ω.interior Z,
      (isLiouvilleVectorField_iff_mextDeriv_interior_eq hω' (hZ.mdifferentiable (by simp))
        hdω).1 hZω, Z, hZ, rfl, hZι⟩

end TauCeti
