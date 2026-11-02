/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# Symplectic vector fields and their de Rham classes

Let `σ` be a smooth two-form on a manifold `M`. A smooth vector field `X` is a **symplectic vector
field** when its contraction `ι_X σ` is a closed one-form
(`TauCeti.SmoothTwoForm.symplecticVectorFields`). When `σ` is closed, Cartan's formula
`L_X σ = ι_X dσ + d(ι_X σ) = d(ι_X σ)` shows that these are exactly the smooth vector fields with
`L_X σ = 0`, the infinitesimal symmetries of `σ`
(`TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`).

Sending a symplectic vector field to the de Rham class of its contraction gives a linear map
`X ↦ [ι_X σ]` to the first de Rham cohomology `H¹_dR(M)`
(`TauCeti.SmoothTwoForm.interiorClass`). For a nondegenerate `σ` on a finite-dimensional
manifold, a smooth function `f` has the smooth Hamiltonian vector field `X_f`, with
`ι_{X_f} σ = df`.
The sequence below uses `f ↦ -X_f`
(`TauCeti.SmoothTwoForm.IsNondegenerate.negHamiltonianₗ`, defined on smooth `0`-forms). This sign
follows the identity `X_{{f, g}} = -[X_f, X_g]`, valid for closed `σ` with the bracket
`{f, g} = df(X_g)`, under which `f ↦ -X_f` respects Lie brackets
(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`); brackets
themselves are not treated in this file. These maps
form the exact sequence

`0 → H⁰_dR(M) → C^∞(M) → {symplectic vector fields} → H¹_dR(M) → 0`.

Here the first term is the space `closedForms I M 0` of locally constant smooth functions, which
`TauCeti.deRhamCohomology.mk` identifies with `H⁰_dR(M)`.

* At `C^∞(M)`: `-X_f = 0` exactly when `df = 0`, so the kernel of `f ↦ -X_f` is the space of
  closed `0`-forms (`TauCeti.SmoothTwoForm.IsNondegenerate.ker_negHamiltonianₗ`).
* At the symplectic vector fields: `[ι_X σ] = 0` exactly when `ι_X σ = df` for a smooth `f`, that
  is when `X` is the Hamiltonian vector field of `f`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exact_negHamiltonianₗ_interiorClass` and
  `TauCeti.SmoothTwoForm.interiorClass_eq_zero_iff`).
* At `H¹_dR(M)`: every closed one-form `α` is the contraction of the smooth vector field
  `(σ♭)⁻¹ α`, so every class is reached
  (`TauCeti.SmoothTwoForm.IsNondegenerate.interiorClass_surjective`).

No closedness of `σ` is needed for the exactness results. Closedness enters this file only through
the comparison with the Lie derivative; it is also needed for the bracket compatibility above,
which is not treated here.

## Main declarations

* `TauCeti.SmoothTwoForm.symplecticVectorFields`: the smooth vector fields with closed
  contraction.
* `TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`: for closed `σ`,
  these are the smooth vector fields with `L_X σ = 0`.
* `TauCeti.SmoothTwoForm.mem_symplecticVectorFields_of_isHamiltonianVectorField`: Hamiltonian
  vector fields are symplectic.
* `TauCeti.SmoothTwoForm.interiorClass`: the class `[ι_X σ] ∈ H¹_dR(M)`.
* `TauCeti.SmoothTwoForm.interiorClass_eq_zero_iff`: the class vanishes exactly for Hamiltonian
  vector fields.
* `TauCeti.SmoothTwoForm.IsNondegenerate.negHamiltonianₗ`: the map `f ↦ -X_f`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exact_subtype_negHamiltonianₗ`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.exact_negHamiltonianₗ_interiorClass`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.interiorClass_surjective`: exactness of the sequence.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (symplectic and Hamiltonian vector fields, and the exact sequence
  `0 → ℝ → C^∞(M) → symplectic vector fields → H¹(M; ℝ) → 0` for connected `M`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18 (Hamiltonian and symplectic vector fields).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (σ : SmoothTwoForm I M)

/-! ### Symplectic vector fields -/

/-- The **symplectic vector fields** of a two-form `σ`: the smooth vector fields `X` whose
contraction `ι_X σ` is a closed one-form. For a closed `σ` these are the smooth vector fields with
`L_X σ = 0` (`TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`). -/
def symplecticVectorFields : Submodule ℝ Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ :=
  (closedForms I M 1).comap σ.interiorₗ

variable {σ}

/-- A smooth vector field is symplectic exactly when its contraction is closed. -/
@[simp]
theorem mem_symplecticVectorFields_iff {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    X ∈ σ.symplecticVectorFields ↔ mextDeriv (RoughForm.interior X σ.1) = 0 := by
  rw [symplecticVectorFields, Submodule.mem_comap, mem_closedForms, coe_interiorₗ]

/-- For a closed two-form, a smooth vector field is symplectic exactly when its Lie derivative
annihilates the form, `L_X σ = 0`. -/
theorem mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero (hσ : σ.IsClosed)
    {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    X ∈ σ.symplecticVectorFields ↔ mlieDerivForm X σ.1 = 0 := by
  rw [mem_symplecticVectorFields_iff,
    SmoothForm.mlieDerivForm_eq_mextDeriv_interior (X.contMDiff.mdifferentiable (by simp)) hσ]

/-- A smooth vector field is Hamiltonian for a smooth `0`-form precisely when its contraction
is the exterior derivative of that form. -/
theorem isHamiltonianVectorField_iff_interiorₗ_eq {φ : SmoothForm I M ℝ 0}
    {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    σ.IsHamiltonianVectorField (fun y ↦ φ.1 y 0) X ↔ σ.interiorₗ X = mextDerivₗ I 0 φ := by
  -- Compare the underlying rough forms, expressing the `0`-form by its scalar function.
  rw [isHamiltonianVectorField_iff_interior_eq, ← RoughForm.eq_ofFunction φ.1,
    ← coe_interiorₗ, ← mextDerivₗ_apply, SetLike.coe_eq_coe]

/-- **Hamiltonian vector fields are symplectic**: if `ι_X σ = df` for a smooth function `f`, then
`ι_X σ` is closed. -/
theorem mem_symplecticVectorFields_of_isHamiltonianVectorField {φ : SmoothForm I M ℝ 0}
    {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}
    (hX : σ.IsHamiltonianVectorField (fun y ↦ φ.1 y 0) X) : X ∈ σ.symplecticVectorFields := by
  rw [symplecticVectorFields, Submodule.mem_comap, isHamiltonianVectorField_iff_interiorₗ_eq.1 hX]
  exact mextDerivₗ_mem_closedForms I 0 φ

variable (σ)

/-- The **de Rham class of a symplectic vector field**: the class `[ι_X σ] ∈ H¹_dR(M)` of its
closed contraction. -/
def interiorClass : σ.symplecticVectorFields →ₗ[ℝ] deRhamCohomology I M 1 :=
  deRhamCohomology.mk I 1 ∘ₗ σ.interiorₗ.restrict fun _ hX ↦ hX

/-- The class of a symplectic vector field is the class of its contraction. -/
theorem interiorClass_apply (X : σ.symplecticVectorFields) :
    σ.interiorClass X = deRhamCohomology.mk I 1
      ⟨σ.interiorₗ X, by simpa only [symplecticVectorFields, Submodule.mem_comap] using X.2⟩ :=
  (rfl)

variable {σ}

/-- A symplectic vector field has zero de Rham class precisely when its contraction is the
exterior derivative of a smooth `0`-form. -/
theorem interiorClass_eq_zero_iff_exists_mextDerivₗ (X : σ.symplecticVectorFields) :
    σ.interiorClass X = 0 ↔ ∃ φ : SmoothForm I M ℝ 0,
      σ.interiorₗ X = mextDerivₗ I 0 φ := by
  rw [interiorClass_apply, deRhamCohomology.mk_eq_zero_iff, exactForms_succ, LinearMap.mem_range]
  exact exists_congr fun _ ↦ eq_comm

/-- A symplectic vector field has zero class `[ι_X σ]` exactly when it is the Hamiltonian vector
field of a smooth function. -/
theorem interiorClass_eq_zero_iff (X : σ.symplecticVectorFields) :
    σ.interiorClass X = 0 ↔ ∃ φ : SmoothForm I M ℝ 0,
      σ.IsHamiltonianVectorField (fun y ↦ φ.1 y 0) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) := by
  simp only [interiorClass_eq_zero_iff_exists_mextDerivₗ, isHamiltonianVectorField_iff_interiorₗ_eq]

/-! ### The exact sequence of a nondegenerate form -/

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
include h

/-- The contraction of the vector field `-(σ♭)⁻¹ df` is the closed one-form `-df`. -/
private theorem neg_interiorEquiv_symm_mextDerivₗ_mem (φ : SmoothForm I M ℝ 0) :
    -h.interiorEquiv.symm (mextDerivₗ I 0 φ) ∈ σ.symplecticVectorFields := by
  rw [symplecticVectorFields, Submodule.mem_comap, map_neg, interiorₗ_interiorEquiv_symm,
    neg_mem_iff]
  exact mextDerivₗ_mem_closedForms I 0 φ

/-- The map `f ↦ -X_f` from smooth functions, as smooth `0`-forms, to symplectic vector fields.
When `σ` is moreover closed, the convention `{f, g} = df(X_g)` gives `X_{{f, g}} = -[X_f, X_g]`,
and the sign makes this map compatible with the Lie brackets. -/
def negHamiltonianₗ : SmoothForm I M ℝ 0 →ₗ[ℝ] σ.symplecticVectorFields where
  toFun φ := ⟨-h.interiorEquiv.symm (mextDerivₗ I 0 φ), h.neg_interiorEquiv_symm_mextDerivₗ_mem φ⟩
  map_add' φ ψ := Subtype.ext <| by simp only [map_add, neg_add, Submodule.coe_add]
  map_smul' c φ := Subtype.ext <| by
    simp only [map_smul, smul_neg, Submodule.coe_smul, RingHom.id_apply]

/-- The vector field of `f ↦ -X_f` is the negated Hamiltonian vector field of the function. -/
@[simp]
theorem coe_negHamiltonianₗ (φ : SmoothForm I M ℝ 0) (x : M) :
    (h.negHamiltonianₗ φ : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) x =
      -σ.hamiltonianVectorField (fun y ↦ φ.1 y 0) x := by
  -- Both sides are `-(σ♭)⁻¹` of the differential `d(φ)`, read once as a form and once through
  -- `mvfderiv`.
  have hd : SmoothForm.degreeOneEquiv (mextDerivₗ I 0 φ) x = mvfderiv I (fun y ↦ φ.1 y 0) x := by
    ext v
    rw [SmoothForm.degreeOneEquiv_apply_apply, mextDerivₗ_apply, RoughForm.eq_ofFunction φ.1,
      mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply]
    simp only [RoughForm.ofFunction_apply]
  simp only [negHamiltonianₗ, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffSection.coe_neg,
    Pi.neg_apply, interiorEquiv_symm_apply, hd, hamiltonianVectorField_def]

/-- The contraction of `-X_f` is `-df`. -/
@[simp]
theorem interiorₗ_negHamiltonianₗ (φ : SmoothForm I M ℝ 0) :
    σ.interiorₗ (h.negHamiltonianₗ φ) = -mextDerivₗ I 0 φ := by
  simp [negHamiltonianₗ]

/-- **Exactness at the smooth functions**: `-X_f = 0` exactly when `f` is a closed `0`-form, that
is, locally constant. -/
theorem ker_negHamiltonianₗ : LinearMap.ker h.negHamiltonianₗ = closedForms I M 0 := by
  ext φ
  -- The injective `interiorEquiv` sends `-X_f` to `-df`, so one vanishes exactly when the other
  -- does.
  have key := h.interiorEquiv.map_eq_zero_iff
    (x := (h.negHamiltonianₗ φ : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯))
  rw [interiorEquiv_apply, interiorₗ_negHamiltonianₗ, neg_eq_zero, ZeroMemClass.coe_eq_zero] at key
  rw [LinearMap.mem_ker, mem_closedForms_iff_mextDerivₗ_eq_zero, key]

/-- **Exactness at the smooth functions**, as exactness of the inclusion of closed `0`-forms
followed by `f ↦ -X_f`. -/
theorem exact_subtype_negHamiltonianₗ :
    Function.Exact (closedForms I M 0).subtype h.negHamiltonianₗ :=
  LinearMap.exact_iff.2 <| (h.ker_negHamiltonianₗ).trans (Submodule.range_subtype _).symm

/-- **Exactness at the symplectic vector fields**: the symplectic vector fields with zero class
`[ι_X σ]` are exactly the fields `-X_f`. -/
theorem exact_negHamiltonianₗ_interiorClass :
    Function.Exact h.negHamiltonianₗ σ.interiorClass := by
  intro X
  rw [interiorClass_eq_zero_iff_exists_mextDerivₗ, Set.mem_range]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨-φ, Subtype.ext (h.interiorEquiv.injective ?_)⟩
    rw [interiorEquiv_apply, interiorEquiv_apply, interiorₗ_negHamiltonianₗ, map_neg, neg_neg, hφ]
  · rintro ⟨φ, rfl⟩
    exact ⟨-φ, by rw [interiorₗ_negHamiltonianₗ, map_neg]⟩

/-- **Exactness at `H¹_dR(M)`**: every first de Rham class is the class `[ι_X σ]` of a symplectic
vector field, namely of `X = (σ♭)⁻¹ α` for a closed representative `α`. -/
theorem interiorClass_surjective : Function.Surjective σ.interiorClass := by
  intro c
  obtain ⟨α, rfl⟩ := deRhamCohomology.mk_surjective I 1 c
  have hX : h.interiorEquiv.symm α.1 ∈ σ.symplecticVectorFields := by
    rw [symplecticVectorFields, Submodule.mem_comap, interiorₗ_interiorEquiv_symm]
    exact α.2
  refine ⟨⟨_, hX⟩, ?_⟩
  rw [interiorClass_apply]
  congr 1
  exact Subtype.ext (h.interiorₗ_interiorEquiv_symm α.1)

end IsNondegenerate

end SmoothTwoForm

end TauCeti
