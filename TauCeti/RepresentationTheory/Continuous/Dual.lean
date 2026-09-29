/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.RepresentationTheory.Continuous.Conjugate
public import TauCeti.RepresentationTheory.Continuous.LinHom

/-!
# The contragredient of a continuous representation

The **contragredient** (or dual) of a continuous representation `π` on `V` acts on the strong dual
`StrongDual 𝕜 V = V →L[𝕜] 𝕜` by precomposition with the inverse action,
`dual π g φ = φ ∘ π g⁻¹`. It is the Hom representation of `π` into the trivial representation on
`𝕜`, so it is *defined* as `ContRepresentation.linHom π (ContRepresentation.trivial 𝕜 G 𝕜)` and
inherits continuity and its character from that construction rather than repeating either argument.

The point of naming it is the comparison with the **conjugate** representation
`TauCeti.ContRepresentation.conjugate` of
`TauCeti/RepresentationTheory/Continuous/Conjugate.lean`. For a *unitary* `π` on a complete space
the Riesz map `InnerProductSpace.toDual` is equivariant,

`dual π g (toDual v) = toDual (π g v)`,

and, being conjugate-linear, it identifies the contragredient not with `π` but with its conjugate:
`ContRepresentation.conjugateToDual` is the resulting isomorphism of continuous representations
from `conjugate e π` to `dual π`. That is the precise content of the slogan that the representative
ring of `C(G)` is closed under conjugation "via the contragredient": conjugating a matrix
coefficient of `π` gives a matrix coefficient of the conjugate
(`TauCeti.ContRepresentation.star_matrixCoeff_eq_matrixCoeff_conjugate`), and the conjugate is the
contragredient.

No inner product is placed on `StrongDual 𝕜 V`: there is no canonical one, and the equivariant Riesz
map above is conjugate-linear, so the contragredient is not a unitary representation in the sense of
`TauCeti.ContRepresentation.IsUnitary`. What survives, and is what the bounds downstream use, is
that its action operators are **isometric** (`ContRepresentation.norm_dual_apply`). Accordingly its
matrix coefficients are recorded in the duality pairing rather than in an inner product:
`ContRepresentation.dual_apply_toDual_apply` says they are exactly the matrix coefficients of `π`
with its two vectors exchanged.

## Main definitions

* `ContRepresentation.dual`: the contragredient of a continuous representation.
* `ContRepresentation.conjugateToDual`: for a unitary `π`, the isomorphism of continuous
  representations from the conjugate `conjugate e π` to the contragredient `dual π`, namely
  `v ↦ toDual (conjugation e v)`.

## Main statements

* `ContRepresentation.dual_apply` and `ContRepresentation.dual_apply_apply`: the action operators of
  the contragredient are precomposition with the inverse action.
* `ContRepresentation.continuous_dual`: the contragredient of a representation with continuous
  operator-valued action has one.
* `ContRepresentation.dual_dual_apply_inclusionInDoubleDual`: the canonical map of a normed space
  into its double dual is equivariant from `π` to the double contragredient.
* `ContRepresentation.character_dual`: its character is `χ_π(g⁻¹)`.
* `ContRepresentation.norm_dual_apply`: the contragredient of a unitary representation acts by
  isometries of the dual.
* `ContRepresentation.dual_apply_toDual`: the Riesz map is equivariant from `π` to `dual π`, for a
  unitary `π`; `ContRepresentation.dual_apply_toDual_apply` reads it on matrix coefficients.
* `ContRepresentation.norm_conjugateToDual_apply` and
  `ContRepresentation.bijective_conjugateToDual`: the comparison map from `conjugate e π` to
  `dual π` is a bijective isometry, so it is an isomorphism of continuous representations.

The contragredient is the object Layer 3 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
asks for when it requires the representative ring to be closed under conjugation "via the
contragredient", and the `V_π*` of its Layer 5 isotypic decomposition. The mathematical development
follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open TauCeti TauCeti.ContRepresentation
open scoped InnerProductSpace

namespace ContRepresentation

/-! ### The contragredient -/

section Definition

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **The contragredient of a continuous representation**: `G` acts on the strong dual
`StrongDual 𝕜 V = V →L[𝕜] 𝕜` by precomposition with the inverse action, `φ ↦ φ ∘ π g⁻¹`.

This is the Hom representation into the trivial representation on the scalars, and is defined as
such so that its continuity and its character are `ContRepresentation.continuous_linHom` and
`ContRepresentation.character_linHom`. -/
noncomputable def dual (π : ContRepresentation 𝕜 G V) :
    ContRepresentation 𝕜 G (StrongDual 𝕜 V) :=
  linHom π (ContRepresentation.trivial 𝕜 G 𝕜)

variable (π : ContRepresentation 𝕜 G V)

/-- The contragredient is the Hom representation into the trivial representation on the
scalars. -/
theorem dual_def : dual π = linHom π (ContRepresentation.trivial 𝕜 G 𝕜) :=
  (rfl)

/-- **The action operators of the contragredient** are precomposition with the inverse action. -/
@[simp]
theorem dual_apply (g : G) (φ : StrongDual 𝕜 V) : dual π g φ = φ.comp (π g⁻¹) := by
  rw [dual_def, linHom_apply]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [ContRepresentation.trivial_apply]

/-- The contragredient, evaluated at a functional and a vector. -/
theorem dual_apply_apply (g : G) (φ : StrongDual 𝕜 V) (v : V) : dual π g φ v = φ (π g⁻¹ v) := by
  rw [dual_apply]
  rfl

/-- **The contragredient of the trivial representation is trivial**: precomposing with the identity
changes no functional. -/
@[simp]
theorem dual_trivial :
    dual (ContRepresentation.trivial 𝕜 G V) = ContRepresentation.trivial 𝕜 G (StrongDual 𝕜 V) := by
  refine DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun φ ↦ ContinuousLinearMap.ext fun v ↦ ?_
  rw [dual_apply_apply]
  simp [ContRepresentation.trivial_apply]

/-- **The canonical map of a normed space into its double dual is equivariant** from `π` to the
double contragredient `dual (dual π)`. No finite-dimensionality or reflexivity is needed: the two
inversions cancel, which is the reason the contragredient precomposes with `π g⁻¹` rather than with
`π g`. -/
theorem dual_dual_apply_inclusionInDoubleDual (g : G) (v : V) :
    dual (dual π) g (NormedSpace.inclusionInDoubleDual 𝕜 V v)
      = NormedSpace.inclusionInDoubleDual 𝕜 V (π g v) := by
  refine ContinuousLinearMap.ext fun φ ↦ ?_
  rw [dual_apply_apply, NormedSpace.dual_def, NormedSpace.dual_def, dual_apply_apply, inv_inv]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The contragredient has a continuous operator-valued action.** It is the Hom representation
into the trivial representation, whose action is constant. -/
theorem continuous_dual (hπ : Continuous π) : Continuous (dual π) :=
  continuous_linHom π (ContRepresentation.trivial 𝕜 G 𝕜) hπ continuous_const

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 V]

/-- **The character of the contragredient is `χ_π(g⁻¹)`.** This is
`ContRepresentation.character_linHom` at the trivial representation on the scalars, whose character
is the constant `1`. -/
theorem character_dual (hπ : Continuous π) (g : G) :
    character (dual π) (continuous_dual π hπ) g = character π hπ g⁻¹ := by
  have h : character (dual π) (continuous_dual π hπ) g
      = character (linHom π (ContRepresentation.trivial 𝕜 G 𝕜))
        (continuous_linHom π (ContRepresentation.trivial 𝕜 G 𝕜) hπ continuous_const) g :=
    (rfl)
  rw [h, character_linHom π (ContRepresentation.trivial 𝕜 G 𝕜) hπ continuous_const,
    character_trivial]
  simp

end Definition

/-! ### The contragredient of a unitary representation -/

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (π : ContRepresentation 𝕜 G V)

/-- A one-sided bound for `ContRepresentation.norm_dual_apply`: precomposing a functional with an
isometry does not increase its norm. -/
theorem norm_dual_apply_le (hπ : IsUnitary π) (g : G) (φ : StrongDual 𝕜 V) :
    ‖dual π g φ‖ ≤ ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ) fun v ↦ by
    rw [dual_apply_apply]
    calc ‖φ (π g⁻¹ v)‖ ≤ ‖φ‖ * ‖π g⁻¹ v‖ := φ.le_opNorm _
      _ = ‖φ‖ * ‖v‖ := by rw [hπ.norm_map]

/-- **The contragredient of a unitary representation acts by isometries.** There is no canonical
inner product on the dual, so this isometry statement is what replaces unitarity of `dual π`; the
reverse bound comes from applying the forward bound to `g⁻¹`. -/
theorem norm_dual_apply (hπ : IsUnitary π) (g : G) (φ : StrongDual 𝕜 V) :
    ‖dual π g φ‖ = ‖φ‖ := by
  refine le_antisymm (norm_dual_apply_le π hπ g φ) ?_
  have h : dual π g⁻¹ (dual π g φ) = φ := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [dual_apply_apply, dual_apply_apply, inv_inv, ← mul_apply_eq_comp, ← map_mul,
      inv_mul_cancel, map_one, one_apply_eq_self]
  calc ‖φ‖ = ‖dual π g⁻¹ (dual π g φ)‖ := by rw [h]
    _ ≤ ‖dual π g φ‖ := norm_dual_apply_le π hπ g⁻¹ _

variable [CompleteSpace V]

/-- **The Riesz map is equivariant from `π` to its contragredient**, for a unitary `π`: moving a
unitary action across the inner product replaces the group element by its inverse, which is exactly
the precomposition defining `dual π`. Because `InnerProductSpace.toDual` is conjugate-linear, this
identifies `dual π` with the *conjugate* of `π`, not with `π` itself; see
`ContRepresentation.conjugateToDual`. -/
theorem dual_apply_toDual (hπ : IsUnitary π) (g : G) (v : V) :
    dual π g (InnerProductSpace.toDual 𝕜 V v) = InnerProductSpace.toDual 𝕜 V (π g v) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [dual_apply_apply, InnerProductSpace.toDual_apply_apply,
    InnerProductSpace.toDual_apply_apply]
  exact (hπ.inner_map_left g v w).symm

variable [TopologicalSpace G]

/-- **The matrix coefficients of the contragredient, in the duality pairing, are the matrix
coefficients of `π` with its two vectors exchanged.** So passing to the contragredient does not
enlarge the span of the matrix coefficients of a unitary representation. -/
theorem dual_apply_toDual_apply (hπ : IsUnitary π) (hπc : Continuous π) (g : G) (v w : V) :
    dual π g (InnerProductSpace.toDual 𝕜 V w) v = matrixCoeff π hπc w v g := by
  rw [dual_apply_toDual π hπ, InnerProductSpace.toDual_apply_apply, matrixCoeff_apply]

end Unitary

/-! ### The contragredient is the conjugate representation -/

section Conjugate

variable {𝕜 ι G V : Type*} [RCLike 𝕜] [Fintype ι] [Group G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  (e : OrthonormalBasis ι 𝕜 V) (π : ContRepresentation 𝕜 G V)

/-- The Riesz map composed with the coordinatewise conjugation of an orthonormal basis. Each factor
is conjugate-linear, so the composite is linear, and each is isometric. -/
private noncomputable def toDualConj : V →L[𝕜] StrongDual 𝕜 V :=
  LinearMap.mkContinuous
    { toFun := fun v ↦ InnerProductSpace.toDual 𝕜 V (conjugation e v)
      map_add' := fun v w ↦ by simp
      map_smul' := fun c v ↦ by simp [conjugation_smul, map_smulₛₗ] } 1 fun v ↦ by simp

private theorem toDualConj_apply (v : V) :
    toDualConj e v = InnerProductSpace.toDual 𝕜 V (conjugation e v) :=
  (rfl)

/-- **The contragredient of a unitary representation is its conjugate**: the Riesz map composed with
the conjugation of an orthonormal basis,

`v ↦ toDual (conjugation e v)`,

is a continuous intertwiner from the conjugate representation `conjugate e π` to the contragredient
`dual π`. Each factor is conjugate-linear, so the composite is linear; it is a bijective isometry
(`ContRepresentation.bijective_conjugateToDual`,
`ContRepresentation.norm_conjugateToDual_apply`), hence an isomorphism of continuous
representations. -/
noncomputable def conjugateToDual (hπ : IsUnitary π) :
    ContIntertwiningMap (conjugate e π) (dual π) where
  __ := toDualConj e
  isIntertwining' g := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, toDualConj_apply,
      toDualConj_apply, conjugate_apply, conjCLM_apply, conjugation_conjugation,
      dual_apply_toDual π hπ]

variable (hπ : IsUnitary π)

/-- The comparison map of `ContRepresentation.conjugateToDual`, on a vector. -/
@[simp]
theorem conjugateToDual_apply (v : V) :
    (conjugateToDual e π hπ).toContinuousLinearMap v =
      InnerProductSpace.toDual 𝕜 V (conjugation e v) :=
  (rfl)

-- Not `@[simp]`: `ContRepresentation.conjugateToDual_apply` already rewrites the left-hand side,
-- after which the norm is computed by Mathlib's own lemmas, so the `simpNF` linter rejects the tag.
/-- **The comparison map from `conjugate e π` to `dual π` is isometric**: both the conjugation of a
basis and the Riesz map preserve norms. -/
theorem norm_conjugateToDual_apply (v : V) :
    ‖(conjugateToDual e π hπ).toContinuousLinearMap v‖ = ‖v‖ := by
  rw [conjugateToDual_apply]
  simp

/-- **The comparison map from `conjugate e π` to `dual π` is bijective**: the Riesz map is a linear
isometric equivalence and the conjugation of a basis is an involution. With
`ContRepresentation.norm_conjugateToDual_apply` this makes the conjugate and the contragredient of a
unitary representation isomorphic continuous representations. -/
theorem bijective_conjugateToDual :
    Function.Bijective (conjugateToDual e π hπ).toContinuousLinearMap := by
  have h : ((conjugateToDual e π hπ).toContinuousLinearMap : V → StrongDual 𝕜 V) =
      InnerProductSpace.toDual 𝕜 V ∘ conjugation e := funext fun v ↦ conjugateToDual_apply e π hπ v
  rw [h]
  exact (InnerProductSpace.toDual 𝕜 V).bijective.comp
    (Function.Involutive.bijective (conjugation_conjugation e))

end Conjugate

end ContRepresentation
