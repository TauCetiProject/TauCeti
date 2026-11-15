/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Submodule
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Orthogonal complements for invariant forms

For a bilinear form `B` invariant under a representation `ρ` of a *group*, the `B`-orthogonal
complement of a subrepresentation is again a subrepresentation
(`TauCeti.Representation.IsInvariantForm.orthogonalSubrepresentation`): if `w` is orthogonal to the
subrepresentation `S`, then so is `ρ g w`, because `B v (ρ g w) = B (ρ g⁻¹ v) w` and `ρ g⁻¹` maps
`S` into itself.

When `B` moreover has anisotropic diagonal, for instance a real inner product, and the
representation is finite-dimensional, every subrepresentation is complemented by its orthogonal
complement. Applied to a flag `S ≤ T` of subrepresentations this gives the invariant three-term
splitting

`V = S ⊕ (T ⊓ Sᗮ) ⊕ Tᗮ`,

in which `S ⊔ (T ⊓ Sᗮ) = T`, `(T ⊓ Sᗮ) ⊔ Tᗮ = Sᗮ`, and each summand is complementary to the sum of
the other two. No reflexivity of `B` is needed for this; for a reflexive form moreover
`(T ⊓ Sᗮ)ᗮ = S ⊔ Tᗮ`. This is how an inner product averaged over a compact
group produces invariant complements adapted to a flag of invariant subspaces, as for the splitting
`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` of a Lie algebra along subspaces `𝔥 ⊆ 𝔨` invariant under a compact subgroup.

## Main definitions

* `TauCeti.Representation.IsInvariantForm.orthogonalSubrepresentation`: the orthogonal complement
  of a subrepresentation for an invariant form.

## Main results

All in the namespace `TauCeti.Representation.IsInvariantForm`:

* `apply_mem_orthogonal` and `orthogonal_mem_invtSubmodule`: the orthogonal complement of an
  invariant subspace is invariant.
* `orthogonalSubrepresentation_bot`, `orthogonalSubrepresentation_le`,
  `orthogonalSubrepresentation_sup` and
  `le_orthogonalSubrepresentation_orthogonalSubrepresentation`: the order-reversing behaviour of
  the orthogonal complement.
* `isCompl_orthogonalSubrepresentation`: for an anisotropic invariant form, a subrepresentation and
  its orthogonal complement are complementary.
* `sup_inf_orthogonalSubrepresentation`,
  `inf_orthogonalSubrepresentation_sup_orthogonalSubrepresentation`,
  `orthogonalSubrepresentation_inf_orthogonalSubrepresentation` (for a reflexive form),
  `isCompl_inf_orthogonalSubrepresentation_sup` and
  `isCompl_inf_orthogonalSubrepresentation_sup_orthogonalSubrepresentation`: the three-term
  splitting of a flag of subrepresentations.

## Implementation notes

The orthogonal-complement API follows the formal precedents
`ContRepresentation.IsUnitary.orthogonalSubrepresentation` in
`TauCeti.RepresentationTheory.Continuous.InvariantComplement` (for a unitary inner product) and
`TauCeti.orthogonalSubrepresentation` in `TauCeti.RepresentationTheory.PermutationForm` (for the
permutation form), generalised here to an arbitrary invariant bilinear form.

## References

* `TauCeti.RepresentationTheory.Continuous.InvariantComplement` and
  `TauCeti.RepresentationTheory.PermutationForm`, the orthogonal-complement APIs this file adapts
  to a general invariant bilinear form, as described in the implementation notes above.
-/

public section

namespace TauCeti.Representation.IsInvariantForm

open LinearMap (BilinForm)

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  {ρ : Representation k G V} {B : BilinForm k V}

/-- **The orthogonal complement of an invariant subspace is invariant**, for a form invariant under
a representation of a group. -/
theorem apply_mem_orthogonal (hB : IsInvariantForm ρ B) {W : Submodule k V}
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) (g : G) {w : V} (hw : w ∈ B.orthogonal W) :
    ρ g w ∈ B.orthogonal W := by
  rw [BilinForm.mem_orthogonal_iff] at hw ⊢
  intro v hv
  rw [← inv_inv g, ← hB.apply_left]
  exact hw _ (hW g⁻¹ v hv)

/-- **Invariant orthogonal complements**, in the language of Mathlib's invariant submodules: for
a form invariant under a representation of a group, the orthogonal complement of an invariant
submodule is invariant. -/
theorem orthogonal_mem_invtSubmodule (hB : IsInvariantForm ρ B) {W : Submodule k V}
    (hW : W ∈ ρ.invtSubmodule) : B.orthogonal W ∈ ρ.invtSubmodule := by
  rw [Representation.mem_invtSubmodule] at hW ⊢
  exact fun g _ hw ↦ hB.apply_mem_orthogonal (fun g' _ hv ↦ hW g' hv) g hw

/-- The orthogonal complement of a subrepresentation for an invariant form, as a
subrepresentation. -/
def orthogonalSubrepresentation (hB : IsInvariantForm ρ B) (S : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := B.orthogonal S.toSubmodule
  apply_mem_toSubmodule g _ hw :=
    hB.apply_mem_orthogonal (fun g _ hv ↦ S.apply_mem_toSubmodule g hv) g hw

/-- The underlying submodule of the orthogonal complement of a subrepresentation. -/
@[simp]
theorem toSubmodule_orthogonalSubrepresentation (hB : IsInvariantForm ρ B)
    (S : Subrepresentation ρ) :
    (hB.orthogonalSubrepresentation S).toSubmodule = B.orthogonal S.toSubmodule :=
  -- `(rfl)`, not `rfl`: the body of `orthogonalSubrepresentation` is not `@[expose]`d, so this
  -- must not be inferred `@[defeq]`.
  (rfl)

/-- A vector lies in the orthogonal complement of a subrepresentation exactly when the form pairs
every vector of the subrepresentation with it to zero. -/
@[simp]
theorem mem_orthogonalSubrepresentation_iff (hB : IsInvariantForm ρ B)
    {S : Subrepresentation ρ} {w : V} :
    w ∈ hB.orthogonalSubrepresentation S ↔ ∀ v ∈ S, B v w = 0 := by
  rw [← Subrepresentation.mem_toSubmodule, toSubmodule_orthogonalSubrepresentation,
    BilinForm.mem_orthogonal_iff]
  simp only [Subrepresentation.mem_toSubmodule]

/-- The orthogonal complement of the zero subrepresentation is everything. -/
@[simp]
theorem orthogonalSubrepresentation_bot (hB : IsInvariantForm ρ B) :
    hB.orthogonalSubrepresentation ⊥ = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  rw [toSubmodule_orthogonalSubrepresentation, Subrepresentation.toSubmodule_bot,
    Subrepresentation.toSubmodule_top, BilinForm.orthogonal_bot]

/-- Taking orthogonal complements of subrepresentations reverses inclusions. -/
@[gcongr]
theorem orthogonalSubrepresentation_le (hB : IsInvariantForm ρ B) {S T : Subrepresentation ρ}
    (hST : S ≤ T) : hB.orthogonalSubrepresentation T ≤ hB.orthogonalSubrepresentation S := by
  rw [← Subrepresentation.toSubmodule_le_toSubmodule, toSubmodule_orthogonalSubrepresentation,
    toSubmodule_orthogonalSubrepresentation]
  exact BilinForm.orthogonal_le (Subrepresentation.toSubmodule_le_toSubmodule.mpr hST)

/-- The orthogonal complement of a sum of subrepresentations is the intersection of their
orthogonal complements. -/
theorem orthogonalSubrepresentation_sup (hB : IsInvariantForm ρ B) (S T : Subrepresentation ρ) :
    hB.orthogonalSubrepresentation (S ⊔ T) =
      hB.orthogonalSubrepresentation S ⊓ hB.orthogonalSubrepresentation T := by
  apply Subrepresentation.toSubmodule_injective
  simp only [toSubmodule_orthogonalSubrepresentation, Subrepresentation.toSubmodule_sup,
    Subrepresentation.toSubmodule_inf]
  exact Submodule.orthogonalBilin_sup (B := B) S.toSubmodule T.toSubmodule

/-- For a reflexive invariant form, a subrepresentation lies in its double orthogonal
complement. -/
theorem le_orthogonalSubrepresentation_orthogonalSubrepresentation (hB : IsInvariantForm ρ B)
    (hrefl : B.IsRefl) (S : Subrepresentation ρ) :
    S ≤ hB.orthogonalSubrepresentation (hB.orthogonalSubrepresentation S) := by
  rw [← Subrepresentation.toSubmodule_le_toSubmodule, toSubmodule_orthogonalSubrepresentation,
    toSubmodule_orthogonalSubrepresentation]
  exact BilinForm.le_orthogonal_orthogonal hrefl

section Field

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {ρ : Representation k G V} {B : BilinForm k V}
  (hB : IsInvariantForm ρ B) (hani : B.toQuadraticMap.Anisotropic)
include hB hani

/-- **Invariant anisotropic forms complement every subrepresentation.** For an invariant form
with anisotropic diagonal on a finite-dimensional representation, such as an invariant inner
product, a subrepresentation and its orthogonal complement are complementary. -/
theorem isCompl_orthogonalSubrepresentation (S : Subrepresentation ρ) :
    IsCompl S (hB.orthogonalSubrepresentation S) :=
  Subrepresentation.isCompl_toSubmodule.mp <| by
    rw [toSubmodule_orthogonalSubrepresentation]
    exact BilinForm.isCompl_orthogonal_of_anisotropic hani S.toSubmodule

variable {S T : Subrepresentation ρ}

/-- For a flag `S ≤ T` of subrepresentations, `S` and the relative orthogonal complement `T ⊓ Sᗮ`
span `T`: `S ⊔ (T ⊓ Sᗮ) = T`. -/
theorem sup_inf_orthogonalSubrepresentation (hST : S ≤ T) :
    S ⊔ T ⊓ hB.orthogonalSubrepresentation S = T := by
  apply Subrepresentation.toSubmodule_injective
  simp only [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
    toSubmodule_orthogonalSubrepresentation]
  exact BilinForm.sup_inf_orthogonal_of_le hani
    (Subrepresentation.toSubmodule_le_toSubmodule.mpr hST)

/-- For a flag `S ≤ T` of subrepresentations, the orthogonal complement `Sᗮ` is the sum of the
relative complement `T ⊓ Sᗮ` and of `Tᗮ`: `(T ⊓ Sᗮ) ⊔ Tᗮ = Sᗮ`. -/
theorem inf_orthogonalSubrepresentation_sup_orthogonalSubrepresentation (hST : S ≤ T) :
    T ⊓ hB.orthogonalSubrepresentation S ⊔ hB.orthogonalSubrepresentation T =
      hB.orthogonalSubrepresentation S := by
  apply Subrepresentation.toSubmodule_injective
  simp only [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
    toSubmodule_orthogonalSubrepresentation]
  exact BilinForm.inf_orthogonal_sup_orthogonal_of_le hani
    (Subrepresentation.toSubmodule_le_toSubmodule.mpr hST)

/-- For a reflexive form, the orthogonal complement of `T ⊓ Sᗮ` is `S ⊔ Tᗮ`. For a flag `S ≤ T`
this identifies the sum of the two other summands of the splitting `V = S ⊕ (T ⊓ Sᗮ) ⊕ Tᗮ` with
the orthogonal complement of the middle one. -/
theorem orthogonalSubrepresentation_inf_orthogonalSubrepresentation (hrefl : B.IsRefl)
    (S T : Subrepresentation ρ) :
    hB.orthogonalSubrepresentation (T ⊓ hB.orthogonalSubrepresentation S) =
      S ⊔ hB.orthogonalSubrepresentation T := by
  have hnd := B.nondegenerate_of_anisotropic hani
  apply Subrepresentation.toSubmodule_injective
  simp only [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
    toSubmodule_orthogonalSubrepresentation]
  rw [B.orthogonal_inf hnd, BilinForm.orthogonal_orthogonal hnd hrefl, sup_comm]

/-- For a flag `S ≤ T` of subrepresentations, `S` is complementary to the sum `(T ⊓ Sᗮ) ⊔ Tᗮ` of
the two other summands of the splitting `V = S ⊕ (T ⊓ Sᗮ) ⊕ Tᗮ`. -/
theorem isCompl_inf_orthogonalSubrepresentation_sup (hST : S ≤ T) :
    IsCompl S (T ⊓ hB.orthogonalSubrepresentation S ⊔ hB.orthogonalSubrepresentation T) := by
  rw [hB.inf_orthogonalSubrepresentation_sup_orthogonalSubrepresentation hani hST]
  exact hB.isCompl_orthogonalSubrepresentation hani S

/-- For a flag `S ≤ T` of subrepresentations, the relative complement `T ⊓ Sᗮ` is complementary to
the sum `S ⊔ Tᗮ` of the two other summands of the splitting `V = S ⊕ (T ⊓ Sᗮ) ⊕ Tᗮ`. No
reflexivity of the form is needed. -/
theorem isCompl_inf_orthogonalSubrepresentation_sup_orthogonalSubrepresentation (hST : S ≤ T) :
    IsCompl (T ⊓ hB.orthogonalSubrepresentation S) (S ⊔ hB.orthogonalSubrepresentation T) :=
  Subrepresentation.isCompl_toSubmodule.mp <| by
    simp only [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
      toSubmodule_orthogonalSubrepresentation]
    exact BilinForm.isCompl_inf_orthogonal_sup_orthogonal_of_le hani
      (Subrepresentation.toSubmodule_le_toSubmodule.mpr hST)

end Field

end TauCeti.Representation.IsInvariantForm
