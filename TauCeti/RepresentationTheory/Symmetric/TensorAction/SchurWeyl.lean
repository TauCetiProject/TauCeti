/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Maschke
public import TauCeti.RepresentationTheory.AsAlgebraHom
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Centralizer
public import TauCeti.RingTheory.Semisimple.DoubleCentralizer

/-!
# Schur-Weyl duality: the symmetric-group image and the diagonal span are mutual commutants

The symmetric group `S_d` acts on `(kⁿ)^{⊗d}` by permuting the tensor factors, the diagonal
operators `f^{⊗d}` act by applying one endomorphism of `kⁿ` in every factor, and the two actions
commute (`PiTensorProduct.commute_reindexRepresentation_map`). **Schur-Weyl duality** says that
inside `End_k ((kⁿ)^{⊗d})` the two spans are *exactly* each other's commutants.

One half is already available:
`TauCeti.mem_span_range_map_const_iff_forall_commute_permTensorAction` says that the commutant of
the symmetric-group action is the span of the diagonal operators, and it needs only that `d !` is
invertible. This file records that half as an identity of centralizers
(`TauCeti.coe_centralizer_range_permTensorActionAlgHom_eq_span_range_map_const`) and proves the
other half, which needs semisimplicity: over a field in which `d !` is nonzero, an endomorphism
commuting with every diagonal operator already lies in the image of the group algebra `k[S_d]`.

## The argument

The image `A` of `k[S_d]` in `End_k ((kⁿ)^{⊗d})` is a quotient of `k[S_d]`, which is semisimple by
Maschke's theorem, so the double centralizer theorem `TauCeti.centralizer_centralizer_range`
applies and gives `A'' = A`. The commutant `A'` is the span of the diagonal operators by the half
already available, so `A` is the commutant of that span.

The distinction between `k[S_d]` and its image is not cosmetic: the algebra map
`k[S_d] → End_k ((kⁿ)^{⊗d})` is injective only when `d ≤ n`
(`TauCeti.permTensorActionAlgHom_injective_iff`), so the commutant of the diagonal operators is
the *image* of `k[S_d]` and not `k[S_d]` itself. The statements below are accordingly about
`AlgHom.range`.

## Relation to the general-linear image

Every statement below takes the span of the diagonal operators `f^{⊗d}` over *all*
`f : kⁿ →ₗ[k] kⁿ`, matching the half already proved. The general linear group acts through the
subfamily of `g^{⊗d}` with `g` invertible. The downstream module
`TauCeti/RepresentationTheory/Symmetric/TensorAction/GeneralLinear.lean` proves that these already
span everything (`TauCeti.toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const`)
and deduces the image-level mutual commutants, including
`TauCeti.centralizer_range_tensorPowerRep_asAlgebraHom_eq_range_permTensorActionAlgHom`. The results
in this file are the span-level input to that identification.

## Main results

* `TauCeti.commute_permTensorActionAlgHom_of_forall_commute`: commuting with every factor
  permutation propagates to the whole image of the group algebra the permutations span. (In the
  other direction, commuting with every diagonal operator propagates to their span by Mathlib's
  `Commute.span_right`.)
* `TauCeti.mem_centralizer_range_permTensorActionAlgHom_iff_forall_commute`: centralizing the
  symmetric-group algebra image is equivalent to commuting with every factor permutation.
* `TauCeti.coe_centralizer_range_permTensorActionAlgHom_eq_span_range_map_const`: the commutant of
  the symmetric-group image is the span of the diagonal operators.
* `TauCeti.centralizer_span_range_map_const_eq_range_permTensorActionAlgHom`: **the commutant of
  the diagonal operators is the symmetric-group image**, the half that needs semisimplicity.
* `TauCeti.mem_range_permTensorActionAlgHom_iff_forall_commute`: the same statement as a
  membership criterion, `x` acting as an element of `k[S_d]` exactly when it commutes with every
  diagonal operator.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8, "The double centralizer (image-level)", of which this file proves the form with all
  diagonal operators in place of the image of `k[GLₙ]`.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6 and Appendix B.1.
* C. Procesi, *Lie Groups: An Approach through Invariants and Representations*, Chapter 9.
-/

public section

open scoped Nat TensorProduct

open PiTensorProduct

namespace TauCeti

section CommSemiring

variable {R : Type*} {n d : ℕ} [CommSemiring R]

/-- An endomorphism of `(Rⁿ)^{⊗d}` commuting with every factor permutation commutes with the whole
image of the group algebra `R[S_d]`, the group algebra being spanned by the permutations. -/
theorem commute_permTensorActionAlgHom_of_forall_commute
    {y : Module.End R (⨂[R] _ : Fin d, Fin n → R)}
    (hy : ∀ σ : Equiv.Perm (Fin d), Commute y (permTensorAction R n d σ))
    (a : MonoidAlgebra R (Equiv.Perm (Fin d))) :
    Commute y (permTensorActionAlgHom R n d a) := by
  simpa only [permTensorActionAlgHom_def] using
    Representation.commute_asAlgebraHom_of_forall_commute
      (permTensorAction R n d) hy a

/-- An endomorphism centralizes the image of the symmetric-group algebra exactly when it commutes
with every factor permutation. -/
theorem mem_centralizer_range_permTensorActionAlgHom_iff_forall_commute
    {y : Module.End R (⨂[R] _ : Fin d, Fin n → R)} :
    y ∈ Subalgebra.centralizer R (Set.range ⇑(permTensorActionAlgHom R n d)) ↔
      ∀ σ : Equiv.Perm (Fin d), Commute y (permTensorAction R n d σ) := by
  rw [permTensorActionAlgHom_def, Representation.mem_centralizer_range_asAlgebraHom_iff]

end CommSemiring

section CommRing

variable {R : Type*} {n d : ℕ} [CommRing R]

/-- **The commutant of the symmetric-group image is the span of the diagonal operators.** This is
`TauCeti.mem_span_range_map_const_iff_forall_commute_permTensorAction` read as an identity of
centralizers rather than as a membership criterion: passing from the permutations to the group
algebra they span does not change the commutant. -/
theorem coe_centralizer_range_permTensorActionAlgHom_eq_span_range_map_const
    (h : IsUnit (d ! : R)) :
    (Subalgebra.centralizer R
        ((permTensorActionAlgHom R n d).range : Set (Module.End R (⨂[R] _ : Fin d, Fin n → R))) :
        Set (Module.End R (⨂[R] _ : Fin d, Fin n → R))) =
      (Submodule.span R (Set.range fun f : (Fin n → R) →ₗ[R] (Fin n → R) =>
        map fun _ : Fin d => f) : Set (Module.End R (⨂[R] _ : Fin d, Fin n → R))) := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, AlgHom.coe_range,
    mem_centralizer_range_permTensorActionAlgHom_iff_forall_commute,
    mem_span_range_map_const_iff_forall_commute_permTensorAction h]

end CommRing

section Field

variable {k : Type*} {n d : ℕ} [Field k] [NeZero (d ! : k)]

/-- **Schur-Weyl duality.** Over a field in which `d !` is nonzero, the commutant of the diagonal
operators `f^{⊗d}` on `(kⁿ)^{⊗d}`, taken over all endomorphisms `f` of `kⁿ`, is exactly the image
of the group algebra `k[S_d]` acting by permuting the tensor factors.

Together with `TauCeti.coe_centralizer_range_permTensorActionAlgHom_eq_span_range_map_const`, which
computes the commutant in the other direction, this says that the symmetric-group image and the
span of the diagonal operators are each other's commutants. The general linear group acts through
the invertible `g^{⊗d}`. The downstream theorem
`TauCeti.toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const` proves that these
span the same subalgebra, and
`TauCeti.centralizer_range_tensorPowerRep_asAlgebraHom_eq_range_permTensorActionAlgHom` gives the
resulting commutant of the image of `k[GLₙ]`. -/
@[simp]
theorem centralizer_span_range_map_const_eq_range_permTensorActionAlgHom :
    Subalgebra.centralizer k
        (Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
          map fun _ : Fin d => f) : Set (Module.End k (⨂[k] _ : Fin d, Fin n → k))) =
      (permTensorActionAlgHom k n d).range := by
  -- Maschke's theorem, for the group `S_d` of order `d !`.
  have : NeZero (Nat.card (Equiv.Perm (Fin d)) : k) := by
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [← coe_centralizer_range_permTensorActionAlgHom_eq_span_range_map_const
    (isUnit_iff_ne_zero.2 (NeZero.ne _))]
  exact centralizer_centralizer_range (permTensorActionAlgHom k n d)

/-- **Schur-Weyl duality, as a membership criterion.** An endomorphism of `(kⁿ)^{⊗d}` is the action
of an element of the group algebra `k[S_d]` exactly when it commutes with every diagonal operator
`f^{⊗d}`. -/
theorem mem_range_permTensorActionAlgHom_iff_forall_commute
    (x : Module.End k (⨂[k] _ : Fin d, Fin n → k)) :
    x ∈ (permTensorActionAlgHom k n d).range ↔
      ∀ f : (Fin n → k) →ₗ[k] (Fin n → k), Commute x (map fun _ : Fin d => f) := by
  rw [← centralizer_span_range_map_const_eq_range_permTensorActionAlgHom,
    Subalgebra.mem_centralizer_iff]
  refine ⟨fun hx f => (hx _ (Submodule.subset_span ⟨f, rfl⟩)).symm, fun hx g hg => ?_⟩
  -- Commuting with every diagonal operator propagates to their span.
  refine (Commute.span_right ?_ g hg).symm
  rintro _ ⟨f, rfl⟩
  exact hx f

end Field

end TauCeti
