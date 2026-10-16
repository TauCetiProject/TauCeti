/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete

/-!
# Affinoid adic spaces from strongly noetherian Tate pairs

The presentation-limit pre-adic space of a strongly noetherian Tate pair is an affinoid adic
space. This packages the sheafiness theorem for strongly noetherian Tate pairs with the general
criterion that a sheafy affinoid pre-adic space is adic.

The main source of strongly noetherian Tate rings is finite type over one: a ring `B` topologically
of finite type over a strongly noetherian Tate ring is again a strongly noetherian Tate ring, and
complete and Hausdorff. Over a complete nonarchimedean field `k`, the pair `(B, B°)` is then an
affinoid `k`-algebra topologically of finite type in the sense of Wedhorn's Definition 7.56, and
its adic spectrum is an affinoid adic space. These are the classical affinoids of rigid geometry:
the quotients `k⟨X₁, …, Xₙ⟩ ⧸ 𝔞` of Tate algebras, with the closed unit polydiscs as the case
`𝔞 = 0`.

## Main results

* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian`:
  the adic spectrum of a strongly noetherian Tate pair, with its presentation-limit structure
  sheaf, is an adic space.
* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isTopologicallyFiniteType`:
  the adic spectrum of a ring topologically of finite type over a strongly noetherian Tate ring,
  with any plus ring of power-bounded elements containing a ring of definition, is an adic space.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.56,
  Remark 6.37, Definition 8.22 and Theorem 8.28(b).
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

universe u

section StronglyNoetherian

variable {A : Type u} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A) {Aplus : Subring A}

/-- **The adic spectrum of a strongly noetherian Tate pair is an affinoid adic space.** The
structure presheaf is a sheaf by the strongly noetherian form of Tate acyclicity, and the
presentation-limit pre-adic space is affinoid. The ring need not be complete or Hausdorff. -/
theorem isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P Aplus hAplus hP) :=
  isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP
    (isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian P hP hAplus)

end StronglyNoetherian

section TopologicallyFiniteType

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R]
  [IsStronglyNoetherian R] {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] (P : PairOfDefinition A) {Aplus : Subring A}

/-- **The adic spectrum of a ring topologically of finite type over a strongly noetherian Tate ring
is an affinoid adic space.** Let `φ : R → A` be topologically of finite type, with `R` a strongly
noetherian Tate ring and `A` a uniform additive group. Then `A` is a complete Hausdorff strongly
noetherian Tate ring, so for any pair of definition `P` of `A` and any plus ring `A⁺` of
power-bounded elements containing its ring of definition, `Spa(A, A⁺)` is an affinoid adic space.

Over a complete nonarchimedean field `R = k` with `A⁺ = A°` this says that the adic spectrum of an
affinoid `k`-algebra topologically of finite type (Wedhorn, Definition 7.56) is an affinoid adic
space. -/
theorem isAdic_presentationLimitPreAdicSpace_of_isTopologicallyFiniteType {φ : R →+* A}
    (hφ : IsTopologicallyFiniteType φ) (hP : P.ringOfDefinition ≤ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P Aplus hAplus hP) :=
  have := hφ.isTateRing
  have := hφ.completeSpace
  have := hφ.t2Space
  have := hφ.isStronglyNoetherian
  isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian P hP hAplus

end TopologicallyFiniteType

end TauCeti.ValuationSpectrum

end
