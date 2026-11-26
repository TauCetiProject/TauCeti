/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear
public import TauCeti.Analysis.CStarAlgebra.Representation.GNS

/-!
# Nuclearly embeddable C⋆-algebras

A C⋆-algebra `A` is *nuclearly embeddable* (`TauCeti.CStarAlgebra.IsNuclearlyEmbeddable`) when it
has a faithful representation `π : A → B(H)` on a Hilbert space which is a nuclear contraction as
a completely positive map: `π` is a point-norm limit of composites `A → M_n → B(H)` of completely
positive contractions. The approximating maps return to `B(H)`, not to `A`; this is the
difference from nuclearity, where the identity of `A` itself is approximated.

By the CStarAlgebras roadmap (C7.1), this is equivalent to exactness, the tensor exactness of
`A ⊗min −`, and does not depend on the faithful representation (nuclear embeddability,
Blackadar IV.3.4.16 and IV.3.4.18). This file states the notion and its first
properties, which need neither the minimal tensor product nor the Arveson extension theorem.

## Main declarations

* `TauCeti.CStarAlgebra.IsNuclearlyEmbeddable`: some faithful representation of `A` on a Hilbert
  space in the universe of `A` is a nuclear contraction.

## Main statements

* `TauCeti.CStarAlgebra.IsNuclearlyEmbeddable.of_injective`: a C⋆-algebra that embeds by an
  injective star homomorphism into a nuclearly embeddable one is nuclearly embeddable; in
  particular nuclear embeddability passes to C⋆-subalgebras and is invariant under star
  isomorphism (`TauCeti.CStarAlgebra.IsNuclearlyEmbeddable.of_starAlgEquiv`).
* `TauCeti.CStarAlgebra.IsNuclear.isNuclearlyEmbeddable`: nuclear C⋆-algebras are nuclearly
  embeddable, by composing the approximations of the identity with a faithful representation
  from the Gelfand–Naimark theorem. Hence `ℂ` and the matrix algebras `M_n(ℂ)` are nuclearly
  embeddable.

## References

* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences 122, Springer (2006), IV.3.4.16 and IV.3.4.18.
-/

public section

open scoped CStarAlgebra ComplexOrder

open CompletelyPositiveMap CompletelyPositiveMapClass

universe u

namespace TauCeti.CStarAlgebra

variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A C⋆-algebra `A` is **nuclearly embeddable** when it has a faithful representation
`π : A → B(H)` on a Hilbert space `H` in the universe of `A` that is a nuclear contraction as a
completely positive map: `π` is a point-norm limit of composites `A → M_n → B(H)` of completely
positive contractions. -/
class IsNuclearlyEmbeddable : Prop where
  /-- Some faithful representation of `A` is a nuclear contraction. -/
  exists_injective_isNuclearContraction :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), Function.Injective π ∧
        (toCompletelyPositiveLinearMap π).IsNuclearContraction

variable {A}

/-- A faithful representation that is a nuclear contraction makes `A` nuclearly embeddable. -/
theorem IsNuclearlyEmbeddable.of_isNuclearContraction {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) (h : (toCompletelyPositiveLinearMap π).IsNuclearContraction) :
    IsNuclearlyEmbeddable A :=
  ⟨⟨H, _, _, _, π, hπ, h⟩⟩

variable {B : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Subalgebras.** If `ι : A → B` is an injective star homomorphism and `B` is nuclearly
embeddable, then so is `A`: a faithful nuclear representation of `B` restricts along `ι` to a
faithful nuclear representation of `A`. -/
theorem IsNuclearlyEmbeddable.of_injective [IsNuclearlyEmbeddable B] (ι : A →⋆ₙₐ[ℂ] B)
    (hι : Function.Injective ι) : IsNuclearlyEmbeddable A := by
  obtain ⟨H, _, _, _, π, hπ, h⟩ :=
    IsNuclearlyEmbeddable.exists_injective_isNuclearContraction (A := B)
  refine .of_isNuclearContraction (π.comp ι) (hπ.comp hι) ?_
  convert h.comp_right (toCompletelyPositiveLinearMap ι) (NonUnitalStarAlgHom.norm_apply_le ι)
    using 1
  ext a : 1
  simp

/-- Nuclear embeddability is invariant under star isomorphism. -/
theorem IsNuclearlyEmbeddable.of_starAlgEquiv [IsNuclearlyEmbeddable B] (e : A ≃⋆ₐ[ℂ] B) :
    IsNuclearlyEmbeddable A :=
  .of_injective (NonUnitalStarAlgHom.ofClass e) e.injective

/-- **Nuclear C⋆-algebras are nuclearly embeddable**: composing completely positive contractions
`A → M_n → A` approximating the identity with a faithful representation of `A` (Gelfand–Naimark)
approximates that representation. -/
instance (priority := 100) IsNuclear.isNuclearlyEmbeddable [IsNuclear A] :
    IsNuclearlyEmbeddable A := by
  obtain ⟨H, _, _, _, π, hπ, -⟩ := exists_faithful_nondegenerate_representation A
  refine .of_isNuclearContraction π hπ ?_
  convert (IsNuclear.isNuclearContraction_id (A := A)).comp_left
    (toCompletelyPositiveLinearMap π) (NonUnitalStarAlgHom.norm_apply_le π) using 1
  ext a : 1
  simp

end TauCeti.CStarAlgebra
