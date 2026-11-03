/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.CategoryTheory.Galois.Transitive

/-!
# Connected finite étale covers

Mathlib's notion of a connected object of a Galois category,
`CategoryTheory.PreGaloisCategory.IsConnected`, is categorical: the object is not initial and has
no subobjects other than the initial one and itself. This file identifies it, for finite étale
schemes over any base `S`, with topological connectedness of the underlying scheme
(`TauCeti.FiniteEtaleScheme.isConnected_iff_connectedSpace`). The initial finite étale schemes are
the empty ones, and the subobjects of a finite étale scheme are its open and closed subschemes,
since every monomorphism is the inclusion of a direct summand.

When `S` is connected, so that finite étale `S`-schemes form a Galois category, a connected
object is one on whose geometric fibre the fundamental group `Aut (fiber x)` acts transitively.
Hence a nonempty finite étale `S`-scheme is connected exactly when the étale fundamental group
acts transitively on its geometric fibre
(`TauCeti.FiniteEtaleScheme.connectedSpace_iff_isPretransitive`): under the equivalence
`CategoryTheory.PreGaloisCategory.functorToContAction` between finite étale `S`-schemes and finite
continuous sets under the fundamental group, connected covers correspond to transitive sets.

## Main results

* `TauCeti.FiniteEtaleScheme.isConnected_iff_connectedSpace`: a finite étale scheme is a connected
  object if and only if its underlying scheme is connected.
* `TauCeti.FiniteEtaleScheme.connectedSpace_iff_isPretransitive`: over a connected base, a
  nonempty finite étale scheme is connected if and only if the fundamental group acts transitively
  on its geometric fibre.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§5–7.
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}}

/-- **Connected finite étale schemes.** A finite étale `S`-scheme is a connected object of the
category of finite étale `S`-schemes if and only if its underlying scheme is connected. -/
theorem isConnected_iff_connectedSpace (X : FiniteEtaleScheme S) :
    IsConnected X ↔ ConnectedSpace X.obj.left := by
  constructor
  · intro hX
    refine connectedSpace_iff_clopen.mpr ⟨not_isEmpty_iff.mp fun h ↦
      hX.notInitial ((isInitial_iff_isEmpty X).mpr h).some, fun s hs ↦ ?_⟩
    -- An open and closed subset `s` is the image of the corresponding open and closed subscheme,
    -- which is either initial, hence empty, or all of `X`.
    let U : X.obj.left.Opens := ⟨s, hs.isOpen⟩
    have hU : Set.range (clopenSubschemeι U hs.isClosed).hom.left = s :=
      range_clopenSubschemeι_hom_left U hs.isClosed
    by_cases he : IsEmpty (clopenSubscheme U hs.isClosed).obj.left
    · left
      rw [← hU, Set.range_eq_empty]
    · right
      have : IsIso (clopenSubschemeι U hs.isClosed) := hX.noTrivialComponent _ _
        fun h ↦ he ((isInitial_iff_isEmpty _).mp ⟨h⟩)
      have : IsIso (clopenSubschemeι U hs.isClosed).hom.left := inferInstanceAs <|
        IsIso (((finiteEtaleSchemeProperty S).ι ⋙ Over.forget S).map (clopenSubschemeι U _))
      rw [← hU, Set.range_eq_univ]
      exact (clopenSubschemeι U hs.isClosed).hom.left.surjective
  · intro hc
    refine ⟨fun h ↦ ((isInitial_iff_isEmpty X).mp ⟨h⟩).false hc.toNonempty.some,
      fun Y i _ hY ↦ ?_⟩
    -- The image of a monomorphism is open and closed, and here nonempty, so it is everything.
    obtain ⟨y⟩ : Nonempty Y.obj.left :=
      not_isEmpty_iff.mp fun h ↦ hY ((isInitial_iff_isEmpty Y).mpr h).some
    have hcl : IsClopen (Set.range i.hom.left) :=
      ⟨i.hom.left.isClosedMap.isClosed_range, i.hom.left.isOpenMap.isOpen_range⟩
    have : Surjective i.hom.left := ⟨Set.range_eq_univ.mp <|
      (isClopen_iff.mp hcl).resolve_left (Set.range_nonempty_iff_nonempty.mpr ⟨y⟩).ne_empty⟩
    have : Epi i := epi_of_surjective i
    exact isIso_of_mono_of_epi i

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **Connected covers are transitive.** Over a connected base `S`, a nonempty finite étale
`S`-scheme is connected if and only if the étale fundamental group `Aut (fiber x)` acts
transitively on its geometric fibre at `x`. -/
theorem connectedSpace_iff_isPretransitive [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S)
    (X : FiniteEtaleScheme S) [Nonempty X.obj.left] :
    ConnectedSpace X.obj.left ↔ MulAction.IsPretransitive (Aut (fiber x)) ((fiber x).obj X) := by
  have : ConnectedSpace S := { toNonempty := ⟨X.obj.hom (Classical.arbitrary _)⟩ }
  have : Nonempty ((fiber x).obj X) := (nonempty_fiber_obj_iff_nonempty x X).mpr inferInstance
  rw [← isConnected_iff_connectedSpace,
    FiberFunctor.isConnected_iff_isPretransitive (fiber x) (Aut (fiber x))]

end TauCeti.FiniteEtaleScheme
