/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Limits
public import TauCeti.CategoryTheory.Limits.Preserves.Over

/-!
# Exactness and conservativity of geometric fibre functors

For a geometric point `x : Spec Ω ⟶ S`, with `Ω` a separably closed field, the geometric fibre
functor `FiniteEtaleScheme.fiber x` from finite étale `S`-schemes to finite sets preserves finite
limits and finite coproducts, and it reflects isomorphisms when `S` is preconnected. These are
the axioms (G4), the finite-coproduct half of (G5), and (G6) of a fibre functor on a Galois
category in the sense of Lenstra, as they appear in Mathlib's
`CategoryTheory.PreGaloisCategory.FiberFunctor`. Preservation of epimorphisms and of quotients by
finite groups, the rest of (G5), are not treated here.

Base change `FiniteEtaleScheme.pullback f` is computed by `Over.pullback f`. That is a right
adjoint, so it preserves limits, and it preserves finite coproducts because finite coproducts of
schemes are universal (`CategoryTheory.Over.preservesFiniteCoproducts_pullback`). The fibre
functor is base change to the geometric point followed by an equivalence with finite sets.

Conservativity rests on `isEmpty_fiber_obj_iff`: a finite étale morphism is open and closed, so
over a preconnected base a nonempty finite étale scheme surjects onto the base and has nonempty
geometric fibres. Every monomorphism of finite étale schemes is the inclusion of a direct summand
(`exists_isColimit_binaryCofanMk_of_mono`). If `f` is bijective on one geometric fibre, the
summand complementary to its diagonal has empty fibre, hence is empty, so `f` is a monomorphism;
the summand complementary to `f` is then empty in the same way, so `f` is an isomorphism.

## Main results

* `TauCeti.FiniteEtaleScheme.preservesFiniteLimits_fiber`,
  `TauCeti.FiniteEtaleScheme.preservesFiniteCoproducts_fiber`: the geometric fibre functor
  preserves finite limits and finite coproducts.
* `TauCeti.FiniteEtaleScheme.isEmpty_fiber_obj_iff`: over a preconnected base, a finite étale
  scheme has empty geometric fibre exactly when it is empty.
* `TauCeti.FiniteEtaleScheme.reflectsIsomorphisms_fiber`: over a preconnected base, the geometric
  fibre functor reflects isomorphisms.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}}

/-- Base change of finite étale schemes preserves finite limits. -/
instance preservesFiniteLimits_pullback (f : T ⟶ S) : PreservesFiniteLimits (pullback f) := by
  have : PreservesFiniteLimits (pullback f ⋙ (finiteEtaleSchemeProperty T).ι) :=
    inferInstanceAs (PreservesFiniteLimits ((finiteEtaleSchemeProperty S).ι ⋙ Over.pullback f))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (finiteEtaleSchemeProperty T).ι

/-- Base change of finite étale schemes preserves finite coproducts. -/
instance preservesFiniteCoproducts_pullback (f : T ⟶ S) :
    PreservesFiniteCoproducts (pullback f) := by
  have : PreservesFiniteCoproducts (pullback f ⋙ (finiteEtaleSchemeProperty T).ι) :=
    inferInstanceAs
      (PreservesFiniteCoproducts ((finiteEtaleSchemeProperty S).ι ⋙ Over.pullback f))
  exact preservesFiniteCoproducts_of_reflects_of_preserves _ (finiteEtaleSchemeProperty T).ι

/-- Over a separably closed field `K`, the finite set attached to a finite étale scheme is empty
exactly when the scheme is empty. -/
theorem isEmpty_equivOfIsSepClosed_functor_obj_iff (K : Type u) [Field K] [IsSepClosed K]
    (X : FiniteEtaleScheme (Spec (.of K))) :
    IsEmpty ((equivOfIsSepClosed K).functor.obj X) ↔ IsEmpty X.obj.left := by
  rw [← isInitial_iff_isEmpty,
    (IsInitial.isInitialIffObj (equivOfIsSepClosed K).functor X).nonempty_congr,
    Concrete.initial_iff_empty_of_preserves_of_reflects]

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The geometric fibre functor preserves finite limits. -/
instance preservesFiniteLimits_fiber (x : Spec (.of Ω) ⟶ S) :
    PreservesFiniteLimits (fiber x) :=
  inferInstanceAs (PreservesFiniteLimits (pullback x ⋙ _))

/-- The geometric fibre functor preserves finite coproducts. -/
instance preservesFiniteCoproducts_fiber (x : Spec (.of Ω) ⟶ S) :
    PreservesFiniteCoproducts (fiber x) :=
  inferInstanceAs (PreservesFiniteCoproducts (pullback x ⋙ _))

/-- The geometric fibre of `X` at `x` is empty exactly when the base change of `X` to the
geometric point is the empty scheme. -/
theorem isEmpty_fiber_obj_iff_isEmpty_pullback (x : Spec (.of Ω) ⟶ S)
    (X : FiniteEtaleScheme S) :
    IsEmpty ((fiber x).obj X) ↔ IsEmpty ((pullback x).obj X).obj.left := by
  rw [fiber_def, Functor.comp_obj, isEmpty_equivOfIsSepClosed_functor_obj_iff]

/-- Over a preconnected base, a finite étale scheme has empty geometric fibre at a geometric
point exactly when it is empty. -/
theorem isEmpty_fiber_obj_iff [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S)
    (X : FiniteEtaleScheme S) :
    IsEmpty ((fiber x).obj X) ↔ IsEmpty X.obj.left := by
  rw [isEmpty_fiber_obj_iff_isEmpty_pullback]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun y ↦ h.elim (Limits.pullback.fst X.obj.hom x y)⟩⟩
  rw [← not_nonempty_iff] at h ⊢
  rintro ⟨y⟩
  -- The image of `X` in `S` is open and closed and nonempty, hence everything.
  have hclopen : IsClopen (Set.range X.obj.hom) :=
    ⟨X.obj.hom.isClosedMap.isClosed_range, X.obj.hom.isOpenMap.isOpen_range⟩
  obtain ⟨z⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  obtain ⟨w, -⟩ : z ∈ Set.range (Limits.pullback.snd X.obj.hom x) := by
    simp [Scheme.Pullback.range_snd, hclopen.eq_univ ⟨_, y, rfl⟩]
  exact h ⟨w⟩

/-- Over a preconnected base, if the geometric fibre functor sends the first inclusion `i` of a
binary coproduct of finite étale schemes to a bijection, then `i` is an isomorphism. -/
private theorem isIso_of_isColimit_binaryCofanMk [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S)
    {X Y Z : FiniteEtaleScheme S} {i : X ⟶ Y} {u : Z ⟶ Y} (hc : IsColimit (BinaryCofan.mk i u))
    [IsIso ((fiber x).map i)] : IsIso i := by
  -- The fibre of `Z` is disjoint from the image of the fibre of `X`, which is everything.
  have : IsEmpty Z.obj.left := by
    rw [← isEmpty_fiber_obj_iff x]
    obtain ⟨-, -, hcompl⟩ := (Types.binaryCofan_isColimit_iff _).mp
      ⟨isColimitMapCoconeBinaryCofanEquiv (fiber x ⋙ FintypeCat.incl) i u
        (isColimitOfPreserves (fiber x ⋙ FintypeCat.incl) hc)⟩
    have hsurj := (ConcreteCategory.bijective_of_isIso ((fiber x).map i)).2
    exact ⟨fun z ↦ Set.disjoint_left.mp hcompl.disjoint (hsurj ((fiber x).map u z)) ⟨z, rfl⟩⟩
  exact (BinaryCofan.isColimit_iff_isIso_inl (isInitialOfIsEmpty Z) (BinaryCofan.mk i u)).mp ⟨hc⟩

/-- Over a preconnected base, the geometric fibre functor reflects isomorphisms: a morphism of
finite étale schemes which is bijective on the geometric fibre at one geometric point is an
isomorphism. -/
instance reflectsIsomorphisms_fiber [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S) :
    (fiber x).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    -- `f` is a monomorphism: its diagonal is the first inclusion of a binary coproduct, and is
    -- bijective on fibres since the fibre functor preserves the kernel pair of `f`.
    have : Mono f := by
      obtain ⟨Z, u, ⟨hc⟩⟩ := exists_isColimit_binaryCofanMk_of_mono (pullback.diagonal f)
      have := ((IsPullback.of_hasPullback f f).map (fiber x)).isIso_fst_of_isIso
      have : IsIso ((fiber x).map (pullback.diagonal f) ≫ (fiber x).map (pullback.fst f f)) := by
        rw [← Functor.map_comp, pullback.diagonal_fst, CategoryTheory.Functor.map_id]
        infer_instance
      have := IsIso.of_isIso_comp_right ((fiber x).map (pullback.diagonal f))
        ((fiber x).map (pullback.fst f f))
      exact (pullback.isIso_diagonal_iff f).mp (isIso_of_isColimit_binaryCofanMk x hc)
    obtain ⟨Z, u, ⟨hc⟩⟩ := exists_isColimit_binaryCofanMk_of_mono f
    exact isIso_of_isColimit_binaryCofanMk x hc

end TauCeti.FiniteEtaleScheme
