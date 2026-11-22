/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.K3Surface.Basic

/-!
# Base change of K3 surfaces

A K3 surface over a field `k` stays a K3 surface after every extension of the base field `K / k`,
separable or not: if `X ⟶ Spec k` is a K3 surface, then so is `X_K = X ×_k K ⟶ Spec K`. Each
of the defining conditions is checked separately.

* Smoothness of relative dimension two, properness and geometric integrality are stable under
  base change.
* Differential forms commute with base change, `g^* Ω²_{X/k} ≅ Ω²_{X_K/K}` along the projection
  `g : X_K ⟶ X`, and `g^* 𝒪_X ≅ 𝒪_{X_K}`, so a trivialization of `Ω²_{X/k}` pulls back to one of
  `Ω²_{X_K/K}`.
* By flat base change, `H¹(X_K, 𝒪_{X_K}) ≅ K ⊗_k H¹(X, 𝒪_X)`, which vanishes with `H¹(X, 𝒪_X)`.

The base change is stated for an arbitrary cartesian square over `Spec K ⟶ Spec k`. Taking
`K = k`, a cartesian square over the identity of `Spec k` is an isomorphism over `k`, so being a
K3 surface is invariant under isomorphisms of schemes over `k`.

## Main declarations

* `TauCeti.AlgebraicGeometry.IsK3.of_isPullback`: the base change of a K3 surface along a field
  extension, given as a cartesian square, is a K3 surface;
* `TauCeti.AlgebraicGeometry.IsK3.pullback_snd`: the same for the fibre product
  `X ×_{Spec k} Spec K`;
* `TauCeti.AlgebraicGeometry.isK3_comp_iff`: for an isomorphism `e : X' ⟶ X`, `e ≫ f` is a K3
  surface exactly when `f` is.

## References

* D. Huybrechts, *Lectures on K3 Surfaces*, Chapter 1, Definition 1.1, and Chapter 17, §2.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of K)} {g : X' ⟶ X}

/-- **A K3 surface stays a K3 surface after extension of the base field.** If `f : X ⟶ Spec k` is
a K3 surface and `X'` is the base change of `X` along `Spec K ⟶ Spec k` for a field extension
`K / k`, given as a cartesian square with projection `g : X' ⟶ X`, then `X' ⟶ Spec K` is a K3
surface. The extension is arbitrary; it need not be algebraic or separable.
Huybrechts, *Lectures on K3 Surfaces*, Chapter 17, §2.1. -/
theorem IsK3.of_isPullback
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (h : IsK3 k f) :
    IsK3 K f' := by
  -- The base change isomorphisms for differential forms and cohomology are stated for the
  -- structure morphisms of `Over` instances; for these instances `X ↘ Spec k` is `f` and
  -- `X' ↘ Spec K` is `f'`.
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let : X'.Over (Spec (.of K)) := ⟨f'⟩
  have H' : IsPullback g (X' ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := H
  have : IsProper f := h.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨e⟩ := h.nonempty_differentialFormsIso
  refine ⟨MorphismProperty.of_isPullback H h.smoothOfRelativeDimension,
    MorphismProperty.of_isPullback H h.isProper,
    MorphismProperty.of_isPullback H h.geometricallyIntegral,
    ⟨(differentialFormsBaseChangeIso H' 2).symm ≪≫ (Scheme.Modules.pullback g).mapIso e ≪≫
      pullbackObjUnitIso g⟩, ?_⟩
  refine (cohomologyBaseLinearEquivOfIso K (pullbackObjUnitIso g) 1).toEquiv.subsingleton_congr.1
    ((subsingleton_cohomology_pullback_iff_of_isPullback H' _ 1).2 ?_)
  exact h.subsingleton_cohomology_one

/-- **A K3 surface stays a K3 surface after extension of the base field**, for the fibre product
`X ×_{Spec k} Spec K` with its second projection to `Spec K`. -/
theorem IsK3.pullback_snd (h : IsK3 k f) :
    IsK3 K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  h.of_isPullback (IsPullback.of_hasPullback _ _)

/-- **Being a K3 surface is invariant under isomorphisms over the base field.** For an
isomorphism of schemes `e : X' ⟶ X` and `f : X ⟶ Spec k`, the composite `e ≫ f` is a K3 surface
exactly when `f` is. -/
theorem isK3_comp_iff (e : X' ⟶ X) [IsIso e] (f : X ⟶ Spec (.of k)) :
    IsK3 k (e ≫ f) ↔ IsK3 k f := by
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  -- A commutative square over the identity of `Spec k` whose top side is an isomorphism is
  -- cartesian, so `IsK3.of_isPullback` applies with `K = k`.
  have key {Y Y' : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e] (f : Y ⟶ Spec (.of k)) (h : IsK3 k f) :
      IsK3 k (e ≫ f) :=
    h.of_isPullback (g := e) (by rw [hid]; exact IsPullback.of_horiz_isIso ⟨by simp⟩)
  refine ⟨fun h ↦ ?_, key e f⟩
  simpa using key (inv e) _ h

end TauCeti.AlgebraicGeometry
