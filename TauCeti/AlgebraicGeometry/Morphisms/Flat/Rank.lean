/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.RingTheory.Flat.Rank

/-!
# The rank of finite flat morphisms under composition

The rank `Scheme.Hom.finrank` of a finite flat morphism is invariant under isomorphisms over its
base. This packages Mathlib's `Scheme.Hom.finrank_comp_left_of_isIso` for objects of `Over S`.
`TauCeti.finrank_eq_of_nonempty_iso_over` requires only the existence of an isomorphism over the
base, incorporating its commuting triangle. It compares an affine group scheme with the Hopf
spectrum of its coordinate algebra, and also transports rank through isomorphisms with Cartier
duals. Composing with an isomorphism of targets instead moves the point at which the rank is
evaluated (`AlgebraicGeometry.Scheme.Hom.finrank_comp_right_of_isIso`).

For finite flat morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, if `f` has constant rank `n`, then
`(f ≫ g).finrank s = n * g.finrank s` (`AlgebraicGeometry.Scheme.Hom.finrank_comp`): degrees of
finite locally free morphisms multiply in towers. The constancy hypothesis cannot be dropped,
since the points of `Y` over a given point of `S` can carry different ranks of `f`. Over an
affine base this is `TauCeti.Module.rankAtStalk_eq_mul_of_rankAtStalk_eq`, and the general case
reduces to it because the rank is computed after base change to affine opens of `S`.

## Main results

* `TauCeti.finrank_eq_of_nonempty_iso_over`: isomorphic schemes over `S` have the same rank.
* `AlgebraicGeometry.Scheme.Hom.finrank_comp_right_of_isIso`: the rank of `f ≫ e` at `e y` is the
  rank of `f` at `y`, for an isomorphism `e`.
* `AlgebraicGeometry.Scheme.Hom.finrank_comp`: the rank of a composite whose first factor has
  constant rank.

## Usage

For `e : X ≅ Y` in `Over S`, use `TauCeti.finrank_eq_of_nonempty_iso_over ⟨e⟩` to obtain
`X.hom.finrank = Y.hom.finrank` when `Y.hom` is finite and flat.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA): the degree of a finite
  locally free morphism.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

namespace TauCeti

universe u

/-- Isomorphic schemes over a fixed base have the same rank function when the target
structural morphism is finite and flat. -/
theorem finrank_eq_of_nonempty_iso_over {S : Scheme.{u}} {X Y : Over S}
    (h : Nonempty (X ≅ Y))
    [Flat Y.hom] [IsFinite Y.hom] : X.hom.finrank = Y.hom.finrank := by
  obtain ⟨e⟩ := h
  rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]

end TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

/-- Composing a finite flat morphism with an isomorphism of targets transports its rank: the
rank of `f ≫ e` at `e y` is the rank of `f` at `y`. -/
@[simp]
theorem Scheme.Hom.finrank_comp_right_of_isIso (f : X ⟶ Y) (e : Y ⟶ S) [IsIso e] [Flat f]
    [IsFinite f] (y : Y) : (f ≫ e).finrank (e y) = f.finrank y :=
  (finrank_of_isPullback (𝟙 X) f (f ≫ e) e (.of_horiz_isIso ⟨by simp⟩) y).symm

/-- **The rank is multiplicative in towers.** If `f : X ⟶ Y` and `g : Y ⟶ S` are finite and flat
and `f` has constant rank `n`, then the rank of `f ≫ g` is `n` times the rank of `g`. -/
theorem Scheme.Hom.finrank_comp (f : X ⟶ Y) (g : Y ⟶ S) [Flat f] [IsFinite f] [Flat g]
    [IsFinite g] {n : ℕ} (hf : ∀ y, f.finrank y = n) (s : S) :
    (f ≫ g).finrank s = n * g.finrank s := by
  -- Reduce to an affine base: base change along an affine open `Spec R ⟶ S` preserves the ranks
  -- of `g` and of `f ≫ g`, and the base change of `f` still has constant rank `n`.
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · obtain ⟨R, i, _, s, rfl⟩ := S.exists_Spec_apply_eq s
    rw [← finrank_pullback_snd, ← finrank_pullback_snd,
      ← finrank_comp_left_of_isIso (pullbackRightPullbackFstIso g i f).hom,
      pullbackRightPullbackFstIso_hom_snd]
    refine this _ _ (fun y ↦ ?_) s ⟨R, rfl⟩
    rw [finrank_pullback_snd, hf]
  obtain ⟨R, rfl⟩ := hS
  -- Over an affine base, `Y` and `X` are affine, so both may be replaced by spectra.
  wlog hY : ∃ A, Y = Spec A generalizing X Y with H
  · have : IsAffine Y := isAffine_of_isAffineHom g
    have := H (f ≫ Y.isoSpec.hom) (fun y ↦ ?_) (Y.isoSpec.inv ≫ g) ⟨_, rfl⟩
    · simpa using this
    · obtain ⟨y, rfl⟩ := Y.isoSpec.hom.surjective y
      rw [finrank_comp_right_of_isIso, hf]
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X with H
  · have : IsAffine X := isAffine_of_isAffineHom f
    have := H (X.isoSpec.inv ≫ f) (fun y ↦ by rw [finrank_comp_left_of_isIso, hf]) ⟨_, rfl⟩
    rwa [Category.assoc, finrank_comp_left_of_isIso] at this
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  -- For spectra, the ranks are the ranks at stalks of the corresponding algebras.
  have hfin : (ψ ≫ φ).hom.Finite := ‹φ.hom.Finite›.comp ‹ψ.hom.Finite›
  have hflat : (ψ ≫ φ).hom.Flat := ‹ψ.hom.Flat›.comp ‹φ.hom.Flat›
  rw [← Spec.map_comp, finrank_SpecMap_eq_finrank hfin hflat, finrank_SpecMap_eq_finrank ‹_› ‹_›]
  let := ψ.hom.toAlgebra
  let := φ.hom.toAlgebra
  let := (ψ ≫ φ).hom.toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq' rfl
  have : Module.Finite R A := ‹ψ.hom.Finite›
  have : Module.Flat R A := ‹ψ.hom.Flat›
  have : Module.Finite A B := ‹φ.hom.Finite›
  have : Module.Flat A B := ‹φ.hom.Flat›
  rw [← RingHom.algebraMap_toAlgebra ψ.hom, ← RingHom.algebraMap_toAlgebra (ψ ≫ φ).hom,
    RingHom.finrank_algebraMap, RingHom.finrank_algebraMap]
  refine TauCeti.Module.rankAtStalk_eq_mul_of_rankAtStalk_eq (A := A) (fun q ↦ ?_) s
  have := hf q
  rwa [finrank_SpecMap_eq_finrank ‹φ.hom.Finite› ‹φ.hom.Flat›,
    ← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap] at this

end AlgebraicGeometry
