/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
import TauCeti.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Noetherianity under finite-type morphisms and fibres

A scheme of finite type over a Noetherian scheme is Noetherian. In particular, proper schemes
over a field are Noetherian, supplying the finiteness hypothesis in divisor and line-bundle
arguments without requiring a separate instance from the caller.

The fibre `X ×_S Spec κ(s)` of any morphism `f : X ⟶ S` with `X` locally Noetherian is locally
Noetherian (`AlgebraicGeometry.Scheme.Hom.isLocallyNoetherian_fiber`), with no finiteness
hypothesis on `f`: over affine opens `Spec B ⟶ Spec R` it is `Spec (κ(p) ⊗[R] B)`, and
`κ(p) ⊗[R] B` is a quotient of a localization of `B`.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A scheme of finite type over a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsNoetherian Y] : IsNoetherian X where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f

end TauCeti.AlgebraicGeometry

open Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The fibre of a morphism `f : X ⟶ S` over the residue field of a point of `S` is locally
Noetherian whenever `X` is. -/
instance isLocallyNoetherian_fiber {X S : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ S)
    (s : S) : IsLocallyNoetherian (f.fiber s) := by
  change id (IsLocallyNoetherian (f.fiber s)) -- avoid wlog hypotheses confusing the synthesizer
  wlog hS : ∃ R, S = Spec R generalizing X S with H
  · -- Over an affine open `j : Spec R ⟶ S` through `s`, the fibre of `f` is the fibre of its base
    -- change `pullback f j ⟶ Spec R`, whose source is open in `X`.
    obtain ⟨i, t, rfl⟩ := S.affineCover.exists_eq s
    let j := S.affineCover.f i
    have : IsLocallyNoetherian (pullback f j) :=
      isLocallyNoetherian_of_isOpenImmersion (pullback.fst f j)
    have hF : IsLocallyNoetherian ((pullback.snd f j).fiber t) := H (pullback.snd f j) t ⟨_, rfl⟩
    have key {A B : Scheme.{u}} {e : A ⟶ B} (_ : IsIso e) (_ : IsLocallyNoetherian A) :
        IsLocallyNoetherian B :=
      isLocallyNoetherian_of_isOpenImmersion (inv e)
    exact key (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f j) t).isIso_fst_of_isIso hF
  wlog hX : ∃ B, X = Spec B generalizing X with H
  · -- The fibre is covered by the fibres of the restrictions of `f` to an affine cover of `X`.
    refine (isLocallyNoetherian_iff_openCover
      (Pullback.openCoverOfLeft X.affineCover f _)).mpr fun i : X.affineCover.I₀ ↦ ?_
    exact H (X.affineCover.f i ≫ f) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hS
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : IsNoetherianRing B := by simpa using ‹IsLocallyNoetherian (Spec B)›
  algebraize [φ.hom]
  have := s.isPrime
  -- The fibre of `Spec B ⟶ Spec R` over `p` is `Spec (κ(p) ⊗[R] B)`.
  exact isLocallyNoetherian_of_isOpenImmersion (Y := Spec (.of (s.asIdeal.Fiber B)))
    (Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R B s)).hom

end AlgebraicGeometry.Scheme.Hom
