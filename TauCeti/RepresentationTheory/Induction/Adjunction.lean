/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Evaluation in the induction adjunctions

The native induction–restriction and restriction–coinduction Hom equivalences evaluate at the
identity. These equations keep consumers on the public representation carriers. The finite-index
comparison equation likewise evaluates its intertwining map without exposing its construction.
-/

public section

open CategoryTheory Representation

namespace Rep

universe u v w t

/-- Induction–restriction reciprocity evaluates a morphism on the tensor generator at `1`. -/
theorem indResHomEquiv_hom_apply {k : Type u} {G : Type v} {H : Type w}
    [CommRing k] [Group G] [Group H] (φ : G →* H)
    (A : Rep.{max t w u} k G) (B : Rep.{max t w u} k H)
    (f : ind φ A ⟶ B) (a : A) :
    (indResHomEquiv.{t, u, v, w} φ A B f).hom a = f.hom (IndV.mk φ A.ρ 1 a) :=
  rfl

/-- The inverse restriction–coinduction reciprocity evaluates the coinduced function at `1`. -/
theorem resCoindHomEquiv_symm_hom_apply {k : Type u} {G : Type v} {H : Type w}
    [CommRing k] [Monoid G] [Monoid H] (φ : G →* H)
    (B : Rep.{max w t} k H) (A : Rep.{max w t} k G)
    (f : B ⟶ coind φ A) (b : B) :
    ((resCoindHomEquiv.{t, u, v, w} φ B A).symm f).hom b = (f.hom b).1 1 :=
  rfl

/-- The finite-index induction–coinduction comparison is the native map on each vector. -/
theorem indCoindIso_hom_hom_apply {k : Type u} {G : Type v} [CommRing k] [Group G]
    {S : Subgroup G} [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex]
    (A : Rep.{max t u} k S) (a : ind S.subtype A) :
    (indCoindIso A).hom.hom a = indToCoind A a :=
  LinearMap.congr_fun (indCoindIso_hom_hom_toLinearMap A) a

end Rep
