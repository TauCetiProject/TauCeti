/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.Irreducible
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Normal
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Restrict

/-!
# Finite modifications with reduced source of normal integral schemes are isomorphisms

A normal integral scheme admits no nontrivial finite modification with reduced source (Stacks,
Lemma 29.54.8 (0AB1)). The source `X` of a modification `f : X ⟶ Y` of an integral scheme is
birational to `Y`, so irreducible, hence integral when it is reduced. Over a nonempty affine open
`V` of `Y`, the finite map `Γ(Y, V) → Γ(X, f ⁻¹ V)` is then a finite map of domains which becomes
an isomorphism over a nonempty open where `f` is an isomorphism. Hence `Γ(X, f ⁻¹ V)` embeds into
the function field of `Y`, the fraction field of `Γ(Y, V)`, as an integral extension of
`Γ(Y, V)`. When `Γ(Y, V)` is integrally closed, this extension is trivial
(`AlgebraicGeometry.Scheme.Hom.bijective_app_of_isFinite_of_isIso_app`).

Reducedness of the source cannot be dropped: over `Y = Spec k[t]`, the finite morphism from
`Spec k[t, e] ⧸ (e², t e)` is an isomorphism over `D(t)`, whose preimage is dense, but it is not an
isomorphism.

## Main results

* `TauCeti.AlgebraicGeometry.IsModification.isIso_of_isFinite`: a finite modification with reduced
  source of a normal integral scheme is an isomorphism.

## References

* [Stacks Project, Lemma 29.54.8](https://stacks.math.columbia.edu/tag/0AB1).
-/

public section

open CategoryTheory MorphismProperty AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.IsModification

universe u

variable {X Y : Scheme.{u}}

/-- **A finite modification with reduced source of a normal integral scheme is an isomorphism.**
If `Y` is a normal integral scheme, `X` is reduced and `f : X ⟶ Y` is a finite modification, then
`f` is an isomorphism. Stacks, Lemma 29.54.8 (0AB1), where `X` is assumed integral. -/
@[stacks 0AB1]
theorem isIso_of_isFinite [IsReduced X] [IsIntegral Y] [IsNormalScheme Y] (f : X ⟶ Y)
    [IsModification f] [IsFinite f] : IsIso f := by
  have := (birational f).irreducibleSpace
  have := isIntegral_of_irreducibleSpace_of_isReduced X
  obtain ⟨U, hU, -, hfU⟩ := exists_isIso_morphismRestrict (f := f)
  rw [← isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := isomorphisms _) _
    (iSup_affineOpens_eq_top Y)]
  rintro ⟨V, hV⟩
  rw [isomorphisms.iff]
  obtain hVe | hVne := (V : Set Y).eq_empty_or_nonempty
  · have : IsEmpty V := Set.isEmpty_coe_sort.mpr hVe
    infer_instance
  -- A nonempty basic open `D(g)` of `V` inside `U`, over which `f` is an isomorphism.
  obtain ⟨y, hyV, hyU⟩ := hU.inter_open_nonempty V V.isOpen hVne
  obtain ⟨g, hgU, hyg⟩ := hV.exists_basicOpen_le (V := U) ⟨y, hyU⟩ hyV
  have : IsIso (f ∣_ Y.basicOpen g) :=
    IsZariskiLocalAtTarget.restrict_of_le (isomorphisms Scheme) hfU hgU
  have : IsIso (f.app (Y.basicOpen g)) :=
    (isIso_morphismRestrict_iff_isIso_app f (hV.basicOpen g)).mp ‹_›
  have : Nonempty (Y.basicOpen g) := ⟨⟨y, hyg⟩⟩
  rw [isIso_morphismRestrict_iff_isIso_app f hV, ConcreteCategory.isIso_iff_bijective]
  exact f.bijective_app_of_isFinite_of_isIso_app hV (Y.basicOpen_le g)

end TauCeti.AlgebraicGeometry.IsModification
