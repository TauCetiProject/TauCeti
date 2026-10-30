/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Birational.Irreducible
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.Scheme.Normal

/-!
# Finite modifications of normal schemes are isomorphisms

A normal integral scheme admits no nontrivial finite modification with reduced source (Stacks,
Lemma 29.54.8 (0AB1)). The source `X` of a modification `f : X ⟶ Y` of an integral scheme is
birational to `Y`, so irreducible, hence integral when it is reduced. Over a nonempty affine open
`V` of `Y`, the finite map `Γ(Y, V) → Γ(X, f ⁻¹ V)` is then a finite map of domains which becomes
an isomorphism over a nonempty open where `f` is an isomorphism. Hence `Γ(X, f ⁻¹ V)` embeds into
the function field of `Y`, the fraction field of `Γ(Y, V)`, as an integral extension of
`Γ(Y, V)`. When `Γ(Y, V)` is integrally closed, this extension is trivial.

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

/-- The affine step: if `f` is finite between integral schemes with `Y` normal, and `f` is an
isomorphism on sections over a nonempty open `W` of an affine open `V`, then `f` is bijective on
sections over `V`. Restricting to `f ⁻¹ W ≅ W` and taking germs at the generic point embeds
`Γ(X, f ⁻¹ V)` into `k(Y)`, the fraction field of `Γ(Y, V)`, as an integral extension of the
integrally closed domain `Γ(Y, V)`. -/
private theorem bijective_app [IsIntegral X] [IsIntegral Y] [IsNormalScheme Y] (f : X ⟶ Y)
    [IsFinite f] {V W : Y.Opens} (hV : IsAffineOpen V) (hWV : W ≤ V) [Nonempty W]
    [Nonempty (f ⁻¹ᵁ W)] [IsIso (f.app W)] : Function.Bijective (f.app V) := by
  have : Nonempty V := ⟨⟨_, hWV (Classical.choice ‹Nonempty W›).2⟩⟩
  have : Nonempty (f ⁻¹ᵁ V) :=
    ⟨⟨_, f.preimage_mono hWV (Classical.choice ‹Nonempty (f ⁻¹ᵁ W)›).2⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen Y V hV
  have := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hV
  let σ := X.presheaf.map (homOfLE (f.preimage_mono hWV)).op ≫ inv (f.app W) ≫
    Y.germToFunctionField W
  have hσ : Function.Injective σ :=
    (Y.germToFunctionField_injective _).comp
      ((ConcreteCategory.bijective_of_isIso (inv (f.app W))).1.comp
        (map_injective_of_isIntegral X _))
  -- `σ` extends the inclusion of `Γ(Y, V)` into its fraction field `k(Y)`.
  have hσφ (a : Γ(Y, V)) : σ (f.app V a) = algebraMap Γ(Y, V) Y.functionField a := by
    have hnat : f.app V ≫ X.presheaf.map (homOfLE (f.preimage_mono hWV)).op =
        Y.presheaf.map (homOfLE hWV).op ≫ f.app W :=
      (f.naturality _).symm
    have : f.app V ≫ σ = Y.germToFunctionField V := by
      rw [reassoc_of% hnat, IsIso.hom_inv_id_assoc]
      exact TopCat.Presheaf.germ_res _ _ _ _
    exact congr($this a)
  refine ⟨fun a b hab ↦ IsFractionRing.injective Γ(Y, V) Y.functionField ?_, fun b ↦ ?_⟩
  · rw [← hσφ, ← hσφ, hab]
  · -- `σ b` is integral over the integrally closed domain `Γ(Y, V)`, so it comes from `Γ(Y, V)`.
    obtain ⟨p, hp, hpb⟩ := (f.finite_app V hV).to_isIntegral b
    have : _root_.IsIntegral Γ(Y, V) (σ b) := by
      refine ⟨p, hp, ?_⟩
      rw [← RingHom.ext (f := σ.hom.comp (f.app V).hom) hσφ, ← Polynomial.hom_eval₂, hpb,
        map_zero]
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    exact ⟨a, hσ (by rw [hσφ, ha])⟩

/-- **A finite modification of a normal scheme is an isomorphism.** If `Y` is a normal integral
scheme, `X` is reduced and `f : X ⟶ Y` is a finite modification, then `f` is an isomorphism.
Stacks, Lemma 29.54.8 (0AB1), where `X` is assumed integral. -/
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
  have : Nonempty (f ⁻¹ᵁ Y.basicOpen g) := by
    obtain ⟨x, -⟩ := (f ∣_ Y.basicOpen g).surjective ⟨y, hyg⟩
    exact ⟨x⟩
  rw [isIso_morphismRestrict_iff_isIso_app f hV, ConcreteCategory.isIso_iff_bijective]
  exact bijective_app f hV (Y.basicOpen_le g)

end TauCeti.AlgebraicGeometry.IsModification
