/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Basic-open covers of affine schemes

A set `s` generating the unit ideal of a commutative ring `R` gives Mathlib's affine open cover
`AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop` of `Spec R` by the basic opens
`Spec R[1/a]`, `a ∈ s`. This file records the resulting extensionality principle for morphisms out
of `Spec R`, stated with the localization maps `R → R[1/a]`. For a morphism from `Spec R`
to any scheme, the elements whose basic opens map into affine opens generate the unit ideal.

## Main results

* `TauCeti.AlgebraicGeometry.Spec.hom_ext_of_span_eq_top`: two morphisms `Spec R ⟶ X` which agree
  after composing with every `Spec R[1/a] ⟶ Spec R`, `a ∈ s`, are equal.
* `AlgebraicGeometry.Scheme.Hom.span_basicOpen_range_subset_affine_eq_top`: the basic opens
  whose images under a morphism from `Spec R` lie in affine opens cover `Spec R`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The elements whose basic opens map into affine opens generate the unit ideal. Thus they
give a cover via `Scheme.affineOpenCoverOfSpanRangeEqTop` subordinate to affine opens of the
target. -/
theorem span_basicOpen_range_subset_affine_eq_top {A : Type u} [CommRing A]
    {X : Scheme.{u}} (g : Spec (.of A) ⟶ X) :
    Ideal.span {a : A | ∃ U : X.Opens, IsAffineOpen U ∧
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ g) ⊆ U} =
      ⊤ := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hs
  let p : Spec (.of A) := ⟨m, hm.isPrime⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g p)) isOpen_univ
  -- A basic open around `p` which the morphism `g` maps into `U`.
  obtain ⟨_, ⟨a, rfl⟩, hpa, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := g ⁻¹' U) hpU (U.is_open'.preimage g.continuous)
  have has : a ∈ {a : A | ∃ U : X.Opens, IsAffineOpen U ∧
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ g) ⊆ U} := by
    refine ⟨U, hU, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hsub
      ((PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le ⟨q, rfl⟩)
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hpa (hsm (Ideal.subset_span has))

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.Spec

/-- Two morphisms out of `Spec R` agree once they agree on the basic opens `Spec R[1/a]`, `a ∈ s`,
for a set `s` generating the unit ideal of `R`. -/
theorem hom_ext_of_span_eq_top {R : Type u} [CommRing R] (s : Set R) (hs : Ideal.span s = ⊤)
    {X : Scheme.{u}} {f g : Spec (.of R) ⟶ X}
    (h : ∀ a : s, Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a.val))) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a.val))) ≫ g) : f = g :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of R) (fun a : s ↦ a.val)
    (by rwa [Subtype.range_coe])).openCover.hom_ext _ _ h

end TauCeti.AlgebraicGeometry.Spec
