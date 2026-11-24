/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Open covers of schemes

A set `s` generating the unit ideal of a commutative ring `R` gives Mathlib's affine open cover
`AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop` of `Spec R` by the basic opens
`Spec R[1/a]`, `a ∈ s`. This file records the resulting extensionality principle for morphisms out
of `Spec R`, stated with the localization maps `R → R[1/a]`. For a morphism from `Spec R`
to any scheme, the elements whose basic opens map into affine opens generate the unit ideal.

A morphism into a binary coproduct `A ⨿ B` factors through `A` or through `B` on the members of an
open cover of its source. Lifts along a jointly monic pair glue along an open cover.

## Main results

* `TauCeti.AlgebraicGeometry.Spec.hom_ext_of_span_eq_top`: two morphisms `Spec R ⟶ X` which agree
  after composing with every `Spec R[1/a] ⟶ Spec R`, `a ∈ s`, are equal.
* `AlgebraicGeometry.Scheme.Hom.span_basicOpen_range_subset_affine_eq_top`: the basic opens
  whose images under a morphism from `Spec R` lie in affine opens cover `Spec R`.
* `AlgebraicGeometry.Scheme.Hom.exists_openCover_coprod`: a morphism `T ⟶ A ⨿ B` factors
  through `A` or through `B` on each member of an open cover of `T`.
* `AlgebraicGeometry.Scheme.OpenCover.exists_lift_of_jointlyMono₂`: for a jointly monic pair
  `t, s : R ⟶ U`, a pair of morphisms `T ⟶ U` lifts to `R` once it lifts on an open cover of `T`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

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

/-- Every morphism `r : T ⟶ A ⨿ B` restricts, on the members of an open cover of `T`, to a
morphism through `A` or through `B`. -/
theorem exists_openCover_coprod {T A B : Scheme.{u}} (r : T ⟶ A ⨿ B) :
    ∃ 𝒰 : T.OpenCover.{u}, ∀ i, (∃ a, 𝒰.f i ≫ r = a ≫ coprod.inl) ∨
      ∃ b, 𝒰.f i ≫ r = b ≫ coprod.inr :=
  ⟨(coprodOpenCover.{u, u} A B).pullback₁ r, fun i ↦ by
    rcases i with ⟨⟩ | ⟨⟩
    · exact .inl ⟨pullback.snd _ _, pullback.condition⟩
    · exact .inr ⟨pullback.snd _ _, pullback.condition⟩⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.OpenCover

/-- For a jointly monic pair `t, s : R ⟶ U`, the pair `(a, c)` of morphisms `T ⟶ U` lifts to `R`
as soon as it does on the members of an open cover of `T`. -/
theorem exists_lift_of_jointlyMono₂ {T R U : Scheme.{u}} {t s : R ⟶ U} [JointlyMono₂ t s]
    {a c : T ⟶ U} (𝒰 : T.OpenCover.{u})
    (h : ∀ i, ∃ r : 𝒰.X i ⟶ R, r ≫ t = 𝒰.f i ≫ a ∧ r ≫ s = 𝒰.f i ≫ c) :
    ∃ r : T ⟶ R, r ≫ t = a ∧ r ≫ s = c := by
  choose r ht hs using h
  have hr : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ r i = pullback.snd _ _ ≫ r j := fun i j ↦
    JointlyMono₂.right_cancellation (p₁ := t) (p₂ := s) _ _
      (by simp [ht, pullback.condition_assoc])
      (by simp [hs, pullback.condition_assoc])
  exact ⟨𝒰.glueMorphisms r hr, 𝒰.hom_ext _ _ fun i ↦ by simp [ht],
    𝒰.hom_ext _ _ fun i ↦ by simp [hs]⟩

end AlgebraicGeometry.Scheme.OpenCover

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
