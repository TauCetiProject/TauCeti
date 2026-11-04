/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Perfect
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import TauCeti.RingTheory.Perfect.IsPRadical

/-!
# Perfection of affine schemes

Let `p` be a prime and `A` a ring with `p = 0`. The perfection of the affine scheme `Spec A` is
`Spec (PerfectClosure A p)`, the spectrum of Mathlib's colimit perfection
`A → A^{1/p} → A^{1/p²} → ⋯`. This file proves the two properties that make it the perfection,
for every `p`-radical ring map `φ : A ⟶ B` (Mathlib's `IsPRadical`), of which
`PerfectClosure.of A p` is the main example:

* `Spec.map φ : Spec B ⟶ Spec A` is a universal homeomorphism, so passing to the perfection does
  not change the underlying topology, even after base change;
* every morphism from a perfect scheme `Y` to `Spec A` factors uniquely through `Spec.map φ`. When
  `B` is perfect, as for `PerfectClosure A p`, the scheme `Spec B` is itself perfect, so
  `Spec.map φ` is a coreflection of `Spec A` into perfect schemes.

These are the affine building blocks of the perfection `X ↦ X^perf` of an arbitrary scheme over
`𝔽_p`, which is affine-locally `Spec (PerfectClosure A p)`.

## Main results

* `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.SpecMap_of_isPRadical`: if `φ` is
  `p`-radical and `p = 0` in its target, then `Spec.map φ` is a universal homeomorphism.
* `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.SpecMap_perfectClosureOf`: the instance
  that `Spec (PerfectClosure A p) ⟶ Spec A` is a universal homeomorphism.
* `AlgebraicGeometry.Scheme.IsPerfect.bijective_comp_SpecMap`: for a perfect scheme `Y` and a
  `p`-radical `φ : A ⟶ B` with `p = 0` in `A`, composition with `Spec.map φ` is a bijection
  `(Y ⟶ Spec B) → (Y ⟶ Spec A)`.
* `AlgebraicGeometry.Scheme.IsPerfect.homSpecEquiv`: the corresponding equivalence of hom-sets.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Definition 3.1, Lemma 3.4 and Proposition 3.13.
* The Stacks Project, [Tag 04DF](https://stacks.math.columbia.edu/tag/04DF), the integral
  characterization of universal homeomorphisms.
-/

public section

open CategoryTheory Opposite Polynomial

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {A B : CommRingCat.{u}} (φ : A ⟶ B) (p : ℕ) [Fact p.Prime]

/-- **The spectrum of a `p`-radical ring map is a universal homeomorphism.** If `φ : A ⟶ B` is
`p`-radical and `p = 0` in `B`, then `Spec.map φ : Spec B ⟶ Spec A` is integral, universally
injective and surjective. -/
theorem IsUniversalHomeomorphism.SpecMap_of_isPRadical [IsPRadical φ.hom p] (hB : (p : B) = 0) :
    IsUniversalHomeomorphism (Spec.map φ) := by
  refine (IsUniversalHomeomorphism.SpecMap_iff φ).2
    ⟨IsPRadical.isIntegral φ.hom p, fun K _ g₁ g₂ hg ↦ ?_,
      (IsPRadical.isHomeomorph_comap φ.hom p).surjective⟩
  -- A field receiving a map from `B` has characteristic `p`, and is reduced, so two maps into it
  -- agreeing on `A` agree.
  have : CharP K p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast g₁.hom, hB, map_zero])
  ext1
  exact IsPRadical.injective_comp K φ.hom p (congrArg CommRingCat.Hom.hom hg)

/-- **The perfection of an affine scheme is a universal homeomorphism**: for a ring `A` of
characteristic `p`, the map `Spec (PerfectClosure A p) ⟶ Spec A` is a universal homeomorphism. -/
instance IsUniversalHomeomorphism.SpecMap_perfectClosureOf (A : Type u) [CommRing A] [CharP A p] :
    IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom (PerfectClosure.of A p))) :=
  have : IsPRadical (CommRingCat.ofHom (PerfectClosure.of A p)).hom p :=
    PerfectClosure.isPRadical A p
  SpecMap_of_isPRadical _ p (CharP.cast_eq_zero _ p)

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IsPerfect

variable {A B : CommRingCat.{u}} (φ : A ⟶ B) {p : ℕ} [Fact p.Prime] (Y : Scheme.{u})
  [IsPerfect Y p]

/-- **Morphisms from a perfect scheme lift uniquely along the spectrum of a `p`-radical map.** If
`Y` is perfect and `φ : A ⟶ B` is `p`-radical with `p = 0` in `A`, then composition with
`Spec.map φ` is a bijection from morphisms `Y ⟶ Spec B` to morphisms `Y ⟶ Spec A`. -/
theorem bijective_comp_SpecMap [IsPRadical φ.hom p] (hA : (p : A) = 0) :
    Function.Bijective fun f : Y ⟶ Spec B ↦ f ≫ Spec.map φ := by
  -- Under the Γ–Spec adjunction, a morphism `Y ⟶ Spec R` is a ring map `R ⟶ Γ(Y, ⊤)`, and composing
  -- with `Spec.map φ` corresponds to precomposing that ring map with `φ`.
  let e (R : CommRingCat.{u}) : (R ⟶ Γ(Y, ⊤)) ≃ (Y ⟶ Spec R) :=
    (opEquiv _ _).symm.trans (ΓSpec.adjunction.homEquiv Y (op R))
  have he (g : B ⟶ Γ(Y, ⊤)) : e B g ≫ Spec.map φ = e A (φ ≫ g) :=
    (ΓSpec.adjunction.homEquiv_naturality_right _ φ.op).symm
  have h : Function.Bijective fun g : B ⟶ Γ(Y, ⊤) ↦ φ ≫ g :=
    (ConcreteCategory.homEquiv (X := A) (Y := Γ(Y, ⊤))).symm.bijective.comp <|
      (IsPRadical.bijective_comp φ.hom p hA).comp
        (ConcreteCategory.homEquiv (X := B) (Y := Γ(Y, ⊤))).bijective
  convert (e A).bijective.comp (h.comp (e B).symm.bijective) using 1
  ext1 f
  simp [← he]

/-- For a perfect scheme `Y` and a `p`-radical `φ : A ⟶ B` with `p = 0` in `A`, the bijection
`(Y ⟶ Spec B) ≃ (Y ⟶ Spec A)` given by composition with `Spec.map φ`. Its inverse lifts a morphism
`Y ⟶ Spec A` to `Spec B`. -/
noncomputable def homSpecEquiv [IsPRadical φ.hom p] (hA : (p : A) = 0) :
    (Y ⟶ Spec B) ≃ (Y ⟶ Spec A) :=
  .ofBijective _ (bijective_comp_SpecMap φ Y hA)

@[simp]
theorem homSpecEquiv_apply [IsPRadical φ.hom p] (hA : (p : A) = 0) (f : Y ⟶ Spec B) :
    homSpecEquiv φ Y hA f = f ≫ Spec.map φ :=
  (rfl)

/-- The lift of a morphism `g : Y ⟶ Spec A` along `Spec.map φ` composes with `Spec.map φ` to
`g`. -/
@[reassoc (attr := simp)]
theorem homSpecEquiv_symm_comp [IsPRadical φ.hom p] (hA : (p : A) = 0) (g : Y ⟶ Spec A) :
    (homSpecEquiv φ Y hA).symm g ≫ Spec.map φ = g :=
  (homSpecEquiv φ Y hA).apply_symm_apply g

end AlgebraicGeometry.Scheme.IsPerfect

/-! ### Checks -/

namespace AlgebraicGeometry.Scheme

open TauCeti.AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime]

/-- The perfection `Spec 𝔽_p[t^{1/p^∞}] ⟶ 𝔸¹_{𝔽_p}` of the affine line is a universal
homeomorphism. -/
example : IsUniversalHomeomorphism
    (Spec.map (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p))) :=
  inferInstance

/-- The perfection of the affine line is not an isomorphism, since `𝔸¹_{𝔽_p}` is not perfect. -/
example : ¬ IsIso (Spec.map (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p))) := fun _ ↦
  not_isPerfect_Spec_polynomial (p := p) (ZMod p)
    (IsPerfect.of_etale (inv (Spec.map (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p)))))

/-- Every morphism from a perfect scheme to the affine line `𝔸¹_{𝔽_p}` lifts uniquely to its
perfection. -/
example (Y : Scheme.{0}) [IsPerfect Y p] :
    Function.Bijective fun f : Y ⟶ Spec (.of (PerfectClosure (ZMod p)[X] p)) ↦
      f ≫ Spec.map (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p)) :=
  have : IsPRadical (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p)).hom p :=
    PerfectClosure.isPRadical _ p
  IsPerfect.bijective_comp_SpecMap _ Y (CharP.cast_eq_zero _ p)

end AlgebraicGeometry.Scheme
