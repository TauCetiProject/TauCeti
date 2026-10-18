/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Relative
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Mathlib.Algebra.CharP.Reduced

/-!
# Geometric properties of scheme Frobenius

Absolute and relative Frobenius are integral, universally injective and surjective for arbitrary
schemes in characteristic `p`. Consequently every base change of either map is a homeomorphism.
These results apply to nonreduced schemes and to the empty scheme; neither finite type nor
perfectness of the base is required. They provide the geometric input to perfection and
topological invariance of the small étale site.

The constructions and base-change squares are those of
`TauCeti.AlgebraicGeometry.Frobenius.Relative`. Universal homeomorphism is expressed using
Mathlib's universal closure of the topological homeomorphism property.

## References

* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), Frobenii.
* The Stacks Project, [Tag 01S4](https://stacks.math.columbia.edu/tag/01S4), the field-valued
  criterion for universal injectivity.
-/

public section

open CategoryTheory Limits Polynomial AlgebraicGeometry

namespace TauCeti

universe u

variable {X S : _root_.AlgebraicGeometry.Scheme.{u}} {p : ℕ} [hp : Fact p.Prime]

/-- Absolute Frobenius is affine: it fixes every open, including every affine open. -/
instance _root_.AlgebraicGeometry.Scheme.isAffineHom_frobenius
    (hX : (p : Γ(X, ⊤)) = 0) : IsAffineHom (X.frobenius p hX) where
  isAffine_preimage U hU := by
    simpa only [Scheme.frobenius_preimage] using hU

/-- Absolute Frobenius is integral, without any finiteness or reducedness hypothesis. -/
instance _root_.AlgebraicGeometry.Scheme.isIntegralHom_frobenius
    (hX : (p : Γ(X, ⊤)) = 0) : IsIntegralHom (X.frobenius p hX) where
  isIntegral_app U _ := by
    rw [Scheme.Hom.app_eq_appLE]
    apply ((X.frobenius p hX).appLE_congr le_rfl rfl
      (Scheme.frobenius_preimage hX U) (fun {_ _} f ↦ f.hom.IsIntegral)).mpr
    intro r
    refine ⟨Polynomial.X ^ p - Polynomial.C r, monic_X_pow_sub_C _ hp.out.ne_zero, ?_⟩
    simp [Scheme.frobenius_appLE_apply]

/-- Absolute Frobenius is surjective on points, including when the scheme is empty. -/
instance _root_.AlgebraicGeometry.Scheme.surjective_frobenius
    (hX : (p : Γ(X, ⊤)) = 0) : Surjective (X.frobenius p hX) :=
  ⟨fun x ↦ ⟨x, Scheme.frobenius_apply hX x⟩⟩

/-- Absolute Frobenius is universally injective, not just injective on its own points. -/
instance _root_.AlgebraicGeometry.Scheme.universallyInjective_frobenius
    (hX : (p : Γ(X, ⊤)) = 0) : UniversallyInjective (X.frobenius p hX) := by
  apply ((tfae_universallyInjective (X.frobenius p hX)).out 2 1).mp
  intro K _ g₁ g₂ h
  have hK : (p : K) = 0 := by
    have hz := Scheme.natCast_eq_zero_of_hom g₁ hX
    simpa using congr((Scheme.ΓSpecIso (.of K)).hom $hz)
  let : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hK
  have hbase : g₁.base = g₂.base := by
    simpa only [Scheme.Hom.comp_base, Scheme.frobenius_base, Category.comp_id] using
      congrArg (fun f : Spec (.of K) ⟶ X ↦ f.base) h
  have hpoint : g₁ (IsLocalRing.closedPoint K) = g₂ (IsLocalRing.closedPoint K) :=
    ConcreteCategory.congr_hom hbase _
  let U := (X.affineCover.f (X.affineCover.idx (g₁ (IsLocalRing.closedPoint K)))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have h₁ : g₁ ⁻¹ᵁ U = ⊤ := by
    apply top_unique
    intro x _
    have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst x
    exact X.affineCover.covers _
  have h₂ : g₂ ⁻¹ᵁ U = ⊤ := by
    apply top_unique
    intro x _
    have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst x
    apply (Scheme.Hom.mem_preimage g₂).mpr
    exact hpoint ▸ X.affineCover.covers _
  apply eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (frobenius K p)) (frobenius_inj K p) U hU h₁ h₂
  rw [← TauCeti.powRingHom_eq_frobenius hK, Scheme.Spec_map_powRingHom (.of K) hK,
    Scheme.frobenius_naturality _ hX g₁, Scheme.frobenius_naturality _ hX g₂]
  exact h

/-- Absolute Frobenius remains a homeomorphism after every base change. -/
instance _root_.AlgebraicGeometry.Scheme.isUniversalHomeomorphism_frobenius
    (hX : (p : Γ(X, ⊤)) = 0) : AlgebraicGeometry.IsUniversalHomeomorphism (X.frobenius p hX) :=
  (Scheme.Hom.isUniversalHomeomorphism_iff_universallyClosed _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

variable (π : X ⟶ S) (hS : (p : Γ(S, ⊤)) = 0)

/-- Relative Frobenius is integral over an arbitrary characteristic-`p` base. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isIntegralHom_relativeFrobenius :
    IsIntegralHom (π.relativeFrobenius p hS) := by
  have : IsIntegralHom (π.relativeFrobenius p hS ≫ pullback.fst _ _) := by
    rw [Scheme.Hom.relativeFrobenius_fst]
    infer_instance
  exact IsIntegralHom.of_comp (π.relativeFrobenius p hS) (pullback.fst _ _)

/-- Relative Frobenius is universally injective over an arbitrary characteristic-`p` base. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.universallyInjective_relativeFrobenius :
    UniversallyInjective (π.relativeFrobenius p hS) := by
  apply ((tfae_universallyInjective (π.relativeFrobenius p hS)).out 2 1).mp
  intro K _ g₁ g₂ h
  have hF : UniversallyInjective (X.frobenius p (Scheme.natCast_eq_zero_of_hom π hS)) :=
    inferInstance
  have hfield : ∀ (L : Type u) [Field L], Function.Injective
      (fun g : Spec (.of L) ⟶ X ↦
        g ≫ X.frobenius p (Scheme.natCast_eq_zero_of_hom π hS)) :=
    ((tfae_universallyInjective _).out 1 2).mp hF
  apply hfield K
  simpa only [Category.assoc, Scheme.Hom.relativeFrobenius_fst] using
    congrArg (· ≫ pullback.fst π (S.frobenius p hS)) h

/-- Relative Frobenius is surjective; its underlying point map need not be an identity map
because its source and target are different schemes. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.surjective_relativeFrobenius :
    Surjective (π.relativeFrobenius p hS) := by
  constructor
  intro y
  refine ⟨pullback.fst π (S.frobenius p hS) y,
    (pullback.fst π (S.frobenius p hS)).injective ?_⟩
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.relativeFrobenius_fst, Scheme.frobenius_apply]

/-- Relative Frobenius remains a homeomorphism after every base change, with no flatness or
perfectness hypothesis on the base. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isUniversalHomeomorphism_relativeFrobenius :
    AlgebraicGeometry.IsUniversalHomeomorphism (π.relativeFrobenius p hS) :=
  (Scheme.Hom.isUniversalHomeomorphism_iff_universallyClosed _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

end TauCeti
