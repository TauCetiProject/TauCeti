/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic

/-!
# The Riemann–Roch theorem for a proper curve

Let `X` be a proper integral curve over a field `k` whose codimension-one local rings are
discrete valuation rings, with a `k`-rational point and with `H¹(X, 𝒪_X)` finite-dimensional.
For every Weil divisor `D` on `X`,

`χ(𝒪_X(D)) = dim_k H⁰(X, 𝒪_X(D)) - dim_k H¹(X, 𝒪_X(D)) = deg D + 1 - g`,

where `deg D = Σ_y D(y) [κ(y) : k]` is `SchemeWeilDivisor.relativeDegree (X ↘ Spec k)` and
`g = dim_k H¹(X, 𝒪_X)` is the genus. This is the combination of `χ(𝒪_X(D)) = deg D + χ(𝒪_X)`
with `χ(𝒪_X) = 1 - g`, the latter being where the rational point enters: it forces the global
functions to be the constants.

Two consequences are recorded. The first is Riemann's inequality `deg D + 1 - g ≤ dim_k H⁰(𝒪_X(D))`,
obtained by discarding `H¹`. The second is that a divisor of negative degree has no nonzero global
sections, so that its `H¹` has dimension exactly `g - 1 - deg D`: a nonzero global section of
`𝒪_X(D)` is a rational function `f` with `div f + D ≥ 0`, and the degree of that effective divisor
is `deg D`, because degree is a linear-equivalence invariant.

That invariance is itself proved here, together with the vanishing of the degree of a principal
divisor. Linearly equivalent divisors have isomorphic sheaves, hence equal Euler characteristics,
hence equal degrees; this is the scheme-theoretic counterpart of the product formula for a
function field, and it is what makes the degree descend to the divisor class group.

## Main declarations

* `SchemeWeilDivisor.relativeDegree_eq_of_linearlyEquivalent` and
  `SchemeWeilDivisor.relativeDegree_principalDivisor`: the degree is a linear-equivalence
  invariant, and a principal divisor has degree zero;
  `SchemeWeilDivisor.isWeightedDegreeZero_residueDegree` restates the latter in the form the
  abstract degree-zero divisor class group asks for;
* `SchemeWeilDivisor.eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus` and
  `SchemeWeilDivisor.finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf`: the
  Riemann–Roch theorem, for the Euler characteristic and in terms of the two dimensions;
* `InvertibleSheaf.eulerCharBelow_eq_relativeDegree_add_one_sub_genus`: Riemann–Roch for a line
  bundle presented as `𝒪_X(D)`;
* `SchemeWeilDivisor.relativeDegree_add_one_sub_genus_le_finrank_cohomology_zero_sheaf`:
  Riemann's inequality;
* `SchemeWeilDivisor.sections_top_eq_bot_of_relativeDegree_neg`,
  `SchemeWeilDivisor.finrank_cohomology_zero_sheaf_eq_zero_of_relativeDegree_neg` and
  `SchemeWeilDivisor.finrank_cohomology_one_sheaf_eq_of_relativeDegree_neg`: a divisor of
  negative degree has no global sections, and the resulting value of `dim H¹`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Theorem 1.3 and Corollary 1.3.2.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Chapter 7, Theorem 3.17.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

section Degree

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **The degree is a linear-equivalence invariant.** On a proper integral curve over `k` whose
codimension-one local rings are discrete valuation rings, with `H¹(X, 𝒪_X)` finite-dimensional,
linearly equivalent Weil divisors have the same degree: their sheaves are isomorphic, so their
Euler characteristics agree. -/
theorem relativeDegree_eq_of_linearlyEquivalent (hX : ∀ y : X, coheight y ≤ 1)
    {D E : SchemeWeilDivisor X}
    (h : (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E) :
    relativeDegree (X ↘ Spec (.of k)) D = relativeDegree (X ↘ Spec (.of k)) E := by
  have hχ : Scheme.Modules.eulerCharBelow k X (sheaf D) 2 =
      Scheme.Modules.eulerCharBelow k X (sheaf E) 2 :=
    Scheme.Modules.eulerCharBelow_congr k (nonempty_iso_sheaf_of_linearlyEquivalent h).some 2
  rw [eulerCharBelow_sheaf_eq_relativeDegree_add k hX D,
    eulerCharBelow_sheaf_eq_relativeDegree_add k hX E] at hχ
  exact add_right_cancel hχ

/-- **A principal divisor has degree zero.** On a proper integral curve over `k` whose
codimension-one local rings are discrete valuation rings, with `H¹(X, 𝒪_X)` finite-dimensional,
the divisor of a nonzero rational function has degree zero. -/
theorem relativeDegree_principalDivisor (hX : ∀ y : X, coheight y ≤ 1)
    (f : Additive X.functionFieldˣ) :
    relativeDegree (X ↘ Spec (.of k))
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor f) = 0 := by
  have h := relativeDegree_eq_of_linearlyEquivalent k hX
    (D := (WeilDivisor.OrderSystem.ofScheme X).principalDivisor f) (E := 0)
    (by simpa using WeilDivisor.OrderSystem.linearlyEquivalent_add_principalDivisor _ 0 f)
  rwa [map_zero] at h

/-- **The residue-degree weights kill principal divisors.** This is
`SchemeWeilDivisor.relativeDegree_principalDivisor` in the form consumed by the abstract
degree-zero divisor class group `WeilDivisor.OrderSystem.picZero`. -/
theorem isWeightedDegreeZero_residueDegree (hX : ∀ y : X, coheight y ≤ 1) :
    (WeilDivisor.OrderSystem.ofScheme X).IsWeightedDegreeZero
      fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ) := fun f ↦ by
  rw [← relativeDegree_def]
  exact relativeDegree_principalDivisor k hX f

end Degree

section Curve

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  (hX : ∀ y : X, coheight y ≤ 1) {s : Spec (.of k) ⟶ X}
  (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))

include hX

/-- **A divisor of negative degree has no nonzero global sections.** On a proper integral curve
over a field `k` whose codimension-one local rings are discrete valuation rings, with
`H¹(X, 𝒪_X)` finite-dimensional, the Riemann–Roch space `Γ(X, 𝒪_X(D))` of a divisor of negative
degree is zero. -/
theorem sections_top_eq_bot_of_relativeDegree_neg {D : SchemeWeilDivisor X}
    (hD : relativeDegree (X ↘ Spec (.of k)) D < 0) :
    sections D ⊤ = ⊥ := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  have : IsNoetherian X := {}
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  refine (Submodule.eq_bot_iff _).mpr fun s hs ↦ ?_
  by_contra hs0
  have hc0 : Scheme.rationalFunctionsEquiv (⊤ : X.Opens) s ≠ 0 := fun h ↦
    hs0 ((Scheme.rationalFunctionsEquiv (⊤ : X.Opens)).map_eq_zero_iff.mp h)
  have hord := (mem_sections_iff.mp hs).resolve_left hc0
  -- `div f + D` is effective, so it has nonnegative degree, while its degree is `deg D`.
  obtain ⟨f, hordf⟩ : ∃ f : Additive X.functionFieldˣ, ∀ y : CodimensionOnePoint X,
      orderAt y f = X.ord (Scheme.rationalFunctionsEquiv (⊤ : X.Opens) s) (y : X) :=
    ⟨Additive.ofMul (Units.mk0 _ hc0), fun y ↦ by
      rw [orderAt_apply, toMul_ofMul, Units.val_mk0]⟩
  have heff : WeilDivisor.IsEffective
      ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor f + D) :=
    (WeilDivisor.isEffective_iff _).mpr fun y ↦ by
      have hy := hord y trivial
      rw [WeilDivisor.coeff_add, WeilDivisor.OrderSystem.coeff_principalDivisor,
        WeilDivisor.OrderSystem.ofScheme_ord, hordf y]
      omega
  have hnonneg := relativeDegree_nonneg (X ↘ Spec (.of k)) heff
  rw [map_add, relativeDegree_principalDivisor k hX f, zero_add] at hnonneg
  omega

include hs

/-- **The Riemann–Roch theorem.** On a proper integral curve over a field `k` whose
codimension-one local rings are discrete valuation rings, with a `k`-rational point and with
`H¹(X, 𝒪_X)` finite-dimensional, every Weil divisor `D` satisfies

`χ(𝒪_X(D)) = deg D + 1 - g`,

where `χ(M) = dim H⁰(X, M) - dim H¹(X, M)`, `deg D = Σ_y D(y) [κ(y) : k]` and `g` is the
genus. -/
theorem eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus (D : SchemeWeilDivisor X) :
    Scheme.Modules.eulerCharBelow k X (sheaf D) 2 =
      relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k := by
  rw [eulerCharBelow_sheaf_eq_relativeDegree_add k hX D,
    eulerCharBelow_trivial_eq_one_sub_genus k hs]
  ring

/-- **The Riemann–Roch theorem, in terms of the two cohomology dimensions.** On a proper integral
curve over a field `k` whose codimension-one local rings are discrete valuation rings, with a
`k`-rational point and with `H¹(X, 𝒪_X)` finite-dimensional,

`dim_k H⁰(X, 𝒪_X(D)) - dim_k H¹(X, 𝒪_X(D)) = deg D + 1 - g`. -/
theorem finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf (D : SchemeWeilDivisor X) :
    (finrank k (Scheme.Modules.Cohomology (sheaf D) 0) : ℤ) -
        (finrank k (Scheme.Modules.Cohomology (sheaf D) 1) : ℤ) =
      relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k := by
  rw [← Scheme.Modules.eulerCharBelow_two,
    eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus k hX hs D]

/-- **Riemann's inequality.** On a proper integral curve over a field `k` whose codimension-one
local rings are discrete valuation rings, with a `k`-rational point and with `H¹(X, 𝒪_X)`
finite-dimensional, `dim_k H⁰(X, 𝒪_X(D)) ≥ deg D + 1 - g`. -/
theorem relativeDegree_add_one_sub_genus_le_finrank_cohomology_zero_sheaf
    (D : SchemeWeilDivisor X) :
    relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k ≤
      (finrank k (Scheme.Modules.Cohomology (sheaf D) 0) : ℤ) := by
  have h := finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf k hX hs D
  have := Int.natCast_nonneg (finrank k (Scheme.Modules.Cohomology (sheaf D) 1))
  omega

omit hs in
/-- On a proper integral curve over a field `k` whose codimension-one local rings are discrete
valuation rings, with `H¹(X, 𝒪_X)` finite-dimensional, `H⁰(X, 𝒪_X(D))` vanishes for a divisor
`D` of negative degree. -/
theorem finrank_cohomology_zero_sheaf_eq_zero_of_relativeDegree_neg {D : SchemeWeilDivisor X}
    (hD : relativeDegree (X ↘ Spec (.of k)) D < 0) :
    finrank k (Scheme.Modules.Cohomology (sheaf D) 0) = 0 := by
  have hbot := sections_top_eq_bot_of_relativeDegree_neg k hX hD
  -- `Γ(X, 𝒪_X(D))` injects into `𝒦_X` with image `sections D ⊤`, so it too is zero.
  have : Subsingleton Γ(sheaf D, ⊤) := by
    refine ⟨fun a b ↦ sheafι_app_injective D ⊤ ?_⟩
    have ha := sheafι_app_mem D ⊤ a
    have hb := sheafι_app_mem D ⊤ b
    rw [hbot, Submodule.mem_bot] at ha hb
    rw [ha, hb]
  rw [Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections,
    Module.finrank_zero_of_subsingleton]

/-- On a proper integral curve over a field `k` whose codimension-one local rings are discrete
valuation rings, with a `k`-rational point and with `H¹(X, 𝒪_X)` finite-dimensional, a divisor of
negative degree has `dim_k H¹(X, 𝒪_X(D)) = g - 1 - deg D`. -/
theorem finrank_cohomology_one_sheaf_eq_of_relativeDegree_neg {D : SchemeWeilDivisor X}
    (hD : relativeDegree (X ↘ Spec (.of k)) D < 0) :
    (finrank k (Scheme.Modules.Cohomology (sheaf D) 1) : ℤ) =
      X.genus k - 1 - relativeDegree (X ↘ Spec (.of k)) D := by
  have h := finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf k hX hs D
  rw [finrank_cohomology_zero_sheaf_eq_zero_of_relativeDegree_neg k hX hD] at h
  omega

end Curve

end SchemeWeilDivisor

namespace InvertibleSheaf

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **The Riemann–Roch theorem for a line bundle.** On a proper integral curve over a field `k`
whose codimension-one local rings are discrete valuation rings, with a `k`-rational point and with
`H¹(X, 𝒪_X)` finite-dimensional, a line bundle `L ≅ 𝒪_X(D)` satisfies
`χ(L) = deg D + 1 - g`. -/
theorem eulerCharBelow_eq_relativeDegree_add_one_sub_genus (hX : ∀ y : X, coheight y ≤ 1)
    {s : Spec (.of k) ⟶ X} (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    {L : InvertibleSheaf X} {D : SchemeWeilDivisor X} (e : L.obj ≅ SchemeWeilDivisor.sheaf D) :
    Scheme.Modules.eulerCharBelow k X L.obj 2 =
      SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k := by
  rw [Scheme.Modules.eulerCharBelow_congr k e,
    SchemeWeilDivisor.eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus k hX hs D]

end InvertibleSheaf

end AlgebraicGeometry

end TauCeti
