/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic

/-!
# The Riemann–Roch theorem for divisors on a proper curve

For a proper integral curve `X` over a field `k` with a `k`-rational point, whose
codimension-one local rings are discrete valuation rings, and with `H¹(X, 𝒪_X)` of finite
dimension over `k`, this file proves

`χ(𝒪_X(D)) = deg D + 1 - g`,

where `g = dim_k H¹(X, 𝒪_X)` is the genus, `deg D = Σ_y D(y) [κ(y) : k]` is the
residue-degree-weighted degree of a Weil divisor, and
`χ(M) = dim_k H⁰(X, M) - dim_k H¹(X, M)`.

The two inputs are already available: `χ(𝒪_X(D)) = deg D + χ(𝒪_X)`, from the residue sequence of
a divisor sheaf, and `χ(𝒪_X) = 1 - g`, from the fact that a `k`-rational point on a proper
integral scheme forces the global functions to be the constants. This file also records the
normalization identity `χ(L) = eulerDegree(L) + 1 - g`. It is not itself a Riemann–Roch theorem:
`eulerDegree(L)` is defined as `χ(L) - χ(𝒪_X)`. The substantive divisor theorem uses the
independently defined residue-degree sum; the earlier theorem
`InvertibleSheaf.eulerDegree_eq_relativeDegree` identifies the two degrees when `L ≅ 𝒪_X(D)`.

Dropping the nonnegative `dim_k H¹` gives **Riemann's inequality** `ℓ(D) ≥ deg D + 1 - g` for the
Riemann–Roch space `ℓ(D) = dim_k Γ(X, 𝒪_X(D))`. Together with the dictionary between nonzero
global sections of `𝒪_X(D)` and effective divisors in the class of `D`
(`SchemeWeilDivisor.nonempty_completeLinearSystem_iff_nontrivial_globalSections_sheaf`), it shows
that a divisor of degree at least the genus is linearly equivalent to an effective divisor.

The missing half of the classical statement is Serre duality, which identifies `dim_k H¹(L)` with
`dim_k Γ(X, ω_X ⊗ L⁻¹)`; the dualizing sheaf is not constructed here.

A Riemann–Roch theorem for the divisors of an abstract function field, proved by the
valuation-theoretic route with the genus defined as `sup_D (deg D - ℓ(D)) + 1`, lives in
`TauCeti/FieldTheory/FunctionField/RiemannRoch/`; it is a statement about a different object
(`TauCeti.Divisor`, the free group on the places of a function field), and no comparison with the
cohomological genus used here is available yet.

## Main declarations

* `InvertibleSheaf.eulerCharBelow_eq_eulerDegree_add_one_sub_genus` and
  `InvertibleSheaf.finrank_cohomology_zero_sub_one_eq_eulerDegree_add_one_sub_genus`:
  normalization identities for Euler-characteristic degree;
* `SchemeWeilDivisor.eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus` and
  `SchemeWeilDivisor.finrank_cohomology_zero_sub_one_sheaf_eq_relativeDegree_add_one_sub_genus`:
  Riemann–Roch for the sheaf of a Weil divisor on a proper curve;
* `SchemeWeilDivisor.relativeDegree_add_one_sub_genus_le_finrank_globalSections_sheaf`:
  Riemann's inequality;
* `SchemeWeilDivisor.nonempty_completeLinearSystem_iff_nontrivial_globalSections_sheaf`: the
  complete linear system `|D|` is nonempty exactly when `𝒪_X(D)` has a nonzero global section;
* `SchemeWeilDivisor.nonempty_completeLinearSystem_of_genus_le_relativeDegree`: a divisor of
  degree at least the genus is linearly equivalent to an effective divisor.

## References

* R. Hartshorne, *Algebraic Geometry*, IV, Theorem 1.3 (Riemann–Roch).
* W. Fulton, *Algebraic Curves*, Chapter 8, Section 3 (Riemann's theorem and its consequences
  for complete linear systems).
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace InvertibleSheaf

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [UniversallyClosed (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (trivial X).obj 1)]
  {s : Spec (.of k) ⟶ X} (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))

include hs

/-- **The Euler-degree normalization identity.** On an integral scheme universally closed over a
field `k` with a `k`-rational point and with `H¹(X, 𝒪_X)` finite-dimensional,

`χ(L) = deg L + 1 - g`

for every line bundle `L`, where `deg L = χ(L) - χ(𝒪_X)` is the Euler-characteristic degree and
`g = dim_k H¹(X, 𝒪_X)` is the genus. This is a normalization identity, not by itself a
Riemann–Roch theorem. On a proper curve `InvertibleSheaf.eulerDegree_eq_relativeDegree` identifies
the degree on the right with the independently defined degree of any Weil divisor of `L`. -/
theorem eulerCharBelow_eq_eulerDegree_add_one_sub_genus (L : InvertibleSheaf X) :
    Scheme.Modules.eulerCharBelow k X L.obj 2 = L.eulerDegree k + 1 - X.genus k := by
  rw [eulerDegree_def, eulerCharBelow_trivial_eq_one_sub_genus k hs]
  ring

/-- The Euler-degree normalization identity as an equality of dimensions:
`dim H⁰(X, L) - dim H¹(X, L) = deg L + 1 - g`. -/
theorem finrank_cohomology_zero_sub_one_eq_eulerDegree_add_one_sub_genus (L : InvertibleSheaf X) :
    (finrank k (Scheme.Modules.Cohomology L.obj 0) : ℤ) -
        (finrank k (Scheme.Modules.Cohomology L.obj 1) : ℤ) =
      L.eulerDegree k + 1 - X.genus k := by
  rw [← Scheme.Modules.eulerCharBelow_two, eulerCharBelow_eq_eulerDegree_add_one_sub_genus k hs]

end InvertibleSheaf

namespace SchemeWeilDivisor

section LinearSystem

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-- **The complete linear system of `D` is nonempty exactly when `𝒪_X(D)` has a nonzero global
section.** On a Noetherian integral scheme whose codimension-one local rings are discrete
valuation rings, a global section of `𝒪_X(D)` is a rational function `f` with `D + div f ≥ 0`, so
a nonzero one names an effective divisor linearly equivalent to `D`, and conversely. -/
theorem nonempty_completeLinearSystem_iff_nontrivial_globalSections_sheaf
    (D : SchemeWeilDivisor X) :
    ((WeilDivisor.OrderSystem.ofScheme X).completeLinearSystem D).Nonempty ↔
      Nontrivial Γ(sheaf D, ⊤) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  constructor
  · rintro ⟨E, hE⟩
    obtain ⟨hEeff, γ, rfl⟩ :=
      (WeilDivisor.OrderSystem.mem_completeLinearSystem_iff_exists_principalDivisor _).mp hE
    have hbound : ∀ x : CodimensionOnePoint X, (x : X) ∈ (⊤ : X.Opens) →
        -WeilDivisor.coeff D x ≤
          X.ord ((Additive.toMul γ : X.functionFieldˣ) : X.functionField) x := by
      intro x _
      have h := (WeilDivisor.isEffective_iff _).mp hEeff x
      rw [WeilDivisor.coeff_add, WeilDivisor.OrderSystem.coeff_principalDivisor,
        WeilDivisor.OrderSystem.ofScheme_ord, orderAt_apply] at h
      omega
    refine nontrivial_of_ne
      (sectionMk _ (rationalFunctionsEquiv_symm_mem_sections hbound)) 0 fun h ↦ ?_
    have h' := congrArg (Scheme.Modules.Hom.app (sheafι D) ⊤) h
    rw [sheafι_app_sectionMk, map_zero] at h'
    exact Units.ne_zero _
      ((Scheme.rationalFunctionsEquiv (⊤ : X.Opens)).symm.map_eq_zero_iff.mp h')
  · intro _
    obtain ⟨t, ht⟩ := exists_ne (0 : Γ(sheaf D, ⊤))
    set c := Scheme.rationalFunctionsEquiv (⊤ : X.Opens)
      (Scheme.Modules.Hom.app (sheafι D) ⊤ t) with hc'
    have hc : c ≠ 0 := fun h0 ↦ ht <| sheafι_app_injective D ⊤ <| by
      rw [map_zero]
      exact (Scheme.rationalFunctionsEquiv (⊤ : X.Opens)).map_eq_zero_iff.mp h0
    have hbound := (mem_sections_iff.mp (sheafι_app_mem D ⊤ t)).resolve_left hc
    refine ⟨D + (WeilDivisor.OrderSystem.ofScheme X).principalDivisor
      (Additive.ofMul (Units.mk0 c hc)), ?_⟩
    refine (WeilDivisor.OrderSystem.mem_completeLinearSystem_iff_exists_principalDivisor _).mpr
      ⟨(WeilDivisor.isEffective_iff _).mpr fun x ↦ ?_, _, rfl⟩
    have h := hbound x trivial
    rw [← hc'] at h
    rw [WeilDivisor.coeff_add, WeilDivisor.OrderSystem.coeff_principalDivisor,
      WeilDivisor.OrderSystem.ofScheme_ord, orderAt_apply, toMul_ofMul, Units.val_mk0]
    omega

end LinearSystem

section Curve

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  (hX : ∀ y : X, coheight y ≤ 1)
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  {s : Spec (.of k) ⟶ X} (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))

include hX hs

/-- **Riemann–Roch on a proper curve.** Let `X` be a proper integral curve over a field `k` whose
codimension-one local rings are discrete valuation rings, with a `k`-rational point and with
`H¹(X, 𝒪_X)` finite-dimensional over `k`. Then

`χ(𝒪_X(D)) = Σ_y D(y) [κ(y) : k] + 1 - g`

for every Weil divisor `D`, where `g = dim_k H¹(X, 𝒪_X)` is the genus and
`χ(M) = dim_k H⁰(X, M) - dim_k H¹(X, M)`. -/
theorem eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus (D : SchemeWeilDivisor X) :
    Scheme.Modules.eulerCharBelow k X (sheaf D) 2 =
      relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k := by
  rw [eulerCharBelow_sheaf_eq_relativeDegree_add k hX D,
    eulerCharBelow_trivial_eq_one_sub_genus k hs]
  ring

/-- **Riemann–Roch on a proper curve**, as an equality of dimensions:
`ℓ(D) - dim H¹(X, 𝒪_X(D)) = deg D + 1 - g`, where `ℓ(D) = dim_k Γ(X, 𝒪_X(D))` is the dimension
of the Riemann–Roch space. -/
theorem finrank_cohomology_zero_sub_one_sheaf_eq_relativeDegree_add_one_sub_genus
    (D : SchemeWeilDivisor X) :
    (finrank k Γ(sheaf D, ⊤) : ℤ) -
        (finrank k (Scheme.Modules.Cohomology (sheaf D) 1) : ℤ) =
      relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k := by
  rw [← Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections,
    ← Scheme.Modules.eulerCharBelow_two,
    eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus k hX hs D]

/-- **Riemann's inequality.** On a proper curve as above, the Riemann–Roch space of `D` has
dimension at least `deg D + 1 - g`: Riemann–Roch with the nonnegative term `dim H¹(X, 𝒪_X(D))`
dropped. -/
theorem relativeDegree_add_one_sub_genus_le_finrank_globalSections_sheaf
    (D : SchemeWeilDivisor X) :
    relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k ≤ (finrank k Γ(sheaf D, ⊤) : ℤ) := by
  have h := finrank_cohomology_zero_sub_one_sheaf_eq_relativeDegree_add_one_sub_genus k hX hs D
  have h₁ : (0 : ℤ) ≤ (finrank k (Scheme.Modules.Cohomology (sheaf D) 1) : ℤ) :=
    Int.natCast_nonneg _
  omega

end Curve

section CompleteLinearSystem

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  (hX : ∀ y : X, coheight y ≤ 1)
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  {s : Spec (.of k) ⟶ X} (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))

include hX hs

/-- **A divisor of degree at least the genus is linearly equivalent to an effective divisor.**
Riemann's inequality makes the Riemann–Roch space of such a divisor nonzero, and a nonzero global
section of `𝒪_X(D)` names an effective divisor in the class of `D`. The scheme is asked to be
Noetherian, rather than only locally so, because that is what carries the orders of vanishing of
rational functions into an order system, hence what makes the complete linear system available. -/
theorem nonempty_completeLinearSystem_of_genus_le_relativeDegree {D : SchemeWeilDivisor X}
    (hD : (X.genus k : ℤ) ≤ relativeDegree (X ↘ Spec (.of k)) D) :
    ((WeilDivisor.OrderSystem.ofScheme X).completeLinearSystem D).Nonempty := by
  have := finiteDimensional_globalSections_sheaf k hX D
  rw [nonempty_completeLinearSystem_iff_nontrivial_globalSections_sheaf,
    ← Module.finrank_pos_iff_of_free (R := k)]
  have h := relativeDegree_add_one_sub_genus_le_finrank_globalSections_sheaf k hX hs D
  omega

end CompleteLinearSystem

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
