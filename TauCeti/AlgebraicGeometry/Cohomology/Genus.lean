/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# The genus and the Euler characteristic of the structure sheaf

For a scheme `X` over a field `k`, the genus is `g = dim_k H¹(X, 𝒪_X)`. For a smooth proper
geometrically connected curve this is the usual genus, and in general it is the invariant that
appears in Riemann–Roch, `χ(L) = deg L + 1 - g`.

The constant term `1` of that formula is `dim_k H⁰(X, 𝒪_X)`. This file proves that it is `1` on
an integral scheme that is universally closed (for instance proper) over `k` and has a `k`-rational
point: the global functions are then the constants (`appTop_bijective_of_section`). Consequently
the Euler characteristic of the structure sheaf is `χ(𝒪_X) = 1 - g`, and the Euler-characteristic
degree `InvertibleSheaf.eulerDegree` of a line bundle `L` satisfies `χ(L) = deg L + 1 - g`.

As in `TauCeti.AlgebraicGeometry.LineBundle.Degree`, the structure sheaf is written as the trivial
line bundle `(InvertibleSheaf.trivial X).obj`, and Euler characteristics are the degree-`2`
truncations `Scheme.Modules.eulerCharBelow k X M 2 = dim H⁰(X, M) - dim H¹(X, M)`. These are the
Euler characteristics of a curve once `H¹` is known to be finite-dimensional, since cohomology of
line bundles on a curve vanishes above degree one. The genus is defined without any finiteness
hypothesis; when `H¹(X, 𝒪_X)` is infinite-dimensional it takes the junk value `0` of `finrank`.

## Main declarations

* `AlgebraicGeometry.Scheme.genus k X`, the genus `dim_k H¹(X, 𝒪_X)`, and its defining formula
  `AlgebraicGeometry.Scheme.genus_def`;
* `TauCeti.AlgebraicGeometry.finrank_cohomology_zero_trivial_eq_one`: `dim_k H⁰(X, 𝒪_X) = 1`
  for an integral scheme, universally closed over `k`, with a `k`-rational point;
* `TauCeti.AlgebraicGeometry.eulerCharBelow_trivial_eq_one_sub_genus`: under the same hypotheses,
  `χ(𝒪_X) = 1 - g`;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerCharBelow_eq_eulerDegree_add_one_sub_genus`:
  `χ(L) = deg L + 1 - g` for every line bundle `L`, with the Euler-characteristic degree.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.5.3 (the arithmetic genus) and Theorem IV.1.3
  (Riemann–Roch).
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §3 and §4.
-/

public section

open AlgebraicGeometry CategoryTheory
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

variable (k : Type u) [Field k]

/-- The genus `dim_k H¹(X, 𝒪_X)` of a scheme `X` over a field `k`.

For a proper curve over `k` whose global functions are the constants this is the genus of
Riemann–Roch. No finiteness is assumed: if `H¹(X, 𝒪_X)` is infinite-dimensional the genus is the
junk value `0`. -/
def _root_.AlgebraicGeometry.Scheme.genus (X : Scheme.{u}) [X.Over (Spec (.of k))] : ℕ :=
  finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)

/-- The genus is the dimension of the first cohomology of the structure sheaf. -/
lemma _root_.AlgebraicGeometry.Scheme.genus_def (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    X.genus k = finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) :=
  (rfl)

variable {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Only constant global functions.** On an integral scheme that is universally closed over a
field `k` and has a `k`-rational point, `H⁰(X, 𝒪_X)` is one-dimensional over `k`. -/
theorem finrank_cohomology_zero_trivial_eq_one [IsIntegral X]
    [UniversallyClosed (X ↘ Spec (.of k))] {s : Spec (.of k) ⟶ X}
    (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k))) :
    finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0) = 1 := by
  -- The base ring maps onto the global functions, since both factors of
  -- `baseRingToGlobalSections` are bijective.
  have hφ : Function.Surjective (Scheme.Modules.baseRingToGlobalSections k X) := by
    rw [funext (Scheme.Modules.baseRingToGlobalSections_apply k X)]
    exact (appTop_bijective_of_section hs).2.comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective
  -- Pass from the trivial line bundle to the structure sheaf `𝒪_X`, and from `H⁰` to global
  -- sections.
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  rw [InvertibleSheaf.trivial_obj]
  refine (Scheme.Modules.finrank_cohomology_congr (X := X) k
    (TauCeti.SheafOfModules.freePUnitIsoUnit _) 0).trans ?_
  refine (Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections k M).trans ?_
  -- Global sections of the unit sheaf are, by definition, the ring `Γ(X, ⊤)` acting on itself by
  -- multiplication; the ascriptions below use that identification, for which Mathlib records no
  -- lemma. Every global section is then a `k`-multiple of the section `1`.
  let v : Γ(M, ⊤) := (1 : Γ(X, ⊤))
  refine (finrank_eq_one_iff_of_nonzero' v (one_ne_zero (α := Γ(X, ⊤)))).mpr fun w ↦ ?_
  obtain ⟨c, hc⟩ := hφ w
  refine ⟨c, ?_⟩
  rw [Scheme.Modules.base_smul_globalSections]
  exact (mul_one (M := Γ(X, ⊤)) _).trans hc

/-- **The Euler characteristic of the structure sheaf.** On an integral scheme that is universally
closed over a field `k` and has a `k`-rational point, `χ(𝒪_X) = 1 - g`, where `χ` is the
degree-`2` truncation `dim H⁰ - dim H¹` and `g` is the genus. -/
theorem eulerCharBelow_trivial_eq_one_sub_genus [IsIntegral X]
    [UniversallyClosed (X ↘ Spec (.of k))] {s : Spec (.of k) ⟶ X}
    (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k))) :
    Scheme.Modules.eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 = 1 - X.genus k := by
  rw [Scheme.Modules.eulerCharBelow_two, finrank_cohomology_zero_trivial_eq_one k hs,
    Scheme.genus_def, Nat.cast_one]

/-- **Riemann–Roch in Euler-characteristic form.** On an integral scheme that is universally
closed over a field `k` and has a `k`-rational point, every line bundle `L` satisfies
`χ(L) = deg L + 1 - g`, where `deg L = χ(L) - χ(𝒪_X)` is the Euler-characteristic degree and `g`
is the genus. -/
theorem InvertibleSheaf.eulerCharBelow_eq_eulerDegree_add_one_sub_genus [IsIntegral X]
    [UniversallyClosed (X ↘ Spec (.of k))] {s : Spec (.of k) ⟶ X}
    (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k))) (L : InvertibleSheaf X) :
    Scheme.Modules.eulerCharBelow k X L.obj 2 = L.eulerDegree k + 1 - X.genus k := by
  rw [InvertibleSheaf.eulerDegree_def, eulerCharBelow_trivial_eq_one_sub_genus k hs]
  ring

end

end AlgebraicGeometry

end TauCeti
