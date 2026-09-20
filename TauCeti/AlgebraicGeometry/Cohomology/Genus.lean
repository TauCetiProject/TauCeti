/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# The genus and the Euler characteristic of the structure sheaf

For a scheme `X` over a field `k` with finite-dimensional `H¹(X, 𝒪_X)`, the genus is
`g = dim_k H¹(X, 𝒪_X)`. For a smooth proper curve this is the usual genus.

The constant term `1` of that formula is `dim_k H⁰(X, 𝒪_X)`. This file proves that it is `1` on
an integral scheme that is universally closed (for instance proper) over `k` and has a `k`-rational
point: the global functions are then the constants (`appTop_bijective_of_section`). Consequently
the Euler characteristic of the structure sheaf is `χ(𝒪_X) = 1 - g`.

As in `TauCeti.AlgebraicGeometry.LineBundle.Degree`, the structure sheaf is written as the trivial
line bundle `(InvertibleSheaf.trivial X).obj`, and Euler characteristics are the degree-`2`
truncations `Scheme.Modules.eulerCharBelow k X M 2 = dim H⁰(X, M) - dim H¹(X, M)`. These are the
Euler characteristics of a curve once cohomology above degree one is known to vanish. This file
requires finite-dimensionality of `H¹(X, 𝒪_X)` when defining the genus; proving that finiteness for
proper schemes is a separate prerequisite.

## Main declarations

* `AlgebraicGeometry.Scheme.genus k X`, the genus `dim_k H¹(X, 𝒪_X)` of a scheme, and its
  defining formula `AlgebraicGeometry.Scheme.genus_def`;
* `TauCeti.AlgebraicGeometry.finrank_cohomology_zero_trivial_eq_one`: `dim_k H⁰(X, 𝒪_X) = 1`
  for an integral scheme, universally closed over `k`, with a `k`-rational point;
* `TauCeti.AlgebraicGeometry.eulerCharBelow_trivial_eq_one_sub_genus`: for an integral scheme
  universally closed over `k` with a `k`-rational point, `χ(𝒪_X) = 1 - g`.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.5.3 (the arithmetic genus).
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §3.
-/

public section

open AlgebraicGeometry CategoryTheory
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

variable (k : Type u) [Field k]

/-- The genus `dim_k H¹(X, 𝒪_X)` of a scheme `X` over a field `k`, assuming this cohomology
group is finite-dimensional. The finite-dimensionality instance `_fd` does not occur in the value
— it guards the definition, so that `finrank` is never read as a genus `0` coming from its junk
value on an infinite-dimensional space. -/
def _root_.AlgebraicGeometry.Scheme.genus (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [_fd : FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)] :
    ℕ :=
  finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)

/-- The genus is the dimension of the first cohomology of the structure sheaf. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.genus_def (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)] :
    X.genus k = finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) :=
  Scheme.genus.eq_def k X

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
  let _ : Module k Γ(X, ⊤) := Scheme.Modules.globalSectionsBaseModule k X M
  let e : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
    LinearEquiv.refl Γ(X, ⊤) Γ(X, ⊤)
  let v : Γ(M, ⊤) := e.symm 1
  have hv : v ≠ 0 := by
    intro hv
    apply one_ne_zero (α := Γ(X, ⊤))
    calc
      1 = e v := by simp [v]
      _ = e 0 := congrArg e hv
      _ = 0 := e.map_zero
  refine (finrank_eq_one_iff_of_nonzero' v hv).mpr fun w ↦ ?_
  obtain ⟨c, hc⟩ := hφ (e w)
  refine ⟨c, ?_⟩
  apply e.injective
  rw [Scheme.Modules.base_smul_globalSections]
  rw [e.map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    Scheme.Modules.baseRingToGlobalSections k X c = e w := hc

/-- **The Euler characteristic of the structure sheaf.** On an integral scheme universally closed
over a field `k` with a `k`-rational point, `χ(𝒪_X) = 1 - g`, where `χ` is the degree-`2`
truncation `dim H⁰ - dim H¹` and `g` is the genus. -/
theorem eulerCharBelow_trivial_eq_one_sub_genus [IsIntegral X]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    [UniversallyClosed (X ↘ Spec (.of k))]
    {s : Spec (.of k) ⟶ X}
    (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k))) :
    Scheme.Modules.eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 = 1 - X.genus k := by
  rw [Scheme.Modules.eulerCharBelow_two, finrank_cohomology_zero_trivial_eq_one k hs,
    Scheme.genus_def, Nat.cast_one]

end

end AlgebraicGeometry

end TauCeti
