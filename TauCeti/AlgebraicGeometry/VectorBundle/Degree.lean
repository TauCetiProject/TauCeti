/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
public import TauCeti.AlgebraicGeometry.Curves.Cohomology
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic

/-!
# The degree of a vector bundle on a curve

Let `X` be a scheme over a field `k` and `E` a finite locally free sheaf of constant rank `r` on
`X`. Its degree is

`deg E := χ(X, E) - r · χ(X, 𝒪_X)`,

where `χ(X, M) = dim H⁰(X, M) - dim H¹(X, M)` is the degree-`2` truncation
`Scheme.Modules.eulerCharBelow k X M 2` of the Euler characteristic. On a proper scheme of
dimension at most one over `k` this is the degree of `E` in the sense of the Stacks Project,
Definition 0AYR: by Grothendieck vanishing `H¹` is the top cohomology there, so the truncation is
the full Euler characteristic. As for `InvertibleSheaf.eulerDegree`, no hypothesis is needed to
form the invariant, which takes junk values when the cohomology is infinite-dimensional or does
not vanish above degree one.

The degree is normalised by the trivial bundle and is additive in short exact sequences of
vector bundles (Stacks, Lemma 0AYS). In rank one it is the Euler-characteristic degree of a line
bundle, and hence, on a proper integral curve whose codimension-one local rings are discrete
valuation rings, `deg 𝒪_X(D) = Σ_y D(y) [κ(y) : k]` for a Weil divisor `D` (Stacks, Lemma 0AYY).

## Main declarations

* `FiniteLocallyFreeSheaf.FixedRank.vectorBundleDegree k E`: the degree
  `χ(X, E) - r · χ(X, 𝒪_X)` of a finite locally free sheaf of constant rank `r`;
* `FixedRank.vectorBundleDegree_congr`: the degree is an isomorphism invariant;
* `FixedRank.vectorBundleDegree_free`: the trivial bundle `𝒪_X^r` has degree zero;
* `FixedRank.vectorBundleDegree_eq_eulerDegree_toInvertible` and
  `FixedRank.vectorBundleDegree_toFixedRankOne_obj`: in rank one the degree is
  `InvertibleSheaf.eulerDegree`;
* `FixedRank.vectorBundleDegree_eq_relativeDegree`: the degree of `𝒪_X(D)` is the degree of the
  divisor `D`;
* `FixedRank.vectorBundleDegree_add_of_shortExact`: additivity in a short exact sequence, given
  finite-dimensionality of the cohomology it reads and vanishing of `H²` of the subbundle, and
  `FixedRank.vectorBundleDegree_add_of_shortExact_of_isCurveOver`, where these hypotheses are
  discharged on a proper integral curve whose codimension-one local rings are discrete valuation
  rings.

## References

* [The Stacks Project, Section 33.44, Degrees on curves](https://stacks.math.columbia.edu/tag/0AYR):
  Definition 0AYR and Lemmas 0AYS, 0AYY.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order Scheme.Modules
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf.FixedRank

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] {r : ℕ}

/-- The degree `χ(X, E) - r · χ(X, 𝒪_X)` of a finite locally free sheaf `E` of constant rank `r`
on a scheme over a field `k`, using the degree-`2` truncation
`χ(X, M) = dim H⁰(X, M) - dim H¹(X, M)` of the Euler characteristic.

On a proper scheme of dimension at most one over `k`, cohomology is finite-dimensional and
vanishes above degree one, and this is the degree of the vector bundle `E`. No hypothesis is
needed to form the invariant; elsewhere it has the junk values of
`Scheme.Modules.eulerCharBelow`. -/
def vectorBundleDegree (E : FixedRank X r) : ℤ :=
  eulerCharBelow k X E.obj.obj 2 - r * eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2

/-- The defining formula of the degree of a vector bundle. -/
lemma vectorBundleDegree_def (E : FixedRank X r) :
    vectorBundleDegree k E =
      eulerCharBelow k X E.obj.obj 2 -
        r * eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 :=
  (rfl)

/-- The degree of a vector bundle expanded in terms of the dimensions of `H⁰` and `H¹`. -/
lemma vectorBundleDegree_eq_finrank_sub (E : FixedRank X r) :
    vectorBundleDegree k E =
      ((finrank k (Scheme.Modules.Cohomology E.obj.obj 0) : ℤ) -
          (finrank k (Scheme.Modules.Cohomology E.obj.obj 1) : ℤ)) -
        r * ((finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0) : ℤ) -
          (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ)) := by
  rw [vectorBundleDegree_def, eulerCharBelow_two, eulerCharBelow_two]

/-- Vector bundles of the same rank with isomorphic underlying sheaves have the same degree. -/
lemma vectorBundleDegree_congr {E F : FixedRank X r} (e : E.obj.obj ≅ F.obj.obj) :
    vectorBundleDegree k E = vectorBundleDegree k F := by
  rw [vectorBundleDegree_def, vectorBundleDegree_def, eulerCharBelow_congr k e]

variable (X r) in
/-- **The trivial vector bundle has degree zero**: `deg 𝒪_X^r = 0`. No finiteness hypothesis is
needed, since `χ(X, 𝒪_X^r) = r · χ(X, 𝒪_X)` holds for the truncated Euler characteristic as it
stands. -/
@[simp]
lemma vectorBundleDegree_free : vectorBundleDegree k (FixedRank.free X r) = 0 := by
  rw [vectorBundleDegree_def, InvertibleSheaf.trivial_obj, free_obj,
    FiniteLocallyFreeSheaf.free_obj, eulerCharBelow_free, eulerCharBelow_free, Fintype.card_ulift,
    Fintype.card_fin, Fintype.card_punit, Nat.cast_one, one_mul, sub_self]

/-- **The degree in rank one** is the Euler-characteristic degree `χ(L) - χ(𝒪_X)` of the
corresponding line bundle. -/
lemma vectorBundleDegree_eq_eulerDegree_toInvertible (E : FixedRank X 1) :
    vectorBundleDegree k E = ((toInvertible X).obj E).eulerDegree k := by
  rw [vectorBundleDegree_def, InvertibleSheaf.eulerDegree_def, toInvertible_obj_obj, Nat.cast_one,
    one_mul]

/-- The degree of a line bundle regarded as a vector bundle of rank one is its
Euler-characteristic degree. -/
@[simp]
lemma vectorBundleDegree_toFixedRankOne_obj (L : InvertibleSheaf X) :
    vectorBundleDegree k ((InvertibleSheaf.toFixedRankOne X).obj L) = L.eulerDegree k := by
  rw [vectorBundleDegree_def, InvertibleSheaf.eulerDegree_def,
    InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj, Nat.cast_one, one_mul]

/-- **The degree of `𝒪_X(D)`.** On a proper integral curve over `k` whose codimension-one local
rings are discrete valuation rings and with `H¹(X, 𝒪_X)` finite-dimensional, a vector bundle `E`
of rank one with `E ≅ 𝒪_X(D)` has degree `deg D = Σ_y D(y) [κ(y) : k]`. -/
theorem vectorBundleDegree_eq_relativeDegree [IsIntegral X] [IsLocallyNoetherian X]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    [IsProper (X ↘ Spec (.of k))] (hX : ∀ y : X, coheight y ≤ 1)
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    {E : FixedRank X 1} {D : SchemeWeilDivisor X} (e : E.obj.obj ≅ SchemeWeilDivisor.sheaf D) :
    vectorBundleDegree k E = SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D := by
  rw [vectorBundleDegree_eq_eulerDegree_toInvertible]
  exact InvertibleSheaf.eulerDegree_eq_relativeDegree k hX (eqToIso (toInvertible_obj_obj X E) ≪≫ e)

section ShortExact

variable {r₁ r₂ r₃ : ℕ} {E₁ : FixedRank X r₁} {E₂ : FixedRank X r₂} {E₃ : FixedRank X r₃}
  {f : E₁.obj.obj ⟶ E₂.obj.obj} {g : E₂.obj.obj ⟶ E₃.obj.obj} {w : f ≫ g = 0}

/-- **Additivity of the degree in short exact sequences.** For a short exact sequence
`0 ⟶ E₁ ⟶ E₂ ⟶ E₃ ⟶ 0` of vector bundles of constant ranks `r₁`, `r₂ = r₁ + r₃` and `r₃`, with
`H¹(X, E₁)`, `H⁰(X, E₂)` and `H¹(X, E₂)` finite-dimensional and `H²(X, E₁) = 0`, the degrees add
up: `deg E₂ = deg E₁ + deg E₃`. -/
theorem vectorBundleDegree_add_of_shortExact (hS : (ShortComplex.mk f g w).ShortExact)
    (hr : r₂ = r₁ + r₃) [FiniteDimensional k (Scheme.Modules.Cohomology E₁.obj.obj 1)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E₂.obj.obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E₂.obj.obj 1)]
    (hvan : Subsingleton (Scheme.Modules.Cohomology E₁.obj.obj 2)) :
    vectorBundleDegree k E₂ = vectorBundleDegree k E₁ + vectorBundleDegree k E₃ := by
  have h := eulerCharBelow_eq_add k hS 2
    (fun i hi hi₀ ↦ by obtain rfl : i = 1 := (by omega); infer_instance)
    (fun i hi ↦ by interval_cases i <;> infer_instance) hvan
  subst hr
  rw [vectorBundleDegree_def, vectorBundleDegree_def, vectorBundleDegree_def]
  push_cast
  linear_combination h

/-- **Additivity of the degree on a curve.** On a proper integral curve over `k` whose
codimension-one local rings are discrete valuation rings, the degree is additive in every short
exact sequence `0 ⟶ E₁ ⟶ E₂ ⟶ E₃ ⟶ 0` of vector bundles of constant ranks `r₁`, `r₂ = r₁ + r₃`
and `r₃`. -/
theorem vectorBundleDegree_add_of_shortExact_of_isCurveOver [X.IsCurveOver k]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    (hS : (ShortComplex.mk f g w).ShortExact) (hr : r₂ = r₁ + r₃) :
    vectorBundleDegree k E₂ = vectorBundleDegree k E₁ + vectorBundleDegree k E₃ := by
  have := finiteDimensional_cohomology_of_isCurveOver k E₁.obj.obj 1
  have := finiteDimensional_cohomology_of_isCurveOver k E₂.obj.obj 0
  have := finiteDimensional_cohomology_of_isCurveOver k E₂.obj.obj 1
  exact vectorBundleDegree_add_of_shortExact k hS hr
    (subsingleton_cohomology_of_two_le_of_isCurveOver k E₁.obj.obj 2 le_rfl)

end ShortExact

end FiniteLocallyFreeSheaf.FixedRank

end

end AlgebraicGeometry

end TauCeti
