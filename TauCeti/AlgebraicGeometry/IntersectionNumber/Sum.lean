/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Cohomology
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Degrees of line bundles on sums of effective Cartier divisors

Let `X` be a scheme over a field `k`, let `D = V(J)` be an effective Cartier divisor on `X` and let
`V(I)` be a closed subscheme, for instance a second effective Cartier divisor `E`. The degree of a
line bundle `a` on the closed subscheme `V(I * J)`, the divisor `D + E` when `I` is effective
Cartier, is computed from the degree of `a` on `D` and the degrees on `V(I)` of its twist
`a · 𝒪_X(-D)` and of `𝒪_X(-D)`:

`(a · V(I * J)) = (a · V(J)) + ((a · 𝒪_X(-D)) · V(I)) - (𝒪_X(-D) · V(I))`

(`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_subschemeι_mul`), as soon as line
bundles on `V(I)` and `V(J)` have finite-dimensional `H⁰` and `H¹` and line bundles on `V(I)` have
no `H²`. When the degree on `V(I)` is additive, as it is on an integral proper curve, this is the
additivity of degrees in the curve,

`(a · (D + E)) = (a · D) + (a · E)`

(`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_subschemeι_mul_of_isIntegral`, for
`V(I)` an integral proper curve, possibly singular, with no hypothesis on its cohomology). The
curves are not assumed reduced: by induction, the degree on the effective Cartier divisor
`Σᵢ mᵢ Cᵢ` is `Σᵢ mᵢ (a · Cᵢ)`
(`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_subschemeι_prod_pow`), provided
that each `Cᵢ` is an effective Cartier divisor, that line bundles restricted to `Cᵢ` have
finite-dimensional `H⁰` and `H¹` and no `H²`, and that the degree on `Cᵢ` is additive, as it is on
an integral proper curve. Under these conditions on its components, this is how the degree of a
line bundle on a nonreduced curve, such as a fibre of a fibred surface over `k`, is expressed
through its degrees on the components weighted by their multiplicities.

The proof twists the exact sequence of a sum of divisors
`0 ⟶ J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)} ⟶ ι_* 𝒪_{V(J)} ⟶ 0`
(`AlgebraicGeometry.Scheme.IdealSheafData.shortExact_mulSequence`) by a line bundle `L`. By the
projection formula its terms are the direct images of the restrictions of `L ⊗ J`, `L` and `L` to
`V(I)`, `V(I * J)` and `V(J)`, so the Euler characteristics `χ = dim H⁰ - dim H¹` satisfy

`χ(L|_{V(I * J)}) = χ(L|_{V(J)}) + χ((L ⊗ J)|_{V(I)})`

(`TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerCharBelow_pullback_subschemeι_mul` at `n = 2`), and
subtracting the same identity for `𝒪_X` gives the formula for degrees. The vanishing of `H²` on
`V(I)` is what makes the truncated Euler characteristic additive along the sequence, so it is a
hypothesis of the general formula. On an integral proper curve it holds for every line bundle
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.subsingleton_cohomology_of_isIntegral`), so the
additivity along such a curve needs no cohomological hypothesis on it.

## References

* [The Stacks Project, Section 33.44, Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ):
  degrees of invertible modules on proper curves, and their expression through the irreducible
  components with multiplicities.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1, on intersection numbers with
  vertical divisors `Σᵢ mᵢ Cᵢ` on arithmetic surfaces and their linearity in the divisor.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

open Scheme.IdealSheafData

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (I : X.IdealSheafData) {J : X.IdealSheafData} (hJ : J.IsEffectiveCartier)

namespace LineBundleClass

/-- **Degrees on a sum of divisors.** Let `J` be the ideal sheaf of an effective Cartier divisor
`D` on a scheme `X` over `k` and `I` an ideal sheaf, such that line bundles restricted to `V(I)`
and `V(J)` have finite-dimensional `H⁰` and `H¹`, and line bundles restricted to `V(I)` have no
`H²`. Then the degree of a line-bundle class `a` on `V(I * J)` is
`(a · V(I * J)) = (a · V(J)) + ((a · 𝒪_X(-D)) · V(I)) - (𝒪_X(-D) · V(I))`. -/
theorem intersectionNumber_subschemeι_mul
    (hI : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
    (hI₂ : ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2))
    (hJ' : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    intersectionNumber k (I * J).subschemeι a =
      intersectionNumber k J.subschemeι a +
        (intersectionNumber k I.subschemeι (a * mk hJ.toInvertibleSheaf) -
          intersectionNumber k I.subschemeι (mk hJ.toInvertibleSheaf)) := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  have key (M : InvertibleSheaf X) := M.eulerCharBelow_pullback_subschemeι_mul k I hJ 2
    (hI _) (hJ' M) (hI₂ _)
  have hL := key L
  have hT := key (InvertibleSheaf.trivial X)
  have hJ₁ : mk hJ.toInvertibleSheaf =
      mk ((InvertibleSheaf.trivial X).tensorProduct hJ.toInvertibleSheaf) := by
    rw [mk_tensorProduct, mk_trivial, one_mul]
  rw [← mk_tensorProduct, hJ₁, intersectionNumber_mk_eq_eulerCharBelow_sub,
    intersectionNumber_mk_eq_eulerCharBelow_sub, intersectionNumber_mk_eq_eulerCharBelow_sub,
    intersectionNumber_mk_eq_eulerCharBelow_sub]
  linarith

include hJ in
/-- **Additivity of degrees in the curve.** Let `J` be the ideal sheaf of an effective Cartier
divisor on a scheme `X` over `k` and `I` an ideal sheaf, such that line bundles restricted to
`V(I)` and `V(J)` have finite-dimensional `H⁰` and `H¹` and line bundles restricted to `V(I)` have
no `H²`. If the degree on `V(I)` is additive on `a` and the class of `J`, then the degree of `a` on
`V(I * J)` is the sum of its degrees on `V(I)` and on `V(J)`. -/
theorem intersectionNumber_subschemeι_mul_eq_add
    (hI : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
    (hI₂ : ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2))
    (hJ' : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    (a : LineBundleClass X)
    (hIadd : intersectionNumber k I.subschemeι (a * mk hJ.toInvertibleSheaf) =
      intersectionNumber k I.subschemeι a +
        intersectionNumber k I.subschemeι (mk hJ.toInvertibleSheaf)) :
    intersectionNumber k (I * J).subschemeι a =
      intersectionNumber k I.subschemeι a + intersectionNumber k J.subschemeι a := by
  rw [intersectionNumber_subschemeι_mul k I hJ hI hI₂ hJ' a, hIadd]
  ring

include hJ in
/-- **Additivity of degrees along an integral curve.** Let `J` be the ideal sheaf of an effective
Cartier divisor `D` on a scheme `X` over `k`, such that line bundles restricted to `D` have
finite-dimensional `H⁰` and `H¹`, and let `C = V(I)` be an integral proper curve over `k`,
possibly singular. Then `(a · V(I * J)) = (a · C) + (a · D)`; when `I` is effective Cartier,
`V(I * J)` is the divisor `C + D`. -/
theorem intersectionNumber_subschemeι_mul_of_isIntegral [IsIntegral I.subscheme]
    [IsProper (I.subscheme ↘ Spec (.of k))] [RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of k))]
    (hJ' : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    intersectionNumber k (I * J).subschemeι a =
      intersectionNumber k I.subschemeι a + intersectionNumber k J.subschemeι a := by
  -- On a proper integral scheme of dimension at most one, the structure sheaf has
  -- finite-dimensional cohomology and no `H²`, hence so do line bundles.
  have hdim : topologicalKrullDim I.subscheme ≤ 1 := by
    exact_mod_cast (relativeDimensionLE_iff_of_field (d := 1) (I.subscheme ↘ Spec (.of k))).mp
      inferInstance
  have (n : ℕ) :=
    Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one k hdim n
  have hO₂ := Scheme.Modules.subsingleton_cohomology_trivial_of_topologicalKrullDim_le_one k hdim 2
    le_rfl
  exact intersectionNumber_subschemeι_mul_eq_add k I hJ
    (fun _ _ hi ↦ InvertibleSheaf.finiteDimensional_cohomology_of_isIntegral k _ hi)
    (fun _ ↦ InvertibleSheaf.subsingleton_cohomology_of_isIntegral k _ le_rfl hO₂) hJ' a
    (intersectionNumber_mul_of_isIntegral k I.subschemeι _ _)

variable {I} in
include hJ in
/-- Peeling off multiples of a curve `V(I)` along which the degree of `a` is additive: the degree
of `a` on `V(Iⁿ * J)` is `n` times its degree on `V(I)` plus its degree on `V(J)`, with
finite-dimensional cohomology on `V(Iⁿ * J)`. -/
private lemma intersectionNumber_subschemeι_pow_mul (hI : I.IsEffectiveCartier)
    (hIfin : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
    (hI₂ : ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2))
    (hJ' : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i)) (a : LineBundleClass X)
    (hIadd : ∀ b : LineBundleClass X, intersectionNumber k I.subschemeι (a * b) =
      intersectionNumber k I.subschemeι a + intersectionNumber k I.subschemeι b) (n : ℕ) :
    (∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (I ^ n * J).subschemeι).obj L).obj i)) ∧
    intersectionNumber k (I ^ n * J).subschemeι a =
      n * intersectionNumber k I.subschemeι a + intersectionNumber k J.subschemeι a := by
  induction n with
  | zero =>
    rw [pow_zero, one_mul]
    exact ⟨hJ', by rw [Nat.cast_zero, zero_mul, zero_add]⟩
  | succ n ih =>
    have hJn := TauCeti.isEffectiveCartier_mul (TauCeti.isEffectiveCartier_pow hI n) hJ
    rw [pow_succ', mul_assoc]
    refine ⟨fun L i hi ↦ L.finiteDimensional_cohomology_pullback_subschemeι_mul k I hJn
      (hIfin _ i hi) (ih.1 L i hi), ?_⟩
    rw [intersectionNumber_subschemeι_mul_eq_add k I hJn hIfin hI₂ ih.1 a (hIadd _), ih.2]
    push_cast
    ring

/-- **Degrees on a divisor with multiplicities.** Let `X` be a scheme over `k` and `Cᵢ = V(Iᵢ)`,
for `i ∈ s`, effective Cartier divisors such that line bundles restricted to `Cᵢ` have
finite-dimensional `H⁰` and `H¹` and no `H²`, and such that the degree on `Cᵢ` is additive on `a`
and any other class; for instance integral proper curves over `k`. Then the degree of the
line-bundle class `a` on the divisor `Σᵢ mᵢ Cᵢ`, cut out by `∏ᵢ Iᵢ ^ mᵢ`, is `Σᵢ mᵢ (a · Cᵢ)`. The
divisor need not be reduced. -/
theorem intersectionNumber_subschemeι_prod_pow {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (m : ι → ℕ) (hI : ∀ i ∈ s, (I i).IsEffectiveCartier)
    (hIfin : ∀ i ∈ s, ∀ (L : InvertibleSheaf X), ∀ j < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (I i).subschemeι).obj L).obj j))
    (hI₂ : ∀ i ∈ s, ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback (I i).subschemeι).obj L).obj 2))
    (a : LineBundleClass X)
    (hIadd : ∀ i ∈ s, ∀ b : LineBundleClass X, intersectionNumber k (I i).subschemeι (a * b) =
      intersectionNumber k (I i).subschemeι a + intersectionNumber k (I i).subschemeι b) :
    intersectionNumber k (∏ i ∈ s, I i ^ m i).subschemeι a =
      ∑ i ∈ s, m i * intersectionNumber k (I i).subschemeι a := by
  classical
  suffices h : (∀ (L : InvertibleSheaf X), ∀ j < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (∏ i ∈ s, I i ^ m i).subschemeι).obj L).obj j)) ∧
      intersectionNumber k (∏ i ∈ s, I i ^ m i).subschemeι a =
        ∑ i ∈ s, m i * intersectionNumber k (I i).subschemeι a from h.2
  induction s using Finset.induction_on with
  | empty =>
    -- The empty divisor cuts out the empty closed subscheme, which has no cohomology.
    rw [Finset.prod_empty, Finset.sum_empty]
    have : IsEmpty (1 : X.IdealSheafData).subscheme :=
      inferInstanceAs (IsEmpty (⊤ : X.IdealSheafData).subscheme)
    have (M : (1 : X.IdealSheafData).subscheme.Modules) (j : ℕ) :=
      M.subsingleton_cohomology_of_isEmpty j
    exact ⟨fun _ _ _ ↦ inferInstance, intersectionNumber_eq_zero_of_isEmpty k _ a⟩
  | @insert j s hj ih =>
    have hs := ih (fun i hi ↦ hI i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hIfin i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hI₂ i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hIadd i (Finset.mem_insert_of_mem hi))
    have hj' := Finset.mem_insert_self j s
    have h := intersectionNumber_subschemeι_pow_mul k
      (isEffectiveCartier_prod (I := fun i ↦ I i ^ m i) fun i hi ↦
        TauCeti.isEffectiveCartier_pow (hI i (Finset.mem_insert_of_mem hi)) (m i)) (hI j hj')
      (hIfin j hj') (hI₂ j hj') hs.1 a (hIadd j hj') (m j)
    rw [Finset.prod_insert hj]
    exact ⟨h.1, by rw [h.2, hs.2, Finset.sum_insert hj]⟩

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
