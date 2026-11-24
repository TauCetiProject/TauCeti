/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic

/-!
# Degrees of line bundles on sums of effective Cartier divisors

Let `X` be a scheme over a field `k`, let `D = V(J)` be an effective Cartier divisor on `X` and let
`V(I)` be a closed subscheme, for instance a second effective Cartier divisor `E`. The degree of a
line bundle on the closed subscheme `V(I * J)`, the divisor `D + E` when `I` is effective Cartier,
is computed from its degrees on `D` and on `E`:

`(a · V(I * J)) = (a · V(J)) + ((a · 𝒪_X(-D)) · V(I)) - (𝒪_X(-D) · V(I))`

(`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_subschemeι_mul`), as soon as line
bundles on `V(I)` and `V(J)` have finite-dimensional `H⁰` and `H¹` and line bundles on `V(I)` have
no `H²`. When the degree on `V(I)` is additive, as it is on an integral proper curve, this is the
additivity of degrees in the curve,

`(a · (D + E)) = (a · D) + (a · E)`

(`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_subschemeι_mul_of_isIntegral`). The
curves are not assumed reduced: by induction, the degree on an effective Cartier divisor
`Σᵢ mᵢ Cᵢ` is `Σᵢ mᵢ (a · Cᵢ)` whenever the degree is additive on each component `Cᵢ`, as on an
integral proper curve, and line bundles on `Cᵢ` have no `H²`
(`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_subschemeι_prod_pow`). This is how
the degree of a line bundle on a nonreduced curve, such as a fibre of a fibred surface over `k`, is
expressed through its degrees on the components weighted by their multiplicities.

The proof twists the exact sequence of a sum of divisors
`0 ⟶ J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)} ⟶ ι_* 𝒪_{V(J)} ⟶ 0`
(`AlgebraicGeometry.Scheme.IdealSheafData.shortExact_mulSequence`) by a line bundle `L`. By the
projection formula its terms are the direct images of the restrictions of `L ⊗ J`, `L` and `L` to
`V(I)`, `V(I * J)` and `V(J)`, so the Euler characteristics `χ = dim H⁰ - dim H¹` satisfy

`χ(L|_{V(I * J)}) = χ(L|_{V(J)}) + χ((L ⊗ J)|_{V(I)})`

(`TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerCharBelow_pullback_subschemeι_mul`), and
subtracting the same identity for `𝒪_X` gives the formula for degrees. The vanishing of `H²` on
`V(I)` is what makes the truncated Euler characteristic additive along the sequence. Grothendieck
vanishing gives it on every Noetherian curve; in Tau Ceti it is currently proved on regular proper
curves (`AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_isCurveOver`), so
it is kept as a hypothesis here.

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
  have key (M : InvertibleSheaf X) := M.eulerCharBelow_pullback_subschemeι_mul k I hJ
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
`V(I)` and `V(J)` have finite-dimensional `H⁰` and `H¹`, line bundles restricted to `V(I)` have no
`H²`, and the degree on `V(I)` is additive. Then the degree on `V(I * J)` is the sum of the degrees
on `V(I)` and on `V(J)`. -/
theorem intersectionNumber_subschemeι_mul_eq_add
    (hI : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
    (hI₂ : ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2))
    (hIadd : ∀ a b : LineBundleClass X, intersectionNumber k I.subschemeι (a * b) =
      intersectionNumber k I.subschemeι a + intersectionNumber k I.subschemeι b)
    (hJ' : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    intersectionNumber k (I * J).subschemeι a =
      intersectionNumber k I.subschemeι a + intersectionNumber k J.subschemeι a := by
  rw [intersectionNumber_subschemeι_mul k I hJ hI hI₂ hJ' a, hIadd]
  ring

include hJ in
/-- **Additivity of degrees along an integral curve.** Let `J` be the ideal sheaf of an effective
Cartier divisor `D` on a scheme `X` over `k`, such that line bundles restricted to `D` have
finite-dimensional `H⁰` and `H¹`, and let `C = V(I)` be an integral proper curve over `k` with
finite-dimensional `H⁰(C, 𝒪_C)` and `H¹(C, 𝒪_C)`, possibly singular, on which line bundles have no
`H²`. Then `(a · V(I * J)) = (a · C) + (a · D)`; when `I` is effective Cartier, `V(I * J)` is the
divisor `C + D`. -/
theorem intersectionNumber_subschemeι_mul_of_isIntegral [IsIntegral I.subscheme]
    [IsProper (I.subscheme ↘ Spec (.of k))] [RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of k))]
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0)]
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1)]
    (hI₂ : ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2))
    (hJ' : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    intersectionNumber k (I * J).subschemeι a =
      intersectionNumber k I.subschemeι a + intersectionNumber k J.subschemeι a :=
  intersectionNumber_subschemeι_mul_eq_add k I hJ
    (fun _ _ hi ↦ InvertibleSheaf.finiteDimensional_cohomology_of_isIntegral k _ hi) hI₂
    (intersectionNumber_mul_of_isIntegral k I.subschemeι) hJ' a

/-- On the empty closed subscheme `V(⊤)` line bundles have finite-dimensional cohomology and every
class has degree zero. -/
private lemma intersectionNumber_subschemeι_top :
    (∀ (L : InvertibleSheaf X), ∀ j < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (⊤ : X.IdealSheafData).subschemeι).obj L).obj j)) ∧
    ∀ a : LineBundleClass X, intersectionNumber k (⊤ : X.IdealSheafData).subschemeι a = 0 := by
  have (M : (⊤ : X.IdealSheafData).subscheme.Modules) (j : ℕ) :=
    subsingleton_cohomology_subscheme_top M j
  refine ⟨fun _ _ _ ↦ inferInstance, fun a ↦ ?_⟩
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [intersectionNumber_mk, InvertibleSheaf.eulerDegree_eq_finrank_sub]
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_self]

variable {I} in
include hJ in
/-- Peeling off multiples of a curve `V(I)` along which degrees are additive: the degree on
`V(Iⁿ * J)` is `n` times the degree on `V(I)` plus the degree on `V(J)`, with finite-dimensional
cohomology on `V(Iⁿ * J)`. -/
private lemma intersectionNumber_subschemeι_pow_mul (hI : I.IsEffectiveCartier)
    (hIfin : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
    (hI₂ : ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2))
    (hIadd : ∀ a b : LineBundleClass X, intersectionNumber k I.subschemeι (a * b) =
      intersectionNumber k I.subschemeι a + intersectionNumber k I.subschemeι b)
    (hJ' : ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i)) (n : ℕ) :
    (∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (I ^ n * J).subschemeι).obj L).obj i)) ∧
    ∀ a : LineBundleClass X, intersectionNumber k (I ^ n * J).subschemeι a =
      n * intersectionNumber k I.subschemeι a + intersectionNumber k J.subschemeι a := by
  induction n with
  | zero =>
    rw [pow_zero, one_mul]
    exact ⟨hJ', fun a ↦ by rw [Nat.cast_zero, zero_mul, zero_add]⟩
  | succ n ih =>
    have hJn := TauCeti.isEffectiveCartier_mul (TauCeti.isEffectiveCartier_pow hI n) hJ
    rw [pow_succ', mul_assoc]
    refine ⟨fun L i hi ↦ L.finiteDimensional_cohomology_pullback_subschemeι_mul k I hJn
      (hIfin _ i hi) (ih.1 L i hi), fun a ↦ ?_⟩
    rw [intersectionNumber_subschemeι_mul_eq_add k I hJn hIfin hI₂ hIadd ih.1, ih.2]
    push_cast
    ring

/-- **Degrees on a divisor with multiplicities.** Let `X` be a scheme over `k` and `Cᵢ = V(Iᵢ)`,
for `i ∈ s`, effective Cartier divisors along which degrees are additive, such that line bundles
restricted to `Cᵢ` have finite-dimensional `H⁰` and `H¹` and no `H²`; for instance integral proper
curves over `k` with finite-dimensional `H⁰(Cᵢ, 𝒪)` and `H¹(Cᵢ, 𝒪)` on which line bundles have no
`H²`. Then the degree of a line-bundle class on the divisor `Σᵢ mᵢ Cᵢ`, cut out by `∏ᵢ Iᵢ ^ mᵢ`,
is `Σᵢ mᵢ (a · Cᵢ)`. The divisor need not be reduced. -/
theorem intersectionNumber_subschemeι_prod_pow {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (m : ι → ℕ) (hI : ∀ i ∈ s, (I i).IsEffectiveCartier)
    (hIfin : ∀ i ∈ s, ∀ (L : InvertibleSheaf X), ∀ j < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (I i).subschemeι).obj L).obj j))
    (hI₂ : ∀ i ∈ s, ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback (I i).subschemeι).obj L).obj 2))
    (hIadd : ∀ i ∈ s, ∀ a b : LineBundleClass X, intersectionNumber k (I i).subschemeι (a * b) =
      intersectionNumber k (I i).subschemeι a + intersectionNumber k (I i).subschemeι b)
    (a : LineBundleClass X) :
    intersectionNumber k (∏ i ∈ s, I i ^ m i).subschemeι a =
      ∑ i ∈ s, m i * intersectionNumber k (I i).subschemeι a := by
  classical
  suffices h : (∀ (L : InvertibleSheaf X), ∀ j < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (∏ i ∈ s, I i ^ m i).subschemeι).obj L).obj j)) ∧
      ∀ a : LineBundleClass X, intersectionNumber k (∏ i ∈ s, I i ^ m i).subschemeι a =
        ∑ i ∈ s, m i * intersectionNumber k (I i).subschemeι a from h.2 a
  induction s using Finset.induction_on with
  | empty =>
    -- The empty divisor cuts out the empty closed subscheme, which has no cohomology.
    rw [Finset.prod_empty]
    exact ⟨(intersectionNumber_subschemeι_top k).1,
      fun a ↦ ((intersectionNumber_subschemeι_top k).2 a).trans Finset.sum_empty.symm⟩
  | @insert j s hj ih =>
    have hs := ih (fun i hi ↦ hI i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hIfin i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hI₂ i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hIadd i (Finset.mem_insert_of_mem hi))
    have hj' := Finset.mem_insert_self j s
    have h := intersectionNumber_subschemeι_pow_mul k
      (isEffectiveCartier_prod (I := fun i ↦ I i ^ m i) fun i hi ↦
        TauCeti.isEffectiveCartier_pow (hI i (Finset.mem_insert_of_mem hi)) (m i)) (hI j hj')
      (hIfin j hj') (hI₂ j hj') (hIadd j hj') hs.1 (m j)
    rw [Finset.prod_insert hj]
    exact ⟨h.1, fun a ↦ by rw [h.2, hs.2, Finset.sum_insert hj]⟩

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
