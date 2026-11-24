/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.MulSequence
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

namespace InvertibleSheaf

variable (L : InvertibleSheaf X)

/-- The exact sequence of the sum of divisors `V(I * J)`, twisted by `L`. -/
private abbrev twistedMulSequence (J : X.IdealSheafData) : ShortComplex X.Modules :=
  (mulSequence I J).map (tensorLeft L.obj)

private lemma shortExact_twistedMulSequence (J : X.IdealSheafData) :
    (twistedMulSequence I L J).ShortExact :=
  Scheme.Modules.shortExact_map_tensorLeft L.obj (shortExact_mulSequence I J)

/-- The first term of the twisted sequence is `(L ⊗ J) ⊗ ι_* 𝒪_{V(I)}`. -/
private def twistedMulSequenceX₁Iso : (twistedMulSequence I L J).X₁ ≅
    (L.tensorProduct hJ.toInvertibleSheaf).obj ⊗ I.pushforwardSubscheme :=
  (α_ L.obj J.sheaf I.pushforwardSubscheme).symm ≪≫
    whiskerRightIso (whiskerLeftIso L.obj (eqToIso hJ.toInvertibleSheaf_obj.symm) ≪≫
      (tensorProductObjIso L hJ.toInvertibleSheaf).symm) _

/-- The vector bundle of rank one underlying `M` is `M`. -/
private lemma toFixedRankOne_obj_obj_obj (M : InvertibleSheaf X) :
    ((toFixedRankOne X).obj M).obj.obj = M.obj := by
  rw [toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj]

variable {I} in
/-- `H^i(X, M ⊗ ι_* 𝒪_{V(I)})` is finite-dimensional exactly when `H^i(V(I), M|_{V(I)})` is. -/
private lemma finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff (M : InvertibleSheaf X)
    (i : ℕ) : FiniteDimensional k (Cohomology (M.obj ⊗ I.pushforwardSubscheme) i) ↔
      FiniteDimensional k (Cohomology ((pullback I.subschemeι).obj M).obj i) := by
  have h := I.finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k
    ((toFixedRankOne X).obj M).obj i
  rwa [toFixedRankOne_obj_obj_obj, pullback_toFixedRankOne_obj_obj] at h

variable {I} in
/-- `χ(X, M ⊗ ι_* 𝒪_{V(I)}) = χ(V(I), M|_{V(I)})`. -/
private lemma eulerCharBelow_tensor_pushforwardSubscheme (M : InvertibleSheaf X) (n : ℕ) :
    eulerCharBelow k X (M.obj ⊗ I.pushforwardSubscheme) n =
      eulerCharBelow k I.subscheme ((pullback I.subschemeι).obj M).obj n := by
  have h := I.eulerCharBelow_tensor_pushforwardSubscheme k ((toFixedRankOne X).obj M).obj n
  rwa [toFixedRankOne_obj_obj_obj, pullback_toFixedRankOne_obj_obj] at h

variable {I} in
include k in
/-- `H^i(X, M ⊗ ι_* 𝒪_{V(I)})` vanishes exactly when `H^i(V(I), M|_{V(I)})` does. -/
private lemma subsingleton_cohomology_tensor_pushforwardSubscheme_iff (M : InvertibleSheaf X)
    (i : ℕ) : Subsingleton (Cohomology (M.obj ⊗ I.pushforwardSubscheme) i) ↔
      Subsingleton (Cohomology ((pullback I.subschemeι).obj M).obj i) := by
  have h := ((cohomologyBaseLinearEquivOfIso k
    (I.tensorPushforwardSubschemeIso ((toFixedRankOne X).obj M).obj) i).toEquiv.trans
      (cohomologyPushforwardIso I.subschemeι _ i).addCommGroupIsoToAddEquiv.toEquiv)
  replace h := h.subsingleton_congr
  rwa [toFixedRankOne_obj_obj_obj, pullback_toFixedRankOne_obj_obj] at h

variable (hI : ∀ i < 2, FiniteDimensional k
    (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj i))
  (hJL : ∀ i < 2, FiniteDimensional k (Cohomology ((pullback J.subschemeι).obj L).obj i))

include hI hJL in
private lemma finiteDimensional_cohomology_twistedMulSequence_X₂ {i : ℕ} (hi : i < 2) :
    FiniteDimensional k (Cohomology (twistedMulSequence I L J).X₂ i) := by
  have : FiniteDimensional k (Cohomology (twistedMulSequence I L J).X₁ i) :=
    (finiteDimensional_cohomology_congr k (twistedMulSequenceX₁Iso I hJ L) i).mpr
      ((finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k _ i).mpr (hI i hi))
  have : FiniteDimensional k (Cohomology (twistedMulSequence I L J).X₃ i) :=
    (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k L i).mpr (hJL i hi)
  exact finiteDimensional_cohomology_X₂ k X (shortExact_twistedMulSequence I L J) i

include hI hJL in
/-- **Finiteness of cohomology on a sum of divisors.** If the restrictions of `L` to `V(J)` and of
`L ⊗ J` to `V(I)` have finite-dimensional `H⁰` and `H¹`, where `J` is the ideal sheaf of an
effective Cartier divisor, then so does the restriction of `L` to `V(I * J)`. -/
theorem finiteDimensional_cohomology_pullback_subschemeι_mul {i : ℕ} (hi : i < 2) :
    FiniteDimensional k (Cohomology ((pullback (I * J).subschemeι).obj L).obj i) :=
  (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k L i).mp
    (finiteDimensional_cohomology_twistedMulSequence_X₂ k I hJ L hI hJL hi)

include hI hJL in
/-- **Euler characteristics on a sum of divisors.** Let `J` be the ideal sheaf of an effective
Cartier divisor on a scheme `X` over `k` and `I` an ideal sheaf. If the restrictions of `L` to
`V(J)` and of `L ⊗ J` to `V(I)` have finite-dimensional `H⁰` and `H¹`, and `H²` of the restriction
of `L ⊗ J` to `V(I)` vanishes, then
`χ(L|_{V(I * J)}) = χ(L|_{V(J)}) + χ((L ⊗ J)|_{V(I)})`, with `χ = dim H⁰ - dim H¹`. -/
theorem eulerCharBelow_pullback_subschemeι_mul
    (hI₂ : Subsingleton
      (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj 2)) :
    eulerCharBelow k (I * J).subscheme ((pullback (I * J).subschemeι).obj L).obj 2 =
      eulerCharBelow k J.subscheme ((pullback J.subschemeι).obj L).obj 2 +
        eulerCharBelow k I.subscheme
          ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj 2 := by
  have hS := shortExact_twistedMulSequence I L J
  have h₁ (i : ℕ) (hi : i < 2) (_ : 0 < i) :
      FiniteDimensional k (Cohomology (twistedMulSequence I L J).X₁ i) :=
    (finiteDimensional_cohomology_congr k (twistedMulSequenceX₁Iso I hJ L) i).mpr
      ((finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k _ i).mpr (hI i hi))
  have hvan : Subsingleton (Cohomology (twistedMulSequence I L J).X₁ 2) :=
    (cohomologyBaseLinearEquivOfIso k (twistedMulSequenceX₁Iso I hJ L)
      2).toEquiv.subsingleton_congr.mpr
        ((subsingleton_cohomology_tensor_pushforwardSubscheme_iff k _ 2).mpr hI₂)
  have h := eulerCharBelow_eq_add k hS 2 h₁
    (fun i hi ↦ finiteDimensional_cohomology_twistedMulSequence_X₂ k I hJ L hI hJL hi) hvan
  rw [eulerCharBelow_congr k (twistedMulSequenceX₁Iso I hJ L) 2] at h
  -- The other two terms are `(tensorLeft L).obj` of `ι_* 𝒪_{V(I * J)}` and `ι_* 𝒪_{V(J)}`, which
  -- unfold to `L ⊗ ι_* 𝒪_{V(I * J)}` and `L ⊗ ι_* 𝒪_{V(J)}`; `change` displays them in this form
  -- for the projection formula.
  change eulerCharBelow k X (L.obj ⊗ (I * J).pushforwardSubscheme) 2 = _ + eulerCharBelow k X
    (L.obj ⊗ J.pushforwardSubscheme) 2 at h
  rw [eulerCharBelow_tensor_pushforwardSubscheme, eulerCharBelow_tensor_pushforwardSubscheme,
    eulerCharBelow_tensor_pushforwardSubscheme] at h
  rw [h, add_comm]

end InvertibleSheaf

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

/-- On the empty closed subscheme `V(⊤)` every sheaf of modules has trivial cohomology. -/
private lemma subsingleton_cohomology_top (M : (⊤ : X.IdealSheafData).subscheme.Modules)
    (i : ℕ) : Subsingleton (Cohomology M i) := by
  have hM : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    obtain rfl : U = ⊥ := TopologicalSpace.Opens.ext (Set.eq_empty_of_isEmpty _)
    have : Subsingleton Γ(M, ⊥) := (AddCommGrpCat.isZero_iff_subsingleton).mp
      (TopCat.Sheaf.isTerminalOfEmpty ((Scheme.Modules.toSheaf _).obj M)).isZero
    ext
    exact Subsingleton.elim _ _
  exact (AddCommGrpCat.isZero_iff_subsingleton).mp ((cohomologyFunctor _ i).map_isZero hM)

/-- On the empty closed subscheme `V(⊤)` line bundles have finite-dimensional cohomology and every
class has degree zero. -/
private lemma intersectionNumber_subschemeι_top :
    (∀ (L : InvertibleSheaf X), ∀ j < 2, FiniteDimensional k
      (Cohomology ((InvertibleSheaf.pullback (⊤ : X.IdealSheafData).subschemeι).obj L).obj j)) ∧
    ∀ a : LineBundleClass X, intersectionNumber k (⊤ : X.IdealSheafData).subschemeι a = 0 := by
  have (M : (⊤ : X.IdealSheafData).subscheme.Modules) (j : ℕ) :=
    subsingleton_cohomology_top M j
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
      (hIfin _) (ih.1 L) hi, fun a ↦ ?_⟩
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
