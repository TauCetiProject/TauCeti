/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Cohomology
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.SpecialFiber.Decomposition
public import TauCeti.AlgebraicGeometry.SpecialFiber.Dimension
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Degrees on vertical divisors

Let `R` be a local ring with residue field `κ`, and let `X` be a scheme over `R`, such as a
regular model of a curve over a discrete valuation ring. A closed subscheme `V(I)` of `X`
contained in the special fibre, in the sense that its ideal sheaf contains the ideal sheaf of the
special fibre, is a scheme over `κ` (`TauCeti.subschemeOverResidueField`), so a line-bundle class
`a` on `X` has a degree `(a · V(I))` over `κ`. The vertical divisors `Σᵢ nᵢ Cᵢ` with `nᵢ ≤ mᵢ`,
where `Cᵢ` are the components of the special fibre and `mᵢ` their multiplicities, are of this
kind, the special fibre `Σᵢ mᵢ Cᵢ` itself included. This file proves that the degree is additive
in such divisors, multiplicities included:

`(a · Σᵢ nᵢ Cᵢ) = Σᵢ nᵢ (a · Cᵢ)`

(`AlgebraicGeometry.Scheme.Hom.intersectionNumber_subschemeι_prod_pow_of_ker_specialFiberι_le`),
and in particular, for a proper regular model, that the degree of `a` on the special fibre is
`Σᵢ mᵢ (a · Cᵢ)`
(`AlgebraicGeometry.Scheme.Hom.intersectionNumber_subschemeι_ker_specialFiberι_eq_sum`).

For a scheme over the field `κ` itself this is
`TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber_subschemeι_prod_pow`. Here `X` is
not a scheme over `κ`: only its closed subschemes inside the special fibre are. So the exact
sequence `0 ⟶ J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)} ⟶ ι_* 𝒪_{V(J)} ⟶ 0` of a sum of divisors,
whose ambient scheme is `X`, gives a long exact cohomology sequence of `R`-modules rather than of
`κ`-vector spaces. Lengths over `R` are additive along it
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.length_cohomology_pullback_subschemeι_mul`), and on the
cohomology of a scheme over `κ`, through which `R` acts, the `R`-length is the `κ`-dimension
(`AlgebraicGeometry.Scheme.Modules.length_cohomology_eq_of_surjective`). This gives

`(a · V(I * J)) = (a · V(J)) + ((a · 𝒪_X(-D)) · V(I)) - (𝒪_X(-D) · V(I))`

for the effective Cartier divisor `D = V(J)` and `V(I * J)` inside the special fibre, when line
bundles restricted to `V(I)` and `V(J)` have finite-dimensional `H⁰` and `H¹` over `κ` and those
restricted to `V(I)` have no `H²`
(`AlgebraicGeometry.Scheme.Hom.intersectionNumber_subschemeι_mul_of_ker_specialFiberι_le`), and
additivity `(a · V(I * J)) = (a · V(I)) + (a · V(J))` when moreover `V(I)` is an integral proper
curve over `κ`, which supplies the hypotheses on `V(I)`
(`Scheme.Hom.intersectionNumber_subschemeι_mul_of_isIntegral_of_ker_specialFiberι_le`).

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1, on intersection numbers of
  divisors with vertical divisors `Σᵢ nᵢ Cᵢ` on arithmetic surfaces and their additivity.
* [The Stacks Project, Section 33.44, Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ):
  degrees of invertible modules on proper curves, and their expression through the irreducible
  components with multiplicities.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.LineBundleClass (intersectionNumber)
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal
  isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))

/-- A closed subscheme `C = V(I)` of the special fibre, integral, proper and of dimension at most
one over the residue field `κ`, has finite-dimensional `H⁰(C, 𝒪_C)` and `H¹(C, 𝒪_C)` and
`H²(C, 𝒪_C) = 0`. -/
private lemma cohomology_trivial_of_isIntegral {I : X.IdealSheafData}
    (hKI : (specialFiberι R toBase).ker ≤ I) [IsIntegral I.subscheme]
    (hprop : letI := subschemeOverResidueField hKI
      IsProper (I.subscheme ↘ Spec (.of (ResidueField R))))
    (hdim : letI := subschemeOverResidueField hKI
      RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of (ResidueField R)))) :
    letI := subschemeOverResidueField hKI
    FiniteDimensional (ResidueField R) (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0) ∧
      FiniteDimensional (ResidueField R) (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) ∧
      Subsingleton (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 2) := by
  let := subschemeOverResidueField hKI
  have hdim' : topologicalKrullDim I.subscheme ≤ 1 := by
    exact_mod_cast (relativeDimensionLE_iff_of_field (d := 1)
      (I.subscheme ↘ Spec (.of (ResidueField R)))).mp hdim
  exact ⟨Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one
      (ResidueField R) hdim' 0,
    Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one
      (ResidueField R) hdim' 1,
    Scheme.Modules.subsingleton_cohomology_trivial_of_topologicalKrullDim_le_one
      (ResidueField R) hdim' 2 le_rfl⟩

section Sum

variable (I : X.IdealSheafData) {J : X.IdealSheafData} (hJ : J.IsEffectiveCartier)
  (hK : (specialFiberι R toBase).ker ≤ I * J)

include hK in
/-- **Euler characteristics on a sum of vertical divisors.** For `V(I * J)` inside the special
fibre, with `J` effective Cartier, the Euler characteristics `χ = dim_κ H⁰ - dim_κ H¹` of the
restrictions satisfy `χ(L|_{V(I * J)}) = χ(L|_{V(J)}) + χ((L ⊗ J)|_{V(I)})`, and the restriction of
`L` to `V(I * J)` has finite-dimensional `H⁰` and `H¹`, as soon as the restrictions of `L ⊗ J` to
`V(I)` and of `L` to `V(J)` have, and the former has no `H²`. -/
private lemma eulerCharBelow_pullback_subschemeι_mul (L : InvertibleSheaf X)
    (hIL : letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
      ∀ i < 2, FiniteDimensional (ResidueField R) (Cohomology
        ((InvertibleSheaf.pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj i))
    (hI₂ : Subsingleton (Cohomology
      ((InvertibleSheaf.pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj 2))
    (hJL : letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
      ∀ i < 2, FiniteDimensional (ResidueField R)
        (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i)) :
    letI := subschemeOverResidueField hK
    letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
    letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
    (∀ i < 2, FiniteDimensional (ResidueField R)
      (Cohomology ((InvertibleSheaf.pullback (I * J).subschemeι).obj L).obj i)) ∧
    Scheme.Modules.eulerCharBelow (ResidueField R) (I * J).subscheme
        ((InvertibleSheaf.pullback (I * J).subschemeι).obj L).obj 2 =
      Scheme.Modules.eulerCharBelow (ResidueField R) J.subscheme
          ((InvertibleSheaf.pullback J.subschemeι).obj L).obj 2 +
        Scheme.Modules.eulerCharBelow (ResidueField R) I.subscheme
          ((InvertibleSheaf.pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj
            2 := by
  let : X.Over (Spec (.of R)) := ⟨toBase⟩
  let := subschemeOverResidueField hK
  let := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
  let := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
  -- `R` acts on the cohomology of the three subschemes through the residue field.
  have hR : Function.Surjective (algebraMap R (ResidueField R)) := by
    rw [ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hIJ :=
    Scheme.Modules.length_cohomology_eq_of_surjective (subschemeOverResidueField_comp hK) hR
  have hI := Scheme.Modules.length_cohomology_eq_of_surjective
    (subschemeOverResidueField_comp (hK.trans (mul_le_of_le_one_right bot_le le_top))) hR
  have hJ' := Scheme.Modules.length_cohomology_eq_of_surjective
    (subschemeOverResidueField_comp (hK.trans (mul_le_of_le_one_left bot_le le_top))) hR
  have hlen := L.length_cohomology_pullback_subschemeι_mul I hJ R hI₂
  have hle (i : ℕ) := L.length_cohomology_pullback_subschemeι_mul_le I hJ R i
  simp only [hIJ, hI, hJ'] at hlen hle
  have hfin (i : ℕ) (hi : i < 2) : FiniteDimensional (ResidueField R)
      (Cohomology ((InvertibleSheaf.pullback (I * J).subschemeι).obj L).obj i) := by
    have := hIL i hi
    have := hJL i hi
    have h := hle i
    simp only [Module.length_eq_finrank] at h
    -- A vector space of finite length is finite-dimensional.
    have : _root_.IsNoetherian (ResidueField R) _ := (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (Module.length_ne_top_iff.mp (ne_top_of_le_ne_top (by simp) h))).1
    infer_instance
  refine ⟨hfin, ?_⟩
  have := hIL 0 (by norm_num)
  have := hIL 1 (by norm_num)
  have := hJL 0 (by norm_num)
  have := hJL 1 (by norm_num)
  have := hfin 0 (by norm_num)
  have := hfin 1 (by norm_num)
  simp only [Module.length_eq_finrank] at hlen
  norm_cast at hlen
  rw [Scheme.Modules.eulerCharBelow_two, Scheme.Modules.eulerCharBelow_two,
    Scheme.Modules.eulerCharBelow_two]
  omega

include hK in
/-- **Degrees on a sum of vertical divisors.** Let `X` be a scheme over a local ring `R`, let `J`
be the ideal sheaf of an effective Cartier divisor `D` and `I` an ideal sheaf such that `V(I * J)`
lies in the special fibre, so that `V(I)`, `V(J)` and `V(I * J)` are schemes over the residue field
`κ` of `R`. Suppose that line bundles restricted to `V(I)` and `V(J)` have finite-dimensional `H⁰`
and `H¹` over `κ`, and line bundles restricted to `V(I)` have no `H²`. Then the degree over `κ` of
a line-bundle class `a` on `V(I * J)` is
`(a · V(I * J)) = (a · V(J)) + ((a · 𝒪_X(-D)) · V(I)) - (𝒪_X(-D) · V(I))`. -/
theorem intersectionNumber_subschemeι_mul_of_ker_specialFiberι_le
    (hI : letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
      ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional (ResidueField R)
        (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj i))
    (hI₂ : ∀ L : InvertibleSheaf X,
      Subsingleton (Cohomology ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2))
    (hJ' : letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
      ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional (ResidueField R)
        (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    letI := subschemeOverResidueField hK
    letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
    letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
    intersectionNumber (ResidueField R) (I * J).subschemeι a =
      intersectionNumber (ResidueField R) J.subschemeι a +
        (intersectionNumber (ResidueField R) I.subschemeι
            (a * LineBundleClass.mk hJ.toInvertibleSheaf) -
          intersectionNumber (ResidueField R) I.subschemeι
            (LineBundleClass.mk hJ.toInvertibleSheaf)) := by
  let := subschemeOverResidueField hK
  let := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
  let := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  have key (M : InvertibleSheaf X) :=
    (eulerCharBelow_pullback_subschemeι_mul toBase I hJ hK M (hI _) (hI₂ _) (hJ' M)).2
  have hL := key L
  have hT := key (InvertibleSheaf.trivial X)
  have hJ₁ : LineBundleClass.mk hJ.toInvertibleSheaf =
      LineBundleClass.mk ((InvertibleSheaf.trivial X).tensorProduct hJ.toInvertibleSheaf) := by
    rw [LineBundleClass.mk_tensorProduct, LineBundleClass.mk_trivial, one_mul]
  rw [← LineBundleClass.mk_tensorProduct, hJ₁,
    LineBundleClass.intersectionNumber_mk_eq_eulerCharBelow_sub,
    LineBundleClass.intersectionNumber_mk_eq_eulerCharBelow_sub,
    LineBundleClass.intersectionNumber_mk_eq_eulerCharBelow_sub,
    LineBundleClass.intersectionNumber_mk_eq_eulerCharBelow_sub]
  linarith

include hJ hK in
/-- **Additivity of degrees along a vertical curve.** Let `X` be a scheme over a local ring `R`,
let `J` be the ideal sheaf of an effective Cartier divisor `D` such that line bundles restricted
to `D` have finite-dimensional `H⁰` and `H¹` over the residue field `κ` of `R`, and let `C = V(I)`
be an integral proper curve over `κ`, possibly singular, with `V(I * J)` in the special fibre.
Then the degrees over `κ` satisfy `(a · V(I * J)) = (a · C) + (a · D)`; when `I` is effective
Cartier, `V(I * J)` is the divisor `C + D`. -/
theorem intersectionNumber_subschemeι_mul_of_isIntegral_of_ker_specialFiberι_le
    [IsIntegral I.subscheme]
    (hprop : letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
      IsProper (I.subscheme ↘ Spec (.of (ResidueField R))))
    (hdim : letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
      RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of (ResidueField R))))
    (hJ' : letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
      ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional (ResidueField R)
        (Cohomology ((InvertibleSheaf.pullback J.subschemeι).obj L).obj i))
    (a : LineBundleClass X) :
    letI := subschemeOverResidueField hK
    letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
    letI := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
    intersectionNumber (ResidueField R) (I * J).subschemeι a =
      intersectionNumber (ResidueField R) I.subschemeι a +
        intersectionNumber (ResidueField R) J.subschemeι a := by
  let := subschemeOverResidueField hK
  let := subschemeOverResidueField (hK.trans (mul_le_of_le_one_right bot_le le_top))
  let := subschemeOverResidueField (hK.trans (mul_le_of_le_one_left bot_le le_top))
  -- On a proper integral scheme of dimension at most one, line bundles have finite-dimensional
  -- `H⁰` and `H¹` and no `H²`, since the structure sheaf has these properties.
  obtain ⟨_, _, hO₂⟩ := cohomology_trivial_of_isIntegral toBase
    (hK.trans (mul_le_of_le_one_right bot_le le_top)) hprop hdim
  rw [intersectionNumber_subschemeι_mul_of_ker_specialFiberι_le toBase I hJ hK
    (fun _ _ hi ↦ InvertibleSheaf.finiteDimensional_cohomology_of_isIntegral _ _ hi)
    (fun _ ↦ InvertibleSheaf.subsingleton_cohomology_of_isIntegral (ResidueField R) _ le_rfl hO₂)
    hJ' a, LineBundleClass.intersectionNumber_mul_of_isIntegral]
  ring

end Sum

section Prod

/-- Peeling off multiples of a curve `C = V(I)` in the special fibre, an integral proper curve over
the residue field: if `V(Iᵐ * P)` lies in the special fibre, where `P` is effective Cartier and line
bundles restricted to `V(P)` have finite-dimensional `H⁰` and `H¹`, then
`(a · V(Iᵐ * P)) = m (a · C) + (a · V(P))`, and line bundles restricted to `V(Iᵐ * P)` have
finite-dimensional `H⁰` and `H¹`. The ideal `N = Iᵐ * P` is a variable, so that the structure over
the residue field of `V(N)`, which depends on the proof that `N` contains the ideal of the
special fibre, can be transported along `N = Iᵐ * P`. -/
private lemma intersectionNumber_subschemeι_pow_mul {I P : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hP : P.IsEffectiveCartier)
    (hKI : (specialFiberι R toBase).ker ≤ I) (hKP : (specialFiberι R toBase).ker ≤ P)
    [IsIntegral I.subscheme]
    (hprop : letI := subschemeOverResidueField hKI
      IsProper (I.subscheme ↘ Spec (.of (ResidueField R))))
    (hdim : letI := subschemeOverResidueField hKI
      RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of (ResidueField R))))
    (hPfin : letI := subschemeOverResidueField hKP
      ∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional (ResidueField R)
        (Cohomology ((InvertibleSheaf.pullback P.subschemeι).obj L).obj i))
    (a : LineBundleClass X) (m : ℕ) {N : X.IdealSheafData} (hN : N = I ^ m * P)
    (hK : (specialFiberι R toBase).ker ≤ N) :
    letI := subschemeOverResidueField hK
    letI := subschemeOverResidueField hKI
    letI := subschemeOverResidueField hKP
    (∀ (L : InvertibleSheaf X), ∀ i < 2, FiniteDimensional (ResidueField R)
      (Cohomology ((InvertibleSheaf.pullback N.subschemeι).obj L).obj i)) ∧
    intersectionNumber (ResidueField R) N.subschemeι a =
      m * intersectionNumber (ResidueField R) I.subschemeι a +
        intersectionNumber (ResidueField R) P.subschemeι a := by
  induction m generalizing N with
  | zero =>
    rw [pow_zero, one_mul] at hN
    subst hN
    exact ⟨hPfin, by rw [Nat.cast_zero, zero_mul, zero_add]⟩
  | succ m ih =>
    have hN' : N = I * (I ^ m * P) := by rw [hN, pow_succ', mul_assoc]
    subst hN'
    have hKm : (specialFiberι R toBase).ker ≤ I ^ m * P :=
      hK.trans (mul_le_of_le_one_left bot_le le_top)
    obtain ⟨hfin, h⟩ := ih rfl hKm
    have hJm := TauCeti.isEffectiveCartier_mul (TauCeti.isEffectiveCartier_pow hI m) hP
    let := subschemeOverResidueField hKI
    obtain ⟨_, _, hO₂⟩ := cohomology_trivial_of_isIntegral toBase hKI hprop hdim
    refine ⟨fun L ↦ (eulerCharBelow_pullback_subschemeι_mul toBase I hJm hK L
      (fun _ hi ↦ InvertibleSheaf.finiteDimensional_cohomology_of_isIntegral _ _ hi)
      (InvertibleSheaf.subsingleton_cohomology_of_isIntegral (ResidueField R) _ le_rfl hO₂)
      (hfin L)).1, ?_⟩
    rw [intersectionNumber_subschemeι_mul_of_isIntegral_of_ker_specialFiberι_le toBase I hJm hK
      hprop hdim hfin a, h]
    push_cast
    ring

/-- The degree on `V(N)` for `N = ∏ᵢ Iᵢ ^ nᵢ` in the special fibre, by induction on the index
set, together with the finiteness of the cohomology of line bundles restricted to `V(N)` that the
induction carries along. As in `intersectionNumber_subschemeι_pow_mul`, the ideal `N` is a
variable. -/
private lemma intersectionNumber_subschemeι_prod_pow_aux {ι : Type*} (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (hI : ∀ i, (I i).IsEffectiveCartier)
    (hKI : ∀ i, (specialFiberι R toBase).ker ≤ I i) [∀ i, IsIntegral (I i).subscheme]
    (hprop : ∀ i, letI := subschemeOverResidueField (hKI i)
      IsProper ((I i).subscheme ↘ Spec (.of (ResidueField R))))
    (hdim : ∀ i, letI := subschemeOverResidueField (hKI i)
      RelativeDimensionLE 1 ((I i).subscheme ↘ Spec (.of (ResidueField R))))
    (a : LineBundleClass X) (s : Finset ι) {N : X.IdealSheafData} (hN : N = ∏ i ∈ s, I i ^ n i)
    (hK : (specialFiberι R toBase).ker ≤ N) :
    letI := subschemeOverResidueField hK
    (∀ (L : InvertibleSheaf X), ∀ j < 2, FiniteDimensional (ResidueField R)
      (Cohomology ((InvertibleSheaf.pullback N.subschemeι).obj L).obj j)) ∧
    intersectionNumber (ResidueField R) N.subschemeι a =
      ∑ i ∈ s, letI := subschemeOverResidueField (hKI i)
        n i * intersectionNumber (ResidueField R) (I i).subschemeι a := by
  classical
  induction s using Finset.induction_on generalizing N with
  | empty =>
    -- The empty divisor cuts out the empty closed subscheme, which has no cohomology.
    rw [Finset.prod_empty] at hN
    subst hN
    have : IsEmpty (1 : X.IdealSheafData).subscheme :=
      inferInstanceAs (IsEmpty (⊤ : X.IdealSheafData).subscheme)
    have (M : (1 : X.IdealSheafData).subscheme.Modules) (j : ℕ) :=
      M.subsingleton_cohomology_of_isEmpty j
    exact ⟨fun _ _ _ ↦ inferInstance, by
      rw [Finset.sum_empty, LineBundleClass.intersectionNumber_eq_zero_of_isEmpty]⟩
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj] at hN
    have hKs : (specialFiberι R toBase).ker ≤ ∏ i ∈ s, I i ^ n i :=
      hK.trans (hN ▸ mul_le_of_le_one_left bot_le le_top)
    obtain ⟨hfin, h⟩ := ih rfl hKs
    have hP := isEffectiveCartier_prod (s := s) (I := fun i ↦ I i ^ n i) fun i _ ↦
      TauCeti.isEffectiveCartier_pow (hI i) (n i)
    obtain ⟨hNfin, hN'⟩ := intersectionNumber_subschemeι_pow_mul toBase (hI j) hP (hKI j) hKs
      (hprop j) (hdim j) hfin a (n j) hN hK
    exact ⟨hNfin, by rw [hN', h, Finset.sum_insert hj]⟩

/-- **Degrees on vertical divisors with multiplicities.** Let `X` be a scheme over a local ring `R`
with residue field `κ`, and let `Cᵢ = V(Iᵢ)` for `i ∈ s` be effective Cartier divisors contained in
the special fibre that are integral proper curves over `κ`, such as the components of the special
fibre of a proper regular model. If the divisor `Σᵢ nᵢ Cᵢ`, cut out by `∏ᵢ Iᵢ ^ nᵢ`, is contained in
the special fibre, as it is when `nᵢ` is at most the multiplicity of `Cᵢ`, then the degree over `κ`
of a line-bundle class `a` on it is `Σᵢ nᵢ (a · Cᵢ)`. The divisor need not be reduced. The sum
runs over the subtype `↑s`, so that each `Cᵢ` is a scheme over `κ` through the hypotheses on
`i ∈ s` alone. -/
theorem intersectionNumber_subschemeι_prod_pow_of_ker_specialFiberι_le {ι : Type*}
    (s : Finset ι) (I : ι → X.IdealSheafData) (n : ι → ℕ)
    (hI : ∀ i ∈ s, (I i).IsEffectiveCartier)
    (hKI : ∀ i ∈ s, (specialFiberι R toBase).ker ≤ I i)
    (hint : ∀ i ∈ s, IsIntegral (I i).subscheme)
    (hprop : ∀ i (hi : i ∈ s), letI := subschemeOverResidueField (hKI i hi)
      IsProper ((I i).subscheme ↘ Spec (.of (ResidueField R))))
    (hdim : ∀ i (hi : i ∈ s), letI := subschemeOverResidueField (hKI i hi)
      RelativeDimensionLE 1 ((I i).subscheme ↘ Spec (.of (ResidueField R))))
    (hK : (specialFiberι R toBase).ker ≤ ∏ i ∈ s, I i ^ n i) (a : LineBundleClass X) :
    letI := subschemeOverResidueField hK
    intersectionNumber (ResidueField R) (∏ i ∈ s, I i ^ n i).subschemeι a =
      ∑ i : s, letI := subschemeOverResidueField (hKI i i.property)
        n i * intersectionNumber (ResidueField R) (I i).subschemeι a :=
  have (i : s) : IsIntegral (I i).subscheme := hint i i.property
  (intersectionNumber_subschemeι_prod_pow_aux toBase (ι := s) (fun i ↦ I i) (fun i ↦ n i)
    (fun i ↦ hI i i.property) (fun i ↦ hKI i i.property) (fun i ↦ hprop i i.property)
    (fun i ↦ hdim i i.property) a Finset.univ (Finset.prod_coe_sort s _).symm hK).2

/-- **The degree on the special fibre.** Let `X` be a regular Noetherian integral scheme, proper
over a local ring `R` of dimension at most one whose maximal ideal is generated by `π`, with all
points of codimension at most two and generic point away from the closed point, such as a proper
regular model of a curve over a discrete valuation ring. Then the degree over the residue field of
a line-bundle class `a` on the special fibre `X_s = Σᵢ mᵢ Cᵢ` is `Σᵢ mᵢ (a · Cᵢ)`, where `Cᵢ` are
the components of the special fibre, with their reduced structures, and `mᵢ` their multiplicities.
-/
theorem intersectionNumber_subschemeι_ker_specialFiberι_eq_sum [IsProper toBase]
    [Ring.DimensionLEOne R] [IsIntegral X] [IsNoetherian X] [TauCeti.AlgebraicGeometry.IsRegular X]
    (hX : ∀ x : X, Order.coheight x ≤ 2) (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) (a : LineBundleClass X) :
    letI := subschemeOverResidueField (le_refl (specialFiberι R toBase).ker)
    intersectionNumber (ResidueField R) (specialFiberι R toBase).ker.subschemeι a =
      ∑ i : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((Set.Finite.mem_toFinset _).mp i.property))
        (toBase.specialFiberMultiplicity π i : ℤ) * intersectionNumber (ResidueField R)
          (vanishingIdeal
            ⟨closure {((i : CodimensionOnePoint X) : X)}, isClosed_closure⟩).subschemeι a := by
  let S := (toBase.finite_setOf_base_eq_closedPoint
    (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset
  exact (intersectionNumber_subschemeι_prod_pow_aux toBase (ι := S)
    (fun i ↦ vanishingIdeal ⟨closure {((i : CodimensionOnePoint X) : X)}, isClosed_closure⟩)
    (fun i ↦ toBase.specialFiberMultiplicity π i)
    (fun i ↦ isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
      (i : CodimensionOnePoint X).property)
    (fun i ↦ toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
      ((Set.Finite.mem_toFinset _).mp i.property))
    (fun _ ↦ isProper_subschemeOverResidueField _)
    (fun i ↦ toBase.relativeDimensionLE_subscheme_vanishingIdeal_closure_singleton hX
      (fun h ↦ one_ne_zero ((i : CodimensionOnePoint X).property.symm.trans
        (Order.coheight_eq_zero.mpr h))) ((Set.Finite.mem_toFinset _).mp i.property))
    a Finset.univ ((toBase.ker_specialFiberι_eq_prod_vanishingIdeal hX hη hπ).trans
      (Finset.prod_coe_sort S _).symm) le_rfl).2

end Prod

end AlgebraicGeometry.Scheme.Hom
