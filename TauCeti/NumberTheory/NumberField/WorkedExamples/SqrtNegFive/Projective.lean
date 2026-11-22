/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Invertible
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.NumberTheory.NumberField.WorkedExamples.SqrtNegFive.ClassNumber
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Rank
import TauCeti.RingTheory.PicardGroup.RankOne

/-!
# A projective `ℤ[√-5]`-module invisible to all local ranks

Let `A = ℤ[√-5] = QuadraticAlgebra ℤ (-5) 0`, the ring of integers of `ℚ(√-5)`
(`QuadraticAlgebra.ringOfIntegersEquiv`), write `s = √-5`, and let `𝔭 = (2, 1 + s)` be the prime
of `A` above `2`. This file exhibits `𝔭` as an explicit direct summand of `A²` and computes its
class in projective `K₀(A)`, the split Grothendieck group of finitely generated projective
`A`-modules.

The maps

```text
π : A² → 𝔭,  π(r₀, r₁) = 2 r₀ + (1 + s) r₁,
ι : 𝔭 → A²,  ι(a) = (a (s - 1) / 2, -a (1 + s) / 2)
```

are `A`-linear, the fractions being integral because `𝔭 (s - 1) ⊆ (2)` and `𝔭 (1 + s) ⊆ (2)`, and
`π ∘ ι = id`. Hence `ι ∘ π` is right multiplication of row vectors by the idempotent matrix
`e = !![s - 1, -1 - s; -3, 2 - s]`, of trace one, whose image is isomorphic to `𝔭`. The
complementary summand `ker π` is isomorphic to `𝔭` as well, through `b ↦ (-b (1 + s) / 2, b)`, so
that `A² ≃ 𝔭 × 𝔭`.

Consequently the reduced class `x = [𝔭] - [A]` satisfies `2 x = 0`, and `x ≠ 0` because `𝔭` is not
principal. At the same time `𝔭` has rank one at every prime, and `x` maps to zero in projective
`K₀` of every commutative local ring receiving `A`, in particular of every localization `A_q` at a
prime `q`, where `K₀` is torsion-free. So `x` is a nonzero class of order two which no local rank
and no localization detects: neither the local ranks nor the classes in all prime localizations
determine a projective class.

## Main definitions

* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo`: the ideal `𝔭 = (2, 1 + √-5)`.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.retraction`: the surjection `π : A² → 𝔭`.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.inclusion`: its section `ι : 𝔭 → A²`.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.idempotent`: the idempotent matrix of `ι ∘ π`
  acting on row vectors.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.rangeEquiv`: the image of that idempotent is
  isomorphic to `𝔭`.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.prodEquiv`: the isomorphism `A² ≃ 𝔭 × 𝔭`.

## Main results

* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.retraction_comp_inclusion`: `π ∘ ι = id`.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.vecMulLinear_idempotent`,
  `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.isIdempotentElem_idempotent`: `ι ∘ π` is right
  multiplication by the idempotent matrix `e`.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.toSplitK0_mk_idempotent`: the class of `e` in
  `V(A)` maps to the class of `𝔭` in projective `K₀(A)`.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.rankAtStalk_eq_one`: `𝔭` has rank one at every
  prime.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.addOrderOf_classOf`: the reduced class
  `[𝔭] - [A]` has order two.
* `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.map_classOf_eq_zero_of_isLocalRing`,
  `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.map_classOf_localization_eq_zero`: the reduced
  class vanishes in projective `K₀` of every commutative local ring receiving `A`, in particular
  of every prime localization.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, §3 (pp. 18–20),
  on invertible ideals of Dedekind domains as projective modules, and Chapter II, Example 2.6
  (pp. 74–75), on the reduced class of an ideal in `K₀`.
-/

public section

open QuadraticAlgebra Module CategoryTheory Matrix TauCeti.FiniteProjectiveModules

namespace TauCeti.NumberField.SqrtNegFive

/-- The square of `√-5` is `-5`. -/
private theorem omega_mul_omega : (ω : QuadraticAlgebra ℤ (-5) 0) * ω = -5 := by
  ext <;> simp

/-- Multiplication by `2` is injective on `ℤ[√-5]`. -/
private theorem eq_of_two_mul_eq {x y : QuadraticAlgebra ℤ (-5) 0} (h : 2 * x = 2 * y) : x = y :=
  mul_left_cancel₀ (fun h2 ↦ by simpa using congrArg QuadraticAlgebra.re h2) h

/-- The prime `𝔭 = (2, 1 + √-5)` of `ℤ[√-5]` above `2`. -/
noncomputable def primeAboveTwo : Ideal (QuadraticAlgebra ℤ (-5) 0) :=
  Ideal.span {2, 1 + ω}

namespace primeAboveTwo

/-- Membership in `𝔭 = (2, 1 + √-5)`. -/
theorem mem_iff {a : QuadraticAlgebra ℤ (-5) 0} :
    a ∈ primeAboveTwo ↔ ∃ x y, x * 2 + y * (1 + ω) = a :=
  Ideal.mem_span_pair

theorem two_mem : (2 : QuadraticAlgebra ℤ (-5) 0) ∈ primeAboveTwo :=
  Ideal.subset_span (by simp)

theorem one_add_omega_mem : (1 + ω : QuadraticAlgebra ℤ (-5) 0) ∈ primeAboveTwo :=
  Ideal.subset_span (by simp)

/-- The generators `2` and `1 + √-5` of `𝔭` may be replaced by `2` and `√-5 - 1`. -/
theorem eq_span_two_omega_sub_one : primeAboveTwo = Ideal.span {2, ω - 1} := by
  rw [primeAboveTwo]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_) <;>
    rintro _ (rfl | rfl | _) <;> rw [SetLike.mem_coe, Ideal.mem_span_pair]
  exacts [⟨1, 0, by ring⟩, ⟨1, 1, by ring⟩, ⟨1, 0, by ring⟩, ⟨-1, 1, by ring⟩]

/-- `𝔭` is not principal. -/
theorem not_isPrincipal : ¬ primeAboveTwo.IsPrincipal := by
  rw [eq_span_two_omega_sub_one]
  exact not_isPrincipal_span_two_omega_sub_one

/-- `𝔭` is a proper ideal: `1 ∉ 𝔭`. -/
theorem one_notMem : (1 : QuadraticAlgebra ℤ (-5) 0) ∉ primeAboveTwo := fun h ↦ by
  apply not_isPrincipal
  rw [Ideal.eq_top_of_isUnit_mem _ h isUnit_one]
  exact ⟨1, Ideal.span_singleton_one.symm⟩

theorem ne_bot : primeAboveTwo ≠ ⊥ :=
  ne_of_mem_of_not_mem' two_mem (by simp)

/-- `𝔭 (√-5 - 1) ⊆ (2)`. -/
theorem two_dvd_mul_omega_sub_one {a : QuadraticAlgebra ℤ (-5) 0} (ha : a ∈ primeAboveTwo) :
    2 ∣ a * (ω - 1) := by
  obtain ⟨x, y, rfl⟩ := mem_iff.1 ha
  exact ⟨x * (ω - 1) - 3 * y, by linear_combination y * omega_mul_omega⟩

/-- `𝔭 (1 + √-5) ⊆ (2)`. -/
theorem two_dvd_mul_one_add_omega {a : QuadraticAlgebra ℤ (-5) 0} (ha : a ∈ primeAboveTwo) :
    2 ∣ a * (1 + ω) := by
  obtain ⟨x, y, rfl⟩ := mem_iff.1 ha
  exact ⟨x * (1 + ω) + (ω - 2) * y, by linear_combination y * omega_mul_omega⟩

/-- Division by `2` on the ideal `(2)`, the inverse of multiplication by `2`. -/
private noncomputable def halve :
    Ideal.span {(2 : QuadraticAlgebra ℤ (-5) 0)} ≃ₗ[QuadraticAlgebra ℤ (-5) 0]
      QuadraticAlgebra ℤ (-5) 0 :=
  (LinearEquiv.toSpanNonzeroSingleton _ _ 2 two_ne_zero).symm

private theorem two_mul_halve (b : Ideal.span {(2 : QuadraticAlgebra ℤ (-5) 0)}) :
    2 * halve b = b := by
  rw [mul_comm]
  exact LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul _ _ _ _ b

/-- The map `a ↦ a c / 2` on `𝔭`, for `c` with `𝔭 c ⊆ (2)`. -/
private noncomputable def halfMul (c : QuadraticAlgebra ℤ (-5) 0)
    (hc : ∀ a ∈ primeAboveTwo, 2 ∣ a * c) :
    primeAboveTwo →ₗ[QuadraticAlgebra ℤ (-5) 0] QuadraticAlgebra ℤ (-5) 0 :=
  halve.toLinearMap ∘ₗ ((LinearMap.mulRight _ c ∘ₗ primeAboveTwo.subtype).codRestrict _
    fun a ↦ Ideal.mem_span_singleton.2 (hc a a.prop))

private theorem two_mul_halfMul (c : QuadraticAlgebra ℤ (-5) 0)
    (hc : ∀ a ∈ primeAboveTwo, 2 ∣ a * c) (a : primeAboveTwo) :
    2 * halfMul c hc a = a * c :=
  two_mul_halve _

/-- The **section** `ι : 𝔭 → A²`, `ι(a) = (a (√-5 - 1) / 2, -a (1 + √-5) / 2)`, of
`TauCeti.NumberField.SqrtNegFive.primeAboveTwo.retraction`. -/
noncomputable def inclusion :
    primeAboveTwo →ₗ[QuadraticAlgebra ℤ (-5) 0] Fin 2 → QuadraticAlgebra ℤ (-5) 0 :=
  LinearMap.pi ![halfMul (ω - 1) fun _ ↦ two_dvd_mul_omega_sub_one,
    -halfMul (1 + ω) fun _ ↦ two_dvd_mul_one_add_omega]

theorem two_mul_inclusion_zero (a : primeAboveTwo) :
    2 * inclusion a 0 = a * (ω - 1 : QuadraticAlgebra ℤ (-5) 0) :=
  two_mul_halfMul (ω - 1) (fun _ ↦ two_dvd_mul_omega_sub_one) a

theorem two_mul_inclusion_one (a : primeAboveTwo) :
    2 * inclusion a 1 = -(a * (1 + ω : QuadraticAlgebra ℤ (-5) 0)) := by
  simp [inclusion, ← two_mul_halfMul (1 + ω) (fun _ ↦ two_dvd_mul_one_add_omega) a]

/-- **Characterization of the section**: `ι(a)` is the vector `v` with `2 v = (a (√-5 - 1),
-a (1 + √-5))`. -/
theorem inclusion_eq_iff {a : primeAboveTwo} {v : Fin 2 → QuadraticAlgebra ℤ (-5) 0} :
    inclusion a = v ↔ 2 * v 0 = a * (ω - 1 : QuadraticAlgebra ℤ (-5) 0) ∧
      2 * v 1 = -(a * (1 + ω : QuadraticAlgebra ℤ (-5) 0)) := by
  refine ⟨?_, fun ⟨h₀, h₁⟩ ↦ funext fun i ↦ ?_⟩
  · rintro rfl
    exact ⟨two_mul_inclusion_zero a, two_mul_inclusion_one a⟩
  · refine eq_of_two_mul_eq ?_
    fin_cases i
    exacts [(two_mul_inclusion_zero a).trans h₀.symm, (two_mul_inclusion_one a).trans h₁.symm]

/-- At `a = 2` the section is `ι(2) = (√-5 - 1, -1 - √-5)`. -/
theorem inclusion_two : inclusion ⟨2, two_mem⟩ = ![ω - 1, -1 - ω] :=
  inclusion_eq_iff.2 ⟨by simp, by simp; ring⟩

/-- At `a = 1 + √-5` the section is `ι(1 + √-5) = (-3, 2 - √-5)`. -/
theorem inclusion_one_add_omega : inclusion ⟨1 + ω, one_add_omega_mem⟩ = ![-3, 2 - ω] :=
  inclusion_eq_iff.2 ⟨by simp; linear_combination -omega_mul_omega,
    by simp; linear_combination omega_mul_omega⟩

/-- The **retraction** `π : A² → 𝔭`, `π(r₀, r₁) = 2 r₀ + (1 + √-5) r₁`. -/
noncomputable def retraction :
    (Fin 2 → QuadraticAlgebra ℤ (-5) 0) →ₗ[QuadraticAlgebra ℤ (-5) 0] primeAboveTwo :=
  (Fintype.linearCombination _ ![2, 1 + ω]).codRestrict _ fun r ↦
    mem_iff.2 ⟨r 0, r 1, by simp [Fintype.linearCombination_apply, Fin.sum_univ_two]⟩

@[simp]
theorem coe_retraction (r : Fin 2 → QuadraticAlgebra ℤ (-5) 0) :
    (retraction r : QuadraticAlgebra ℤ (-5) 0) = 2 * r 0 + (1 + ω) * r 1 := by
  simp [retraction, Fintype.linearCombination_apply, Fin.sum_univ_two, mul_comm]

/-- **`π ∘ ι = id`**: the ideal `𝔭` is a direct summand of `A²`. -/
theorem retraction_comp_inclusion : retraction ∘ₗ inclusion = LinearMap.id := by
  refine LinearMap.ext fun a ↦ Subtype.ext (eq_of_two_mul_eq ?_)
  simp only [LinearMap.comp_apply, coe_retraction, LinearMap.id_coe, id_eq]
  linear_combination 2 * two_mul_inclusion_zero a + (1 + ω) * two_mul_inclusion_one a -
    (a : QuadraticAlgebra ℤ (-5) 0) * omega_mul_omega

@[simp]
theorem retraction_inclusion (a : primeAboveTwo) : retraction (inclusion a) = a :=
  LinearMap.congr_fun retraction_comp_inclusion a

theorem retraction_surjective : Function.Surjective retraction :=
  fun a ↦ ⟨inclusion a, retraction_inclusion a⟩

theorem inclusion_injective : Function.Injective inclusion :=
  Function.LeftInverse.injective retraction_inclusion

instance : Module.Projective (QuadraticAlgebra ℤ (-5) 0) primeAboveTwo :=
  .of_split inclusion retraction retraction_comp_inclusion

instance : Module.Finite (QuadraticAlgebra ℤ (-5) 0) primeAboveTwo :=
  .of_surjective retraction retraction_surjective

/-- `𝔭` has rank one at every prime of `ℤ[√-5]`. -/
theorem rankAtStalk_eq_one (q : PrimeSpectrum (QuadraticAlgebra ℤ (-5) 0)) :
    rankAtStalk primeAboveTwo q = 1 :=
  have := primeAboveTwo.moduleInvertible_of_ne_bot ne_bot
  Module.Invertible.rankAtStalk_eq_one q

/-! ### The idempotent matrix of `ι ∘ π` -/

/-- The idempotent matrix `!![√-5 - 1, -1 - √-5; -3, 2 - √-5]`, whose right action on row vectors
is `ι ∘ π`. -/
def idempotent : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra ℤ (-5) 0) :=
  !![ω - 1, -1 - ω; -3, 2 - ω]

/-- Right multiplication of row vectors by
`TauCeti.NumberField.SqrtNegFive.primeAboveTwo.idempotent` is `ι ∘ π`. -/
theorem vecMul_idempotent (r : Fin 2 → QuadraticAlgebra ℤ (-5) 0) :
    r ᵥ* idempotent = inclusion (retraction r) := by
  refine (inclusion_eq_iff.2 ⟨?_, ?_⟩).symm <;>
    simp only [idempotent, Matrix.vecMul, dotProduct, Fin.sum_univ_two, coe_retraction] <;>
    simp
  · linear_combination (-r 1) * omega_mul_omega
  · linear_combination r 1 * omega_mul_omega

theorem vecMulLinear_idempotent : idempotent.vecMulLinear = inclusion ∘ₗ retraction :=
  LinearMap.ext vecMul_idempotent

theorem isIdempotentElem_idempotent : IsIdempotentElem idempotent := by
  refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp [idempotent, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination omega_mul_omega
  · ring
  · ring
  · linear_combination omega_mul_omega

/-- The idempotent has trace one, the rank of `𝔭`. -/
theorem trace_idempotent : idempotent.trace = 1 := by
  simp [idempotent, Matrix.trace_fin_two]
  ring

/-- The image of the right action of `TauCeti.NumberField.SqrtNegFive.primeAboveTwo.idempotent` on
row vectors is isomorphic to `𝔭`, through `π`. -/
noncomputable def rangeEquiv :
    LinearMap.range idempotent.vecMulLinear ≃ₗ[QuadraticAlgebra ℤ (-5) 0] primeAboveTwo :=
  (LinearEquiv.ofEq _ _ (by
    rw [vecMulLinear_idempotent, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 retraction_surjective)])).trans
    (LinearEquiv.ofLeftInverse retraction_inclusion).symm

@[simp]
theorem rangeEquiv_apply (x : LinearMap.range idempotent.vecMulLinear) :
    rangeEquiv x = retraction x :=
  (rfl)

theorem inclusion_rangeEquiv (x : LinearMap.range idempotent.vecMulLinear) :
    inclusion (rangeEquiv x) = x :=
  congrArg Subtype.val ((LinearEquiv.ofLeftInverse retraction_inclusion).apply_symm_apply _)

/-- The class of the idempotent `e` in `V(A)` maps to the class `[𝔭]` in projective `K₀(A)`. -/
theorem toSplitK0_mk_idempotent :
    IdempotentMonoid.toSplitK0 (IdempotentMonoid.mk idempotent isIdempotentElem_idempotent) =
      SplitK0.of.{0} ⟨ModuleCat.of (QuadraticAlgebra ℤ (-5) 0) primeAboveTwo,
        finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩ :=
  IdempotentMonoid.toSplitK0_mk _ _ rangeEquiv.symm

/-! ### The complementary summand and `A² ≃ 𝔭 × 𝔭` -/

/-- The inclusion `b ↦ (-b (1 + √-5) / 2, b)` of `𝔭` onto the kernel of `π`. -/
noncomputable def kerInclusion :
    primeAboveTwo →ₗ[QuadraticAlgebra ℤ (-5) 0] Fin 2 → QuadraticAlgebra ℤ (-5) 0 :=
  LinearMap.pi ![LinearMap.proj 1 ∘ₗ inclusion, primeAboveTwo.subtype]

@[simp]
theorem kerInclusion_zero (b : primeAboveTwo) : kerInclusion b 0 = inclusion b 1 :=
  (rfl)

@[simp]
theorem kerInclusion_one (b : primeAboveTwo) : kerInclusion b 1 = b :=
  (rfl)

theorem retraction_comp_kerInclusion : retraction ∘ₗ kerInclusion = 0 := by
  refine LinearMap.ext fun b ↦ Subtype.ext ?_
  simp only [LinearMap.comp_apply, coe_retraction, kerInclusion_zero, kerInclusion_one,
    LinearMap.zero_apply, ZeroMemClass.coe_zero]
  linear_combination two_mul_inclusion_one b

/-- The retraction `ρ(r₀, r₁) = (1 + √-5) r₀ + (√-5 - 1) r₁` of `A²` onto `ker π ≃ 𝔭`. -/
noncomputable def kerRetraction :
    (Fin 2 → QuadraticAlgebra ℤ (-5) 0) →ₗ[QuadraticAlgebra ℤ (-5) 0] primeAboveTwo :=
  (Fintype.linearCombination _ ![1 + ω, ω - 1]).codRestrict _ fun r ↦
    mem_iff.2 ⟨-r 1, r 0 + r 1, by
      simp [Fintype.linearCombination_apply, Fin.sum_univ_two]; ring⟩

@[simp]
theorem coe_kerRetraction (r : Fin 2 → QuadraticAlgebra ℤ (-5) 0) :
    (kerRetraction r : QuadraticAlgebra ℤ (-5) 0) = (1 + ω) * r 0 + (ω - 1) * r 1 := by
  simp [kerRetraction, Fintype.linearCombination_apply, Fin.sum_univ_two, mul_comm]

theorem prod_comp_coprod :
    (retraction.prod kerRetraction) ∘ₗ (inclusion.coprod kerInclusion) = LinearMap.id := by
  refine LinearMap.ext fun ⟨a, b⟩ ↦ Prod.ext (Subtype.ext (eq_of_two_mul_eq ?_))
    (Subtype.ext (eq_of_two_mul_eq ?_)) <;>
    simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.coe_prod,
      Function.prod_apply, LinearMap.id_coe, id_eq, map_add, Prod.fst_add, Prod.snd_add,
      Submodule.coe_add, coe_retraction, coe_kerRetraction, kerInclusion_zero, kerInclusion_one]
  · linear_combination 2 * two_mul_inclusion_zero a + 2 * two_mul_inclusion_one b +
      (1 + ω) * two_mul_inclusion_one a - (a : QuadraticAlgebra ℤ (-5) 0) * omega_mul_omega
  · linear_combination (1 + ω) * two_mul_inclusion_zero a + (1 + ω) * two_mul_inclusion_one b +
      (ω - 1) * two_mul_inclusion_one a - (b : QuadraticAlgebra ℤ (-5) 0) * omega_mul_omega

theorem coprod_comp_prod :
    (inclusion.coprod kerInclusion) ∘ₗ (retraction.prod kerRetraction) = LinearMap.id := by
  refine LinearMap.ext fun r ↦ funext fun i ↦ eq_of_two_mul_eq ?_
  fin_cases i <;>
    simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.coe_prod,
      Function.prod_apply, LinearMap.id_coe, id_eq, Pi.add_apply, kerInclusion_zero,
      kerInclusion_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · linear_combination two_mul_inclusion_zero (retraction r) +
      two_mul_inclusion_one (kerRetraction r) + (ω - 1) * coe_retraction r -
      (1 + ω) * coe_kerRetraction r - r 0 * omega_mul_omega
  · linear_combination two_mul_inclusion_one (retraction r) - (1 + ω) * coe_retraction r +
      2 * coe_kerRetraction r - r 1 * omega_mul_omega

/-- **`A² ≃ 𝔭 × 𝔭`**: `r ↦ (π r, ρ r)`, with inverse `(a, b) ↦ ι(a) + (-b (1 + √-5) / 2, b)`. -/
noncomputable def prodEquiv :
    (Fin 2 → QuadraticAlgebra ℤ (-5) 0) ≃ₗ[QuadraticAlgebra ℤ (-5) 0]
      primeAboveTwo × primeAboveTwo :=
  .ofLinearMap _ _ prod_comp_coprod coprod_comp_prod

@[simp]
theorem prodEquiv_apply (r : Fin 2 → QuadraticAlgebra ℤ (-5) 0) :
    prodEquiv r = (retraction r, kerRetraction r) :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (x : primeAboveTwo × primeAboveTwo) :
    prodEquiv.symm x = inclusion x.1 + kerInclusion x.2 :=
  (rfl)

/-! ### The reduced class `[𝔭] - [A]` -/

/-- `2 ([𝔭] - [A]) = 0`, from `𝔭 × 𝔭 ≃ A²`. -/
theorem two_nsmul_classOf : 2 • classOf (QuadraticAlgebra ℤ (-5) 0) primeAboveTwo 1 = 0 := by
  rw [two_nsmul, ← classOf_prod, ← classOf_congr prodEquiv, classOf_free]

/-- `[𝔭] - [A] ≠ 0`, since `𝔭` is not principal. -/
theorem classOf_ne_zero : classOf (QuadraticAlgebra ℤ (-5) 0) primeAboveTwo 1 ≠ 0 := by
  rw [Ne, classOf_ideal_eq_zero_iff_isPrincipal ne_bot]
  exact not_isPrincipal

/-- **The reduced class `[𝔭] - [A]` has order two** in projective `K₀(ℤ[√-5])`. -/
theorem addOrderOf_classOf :
    addOrderOf (classOf (QuadraticAlgebra ℤ (-5) 0) primeAboveTwo 1) = 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  addOrderOf_eq_prime two_nsmul_classOf classOf_ne_zero

/-- **`[𝔭] - [A]` is invisible locally**: it maps to zero in projective `K₀` of every commutative
local ring `B` receiving `ℤ[√-5]`. There every finitely generated projective module is free, so
`K₀(B) ≃ ℤ` is torsion-free, while `[𝔭] - [A]` is `2`-torsion. -/
theorem map_classOf_eq_zero_of_isLocalRing {B : Type} [CommRing B] [IsLocalRing B]
    (f : QuadraticAlgebra ℤ (-5) 0 →+* B) :
    SplitK0.map.{0, 0} f.finiteProjectiveModulesExtendScalars
      (classOf (QuadraticAlgebra ℤ (-5) 0) primeAboveTwo 1) = 0 := by
  let e := rankEquiv B fun P ↦
    have : Module.Free B P.obj := Module.free_of_flat_of_isLocalRing
    inferInstance
  have h := congrArg e (congrArg (SplitK0.map.{0, 0} f.finiteProjectiveModulesExtendScalars)
    two_nsmul_classOf)
  rw [map_nsmul, map_nsmul, map_zero, map_zero, nsmul_eq_mul] at h
  rw [← e.map_eq_zero_iff]
  simpa using h

/-- `[𝔭] - [A]` maps to zero in projective `K₀` of the localization of `ℤ[√-5]` at every prime. -/
theorem map_classOf_localization_eq_zero (q : Ideal (QuadraticAlgebra ℤ (-5) 0)) [q.IsPrime] :
    SplitK0.map.{0, 0} (algebraMap _ (Localization.AtPrime q)).finiteProjectiveModulesExtendScalars
      (classOf (QuadraticAlgebra ℤ (-5) 0) primeAboveTwo 1) = 0 :=
  map_classOf_eq_zero_of_isLocalRing _

end primeAboveTwo

end TauCeti.NumberField.SqrtNegFive
