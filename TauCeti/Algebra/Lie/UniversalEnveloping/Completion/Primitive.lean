/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Completion
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Bialgebra

import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Completed primitive elements of positively graded universal enveloping algebras

Let `L` be a Lie algebra over a commutative ring `R` equipped with a positive grading `ℒ` by
`(d : PositiveDegrees N)`. The canonical Lie homomorphism `ι : L → U(L)` carries the degree ideal
`d.degreeIdeal ℒ k` of elements strictly above cutoff `k` into
`(degreeFiltration ℒ d.degree _).ideal (k + 1)`, inducing compatible Lie homomorphisms
`truncatedLieToU` at every finite cutoff and a Lie homomorphism `completedLieToU` from the
completed Lie algebra `d.completedLie ℒ` into `completedEnveloping`.

Every element in the image of `completedLieToU` is completed primitive and lies in the first
completion ideal. When `ι : L → U(L)` is injective, `truncatedLieToU` and `completedLieToU` are
injective. Conversely, using the internal tensor-product grading of `U(L) ⊗[R] U(L)`, every
homogeneous component of a completed primitive element in `completedEnveloping` is an ordinary
primitive element of `U(L)`. Over a commutative `ℚ`-algebra `R : Type`, combining this
componentwise primitivity with `TauCeti.UniversalEnvelopingAlgebra.primitiveEquiv` identifies the
completed primitive Lie subalgebra of `completedEnveloping` with `d.completedLie ℒ`, without any
freeness or finite-rank hypothesis on `L`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.truncatedLieToU`: the Lie homomorphism from
  `d.truncatedLie ℒ k` to the order-`k` enveloping quotient.
* `TauCeti.UniversalEnvelopingAlgebra.completedLieToU`: the Lie homomorphism from
  `d.completedLie ℒ` to `completedEnveloping`.
* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv`: Lie isomorphism between
  `d.completedLie ℒ` and `completedPrimitiveLieSubalgebra` over a commutative `ℚ`-algebra.
* `TauCeti.UniversalEnvelopingAlgebra.completedLieExpEquiv`: equivalence between
  `d.completedLie ℒ` and the completed grouplike elements of `completedEnveloping` over a
  commutative `ℚ`-algebra.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.completedLieToU_injective`: `completedLieToU` is injective
  whenever `ι : L → U(L)` is injective.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLieToU`: every element in the
  image of `completedLieToU` is completed primitive.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_iff_mem_range_completedLieToU`: over a
  commutative `ℚ`-algebra `R : Type`, the completed primitive elements of `completedEnveloping`
  are precisely the image of `completedLieToU`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
-/

public section

open scoped TensorProduct DirectSum

namespace TauCeti.PositiveDegrees

/-- A positive grading has no pieces of negative degree. -/
theorem eq_bot_of_degree_neg {N R M : Type*} [AddCommMonoid N] [Semiring R] [AddCommMonoid M]
    [Module R M] (d : PositiveDegrees N) (ℒ : N → Submodule R M) [IsPositiveGrading d ℒ]
    (n : N) (hn : d.degree n < 0) : ℒ n = ⊥ :=
  d.eq_bot_of_degree_nonpos ℒ n hn.le

end TauCeti.PositiveDegrees

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section CommRing

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The canonical Lie map sends `d.degreeIdeal ℒ k` into filtration order `k + 1`. -/
theorem ι_mem_degreeFiltration_succ_of_mem_degreeIdeal {k : ℕ} {x : L}
    (hx : x ∈ d.degreeIdeal ℒ k) :
    ι R x ∈ (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1) := by
  rw [mem_degreeFiltration_ideal_iff]
  intro n hn
  rw [ι_apply, coe_decompose_mkAlgHom_ι,
    (d.mem_degreeIdeal_iff ℒ).mp hx n (by omega), map_zero]

/-- When `ι : L → U(L)` is injective, the preimage of filtration order `k + 1` is
`d.degreeIdeal ℒ k`. -/
theorem comap_degreeFiltration_succ_ι (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    (((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1)).restrictScalars
        R).comap (ι R : L →ₗ⁅R⁆ U).toLinearMap =
      (d.degreeIdeal ℒ k).toSubmodule := by
  rw [comap_degreeFiltration_ι ℒ d.degree (d.eq_bot_of_degree_neg ℒ) hι (k + 1)]
  ext x
  simp only [TauCeti.DirectSum.mem_degreeTail_iff, LieSubmodule.mem_toSubmodule,
    d.mem_degreeIdeal_iff ℒ]
  exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩

/-- The Lie homomorphism from the order-`k` Lie truncation to the order-`k` enveloping quotient. -/
noncomputable def truncatedLieToU (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆
      U ⧸ (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1) :=
  (d.degreeIdeal ℒ k).liftQ
    ((Ideal.Quotient.mkₐ R
      ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1))).toLieHom.comp
        (ι R))
    fun _ hx => by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using
        ι_mem_degreeFiltration_succ_of_mem_degreeIdeal d ℒ hx

@[simp]
theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    truncatedLieToU d ℒ k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk
        ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1)) (ι R x) := by
  simp [truncatedLieToU]

/-- When `ι : L → U(L)` is injective, every truncated Lie-to-enveloping map is injective. -/
theorem truncatedLieToU_injective (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    Function.Injective (truncatedLieToU d ℒ k) := by
  rw [truncatedLieToU, LieIdeal.liftQ_injective_iff]
  intro x hx
  have hmem :
      ι R x ∈ (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1) := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
  exact (comap_degreeFiltration_succ_ι d ℒ hι k).le hmem

/-- `truncatedLieToU` commutes with transitions between degree cutoffs. -/
theorem factor_truncatedLieToU {k l : ℕ} (h : k ≤ l) (z : d.truncatedLie ℒ l) :
    Ideal.Quotient.factor
        ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).antitone
          (Nat.add_le_add_right h 1))
        (truncatedLieToU d ℒ l z) =
      truncatedLieToU d ℒ k (LieIdeal.factor (d.degreeIdeal_antitone ℒ h) z) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ z
  simp [LieIdeal.mkQ_apply]

private noncomputable def completedLieToUFun (x : d.completedLie ℒ) :
    completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ) :=
  ⟨fun k => truncatedLieToU d ℒ k.unop
      (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k.unop x),
    ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).mem_completion_iff _).mpr
      fun {_ _} h => by rw [factor_truncatedLieToU d ℒ h, LieIdeal.factor_completionProjection]⟩

private theorem projection_completedLieToUFun (k : ℕ) (x : d.completedLie ℒ) :
    (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).projection k
        (completedLieToUFun d ℒ x) =
      truncatedLieToU d ℒ k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x) :=
  (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).projection_apply k _

/-- The canonical Lie homomorphism from the completed Lie algebra `d.completedLie ℒ` to
`completedEnveloping`. -/
noncomputable def completedLieToU :
    d.completedLie ℒ →ₗ⁅R⁆
      completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ) where
  toFun := completedLieToUFun d ℒ
  map_add' x y := by
    refine (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).completion_ext fun k => ?_
    simp only [map_add, projection_completedLieToUFun]
  map_smul' r x := by
    let 𝓕 := degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
    refine 𝓕.completion_ext fun k => ?_
    rw [RingHom.id_apply, projection_completedLieToUFun, map_smul, map_smul,
      ← 𝓕.projectionₐ_apply (R := R), map_smul, 𝓕.projectionₐ_apply,
      projection_completedLieToUFun]
  map_lie' {x y} := by
    refine (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).completion_ext fun k => ?_
    rw [projection_completedLieToUFun, LieHom.map_lie, LieHom.map_lie,
      LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket,
      map_sub, map_mul, map_mul, projection_completedLieToUFun, projection_completedLieToUFun]

/-- At cutoff `k`, `completedLieToU` applies `truncatedLieToU` to the `k`-th Lie projection. -/
@[simp]
theorem projection_completedLieToU (k : ℕ) (x : d.completedLie ℒ) :
    (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).projection k
        (completedLieToU d ℒ x) =
      truncatedLieToU d ℒ k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x) :=
  projection_completedLieToUFun d ℒ k x

/-- `completedLieToU` extends `ι : L → U(L)` along the two completion maps. -/
@[simp]
theorem completedLieToU_toCompletion (x : L) :
    completedLieToU d ℒ
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).toCompletion (ι R x) := by
  refine (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).completion_ext fun k => ?_
  simp [LieIdeal.mkQ_apply]

/-- Every element in the image of `completedLieToU` lies in the first completion ideal. -/
theorem completedLieToU_mem_completionIdeal_one (x : d.completedLie ℒ) :
    completedLieToU d ℒ x ∈
      (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).completionIdeal 1 := by
  rw [TauCeti.AlgFiltration.completionIdeal_succ, RingHom.mem_ker, projection_completedLieToU]
  have h0 :
      LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) 0 x = 0 :=
    Subsingleton.elim _ 0
  rw [h0, map_zero]

/-- When `ι : L → U(L)` is injective, `completedLieToU` is injective. -/
theorem completedLieToU_injective (hι : Function.Injective (ι R : L → U)) :
    Function.Injective (completedLieToU d ℒ) := by
  intro x y h
  refine LieIdeal.completion_ext _ _ fun k => ?_
  apply truncatedLieToU_injective d ℒ hι k
  simpa only [projection_completedLieToU] using
    congrArg ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).projection k) h

/-- Every element in the image of `completedLieToU` is completed primitive. -/
theorem isCompletedPrimitive_completedLieToU (x : d.completedLie ℒ) :
    IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) (completedLieToU d ℒ x) := by
  let 𝓕 := degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
  rw [isCompletedPrimitive_iff_includeCompletion]
  refine (𝓕.tensorProduct R 𝓕).completion_ext fun k => ?_
  obtain ⟨y, hy⟩ := (d.degreeIdeal ℒ k).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x)
  have hrep : 𝓕.projection k (completedLieToU d ℒ x) =
      𝓕.projection k (𝓕.toCompletion (ι R y)) := by
    simp only [𝓕, projection_completedLieToU, ← hy, LieIdeal.mkQ_apply, truncatedLieToU_mk,
      TauCeti.AlgFiltration.projection_toCompletion]
  have hprim := (isCompletedPrimitive_iff_includeCompletion ℒ d.degree
    (d.eq_bot_of_degree_neg ℒ)).mp
      (isCompletedPrimitive_toCompletion_ι ℒ d.degree (d.eq_bot_of_degree_neg ℒ) y)
  simpa only [𝓕, projection_completedCoproduct, map_add,
    TauCeti.AlgFiltration.projection_includeLeftCompletion,
    TauCeti.AlgFiltration.projection_includeRightCompletion, hrep] using
      congrArg ((𝓕.tensorProduct R 𝓕).projection k) hprim

/-! ### Homogeneous components of completed primitive elements -/

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
/-- Homogeneous enveloping pieces vanish outside the positive degree monoid. -/
theorem homogeneousSubmodule_eq_bot_of_not_mem_monoid {n : N} (hn : n ∉ d.monoid) :
    homogeneousSubmodule ℒ n = ⊥ := by
  rw [eq_bot_iff]
  refine (homogeneousSubmodule_le_iff ℒ n ⊥).mpr fun l hl => ?_
  rw [Submodule.mem_bot]
  by_cases hall : ∀ a ∈ l, a.1 ∈ d.monoid
  · refine (hn (hl ▸ list_sum_mem fun m hm => ?_)).elim
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact hall a ha
  · push Not at hall
    obtain ⟨a, hal, han⟩ := hall
    have ha0 : (a.2 : L) = 0 := by
      simpa only [IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) a.1 (Or.inl han),
        Submodule.mem_bot] using a.2.property
    exact List.prod_eq_zero <| List.mem_map.mpr ⟨a, hal, by simp [ha0]⟩

private noncomputable def projHomogeneous (n : N) : U →ₗ[R] homogeneousSubmodule ℒ n :=
  (_root_.DirectSum.component R N (fun m => homogeneousSubmodule ℒ m) n).comp
    (_root_.DirectSum.decomposeLinearEquiv (homogeneousSubmodule ℒ)).toLinearMap

private noncomputable def envelopingQuotientComponent (k : ℕ) (n : N) (hn : d.degree n ≤ k) :
    (U ⧸ (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1)) →ₗ[R]
      homogeneousSubmodule ℒ n :=
  ((((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1)).restrictScalars
      R).liftQ (projHomogeneous ℒ n) fun a ha =>
    LinearMap.mem_ker.mpr <| Subtype.ext <|
      (mem_degreeFiltration_ideal_iff ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).mp ha n
        (by omega)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R
      ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1))).symm.toLinearMap

@[simp]
private theorem envelopingQuotientComponent_mk (k : ℕ) (n : N) (hn : d.degree n ≤ k) (a : U) :
    envelopingQuotientComponent d ℒ k n hn
        (Ideal.Quotient.mk
          ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1)) a) =
      _root_.DirectSum.decompose (homogeneousSubmodule ℒ) a n := by
  simp only [envelopingQuotientComponent, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    Submodule.liftQ_apply]
  rfl

/-- The `n`-th homogeneous enveloping component of an element of `completedEnveloping`. -/
noncomputable def envelopingComponent (n : N) :
    completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ) →ₗ[R]
      homogeneousSubmodule ℒ n :=
  (envelopingQuotientComponent d ℒ (d.degree n).toNat n (Int.self_le_toNat _)).comp
    ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).projectionₐ
      (R := R) (d.degree n).toNat).toLinearMap

/-- Any representative at a cutoff `k ≥ d.degree n` computes `envelopingComponent`. -/
theorem envelopingComponent_eq_of_representative {n : N} {k : ℕ} (hn : d.degree n ≤ k)
    (u : completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) (a : U)
    (ha : Ideal.Quotient.mk
      ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1)) a =
        (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).projection k u) :
    envelopingComponent d ℒ n u =
      _root_.DirectSum.decompose (homogeneousSubmodule ℒ) a n := by
  let 𝓕 := degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
  have hle : (d.degree n).toNat ≤ k := by omega
  have hproj : 𝓕.projection (d.degree n).toNat u =
      Ideal.Quotient.mk (𝓕.ideal ((d.degree n).toNat + 1)) a := by
    rw [← 𝓕.factor_projection hle u, ← ha, Ideal.Quotient.factor_mk]
  simp only [envelopingComponent, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TauCeti.AlgFiltration.projectionₐ_apply, 𝓕] at hproj ⊢
  rw [hproj, envelopingQuotientComponent_mk]

/-- At cutoff `k`, every element of `completedEnveloping` is represented by the finite sum of its
homogeneous components in `d.cutoff k`. -/
theorem mk_sum_envelopingComponent (k : ℕ)
    (u : completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) :
    Ideal.Quotient.mk
        ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).ideal (k + 1))
        (∑ m ∈ (d.finite_cutoff k).toFinset, (envelopingComponent d ℒ m u : U)) =
      (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).projection k u := by
  classical
  let 𝓕 := degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (𝓕.projection k u)
  rw [← ha, Ideal.Quotient.eq, mem_degreeFiltration_ideal_iff]
  intro n hn
  have hnk : d.degree n ≤ k := by omega
  by_cases hP : n ∈ d.monoid
  · have hmem : n ∈ (d.finite_cutoff k).toFinset := by simp [hP, hnk]
    rw [_root_.DirectSum.decompose_sub, _root_.DirectSum.sub_apply, Submodule.coe_sub,
      _root_.DirectSum.decompose_sum, _root_.DirectSum.sum_apply, Submodule.coe_sum,
      Finset.sum_eq_single n]
    · rw [_root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ)
        (envelopingComponent d ℒ n u).property,
        envelopingComponent_eq_of_representative d ℒ hnk u a ha, sub_self]
    · intro m _ hmn
      exact _root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ)
        (envelopingComponent d ℒ m u).property hmn
    · exact fun h => (h hmem).elim
  · have hbot := homogeneousSubmodule_eq_bot_of_not_mem_monoid d ℒ hP
    exact (Submodule.mem_bot R).mp
      (hbot ▸ (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) _ n).property)

private def tensorGrading (p : N × N) : Submodule R (U ⊗[R] U) :=
  Submodule.map₂ (TensorProduct.mk R U U)
    (homogeneousSubmodule ℒ p.1) (homogeneousSubmodule ℒ p.2)

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem tensorGrading_eq_bot_of_not_mem {p : N × N}
    (hp : ¬ (p.1 ∈ d.monoid ∧ p.2 ∈ d.monoid)) :
    tensorGrading ℒ p = ⊥ := by
  rw [not_and_or] at hp
  rw [eq_bot_iff]
  refine Submodule.map₂_le.mpr fun u hu v hv => ?_
  rcases hp with hp1 | hp2
  · have hu0 : u = 0 := (Submodule.mem_bot R).mp
      (homogeneousSubmodule_eq_bot_of_not_mem_monoid d ℒ hp1 ▸ hu)
    simp [hu0]
  · have hv0 : v = 0 := (Submodule.mem_bot R).mp
      (homogeneousSubmodule_eq_bot_of_not_mem_monoid d ℒ hp2 ▸ hv)
    simp [hv0]

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem mul_mem_tensorGrading {p q : N × N} {x y : U ⊗[R] U}
    (hx : x ∈ tensorGrading ℒ p) (hy : y ∈ tensorGrading ℒ q) :
    x * y ∈ tensorGrading ℒ (p + q) := by
  have h₁ : tensorGrading ℒ p ≤
      (tensorGrading ℒ (p + q)).comap ((LinearMap.mul R (U ⊗[R] U)).flip y) := by
    refine Submodule.map₂_le.mpr fun u₁ hu₁ v₁ hv₁ => ?_
    rw [Submodule.mem_comap, LinearMap.flip_apply, LinearMap.mul_apply']
    have h₂ : tensorGrading ℒ q ≤
        (tensorGrading ℒ (p + q)).comap (LinearMap.mul R (U ⊗[R] U) (u₁ ⊗ₜ[R] v₁)) := by
      refine Submodule.map₂_le.mpr fun u₂ hu₂ v₂ hv₂ => ?_
      simp only [Submodule.mem_comap, TensorProduct.mk_apply, LinearMap.mul_apply',
        Algebra.TensorProduct.tmul_mul_tmul]
      exact Submodule.apply_mem_map₂ (TensorProduct.mk R U U)
        (SetLike.mul_mem_graded hu₁ hu₂) (SetLike.mul_mem_graded hv₁ hv₂)
    exact h₂ hy
  exact h₁ hx

private def tensorTotalDegree (m : N) : Submodule R (U ⊗[R] U) :=
  ⨆ p : {p : N × N // p.1 + p.2 = m}, tensorGrading ℒ p.1

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem mul_mem_tensorTotalDegree {m₁ m₂ : N} {x y : U ⊗[R] U}
    (hx : x ∈ tensorTotalDegree ℒ m₁) (hy : y ∈ tensorTotalDegree ℒ m₂) :
    x * y ∈ tensorTotalDegree ℒ (m₁ + m₂) := by
  rw [tensorTotalDegree] at hx hy
  refine Submodule.iSup_induction _
    (motive := fun x => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hx
    (fun p x hx => ?_) (by simp)
    (fun _ _ h₁ h₂ => by simpa [add_mul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _
    (motive := fun y => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hy
    (fun q y hy => ?_) (by simp)
    (fun _ _ h₁ h₂ => by simpa [mul_add] using add_mem h₁ h₂)
  have hpq : (p.1 + q.1).1 + (p.1 + q.1).2 = m₁ + m₂ := by
    calc p.1.1 + q.1.1 + (p.1.2 + q.1.2)
        = (p.1.1 + p.1.2) + (q.1.1 + q.1.2) := by abel
      _ = m₁ + m₂ := by rw [p.2, q.2]
  exact Submodule.mem_iSup_of_mem ⟨p.1 + q.1, hpq⟩ (mul_mem_tensorGrading ℒ hx hy)

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem comul_mem_tensorTotalDegree {m : N} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a ∈ tensorTotalDegree ℒ m := by
  have hle : homogeneousSubmodule ℒ m ≤
      (tensorTotalDegree ℒ m).comap (Bialgebra.comulAlgHom R U).toLinearMap := by
    clear ha a
    refine (homogeneousSubmodule_le_iff ℒ m _).mpr fun l hl => ?_
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply]
    subst m
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, map_one,
        Algebra.TensorProduct.one_def]
      exact Submodule.mem_iSup_of_mem ⟨(0, 0), add_zero 0⟩
        (Submodule.apply_mem_map₂ (TensorProduct.mk R U U)
          (SetLike.one_mem_graded (homogeneousSubmodule ℒ))
          (SetLike.one_mem_graded (homogeneousSubmodule ℒ)))
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul]
      refine mul_mem_tensorTotalDegree ℒ ?_ ih
      rw [Bialgebra.comulAlgHom_apply, comul_ι]
      refine add_mem ?_ ?_
      · exact Submodule.mem_iSup_of_mem ⟨(b.1, 0), add_zero b.1⟩
          (Submodule.apply_mem_map₂ (TensorProduct.mk R U U)
            (ι_mem_homogeneousSubmodule ℒ b.2.property)
            (SetLike.one_mem_graded (homogeneousSubmodule ℒ)))
      · exact Submodule.mem_iSup_of_mem ⟨(0, b.1), zero_add b.1⟩
          (Submodule.apply_mem_map₂ (TensorProduct.mk R U U)
            (SetLike.one_mem_graded (homogeneousSubmodule ℒ))
            (ι_mem_homogeneousSubmodule ℒ b.2.property))
  exact hle ha

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem primDefect_mem_tensorTotalDegree {m : N} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a - (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) ∈ tensorTotalDegree ℒ m := by
  refine sub_mem (comul_mem_tensorTotalDegree ℒ ha) (add_mem ?_ ?_)
  · exact Submodule.mem_iSup_of_mem ⟨(0, m), zero_add m⟩
      (Submodule.apply_mem_map₂ (TensorProduct.mk R U U)
        (SetLike.one_mem_graded (homogeneousSubmodule ℒ)) ha)
  · exact Submodule.mem_iSup_of_mem ⟨(m, 0), add_zero m⟩
      (Submodule.apply_mem_map₂ (TensorProduct.mk R U U) ha
        (SetLike.one_mem_graded (homogeneousSubmodule ℒ)))

omit [GradedLieAlgebra ℒ] in
private theorem decompose_eq_zero_of_mem_tensorTotalDegree
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] {m : N} {z : U ⊗[R] U}
    (hz : z ∈ tensorTotalDegree ℒ m) {p : N × N} (hp : p.1 + p.2 ≠ m) :
    (_root_.DirectSum.decompose (tensorGrading ℒ) z p : U ⊗[R] U) = 0 := by
  let K : Submodule R (U ⊗[R] U) := LinearMap.ker
    ((tensorGrading ℒ p).subtype.comp
      ((_root_.DirectSum.component R (N × N) (fun q => tensorGrading ℒ q) p).comp
        (_root_.DirectSum.decomposeLinearEquiv (tensorGrading ℒ)).toLinearMap))
  have hK : z ∈ K := by
    refine Submodule.iSup_induction _ (motive := fun w => w ∈ K) hz (fun q w hw => ?_)
      (zero_mem K) (fun _ _ h₁ h₂ => add_mem h₁ h₂)
    exact _root_.DirectSum.decompose_of_mem_ne (tensorGrading ℒ) hw (fun h => hp (h ▸ q.2))
  exact hK

private theorem decompose_eq_zero_of_mem_tensorProduct_ideal
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] {k : ℕ} {t : U ⊗[R] U}
    (ht : t ∈ ((degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).tensorProduct R
      (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ))).ideal (k + 1))
    {p : N × N} (hp : d.degree p.1 + d.degree p.2 ≤ k) :
    (_root_.DirectSum.decompose (tensorGrading ℒ) t p : U ⊗[R] U) = 0 := by
  let K : Submodule R (U ⊗[R] U) := LinearMap.ker
    ((tensorGrading ℒ p).subtype.comp
      ((_root_.DirectSum.component R (N × N) (fun q => tensorGrading ℒ q) p).comp
        (_root_.DirectSum.decomposeLinearEquiv (tensorGrading ℒ)).toLinearMap))
  rw [TauCeti.AlgFiltration.mem_tensorProduct_ideal_iff, tensorFiltrationTail_def] at ht
  have hK : t ∈ K := by
    refine Submodule.iSup_induction _ (motive := fun z => z ∈ K) ht (fun a z hz => ?_)
      (zero_mem K) (fun _ _ h₁ h₂ => add_mem h₁ h₂)
    refine Submodule.iSup_induction _ (motive := fun z => z ∈ K) hz (fun b z hz => ?_)
      (zero_mem K) (fun _ _ h₁ h₂ => add_mem h₁ h₂)
    refine Submodule.iSup_induction _ (motive := fun z => z ∈ K) hz (fun hab z hz => ?_)
      (zero_mem K) (fun _ _ h₁ h₂ => add_mem h₁ h₂)
    refine Submodule.map₂_le.mpr (fun u hu v hv => ?_) hz
    rw [Submodule.restrictScalars_mem, degreeFiltration_ideal,
      ← Submodule.restrictScalars_mem R, TauCeti.GradedAlgebra.degreeIdeal_restrictScalars,
      TauCeti.DirectSum.degreeTail_def] at hu hv
    refine Submodule.iSup_induction _ (motive := fun u => TensorProduct.mk R U U u v ∈ K) hu
      (fun i u hu => ?_) (by simp [zero_mem K])
      (fun _ _ h₁ h₂ => by
        simpa only [TensorProduct.mk_apply, TensorProduct.add_tmul] using add_mem h₁ h₂)
    refine Submodule.iSup_induction _ (motive := fun u => TensorProduct.mk R U U u v ∈ K) hu
      (fun hi u hu => ?_) (by simp [zero_mem K])
      (fun _ _ h₁ h₂ => by
        simpa only [TensorProduct.mk_apply, TensorProduct.add_tmul] using add_mem h₁ h₂)
    refine Submodule.iSup_induction _ (motive := fun v => TensorProduct.mk R U U u v ∈ K) hv
      (fun j v hv => ?_) (by simp [zero_mem K])
      (fun _ _ h₁ h₂ => by
        simpa only [TensorProduct.mk_apply, TensorProduct.tmul_add] using add_mem h₁ h₂)
    refine Submodule.iSup_induction _ (motive := fun v => TensorProduct.mk R U U u v ∈ K) hv
      (fun hj v hv => ?_) (by simp [zero_mem K])
      (fun _ _ h₁ h₂ => by
        simpa only [TensorProduct.mk_apply, TensorProduct.tmul_add] using add_mem h₁ h₂)
    have hijp : (i, j) ≠ p := by
      intro heq
      rw [Prod.ext_iff] at heq
      rcases heq with ⟨rfl, rfl⟩
      omega
    exact _root_.DirectSum.decompose_of_mem_ne (tensorGrading ℒ)
      (Submodule.apply_mem_map₂ (TensorProduct.mk R U U) hu hv) hijp
  exact hK

private theorem isPrimitiveElem_envelopingComponent_of_mem_monoid
    {u : completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)}
    (hu : IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u)
    {n : N} (hnP : n ∈ d.monoid) :
    Bialgebra.IsPrimitiveElem R (envelopingComponent d ℒ n u : U) := by
  classical
  let 𝓕 := degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
  let _ : _root_.DirectSum.Decomposition (tensorGrading ℒ) :=
    (_root_.DirectSum.IsInternal.tensorProduct _ _
      (isInternal_homogeneousSubmodule ℒ)
      (isInternal_homogeneousSubmodule ℒ)).chooseDecomposition
  let k := (d.degree n).toNat
  let s := (d.finite_cutoff k).toFinset
  let a : U := ∑ m ∈ s, (envelopingComponent d ℒ m u : U)
  have ha : Ideal.Quotient.mk (𝓕.ideal (k + 1)) a = 𝓕.projection k u :=
    mk_sum_envelopingComponent d ℒ k u
  have h1 : Ideal.Quotient.mk (𝓕.ideal (k + 1)) (1 : U) = 𝓕.projection k 1 :=
    (map_one (𝓕.projection k)).symm
  have hmem : Coalgebra.comul (R := R) a - (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) ∈
      (𝓕.tensorProduct R 𝓕).ideal (k + 1) := by
    have hprim := (isCompletedPrimitive_iff ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).mp hu
    have hproj := congrArg ((𝓕.tensorProduct R 𝓕).projection k) hprim
    rw [projection_completedCoproduct, ← ha, Ideal.quotient_map_mkₐ,
      Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply, map_add,
      𝓕.projection_completedTensor_of_representatives R 𝓕 k u 1 a 1 ha h1,
      𝓕.projection_completedTensor_of_representatives R 𝓕 k 1 u 1 a h1 ha,
      add_comm (Ideal.Quotient.mk _ (a ⊗ₜ[R] 1)), ← map_add, Ideal.Quotient.eq] at hproj
    exact hproj
  let δ : U →ₗ[R] U ⊗[R] U :=
    Coalgebra.comul - ((TensorProduct.mk R U U 1) + (TensorProduct.mk R U U).flip 1)
  have hδ (b : U) : δ b = Coalgebra.comul (R := R) b - (1 ⊗ₜ[R] b + b ⊗ₜ[R] 1) := rfl
  refine Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr (sub_eq_zero.mp ?_)
  apply (_root_.DirectSum.decomposeLinearEquiv (tensorGrading ℒ)).injective
  rw [map_zero]
  ext p
  simp only [_root_.DirectSum.decomposeLinearEquiv_apply, _root_.DirectSum.zero_apply,
    ZeroMemClass.coe_zero]
  by_cases hpn : p.1 + p.2 = n
  · by_cases hpP : p.1 ∈ d.monoid ∧ p.2 ∈ d.monoid
    · have hpk : d.degree p.1 + d.degree p.2 ≤ k := by
        rw [← map_add, hpn]
        exact Int.self_le_toNat _
      have h0 := decompose_eq_zero_of_mem_tensorProduct_ideal d ℒ hmem hpk
      rw [← hδ a, map_sum δ _ s, _root_.DirectSum.decompose_sum, _root_.DirectSum.sum_apply,
        Submodule.coe_sum, Finset.sum_eq_single n] at h0
      · exact h0
      · intro m _ hmn
        exact decompose_eq_zero_of_mem_tensorTotalDegree ℒ
          (primDefect_mem_tensorTotalDegree ℒ (envelopingComponent d ℒ m u).property)
          (hpn.trans_ne hmn.symm)
      · exact fun hns => (hns (by simp [s, k, hnP])).elim
    · have hbot := tensorGrading_eq_bot_of_not_mem d ℒ hpP
      exact (Submodule.mem_bot R).mp
        (hbot ▸ (_root_.DirectSum.decompose (tensorGrading ℒ) _ p).property)
  · exact decompose_eq_zero_of_mem_tensorTotalDegree ℒ
      (primDefect_mem_tensorTotalDegree ℒ (envelopingComponent d ℒ n u).property) hpn

/-- Every homogeneous enveloping component of a completed primitive element is an ordinary
primitive element of `U(L)`. -/
theorem isPrimitiveElem_envelopingComponent
    {u : completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)}
    (hu : IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u) (n : N) :
    Bialgebra.IsPrimitiveElem R (envelopingComponent d ℒ n u : U) := by
  by_cases hnP : n ∈ d.monoid
  · exact isPrimitiveElem_envelopingComponent_of_mem_monoid d ℒ hu hnP
  · have hbot := homogeneousSubmodule_eq_bot_of_not_mem_monoid d ℒ hnP
    have hc0 : (envelopingComponent d ℒ n u : U) = 0 :=
      (Submodule.mem_bot R).mp (hbot ▸ (envelopingComponent d ℒ n u).property)
    rw [hc0]
    exact (Coalgebra.skewPrimitive R (1 : U) 1).zero_mem

end CommRing

/-! ### Identification of completed primitive elements over `ℚ`-algebras -/

section Rational

universe u v

variable {N : Type u} {R : Type} {L : Type v} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` is injective without a freeness
hypothesis. -/
theorem completedLieToU_injective_of_algebra_rat :
    Function.Injective (completedLieToU d ℒ) :=
  completedLieToU_injective d ℒ (ι_injective_of_algebra_rat R L)

/-- Over a commutative `ℚ`-algebra `R : Type`, an element of `completedEnveloping` is completed
primitive if and only if it lies in the image of `completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU
    (u : completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) :
    IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u ↔
      u ∈ Set.range (completedLieToU d ℒ) := by
  refine ⟨fun hu => ?_, ?_⟩
  · let _ := d.lieRingPi ℒ
    let _ := d.lieAlgebraPi ℒ
    let y : N → L := fun n =>
      (primitiveEquiv R L).symm
        ⟨(envelopingComponent d ℒ n u : U), isPrimitiveElem_envelopingComponent d ℒ hu n⟩
    let x : ∀ n, ℒ n := fun n => _root_.DirectSum.decompose ℒ (y n) n
    have hx (n : N) : ι R (x n : L) = (envelopingComponent d ℒ n u : U) := by
      have hy : ι R (y n) = (envelopingComponent d ℒ n u : U) :=
        ι_primitiveEquiv_symm R L _
      calc ι R (x n : L)
          = (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) (ι R (y n)) n : U) := by
              rw [ι_apply (R := R) (x := y n), coe_decompose_mkAlgHom_ι]
        _ = (_root_.DirectSum.decompose (homogeneousSubmodule ℒ)
              (envelopingComponent d ℒ n u : U) n : U) := by rw [hy]
        _ = (envelopingComponent d ℒ n u : U) :=
              _root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ)
                (envelopingComponent d ℒ n u).property
    refine ⟨(d.completionLieEquivPi ℒ).symm x,
      (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).completion_ext fun k => ?_⟩
    rw [projection_completedLieToU, d.completionProjection_completionLieEquivPi_symm ℒ x k,
      LieIdeal.mkQ_apply, truncatedLieToU_mk, map_sum]
    simp_rw [hx]
    exact mk_sum_envelopingComponent d ℒ k u
  · rintro ⟨x, rfl⟩
    exact isCompletedPrimitive_completedLieToU d ℒ x

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` identifies `d.completedLie ℒ`
with the Lie subalgebra of completed primitive elements in `completedEnveloping`. -/
noncomputable def completedPrimitiveLieEquiv :
    d.completedLie ℒ ≃ₗ⁅R⁆
      completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ) :=
  LieEquiv.ofBijective
    { toLinearMap := (completedLieToU d ℒ).toLinearMap.codRestrict
        (completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).toSubmodule
        fun x => (mem_completedPrimitiveLieSubalgebra_iff _ _ _).mpr
          (isCompletedPrimitive_completedLieToU d ℒ x)
      map_lie' := fun {x y} => Subtype.ext ((completedLieToU d ℒ).map_lie x y) }
    ⟨fun _ _ h => completedLieToU_injective_of_algebra_rat d ℒ (congrArg Subtype.val h),
      fun u => by
        obtain ⟨x, hx⟩ :=
          (isCompletedPrimitive_iff_mem_range_completedLieToU d ℒ u.1).mp
            ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp u.2)
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp]
theorem coe_completedPrimitiveLieEquiv_apply (x : d.completedLie ℒ) :
    (completedPrimitiveLieEquiv d ℒ x :
      completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) =
      completedLieToU d ℒ x :=
  (rfl)

@[simp]
theorem completedLieToU_completedPrimitiveLieEquiv_symm
    (u : completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) :
    completedLieToU d ℒ ((completedPrimitiveLieEquiv d ℒ).symm u) =
      (u : completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) :=
  congrArg Subtype.val ((completedPrimitiveLieEquiv d ℒ).apply_symm_apply u)

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedExp ∘ completedLieToU` identifies
`d.completedLie ℒ` with the completed grouplike elements of `completedEnveloping`. -/
noncomputable def completedLieExpEquiv :
    d.completedLie ℒ ≃
      {u : completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ) //
        IsCompletedGroupLike ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u} where
  toFun x :=
    completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)
      ⟨⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩,
        isCompletedPrimitive_completedLieToU d ℒ x⟩
  invFun u :=
    let p := (completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)).symm u
    (completedPrimitiveLieEquiv d ℒ).symm
      ⟨p.1.1, (mem_completedPrimitiveLieSubalgebra_iff _ _ _).mpr p.2⟩
  left_inv x := by
    simp only [Equiv.symm_apply_apply]
    have h : (⟨completedLieToU d ℒ x,
        (mem_completedPrimitiveLieSubalgebra_iff _ _ _).mpr
          (isCompletedPrimitive_completedLieToU d ℒ x)⟩ :
        completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) =
        completedPrimitiveLieEquiv d ℒ x :=
      Subtype.ext (coe_completedPrimitiveLieEquiv_apply d ℒ x).symm
    rw [h]
    exact (completedPrimitiveLieEquiv d ℒ).symm_apply_apply x
  right_inv u :=
    let p := (completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)).symm u
    let hp : completedLieToU d ℒ
        ((completedPrimitiveLieEquiv d ℒ).symm
          ⟨p.1.1, (mem_completedPrimitiveLieSubalgebra_iff _ _ _).mpr p.2⟩) = p.1.1 :=
      completedLieToU_completedPrimitiveLieEquiv_symm d ℒ _
    let hsub :
        (⟨⟨completedLieToU d ℒ
              ((completedPrimitiveLieEquiv d ℒ).symm
                ⟨p.1.1, (mem_completedPrimitiveLieSubalgebra_iff _ _ _).mpr p.2⟩),
            completedLieToU_mem_completionIdeal_one d ℒ _⟩,
          isCompletedPrimitive_completedLieToU d ℒ _⟩ :
          {x : (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).completionIdeal 1 //
            IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) x.1}) = p :=
      Subtype.ext (Subtype.ext hp)
    (congrArg (completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)) hsub).trans
      ((completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)).apply_symm_apply u)

@[simp]
theorem coe_completedLieExpEquiv_apply (x : d.completedLie ℒ) :
    (completedLieExpEquiv d ℒ x :
      completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) =
      (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).completedExp
        ⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩ :=
  coe_completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) _

@[simp]
theorem completedLieToU_completedLieExpEquiv_symm
    (u : {u : completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ) //
      IsCompletedGroupLike ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u}) :
    completedLieToU d ℒ ((completedLieExpEquiv d ℒ).symm u) =
      (degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).completedLog
        ⟨u.1, u.2.sub_one_mem_completionIdeal_one ℒ d.degree
          (hpos := d.eq_bot_of_degree_nonpos ℒ)⟩ := by
  rw [completedLieExpEquiv, Equiv.coe_fn_symm_mk,
    completedLieToU_completedPrimitiveLieEquiv_symm]
  exact coe_completedPrimitiveExpEquiv_symm ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) u

end Rational

end TauCeti.UniversalEnvelopingAlgebra
