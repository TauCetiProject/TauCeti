/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# The Huber pair `A⟨X⟩_T`

Let `(A, A⁺)` be a Huber pair and `T = (T₁, …, Tₖ)` a weight family of subsets of `A`. Wedhorn
(Remark and Definition 8.41) makes the weighted restricted power-series ring `A⟨X⟩_T` into a Huber
pair: the series all of whose coefficients satisfy `aν ∈ Tν · A⁺`,

```text
A⁺⟨X⟩_T = { ∑ aν Xν ∈ A⟨X⟩_T | aν ∈ Tν · A⁺ for every ν },
```

form a subring (`TauCeti.Huber.weightedSubring`), and its integral closure in `A⟨X⟩_T` is a ring
of integral elements. Wedhorn takes this pair as the source of the quotient mappings that present
morphisms of Huber pairs topologically of finite type (Definition 8.42).

The subring `A⁺⟨X⟩_T` is open since `A⁺` is, and it consists of power-bounded elements although
`A⁺` need not be bounded: a series in it is a polynomial with coefficients in `Tν · A⁺` plus a
series in the bounded ring of definition `A₀⟨X⟩_T`.

The plus ring is the smallest closed, integrally closed subring of `A⟨X⟩_T` containing the
constants from `A⁺` and the weighted variables `t Xᵢ` with `t ∈ Tᵢ`. Consequently a continuous
ring homomorphism out of `A⟨X⟩_T` into a Huber pair `(B, B⁺)` is a morphism of Huber pairs as soon
as it carries those generators into `B⁺`.

## Main definitions

* `TauCeti.Huber.Pair.weighted`: the Huber pair `(A⟨X⟩_T, A⟨X⟩_T⁺)`, whose plus ring is the
  integral closure of `A⁺⟨X⟩_T`.
* `TauCeti.Huber.Pair.weightedHom`: the structure map `(A, A⁺) → (A⟨X⟩_T, A⟨X⟩_T⁺)`, the constant
  series, as a morphism of Huber pairs.

## Main results

* `TauCeti.Huber.exists_mvPolynomial_sub_mem_weightedNhd_of_mem_weightedSubring`: a series of
  `R⟨X⟩_T` is approximated by polynomials whose coefficients meet the `R` bound.
* `TauCeti.Huber.weightedSubring_le_powerBoundedSubring`: for a Huber ring `A` and a subring
  `R ⊆ A°`, every series with coefficients in `Tν · R` is power-bounded in `A⟨X⟩_T`.
* `TauCeti.Huber.Pair.weightedSubring_le_weighted_plus`,
  `TauCeti.Huber.Pair.weightedC_mem_weighted_plus` and
  `TauCeti.Huber.Pair.weightedC_mul_weightedX_mem_weighted_plus`: the plus ring contains
  `A⁺⟨X⟩_T`, the constants from `A⁺` and the weighted variables `t Xᵢ`.
* `TauCeti.Huber.Pair.weighted_plus_le`: it is the smallest closed, integrally closed subring
  containing those generators.
* `TauCeti.Huber.Pair.weighted_plus_le_comap`: a continuous ring homomorphism out of `A⟨X⟩_T`
  sending the generators into a ring of integral elements `B⁺` sends the whole plus ring into `B⁺`.
* `TauCeti.Huber.PairOfDefinition.weighted_ringOfDefinition_le_weighted_plus`: the ring of
  definition `A₀⟨X⟩_T` lies in the plus ring when `A₀ ⊆ A⁺`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 5.48 for
  `A⟨X⟩_T` and Remark and Definition 8.41 for its plus ring.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] {T : Fin k → Set A}
  (hT : IsWeightFamily T)

/-! ### Truncation and generation -/

section Nonarchimedean

variable [NonarchimedeanRing A]

/-- **Truncating a series of `R⟨X⟩_T`**: for every open subgroup `U` of `A`, a series all of whose
coefficients meet the `R` bound differs by an element of `U⟨X⟩` from a polynomial whose
coefficients still meet the `R` bound. Compare
`TauCeti.Huber.exists_mvPolynomial_forall_coeff_sub_mem`, which approximates any restricted series
but says nothing about the coefficients of the polynomial. -/
theorem exists_mvPolynomial_sub_mem_weightedNhd_of_mem_weightedSubring {R : Subring A}
    {f : weightedRestrictedSubring T hT} (hf : f ∈ weightedSubring T hT R) (U : OpenAddSubgroup A) :
    ∃ p : MvPolynomial (Fin k) A, (∀ ν, p.coeff ν ∈ weightMul T ν R.toAddSubgroup) ∧
      f - weightedPolynomialHom T hT p ∈ weightedNhd T hT U.toAddSubgroup := by
  classical
  -- truncate `f` at the finitely many indices where its coefficient escapes `Tν · U`
  have hbad := (mem_weightedRestrictedSubring.mp f.2).finite_coeff_notMem U
  refine ⟨MvPowerSeries.truncFinset A hbad.toFinset (f : MvPowerSeries (Fin k) A),
    fun ν ↦ ?_, mem_weightedNhd.mpr fun ν ↦ ?_⟩
  · rw [MvPowerSeries.coeff_truncFinset]
    split_ifs
    · exact mem_weightedNhd.mp (mem_weightedSubring.mp hf) ν
    · exact zero_mem _
  · rw [AddSubgroupClass.coe_sub, coe_weightedPolynomialHom, map_sub, MvPolynomial.coeff_coe,
      MvPowerSeries.coeff_truncFinset]
    split_ifs with hν
    · simp
    · simpa using not_not.mp fun h ↦ hν (hbad.mem_toFinset.mpr h)

/-- A subring of `A⟨X⟩_T` containing every weighted variable `t Xᵢ` with `t ∈ Tᵢ` contains every
weighted monomial `t Xν` with `t ∈ Tν`. -/
private theorem weightedPolynomialHom_monomial_mem {B : Subring (weightedRestrictedSubring T hT)}
    (hX : ∀ i, ∀ t ∈ T i, weightedC T hT t * weightedX T hT i ∈ B) (ν : Fin k →₀ ℕ) :
    ∀ t ∈ weightPow T ν, weightedPolynomialHom T hT (MvPolynomial.monomial ν t) ∈ B := by
  induction ν using Finsupp.induction_linear with
  | zero =>
    intro t ht
    obtain rfl : t = 1 := by simpa using ht
    simp
  | add μ ν hμ hν =>
    intro t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp (weightPow_add T μ ν ▸ ht)
    rw [← MvPolynomial.monomial_mul_monomial, map_mul]
    exact mul_mem (hμ a ha) (hν b hb)
  | single i m =>
    rw [weightPow_single]
    induction m with
    | zero =>
      intro t ht
      obtain rfl : t = 1 := by simpa using ht
      simp
    | succ m ih =>
      intro t ht
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp (pow_succ (T i) m ▸ ht)
      rw [Finsupp.single_add, ← MvPolynomial.monomial_mul_monomial, map_mul,
        ← MvPolynomial.C_mul_X_eq_monomial, map_mul, weightedPolynomialHom_C,
        weightedPolynomialHom_X]
      exact mul_mem (ih a ha) (hX i b hb)

/-- A subring of `A⟨X⟩_T` containing the constants from `R` and every weighted monomial `t Xν`
with `t ∈ Tν` contains every monomial `a Xν` with `a ∈ Tν · R`. -/
private theorem weightedPolynomialHom_monomial_mem_of_mem_weightMul
    {Q : Subring (weightedRestrictedSubring T hT)} {R : Subring A}
    (hC : ∀ a ∈ R, weightedC T hT a ∈ Q)
    (hmon : ∀ ν, ∀ t ∈ weightPow T ν, weightedPolynomialHom T hT (MvPolynomial.monomial ν t) ∈ Q)
    {ν : Fin k →₀ ℕ} {a : A} (ha : a ∈ weightMul T ν R.toAddSubgroup) :
    weightedPolynomialHom T hT (MvPolynomial.monomial ν a) ∈ Q := by
  rw [weightMul_def] at ha
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.mp hx
    rw [mul_comm, ← MvPolynomial.C_mul_monomial, map_mul, weightedPolynomialHom_C]
    exact mul_mem (hC u hu) (hmon ν t ht)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, map_neg]; exact neg_mem hx

end Nonarchimedean

variable [IsTopologicalRing A] [IsHuberRing A]

/-! ### Power-boundedness of `R⟨X⟩_T` -/

/-- **A series with coefficients in `Tν · R` is power-bounded** in `A⟨X⟩_T`, for a subring
`R ⊆ A°` of a Huber ring `A`. This holds although `R` need not be bounded. -/
theorem weightedSubring_le_powerBoundedSubring {R : Subring A} (hR : R ≤ powerBoundedSubring A) :
    weightedSubring T hT R ≤ powerBoundedSubring (weightedRestrictedSubring T hT) := by
  intro f hf
  -- split `f` into a polynomial head and a tail in the bounded ring of definition `A₀⟨X⟩_T`
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  obtain ⟨p, hp, hfp⟩ := exists_mvPolynomial_sub_mem_weightedNhd_of_mem_weightedSubring hT hf
    ⟨P.ringOfDefinition.toAddSubgroup, P.isOpen_ringOfDefinition⟩
  rw [← add_sub_cancel (weightedPolynomialHom T hT p) f]
  refine add_mem ?_ ((P.weighted hT).le_powerBoundedSubring ?_)
  · -- the head is a sum of monomials whose coefficients meet the `R` bound
    rw [p.as_sum, map_sum]
    exact sum_mem fun ν _ ↦ weightedPolynomialHom_monomial_mem_of_mem_weightMul hT
      (fun a ha ↦ mem_powerBoundedSubring.mpr
        (isPowerBounded_weightedC hT (mem_powerBoundedSubring.mp (hR ha))))
      (fun _ _ ht ↦ mem_powerBoundedSubring.mpr
        (isPowerBounded_weightedPolynomialHom_monomial hT ht)) (hp ν)
  · rwa [PairOfDefinition.weighted_ringOfDefinition,
      PairOfDefinition.mem_weightedRingOfDefinition]

namespace Pair

variable (S : Pair A)

/-- **The Huber pair `(A⟨X⟩_T, A⟨X⟩_T⁺)`** (Wedhorn, Remark and Definition 8.41): its plus ring is
the integral closure in `A⟨X⟩_T` of the subring `A⁺⟨X⟩_T` of series all of whose coefficients
satisfy `aν ∈ Tν · A⁺`. -/
noncomputable def weighted : Pair (weightedRestrictedSubring T hT) where
  plus := (integralClosure (weightedSubring T hT S.plus) (weightedRestrictedSubring T hT)).toSubring
  isRingOfIntegralElements := isRingOfIntegralElements_integralClosure
    (isOpen_weightedSubring hT S.isRingOfIntegralElements.isOpen)
    (weightedSubring_le_powerBoundedSubring hT S.isRingOfIntegralElements.le_powerBoundedSubring)

/-- The plus ring of `A⟨X⟩_T` is the integral closure of `A⁺⟨X⟩_T`. -/
@[simp]
theorem weighted_plus : (S.weighted hT).plus =
    (integralClosure (weightedSubring T hT S.plus) (weightedRestrictedSubring T hT)).toSubring :=
  (rfl)

/-- The plus ring of `A⟨X⟩_T` contains `A⁺⟨X⟩_T`. -/
theorem weightedSubring_le_weighted_plus : weightedSubring T hT S.plus ≤ (S.weighted hT).plus :=
  fun f hf ↦ algebraMap_mem (integralClosure (weightedSubring T hT S.plus) _) ⟨f, hf⟩

/-- The plus ring of `A⟨X⟩_T` contains the constants from `A⁺`. -/
theorem weightedC_mem_weighted_plus {a : A} (ha : a ∈ S.plus) :
    weightedC T hT a ∈ (S.weighted hT).plus :=
  S.weightedSubring_le_weighted_plus hT ((weightedC_mem_weightedSubring hT).mpr ha)

/-- The plus ring of `A⟨X⟩_T` contains the weighted variables `t Xᵢ` with `t ∈ Tᵢ`. -/
theorem weightedC_mul_weightedX_mem_weighted_plus {i : Fin k} {t : A} (ht : t ∈ T i) :
    weightedC T hT t * weightedX T hT i ∈ (S.weighted hT).plus := by
  refine S.weightedSubring_le_weighted_plus hT ?_
  rw [← weightedPolynomialHom_C, ← weightedPolynomialHom_X, ← map_mul,
    MvPolynomial.C_mul_X_eq_monomial, weightedPolynomialHom_monomial_mem_weightedSubring,
    ← mul_one t]
  exact mul_mem_weightMul T _ _ (by rwa [weightPow_single, pow_one]) S.plus.one_mem

/-- **`A⟨X⟩_T⁺` is the smallest closed, integrally closed subring of `A⟨X⟩_T` containing the
constants from `A⁺` and the weighted variables `t Xᵢ` with `t ∈ Tᵢ`.** -/
theorem weighted_plus_le {B : Subring (weightedRestrictedSubring T hT)}
    (hB : IsClosed (B : Set (weightedRestrictedSubring T hT)))
    [IsIntegrallyClosedIn B (weightedRestrictedSubring T hT)]
    (hC : ∀ a ∈ S.plus, weightedC T hT a ∈ B)
    (hX : ∀ i, ∀ t ∈ T i, weightedC T hT t * weightedX T hT i ∈ B) :
    (S.weighted hT).plus ≤ B := by
  rw [weighted_plus, Subring.integralClosure_subring_le_iff]
  -- every series of `A⁺⟨X⟩_T` is a limit of polynomials lying in `B`
  intro f hf
  refine hB.closure_subset_iff.mpr (fun g hg ↦ hg) (mem_closure_iff_nhds.mpr fun V hV ↦ ?_)
  rw [← nhds_translation_add_neg f, Filter.mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  obtain ⟨U, -, hU⟩ := (hasBasis_nhds_zero_weightedTopology hT).mem_iff.mp hW
  obtain ⟨p, hp, hfp⟩ := exists_mvPolynomial_sub_mem_weightedNhd_of_mem_weightedSubring hT hf U
  have hpf : weightedPolynomialHom T hT p - f ∈ weightedNhd T hT U.toAddSubgroup := by
    simpa only [neg_sub] using (weightedNhd T hT U.toAddSubgroup).neg_mem hfp
  refine ⟨weightedPolynomialHom T hT p,
    hWV (hU (by simpa only [SetLike.mem_coe, sub_eq_add_neg] using hpf)), ?_⟩
  rw [p.as_sum, map_sum]
  exact sum_mem fun ν _ ↦ weightedPolynomialHom_monomial_mem_of_mem_weightMul hT hC
    (weightedPolynomialHom_monomial_mem hT hX) (hp ν)

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]

/-- **Morphisms out of `(A⟨X⟩_T, A⟨X⟩_T⁺)`**: a continuous ring homomorphism `ψ : A⟨X⟩_T → B`
carrying the constants from `A⁺` and the weighted variables `t Xᵢ` (`t ∈ Tᵢ`) into the plus ring
of a Huber pair `(B, B⁺)` carries all of `A⟨X⟩_T⁺` into `B⁺`. -/
theorem weighted_plus_le_comap (S' : Pair B) {ψ : weightedRestrictedSubring T hT →+* B}
    (hψ : Continuous ψ) (hC : ∀ a ∈ S.plus, ψ (weightedC T hT a) ∈ S'.plus)
    (hX : ∀ i, ∀ t ∈ T i, ψ (weightedC T hT t * weightedX T hT i) ∈ S'.plus) :
    (S.weighted hT).plus ≤ S'.plus.comap ψ := by
  have := S'.isRingOfIntegralElements.isIntegrallyClosedIn
  exact S.weighted_plus_le hT
    ((S'.plus.toAddSubgroup.isClosed_of_isOpen S'.isRingOfIntegralElements.isOpen).preimage hψ)
    hC hX

/-- **The structure map `(A, A⁺) → (A⟨X⟩_T, A⟨X⟩_T⁺)`**, the constant-series embedding, as a
morphism of Huber pairs. -/
noncomputable def weightedHom : Hom S (S.weighted hT) where
  toRingHom := weightedC T hT
  continuous_toRingHom := continuous_weightedC hT
  map_mem_plus _ ha := S.weightedC_mem_weighted_plus hT ha

/-- The underlying ring homomorphism of the structure map is the constant-series embedding. -/
@[simp]
theorem Hom.toRingHom_weightedHom : (S.weightedHom hT).toRingHom = weightedC T hT := (rfl)

end Pair

/-- The ring of definition `A₀⟨X⟩_T` lies in the plus ring of `A⟨X⟩_T` when `A₀ ⊆ A⁺`, so the
pair of definition `(A₀⟨X⟩_T, I⟨X⟩_T)` is compatible with the Huber pair `(A⟨X⟩_T, A⟨X⟩_T⁺)`. -/
theorem PairOfDefinition.weighted_ringOfDefinition_le_weighted_plus (P : PairOfDefinition A)
    {S : Pair A} (hP : P.ringOfDefinition ≤ S.plus) :
    (P.weighted hT).ringOfDefinition ≤ (S.weighted hT).plus := by
  rw [PairOfDefinition.weighted_ringOfDefinition, PairOfDefinition.weightedRingOfDefinition_def]
  exact (weightedSubring_mono hP).trans (S.weightedSubring_le_weighted_plus hT)

end TauCeti.Huber
