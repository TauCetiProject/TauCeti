/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

/-!
# Power-bounded elements of `A⟨X₁, …, Xₖ⟩_T`

The variables `Xᵢ` and the power-bounded constants of a weighted restricted power-series ring are
power-bounded in it. Together they exhibit the image of `A°[X₁, …, Xₖ]` inside `A⟨X₁, …, Xₖ⟩°`,
the plus ring `TauCeti.ValuationSpectrum.closedPolydisc` designates for the closed polydisc; they
exhibit elements of that plus ring rather than determining it.

Neither result needs the trivial weight family. The constant result holds for every weight family;
the variable result is the case `a = 1` of the power-boundedness of `a Xᵢ` for `a ∈ T i`, so it
needs only `1 ∈ T i`, which the trivial family satisfies.

More generally every weighted monomial `t Xν` with `t ∈ Tν` is power-bounded. This is what puts
the subring whose integral closure is the plus ring of the Huber pair `A⟨X⟩_T`
(`TauCeti.Huber.Pair.weighted`) inside `A⟨X⟩_T°`.

## Main results

* `TauCeti.Huber.isPowerBounded_weightedPolynomialHom_monomial`: the weighted monomial `t Xν` is
  power-bounded whenever `t ∈ Tν`.
* `TauCeti.Huber.isPowerBounded_weightedC_mul_weightedX`: in particular the weighted variable
  `a Xᵢ` is power-bounded whenever `a ∈ T i`.
* `TauCeti.Huber.isPowerBounded_weightedX`: the variable `Xᵢ` is power-bounded whenever `1 ∈ T i`,
  with `TauCeti.Huber.isPowerBounded_weightedX_one_weight` the trivial-weight case the closed
  polydisc uses.
* `TauCeti.Huber.isPowerBounded_weightedC`: a constant power-bounded in `A` is power-bounded in
  `A⟨X⟩_T`, for every weight family.
* `TauCeti.Huber.closure_weightedC_weightedX_le_powerBoundedSubring`: the inclusion itself, as a
  containment of subrings.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.56 and
  Example 7.57.

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, `projects/AdicSpaces/Adic spaces/Wedhorn828.lean`,
has the power-boundedness of `Xᵢ` under stronger hypotheses: there it follows from membership in a
ring of definition, which needs `A` to be Huber. For that route in this repository, see
`TauCeti.Huber.IsBounded.isPowerBounded_of_mem`.
-/
public section

open Pointwise

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **A weighted monomial `t Xᵛ` is power-bounded** whenever `t ∈ Tᵛ`: the weight `Tᵛ` is exactly
what multiplies `Xᵛ` back into the unit ball of `A⟨X⟩_T`. -/
theorem isPowerBounded_weightedPolynomialHom_monomial {T : Fin k → Set A} (hT : IsWeightFamily T)
    {ν : Fin k →₀ ℕ} {t : A} (ht : t ∈ weightPow T ν) :
    IsPowerBounded (weightedPolynomialHom T hT (MvPolynomial.monomial ν t)) := by
  classical
  -- multiplying by `(t Xᵛ)ⁿ = tⁿ Xⁿᵛ` moves the coefficient at `μ` to `μ + n • ν` and multiplies it
  -- by `tⁿ ∈ Tⁿᵛ`, so it lands in the weight subgroup at the shifted index and one neighbourhood
  -- absorbs every power
  refine isPowerBounded_iff.mpr <| isBounded_iff.mpr fun U hU ↦ ?_
  have hbasis := hasBasis_nhds_zero_weightedTopology hT
  obtain ⟨W, -, hWU⟩ := hbasis.mem_iff.mp hU
  refine ⟨_, hbasis.mem_of_mem (i := W) trivial, ?_⟩
  rintro _ ⟨g, hg, _, ⟨n, rfl⟩, rfl⟩
  refine hWU ?_
  simp only [SetLike.mem_coe, mem_weightedNhd] at hg ⊢
  intro μ
  rw [← map_pow, MvPolynomial.monomial_pow, Subring.coe_mul, coe_weightedPolynomialHom,
    MvPolynomial.coe_monomial, MvPowerSeries.coeff_mul_monomial]
  split
  · -- the coefficient moves from `μ - n • ν` to `μ`, picking up the weight `tⁿ ∈ Tⁿᵛ`
    rename_i hle
    have hpow : t ^ n ∈ weightPow T (n • ν) := weightPow_nsmul T n ν ▸ Set.pow_mem_pow ht
    have h2 := mul_mem_weightMul_add_of_mem_weightPow hpow (hg (μ - n • ν))
    rwa [tsub_add_cancel_of_le hle, mul_comm] at h2
  · exact (weightMul T μ W.toAddSubgroup).zero_mem

/-- **A weighted variable `a · Xᵢ` is power-bounded** whenever `a ∈ T i`. This is
`TauCeti.Huber.isPowerBounded_weightedPolynomialHom_monomial` at `ν = eᵢ`.

Over a Tate ring the images of these elements present the completion of `A⟨X⟩_T` as a
quotient of an unweighted restricted power-series algebra, one variable for each element of
each finite `Tᵢ`
(`TauCeti.Huber.isStrictlyTopologicallyFiniteType_algebraMap_completion_weightedRestrictedSubring`).
-/
theorem isPowerBounded_weightedC_mul_weightedX {T : Fin k → Set A} (hT : IsWeightFamily T)
    {i : Fin k} {a : A} (ha : a ∈ T i) :
    IsPowerBounded (weightedC T hT a * weightedX T hT i) := by
  rw [← weightedPolynomialHom_C, ← weightedPolynomialHom_X, ← map_mul,
    MvPolynomial.C_mul_X_eq_monomial]
  exact isPowerBounded_weightedPolynomialHom_monomial hT (by rwa [weightPow_single, pow_one])

/-- **The variable `Xᵢ` is power-bounded** whenever `1 ∈ T i`. This is
`TauCeti.Huber.isPowerBounded_weightedC_mul_weightedX` at `a = 1`.

Its use is to put the coordinates of the closed polydisc inside the plus ring `A⟨T⟩°` that
`TauCeti.ValuationSpectrum.closedPolydisc` designates; there the weights are trivial, which is
`TauCeti.Huber.isPowerBounded_weightedX_one_weight`. -/
theorem isPowerBounded_weightedX {T : Fin k → Set A} (hT : IsWeightFamily T) {i : Fin k}
    (hi : (1 : A) ∈ T i) : IsPowerBounded (weightedX T hT i) := by
  simpa using isPowerBounded_weightedC_mul_weightedX hT hi

/-- **The variable `Xᵢ` is power-bounded at the trivial weight family**, the case
`TauCeti.ValuationSpectrum.closedPolydisc` uses.

`@[simp]` because it is unconditional: `simp` closes the goal outright rather than rewriting it. -/
@[simp]
theorem isPowerBounded_weightedX_one_weight (i : Fin k) :
    IsPowerBounded (weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i) :=
  isPowerBounded_weightedX _ rfl

/-- **A power-bounded constant stays power-bounded**, at any weight family — no hypothesis on `T`
beyond `TauCeti.Huber.IsWeightFamily`. Contrast `TauCeti.Huber.isPowerBounded_weightedX`, which
needs `1 ∈ T i`.

With the variable case it places `A°[X₁, …, Xₖ]` inside `A⟨X₁, …, Xₖ⟩°`. -/
theorem isPowerBounded_weightedC {T : Fin k → Set A} (hT : IsWeightFamily T) {a : A}
    (ha : IsPowerBounded a) : IsPowerBounded (weightedC T hT a) := by
  -- continuity of `weightedC` would not settle this: a continuous ring homomorphism need not
  -- preserve power-boundedness. The `n`-th power of the constant `a` multiplies every coefficient
  -- by `aⁿ` and moves none of them, so the weight at each `ν` is unchanged and one neighbourhood
  -- absorbs the whole family
  refine isPowerBounded_iff.mpr <| isBounded_iff.mpr fun U hU ↦ ?_
  have hbasis := hasBasis_nhds_zero_weightedTopology hT
  obtain ⟨W, -, hWU⟩ := hbasis.mem_iff.mp hU
  obtain ⟨V, hV, hVW⟩ :=
    isBounded_iff.mp (isPowerBounded_iff.mp ha) (W : Set A) (W.isOpen.mem_nhds W.zero_mem)
  obtain ⟨V', hV'⟩ := NonarchimedeanRing.is_nonarchimedean V hV
  refine ⟨_, hbasis.mem_of_mem (i := V') trivial, ?_⟩
  rintro _ ⟨g, hg, _, ⟨n, rfl⟩, rfl⟩
  refine hWU ?_
  simp only [SetLike.mem_coe, mem_weightedNhd] at hg ⊢
  intro ν
  have hcoe : MvPowerSeries.coeff ν
      ((g * weightedC T hT a ^ n : weightedRestrictedSubring T hT) : MvPowerSeries (Fin k) A)
      = MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) A) * a ^ n := by
    push_cast [coe_weightedC, ← map_pow, MvPowerSeries.coeff_mul_C]
    rfl
  rw [hcoe, mul_comm]
  refine mul_mem_of_forall_mul_mul_mem (fun t ht u hu ↦ ?_) (hg ν)
  have huW : u * a ^ n ∈ W.toAddSubgroup := hVW ⟨u, hV' hu, _, ⟨n, rfl⟩, rfl⟩
  have hassoc : a ^ n * (t * u) = t * (u * a ^ n) := by ring
  rw [hassoc]
  exact mul_mem_weightMul T ν _ ht huW

/-- **`A°[X₁, …, Xₖ]` lands inside `A⟨X₁, …, Xₖ⟩_T°`.** The subring generated by the power-bounded
constants and the variables consists of power-bounded elements.

This is the inclusion the two results above are for, stated as a subring containment so that a
consumer discharges membership for a whole polynomial expression at once rather than by induction
on its shape. -/
theorem closure_weightedC_weightedX_le_powerBoundedSubring {T : Fin k → Set A}
    (hT : IsWeightFamily T) (hi : ∀ i, (1 : A) ∈ T i) :
    Subring.closure (weightedC T hT '' (powerBoundedSubring A : Set A) ∪
        Set.range (weightedX T hT))
      ≤ powerBoundedSubring (weightedRestrictedSubring T hT) := by
  rw [Subring.closure_le]
  rintro x (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
  · exact mem_powerBoundedSubring.mpr
      (isPowerBounded_weightedC hT (mem_powerBoundedSubring.mp ha))
  · exact mem_powerBoundedSubring.mpr (isPowerBounded_weightedX hT (hi i))

end TauCeti.Huber

end
