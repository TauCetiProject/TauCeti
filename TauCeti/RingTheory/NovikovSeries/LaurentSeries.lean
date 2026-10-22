/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial
public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import TauCeti.RingTheory.NovikovSeries.Topology

/-!
# Novikov series on the integers are Laurent series

For the exponent group `ℤ` with the period map `k ↦ k` (`Int.castAddHom ℝ`), the Novikov
support condition says exactly that the support is bounded below
(`TauCeti.NovikovSeries.forall_finite_lt_iff_bddBelow_support`). Hence the Novikov series are the
formal Laurent series `R⸨X⸩ = HahnSeries ℤ R` of Mathlib, with the same coefficients. This file
constructs that comparison as a ring isomorphism `TauCeti.NovikovSeries.toLaurentSeries`. It sends
the monomial `r e^n` to `r Xⁿ`, and it restricts on finitely supported series to the inclusion
`LaurentPolynomial.toLaurentSeries` of Laurent polynomials, the group ring `R[ℤ]`.

Over a field `K`, the comparison also matches the topologies: the period filtration `U_D` is the
closed ball `v ≤ exp (-D)` of the `X`-adic valuation
(`TauCeti.NovikovSeries.valuation_toLaurentSeries_le_exp_iff`), and the comparison is a uniform
equivalence between the period topology and the valuation topology
(`TauCeti.NovikovSeries.toLaurentSeriesUniformEquiv`). Through it, the circle-valued Novikov
complexes with coefficients in `Nov(ℤ, ℤ, id)` can be computed with the Laurent-series API of
Mathlib.

## Main definitions

* `TauCeti.NovikovSeries.toLaurentSeries`: the coefficient-preserving ring isomorphism between
  Novikov series on `ℤ` for the period map `k ↦ k` and Laurent series.
* `TauCeti.NovikovSeries.toLaurentSeriesUniformEquiv`: over a field, the same map as a uniform
  equivalence for the period and valuation topologies.

## Main results

* `TauCeti.NovikovSeries.toLaurentSeries_single` and
  `TauCeti.NovikovSeries.toLaurentSeries_ofAddMonoidAlgebra`: the comparison sends monomials to
  monomials and restricts to the inclusion of Laurent polynomials.
* `TauCeti.NovikovSeries.toLaurentSeries_algebraMap`: for an `S`-algebra `R`, the comparison
  commutes with `algebraMap S`.
* `TauCeti.NovikovSeries.valuation_toLaurentSeries_le_exp_iff`: the period filtration corresponds
  to the valuation filtration.
* `TauCeti.NovikovSeries.tendsto_toLaurentSeries_iff`: the comparison and its inverse preserve
  convergence.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

open Filter Function Set Topology

open scoped LaurentPolynomial LaurentSeries

namespace TauCeti

namespace NovikovSeries

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- Novikov series on `ℤ` for the period map `k ↦ k` are the Laurent series: the ring isomorphism
which keeps every coefficient. -/
def toLaurentSeries : NovikovSeries R ℤ (Int.castAddHom ℝ) ≃+* R⸨X⸩ where
  toFun a := HahnSeries.ofSuppBddBelow a.coeff <|
    a.bddBelow_support_int.mono fun _ => mem_support.2
  invFun f := ⟨f.coeff, (forall_finite_lt_iff_bddBelow_support f.coeff).2
    ⟨f.order, fun _ => HahnSeries.order_le_of_coeff_ne_zero⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' a b := by
    ext n
    rw [HahnSeries.coeff_mul, HahnSeries.coeff_ofSuppBddBelow]
    exact coeff_mul_eq_sum (fun p hp => (Finset.mem_antidiagonal.1 hp).2.2)
      fun u v huv hu hv => Finset.mem_antidiagonal.2 ⟨hu, hv, huv⟩

@[simp]
theorem coeff_toLaurentSeries (a : NovikovSeries R ℤ (Int.castAddHom ℝ)) :
    (toLaurentSeries a).coeff = a.coeff :=
  (rfl)

@[simp]
theorem coeff_toLaurentSeries_symm (f : R⸨X⸩) :
    (toLaurentSeries.symm f : NovikovSeries R ℤ (Int.castAddHom ℝ)).coeff = f.coeff :=
  (rfl)

@[simp]
theorem support_toLaurentSeries (a : NovikovSeries R ℤ (Int.castAddHom ℝ)) :
    (toLaurentSeries a).support = a.support :=
  Set.ext fun _ => mem_support.symm

/-- The comparison sends the monomial `r e^n` to the Laurent monomial `r Xⁿ`. -/
@[simp]
theorem toLaurentSeries_single (n : ℤ) (r : R) :
    toLaurentSeries (single n r : NovikovSeries R ℤ (Int.castAddHom ℝ)) =
      HahnSeries.single n r := by
  ext k
  rw [coeff_toLaurentSeries, HahnSeries.coeff_single]
  split_ifs with hk
  · rw [hk, coeff_single_same]
  · exact coeff_single_of_ne hk r

/-- For an `S`-algebra `R`, the comparison is compatible with the `S`-algebra structures: it
sends the constant series `algebraMap S _ s` to the constant Laurent series. -/
theorem toLaurentSeries_algebraMap {S : Type*} [CommSemiring S] [Algebra S R] (s : S) :
    toLaurentSeries (algebraMap S (NovikovSeries R ℤ (Int.castAddHom ℝ)) s) =
      algebraMap S R⸨X⸩ s := by
  rw [NovikovSeries.algebraMap_apply, toLaurentSeries_single, HahnSeries.algebraMap_apply,
    HahnSeries.C_apply]

/-- On the group ring `R[ℤ] = R[T;T⁻¹]`, the comparison restricts to the inclusion of Laurent
polynomials into Laurent series. -/
@[simp]
theorem toLaurentSeries_ofAddMonoidAlgebra (p : R[T;T⁻¹]) :
    toLaurentSeries (ofAddMonoidAlgebra p : NovikovSeries R ℤ (Int.castAddHom ℝ)) =
      LaurentPolynomial.toLaurentSeries p := by
  ext n
  rw [coeff_toLaurentSeries, coeff_ofAddMonoidAlgebra, LaurentPolynomial.coeff_toLaurentSeries]

end Semiring

section Field

variable {K : Type*} [Field K]

/-- The period filtration `U_D` corresponds to the closed ball `v ≤ exp (-D)` of the `X`-adic
valuation on Laurent series. -/
theorem valuation_toLaurentSeries_le_exp_iff {a : NovikovSeries K ℤ (Int.castAddHom ℝ)}
    {D : ℤ} :
    Valued.v (toLaurentSeries a) ≤ WithZero.exp (-D) ↔
      a ∈ periodFiltration K (Int.castAddHom ℝ) D := by
  simp [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]

/-- A family of Novikov series on `ℤ` converges in the period topology if and only if its image
converges in the valuation topology on Laurent series. -/
theorem tendsto_toLaurentSeries_iff {ι : Type*} {l : Filter ι}
    {f : ι → NovikovSeries K ℤ (Int.castAddHom ℝ)} {a : NovikovSeries K ℤ (Int.castAddHom ℝ)} :
    Tendsto (fun i => toLaurentSeries (f i)) l (𝓝 (toLaurentSeries a)) ↔ Tendsto f l (𝓝 a) := by
  rw [tendsto_laurentSeries_iff_coeff, tendsto_nhds_iff]
  refine ⟨fun ⟨⟨b, hb⟩, hcoeff⟩ C => ?_, fun h => ?_⟩
  · filter_upwards [hahnSeries_eventually_forall_lt_coeff_eq hb hcoeff ⌈C⌉] with i hi k hk
    exact hi k (Int.lt_ceil.2 hk)
  simp only [coeff_toLaurentSeries]
  obtain ⟨m, hm⟩ := a.bddBelow_support_int
  have ha (k : ℤ) (hk : k < m) : a.coeff k = 0 :=
    by_contra fun hk' => (hm (mem_support.2 hk')).not_gt hk
  refine ⟨⟨m, ?_⟩, fun k => ?_⟩
  · filter_upwards [h m] with i hi k hk
    rw [hi k (Int.cast_lt.2 hk), ha k hk]
  · filter_upwards [h (k + 1)] with i hi
    exact hi k (by simp)

/-- Over a field, the comparison is continuous for the period and valuation topologies. -/
theorem continuous_toLaurentSeries :
    Continuous (toLaurentSeries : NovikovSeries K ℤ (Int.castAddHom ℝ) → K⸨X⸩) :=
  continuous_iff_continuousAt.2 fun _ => tendsto_toLaurentSeries_iff.2 tendsto_id

/-- Over a field, the inverse comparison is continuous for the valuation and period
topologies. -/
theorem continuous_toLaurentSeries_symm :
    Continuous (toLaurentSeries.symm : K⸨X⸩ → NovikovSeries K ℤ (Int.castAddHom ℝ)) :=
  continuous_iff_continuousAt.2 fun f => by
    refine tendsto_toLaurentSeries_iff.1 ?_
    simp only [RingEquiv.apply_symm_apply]
    exact tendsto_id

/-- Over a field, the comparison between Novikov series on `ℤ` and Laurent series is a uniform
equivalence for the period topology and the `X`-adic valuation topology. -/
def toLaurentSeriesUniformEquiv : NovikovSeries K ℤ (Int.castAddHom ℝ) ≃ᵤ K⸨X⸩ where
  toEquiv := toLaurentSeries.toEquiv
  uniformContinuous_toFun := uniformContinuous_addMonoidHom_of_continuous
    (f := toLaurentSeries.toAddMonoidHom) continuous_toLaurentSeries
  uniformContinuous_invFun := uniformContinuous_addMonoidHom_of_continuous
    (f := toLaurentSeries.symm.toAddMonoidHom) continuous_toLaurentSeries_symm

@[simp]
theorem coe_toLaurentSeriesUniformEquiv :
    ⇑(toLaurentSeriesUniformEquiv : NovikovSeries K ℤ (Int.castAddHom ℝ) ≃ᵤ K⸨X⸩) =
      toLaurentSeries :=
  (rfl)

@[simp]
theorem coe_toLaurentSeriesUniformEquiv_symm :
    ⇑(toLaurentSeriesUniformEquiv.symm : K⸨X⸩ ≃ᵤ NovikovSeries K ℤ (Int.castAddHom ℝ)) =
      toLaurentSeries.symm :=
  (rfl)

end Field

end NovikovSeries

end TauCeti
