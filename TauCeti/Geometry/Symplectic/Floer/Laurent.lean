/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.NovikovRing
public import TauCeti.RingTheory.NovikovSeries.Equiv
public import TauCeti.RingTheory.NovikovSeries.LaurentSeries
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Laurent coordinates for monotone Floer coefficients

When the Chern homomorphism is nonzero and its kernel lies in the area kernel, the period
group is infinite cyclic. Its positive Chern generator has Chern number `N > 0`, the minimal
Chern number. The Floer Laurent variable represents the *negative* of this generator:
`T^k = e^(-k B)` has raw degree `-2 N k` and, for area `ω = τ c`, valuation `τ N k`.

This file constructs the finite Laurent coefficient model over any semiring. Its image in the
Floer Novikov ring consists exactly of the finitely supported series. For positive `τ`, the
completed ring is identified with formal Laurent series, compatibly with that finite model.
Over a field the identification preserves convergence for the period and valuation topologies.
The nonzero-Chern hypothesis is essential: the trivial period group has a constant coefficient
model instead, and the Chern-zero branch has its separate completion.

The constructions reuse `AddMonoidAlgebra.mapDomainRingEquiv`,
`NovikovSeries.domCongr`, and `NovikovSeries.toLaurentSeries`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the Novikov
  coefficient conventions in the chapter on quantum cohomology.
-/

public noncomputable section

open scoped LaurentPolynomial LaurentSeries

namespace TauCeti.Floer.NovikovRing

open PeriodGroup NovikovSeries

variable {S R : Type*} [AddGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}

section Finite

variable [Semiring R] (hker : c.ker ≤ ω.ker) (hc : c ≠ 0)

/-- The finite Laurent coefficient model, embedded in the Floer Novikov ring. The variable
represents the negative of the positive Chern generator. -/
def ofLaurentPolynomial : R[T;T⁻¹] →+* NovikovRing R ω c :=
  NovikovSeries.ofAddMonoidAlgebra.comp
    (AddMonoidAlgebra.mapDomainRingEquiv R (laurentExponent hker hc).symm).toRingHom

/-- The finite model reads coefficients in Laurent exponent coordinates. -/
@[simp]
theorem coeff_ofLaurentPolynomial (p : R[T;T⁻¹]) (γ : PeriodGroup ω c) :
    (ofLaurentPolynomial hker hc p).coeff γ = p.coeff (laurentExponent hker hc γ) := by
  simp [ofLaurentPolynomial, Finsupp.equivMapDomain_apply]

/-- Constant Laurent polynomials give constant Floer coefficients. -/
@[simp]
theorem ofLaurentPolynomial_C (r : R) :
    ofLaurentPolynomial hker hc (LaurentPolynomial.C r) = single 0 r := by
  rw [← LaurentPolynomial.single_eq_C]
  simp only [ofLaurentPolynomial, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AddMonoidAlgebra.mapDomainRingEquiv_single,
    ofAddMonoidAlgebra_single, map_zero]

/-- A Laurent power represents the corresponding recapping class. -/
@[simp]
theorem ofLaurentPolynomial_T (k : ℤ) :
    ofLaurentPolynomial hker hc (LaurentPolynomial.T k) =
      single ((laurentExponent hker hc).symm k) 1 := by
  rw [LaurentPolynomial.T]
  simp only [ofLaurentPolynomial, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AddMonoidAlgebra.mapDomainRingEquiv_single,
    ofAddMonoidAlgebra_single]

/-- The finite Laurent coefficient model is faithful. -/
theorem ofLaurentPolynomial_injective :
    Function.Injective (ofLaurentPolynomial (R := R) hker hc) :=
  NovikovSeries.ofAddMonoidAlgebra_injective.comp
    (AddMonoidAlgebra.mapDomainRingEquiv R (laurentExponent hker hc).symm).injective

/-- Exactly the Floer series with finite support lie in the finite Laurent model. -/
theorem mem_range_ofLaurentPolynomial_iff {a : NovikovRing R ω c} :
    a ∈ Set.range (ofLaurentPolynomial hker hc) ↔ a.support.Finite := by
  simp only [ofLaurentPolynomial, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  rw [(AddMonoidAlgebra.mapDomainRingEquiv R (laurentExponent hker hc).symm).surjective.range_comp]
  constructor
  · rintro ⟨p, rfl⟩
    exact (NovikovSeries.mem_range_ofFinsupp_iff).mp ⟨p.coeff, by ext γ; simp⟩
  · intro ha
    obtain ⟨p, hp⟩ := (NovikovSeries.mem_range_ofFinsupp_iff).mpr ha
    refine ⟨AddMonoidAlgebra.ofCoeff p, ?_⟩
    ext γ
    simpa using congrArg (fun b => b.coeff γ) hp

end Finite

section Monotone

variable [Semiring R] {τ : ℝ} (h : ∀ s, ω s = τ * c s) (hc : c ≠ 0)

private theorem laurent_period_rescale (hτ : 0 < τ) :
    ∃ a > 0, ∀ k : ℤ,
      (-area ω c) ((laurentExponent (ker_le_ker_of_area_eq_mul_chern h) hc).symm k) =
        a * (Int.castAddHom ℝ) k := by
  refine ⟨τ * chern ω c ((chernEquivInt (ker_le_ker_of_area_eq_mul_chern h) hc).symm 1),
    mul_pos hτ (Int.cast_pos.mpr (chern_chernEquivInt_symm_pos _ hc)), fun k => ?_⟩
  rw [AddMonoidHom.neg_apply, area_laurentExponent_symm h hc]
  simp

/-- Positive monotone Floer coefficients are formal Laurent series in the negative
positive-Chern generator. The coefficient at a class `γ` becomes the Laurent coefficient at
`laurentExponent γ`. -/
def toLaurentSeries (hτ : 0 < τ) : NovikovRing R ω c ≃+* R⸨X⸩ :=
  ((domCongr ℕ
    (laurentExponent (ker_le_ker_of_area_eq_mul_chern h) hc).symm
    (laurent_period_rescale h hc hτ)).symm.toRingEquiv).trans
      NovikovSeries.toLaurentSeries

/-- The completed comparison reads precisely the coefficient of the corresponding class. -/
@[simp]
theorem coeff_toLaurentSeries (hτ : 0 < τ) (a : NovikovRing R ω c) (k : ℤ) :
    (toLaurentSeries h hc hτ a).coeff k =
      a.coeff ((laurentExponent (ker_le_ker_of_area_eq_mul_chern h) hc).symm k) := by
  simp [toLaurentSeries]

/-- The coefficient of the inverse image at `γ` is the Laurent coefficient at
`laurentExponent γ`. -/
@[simp]
theorem coeff_toLaurentSeries_symm (hτ : 0 < τ) (f : R⸨X⸩) (γ : PeriodGroup ω c) :
    ((toLaurentSeries h hc hτ).symm f).coeff γ =
      f.coeff (laurentExponent (ker_le_ker_of_area_eq_mul_chern h) hc γ) := by
  simpa only [RingEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] using
    (coeff_toLaurentSeries h hc hτ ((toLaurentSeries h hc hτ).symm f)
      (laurentExponent (ker_le_ker_of_area_eq_mul_chern h) hc γ)).symm

/-- The completed comparison sends a recapping monomial to its Laurent monomial. -/
@[simp]
theorem toLaurentSeries_single (hτ : 0 < τ) (γ : PeriodGroup ω c) (r : R) :
    toLaurentSeries h hc hτ (single γ r) =
      HahnSeries.single (laurentExponent (ker_le_ker_of_area_eq_mul_chern h) hc γ) r := by
  simp [toLaurentSeries]

/-- The finite Laurent model and its completion use the same variable and coefficients. -/
@[simp]
theorem toLaurentSeries_ofLaurentPolynomial (hτ : 0 < τ) (p : R[T;T⁻¹]) :
    toLaurentSeries h hc hτ
      (ofLaurentPolynomial (ker_le_ker_of_area_eq_mul_chern h) hc p) =
        LaurentPolynomial.toLaurentSeries p := by
  ext k
  simp [LaurentPolynomial.coeff_toLaurentSeries]

end Monotone

section Topology

open Filter Topology

variable {K : Type*} [Field K] {τ : ℝ} (h : ∀ s, ω s = τ * c s)
  (hc : c ≠ 0) (hτ : 0 < τ)

/-- The Laurent comparison identifies convergence in the Floer period topology and the
Laurent valuation topology. -/
theorem tendsto_toLaurentSeries_iff {ι : Type*} {l : Filter ι}
    {f : ι → NovikovRing K ω c} {a : NovikovRing K ω c} :
    Tendsto (fun i => toLaurentSeries h hc hτ (f i)) l
        (𝓝 (toLaurentSeries h hc hτ a)) ↔ Tendsto f l (𝓝 a) := by
  simp only [toLaurentSeries, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
  rw [NovikovSeries.tendsto_toLaurentSeries_iff]
  let E := continuousDomCongr ℕ (R := K)
    (laurentExponent (ker_le_ker_of_area_eq_mul_chern h) hc).symm
    (laurent_period_rescale h hc hτ)
  -- The homeomorphism projection uses the same function as the continuous algebra equivalence.
  have hE (b : NovikovRing K ω c) : E.symm.toHomeomorph b = E.symm b := rfl
  have ht :=
    (E.symm.toHomeomorph.isEmbedding.tendsto_nhds_iff (f := f) (y := a) (l := l)).symm
  simp only [Function.comp_def, hE] at ht
  simpa only [E, continuousDomCongr_symm, continuousDomCongr_apply, domCongr_symm] using ht

end Topology

end TauCeti.Floer.NovikovRing
