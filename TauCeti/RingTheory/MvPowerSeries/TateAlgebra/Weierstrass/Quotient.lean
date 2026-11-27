/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Finite
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Basis

/-!
# Weierstrass quotients of multivariable restricted series

Separating `X none` by `MvPowerSeries.restrictedOptionEquiv` identifies the quotient by a
multiplicatively distinguished series with the univariate Weierstrass quotient over the
restricted series in the remaining variables. The comparison yields a power basis and
remainder coordinates directly on the multivariable quotient.

## Main results

* `MvPowerSeries.restrictedOptionQuotientEquiv`: the quotient comparison after separating
  a variable.
* `MvPowerSeries.restrictedOptionQuotientPowerBasis`: the basis of powers of
  the class of `X none`.
* `MvPowerSeries.restrictedOptionQuotientRemainderEquiv`: the remainder coordinates from
  `TauCeti.PowerSeries.IsMulDistinguished.quotientRemainderEquiv`.
* `MvPowerSeries.finite_of_isTorsionBy_restrictedOption`: finite modules killed by the divisor
  are finite over the coefficient algebra.

## References

* Bosch, Güntzer and Remmert, *Non-Archimedean Analysis*, §§5.2.1–5.2.2.
-/

public section

noncomputable section

namespace MvPowerSeries

open TauCeti.PowerSeries (IsMulDistinguished)

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {c : Option σ → ℝ} [∀ i, Fact (0 < c i)]

local notation "Inner" => IsRestricted.subring (R := R) (fun i : σ ↦ c (some i))
local notation "Flat" => IsRestricted.subring (R := R) c
local notation "Iter" => PowerSeries.IsRestricted.subring (R := Inner) (c none)
local notation "Q(" g ")" => (Flat ⧸ Ideal.span ({g} : Set Flat))
local notation "QI(" g ")" => (Iter ⧸ Ideal.span ({restrictedOptionEquiv g} : Set Iter))

/-- Splitting off `X none` carries a principal quotient to the quotient by the corresponding
univariate restricted series. -/
def restrictedOptionQuotientEquiv (g : Flat) : Q(g) ≃ₐ[Inner] QI(g) :=
  Ideal.quotientEquivAlg _ _ restrictedOptionCoeffAlgEquiv (by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x : Iter ↦ Ideal.span ({x} : Set Iter))
      (restrictedOptionCoeffAlgEquiv_apply g).symm)

/-- On quotient classes the comparison applies `restrictedOptionEquiv`. -/
@[simp]
theorem restrictedOptionQuotientEquiv_mk (g f : Flat) :
    restrictedOptionQuotientEquiv g (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (restrictedOptionEquiv f) := by
  rw [restrictedOptionQuotientEquiv, Ideal.quotientEquivAlg_mk,
    restrictedOptionCoeffAlgEquiv_apply]

/-- The inverse quotient comparison flattens the univariate representative. -/
@[simp]
theorem restrictedOptionQuotientEquiv_symm_mk (g : Flat) (f : Iter) :
    (restrictedOptionQuotientEquiv g).symm (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (restrictedOptionEquiv.symm f) := by
  rw [AlgEquiv.symm_apply_eq, restrictedOptionQuotientEquiv_mk, AlgEquiv.apply_symm_apply]

variable [CompleteSpace R]

/-- The class of `X none` generates the power basis of a quotient by a multiplicatively
distinguished restricted series of degree `s` in that variable. -/
def restrictedOptionQuotientPowerBasis
    {g : Flat} {s : ℕ}
    (hg : IsMulDistinguished (c none) s (restrictedOptionEquiv g : Iter).val) :
    PowerBasis Inner (Q(g)) :=
  (hg.quotientPowerBasis (R := Inner) (c := c none) (s := s) (g := restrictedOptionEquiv g)
    Fact.out).map (restrictedOptionQuotientEquiv g).symm

/-- The generator of the power basis is the class of the separated variable. -/
@[simp]
theorem restrictedOptionQuotientPowerBasis_gen
    {g : Flat} {s : ℕ}
    (hg : IsMulDistinguished (c none) s (restrictedOptionEquiv g : Iter).val) :
    (restrictedOptionQuotientPowerBasis hg).gen =
      Ideal.Quotient.mk (Ideal.span {g}) ⟨X none, isRestricted_X c none⟩ := by
  apply (restrictedOptionQuotientEquiv g).injective
  unfold restrictedOptionQuotientPowerBasis
  simp only [PowerBasis.map, AlgEquiv.apply_symm_apply,
    restrictedOptionQuotientEquiv_mk, IsMulDistinguished.quotientPowerBasis_gen]
  congr 1
  apply Subtype.ext
  rw [coe_restrictedOptionEquiv_X_none, TauCeti.PowerSeries.coe_polynomialToRestricted,
    Polynomial.coe_X]

/-- The power basis has one element for each exponent less than the distinguished degree. -/
@[simp]
theorem restrictedOptionQuotientPowerBasis_dim
    {g : Flat} {s : ℕ}
    (hg : IsMulDistinguished (c none) s (restrictedOptionEquiv g : Iter).val) :
    (restrictedOptionQuotientPowerBasis hg).dim = s := by
  unfold restrictedOptionQuotientPowerBasis
  exact hg.quotientPowerBasis_dim (R := Inner) (c := c none) (g := restrictedOptionEquiv g) Fact.out

/-- A class modulo a multiplicatively distinguished series of degree `s` is represented uniquely by
a polynomial of degree less than `s` in `X none`, with restricted coefficients. -/
def restrictedOptionQuotientRemainderEquiv
    {g : Flat} {s : ℕ}
    (hg : IsMulDistinguished (c none) s (restrictedOptionEquiv g : Iter).val) :
    Q(g) ≃ₗ[Inner] Polynomial.degreeLT Inner s :=
  (restrictedOptionQuotientEquiv g).toLinearEquiv.trans
    (hg.quotientRemainderEquiv (R := Inner) (c := c none) (s := s) (g := restrictedOptionEquiv g)
      Fact.out)

/-- The representative of a class is the Weierstrass remainder after separating `X none`. -/
@[simp]
theorem restrictedOptionQuotientRemainderEquiv_mk
    {g : Flat} {s : ℕ}
    (hg : IsMulDistinguished (c none) s (restrictedOptionEquiv g : Iter).val)
    (f : Flat) :
    (restrictedOptionQuotientRemainderEquiv hg (Ideal.Quotient.mk _ f)).val =
      hg.weierstrassMod Fact.out (restrictedOptionEquiv f) := by
  unfold restrictedOptionQuotientRemainderEquiv
  simp only [LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, restrictedOptionQuotientEquiv_mk,
    IsMulDistinguished.quotientRemainderEquiv_mk]

/-- A polynomial of degree less than `s` represents its flattened series class. -/
@[simp]
theorem restrictedOptionQuotientRemainderEquiv_symm_apply
    {g : Flat} {s : ℕ}
    (hg : IsMulDistinguished (c none) s (restrictedOptionEquiv g : Iter).val)
    (p : Polynomial.degreeLT Inner s) :
    (restrictedOptionQuotientRemainderEquiv hg).symm p =
      Ideal.Quotient.mk _ (restrictedOptionEquiv.symm
        (TauCeti.PowerSeries.polynomialToRestricted (c none) p.val)) := by
  unfold restrictedOptionQuotientRemainderEquiv
  simp only [LinearEquiv.symm_trans_apply,
    AlgEquiv.coe_symm_toLinearEquiv,
    IsMulDistinguished.quotientRemainderEquiv_symm_apply, restrictedOptionQuotientEquiv_symm_mk]

/-- Multiplication in remainder coordinates is polynomial multiplication followed by
Weierstrass reduction. -/
theorem restrictedOptionQuotientRemainderEquiv_mul
    {g : Flat} {s : ℕ}
    (hg : IsMulDistinguished (c none) s (restrictedOptionEquiv g : Iter).val)
    (x y : Q(g)) :
    (restrictedOptionQuotientRemainderEquiv hg (x * y)).val =
      hg.weierstrassMod Fact.out (TauCeti.PowerSeries.polynomialToRestricted (c none)
        ((restrictedOptionQuotientRemainderEquiv hg x).val *
          (restrictedOptionQuotientRemainderEquiv hg y).val)) := by
  unfold restrictedOptionQuotientRemainderEquiv
  simp only [LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, map_mul, IsMulDistinguished.quotientRemainderEquiv_mul]

/-- A finite module killed by a multiplicatively distinguished series is finite over the
restricted series in the remaining variables. -/
theorem finite_of_isTorsionBy_restrictedOption
    {g : Flat} {s : ℕ}
    (hg : IsMulDistinguished (c none) s (restrictedOptionEquiv g : Iter).val)
    {M : Type*} [AddCommGroup M] [Module Flat M] [Module Inner M] [IsScalarTower Inner Flat M]
    [Module.Finite Flat M] (hM : Module.IsTorsionBy Flat M g) :
    Module.Finite Inner M := by
  have hfinite : Module.Finite Inner (Q(g)) :=
    .of_basis (restrictedOptionQuotientPowerBasis hg).basis
  exact Module.IsTorsionBy.finite_of_finite_quotient (A := Inner) hM

end MvPowerSeries
