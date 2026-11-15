/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.DivMod
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.PowerBasis

/-!
# Coordinates on Weierstrass quotients

For a multiplicatively distinguished restricted series `g` of degree `s`, taking the
Weierstrass remainder identifies the quotient by `g` with polynomials of degree less than `s`
as a module over the coefficient ring. The classes of `1, X, …, X^(s-1)` therefore give a
basis of powers. Its coordinates are the coefficients of the remainder, and multiplication is
computed by taking the remainder of the product of the polynomial representatives. For a monic
polynomial divisor this is ordinary polynomial remainder; the structure constants are the
coefficients of `X^(i+j) %ₘ p`.

The coefficient ring may be any complete ultrametric normed commutative ring, and the radius
any positive real number. No globally multiplicative norm is assumed. This applies in particular
to series over the Tate algebra in the remaining variables. Distinguished degree zero gives
an empty basis of the zero quotient.

The construction uses Mathlib's `Polynomial.degreeLT.basis` for the polynomial coordinates.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.2.1–5.2.2.
-/

public section

noncomputable section

namespace TauCeti.PowerSeries.IsMulDistinguished

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {c : ℝ} {s : ℕ} {g : PowerSeries.IsRestricted.subring (R := R) c}

local notation "S" => PowerSeries.IsRestricted.subring (R := R) c
local notation "Q" => S ⧸ Ideal.span (singleton g : Set S)

/-- A restricted series and its Weierstrass remainder represent the same quotient class. -/
@[simp]
theorem mk_polynomialToRestricted_weierstrassMod
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) (f : S) :
    Ideal.Quotient.mk (Ideal.span {g}) (polynomialToRestricted c (hg.weierstrassMod hc f)) =
      Ideal.Quotient.mk _ f := by
  have h := congrArg (Ideal.Quotient.mk (Ideal.span {g}))
    (hg.mul_weierstrassDiv_add_weierstrassMod hc f)
  simpa using h

/-- Taking the Weierstrass remainder identifies the quotient by a multiplicatively distinguished
series with the coefficient module of polynomials of degree less than its distinguished degree. -/
def quotientRemainderEquiv (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    Q ≃ₗ[R] Polynomial.degreeLT R s := by
  let F : Polynomial.degreeLT R s →ₗ[R] Q :=
    ((Ideal.Quotient.mkₐ R (Ideal.span {g})).comp (polynomialToRestricted c)).toLinearMap.comp
      (Polynomial.degreeLT R s).subtype
  refine (LinearEquiv.ofBijective F ⟨?_, ?_⟩).symm
  · refine (injective_iff_map_eq_zero F).mpr fun p hp ↦ ?_
    have hmem : polynomialToRestricted c p.val ∈ Ideal.span {g} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hp
    have hzero := hg.weierstrassMod_eq_zero_iff_dvd hc |>.mpr
      (Ideal.mem_span_singleton.mp hmem)
    rw [hg.weierstrassMod_polynomialToRestricted_of_degree_lt hc
      (Polynomial.mem_degreeLT.mp p.property)] at hzero
    exact Subtype.ext hzero
  · intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨⟨hg.weierstrassMod hc f,
      Polynomial.mem_degreeLT.mpr (hg.degree_weierstrassMod_lt hc f)⟩, ?_⟩
    exact hg.mk_polynomialToRestricted_weierstrassMod hc f

/-- The inverse remainder equivalence includes the polynomial representative in the quotient. -/
@[simp]
theorem quotientRemainderEquiv_symm_apply
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c)
    (p : Polynomial.degreeLT R s) :
    (hg.quotientRemainderEquiv hc).symm p =
      Ideal.Quotient.mk _ (polynomialToRestricted c p.val) := (rfl)

/-- The representative selected from a series class is its Weierstrass remainder. -/
@[simp]
theorem quotientRemainderEquiv_mk
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) (f : S) :
    (hg.quotientRemainderEquiv hc (Ideal.Quotient.mk _ f)).val = hg.weierstrassMod hc f := by
  have heq : (hg.quotientRemainderEquiv hc).symm
      ⟨hg.weierstrassMod hc f, Polynomial.mem_degreeLT.mpr
        (hg.degree_weierstrassMod_lt hc f)⟩ = Ideal.Quotient.mk _ f :=
    hg.mk_polynomialToRestricted_weierstrassMod hc f
  exact congrArg Subtype.val ((hg.quotientRemainderEquiv hc).symm_apply_eq.mp heq).symm

/-- The polynomial selected from a quotient class represents that class. -/
@[simp]
theorem mk_quotientRemainderEquiv
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) (x : Q) :
    Ideal.Quotient.mk _ (polynomialToRestricted c (hg.quotientRemainderEquiv hc x).val) = x := by
  rw [← hg.quotientRemainderEquiv_symm_apply hc]
  exact (hg.quotientRemainderEquiv hc).symm_apply_apply x

/-- Multiplication in a Weierstrass quotient is multiplication of its polynomial representatives
followed by taking the Weierstrass remainder. -/
theorem quotientRemainderEquiv_mul
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) (x y : Q) :
    (hg.quotientRemainderEquiv hc (x * y)).val =
      hg.weierstrassMod hc (polynomialToRestricted c
        ((hg.quotientRemainderEquiv hc x).val * (hg.quotientRemainderEquiv hc y).val)) := by
  conv_lhs => rw [← hg.mk_quotientRemainderEquiv hc x, ← hg.mk_quotientRemainderEquiv hc y]
  rw [← map_mul, ← map_mul, hg.quotientRemainderEquiv_mk hc]

/-- The classes of the first `s` powers of the variable form a basis of the quotient by a
multiplicatively distinguished series of degree `s`. At degree zero this is the empty basis. -/
def quotientBasis (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    Module.Basis (Fin s) R Q :=
  (Polynomial.degreeLT.basis R s).map (hg.quotientRemainderEquiv hc).symm

/-- The quotient by a multiplicatively distinguished restricted series is finite over the
coefficient ring, without requiring a multiplicative coefficient norm. -/
theorem finite_quotient (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    Module.Finite R Q :=
  .of_basis (hg.quotientBasis hc)

/-- The quotient by a multiplicatively distinguished restricted series is free over the
coefficient ring, without requiring a multiplicative coefficient norm. -/
theorem free_quotient (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    Module.Free R Q :=
  .of_basis (hg.quotientBasis hc)

/-- The `i`-th basis vector is the class of `X^i`. -/
@[simp]
theorem quotientBasis_apply
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) (i : Fin s) :
    hg.quotientBasis hc i =
      Ideal.Quotient.mk (Ideal.span {g})
        (polynomialToRestricted c (Polynomial.X : Polynomial R)) ^ (i : ℕ) := by
  rw [quotientBasis, Module.Basis.map_apply, quotientRemainderEquiv_symm_apply,
    Polynomial.degreeLT.basis_val, map_pow, map_pow]

/-- The quotient by a multiplicatively distinguished series is generated by the class of `X`,
with its first `s` powers forming the remainder-coordinate basis. -/
def quotientPowerBasis (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    PowerBasis R Q where
  gen := Ideal.Quotient.mk (Ideal.span {g})
    (polynomialToRestricted c (Polynomial.X : Polynomial R))
  dim := s
  basis := hg.quotientBasis hc
  basis_eq_pow := hg.quotientBasis_apply hc

/-- The generator of the quotient power basis is the class of the variable. -/
@[simp]
theorem quotientPowerBasis_gen
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    (hg.quotientPowerBasis hc).gen =
      Ideal.Quotient.mk (Ideal.span {g})
        (polynomialToRestricted c (Polynomial.X : Polynomial R)) := (rfl)

/-- The dimension of the quotient power basis is the distinguished degree. -/
@[simp]
theorem quotientPowerBasis_dim
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    (hg.quotientPowerBasis hc).dim = s := (rfl)

/-- The underlying basis of the quotient power basis is the remainder-coordinate basis. -/
@[simp]
theorem quotientPowerBasis_basis
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    (hg.quotientPowerBasis hc).basis.reindex (finCongr (hg.quotientPowerBasis_dim hc)) =
      hg.quotientBasis hc := by
  unfold quotientPowerBasis
  rw [finCongr_refl, Module.Basis.reindex_refl]

/-- Basis coordinates are coefficients of the polynomial representative selected by division. -/
@[simp]
theorem quotientBasis_repr
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) (x : Q) (i : Fin s) :
    (hg.quotientBasis hc).repr x i =
      (hg.quotientRemainderEquiv hc x).val.coeff i := by
  simp [quotientBasis, Module.Basis.map_repr]

/-- Multiplication coordinates are obtained by reducing the product of the two remainders. -/
theorem quotientBasis_repr_mul
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) (x y : Q) (i : Fin s) :
    (hg.quotientBasis hc).repr (x * y) i =
      (hg.weierstrassMod hc (polynomialToRestricted c
        ((hg.quotientRemainderEquiv hc x).val *
          (hg.quotientRemainderEquiv hc y).val))).coeff i := by
  rw [hg.quotientBasis_repr hc, hg.quotientRemainderEquiv_mul hc]

/-- For a monic polynomial divisor the multiplication table of the power basis is given by
reducing `X^(i+j)` modulo the divisor. -/
theorem quotientBasis_repr_mul_basis {p : Polynomial R} (hp : p.IsMonicOfDegree s)
    (hg : IsMulDistinguished c s (polynomialToRestricted c p : PowerSeries R))
    (hc : 0 < c) (i j k : Fin s) :
    (hg.quotientBasis hc).repr (hg.quotientBasis hc i * hg.quotientBasis hc j) k =
      ((Polynomial.X ^ (i.val + j.val)) %ₘ p).coeff k := by
  have hmul : hg.quotientBasis hc i * hg.quotientBasis hc j =
      Ideal.Quotient.mk (Ideal.span {polynomialToRestricted c p})
        (polynomialToRestricted c (Polynomial.X ^ (i.val + j.val))) := by
    simp only [quotientBasis_apply, pow_add, map_mul, map_pow]
  simp only [hmul, quotientBasis_repr, quotientRemainderEquiv_mk,
    hg.weierstrassMod_polynomialToRestricted_eq_modByMonic hc hp]

end TauCeti.PowerSeries.IsMulDistinguished
