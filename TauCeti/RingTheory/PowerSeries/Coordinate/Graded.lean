/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
public import TauCeti.RingTheory.GradedAlgebra.Polynomial
public import Mathlib.Algebra.Polynomial.Laurent
-- Proof-only: membership in the equality locus of group homomorphisms.
import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# Graded formal coordinates

For an `ℕ`-graded commutative ring `A` and a parameter degree `w`, the coordinates
`φ(X) = u X + ∑ bᵢ X^(i+1)` with `u` in degree zero and `bᵢ` in degree `w * i` form a subgroup of
`FormalCoordinate A`. In particular, their compositional inverses have coefficients in the
same degrees. The intersection with the kernel of `linearCoeff` is the group of strict graded
coordinates, parametrized by arbitrary homogeneous coefficients `bᵢ`.

Homogeneity can be tested by applying the grading homomorphism `a ↦ ∑ aₙ Tⁿ` and comparing
with conjugation by `X ↦ T^w X`. We make this comparison in Laurent polynomials, where `T^w`
is a unit. This proves closure under inversion over arbitrary graded rings, without dividing
by integers or imposing conditions on torsion. The case `w = 2` is the homological grading of
strict coordinate changes of complex-oriented formal groups.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

namespace TauCeti.FormalCoordinate

open PowerSeries LaurentPolynomial TauCeti.GradedAlgebra

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem coeff_grading_conjugate (w : ℕ) (φ : FormalCoordinate A) (n : ℕ) :
    coeff n (homothety (unitOfInvertible (T (w : ℤ)))⁻¹ * map LaurentPolynomial.C φ *
      homothety (unitOfInvertible (T (w : ℤ)))).toPowerSeries =
      LaurentPolynomial.C (coeff n φ.toPowerSeries) * T (w * (n - 1) : ℕ) := by
  rw [coeff_homothety_inv_mul_mul_homothety, toPowerSeries_map, coeff_map]
  simp only [unitOfInvertible, Units.val_mk, Units.inv_mk, LaurentPolynomial.invOf_T]
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [T_pow, ← T_add]
    have hi : -(w : ℤ) + (n + 1 : ℕ) * (w : ℤ) = (w * n : ℕ) := by
      push_cast
      ring
    rw [hi, Nat.add_one_sub_one, mul_comm]

/-- A coordinate is graded exactly when its image under the grading homomorphism is the
conjugate of its constant base change by the homothety `X ↦ T^w X`. -/
theorem map_toLaurent_eq_conjugate_iff (w : ℕ) (φ : FormalCoordinate A) :
    map (Polynomial.toLaurent.comp (toPolynomial 𝒜)) φ =
        homothety (unitOfInvertible (T (w : ℤ)))⁻¹ * map LaurentPolynomial.C φ *
          homothety (unitOfInvertible (T (w : ℤ))) ↔
      ∀ n, coeff n φ.toPowerSeries ∈ 𝒜 (w * (n - 1)) := by
  rw [FormalCoordinate.ext_iff, PowerSeries.ext_iff]
  refine forall_congr' fun n ↦ ?_
  rw [toPowerSeries_map, coeff_map, coeff_grading_conjugate, RingHom.comp_apply,
    ← Polynomial.toLaurent_C_mul_T, Polynomial.toLaurent_inj,
    toPolynomial_eq_monomial_iff]

/-- The subgroup of formal coordinates whose coefficient of `Xⁿ` has degree `w * (n - 1)`.
For complex orientations in homological grading, take `w = 2`. -/
def gradedSubgroup (w : ℕ) : Subgroup (FormalCoordinate A) :=
  (map (Polynomial.toLaurent.comp (toPolynomial 𝒜))).eqLocus
    (((MulAut.conj (homothety (unitOfInvertible (T (w : ℤ)))⁻¹)).toMonoidHom).comp
      (map LaurentPolynomial.C))

/-- Membership in the graded coordinate subgroup is coefficientwise homogeneity. -/
@[simp]
theorem mem_gradedSubgroup (w : ℕ) (φ : FormalCoordinate A) :
    φ ∈ gradedSubgroup 𝒜 w ↔ ∀ n, coeff n φ.toPowerSeries ∈ 𝒜 (w * (n - 1)) := by
  rw [gradedSubgroup, MonoidHom.mem_eqLocus]
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv,
    inv_inv] using
    map_toLaurent_eq_conjugate_iff 𝒜 w φ

/-- A strict coordinate is graded precisely when its freely specified coefficients are
homogeneous in the required degrees. -/
@[simp high]
theorem ofStrictCoeffs_mem_gradedSubgroup (w : ℕ) (b : ℕ+ → A) :
    ofStrictCoeffs b ∈ gradedSubgroup 𝒜 w ↔ ∀ i : ℕ+, b i ∈ 𝒜 (w * i) := by
  rw [mem_gradedSubgroup]
  constructor
  · intro h i
    simpa using h (i + 1)
  · intro h n
    rcases n with _ | _ | n
    · simp [coeff_zero_eq_constantCoeff_apply]
    · simpa using (SetLike.one_mem_graded (A := 𝒜))
    · have hc := coeff_succ_ofStrictCoeffs b n.succPNat
      rw [Nat.succPNat_coe] at hc
      simpa [hc] using h n.succPNat

/-- Strict graded coordinates are parametrized by arbitrary homogeneous coefficients: the
coefficient of `X^(i+1)` lies in degree `w * i`. -/
def gradedStrictCoeffsEquiv (w : ℕ) :
    (∀ i : ℕ+, 𝒜 (w * i)) ≃
      ↥(gradedSubgroup 𝒜 w ⊓ (linearCoeff (R := A)).ker) where
  toFun b := ⟨ofStrictCoeffs (fun i : ℕ+ ↦ b i),
    (ofStrictCoeffs_mem_gradedSubgroup 𝒜 w _).2 (fun i ↦ (b i).2),
    ofStrictCoeffs_mem_ker_linearCoeff _⟩
  invFun φ i := ⟨coeff (i + 1) φ.1.toPowerSeries, by
    simpa using (mem_gradedSubgroup 𝒜 w φ.1).1 φ.2.1 (i + 1)⟩
  left_inv b := by
    funext i
    exact Subtype.ext (coeff_succ_ofStrictCoeffs _ _)
  right_inv φ := by
    apply Subtype.ext
    have he := congrArg Subtype.val (strictCoeffsEquiv.apply_symm_apply ⟨φ.1, φ.2.2⟩)
    rw [coe_strictCoeffsEquiv_apply] at he
    have hc : strictCoeffsEquiv.symm ⟨φ.1, φ.2.2⟩ =
        fun i : ℕ+ ↦ coeff (i + 1) φ.1.toPowerSeries :=
      funext fun i ↦ strictCoeffsEquiv_symm_apply _ i
    rw [hc] at he
    exact he

/-- The coordinate attached to a family of homogeneous coefficients is `X + ∑ bᵢ X^(i+1)`. -/
@[simp]
theorem coe_gradedStrictCoeffsEquiv (w : ℕ) (b : ∀ i : ℕ+, 𝒜 (w * i)) :
    (gradedStrictCoeffsEquiv 𝒜 w b : FormalCoordinate A) = ofStrictCoeffs (fun i : ℕ+ ↦ b i) :=
  (rfl)

/-- The inverse parametrization reads the coefficients of the strict graded coordinate. -/
@[simp]
theorem gradedStrictCoeffsEquiv_symm_apply (w : ℕ)
    (φ : ↥(gradedSubgroup 𝒜 w ⊓ (linearCoeff (R := A)).ker)) (i : ℕ+) :
    ((gradedStrictCoeffsEquiv 𝒜 w).symm φ i : A) = coeff (i + 1) φ.1.toPowerSeries :=
  (rfl)

end TauCeti.FormalCoordinate
