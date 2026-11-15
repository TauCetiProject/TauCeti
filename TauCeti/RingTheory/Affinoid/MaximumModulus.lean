/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm

import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Algebraic.Basic
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.MaximumModulus
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization

/-!
# The maximum modulus principle for affinoid algebras

Let `A` be a nonzero affinoid algebra over a complete nonarchimedean field `K`. For every `f : A`
the supremum `|f|sup` of the absolute values `|f(x)|` over the classical points `x` of `A` is
attained: there is a maximal ideal `x` of `A` with `|f(x)| = |f|sup`. For the Tate algebra
`Tₙ = K⟨X₁, …, Xₙ⟩` the supremum seminorm is moreover the Gauss norm.

For `Tₙ`, a series `f` attains its Gauss norm at a point whose coordinates are `m`-th roots of
unity in the cyclotomic extension `E = K(μₘ)`, for a suitable `m` of norm one
(`MvPowerSeries.exists_norm_restrictedEval₂_eq_norm`). The field `E` is finite over `K` and
carries the spectral norm, so the kernel of evaluation at that point is a classical point `x` of
`Tₙ`, at which `|f(x)|` is the norm of the value in `E`.

For a general affinoid algebra, `|f|sup` is attained on the quotient by a minimal prime, so it
suffices to treat an affinoid domain `B`. Choose a finite injective map `Tₙ → B`, and let
`X ^ d + ∑_{i < d} aᵢ X ^ i` be the minimal polynomial of `f` over the integrally closed domain
`Tₙ`. Then `|f|sup = max_{i < d} |aᵢ|sup ^ (1 / (d - i))`; take an index `i` realising the
maximum, and a classical point `x` of `Tₙ` with `|aᵢ(x)| = |aᵢ|sup`. A root of largest absolute
value of the reduction of the minimal polynomial at `x` is the value of `f` at a classical point
`y` of `B`, and `|f|sup ≤ |aᵢ(x)| ^ (1 / (d - i)) ≤ |f(y)|`.

## Main results

* `TauCeti.MvPowerSeries.exists_pointNorm_eq_norm`: a Tate series attains its Gauss norm at a
  classical point.
* `TauCeti.MvPowerSeries.supSeminorm_eq_norm`: on a Tate algebra the supremum seminorm is the
  Gauss norm.
* `TauCeti.IsAffinoidAlgebra.exists_pointNorm_eq_supSeminorm`: **the maximum modulus principle**,
  the supremum seminorm of a nonzero affinoid algebra is attained at a classical point.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_map_sub_algebraMap_constantCoeff_le`: a Tate series of
  Gauss norm at most one, mapped by a homomorphism sending the variables to elements with
  `|·|sup ≤ ε ≤ 1`, differs from its constant coefficient by an element with `|·|sup ≤ ε`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.1.4 and
  §6.2.1, Proposition 4.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace MvPowerSeries

variable {n : ℕ}

local notation "T" => IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)

/-- **Maximum modulus principle for Tate algebras.** Every series `f ∈ K⟨X₁, …, Xₙ⟩` attains its
Gauss norm at a classical point: `|f(x)| = ‖f‖` for some maximal ideal `x`. -/
theorem exists_pointNorm_eq_norm (f : T) : ∃ x : MaximalSpectrum T, pointNorm K x f = ‖f‖ := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal T
    exact ⟨⟨m, hm⟩, by simp⟩
  -- Choose `m` of norm one exceeding every exponent of every coefficient of norm `‖f‖`; there are
  -- finitely many such coefficients since `f` is restricted and nonzero.
  have hD : {t : Fin n →₀ ℕ | ‖coeff t (f : MvPowerSeries (Fin n) K)‖ = ‖f‖}.Finite := by
    have h := f.2.eventually (gt_mem_nhds (norm_pos_iff.mpr hf))
    simp only [Filter.eventually_cofinite, not_lt, one_pow, Finsupp.prod_fun_one, mul_one] at h
    exact h.subset fun t ht ↦ ht.ge
  obtain ⟨m, hNm, hm⟩ := IsUltrametricDist.exists_lt_norm_natCast_eq_one K
    (hD.toFinset.sup Finsupp.degree)
  have hfm (t : Fin n →₀ ℕ) (ht : ‖coeff t (f : MvPowerSeries (Fin n) K)‖ = ‖f‖) (i : Fin n) :
      t i < m :=
    (Finsupp.le_degree i t).trans_lt ((Finset.le_sup (hD.mem_toFinset.mpr ht)).trans_lt hNm)
  -- Evaluate at roots of unity in the cyclotomic extension `E = K(μₘ)` with its spectral norm.
  have : NeZero (m : K) := ⟨fun h ↦ by simp [h] at hm⟩
  have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
  let E := CyclotomicField m K
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {m} K E
  let : NormedField E := spectralNorm.normedField K E
  let : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  have : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun a b ↦
      isNonarchimedean_spectralNorm (K := K) (L := E) a b
  have : CompleteSpace E := FiniteDimensional.completeSpace K E
  have hφ (r : K) : ‖algebraMap K E r‖ = ‖r‖ := norm_algebraMap' E r
  have hmE : ‖(m : E)‖ = 1 := by rw [← map_natCast (algebraMap K E), hφ, hm]
  obtain ⟨x, hx, -, hfx⟩ := exists_norm_restrictedEval₂_eq_norm (algebraMap K E) hφ
    (IsCyclotomicExtension.zeta_spec m K E) hmE f hfm
  -- The kernel of evaluation at `x` is a classical point at which `|f|` is `‖f‖`.
  let ψ : T →ₐ[K] E :=
    { restrictedEval₂ (algebraMap K E) x (fun r ↦ (hφ r).le) hx with
      commutes' := restrictedEval₂_algebraMap _ _ _ _ }
  refine ⟨⟨RingHom.ker ψ, ψ.ker_isMaximal_of_isAlgebraic⟩, ?_⟩
  rw [pointNorm_eq_spectralNorm (ψ := ψ) le_rfl, ← NormedAlgebra.norm_eq_spectralNorm K]
  exact hfx

/-- On a Tate algebra the supremum seminorm is the Gauss norm: `|f|sup = ‖f‖`. -/
@[simp]
theorem supSeminorm_eq_norm (f : T) : supSeminorm K f = ‖f‖ := by
  obtain ⟨x, hx⟩ := exists_pointNorm_eq_norm f
  exact le_antisymm (isAffinoidAlgebra_tate.supSeminorm_le_norm f)
    (hx ▸ isAffinoidAlgebra_tate.pointNorm_le_supSeminorm x f)

end MvPowerSeries

namespace IsAffinoidAlgebra

/-- The maximum modulus principle for an affinoid domain `B`: `|f|sup` is bounded by `|f(y)|` at
some classical point `y`. -/
private theorem exists_supSeminorm_le_pointNorm_of_isDomain {B : Type*} [CommRing B] [IsDomain B]
    [Algebra K B] (hB : IsAffinoidAlgebra K B) (f : B) :
    ∃ y : MaximalSpectrum B, supSeminorm K f ≤ pointNorm K y f := by
  -- A Noether normalisation `T → B` makes `B` finite and torsion-free over the integrally closed
  -- domain `T = K⟨X₁, …, Xₙ⟩`.
  obtain ⟨n, g, hg, hfin⟩ := hB.exists_finite_injective
  let T := IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)
  let := g.toRingHom.toAlgebra
  have : IsScalarTower K T B := IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Module.Finite T B := hfin
  have : Algebra.IsIntegral T B := Algebra.IsIntegral.of_finite T B
  have : FaithfulSMul T B := (faithfulSMul_iff_algebraMap_injective T B).mpr hg
  -- `|f|sup` is the spectral value of the minimal polynomial `p` of `f` over `T`, attained at a
  -- coefficient `aᵢ`; take a classical point `x` of `T` with `|aᵢ(x)| = |aᵢ|sup`.
  have hf := Algebra.IsIntegral.isIntegral (R := T) f
  have hpos := minpoly.natDegree_pos hf
  have : Nonempty (Fin (minpoly T f).natDegree) := ⟨⟨0, hpos⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (minpoly T f).natDegree ↦
    supSeminorm K ((minpoly T f).coeff i) ^ (1 / ((minpoly T f).natDegree - i : ℝ)))
  obtain ⟨x, hx⟩ := MvPowerSeries.exists_pointNorm_eq_norm ((minpoly T f).coeff i)
  obtain ⟨y, hy⟩ := hB.exists_pointNorm_coeff_le_pointNorm_pow (minpoly.monic hf) hpos
    (fun _ ↦ TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree hf) x
  refine ⟨y, ?_⟩
  rw [hB.supSeminorm_eq_iSup_minpoly_coeff_rpow (A := T) f, ← hi,
    MvPowerSeries.supSeminorm_eq_norm, ← hx]
  exact (Real.rpow_one_div_natCast_sub_le_iff (pointNorm_nonneg _) (pointNorm_nonneg f) i.2).mpr
    (hy i)

/-- **The maximum modulus principle.** On a nonzero affinoid algebra the supremum seminorm is
attained at a classical point: for every `f : A` there is a maximal ideal `x` of `A` with
`|f(x)| = |f|sup`. -/
theorem exists_pointNorm_eq_supSeminorm {A : Type*} [CommRing A] [Algebra K A] [Nontrivial A]
    (hA : IsAffinoidAlgebra K A) (f : A) :
    ∃ x : MaximalSpectrum A, pointNorm K x f = supSeminorm K f := by
  -- `|f|sup` is attained on the affinoid domain `A ⧸ 𝔭` for a minimal prime `𝔭`.
  obtain ⟨𝔭, h𝔭, hsup⟩ := hA.exists_mem_minimalPrimes_supSeminorm_eq f
  have : 𝔭.IsPrime := Ideal.IsMinimalPrime.isPrime h𝔭
  have hA𝔭 := hA.quotient 𝔭
  obtain ⟨y, hy⟩ := hA𝔭.exists_supSeminorm_le_pointNorm_of_isDomain (Ideal.Quotient.mk 𝔭 f)
  refine ⟨hA𝔭.maximalSpectrumComap (Ideal.Quotient.mkₐ K 𝔭) y,
    le_antisymm (hA.pointNorm_le_supSeminorm _ f) ?_⟩
  rw [hA𝔭.pointNorm_maximalSpectrumComap, ← hsup]
  exact hy

/-- By the maximum modulus principle, a positive real bounds the supremum seminorm strictly
exactly when it bounds every value strictly. -/
theorem supSeminorm_lt_iff {A : Type*} [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A)
    {f : A} {r : ℝ} (hr : 0 < r) : supSeminorm K f < r ↔ ∀ x, pointNorm K x f < r := by
  refine ⟨fun h x ↦ (hA.pointNorm_le_supSeminorm x f).trans_lt h, fun h ↦ ?_⟩
  cases subsingleton_or_nontrivial A with
  | inl _ => rwa [supSeminorm_eq_zero_of_subsingleton]
  | inr _ =>
    obtain ⟨x, hx⟩ := hA.exists_pointNorm_eq_supSeminorm f
    exact hx ▸ h x


open TauCeti.MvPowerSeries in
/-- A Tate series of Gauss norm at most one, mapped to an affinoid algebra `B` by a homomorphism
sending the variables to elements of supremum seminorm at most `ε ≤ 1`, differs from its constant
coefficient by an element of supremum seminorm at most `ε`. -/
theorem supSeminorm_map_sub_algebraMap_constantCoeff_le {B : Type*} [CommRing B] [Algebra K B]
    {n : ℕ} (hB : IsAffinoidAlgebra K B)
    (ψ : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] B) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hX : ∀ i, supSeminorm K (ψ ⟨X i, isRestricted_X _ i⟩) ≤ ε)
    {g : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)} (hg : ‖g‖ ≤ 1) :
    supSeminorm K (ψ g - algebraMap K B (constantCoeff (g : MvPowerSeries (Fin n) K))) ≤ ε := by
  have hT := isAffinoidAlgebra_tate (K := K) (σ := Fin n)
  -- Approximate `g` within `ε` by a polynomial `p`.
  obtain ⟨p, hp⟩ := (denseRange_polynomialToRestricted (R := K)
    (c := fun _ : Fin n ↦ 1)).exists_dist_lt g hε0
  rw [dist_eq_norm] at hp
  set P := polynomialToRestricted (fun _ : Fin n ↦ (1 : ℝ)) p with hP
  have hPg : ‖P‖ ≤ 1 := by
    have h := (IsUltrametricDist.norm_add_le_max g (P - g)).trans
      (max_le hg ((norm_sub_rev P g).trans_le (hp.le.trans hε1)))
    rwa [add_sub_cancel] at h
  -- On polynomials, `ψ` is evaluation at the images of the variables.
  have hψp : ψ P = MvPolynomial.aeval (fun i ↦ ψ ⟨X i, isRestricted_X _ i⟩) p := by
    rw [← AlgHom.comp_apply]
    congr 1
    exact MvPolynomial.algHom_ext fun i ↦ by simp
  set c₀ := p.coeff 0
  have hcoeff : constantCoeff (g : MvPowerSeries (Fin n) K) = c₀ +
      constantCoeff ((g - P : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :
        MvPowerSeries (Fin n) K) := by
    simp only [c₀, hP, AddSubgroupClass.coe_sub, coe_polynomialToRestricted, map_sub,
      ← _root_.MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    ring
  -- `ψ g - g₀ = ψ (g - p) - (g - p)₀ + (ψ p - p₀)`, and each part is at most `ε`.
  have hsplit : ψ g - algebraMap K B (constantCoeff (g : MvPowerSeries (Fin n) K)) =
      (ψ (g - P) - algebraMap K B (constantCoeff ((g - P :
        IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) : MvPowerSeries (Fin n) K))) +
        MvPolynomial.aeval (fun i ↦ ψ ⟨X i, isRestricted_X _ i⟩) (p - MvPolynomial.C c₀) := by
    rw [hcoeff, map_sub, map_sub, map_add, MvPolynomial.aeval_C, ← hψp]
    ring
  rw [hsplit]
  refine (hB.supSeminorm_add_le _ _).trans (max_le ?_ ?_)
  · have h₁ : supSeminorm K (ψ (g - P)) ≤ ε :=
      (hT.supSeminorm_map_le hB ψ _).trans ((supSeminorm_eq_norm _).trans_le hp.le)
    have h₂ : supSeminorm K (algebraMap K B (constantCoeff ((g - P :
        IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) : MvPowerSeries (Fin n) K))) ≤ ε := by
      refine supSeminorm_le hε0.le fun y ↦ ?_
      rw [pointNorm_algebraMap]
      exact (norm_constantCoeff_le _).trans hp.le
    rw [sub_eq_add_neg]
    exact (hB.supSeminorm_add_le _ _).trans (max_le h₁ ((supSeminorm_neg _).trans_le h₂))
  · refine hB.supSeminorm_aeval_le hε0.le hε1 hX (by simp [c₀]) fun t ↦ ?_
    rcases eq_or_ne t 0 with rfl | ht
    · simp [c₀]
    · rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_of_ne_zero ht, sub_zero]
      have h := norm_coeff_le_norm P t
      rw [hP, coe_polynomialToRestricted, MvPolynomial.coeff_coe] at h
      exact h.trans hPg

end IsAffinoidAlgebra

end TauCeti
