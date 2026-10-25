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
  have : CompleteSpace E := FiniteDimensional.complete K E
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

end IsAffinoidAlgebra

end TauCeti
