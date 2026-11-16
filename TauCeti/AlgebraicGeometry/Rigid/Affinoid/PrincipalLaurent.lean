/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Subdomain
import TauCeti.RingTheory.Affinoid.SupSeminorm

/-!
# Laurent exhaustions of principal Zariski opens

For a nonzero scalar `c`, the Laurent cutoff `|c| ≤ |f|` is a rational affinoid subdomain.
For `0 < |ϖ| < 1`, the cutoffs with `c = ϖⁿ` increase to the principal Zariski open `D(f)`.
Every affinoid subdomain contained in `D(f)` lies in a single cutoff, since the inverse of the
restricted function has bounded supremum seminorm.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§7.2.3 and 9.1.4.
-/

public section

namespace TauCeti

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- A principal Zariski open `D(f)` is exhausted by the rational domains `R(ϖⁿ / f)` for any
`‖ϖ‖ < 1`. -/
theorem basicOpen_eq_iUnion_rationalDomain (hA : IsAffinoidAlgebra K A) (f : A)
    {ϖ : K} (hϖ₁ : ‖ϖ‖ < 1) :
    (MaximalSpectrum.basicOpen f : Set (MaximalSpectrum A)) =
      ⋃ n : ℕ, rationalDomain K f (fun _ : Fin 1 ↦ algebraMap K A (ϖ ^ n)) := by
  ext x
  simp only [SetLike.mem_coe, MaximalSpectrum.mem_basicOpen, Set.mem_iUnion,
    mem_rationalDomain, forall_const, pointNorm_algebraMap, norm_pow, ne_eq,
    hA.pointNorm_eq_zero_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨_, hx, _⟩ ↦ hx⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (lt_of_le_of_ne (pointNorm_nonneg f) (Ne.symm (hA.pointNorm_eq_zero_iff.not.mpr hx))) hϖ₁
  exact ⟨n, hx, hn.le⟩

/-- The point norms of a unit are uniformly bounded below by some power of any
nonnegative real number less than one. -/
theorem IsAffinoidAlgebra.exists_pow_le_pointNorm_of_isUnit (hA : IsAffinoidAlgebra K A)
    {f : A} (hf : IsUnit f) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    ∃ n : ℕ, ∀ x : MaximalSpectrum A, r ^ n ≤ pointNorm K x f := by
  obtain ⟨u, hu⟩ := hf.exists_right_inv
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r ^ n * supSeminorm K u ≤ 1 := by
    rcases eq_or_lt_of_le (supSeminorm_nonneg (K := K) u) with h0 | hpos
    · exact ⟨0, by simp [← h0]⟩
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) hr₁
      exact ⟨n, (inv_mul_cancel₀ hpos.ne' ▸ mul_lt_mul_of_pos_right hn hpos).le⟩
  refine ⟨n, fun x ↦ ?_⟩
  have h1 : 1 ≤ pointNorm K x f * supSeminorm K u := by
    rw [← pointNorm_one (K := K) (x := x), ← hu, hA.pointNorm_mul]
    exact mul_le_mul_of_nonneg_left (hA.pointNorm_le_supSeminorm x u) (pointNorm_nonneg _)
  calc r ^ n ≤ r ^ n * (pointNorm K x f * supSeminorm K u) :=
        le_mul_of_one_le_right (pow_nonneg hr₀ _) h1
    _ = pointNorm K x f * (r ^ n * supSeminorm K u) := by ring
    _ ≤ pointNorm K x f := mul_le_of_le_one_right (pointNorm_nonneg _) hn

namespace AffinoidSubdomain

/-- The affinoid Laurent subdomain `|c| ≤ |f|`, for a nonzero scalar `c`. -/
noncomputable def principalLaurent (hA : IsAffinoidAlgebra K A) (f : A) (c : Kˣ) :
    AffinoidSubdomain K A :=
  rational hA (Ideal.eq_top_of_isUnit_mem _
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self 0)))
    (c.isUnit.map (algebraMap K A)) :
    Ideal.span (insert f (Set.range (fun _ : Fin 1 ↦ algebraMap K A (c : K)))) = ⊤)

/-- The Laurent cutoff is the rational domain with denominator `f` and sole numerator `c`. -/
theorem coe_principalLaurent_eq_rationalDomain (hA : IsAffinoidAlgebra K A) (f : A) (c : Kˣ) :
    (principalLaurent hA f c : Set (MaximalSpectrum A)) =
      rationalDomain K f (fun _ : Fin 1 ↦ algebraMap K A (c : K)) :=
  coe_rational hA _

/-- The underlying set of the Laurent cutoff is its defining lower bound. -/
@[simp]
theorem coe_principalLaurent (hA : IsAffinoidAlgebra K A) (f : A) (c : Kˣ) :
    (principalLaurent hA f c : Set (MaximalSpectrum A)) =
      {x | ‖(c : K)‖ ≤ pointNorm K x f} := by
  ext x
  rw [coe_principalLaurent_eq_rationalDomain]
  simp only [mem_rationalDomain, pointNorm_algebraMap, forall_const, Set.mem_ofPred_eq]
  exact ⟨And.right, fun h ↦ ⟨ne_of_gt ((norm_pos_iff.mpr c.ne_zero).trans_le h), h⟩⟩

/-- Membership in the Laurent cutoff is its defining lower bound. -/
@[simp]
theorem mem_principalLaurent (hA : IsAffinoidAlgebra K A) (f : A) (c : Kˣ) (x : MaximalSpectrum A) :
    x ∈ principalLaurent hA f c ↔ ‖(c : K)‖ ≤ pointNorm K x f :=
  Set.ext_iff.mp (coe_principalLaurent hA f c) x

/-- Laurent cutoffs with smaller scalar norm contain those with larger scalar norm. -/
theorem principalLaurent_le (hA : IsAffinoidAlgebra K A) {f : A} {c d : Kˣ}
    (h : ‖(d : K)‖ ≤ ‖(c : K)‖) : principalLaurent hA f c ≤ principalLaurent hA f d :=
  fun x hx ↦ (mem_principalLaurent hA f d x).mpr (h.trans ((mem_principalLaurent hA f c x).mp hx))

/-- The Laurent cutoffs form an increasing sequence when the scalar norm is at most one. -/
theorem monotone_principalLaurent_pow (hA : IsAffinoidAlgebra K A) (f : A) (ϖ : Kˣ)
    (hϖ : ‖(ϖ : K)‖ ≤ 1) : Monotone (fun n : ℕ ↦ principalLaurent hA f (ϖ ^ n)) := by
  intro m n hmn
  apply principalLaurent_le
  simpa only [Units.val_pow_eq_pow_val, norm_pow] using
    pow_le_pow_of_le_one (norm_nonneg (ϖ : K)) hϖ hmn

/-- Every affinoid subdomain avoiding the zero locus of `f` lies in one Laurent cutoff. -/
theorem exists_le_principalLaurent_pow (U : AffinoidSubdomain K A) (hA : IsAffinoidAlgebra K A)
    (f : A) (ϖ : Kˣ) (hϖ : ‖(ϖ : K)‖ < 1) (hU : ∀ x ∈ U, f ∉ x.asIdeal) :
    ∃ n : ℕ, U ≤ principalLaurent hA f (ϖ ^ n) := by
  have hf : IsUnit (U.toSections f) :=
    U.isAffinoidAlgebra.isUnit_iff_forall_pointNorm_ne_zero.mpr fun y ↦ by
      rw [← U.isAffinoidAlgebra.pointNorm_maximalSpectrumComap U.toSections]
      exact hA.pointNorm_eq_zero_iff.not.mpr
        (hU _ (U.isAffinoidSubdomainMap.range_maximalSpectrumComap_subset ⟨y, rfl⟩))
  obtain ⟨n, hn⟩ := U.isAffinoidAlgebra.exists_pow_le_pointNorm_of_isUnit hf (norm_nonneg _) hϖ
  refine ⟨n, fun x hx ↦ ?_⟩
  have hx' : x ∈ (U : Set (MaximalSpectrum A)) := hx
  rw [← U.isAffinoidSubdomainMap.range_maximalSpectrumComap hA] at hx'
  obtain ⟨y, rfl⟩ := hx'
  rw [mem_principalLaurent, Units.val_pow_eq_pow_val, norm_pow,
    IsAffinoidAlgebra.pointNorm_maximalSpectrumComap]
  exact hn y

end AffinoidSubdomain

end TauCeti
