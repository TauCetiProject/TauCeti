/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PeriodGroup
public import TauCeti.RingTheory.NovikovSeries.Grading
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval

/-!
# The Floer Novikov ring

Let `Γ = PeriodGroup ω c` be the period group of a closed symplectic manifold, with symplectic
area `ω` and first Chern number `c`. Capped Hamiltonian Floer complexes are modules over the
*Floer Novikov ring* `Λ`: Novikov series `∑ a_γ e^γ` in the classes `γ ∈ Γ`, where the monomial
`e^γ` has

* valuation `ν(γ) = -ω(γ)`: for every bound `C` only finitely many `γ` with `a_γ ≠ 0` have
  `ν(γ) < C`, so infinitely many terms are allowed only as the area tends to `-∞`;
* degree `2 c(γ)`, the grading shift of a recapping by `γ`.

We write `Λ` as `NovikovSeries R Γ (-area)`, so the ring structure, the period-filtration
topology and the completeness of Novikov series apply to it directly, and we grade it by the
homomorphism `PeriodGroup.degree = 2 • chern`. Since `Γ` need not be discrete in area, `Λ` is not
in general the direct sum of its homogeneous pieces; the graded structure is the graded monoid
of homogeneous series of `TauCeti.RingTheory.NovikovSeries.Grading`.

The two classical coefficient regimes are distinguished by this grading.

* If `c` vanishes on spherical classes, every series has degree `0`: the grading of the Floer
  complex is entirely carried by the generators.
* If `ω = τ c` on spherical classes (spherical monotonicity), each degree is carried by at most
  one class, so every homogeneous series is a monomial, and the homogeneous series span exactly
  the group ring `R[Γ]` of the cyclic group `Γ` (`PeriodGroup.isAddCyclic_of_area_eq_mul_chern`):
  this is the finite Laurent model of the monotone coefficient ring. When moreover `τ > 0`, the
  Novikov condition says exactly that the degrees of the support are bounded above.

## Main definitions

* `TauCeti.Floer.PeriodGroup.degree`: the degree `γ ↦ 2 c(γ)` of the monomial `e^γ`.
* `TauCeti.Floer.NovikovRing R ω c`: the Floer Novikov ring over `R`.

## Main results

* `TauCeti.Floer.NovikovRing.gradeBy_degree_eq_bot_of_odd`: there are no nonzero series of odd
  degree.
* `TauCeti.Floer.NovikovRing.gradeBy_degree_zero_eq_top`,
  `TauCeti.Floer.NovikovRing.gradeBy_degree_eq_bot_of_chern_eq_zero`: if the first Chern number
  vanishes, the ring is concentrated in degree `0`.
* `TauCeti.Floer.NovikovRing.eq_single_of_mem_gradeBy_degree`: for a spherically monotone pair,
  every homogeneous series is a monomial.
* `TauCeti.Floer.NovikovRing.mem_iSup_gradeBy_degree_iff`: for a spherically monotone pair, the
  homogeneous series span exactly the finitely supported series, the image of `R[Γ]`.
* `TauCeti.Floer.NovikovRing.forall_finite_lt_iff_bddAbove_degree`: for a positively monotone
  pair, a coefficient function is a Floer Novikov series exactly when the degrees of its support
  are bounded above.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the construction of
  the Novikov ring in the chapter on quantum cohomology.
-/

public section

noncomputable section

open Function Set

namespace TauCeti.Floer

variable {S : Type*} [AddGroup S]

namespace PeriodGroup

variable (ω : S →+ ℝ) (c : S →+ ℤ)

/-- The degree `2 c(γ)` of the monomial `e^γ` of the Floer Novikov ring: recapping an orbit by
`γ` shifts its Conley–Zehnder grading by `2 c(γ)`. -/
def degree : PeriodGroup ω c →+ ℤ :=
  2 • chern ω c

/-- The degree of a class is twice its first Chern number. -/
@[simp]
theorem degree_apply (γ : PeriodGroup ω c) : degree ω c γ = 2 * chern ω c γ := by
  rw [degree, AddMonoidHom.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]

/-- Degrees in the period group are even. -/
theorem even_degree (γ : PeriodGroup ω c) : Even (degree ω c γ) :=
  ⟨chern ω c γ, by rw [degree_apply, two_mul]⟩

variable {ω c} in
/-- The degree is injective exactly when the first Chern number is. -/
theorem degree_injective_iff : Injective (degree ω c) ↔ Injective (chern ω c) := by
  refine ⟨fun h γ γ' hγ => h ?_, fun h γ γ' hγ => h ?_⟩
  · rw [degree_apply, degree_apply, hγ]
  · simpa using hγ

end PeriodGroup

open PeriodGroup

variable (R : Type*) (ω : S →+ ℝ) (c : S →+ ℤ)

/-- The Floer Novikov ring over `R`: Novikov series `∑ a_γ e^γ` over the period group, with
valuation `ν(γ) = -ω(γ)`, so that for every bound `C` only finitely many classes with nonzero
coefficient have area greater than `-C`. It is graded by `PeriodGroup.degree`. -/
abbrev NovikovRing [Zero R] : Type _ :=
  NovikovSeries R (PeriodGroup ω c) (-area ω c)

namespace NovikovRing

variable {R ω c} [Semiring R]

/-- There are no nonzero Floer Novikov series of odd degree. -/
theorem gradeBy_degree_eq_bot_of_odd {k : ℤ} (hk : Odd k) :
    NovikovSeries.gradeBy R (-area ω c) (degree ω c) k = ⊥ :=
  NovikovSeries.gradeBy_eq_bot fun ⟨γ, hγ⟩ =>
    Int.not_even_iff_odd.2 hk (hγ ▸ even_degree ω c γ)

section ChernZero

variable (h : ∀ s, c s = 0)
include h

/-- If the first Chern number vanishes on spherical classes, every Floer Novikov series has
degree `0`. -/
theorem gradeBy_degree_zero_eq_top :
    NovikovSeries.gradeBy R (-area ω c) (degree ω c) 0 = ⊤ :=
  NovikovSeries.gradeBy_eq_top fun γ => by rw [degree_apply, chern_eq_zero h, mul_zero]

/-- If the first Chern number vanishes on spherical classes, there are no nonzero Floer Novikov
series of nonzero degree. -/
theorem gradeBy_degree_eq_bot_of_chern_eq_zero {k : ℤ} (hk : k ≠ 0) :
    NovikovSeries.gradeBy R (-area ω c) (degree ω c) k = ⊥ :=
  NovikovSeries.gradeBy_eq_bot fun ⟨γ, hγ⟩ =>
    hk (by rw [← hγ, degree_apply, chern_eq_zero h, mul_zero])

end ChernZero

section Monotone

variable {τ : ℝ} (h : ∀ s, ω s = τ * c s)
include h

/-- For a spherically monotone pair, the degree embeds the period group into `ℤ`. -/
theorem degree_injective_of_area_eq_mul_chern : Injective (degree ω c) :=
  degree_injective_iff.2 (chern_injective_of_area_eq_mul_chern h)

/-- For a spherically monotone pair, a Floer Novikov series of the degree of `γ` is the monomial
`a_γ e^γ`. -/
theorem eq_single_of_mem_gradeBy_degree {γ : PeriodGroup ω c} {a : NovikovRing R ω c}
    (ha : a ∈ NovikovSeries.gradeBy R (-area ω c) (degree ω c) (degree ω c γ)) :
    a = NovikovSeries.single γ (a.coeff γ) :=
  NovikovSeries.eq_single_of_mem_gradeBy (degree_injective_of_area_eq_mul_chern h) ha

/-- For a spherically monotone pair, the homogeneous Floer Novikov series span exactly the
finitely supported series, that is, the image of the group ring `R[Γ]`
(`TauCeti.NovikovSeries.mem_range_ofFinsupp_iff`). -/
theorem mem_iSup_gradeBy_degree_iff {a : NovikovRing R ω c} :
    a ∈ ⨆ k, NovikovSeries.gradeBy R (-area ω c) (degree ω c) k ↔ a.support.Finite :=
  NovikovSeries.mem_iSup_gradeBy_iff fun _ =>
    ((subsingleton_singleton.preimage (degree_injective_of_area_eq_mul_chern h)).finite.image
      _).bddAbove

/-- For a positively monotone pair, a coefficient function on the period group satisfies the
Novikov condition of the Floer Novikov ring exactly when the degrees of its support are bounded
above. -/
theorem forall_finite_lt_iff_bddAbove_degree (hτ : 0 < τ) (g : PeriodGroup ω c → R) :
    (∀ C : ℝ, {γ | g γ ≠ 0 ∧ (-area ω c) γ < C}.Finite) ↔
      BddAbove (degree ω c '' support g) := by
  -- On the period group `-area = -(τ / 2) • degree`.
  have hval (γ : PeriodGroup ω c) : (-area ω c) γ = -(τ / 2) * degree ω c γ := by
    rw [AddMonoidHom.neg_apply, area_eq_mul_chern h, degree_apply]
    push_cast
    ring
  refine ⟨fun hg => ?_, fun ⟨D, hD⟩ C => ?_⟩
  · obtain ⟨D, hD⟩ := ((hg 0).image (degree ω c)).bddAbove
    refine ⟨max D 0, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    by_cases hpos : 0 < degree ω c γ
    · refine le_max_of_le_left (hD ⟨γ, ⟨hγ, ?_⟩, rfl⟩)
      rw [hval]
      have : (0 : ℝ) < degree ω c γ := by exact_mod_cast hpos
      nlinarith
    · exact le_max_of_le_right (not_lt.1 hpos)
  · -- The support below `C` has degrees in `[⌊-2C/τ⌋, D]`, a finite set of integers.
    refine ((finite_Icc ⌊-(2 * C / τ)⌋ D).preimage
      (degree_injective_of_area_eq_mul_chern h).injOn).subset ?_
    rintro γ ⟨hγ, hC⟩
    refine ⟨Int.floor_le_iff.2 ?_, hD ⟨γ, hγ, rfl⟩⟩
    rw [hval] at hC
    have hdeg : -(2 * C / τ) < degree ω c γ := by
      rw [neg_lt, lt_div_iff₀ hτ]
      linarith
    linarith

/-- For a positively monotone pair, the degrees of the support of a Floer Novikov series are
bounded above. -/
theorem bddAbove_degree_image_support (hτ : 0 < τ) (a : NovikovRing R ω c) :
    BddAbove (degree ω c '' a.support) := by
  have hsupp : a.support = support a.coeff :=
    Set.ext fun _ => NovikovSeries.mem_support.trans Function.mem_support.symm
  rw [hsupp]
  exact (forall_finite_lt_iff_bddAbove_degree h hτ a.coeff).1 a.finite_lt

end Monotone

end NovikovRing

end TauCeti.Floer
