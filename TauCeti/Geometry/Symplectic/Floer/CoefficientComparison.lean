/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PeriodGroup
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Comparing quantum and Floer coefficients

Quantum coefficients use the area period `ω`, whereas Floer coefficients use the negative
area period. The comparison sends a class `A` to the negative of its image in the chosen
Floer class group: `q^A ↦ e^(-q A)`. This preserves periods, so it extends to a continuous
unital homomorphism of the completed rings. Its coefficients are finite sums even if the
class-group map has infinite kernel or area has dense image.

We allow any class-group homomorphism preserving area. If it also preserves a Chern map,
the comparison negates Chern number on homogeneous supports. Thus raw Floer coefficient
degree `2 c₁` becomes quantum coefficient degree after cochain regrading. For a quotient by
any subgroup of the joint area/Chern kernel, use the descended area and Chern homomorphisms.
`periodGroupComparison` specializes to the quotient by the entire joint kernel. In that case
two monomials with the same nonzero coefficient become equal exactly when their areas and
Chern numbers agree. No individual quantum invariant is assumed to descend without summation.

The construction reuses `NovikovSeries.mapRingHom`; no augmentation at `q = 1` is involved.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the Novikov
  coefficient conventions in the chapter on quantum cohomology.
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovSeries

variable {R S Γ : Type*}

section Comparison

variable [AddMonoid S] [AddCommGroup Γ]
  {ω : S →+ ℝ} {Ω : Γ →+ ℝ}

section Semiring

variable [Semiring R] (q : S →+ Γ) (hω : ∀ A, Ω (q A) = ω A)

/-- The completed coefficient comparison `q^A ↦ e^(-q A)`, with source period `ω` and
target period `-Ω`. Area preservation makes it a unital ring homomorphism. -/
def coefficientComparison : NovikovSeries R S ω →+* NovikovSeries R Γ (-Ω) :=
  mapRingHom (RingHom.id R) (-q) ⟨1, one_pos, period_rescale_neg hω⟩

/-- The comparison is the existing finite-fibre Novikov pushforward along negative class
projection. -/
theorem coefficientComparison_apply (a : NovikovSeries R S ω) :
    coefficientComparison q hω a =
      map (RingHom.id R : R →+ R) (-q) ⟨1, one_pos, period_rescale_neg hω⟩ a := by
  rw [coefficientComparison, mapRingHom_apply]

/-- The comparison sends a quantum monomial to its negatively indexed Floer monomial. -/
@[simp]
theorem coefficientComparison_single (A : S) (r : R) :
    coefficientComparison q hω (single A r) = single (-q A) r := by
  simp [coefficientComparison]

/-- A coefficient of the comparison is the finite sum over its supported fibre. -/
theorem coeff_coefficientComparison (a : NovikovSeries R S ω) (γ : Γ) :
    (coefficientComparison q hω a).coeff γ =
      ∑ A ∈ (finite_support_inter_preimage_singleton (N' := -Ω) a (φ := -q)
        ⟨1, one_pos, period_rescale_neg hω⟩ γ).toFinset, a.coeff A := by
  classical
  rw [coefficientComparison_apply]
  apply coeff_map_eq_sum (RingHom.id R : R →+ R) (-q) _ a
  · exact fun A hA => (Set.Finite.mem_toFinset _).2 hA
  · intro A hA
    exact ((Set.Finite.mem_toFinset _).1 hA).2

/-- No new support classes appear except images under negative class projection. -/
theorem support_coefficientComparison_subset (a : NovikovSeries R S ω) :
    (coefficientComparison q hω a).support ⊆ (-q) '' a.support := by
  rw [coefficientComparison_apply]
  exact support_map_subset _ _ _ a

/-- A quotient of class groups gives a surjective comparison, without a finite-kernel
assumption. Each target series can be lifted using one representative of each exponent. -/
theorem coefficientComparison_surjective (hq : Function.Surjective q) :
    Function.Surjective (coefficientComparison (R := R) q hω) := by
  intro b
  obtain ⟨a, ha⟩ := map_surjective (RingHom.id R : R →+ R) (-q)
    (N := ω) (N' := -Ω) ⟨1, one_pos, period_rescale_neg hω⟩
    Function.surjective_id (neg_surjective.comp hq) b
  exact ⟨a, (coefficientComparison_apply q hω a).trans ha⟩

/-- If source and target Chern maps agree under class projection, the comparison negates the
Chern number of a homogeneous support. -/
theorem chern_support_coefficientComparison (c : S →+ ℤ) (c' : Γ →+ ℤ)
    (hc : ∀ A, c' (q A) = c A) {k : ℤ} {a : NovikovSeries R S ω}
    (ha : ∀ A ∈ a.support, c A = k) :
    ∀ γ ∈ (coefficientComparison q hω a).support, c' γ = -k := by
  intro γ hγ
  obtain ⟨A, hA, rfl⟩ := support_coefficientComparison_subset q hω a hγ
  simp [hc A, ha A hA]

end Semiring

section Ring

variable [Ring R] (q : S →+ Γ) (hω : ∀ A, Ω (q A) = ω A)

/-- The coefficient comparison is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_coefficientComparison :
    Continuous (coefficientComparison (R := R) q hω) :=
  continuous_mapRingHom _ _ _

/-- The comparison preserves every energy cutoff, including all reference-class constants
that have already been incorporated into that cutoff. -/
theorem coefficientComparison_mem_periodFiltration {C : ℝ} {a : NovikovSeries R S ω}
    (ha : a ∈ periodFiltration R ω C) :
    coefficientComparison q hω a ∈ periodFiltration R (-Ω) C := by
  rw [coefficientComparison_apply]
  simpa only [one_mul] using map_mem_periodFiltration (RingHom.id R : R →+ R) (-q)
    (N' := -Ω) _ zero_le_one (period_rescale_neg hω) ha

end Ring

end Comparison

section PeriodGroup

variable [AddCommGroup S] (ω : S →+ ℝ) (c : S →+ ℤ)

/-- Descent from a common class group to the Floer joint-period quotient, with the sign
change `q^A ↦ e^(-[A])` and finite summation of all coefficients having that image. -/
def periodGroupComparison [Semiring R] :
    NovikovSeries R S ω →+* NovikovSeries R (PeriodGroup ω c) (-PeriodGroup.area ω c) :=
  coefficientComparison (QuotientAddGroup.mk' (ω.prod c).ker) (PeriodGroup.area_mk ω c)

/-- The joint-period comparison is the signed coefficient comparison for the canonical
quotient projection. This gives access to its finite coefficient-sum and support formulas. -/
theorem periodGroupComparison_apply [Semiring R] (a : NovikovSeries R S ω) :
    periodGroupComparison ω c a =
      coefficientComparison (QuotientAddGroup.mk' (ω.prod c).ker)
        (PeriodGroup.area_mk ω c) a :=
  (rfl)

/-- The joint-period comparison sends `q^A` to `e^(-[A])`. -/
@[simp]
theorem periodGroupComparison_single [Semiring R] (A : S) (r : R) :
    periodGroupComparison ω c (single A r) = single (-(A : PeriodGroup ω c)) r :=
  coefficientComparison_single _ _ _ _

/-- Descent to the joint-period quotient is surjective even when area alone fails to
separate classes. -/
theorem periodGroupComparison_surjective [Semiring R] :
    Function.Surjective (periodGroupComparison (R := R) ω c) :=
  coefficientComparison_surjective _ _ (QuotientAddGroup.mk'_surjective _)

/-- The joint-period comparison is continuous for the energy topologies. -/
@[fun_prop]
theorem continuous_periodGroupComparison [Ring R] :
    Continuous (periodGroupComparison (R := R) ω c) :=
  continuous_coefficientComparison _ _

/-- Monomial descent identifies precisely the joint periods, retaining equal-area classes
of different Chern number. The coefficient is assumed nonzero. -/
theorem periodGroupComparison_single_eq_iff [Semiring R] {r : R} (hr : r ≠ 0) (A B : S) :
    periodGroupComparison ω c (single A r) = periodGroupComparison ω c (single B r) ↔
      ω A = ω B ∧ c A = c B := by
  rw [periodGroupComparison_single, periodGroupComparison_single]
  constructor
  · intro h
    have hs := congrArg NovikovSeries.support h
    rw [support_single_of_ne hr, support_single_of_ne hr, Set.singleton_eq_singleton_iff,
      neg_inj] at hs
    exact PeriodGroup.mk_eq_mk_iff.1 hs
  · intro h
    rw [PeriodGroup.mk_eq_mk_iff.2 h]

end PeriodGroup

end TauCeti.Floer
