/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Algebra.MonoidAlgebra.Grading
public import TauCeti.RingTheory.GradedAlgebra.Degree.Width

/-!
# Leading coefficients, coefficient maps, and weighted graded degrees

A coefficient map preserves the existing generic leading coefficient when it does not kill that
coefficient. This applies to quotient maps at unit leading coefficients, even when lower
coefficients disappear. The separate-variable Laurent intersection uses this to retain a unit
highest coefficient over a possibly nonreduced coefficient quotient.

For an additive homomorphism `w : M →+ ι` into a linearly ordered monoid or commutative group, the
second section relates `TauCeti.GradedAlgebra.minDeg`, `maxDeg`, and `degWidth` for
`AddMonoidAlgebra.gradeBy R w` to `x.coeff.support`, `AddMonoidAlgebra.supDegree`, and
`AddMonoidAlgebra.infDegree`.
-/

public section

namespace AddMonoidAlgebra

section MapRingHom

variable {R S A B : Type*} [Semiring R] [Semiring S] [AddMonoid A]
  [LinearOrder B] [OrderBot B] {D : A → B}

/-- A coefficient homomorphism cannot increase the supremum of the exponent degrees. -/
theorem supDegree_mapRingHom_le (f : R →+* S) (p : R[A]) :
    (mapRingHom A f p).supDegree D ≤ p.supDegree D := by
  classical
  apply Finset.sup_le
  intro a ha
  apply Finset.le_sup
  simp only [Finsupp.mem_support_iff, coeff_mapRingHom] at ha ⊢
  exact fun h ↦ ha (by simp [h])

/-- A coefficient homomorphism preserves the supremum degree if it retains the leading term. -/
theorem supDegree_mapRingHom_eq_of_leadingCoeff_ne_zero (hD : Function.Injective D)
    (f : R →+* S) {p : R[A]} (hp : f (p.leadingCoeff D) ≠ 0) :
    (mapRingHom A f p).supDegree D = p.supDegree D := by
  classical
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp0
  have hl : p.leadingCoeff D = p.coeff a := by
    rw [leadingCoeff, he, Function.leftInverse_invFun hD a]
  apply le_antisymm (supDegree_mapRingHom_le f p)
  rw [he]
  apply Finset.le_sup
  simpa only [Finsupp.mem_support_iff, coeff_mapRingHom, ← hl] using hp

/-- A coefficient homomorphism preserves the leading coefficient when it does not kill it. -/
theorem leadingCoeff_mapRingHom_of_leadingCoeff_ne_zero (hD : Function.Injective D)
    (f : R →+* S) {p : R[A]} (hp : f (p.leadingCoeff D) ≠ 0) :
    (mapRingHom A f p).leadingCoeff D = f (p.leadingCoeff D) := by
  rw [leadingCoeff, supDegree_mapRingHom_eq_of_leadingCoeff_ne_zero hD f hp,
    coeff_mapRingHom, leadingCoeff]

/-- A coefficient homomorphism preserves a unit leading coefficient, including in a zero ring. -/
theorem isUnit_leadingCoeff_mapRingHom (hD : Function.Injective D) (f : R →+* S)
    {p : R[A]} (hp : IsUnit (p.leadingCoeff D)) :
    IsUnit ((mapRingHom A f p).leadingCoeff D) := by
  cases subsingleton_or_nontrivial S
  · exact isUnit_of_subsingleton _
  rw [leadingCoeff_mapRingHom_of_leadingCoeff_ne_zero hD f (hp.map f).ne_zero]
  exact hp.map f

end MapRingHom

section WeightDegree

open TauCeti.GradedAlgebra

variable {R M ι : Type*} [CommSemiring R] [AddMonoid M] [DecidableEq ι]

section AddMonoid

variable [AddMonoid ι] [LinearOrder ι] (w : M →+ ι)

/-- Every supported exponent of `x : R[M]` has weight at least `minDeg (gradeBy R w) x`. -/
theorem minDeg_gradeBy_le_of_mem_support {x : R[M]} {m : M} (hm : m ∈ x.coeff.support) :
    minDeg (gradeBy R w) x ≤ w m :=
  minDeg_le_of_decompose_ne_zero (gradeBy R w)
    ((coe_decompose_gradeBy_ne_zero_iff w x (w m)).mpr ⟨m, hm, rfl⟩)

/-- Every supported exponent of `x : R[M]` has weight at most `maxDeg (gradeBy R w) x`. -/
theorem le_maxDeg_gradeBy_of_mem_support {x : R[M]} {m : M} (hm : m ∈ x.coeff.support) :
    w m ≤ maxDeg (gradeBy R w) x :=
  le_maxDeg_of_decompose_ne_zero (gradeBy R w)
    ((coe_decompose_gradeBy_ne_zero_iff w x (w m)).mpr ⟨m, hm, rfl⟩)

/-- For nonzero `x : R[M]`, `minDeg (gradeBy R w) x` is attained at some supported exponent. -/
theorem exists_mem_support_minDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    ∃ m ∈ x.coeff.support, w m = minDeg (gradeBy R w) x := by
  have hne := minHomogPart_ne_zero (gradeBy R w) hx
  rw [minHomogPart_def] at hne
  exact (coe_decompose_gradeBy_ne_zero_iff w x _).mp hne

/-- For nonzero `x : R[M]`, `maxDeg (gradeBy R w) x` is attained at some supported exponent. -/
theorem exists_mem_support_maxDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    ∃ m ∈ x.coeff.support, w m = maxDeg (gradeBy R w) x := by
  have hne := maxHomogPart_ne_zero (gradeBy R w) hx
  rw [maxHomogPart_def] at hne
  exact (coe_decompose_gradeBy_ne_zero_iff w x _).mp hne

/-- For nonzero `x : R[M]`, `supDegree` along `w : M → WithBot ι` agrees with
`maxDeg (gradeBy R w) x`. -/
theorem supDegree_withBot_eq_maxDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    x.supDegree (fun m ↦ (w m : WithBot ι)) = maxDeg (gradeBy R w) x := by
  refine le_antisymm
    (Finset.sup_le fun m hm ↦ WithBot.coe_le_coe.mpr (le_maxDeg_gradeBy_of_mem_support w hm)) ?_
  obtain ⟨m, hm, hwm⟩ := exists_mem_support_maxDeg_gradeBy w hx
  rw [← hwm]
  exact Finset.le_sup (f := fun m ↦ (w m : WithBot ι)) hm

/-- For nonzero `x : R[M]`, `infDegree` along `w : M → WithTop ι` agrees with
`minDeg (gradeBy R w) x`. -/
theorem infDegree_withTop_eq_minDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    x.infDegree (fun m ↦ (w m : WithTop ι)) = minDeg (gradeBy R w) x := by
  refine le_antisymm ?_
    (Finset.le_inf fun m hm ↦ WithTop.coe_le_coe.mpr (minDeg_gradeBy_le_of_mem_support w hm))
  obtain ⟨m, hm, hwm⟩ := exists_mem_support_minDeg_gradeBy w hx
  rw [← hwm]
  exact Finset.inf_le (f := fun m ↦ (w m : WithTop ι)) hm

end AddMonoid

section AddCommGroup

variable [AddCommGroup ι] [LinearOrder ι] (w : M →+ ι)

/-- The difference of weights of any two supported exponents of `x` is bounded above by
`degWidth (gradeBy R w) x`. -/
theorem le_degWidth_gradeBy_of_mem_support [IsOrderedAddMonoid ι] {x : R[M]} {m₁ m₂ : M}
    (hm₁ : m₁ ∈ x.coeff.support) (hm₂ : m₂ ∈ x.coeff.support) :
    w m₁ - w m₂ ≤ degWidth (gradeBy R w) x := by
  rw [degWidth_def]
  exact sub_le_sub (le_maxDeg_gradeBy_of_mem_support w hm₁)
    (minDeg_gradeBy_le_of_mem_support w hm₂)

/-- The degree width of `x : R[M]` along `w` vanishes if and only if `w` takes the same value on
all supported exponents of `x`. -/
theorem degWidth_gradeBy_eq_zero_iff_forall_mem_support {x : R[M]} :
    degWidth (gradeBy R w) x = 0 ↔
      ∀ m₁ ∈ x.coeff.support, ∀ m₂ ∈ x.coeff.support, w m₁ = w m₂ := by
  rw [degWidth_eq_zero_iff]
  refine ⟨fun ⟨d, hd⟩ m₁ hm₁ m₂ hm₂ ↦ by rw [hd m₁ hm₁, hd m₂ hm₂], fun h ↦ ?_⟩
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ Submodule.zero_mem _⟩
  · obtain ⟨m₀, hm₀⟩ := Finsupp.support_nonempty_iff.mpr (mt coeff_eq_zero.mp hx)
    exact ⟨w m₀, fun m hm ↦ h m hm m₀ hm₀⟩

end AddCommGroup

end WeightDegree

end AddMonoidAlgebra
