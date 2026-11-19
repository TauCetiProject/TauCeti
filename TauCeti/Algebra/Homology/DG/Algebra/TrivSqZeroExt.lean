/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation

/-!
# The differential graded algebra of a derivation

For a commutative `S`-algebra `R`, a symmetric `R`-module `M` and an `S`-linear derivation
`D : R → M`, the trivial square-zero extension `R ⊕ M` (Mathlib's `TrivSqZeroExt R M`), with `R` in
degree `0` and `M` in degree `1`, is a differential graded algebra for the differential
`(r, m) ↦ (0, D r)`.  It is the two-term complex `R → M` made multiplicative: the Leibniz rule
for `d` is exactly the Leibniz rule for `D`, and `M · M = 0` makes it graded-commutative.

Its cohomology is `ker D` in degree `0` and `coker D` in degree `1`.  This file records the
consequence used for interval objects: the unit `S → R ⊕ M` is a quasi-isomorphism exactly when
`S → R` is injective, `ker D` consists of scalars and `D` is surjective, and then so is every
augmentation `R ⊕ M → S`.  The basic example is the polynomial interval `Λ(t, dt)` of rational
homotopy theory, where `R = M = K[t]` and `D` is differentiation
(`TauCeti.AlgebraicTopology.RationalHomotopy.PolynomialInterval`).

## Main definitions

* `TrivSqZeroExt.grading`: the grading of `R ⊕ M` with `R` in degree `0` and `M` in degree `1`.
* `Derivation.trivSqZeroExtDifferential`: the differential `(r, m) ↦ (0, D r)` of a derivation.
* `Derivation.trivSqZeroExtAugmentation`: the augmentation `(r, m) ↦ φ r` of a character
  `φ : R → S`.

## Main results

* `TrivSqZeroExt.instGradedAlgebraGrading`: `R ⊕ M` is a graded algebra.
* `TrivSqZeroExt.mul_comm_of_mem_grading`: `R ⊕ M` is graded-commutative.
* `Derivation.isDGAlgebra_trivSqZeroExtDifferential`: `R ⊕ M` is a differential graded algebra.
* `Derivation.bijective_cohomologyMap_unitHom_iff`: the unit `S → R ⊕ M` is a quasi-isomorphism
  exactly when `S → R` is injective and `D` is surjective with kernel the scalars.
* `Derivation.bijective_cohomologyMap_trivSqZeroExtAugmentation_iff`: the same criterion for
  every augmentation.
-/

public section

open DirectSum TauCeti

@[inherit_doc] local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

section Grading

variable (S R M : Type*) [CommSemiring S] [Semiring R] [AddCommMonoid M] [Module S R]
  [Module S M]

/-- The grading of the trivial square-zero extension `R ⊕ M` with `R` in degree `0`, `M` in degree
`1`, and nothing in any other degree: the degree-`n` piece consists of the `x` whose `R`-component
vanishes unless `n = 0` and whose `M`-component vanishes unless `n = 1`. -/
def grading (n : ℤ) : Submodule S (tsze R M) where
  carrier := {x | (n ≠ 0 → x.fst = 0) ∧ (n ≠ 1 → x.snd = 0)}
  add_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨fun hn ↦ by simp [hx₁ hn, hy₁ hn], fun hn ↦ by simp [hx₂ hn, hy₂ hn]⟩
  zero_mem' := ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  smul_mem' := by
    rintro s x ⟨hx₁, hx₂⟩
    exact ⟨fun hn ↦ by simp [hx₁ hn], fun hn ↦ by simp [hx₂ hn]⟩

variable {S R M}

/-- An element has degree `n` when its `R`-component vanishes unless `n = 0` and its
`M`-component vanishes unless `n = 1`. -/
theorem mem_grading_iff {n : ℤ} {x : tsze R M} :
    x ∈ grading S R M n ↔ (n ≠ 0 → x.fst = 0) ∧ (n ≠ 1 → x.snd = 0) :=
  Iff.rfl

/-- The elements of degree `0` are those with zero `M`-component. -/
@[simp]
theorem mem_grading_zero_iff {x : tsze R M} : x ∈ grading S R M 0 ↔ x.snd = 0 := by
  simp [mem_grading_iff]

/-- The elements of degree `1` are those with zero `R`-component. -/
@[simp]
theorem mem_grading_one_iff {x : tsze R M} : x ∈ grading S R M 1 ↔ x.fst = 0 := by
  simp [mem_grading_iff]

/-- Every degree other than `0` and `1` is zero. -/
theorem grading_eq_bot {n : ℤ} (h₀ : n ≠ 0) (h₁ : n ≠ 1) : grading S R M n = ⊥ := by
  ext x
  simp only [mem_grading_iff, h₀, h₁, ne_eq, not_false_eq_true, forall_const, Submodule.mem_bot]
  exact ⟨fun h ↦ ext h.1 h.2, fun h ↦ by simp [h]⟩

/-- `R` sits in degree `0`. -/
theorem inl_mem_grading_zero (r : R) : inl r ∈ grading S R M 0 := by
  simp

/-- `M` sits in degree `1`. -/
theorem inr_mem_grading_one (m : M) : inr m ∈ grading S R M 1 := by
  simp

/-- A homogeneous element of nonzero degree has zero `R`-component. -/
theorem fst_eq_zero_of_mem_grading {n : ℤ} {x : tsze R M} (hx : x ∈ grading S R M n)
    (hn : n ≠ 0) : x.fst = 0 :=
  (mem_grading_iff.mp hx).1 hn

/-- A homogeneous element of degree other than `1` has zero `M`-component. -/
theorem snd_eq_zero_of_mem_grading {n : ℤ} {x : tsze R M} (hx : x ∈ grading S R M n)
    (hn : n ≠ 1) : x.snd = 0 :=
  (mem_grading_iff.mp hx).2 hn

variable (S R M) in
/-- The `R`-component of an element of `R ⊕ M`, as an element of degree `0`. -/
private def projZero : tsze R M →ₗ[S] grading S R M 0 where
  toFun x := ⟨inl x.fst, inl_mem_grading_zero _⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' s x := Subtype.ext (by simp)

private theorem coe_projZero (x : tsze R M) : (projZero S R M x : tsze R M) = inl x.fst :=
  rfl

variable (S R M) in
/-- The `M`-component of an element of `R ⊕ M`, as an element of degree `1`. -/
private def projOne : tsze R M →ₗ[S] grading S R M 1 where
  toFun x := ⟨inr x.snd, inr_mem_grading_one _⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' s x := Subtype.ext (by simp)

private theorem coe_projOne (x : tsze R M) : (projOne S R M x : tsze R M) = inr x.snd :=
  rfl

variable (S R M) in
/-- The homogeneous decomposition of `R ⊕ M`: an element is its `R`-component in degree `0` plus
its `M`-component in degree `1`. -/
def decomposeGrading : tsze R M →ₗ[S] ⨁ n, grading S R M n :=
  lof S ℤ (fun n ↦ grading S R M n) 0 ∘ₗ projZero S R M +
    lof S ℤ (fun n ↦ grading S R M n) 1 ∘ₗ projOne S R M

/-- Reassembling the homogeneous decomposition of `R ⊕ M` gives back the element. -/
theorem coeLinearMap_comp_decomposeGrading :
    coeLinearMap (grading S R M) ∘ₗ decomposeGrading S R M = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    simp [decomposeGrading, coe_projZero, coe_projOne, inl_fst_add_inr_snd_eq]

/-- Decomposing a sum of homogeneous elements of `R ⊕ M` recovers the summands. -/
theorem decomposeGrading_comp_coeLinearMap :
    decomposeGrading S R M ∘ₗ coeLinearMap (grading S R M) = LinearMap.id := by
  refine DirectSum.linearMap_ext _ fun n ↦ LinearMap.ext fun ⟨x, hx⟩ ↦ ?_
  simp only [LinearMap.comp_apply, coeLinearMap_lof, LinearMap.id_comp, decomposeGrading,
    LinearMap.add_apply]
  by_cases h₀ : n = 0
  · subst h₀
    have h₁ : projOne S R M x = 0 :=
      Subtype.ext (by simp [coe_projOne, mem_grading_zero_iff.mp hx])
    have h₂ : projZero S R M x = ⟨x, hx⟩ :=
      Subtype.ext (ext rfl (mem_grading_zero_iff.mp hx).symm)
    rw [h₁, h₂, map_zero, add_zero]
  by_cases h₁ : n = 1
  · subst h₁
    have h₂ : projZero S R M x = 0 :=
      Subtype.ext (by simp [coe_projZero, mem_grading_one_iff.mp hx])
    have h₃ : projOne S R M x = ⟨x, hx⟩ :=
      Subtype.ext (ext (mem_grading_one_iff.mp hx).symm rfl)
    rw [h₂, h₃, map_zero, zero_add]
  · obtain rfl : x = 0 := by simpa [grading_eq_bot h₀ h₁] using hx
    simp only [map_zero, add_zero]
    exact ((lof S ℤ (fun n ↦ grading S R M n) n).map_zero.trans (by congr)).symm

instance : Decomposition (grading S R M) :=
  Decomposition.ofLinearMap _ (decomposeGrading S R M) coeLinearMap_comp_decomposeGrading
    decomposeGrading_comp_coeLinearMap

/-- The degree-`0` component of an element of `R ⊕ M` is its `R`-component. -/
@[simp]
theorem coe_decompose_zero (x : tsze R M) :
    (decompose (grading S R M) x 0 : tsze R M) = inl x.fst := by
  conv_lhs => rw [← inl_fst_add_inr_snd_eq x]
  rw [decompose_add, DirectSum.add_apply, Submodule.coe_add,
    decompose_of_mem_same _ (inl_mem_grading_zero _),
    decompose_of_mem_ne _ (inr_mem_grading_one _) one_ne_zero, add_zero]

/-- The degree-`1` component of an element of `R ⊕ M` is its `M`-component. -/
@[simp]
theorem coe_decompose_one (x : tsze R M) :
    (decompose (grading S R M) x 1 : tsze R M) = inr x.snd := by
  conv_lhs => rw [← inl_fst_add_inr_snd_eq x]
  rw [decompose_add, DirectSum.add_apply, Submodule.coe_add,
    decompose_of_mem_ne _ (inl_mem_grading_zero _) zero_ne_one,
    decompose_of_mem_same _ (inr_mem_grading_one _), zero_add]

end Grading

section GradedAlgebra

variable {S R M : Type*} [CommSemiring S] [Semiring R] [AddCommMonoid M] [Algebra S R]
  [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower S R M]
  [IsScalarTower S Rᵐᵒᵖ M]

/-- The trivial square-zero extension `R ⊕ M`, with `R` in degree `0` and `M` in degree `1`, is a
graded algebra: `M · M = 0` lands in degree `2`, where there is nothing. -/
instance instGradedAlgebraGrading : GradedAlgebra (grading S R M) where
  one_mem := by simp
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨hx₁, hx₂⟩ := mem_grading_iff.mp hx
    obtain ⟨hy₁, hy₂⟩ := mem_grading_iff.mp hy
    refine mem_grading_iff.mpr ⟨fun hij ↦ ?_, fun hij ↦ ?_⟩
    · by_cases hi : i = 0
      · simp [hy₁ (by omega)]
      · simp [hx₁ hi]
    · rw [snd_mul]
      by_cases hi : i = 0
      · subst hi
        simp [hy₂ (by omega), hx₂ (by omega)]
      · by_cases hi' : i = 1
        · subst hi'
          simp [hx₁ (by omega), hy₁ (by omega)]
        · simp [hx₁ hi, hx₂ hi']

end GradedAlgebra

section Comm

variable {S R M : Type*} [CommSemiring S] [CommRing R] [AddCommGroup M] [Module S R]
  [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/-- The trivial square-zero extension `R ⊕ M` of a commutative ring by a symmetric module, graded
with `R` in degree `0` and `M` in degree `1`, is graded-commutative: two homogeneous elements
commute up to the Koszul sign. -/
theorem mul_comm_of_mem_grading {p q : ℤ} {x y : tsze R M} (hx : x ∈ grading S R M p)
    (hy : y ∈ grading S R M q) : x * y = (p * q).negOnePow • (y * x) := by
  by_cases hpq : Even (p * q)
  · rw [Int.negOnePow_even _ hpq, one_smul, mul_comm]
  · have hp : p ≠ 0 := by rintro rfl; simp at hpq
    have hq : q ≠ 0 := by rintro rfl; simp at hpq
    have hxy : ∀ {a b : tsze R M}, a.fst = 0 → b.fst = 0 → a * b = 0 := fun ha hb ↦
      ext (by simp [ha]) (by simp [ha, hb])
    rw [hxy (fst_eq_zero_of_mem_grading hx hp) (fst_eq_zero_of_mem_grading hy hq),
      hxy (fst_eq_zero_of_mem_grading hy hq) (fst_eq_zero_of_mem_grading hx hp), smul_zero]

end Comm

end TrivSqZeroExt

namespace Derivation

open TrivSqZeroExt

variable {S R M : Type*} [CommRing S] [CommRing R] [AddCommGroup M] [Algebra S R]
  [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsScalarTower S R M]
  [IsScalarTower S Rᵐᵒᵖ M] (D : Derivation S R M)

/-- The differential `(r, m) ↦ (0, D r)` on the trivial square-zero extension `R ⊕ M` defined by a
derivation `D : R → M`. -/
def trivSqZeroExtDifferential : tsze R M →ₗ[S] tsze R M where
  toFun x := inr (D x.fst)
  map_add' x y := by simp
  map_smul' s x := by simp

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M] in
@[simp]
theorem trivSqZeroExtDifferential_apply (x : tsze R M) :
    D.trivSqZeroExtDifferential x = inr (D x.fst) :=
  (rfl)

/-- The trivial square-zero extension `R ⊕ M`, with `R` in degree `0` and `M` in degree `1`, is a
differential graded algebra for the differential `(r, m) ↦ (0, D r)` of a derivation
`D : R → M`. -/
theorem isDGAlgebra_trivSqZeroExtDifferential :
    IsDGAlgebra (grading S R M) D.trivSqZeroExtDifferential where
  map_mem {p} x hx := by
    by_cases hp : p = 0
    · subst hp
      simp
    · simp [fst_eq_zero_of_mem_grading hx hp]
  sq_zero x := by simp
  leibniz {p} x hx y := by
    by_cases hp : p = 0
    · subst hp
      have hx₂ : x.snd = 0 := mem_grading_zero_iff.mp hx
      ext <;> simp [hx₂, mul_comm, add_comm]
    · ext <;> simp [fst_eq_zero_of_mem_grading hx hp, Units.smul_def]

/-- The augmentation `(r, m) ↦ φ r` of the differential graded algebra `R ⊕ M` of a derivation,
defined by an `S`-algebra map `φ : R → S`. -/
def trivSqZeroExtAugmentation (φ : R →ₐ[S] S) :
    DGAlgAugmentation D.isDGAlgebra_trivSqZeroExtDifferential where
  toGradedAlgHom :=
    { toAlgHom := φ.comp (fstHom S R M)
      map_mem := fun {p} {x} hx ↦ by
        rw [mem_trivialGrading_iff]
        by_cases hp : p = 0
        · exact Or.inl hp
        · exact Or.inr (by simp [fst_eq_zero_of_mem_grading hx hp]) }
  map_d' x := by simp

@[simp]
theorem trivSqZeroExtAugmentation_apply (φ : R →ₐ[S] S) (x : tsze R M) :
    D.trivSqZeroExtAugmentation φ x = φ x.fst :=
  (rfl)

/-- The unit morphism sends the class of a scalar `s` to the class of a cycle `z` exactly when
`algebraMap s - z` is a boundary `(0, D r)`. -/
private theorem cohomologyMap_unitHom_mk_eq_iff (s : S)
    (z : D.isDGAlgebra_trivSqZeroExtDifferential.cycles) :
    D.isDGAlgebra_trivSqZeroExtDifferential.unitHom.cohomologyMap
        (Ideal.Quotient.mk _ ⟨s, by simp⟩) = Ideal.Quotient.mk _ z ↔
      ∃ r : R, inr (D r) = inl (algebraMap S R s) - (z : tsze R M) := by
  rw [DGAlgHom.cohomologyMap_mk, Ideal.Quotient.eq, TwoSidedIdeal.mem_asIdeal,
    IsDGAlgebra.mem_boundaries]
  simp only [LinearMap.mem_range, trivSqZeroExtDifferential_apply, AddSubgroupClass.coe_sub,
    DGAlgHom.cyclesMap_apply_coe, IsDGAlgebra.unitHom_apply, algebraMap_eq_inl']
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y.fst, hy⟩, fun ⟨r, hr⟩ ↦ ⟨inl r, hr⟩⟩

/-- The unit `S → R ⊕ M` of the differential graded algebra of a derivation `D : R → M` is a
quasi-isomorphism exactly when `S → R` is injective, every `r` with `D r = 0` is a scalar, and `D`
is surjective: the cohomology of `R ⊕ M` is `ker D` in degree `0` and `coker D` in degree `1`. -/
theorem bijective_cohomologyMap_unitHom_iff :
    Function.Bijective D.isDGAlgebra_trivSqZeroExtDifferential.unitHom.cohomologyMap ↔
      Function.Injective (algebraMap S R) ∧ (∀ r, D r = 0 → ∃ s, algebraMap S R s = r) ∧
        Function.Surjective D := by
  set h := D.isDGAlgebra_trivSqZeroExtDifferential
  have h₀ := isDGAlgebra_trivialGrading S
  -- Every class of the ground ring is the class of a scalar.
  have hmk : ∀ c : h₀.Cohomology, ∃ s : S, Ideal.Quotient.mk _ ⟨s, by simp⟩ = c := fun c ↦ by
    obtain ⟨⟨s, hs⟩, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨s, rfl⟩
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨(injective_iff_map_eq_zero _).mpr fun s hs ↦ ?_, fun r hr ↦ ?_, fun m ↦ ?_⟩
    · have hzero := (D.cohomologyMap_unitHom_mk_eq_iff s 0).mpr ⟨0, by simp [hs]⟩
      rw [map_zero, ← map_zero h.unitHom.cohomologyMap] at hzero
      have := h₀.mem_boundaries.mp ((h₀.quotientMk_eq_zero_iff).mp (hinj hzero))
      simpa [eq_comm] using this
    · obtain ⟨s, hs⟩ := hmk (Classical.choose (hsurj (Ideal.Quotient.mk _
        ⟨inl r, by simp [hr]⟩)))
      obtain ⟨r', hr'⟩ := (D.cohomologyMap_unitHom_mk_eq_iff s _).mp
        (hs ▸ Classical.choose_spec (hsurj _))
      exact ⟨s, sub_eq_zero.mp (by simpa [eq_comm] using congrArg fst hr')⟩
    · obtain ⟨s, hs⟩ := hmk (Classical.choose (hsurj (Ideal.Quotient.mk _
        ⟨inr m, by simp⟩)))
      obtain ⟨r', hr'⟩ := (D.cohomologyMap_unitHom_mk_eq_iff s _).mp
        (hs ▸ Classical.choose_spec (hsurj _))
      exact ⟨-r', by simpa [neg_eq_iff_eq_neg] using congrArg snd hr'⟩
  · rintro ⟨hinj, hker, hsurj⟩
    refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_, fun c ↦ ?_⟩
    · obtain ⟨s, rfl⟩ := hmk c
      rw [← map_zero (Ideal.Quotient.mk h.boundaries.asIdeal),
        D.cohomologyMap_unitHom_mk_eq_iff] at hc
      obtain ⟨r, hr⟩ := hc
      have hs : algebraMap S R s = 0 := by simpa [eq_comm] using congrArg fst hr
      rw [h₀.quotientMk_eq_zero_iff, h₀.mem_boundaries]
      exact ⟨0, by simpa using (hinj (hs.trans (map_zero _).symm)).symm⟩
    · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨s, hs⟩ := hker _ (by simpa using congrArg snd (h.mem_cycles.mp z.2))
      obtain ⟨r, hr⟩ := hsurj (z : tsze R M).snd
      refine ⟨_, (D.cohomologyMap_unitHom_mk_eq_iff s z).mpr ⟨-r, TrivSqZeroExt.ext ?_ ?_⟩⟩ <;>
        simp [hs, hr]

/-- An augmentation of the differential graded algebra `R ⊕ M` of a derivation `D : R → M` is a
quasi-isomorphism exactly when `S → R` is injective, every `r` with `D r = 0` is a scalar, and `D`
is surjective. -/
theorem bijective_cohomologyMap_trivSqZeroExtAugmentation_iff (φ : R →ₐ[S] S) :
    Function.Bijective (D.trivSqZeroExtAugmentation φ).cohomologyMap ↔
      Function.Injective (algebraMap S R) ∧ (∀ r, D r = 0 → ∃ s, algebraMap S R s = r) ∧
        Function.Surjective D :=
  (DGAlgAugmentation.bijective_cohomologyMap_iff _).trans D.bijective_cohomologyMap_unitHom_iff

end Derivation
