/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Noetherian
public import TauCeti.RingTheory.Huber.NoetherianType.Basic
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.RingTheory.Huber.NoetherianType.Quotient
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete

/-!
# Noetherian type ascends along homomorphisms topologically of finite type

Let `A` be a Huber ring with a pair of definition `(A₀, I)` and let `T = (T₁, …, Tₖ)` be a weight
family of finite subsets of `A`. The ring of definition `A₀⟨X⟩_T` of `A⟨X⟩_T` is a ring of
restricted series rather than polynomials, but modulo its ideal of definition `I⟨X⟩_T` it is a
quotient of the polynomial ring over `A₀` in the finitely many variables `Y_{i,t}`, `t ∈ Tᵢ`,
sending `Y_{i,t}` to `t Xᵢ`: a weighted restricted series is a polynomial modulo `I⟨X⟩_T`, and a
monomial `a Xν` with `a ∈ Tν · A₀` is a polynomial in the `t Xᵢ` with coefficients in `A₀`. So
when `A₀` is noetherian, so is `A₀⟨X⟩_T ⧸ I⟨X⟩_T`, and the ring of definition of the completion
of `A⟨X⟩_T`, which is complete for a finitely generated ideal with the same quotient, is
noetherian (EGA I, Ch. 0, (7.2.6)).

An open quotient map carries rings of definition onto rings of definition, so every ring `B`
topologically of finite type over `A` has a noetherian ring of definition (Huber, Corollary
3.4(iii); Wedhorn, Proposition 6.35). Together with the strongly noetherian Tate case
(`TauCeti.Huber.IsTopologicallyFiniteType.isStronglyNoetherian`), this shows that noetherian type
ascends along homomorphisms topologically of finite type. No completeness of `A` or of `B` is
assumed: the presentation of `B` already passes through a completion.

## Main results

* `TauCeti.Huber.PairOfDefinition.isNoetherianRing_weighted_quotient`: `A₀⟨X⟩_T ⧸ I⟨X⟩_T` is
  noetherian when `A₀` is and every weight is finite.
* `TauCeti.Huber.PairOfDefinition.isNoetherianRing_weighted_completion`: the ring of definition
  of the completion of `A⟨X⟩_T` is then noetherian.
* `TauCeti.Huber.IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing`: over a ring
  with a noetherian ring of definition, a ring topologically of finite type has a noetherian ring
  of definition.
* `TauCeti.Huber.IsNoetherianType.of_isTopologicallyFiniteType`: a ring topologically of finite
  type over a Huber ring of noetherian type is of noetherian type.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Corollary 3.4.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.35 and
  Remark 6.37.
* A. Grothendieck, J. Dieudonné, *EGA I*, Ch. 0, (7.2.6).
-/

public section

open MvPolynomial
open scoped Pointwise

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A]

section Generators

variable (R : Subring A) (T : Fin k → Set A)

/-- The polynomials over `R` in the variables `Y_{i,t}`, `t ∈ Tᵢ`, read as polynomials over `A`
in `X₁, …, Xₖ` through `Y_{i,t} ↦ t Xᵢ`. -/
private noncomputable def weightedGenHom :
    MvPolynomial (Σ i, T i) R →+* MvPolynomial (Fin k) A :=
  eval₂Hom (C.comp R.subtype) fun x ↦ C (x.2 : A) * X x.1

variable {R T}

/-- The constants from `R` are polynomials in the generators. -/
private theorem C_mem_range_weightedGenHom {r : A} (hr : r ∈ R) :
    C r ∈ (weightedGenHom R T).range :=
  ⟨C ⟨r, hr⟩, by simp [weightedGenHom]⟩

/-- A monomial whose coefficient lies in the weight `Tν` is a product of the generators
`t Xᵢ`. -/
private theorem monomial_mem_range_weightedGenHom_of_mem_weightPow {ν : Fin k →₀ ℕ} {t : A}
    (ht : t ∈ weightPow T ν) : monomial ν t ∈ (weightedGenHom R T).range := by
  induction ν using Finsupp.induction_linear generalizing t with
  | zero =>
    rw [weightPow_zero, Set.mem_one] at ht
    simp [ht]
  | add α β hα hβ =>
    rw [weightPow_add] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp ht
    rw [← monomial_mul_monomial]
    exact mul_mem (hα ha) (hβ hb)
  | single i n =>
    rw [weightPow_single] at ht
    induction n generalizing t with
    | zero =>
      rw [pow_zero, Set.mem_one] at ht
      simp [ht]
    | succ n ih =>
      rw [pow_succ] at ht
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp ht
      rw [Finsupp.single_add, ← monomial_mul_monomial, ← C_mul_X_eq_monomial]
      exact mul_mem (ih ha) ⟨X ⟨i, b, hb⟩, by simp [weightedGenHom]⟩

/-- A monomial whose coefficient lies in `Tν · R` is a polynomial in the generators `t Xᵢ` with
coefficients in `R`. -/
private theorem monomial_mem_range_weightedGenHom {ν : Fin k →₀ ℕ} {a : A}
    (ha : a ∈ weightMul T ν R.toAddSubgroup) : monomial ν a ∈ (weightedGenHom R T).range := by
  rw [weightMul_def] at ha
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, r, hr, rfl⟩ := Set.mem_mul.mp hx
    rw [mul_comm, ← C_mul_monomial]
    exact mul_mem (C_mem_range_weightedGenHom hr)
      (monomial_mem_range_weightedGenHom_of_mem_weightPow ht)
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx

/-- A polynomial all of whose coefficients meet the `R` bound is a polynomial in the generators
`t Xᵢ` with coefficients in `R`. -/
private theorem mem_range_weightedGenHom {q : MvPolynomial (Fin k) A}
    (hq : ∀ ν, q.coeff ν ∈ weightMul T ν R.toAddSubgroup) : q ∈ (weightedGenHom R T).range := by
  rw [q.as_sum]
  exact sum_mem fun ν _ ↦ monomial_mem_range_weightedGenHom (hq ν)

variable [TopologicalSpace A] [NonarchimedeanRing A]

/-- The generators `t Xᵢ` and the constants from `R` lie in `R⟨X⟩_T`. -/
private theorem weightedPolynomialHom_weightedGenHom_mem (hT : IsWeightFamily T)
    (p : MvPolynomial (Σ i, T i) R) :
    weightedPolynomialHom T hT (weightedGenHom R T p) ∈ weightedSubring T hT R := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [weightedGenHom]
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p x hp =>
    rw [map_mul, map_mul]
    refine mul_mem hp ?_
    rw [weightedGenHom, eval₂Hom_X', C_mul_X_eq_monomial,
      weightedPolynomialHom_monomial_mem_weightedSubring]
    simpa using mul_mem_weightMul T _ R.toAddSubgroup
      (by rw [weightPow_single, pow_one]; exact x.2.2) R.one_mem

end Generators

namespace PairOfDefinition

variable [TopologicalSpace A] [NonarchimedeanRing A]

variable (P : PairOfDefinition A) {T : Fin k → Set A} (hT : IsWeightFamily T)

/-- The polynomial presentation `A₀[Y_{i,t}] → A₀⟨X⟩_T`, `Y_{i,t} ↦ t Xᵢ`, of the ring of
definition of `A⟨X⟩_T`, surjective modulo its ideal of definition. -/
private noncomputable def weightedPresentation :
    MvPolynomial (Σ i, T i) P.ringOfDefinition →+* (P.weighted hT).ringOfDefinition :=
  ((weightedPolynomialHom T hT).comp (weightedGenHom P.ringOfDefinition T)).codRestrict _
    fun p ↦ by
      rw [weighted_ringOfDefinition, weightedRingOfDefinition_def]
      exact weightedPolynomialHom_weightedGenHom_mem hT p

/-- Every element of `A₀⟨X⟩_T` is congruent modulo `I⟨X⟩_T` to a polynomial in the `t Xᵢ` with
coefficients in `A₀`: truncate it at the finitely many coefficients outside `Tν · I`. -/
private theorem surjective_weightedPresentation :
    Function.Surjective
      ((Ideal.Quotient.mk (P.weighted hT).idealOfDefinition).comp (P.weightedPresentation hT)) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  let U : OpenAddSubgroup A :=
    { toAddSubgroup := P.idealImage 1
      isOpen' := P.isOpen_idealImage 1 }
  obtain ⟨q, hq⟩ :=
    exists_mvPolynomial_forall_coeff_sub_mem (mem_weightedRestrictedSubring.mp f.1.2) U
  have hf : (f : weightedRestrictedSubring T hT) ∈ P.weightedRingOfDefinition hT := by
    simpa using f.2
  rw [mem_weightedRingOfDefinition] at hf
  have hle (ν : Fin k →₀ ℕ) := weightMul_mono T ν (P.idealImage_le_ringOfDefinition 1)
  obtain ⟨p, hp⟩ := mem_range_weightedGenHom (R := P.ringOfDefinition) (T := T) fun ν ↦ by
    simpa using sub_mem (mem_weightedNhd.mp hf ν) (hle ν (hq ν))
  refine ⟨p, Ideal.Quotient.eq.mpr ((P.mem_weighted_idealOfDefinition hT).mpr
    ((P.mem_weightedIdeal hT 1).mpr (mem_weightedNhd.mpr fun ν ↦ ?_)))⟩
  have hpq : ((P.weightedPresentation hT p : weightedRestrictedSubring T hT) :
      MvPowerSeries (Fin k) A) = q := by
    simp [weightedPresentation, hp]
  have hν := neg_mem (hq ν)
  rw [← map_neg, neg_sub] at hν
  simpa [hpq] using hν

/-- **The ring of definition of `A⟨X⟩_T` is noetherian modulo its ideal of definition** when `A₀`
is noetherian and every weight is finite: `A₀⟨X⟩_T ⧸ I⟨X⟩_T` is a quotient of the polynomial ring
over `A₀` in the finitely many variables `Y_{i,t}`, `t ∈ Tᵢ`. -/
theorem isNoetherianRing_weighted_quotient [IsNoetherianRing P.ringOfDefinition]
    (hTfin : ∀ i, (T i).Finite) :
    IsNoetherianRing ((P.weighted hT).ringOfDefinition ⧸ (P.weighted hT).idealOfDefinition) := by
  have (i : Fin k) : Finite (T i) := (hTfin i).to_subtype
  exact isNoetherianRing_of_surjective _ _ _ (P.surjective_weightedPresentation hT)

/-- **The completed ring of definition of `A⟨X⟩_T` is noetherian** when `A₀` is noetherian and
every weight is finite (Wedhorn, proof of Proposition 6.35): the ring of definition of the
completion of `A⟨X⟩_T` is complete for a finitely generated ideal, with quotient
`A₀⟨X⟩_T ⧸ I⟨X⟩_T`. -/
theorem isNoetherianRing_weighted_completion [IsNoetherianRing P.ringOfDefinition]
    (hTfin : ∀ i, (T i).Finite) :
    IsNoetherianRing (P.weighted hT).completion.ringOfDefinition := by
  have := P.isNoetherianRing_weighted_quotient hT hTfin
  rw [completion_ringOfDefinition]
  exact (P.weighted hT).isNoetherianRing_completionRingOfDefinition_of_quotient

end PairOfDefinition

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

section NonarchimedeanRing

variable [TopologicalSpace A] [NonarchimedeanRing A] {φ : A →+* B}

/-- **A noetherian ring of definition ascends along homomorphisms topologically of finite type**
(Huber, Corollary 3.4(iii); Wedhorn, Proposition 6.35). If `A` has a pair of definition with
noetherian ring of definition and `B` is presented by an open quotient map `π` out of the
completion of `A⟨X⟩_T`, then the image under `π` of the completed ring of definition of `A⟨X⟩_T`
is a noetherian ring of definition of `B`. -/
theorem IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing
    (hφ : IsTopologicallyFiniteType φ) (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] :
    ∃ Q : PairOfDefinition B, IsNoetherianRing Q.ringOfDefinition := by
  obtain ⟨k, T, hTfin, hT, π, hπ, -⟩ := isTopologicallyFiniteType_iff.mp hφ
  have := P.isNoetherianRing_weighted_completion hT hTfin
  exact ⟨(P.weighted hT).completion.map π hπ, inferInstance⟩

end NonarchimedeanRing

section HuberRing

variable [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {φ : A →+* B}

/-- **Noetherian type ascends along homomorphisms topologically of finite type** (Huber,
Corollary 3.4; Wedhorn, Proposition 6.35 and Remark 6.37). If `A` has a noetherian ring of
definition, so does `B`
(`TauCeti.Huber.IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing`); if `A` is a
strongly noetherian Tate ring, then `B` is a complete Hausdorff Tate ring, hence strongly
noetherian. The Huber structure on `B` is automatic
(`TauCeti.Huber.IsTopologicallyFiniteType.isHuberRing`). -/
theorem IsNoetherianType.of_isTopologicallyFiniteType [IsNoetherianType A] [IsHuberRing B]
    (hφ : IsTopologicallyFiniteType φ) : IsNoetherianType B :=
  IsNoetherianType.elim ‹_›
    (fun P _ ↦
      let ⟨Q, hQ⟩ := hφ.exists_pairOfDefinition_isNoetherianRing P
      .of_pairOfDefinition Q hQ)
    fun _ _ ↦ by
      have := hφ.isTateRing
      let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
      have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
      have := hφ.completeSpace
      have := hφ.t2Space
      have := hφ.isStronglyNoetherian
      infer_instance

end HuberRing

end TauCeti.Huber
