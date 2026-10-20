/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianType.Quotient
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

import TauCeti.RingTheory.Huber.Completion.Noetherian

/-!
# Noetherian type ascends along homomorphisms topologically of finite type

Let `A` be a Huber ring of noetherian type and `φ : A → B` a ring homomorphism topologically of
finite type, so that `B` is an open quotient of the completion of a weighted restricted
power-series ring `A⟨X₁, …, Xₖ⟩_T` with finite weights `Tᵢ`. Then `B` is again of noetherian type
(Huber, Corollary 3.4; Wedhorn, Proposition 6.35 and Remark 6.37(1)). This is the form in which
the noetherian hypothesis of Huber's sheafiness theorem reaches rational localisations and
algebras topologically of finite type.

The two alternatives defining noetherian type are treated separately.

* If `A` is a strongly noetherian Tate ring, `B` is Tate, complete and Hausdorff, and strongly
  noetherian (`TauCeti.Huber.IsTopologicallyFiniteType.isStronglyNoetherian`).
* If `A` has a noetherian ring of definition `A₀` with ideal of definition `I`, the ring of
  definition `A₀⟨X⟩_T` of `A⟨X⟩_T` is not noetherian in general, but modulo its ideal of
  definition `I⟨X⟩_T` it is a quotient of the polynomial ring over `A₀` in one variable for each
  weighted variable `t Xᵢ` with `t ∈ Tᵢ`: the coefficients of a restricted series lie in the
  weights times `I` for all but finitely many indices, and the remaining finitely many monomials
  are polynomials in the weighted variables. Since the weights are finite, `A₀⟨X⟩_T ⧸ I⟨X⟩_T` is
  noetherian, so the completed ring of definition is noetherian, being adically complete for a
  finitely generated ideal with noetherian quotient. Its image under the presentation is a
  noetherian ring of definition of `B`.

No completeness is assumed of `A` or of `B`.

## Main results

* `TauCeti.Huber.PairOfDefinition.isNoetherianRing_weightedRingOfDefinition_quotient`: for finite
  weights and a noetherian `A₀`, the ring `A₀⟨X⟩_T ⧸ I⟨X⟩_T` is noetherian.
* `TauCeti.Huber.PairOfDefinition.isNoetherianRing_weighted_completion_ringOfDefinition`: the ring
  of definition of the completion of `A⟨X⟩_T` is then noetherian.
* `TauCeti.Huber.IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing`: an algebra
  topologically of finite type over a Huber ring with a noetherian ring of definition has a
  noetherian ring of definition.
* `TauCeti.Huber.IsNoetherianType.of_isTopologicallyFiniteType`: noetherian type ascends along
  homomorphisms topologically of finite type.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Corollary 3.4.
* T. Wedhorn, *Adic Spaces*, Proposition 6.35 and Remark 6.37.
-/

public section

open UniformSpace
open scoped Pointwise

namespace TauCeti.Huber

namespace PairOfDefinition

section Weighted

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {T : Fin k → Set A} (P : PairOfDefinition A) (hT : IsWeightFamily T)

/-- A weighted variable `t Xᵢ`, for `t ∈ Tᵢ`, lies in `A₀⟨X⟩_T`. -/
private theorem weightedC_mul_weightedX_mem (i : Fin k) {t : A} (ht : t ∈ T i) :
    weightedC T hT t * weightedX T hT i ∈ P.weightedRingOfDefinition hT := by
  have hmem : t * 1 ∈ weightMul T (Finsupp.single i 1) P.ringOfDefinition.toAddSubgroup :=
    mul_mem_weightMul T _ _ (by rwa [weightPow_single, pow_one]) P.ringOfDefinition.one_mem
  rw [mul_one] at hmem
  simpa using weightedC_mul_weightedX_pow_mem_weightedNhd hT hmem

/-- The map from the polynomial ring over `A₀` in one variable for each pair `(i, t)` with
`t ∈ Tᵢ` to `A₀⟨X⟩_T`, sending that variable to the weighted variable `t Xᵢ`. -/
private noncomputable def weightedVarHom :
    MvPolynomial (Σ i, T i) P.ringOfDefinition →+* P.weightedRingOfDefinition hT :=
  MvPolynomial.eval₂Hom (P.weightedRingOfDefinitionC hT)
    fun s ↦ ⟨_, P.weightedC_mul_weightedX_mem hT s.1 s.2.2⟩

/-- A monomial `t Xν` with `t` in the weight `Tν` is a polynomial over `A₀` in the weighted
variables. -/
private theorem weightedPolynomialHom_monomial_mem_range_of_mem_weightPow {ν : Fin k →₀ ℕ}
    {t : A} (ht : t ∈ weightPow T ν) :
    weightedPolynomialHom T hT (MvPolynomial.monomial ν t) ∈
      ((P.weightedRingOfDefinition hT).subtype.comp (P.weightedVarHom hT)).range := by
  set R := ((P.weightedRingOfDefinition hT).subtype.comp (P.weightedVarHom hT)).range
  -- the case of a single variable `Xᵢ ^ m`, with `t` a product of `m` elements of `Tᵢ`
  have hsingle (i : Fin k) (m : ℕ) {u : A} (hu : u ∈ T i ^ m) :
      weightedPolynomialHom T hT (MvPolynomial.monomial (Finsupp.single i m) u) ∈ R := by
    induction m generalizing u with
    | zero =>
      obtain rfl : u = 1 := by simpa using hu
      simp
    | succ m ih =>
      rw [pow_succ] at hu
      obtain ⟨v, hv, t, ht, rfl⟩ := Set.mem_mul.mp hu
      have hgen : weightedPolynomialHom T hT (MvPolynomial.monomial (Finsupp.single i 1) t) ∈ R :=
        ⟨MvPolynomial.X ⟨i, t, ht⟩, by
          simp [weightedVarHom, ← MvPolynomial.C_mul_X_eq_monomial]⟩
      rw [Finsupp.single_add, ← MvPolynomial.monomial_mul_monomial, map_mul]
      exact R.mul_mem (ih hv) hgen
  induction ν using Finsupp.induction generalizing t with
  | zero =>
    obtain rfl : t = 1 := by simpa using ht
    simp
  | single_add i m ν _ _ ih =>
    rw [weightPow_add, weightPow_single] at ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp ht
    rw [← MvPolynomial.monomial_mul_monomial, map_mul]
    exact R.mul_mem (hsingle i m hu) (ih hv)

/-- A monomial `c Xν` whose coefficient meets the `A₀` bound, `c ∈ Tν · A₀`, is a polynomial over
`A₀` in the weighted variables. -/
private theorem weightedPolynomialHom_monomial_mem_range {ν : Fin k →₀ ℕ} {c : A}
    (hc : c ∈ weightMul T ν P.ringOfDefinition.toAddSubgroup) :
    weightedPolynomialHom T hT (MvPolynomial.monomial ν c) ∈
      ((P.weightedRingOfDefinition hT).subtype.comp (P.weightedVarHom hT)).range := by
  set R := ((P.weightedRingOfDefinition hT).subtype.comp (P.weightedVarHom hT)).range
  let f : A →+ weightedRestrictedSubring T hT :=
    (weightedPolynomialHom T hT).toAddMonoidHom.comp (MvPolynomial.monomial ν).toAddMonoidHom
  refine (weightMul_le (V := R.toAddSubgroup.comap f)).mpr (fun t ht a ha ↦ ?_) hc
  have hC : weightedC T hT a ∈ R := ⟨MvPolynomial.C ⟨a, ha⟩, by simp [weightedVarHom]⟩
  rw [AddSubgroup.mem_comap]
  simpa [f, mul_comm t a, ← MvPolynomial.C_mul_monomial] using
    R.mul_mem hC (P.weightedPolynomialHom_monomial_mem_range_of_mem_weightPow hT ht)

/-- Modulo the ideal of definition `I⟨X⟩_T`, every element of `A₀⟨X⟩_T` is a polynomial over `A₀`
in the weighted variables `t Xᵢ`, `t ∈ Tᵢ`: all but finitely many coefficients of a restricted
series lie in the weights times `I`. -/
private theorem surjective_mk_comp_weightedVarHom :
    Function.Surjective
      ((Ideal.Quotient.mk (P.weightedIdeal hT 1)).comp (P.weightedVarHom hT)) := by
  classical
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- the finitely many indices at which the coefficient of `f` escapes `Tν · I`
  let U : OpenAddSubgroup A := ⟨P.idealImage 1, P.isOpen_idealImage 1⟩
  have hres : IsWeightedRestricted T (f : MvPowerSeries (Fin k) A) :=
    mem_weightedRestrictedSubring.mp (f : weightedRestrictedSubring T hT).2
  let S := (hres.finite_coeff_notMem U).toFinset
  -- the truncation of `f` to these indices
  let p : MvPolynomial (Fin k) A := ∑ ν ∈ S,
    MvPolynomial.monomial ν (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A))
  have hf := (P.mem_weightedRingOfDefinition hT).mp f.2
  obtain ⟨q, hq⟩ : weightedPolynomialHom T hT p ∈
      ((P.weightedRingOfDefinition hT).subtype.comp (P.weightedVarHom hT)).range := by
    rw [map_sum]
    exact Subring.sum_mem _ fun ν _ ↦
      P.weightedPolynomialHom_monomial_mem_range hT (mem_weightedNhd.mp hf ν)
  refine ⟨q, Ideal.Quotient.eq.mpr ?_⟩
  rw [RingHom.comp_apply, Subring.coe_subtype] at hq
  rw [mem_weightedIdeal, mem_weightedNhd]
  intro μ
  rw [AddSubgroupClass.coe_sub, hq, AddSubgroupClass.coe_sub, coe_weightedPolynomialHom, map_sub,
    MvPolynomial.coeff_coe]
  by_cases hμ : μ ∈ S
  · simp [p, MvPolynomial.coeff_monomial, hμ]
  · have hcoeff : MvPowerSeries.coeff μ (f : MvPowerSeries (Fin k) A) ∈
        weightMul T μ (P.idealImage 1) := by
      by_contra h
      exact hμ (Set.Finite.mem_toFinset _ |>.mpr h)
    simpa [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hμ] using hcoeff

/-- **`A₀⟨X⟩_T ⧸ I⟨X⟩_T` is noetherian** for finite weights `Tᵢ` and a noetherian ring of
definition `A₀`: it is generated over `A₀` by the finitely many weighted variables `t Xᵢ` with
`t ∈ Tᵢ`. -/
theorem isNoetherianRing_weightedRingOfDefinition_quotient [IsNoetherianRing P.ringOfDefinition]
    (hTfin : ∀ i, (T i).Finite) :
    IsNoetherianRing (P.weightedRingOfDefinition hT ⧸ P.weightedIdeal hT 1) :=
  have : ∀ i, Finite (T i) := fun i ↦ (hTfin i).to_subtype
  isNoetherianRing_of_surjective _ _ _ (P.surjective_mk_comp_weightedVarHom hT)

/-- **The completed ring of definition of `A⟨X⟩_T` is noetherian** for finite weights `Tᵢ` and a
noetherian ring of definition `A₀`. It is the ring of definition of the completion of the pair of
definition `(A₀⟨X⟩_T, I⟨X⟩_T)`, complete for a finitely generated ideal with quotient
`A₀⟨X⟩_T ⧸ I⟨X⟩_T`. -/
theorem isNoetherianRing_weighted_completion_ringOfDefinition
    [IsNoetherianRing P.ringOfDefinition] (hTfin : ∀ i, (T i).Finite) :
    IsNoetherianRing (P.weighted hT).completion.ringOfDefinition := by
  -- transport the quotient along `(P.weighted hT).ringOfDefinition = A₀⟨X⟩_T`
  let e : (P.weighted hT).ringOfDefinition ≃+* P.weightedRingOfDefinition hT :=
    RingEquiv.subringCongr (P.weighted_ringOfDefinition hT)
  have he : P.weightedIdeal hT 1 = (P.weighted hT).idealOfDefinition.map e := by
    ext x
    rw [← Ideal.comap_symm, Ideal.mem_comap, mem_weighted_idealOfDefinition]
    simp [e]
  have := P.isNoetherianRing_weightedRingOfDefinition_quotient hT hTfin
  have : IsNoetherianRing
      ((P.weighted hT).ringOfDefinition ⧸ (P.weighted hT).idealOfDefinition) :=
    isNoetherianRing_of_ringEquiv _ (Ideal.quotientEquiv _ _ e he).symm
  rw [completion_ringOfDefinition]
  exact (P.weighted hT).isNoetherianRing_completionRingOfDefinition_of_quotient

end Weighted

end PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {φ : A →+* B}

/-- **A noetherian ring of definition ascends along a homomorphism topologically of finite type**
(Huber, Corollary 3.4(iii); Wedhorn, Proposition 6.35). If `A` has a noetherian ring of definition
and `φ : A → B` is topologically of finite type, then `B` has a noetherian ring of definition. -/
theorem IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing
    (P : PairOfDefinition A) [IsNoetherianRing P.ringOfDefinition]
    (hφ : IsTopologicallyFiniteType φ) :
    ∃ Q : PairOfDefinition B, IsNoetherianRing Q.ringOfDefinition := by
  obtain ⟨k, T, hTfin, hT, π, hπ, -⟩ := isTopologicallyFiniteType_iff.mp hφ
  have := P.isNoetherianRing_weighted_completion_ringOfDefinition hT hTfin
  exact ⟨(P.weighted hT).completion.map π hπ, inferInstance⟩

/-- **Noetherian type ascends along homomorphisms topologically of finite type** (Huber,
Corollary 3.4; Wedhorn, Proposition 6.35 and Remark 6.37(1)). If `A` is a Huber ring of
noetherian type and `φ : A → B` is topologically of finite type, then `B` is of noetherian type.
Neither `A` nor `B` needs to be complete. -/
theorem IsNoetherianType.of_isTopologicallyFiniteType [IsHuberRing A] [IsNoetherianType A]
    [IsHuberRing B] (hφ : IsTopologicallyFiniteType φ) : IsNoetherianType B := by
  refine IsNoetherianType.elim ‹_› (fun P _ ↦ ?_) fun _ _ ↦ ?_
  · obtain ⟨Q, hQ⟩ := hφ.exists_pairOfDefinition_isNoetherianRing P
    exact .of_pairOfDefinition Q hQ
  · -- `B` is Tate, and complete and Hausdorff for its additive uniformity, so strongly noetherian
    have := hφ.isTateRing
    let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
    have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
    have := hφ.completeSpace
    have := hφ.t2Space
    have := hφ.isStronglyNoetherian
    infer_instance

end TauCeti.Huber
