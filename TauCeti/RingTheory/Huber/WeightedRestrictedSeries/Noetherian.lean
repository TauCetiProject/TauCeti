/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

import TauCeti.RingTheory.Huber.Completion.Noetherian
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Basic

/-!
# Noetherianity of the ring of definition of `A⟨X⟩_T` modulo its ideal of definition

Let `(A₀, I)` be a pair of definition of `A` and `T = (T₁, …, Tₖ)` a weight family of finite
subsets of `A`. The ring of definition `A₀⟨X⟩_T` of `A⟨X⟩_T` is not noetherian in general, but
modulo its ideal of definition `I⟨X⟩_T` it is a quotient of the polynomial ring over `A₀` in one
variable for each weighted variable `t Xᵢ` with `t ∈ Tᵢ`: the coefficients of a restricted series
lie in the weights times `I` for all but finitely many indices, and the remaining finitely many
monomials are polynomials in the weighted variables. So if `A₀` is noetherian, then so is
`A₀⟨X⟩_T ⧸ I⟨X⟩_T`, and hence so is the completed ring of definition, being adically complete for
a finitely generated ideal with noetherian quotient (Huber, proof of Corollary 3.4; Wedhorn,
proof of Proposition 6.35).

## Main results

* `TauCeti.Huber.PairOfDefinition.isNoetherianRing_weightedRingOfDefinition_quotient`: for finite
  weights and a noetherian `A₀`, the ring `A₀⟨X⟩_T ⧸ I⟨X⟩_T` is noetherian.
* `TauCeti.Huber.PairOfDefinition.isNoetherianRing_weighted_completion_ringOfDefinition`: the ring
  of definition of the completion of `A⟨X⟩_T` is then noetherian.
* `TauCeti.Huber.PairOfDefinition.finiteType_weighted_completion`: if `A` is finite type over `A₀`,
  the completion of `A⟨X⟩_T` is finite type over `(P.weighted hT).completion.ringOfDefinition`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Corollary 3.4.
* T. Wedhorn, *Adic Spaces*, Proposition 6.35.
-/

public section

namespace TauCeti.Huber

namespace PairOfDefinition

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {T : Fin k → Set A} (P : PairOfDefinition A) (hT : IsWeightFamily T)

/-- The map from the polynomial ring over `A₀` in one variable for each pair `(i, t)` with
`t ∈ Tᵢ` to `A₀⟨X⟩_T`, sending that variable to the weighted variable `t Xᵢ`. -/
private noncomputable def weightedVarHom :
    MvPolynomial (Σ i, T i) P.ringOfDefinition →+* P.weightedRingOfDefinition hT :=
  MvPolynomial.eval₂Hom (P.weightedRingOfDefinitionC hT)
    fun s ↦ ⟨_, P.weightedC_mul_weightedX_mem_weightedRingOfDefinition hT s.2.2⟩

/-- Modulo the ideal of definition `I⟨X⟩_T`, every element of `A₀⟨X⟩_T` is a polynomial over `A₀`
in the weighted variables `t Xᵢ`, `t ∈ Tᵢ`: all but finitely many coefficients of a restricted
series lie in the weights times `I`. -/
private theorem surjective_mk_comp_weightedVarHom :
    Function.Surjective
      ((Ideal.Quotient.mk (P.weightedIdeal hT 1)).comp (P.weightedVarHom hT)) := by
  set R := ((P.weightedRingOfDefinition hT).subtype.comp (P.weightedVarHom hT)).range
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- truncate `f` to a polynomial whose coefficients still meet the `A₀` bound
  obtain ⟨p, hp, hfp⟩ := exists_mvPolynomial_sub_mem_weightedNhd_of_mem_weightedSubring hT
    ((P.weightedRingOfDefinition_def hT).le f.2) ⟨P.idealImage 1, P.isOpen_idealImage 1⟩
  obtain ⟨q, hq⟩ : weightedPolynomialHom T hT p ∈ R := by
    rw [p.as_sum, map_sum]
    exact sum_mem fun ν _ ↦ weightedPolynomialHom_monomial_mem_of_mem_weightMul hT (Q := R)
      (fun a ha ↦ ⟨MvPolynomial.C ⟨a, ha⟩, by simp [weightedVarHom]⟩)
      (weightedPolynomialHom_monomial_mem hT (B := R) fun i t ht ↦
        ⟨MvPolynomial.X ⟨i, t, ht⟩, by simp [weightedVarHom]⟩) (hp ν)
  refine ⟨q, (Ideal.Quotient.eq.mpr ?_).symm⟩
  rw [RingHom.comp_apply, Subring.coe_subtype] at hq
  rw [mem_weightedIdeal, AddSubgroupClass.coe_sub, hq]
  exact hfp

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

/-- **Finite generation over a ring of definition passes to completed weighted restricted power
series**: if `A` is finite type over `P.ringOfDefinition`, then the completion of `A⟨X₁, …, Xₖ⟩_T`
is finite type over `(P.weighted hT).completion.ringOfDefinition`, generated by the images of a
finite generating set of `A` together with the variables `X₁, …, Xₖ`. -/
instance finiteType_weighted_completion [hfg : Algebra.FiniteType P.ringOfDefinition A] :
    Algebra.FiniteType (P.weighted hT).completion.ringOfDefinition
      (UniformSpace.Completion (weightedRestrictedSubring T hT)) := by
  classical
  obtain ⟨G, hG⟩ := hfg.out
  let R := UniformSpace.Completion (weightedRestrictedSubring T hT)
  let F : Finset R :=
    G.image (algebraMap A R) ∪ Finset.univ.image fun i : Fin k ↦
      ((weightedX T hT i : weightedRestrictedSubring T hT) : R)
  let S := Algebra.adjoin (P.weighted hT).completion.ringOfDefinition (F : Set R)
  have hle : (Algebra.adjoin P.ringOfDefinition (G : Set A)).toSubring ≤
      S.toSubring.comap (algebraMap A R) := by
    rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro a (⟨r, rfl⟩ | ha)
    · refine S.algebraMap_mem ⟨algebraMap A R (r : A), ?_⟩
      rw [algebraMap_completion_weightedRestrictedSubring_apply,
        (P.weighted hT).completion_ringOfDefinition]
      refine (P.weighted hT).coe_mem_completionRingOfDefinition_iff.mpr ?_
      rw [P.weighted_ringOfDefinition hT, P.weightedRingOfDefinition_def hT]
      exact (weightedC_mem_weightedSubring hT).mpr r.2
    · exact Algebra.subset_adjoin <| Finset.mem_coe.mpr <|
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
  have hnhds : (S.toSubring : Set R) ∈ nhds (0 : R) :=
    Filter.mem_of_superset
      ((P.weighted hT).completion.isOpen_ringOfDefinition.mem_nhds
        (P.weighted hT).completion.ringOfDefinition.zero_mem)
      fun x hx ↦ S.algebraMap_mem ⟨x, hx⟩
  refine ⟨⟨F, eq_top_iff.mpr fun y _ ↦ mem_of_mem_nhds_of_forall_weightedX_mem hT hnhds
    (fun a ↦ hle (by rw [hG]; trivial)) (fun i ↦ ?_) y⟩⟩
  exact Algebra.subset_adjoin <| Finset.mem_coe.mpr <|
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end PairOfDefinition

end TauCeti.Huber
