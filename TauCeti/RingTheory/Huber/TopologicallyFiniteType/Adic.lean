/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import TauCeti.RingTheory.Huber.AdicHom.Basic
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.Huber.Restricted.Adic
import TauCeti.RingTheory.Huber.WeightedEval.Completion

/-!
# Topologically finite type and adic topologies

A topologically finite type homomorphism of Huber rings is continuous and preserves open ideals,
so it is adic (`TauCeti.Huber.IsTopologicallyFiniteType.isAdicHom`). This allows finite type
presentations to supply adic homomorphisms without choosing compatible rings of definition again.

Let `A` be a ring with the `I`-adic topology for a finitely generated ideal `I`, and let `B` be a
topological `A`-algebra. This file also characterises when `B` is *strictly topologically of
finite type* over `A`, that is, an open quotient of a restricted power-series algebra
`A⟨X₁, …, Xₖ⟩` over `A` (`TauCeti.Huber.IsStrictlyTopologicallyFiniteType`), by conditions on
`B` and on its reduction `B ⧸ I·B`.

## Main results

* `TauCeti.Huber.IsTopologicallyFiniteType.isAdicHom`: a topologically finite type homomorphism
  of Huber rings is adic.
* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_of_isAdic`: if `B` is `I·B`-adic,
  `I·B`-adically separated and complete, and `B ⧸ I·B` is a finitely generated `A ⧸ I`-algebra,
  then `B` is strictly topologically of finite type over `A`. The presentation sends the
  variables to lifts of generators of `B ⧸ I·B`, using the evaluation map of Wedhorn's
  Proposition 5.50 (`TauCeti.Huber.weightedEvalHomCompletion`).
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.isAdic` and
  `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.finiteType_quotient`: conversely, an algebra
  strictly topologically of finite type is `I·B`-adic, and its reduction is a finitely generated
  `A ⧸ I`-algebra.
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.isNoetherianRing` and
  `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.isAdicComplete`: if moreover `A` is
  noetherian, such an algebra is noetherian and `I·B`-adically separated and complete.
* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_algebraMap_iff`: for noetherian `A`, being
  strictly topologically of finite type is equivalent to the conjunction of these four
  conditions (EGA I, Ch. 0, 7.5.5, (a) ⇔ (c)).

Neither completeness of `A` nor continuity of the structure map `A → B` is assumed: the
presenting algebra `A⟨X₁, …, Xₖ⟩` is a completion in any case, and a ring homomorphism into an
`I·B`-adic ring is automatically continuous.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.5.5
  Proposition, (a) ⇔ (c).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50: the
  universal property of `A⟨X₁, …, Xₖ⟩`, used through `TauCeti.Huber.weightedEvalHomCompletion` to
  build the presentation in `TauCeti.Huber.isStrictlyTopologicallyFiniteType_of_isAdic`.
-/

public section

open UniformSpace

namespace TauCeti.Huber

/-- A topologically finite type homomorphism of Huber rings is adic. -/
theorem IsTopologicallyFiniteType.isAdicHom {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] {f : A →+* B} (hf : IsTopologicallyFiniteType f) :
    IsAdicHom f := by
  obtain ⟨k, T, hfinite, hT, π, hπ, _⟩ := isTopologicallyFiniteType_iff.mp hf
  have : IsHuberRing B := IsHuberRing.of_isOpenQuotientMap hπ
  exact IsAdicHom.of_continuous_isOpen_map hf.continuous fun _ hI ↦ hf.isOpen_map hI

/-! ### Algebras over an adic ring -/

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] {I : Ideal A}
  {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]

omit [TopologicalSpace B] in
/-- The ideal `I·A⟨X₁, …, Xₖ⟩` maps onto `I·B` along a presentation of `B`. -/
private theorem map_map_algebraMap_eq {k : ℕ} {π : restrictedMvPowerSeriesCompletion k A →+* B}
    (hcomm : π.comp (algebraMap A (restrictedMvPowerSeriesCompletion k A)) = algebraMap A B) :
    (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))).map π =
      I.map (algebraMap A B) := by
  rw [Ideal.map_map, hcomm]

/-! ### From a presentation to the adic description -/

section Presentation

/-- **An algebra strictly topologically of finite type is adic for the extended ideal.** If `B`
is an open quotient of `A⟨X₁, …, Xₖ⟩` over an `I`-adic ring `A`, with `I` finitely generated,
then the topology of `B` is the `I·B`-adic one. -/
theorem IsStrictlyTopologicallyFiniteType.isAdic [IsTopologicalRing B]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap A B)) (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap A B)) := by
  obtain ⟨k, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  rw [← map_map_algebraMap_eq hcomm]
  exact (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).map_of_isOpenQuotientMap
    π hπ

/-- **An algebra strictly topologically of finite type over a noetherian `I`-adic ring is
noetherian.** -/
theorem IsStrictlyTopologicallyFiniteType.isNoetherianRing [IsNoetherianRing A]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap A B)) (hI : IsAdic I) :
    IsNoetherianRing B := by
  obtain ⟨k, π, hπ, -⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  exact isNoetherianRing_of_surjective _ _ π hπ.surjective

/-- **An algebra strictly topologically of finite type over a noetherian `I`-adic ring is
`I·B`-adically separated and complete.** The ring `A` itself need not be complete. -/
theorem IsStrictlyTopologicallyFiniteType.isAdicComplete [IsNoetherianRing A]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap A B)) (hI : IsAdic I) :
    IsAdicComplete (I.map (algebraMap A B)) B := by
  obtain ⟨k, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  -- `B` is a finite module over the noetherian `I·A⟨X⟩`-adically complete ring `A⟨X⟩`
  let R := restrictedMvPowerSeriesCompletion k A
  let J := I.map (algebraMap A R)
  have hJ : IsAdic J :=
    isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI (IsNoetherian.noetherian I)
  have : IsNoetherianRing R := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  have : IsAdicComplete J R := hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  let _ := π.toAlgebra
  have : Module.Finite R B := Module.Finite.of_surjective (Algebra.linearMap R B) hπ.surjective
  have : IsAdicComplete J B := IsAdicComplete.of_finite J B
  have hmap : J.map (algebraMap R B) = I.map (algebraMap A B) := map_map_algebraMap_eq hcomm
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff J B).mpr inferInstance

/-- **The reduction of an algebra strictly topologically of finite type is of finite type.** If
`B` is strictly topologically of finite type over an `I`-adic ring `A`, with `I` finitely
generated, then `B ⧸ I·B` is a finitely generated `A ⧸ I`-algebra. -/
theorem IsStrictlyTopologicallyFiniteType.finiteType_quotient
    (h : IsStrictlyTopologicallyFiniteType (algebraMap A B)) (hI : IsAdic I) (hfg : I.FG) :
    Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  obtain ⟨k, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  let R := restrictedMvPowerSeriesCompletion k A
  let q := (Ideal.Quotient.mk (I.map (algebraMap A B))).comp π
  -- the images of the variables
  let g : Fin k → B ⧸ I.map (algebraMap A B) := fun i ↦
    q ((weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :
      weightedRestrictedSubring _ isWeightFamily_one_weight) : R)
  let S := Algebra.adjoin A (Set.range g)
  -- the elements of `A⟨X⟩` whose reduction lies in the subalgebra generated by the variables form
  -- a subring containing the open ideal `I·A⟨X⟩`, the constants and the variables
  have hall (x : R) : q x ∈ S := by
    refine mem_of_mem_nhds_of_forall_weightedX_mem isWeightFamily_one_weight
      (R := S.toSubring.comap q) ?_ (fun a ↦ ?_) (fun i ↦ Algebra.subset_adjoin ⟨i, rfl⟩) x
    · have hJ := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
      refine Filter.mem_of_superset ((hJ.isOpen_pow 1).mem_nhds (by simp)) fun y hy ↦ ?_
      have hy' : π y ∈ I.map (algebraMap A B) := by
        rw [← map_map_algebraMap_eq hcomm]
        exact Ideal.mem_map_of_mem π (by simpa using hy)
      simp [q, Ideal.Quotient.eq_zero_iff_mem.mpr hy']
    · have hπa : π (algebraMap A R a) = algebraMap A B a := RingHom.congr_fun hcomm a
      rw [Subring.mem_comap, Subalgebra.mem_toSubring, RingHom.comp_apply, hπa,
        Ideal.Quotient.mk_algebraMap]
      exact S.algebraMap_mem a
  have htop : S = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := I.map (algebraMap A B)) y
    obtain ⟨z, rfl⟩ := hπ.surjective x
    exact hall z
  have : Algebra.FiniteType A (B ⧸ I.map (algebraMap A B)) :=
    ⟨⟨(Set.finite_range g).toFinset, by rw [Set.Finite.coe_toFinset, ← htop]⟩⟩
  exact Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ I) _

end Presentation

/-! ### From the adic description to a presentation -/

section Lift

/-- **An adically complete algebra with a finite type reduction is strictly topologically of
finite type** (EGA I, Ch. 0, 7.5.5, (a) ⇒ (c)). Let `A` be `I`-adic with `I` finitely generated,
and let `B` be an `A`-algebra that is `I·B`-adic, `I·B`-adically separated and complete, and whose
reduction `B ⧸ I·B` is a finitely generated `A ⧸ I`-algebra. Then `B` is an open quotient of some
`A⟨X₁, …, Xₖ⟩` over `A`. Neither `A` nor the structure map is assumed complete or continuous. -/
theorem isStrictlyTopologicallyFiniteType_of_isAdic (hI : IsAdic I) (hfg : I.FG)
    (hB : IsAdic (I.map (algebraMap A B))) [hc : IsAdicComplete (I.map (algebraMap A B)) B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))] :
    IsStrictlyTopologicallyFiniteType (algebraMap A B) := by
  set J := I.map (algebraMap A B) with hJ
  have : IsTopologicalRing B := hB ▸ J.nonarchimedean.toIsTopologicalRing
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : NonarchimedeanRing B := hB ▸ J.nonarchimedean
  obtain ⟨_, _⟩ : CompleteSpace B ∧ T2Space B := hB.isAdicComplete_iff.mp hc
  have : IsLinearTopology B B := hB.isLinearTopology
  -- generators of the reduction, and lifts of them to `B`
  have : Algebra.FiniteType A (B ⧸ J) := .trans (S := A ⧸ I) inferInstance inferInstance
  obtain ⟨k, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  choose b hb using fun i : Fin k ↦ Ideal.Quotient.mk_surjective (f (MvPolynomial.X i))
  -- the evaluation `A⟨X₁, …, Xₖ⟩ → B` at the lifts
  have hcont : Continuous (algebraMap A B) :=
    hI.continuous_of_map_le_radical hB hfg Ideal.le_radical
  have hbdd : IsWeightBounded (algebraMap A B) (fun _ : Fin k ↦ ({1} : Set A)) b :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun i ↦
      isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)
  let ψ : restrictedMvPowerSeriesCompletion k A →+* B :=
    weightedEvalHomCompletion isWeightFamily_one_weight hcont.continuousAt hbdd
  have hψc : Continuous ψ := continuous_weightedEvalHomCompletion _ _ _
  have hψA : ψ.comp (algebraMap A (restrictedMvPowerSeriesCompletion k A)) = algebraMap A B := by
    ext a
    rw [RingHom.comp_apply, algebraMap_completion_weightedRestrictedSubring_apply,
      weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]
  have hψX (i : Fin k) : ψ ((weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :
      weightedRestrictedSubring _ isWeightFamily_one_weight) :
        restrictedMvPowerSeriesCompletion k A) = b i := by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
  set R := restrictedMvPowerSeriesCompletion k A
  set JR := I.map (algebraMap A R)
  have hJR : IsAdic JR := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have hmap : JR.map ψ = J := map_map_algebraMap_eq hψA
  -- `ψ` is surjective modulo `I·B`, hence surjective, since `A⟨X⟩` is complete and `B` separated
  have hsurj : Function.Surjective ψ := by
    have : IsPrecomplete JR R :=
      (hJR.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩).toIsPrecomplete
    have : IsHausdorff (JR.map ψ) B := by
      rw [hmap]
      exact hc.toIsHausdorff
    refine surjective_of_mk_map_comp_surjective (I := JR) ψ ?_
    rw [hmap]
    -- the reduction of `ψ` is an `A`-algebra map whose range contains the generators
    let ψA : R →ₐ[A] B := { ψ with commutes' := RingHom.congr_fun hψA }
    let q := (Ideal.Quotient.mkₐ A J).comp ψA
    have hle : Algebra.adjoin A (Set.range fun i ↦ f (MvPolynomial.X i)) ≤ q.range :=
      Algebra.adjoin_le <| by
        rintro _ ⟨i, rfl⟩
        exact ⟨_, (congrArg (Ideal.Quotient.mk J) (hψX i)).trans (hb i)⟩
    intro y
    obtain ⟨p, rfl⟩ := hf y
    have hp : f p ∈ Algebra.adjoin A (Set.range fun i ↦ f (MvPolynomial.X i)) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨p, (RingHom.congr_fun (congrArg AlgHom.toRingHom (MvPolynomial.aeval_unique f))
        p).symm⟩
    obtain ⟨x, hx⟩ := hle hp
    exact ⟨x, by simpa [q, ψA] using hx⟩
  -- `ψ` is open: it carries the powers of `I·A⟨X⟩` onto the open powers of `I·B`
  have hopen : IsOpenMap ψ := by
    refine (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero (f := ψ)).mpr ?_
    refine (hB.hasBasis_nhds_zero.le_basis_iff (hJR.hasBasis_nhds_zero.map ψ)).mpr fun n _ ↦
      ⟨n, trivial, ?_⟩
    rw [← hmap, ← Ideal.map_pow, Ideal.map_eq_image_of_surjective ψ hsurj]
  exact isStrictlyTopologicallyFiniteType_iff.mpr
    ⟨k, ψ, ⟨hsurj, hψc, hopen⟩, hψA⟩

end Lift

/-- **EGA I, Ch. 0, 7.5.5, (a) ⇔ (c).** Over a noetherian ring `A` with the `I`-adic topology, a
topological `A`-algebra `B` is strictly topologically of finite type exactly when `B` is
noetherian, `I·B`-adic, `I·B`-adically separated and complete, and `B ⧸ I·B` is a finitely
generated `A ⧸ I`-algebra. Noetherianity of `B` follows from the other three conditions. -/
theorem isStrictlyTopologicallyFiniteType_algebraMap_iff [IsTopologicalRing B] [IsNoetherianRing A]
    (hI : IsAdic I) :
    IsStrictlyTopologicallyFiniteType (algebraMap A B) ↔
      IsNoetherianRing B ∧ IsAdic (I.map (algebraMap A B)) ∧
        IsAdicComplete (I.map (algebraMap A B)) B ∧
          Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  have hfg : I.FG := IsNoetherian.noetherian I
  refine ⟨fun h ↦ ⟨h.isNoetherianRing hI, h.isAdic hI hfg, h.isAdicComplete hI,
    h.finiteType_quotient hI hfg⟩, fun h ↦ ?_⟩
  have := h.2.2.1
  have := h.2.2.2
  exact isStrictlyTopologicallyFiniteType_of_isAdic hI hfg h.2.1

end TauCeti.Huber
