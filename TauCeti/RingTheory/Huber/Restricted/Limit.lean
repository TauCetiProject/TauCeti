/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Limit
public import TauCeti.RingTheory.Huber.Restricted.Reduction

/-!
# Adic restricted power series as limits of polynomial algebras

For a finitely generated ideal of definition `I` of a nonarchimedean commutative ring `A`, the
completed restricted power-series algebra `A⟨X₁, …, Xₖ⟩` is `(I · A⟨X₁, …, Xₖ⟩)`-adically complete
and its quotients modulo `(I · A⟨X₁, …, Xₖ⟩) ^ (n + 1)` are isomorphic to the polynomial rings
`(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`. Assembling the completed polynomial reductions
`Ideal.restrictedReductionCompletion` therefore exhibits `A⟨X₁, …, Xₖ⟩` as the limit in
`CommRingCat` of the inverse system `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`, with no completeness or
Hausdorffness hypothesis on `A`.

When `A` itself is `I`-adically complete, `A⟨X₁, …, Xₖ⟩` agrees with the uncompleted restricted
power-series subring, and the cone of uncompleted reductions `Ideal.restrictedReduction` is
likewise a limit cone.

## Main definitions

* `Ideal.mvPolynomialQuotientPowSuccDiagram`: the diagram `n ↦ (A ⧸ I ^ (n + 1))[X₁, …, Xₖ]` in
  `CommRingCat`, with `MvPolynomial.map (Ideal.Quotient.factor …)` as transition maps.
* `TauCeti.Huber.restrictedCompletionPolynomialCone`: the cone with apex
  `restrictedMvPowerSeriesCompletion k A` and legs `(I ^ (n + 1)).restrictedReductionCompletion`.
* `TauCeti.Huber.weightedRestrictedPolynomialCone`: the cone with apex
  `weightedRestrictedSubring` and legs `(I ^ (n + 1)).restrictedReduction`.

## Main results

* `TauCeti.Huber.isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion` and
  `TauCeti.Huber.isAdicComplete_map_algebraMap_weightedRestrictedSubring_one_weight`: adic
  completeness with respect to the extended ideal of definition.
* `TauCeti.Huber.isLimitRestrictedCompletionPolynomialCone`: `A⟨X₁, …, Xₖ⟩` is the limit of
  `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]` in `CommRingCat`.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletion_ext_of_isAdic`: elements of `A⟨X₁, …, Xₖ⟩` are
  determined by their polynomial reductions modulo `I ^ (n + 1)`.
* `TauCeti.Huber.isLimitWeightedRestrictedPolynomialCone`: the corresponding limit theorem on the
  uncompleted restricted-series subring when `A` is `I`-adically complete.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.1.
* T. Wedhorn, *Adic Spaces*, §5.6.
-/

universe u

open CategoryTheory Limits Opposite

public section

namespace Ideal

/-- The inverse system `(A ⧸ I)[X₁, …, Xₖ] ← (A ⧸ I ^ 2)[X₁, …, Xₖ] ← ⋯` of polynomial rings over
successive infinitesimal thickenings, in `CommRingCat`. -/
noncomputable abbrev mvPolynomialQuotientPowSuccDiagram {A : Type u} [CommRing A]
    (I : Ideal A) (k : ℕ) : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (MvPolynomial (Fin k) (A ⧸ I ^ (n.unop + 1)))
  map f := CommRingCat.ofHom (MvPolynomial.map
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop)))))
  map_id _ := CommRingCat.hom_ext <| MvPolynomial.ringHom_ext
    (fun a ↦ by obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a; simp)
    (fun _ ↦ by simp)
  map_comp _ _ := CommRingCat.hom_ext <| MvPolynomial.ringHom_ext
    (fun a ↦ by obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a; simp)
    (fun _ ↦ by simp)

end Ideal

namespace TauCeti.Huber

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] {I : Ideal A}

/-- For a finitely generated ideal of definition `I` of `A`, the completed restricted power-series
algebra `A⟨X₁, …, Xₖ⟩` is adically complete with respect to `I · A⟨X₁, …, Xₖ⟩`, with no
completeness or Hausdorffness hypothesis on `A`. -/
theorem isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion
    (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    IsAdicComplete (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
      (restrictedMvPowerSeriesCompletion k A) :=
  (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

/-- Over an `I`-adically complete base `A` whose topology is `I`-adic for finitely generated `I`,
the uncompleted restricted-series subring is adically complete with respect to the extended ideal
`I · A⟨X₁, …, Xₖ⟩`. -/
theorem isAdicComplete_map_algebraMap_weightedRestrictedSubring_one_weight
    (k : ℕ) (hI : IsAdic I) (hfg : I.FG) [IsAdicComplete I A] :
    IsAdicComplete
      (I.map (algebraMap A (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight)))
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ : CompleteSpace A ∧ T2Space A := hI.isAdicComplete_iff.mp ‹_›
  exact (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

/-- Levelwise identification of the `(I · A⟨X₁, …, Xₖ⟩)`-adic quotient diagram of
`restrictedMvPowerSeriesCompletion k A` with `I.mvPolynomialQuotientPowSuccDiagram k`. -/
noncomputable def restrictedCompletionQuotientDiagramIso (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))).quotientPowSuccDiagram ≅
      I.mvPolynomialQuotientPowSuccDiagram k :=
  NatIso.ofComponents
    (fun n ↦ (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
      n.unop.succ_pos).toRingEquiv.toCommRingCatIso)
    fun {m n} f ↦ by
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro x
      dsimp only [Ideal.quotientPowSuccDiagram, antitoneQuotientDiagram,
        Ideal.mvPolynomialQuotientPowSuccDiagram, RingEquiv.toCommRingCatIso,
        CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        Ideal.Quotient.factor_mk, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_toRingEquiv]
      rw [quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk,
        quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk,
        map_restrictedReductionCompletion]

/-- The cone with apex `restrictedMvPowerSeriesCompletion k A` over
`I.mvPolynomialQuotientPowSuccDiagram k`, whose projections are the completed polynomial reductions
`(I ^ (n + 1)).restrictedReductionCompletion`. -/
noncomputable abbrev restrictedCompletionPolynomialCone (k : ℕ) (hI : IsAdic I) :
    Cone (I.mvPolynomialQuotientPowSuccDiagram k) where
  pt := CommRingCat.of (restrictedMvPowerSeriesCompletion k A)
  π.app n := CommRingCat.ofHom
    ((I ^ (n.unop + 1)).restrictedReductionCompletion (hI.isOpen_pow (n.unop + 1)))
  π.naturality _ _ f := CommRingCat.hom_ext <| RingHom.ext fun x ↦ by
    simpa [Ideal.mvPolynomialQuotientPowSuccDiagram] using
      (map_restrictedReductionCompletion (hI.isOpen_pow _) (hI.isOpen_pow _)
        (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) x).symm

/-- **The completed restricted power-series algebra as a limit of polynomial algebras**
(EGA I, Ch. 0, §7.5.1). For a finitely generated ideal of definition `I` of `A`,
`restrictedMvPowerSeriesCompletion k A` is the limit in `CommRingCat` of
`(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]` along the coefficient reduction maps. -/
noncomputable def isLimitRestrictedCompletionPolynomialCone (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    IsLimit (restrictedCompletionPolynomialCone k hI) := by
  have := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  refine IsLimit.ofIsoLimit
    ((IsLimit.postcomposeHomEquiv (restrictedCompletionQuotientDiagramIso k hI hfg) _).symm
      (IsAdicComplete.isLimitQuotientPowSuccCone
        (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))))) ?_
  refine Cone.ext (Iso.refl _) fun n ↦ CommRingCat.hom_ext <| RingHom.ext fun x ↦ ?_
  dsimp [restrictedCompletionQuotientDiagramIso, restrictedCompletionPolynomialCone,
    Ideal.quotientPowSuccCone, RingEquiv.toCommRingCatIso]
  exact quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk hI hfg n.unop.succ_pos x

/-- Elements of `restrictedMvPowerSeriesCompletion k A` over an `I`-adic ring (with `I` finitely
generated) are equal when all of their polynomial reductions modulo `I ^ (n + 1)` agree. -/
theorem restrictedMvPowerSeriesCompletion_ext_of_isAdic {k : ℕ} (hI : IsAdic I) (hfg : I.FG)
    {x y : restrictedMvPowerSeriesCompletion k A}
    (h : ∀ n : ℕ, (I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1)) x =
      (I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1)) y) :
    x = y := by
  refine Concrete.isLimit_ext _ (isLimitRestrictedCompletionPolynomialCone k hI hfg) x y fun n ↦ ?_
  exact h n.unop

/-- The cone with apex `weightedRestrictedSubring` over `I.mvPolynomialQuotientPowSuccDiagram k`,
whose projections are the uncompleted polynomial reductions `(I ^ (n + 1)).restrictedReduction`. -/
noncomputable abbrev weightedRestrictedPolynomialCone (k : ℕ) (hI : IsAdic I) :
    Cone (I.mvPolynomialQuotientPowSuccDiagram k) where
  pt := CommRingCat.of
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
  π.app n := CommRingCat.ofHom
    ((I ^ (n.unop + 1)).restrictedReduction (hI.isOpen_pow (n.unop + 1)))
  π.naturality _ _ f := CommRingCat.hom_ext <| RingHom.ext fun x ↦ by
    simpa [Ideal.mvPolynomialQuotientPowSuccDiagram] using
      (map_restrictedReduction (hI.isOpen_pow _) (hI.isOpen_pow _)
        (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) x).symm

/-- When `A` is `I`-adically complete and its topology is `I`-adic for finitely generated `I`,
the uncompleted restricted power-series subring is the limit in `CommRingCat` of
`(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`. -/
noncomputable def isLimitWeightedRestrictedPolynomialCone (k : ℕ) (hI : IsAdic I) (hfg : I.FG)
    [IsAdicComplete I A] :
    IsLimit (weightedRestrictedPolynomialCone k hI) := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ : CompleteSpace A ∧ T2Space A := hI.isAdicComplete_iff.mp ‹_›
  refine IsLimit.ofIsoLimit (isLimitRestrictedCompletionPolynomialCone k hI hfg)
    ((Cone.extendIso _ (restrictedMvPowerSeriesCompletionEquiv k A).toCommRingCatIso).trans ?_)
  refine Cone.ext (Iso.refl _) fun n ↦ CommRingCat.hom_ext <| RingHom.ext fun f ↦ ?_
  simp [restrictedCompletionPolynomialCone, weightedRestrictedPolynomialCone,
    RingEquiv.toCommRingCatIso]

end TauCeti.Huber

end
