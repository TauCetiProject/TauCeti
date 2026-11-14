/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Limit
public import TauCeti.RingTheory.Huber.Restricted.Reduction.Basic

/-!
# Adic restricted power series as inverse limits of polynomial rings

For an ideal `I` of a commutative ring `A`, the polynomial rings `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`
with the coefficientwise reduction maps form a diagram
`TauCeti.Huber.polynomialQuotientPowSuccDiagram k I : ℕᵒᵖ ⥤ CommRingCat`. When `I` defines the
topology of a nonarchimedean ring `A` (`IsAdic I`), open-ideal polynomial reductions assemble into
cones with apex `weightedRestrictedSubring` (`restrictedReductionPowSuccCone`) and apex
`restrictedMvPowerSeriesCompletion k A` (`restrictedCompletionReductionPowSuccCone`).

Because the kernels of reduction modulo `I ^ (n + 1)` form a countable neighbourhood basis of zero
in both carriers (`hasBasis_nhds_zero_ker_restrictedReduction` and
`hasBasis_nhds_zero_ker_restrictedCompletionReduction`), the completed restricted-series algebra
`A⟨X₁, …, Xₖ⟩` is unconditionally the limit in `CommRingCat` of `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`
(`isLimitRestrictedCompletionReductionPowSuccCone`), and every compatible sequence of polynomials
modulo `I ^ (n + 1)` lifts to a unique element of `A⟨X₁, …, Xₖ⟩`
(`existsUnique_restrictedCompletionReduction_pow_succ_eq`), without assuming `I.FG`, completeness,
or separatedness of `A`.

When the uncompleted restricted-series subring is itself complete and Hausdorff, transporting along
`restrictedMvPowerSeriesCompletionEquiv` shows that `restrictedReductionPowSuccCone` is likewise a
limit cone (`isLimitRestrictedReductionPowSuccCone`), again without `I.FG`. When `I` is finitely
generated, `quotientPowRestrictedEquivMvPolynomialQuotient` and
`quotientPowRestrictedCompletionEquivMvPolynomialQuotient` further identify
`polynomialQuotientPowSuccDiagram k I` with `Ideal.quotientPowSuccDiagram` of the extended ideals.

## Main definitions

* `TauCeti.Huber.polynomialQuotientPowSuccDiagram`: the diagram
  `n ↦ CommRingCat.of (MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))`.
* `TauCeti.Huber.restrictedReductionPowSuccCone` and
  `TauCeti.Huber.restrictedCompletionReductionPowSuccCone`: the reduction cones over it.
* `TauCeti.Huber.quotientPowSuccDiagramRestrictedIso` and
  `TauCeti.Huber.quotientPowSuccDiagramRestrictedCompletionIso`: natural isomorphisms with
  `Ideal.quotientPowSuccDiagram` of the extended ideals when `I.FG`.

## Main results

* `TauCeti.Huber.hasBasis_nhds_zero_ker_restrictedReduction` and
  `TauCeti.Huber.hasBasis_nhds_zero_ker_restrictedCompletionReduction`: the kernels of reduction
  modulo `I ^ (n + 1)` form a neighbourhood basis of zero.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletion_ext_of_isAdic`,
  `TauCeti.Huber.existsUnique_restrictedCompletionReduction_pow_succ_eq`, and
  `TauCeti.Huber.isLimitRestrictedCompletionReductionPowSuccCone`: `A⟨X₁, …, Xₖ⟩` is the inverse
  limit of `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`.
* `TauCeti.Huber.isLimitRestrictedReductionPowSuccCone` and
  `TauCeti.Huber.existsUnique_restrictedReduction_pow_succ_eq`: the uncompleted counterpart when
  `weightedRestrictedSubring` is complete and separated.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, §2.2.
-/

universe u

open CategoryTheory Limits Opposite Topology UniformSpace

@[expose] public section

namespace TauCeti.Huber

section Diagram

variable {A : Type u} [CommRing A]

/-- The inverse system `(A ⧸ I)[X₁, …, Xₖ] ← (A ⧸ I ^ 2)[X₁, …, Xₖ] ← ⋯` in `CommRingCat`
whose transitions reduce coefficients along `Ideal.Quotient.factor`. -/
@[simps]
noncomputable def polynomialQuotientPowSuccDiagram (k : ℕ) (I : Ideal A) :
    ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (MvPolynomial (Fin k) (A ⧸ I ^ (n.unop + 1)))
  map f := CommRingCat.ofHom <| MvPolynomial.map <|
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop)))
  map_id _ := by
    ext1
    refine MvPolynomial.ringHom_ext (fun y ↦ ?_) fun i ↦ by simp
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp
  map_comp _ _ := by
    ext1
    refine MvPolynomial.ringHom_ext (fun y ↦ ?_) fun i ↦ by simp
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp

end Diagram

section Cones

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

/-- The cone of polynomial reductions `A⟨X⟩ → (A ⧸ I ^ (n + 1))[X]` on the uncompleted
restricted-series subring. -/
@[simps]
noncomputable def restrictedReductionPowSuccCone (hI : IsAdic I) :
    Cone (polynomialQuotientPowSuccDiagram k I) where
  pt := CommRingCat.of
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
  π.app n := CommRingCat.ofHom <|
    (I ^ (n.unop + 1)).restrictedReduction (hI.isOpen_pow (n.unop + 1))
  π.naturality _ _ f := by
    ext g
    dsimp
    exact (map_restrictedReduction (hI.isOpen_pow _) (hI.isOpen_pow _)
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) g).symm

/-- The cone of completed polynomial reductions `A⟨X⟩ → (A ⧸ I ^ (n + 1))[X]` on
`restrictedMvPowerSeriesCompletion k A`. -/
@[simps]
noncomputable def restrictedCompletionReductionPowSuccCone (hI : IsAdic I) :
    Cone (polynomialQuotientPowSuccDiagram k I) where
  pt := CommRingCat.of (restrictedMvPowerSeriesCompletion k A)
  π.app n := CommRingCat.ofHom <|
    (I ^ (n.unop + 1)).restrictedCompletionReduction (hI.isOpen_pow (n.unop + 1))
  π.naturality _ _ f := by
    ext x
    dsimp
    exact (map_restrictedCompletionReduction (hI.isOpen_pow _) (hI.isOpen_pow _)
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) x).symm

end Cones

end TauCeti.Huber

end

public section

namespace TauCeti.Huber

/-- One-step compatibility along `polynomialQuotientPowSuccDiagram` implies compatibility across
arbitrary indices `m ≤ n`. -/
private theorem polynomialQuotientPowSucc_compat {A : Type u} [CommRing A] {k : ℕ} {I : Ideal A}
    {p : ∀ n : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (n + 1))}
    (hp : ∀ n : ℕ, MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (p (n + 1)) = p n)
    {m n : ℕ} (hmn : m ≤ n) :
    MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)))
      (p n) = p m := by
  induction n, hmn using Nat.le_induction with
  | base =>
      have hid : Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := I) (Nat.succ_le_succ (le_refl m))) = RingHom.id _ := by
        ext
        rfl
      rw [hid, MvPolynomial.map_id]
  | succ n hmn ih =>
      have hcomp : Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (I := I) (Nat.succ_le_succ (Nat.le_succ_of_le hmn))) =
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn))).comp
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) := by
        ext
        rfl
      rw [hcomp, ← MvPolynomial.map_map, hp n, ih]

section CompletionLimit

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

/-- When `I` defines the topology of `A`, the kernels of reduction modulo `I ^ (n + 1)` form a
neighbourhood basis of zero in `weightedRestrictedSubring`. -/
theorem hasBasis_nhds_zero_ker_restrictedReduction (hI : IsAdic I) :
    (𝓝 (0 : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (RingHom.ker ((I ^ (n + 1)).restrictedReduction (k := k)
        (hI.isOpen_pow (n + 1))) : Set _) := by
  refine Filter.hasBasis_iff.mpr fun W ↦ ⟨fun hW ↦ ?_, ?_⟩
  · obtain ⟨U, -, hUW⟩ :=
      (hasBasis_nhds_zero_weightedTopology (k := k) (A := A)
        isWeightFamily_one_weight).mem_iff.mp hW
    obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp U.mem_nhds_zero
    refine ⟨n, trivial, fun f hf ↦ hUW ?_⟩
    rw [SetLike.mem_coe, mem_weightedNhd]
    intro ν
    rw [weightMul_one_weight]
    exact hn (Ideal.pow_le_pow_right n.le_succ
      (((I ^ (n + 1)).mem_ker_restrictedReduction (hI.isOpen_pow (n + 1)) f).mp hf ν))
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset
      (((I ^ (n + 1)).isOpen_ker_restrictedReduction (hI.isOpen_pow (n + 1))).mem_nhds
        (RingHom.ker _).zero_mem) hn

/-- When `I` defines the topology of `A`, the kernels of completed reduction modulo `I ^ (n + 1)`
form a neighbourhood basis of zero in `restrictedMvPowerSeriesCompletion k A`. -/
theorem hasBasis_nhds_zero_ker_restrictedCompletionReduction (hI : IsAdic I) :
    (𝓝 (0 : restrictedMvPowerSeriesCompletion k A)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (RingHom.ker ((I ^ (n + 1)).restrictedCompletionReduction (k := k)
        (hI.isOpen_pow (n + 1))) : Set _) := by
  let S := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  refine Filter.hasBasis_iff.mpr fun W ↦ ⟨fun hW ↦ ?_, ?_⟩
  · obtain ⟨F, ⟨hF, hFclosed⟩, hFW⟩ :=
      (closed_nhds_basis (0 : restrictedMvPowerSeriesCompletion k A)).mem_iff.mp hW
    have hpre : ((↑) : S → restrictedMvPowerSeriesCompletion k A) ⁻¹' F ∈ 𝓝 (0 : S) :=
      (Completion.continuous_coe S).continuousAt.preimage_mem_nhds (by rwa [Completion.coe_zero])
    obtain ⟨n, -, hn⟩ := (hasBasis_nhds_zero_ker_restrictedReduction (k := k) hI).mem_iff.mp hpre
    refine ⟨n, trivial, fun x hx ↦ hFW ?_⟩
    have hxcl : x ∈ closure (((↑) : S → restrictedMvPowerSeriesCompletion k A) ''
        (RingHom.ker ((I ^ (n + 1)).restrictedReduction (k := k) (hI.isOpen_pow (n + 1))) :
          Set S)) := by
      refine mem_closure_iff.mpr fun V hV hxV ↦ ?_
      obtain ⟨f, hfV, hfker⟩ := (Completion.denseRange_coe (α := S)).exists_mem_open
        (hV.inter ((I ^ (n + 1)).isOpen_ker_restrictedCompletionReduction
          (hI.isOpen_pow (n + 1)))) ⟨x, hxV, hx⟩
      refine ⟨f, hfV, f, ?_, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker] at hfker ⊢
      exact ((I ^ (n + 1)).restrictedCompletionReduction_coe (hI.isOpen_pow (n + 1)) f).symm.trans
        hfker
    exact (closure_minimal (Set.image_subset_iff.mpr hn) hFclosed) hxcl
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset
      (((I ^ (n + 1)).isOpen_ker_restrictedCompletionReduction (hI.isOpen_pow (n + 1))).mem_nhds
        (RingHom.ker _).zero_mem) hn

/-- Elements of `restrictedMvPowerSeriesCompletion k A` over an `I`-adic ring are determined by
their completed polynomial reductions modulo `I ^ (n + 1)`. -/
theorem restrictedMvPowerSeriesCompletion_ext_of_isAdic (hI : IsAdic I)
    {x y : restrictedMvPowerSeriesCompletion k A}
    (h : ∀ n : ℕ, (I ^ (n + 1)).restrictedCompletionReduction (hI.isOpen_pow (n + 1)) x =
      (I ^ (n + 1)).restrictedCompletionReduction (hI.isOpen_pow (n + 1)) y) :
    x = y := by
  suffices x - y = 0 from sub_eq_zero.mp this
  have h0 : Filter.Tendsto (fun _ : ℕ ↦ x - y) Filter.atTop
      (𝓝 (0 : restrictedMvPowerSeriesCompletion k A)) :=
    (hasBasis_nhds_zero_ker_restrictedCompletionReduction (k := k) hI).tendsto_right_iff.mpr
      fun n _ ↦ Filter.Eventually.of_forall fun _ ↦ by
        simp [SetLike.mem_coe, RingHom.mem_ker, h n]
  exact tendsto_nhds_unique tendsto_const_nhds h0

/-- **Compatible polynomial reductions determine a unique completed restricted series.** If `I`
defines the topology of `A`, every sequence of polynomials `p n ∈ (A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`
compatible under coefficient reduction lifts to a unique element of
`restrictedMvPowerSeriesCompletion k A`. Neither `I.FG`, completeness of `A`, nor separatedness of
`A` is required. -/
theorem existsUnique_restrictedCompletionReduction_pow_succ_eq (hI : IsAdic I)
    (p : ∀ n : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hp : ∀ n : ℕ, MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (p (n + 1)) = p n) :
    ∃! x : restrictedMvPowerSeriesCompletion k A,
      ∀ n : ℕ, (I ^ (n + 1)).restrictedCompletionReduction (hI.isOpen_pow (n + 1)) x = p n := by
  choose y hy using fun n ↦
    (I ^ (n + 1)).restrictedCompletionReduction_surjective (k := k) (hI.isOpen_pow (n + 1)) (p n)
  have hdiff {j m : ℕ} (hjm : j ≤ m) :
      y m - y j ∈ RingHom.ker
        ((I ^ (j + 1)).restrictedCompletionReduction (k := k) (hI.isOpen_pow (j + 1))) := by
    rw [RingHom.mem_ker, map_sub, hy j, ← map_restrictedCompletionReduction
      (hI.isOpen_pow (m + 1)) (hI.isOpen_pow (j + 1))
      (Ideal.pow_le_pow_right (Nat.succ_le_succ hjm)), hy m,
      polynomialQuotientPowSucc_compat hp hjm, sub_self]
  have hcauchy : CauchySeq y := by
    refine (hasBasis_nhds_zero_ker_restrictedCompletionReduction (k := k)
      hI).uniformity_of_nhds_zero.cauchySeq_iff.mpr fun j _ ↦ ⟨j, fun m hm n hn ↦ ?_⟩
    have h := (RingHom.ker _).sub_mem (hdiff hn) (hdiff hm)
    rwa [sub_sub_sub_cancel_right] at h
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hx_red (n : ℕ) :
      (I ^ (n + 1)).restrictedCompletionReduction (hI.isOpen_pow (n + 1)) x = p n := by
    let : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ I ^ (n + 1))) := ⊥
    have : DiscreteTopology (MvPolynomial (Fin k) (A ⧸ I ^ (n + 1))) := ⟨rfl⟩
    have hlim := ((I ^ (n + 1)).isLocallyConstant_restrictedCompletionReduction
      (hI.isOpen_pow (n + 1))).continuous.continuousAt.tendsto.comp hx
    have hev : (fun m ↦ (I ^ (n + 1)).restrictedCompletionReduction (hI.isOpen_pow (n + 1)) (y m))
        =ᶠ[Filter.atTop] fun _ ↦ p n := by
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      rw [← map_restrictedCompletionReduction (hI.isOpen_pow (m + 1)) (hI.isOpen_pow (n + 1))
        (Ideal.pow_le_pow_right (Nat.succ_le_succ hm)), hy m,
        polynomialQuotientPowSucc_compat hp hm]
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
  exact ⟨x, hx_red, fun z hz ↦
    restrictedMvPowerSeriesCompletion_ext_of_isAdic hI fun n ↦ (hz n).trans (hx_red n).symm⟩

/-- Pointwise lift of a cone over `polynomialQuotientPowSuccDiagram k I` into
`restrictedMvPowerSeriesCompletion k A`. -/
private noncomputable def coneLiftCompletionFun (hI : IsAdic I)
    (s : Cone (polynomialQuotientPowSuccDiagram k I)) (y : s.pt) :
    restrictedMvPowerSeriesCompletion k A :=
  (existsUnique_restrictedCompletionReduction_pow_succ_eq (k := k) hI
    (fun n ↦ (s.π.app (op n)).hom y)
    (fun n ↦ congr($(s.w (homOfLE (Nat.le_succ n)).op).hom y))).choose

private theorem restrictedCompletionReduction_coneLiftCompletionFun (hI : IsAdic I)
    (s : Cone (polynomialQuotientPowSuccDiagram k I)) (y : s.pt) (n : ℕ) :
    (I ^ (n + 1)).restrictedCompletionReduction (hI.isOpen_pow (n + 1))
        (coneLiftCompletionFun hI s y) =
      (s.π.app (op n)).hom y :=
  (existsUnique_restrictedCompletionReduction_pow_succ_eq (k := k) hI
    (fun m ↦ (s.π.app (op m)).hom y)
    (fun m ↦ congr($(s.w (homOfLE (Nat.le_succ m)).op).hom y))).choose_spec.1 n

/-- Ring homomorphism induced by a cone over `polynomialQuotientPowSuccDiagram k I`. -/
private noncomputable def coneLiftCompletionRingHom (hI : IsAdic I)
    (s : Cone (polynomialQuotientPowSuccDiagram k I)) :
    s.pt →+* restrictedMvPowerSeriesCompletion k A where
  toFun := coneLiftCompletionFun hI s
  map_one' := restrictedMvPowerSeriesCompletion_ext_of_isAdic hI fun n ↦ by
    simp [restrictedCompletionReduction_coneLiftCompletionFun]
    rfl
  map_mul' y z := restrictedMvPowerSeriesCompletion_ext_of_isAdic hI fun n ↦ by
    simp [restrictedCompletionReduction_coneLiftCompletionFun]
    rfl
  map_zero' := restrictedMvPowerSeriesCompletion_ext_of_isAdic hI fun n ↦ by
    simp [restrictedCompletionReduction_coneLiftCompletionFun]
    rfl
  map_add' y z := restrictedMvPowerSeriesCompletion_ext_of_isAdic hI fun n ↦ by
    simp [restrictedCompletionReduction_coneLiftCompletionFun]
    rfl

/-- **The completed restricted-series algebra `A⟨X₁, …, Xₖ⟩` is the limit in `CommRingCat` of
`(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`.** Only `IsAdic I` is required; `I` need not be finitely generated
and `A` need not be complete or separated. -/
noncomputable def isLimitRestrictedCompletionReductionPowSuccCone (hI : IsAdic I) :
    IsLimit (restrictedCompletionReductionPowSuccCone (k := k) hI) where
  lift s := CommRingCat.ofHom (coneLiftCompletionRingHom hI s)
  fac s n := by
    ext y
    exact restrictedCompletionReduction_coneLiftCompletionFun hI s y n.unop
  uniq s m hm := by
    ext y
    refine restrictedMvPowerSeriesCompletion_ext_of_isAdic hI fun n ↦ ?_
    exact congr($(hm (op n)).hom y).trans
      (restrictedCompletionReduction_coneLiftCompletionFun hI s y n).symm

end CompletionLimit

section ExtendedIdealDiagram

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

/-- When `I` is a finitely generated ideal of definition of `A`, the quotient diagram of
`weightedRestrictedSubring` modulo powers of `I · A⟨X⟩` is naturally isomorphic to
`polynomialQuotientPowSuccDiagram k I`. -/
noncomputable def quotientPowSuccDiagramRestrictedIso (hI : IsAdic I) (hfg : I.FG) :
    Ideal.quotientPowSuccDiagram
      (I.map (weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)) ≅
      polynomialQuotientPowSuccDiagram k I :=
  NatIso.ofComponents
    (fun n ↦ (quotientPowRestrictedEquivMvPolynomialQuotient (k := k) hI hfg
      (n.unop + 1)).toRingEquiv.toCommRingCatIso)
    fun {m n} f ↦ by
      ext q
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact (quotientPowRestrictedEquivMvPolynomialQuotient_mk hI hfg (n.unop + 1) g).trans
        ((map_restrictedReduction (hI.isOpen_pow (m.unop + 1)) (hI.isOpen_pow (n.unop + 1))
          (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) g).symm.trans <|
          congrArg (MvPolynomial.map _)
            (quotientPowRestrictedEquivMvPolynomialQuotient_mk hI hfg (m.unop + 1) g).symm)

/-- When `I` is a finitely generated ideal of definition of `A`, the quotient diagram of
`restrictedMvPowerSeriesCompletion k A` modulo powers of `I · A⟨X⟩` is naturally isomorphic to
`polynomialQuotientPowSuccDiagram k I`. -/
noncomputable def quotientPowSuccDiagramRestrictedCompletionIso (hI : IsAdic I) (hfg : I.FG) :
    Ideal.quotientPowSuccDiagram
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ≅
      polynomialQuotientPowSuccDiagram k I :=
  NatIso.ofComponents
    (fun n ↦ (quotientPowRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg
      (n.unop + 1)).toRingEquiv.toCommRingCatIso)
    fun {m n} f ↦ by
      ext q
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact (quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk hI hfg (n.unop + 1)
          x).trans
        ((map_restrictedCompletionReduction (hI.isOpen_pow (m.unop + 1))
            (hI.isOpen_pow (n.unop + 1))
            (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) x).symm.trans <|
          congrArg (MvPolynomial.map _)
            (quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk hI hfg (m.unop + 1)
              x).symm)

/-- If the uncompleted restricted-series subring is complete and Hausdorff, then
`restrictedReductionPowSuccCone` is a limit cone in `CommRingCat`, without assuming `I.FG`. -/
noncomputable def isLimitRestrictedReductionPowSuccCone (hI : IsAdic I)
    [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)]
    [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)] :
    IsLimit (restrictedReductionPowSuccCone (k := k) hI) :=
  IsLimit.ofIsoLimit (isLimitRestrictedCompletionReductionPowSuccCone (k := k) hI) <|
    Cone.ext (restrictedMvPowerSeriesCompletionAlgEquiv k A).toRingEquiv.toCommRingCatIso
      fun n ↦ by
        ext x
        exact Ideal.restrictedCompletionReduction_eq_restrictedReduction_algEquiv
          (I ^ (n.unop + 1)) (hI.isOpen_pow (n.unop + 1)) x

/-- When the uncompleted restricted-series subring is complete and Hausdorff, every compatible
sequence of polynomials modulo `I ^ (n + 1)` lifts to a unique restricted power series, without
assuming `I.FG`. -/
theorem existsUnique_restrictedReduction_pow_succ_eq (hI : IsAdic I)
    [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)]
    [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)]
    (p : ∀ n : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hp : ∀ n : ℕ, MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (p (n + 1)) = p n) :
    ∃! f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight,
      ∀ n : ℕ, (I ^ (n + 1)).restrictedReduction (hI.isOpen_pow (n + 1)) f = p n := by
  let e := restrictedMvPowerSeriesCompletionAlgEquiv k A
  obtain ⟨x, hx, huniq⟩ := existsUnique_restrictedCompletionReduction_pow_succ_eq (k := k) hI p hp
  refine ⟨e x, fun n ↦ ?_, fun f hf ↦ ?_⟩
  · rw [← Ideal.restrictedCompletionReduction_eq_restrictedReduction_algEquiv]
    exact hx n
  · have hfx : e.symm f = x := huniq (e.symm f) fun n ↦ by
      rw [Ideal.restrictedCompletionReduction_eq_restrictedReduction_algEquiv, e.apply_symm_apply]
      exact hf n
    simp [← hfx]

end ExtendedIdealDiagram

end TauCeti.Huber
