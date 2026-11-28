/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Hilbert.Affine
public import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
public import TauCeti.AlgebraicGeometry.Hilbert.BasisChart
public import TauCeti.RingTheory.MvPolynomial.Quotient.Span
public import TauCeti.RingTheory.MvPolynomial.Quotient.FiniteLocallyFree
public import TauCeti.AlgebraicGeometry.AffineSpace.BaseChange

/-!
# Affine basis charts of the Hilbert functor

Finite flat subschemes of affine space over affine test schemes are described
by polynomial quotient algebras. The universal quotient-basis rings give actual
Hilbert families. Their images are open basis loci and cover every affine test
scheme locally.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TauCeti.PolynomialQuotient RingHom TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Hilbert



section Dictionary

variable {n : Type u} {S : Scheme.{u}} {d : ℕ}

/-- The native affine ideal correspondence identifies Hilbert families with polynomial
quotients that are finite and flat of the prescribed rank. -/
noncomputable def polynomialIdealEquiv {T : Over S} [IsAffine T.left] :
    (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T) ≃
      {K : Ideal (MvPolynomial n Γ(T.left, ⊤)) //
        RingHom.IsFiniteLocallyFreeOfRank d
          (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ K))} := by
  let e : (pullback T.hom (𝔸(n; S) ↘ S)).IdealSheafData ≃
      Ideal (MvPolynomial n Γ(T.left, ⊤)) :=
    Scheme.IdealSheafData.equivOfIsAffine.toEquiv |>.trans
      (AffineSpace.toΓBaseChangeEquiv n T.hom).idealComapOrderIso.toEquiv
  apply e.subtypeEquiv
  intro I
  rw [mem_hilbertSubfunctor_obj_iff]
  exact
    (I.isFiniteLocallyFreeOfDegree_iff_of_isAffine _ d).trans
      (MvPolynomial.isFiniteLocallyFreeOfRank_quotient_iff
        (AffineSpace.toΓBaseChangeEquiv n T.hom) _
        (AffineSpace.toΓBaseChangeEquiv_comp_C n T.hom) _)

/-- The ideal of `Γ(T)[n]` of a point of the Hilbert functor of `𝔸(n; S)` over an affine `T`. -/
noncomputable def polynomialIdeal {T : Over S} [IsAffine T.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) : Ideal (MvPolynomial n Γ(T.left, ⊤)) :=
  (polynomialIdealEquiv x).val

/-- The polynomial-ideal equivalence has the prescribed underlying ideal. -/
lemma polynomialIdealEquiv_apply_val {T : Over S} [IsAffine T.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) :
    (polynomialIdealEquiv x).val = polynomialIdeal x := (rfl)

/-- The polynomial ideal is the inverse image of the family's global ideal under the affine
coordinate isomorphism. -/
lemma polynomialIdeal_def {T : Over S} [IsAffine T.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) :
    polynomialIdeal x =
      (x.val.ideal ⟨⊤, isAffineOpen_top _⟩).comap (AffineSpace.toΓBaseChange n T.hom) := by
  -- The composite uses the coordinate equivalence's ring map before its characteristic law.
  have h : polynomialIdeal x = (x.val.ideal ⟨⊤, isAffineOpen_top _⟩).comap
      (AffineSpace.toΓBaseChangeEquiv n T.hom).toRingHom := (rfl)
  simpa only [RingEquiv.toRingHom_eq_coe, AffineSpace.toΓBaseChangeEquiv_toRingHom] using h

/-- Extending the polynomial ideal to the base-changed affine space recovers the global ideal
of its Hilbert family. -/
@[simp]
lemma map_polynomialIdeal {T : Over S} [IsAffine T.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) :
    (polynomialIdeal x).map (AffineSpace.toΓBaseChange n T.hom) =
      x.val.ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [polynomialIdeal_def]
  exact Ideal.map_comap_of_surjective _ (AffineSpace.toΓBaseChange_bijective n T.hom).2 _

/-- Over an affine test scheme, a point of the Hilbert functor is determined by its ideal. -/
lemma polynomialIdeal_injective {T : Over S} [IsAffine T.left] :
    Function.Injective (polynomialIdeal (n := n) (d := d) (T := T)) := by
  intro x y h
  apply polynomialIdealEquiv.injective
  exact Subtype.ext h

/-- The quotient by the ideal of a point is finite and flat of rank `d`. -/
lemma isFiniteLocallyFreeOfRank_polynomialIdeal {T : Over S} [IsAffine T.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) :
    RingHom.IsFiniteLocallyFreeOfRank d
      (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ polynomialIdeal x)) :=
  (polynomialIdealEquiv x).property

/-- The point of the Hilbert functor with a given ideal of `Γ(T)[n]`. -/
noncomputable def ofPolynomialIdeal {T : Over S} [IsAffine T.left]
    (K : Ideal (MvPolynomial n Γ(T.left, ⊤)))
    (hK : RingHom.IsFiniteLocallyFreeOfRank d
      (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ K))) :
    (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T) :=
  polynomialIdealEquiv.symm ⟨K, hK⟩

/-- The ideal of `ofPolynomialIdeal K` is `K`. -/
@[simp]
lemma polynomialIdeal_ofPolynomialIdeal {T : Over S} [IsAffine T.left]
    (K : Ideal (MvPolynomial n Γ(T.left, ⊤)))
    (hK : RingHom.IsFiniteLocallyFreeOfRank d
      (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ K))) :
    polynomialIdeal (ofPolynomialIdeal K hK) = K :=
  congrArg Subtype.val (polynomialIdealEquiv.apply_symm_apply ⟨K, hK⟩)

/-- Reconstructing a Hilbert point from its polynomial ideal returns that point. -/
@[simp]
lemma ofPolynomialIdeal_polynomialIdeal {T : Over S} [IsAffine T.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) :
    ofPolynomialIdeal (polynomialIdeal x) (isFiniteLocallyFreeOfRank_polynomialIdeal x) = x :=
  polynomialIdealEquiv.symm_apply_apply x

/-- Naturality of `polynomialIdeal`: pulling back a point extends its ideal. -/
lemma polynomialIdeal_map {T W : Over S} [IsAffine T.left] [IsAffine W.left] (a : W ⟶ T)
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) :
    polynomialIdeal ((hilbertFunctor (𝔸(n; S) ↘ S) d).map a.op x) =
      (polynomialIdeal x).map (MvPolynomial.map a.left.appTop.hom) := by
  have hT : x.val.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (polynomialIdeal x).map (AffineSpace.toΓBaseChange n T.hom) :=
    (map_polynomialIdeal x).symm
  generalize polynomialIdeal x = K at hT
  rw [polynomialIdeal_def]
  refine Eq.trans ?_
    (Ideal.comap_map_of_bijective _ (AffineSpace.toΓBaseChange_bijective n W.hom))
  congr 1
  refine (Scheme.IdealSheafData.ideal_comap_of_le _ _ ⟨⊤, isAffineOpen_top _⟩
    ⟨⊤, isAffineOpen_top _⟩ le_top).trans ?_
  rw [hT, Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p ↦ ?_
  have htop : ((Over.pullback (𝔸(n; S) ↘ S)).map a).left.appLE ⊤ ⊤ le_top =
      ((Over.pullback (𝔸(n; S) ↘ S)).map a).left.appTop :=
    Scheme.Hom.appLE_eq_app _
  refine (congrArg (fun r ↦ r (AffineSpace.toΓBaseChange n T.hom p)) htop).trans ?_
  simpa only [Over.pullback_map_left, pullback.map,
    Category.comp_id, RingHom.comp_apply] using
      AffineSpace.appTop_pullbackMap_toΓBaseChange (n := n) T.hom W.hom a.left (Over.w a) p

end Dictionary

section Universal


variable {n : Type u} {S : Scheme.{u}} [IsAffine S] {d : ℕ}


/-- The universal point of the Hilbert functor over `basisChart w`. -/
noncomputable def basisChartPoint (w : Fin d → MvPolynomial n Γ(S, ⊤)) :
    (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op (basisChart w)) := by
  let := (basisChart w).hom.appTop.hom.toAlgebra
  exact ofPolynomialIdeal (basisChartEquiv w (basisChart w) (𝟙 _)).val
    (by
      simpa only [Fintype.card_fin] using
        (IsQuotientBasis.isFiniteLocallyFreeOfRank
          (basisChartEquiv w (basisChart w) (𝟙 _)).property))

/-- The ideal of the pullback of the universal point along `b`. -/
lemma polynomialIdeal_map_basisChartPoint {w : Fin d → MvPolynomial n Γ(S, ⊤)} {W : Over S}
    [IsAffine W.left] (b : W ⟶ basisChart w) :
    polynomialIdeal ((hilbertFunctor (𝔸(n; S) ↘ S) d).map b.op (basisChartPoint w)) =
      (quotientBasisIdeal w).map (MvPolynomial.map (basisChartRingHom b)) := by
  rw [polynomialIdeal_map, basisChartPoint, polynomialIdeal_ofPolynomialIdeal,
    ← basisChartEquiv_comp, Category.comp_id, basisChartEquiv_apply]

/-- The annihilator of the cokernel of the images of the `w l` in the quotient of `Γ(T)[n]`
of a point `x`: the locus of `T` where these images span, hence form a basis. -/
noncomputable def basisAnnihilator {T : Over S} [IsAffine T.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) (w : Fin d → MvPolynomial n Γ(S, ⊤)) :
    Ideal Γ(T.left, ⊤) :=
  Module.annihilator Γ(T.left, ⊤) ((MvPolynomial n Γ(T.left, ⊤) ⧸ polynomialIdeal x) ⧸
    Submodule.span Γ(T.left, ⊤) (Set.range fun l ↦
      Ideal.Quotient.mk (polynomialIdeal x) (MvPolynomial.map T.hom.appTop.hom (w l))))

omit [IsAffine S] in
/-- The basis annihilator is the annihilator of the cokernel of the prescribed generators. -/
lemma basisAnnihilator_def {T : Over S} [IsAffine T.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T))
    (w : Fin d → MvPolynomial n Γ(S, ⊤)) :
    basisAnnihilator x w =
      Module.annihilator Γ(T.left, ⊤) ((MvPolynomial n Γ(T.left, ⊤) ⧸ polynomialIdeal x) ⧸
        Submodule.span Γ(T.left, ⊤) (Set.range fun l ↦
          Ideal.Quotient.mk (polynomialIdeal x) (MvPolynomial.map T.hom.appTop.hom (w l)))) :=
  (rfl)

/-- A pullback of `x` comes from the universal point if and only if `basisAnnihilator x w` generates
the unit ideal. -/
lemma exists_eq_basisChartPoint_iff {T W : Over S} [IsAffine T.left] [IsAffine W.left]
    (x : (hilbertFunctor (𝔸(n; S) ↘ S) d).obj (op T)) (w : Fin d → MvPolynomial n Γ(S, ⊤))
    (a : W ⟶ T) :
    (∃ b : W ⟶ basisChart w, (hilbertFunctor (𝔸(n; S) ↘ S) d).map a.op x =
      (hilbertFunctor (𝔸(n; S) ↘ S) d).map b.op (basisChartPoint w)) ↔
      (basisAnnihilator x w).map a.left.appTop.hom = ⊤ := by
  let := W.hom.appTop.hom.toAlgebra
  obtain ⟨hfin, -, -⟩ := (RingHom.isFiniteLocallyFreeOfRank_algebraMap_iff (d := d)).mp
    (isFiniteLocallyFreeOfRank_polynomialIdeal x)
  have hW := isFiniteLocallyFreeOfRank_polynomialIdeal
    ((hilbertFunctor (𝔸(n; S) ↘ S) d).map a.op x)
  rw [polynomialIdeal_map] at hW
  obtain ⟨-, hflat, hrank⟩ :=
    (RingHom.isFiniteLocallyFreeOfRank_algebraMap_iff (d := d)).mp hW
  have hw (l : Fin d) : MvPolynomial.map (algebraMap Γ(S, ⊤) Γ(W.left, ⊤)) (w l) =
      MvPolynomial.map a.left.appTop.hom (MvPolynomial.map T.hom.appTop.hom (w l)) := by
    rw [MvPolynomial.map_map, RingHom.algebraMap_toAlgebra, ← Over.w a, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp]
  rw [basisAnnihilator_def, ← RingHom.span_range_mk_map_eq_top_iff]
  simp_rw [← hw]
  trans IsQuotientBasis w ((polynomialIdeal x).map (MvPolynomial.map a.left.appTop.hom))
  · rw [← polynomialIdeal_map]
    constructor
    · rintro ⟨b, hb⟩
      rw [hb, polynomialIdeal_map_basisChartPoint]
      simpa only [basisChartEquiv_apply] using (basisChartEquiv w W b).property
    · intro h
      let b := (basisChartEquiv w W).symm ⟨_, h⟩
      refine ⟨b, polynomialIdeal_injective ?_⟩
      rw [polynomialIdeal_map_basisChartPoint, ← basisChartEquiv_apply]
      exact congrArg Subtype.val ((basisChartEquiv w W).apply_symm_apply ⟨_, h⟩).symm
  · exact ⟨fun h ↦ h.span_eq_top, fun h ↦
      ⟨Module.linearIndependent_of_span_eq_top_of_rankAtStalk _ h
        (fun m _ ↦ by simpa only [Fintype.card_fin] using hrank ⟨m, inferInstance⟩), h⟩⟩

end Universal

/-- A basis-chart morphism over an affine test scheme is determined by its Hilbert family. -/
lemma basisChartPoint_injective {indeterminates : Type u} {base : Scheme.{u}} [IsAffine base]
    {rank : ℕ} (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) [IsAffine test.left] :
    Function.Injective (fun chartMap : test ⟶ basisChart family ↦
      (hilbertFunctor (𝔸(indeterminates; base) ↘ base) rank).map chartMap.op
        (basisChartPoint family)) := by
  intro firstMap secondMap equality
  let := test.hom.appTop.hom.toAlgebra
  have idealEquality := congrArg polynomialIdeal equality
  rw [polynomialIdeal_map_basisChartPoint, polynomialIdeal_map_basisChartPoint] at idealEquality
  apply (basisChartEquiv family test).injective
  apply Subtype.ext
  simpa only [basisChartEquiv_apply] using idealEquality

/-- On an affine test scheme, the locus where a Hilbert point factors through a basis chart
is open. -/
lemma exists_opens_basisChartPoint {indeterminates : Type u} {base : Scheme.{u}} [IsAffine base]
    {rank : ℕ} (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) [IsAffine test.left]
    (point : (hilbertFunctor (𝔸(indeterminates; base) ↘ base) rank).obj (op test)) :
    ∃ openSubset : test.left.Opens, ∀ (smallerTest : Over base) [IsAffine smallerTest.left]
      (restriction : smallerTest ⟶ test),
      (∃ chartMap : smallerTest ⟶ basisChart family,
        (hilbertFunctor (𝔸(indeterminates; base) ↘ base) rank).map restriction.op point =
          (hilbertFunctor (𝔸(indeterminates; base) ↘ base) rank).map chartMap.op
            (basisChartPoint family)) ↔ Set.range restriction.left ⊆ openSubset := by
  refine ⟨⟨(test.left.zeroLocus (U := ⊤)
    (basisAnnihilator point family : Set Γ(test.left, ⊤)))ᶜ,
      (Scheme.zeroLocus_isClosed _ _).isOpen_compl⟩, fun smallerTest _ restriction ↦ ?_⟩
  rw [exists_eq_basisChartPoint_iff, ← Scheme.Hom.range_subset_compl_zeroLocus_iff]
  -- Membership in the constructed Opens object is membership in its complement-zero-locus set.
  rfl

/-- Every Hilbert point over an affine scheme is locally induced by a basis chart. -/
lemma exists_basisChartPoint {indeterminates : Type u} {base : Scheme.{u}} [IsAffine base]
    {rank : ℕ} (test : Over base) [IsAffine test.left]
    (point : (hilbertFunctor (𝔸(indeterminates; base) ↘ base) rank).obj (op test))
    (testPoint : test.left) :
    ∃ (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
      (smallerTest : Over base) (restriction : smallerTest ⟶ test)
      (chartMap : smallerTest ⟶ basisChart family),
      IsOpenImmersion restriction.left ∧ testPoint ∈ Set.range restriction.left ∧
        (hilbertFunctor (𝔸(indeterminates; base) ↘ base) rank).map restriction.op point =
          (hilbertFunctor (𝔸(indeterminates; base) ↘ base) rank).map chartMap.op
            (basisChartPoint family) := by
  obtain ⟨finite, flat, constantRank⟩ :=
    (RingHom.isFiniteLocallyFreeOfRank_algebraMap_iff (d := rank)).mp
      (isFiniteLocallyFreeOfRank_polynomialIdeal point)
  obtain ⟨monomials, annihilatorNotContained⟩ :=
    Ideal.exists_monomials_annihilator_not_le (polynomialIdeal point)
      (test.left.toSpecΓ testPoint) (constantRank _)
  obtain ⟨denominator, inAnnihilator, notInPrime⟩ := Set.not_subset.mp annihilatorNotContained
  let family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤) :=
    fun index ↦ MvPolynomial.monomial (monomials index) 1
  have familyEquality : (fun index ↦ Ideal.Quotient.mk (polynomialIdeal point)
      (MvPolynomial.map test.hom.appTop.hom (family index))) =
      fun index ↦ Ideal.Quotient.mk (polynomialIdeal point)
        (MvPolynomial.monomial (monomials index) 1) := by
    simp [family, MvPolynomial.map_monomial]
  have denominatorInAnnihilator : denominator ∈ basisAnnihilator point family := by
    rwa [basisAnnihilator, familyEquality]
  let smallerTest : Over base := Over.mk ((test.left.basicOpen denominator).ι ≫ test.hom)
  have : IsAffine smallerTest.left := (isAffineOpen_top test.left).basicOpen denominator
  let restriction : smallerTest ⟶ test := Over.homMk (test.left.basicOpen denominator).ι
  have restrictionRange : Set.range restriction.left = test.left.basicOpen denominator :=
    Scheme.Opens.range_ι _
  obtain ⟨chartMap, familyEquality⟩ :=
    (exists_eq_basisChartPoint_iff (W := smallerTest) point family restriction).mpr (by
      rw [← Scheme.Hom.range_subset_compl_zeroLocus_iff, restrictionRange]
      exact fun element membership vanishing ↦
        (Scheme.mem_zeroLocus_iff _ _ _).mp vanishing denominator
          denominatorInAnnihilator membership)
  refine ⟨family, smallerTest, restriction, chartMap,
    inferInstanceAs (IsOpenImmersion (test.left.basicOpen denominator).ι), ?_, familyEquality⟩
  rw [restrictionRange, ← Scheme.toSpecΓ_preimage_basicOpen]
  exact notInPrime

end AlgebraicGeometry.Hilbert
