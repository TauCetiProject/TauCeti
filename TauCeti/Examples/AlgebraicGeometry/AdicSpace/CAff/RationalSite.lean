/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Sheaves.SheafCondition.Sites
import TauCeti.AlgebraicGeometry.AdicSpace.CAff.RationalSite
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.PadicInt
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.OpenMapping
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.StableUniform
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
import TauCeti.RingTheory.Huber.Padic.TateAlgebra
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Tests for `CAff`, the rational-covering site, and `OpenMapping`

Concrete positive checks, degenerate boundary checks, and sharpness non-examples for:
* `TauCeti.CAff`, `TauCeti.CAff.affineLine`, and `TauCeti.CAff.globalSectionsIsoYoneda`;
* `TauCeti.CAff.IsRationalLocalization`, `TauCeti.CAff.IsRationalCovering`, and
  `TauCeti.CAff.ratTopology`;
* `TauCeti.CAff.IsRationalSheafy` and
  `TauCeti.CAff.isRationalSheafy_iff_isSheafyForEveryPresentation`;
* `TauCeti.ValuationSpectrum.isInducing_presentationLimitMap_of_isSheafFor_spaRationalOpens` and
  `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_iff_isSheaf_forget`.
-/

open CategoryTheory Opposite TopologicalSpace
open scoped Topology

namespace TauCeti.CAff

open Huber ValuationSpectrum

/-! ### Representability of `globalSections` by `(ℤ[T], ℤ)` vs `(ℤ[T], ℤ[T])` -/

/-- *affineLine_eval_and_yoneda*: on `CAff.discrete ℤ`, evaluation at `0` and `1` gives distinct
morphisms out of `affineLine`, the indeterminate `X` lies outside `(ℤ[X], ℤ)⁺`, and
`CAff.globalSections` is naturally isomorphic to `yoneda.obj (op affineLine)`. -/
example :
    eval (discrete ℤ) (0 : ℤ) ≠ eval (discrete ℤ) (1 : ℤ) ∧
      affineLineVar ∉ affineLine.pair.plus ∧
      Nonempty (globalSections.{0} ≅ yoneda.obj (op affineLine)) :=
  ⟨fun h ↦ Int.zero_ne_one ((eval_bijective (discrete ℤ)).1 h),
    affineLineVar_notMem_plus, ⟨globalSectionsIsoYoneda⟩⟩

/-- *affineLine_vs_discrete_polynomial_sharpness*: for `(ℚ_[p], ℚ_[p]°)`, the unbounded element
`p⁻¹ ∈ ℚ_[p]` corresponds via `eval` to a morphism `affineLine ⟶ CAff.of (ℚ_[p], ℚ_[p]°)`, whereas
NO morphism `discrete (Polynomial ℤ) ⟶ CAff.of (ℚ_[p], ℚ_[p]°)` can send `X` to `p⁻¹` because
`X ∈ (discrete ℤ[X]).pair.plus = ⊤` while `p⁻¹ ∉ ℚ_[p]°`. -/
example (p : ℕ) [Fact p.Prime] :
    (∃ f : affineLine ⟶ CAff.of (Pair.powerBounded ℚ_[p]),
        f.toRingHom affineLineVar = (p : ℚ_[p])⁻¹) ∧
      ¬ ∃ g : discrete (Polynomial ℤ) ⟶ CAff.of (Pair.powerBounded ℚ_[p]),
        g.toRingHom Polynomial.X = (p : ℚ_[p])⁻¹ := by
  refine ⟨⟨eval (CAff.of (Pair.powerBounded ℚ_[p])) (p : ℚ_[p])⁻¹, eval_affineLineVar _ _⟩, ?_⟩
  rintro ⟨g, hg⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  have hx : (Polynomial.X : (discrete (Polynomial ℤ)).ring) ∈
      (discrete (Polynomial ℤ)).pair.plus := by
    rw [discrete_plus]
    exact Subring.mem_top _
  have hmem : (p : ℚ_[p])⁻¹ ∈ powerBoundedSubring ℚ_[p] := by
    have h := g.map_mem_plus Polynomial.X hx
    rwa [hg, Pair.powerBounded_plus] at h
  have hle : ‖(p : ℚ_[p])⁻¹‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp hmem)
  rw [norm_inv] at hle
  exact not_lt_of_ge hle (one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hp0, _root_.Padic.norm_p_lt_one⟩)

/-! ### Degenerate vs nontrivial boundary cases (`PUnit` vs `ℤ`) -/

/-- *degenerate_zero_pair*: on `discrete PUnit`, `Spa` is empty, `𝟙` is a rational localization for
`({1}, 0)`, the empty family is a rational covering, and the empty sieve belongs to `ratTopology`.
-/
example :
    IsEmpty (spa.obj (op (discrete PUnit.{1}))) ∧
      IsRationalLocalization (𝟙 (discrete PUnit.{1})) {1} 0 ∧
      IsRationalCovering (discrete PUnit.{1}) Fin.elim0 Fin.elim0 ∧
      (⊥ : Sieve (op (discrete PUnit.{1}))) ∈ ratTopology (op (discrete PUnit.{1})) := by
  have hsub : Subsingleton (discrete PUnit.{1}).ring := inferInstanceAs (Subsingleton PUnit.{1})
  exact ⟨(isEmpty_spa_iff _).mpr hsub,
    (isRationalLocalization_id_zero_iff _ {1} (by simp)).mpr hsub,
    (isRationalCovering_empty_iff _ Fin.elim0 Fin.elim0).mpr hsub,
    (bot_mem_ratTopology_iff _).mpr hsub⟩

/-- *nontrivial_discrete_int*: on `discrete ℤ`, `Spa` is nonempty, `𝟙` is a rational localization
for `({1}, 1)` but NOT for `({1}, 0)`, the empty family is NOT a rational covering, and `⊥` is NOT
in `ratTopology`. -/
example :
    ¬ IsEmpty (spa.obj (op (discrete ℤ))) ∧
      IsRationalLocalization (𝟙 (discrete ℤ)) {1} 1 ∧
      ¬ IsRationalLocalization (𝟙 (discrete ℤ)) {1} 0 ∧
      ¬ IsRationalCovering (discrete ℤ) Fin.elim0 Fin.elim0 ∧
      (⊥ : Sieve (op (discrete ℤ))) ∉ ratTopology (op (discrete ℤ)) :=
  ⟨by rw [isEmpty_spa_iff, discrete_ring]; exact not_subsingleton ℤ,
    isRationalLocalization_id_one _,
    by rw [isRationalLocalization_id_zero_iff _ {1} (by simp), discrete_ring]
       exact not_subsingleton ℤ,
    by rw [isRationalCovering_empty_iff, discrete_ring]; exact not_subsingleton ℤ,
    by rw [bot_mem_ratTopology_iff, discrete_ring]; exact not_subsingleton ℤ⟩

/-! ### Positive rational-sheafiness and open-mapping checks on Tate pairs -/

/-- *padic_and_tateAlgebra_isRationalSheafy*: every complete Huber pair on `ℚ_[p]` or on the
Gauss-normed Tate algebra `ℚ_p⟨T₁, …, Tₘ⟩` satisfies `IsRationalSheafy`, and on `ℚ_[p]` the site
condition `IsRationalSheafy` is equivalent to `IsSheafyForEveryPresentation`. -/
example (p m : ℕ) [Fact p.Prime] (S : Pair ℚ_[p])
    (T : Pair (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin m ↦ (1 : ℝ))) :
    (CAff.of S).IsRationalSheafy ∧
      (CAff.of T).IsRationalSheafy ∧
      ((CAff.of S).IsRationalSheafy ↔ IsSheafyForEveryPresentation S.plus) :=
  ⟨(isRationalSheafy_iff_isSheafyForEveryPresentation (CAff.of S)).mpr
      (isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements),
    (isRationalSheafy_iff_isSheafyForEveryPresentation (CAff.of T)).mpr
      (isSheafyForEveryPresentation_of_isStronglyNoetherian T.isRingOfIntegralElements),
    isRationalSheafy_iff_isSheafyForEveryPresentation (CAff.of S)⟩

/-- *stablyUniform_isRationalSheafy_and_inducing*: every complete Hausdorff stably uniform Tate
Huber pair is rational-sheafy, its topological structure presheaf sheafiness is equivalent to
set-level sheafiness, and on any countable rational cover of a rational open the product
restriction map on presentation limits is inducing (`Topology.IsInducing`). -/
example {A : Type} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsTateRing A] [IsStablyUniform A] (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    (CAff.of S).IsRationalSheafy ∧
      (Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
          (presentationLimitPresheaf P S.plus) ↔
        Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
          (presentationLimitPresheaf P S.plus ⋙
            TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat)) ∧
      ∀ {W : Opens ↥(ValuationSpectrum.spa S.plus)} {κ : Type} [Countable κ]
        {V : κ → Opens ↥(ValuationSpectrum.spa S.plus)},
        W ∈ spaRationalOpens S.plus → (∀ k, V k ∈ spaRationalOpens S.plus) →
        ∀ hcov : ⨆ k, V k = W,
        Topology.IsInducing (fun (x : presentationLimit (P := P) S.plus W) (k : κ) ↦
          (presentationLimitMap (P := P) ((le_iSup V k).trans_eq hcov)).hom.1 x) := by
  have hsheaf : IsSheafyForEveryPresentation S.plus :=
    isSheafyForEveryPresentation_of_isStablyUniform S.isRingOfIntegralElements
  have hset : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
      (presentationLimitPresheaf P S.plus ⋙
        TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat) (hsheaf.isSheaf P hP)
  refine ⟨.of_isSheafyForEveryPresentation hsheaf,
    isSheaf_presentationLimitPresheaf_iff_isSheaf_forget P
      S.isRingOfIntegralElements.isPowerBounded_of_mem,
    fun {W} {κ} _ {V} hW hV hcov ↦ isInducing_presentationLimitMap_of_isSheafFor_spaRationalOpens P
      S.isRingOfIntegralElements.isPowerBounded_of_mem hW hV
      (fun k ↦ (le_iSup V k).trans_eq hcov) ?_⟩
  subst hcov
  rw [Presieve.isSheafFor_iff_generate]
  refine hset.isSheafFor _ ?_
  convert TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology (X := TopCat.of _) V
  funext Z f
  exact propext ⟨fun ⟨k⟩ ↦ ⟨k, rfl⟩,
    fun ⟨k, hk⟩ ↦ by subst hk; rw [Subsingleton.elim f (homOfLE (le_iSup V k))]; exact .mk k⟩

/-! ### Sharpness non-examples on `(ℤ_p, ℤ_p)` -/

/-- *isRationalLocalization_isOpen_span_sharp*: on `Zp = (ℤ_[p], ℤ_[p])`, the identity `𝟙 Zp` with
`(T, s) = (∅, 1)` satisfies both `mapsTo_spaComap` (every point of `Spa(Zp)` lies in `R(∅/1)`) and
`existsUnique_factorization` (every `ψ : Zp ⟶ Z` factors uniquely through `𝟙 Zp`), yet
`¬ IsRationalLocalization (𝟙 Zp) ∅ 1` because `Ideal.span ∅ = ⊥` is not open in `ℤ_[p]`. -/
example (p : ℕ) [Fact p.Prime] :
    (∀ w : ValuationSpectrum.spa (CAff.of (Pair.powerBounded ℤ_[p])).pair.plus,
      (Pair.Hom.spaComap (𝟙 (CAff.of (Pair.powerBounded ℤ_[p]))) w).1 ∈
        rationalSubset (Pair.powerBounded ℤ_[p]).plus ∅ 1) ∧
      (∀ (Z : CAff.{0}) (ψ : CAff.of (Pair.powerBounded ℤ_[p]) ⟶ Z),
        ∃! χ : CAff.of (Pair.powerBounded ℤ_[p]) ⟶ Z,
          𝟙 (CAff.of (Pair.powerBounded ℤ_[p])) ≫ χ = ψ) ∧
      ¬ IsRationalLocalization (𝟙 (CAff.of (Pair.powerBounded ℤ_[p]))) ∅ 1 := by
  refine ⟨fun w ↦ ?_,
    fun Z ψ ↦ ⟨ψ, Category.id_comp ψ, fun χ hχ ↦ (Category.id_comp χ).symm.trans hχ⟩,
    fun h ↦ ?_⟩
  · rw [id_spaComap, id_eq, mem_rationalSubset_iff]
    have hw1 : w.1 ∈ rationalSubset (Pair.powerBounded ℤ_[p]).plus {1} 1 := by
      rw [rationalSubset_singleton_one]
      exact w.2
    exact ⟨w.2, fun t ht ↦ absurd ht (Finset.notMem_empty t),
      ((mem_rationalSubset_iff _ {1} 1 w.1).mp hw1).2.2⟩
  · have hopen : IsOpen ({0} : Set ℤ_[p]) := by
      simpa only [Finset.coe_empty, Ideal.span_empty, Submodule.bot_coe] using h.isOpen_span
    have : (𝓝[≠] (0 : ℤ_[p])).NeBot :=
      (_root_.PadicInt.isOpenEmbedding_coe.toOpenPartialHomeomorph _).nhdsNE_neBot trivial
    exact not_isOpen_singleton (0 : ℤ_[p]) hopen

/-- *isRationalLocalization_mapsTo_sharp*: on `Zp = (ℤ_[p], ℤ_[p])`, `(T, s) = ({1}, p)` has open
span `Ideal.span {1} = ⊤`, yet `¬ IsRationalLocalization (𝟙 Zp) {1} p` because the non-analytic
closed point of `Spa(ℤ_[p], ℤ_[p])` sends `p` to `0` and therefore lies outside `R({1}/p)`. -/
example (p : ℕ) [Fact p.Prime] :
    IsOpen (Ideal.span ({1} : Set ℤ_[p]) : Set ℤ_[p]) ∧
      ¬ IsRationalLocalization (𝟙 (CAff.of (Pair.powerBounded ℤ_[p]))) {1} (p : ℤ_[p]) := by
  refine ⟨by simp, fun h ↦ ?_⟩
  have hmem_spa : trivialSection (⊤ : PrimeSpectrum ℤ_[p]) ∈
      ValuationSpectrum.spa (CAff.of (Pair.powerBounded ℤ_[p])).pair.plus := by
    rw [spa_padicInt]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hrat := h.mapsTo_spaComap ⟨trivialSection (⊤ : PrimeSpectrum ℤ_[p]), hmem_spa⟩
  rw [id_spaComap, id_eq, mem_rationalSubset_iff] at hrat
  refine hrat.2.2 ((trivialSection_vle_iff _ _ _).mpr (Or.inl ?_))
  rw [IsLocalRing.PrimeSpectrum.asIdeal_top, _root_.PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.mem_span_singleton_self _

/-- *nonAdic_pullback_sharp*: the canonical morphism `ψ : discrete ℤ ⟶ (ℤ_[p], ℤ_[p])` is not adic;
the family `T () = ∅`, `s () = 1` is a rational covering of `discrete ℤ`, the naive image family
`T' () = ∅`, `s' () = 1` along `ψ` is NOT a rational covering of `(ℤ_[p], ℤ_[p])` (showing
`[IsAdicHom]` in `IsRationalCovering.pullback` is necessary), yet pulling back the generated sieve
in `CAffᵒᵖ` still lies in `ratTopology` on `(ℤ_[p], ℤ_[p])`. -/
example (p : ℕ) [Fact p.Prime] :
    ∃ (ψ : discrete ℤ ⟶ CAff.of (Pair.powerBounded ℤ_[p]))
      (hcovZ : IsRationalCovering (discrete ℤ) (fun _ : Unit ↦ ∅) (fun _ : Unit ↦ 1)),
      ψ.toRingHom = Int.castRingHom ℤ_[p] ∧
      ¬ IsAdicHom ψ.toRingHom ∧
      ¬ IsRationalCovering (CAff.of (Pair.powerBounded ℤ_[p]))
        (fun _ : Unit ↦ ∅) (fun _ : Unit ↦ 1) ∧
      (Sieve.generate ((discrete ℤ).rationalCoverPresieve (fun _ : Unit ↦ ∅) (fun _ : Unit ↦ 1)
        hcovZ.isOpen_span)).pullback ψ.op ∈
        ratTopology (op (CAff.of (Pair.powerBounded ℤ_[p]))) := by
  let ψ : discrete ℤ ⟶ CAff.of (Pair.powerBounded ℤ_[p]) :=
    { toRingHom := Int.castRingHom ℤ_[p]
      continuous_toRingHom := continuous_of_discreteTopology
      map_mem_plus := fun (n : ℤ) _ ↦ by
        rw [Pair.powerBounded_plus]
        exact mem_powerBoundedSubring.mpr
          (IsPowerBounded.of_norm_le_one (_root_.PadicInt.norm_le_one (n : ℤ_[p]))) }
  have hcovZ : IsRationalCovering (discrete ℤ) (fun _ : Unit ↦ ∅) (fun _ : Unit ↦ 1) :=
    { isOpen_span _ := isOpen_discrete _
      iUnion_eq_univ := Set.eq_univ_of_forall fun v ↦ Set.mem_iUnion.mpr ⟨(), by
        have hv1 : v.1 ∈ rationalSubset (discrete ℤ).pair.plus {1} 1 := by
          rw [rationalSubset_singleton_one]
          exact v.2
        exact (mem_rationalSubset_iff _ ∅ 1 v.1).mpr
          ⟨v.2, fun t ht ↦ absurd ht (Finset.notMem_empty t),
            ((mem_rationalSubset_iff _ {1} 1 v.1).mp hv1).2.2⟩⟩ }
  have : (𝓝[≠] (0 : ℤ_[p])).NeBot :=
    (_root_.PadicInt.isOpenEmbedding_coe.toOpenPartialHomeomorph _).nhdsNE_neBot trivial
  refine ⟨ψ, hcovZ, rfl, fun hadic ↦ ?_, fun hcovZp ↦ ?_, ?_⟩
  · have hopen_bot : IsOpen (Ideal.span (ψ.toRingHom ''
        (((⊥ : Ideal (discrete ℤ).ring) : Set (discrete ℤ).ring))) : Set ℤ_[p]) :=
      hadic.isOpen_map (isOpen_discrete _)
    rw [Submodule.bot_coe, Set.image_singleton, map_zero,
      Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_coe] at hopen_bot
    exact not_isOpen_singleton (0 : ℤ_[p]) hopen_bot
  · have hopen_emp : IsOpen (Ideal.span ((∅ : Finset ℤ_[p]) : Set ℤ_[p]) : Set ℤ_[p]) :=
      hcovZp.isOpen_span ()
    rw [Finset.coe_empty, Ideal.span_empty, Submodule.bot_coe] at hopen_emp
    exact not_isOpen_singleton (0 : ℤ_[p]) hopen_emp
  · exact ratTopology.pullback_stable ψ.op (generate_rationalCoverPresieve_mem_ratTopology hcovZ)

end TauCeti.CAff
