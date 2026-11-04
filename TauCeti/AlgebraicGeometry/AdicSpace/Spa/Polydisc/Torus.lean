/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Pair

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral

/-!
# The affinoid relative torus inside the relative closed polydisc

Given a Huber pair `S = (A, A⁺)` and `n : ℕ`, the *relative torus locus*
`TauCeti.Huber.Pair.torusLocus S n` inside `Spa(A⟨T₁, …, Tₙ⟩, A⁺⟨T₁, …, Tₙ⟩)` is the rational
subset `R({1} / (T₁ ⋯ Tₙ))` where the product of the coordinate variables has valuation at least
`1`. Since every coordinate variable `Tᵢ` already lies in `S.polydiscPlus n` and therefore satisfies
`v(Tᵢ) ≤ 1` on `spa (S.polydiscPlus n)`, the single inequality `1 ≤ v(T₁ ⋯ Tₙ)` forces `v(Tᵢ) = 1`
for every `i : Fin n` simultaneously (`TauCeti.Huber.Pair.mem_torusLocus_iff_forall_one_vle` and
`TauCeti.Huber.Pair.mem_torusLocus_iff_forall_valuation_eq_one`). At `n = 0` the empty product is
`1` and `S.torusLocus 0 = spa (S.polydiscPlus 0)`.

For a morphism `h : Pair.Hom (S.polydisc n) U` into a complete Hausdorff Huber pair `U = (C, C⁺)`,
`h.spaComap` maps `spa U.plus` into `S.torusLocus n` if and only if each coordinate image
`h(Tᵢ) ∈ C` is a unit whose inverse also lies in `C⁺` (`TauCeti.Huber.Pair.mem_torusLocus_iff`),
equivalently a unit of the ring `C⁺`. Combining this characterization with the universal property of
`S.polydisc n` identifies morphisms `S.polydisc n → U` over `z : Pair.Hom S U` factoring through
the torus locus with `n`-tuples in `(U.plus)ˣ` (`TauCeti.Huber.Pair.polydisc.torusHomEquiv`).

Translating coordinates by `a : Fin n → S.plus` via `TauCeti.Huber.Pair.polydisc.taylorHom` gives
automorphisms of `S.polydisc n` over `S`. In dimension `1`, the unit circle `S.torusLocus 1`
(`|T| = 1`) and its translate by `1` (`|T + 1| = 1`) cover the whole relative closed unit disc
`spa (S.polydiscPlus 1)` (`TauCeti.Huber.Pair.torusLocus_union_preimage_taylorHom_eq_spa`), since
`1 = (T + 1) - T` prevents both `|T| < 1` and `|T + 1| < 1` at any nonarchimedean valuation. None
of the results in this file require completeness, Hausdorffness, or a uniform structure on the base
ring `A`.

## Main definitions

* `TauCeti.Huber.Pair.torusLocus`: the rational subset `R({1} / (∏ᵢ Tᵢ))` inside
  `spa (S.polydiscPlus n)`.
* `TauCeti.Huber.Pair.polydisc.torusHomEquiv`: bijection between morphisms `S.polydisc n → U` over
  `z : Pair.Hom S U` landing in `S.torusLocus n` and unit tuples `Fin n → (U.plus)ˣ`.

## Main results

* `TauCeti.Huber.Pair.mem_torusLocus_iff_forall_one_vle` and
  `TauCeti.Huber.Pair.mem_torusLocus_iff_forall_valuation_eq_one`: coordinatewise characterization
  of points in `S.torusLocus n`.
* `TauCeti.Huber.Pair.mem_torusLocus_iff`: pullback characterization of morphisms into a complete
  Hausdorff Huber pair landing in `S.torusLocus n`.
* `TauCeti.Huber.Pair.torusLocus_union_preimage_taylorHom_eq_spa`: the two-torus open cover
  `spa (S.polydiscPlus 1) = S.torusLocus 1 ∪ comap (T ↦ T + 1) ⁻¹' S.torusLocus 1`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §7.3 and Lemma 8.1.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343v3, §24, Proposition 24.4.
* P. Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. (2)
  182 (2015), 945–1066, §4, Example 4.4.
-/

public section

namespace TauCeti.Huber

open TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-! ### The torus locus and its pointwise description -/

/-- **The relative torus locus inside `Spa(A⟨T₁, …, Tₙ⟩, A⁺⟨T₁, …, Tₙ⟩)`**: the rational subset
`R({1} / (T₁ ⋯ Tₙ))` where every coordinate variable has valuation `1`. -/
noncomputable def Pair.torusLocus (S : Pair A) (n : ℕ) :
    Set (Spv (restrictedMvPowerSeriesCompletion n A)) :=
  rationalSubset (Pair.polydiscPlus S n) {1} (∏ i, Pair.polydiscVar n A i)

/-- Unfolding equation for `TauCeti.Huber.Pair.torusLocus`. -/
theorem Pair.torusLocus_def (S : Pair A) (n : ℕ) :
    S.torusLocus n =
      rationalSubset (Pair.polydiscPlus S n) {1} (∏ i, Pair.polydiscVar n A i) :=
  (rfl)

/-- Every point of `S.torusLocus n` lies in `spa (S.polydiscPlus n)`. -/
theorem Pair.torusLocus_subset_spa (S : Pair A) (n : ℕ) :
    S.torusLocus n ⊆ spa (S.polydiscPlus n) :=
  rationalSubset_subset_spa _ _ _

/-- The preimage of `S.torusLocus n` in `spa (S.polydiscPlus n)` is open. -/
theorem Pair.isOpen_val_preimage_torusLocus (S : Pair A) (n : ℕ) :
    IsOpen (((↑) : spa (S.polydiscPlus n) → Spv (restrictedMvPowerSeriesCompletion n A)) ⁻¹'
      S.torusLocus n) :=
  isOpen_val_preimage_rationalSubset _ _ _

/-- In zero variables, the empty product of coordinates is `1` and the torus locus is the whole
adic spectrum `spa (S.polydiscPlus 0)`. -/
@[simp]
theorem Pair.torusLocus_zero (S : Pair A) :
    S.torusLocus 0 = spa (S.polydiscPlus 0) := by
  simpa only [Pair.torusLocus_def, Finset.univ_eq_empty, Finset.prod_empty, Finset.image_singleton,
    RingHom.id_apply] using
    rationalSubset_image_eq_spa (RingHom.id (restrictedMvPowerSeriesCompletion 0 A))
      (S.polydiscPlus 0) {1} 1 (c := 1) (mul_one 1)
      (fun t ht ↦ by
        obtain rfl : t = 1 := Finset.mem_singleton.mp ht
        simp)

/-- **Coordinatewise characterization of `S.torusLocus n` by inequalities**: a point of
`Spv (A⟨T₁, …, Tₙ⟩)` lies in `S.torusLocus n` if and only if it lies in `spa (S.polydiscPlus n)`
and satisfies `1 ≤ᵥ Tᵢ` for every `i : Fin n`. -/
theorem Pair.mem_torusLocus_iff_forall_one_vle (S : Pair A) {n : ℕ}
    {v : Spv (restrictedMvPowerSeriesCompletion n A)} :
    v ∈ S.torusLocus n ↔
      v ∈ spa (S.polydiscPlus n) ∧
        ∀ i : Fin n, v.toValuativeRel.vle 1 (Pair.polydiscVar n A i) := by
  rw [Pair.torusLocus_def, mem_rationalSubset_iff]
  refine ⟨fun ⟨hv, hT, _⟩ ↦ ⟨hv, fun i ↦ ?_⟩, fun ⟨hv, hcoords⟩ ↦ ?_⟩
  · have hprod : 1 ≤ v.valuation (∏ j, Pair.polydiscVar n A j) := by
      simpa only [map_one] using
        (valuation_le_iff v 1 _).mpr (hT 1 (Finset.mem_singleton_self 1))
    rw [map_prod] at hprod
    have herase_le :
        ∏ j ∈ Finset.univ.erase i, v.valuation (Pair.polydiscVar n A j) ≤ 1 :=
      Finset.prod_le_one fun j _ ↦
        valuation_le_one_of_mem_spa hv (S.polydiscVar_mem_polydiscPlus n j)
    have hi : 1 ≤ v.valuation (Pair.polydiscVar n A i) := by
      calc 1 ≤ ∏ j, v.valuation (Pair.polydiscVar n A j) := hprod
        _ = v.valuation (Pair.polydiscVar n A i) *
              ∏ j ∈ Finset.univ.erase i, v.valuation (Pair.polydiscVar n A j) := by
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        _ ≤ v.valuation (Pair.polydiscVar n A i) * 1 := mul_le_mul_right herase_le _
        _ = v.valuation (Pair.polydiscVar n A i) := mul_one _
    exact (valuation_le_iff v 1 _).mp (by simpa only [map_one] using hi)
  · have hprod : v.toValuativeRel.vle 1 (∏ i, Pair.polydiscVar n A i) := by
      have h1 : 1 ≤ v.valuation (∏ i, Pair.polydiscVar n A i) := by
        rw [map_prod]
        exact Finset.one_le_prod fun i _ ↦ by
          simpa only [map_one] using (valuation_le_iff v 1 _).mpr (hcoords i)
      exact (valuation_le_iff v 1 _).mp (by simpa only [map_one] using h1)
    refine ⟨hv, fun t ht ↦ ?_, fun hv0 ↦
      @TauCeti.ValuativeRel.not_vle_zero_of_isUnit _ _ v.toValuativeRel _ isUnit_one
        (v.toValuativeRel.vle_trans hprod hv0)⟩
    obtain rfl : t = 1 := Finset.mem_singleton.mp ht
    exact hprod

/-- **Coordinatewise characterization of `S.torusLocus n` by valuation equalities**: a point lies
in `S.torusLocus n` if and only if it lies in `spa (S.polydiscPlus n)` and every coordinate `Tᵢ`
has valuation `1`. -/
theorem Pair.mem_torusLocus_iff_forall_valuation_eq_one (S : Pair A) {n : ℕ}
    {v : Spv (restrictedMvPowerSeriesCompletion n A)} :
    v ∈ S.torusLocus n ↔
      v ∈ spa (S.polydiscPlus n) ∧
        ∀ i : Fin n, v.valuation (Pair.polydiscVar n A i) = 1 := by
  rw [S.mem_torusLocus_iff_forall_one_vle]
  refine and_congr_right fun hv ↦ forall_congr' fun i ↦ ?_
  rw [← valuation_le_iff, map_one]
  exact ⟨fun h1 ↦ le_antisymm (valuation_le_one_of_mem_spa hv
    (S.polydiscVar_mem_polydiscPlus n i)) h1, fun h ↦ h.ge⟩

/-- No point in `S.torusLocus n` can contain any coordinate `Tᵢ` in its support. -/
theorem Pair.notMem_torusLocus_of_mem_supp (S : Pair A) {n : ℕ}
    {v : Spv (restrictedMvPowerSeriesCompletion n A)} {i : Fin n}
    (hsupp : Pair.polydiscVar n A i ∈ v.supp) :
    v ∉ S.torusLocus n := by
  intro hv
  have h1 := (S.mem_torusLocus_iff_forall_one_vle.mp hv).2 i
  have h0 := (mem_supp_iff v _).mp hsupp
  exact @TauCeti.ValuativeRel.not_vle_zero_of_isUnit _ _ v.toValuativeRel _ isUnit_one
    (v.toValuativeRel.vle_trans h1 h0)

/-! ### Universal property of the relative torus and the two-torus cover -/

/-- If every coordinate `h(Tᵢ)` of a Huber-pair morphism `h : S.polydisc n → U` is a unit whose
inverse lies in `U.plus`, then `h.spaComap` lands in `S.torusLocus n` (with no completeness or
Hausdorffness hypothesis on `U`). -/
theorem Pair.spaComap_mem_torusLocus_of_forall_exists_unit {C : Type*} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    (S : Pair A) {U : Pair C} (n : ℕ)
    (h : Pair.Hom (S.polydisc n) U)
    (hu : ∀ i, ∃ u : Cˣ, (u : C) = h.toRingHom (Pair.polydiscVar n A i) ∧
      ((u⁻¹ : Cˣ) : C) ∈ U.plus)
    (v : spa U.plus) :
    (h.spaComap v).1 ∈ S.torusLocus n := by
  choose u hu_eq hu_inv using hu
  let c : C := ∏ i : Fin n, ((u i)⁻¹ : Cˣ)
  have hc_plus : c ∈ U.plus := prod_mem fun i _ ↦ hu_inv i
  have hmul : h.toRingHom (∏ i, Pair.polydiscVar n A i) * c = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    rw [← hu_eq i, Units.mul_inv]
  rw [Pair.torusLocus_def, Pair.Hom.spaComap_val]
  exact comap_mem_rationalSubset h.continuous_toRingHom h.map_mem_plus {1}
    (∏ i, Pair.polydiscVar n A i) hmul
    (fun t ht ↦ by
      obtain rfl : t = 1 := Finset.mem_singleton.mp ht
      simpa only [map_one, one_mul] using hc_plus) v.2

section CompleteTarget

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [IsHuberRing C] [CompleteSpace C] [T0Space C]

/-- **Characterization of morphisms into a complete Hausdorff Huber pair factoring through
`S.torusLocus n`**: `h.spaComap` maps every point of `spa U.plus` into `S.torusLocus n` if and only
if each `h(Tᵢ)` is a unit of `C` whose inverse lies in `U.plus`. -/
theorem Pair.mem_torusLocus_iff
    (S : Pair A) {U : Pair C} (n : ℕ) (h : Pair.Hom (Pair.polydisc S n) U) :
    (∀ v : spa U.plus, (h.spaComap v).1 ∈ Pair.torusLocus S n) ↔
      ∀ i, ∃ u : Cˣ, (u : C) = h.toRingHom (Pair.polydiscVar n A i) ∧
        ((u⁻¹ : Cˣ) : C) ∈ U.plus := by
  refine ⟨fun hfac i ↦ ?_, S.spaComap_mem_torusLocus_of_forall_exists_unit n h⟩
  have hfac' : ∀ w ∈ spa U.plus,
      comap h.toRingHom w ∈
        rationalSubset (S.polydisc n).plus {1} (∏ j, Pair.polydiscVar n A j) :=
    fun w hw ↦ by
      simpa only [Pair.torusLocus_def, Pair.Hom.spaComap_val] using hfac ⟨w, hw⟩
  have hs : IsUnit (h.toRingHom (∏ j, Pair.polydiscVar n A j)) :=
    isUnit_of_forall_comap_mem_rationalSubset {1} U.isRingOfIntegralElements hfac'
  have := U.isRingOfIntegralElements.isIntegrallyClosedIn
  have hinv_plus : (↑hs.unit⁻¹ : C) ∈ U.plus := by
    rw [← SetLike.mem_coe, coe_eq_setOf_forall_vle_one U.isRingOfIntegralElements.isOpen]
    intro w hw
    simpa only [map_one, one_mul] using
      vle_one_of_comap_mem_rationalSubset hs (hfac' w hw) (Finset.mem_singleton_self 1)
  let r : C :=
    (∏ j ∈ Finset.univ.erase i, h.toRingHom (Pair.polydiscVar n A j)) * ↑hs.unit⁻¹
  have hr_plus : r ∈ U.plus :=
    mul_mem
      (prod_mem fun j _ ↦ h.map_mem_plus _ (S.polydiscVar_mem_polydiscPlus n j))
      hinv_plus
  have hmul : h.toRingHom (Pair.polydiscVar n A i) * r = 1 := by
    calc h.toRingHom (Pair.polydiscVar n A i) * r
        = (h.toRingHom (Pair.polydiscVar n A i) *
            ∏ j ∈ Finset.univ.erase i, h.toRingHom (Pair.polydiscVar n A j)) *
          ↑hs.unit⁻¹ := (mul_assoc _ _ _).symm
      _ = (∏ j, h.toRingHom (Pair.polydiscVar n A j)) * ↑hs.unit⁻¹ :=
          congrArg (· * ↑hs.unit⁻¹)
            (Finset.mul_prod_erase Finset.univ
              (fun j ↦ h.toRingHom (Pair.polydiscVar n A j)) (Finset.mem_univ i))
      _ = h.toRingHom (∏ j, Pair.polydiscVar n A j) * ↑hs.unit⁻¹ :=
          congrArg (· * ↑hs.unit⁻¹) (map_prod h.toRingHom (Pair.polydiscVar n A) Finset.univ).symm
      _ = 1 := hs.mul_val_inv
  exact ⟨⟨h.toRingHom (Pair.polydiscVar n A i), r, hmul, mul_comm _ r ▸ hmul⟩, rfl, hr_plus⟩

/-- **Morphisms `S.polydisc n → U` over `z : Pair.Hom S U` whose `spaComap` lands in
`S.torusLocus n` correspond bijectively to `n`-tuples of units `(U.plus)ˣ`.** -/
noncomputable def Pair.polydisc.torusHomEquiv {S : Pair A}
    {U : Pair C} (z : Pair.Hom S U) (n : ℕ) :
    {h : Pair.Hom (S.polydisc n) U //
      h.comp (S.weightedCompletionHom isWeightFamily_one_weight) = z ∧
        ∀ v : spa U.plus, (h.spaComap v).1 ∈ S.torusLocus n} ≃
      (Fin n → (U.plus)ˣ) where
  toFun h i :=
    let hex := (S.mem_torusLocus_iff n h.1).mp h.2.2 i
    let u := hex.choose
    { val := ⟨h.1.toRingHom (Pair.polydiscVar n A i),
        h.1.map_mem_plus _ (S.polydiscVar_mem_polydiscPlus n i)⟩
      inv := ⟨((u⁻¹ : Cˣ) : C), hex.choose_spec.2⟩
      val_inv := Subtype.ext <|
        (congrArg (· * ((u⁻¹ : Cˣ) : C)) hex.choose_spec.1.symm).trans u.mul_inv
      inv_val := Subtype.ext <|
        (congrArg (((u⁻¹ : Cˣ) : C) * ·) hex.choose_spec.1.symm).trans u.inv_mul }
  invFun u :=
    { val := Pair.polydisc.evalHom z (fun i ↦ (u i : U.plus))
      property := ⟨Pair.polydisc.evalHom_comp_weightedCompletionHom z _,
        (S.mem_torusLocus_iff n _).mpr fun i ↦
          ⟨Units.map U.plus.subtype.toMonoidHom (u i),
            by simp, (u i)⁻¹.1.2⟩⟩ }
  left_inv h := Subtype.ext <| Pair.polydisc.hom_ext
    ((Pair.polydisc.evalHom_comp_weightedCompletionHom z _).trans h.2.1.symm)
    fun i ↦ Pair.polydisc.toRingHom_evalHom_polydiscVar z _ i
  right_inv u := funext fun i ↦ Units.ext <| Subtype.ext <|
    Pair.polydisc.toRingHom_evalHom_polydiscVar z (fun j ↦ (u j : U.plus)) i

@[simp]
theorem Pair.polydisc.torusHomEquiv_apply_coe {S : Pair A}
    {U : Pair C} (z : Pair.Hom S U) (n : ℕ)
    (h : {h : Pair.Hom (S.polydisc n) U //
      h.comp (S.weightedCompletionHom isWeightFamily_one_weight) = z ∧
        ∀ v : spa U.plus, (h.spaComap v).1 ∈ S.torusLocus n})
    (i : Fin n) :
    (((Pair.polydisc.torusHomEquiv z n h i : (U.plus)ˣ) : U.plus) : C) =
      h.1.toRingHom (Pair.polydiscVar n A i) :=
  (rfl)

@[simp]
theorem Pair.polydisc.torusHomEquiv_symm_apply_val {S : Pair A}
    {U : Pair C} (z : Pair.Hom S U) (n : ℕ) (u : Fin n → (U.plus)ˣ) :
    ((Pair.polydisc.torusHomEquiv z n).symm u).1 =
      Pair.polydisc.evalHom z (fun i ↦ (u i : U.plus)) :=
  (rfl)

end CompleteTarget

/-! ### The two-torus cover of the relative closed unit disc -/

/-- **The two-torus cover of the relative closed unit disc** (Scholze, *Étale cohomology of
diamonds*, Proposition 24.4): the relative closed unit disc `spa (S.polydiscPlus 1)` is covered by
the unit torus `S.torusLocus 1` (`|T| = 1`) and its translate by `1` (`|T + 1| = 1`). -/
theorem Pair.torusLocus_union_preimage_taylorHom_eq_spa (S : Pair A) :
    spa (S.polydiscPlus 1) =
      S.torusLocus 1 ∪
        comap (Pair.polydisc.taylorHom S (fun _ : Fin 1 ↦ (1 : S.plus))).toRingHom ⁻¹'
          S.torusLocus 1 := by
  set τ := Pair.polydisc.taylorHom S (fun _ : Fin 1 ↦ (1 : S.plus))
  set τ_inv := Pair.polydisc.taylorHom S (fun _ : Fin 1 ↦ (-1 : S.plus))
  refine Set.Subset.antisymm (fun v hv ↦ ?_) ?_
  · set T := Pair.polydiscVar 1 A 0
    have h1 : 1 ≤ max (v.valuation (T + 1)) (v.valuation T) := by
      calc 1 = v.valuation ((T + 1) - T) := by rw [add_sub_cancel_left, map_one]
        _ ≤ max (v.valuation (T + 1)) (v.valuation T) := v.valuation.map_sub (T + 1) T
    rcases le_max_iff.mp h1 with hT1 | hT
    · refine Or.inr ?_
      rw [Set.mem_preimage, S.mem_torusLocus_iff_forall_one_vle]
      refine ⟨comap_mem_spa τ.continuous_toRingHom τ.map_mem_plus hv,
        Fin.forall_fin_one.mpr ?_⟩
      rw [comap_vle, map_one]
      have hτT : τ.toRingHom T = T + 1 := by
        rw [Pair.polydisc.toRingHom_taylorHom_polydiscVar, OneMemClass.coe_one, map_one]
      rw [hτT, ← valuation_le_iff, map_one]
      exact hT1
    · refine Or.inl (S.mem_torusLocus_iff_forall_one_vle.mpr ⟨hv, Fin.forall_fin_one.mpr ?_⟩)
      exact (valuation_le_iff v 1 T).mp (by simpa only [map_one] using hT)
  · refine Set.union_subset (S.torusLocus_subset_spa 1) fun v hv ↦ ?_
    have hv_spa : comap τ.toRingHom v ∈ spa (S.polydisc 1).plus :=
      S.torusLocus_subset_spa 1 hv
    have hcomp : τ.comp τ_inv = Pair.Hom.id (S.polydisc 1) := by
      have h0 : (fun _ : Fin 1 ↦ (1 : S.plus)) + (fun _ : Fin 1 ↦ (-1 : S.plus)) = 0 := by
        ext
        simp
      rw [Pair.polydisc.taylorHom_comp_taylorHom, h0, Pair.polydisc.taylorHom_zero]
    have hid : comap τ_inv.toRingHom (comap τ.toRingHom v) = v := by
      rw [← Function.comp_apply (f := comap _), ← comap_comp, ← Pair.Hom.toRingHom_comp, hcomp,
        Pair.Hom.toRingHom_id, ValuationSpectrum.comap_id, id]
    rw [← hid]
    exact comap_mem_spa τ_inv.continuous_toRingHom τ_inv.map_mem_plus hv_spa

end TauCeti.Huber
