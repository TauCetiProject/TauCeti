/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.StrongSite.Basic
public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Subdomain
public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.SupSeminorm

import Mathlib.RingTheory.AdjoinRoot
import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Algebraic.Basic
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval

/-!
# Strict sublevel opens and the unit-disc checks for the strong affinoid G-topology

For any element `f` of an affinoid `K`-algebra `A`, the strict sublevel locus
`{x ∈ Sp A : |f(x)| < 1}` is strong-admissible: for `0 < ‖ϖ‖ < 1`, it is exhausted by the rational
subdomains `R(fⁿ / ϖ) = {|f|ⁿ ≤ ‖ϖ‖}` (`n ≥ 1`), and the maximum modulus principle refines every
affinoid test map into `{|f| < 1}` through a single stage. Specialising to `K⟨X⟩` gives the two
checks of [BGR, §§9.1.2, 9.1.4]: `{|X| < 1}` is strong-admissible, whereas `{openUnitDisc,
unitCircle}` covers `Sp K⟨X⟩` set-theoretically without being strong-admissible.

## Main definitions

* `TauCeti.StrongAdmissibleOpen.ltOne`: the strict sublevel open `{x ∈ Sp A : |f(x)| < 1}`.
* `TauCeti.MvPowerSeries.openUnitDisc`, `TauCeti.MvPowerSeries.closedSubdisc`,
  `TauCeti.MvPowerSeries.unitCircle`: the open unit disc, closed subdiscs, and unit circle.

## Main results

* `TauCeti.StrongAdmissibleOpen.covers_ltOne_closedSublevelPow` and
  `TauCeti.MvPowerSeries.covers_openUnitDisc_closedSubdisc`: strong exhaustion by `{|f|ⁿ ≤ ‖ϖ‖}`.
* `TauCeti.MvPowerSeries.exists_pointNorm_X_pow_eq_norm`,
  `TauCeti.MvPowerSeries.openUnitDisc_union_unitCircle`, and
  `TauCeti.MvPowerSeries.not_covers_openUnitDisc_unitCircle`: set cover vs. non-admissibility.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§9.1.2 and 9.1.4.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries TauCeti.MvPowerSeries Polynomial

universe u

section Sublevel

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- For any `0 < ‖ϖ‖ < 1`, the strict sublevel locus `{|f| < 1}` is the union over `n ≥ 1` of the
closed sublevel sets `{|f|ⁿ ≤ ‖ϖ‖}`. -/
theorem ltOne_eq_biUnion_closedSublevelPow (f : A) {ϖ : K} (hϖ₀ : 0 < ‖ϖ‖) (hϖ₁ : ‖ϖ‖ < 1) :
    {x : MaximalSpectrum A | pointNorm K x f < 1} =
      ⋃ n ∈ {n : ℕ | 1 ≤ n}, {x : MaximalSpectrum A | pointNorm K x f ^ n ≤ ‖ϖ‖} := by
  ext x; simp only [Set.mem_iUnion, Set.mem_ofPred]
  refine ⟨fun hx ↦ ?_, fun ⟨n, _, hxn⟩ ↦
    lt_of_pow_lt_pow_left₀ n zero_le_one (by simpa using hxn.trans_lt hϖ₁)⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hϖ₀ hx
  exact ⟨m + 1, Nat.succ_pos m,
    (pow_le_pow_of_le_one (pointNorm_nonneg f) hx.le (Nat.le_succ m)).trans hm.le⟩

/-- For any `0 < ‖ϖ‖`, the family of closed sublevel sets `{|f|ⁿ ≤ ‖ϖ‖}` (`n ≥ 1`) is affinoid-test
refined on `{|f| < 1}`. -/
theorem isAffinoidTestRefined_ltOne (f : A) {ϖ : K} (hϖ₀ : 0 < ‖ϖ‖) :
    IsAffinoidTestRefined K {x : MaximalSpectrum A | pointNorm K x f < 1}
      ((fun n : ℕ ↦ {x : MaximalSpectrum A | pointNorm K x f ^ n ≤ ‖ϖ‖}) '' {n : ℕ | 1 ≤ n}) := by
  rw [isAffinoidTestRefined_iff]
  intro B _ _ hB φ hφ
  have hsup : supSeminorm K (φ f) < 1 := (hB.supSeminorm_lt_iff zero_lt_one).mpr fun y ↦ by
    rw [← hB.pointNorm_maximalSpectrumComap φ y f]; exact hφ ⟨y, rfl⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hϖ₀ hsup
  have hle : supSeminorm K (φ f) ^ (m + 1) ≤ ‖ϖ‖ :=
    (pow_le_pow_of_le_one (supSeminorm_nonneg _) hsup.le (Nat.le_succ m)).trans hm.le
  refine ⟨{AffinoidSubdomain.univ hB}, Set.finite_singleton _, by simp, ?_⟩
  rintro W hW; obtain rfl := Set.mem_singleton_iff.mp hW
  refine ⟨{x | pointNorm K x f ^ (m + 1) ≤ ‖ϖ‖}, ⟨m + 1, Nat.succ_pos m, rfl⟩, fun y _ ↦ ?_⟩
  rw [Set.mem_preimage, Set.mem_ofPred, hB.pointNorm_maximalSpectrumComap]
  exact (pow_le_pow_left₀ (pointNorm_nonneg _) (hB.pointNorm_le_supSeminorm y (φ f)) _).trans hle

namespace StrongAdmissibleOpen

/-- The strict sublevel locus `{x ∈ Sp A : |f(x)| < 1}` as a strong-admissible open of `Sp A`. -/
noncomputable def ltOne (hA : IsAffinoidAlgebra K A) (f : A) : StrongAdmissibleOpen K A :=
  let hϖ := NormedField.exists_norm_lt_one K
  have hϖ₀ : 0 < ‖hϖ.choose‖ := hϖ.choose_spec.1
  ⟨{x | pointNorm K x f < 1},
    AffinoidSubdomain.closedSublevelPow hA f (norm_pos_iff.mp hϖ₀) '' {n : ℕ | 1 ≤ n},
    by simp only [Set.image_image, AffinoidSubdomain.coe_closedSublevelPow, Set.sUnion_image]
       exact (ltOne_eq_biUnion_closedSublevelPow f hϖ₀ hϖ.choose_spec.2).symm,
    by simp only [Set.image_image, AffinoidSubdomain.coe_closedSublevelPow]
       exact isAffinoidTestRefined_ltOne f hϖ₀⟩

@[simp]
theorem coe_ltOne (hA : IsAffinoidAlgebra K A) (f : A) :
    (ltOne hA f : Set (MaximalSpectrum A)) = {x | pointNorm K x f < 1} := (rfl)

@[simp]
theorem mem_ltOne (hA : IsAffinoidAlgebra K A) (f : A) (x : MaximalSpectrum A) :
    x ∈ ltOne hA f ↔ pointNorm K x f < 1 := Iff.rfl

/-- For any `0 < ‖ϖ‖ < 1`, the rational subdomains `{|f|ⁿ ≤ ‖ϖ‖}` (`n ≥ 1`) form a
strong-admissible cover of `{|f| < 1}`. -/
theorem covers_ltOne_closedSublevelPow [hA : Fact (IsAffinoidAlgebra K A)] (f : A) {ϖ : K}
    (hϖ₀ : 0 < ‖ϖ‖) (hϖ₁ : ‖ϖ‖ < 1) :
    (strongGTopology (K := K) (A := A)).Covers (ltOne hA.out f)
      ((fun n : ℕ ↦
        (AffinoidSubdomain.closedSublevelPow hA.out f
          (norm_pos_iff.mp hϖ₀) n).toStrongAdmissibleOpen) ''
        {n : ℕ | 1 ≤ n}) := by
  rw [strongGTopology_covers_iff]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨n, _, rfl⟩ x hx
    rw [← SetLike.mem_coe, AffinoidSubdomain.coe_toStrongAdmissibleOpen,
      AffinoidSubdomain.coe_closedSublevelPow, Set.mem_ofPred] at hx
    have hpow : pointNorm K x f ^ n < 1 ^ n := by simpa using hx.trans_lt hϖ₁
    exact lt_of_pow_lt_pow_left₀ n zero_le_one hpow
  · simp only [Set.image_image, AffinoidSubdomain.coe_toStrongAdmissibleOpen,
      AffinoidSubdomain.coe_closedSublevelPow, coe_ltOne]
    exact isAffinoidTestRefined_ltOne f hϖ₀

end StrongAdmissibleOpen

end Sublevel

namespace MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "T₁" => IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1)

/-- The coordinate variable `X₀` of the one-variable Tate algebra `K⟨X⟩`. -/
noncomputable def unitDiscCoord : T₁ := ⟨X 0, isRestricted_X _ 0⟩

/-- The open unit disc `{x ∈ Sp K⟨X⟩ : |X(x)| < 1}` as a strong-admissible open of `Sp K⟨X⟩`. -/
noncomputable def openUnitDisc : StrongAdmissibleOpen K T₁ :=
  StrongAdmissibleOpen.ltOne isAffinoidAlgebra_tate unitDiscCoord

@[simp]
theorem coe_openUnitDisc :
    (openUnitDisc (K := K) : Set (MaximalSpectrum T₁)) =
      {x | pointNorm K x unitDiscCoord < 1} := (rfl)

/-- The closed subdisc `{x ∈ Sp K⟨X⟩ : |X(x)|ⁿ ≤ ‖ϖ‖}` (`ϖ ≠ 0`) as a rational affinoid subdomain
of `Sp K⟨X⟩`. -/
noncomputable def closedSubdisc {ϖ : K} (hϖ : ϖ ≠ 0) (n : ℕ) : AffinoidSubdomain K T₁ :=
  AffinoidSubdomain.closedSublevelPow isAffinoidAlgebra_tate unitDiscCoord hϖ n

@[simp]
theorem coe_closedSubdisc {ϖ : K} (hϖ : ϖ ≠ 0) (n : ℕ) :
    (closedSubdisc hϖ n : Set (MaximalSpectrum T₁)) =
      {x | pointNorm K x unitDiscCoord ^ n ≤ ‖ϖ‖} :=
  AffinoidSubdomain.coe_closedSublevelPow _ _ hϖ n

/-- The unit circle `{x ∈ Sp K⟨X⟩ : |X(x)| = 1}` as a Laurent affinoid subdomain of `Sp K⟨X⟩`. -/
noncomputable def unitCircle : AffinoidSubdomain K T₁ :=
  AffinoidSubdomain.eqOne isAffinoidAlgebra_tate unitDiscCoord

@[simp]
theorem coe_unitCircle :
    (unitCircle (K := K) : Set (MaximalSpectrum T₁)) =
      {x | pointNorm K x unitDiscCoord = 1} :=
  AffinoidSubdomain.coe_eqOne _ _

/-- For any `0 < ‖ϖ‖ < 1`, the closed subdiscs `{|X|ⁿ ≤ ‖ϖ‖}` (`n ≥ 1`) form a strong-admissible
cover of the open unit disc in `Sp K⟨X⟩` [BGR, §9.1.4]. -/
theorem covers_openUnitDisc_closedSubdisc {ϖ : K} (hϖ₀ : 0 < ‖ϖ‖) (hϖ₁ : ‖ϖ‖ < 1) :
    (StrongAdmissibleOpen.strongGTopology (K := K) (A := T₁)).Covers openUnitDisc
      ((fun n : ℕ ↦ (closedSubdisc (norm_pos_iff.mp hϖ₀) n).toStrongAdmissibleOpen) ''
        {n : ℕ | 1 ≤ n}) :=
  StrongAdmissibleOpen.covers_ltOne_closedSublevelPow unitDiscCoord hϖ₀ hϖ₁

/-- Every classical point of `Sp K⟨X⟩` satisfies `|X(x)| ≤ 1`. -/
theorem pointNorm_unitDiscCoord_le_one (x : MaximalSpectrum T₁) :
    pointNorm K x unitDiscCoord ≤ 1 :=
  (isAffinoidAlgebra_tate.pointNorm_le_supSeminorm x unitDiscCoord).trans
    (isAffinoidAlgebra_tate.isPowerBounded_iff_supSeminorm_le_one.mp (isPowerBounded_X 0))

/-- The open unit disc and the unit circle are disjoint in `Sp K⟨X⟩`. -/
theorem disjoint_openUnitDisc_unitCircle :
    Disjoint (openUnitDisc (K := K) : Set (MaximalSpectrum T₁))
      (unitCircle (K := K) : Set (MaximalSpectrum T₁)) :=
  Set.disjoint_left.mpr fun _ hxlt hxeq ↦ by
    rw [coe_openUnitDisc] at hxlt; rw [coe_unitCircle] at hxeq; exact hxlt.ne hxeq

/-- The open unit disc and the unit circle cover `Sp K⟨X⟩` set-theoretically. -/
theorem openUnitDisc_union_unitCircle :
    (openUnitDisc (K := K) : Set (MaximalSpectrum T₁)) ∪
      (unitCircle (K := K) : Set (MaximalSpectrum T₁)) = Set.univ := by
  ext x; simp [lt_or_eq_of_le (pointNorm_unitDiscCoord_le_one x)]

/-- For any `ϖ : K` with `‖ϖ‖ ≤ 1` and `n ≥ 1`, the closed unit disc `Sp K⟨X⟩` contains a classical
point `x` at which `|X(x)|ⁿ = ‖ϖ‖`. -/
theorem exists_pointNorm_X_pow_eq_norm {ϖ : K} (hϖ : ‖ϖ‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : MaximalSpectrum T₁, pointNorm K x unitDiscCoord ^ n = ‖ϖ‖ := by
  let g : K[X] := Polynomial.X ^ n - Polynomial.C ϖ
  have hg : g.Monic := Polynomial.monic_X_pow_sub_C ϖ (by omega)
  have : Module.Finite K (AdjoinRoot g) := hg.finite_adjoinRoot
  have : Nontrivial (AdjoinRoot g) := by
    rw [AdjoinRoot.nontrivial_iff_of_monic hg, Polynomial.degree_X_pow_sub_C (by omega)]
    exact Nat.cast_pos.mpr hn
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (AdjoinRoot g)
  let L := AdjoinRoot g ⧸ m
  let _ : Field L := Ideal.Quotient.field m
  have : FiniteDimensional K L :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  let _ : NormedField L := spectralNorm.normedField K L
  let _ : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  have : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun a b ↦
      isNonarchimedean_spectralNorm (K := K) (L := L) a b
  have : CompleteSpace L := FiniteDimensional.completeSpace K L
  have hφ (r : K) : ‖algebraMap K L r‖ = ‖r‖ := norm_algebraMap' L r
  let α : L := Ideal.Quotient.mk m (AdjoinRoot.root g)
  have hαn : α ^ n = algebraMap K L ϖ := sub_eq_zero.mp <| by
    simpa [g, α, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_eq K (AdjoinRoot g) L]
      using congrArg (Ideal.Quotient.mk m) (AdjoinRoot.eval₂_root g)
  have hαnorm : ‖α‖ ^ n = ‖ϖ‖ := by rw [← norm_pow, hαn, hφ]
  have hαle : ∀ _ : Fin 1, ‖α‖ ≤ 1 := fun _ ↦
    le_of_pow_le_pow_left₀ (by omega : n ≠ 0) zero_le_one (by simpa [hαnorm] using hϖ)
  let ψ : T₁ →ₐ[K] L :=
    { _root_.MvPowerSeries.restrictedEval₂ (algebraMap K L) (fun _ ↦ α) (fun r ↦ (hφ r).le) hαle
      with commutes' := _root_.MvPowerSeries.restrictedEval₂_algebraMap _ _ _ _ }
  refine ⟨⟨RingHom.ker ψ, ψ.ker_isMaximal_of_isAlgebraic⟩, ?_⟩
  rw [pointNorm_eq_spectralNorm (ψ := ψ) le_rfl, ← NormedAlgebra.norm_eq_spectralNorm K]
  exact (congrArg (fun a ↦ ‖a‖ ^ n)
    (_root_.MvPowerSeries.restrictedEval₂_X (algebraMap K L) (fun _ ↦ α) _ hαle 0)).trans hαnorm

private theorem exists_lt_one_forall_pointNorm_le (R' : Finset (AffinoidSubdomain K T₁))
    (hR' : ∀ W ∈ R', (W : Set (MaximalSpectrum T₁)) ⊆ (openUnitDisc (K := K) : Set _)) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ W ∈ R', ∀ x ∈ W, pointNorm K x unitDiscCoord ≤ r := by
  classical
  let S : Finset ℝ := R'.image (fun W ↦ supSeminorm K (W.toSections unitDiscCoord)) ∪ {0}
  have hS : S.Nonempty := by simp [S]
  refine ⟨S.max' hS, Finset.le_max' S 0 (by simp [S]), (Finset.max'_lt_iff S hS).mpr ?_,
    fun W hW x hx ↦ ?_⟩
  · simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    rintro _ (⟨W, hW, rfl⟩ | rfl)
    · exact (AffinoidSubdomain.supSeminorm_toSections_lt_iff isAffinoidAlgebra_tate W
        unitDiscCoord zero_lt_one).mpr fun y hy ↦ hR' W hW hy
    · exact zero_lt_one
  · exact ((AffinoidSubdomain.supSeminorm_toSections_le_iff isAffinoidAlgebra_tate W
      unitDiscCoord (supSeminorm_nonneg _)).mp le_rfl x hx).trans
      (Finset.le_max' S _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hW)))

/-- Although `{openUnitDisc, unitCircle}` covers `Sp K⟨X⟩` as sets, it is **not** an admissible
cover in `strongGTopology` [BGR, §9.1.2]. -/
theorem not_covers_openUnitDisc_unitCircle :
    ¬ (StrongAdmissibleOpen.strongGTopology (K := K) (A := T₁)).Covers ⊤
      {openUnitDisc, unitCircle.toStrongAdmissibleOpen} := by
  classical
  intro hcov
  obtain ⟨R, hfin, hRuniv, hRref⟩ := (isAffinoidTestRefined_iff.mp
    (((StrongAdmissibleOpen.strongGTopology_covers_iff (K := K) (A := T₁)).mp hcov).2))
    isAffinoidAlgebra_tate (AlgHom.id K T₁) (by simp [StrongAdmissibleOpen.coe_top])
  obtain ⟨r, hr₀, hr₁, hr⟩ := exists_lt_one_forall_pointNorm_le
    {W ∈ hfin.toFinset | (W : Set (MaximalSpectrum T₁)) ⊆ (openUnitDisc (K := K) : Set _)}
    fun _ hW ↦ (Finset.mem_filter.mp hW).2
  obtain ⟨ϖ, hϖ₀, hϖ₁⟩ := NormedField.exists_norm_lt_one K
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hϖ₀ hr₁
  obtain ⟨x, hx⟩ := exists_pointNorm_X_pow_eq_norm hϖ₁.le (Nat.succ_pos m)
  have hxlt : pointNorm K x unitDiscCoord < 1 :=
    lt_of_pow_lt_pow_left₀ (m + 1) zero_le_one (by simpa [hx] using hϖ₁)
  obtain ⟨_, ⟨W, hWR, rfl⟩, hxW⟩ := Set.mem_sUnion.mp (hRuniv ▸ Set.mem_univ x)
  obtain ⟨V, hVmem, hWV⟩ := hRref W hWR
  rw [IsAffinoidAlgebra.maximalSpectrumComap_id, Set.preimage_id] at hWV
  have hWsub : (W : Set (MaximalSpectrum T₁)) ⊆ (openUnitDisc (K := K) : Set _) := by
    have hVeq : V = (openUnitDisc (K := K) : Set _) ∨
        V = (unitCircle (K := K) : Set _) := by
      simpa using hVmem
    rcases hVeq with rfl | rfl
    · exact hWV
    · exact False.elim (hxlt.ne (by simpa using hWV hxW))
  have hxle := hr W (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hWR, hWsub⟩) x hxW
  exact ((hx ▸ pow_le_pow_left₀ (pointNorm_nonneg _) hxle (m + 1)).trans_lt
    ((pow_le_pow_of_le_one hr₀ hr₁.le (Nat.le_succ m)).trans_lt hm)).false

end MvPowerSeries

end TauCeti
