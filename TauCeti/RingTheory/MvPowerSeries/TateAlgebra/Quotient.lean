/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.OpenMapping
public import TauCeti.Analysis.Normed.Group.Quotient
public import TauCeti.Analysis.Normed.Ring.Quotient.Isometry
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Quotient maps, bounded lifts, and isometric quotients of restricted power series

Let `φ : R →+* S` be a bounded ring homomorphism between ultrametric normed rings and `c : σ → ℝ`
a positive polyradius. Neither completeness nor finiteness of `σ` is needed. Three successively
stronger lifting hypotheses on `φ` control the topological and metric behaviour of
`restrictedMap φ hφ : R{X/c} →+* S{X/c}`:

1. **Uniformly bounded lifts** (`∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖`): `restrictedMap φ hφ` lifts
   series with the same Gauss-norm bound `L` (`exists_restrictedMap_eq_and_norm_le`), is an open
   quotient map (`isOpenQuotientMap_restrictedMap`), and induces a bi-Lipschitz first-isomorphism
   equivalence `R{X/c} ⧸ ker ≃+* S{X/c}`
   (`lipschitzWith_quotientKerEquivOfSurjective_restrictedMap_symm`).
2. **Sharp approximate lifts** (`∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖ + ε`): every restricted
   series `g` over `S` lifts to a restricted series over `R` of Gauss norm strictly below `‖g‖ + ε`
   (`exists_restrictedMap_eq_and_norm_lt_add`), and `restrictedMap φ hφ` is an open quotient map
   (`isOpenQuotientMap_restrictedMap_of_forall_pos_exists_norm_le_add`). Together with contractivity
   of `φ`, this hypothesis is both necessary and sufficient for the quotient Gauss norm on
   `R{X/c} ⧸ ker` to agree with the Gauss norm on `S{X/c}` (`isometry_kerLift_restrictedMap_iff`,
   `isometry_quotientKerEquivOfSurjective_restrictedMap_iff`). In particular, reducing modulo any
   closed two-sided ideal `I` of `R` induces an isometric ring isomorphism
   `R{X/c} ⧸ ker ≃+* (R ⧸ I){X/c}` (`Ideal.isometry_quotientKerEquivOfSurjective_restrictedMap_mk`).
3. **Exact norm-attaining lifts** (`∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖` with contractive `φ`): every
   restricted series over `S` lifts to one over `R` of the exact same Gauss norm
   (`exists_restrictedMap_eq_and_norm_eq`).

## Main results

* `TauCeti.MvPowerSeries.isOpenQuotientMap_restrictedMap` and
  `TauCeti.MvPowerSeries.isOpenQuotientMap_restrictedMap_of_forall_pos_exists_norm_le_add`:
  uniformly bounded or sharp approximate coefficient lifts give an open quotient map on restricted
  series.
* `TauCeti.MvPowerSeries.exists_restrictedMap_eq_and_norm_lt_add` and
  `TauCeti.MvPowerSeries.exists_restrictedMap_eq_and_norm_eq`: sharp approximate and exact
  Gauss-norm lifts.
* `TauCeti.MvPowerSeries.isometry_kerLift_restrictedMap_iff` and
  `TauCeti.MvPowerSeries.isometry_quotientKerEquivOfSurjective_restrictedMap_iff`: necessary and
  sufficient conditions for the quotient Gauss norm to match the target Gauss norm.
* `Ideal.isometry_quotientKerEquivOfSurjective_restrictedMap_mk`: isometric quotient theorem for
  closed two-sided ideals.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.1.1 and 5.2.7.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section QuotientMap

variable {σ R S : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedRing S] [IsUltrametricDist S] {c : σ → ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖) [∀ i, Fact (0 < c i)]

/-- A bound on coefficient lifts is also a bound on lifts for the Gauss norm. -/
theorem exists_restrictedMap_eq_and_norm_le {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖)
    (g : IsRestricted.subring (R := S) c) :
    ∃ f, restrictedMap φ hφ f = g ∧ ‖f‖ ≤ L * ‖g‖ := by
  obtain ⟨f, hf, hcoeff⟩ := exists_restrictedMap_eq_and_norm_coeff_le φ hφ hlift g
  exact ⟨f, hf, norm_le_mul_of_norm_coeff_le hcoeff⟩

/-- Uniformly bounded coefficient lifts make the induced map of restricted series open. -/
theorem isOpenMap_restrictedMap {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    IsOpenMap (restrictedMap (c := c) φ hφ) :=
  isOpenMap_of_exists_norm_le _ (exists_restrictedMap_eq_and_norm_le φ hφ hlift)

/-- A bounded coefficient homomorphism with uniformly bounded lifts induces an open quotient map
for the Gauss norm topologies at arbitrary positive polyradii. -/
theorem isOpenQuotientMap_restrictedMap {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    IsOpenQuotientMap (restrictedMap (c := c) φ hφ) :=
  isOpenQuotientMap_of_exists_norm_le (continuous_restrictedMap φ hφ)
    (exists_restrictedMap_eq_and_norm_le φ hφ hlift)

/-- A bounded coefficient homomorphism with uniformly bounded lifts induces a quotient map
for the Gauss norm topologies at arbitrary positive polyradii. -/
theorem isQuotientMap_restrictedMap {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    Topology.IsQuotientMap (restrictedMap (c := c) φ hφ) :=
  (isOpenQuotientMap_restrictedMap φ hφ hlift).isQuotientMap

/-- Uniformly `L`-bounded coefficient lifts make the inverse of the first-isomorphism equivalence
`R{X/c} ⧸ ker ≃+* S{X/c}` Lipschitz with constant `L`. -/
theorem lipschitzWith_quotientKerEquivOfSurjective_restrictedMap_symm {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    LipschitzWith (Real.toNNReal L)
      ((restrictedMap (c := c) φ hφ).quotientKerEquivOfSurjective
        (restrictedMap_surjective φ hφ hlift)).symm :=
  (restrictedMap (c := c) φ hφ).lipschitzWith_quotientKerEquivOfSurjective_symm
    (restrictedMap_surjective φ hφ hlift) (exists_restrictedMap_eq_and_norm_le φ hφ hlift)

end QuotientMap

section IsometricQuotient

variable {σ R S : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedRing S] [IsUltrametricDist S] {c : σ → ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖) [∀ i, Fact (0 < c i)]

/-- If every image `φ a` lifts to elements of `R` of norm arbitrarily close to `‖φ a‖`, then every
image `restrictedMap φ hφ f` lifts to a restricted series of Gauss norm strictly below
`‖restrictedMap φ hφ f‖ + ε`. -/
theorem exists_restrictedMap_eq_restrictedMap_and_norm_lt_add
    (hlift : ∀ a, ∀ ε > 0, ∃ a', φ a' = φ a ∧ ‖a'‖ ≤ ‖φ a‖ + ε)
    (f : IsRestricted.subring (R := R) c) {ε : ℝ} (hε : 0 < ε) :
    ∃ f', restrictedMap φ hφ f' = restrictedMap φ hφ f ∧
      ‖f'‖ < ‖restrictedMap φ hφ f‖ + ε := by
  set g := restrictedMap φ hφ f
  -- At each nonzero coefficient `gₜ`, choosing the monomial-dependent tolerance
  -- `δ = min ‖gₜ‖ (ε / (2 * cᵗ))` keeps `f'` restricted via `‖a'ₜ‖ ≤ 2 * ‖gₜ‖` while bounding
  -- every weighted coefficient by `‖g‖ + ε / 2`.
  have hchoice (t : σ →₀ ℕ) : ∃ a' : R, φ a' = coeff t (g : MvPowerSeries σ S) ∧
      ‖a'‖ ≤ 2 * ‖coeff t (g : MvPowerSeries σ S)‖ ∧
      ‖a'‖ * t.prod (c · ^ ·) ≤ ‖coeff t (g : MvPowerSeries σ S)‖ * t.prod (c · ^ ·) + ε / 2 := by
    by_cases ht : coeff t (g : MvPowerSeries σ S) = 0
    · exact ⟨0, by simp [ht], by simp, by rw [ht]; simp only [norm_zero, zero_mul]; positivity⟩
    · have hw : 0 < t.prod (c · ^ ·) := prod_pow_pos t
      have hgt : 0 < ‖coeff t (g : MvPowerSeries σ S)‖ := norm_pos_iff.mpr ht
      set δ := min ‖coeff t (g : MvPowerSeries σ S)‖ (ε / 2 / t.prod (c · ^ ·))
      have hδ : 0 < δ := lt_min hgt (div_pos (half_pos hε) hw)
      have heq : coeff t (g : MvPowerSeries σ S) = φ (coeff t (f : MvPowerSeries σ R)) :=
        coeff_restrictedMap φ hφ f t
      obtain ⟨a', ha'φ, ha'n⟩ := hlift (coeff t (f : MvPowerSeries σ R)) δ hδ
      rw [← heq] at ha'φ ha'n
      refine ⟨a', ha'φ, ?_, ?_⟩
      · linarith [min_le_left ‖coeff t (g : MvPowerSeries σ S)‖ (ε / 2 / t.prod (c · ^ ·))]
      · have hδw : δ * t.prod (c · ^ ·) ≤ ε / 2 := by
          calc δ * t.prod (c · ^ ·) ≤ (ε / 2 / t.prod (c · ^ ·)) * t.prod (c · ^ ·) :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hw.le
            _ = ε / 2 := div_mul_cancel₀ _ hw.ne'
        calc ‖a'‖ * t.prod (c · ^ ·) ≤ (‖coeff t (g : MvPowerSeries σ S)‖ + δ) * t.prod (c · ^ ·) :=
              mul_le_mul_of_nonneg_right ha'n hw.le
          _ = ‖coeff t (g : MvPowerSeries σ S)‖ * t.prod (c · ^ ·) + δ * t.prod (c · ^ ·) :=
              add_mul _ _ _
          _ ≤ ‖coeff t (g : MvPowerSeries σ S)‖ * t.prod (c · ^ ·) + ε / 2 := by linarith
  choose a' ha'φ ha'2 ha'ε using hchoice
  let f' : MvPowerSeries σ R := fun t ↦ a' t
  have hf' : IsRestricted c f' := isRestricted_of_norm_coeff_le g.2 ha'2
  refine ⟨⟨f', hf'⟩, Subtype.ext <| MvPowerSeries.ext fun t ↦ ?_, ?_⟩
  · rw [coeff_restrictedMap]
    exact ha'φ t
  · have hle : ‖(⟨f', hf'⟩ : IsRestricted.subring (R := R) c)‖ ≤ ‖g‖ + ε / 2 := by
      rw [norm_le_iff]
      intro t
      have ht : coeff t (f' : MvPowerSeries σ R) = a' t := coeff_apply _ t
      linarith [ht ▸ ha'ε t, norm_coeff_mul_prod_le g t]
    linarith [half_lt_self hε]

omit [∀ i, Fact (0 < c i)] in
/-- Sharp approximate coefficient lifts make `restrictedMap` surjective at every polyradius. -/
theorem restrictedMap_surjective_of_forall_pos_exists_norm_le_add
    (hlift : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖ + ε) :
    Function.Surjective (restrictedMap (c := c) φ hφ) :=
  restrictedMap_surjective φ hφ (exists_norm_le_two_mul_of_forall_pos_exists_norm_le_add hlift)

/-- Sharp approximate coefficient lifts make `restrictedMap` an open quotient map for the Gauss
norm topologies at arbitrary positive polyradii. -/
theorem isOpenQuotientMap_restrictedMap_of_forall_pos_exists_norm_le_add
    (hlift : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖ + ε) :
    IsOpenQuotientMap (restrictedMap (c := c) φ hφ) :=
  isOpenQuotientMap_restrictedMap φ hφ
    (exists_norm_le_two_mul_of_forall_pos_exists_norm_le_add hlift)

/-- **Sharp approximate Gauss-norm lifts.** If every `b : S` lifts along `φ` to elements of norm
at most `‖b‖ + ε` for every `ε > 0`, then every restricted series `g` over `S` lifts to a
restricted series over `R` of Gauss norm strictly below `‖g‖ + ε`. -/
theorem exists_restrictedMap_eq_and_norm_lt_add
    (hlift : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖ + ε)
    (g : IsRestricted.subring (R := S) c) {ε : ℝ} (hε : 0 < ε) :
    ∃ f, restrictedMap φ hφ f = g ∧ ‖f‖ < ‖g‖ + ε := by
  obtain ⟨f₀, rfl⟩ := restrictedMap_surjective_of_forall_pos_exists_norm_le_add φ hφ hlift g
  exact exists_restrictedMap_eq_restrictedMap_and_norm_lt_add φ hφ
    (fun a δ hδ ↦ hlift (φ a) δ hδ) f₀ hε

/-- Non-strict form of `exists_restrictedMap_eq_and_norm_lt_add`. -/
theorem exists_restrictedMap_eq_and_norm_le_add
    (hlift : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖ + ε)
    (g : IsRestricted.subring (R := S) c) {ε : ℝ} (hε : 0 < ε) :
    ∃ f, restrictedMap φ hφ f = g ∧ ‖f‖ ≤ ‖g‖ + ε :=
  let ⟨f, hf, hlt⟩ := exists_restrictedMap_eq_and_norm_lt_add φ hφ hlift g hε
  ⟨f, hf, hlt.le⟩

/-- **Exact Gauss-norm-attaining lifts.** If `φ` is contractive and every `b : S` admits a lift of
norm at most `‖b‖`, then every restricted series over `S` admits a restricted lift of the exact
same Gauss norm. -/
theorem exists_restrictedMap_eq_and_norm_eq (hφ1 : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖) (g : IsRestricted.subring (R := S) c) :
    ∃ f, restrictedMap φ hφ f = g ∧ ‖f‖ = ‖g‖ := by
  obtain ⟨f, rfl, hfle⟩ := exists_restrictedMap_eq_and_norm_le φ hφ (L := 1)
    (fun b ↦ by simpa only [one_mul] using hlift b) g
  exact ⟨f, rfl, le_antisymm (by simpa only [one_mul] using hfle)
    (norm_restrictedMap_le_of_norm_le φ hφ hφ1 f)⟩

/-- **Necessary and sufficient criterion for `restrictedMap.kerLift` to be an isometry.** At any
positive polyradius `c`, the quotient Gauss norm on `R{X/c} ⧸ ker (restrictedMap φ hφ)` agrees with
the Gauss norm on images in `S{X/c}` if and only if the same holds on constants, i.e. `φ.kerLift`
is an isometry. -/
theorem isometry_kerLift_restrictedMap_iff :
    Isometry (restrictedMap (c := c) φ hφ).kerLift ↔ Isometry φ.kerLift := by
  rw [(restrictedMap (c := c) φ hφ).isometry_kerLift_iff, φ.isometry_kerLift_iff]
  constructor
  · rintro ⟨h1, h2⟩
    let f₀ (a : R) : IsRestricted.subring (R := R) c :=
      ⟨_root_.MvPowerSeries.C a, isRestricted_C c a⟩
    have hf₀ (a : R) :
        restrictedMap φ hφ (f₀ a) = ⟨_root_.MvPowerSeries.C (φ a), isRestricted_C c (φ a)⟩ :=
      Subtype.ext (by simp [f₀, coe_restrictedMap])
    refine ⟨fun a ↦ by simpa only [f₀, hf₀ a, norm_C] using h1 (f₀ a), fun a ε hε ↦ ?_⟩
    obtain ⟨f', hf'eq, hf'lt⟩ := h2 (f₀ a) ε hε
    refine ⟨constantCoeff (f' : MvPowerSeries σ R), ?_,
      (norm_constantCoeff_le f').trans_lt (by simpa only [hf₀ a, norm_C] using hf'lt)⟩
    have h0 := congrArg (fun g : IsRestricted.subring (R := S) c ↦
      coeff 0 (g : MvPowerSeries σ S)) (hf'eq.trans (hf₀ a))
    simpa only [coeff_restrictedMap, coeff_zero_eq_constantCoeff_apply, constantCoeff_C] using h0
  · rintro ⟨h1, h2⟩
    exact ⟨norm_restrictedMap_le_of_norm_le φ hφ h1,
      fun f ε hε ↦ exists_restrictedMap_eq_restrictedMap_and_norm_lt_add φ hφ
        (fun a δ hδ ↦ let ⟨a', ha', hlt⟩ := h2 a δ hδ; ⟨a', ha', hlt.le⟩) f hε⟩

/-- **Quotient-norm equality for `restrictedMap`.** The quotient Gauss norm modulo
`ker (restrictedMap φ hφ)` equals `‖restrictedMap φ hφ ·‖` everywhere if and only if `φ` is
contractive and every image `φ a` lifts to elements of `R` of norm arbitrarily close to `‖φ a‖`. -/
theorem norm_mk_ker_restrictedMap_eq_iff :
    (∀ f, ‖Ideal.Quotient.mk (RingHom.ker (restrictedMap (c := c) φ hφ)) f‖ =
      ‖restrictedMap φ hφ f‖) ↔
      (∀ a, ‖φ a‖ ≤ ‖a‖) ∧ ∀ a, ∀ ε > 0, ∃ a', φ a' = φ a ∧ ‖a'‖ < ‖φ a‖ + ε := by
  rw [(restrictedMap (c := c) φ hφ).norm_mk_ker_eq_iff,
    ← (restrictedMap (c := c) φ hφ).isometry_kerLift_iff,
    isometry_kerLift_restrictedMap_iff (c := c) φ hφ, φ.isometry_kerLift_iff]

/-- **Isometric quotient characterisation for restricted power series.** When `restrictedMap φ hφ`
is surjective, its first-isomorphism equivalence `R{X/c} ⧸ ker ≃+* S{X/c}` is an isometry if and
only if `φ` is contractive and every `b : S` admits preimages of norm arbitrarily close to `‖b‖`.
Mere algebraic surjectivity, or even uniformly `L`-bounded lifting with `L > 1`, is insufficient. -/
theorem isometry_quotientKerEquivOfSurjective_restrictedMap_iff
    (hsurj : Function.Surjective (restrictedMap (c := c) φ hφ)) :
    Isometry ((restrictedMap (c := c) φ hφ).quotientKerEquivOfSurjective hsurj) ↔
      (∀ a, ‖φ a‖ ≤ ‖a‖) ∧ ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ < ‖b‖ + ε := by
  rw [(restrictedMap (c := c) φ hφ).isometry_quotientKerEquivOfSurjective_iff hsurj,
    hsurj.forall, ← (restrictedMap (c := c) φ hφ).isometry_kerLift_iff,
    isometry_kerLift_restrictedMap_iff (c := c) φ hφ, φ.isometry_kerLift_iff,
    (surjective_of_restrictedMap_surjective φ hφ hsurj).forall]

/-- A contractive coefficient homomorphism with sharp approximate preimages induces an isometric
first-isomorphism equivalence `R{X/c} ⧸ ker ≃+* S{X/c}` at every positive polyradius. -/
theorem isometry_quotientKerEquivOfSurjective_restrictedMap (hφ1 : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (hlift : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖ + ε) :
    Isometry ((restrictedMap (c := c) φ hφ).quotientKerEquivOfSurjective
      (restrictedMap_surjective_of_forall_pos_exists_norm_le_add φ hφ hlift)) :=
  RingHom.isometry_quotientKerEquivOfSurjective_of_forall_pos_exists_norm_le_add
    _ (norm_restrictedMap_le_of_norm_le φ hφ hφ1)
    (fun g _ hε ↦ exists_restrictedMap_eq_and_norm_le_add φ hφ hlift g hε)

end IsometricQuotient

end TauCeti.MvPowerSeries

namespace Ideal

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {σ R : Type*} [NormedRing R] [IsUltrametricDist R]
  (I : Ideal R) [I.IsTwoSided] [IsClosed (I : Set R)]
  {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- Reducing coefficients modulo a closed two-sided ideal `I` admits sharp approximate Gauss-norm
lifts at every positive polyradius. -/
theorem exists_restrictedMap_mk_eq_and_norm_lt_add (g : IsRestricted.subring (R := R ⧸ I) c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : IsRestricted.subring (R := R) c,
      restrictedMap (Quotient.mk I)
        (fun a ↦ (one_mul ‖a‖).symm ▸ Quotient.norm_mk_le_norm I a) f = g ∧
      ‖f‖ < ‖g‖ + ε :=
  exists_restrictedMap_eq_and_norm_lt_add (Quotient.mk I) _
    (fun x _ hδ ↦ let ⟨a, ha, hlt⟩ := Quotient.exists_norm_mk_lt x hδ; ⟨a, ha, hlt.le⟩) g hε

/-- Reducing coefficients modulo a closed two-sided ideal `I` induces an open quotient map
`R{X/c} → (R ⧸ I){X/c}` for the Gauss norm topologies. -/
theorem isOpenQuotientMap_restrictedMap_mk :
    IsOpenQuotientMap (restrictedMap (c := c) (Quotient.mk I)
      (fun a : R ↦ (one_mul ‖a‖).symm ▸ Quotient.norm_mk_le_norm I a)) :=
  isOpenQuotientMap_restrictedMap_of_forall_pos_exists_norm_le_add (Quotient.mk I) _
    fun x _ hδ ↦ let ⟨a, ha, hlt⟩ := Quotient.exists_norm_mk_lt x hδ; ⟨a, ha, hlt.le⟩

/-- **Isometric quotient theorem for closed two-sided ideals.** For any closed two-sided ideal `I`
of an ultrametric normed ring `R` and any positive polyradius `c`, the first-isomorphism
equivalence `R{X/c} ⧸ ker ≃+* (R ⧸ I){X/c}` induced by reducing coefficients modulo `I` is an
isometry for the quotient Gauss norm and the Gauss norm over `R ⧸ I`. -/
theorem isometry_quotientKerEquivOfSurjective_restrictedMap_mk :
    Isometry (RingHom.quotientKerEquivOfSurjective
      (f := restrictedMap (c := c) (Quotient.mk I)
        (fun a : R ↦ (one_mul ‖a‖).symm ▸ Quotient.norm_mk_le_norm I a))
      (isOpenQuotientMap_restrictedMap_mk I).surjective) :=
  (isometry_quotientKerEquivOfSurjective_restrictedMap_iff (Quotient.mk I) _
    (isOpenQuotientMap_restrictedMap_mk I).surjective).mpr
    ⟨Quotient.norm_mk_le_norm I, fun x _ hε ↦ Quotient.exists_norm_mk_lt x hε⟩

end Ideal
