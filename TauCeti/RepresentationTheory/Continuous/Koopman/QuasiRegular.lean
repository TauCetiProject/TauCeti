/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Coset
public import TauCeti.RepresentationTheory.Continuous.Koopman.Basic
public import TauCeti.RepresentationTheory.Continuous.SpectralGap
import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Quasi-regular, permutation, and counting-measure Koopman spectral gap

Let a group `G` act on a set `X`. Combining the Koopman $P_2$ squared-density bound with Reiter
density truncation (`TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_tsum_eq_one`), orbit
pigeonhole (`TauCeti.exists_quotient_finset_of_sum_card_smul_symmDiff_lt`), and the Mackey–Eymard
coset Følner lift (`TauCeti.exists_finset_card_smul_symmDiff_lt_of_quotient`), this file establishes
the discrete $P_2$ converse criterion from `ℓ²(X, E)` almost invariant vectors to Følner sets on
`X` together with **Anantharaman–Popa Lemma 15.1.9**: when `G` does not have Følner sets and every
non-fixed point of `X` has stabilizer with Følner sets (in particular, finite stabilizer), the
Koopman representation on `ℓ²(X, E)` — and any representation permuting a `HilbertBasis` indexed by
`X` — has spectral gap.

For the quasi-regular representation on `ℓ²(G ⧸ H, E)` with `HasFoelnerSets H`, we obtain complete
necessary and sufficient characterizations of both almost invariant vectors and spectral gap.
Combined with `Finset.finite_stabilizer` and `MulAction.finite_stabilizer_of_finset_invariant` in
`TauCeti.GroupTheory.GroupAction.Stabilizer.Basic`, the finite-stabilizer criteria apply directly
to Bernoulli-shift cylinder configurations.

## Main results

* `Measure.exists_finset_sum_card_smul_symmDiff_lt_of_norm_koopman_sub_lt` and
  `Measure.exists_finset_card_smul_symmDiff_lt_of_hasAlmostInvariantVectors_count_koopman`
  give the discrete $P_2$ criterion from `ℓ²(X, E)` almost invariant vectors to Følner sets in `X`.
* `MeasureTheory.Measure.hasAlmostInvariantVectors_count_koopman_quotient_iff`: when
  `HasFoelnerSets H`, `ℓ²(G ⧸ H, E)` has almost invariant vectors iff `Nontrivial E` and
  `HasFoelnerSets G`.
* `MeasureTheory.Measure.hasSpectralGap_count_koopman_of_not_hasFoelnerSets` and
  `MeasureTheory.Measure.hasSpectralGap_count_koopman_of_finite_stabilizer`: Anantharaman–Popa
  Lemma 15.1.9 for vector-valued counting-measure Koopman representations.
* `MeasureTheory.Measure.hasSpectralGap_count_koopman_quotient_iff` and
  `MeasureTheory.Measure.hasSpectralGap_count_koopman_quotient_scalar_iff`: necessary and
  sufficient criterion for spectral gap of `ℓ²(G ⧸ H, E)` when `HasFoelnerSets H`.
* `HilbertBasis.hasSpectralGap_of_not_hasFoelnerSets` and
  `HilbertBasis.hasSpectralGap_of_finite_stabilizer`: spectral gap for any representation permuting
  a `HilbertBasis` whose non-fixed indices have amenable or finite stabilizers.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Lemma 15.1.9.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
* P. Eymard, *Moyennes invariantes et représentations unitaires*, Lecture Notes in Mathematics 300.
-/

public section

open MeasureTheory Finset
open scoped ENNReal InnerProductSpace Pointwise symmDiff

namespace MeasureTheory.Measure

section P2Criterion

variable {G X 𝕜 E : Type*} [Group G] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MulAction G X] [MeasurableConstSMul G X] [NormedRing 𝕜] [NormedAddCommGroup E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

omit [MeasurableSingletonClass X] in
/-- **Discrete $P_2$ converse, single-vector form.** If a unit vector `v ∈ ℓ²(X, E)` has small
Koopman displacement on `K`, then some finite nonempty subset `F ⊆ X` satisfies
`∑_{g ∈ K} |g • F ∆ F| < ε |F|`. -/
theorem exists_finset_sum_card_smul_symmDiff_lt_of_norm_koopman_sub_lt [DecidableEq X]
    (K : Finset G) {ε : ℝ} (hε : 0 < ε) {v : Lp E 2 (count : Measure X)} (hv : ‖v‖ = 1)
    (hdisp : ∀ g ∈ K,
      ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ ≤ ε / (8 * (#K + 1))) :
    ∃ F : Finset X, F.Nonempty ∧ ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  let q : X → ℝ := fun x ↦ ‖v x‖ ^ 2
  have hq0 (x : X) : 0 ≤ q x := sq_nonneg _
  have hq_sum : Summable q := L2.summable_norm_sq_apply v
  have hq1 : ∑' x, q x = 1 := by
    rw [← L2.norm_sq_eq_tsum_apply v, hv, one_pow]
  have hvar (g : G) (hg : g ∈ K) : ∑' x, |q (g⁻¹ • x) - q x| ≤ ε / (4 * (#K + 1)) := by
    have hd_int : Integrable (fun x ↦ |q (g⁻¹ • x) - q x|) (count : Measure X) := by
      have hcongr : (fun x ↦ |q (g⁻¹ • x) - q x|) =ᵐ[count]
          fun x ↦ |‖((count : Measure X).koopman G 𝕜 E 2 g v) x‖ ^ 2 - ‖v x‖ ^ 2| := by
        filter_upwards [coeFn_koopman (G := G) (𝕜 := 𝕜) count 2 g v] with x hx
        simp [q, hx]
      exact (integrable_congr hcongr).mpr (Lp.integrable_norm_sq_sub _ _).abs
    rw [← integral_count_eq_tsum hd_int]
    calc ∫ x, |q (g⁻¹ • x) - q x| ∂(count : Measure X)
        ≤ 2 * ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ :=
          integral_abs_norm_sq_koopman_sub_le_two_mul (𝕜 := 𝕜) count g hv
      _ ≤ 2 * (ε / (8 * (#K + 1))) := mul_le_mul_of_nonneg_left (hdisp g hg) zero_le_two
      _ = ε / (4 * (#K + 1)) := by
          have : (0 : ℝ) < #K + 1 := by positivity
          field_simp
          ring
  exact TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_tsum_eq_one hq0 hq_sum hq1 K hε hvar

omit [MeasurableSingletonClass X] in
/-- **Discrete $P_2$ converse.** Almost invariant vectors in `ℓ²(X, E)` yield finite nonempty Følner
sets in `X` for every finite `K ⊆ G` and `ε > 0`. -/
theorem exists_finset_card_smul_symmDiff_lt_of_hasAlmostInvariantVectors_count_koopman
    [DecidableEq X]
    (h : ((count : Measure X).koopman G 𝕜 E 2).HasAlmostInvariantVectors)
    (K : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset X, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  rw [ContRepresentation.hasAlmostInvariantVectors_def] at h
  obtain ⟨v, hv, hdisp⟩ := h K (ε / (8 * (#K + 1))) (by positivity)
  obtain ⟨F, hF, hsum⟩ :=
    exists_finset_sum_card_smul_symmDiff_lt_of_norm_koopman_sub_lt K hε hv
      fun g hg ↦ (hdisp g hg).le
  exact ⟨F, hF, fun g hg ↦
    (single_le_sum (f := fun g ↦ (#((g • F) ∆ F) : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) hg).trans_lt hsum⟩

end P2Criterion

section QuasiRegularAndKoopman

variable {G 𝕜 E : Type*} [Group G] [RCLike 𝕜]

/-- **Mackey–Eymard theorem for quasi-regular almost invariant vectors.** When `H` has Følner sets,
the quasi-regular representation on `ℓ²(G ⧸ H, E)` has almost invariant vectors if and only if `E`
is nontrivial and `G` has Følner sets. -/
theorem hasAlmostInvariantVectors_count_koopman_quotient_iff {H : Subgroup G}
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableConstSMul G (G ⧸ H)] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hH : TauCeti.HasFoelnerSets H) :
    ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).HasAlmostInvariantVectors ↔
      Nontrivial E ∧ TauCeti.HasFoelnerSets G := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hsub
      rw [not_nontrivial_iff_subsingleton] at hsub
      obtain ⟨v, hv⟩ := h.exists_ne_zero
      exact hv (Lp.eq_zero_iff_ae_eq_zero.mpr (ae_of_all _ fun x ↦ Subsingleton.elim (v x) 0))
    · exact (TauCeti.hasFoelnerSets_iff_exists_finset_quotient hH).mpr
        (exists_finset_card_smul_symmDiff_lt_of_hasAlmostInvariantVectors_count_koopman h)
  · rintro ⟨hE, hG⟩
    exact hasAlmostInvariantVectors_count_koopman_of_forall_exists_finset
      ((TauCeti.hasFoelnerSets_iff_exists_finset_quotient hH).mp hG)

/-- **Anantharaman–Popa Lemma 15.1.9.** If `G` does not have Følner sets and every non-fixed point
of `X` has stabilizer with Følner sets, then the Koopman representation of `G` on `ℓ²(X, E)` has
spectral gap. -/
theorem hasSpectralGap_count_koopman_of_not_hasFoelnerSets {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MulAction G X] [MeasurableConstSMul G X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (hG : ¬ TauCeti.HasFoelnerSets G)
    (hstab : ∀ x ∉ MulAction.fixedPoints G X, TauCeti.HasFoelnerSets (MulAction.stabilizer G x)) :
    ((count : Measure X).koopman G 𝕜 E 2).HasSpectralGap := by
  classical
  have hunit := isUnitary_koopman (G := G) (𝕜 := 𝕜) (E := E) (count : Measure X)
  rw [ContRepresentation.hasSpectralGap_iff_not_hasAlmostInvariantVectors _ hunit]
  intro haiv
  rw [ContRepresentation.hasAlmostInvariantVectors_def] at haiv
  apply hG
  rw [TauCeti.hasFoelnerSets_iff]
  intro K ε hε
  let U : SubMulAction G X :=
    { carrier := (MulAction.fixedPoints G X)ᶜ
      smul_mem' := fun g x hx hfix ↦ hx fun h ↦
        MulAction.injective g (by simpa [mul_smul] using hfix (g * h * g⁻¹)) }
  obtain ⟨u, hu_norm, hu_disp⟩ := haiv K (ε / (16 * (#K + 1))) (by positivity)
  let v : Lp E 2 (count : Measure X) := u
  have hv_norm : ‖v‖ = 1 := Submodule.norm_coe u ▸ hu_norm
  have hv_fix (x : X) (hx : x ∈ MulAction.fixedPoints G X) : v x = 0 :=
    apply_eq_zero_of_mem_orthogonal_invariants_count_koopman u.property hx
  let qX : X → ℝ := fun x ↦ ‖v x‖ ^ 2
  have hqX0 (x : X) : 0 ≤ qX x := sq_nonneg _
  have hqX_sum : Summable qX := L2.summable_norm_sq_apply v
  have hqX1 : ∑' x, qX x = 1 := by
    rw [← L2.norm_sq_eq_tsum_apply v, hv_norm, one_pow]
  let q : U → ℝ := fun y ↦ qX y.val
  have hq0 (y : U) : 0 ≤ q y := hqX0 y.val
  have hq_sum : Summable q := hqX_sum.subtype _
  have hq1 : ∑' y, q y = 1 := by
    have htsum : ∑' y : U, q y = ∑' x, qX x :=
      Function.Injective.tsum_eq (g := (Subtype.val : U → X)) Subtype.val_injective
        (f := qX) fun x hx ↦ ⟨⟨x, fun hfix ↦ hx (by simp [qX, hv_fix x hfix])⟩, rfl⟩
    exact htsum.trans hqX1
  have hvar (g : G) (hg : g ∈ K) : ∑' y, |q (g⁻¹ • y) - q y| ≤ (ε / 2) / (4 * (#K + 1)) := by
    have hd_int : Integrable (fun x ↦ |qX (g⁻¹ • x) - qX x|) (count : Measure X) := by
      have hcongr : (fun x ↦ |qX (g⁻¹ • x) - qX x|) =ᵐ[count]
          fun x ↦ |‖((count : Measure X).koopman G 𝕜 E 2 g v) x‖ ^ 2 - ‖v x‖ ^ 2| := by
        filter_upwards [coeFn_koopman (G := G) (𝕜 := 𝕜) count 2 g v] with x hx
        simp [qX, hx]
      exact (integrable_congr hcongr).mpr (Lp.integrable_norm_sq_sub _ _).abs
    have hd_sub : (∑' y : U, |q (g⁻¹ • y) - q y|) = ∑' x, |qX (g⁻¹ • x) - qX x| :=
      Function.Injective.tsum_eq (g := (Subtype.val : U → X)) Subtype.val_injective
        (f := fun x ↦ |qX (g⁻¹ • x) - qX x|) fun x hx ↦
          ⟨⟨x, fun hfix ↦ hx (by
            dsimp only
            rw [hfix g⁻¹, sub_self, abs_zero])⟩, rfl⟩
    have hdisp_v : ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ < ε / (16 * (#K + 1)) := by
      simpa [v, ← Submodule.norm_coe] using hu_disp g hg
    rw [hd_sub, ← integral_count_eq_tsum hd_int]
    calc ∫ x, |qX (g⁻¹ • x) - qX x| ∂(count : Measure X)
        ≤ 2 * ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ :=
          integral_abs_norm_sq_koopman_sub_le_two_mul (𝕜 := 𝕜) count g hv_norm
      _ ≤ 2 * (ε / (16 * (#K + 1))) := mul_le_mul_of_nonneg_left hdisp_v.le zero_le_two
      _ = (ε / 2) / (4 * (#K + 1)) := by
          have : (0 : ℝ) < #K + 1 := by positivity
          field_simp
          ring
  obtain ⟨F_U, _, hF_U⟩ :=
    TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_tsum_eq_one hq0 hq_sum hq1 K
      (half_pos hε) hvar
  obtain ⟨y₀, _, F₁, hF₁_ne, hF₁⟩ :=
    TauCeti.exists_quotient_finset_of_sum_card_smul_symmDiff_lt hF_U
  have hstab_eq : MulAction.stabilizer G y₀ = MulAction.stabilizer G y₀.val := by
    ext g
    simp [Subtype.ext_iff]
  have hstab_foelner : TauCeti.HasFoelnerSets (MulAction.stabilizer G y₀) :=
    (MulEquiv.hasFoelnerSets_iff (MulEquiv.subgroupCongr hstab_eq)).mpr
      (hstab y₀.val y₀.property)
  exact TauCeti.exists_finset_card_smul_symmDiff_lt_of_quotient hstab_foelner K hε hF₁_ne hF₁

/-- Finite-stabilizer specialization of `hasSpectralGap_count_koopman_of_not_hasFoelnerSets`: if
`G` does not have Følner sets and every non-fixed point of `X` has finite stabilizer, then
`ℓ²(X, E)` has spectral gap. -/
theorem hasSpectralGap_count_koopman_of_finite_stabilizer {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MulAction G X] [MeasurableConstSMul G X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (hG : ¬ TauCeti.HasFoelnerSets G)
    (hstab : ∀ x ∉ MulAction.fixedPoints G X, Finite (MulAction.stabilizer G x)) :
    ((count : Measure X).koopman G 𝕜 E 2).HasSpectralGap :=
  hasSpectralGap_count_koopman_of_not_hasFoelnerSets hG fun x hx ↦
    have := hstab x hx
    .of_finite

/-- **Quasi-regular spectral gap characterization.** When `H` has Følner sets, the quasi-regular
representation of `G` on `ℓ²(G ⧸ H, E)` has spectral gap if and only if `G ⧸ H` is finite, `E` is
a subsingleton, or `G` does not have Følner sets. -/
theorem hasSpectralGap_count_koopman_quotient_iff {H : Subgroup G}
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableConstSMul G (G ⧸ H)] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (hH : TauCeti.HasFoelnerSets H) :
    ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).HasSpectralGap ↔
      Finite (G ⧸ H) ∨ Subsingleton E ∨ ¬ TauCeti.HasFoelnerSets G := by
  constructor
  · intro hgap
    by_contra! hnot
    obtain ⟨hinf, hnontriv, hG⟩ := hnot
    have horb (q : G ⧸ H) : (MulAction.orbit G q).Infinite := by
      have huniv : MulAction.orbit G q = Set.univ := by
        ext q'
        simp only [MulAction.mem_orbit_iff, Set.mem_univ, iff_true]
        induction q using QuotientGroup.induction_on with
        | H x =>
          induction q' using QuotientGroup.induction_on with
          | H y =>
            refine ⟨y * x⁻¹, ?_⟩
            rw [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel_right]
      rw [huniv]
      exact Set.infinite_univ
    have hinv : ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).invariants = ⊥ :=
      invariants_count_koopman_of_infinite_orbit (by norm_num) horb
    have horth : ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).invariantsᗮ = ⊤ := by
      rw [hinv, Submodule.bot_orthogonal_eq_top]
    have hunit := isUnitary_koopman (G := G) (𝕜 := 𝕜) (E := E) (count : Measure (G ⧸ H))
    have haiv : ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).HasAlmostInvariantVectors :=
      (hasAlmostInvariantVectors_count_koopman_quotient_iff hH).mpr ⟨hnontriv, hG⟩
    let e := LinearIsometryEquiv.ofTop _ _ horth
    have haiv_orth : hunit.invariantsOrthogonal.HasAlmostInvariantVectors :=
      (ContRepresentation.hasAlmostInvariantVectors_iff_of_linearIsometryEquiv e
        fun g v ↦ hunit.coe_invariantsOrthogonal_apply g v).mpr haiv
    exact (ContRepresentation.hasSpectralGap_iff_not_hasAlmostInvariantVectors _ hunit).mp
      hgap haiv_orth
  · rintro (hfin | hsub | hnotG)
    · have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      refine ContRepresentation.hasSpectralGap_of_finite_quotient _ H.normalCore fun n hn ↦ ?_
      have hker : n⁻¹ ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
        rw [← H.normalCore_eq_ker]
        exact H.normalCore.inv_mem hn
      have hsmul : (fun q : G ⧸ H ↦ n⁻¹ • q) = id := by
        funext q
        exact Equiv.Perm.ext_iff.mp (MonoidHom.mem_ker.mp hker) q
      ext f : 1
      rw [one_apply_eq_self, koopman_apply]
      simpa only [hsmul] using Lp.compMeasurePreserving_id_apply f
    · have : Subsingleton (Lp E 2 (count : Measure (G ⧸ H))) :=
        ⟨fun f g ↦ Lp.ext (ae_of_all _ fun x ↦ Subsingleton.elim (f x) (g x))⟩
      exact ContRepresentation.hasSpectralGap_of_subsingleton _
    · refine hasSpectralGap_count_koopman_of_not_hasFoelnerSets hnotG fun q _ ↦ ?_
      induction q using QuotientGroup.induction_on with
      | H x =>
        have hq : (x : G ⧸ H) = x • ((1 : G) : G ⧸ H) := by
          rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
        let e : H ≃* MulAction.stabilizer G (x : G ⧸ H) :=
          (MulEquiv.subgroupCongr (MulAction.stabilizer_quotient H)).symm.trans
            (MulAction.stabilizerEquivStabilizer hq)
        exact (MulEquiv.hasFoelnerSets_iff e).mp hH

/-- Scalar specialization of `hasSpectralGap_count_koopman_quotient_iff`: when `H` has Følner sets,
`ℓ²(G ⧸ H, 𝕜)` has spectral gap iff `G ⧸ H` is finite or `G` does not have Følner sets. -/
theorem hasSpectralGap_count_koopman_quotient_scalar_iff {H : Subgroup G}
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableConstSMul G (G ⧸ H)] (hH : TauCeti.HasFoelnerSets H) :
    ((count : Measure (G ⧸ H)).koopman G 𝕜 𝕜 2).HasSpectralGap ↔
      Finite (G ⧸ H) ∨ ¬ TauCeti.HasFoelnerSets G := by
  rw [hasSpectralGap_count_koopman_quotient_iff hH]
  simp [not_subsingleton]

end QuasiRegularAndKoopman

end MeasureTheory.Measure

section HilbertBasisPermutation

/-- **Spectral gap for `HilbertBasis` permutation representations.** If a representation `ρ` of `G`
permutes a `HilbertBasis` indexed by a `G`-set `X`, `G` does not have Følner sets, and every
non-fixed index in `X` has stabilizer with Følner sets, then `ρ` has spectral gap. Neither a
measurable-space structure on `X` nor an explicit completeness hypothesis on `V` is required. -/
theorem HilbertBasis.hasSpectralGap_of_not_hasFoelnerSets {G X 𝕜 V : Type*} [Group G]
    [MulAction G X] [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : HilbertBasis X 𝕜 V) {ρ : ContRepresentation 𝕜 G V}
    (hb : ∀ g x, ρ g (b x) = b (g • x))
    (hG : ¬ TauCeti.HasFoelnerSets G)
    (hstab : ∀ x ∉ MulAction.fixedPoints G X, TauCeti.HasFoelnerSets (MulAction.stabilizer G x)) :
    ρ.HasSpectralGap := by
  let : MeasurableSpace X := ⊤
  have : DiscreteMeasurableSpace X := ⟨fun _ ↦ trivial⟩
  let δ := MeasureTheory.L2.countHilbertBasis 𝕜 X
  let e : V ≃ₗᵢ[𝕜] Lp 𝕜 2 (Measure.count : Measure X) := b.repr.trans δ.repr.symm
  have he_basis (x : X) : e (b x) = δ x := by
    classical
    simp [e, HilbertBasis.repr_self, HilbertBasis.repr_symm_single]
  have he (g : G) (v : V) :
      e (ρ g v) = (Measure.count : Measure X).koopman G 𝕜 𝕜 2 g (e v) := by
    let L₁ : V →L[𝕜] Lp 𝕜 2 (Measure.count : Measure X) :=
      e.toLinearIsometry.toContinuousLinearMap.comp (ρ g)
    let L₂ : V →L[𝕜] Lp 𝕜 2 (Measure.count : Measure X) :=
      ((Measure.count : Measure X).koopman G 𝕜 𝕜 2 g).comp
        e.toLinearIsometry.toContinuousLinearMap
    have hspan : ∀ w ∈ Submodule.span 𝕜 (Set.range b), L₁ w = L₂ w := fun w hw ↦
      Submodule.span_induction (fun _ ⟨x, hx⟩ ↦ by
        subst hx
        simp [L₁, L₂, hb, he_basis, δ])
        (by simp) (fun _ _ _ _ h1 h2 ↦ by simp [h1, h2])
        (fun c _ _ h1 ↦ by simp [h1]) hw
    have hcl : ∀ w ∈ (Submodule.span 𝕜 (Set.range b)).topologicalClosure, L₁ w = L₂ w := by
      intro w hw
      have hclosed : IsClosed {u : V | L₁ u = L₂ u} := isClosed_eq L₁.continuous L₂.continuous
      exact hclosed.closure_subset_iff.mpr hspan hw
    exact hcl v (b.dense_span.symm ▸ Submodule.mem_top)
  exact (ContRepresentation.hasSpectralGap_iff_of_linearIsometryEquiv e he).mpr
    (MeasureTheory.Measure.hasSpectralGap_count_koopman_of_not_hasFoelnerSets hG hstab)

/-- Finite-stabilizer specialization of `HilbertBasis.hasSpectralGap_of_not_hasFoelnerSets`: if
`ρ` permutes a `HilbertBasis` indexed by `X`, `G` does not have Følner sets, and every non-fixed
index in `X` has finite stabilizer, then `ρ` has spectral gap. -/
theorem HilbertBasis.hasSpectralGap_of_finite_stabilizer {G X 𝕜 V : Type*} [Group G]
    [MulAction G X] [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : HilbertBasis X 𝕜 V) {ρ : ContRepresentation 𝕜 G V}
    (hb : ∀ g x, ρ g (b x) = b (g • x))
    (hG : ¬ TauCeti.HasFoelnerSets G)
    (hstab : ∀ x ∉ MulAction.fixedPoints G X, Finite (MulAction.stabilizer G x)) :
    ρ.HasSpectralGap :=
  b.hasSpectralGap_of_not_hasFoelnerSets hb hG fun x hx ↦
    have := hstab x hx
    .of_finite

end HilbertBasisPermutation
