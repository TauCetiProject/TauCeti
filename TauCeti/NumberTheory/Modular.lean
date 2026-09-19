/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.GroupTheory.Index.Basic
import TauCeti.GroupTheory.QuotientGroup.ThirdIso
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure theory of the standard fundamental domain

The measure theory of the standard fundamental domain `𝒟 = ModularGroup.fd` for `SL₂(ℤ)`,
complementing its topology from `Mathlib/NumberTheory/Modular.lean`: `𝒟` has finite
invariant measure, its frontier is null, and therefore integrals over `𝒟` and its interior
`𝒟ᵒ` agree. The next section records that the translates `γ • 𝒟ᵒ` are open and that two are
disjoint unless their translating elements differ by a sign; these facts turn suitable finite
sums of integrals over translates into a single integral over their union.

Those two halves are exactly what `MeasureTheory.IsFundamentalDomain` asks for, and the last
section assembles them: `𝒟ᵒ` is a fundamental domain in the measure-theoretic sense. The group
acting has to be `PSL(2, ℤ)`, not `SL(2, ℤ)` — `−I` fixes every point of `ℍ`, so the translates
indexed by `SL(2, ℤ)` are never pairwise disjoint — and the domain has to be the open `𝒟ᵒ`, on
which Mathlib's Second Fundamental Domain Lemma is an honest disjointness rather than a
statement about a boundary. Covering is then only almost everywhere, the two domains differing
by the null frontier. Tiled over the cosets of a subgroup this gives a fundamental domain at
every level, which is what a Petersson product for a congruence subgroup is an integral over.

## Main results

* `ModularGroup.volume_fd_lt_top`: the standard fundamental domain has finite invariant
  measure.
* `ModularGroup.volume_frontier_fd`: the frontier of `𝒟` has zero invariant measure.
* `ModularGroup.fd_ae_eq_fdo`: `𝒟` and `𝒟ᵒ` agree almost everywhere (so set integrals
  over them coincide, via `MeasureTheory.setIntegral_congr_set`).
* `ModularGroup.isOpen_smul_fdo` and `ModularGroup.disjoint_smul_fdo`: the translates of the
  open fundamental domain are open, and two of them are disjoint unless the translating
  elements differ by a sign.
* `ModularGroup.isFundamentalDomain_fdo`: `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)` acting
  on `ℍ` with the invariant measure.
* `ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo`: the coset tiling of `𝒟ᵒ` is a
  fundamental domain for any subgroup of `PSL(2, ℤ)`.
* `ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter`: the same tiling indexed
  by `SL(2, ℤ) ⧸ Γ.withCenter`, which is the indexing the Petersson product uses.
* `ModularGroup.isFundamentalDomain_smul_of_inv_conjAct_eq`: an element of `GL(2, ℝ)`
  conjugating the image of `Γ` onto that of `Γ'` carries a fundamental domain for `Γ` to one for
  `Γ'` — the step that lets a Petersson product be compared with its translate under the Fricke
  or an Atkin–Lehner matrix, or under the matrix of a double coset operator.

Split out of the Petersson inner-product development ported from the AINTLIB
`LeanModularForms` project
(<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>,
`Modularforms/PeterssonInnerProduct.lean`, Chris Birkbeck).

Two of the results correspond to statements in that project:
`ModularGroup.isFundamentalDomain_fdo` to `isFundamentalDomain_fdo_PSL`
(`Modularforms/PSL2Action.lean`), and `ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo`
to `isFundamentalDomain_Gamma1_PSL` (`Modularforms/PeterssonLevelN.lean`), of which it is the
arbitrary-subgroup form — that one states the tiling for the image of `Γ₁(N)`. Both are stated
here for Mathlib's `volume : Measure ℍ` rather than that project's own hyperbolic measure. The
results on translates of `𝒟ᵒ` have no counterpart there.
-/

public section

noncomputable section

open MeasureTheory Measure UpperHalfPlane Complex Set ENNReal

open scoped NNReal MatrixGroups Pointwise

namespace ModularGroup

private theorem integrableOn_zpow_neg_two_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (· ^ (-2 : ℤ)) (Ioi c) (volume : Measure ℝ) := by
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc
  have h_eq : (· ^ (-2 : ℝ) : ℝ → ℝ) = (· ^ (-2 : ℤ)) := by
    funext x
    rw [← Real.rpow_intCast]
    norm_num
  rwa [h_eq] at h

private theorem strip_lintegral_lt_top {c : ℝ} (hc : 0 < c) :
    ∫⁻ p in Icc (-1/2 : ℝ) (1/2) ×ˢ Ioi c,
      ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂(volume : Measure (ℝ × ℝ)) < ⊤ := by
  rw [volume_eq_prod ℝ ℝ, setLIntegral_prod_symm _ (by fun_prop)]
  simp_rw [setLIntegral_const]
  calc ∫⁻ y in Ioi c, ENNReal.ofReal (y ^ (-2 : ℤ)) *
        volume (Icc (-1/2 : ℝ) (1/2)) ∂volume
      ≤ ∫⁻ y in Ioi c, ENNReal.ofReal (y ^ (-2 : ℤ)) * 1 ∂volume := by
        gcongr with y; rw [Real.volume_Icc]; norm_num
    _ = _ := by simp
    _ < ⊤ := lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi
        fun y _ ↦ Real.ofReal_le_enorm _)
        (integrableOn_zpow_neg_two_Ioi hc).hasFiniteIntegral

private theorem setLIntegral_im_eq_prod (g : ℝ → ENNReal) (T : Set (ℝ × ℝ)) :
    ∫⁻ z in measurableEquivRealProd ⁻¹' T, g z.im ∂(volume : Measure ℂ) =
      ∫⁻ p in T, g p.2 ∂(volume : Measure (ℝ × ℝ)) := by
  have h := volume_preserving_equiv_real_prod.setLIntegral_comp_emb
      measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ ↦ g p.2)
      (measurableEquivRealProd ⁻¹' T)
  rw [MeasurableEquiv.image_preimage] at h
  simpa only [measurableEquivRealProd_apply] using h

/-- The invariant measure of the standard fundamental domain is finite. -/
theorem volume_fd_lt_top : (volume : Measure ℍ) fd < ⊤ := by
  rw [volume_eq_lintegral]
  set T := Icc (-1/2 : ℝ) (1/2) ×ˢ Ioi (Real.sqrt 3 / 4)
  calc ∫⁻ z in UpperHalfPlane.coe '' fd, ↑((1 / ‖z.im‖₊) ^ 2 : ℝ≥0)
      = ∫⁻ z in UpperHalfPlane.coe '' fd, ENNReal.ofReal (z.im ^ (-2 : ℤ)) := by
        refine setLIntegral_congr_fun
          (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr
            isClosed_fd.measurableSet) fun z hz ↦ ?_
        obtain ⟨τ, -, rfl⟩ := hz
        rw [← ENNReal.ofReal_coe_nnreal]
        congr 1
        push_cast [Real.nnnorm_of_nonneg τ.im_pos.le]
        rw [one_div, inv_pow, zpow_neg]
        norm_num
    _ ≤ ∫⁻ z in measurableEquivRealProd ⁻¹' T, ENNReal.ofReal (z.im ^ (-2 : ℤ)) :=
        lintegral_mono_set fun z ↦ by
          rintro ⟨τ, hτ, rfl⟩
          simp only [mem_preimage, measurableEquivRealProd_apply, coe_re, coe_im]
          refine ⟨⟨by linarith [(abs_le.mp hτ.2).1], (abs_le.mp hτ.2).2⟩,
            mem_Ioi.mpr ?_⟩
          have h := three_le_four_mul_im_sq_of_mem_fd hτ
          have h_sq : (4 : ℝ) * τ.im ^ 2 = (2 * τ.im) ^ 2 := by ring
          rw [h_sq] at h
          have h2 := Real.sqrt_le_sqrt h
          rw [Real.sqrt_sq (by linarith [τ.im_pos])] at h2
          nlinarith [Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ = ∫⁻ p in T, ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂volume :=
        setLIntegral_im_eq_prod (fun y ↦ ENNReal.ofReal (y ^ (-2 : ℤ))) T
    _ < ⊤ := strip_lintegral_lt_top (by positivity)

private theorem volume_complex_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h_eq : {z : ℂ | z.re = c} = measurableEquivRealProd ⁻¹' ({c} ×ˢ univ) := by
    ext z
    simp [measurableEquivRealProd_apply]
  rw [h_eq, volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem volume_complex_normSq_eq (c : ℝ) :
    volume {z : ℂ | Complex.normSq z = c} = 0 := by
  rcases le_or_gt 0 c with hc | hc
  · have h_eq : {z : ℂ | Complex.normSq z = c} = Metric.sphere (0 : ℂ) (Real.sqrt c) := by
      ext z
      simp only [mem_ofPred_eq, Complex.normSq_eq_norm_sq, mem_sphere_zero_iff_norm]
      constructor
      · intro h
        rw [← h, Real.sqrt_sq (norm_nonneg z)]
      · intro h
        rw [h, Real.sq_sqrt hc]
    rw [h_eq]
    exact Measure.addHaar_sphere volume 0 _
  · have h_empty : {z : ℂ | Complex.normSq z = c} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun z hz ↦ not_le.mpr hc (hz ▸ Complex.normSq_nonneg z)
    rw [h_empty]
    exact measure_empty

/-- **The frontier of the standard fundamental domain has zero invariant measure.**

`frontier 𝒟 = 𝒟 \ 𝒟ᵒ ⊆ {normSq = 1} ∪ {Re = 1/2} ∪ {Re = −1/2}`, each of which has
zero Lebesgue measure in `ℂ`. -/
theorem volume_frontier_fd : (volume : Measure ℍ) (frontier (fd : Set ℍ)) = 0 := by
  rw [frontier, isClosed_fd.closure_eq, ← fdo_eq_interior_fd]
  apply measure_mono_null _ (volume_preimage_coe_null
    (measure_union_null
      (measure_union_null (volume_complex_normSq_eq 1) (volume_complex_re_eq (1/2)))
      (volume_complex_re_eq (-1/2))))
  intro τ ⟨hfd, hfdo⟩
  simp only [fd, fdo, mem_ofPred_eq, not_and, not_lt] at hfd hfdo
  obtain ⟨h1, h2⟩ := hfd
  simp only [mem_preimage, mem_union, mem_ofPred_eq]
  by_cases h : Complex.normSq (τ : ℂ) = 1
  · left; left; exact h
  · have hns : 1 < Complex.normSq (τ : ℂ) := lt_of_le_of_ne h1 (Ne.symm h)
    have habs : |τ.re| = 1 / 2 := le_antisymm h2 (hfdo hns)
    by_cases hre : 0 ≤ τ.re
    · left; right; rw [coe_re]; rwa [abs_of_nonneg hre] at habs
    · push Not at hre; right
      rw [coe_re]; rw [abs_of_neg hre] at habs; linarith

/-- `fd` and `fdo` are a.e. equal w.r.t. the invariant measure. -/
theorem fd_ae_eq_fdo : (fd : Set ℍ) =ᶠ[ae (volume : Measure ℍ)] fdo :=
  ((fdo_eq_interior_fd.symm ▸ interior_ae_eq_of_null_frontier volume_frontier_fd :
    (fdo : Set ℍ) =ᶠ[ae (volume : Measure ℍ)] fd)).symm

/-! ### Disjointness of translates of the open fundamental domain -/

/-- Every translate of the open fundamental domain is open: translation is a homeomorphism
of `ℍ`. -/
theorem isOpen_smul_fdo (γ : SL(2, ℤ)) : IsOpen (γ • fdo) := by
  rw [sl_smul_set]
  exact isOpen_fdo.smul _

/-- **Distinct translates of the open fundamental domain are disjoint.** A point of
`γ • 𝒟ᵒ ∩ δ • 𝒟ᵒ` exhibits two points of `𝒟ᵒ` in the same `SL(2, ℤ)`-orbit, which forces
`γ⁻¹δ = ±I` by `ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo`. Both signs must be excluded,
`−I` acting trivially on `ℍ`: it is the translates indexed by `SL(2, ℤ)/{±I}`, not by
`SL(2, ℤ)`, that are genuinely distinct. -/
theorem disjoint_smul_fdo {γ δ : SL(2, ℤ)} (h₁ : γ⁻¹ * δ ≠ 1) (h₂ : γ⁻¹ * δ ≠ -1) :
    Disjoint (γ • fdo) (δ • fdo) := by
  rw [Set.disjoint_left]
  rintro w ⟨z, hz, rfl⟩ ⟨z', hz', hw⟩
  -- Beta-reduce the pointwise-set action recorded by membership in the translated set.
  have hw' : δ • z' = γ • z := hw
  refine (eq_one_or_neg_one_of_mem_fdo_mem_fdo hz' (g := γ⁻¹ * δ) ?_).elim h₁ h₂
  rw [mul_smul, hw', inv_smul_smul]
  exact hz



/-! ### `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)` -/

open Matrix.SpecialLinearGroup in
/-- **The open standard domain `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)` acting on `ℍ`**,
with respect to the invariant measure: almost every point of `ℍ` is carried into `𝒟ᵒ` by some
element, and distinct elements carry `𝒟ᵒ` to sets meeting in a null set.

It is `PSL(2, ℤ)` and the *open* domain, not `SL(2, ℤ)` and `𝒟`, that make the statement true;
the module docstring says why. -/
theorem isFundamentalDomain_fdo :
    MeasureTheory.IsFundamentalDomain PSL(2, ℤ) (fdo : Set ℍ) volume := by
  refine MeasureTheory.IsFundamentalDomain.mk'' isOpen_fdo.measurableSet.nullMeasurableSet
    ?_ ?_ fun g ↦ (measurePreserving_smul g volume).quasiMeasurePreserving
  · -- the points never landing in `𝒟ᵒ` are covered by the translates of the null `𝒟 \ 𝒟ᵒ`
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := ⋃ γ : SL(2, ℤ), (γ • ·) ⁻¹' ((fd : Set ℍ) \ fdo))
      (fun τ hτ ↦ ?_) (measure_iUnion_null fun γ ↦
        (measurePreserving_smul γ (volume : Measure ℍ)).quasiMeasurePreserving.preimage_null
          (MeasureTheory.ae_eq_set.mp fd_ae_eq_fdo).1)
    obtain ⟨γ, hγ⟩ := exists_smul_mem_fd τ
    exact Set.mem_iUnion.mpr ⟨γ, hγ, not_exists.mp hτ (γ : PSL(2, ℤ))⟩
  · refine fun g hg ↦ QuotientGroup.induction_on g (fun γ hγ ↦ ?_) hg
    have hne : ¬ (γ = 1 ∨ γ = -1) := fun h ↦ hγ (by
      simp only [QuotientGroup.eq_one_iff,
        Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
      exact h)
    rw [pslMk_smul_set]
    refine Disjoint.aedisjoint (Disjoint.symm ?_)
    simpa using disjoint_smul_fdo (γ := 1) (δ := γ) (by simpa using fun h ↦ hne (Or.inl h))
      (by simpa using fun h ↦ hne (Or.inr h))

/-- **A fundamental domain for a subgroup of `PSL(2, ℤ)`**: the union of the `[PSL(2, ℤ) : H]`
translates `(q.out)⁻¹ • 𝒟ᵒ`, one for each coset `q ∈ PSL(2, ℤ) ⧸ H`, is a fundamental domain for
`H` acting on `ℍ` with the invariant measure — for **every** subgroup, no finiteness needed, since
`PSL(2, ℤ)` is countable and so is each of its coset spaces. At a congruence subgroup this is the
domain a Petersson product at level `N` is an integral over. -/
theorem isFundamentalDomain_iUnion_out_inv_smul_fdo (H : Subgroup PSL(2, ℤ)) :
    MeasureTheory.IsFundamentalDomain H
      (⋃ q : PSL(2, ℤ) ⧸ H, ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ)) volume :=
  isFundamentalDomain_fdo.subgroup_iUnion_out_inv_smul H

/-- **The same tiling, indexed by the cosets of `Γ·{±I}` in `SL(2, ℤ)`.** For
`Γ ≤ SL(2, ℤ)`, the translates `(q.out)⁻¹ • 𝒟ᵒ` taken over `q ∈ SL(2, ℤ) ⧸ Γ.withCenter` tile a
fundamental domain for the image of `Γ` in `PSL(2, ℤ)`.

This is the shape the Petersson product presents: `CuspForm.peterssonInnerCosets` sums over
`SL(2, ℤ) ⧸ Γ.withCenter`, one coset at a time, because `±I` acts trivially on `ℍ`. The
`PSL(2, ℤ)`-indexed statement above does not apply to it directly: the two index sets are
different types, and `Quotient.out` picks unrelated representatives in each, so the two unions
are different sets. -/
theorem isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter (Γ : Subgroup SL(2, ℤ)) :
    MeasureTheory.IsFundamentalDomain
      (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
      (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, ((q.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ)) volume := by
  -- The `PSL(2, ℤ)`-indexed tiling cannot be transported here, the representatives being
  -- unrelated; what applies is the *transversal* form, which asks only that `q ↦ ⟦q.out⟧`
  -- enumerate `PSL(2, ℤ) ⧸ Γ` bijectively — and that is the third isomorphism theorem for coset
  -- spaces, `QuotientGroup.quotientQuotientEquivQuotientSup`, at `N = Z(SL(2, ℤ))`.
  -- The transversal: the inverse in `PSL(2, ℤ)` of the class of the chosen representative.
  set r : SL(2, ℤ) ⧸ Γ.withCenter → PSL(2, ℤ) :=
    fun q ↦ (((q.out : SL(2, ℤ)) : PSL(2, ℤ)))⁻¹ with hr_def
  have hset : (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, ((q.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ)) =
      ⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, r q • (fdo : Set ℍ) :=
    Set.iUnion_congr fun q ↦ (Matrix.SpecialLinearGroup.pslMk_smul_set _ _).symm
  rw [hset]
  refine isFundamentalDomain_fdo.iUnion_smul_of_transversal (r := r)
    (fun q ↦ isFundamentalDomain_fdo.nullMeasurableSet_smul _) ?_
  -- `q ↦ ⟦q.out⟧` enumerates `PSL(2, ℤ) ⧸ Γ` bijectively: that is the third isomorphism
  -- theorem for coset spaces, at `N = Z(SL(2, ℤ))`
  have hfun : (fun q : SL(2, ℤ) ⧸ Γ.withCenter ↦
      (QuotientGroup.mk ((r q)⁻¹) :
        PSL(2, ℤ) ⧸ Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))) =
      ⇑((Subgroup.quotientEquivOfEq (Subgroup.withCenter_def Γ)).trans
        (QuotientGroup.quotientQuotientEquivQuotientSup Γ (Subgroup.center SL(2, ℤ))).symm) := by
    funext q
    rw [hr_def, inv_inv]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk,
      QuotientGroup.quotientQuotientEquivQuotientSup_symm_mk]
  rw [hfun]
  exact ((Subgroup.quotientEquivOfEq (Subgroup.withCenter_def Γ)).trans
    (QuotientGroup.quotientQuotientEquivQuotientSup Γ
      (Subgroup.center SL(2, ℤ))).symm).bijective

open Matrix.SpecialLinearGroup in
/-- **A conjugating translate of a fundamental domain is a fundamental domain for the conjugate
group.** If `α ∈ GL(2, ℝ)` conjugates the image of `Γ` in `GL(2, ℝ)` onto that of `Γ'` —
`α⁻¹ Γ' α = Γ`, stated as `ConjAct.toConjAct α⁻¹ • Γ' = Γ` — then for every fundamental domain
`S` of the image of `Γ` in `PSL(2, ℤ)`, the translate `α • S` is a fundamental domain for the
image of `Γ'`: `α` carries `Γ`-orbits on `ℍ` to `Γ'`-orbits, since `α γ α⁻¹` acts on `ℍ` as an
element of `Γ'` does, and it preserves the invariant measure.

`α` need not lie in `SL(2, ℤ)`, nor even have integral entries. With `Γ' = Γ` this is the case of
a normaliser: the Fricke matrix `!![0, -1; N, 0]`, which normalises `Γ₁(N)` and `Γ₀(N)`, and the
Atkin–Lehner matrices, which normalise `Γ₀(N)`. With `Γ' ≠ Γ` it is the case of the double coset
operators, where a rational `α` carries `Γ ∩ α⁻¹ Γ α` onto `α Γ α⁻¹ ∩ Γ`. That is also why
`MeasureTheory.IsFundamentalDomain.smul_of_eq_conjAct_pointwise_smul` does not apply: it translates
by an element of the acting group itself, and `α` does not lie in `PSL(2, ℤ)`. -/
theorem isFundamentalDomain_smul_of_inv_conjAct_eq {Γ Γ' : Subgroup SL(2, ℤ)}
    {α : GL (Fin 2) ℝ} (hα : ConjAct.toConjAct α⁻¹ • Γ'.map (mapGL ℝ) = Γ.map (mapGL ℝ))
    {S : Set ℍ}
    (hS : IsFundamentalDomain (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) S volume) :
    IsFundamentalDomain (Γ'.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (α • S)
      volume := by
  have hmem : ∀ x : GL (Fin 2) ℝ, α * x * α⁻¹ ∈ Γ'.map (mapGL ℝ) ↔ x ∈ Γ.map (mapGL ℝ) := by
    intro x
    conv_rhs => rw [← hα]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [ConjAct.smul_def]
  have hconj : ∀ {A B : Subgroup SL(2, ℤ)} (β : GL (Fin 2) ℝ),
      (∀ x ∈ A.map (mapGL ℝ), β * x * β⁻¹ ∈ B.map (mapGL ℝ)) →
      ∀ h : A.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))),
        ∃ h' : B.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))), ∀ τ : ℍ,
          (h' : PSL(2, ℤ)) • τ = β • ((h : PSL(2, ℤ)) • (β⁻¹ • τ)) := by
    rintro A B β hβ ⟨_, γ, hγ, rfl⟩
    obtain ⟨γ', hγ', he⟩ := hβ _ ⟨γ, hγ, rfl⟩
    refine ⟨⟨QuotientGroup.mk' _ γ', γ', hγ', rfl⟩, fun τ ↦ ?_⟩
    simp only [QuotientGroup.mk'_apply, pslMk_smul, sl_moeb]
    rw [← mul_smul, ← mul_smul]
    -- `sl_moeb` states the action through the coercion `SL(2, ℤ) → GL (Fin 2) ℝ`, which is
    -- `mapGL ℝ` by definition
    exact congrArg (· • τ) he
  have hα' : ∀ x ∈ Γ.map (mapGL ℝ), α * x * α⁻¹ ∈ Γ'.map (mapGL ℝ) := fun x ↦ (hmem x).mpr
  have hα'' : ∀ x ∈ Γ'.map (mapGL ℝ), α⁻¹ * x * α⁻¹⁻¹ ∈ Γ.map (mapGL ℝ) := fun x hx ↦
    (hmem _).mp (by simpa [mul_assoc] using hx)
  choose e he using hconj α hα'
  have heq : ∀ {C : Subgroup SL(2, ℤ)}
      {g h : C.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))},
      (∀ τ : ℍ, (g : PSL(2, ℤ)) • τ = (h : PSL(2, ℤ)) • τ) → g = h :=
    fun hgh ↦ Subtype.ext (eq_of_smul_eq_smul hgh)
  have hbij : Function.Bijective e := by
    refine ⟨fun g h hgh ↦ heq fun τ ↦ ?_, fun h ↦ ?_⟩
    · have := congrArg (fun g : Γ'.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) ↦
        (g : PSL(2, ℤ)) • (α • τ)) hgh
      simpa [he] using this
    · obtain ⟨g, hg⟩ := hconj α⁻¹ hα'' h
      exact ⟨g, heq fun τ ↦ by simp [he, hg]⟩
  rw [← Set.preimage_smul_inv]
  exact hS.preimage_of_equiv (measurePreserving_smul α⁻¹ volume).quasiMeasurePreserving hbij
    fun g τ ↦ by simp only [Subgroup.smul_def, he, inv_smul_smul]

end ModularGroup
