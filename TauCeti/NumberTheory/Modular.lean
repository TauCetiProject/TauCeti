/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
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
* `ModularGroup.sl_smul_set`: the `SL(2, ℤ)`-action on subsets of `ℍ` is the `GL(2, ℝ)`-action
  along the coercion.
* `ModularGroup.isOpen_smul_fdo` and `ModularGroup.disjoint_smul_fdo`: the translates of the
  open fundamental domain are open, and two of them are disjoint unless the translating
  elements differ by a sign.
* `ModularGroup.isFundamentalDomain_fdo`: `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)` acting
  on `ℍ` with the invariant measure.
* `ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo`: the coset tiling of `𝒟ᵒ` is a
  fundamental domain for a subgroup of `PSL(2, ℤ)` with countable coset space.

Split out of the Petersson inner-product development ported from the AINTLIB
`LeanModularForms` project
(<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>,
`Modularforms/PeterssonInnerProduct.lean`, Chris Birkbeck).

The section on translates of `𝒟ᵒ` was developed in Tau Ceti and has no counterpart in that
AINTLIB source. The two fundamental-domain statements do have counterparts there, both in the
same project: `ModularGroup.isFundamentalDomain_fdo` restates `isFundamentalDomain_fdo_PSL`
(`Modularforms/PSL2Action.lean`), and `ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo`
is the arbitrary-subgroup form of `isFundamentalDomain_Gamma1_PSL`
(`Modularforms/PeterssonLevelN.lean`), which states the tiling for the image of `Γ₁(N)`. Both are
restated for Mathlib's `volume : Measure ℍ` in place of that project's own hyperbolic measure.
The proofs are shorter here, resting on `ModularGroup.disjoint_smul_fdo`,
`Matrix.SpecialLinearGroup.pslMk_eq_one_iff` and the coset-tiling transport of
`TauCeti/MeasureTheory/Group/FundamentalDomain.lean`, which Tau Ceti already had.
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

/-- **The `SL(2, ℤ)`-action on subsets of `ℍ` is the `GL(2, ℝ)`-action along the coercion**, the
pointwise-image counterpart of `ModularGroup.sl_moeb`. This is useful as a rewrite even though
the two actions are definitionally equal. -/
@[simp]
theorem sl_smul_set (γ : SL(2, ℤ)) (S : Set ℍ) : γ • S = (γ : GL (Fin 2) ℝ) • S := (rfl)

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
    -- `simp` takes `(γ : PSL(2, ℤ)) = 1` to `γ = ±1` through `QuotientGroup.eq_one_iff`
    -- and `Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one`
    have hne : ¬ (γ = 1 ∨ γ = -1) := fun h ↦ hγ (by simpa using h)
    rw [pslMk_smul_set]
    refine Disjoint.aedisjoint (Disjoint.symm ?_)
    simpa using disjoint_smul_fdo (γ := 1) (δ := γ) (by simpa using fun h ↦ hne (Or.inl h))
      (by simpa using fun h ↦ hne (Or.inr h))

/-- **A fundamental domain for a subgroup of `PSL(2, ℤ)`**: the union of the `[PSL(2, ℤ) : H]`
translates `(q.out)⁻¹ • 𝒟ᵒ`, one for each coset `q ∈ PSL(2, ℤ) ⧸ H`, is a fundamental domain for
`H` acting on `ℍ` with the invariant measure. The coset space is countable at finite index, so
this covers every congruence subgroup, and it is the domain a Petersson product at level `N` is
an integral over. -/
theorem isFundamentalDomain_iUnion_out_inv_smul_fdo (H : Subgroup PSL(2, ℤ))
    [Countable (PSL(2, ℤ) ⧸ H)] :
    MeasureTheory.IsFundamentalDomain H
      (⋃ q : PSL(2, ℤ) ⧸ H, ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ)) volume :=
  isFundamentalDomain_fdo.subgroup_iUnion_out_inv_smul H

end ModularGroup
