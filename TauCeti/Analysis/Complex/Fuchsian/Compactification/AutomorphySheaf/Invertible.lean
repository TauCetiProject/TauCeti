/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalBasis
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.AutomorphySheaf.Basic
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Automorphy.Section
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.NumberTheory.ModularForms.Basic
import TauCeti.Topology.MetricSpace.ProperlyDiscontinuous

/-!
# The weight-`k` automorphy sheaf is invertible

Let `Γ ≤ PSL(2, ℝ)` be discrete and let `Γ' ≤ SL(2, ℝ)` have image `Γ`. This file proves that the
weight-`k` automorphy sheaf `Subgroup.CompactifiedQuotient.automorphySheafOfModules` of `Γ'` on the
compactified quotient `X(Γ)` is invertible, that is, locally free of rank one over the holomorphic
structure sheaf, as soon as the ineffective stabilizer acts trivially: `k` is even or `-1 ∉ Γ'`
(`Subgroup.CompactifiedQuotient.isInvertible_automorphySheafOfModules`). When `-1 ∈ Γ'` and `k` is
odd the sheaf is zero (`Subgroup.CompactifiedQuotient.IsAutomorphySection.eq_zero_of_neg_one_mem`),
and no rank-one descent is asserted.

The trivializations are built by explicit local descent, chart by chart of `X(Γ)`:

* At the orbit of a point `z` of `ℍ`, on a precisely invariant disc whose local orbit space is a
  chart, the chart is the local quotient coordinate `w = u ^ m` of the disc coordinate `u` at `z`,
  where `m` is the order of the stabilizer of `z`. The frame is the automorphic extension
  (`Subgroup.automorphyExtension`) of `(τ - conj z) ^ (-k) * u ^ r`, where `0 ≤ r < m` and
  `denom g z ^ (2 * r + k) = 1` for the lifts `g ∈ Γ'` of the stabilizer
  (`Subgroup.exists_lt_forall_denom_zpow_eq_one`). The invariant sections are the frame times the
  holomorphic functions of `w`
  (`Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent_of_mem`). For `r ≠ 0` the
  frame vanishes on the orbit of `z`, and a section is still determined there by continuity.
* At a cusp orbit, represented by a cusp datum `D`, the chart is the cusp coordinate `q`, and the
  frame is the automorphic extension of `denom s τ ^ (-k) * q₂ ^ r` in the width parameter `q₂`,
  with `q₂ ^ 2 = q`, where `r < 2` is fixed by the sign condition
  (`TauCeti.Subgroup.CuspDatum.exists_lt_two_forall_zpow_eq_neg_one_pow`). So `r = 1` exactly at an
  irregular cusp in odd weight: the order of a section there is `1 / 2` plus the order of its
  coefficient, the order convention of the Diamond–Shurman errata. The sections are the frame times
  the holomorphic functions of `q`; holomorphy of the coefficient at `q = 0` comes from boundedness
  at the cusp (`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent`).

In each chart every local section over an open subset is the frame times a unique holomorphic
function on that subset, which is the local basis criterion
`TauCeti.SheafOfModules.IsInvertible.of_bijective_smul`.

## Main declarations

* `Subgroup.CompactifiedQuotient.isInvertible_automorphySheafOfModules`: the weight-`k` automorphy
  sheaf is invertible.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3–2.4 and 3.1–3.6, with the corrected irregular-cusp order
  convention of the errata to pp. 74–75.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§2.1, 2.6.
-/

public noncomputable section

open CategoryTheory Filter Metric MulAction Opposite Set TopologicalSpace Topology UpperHalfPlane
open scoped ComplexConjugate ContDiff Manifold MatrixGroups ModularForm Pointwise
open TauCeti (holomorphicStructureSheaf)

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} {Γ' : _root_.Subgroup SL(2, ℝ)} {k : ℤ}

/-! ### Automorphic extensions over saturations -/

section Extension

variable {W : Set ℍ} {F₀ : ℍ → ℂ}

/-- The automorphic extension of a compatible holomorphic function `F₀` on an open set `W ⊆ ℍ` is
a local section over every subset `U` of the compactified quotient whose preimage in `ℍ` is the
saturation of `W`, as soon as it is bounded at the cusps in `U`. -/
private theorem isAutomorphySection_automorphyExtension (hW : IsOpen W)
    (hF₀ : ∀ g ∈ Γ', ∀ σ ∈ W, g • σ ∈ W →
      F₀ (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F₀ σ)
    (hF₀d : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F₀ W) {U : Set Γ.CompactifiedQuotient}
    (hU : ∀ τ : ℍ, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U ↔ τ ∈ (Γ' : Set SL(2, ℝ)) • W)
    (hb : ∀ D : Γ.CuspDatum, ofCusp D.cuspOrbit ∈ U →
      OnePoint.IsBoundedAt D.cusp (Γ'.automorphyExtension W k F₀) k) :
    IsAutomorphySection Γ' k U (Γ'.automorphyExtension W k F₀) where
  eq_zero_of_notMem τ hτ := automorphyExtension_of_notMem ((hU τ).not.mp hτ)
  apply_smul _ hg τ := automorphyExtension_smul hF₀ hg τ
  mdifferentiableAt τ hτ := (mdifferentiableOn_automorphyExtension hF₀ hW hF₀d).mdifferentiableAt
    (hW.smul_left.mem_nhds ((hU τ).mp hτ))
  isBoundedAt := hb

/-- If a local section `G` over `V ⊆ U` is `c` times `F₀` on the points of `W` over `V`, then it is
`c` times the automorphic extension of `F₀` on the whole preimage of `V`. -/
private theorem eq_mul_automorphyExtension
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) ≤ Γ)
    (hF₀ : ∀ g ∈ Γ', ∀ σ ∈ W, g • σ ∈ W →
      F₀ (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F₀ σ)
    {U V : Set Γ.CompactifiedQuotient}
    (hU : ∀ τ : ℍ, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ U ↔ τ ∈ (Γ' : Set SL(2, ℝ)) • W)
    (hVU : V ⊆ U) {G : ℍ → ℂ} (hG : IsAutomorphySection Γ' k V G)
    {c : Γ.CompactifiedQuotient → ℂ}
    (h : ∀ σ ∈ W, ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ) ∈ V →
      G σ = c (ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ)) * F₀ σ)
    {τ : ℍ} (hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ V) :
    G τ = c (ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) * Γ'.automorphyExtension W k F₀ τ := by
  obtain ⟨g, hg, hgτ⟩ :=
    _root_.Subgroup.mem_smul_set_iff_exists_smul_mem.mp ((hU τ).mp (hVU hτ))
  have hπ := ofQuotient_quotientMk_smul hΓ hg τ
  have hlaw := hG.apply_smul g hg τ
  rw [h _ hgτ (hπ ▸ hτ), hπ] at hlaw
  rw [automorphyExtension_eq hF₀ hg hgτ]
  linear_combination (-(denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ (-k))) * hlaw -
    G τ * zpow_neg_mul_zpow_self k (denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) τ)

end Extension

/-! ### The charts of the compactified quotient as saturations -/

section Charts

/-- The preimage in `ℍ` of a cusp neighbourhood of `X(Γ)` is the saturation of the horodisc under
`Γ'`. -/
private theorem ofQuotient_mem_cuspNhd_iff_mem_smul_horodisc
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ) (D : Γ.CuspDatum)
    (A : ℝ) (τ : ℍ) :
    ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ cuspNhd D A ↔
      τ ∈ (Γ' : Set SL(2, ℝ)) • TauCeti.Subgroup.CuspDatum.horodisc D A := by
  rw [ofQuotient_mem_cuspNhd_iff, ← exists_smul_mem_iff_mem_smul_set_of_map_eq hΓ]
  refine ⟨fun ⟨σ, hσ, hστ⟩ ↦ ?_, fun ⟨γ, hγ⟩ ↦
    ⟨γ • τ, hγ, Quotient.sound (orbitRel_apply.mpr (mem_orbit τ γ))⟩⟩
  obtain ⟨γ, hγ⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hστ))
  exact ⟨γ, hγ ▸ hσ⟩

/-- Every point of a cusp neighbourhood of `X(Γ)` other than the cusp orbit is the orbit of a
point of the horodisc. -/
private theorem exists_mem_horodisc_of_mem_cuspNhd {D : Γ.CuspDatum} {A : ℝ}
    {y : Γ.CompactifiedQuotient} (hy : y ∈ cuspNhd D A) (hyD : y ≠ ofCusp D.cuspOrbit) :
    ∃ σ ∈ TauCeti.Subgroup.CuspDatum.horodisc D A,
      ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ) = y := by
  cases y with
  | ofCusp C' => exact absurd (by rw [(ofCusp_mem_cuspNhd_iff D _).mp hy]) hyD
  | ofQuotient p =>
    obtain ⟨σ, hσ, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D _).mp hy
    exact ⟨σ, hσ, rfl⟩

/-- The automorphic extension of the frame at a cusp from the horodisc of height the width is
bounded at the cusp, where it agrees with the frame. -/
private theorem isBoundedAt_automorphyExtension_automorphyFrame {D : Γ.CuspDatum} {s : SL(2, ℝ)}
    {r : ℕ} (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hF₀ : ∀ g ∈ Γ', ∀ σ ∈ TauCeti.Subgroup.CuspDatum.horodisc D D.width,
      g • σ ∈ TauCeti.Subgroup.CuspDatum.horodisc D D.width →
        TauCeti.Subgroup.CuspDatum.automorphyFrame D s k r (g • σ) =
          denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k *
            TauCeti.Subgroup.CuspDatum.automorphyFrame D s k r σ) :
    OnePoint.IsBoundedAt D.cusp (Γ'.automorphyExtension
      (TauCeti.Subgroup.CuspDatum.horodisc D D.width) k
        (TauCeti.Subgroup.CuspDatum.automorphyFrame D s k r)) k := by
  rw [OnePoint.isBoundedAt_iff (CuspDatum.mapGL_inv_smul_infty hs)]
  refine (TauCeti.Subgroup.CuspDatum.isBoundedAtImInfty_slash_automorphySection (k := k) (r := r)
    hs (continuousAt_const (y := (1 : ℂ)))).congr' ?_ EventuallyEq.rfl
  filter_upwards [(atImInfty_mem {z : ℍ | D.width < z.im}).mpr
    ⟨D.width + 1, fun z hz ↦ by
      simp only [Set.mem_ofPred_eq]
      linarith⟩] with z hz
  have hmem : s⁻¹ • z ∈ TauCeti.Subgroup.CuspDatum.horodisc D D.width := by
    rwa [TauCeti.Subgroup.CuspDatum.mem_horodisc, ← hs, pslMk_smul, smul_inv_smul]
  rw [ModularForm.slash_apply, ModularForm.slash_apply, Matrix.SpecialLinearGroup.mapGL_smul,
    automorphyExtension_of_mem hF₀ hmem, TauCeti.Subgroup.CuspDatum.automorphySection_def,
    mul_one]

variable [DiscreteTopology Γ]

/-- A radius at which the disc about `z` is precisely invariant under `Γ` and its local orbit
space is a chart of the coarse quotient. -/
private theorem exists_pos_isOpenEmbedding_and_smul_eq_self (Γ : Subgroup PSL(2, ℝ))
    [DiscreteTopology Γ] (z : ℍ) :
    ∃ ε > 0, IsOpenEmbedding (stabilizerBall Γ z ε).orbitRelQuotientMap ∧
      ∀ g : Γ, ((fun x ↦ g • x) '' ball z ε ∩ ball z ε).Nonempty → g • z = z := by
  obtain ⟨ε, h, hε⟩ := ((eventually_isOpenEmbedding_orbitRelQuotientMap_stabilizerBall Γ z).and
    (TauCeti.eventually_smul_eq_self_of_image_smul_ball_inter_nonempty Γ z)).and
      self_mem_nhdsWithin |>.exists
  exact ⟨ε, hε, h⟩

/-- The preimage in `ℍ` of the chart of `X(Γ)` given by the local orbit space of a disc is the
saturation of the disc under `Γ'`. -/
private theorem ofQuotient_mem_ofQuotientChart_source_iff_mem_smul_ball
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ) {z : ℍ} {ε : ℝ}
    [Finite (stabilizer Γ z)] (hε : 0 < ε)
    (hopen : IsOpenEmbedding (stabilizerBall Γ z ε).orbitRelQuotientMap) (τ : ℍ) :
    ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈
        (ofQuotientChart (stabilizerBallQuotientChart hε hopen)).source ↔
      τ ∈ (Γ' : Set SL(2, ℝ)) • ball z ε := by
  rw [ofQuotient_mem_ofQuotientChart_source_iff, mem_stabilizerBallQuotientChart_source_iff,
    ← exists_smul_mem_iff_mem_smul_set_of_map_eq hΓ]
  simp only [mem_ball]

/-- Every point of the chart of `X(Γ)` given by the local orbit space of a disc is the orbit of a
point of the disc. -/
private theorem exists_mem_ball_of_mem_ofQuotientChart_source {z : ℍ} {ε : ℝ}
    [Finite (stabilizer Γ z)] (hε : 0 < ε)
    (hopen : IsOpenEmbedding (stabilizerBall Γ z ε).orbitRelQuotientMap)
    {y : Γ.CompactifiedQuotient}
    (hy : y ∈ (ofQuotientChart (stabilizerBallQuotientChart hε hopen)).source) :
    ∃ σ ∈ ball z ε, ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ) = y := by
  rw [ofQuotientChart_source] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  induction q using Quotient.inductionOn with | h τ => ?_
  obtain ⟨g, hg⟩ := (mem_stabilizerBallQuotientChart_source_iff hε hopen).mp hq
  exact ⟨g • τ, mem_ball.mpr hg,
    congrArg ofQuotient (Quotient.sound (orbitRel_apply.mpr (mem_orbit τ g)))⟩

end Charts

/-! ### Local frames are local bases -/

variable [DiscreteTopology Γ]

/-- The data of a local frame of the automorphy sheaf about `x`, in the form consumed by
`bijective_smul_map`. -/
private def HasLocalFrame (Γ' : _root_.Subgroup SL(2, ℝ)) (k : ℤ) (x : Γ.CompactifiedQuotient) :
    Prop :=
  ∃ (U : Opens Γ.CompactifiedQuotient) (e : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ)
    (F : ℍ → ℂ) (x₀ : Γ.CompactifiedQuotient), x ∈ U ∧ e ∈ atlas ℂ Γ.CompactifiedQuotient ∧
    (U : Set Γ.CompactifiedQuotient) ⊆ e.source ∧
    IsAutomorphySection Γ' k (U : Set Γ.CompactifiedQuotient) F ∧
    (∀ y ∈ U, y ≠ x₀ → ∃ τ : ℍ, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) = y ∧ F τ ≠ 0) ∧
    ∀ V : Opens Γ.CompactifiedQuotient, V ≤ U → ∀ G : ℍ → ℂ,
      IsAutomorphySection Γ' k (V : Set Γ.CompactifiedQuotient) G →
      ∃ c : ℂ → ℂ, (∀ y ∈ V, DifferentiableAt ℂ c (e y)) ∧
        ∀ τ : ℍ, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ V →
          G τ = c (e (ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ))) * F τ

/-- **A local frame is a local basis.** Let `e` be a chart of the compactified quotient whose
source contains the open set `U`, and let `F` be a local section over `U` such that every point of
`U` other than `x₀` is the orbit of a point of `ℍ` at which `F` does not vanish. Suppose every local
section `G` over an open `V ⊆ U` is `F` times a coefficient `c ∘ e`, a function of the point of the
compactified quotient read in the chart `e`, with `c` holomorphic on `e '' V`. Then over every open
`V ⊆ U` every local section is a unique multiple of the restriction of `F` by a holomorphic
function on `V`. -/
private theorem bijective_smul_map
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) ≤ Γ)
    {e : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ} (he : e ∈ atlas ℂ Γ.CompactifiedQuotient)
    {U : Opens Γ.CompactifiedQuotient}
    (hUe : (U : Set Γ.CompactifiedQuotient) ⊆ e.source) {F : ℍ → ℂ}
    (hF : IsAutomorphySection Γ' k (U : Set Γ.CompactifiedQuotient) F)
    {x₀ : Γ.CompactifiedQuotient}
    (hF0 : ∀ y ∈ U, y ≠ x₀ → ∃ τ : ℍ, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) = y ∧ F τ ≠ 0)
    (hcoef : ∀ V : Opens Γ.CompactifiedQuotient, V ≤ U → ∀ G : ℍ → ℂ,
      IsAutomorphySection Γ' k (V : Set Γ.CompactifiedQuotient) G →
      ∃ c : ℂ → ℂ, (∀ y ∈ V, DifferentiableAt ℂ c (e y)) ∧
        ∀ τ : ℍ, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ V →
          G τ = c (e (ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ))) * F τ)
    {V : Opens Γ.CompactifiedQuotient} (f : V ⟶ U) :
    Function.Bijective fun φ : ((sheafCompose (Opens.grothendieckTopology (TopCat.of
        Γ.CompactifiedQuotient)) (forget₂ CommRingCat RingCat)).obj
          (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient)).obj.obj (op V) ↦
      φ • (automorphySheafOfModules hΓ k).val.map f.op
        ((automorphySheafOfModulesSectionsEquiv hΓ k U).symm
          ⟨F, mem_automorphySections_iff.mpr hF⟩) := by
  set s := (automorphySheafOfModulesSectionsEquiv hΓ k U).symm
    ⟨F, mem_automorphySections_iff.mpr hF⟩
  -- on the preimage of `V`, a multiple of the restricted frame is the function times `F`
  have hval (φ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op V)) {τ : ℍ}
      (hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ V) :
      (automorphySheafOfModulesSectionsEquiv hΓ k V
        (φ • (automorphySheafOfModules hΓ k).val.map f.op s) : ℍ → ℂ) τ = φ ⟨_, hτ⟩ * F τ := by
    refine (automorphySheafOfModulesSectionsEquiv_smul_apply hΓ k φ
      ((automorphySheafOfModules hΓ k).val.map f.op s) hτ).trans ?_
    rw [automorphySheafOfModulesSectionsEquiv_map, AddEquiv.apply_symm_apply,
      indicator_of_mem (mem_preimage.2 hτ : τ ∈ _)]
  refine ⟨fun (φ₁ φ₂ : (holomorphicStructureSheaf 𝓘(ℂ) Γ.CompactifiedQuotient).obj.obj (op V)) h ↦
    ?_, fun t ↦ ?_⟩
  · -- away from `x₀` the frame does not vanish, so the coefficients agree there
    have hpt (y : V) (hy : (y : Γ.CompactifiedQuotient) ≠ x₀) : φ₁ y = φ₂ y := by
      obtain ⟨τ, hτy, hFτ⟩ := hF0 y (f.le y.property) hy
      have hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ V := hτy ▸ y.property
      have h' := congrArg (fun t ↦ (automorphySheafOfModulesSectionsEquiv hΓ k V t : ℍ → ℂ) τ) h
      have hy' : y = ⟨_, hτ⟩ := Subtype.ext hτy.symm
      simp only at h'
      rw [hval φ₁ hτ, hval φ₂ hτ] at h'
      rw [hy']
      exact mul_right_cancel₀ hFτ h'
    -- at `x₀` they agree by continuity, since `x₀` is not isolated
    have : PerfectSpace V := ChartedSpace.perfectSpace (H := ℂ)
    refine TauCeti.holomorphicStructureSheaf.ext fun y ↦ ?_
    by_cases hx₀ : x₀ ∈ V
    · exact congrFun ((TauCeti.holomorphicStructureSheaf.contMDiff φ₁).continuous.ext_on
        (dense_compl_singleton (⟨x₀, hx₀⟩ : V))
        (TauCeti.holomorphicStructureSheaf.contMDiff φ₂).continuous
        fun y hy ↦ hpt y fun h ↦ hy (Subtype.ext h)) y
    · exact hpt y fun h ↦ hx₀ (h ▸ y.property)
  · -- the coefficient of a section, read in the chart, is a holomorphic function on `V`
    set G : ℍ → ℂ := (automorphySheafOfModulesSectionsEquiv hΓ k V t : ℍ → ℂ)
    have hG : IsAutomorphySection Γ' k (V : Set Γ.CompactifiedQuotient) G :=
      mem_automorphySections_iff.mp (automorphySheafOfModulesSectionsEquiv hΓ k V t).property
    obtain ⟨c, hcd, hc⟩ := hcoef V f.le G hG
    have hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun y : V ↦ c (e y) := fun y ↦
      ((hcd y y.property).comp_mdifferentiableAt
        (mdifferentiableAt_atlas he (hUe (f.le y.property)))).comp y
        ((contMDiff_subtypeVal (n := 1)).mdifferentiable one_ne_zero y)
    refine ⟨TauCeti.holomorphicStructureSheaf.ofMDifferentiable _ hφ,
      (automorphySheafOfModulesSectionsEquiv hΓ k V).injective
        (Subtype.ext (funext fun τ ↦ ?_))⟩
    by_cases hτ : ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ V
    · rw [hval _ hτ, TauCeti.holomorphicStructureSheaf.ofMDifferentiable_apply, ← hc τ hτ]
    · exact ((mem_automorphySections_iff.mp
        (automorphySheafOfModulesSectionsEquiv hΓ k V _).property).eq_zero_of_notMem τ hτ).trans
          (hG.eq_zero_of_notMem τ hτ).symm

/-! ### The local frames at points and at cusps -/

/-- **Local frames by automorphic extension.** Let `e` be a chart of `X(Γ)` about `x` whose source
has as preimage in `ℍ` the saturation of an open set `W`, and let `F₀` be holomorphic on `W` and
compatible with the weight-`k` action of `Γ'`, with automorphic extension bounded at the cusps in
the source. Suppose every point of the source other than `x₀` is the orbit of a point of `W` at
which `F₀` does not vanish, and every local section over an open subset `V` of the source is, on
the points of `W` over `V`, a coefficient holomorphic in the chart times `F₀`. Then the automorphic
extension of `F₀` is a local frame about `x`. -/
private theorem hasLocalFrame_of_automorphyExtension
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) ≤ Γ)
    {x x₀ : Γ.CompactifiedQuotient} {e : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ}
    (he : e ∈ atlas ℂ Γ.CompactifiedQuotient) (hx : x ∈ e.source) {W : Set ℍ} (hW : IsOpen W)
    {F₀ : ℍ → ℂ} (hF₀ : ∀ g ∈ Γ', ∀ σ ∈ W, g • σ ∈ W →
      F₀ (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F₀ σ)
    (hF₀d : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F₀ W)
    (hU : ∀ τ : ℍ, ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ) ∈ e.source ↔
      τ ∈ (Γ' : Set SL(2, ℝ)) • W)
    (hb : ∀ D : Γ.CuspDatum, ofCusp D.cuspOrbit ∈ e.source →
      OnePoint.IsBoundedAt D.cusp (Γ'.automorphyExtension W k F₀) k)
    (hF0 : ∀ y ∈ e.source, y ≠ x₀ →
      ∃ σ ∈ W, ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ) = y ∧ F₀ σ ≠ 0)
    (hcoef : ∀ V : Opens Γ.CompactifiedQuotient, (V : Set Γ.CompactifiedQuotient) ⊆ e.source →
      ∀ G : ℍ → ℂ, IsAutomorphySection Γ' k (V : Set Γ.CompactifiedQuotient) G →
      ∃ c : ℂ → ℂ, (∀ y ∈ V, DifferentiableAt ℂ c (e y)) ∧
        ∀ σ ∈ W, ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ) ∈ V →
          G σ = c (e (ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ))) * F₀ σ) :
    HasLocalFrame Γ' k x := by
  refine ⟨⟨e.source, e.open_source⟩, e, _, x₀, hx, he, subset_rfl,
    isAutomorphySection_automorphyExtension hW hF₀ hF₀d hU hb, fun y hy hyx ↦ ?_,
    fun V hVU G hG ↦ ?_⟩
  · obtain ⟨σ, hσ, rfl, hσ0⟩ := hF0 y hy hyx
    exact ⟨σ, rfl, by rwa [automorphyExtension_of_mem hF₀ hσ]⟩
  · obtain ⟨c, hcd, hc⟩ := hcoef V hVU G hG
    exact ⟨c, hcd, fun τ hτ ↦
      eq_mul_automorphyExtension hΓ hF₀ hU hVU hG (c := fun y ↦ c (e y)) hc hτ⟩

/-- **The local frame at a point of the coarse quotient.** About the orbit of `z ∈ ℍ`, on a
precisely invariant disc whose local orbit space is a chart, the automorphic extension of the frame
`(τ - conj z) ^ (-k) * u ^ r` of the disc coordinate `u` is a local frame: it vanishes at most on
the orbit of `z`, and the coefficient of a section with respect to it is its descent through
`u ↦ u ^ m`, a holomorphic function of the chart. -/
private theorem hasLocalFrame_ofQuotient
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ)
    (hk : -1 ∈ Γ' → Even k) (p : orbitRel.Quotient Γ ℍ) : HasLocalFrame Γ' k (ofQuotient p) := by
  induction p using Quotient.inductionOn with | h z => ?_
  have : Finite (stabilizer Γ z) := (ProperlyDiscontinuousSMul.finite_stabilizer z).to_subtype
  obtain ⟨ε, hε, hopen, hsep⟩ := exists_pos_isOpenEmbedding_and_smul_eq_self Γ z
  let ψ : Γ.LinearizingCoordinate z ε := LinearizingCoordinate.discCoordinate hε
  obtain ⟨r, hr, hkr⟩ := exists_lt_forall_denom_zpow_eq_one hΓ.le hk (z := z)
  set e := ofQuotientChart (stabilizerBallQuotientChart hε hopen)
  have hU := ofQuotient_mem_ofQuotientChart_source_iff_mem_smul_ball (Γ' := Γ') hΓ hε hopen
  have hσ' {σ : ℍ} (hσ : σ ∈ ball z ε) : σ ∈ stabilizerBall Γ z ε :=
    (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hσ)
  -- the chart reads the orbit of a point of the disc as its quotient coordinate
  have hchart (σ : ℍ) (hσ : σ ∈ ball z ε) :
      e (ofQuotient (Quotient.mk (orbitRel Γ ℍ) σ)) = ψ.quotientCoordinate ⟨σ, hσ' hσ⟩ := by
    rw [ofQuotientChart_ofQuotient, stabilizerBallQuotientChart_mk hε hopen (mem_ball.mp hσ),
      LinearizingCoordinate.quotientCoordinate_discCoordinate]
  have hF₀ := ψ.automorphyFrame_compatible hΓ.le hkr fun g hg σ hσ hgσ ↦
    hsep ⟨g, hΓ ▸ mem_map_of_mem _ hg⟩ ⟨g • σ, ⟨σ, hσ, rfl⟩, hgσ⟩
  have hframe (σ : ℍ) (hσ : σ ∈ ball z ε) :
      ((σ : ℂ) - conj (z : ℂ)) ^ (-k) * ψ.toEquiv (UpperHalfPlane.discCoordinate z σ) ^ r =
        ψ.automorphyFrame k r ⟨σ, hσ' hσ⟩ :=
    (ψ.automorphyFrame_eq_toEquiv_discCoordinate k r ⟨σ, hσ' hσ⟩).symm
  refine hasLocalFrame_of_automorphyExtension hΓ.le (x₀ := ofQuotient (Quotient.mk _ z))
    (ofQuotientChart_mem_atlas (stabilizerBallQuotientChart_mem_atlas Γ hε hopen))
    ((hU z).mpr (_root_.Subgroup.mem_smul_set_iff_exists_smul_mem.mpr
      ⟨1, Γ'.one_mem, by rw [one_smul]; exact mem_ball_self hε⟩))
    isOpen_ball hF₀ (ψ.mdifferentiableOn_automorphyFrame k r) hU (fun D hD ↦ ?_)
    (fun y hy hyz ↦ ?_) fun V hVU G hG ↦ ?_
  · -- the chart contains no cusp
    rw [ofQuotientChart_source] at hD
    obtain ⟨q, -, h⟩ := hD
    cases h
  · -- the frame vanishes at most at the centre
    obtain ⟨σ, hσ, rfl⟩ := exists_mem_ball_of_mem_ofQuotientChart_source hε hopen hy
    refine ⟨σ, hσ, rfl, ?_⟩
    rw [hframe σ hσ, Ne, LinearizingCoordinate.automorphyFrame_eq_zero_iff]
    exact fun h ↦ hyz (congrArg (fun τ : ℍ ↦ ofQuotient (Quotient.mk _ τ))
      h.1)
  · -- the coefficient of a section is its descent, holomorphic in the chart
    have hVo : IsOpen ((fun τ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) ⁻¹' V) :=
      (continuous_ofQuotient.comp continuous_quotient_mk').isOpen_preimage
        (V : Set Γ.CompactifiedQuotient) V.isOpen
    have hf (g : SL(2, ℝ)) (hg : g ∈ Γ') (_ : g • z = z) (τ : ℍ) (_ : τ ∈ ball z ε ∩
        (fun τ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) ⁻¹' V) :
        G (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * G τ :=
      hG.apply_smul g hg τ
    have hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) G
        (ball z ε ∩ (fun τ : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) τ)) ⁻¹' V) :=
      fun τ hτ ↦ (hG.mdifferentiableAt τ hτ.2).mdifferentiableWithinAt
    refine ⟨ψ.automorphyDescent k r G, fun y hy ↦ ?_, fun σ hσ hσV ↦ ?_⟩
    · obtain ⟨σ, hσ, rfl⟩ := exists_mem_ball_of_mem_ofQuotientChart_source hε hopen (hVU hy)
      rw [hchart σ hσ]
      exact ψ.differentiableAt_automorphyDescent hΓ.ge hkr hVo hf hfd hr.le hy
    · rw [hchart σ hσ, hframe σ hσ, mul_comm]
      exact (ψ.automorphyFrame_mul_automorphyDescent_of_mem hΓ.ge hkr hVo hf hfd hr
        (τ := ⟨σ, hσ' hσ⟩) hσV).symm

/-- **The coefficient of a section at a cusp is holomorphic at the cusp.** If `G` is a local
section over a neighbourhood `V` of the cusp orbit of `D`, its coefficient with respect to the frame
at the cusp is holomorphic at `q = 0`: on a high horodisc `G` is holomorphic and it is bounded at
the cusp, so the singularity at the cusp is removable. -/
private theorem differentiableAt_automorphyDescent_zero {D : Γ.CuspDatum} {s g : SL(2, ℝ)}
    {r : ℕ} (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r) (hr : r < 2) (hgΓ : g ∈ Γ')
    {V : Opens Γ.CompactifiedQuotient} (hV : ofCusp D.cuspOrbit ∈ V) {G : ℍ → ℂ}
    (hG : IsAutomorphySection Γ' k (V : Set Γ.CompactifiedQuotient) G) :
    DifferentiableAt ℂ (TauCeti.Subgroup.CuspDatum.automorphyDescent D s k r G) 0 := by
  obtain ⟨A, hA⟩ := (mem_nhds_ofCusp_iff D).mp (V.isOpen.mem_nhds hV)
  have hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) G (TauCeti.Subgroup.CuspDatum.horodisc D (max A 0)) :=
    fun σ hσ ↦ (hG.mdifferentiableAt σ (hA ((ofQuotient_mem_cuspNhd_iff D A).mpr
      ⟨σ, TauCeti.Subgroup.CuspDatum.horodisc_antitone D (le_max_left A 0) hσ, rfl⟩)))
        |>.mdifferentiableWithinAt
  exact (TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent hs hg hk
    (fun τ _ ↦ hG.apply_smul g hgΓ τ) hfd ((OnePoint.isBoundedAt_iff
      (CuspDatum.mapGL_inv_smul_infty hs)).mp (hG.isBoundedAt D hV)) (le_max_right A 0)
        hr.le).differentiableAt (ball_mem_nhds 0 (Real.exp_pos _))

/-- **The local frame at a cusp.** About the cusp orbit of a cusp datum `D`, with the horodisc of
height the width of `D`, the automorphic extension of the frame `denom s τ ^ (-k) * q₂ ^ r` in the
width parameter `q₂` is a local frame: it vanishes nowhere on `ℍ`, it is bounded at the cusp, and
the coefficient of a section with respect to it is its descent through `q₂ ↦ q₂ ^ 2`, a holomorphic
function of the cusp coordinate `q`, also at `q = 0`. -/
private theorem hasLocalFrame_ofCusp
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ)
    (hk : -1 ∈ Γ' → Even k) (C : Γ.CuspOrbit) : HasLocalFrame Γ' k (ofCusp C) := by
  set D := C.cuspDatum
  have hA : D.width ≤ D.width := le_rfl
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective D.scaling
  obtain ⟨r, hr, hkr⟩ :=
    TauCeti.Subgroup.CuspDatum.exists_lt_two_forall_zpow_eq_neg_one_pow hs hk
  obtain ⟨g₀, hg₀, hg₀gen⟩ := _root_.Subgroup.mem_map.mp (hΓ.symm ▸ D.generator.property :
    (D.generator : PSL(2, ℝ)) ∈ Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))))
  have hg₀gen' : (g₀ : PSL(2, ℝ)) = D.generator := hg₀gen
  have hkr₀ := hkr g₀ hg₀ hg₀gen'
  have hF₀ := TauCeti.Subgroup.CuspDatum.automorphyFrame_compatible hΓ hs hkr
    fun g hg σ hσ hgσ ↦ TauCeti.Subgroup.CuspDatum.smul_cusp_eq_of_mem_horodisc_of_smul_mem_horodisc
      D hΓ.le hA hg hσ hgσ
  refine hasLocalFrame_of_automorphyExtension hΓ.le (x₀ := ofCusp D.cuspOrbit)
    (cuspChart_mem_atlas D hA)
    (by rw [cuspChart_source, ← C.cuspOrbit_cuspDatum]; exact ofCusp_mem_cuspNhd D _)
    (TauCeti.Subgroup.CuspDatum.isOpen_horodisc D _) hF₀
    (TauCeti.Subgroup.CuspDatum.mdifferentiable_automorphyFrame D s k r).mdifferentiableOn
    (by rw [cuspChart_source]; exact ofQuotient_mem_cuspNhd_iff_mem_smul_horodisc hΓ D D.width)
    (fun D' hD' ↦ ?_) (fun y hy hyD ↦ ?_) fun V hVU G hG ↦ ?_
  · -- the frame is bounded at the cusp
    rw [cuspChart_source, ofCusp_mem_cuspNhd_iff] at hD'
    exact CuspDatum.isBoundedAt_of_cuspOrbit_eq hΓ.ge
      (fun g hg τ ↦ automorphyExtension_smul hF₀ hg τ) hD'
      (isBoundedAt_automorphyExtension_automorphyFrame hs hF₀)
  · -- the frame vanishes nowhere on `ℍ`
    rw [cuspChart_source] at hy
    obtain ⟨σ, hσ, rfl⟩ := exists_mem_horodisc_of_mem_cuspNhd hy hyD
    exact ⟨σ, hσ, rfl, TauCeti.Subgroup.CuspDatum.automorphyFrame_ne_zero D s k r σ⟩
  · -- the coefficient of a section is its descent, holomorphic in the cusp coordinate
    rw [cuspChart_source] at hVU
    refine ⟨TauCeti.Subgroup.CuspDatum.automorphyDescent D s k r G, fun y hy ↦ ?_,
      fun σ hσ _ ↦ ?_⟩
    · by_cases hyD : y = ofCusp D.cuspOrbit
      · subst hyD
        rw [cuspChart_ofCusp]
        exact differentiableAt_automorphyDescent_zero hs hg₀gen' hkr₀ hr hg₀ hy hG
      · obtain ⟨σ, hσ, rfl⟩ := exists_mem_horodisc_of_mem_cuspNhd (hVU hy) hyD
        rw [cuspChart_ofQuotient_mk D hA hσ]
        exact TauCeti.Subgroup.CuspDatum.differentiableAt_automorphyDescent hs hg₀gen' hkr₀
          (fun τ _ ↦ hG.apply_smul g₀ hg₀ τ) hr.le hσ (hG.mdifferentiableAt σ hy)
    · rw [cuspChart_ofQuotient_mk D hA hσ, mul_comm]
      exact (TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent hs hg₀gen' hkr₀
        (fun τ _ ↦ hG.apply_smul g₀ hg₀ τ) hr hσ).symm

/-- **The weight-`k` automorphy sheaf is invertible.** Let `Γ ≤ PSL(2, ℝ)` be discrete and let
`Γ' ≤ SL(2, ℝ)` have image `Γ`. If the ineffective stabilizer acts trivially, that is, if `k` is
even or `-1 ∉ Γ'`, then the sheaf of local weight-`k` automorphic forms for `Γ'` on the compactified
quotient `X(Γ)` is locally free of rank one over its holomorphic structure sheaf. Near the orbit of
a point `z` of `ℍ` it is trivialized by the frame `(τ - conj z) ^ (-k) * u ^ r` in the disc
coordinate `u` at `z`, and near a cusp by the frame `denom s τ ^ (-k) * q₂ ^ r` in the width
parameter `q₂`, with the exponents `r` of `Subgroup.exists_lt_forall_denom_zpow_eq_one` and
`TauCeti.Subgroup.CuspDatum.exists_lt_two_forall_zpow_eq_neg_one_pow`. If instead `-1 ∈ Γ'` and `k`
is odd, the sheaf is zero
(`Subgroup.CompactifiedQuotient.IsAutomorphySection.eq_zero_of_neg_one_mem`). -/
theorem isInvertible_automorphySheafOfModules
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ)
    (hk : -1 ∈ Γ' → Even k) :
    TauCeti.SheafOfModules.IsInvertible (automorphySheafOfModules hΓ.le k) := by
  have hloc (x : Γ.CompactifiedQuotient) : HasLocalFrame Γ' k x := by
    cases x with
    | ofQuotient p => exact hasLocalFrame_ofQuotient hΓ hk p
    | ofCusp C => exact hasLocalFrame_ofCusp hΓ hk C
  choose U e F x₀ hxU he hUe hF hF0 hcoef using hloc
  exact TauCeti.SheafOfModules.IsInvertible.of_bijective_smul
    (M := automorphySheafOfModules hΓ.le k) U
    ((Opens.coversTop_iff _ U).mpr
      (IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩)))
    (fun x ↦ (automorphySheafOfModulesSectionsEquiv hΓ.le k (U x)).symm
      ⟨F x, mem_automorphySections_iff.mpr (hF x)⟩)
    fun x _ f ↦ bijective_smul_map hΓ.le (he x) (hUe x) (hF x) (hF0 x) (hcoef x) f

end Subgroup.CompactifiedQuotient
