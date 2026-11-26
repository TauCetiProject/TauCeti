/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure
public import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow
public import TauCeti.Geometry.Symplectic.Manifold.Volume
public import TauCeti.Geometry.Symplectic.Darboux.EuclideanBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The Liouville measure of a symplectic manifold

Let `σ` be a smooth two-form on a manifold `M` modelled on a space of dimension `2 * n`. The
**Liouville measure** of `σ` (`TauCeti.SmoothTwoForm.liouvilleMeasure σ n`) is the measure
`|σⁿ / n!|` of its symplectic volume form: in each chart it is Lebesgue measure weighted by the
absolute value of the coefficient of `σⁿ / n!`
(`TauCeti.SmoothTwoForm.liouvilleMeasure_apply_of_subset`), where `σⁿ / n!` is normalized to take
the value `1` on Darboux bases. The measure is built on the Borel `σ`-algebra of any Lindelöf
manifold, uses no orientation and no Riemannian metric, and allows boundary and corners.

The Liouville measure is locally finite, so it is a finite measure on a compact manifold. When `σ`
is nondegenerate, the volume form vanishes nowhere and every nonempty open set has positive
Liouville measure. If a differentiable homeomorphism `Φ` satisfies `Φ^* τ = σ`, then `Φ` carries
the Liouville measure of `σ` to that of `τ`; in particular symplectomorphisms preserve the
Liouville measure. Since Hamiltonian flows preserve a symplectic form, this gives
**Liouville's theorem**: the time-`t` maps of a complete Hamiltonian flow preserve the Liouville
measure
(`TauCeti.SmoothTwoForm.IsSymplectic.measurePreserving_globalFlowDiffeomorph_liouvilleMeasure`).

The Liouville measure is also natural for embeddings and rescalings. A differentiable measurable
embedding `f : M → N` between manifolds of the same dimension with `f^* τ = σ`, such as a symplectic
open embedding, carries the Liouville measure of `σ` to the restriction of that of `τ` to the
range of `f` (`MeasurableEmbedding.map_liouvilleMeasure`). In particular the
Liouville measure of the restriction of `σ` to an open subset `U` is the restriction of the
Liouville measure of `σ` to `U`
(`TauCeti.SmoothTwoForm.map_liouvilleMeasure_mpullback_subtypeVal`). Replacing `σ` by `r • σ`
multiplies the Liouville measure by `|r|ⁿ` (`TauCeti.SmoothTwoForm.liouvilleMeasure_smul`).

On a symplectic vector space `(V, σ)`, regarded as a manifold with the constant form `σ`, the
Liouville measure is the Haar measure normalized by any Darboux basis
(`TauCeti.SymplecticForm.liouvilleMeasure_constSmooth`). In particular the Liouville measure of
the standard form `Σ dq_i ∧ dp_i` on `ℂ^ι = EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` is Lebesgue
measure (`TauCeti.SymplecticForm.liouvilleMeasure_constSmooth_stdSymplecticForm`). Likewise on a
plane the Liouville measure of the determinant form of a basis is the Haar measure of that basis
(`TauCeti.SmoothTwoForm.liouvilleMeasure_const_continuousDet`), so the area form `dx ∧ dy` of `ℝ²`
has Liouville measure Lebesgue measure. Consequently the inverse of a Darboux chart, a partial
homeomorphism to `ℂ^ι` whose inverse pulls `σ` back to the standard form, carries Lebesgue
measure on the target of the chart to the Liouville measure of `σ` on its source
(`OpenPartialHomeomorph.map_symm_volume_restrict_target`).

## Main definitions

* `TauCeti.SmoothTwoForm.liouvilleMeasure σ n`: the Liouville measure `|σⁿ / n!|`.

## Main results

* `TauCeti.SmoothTwoForm.liouvilleMeasure_apply_of_subset`: the Liouville measure in a chart.
* `TauCeti.SmoothTwoForm.liouvilleMeasure_one`: on a surface it is the measure `|σ|` of `σ`.
* `TauCeti.SmoothTwoForm.isLocallyFiniteMeasure_liouvilleMeasure`: it is locally finite.
* `TauCeti.SmoothTwoForm.nullSingletonClass_liouvilleMeasure`: in positive dimension points are
  null.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isOpenPosMeasure_liouvilleMeasure`: for nondegenerate
  `σ` it is positive on nonempty open sets.
* `Homeomorph.measurePreserving_liouvilleMeasure`: maps pulling `τ` back to `σ` carry the
  Liouville measure of `σ` to that of `τ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.measurePreserving_globalFlowDiffeomorph_liouvilleMeasure`:
  Liouville's theorem, Hamiltonian flows preserve the Liouville measure.
* `MeasurableEmbedding.map_liouvilleMeasure`, `MeasurableEmbedding.liouvilleMeasure_eq_comap`:
  embeddings pulling `τ` back to `σ` carry the Liouville measure of `σ` to the restriction of that
  of `τ` to their range.
* `TauCeti.SmoothTwoForm.liouvilleMeasure_mpullback_subtypeVal`,
  `TauCeti.SmoothTwoForm.map_liouvilleMeasure_mpullback_subtypeVal`: the Liouville measure of the
  restriction to an open subset is the restricted Liouville measure.
* `TauCeti.SmoothTwoForm.liouvilleMeasure_smul`: the Liouville measure of `r • σ` is `|r|ⁿ` times
  that of `σ`.
* `TauCeti.SymplecticForm.liouvilleMeasure_constSmooth`: the Liouville measure of a constant
  symplectic form is the Haar measure of a Darboux basis.
* `TauCeti.SymplecticForm.liouvilleMeasure_constSmooth_stdSymplecticForm`: the Liouville measure of
  the standard symplectic form on `ℂ^ι` is Lebesgue measure.
* `TauCeti.SmoothTwoForm.liouvilleMeasure_const_continuousDet`: on a plane, the Liouville measure
  of the determinant form of a basis is the Haar measure of that basis.
* `OpenPartialHomeomorph.map_symm_volume_restrict_target`: the inverse of a Darboux chart carries
  Lebesgue measure on its target to the Liouville measure on its source.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 16 (Liouville's theorem).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 3 (the volume form `ωⁿ / n!` of a symplectic manifold).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped ContDiff ENNReal Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {n : ℕ} [hn : Fact (finrank ℝ E = 2 * n)]

section ChartMeasure

attribute [local instance] TauCeti.extChartAtMeasurableSpaceE TauCeti.extChartAtBorelSpaceE

namespace TauCeti

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I M}

variable (σ n) in
/-- The **Liouville measure** of a two-form `σ` on a manifold modelled on a space of dimension
`2 * n`: the measure `|σⁿ / n!|` of its symplectic volume form. For a symplectic form this is the
canonical volume of the symplectic manifold. -/
def liouvilleMeasure : Measure M :=
  RoughForm.measure (σ.volumeForm n).val

variable (σ n) in
/-- The Liouville measure is the measure of the symplectic volume form. -/
theorem liouvilleMeasure_def : σ.liouvilleMeasure n = RoughForm.measure (σ.volumeForm n).val :=
  (rfl)

/-- On a surface the Liouville measure of `σ` is the measure `|σ|` of the two-form itself. -/
theorem liouvilleMeasure_one [Fact (finrank ℝ E = 2 * 1)] (σ : SmoothTwoForm I M) :
    σ.liouvilleMeasure 1 = RoughForm.measure σ.val := by
  rw [liouvilleMeasure_def, volumeForm_one]

/-- **The Liouville measure in coordinates.** The Liouville measure of a measurable subset of a
chart source is the integral over its coordinate image of the absolute value of the coefficient of
`σⁿ / n!` in that chart. -/
theorem liouvilleMeasure_apply_of_subset {α : M} {s : Set M} (hs : MeasurableSet s)
    (hsub : s ⊆ (extChartAt I α).source) :
    σ.liouvilleMeasure n s =
      ∫⁻ y in (extChartAt I α) '' s,
        ENNReal.ofReal |RoughForm.inChartAt (σ.volumeForm n).val α y
            (finBasisOfFinrankEq ℝ E hn.out)|
          ∂(finBasisOfFinrankEq ℝ E hn.out).addHaar :=
  RoughForm.measure_apply_of_subset _ hs hsub

/-- The Liouville measure is locally finite. In particular it is a finite measure on a compact
manifold. -/
instance isLocallyFiniteMeasure_liouvilleMeasure : IsLocallyFiniteMeasure (σ.liouvilleMeasure n) :=
  RoughForm.isLocallyFiniteMeasure_measure ((σ.volumeForm n).isSmoothForm.of_le bot_le)

/-- In positive dimension points are null for the Liouville measure. -/
instance nullSingletonClass_liouvilleMeasure [Nontrivial E] :
    NullSingletonClass (σ.liouvilleMeasure n) :=
  RoughForm.nullSingletonClass_measure _

/-- The Liouville measure of a nondegenerate two-form is positive on nonempty open sets. -/
theorem IsNondegenerate.isOpenPosMeasure_liouvilleMeasure (h : σ.IsNondegenerate) :
    (σ.liouvilleMeasure n).IsOpenPosMeasure :=
  RoughForm.isOpenPosMeasure_measure ((σ.volumeForm n).isSmoothForm.of_le bot_le)
    (h.volumeForm_apply_ne_zero hn.out)

/-- **Rescaling the form.** Replacing `σ` by `r • σ` multiplies the Liouville measure by `|r|ⁿ`. -/
@[simp]
theorem liouvilleMeasure_smul (r : ℝ) (σ : SmoothTwoForm I M) :
    (r • σ).liouvilleMeasure n = ENNReal.ofReal (|r| ^ n) • σ.liouvilleMeasure n := by
  rw [liouvilleMeasure_def, liouvilleMeasure_def, volumeForm_smul, Submodule.coe_smul,
    RoughForm.measure_smul, abs_pow]

end SmoothTwoForm

end TauCeti

namespace Homeomorph

open TauCeti

variable {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J ∞ N] [MeasurableSpace N] [BorelSpace N] [LindelofSpace N]

/-- **Maps pulling back the two-form preserve the Liouville measure.** A differentiable
homeomorphism `Φ : M → N` with `Φ^* τ = σ` carries the Liouville measure of `σ` to that of `τ`. In
particular a symplectomorphism preserves the Liouville measure. -/
theorem measurePreserving_liouvilleMeasure {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (Φ : M ≃ₜ N) (hΦ : MDifferentiable I J Φ) (h : mpullback I J Φ τ.val = σ.val) :
    MeasurePreserving Φ (σ.liouvilleMeasure n) (τ.liouvilleMeasure n) := by
  rw [SmoothTwoForm.liouvilleMeasure_def, SmoothTwoForm.liouvilleMeasure_def,
    ← SmoothTwoForm.mpullback_volumeForm h]
  exact Φ.measurePreserving_measure_mpullback hΦ _

end Homeomorph

namespace MeasurableEmbedding

open TauCeti

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [Fact (finrank ℝ E' = 2 * n)] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [MeasurableSpace N] [BorelSpace N]
  [LindelofSpace N] {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N} {f : M → N}

/-- **Embeddings pulling back the two-form carry Liouville measure to Liouville measure.** A
differentiable measurable embedding `f : M → N` between manifolds of the same dimension with
`f^* τ = σ`, such as a symplectic open embedding, carries the Liouville measure of `σ` to the
restriction of the Liouville measure of `τ` to the range of `f`. -/
theorem map_liouvilleMeasure (hf : MeasurableEmbedding f) (hfd : MDifferentiable I J f)
    (h : mpullback I J f τ.val = σ.val) :
    (σ.liouvilleMeasure n).map f = (τ.liouvilleMeasure n).restrict (range f) := by
  rw [SmoothTwoForm.liouvilleMeasure_def, SmoothTwoForm.liouvilleMeasure_def,
    ← SmoothTwoForm.mpullback_volumeForm h]
  exact hf.map_measure_mpullback hfd _

/-- If a differentiable measurable embedding `f : M → N` between manifolds of the same dimension
pulls `τ` back to `σ`, then the Liouville measure of `σ` gives a set `s` the Liouville measure of
`τ` of its image `f '' s`. -/
theorem liouvilleMeasure_eq_comap (hf : MeasurableEmbedding f) (hfd : MDifferentiable I J f)
    (h : mpullback I J f τ.val = σ.val) : σ.liouvilleMeasure n = (τ.liouvilleMeasure n).comap f
        := by
  rw [SmoothTwoForm.liouvilleMeasure_def, SmoothTwoForm.liouvilleMeasure_def,
    ← SmoothTwoForm.mpullback_volumeForm h]
  exact hf.measure_mpullback hfd _

end MeasurableEmbedding

namespace TauCeti.SmoothTwoForm

open TopologicalSpace

variable {σ : SmoothTwoForm I M} (U : Opens M) [LindelofSpace U]

/-- **The Liouville measure of an open subset.** The Liouville measure of the restriction of `σ` to
an open subset `U` gives a subset of `U` its Liouville measure in `M`. -/
theorem liouvilleMeasure_mpullback_subtypeVal :
    liouvilleMeasure n (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ) =
      (σ.liouvilleMeasure n).comap Subtype.val := by
  have hU : MeasurableEmbedding (Subtype.val : U → M) :=
    MeasurableEmbedding.subtypeVal U.isOpen.measurableSet
  exact hU.liouvilleMeasure_eq_comap (contMDiff_subtypeVal.mdifferentiable one_ne_zero)
    (SmoothForm.coe_mpullback _ _ _).symm

/-- **Restriction of the Liouville measure to an open subset.** Pushed forward to `M`, the Liouville
measure of the restriction of `σ` to an open subset `U` is the restriction to `U` of the Liouville
measure of `σ`. -/
theorem map_liouvilleMeasure_mpullback_subtypeVal :
    (liouvilleMeasure n (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ)).map
      Subtype.val = (σ.liouvilleMeasure n).restrict U := by
  have hU : MeasurableEmbedding (Subtype.val : U → M) :=
    MeasurableEmbedding.subtypeVal U.isOpen.measurableSet
  rw [hU.map_liouvilleMeasure (contMDiff_subtypeVal.mdifferentiable one_ne_zero)
    (SmoothForm.coe_mpullback _ _ _).symm, Subtype.range_coe]

end TauCeti.SmoothTwoForm

namespace TauCeti.SmoothTwoForm.IsSymplectic

variable [T2Space M] [I.Boundaryless] {σ : SmoothTwoForm I M} {f : M → ℝ}

/-- **Liouville's theorem.** For a symplectic form `σ` and a smooth function `f` with complete
Hamiltonian vector field, every time-`t` map of the Hamiltonian flow of `f` preserves the Liouville
measure. -/
theorem measurePreserving_globalFlowDiffeomorph_liouvilleMeasure (hσ : σ.IsSymplectic)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (σ.hamiltonianVectorField f)) (t : ℝ) :
    MeasurePreserving (globalFlowDiffeomorph hc le_top
      (hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl (by simpa using hf)) t)
      (σ.liouvilleMeasure n) (σ.liouvilleMeasure n) := by
  have hv : ContMDiff I I.tangent (⊤ : ℕ∞)
      (fun y ↦ (⟨y, σ.hamiltonianVectorField f y⟩ : TangentBundle I M)) :=
    hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl (by simpa using hf)
  set ψ := globalFlowDiffeomorph hc le_top hv t
  refine ψ.toHomeomorph.measurePreserving_liouvilleMeasure (ψ.mdifferentiable (by simp)) ?_
  have h := congrArg Subtype.val (hσ.mpullback_globalFlowDiffeomorph hf hc hv t)
  rw [SmoothForm.coe_mpullback] at h
  rwa [Diffeomorph.coe_toHomeomorph]

end TauCeti.SmoothTwoForm.IsSymplectic

end ChartMeasure

/-! ### Constant symplectic forms on a vector space -/

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : ℕ} [Fact (finrank ℝ V = 2 * m)]

/-- **The Liouville measure of a constant symplectic form.** On a symplectic vector space
`(V, σ)`, regarded as a manifold with the constant form `σ`, the Liouville measure `|σᵐ / m!|` is
the Haar measure normalized by any Darboux basis: it gives the parallelepiped spanned by a Darboux
basis measure one. -/
theorem liouvilleMeasure_constSmooth (σ : SymplecticForm V) {b : Basis (Fin m × Fin 2) ℝ V}
    (hb : σ.IsDarbouxBasis b) : σ.constSmooth.liouvilleMeasure m = b.addHaar := by
  set e := finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))
  -- The tangent spaces of the model space are `V` itself, and `b` is a basis of each of them.
  have hval (x : V) : (σ.constSmooth.volumeForm m).val x (b.reindex e) = 1 :=
    σ.isNondegenerate_constSmooth.volumeForm_apply_reindex (x := x) (b := b)
      (by rwa [isNondegenerate_constSmooth_symplecticFormAt])
  rw [SmoothTwoForm.liouvilleMeasure_def, RoughForm.measure_eq_smul_addHaar (c := 1) _ hval,
    abs_one, ENNReal.ofReal_one, one_smul, Basis.addHaar_reindex]

/-- **The Liouville measure of the standard symplectic form is Lebesgue measure.** On
`ℂ^ι = EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`, written in the real coordinates
`z_i = q_i + i p_i`, the Liouville measure of the standard form `Σ dq_i ∧ dp_i` is the Lebesgue
measure `volume`. -/
theorem liouvilleMeasure_constSmooth_stdSymplecticForm {ι : Type*} [Fintype ι] :
    (stdSymplecticForm (V := EuclideanSpace ℝ ι)).constSmooth.liouvilleMeasure (Fintype.card ι) =
      volume := by
  classical
  set e := Fintype.equivFin ι
  set d := (stdSymplecticBasis ι).reindex (Equiv.sumCongr e e)
  have hd : LinearMap.BilinForm.toMatrix d
      (stdSymplecticForm (V := EuclideanSpace ℝ ι)).toBilinForm =
        Matrix.J (Fin (Fintype.card ι)) ℝ := by
    ext a c
    rw [LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply,
      ← LinearMap.BilinForm.toMatrix_apply, toMatrix_stdSymplecticBasis]
    rcases a with a | a <;> rcases c with c | c <;> simp [Matrix.J, Matrix.one_apply]
  refine (liouvilleMeasure_constSmooth _ (isDarbouxBasis_reindex_symm_iff.2 hd)).trans ?_
  rw [Basis.addHaar_reindex, Basis.addHaar_reindex, stdSymplecticBasis_def, Basis.addHaar_reindex,
    Basis.prod_addHaar, OrthonormalBasis.addHaar_eq_volume, Measure.volume_eq_prod]

end TauCeti.SymplecticForm

/-! ### Darboux charts -/

namespace OpenPartialHomeomorph

open TauCeti TopologicalSpace

variable {ι : Type*} [Fintype ι] [Fact (finrank ℝ E = 2 * Fintype.card ι)] {σ : SmoothTwoForm I M}

/-- **Darboux charts carry Lebesgue measure to the Liouville measure.** Let `e` be a partial
homeomorphism from `M` to `ℂ^ι = EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` whose inverse is smooth
on the target of `e` and pulls `σ` back to the standard symplectic form `Σ dq_i ∧ dp_i` there. Then
the inverse of `e` carries Lebesgue measure on the target of `e` to the Liouville measure of `σ` on
the source of `e`. -/
theorem map_symm_volume_restrict_target
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (he : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) I ∞ e.symm e.target)
    (h : ∀ w ∈ e.target, ∀ a b, σ.eval₂ (e.symm w)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) I e.symm w a)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) I e.symm w b) =
        stdSymplecticForm a b) :
    (volume.restrict e.target).map e.symm =
      (σ.liouvilleMeasure (Fintype.card ι)).restrict e.source := by
  set W : Opens (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) := ⟨_, e.open_target⟩
  set g : W → M := fun w ↦ e.symm w
  have hd (w : W) : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) I ∞ e.symm w :=
    (he w w.property).contMDiffAt (e.open_target.mem_nhds w.property)
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) I ∞ g := fun w ↦
    (hd w).comp w contMDiff_subtypeVal.contMDiffAt
  -- The restricted inverse `g` pulls `σ` back to the standard form restricted to `W`.
  have hpull : SmoothForm.mpullback _ hg σ = SmoothForm.mpullback (Subtype.val : W → _)
      contMDiff_subtypeVal (stdSymplecticForm (V := EuclideanSpace ℝ ι)).constSmooth := by
    refine SmoothBundleForm.ext_eval₂ fun w a b ↦ ?_
    have hval : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (Subtype.val : W → _) w :=
      contMDiff_subtypeVal.mdifferentiable one_ne_zero w
    -- By definition `g` is the inclusion of `W` followed by the inverse of `e`.
    rw [SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback,
      show g = e.symm ∘ Subtype.val from rfl,
      mfderiv_comp_apply w ((hd w).mdifferentiableAt (by simp)) hval,
      mfderiv_comp_apply w ((hd w).mdifferentiableAt (by simp)) hval,
      TauCeti.Manifold.mfderiv_subtype_val_apply, TauCeti.Manifold.mfderiv_subtype_val_apply]
    exact (h w w.property a b).trans (SymplecticForm.constSmooth_apply _ _ _ _).symm
  have hpull' := congrArg Subtype.val hpull
  rw [SmoothForm.coe_mpullback] at hpull'
  have hrange : range g = e.source := by
    ext x
    simp only [← e.symm_image_target_eq_source, g, W, mem_range, Subtype.exists, Opens.mem_mk,
      exists_prop, mem_image]
  have : Fact (finrank ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) = 2 * Fintype.card ι) :=
    ⟨by rw [finrank_prod, finrank_euclideanSpace, two_mul]⟩
  -- Lebesgue measure on `W` is the Liouville measure of the restricted standard form, which `g`
  -- carries to the Liouville measure of `σ` on the range of `g`.
  have hW : volume.restrict e.target = (SmoothTwoForm.liouvilleMeasure (Fintype.card ι)
      (SmoothForm.mpullback (Subtype.val : W → _) contMDiff_subtypeVal
        (stdSymplecticForm (V := EuclideanSpace ℝ ι)).constSmooth)).map Subtype.val := by
    rw [SmoothTwoForm.map_liouvilleMeasure_mpullback_subtypeVal,
      SymplecticForm.liouvilleMeasure_constSmooth_stdSymplecticForm]
    simp only [W, Opens.coe_mk]
  rw [hW, AEMeasurable.map_map_of_aemeasurable (by
      rw [← hW]
      exact e.continuousOn_symm.aemeasurable e.open_target.measurableSet)
    measurable_subtypeVal.aemeasurable,
    ← hrange]
  have hemb : MeasurableEmbedding g := e.symm.isOpenEmbedding_restrict.measurableEmbedding
  exact hemb.map_liouvilleMeasure (hg.mdifferentiable (by simp)) hpull'

end OpenPartialHomeomorph

/-! ### The area form of the plane -/

namespace TauCeti

/-- `ℝ²` has dimension `2 * 1`: it is the model space of symplectic surfaces, such as the
two-sphere, whose Liouville measure `|σ¹ / 1!|` is built on it. -/
instance fact_finrank_euclideanSpace_fin_two :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 * 1) :=
  ⟨by simp⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Fact (finrank ℝ V = 2 * 1)]

/-- **The Liouville measure of a constant area form on a plane.** On a two-dimensional space `V`,
the constant two-form given by the determinant form of a basis `b` has Liouville measure the Haar
measure normalized by `b`. For the standard basis of `ℝ²`, the form `dx ∧ dy`, this is Lebesgue
measure. -/
theorem SmoothTwoForm.liouvilleMeasure_const_continuousDet {b : Basis (Fin 2) ℝ V} :
    SmoothTwoForm.liouvilleMeasure 1 (SmoothForm.const b.continuousDet) = b.addHaar := by
  set b' := b.reindex (finCongr (by norm_num : 2 = 2 * 1))
  set α : SmoothTwoForm 𝓘(ℝ, V) V := SmoothForm.const b.continuousDet
  -- The determinant form is its own volume form, and it takes the value `1` on `b`.
  have hval (x : V) : (α.volumeForm 1).val x b' = 1 := by
    have hb : ⇑b' = fun r ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 1) r)).2 := by
      funext r
      rw [Module.Basis.reindex_apply, finProdFinEquiv_symm_apply]
      congr 1
      -- An equation between two indices in `Fin 2`, checked on both values.
      revert r
      decide
    have h := ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv (α.val x) (m := 1)
      (fun p ↦ b p.2) (fun _ _ ↦ ?_) (fun i j ↦ ?_)
    · rw [SmoothTwoForm.volumeForm_apply]
      refine (ContinuousAlternatingMap.smul_apply _ _ _).trans ?_
      rw [hb, h, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
    · -- The goal's vector reduces to `![b 0, b 0]` by beta and `Prod.snd` reduction, and its
      -- entries `0` and `1` both unfold to `b 0`, so they agree by `rfl`.
      exact (α.val x).map_eq_zero_of_eq ![b 0, b 0] (i := 0) (j := 1) rfl (by decide)
    · fin_cases i
      fin_cases j
      rw [SmoothForm.const_apply, Module.Basis.continuousDet_apply]
      convert b.det_self using 2
      · funext k
        rw [NormedSpace.fromTangentSpace_apply]
        fin_cases k <;> simp
      · simp
  rw [SmoothTwoForm.liouvilleMeasure_def, RoughForm.measure_eq_smul_addHaar (c := 1) b' hval,
    abs_one, ENNReal.ofReal_one, one_smul, Module.Basis.addHaar_reindex]

end TauCeti
