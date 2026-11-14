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
measure (`TauCeti.SymplecticForm.liouvilleMeasure_constSmooth_stdSymplecticForm`).

## Main definitions

* `TauCeti.SmoothTwoForm.liouvilleMeasure σ n`: the Liouville measure `|σⁿ / n!|`.

## Main results

* `TauCeti.SmoothTwoForm.liouvilleMeasure_apply_of_subset`: the Liouville measure in a chart.
* `TauCeti.SmoothTwoForm.isLocallyFiniteMeasure_liouvilleMeasure`: it is locally finite.
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
  RoughForm.measure (σ.volumeForm n).1

variable (σ n) in
/-- The Liouville measure is the measure of the symplectic volume form. -/
theorem liouvilleMeasure_def : σ.liouvilleMeasure n = RoughForm.measure (σ.volumeForm n).1 :=
  (rfl)

/-- **The Liouville measure in coordinates.** The Liouville measure of a measurable subset of a
chart source is the integral over its coordinate image of the absolute value of the coefficient of
`σⁿ / n!` in that chart. -/
theorem liouvilleMeasure_apply_of_subset {α : M} {s : Set M} (hs : MeasurableSet s)
    (hsub : s ⊆ (extChartAt I α).source) :
    σ.liouvilleMeasure n s =
      ∫⁻ y in (extChartAt I α) '' s,
        ENNReal.ofReal |RoughForm.inChartAt (σ.volumeForm n).1 α y (finBasisOfFinrankEq ℝ E hn.out)|
          ∂(finBasisOfFinrankEq ℝ E hn.out).addHaar :=
  RoughForm.measure_apply_of_subset _ hs hsub

/-- The Liouville measure is locally finite. In particular it is a finite measure on a compact
manifold. -/
instance isLocallyFiniteMeasure_liouvilleMeasure : IsLocallyFiniteMeasure (σ.liouvilleMeasure n) :=
  RoughForm.isLocallyFiniteMeasure_measure ((σ.volumeForm n).isSmoothForm.of_le bot_le)

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
    (Φ : M ≃ₜ N) (hΦ : MDifferentiable I J Φ) (h : mpullback I J Φ τ.1 = σ.1) :
    MeasurePreserving Φ (σ.liouvilleMeasure n) (τ.liouvilleMeasure n) := by
  rw [SmoothTwoForm.liouvilleMeasure_def, SmoothTwoForm.liouvilleMeasure_def,
    ← SmoothTwoForm.mpullback_volumeForm h]
  exact Φ.measurePreserving_measure_mpullback hΦ _

end Homeomorph

namespace MeasurableEmbedding

open TauCeti

variable {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J ∞ N] [MeasurableSpace N] [BorelSpace N] [LindelofSpace N]
  {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N} {f : M → N}

/-- **Embeddings pulling back the two-form carry Liouville measure to Liouville measure.** A
differentiable measurable embedding `f : M → N` between manifolds of the same dimension with
`f^* τ = σ`, such as a symplectic open embedding, carries the Liouville measure of `σ` to the
restriction of the Liouville measure of `τ` to the range of `f`. -/
theorem map_liouvilleMeasure (hf : MeasurableEmbedding f) (hfd : MDifferentiable I J f)
    (h : mpullback I J f τ.1 = σ.1) :
    (σ.liouvilleMeasure n).map f = (τ.liouvilleMeasure n).restrict (range f) := by
  rw [SmoothTwoForm.liouvilleMeasure_def, SmoothTwoForm.liouvilleMeasure_def,
    ← SmoothTwoForm.mpullback_volumeForm h]
  exact hf.map_measure_mpullback hfd _

/-- If a differentiable measurable embedding `f : M → N` between manifolds of the same dimension
pulls `τ` back to `σ`, then the Liouville measure of `σ` gives a set `s` the Liouville measure of
`τ` of its image `f '' s`. -/
theorem liouvilleMeasure_eq_comap (hf : MeasurableEmbedding f) (hfd : MDifferentiable I J f)
    (h : mpullback I J f τ.1 = σ.1) : σ.liouvilleMeasure n = (τ.liouvilleMeasure n).comap f := by
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
    liouvilleMeasure n (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ) =
      (σ.liouvilleMeasure n).comap Subtype.val := by
  have hU : MeasurableEmbedding (Subtype.val : U → M) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  exact hU.liouvilleMeasure_eq_comap (contMDiff_subtype_val.mdifferentiable one_ne_zero)
    (SmoothForm.coe_mpullback _ _ _).symm

/-- **Restriction of the Liouville measure to an open subset.** Pushed forward to `M`, the Liouville
measure of the restriction of `σ` to an open subset `U` is the restriction to `U` of the Liouville
measure of `σ`. -/
theorem map_liouvilleMeasure_mpullback_subtypeVal :
    (liouvilleMeasure n (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ)).map
      Subtype.val = (σ.liouvilleMeasure n).restrict U := by
  have hU : MeasurableEmbedding (Subtype.val : U → M) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  rw [hU.map_liouvilleMeasure (contMDiff_subtype_val.mdifferentiable one_ne_zero)
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
  have hval (x : V) : (σ.constSmooth.volumeForm m).1 x (b.reindex e) = 1 :=
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

