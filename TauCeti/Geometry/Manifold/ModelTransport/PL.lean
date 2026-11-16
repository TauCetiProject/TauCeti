/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.HasGroupoid
public import TauCeti.Geometry.Manifold.PLGroupoid.Map

/-!
# Changing the model space of a PL manifold

Let `Φ : H ≃ₜ H'` be a homeomorphism between two model spaces which is PL in both directions,
for models with corners `I` on `H` and `I'` on `H'`. Conjugating a chart change of the PL groupoid
of `I` by `Φ` gives a chart change of the PL groupoid of `I'`
(`Homeomorph.symm_trans_trans_mem_PLGroupoid`). Consequently, a PL manifold modelled on `I` is a
PL manifold modelled on `I'` for the composite charts `ChartedSpace.comp H' H M`, where `H` carries
the single chart `Φ` (`Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp`). This is the PL
counterpart of `Diffeomorph.isManifold_chartedSpaceComp`; both are instances of
`Homeomorph.hasGroupoid_chartedSpaceComp`.

The main instance is the homeomorphism `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` of the
product half-space `{q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}` onto Mathlib's half-space
`EuclideanHalfSpace (n + 1)`, which is PL in both directions
(`TauCeti.isPLMap_halfSpaceHomeomorphEuclideanHalfSpace`,
`TauCeti.isPLMap_halfSpaceHomeomorphEuclideanHalfSpace_symm`).

## Main results

* `Homeomorph.symm_trans_trans_mem_PLGroupoid`: conjugating by a PL homeomorphism of models
  carries the PL groupoid of `I` into the PL groupoid of `I'`.
* `Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp`: a PL manifold modelled on `I` is a PL
  manifold modelled on `I'` for the composite charts.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1 (PL manifolds).
-/

public section

open Set Function
open scoped Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}

open TauCeti

namespace Homeomorph

variable (Φ : H ≃ₜ H')

/-- Conjugating a map of `H` which is PL on `s` by a PL homeomorphism `Φ` of models gives a map of
`H'` which is PL on `Φ '' s`, written as the preimage under `Φ.symm`. -/
private theorem isPLOn_conj (hΦ : IsPLMap I I' Φ) (hΦ' : IsPLMap I' I Φ.symm) {f : H → H}
    {s : Set H} (hf : IsPLOn (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)) :
    IsPLOn (I' ∘ Φ ∘ f ∘ Φ.symm ∘ I'.symm) (I'.symm ⁻¹' (Φ.symm ⁻¹' s) ∩ range I') := by
  have hg := isPLMap_iff_isPLOn_range.1 hΦ
  have hg' := isPLMap_iff_isPLOn_range.1 hΦ'
  -- Read in the model vector spaces, the conjugate is `g ∘ (I ∘ f ∘ I.symm) ∘ g'`.
  have hcomp := hg.comp (hf.comp (hg'.mono inter_subset_right)
    fun y (hy : y ∈ I'.symm ⁻¹' (Φ.symm ⁻¹' s) ∩ range I') =>
      ⟨by simpa using hy.1, mem_range_self _⟩) fun _ _ => mem_range_self _
  exact hcomp.congr fun y _ => by simp

/-- **Changing the model of the PL groupoid.** Conjugating a member of the PL groupoid of `I` by a
homeomorphism of models `Φ` which is PL in both directions gives a member of the PL groupoid of
`I'`. -/
theorem symm_trans_trans_mem_PLGroupoid (hΦ : IsPLMap I I' Φ) (hΦ' : IsPLMap I' I Φ.symm)
    {e : OpenPartialHomeomorph H H} (he : e ∈ PLGroupoid I) :
    Φ.toOpenPartialHomeomorph.symm ≫ₕ (e ≫ₕ Φ.toOpenPartialHomeomorph) ∈ PLGroupoid I' := by
  rw [mem_PLGroupoid_iff] at he ⊢
  have hsource : (Φ.toOpenPartialHomeomorph.symm ≫ₕ (e ≫ₕ Φ.toOpenPartialHomeomorph)).source =
      Φ.symm ⁻¹' e.source := by
    ext; simp
  have htarget : (Φ.toOpenPartialHomeomorph.symm ≫ₕ (e ≫ₕ Φ.toOpenPartialHomeomorph)).target =
      Φ.symm ⁻¹' e.target := by
    ext; simp
  rw [hsource, htarget]
  simp only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans_symm,
    OpenPartialHomeomorph.symm_symm, Homeomorph.toOpenPartialHomeomorph_apply,
    Homeomorph.toOpenPartialHomeomorph_symm_apply, comp_assoc]
  exact ⟨isPLOn_conj Φ hΦ hΦ' he.1, isPLOn_conj Φ hΦ hΦ' he.2⟩

/-- **A PL manifold over one model is a PL manifold over a PL homeomorphic model.** If `Φ : H ≃ₜ H'`
is PL in both directions, a PL manifold modelled on `I` is a PL manifold modelled on `I'` for the
composite charts `ChartedSpace.comp H' H M`, when `H` carries the single chart `Φ`. -/
theorem hasGroupoid_PLGroupoid_chartedSpaceComp (hΦ : IsPLMap I I' Φ) (hΦ' : IsPLMap I' I Φ.symm)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M (PLGroupoid I)] :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    HasGroupoid M (PLGroupoid I') :=
  Φ.hasGroupoid_chartedSpaceComp (fun _ he => Φ.symm_trans_trans_mem_PLGroupoid hΦ hΦ' he) M

end Homeomorph
