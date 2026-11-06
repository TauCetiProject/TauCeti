/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Hyperplane
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A lower bound for the dimension of holomorphic local rings

The Krull dimension of the holomorphic stalk at any point of a finite-dimensional complex
manifold without boundary is at least the complex dimension of its model. Restricting germs
to a coordinate hyperplane is surjective and kills a nonzero coordinate germ. Since the ambient
stalk is a domain, adjoining a complex coordinate therefore increases Krull dimension by at
least one, by Mathlib's `ringKrullDim_succ_le_of_surjective`. Induction, complex linear changes
of coordinates and local chart pullback give the lower bound without assuming Noetherianity.

The result concerns the actual holomorphic structure-sheaf stalk, not a formal power-series
ring, and is also exported for Mathlib's native complex-smooth stalk via `smoothStalkIso`.
It supplies the geometric lower bound needed when comparing local-ring dimension with the
dimension of the cotangent space. It does not assert the upper bound.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II.
-/

public noncomputable section

open Filter
open scoped Manifold ContDiff Topology

open TauCeti TauCeti.holomorphicStructureSheaf

namespace ContinuousLinearEquiv

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A complex linear change of coordinates preserves the Krull dimension of holomorphic
stalks. No finite-dimensionality assumption is required for this comparison. -/
theorem ringKrullDim_holomorphicStalk (e : E ≃L[ℂ] F) (a : E) :
    ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk a) =
      ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, F) F).presheaf.stalk (e a)) := by
  have hle : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
      [NormedAddCommGroup W] [NormedSpace ℂ W] (e : V ≃L[ℂ] W) (v : V),
      ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk v) ≤
        ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, W) W).presheaf.stalk (e v)) := by
    intro V W _ _ _ _ e v
    apply ringKrullDim_le_of_surjective (stalkPrecomp 𝓘(ℂ, V) V e e.contDiff.contMDiff v)
    intro s
    obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq v s
    have hnear : ∀ᶠ w in 𝓝 (e v), ContMDiffAt 𝓘(ℂ, W) 𝓘(ℂ) ω (f ∘ e.symm) w := by
      filter_upwards [(e.symm.continuousAt.tendsto.eventually (by
        simpa only [e.symm_apply_apply] using hf))] with w hw
      exact hw.comp w e.symm.contDiff.contMDiff.contMDiffAt
    obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt hnear
    refine ⟨t, toFilterGerm_nhds_injective v ?_⟩
    rw [toFilterGerm_stalkPrecomp, ht, Germ.coe_compTendsto, hfs]
    congr 1
    ext z
    simp
  refine le_antisymm (hle E F e a) ?_
  -- Transport the base point explicitly through the stalk's colimit carrier.
  exact (hle F E e.symm (e a)).trans_eq
    (congrArg (fun x ↦ ringKrullDim
      ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x)) (e.symm_apply_apply a))

end ContinuousLinearEquiv

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Passing from a coordinate hyperplane to its ambient complex vector space raises the
Krull dimension of the holomorphic local ring by at least one. -/
theorem ringKrullDim_stalk_add_one_le_prod (a : E) (b : ℂ) :
    ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk a) + 1 ≤
      ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (a, b)) := by
  exact ringKrullDim_succ_le_of_surjective (restrictHyperplane a b)
    (restrictHyperplane_surjective a b)
    (mem_nonZeroDivisors_iff_ne_zero.mpr (hyperplaneCoordinateGerm_ne_zero a b))
    (restrictHyperplane_hyperplaneCoordinateGerm a b)

/-- The holomorphic local ring of a finite-dimensional complex vector space has Krull
dimension at least the complex dimension of the space. This includes dimension zero and
requires no Noetherianity hypothesis. -/
theorem finrank_le_ringKrullDim_stalk_modelSpace (a : E) :
    (Module.finrank ℂ E : WithBot ℕ∞) ≤
      ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk a) := by
  suffices h : ∀ n, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
      [FiniteDimensional ℂ V], Module.finrank ℂ V = n → ∀ v : V,
        (n : WithBot ℕ∞) ≤ ringKrullDim
          ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk v) from
    h (Module.finrank ℂ E) E rfl a
  intro n
  induction n with
  | zero =>
    intro V _ _ _ _ v
    exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    intro V _ _ _ hn v
    let e : V ≃L[ℂ] ((Fin n → ℂ) × ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hn])
    rw [e.ringKrullDim_holomorphicStalk v]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (add_le_add (ih (Fin n → ℂ) (by simp) (e v).1) (le_refl (1 : WithBot ℕ∞))).trans
        (ringKrullDim_stalk_add_one_le_prod (e v).1 (e v).2)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The Krull dimension of the holomorphic local ring at a point of a complex manifold
without boundary is at least the complex dimension of its model. No separation,
countability or Noetherianity hypothesis is needed. -/
theorem finrank_le_ringKrullDim_stalk (x : X) :
    (Module.finrank ℂ E : WithBot ℕ∞) ≤
      ringKrullDim ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let e := extChartAt I x
  have he : ∀ᶠ z in 𝓝 (e x), ContMDiffAt 𝓘(ℂ, E) I ω e.symm z := by
    filter_upwards [extChartAt_target_mem_nhds (I := I) x] with z hz
    exact (contMDiffOn_extChartAt_symm x z hz).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  -- Restriction to the inverse chart is onto: extend a model germ using the chart.
  have hsurj : Function.Surjective (stalkPullback he) := by
    intro s
    obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq (e x) s
    have hnear : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℂ) ω (f ∘ e) y := by
      filter_upwards [(contMDiffAt_extChartAt (I := I) (n := ω) (x := x)).continuousAt.tendsto
        |>.eventually hf, (chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy hy'
      exact hy.comp y (contMDiffAt_extChartAt' hy')
    have hx : e.symm (e x) = x := extChartAt_to_inv x
    obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt
      (hx.symm ▸ hnear)
    refine ⟨t, toFilterGerm_nhds_injective (e x) ?_⟩
    rw [toFilterGerm_stalkPullback, ht, Germ.coe_compTendsto, hfs, Germ.coe_eq]
    filter_upwards [extChartAt_target_mem_nhds (I := I) x] with z hz
    simp only [Function.comp_apply, e.right_inv hz]
  have hdim := ringKrullDim_le_of_surjective (stalkPullback he) hsurj
  have hx : e.symm (e x) = x := extChartAt_to_inv x
  exact (finrank_le_ringKrullDim_stalk_modelSpace (e x)).trans <|
    hdim.trans_eq (congrArg (fun y ↦ ringKrullDim
      ((holomorphicStructureSheaf I X).presheaf.stalk y)) hx)

/-- The same dimension lower bound on Mathlib's native complex-smooth structure-sheaf stalk,
via the canonical holomorphic/complex-smooth comparison. -/
theorem finrank_le_ringKrullDim_smoothStalk (x : X) :
    (Module.finrank ℂ E : WithBot ℕ∞) ≤
      ringKrullDim ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) := by
  rw [← (smoothStalkIso I X x).commRingCatIsoToRingEquiv.ringKrullDim]
  exact finrank_le_ringKrullDim_stalk x

end TauCeti.holomorphicStructureSheaf
