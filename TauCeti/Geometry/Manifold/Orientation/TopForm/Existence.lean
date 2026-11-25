/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Top forms of an orientation

A nowhere-vanishing continuous top form orients a manifold
(`TauCeti.Manifold.Orientation.ofTopForm`). This file proves the converse on a Hausdorff
σ-compact smooth manifold modelled on a finite-dimensional space: every orientation `o` is the
orientation of a smooth top form, which vanishes nowhere and is positive exactly on the bases
positively oriented by `o` (`TauCeti.exists_topForm_of_orientation`). So such a manifold is
orientable exactly when it carries a nowhere-vanishing smooth top form
(`TauCeti.orientable_iff_exists_smoothForm_ne_zero`).

The form is the Riemannian volume form of `o` (`TauCeti.riemannianVolumeForm`) for a smooth
Riemannian metric, which exists by a partition of unity
(`TauCeti.nonempty_contMDiffRiemannianMetric`); the volume form is smooth and positive exactly on
positively oriented bases. Boundary and corner points are allowed. On a surface such a top form
is an area form, a symplectic form inducing the given orientation.

## Main results

* `TauCeti.exists_topForm_of_orientation`: an orientation has a nowhere-vanishing smooth top form
  positive exactly on its positively oriented bases.
* `TauCeti.Manifold.Orientation.exists_ofTopForm_eq`: every orientation is the orientation of a
  nowhere-vanishing smooth top form.
* `TauCeti.orientable_iff_exists_smoothForm_ne_zero`: a manifold is orientable exactly when it
  carries a nowhere-vanishing smooth top form.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Proposition 15.5 (orientations and nonvanishing top forms) and Proposition 15.29 (the Riemannian
  volume form).
-/

public section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {m : ℕ}

/-- **Top forms of an orientation.** On a Hausdorff σ-compact smooth manifold, every orientation
`o` has a smooth top form `φ` which vanishes nowhere and is positive on a tangent basis exactly
when the basis is positively oriented by `o`. -/
theorem exists_topForm_of_orientation (o : Manifold.Orientation I M (Fin m)) :
    ∃ φ : SmoothForm I M ℝ m, (∀ x, φ.val x ≠ 0) ∧
      ∀ x (b : Basis (Fin m) ℝ (TangentSpace I x)),
        0 < φ.val x b ↔ b.orientation = o.orientationAt x := by
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  refine ⟨⟨riemannianVolumeForm o, (isSmoothForm_riemannianVolumeForm o).mem_smoothBundleForms⟩,
    riemannianVolumeForm_apply_ne_zero o, fun x b ↦ ?_⟩
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_apply]
  exact _root_.Orientation.volumeForm_apply_pos_iff

namespace Manifold.Orientation

/-- **Every orientation is the orientation of a top form.** On a Hausdorff σ-compact smooth
manifold, every orientation is `TauCeti.Manifold.Orientation.ofTopForm` of a nowhere-vanishing
smooth top form. -/
theorem exists_ofTopForm_eq (hk : finrank ℝ E = m) (o : Orientation I M (Fin m)) :
    ∃ (φ : SmoothForm I M ℝ m) (h0 : ∀ x, φ.val x ≠ 0),
      ofTopForm hk φ.val (φ.isSmoothForm.of_le zero_le) h0 = o := by
  obtain ⟨φ, h0, hφ⟩ := exists_topForm_of_orientation o
  refine ⟨φ, h0, ext fun x ↦ ?_⟩
  -- On a basis `b`, both tangent orientations at `x` are read off the sign of `φ x b`. So `b` is
  -- positive for one exactly when it is positive for the other, and otherwise both are
  -- `-b.orientation`. (`adjustToOrientation` would need `Nonempty (Fin m)`, failing for `m = 0`.)
  let b := finBasisOfFinrankEq ℝ (TangentSpace I x) ((finrank_tangentSpace (I := I) x).trans hk)
  have hcard := Nat.card_eq_fintype_card.trans (o.finrank_tangentSpace_eq x).symm
  have h := (orientation_eq_orientationAt_ofTopForm_iff hk (φ.isSmoothForm.of_le zero_le) h0
    b).trans (hφ x b)
  by_cases hb : b.orientation = o.orientationAt x
  · exact (h.mpr hb).symm.trans hb
  · exact neg_injective (((b.orientation.ne_iff_eq_neg _ hcard).mp (mt h.mp hb)).symm.trans
      ((b.orientation.ne_iff_eq_neg _ hcard).mp hb))

end Manifold.Orientation

/-- **Orientability through top forms.** A Hausdorff σ-compact smooth manifold is orientable
exactly when it carries a nowhere-vanishing smooth top form. -/
theorem orientable_iff_exists_smoothForm_ne_zero :
    Orientable I M ↔ ∃ φ : SmoothForm I M ℝ (finrank ℝ E), ∀ x, φ.val x ≠ 0 :=
  ⟨fun ⟨⟨o⟩⟩ ↦ (exists_topForm_of_orientation o).imp fun _ h ↦ h.1, fun ⟨φ, h0⟩ ↦
    ⟨⟨Manifold.Orientation.ofTopForm rfl φ.val (φ.isSmoothForm.of_le zero_le) h0⟩⟩⟩

end TauCeti
