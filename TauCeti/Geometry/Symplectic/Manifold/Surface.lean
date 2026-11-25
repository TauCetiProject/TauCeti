/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.TopForm.Existence
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.Geometry.Symplectic.Plane
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Symplectic and almost complex geometry on surfaces

On a two-dimensional manifold, both the symplectic condition on a two-form and the formal
integrability condition on an almost complex structure simplify:

* a smooth two-form is closed automatically, because a three-form on a two-dimensional space
  vanishes (`TauCeti.SmoothForm.isClosed_of_finrank_le`), and an alternating form on a
  two-dimensional space is nondegenerate exactly when it is nonzero
  (`LinearMap.BilinForm.IsAlt.nondegenerate_iff_ne_zero_of_finrank_eq_two`);
* the Nijenhuis tensor of every smooth almost complex structure `J` vanishes identically: it
  vanishes on `(v, v)` by skew-symmetry and on `(v, J v)` by anticommutation with `J`, and every
  nonzero vector `v` together with `J v` spans a two-dimensional tangent space.

So every surface carrying a nowhere-vanishing two-form is a symplectic manifold, and every smooth
almost complex structure on a manifold of dimension at most two has vanishing Nijenhuis tensor.

The symplectic orientation of such an area form is its orientation as a top form
(`TauCeti.Manifold.Orientation.ofTopForm`), in which a tangent basis `(e₀, e₁)` is positive
exactly when `σ(e₀, e₁) > 0`. Conversely, every orientation of a Hausdorff σ-compact surface is
the orientation of a nowhere-vanishing smooth top form
(`TauCeti.Manifold.Orientation.exists_ofTopForm_eq`), hence the symplectic orientation of an area
form. So such a surface is orientable exactly when it carries a symplectic form.

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`: on a surface, a
  smooth two-form is fiberwise nondegenerate exactly when it vanishes nowhere.
* `TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two`: on a surface, a
  smooth two-form is symplectic exactly when it vanishes nowhere.
* `TauCeti.SmoothTwoForm.IsNondegenerate.orientation_eq_ofTopForm`: on a surface, the symplectic
  orientation of an area form is its orientation as a top form.
* `TauCeti.exists_isSymplectic_orientation_eq_of_finrank_eq_two`: every orientation of a
  Hausdorff σ-compact surface is the symplectic orientation of an area form.
* `TauCeti.orientable_iff_exists_isSymplectic_of_finrank_eq_two`: a Hausdorff σ-compact surface
  is orientable exactly when it carries a symplectic form.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_eq_zero_of_finrank_le_two` and
  `TauCeti.SmoothAlmostComplexStructure.nijenhuis_eq_zero_of_finrank_eq_two`: on a manifold of
  real dimension at most two (in particular on any surface), the Nijenhuis tensor vanishes.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.3 (area forms on oriented surfaces).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Appendix C.6 (integrability in real dimension two).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I M}

/-- On a two-dimensional manifold, a smooth two-form is fiberwise nondegenerate exactly when it
vanishes nowhere. -/
theorem isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two (hE : Module.finrank ℝ E = 2) :
    σ.IsNondegenerate ↔ ∀ x, σ.val x ≠ 0 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  refine ⟨fun h ↦ h.apply_ne_zero, fun h ↦ isNondegenerate_iff_separatingLeft.2 fun x v hv ↦ ?_⟩
  -- `TangentSpace I x` is the model space `E` by definition
  have hx : Module.finrank ℝ (TangentSpace I x) = 2 := hE
  have hnd : (σ.bilinFormAt x).Nondegenerate := by
    rw [(SmoothForm.isAlt_bilinFormAt σ x).nondegenerate_iff_ne_zero_of_finrank_eq_two hx, ne_eq,
      SmoothForm.bilinFormAt_eq_zero_iff]
    exact h x
  exact hnd.1 v fun w ↦ by rw [SmoothForm.bilinFormAt_apply, hv w]

/-- **Area forms on surfaces are symplectic.** On a two-dimensional manifold, a smooth two-form is
symplectic exactly when it vanishes nowhere: closedness is automatic in dimension two. -/
theorem isSymplectic_iff_forall_ne_zero_of_finrank_eq_two (hE : Module.finrank ℝ E = 2) :
    σ.IsSymplectic ↔ ∀ x, σ.val x ≠ 0 := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  rw [← isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two hE]
  exact ⟨IsSymplectic.isNondegenerate, fun h ↦ ⟨SmoothForm.isClosed_of_finrank_le hE.le σ, h⟩⟩

/-- **The symplectic orientation of an area form.** On a two-dimensional manifold, the symplectic
orientation of a nondegenerate two-form `σ` is its orientation as a nowhere-vanishing top form
(`TauCeti.Manifold.Orientation.ofTopForm`): a tangent basis `(e₀, e₁)` is positive exactly when
`σ(e₀, e₁) > 0`. -/
theorem IsNondegenerate.orientation_eq_ofTopForm [FiniteDimensional ℝ E] (hσ : σ.IsNondegenerate)
    (hE : Module.finrank ℝ E = 2) :
    hσ.orientation hE = Manifold.Orientation.ofTopForm hE σ.val (σ.isSmoothForm.of_le zero_le)
      ((isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two hE).1 hσ) := by
  refine Manifold.Orientation.ext fun x ↦ ?_
  -- `TangentSpace I x` is the model space `E` by definition
  have hx : Module.finrank ℝ (TangentSpace I x) = 2 := hE
  -- Both tangent orientations at `x` are the orientation of a basis `b` positive for `σ_x`.
  let b := (Module.finBasisOfFinrankEq ℝ (TangentSpace I x) hx).adjustToOrientation
    ((hσ.orientation hE).orientationAt x)
  have hb : b.orientation = (hσ.orientation hE).orientationAt x :=
    Module.Basis.orientation_adjustToOrientation _ _
  have hpos : 0 < σ.val x b := by
    rw [orientationAt_orientation] at hb
    have h : 0 < hσ.symplecticFormAt x (b 0) (b 1) :=
      (SymplecticForm.basis_orientation_eq_orientation_iff hx b).mp hb
    rw [show (⇑b : Fin 2 → TangentSpace I x) = ![b 0, b 1] from (FinVec.etaExpand_eq _).symm]
    simpa only [symplecticFormAt_apply, SmoothBundleForm.eval₂_apply] using h
  rw [← hb, Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff]
  exact hpos

end SmoothTwoForm

/-- **Area forms on oriented surfaces.** Every orientation of a Hausdorff σ-compact
two-dimensional manifold is the symplectic orientation of a symplectic form, a nowhere-vanishing
smooth two-form positive on the positively oriented tangent bases. -/
theorem exists_isSymplectic_orientation_eq_of_finrank_eq_two [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] (hE : Module.finrank ℝ E = 2) (o : Manifold.Orientation I M (Fin 2)) :
    ∃ (σ : SmoothTwoForm I M) (hσ : σ.IsSymplectic), hσ.isNondegenerate.orientation hE = o := by
  obtain ⟨σ, h0, hσo⟩ := Manifold.Orientation.exists_ofTopForm_eq hE o
  have hσ : SmoothTwoForm.IsSymplectic σ :=
    (SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two hE).2 h0
  exact ⟨σ, hσ, (hσ.isNondegenerate.orientation_eq_ofTopForm hE).trans hσo⟩

/-- **Orientable surfaces are the symplectic surfaces.** A Hausdorff σ-compact two-dimensional
manifold is orientable exactly when it carries a symplectic form. -/
theorem orientable_iff_exists_isSymplectic_of_finrank_eq_two [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] (hE : Module.finrank ℝ E = 2) :
    Orientable I M ↔ ∃ σ : SmoothTwoForm I M, σ.IsSymplectic := by
  refine ⟨fun ⟨⟨o⟩⟩ ↦ ?_, fun ⟨σ, hσ⟩ ↦ ⟨⟨hσ.isNondegenerate.orientation rfl⟩⟩⟩
  obtain ⟨σ, hσ, -⟩ := exists_isSymplectic_orientation_eq_of_finrank_eq_two hE
    (o.reindex (finCongr hE))
  exact ⟨σ, hσ⟩

namespace SmoothAlmostComplexStructure

/-- On a finite-dimensional real manifold of dimension at most two, every smooth almost complex
structure has vanishing Nijenhuis tensor. -/
theorem nijenhuis_eq_zero_of_finrank_le_two [FiniteDimensional ℝ E]
    (J : SmoothAlmostComplexStructure I M) (hE : Module.finrank ℝ E ≤ 2) :
    J.nijenhuis = 0 := by
  ext x v w
  have hB : (J.nijenhuis x).toLinearMap₁₂ = 0 :=
    (J.almostComplexStructureAt x).bilin_eq_zero_of_finrank_le_two
      (hE : Module.finrank ℝ (TangentSpace I x) ≤ 2) (fun u ↦ J.nijenhuis_self u) (by simp)
  exact LinearMap.congr_fun₂ hB v w

/-- **Every almost complex structure on a surface has vanishing Nijenhuis tensor.** -/
theorem nijenhuis_eq_zero_of_finrank_eq_two [FiniteDimensional ℝ E]
    (J : SmoothAlmostComplexStructure I M) (hE : Module.finrank ℝ E = 2) :
    J.nijenhuis = 0 :=
  J.nijenhuis_eq_zero_of_finrank_le_two hE.le

end SmoothAlmostComplexStructure

end TauCeti
