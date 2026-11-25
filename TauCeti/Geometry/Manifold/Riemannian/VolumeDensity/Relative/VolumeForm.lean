/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm

/-!
# The relative volume density and oriented volume forms

Let `g` and `g'` be Riemannian metrics on an oriented manifold `M`. The relative volume density
`J = J(g, g')` (`Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity`) is the ratio of the
positive oriented volume forms: `vol_{g'} = J vol_g` pointwise, for every orientation of `M`
(`Bundle.ContMDiffRiemannianMetric.riemannianVolumeForm_eq_relativeVolumeDensity_smul`, evaluated
in `Bundle.ContMDiffRiemannianMetric.riemannianVolumeForm_apply_eq_relativeVolumeDensity_mul`).
In particular `J` does not depend on the orientation, and reversing it negates both forms.

The proof evaluates both volume forms on one basis `b` of `T_x M`: on it they are `± √(det G)`
for the Gram matrices `G` of `b` for `g` and `g'`, with the same sign, positive exactly when `b`
is positively oriented (`Orientation.volumeForm_apply_eq_sqrt_det_gram`), while
`J = √(det G' / det G)` (`Module.Basis.relativeVolumeDensity_eq_sqrt_div`). A top-degree
alternating form is determined by its value on a basis.
-/

public section

open Bundle TauCeti
open scoped Manifold ContDiff

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω} {m : ℕ}

open scoped Classical in
/-- The value of an oriented volume form on a basis `b` is `± √(det G)` for the Gram matrix `G`
of `b`, with the sign given by the orientation of `b`. -/
private theorem riemannianVolumeForm_basis
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : Module.Basis (Fin m) ℝ (TangentSpace I x)) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      riemannianVolumeForm o x b) =
    (if b.orientation = Manifold.Orientation.orientationAt o x then 1 else -1) *
      √(Matrix.of fun i j ↦ g.inner x (b i) (b j)).det := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let := o.fact_finrank_tangentSpace x
  have hgram : Matrix.gram ℝ b = Matrix.of fun i j ↦ g.inner x (b i) (b j) := by
    ext i j
    exact inner_riemannianBundle g x (b i) (b j)
  rw [riemannianVolumeForm_apply, ← hgram]
  split_ifs with hb
  · rw [one_mul, Orientation.volumeForm_apply_eq_sqrt_det_gram _ b hb]
  · rw [neg_one_mul, Orientation.volumeForm_apply_eq_neg_sqrt_det_gram _ b hb]

/-- An oriented volume form is its value on a basis `b` times the determinant in `b`. -/
private theorem riemannianVolumeForm_eq_mul_det
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : Module.Basis (Fin m) ℝ (TangentSpace I x)) (v : Fin m → TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      riemannianVolumeForm o x v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      riemannianVolumeForm o x b) * b.det v := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let := o.fact_finrank_tangentSpace x
  simp only [riemannianVolumeForm_apply]
  rw [← smul_eq_mul, ← smul_apply,
    ← AlternatingMap.eq_smul_basis_det b (Manifold.Orientation.orientationAt o x).volumeForm]

/-- **The relative density is the ratio of the oriented volume forms**: for every orientation of
`M`, `vol_{g'} = J(g, g') vol_g` at every point. -/
theorem riemannianVolumeForm_apply_eq_relativeVolumeDensity_mul
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) (x : M) (v : Fin m → TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      riemannianVolumeForm o x v) =
    relativeVolumeDensity g g' x *
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        riemannianVolumeForm o x v) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b : Module.Basis (Fin m) ℝ (TangentSpace I x) :=
    Module.finBasisOfFinrankEq ℝ _ (o.fact_finrank_tangentSpace x).out
  have hpos : 0 < (Matrix.of fun i j ↦ g.inner x (b i) (b j)).det := by
    convert b.det_bilinFormToMatrix_pos (B := (g.inner x).toBilinForm) (g.symm x) (g.pos x)
      using 2
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  have hs : √(Matrix.of fun i j ↦ g.inner x (b i) (b j)).det ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  rw [riemannianVolumeForm_eq_mul_det g' o x b v, riemannianVolumeForm_eq_mul_det g o x b v,
    riemannianVolumeForm_basis g' o x b, riemannianVolumeForm_basis g o x b,
    b.relativeVolumeDensity_eq_sqrt_div, Real.sqrt_div' _ hpos.le]
  field_simp

/-- **The relative density is the ratio of the oriented volume forms**, as forms: for every
orientation of `M`, `vol_{g'} = J(g, g') • vol_g`. -/
theorem riemannianVolumeForm_eq_relativeVolumeDensity_smul
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      riemannianVolumeForm o x) =
    relativeVolumeDensity g g' x •
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        riemannianVolumeForm o x) := by
  ext v
  exact riemannianVolumeForm_apply_eq_relativeVolumeDensity_mul g g' o x v

end Bundle.ContMDiffRiemannianMetric
