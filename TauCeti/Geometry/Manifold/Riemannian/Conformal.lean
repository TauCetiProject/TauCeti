/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Conformal classes and positive conformal factors

The conformal class of a native `C^k` Riemannian metric consists of its rescalings
by strictly positive `C^k` functions. Membership is symmetric and transitive, so
changing the representative does not change the class.

Writing `n = Module.finrank ℝ E`, in dimension different from two every metric in
the class has the form
`u^(4/(n-2)) g` for a positive `C^k` function `u`. When the tangent fibres are
nonzero, this function is unique. These statements hold at finite regularity,
without installing either of the compared metrics as a typeclass instance.

The convention for the conformal factor follows Lee and Parker, *The Yamabe
Problem*, Bulletin of the AMS 17 (1987), Section 2.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {k : ℕ∞ω}

/-- The conformal class of a `C^k` metric, with positive `C^k` rescaling factors. -/
def conformalClass (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)) :
    Set (ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)) :=
  {h | ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) k f) (hpos : ∀ x, 0 < f x),
    g.rescale f hf hpos = h}

/-- Membership means rescaling by a positive function of the same regularity. -/
theorem mem_conformalClass_iff
    {g h : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)} :
    h ∈ conformalClass g ↔
      ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) k f) (hpos : ∀ x, 0 < f x),
        g.rescale f hf hpos = h := Iff.rfl

/-- A metric belongs to its own conformal class. -/
@[simp]
theorem self_mem_conformalClass
    {g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)} :
    g ∈ conformalClass g := by
  refine ⟨fun _ ↦ 1, contMDiff_const, fun _ ↦ one_pos, ?_⟩
  ext x v w
  simp

/-- Belonging to the same conformal class is symmetric. -/
theorem mem_conformalClass_symm
    {g h : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    (hh : h ∈ conformalClass g) : g ∈ conformalClass h := by
  obtain ⟨f, hf, hp, rfl⟩ := hh
  refine ⟨fun x ↦ (f x)⁻¹, hf.inv₀ (fun x ↦ (hp x).ne'),
    fun x ↦ inv_pos.mpr (hp x), ?_⟩
  ext x v w
  simp [(hp x).ne']

/-- Successive positive rescalings remain in the original conformal class. -/
theorem mem_conformalClass_trans
    {g h j : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    (hh : h ∈ conformalClass g) (hj : j ∈ conformalClass h) :
    j ∈ conformalClass g := by
  obtain ⟨f, hf, hp, rfl⟩ := hh
  obtain ⟨q, hq, hqp, rfl⟩ := hj
  refine ⟨fun x ↦ q x * f x, hq.mul hf, fun x ↦ mul_pos (hqp x) (hp x), ?_⟩
  ext x v w
  simp [mul_assoc]

/-- Two metrics determine the same conformal class exactly when one belongs to the
conformal class of the other. -/
theorem conformalClass_eq_iff
    {g h : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)} :
    conformalClass h = conformalClass g ↔ h ∈ conformalClass g := by
  constructor
  · intro hh
    rw [← hh]
    exact self_mem_conformalClass
  · intro hh
    ext j
    exact ⟨mem_conformalClass_trans hh, mem_conformalClass_trans (mem_conformalClass_symm hh)⟩

/-- Rescale a metric by the positive conformal factor `u`, using exponent `4/(n-2)`.
The construction preserves `C^k` regularity. -/
def yamabeRescale
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) k u) (hpos : ∀ x, 0 < u x) :
    ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _) :=
  g.rescale (fun x ↦ (u x) ^ (4 / ((Module.finrank ℝ E : ℝ) - 2)))
    (fun x ↦ (Real.contDiffAt_rpow_const_of_ne (hpos x).ne').comp_contMDiffAt hu.contMDiffAt)
    (fun x ↦ Real.rpow_pos_of_pos (hpos x) _)

/-- The inner product of a conformally rescaled metric on the native tangent fibre. -/
@[simp]
theorem yamabeRescale_inner
    {g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    {u : M → ℝ} {hu : ContMDiff I 𝓘(ℝ) k u} {hpos : ∀ x, 0 < u x}
    (x : M) (v w : TangentSpace I x) :
    (yamabeRescale g u hu hpos).inner x v w =
      (u x) ^ (4 / ((Module.finrank ℝ E : ℝ) - 2)) * g.inner x v w := by
  unfold yamabeRescale
  exact g.rescale_inner _ _ _ x v w

/-- A positive conformal factor gives a member of the original conformal class. -/
@[simp]
theorem yamabeRescale_mem_conformalClass
    {g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    {u : M → ℝ} {hu : ContMDiff I 𝓘(ℝ) k u} {hpos : ∀ x, 0 < u x} :
    yamabeRescale g u hu hpos ∈ conformalClass g :=
  ⟨_, _, _, rfl⟩

/-- Every metric in the conformal class admits the positive-function parametrization
`u^(4/(n-2)) g`, provided the dimension is not two. -/
theorem mem_conformalClass_iff_exists_yamabeRescale
    {g h : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    (hdim : Module.finrank ℝ E ≠ 2) :
    h ∈ conformalClass g ↔
      ∃ (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) k u) (hp : ∀ x, 0 < u x),
        yamabeRescale g u hu hp = h := by
  constructor
  · rintro ⟨f, hf, hp, rfl⟩
    let a : ℝ := 4 / ((Module.finrank ℝ E : ℝ) - 2)
    have ha : a ≠ 0 := div_ne_zero (by norm_num) (sub_ne_zero.mpr (by exact_mod_cast hdim))
    have hu : ContMDiff I 𝓘(ℝ) k (fun x ↦ (f x) ^ a⁻¹) := by
      intro x
      exact (Real.contDiffAt_rpow_const_of_ne (hp x).ne').comp_contMDiffAt hf.contMDiffAt
    refine ⟨fun x ↦ (f x) ^ a⁻¹, hu, fun x ↦ Real.rpow_pos_of_pos (hp x) _, ?_⟩
    ext x v w
    rw [yamabeRescale_inner, ContMDiffRiemannianMetric.rescale_inner,
      Real.rpow_inv_rpow (hp x).le ha]
  · rintro ⟨u, hu, hp, rfl⟩
    exact yamabeRescale_mem_conformalClass

/-- The unit conformal factor leaves the metric unchanged. -/
@[simp]
theorem yamabeRescale_one
    {g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)} :
    yamabeRescale g (fun _ ↦ 1) contMDiff_const (fun _ ↦ one_pos) = g := by
  ext x v w
  simp

/-- Successive conformal changes multiply their positive factors. -/
@[simp]
theorem yamabeRescale_yamabeRescale
    {g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    {u v : M → ℝ} {hu : ContMDiff I 𝓘(ℝ) k u} {hv : ContMDiff I 𝓘(ℝ) k v}
    {hup : ∀ x, 0 < u x} {hvp : ∀ x, 0 < v x} :
    yamabeRescale (yamabeRescale g u hu hup) v hv hvp =
      yamabeRescale g (fun x ↦ u x * v x) (hu.mul hv)
        (fun x ↦ mul_pos (hup x) (hvp x)) := by
  ext x a b
  simp only [yamabeRescale_inner, Real.mul_rpow (hup x).le (hvp x).le]
  ring

/-- The reciprocal positive factor undoes a conformal change. -/
-- Cancel before the composition rule replaces the factors by their product.
@[simp high]
theorem yamabeRescale_yamabeRescale_inv
    {g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    {u : M → ℝ} {hu : ContMDiff I 𝓘(ℝ) k u} {hp : ∀ x, 0 < u x} :
    yamabeRescale (yamabeRescale g u hu hp) (fun x ↦ (u x)⁻¹)
      (hu.inv₀ (fun x ↦ (hp x).ne')) (fun x ↦ inv_pos.mpr (hp x)) = g := by
  ext x a b
  simp [(hp x).ne']

/-- Positive conformal factors are determined by the rescaled metric when the
model space is nonzero and its dimension is not two. -/
@[simp]
theorem yamabeRescale_eq_iff [Nontrivial E]
    {g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    {u v : M → ℝ} {hu : ContMDiff I 𝓘(ℝ) k u} {hv : ContMDiff I 𝓘(ℝ) k v}
    {hup : ∀ x, 0 < u x} {hvp : ∀ x, 0 < v x}
    (hdim : Module.finrank ℝ E ≠ 2) :
    yamabeRescale g u hu hup = yamabeRescale g v hv hvp ↔ u = v := by
  constructor
  · intro h
    funext x
    let e := (FiberBundle.trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)
    have : Nontrivial (TangentSpace I x) := e.toEquiv.nontrivial
    obtain ⟨w, hw⟩ := exists_ne (0 : TangentSpace I x)
    have heq := congrArg (fun q : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _) ↦
      q.inner x w w) h
    simp only [yamabeRescale_inner] at heq
    have hpowers := mul_right_cancel₀ (g.pos x w hw).ne' heq
    exact (Real.rpow_left_inj (hup x).le (hvp x).le
      (div_ne_zero (by norm_num) (sub_ne_zero.mpr (by exact_mod_cast hdim)))).mp hpowers
  · rintro rfl
    rfl

/-- Every metric in the conformal class has a unique positive `C^k` Yamabe factor,
when the tangent fibres are nonzero and the dimension is not two. -/
theorem mem_conformalClass_iff_existsUnique_yamabeRescale [Nontrivial E]
    {g h : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _)}
    (hdim : Module.finrank ℝ E ≠ 2) :
    h ∈ conformalClass g ↔
      ∃! u : M → ℝ, ∃ (hu : ContMDiff I 𝓘(ℝ) k u) (hp : ∀ x, 0 < u x),
        yamabeRescale g u hu hp = h := by
  constructor
  · intro hh
    obtain ⟨u, hu, hp, heq⟩ := (mem_conformalClass_iff_exists_yamabeRescale hdim).mp hh
    refine ⟨u, ⟨hu, hp, heq⟩, ?_⟩
    rintro v ⟨hv, hvp, hv_eq⟩
    exact (yamabeRescale_eq_iff hdim).mp (hv_eq.trans heq.symm)
  · rintro ⟨u, ⟨hu, hp, rfl⟩, -⟩
    exact yamabeRescale_mem_conformalClass

end TauCeti
