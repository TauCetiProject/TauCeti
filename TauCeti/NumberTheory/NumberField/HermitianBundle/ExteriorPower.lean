/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.GramForm
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.NumberTheory.NumberField.HermitianBundle.BaseChange

import TauCeti.LinearAlgebra.ExteriorPower.Localization

/-!
# Exterior powers and determinants of hermitian vector bundles

For a hermitian metric `h` on an `𝓞 K`-module `E`, the exterior power
`⋀ⁿ E` carries the metric whose form at each complex embedding `σ` is the Gram form of `h_σ` on
the complex fibre `(⋀ⁿ E)_σ = ⋀ⁿ_ℂ E_σ`, identified by
`NumberField.ComplexEmbedding.Codomain.exteriorPowerEquiv`; the Gram form is
`(innerₛₗ ℂ).sesqExteriorPower n`. On decomposable vectors it is the Gram determinant

  `(⋀ⁿ h)_σ(x₁ ∧ ⋯ ∧ xₙ, y₁ ∧ ⋯ ∧ yₙ) = det (h_σ(xᵢ, yⱼ))`,

and these values determine it. The top exterior power of a hermitian vector bundle `Ē` of rank `r`
is the hermitian line `det Ē = Λʳ Ē`, the input for defining the Arakelov degree of a hermitian
vector bundle of higher rank.

## Main definitions

* `TauCeti.HermitianMetric.exteriorPower`: the metric on `⋀ⁿ E`.
* `TauCeti.HermitianMetric.IsometryEquiv.exteriorPower`: the isometry `⋀ⁿ E ≅ ⋀ⁿ F` induced by an
  isometry `E ≅ F`.
* `TauCeti.HermitianBundle.exteriorPower`, `TauCeti.HermitianBundle.det`: the exterior powers
  `Λⁿ Ē`, of rank `(rank Ē).choose n`, and the determinant `det Ē = Λ^{rank Ē} Ē`, a hermitian
  line.

## Main results

* `TauCeti.HermitianMetric.exteriorPower_form_tmul_ιMulti`: the Gram-determinant formula.
* `TauCeti.HermitianMetric.ext_ιMulti`: metrics on `⋀ⁿ E` are determined by their values on
  decomposable vectors.
* `TauCeti.HermitianMetric.exteriorPower_rescale`: `⋀ⁿ (Ē(c)) = (⋀ⁿ Ē)(n c)`.
* `TauCeti.HermitianBundle.rank_det`: the determinant of a hermitian vector bundle is a line.
* `TauCeti.HermitianMetric.isometryEquivBaseChangeExteriorPower`: the exterior-power
  scalar-extension equivalence `TauCeti.exteriorPower.equivBaseChange` preserves the Gram metric.
* `TauCeti.HermitianBundle.isometryEquivBaseChangeDet`: base change preserves the metrized
  determinant, using rank preservation.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.2.
* P. Deligne, *Preuves des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616,
  §2.1.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate ComplexOrder

namespace TauCeti

open NumberField NumberField.ComplexEmbedding

namespace HermitianMetric

variable {K : Type*} [Field K]
variable {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F]
variable (h : HermitianMetric K E)

section Gram

/-- The complex fibre of `E` at `σ` as a normed group, with the norm of `h_σ`. -/
private abbrev fiberNormedAddCommGroup (σ : K →+* ℂ) : NormedAddCommGroup (Codomain σ ⊗[𝓞 K] E) :=
  (h.toCore σ).toNormedAddCommGroup

/-- The complex fibre of `E` at `σ` as an inner product space, with the inner product `h_σ`. -/
private abbrev fiberInnerProductSpace (σ : K →+* ℂ) :
    letI := h.fiberNormedAddCommGroup σ
    InnerProductSpace ℂ (Codomain σ ⊗[𝓞 K] E) :=
  .ofCore (h.toCore σ).toCore

/-- The Gram form of `h_σ` on the `n`-th complex exterior power of the complex fibre of `E`.
This definition and the lemmas below about it all install the same fibre instances
`fiberNormedAddCommGroup` and `fiberInnerProductSpace`, so the Gram-form lemmas apply to it as
stated. -/
private def fiberGram (σ : K →+* ℂ) (n : ℕ) :
    ⋀[ℂ]^n (Codomain σ ⊗[𝓞 K] E) →ₗ⋆[ℂ] ⋀[ℂ]^n (Codomain σ ⊗[𝓞 K] E) →ₗ[ℂ] ℂ :=
  letI := h.fiberNormedAddCommGroup σ
  letI := h.fiberInnerProductSpace σ
  (innerₛₗ ℂ).sesqExteriorPower n

private theorem fiberGram_ιMulti_ιMulti (σ : K →+* ℂ) {n : ℕ}
    (u v : Fin n → Codomain σ ⊗[𝓞 K] E) :
    h.fiberGram σ n (exteriorPower.ιMulti ℂ n u) (exteriorPower.ιMulti ℂ n v) =
      (Matrix.of fun i j ↦ h.form σ (u i) (v j)).det := by
  let _ := h.fiberNormedAddCommGroup σ
  let _ := h.fiberInnerProductSpace σ
  refine ((innerₛₗ ℂ).sesqExteriorPower_ιMulti_ιMulti n u v).trans ?_
  -- The inner product of the local inner product space is the form `h_σ`.
  simp only [innerₛₗ_apply_apply, ← h.inner_toCore]

private theorem isSymm_fiberGram (σ : K →+* ℂ) (n : ℕ) : (h.fiberGram σ n).IsSymm :=
  letI := h.fiberNormedAddCommGroup σ
  letI := h.fiberInnerProductSpace σ
  exteriorPower.isSymm_sesqExteriorPower_innerₛₗ n

private theorem fiberGram_self_pos (σ : K →+* ℂ) {n : ℕ} {u : ⋀[ℂ]^n (Codomain σ ⊗[𝓞 K] E)}
    (hu : u ≠ 0) : 0 < h.fiberGram σ n u u :=
  letI := h.fiberNormedAddCommGroup σ
  letI := h.fiberInnerProductSpace σ
  exteriorPower.sesqExteriorPower_innerₛₗ_self_pos hu

/-- The Gram form at `σ` on vectors `1 ⊗ (x₁ ∧ ⋯ ∧ xₙ)` of the complex fibre of `⋀ⁿ E`. -/
private theorem fiberGram_exteriorPowerEquiv_tmul_ιMulti (σ : K →+* ℂ) {n : ℕ}
    (x y : Fin n → E) :
    h.fiberGram σ n (Codomain.exteriorPowerEquiv σ E n (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n x))
        (Codomain.exteriorPowerEquiv σ E n (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n y)) =
      (Matrix.of fun i j ↦ h.form σ (1 ⊗ₜ x i) (1 ⊗ₜ y j)).det := by
  simp only [Codomain.exteriorPowerEquiv_tmul_ιMulti, map_one, one_smul, fiberGram_ιMulti_ιMulti]

/-- The Gram forms at complex conjugate embeddings are complex conjugate on `⋀ⁿ E`. -/
private theorem fiberGram_conjugate (σ : K →+* ℂ) {n : ℕ} (x y : ⋀[𝓞 K]^n E) :
    h.fiberGram (conjugate σ) n (Codomain.exteriorPowerEquiv _ E n (1 ⊗ₜ x))
        (Codomain.exteriorPowerEquiv _ E n (1 ⊗ₜ y)) =
      conj (h.fiberGram σ n (Codomain.exteriorPowerEquiv σ E n (1 ⊗ₜ x))
        (Codomain.exteriorPowerEquiv σ E n (1 ⊗ₜ y))) := by
  induction exteriorPower.mem_span_ιMulti x using Submodule.span_induction generalizing y with
  | mem _ hx =>
    obtain ⟨a, rfl⟩ := hx
    induction exteriorPower.mem_span_ιMulti y using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [fiberGram_exteriorPowerEquiv_tmul_ιMulti, fiberGram_exteriorPowerEquiv_tmul_ιMulti,
        RingHom.map_det]
      congr 1
      ext i j
      simp [h.form_conjugate_tmul]
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
    | smul a _ _ hy =>
      simp only [Codomain.tmul_smul, map_smul, smul_eq_mul, hy, map_mul, conjugate_coe_eq]
  | zero => simp
  | add _ _ _ _ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, h₁, h₂]
  | smul a _ _ hx =>
    simp only [Codomain.tmul_smul, map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul, hx, map_mul,
      conjugate_coe_eq, Complex.conj_conj]

end Gram

/-- The **exterior power** of a hermitian metric `h` on `E`: the metric on `⋀ⁿ E` whose form at
`σ` is the Gram form of `h_σ` on the complex fibre `(⋀ⁿ E)_σ = ⋀ⁿ_ℂ E_σ`, determined by
`(⋀ⁿ h)_σ(x₁ ∧ ⋯ ∧ xₙ, y₁ ∧ ⋯ ∧ yₙ) = det (h_σ(xᵢ, yⱼ))`
(`TauCeti.HermitianMetric.exteriorPower_form_tmul_ιMulti`). -/
def exteriorPower (n : ℕ) : HermitianMetric K (⋀[𝓞 K]^n E) where
  form σ := (h.fiberGram σ n ∘ₛₗ (Codomain.exteriorPowerEquiv σ E n).toLinearMap).compl₂
    (Codomain.exteriorPowerEquiv σ E n).toLinearMap
  isSymm_form σ := LinearMap.isSymm_def.mpr fun _ _ ↦ (h.isSymm_fiberGram σ n).eq _ _
  form_self_pos σ _ hu :=
    h.fiberGram_self_pos σ ((Codomain.exteriorPowerEquiv σ E n).map_ne_zero_iff.mpr hu)
  form_conjugate_tmul σ x y := h.fiberGram_conjugate σ x y

/-- **The Gram-determinant formula**:
`(⋀ⁿ h)_σ(x₁ ∧ ⋯ ∧ xₙ, y₁ ∧ ⋯ ∧ yₙ) = det (h_σ(xᵢ, yⱼ))`. -/
@[simp]
theorem exteriorPower_form_tmul_ιMulti (σ : K →+* ℂ) {n : ℕ} (x y : Fin n → E) :
    (h.exteriorPower n).form σ (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n x)
        (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n y) =
      (Matrix.of fun i j ↦ h.form σ (1 ⊗ₜ x i) (1 ⊗ₜ y j)).det :=
  h.fiberGram_exteriorPowerEquiv_tmul_ιMulti σ x y

/-- The squared norm of `1 ⊗ (x₁ ∧ ⋯ ∧ xₙ)` is the Gram determinant `det (h_σ(xᵢ, xⱼ))`. -/
theorem norm_exteriorPower_tmul_ιMulti_sq (σ : K →+* ℂ) {n : ℕ} (x : Fin n → E) :
    (h.exteriorPower n).norm σ (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n x) ^ 2 =
      (Matrix.of fun i j ↦ h.form σ (1 ⊗ₜ x i) (1 ⊗ₜ x j)).det.re := by
  rw [norm_sq, exteriorPower_form_tmul_ιMulti]

/-- The forms of a metric on `⋀ⁿ E` and of a metric on `F`, pulled back along a linear map
`f : ⋀ⁿ E → F`, agree on all of `⋀ⁿ E` once they agree on decomposable vectors. -/
theorem form_tmul_map_eq_of_ιMulti {n : ℕ} {g : HermitianMetric K (⋀[𝓞 K]^n E)}
    {g' : HermitianMetric K F} (f : ⋀[𝓞 K]^n E →ₗ[𝓞 K] F) (σ : K →+* ℂ)
    (hf : ∀ a b : Fin n → E,
      g'.form σ (1 ⊗ₜ f (exteriorPower.ιMulti (𝓞 K) n a))
          (1 ⊗ₜ f (exteriorPower.ιMulti (𝓞 K) n b)) =
        g.form σ (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n a) (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n b))
    (x y : ⋀[𝓞 K]^n E) :
    g'.form σ (1 ⊗ₜ f x) (1 ⊗ₜ f y) = g.form σ (1 ⊗ₜ x) (1 ⊗ₜ y) := by
  induction exteriorPower.mem_span_ιMulti x using Submodule.span_induction generalizing y with
  | mem _ hx =>
    obtain ⟨a, rfl⟩ := hx
    induction exteriorPower.mem_span_ιMulti y using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨b, rfl⟩ := hy
      exact hf a b
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add, h₁, h₂]
    | smul c _ _ hy => simp only [map_smul, Codomain.tmul_smul, hy]
  | zero => simp
  | add _ _ _ _ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add, LinearMap.add_apply, h₁, h₂]
  | smul c _ _ hx => simp only [map_smul, Codomain.tmul_smul, LinearMap.map_smulₛₗ₂, hx]

/-- Two hermitian metrics on `⋀ⁿ E` are equal when their forms agree on decomposable vectors. -/
theorem ext_ιMulti {n : ℕ} {g g' : HermitianMetric K (⋀[𝓞 K]^n E)}
    (hg : ∀ σ (a b : Fin n → E),
      g.form σ (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n a) (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n b) =
        g'.form σ (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n a) (1 ⊗ₜ exteriorPower.ιMulti (𝓞 K) n b)) :
    g = g' :=
  ext_tmul _ fun σ x y ↦
    (form_tmul_map_eq_of_ιMulti LinearMap.id σ (fun a b ↦ (hg σ a b).symm) x y).symm

/-- Rescaling the metric by `c` rescales its `n`-th exterior power by `n c`: the norm of a
decomposable `n`-vector is multiplied by `e^{-n c}`. -/
theorem exteriorPower_rescale (c : ℝ) (n : ℕ) :
    (h.rescale c).exteriorPower n = (h.exteriorPower n).rescale (n * c) := by
  refine ext_ιMulti fun σ a b ↦ ?_
  have hmat : (Matrix.of fun i j ↦ (h.rescale c).form σ (1 ⊗ₜ a i) (1 ⊗ₜ b j)) =
      ((Real.exp (-2 * c) : ℝ) : ℂ) • Matrix.of fun i j ↦ h.form σ (1 ⊗ₜ a i) (1 ⊗ₜ b j) := by
    ext i j
    simp
  rw [exteriorPower_form_tmul_ιMulti, rescale_form_apply, exteriorPower_form_tmul_ιMulti, hmat,
    Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, ← Real.exp_natCast_mul,
    show (n : ℝ) * (-2 * c) = -2 * (n * c) by ring]

/-- The zeroth exterior power of any hermitian metric is the trivial line: `⋀⁰ E ≅ Ō_K` through
`exteriorPower.zeroEquiv`. -/
def isometryEquivExteriorPowerZero [NumberField K] :
    IsometryEquiv (h.exteriorPower 0) (trivial K) where
  toLinearEquiv := exteriorPower.zeroEquiv (𝓞 K) E
  form_tmul σ := form_tmul_map_eq_of_ιMulti _ σ fun a b ↦ by
    simp [Matrix.det_fin_zero]

@[simp]
theorem isometryEquivExteriorPowerZero_apply [NumberField K] (x : ⋀[𝓞 K]^0 E) :
    h.isometryEquivExteriorPowerZero x = exteriorPower.zeroEquiv (𝓞 K) E x :=
  (rfl)

/-- The first exterior power of a hermitian metric is the metric itself: `⋀¹ E ≅ E` through
`exteriorPower.oneEquiv`. -/
def isometryEquivExteriorPowerOne : IsometryEquiv (h.exteriorPower 1) h where
  toLinearEquiv := exteriorPower.oneEquiv (𝓞 K) E
  form_tmul σ := form_tmul_map_eq_of_ιMulti _ σ fun a b ↦ by
    simp [Matrix.det_unique]

@[simp]
theorem isometryEquivExteriorPowerOne_apply (x : ⋀[𝓞 K]^1 E) :
    h.isometryEquivExteriorPowerOne x = exteriorPower.oneEquiv (𝓞 K) E x :=
  (rfl)

section BaseChange

open TauCeti.exteriorPower (equivBaseChange_symm_tmul_ιMulti)

variable {L : Type*} [Field L] [Algebra K L]

/-- The canonical scalar-extension map preserves the forms on integral exterior vectors. -/
private theorem baseChange_exteriorPower_form_tmul (n : ℕ) (τ : L →+* ℂ)
    (x y : 𝓞 L ⊗[𝓞 K] (⋀[𝓞 K]^n E)) :
    (h.baseChange.exteriorPower n).form τ
        (1 ⊗ₜ (TauCeti.exteriorPower.equivBaseChange (𝓞 L) n).symm x)
        (1 ⊗ₜ (TauCeti.exteriorPower.equivBaseChange (𝓞 L) n).symm y) =
      ((h.exteriorPower n).baseChange (L := L)).form τ (1 ⊗ₜ x) (1 ⊗ₜ y) := by
  -- It suffices to compare Gram determinants on wedges of vectors from the original module.
  let w (a : Fin n → E) := (1 : 𝓞 L) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) n a
  have hspan : Submodule.span (𝓞 L) (Set.range w) = ⊤ := by
    have hspan' := Submodule.baseChange_span (R := 𝓞 K) (𝓞 L)
      (Set.range (exteriorPower.ιMulti (𝓞 K) n (M := E)))
    rw [exteriorPower.ιMulti_span, Submodule.baseChange_top, ← Set.range_comp] at hspan'
    exact hspan'.symm
  have hx : x ∈ Submodule.span (𝓞 L) (Set.range w) := hspan ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span (𝓞 L) (Set.range w) := hspan ▸ Submodule.mem_top
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    simp only [w, equivBaseChange_symm_tmul_ιMulti, one_smul,
      exteriorPower_form_tmul_ιMulti, baseChange_form_tmul_tmul, map_one, one_mul]
  | zero_left | zero_right => simp
  | add_left _ _ _ _ _ _ h₁ h₂ =>
    simp only [map_add, TensorProduct.tmul_add, LinearMap.add_apply, h₁, h₂]
  | add_right _ _ _ _ _ _ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add, h₁, h₂]
  | smul_left _ _ _ _ _ ih => simp only [map_smul, Codomain.tmul_smul, LinearMap.map_smulₛₗ₂, ih]
  | smul_right _ _ _ _ _ ih => simp only [map_smul, Codomain.tmul_smul, ih]

/-- The canonical scalar-extension comparison is an isometry from the base change of the
`n`-th exterior power metric to the exterior power of the base-changed metric
(Bost, Appendice A.2). -/
def isometryEquivBaseChangeExteriorPower (n : ℕ) :
    IsometryEquiv ((h.exteriorPower n).baseChange (L := L)) (h.baseChange.exteriorPower n) where
  toLinearEquiv := (TauCeti.exteriorPower.equivBaseChange (𝓞 L) n).symm
  form_tmul := h.baseChange_exteriorPower_form_tmul n

/-- The underlying linear equivalence of the metric comparison is the canonical
exterior-power base-change equivalence, in the direction from tensors to wedges. -/
@[simp]
theorem isometryEquivBaseChangeExteriorPower_toLinearEquiv (n : ℕ) :
    (h.isometryEquivBaseChangeExteriorPower (L := L) n).toLinearEquiv =
      (TauCeti.exteriorPower.equivBaseChange (𝓞 L) n).symm :=
  (rfl)

/-- On a scalar tensored with a decomposable vector, the isometry applies base change to each
wedge factor and multiplies by the scalar. -/
@[simp]
theorem isometryEquivBaseChangeExteriorPower_tmul_ιMulti {n : ℕ} (a : 𝓞 L) (x : Fin n → E) :
    h.isometryEquivBaseChangeExteriorPower n (a ⊗ₜ exteriorPower.ιMulti (𝓞 K) n x) =
      a • exteriorPower.ιMulti (𝓞 L) n (fun i ↦ (1 : 𝓞 L) ⊗ₜ x i) := by
  rw [← IsometryEquiv.coe_toLinearEquiv, isometryEquivBaseChangeExteriorPower_toLinearEquiv,
    equivBaseChange_symm_tmul_ιMulti]

end BaseChange

namespace IsometryEquiv

variable {h} {h' : HermitianMetric K F}

/-- The isometry `⋀ⁿ E ≅ ⋀ⁿ F` induced by an isometry `e : E ≅ F`, sending
`x₁ ∧ ⋯ ∧ xₙ` to `e x₁ ∧ ⋯ ∧ e xₙ`. -/
def exteriorPower (e : IsometryEquiv h h') (n : ℕ) :
    IsometryEquiv (h.exteriorPower n) (h'.exteriorPower n) where
  toLinearEquiv := e.toLinearEquiv.exteriorPower n
  form_tmul σ := form_tmul_map_eq_of_ιMulti _ σ fun a b ↦ by
    simp only [LinearEquiv.coe_coe, LinearEquiv.exteriorPower_apply_ιMulti,
      exteriorPower_form_tmul_ιMulti, Function.comp_apply, coe_toLinearEquiv, form_tmul_map]

@[simp]
theorem exteriorPower_apply_ιMulti (e : IsometryEquiv h h') {n : ℕ} (a : Fin n → E) :
    e.exteriorPower n (_root_.exteriorPower.ιMulti (𝓞 K) n a) =
      _root_.exteriorPower.ιMulti (𝓞 K) n (e ∘ a) :=
  LinearEquiv.exteriorPower_apply_ιMulti _ n a

end IsometryEquiv

end HermitianMetric

namespace HermitianBundle

universe u v

variable {K : Type u} [Field K]

/-- The **`n`-th exterior power** `Λⁿ Ē` of a hermitian vector bundle: the module `⋀ⁿ Ē` with the
exterior power metric. -/
@[expose] def exteriorPower (Ē : HermitianBundle.{u, v} K) (n : ℕ) :
    HermitianBundle.{u, max u v} K where
  carrier := ⋀[𝓞 K]^n Ē
  metric := Ē.metric.exteriorPower n

theorem exteriorPower_metric (Ē : HermitianBundle.{u, v} K) (n : ℕ) :
    (Ē.exteriorPower n).metric = Ē.metric.exteriorPower n :=
  (rfl)

/-- The rank of `Λⁿ Ē` is `(rank Ē).choose n`. -/
@[simp]
theorem rank_exteriorPower (Ē : HermitianBundle.{u, v} K) (n : ℕ) :
    (Ē.exteriorPower n).rank = Ē.rank.choose n := by
  rw [rank_eq_finrank_tensorProduct, rank_eq_finrank_tensorProduct]
  exact ((TensorProduct.isBaseChange (𝓞 K) Ē K).exteriorPowerEquiv n).finrank_eq.trans
    (exteriorPower.finrank_eq (R := K) (M := K ⊗[𝓞 K] Ē) (n := n))

/-- The **determinant** `det Ē = Λ^{rank Ē} Ē` of a hermitian vector bundle, a hermitian line
(`TauCeti.HermitianBundle.rank_det`). -/
@[expose] def det (Ē : HermitianBundle.{u, v} K) : HermitianBundle.{u, max u v} K :=
  Ē.exteriorPower Ē.rank

theorem det_def (Ē : HermitianBundle.{u, v} K) : Ē.det = Ē.exteriorPower Ē.rank :=
  (rfl)

/-- The determinant of a hermitian vector bundle has rank one. -/
@[simp]
theorem rank_det (Ē : HermitianBundle.{u, v} K) : Ē.det.rank = 1 := by
  rw [det_def, rank_exteriorPower, Nat.choose_self]

/-- Formation of the determinant of a hermitian bundle commutes isometrically with base
change (Bost, Appendice A.2). -/
def isometryEquivBaseChangeDet {L : Type*} [Field L] [Algebra K L] (Ē : HermitianBundle.{u, v} K) :
    HermitianMetric.IsometryEquiv (Ē.det.baseChange (L := L)).metric
      (Ē.baseChange (L := L)).det.metric :=
  Eq.ndrec (motive := fun n ↦ HermitianMetric.IsometryEquiv
    (Ē.det.baseChange (L := L)).metric ((Ē.baseChange (L := L)).exteriorPower n).metric)
    (Ē.metric.isometryEquivBaseChangeExteriorPower (L := L) Ē.rank)
    (rank_baseChange (L := L) Ē).symm

/-- The determinant comparison sends a wedge to the wedge of its images under base change,
with the factors indexed by the unchanged rank. -/
@[simp]
theorem isometryEquivBaseChangeDet_tmul_ιMulti {L : Type*} [Field L] [Algebra K L]
    (Ē : HermitianBundle.{u, v} K) (a : 𝓞 L) (x : Fin Ē.rank → Ē) :
    Ē.isometryEquivBaseChangeDet (L := L) (a ⊗ₜ exteriorPower.ιMulti (𝓞 K) Ē.rank x) =
      a • exteriorPower.ιMulti (𝓞 L) (Ē.baseChange (L := L)).rank
        (fun i ↦ (1 : 𝓞 L) ⊗ₜ x (Fin.cast (rank_baseChange Ē) i)) := by
  have apply_cast (m : ℕ) (hm : Ē.rank = m) :
      (Eq.ndrec (motive := fun n ↦ HermitianMetric.IsometryEquiv
        (Ē.det.baseChange (L := L)).metric ((Ē.baseChange (L := L)).exteriorPower n).metric)
        (Ē.metric.isometryEquivBaseChangeExteriorPower (L := L) Ē.rank) hm)
        (a ⊗ₜ exteriorPower.ιMulti (𝓞 K) Ē.rank x) =
      a • exteriorPower.ιMulti (𝓞 L) m
        (fun i ↦ (1 : 𝓞 L) ⊗ₜ x (Fin.cast hm.symm i)) := by
    cases hm
    exact Ē.metric.isometryEquivBaseChangeExteriorPower_tmul_ιMulti a x
  exact apply_cast _ (rank_baseChange (L := L) Ē).symm

end HermitianBundle

end TauCeti
