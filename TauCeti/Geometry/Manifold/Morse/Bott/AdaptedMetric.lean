/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Geometry.Manifold.Morse.Bott.Coordinates
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The fibre metric adapted to the normal Hessian of a Morse–Bott submanifold

Let `i : S → M` be a nondegenerate critical submanifold of `f`, and let `g` be a fibre metric on
its normal bundle. The normal space at `s` splits as `ν⁻ s ⊕ ν⁺ s` into the negative and positive
normal spaces relative to `g`, on which the normal Hessian `Hess` is negative and positive
definite, and which are `Hess`-orthogonal. Write `v = v⁻ + v⁺` for this splitting, with `v⁻ = P v`
for the projection `P` along `ν⁺`
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.negativeNormalProjection`).
The **adapted metric** is

`g' (v, w) = (Hess (v⁺, w⁺) - Hess (v⁻, w⁻)) / 2`

(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.adaptedMetric`). It is a fibre metric
in which the two spaces are still orthogonal, and in which the normal Hessian is twice the
difference of the squared norms of the two components:

`Hess (v, v) / 2 = ‖v⁺‖² - ‖v⁻‖²`.

So if, near the critical submanifold, `f` is its critical value plus half the normal Hessian of the
normal coordinate, as in the parametric Morse lemma, then in the norm of `g'` it takes the form
`c - ‖u‖² + ‖v‖²` on `ν⁻ ⊕ ν⁺`. This is the quadratic model in which Milnor's handle retraction
runs fibrewise (`TauCeti.bundleQuadraticHandleRetraction`), and its disc bundle of radius `√ε` in
`ν⁻` is the one attached when the critical level is crossed. The metric `g'` is the analogue of the
normalized Morse chart, in which the Hessian is diagonal with entries `±2`, without a choice of
basis.

The negative and positive normal spaces relative to `g'` are those relative to `g`
(`IsNondegenerateCriticalSubmanifold.negativeNormalSpace_adaptedMetric`): in `g'` the normal
Hessian acts as `-2` on `ν⁻` and as `2` on `ν⁺`. When `g` is a `C^k` fibre metric, `f` is
`C^{k+2}` along the submanifold and the embedding is `C^{k+1}`, `g'` is again `C^k`
(`IsNondegenerateCriticalSubmanifold.contMDiffAdaptedMetric`): read in a normal-bundle
trivialization, it is `(u, v) ↦ (Q (u - p u) (v - p v) - Q (p u) (p v)) / 2` for the `C^k` families
`Q` of the normal Hessian and `p` of the projections onto `ν⁻`.

## Main declarations

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `adaptedMetric`: the fibre metric adapted to the normal Hessian, with `adaptedMetric_inner`.
* `adaptedMetric_inner_of_mem_negativeNormalSpace`,
  `adaptedMetric_inner_of_mem_positiveNormalSpace` and
  `adaptedMetric_inner_eq_zero_of_mem_negativeNormalSpace`: on `ν⁻` it is `-Hess / 2`, on `ν⁺` it is
  `Hess / 2`, and `ν⁻` and `ν⁺` are orthogonal for it.
* `normalHessian_apply_eq`: `Hess (v, w) = 2 (g' (v⁺, w⁺) - g' (v⁻, w⁻))`, so in particular
  `Hess (v, v) = 2 (‖v⁺‖² - ‖v⁻‖²)` in `g'`.
* `negativeNormalSpace_adaptedMetric`, `positiveNormalSpace_adaptedMetric` and
  `negativeNormalProjection_adaptedMetric`: the splitting is the same for `g'` as for `g`.
* `contMDiffAdaptedMetric`: the adapted metric of a `C^k` fibre metric as a `C^k` fibre metric.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 2.2.
-/

public section

open Bundle Set Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E]

section Pointwise

variable [IsManifold I 2 M] (h : i.IsNondegenerateCriticalSubmanifold f)
  (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- The bilinear form `(v, w) ↦ (Hess (v⁺, w⁺) - Hess (v⁻, w⁻)) / 2` on the normal space, where
`v⁻` and `v⁺` are the components of `v` in the negative and positive normal spaces relative to
`g`. -/
private def adaptedForm (s : S) : LinearMap.BilinForm ℝ (i.NormalSpace s hn) :=
  (2⁻¹ : ℝ) • ((h.normalHessian hn s).compl₁₂ (1 - h.negativeNormalProjection hn g s)
      (1 - h.negativeNormalProjection hn g s) -
    (h.normalHessian hn s).compl₁₂ (h.negativeNormalProjection hn g s)
      (h.negativeNormalProjection hn g s))

private theorem adaptedForm_apply {s : S} (v w : i.NormalSpace s hn) :
    h.adaptedForm hn g s v w =
      (h.normalHessian hn s (v - h.negativeNormalProjection hn g s v)
          (w - h.negativeNormalProjection hn g s w) -
        h.normalHessian hn s (h.negativeNormalProjection hn g s v)
          (h.negativeNormalProjection hn g s w)) / 2 := by
  simp [adaptedForm, div_eq_inv_mul]

private theorem adaptedForm_symm {s : S} (v w : i.NormalSpace s hn) :
    h.adaptedForm hn g s v w = h.adaptedForm hn g s w v := by
  simp only [adaptedForm_apply, (h.isSymm_normalHessian hn s).eq (v - _),
    (h.isSymm_normalHessian hn s).eq (h.negativeNormalProjection hn g s v)]

private theorem adaptedForm_pos {s : S} {v : i.NormalSpace s hn} (hv : v ≠ 0) :
    0 < h.adaptedForm hn g s v v := by
  set P := h.negativeNormalProjection hn g s
  rw [adaptedForm_apply]
  have hneg : h.normalHessian hn s (P v) (P v) ≤ 0 := by
    rcases eq_or_ne (P v) 0 with h0 | h0
    · simp [h0]
    · exact (h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g
        (h.negativeNormalProjection_apply_mem hn g v) h0).le
  have hpos : 0 ≤ h.normalHessian hn s (v - P v) (v - P v) := by
    rcases eq_or_ne (v - P v) 0 with h0 | h0
    · simp [h0]
    · exact (h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g
        (h.sub_negativeNormalProjection_apply_mem hn g v) h0).le
  -- The two components of the nonzero vector `v` do not both vanish.
  rcases eq_or_ne (P v) 0 with h0 | h0
  · have h1 : v - P v ≠ 0 := by simpa [h0] using hv
    have := h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g
      (h.sub_negativeNormalProjection_apply_mem hn g v) h1
    linarith
  · have := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g
      (h.negativeNormalProjection_apply_mem hn g v) h0
    linarith

/-- The bilinear form `adaptedForm` read in the coordinates of a basis of the normal space, where
it is a continuous bilinear map of normed spaces. -/
private def adaptedFormCoord (s : S) :
    (Fin (finrank ℝ (i.NormalSpace s hn)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (i.NormalSpace s hn)) → ℝ) →L[ℝ] ℝ :=
  ((h.adaptedForm hn g s).compl₁₂
    (Module.finBasis ℝ (i.NormalSpace s hn)).equivFun.symm.toLinearMap
    (Module.finBasis ℝ (i.NormalSpace s hn)).equivFun.symm.toLinearMap).toContinuousBilinearMap

@[simp]
private theorem adaptedFormCoord_apply {s : S} (x y : Fin (finrank ℝ (i.NormalSpace s hn)) → ℝ) :
    h.adaptedFormCoord hn g s x y =
      h.adaptedForm hn g s ((Module.finBasis ℝ (i.NormalSpace s hn)).equivFun.symm x)
        ((Module.finBasis ℝ (i.NormalSpace s hn)).equivFun.symm y) := by
  simp [adaptedFormCoord]

/-- **The fibre metric adapted to the normal Hessian.** For a Morse–Bott submanifold with a fibre
metric `g` on its normal bundle, the fibre metric `(v, w) ↦ (Hess (v⁺, w⁺) - Hess (v⁻, w⁻)) / 2`,
where `v⁻` and `v⁺` are the components of `v` in the negative and positive normal spaces relative
to `g`. In it the normal Hessian is `2 (‖v⁺‖² - ‖v⁻‖²)` (`normalHessian_apply_eq`). -/
def adaptedMetric : RiemannianMetric fun s ↦ i.NormalSpace s hn where
  inner s := (h.adaptedForm hn g s).toContinuousBilinearMap
  symm s v w := by
    simp only [LinearMap.toContinuousBilinearMap_apply, h.adaptedForm_symm hn g v w]
  pos s v hv := by
    simpa only [LinearMap.toContinuousBilinearMap_apply] using h.adaptedForm_pos hn g hv
  continuousAt s := by
    -- Read the form through the coordinates of a basis.
    let e := (Module.finBasis ℝ (i.NormalSpace s hn)).equivFun
    have he : Continuous e := LinearMap.continuous_of_finiteDimensional e.toLinearMap
    refine ((((h.adaptedFormCoord hn g s).continuous.comp he).clm_apply he).congr
      fun v ↦ ?_).continuousAt
    simp [e]
  isVonNBounded s := by
    -- In the coordinates of a basis, a positive definite form has a bounded unit set.
    let e := (Module.finBasis ℝ (i.NormalSpace s hn)).equivFun
    have hb : Bornology.IsVonNBounded ℝ {v | h.adaptedFormCoord hn g s v v < 1} :=
      (h.adaptedFormCoord hn g s).isVonNBounded_setOf_lt_one_of_pos fun v hv ↦ by
        rw [adaptedFormCoord_apply]
        exact h.adaptedForm_pos hn g ((map_ne_zero_iff _ e.symm.injective).2 hv)
    refine (hb.image (LinearMap.toContinuousLinearMap e.symm.toLinearMap)).subset ?_
    intro v hv
    refine ⟨e v, ?_, by simp⟩
    rw [Set.mem_ofPred_eq, adaptedFormCoord_apply, LinearEquiv.symm_apply_apply]
    simpa using hv

/-- The adapted metric is `(Hess (v⁺, w⁺) - Hess (v⁻, w⁻)) / 2`, with `v⁻ = P v` and
`v⁺ = v - P v` for the projection `P` onto the negative normal space along the positive one. -/
theorem adaptedMetric_inner {s : S} (v w : i.NormalSpace s hn) :
    (h.adaptedMetric hn g).inner s v w =
      (h.normalHessian hn s (v - h.negativeNormalProjection hn g s v)
          (w - h.negativeNormalProjection hn g s w) -
        h.normalHessian hn s (h.negativeNormalProjection hn g s v)
          (h.negativeNormalProjection hn g s w)) / 2 := by
  simp only [adaptedMetric, LinearMap.toContinuousBilinearMap_apply, adaptedForm_apply]

/-- **On the negative normal space the adapted metric is `-Hess / 2`.** -/
theorem adaptedMetric_inner_of_mem_negativeNormalSpace {s : S} {v : i.NormalSpace s hn}
    (hv : v ∈ h.negativeNormalSpace hn g s) (w : i.NormalSpace s hn) :
    (h.adaptedMetric hn g).inner s v w = -h.normalHessian hn s v w / 2 := by
  rw [adaptedMetric_inner, h.negativeNormalProjection_apply_of_mem hn g hv, sub_self,
    h.normalHessian_apply_eq_add hn g v w, h.negativeNormalProjection_apply_of_mem hn g hv,
    sub_self]
  simp

/-- **On the positive normal space the adapted metric is `Hess / 2`.** -/
theorem adaptedMetric_inner_of_mem_positiveNormalSpace {s : S} {v : i.NormalSpace s hn}
    (hv : v ∈ h.positiveNormalSpace hn g s) (w : i.NormalSpace s hn) :
    (h.adaptedMetric hn g).inner s v w = h.normalHessian hn s v w / 2 := by
  have hP : h.negativeNormalProjection hn g s v = 0 :=
    h.negativeNormalProjection_apply_eq_zero_of_mem hn g hv
  rw [adaptedMetric_inner, h.normalHessian_apply_eq_add hn g v w, hP]
  simp

/-- **The negative and positive normal spaces are orthogonal for the adapted metric.** -/
theorem adaptedMetric_inner_eq_zero_of_mem_negativeNormalSpace {s : S} {v w : i.NormalSpace s hn}
    (hv : v ∈ h.negativeNormalSpace hn g s) (hw : w ∈ h.positiveNormalSpace hn g s) :
    (h.adaptedMetric hn g).inner s v w = 0 := by
  rw [h.adaptedMetric_inner_of_mem_negativeNormalSpace hn g hv,
    h.normalHessian_eq_zero_of_mem_negativeNormalSpace hn g hv hw, neg_zero, zero_div]

/-- **The normal Hessian in the adapted metric.** The normal Hessian of `v` and `w` is twice the
adapted inner product of their positive components minus twice that of their negative components.
For `w = v` it is twice the squared norm of the positive component minus twice the squared norm of
the negative component, both taken in the adapted metric. -/
theorem normalHessian_apply_eq {s : S} (v w : i.NormalSpace s hn) :
    h.normalHessian hn s v w =
      2 * ((h.adaptedMetric hn g).inner s (v - h.negativeNormalProjection hn g s v)
          (w - h.negativeNormalProjection hn g s w) -
        (h.adaptedMetric hn g).inner s (h.negativeNormalProjection hn g s v)
          (h.negativeNormalProjection hn g s w)) := by
  rw [h.adaptedMetric_inner_of_mem_positiveNormalSpace hn g
      (h.sub_negativeNormalProjection_apply_mem hn g v),
    h.adaptedMetric_inner_of_mem_negativeNormalSpace hn g
      (h.negativeNormalProjection_apply_mem hn g v),
    h.normalHessian_apply_eq_add hn g v w]
  ring

/-- The normal Hessian acts as `-2` times the adapted metric on the negative normal space. -/
private theorem negativeNormalSpace_le_adaptedMetric (s : S) :
    h.negativeNormalSpace hn g s ≤ h.negativeNormalSpace hn (h.adaptedMetric hn g) s := by
  intro v hv
  have hv' : v ∈ ((h.adaptedMetric hn g).inner s).toBilinForm.relativeEigenspace
      (h.normalHessian hn s) (-2 : ℝ) :=
    LinearMap.BilinForm.mem_relativeEigenspace_iff.mpr fun w ↦ by
      rw [ContinuousLinearMap.toBilinForm_apply,
        h.adaptedMetric_inner_of_mem_negativeNormalSpace hn g hv]
      ring
  rw [IsCriticalSubmanifold.negativeNormalSpace_def]
  exact LinearMap.BilinForm.relativeEigenspace_le_relativeSpectralSubspace
    (show (-2 : ℝ) ∈ Iio 0 by norm_num) hv'

/-- The normal Hessian acts as `2` times the adapted metric on the positive normal space. -/
private theorem positiveNormalSpace_le_adaptedMetric (s : S) :
    h.positiveNormalSpace hn g s ≤ h.positiveNormalSpace hn (h.adaptedMetric hn g) s := by
  intro v hv
  have hv' : v ∈ ((h.adaptedMetric hn g).inner s).toBilinForm.relativeEigenspace
      (h.normalHessian hn s) (2 : ℝ) :=
    LinearMap.BilinForm.mem_relativeEigenspace_iff.mpr fun w ↦ by
      rw [ContinuousLinearMap.toBilinForm_apply,
        h.adaptedMetric_inner_of_mem_positiveNormalSpace hn g hv]
      ring
  rw [IsCriticalSubmanifold.positiveNormalSpace_def]
  exact LinearMap.BilinForm.relativeEigenspace_le_relativeSpectralSubspace
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) hv'

/-- **The adapted metric has the same negative normal space as `g`.** -/
@[simp]
theorem negativeNormalSpace_adaptedMetric (s : S) :
    h.negativeNormalSpace hn (h.adaptedMetric hn g) s = h.negativeNormalSpace hn g s := by
  refine ((h.negativeNormalSpace_le_adaptedMetric hn g s).antisymm fun v hv ↦ ?_).symm
  -- The positive component of `v` lies in both normal spaces of the adapted metric.
  have hsub : v - h.negativeNormalProjection hn g s v ∈
      h.negativeNormalSpace hn (h.adaptedMetric hn g) s ⊓
        h.positiveNormalSpace hn (h.adaptedMetric hn g) s :=
    ⟨sub_mem hv (h.negativeNormalSpace_le_adaptedMetric hn g s
      (h.negativeNormalProjection_apply_mem hn g v)),
      h.positiveNormalSpace_le_adaptedMetric hn g s
        (h.sub_negativeNormalProjection_apply_mem hn g v)⟩
  rw [(h.disjoint_negativeNormalSpace_positiveNormalSpace hn _).eq_bot, Submodule.mem_bot,
    sub_eq_zero] at hsub
  exact hsub ▸ h.negativeNormalProjection_apply_mem hn g v

/-- **The adapted metric has the same positive normal space as `g`.** -/
@[simp]
theorem positiveNormalSpace_adaptedMetric (s : S) :
    h.positiveNormalSpace hn (h.adaptedMetric hn g) s = h.positiveNormalSpace hn g s := by
  refine ((h.positiveNormalSpace_le_adaptedMetric hn g s).antisymm fun v hv ↦ ?_).symm
  -- The negative component of `v` lies in both normal spaces of the adapted metric.
  have hneg : h.negativeNormalProjection hn g s v ∈
      h.negativeNormalSpace hn (h.adaptedMetric hn g) s ⊓
        h.positiveNormalSpace hn (h.adaptedMetric hn g) s := by
    refine ⟨h.negativeNormalSpace_le_adaptedMetric hn g s
      (h.negativeNormalProjection_apply_mem hn g v), ?_⟩
    simpa using sub_mem hv (h.positiveNormalSpace_le_adaptedMetric hn g s
      (h.sub_negativeNormalProjection_apply_mem hn g v))
  rw [(h.disjoint_negativeNormalSpace_positiveNormalSpace hn _).eq_bot, Submodule.mem_bot,
    negativeNormalProjection_apply_eq_zero_iff] at hneg
  exact hneg

/-- **The adapted metric has the same projection onto the negative normal space as `g`.** -/
@[simp]
theorem negativeNormalProjection_adaptedMetric (s : S) :
    h.negativeNormalProjection hn (h.adaptedMetric hn g) s = h.negativeNormalProjection hn g s := by
  ext v
  set P' := h.negativeNormalProjection hn (h.adaptedMetric hn g) s
  have h₁ : P' v ∈ h.negativeNormalSpace hn g s := by
    simpa using h.negativeNormalProjection_apply_mem hn (h.adaptedMetric hn g) v
  have h₂ : v - P' v ∈ h.positiveNormalSpace hn g s := by
    simpa using h.sub_negativeNormalProjection_apply_mem hn (h.adaptedMetric hn g) v
  exact (h.negativeNormalProjection_apply_eq_of_mem hn g h₁ h₂).symm

end Pointwise

section Smooth

variable [FiniteDimensional ℝ E'] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold J (k + 1) S]

/-- **The adapted metric of a `C^k` fibre metric is `C^k`.** Let `i` be a nondegenerate critical
submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class `C^{k+1}`, and let `g` be
a `C^k` fibre metric on the normal bundle, with fibre model `P`. Then the adapted metric of `g` is a
`C^k` section of the bundle of bilinear forms on the normal bundle. -/
theorem contMDiff_adaptedMetric (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff J (J.prod 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ)) k fun s ↦
      TotalSpace.mk' (P →L[ℝ] P →L[ℝ] ℝ)
        (E := fun s ↦ i.NormalSpace s hn →L[ℝ] i.NormalSpace s hn →L[ℝ] ℝ) s
        ((h.adaptedMetric hn g.toRiemannianMetric).inner s) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  intro s₀
  set e := i.normalSpaceTrivialization hn hdim s₀
  have hs₀ : s₀ ∈ e.baseSet := i.mem_normalSpaceTrivialization_baseSet hn hdim s₀
  -- In the trivialization at `s₀`, the projections onto the negative normal spaces are a `C^k`
  -- family `p`, and the normal Hessian is a `C^k` family `Q` of bilinear forms.
  obtain ⟨p, hp, hps⟩ := h.exists_contMDiffOn_negativeNormalSpace_eq_map hn hk hf hdim g s₀
  simp only [normalSpaceFiberBundle_trivializationAt] at hp hps
  obtain ⟨Q, hQ, hQs⟩ :=
    h.toIsCriticalSubmanifold.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn
      (le_self_add.trans hk) hf hdim s₀
  -- The adapted metric reads as the same expression in `p` and `Q`.
  set φ : S → P →L[ℝ] P →L[ℝ] ℝ := fun s ↦ (2⁻¹ : ℝ) •
    ((ContinuousLinearMap.precomp ℝ (1 - p s)).comp ((Q s).comp (1 - p s)) -
      (ContinuousLinearMap.precomp ℝ (p s)).comp ((Q s).comp (p s)))
  have hφ : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k φ e.baseSet := by
    have hpb : ContDiff ℝ k fun q : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P) ↦
        (ContinuousLinearMap.precomp ℝ q.2).comp (q.1.comp q.2) :=
      ContinuousLinearMap.contDiff_precomp_comp
    have hΦ : ContDiff ℝ k fun q : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P) ↦ (2⁻¹ : ℝ) •
        ((ContinuousLinearMap.precomp ℝ (1 - q.2)).comp (q.1.comp (1 - q.2)) -
          (ContinuousLinearMap.precomp ℝ q.2).comp (q.1.comp q.2)) :=
      ((hpb.comp (contDiff_fst.prodMk (contDiff_const.sub contDiff_snd))).sub hpb).const_smul _
    have hQp : ContMDiffOn J 𝓘(ℝ, (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P)) k (fun s ↦ (Q s, p s))
        e.baseSet :=
      hQ.prodMk_space hp
    exact fun x hx ↦ hΦ.comp_contMDiffWithinAt (f := fun s ↦ (Q s, p s)) (hQp x hx)
  have heq {s : S} (hs : s ∈ e.baseSet) (u v : P) :
      φ s u v = (h.adaptedMetric hn g.toRiemannianMetric).inner s (e.symm s u) (e.symm s v) := by
    have hsub (w : P) : e.symm s w - e.symm s (p s w) = e.symm s ((1 - p s) w) := by
      rw [sub_apply, one_apply_eq_self, ← e.symmₗ_apply (R := ℝ) hs,
        ← e.symmₗ_apply (R := ℝ) hs, ← e.symmₗ_apply (R := ℝ) hs, ← map_sub]
    have hQe (x y : P) : h.normalHessian hn s (e.symm s x) (e.symm s y) = Q s x y :=
      (hQs s hs x y).1
    obtain ⟨-, -, -, -, -, hpe⟩ := hps s hs
    rw [adaptedMetric_inner, ← hpe, ← hpe, hsub, hsub, hQe, hQe]
    simp only [φ, smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply, smul_eq_mul]
    ring
  refine (contMDiffAt_hom_bundle _).2 ⟨contMDiffAt_id,
    (hφ.contMDiffAt (e.open_baseSet.mem_nhds hs₀)).congr_of_eventuallyEq ?_⟩
  filter_upwards [e.open_baseSet.mem_nhds hs₀] with s hs
  have hs' : s ∈ (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).baseSet := by
    rwa [normalSpaceFiberBundle_trivializationAt]
  ext u v
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) (F₃ := ℝ) (E₃ := Trivial S ℝ) hs' hs' (Set.mem_univ _)]
  simp only [normalSpaceFiberBundle_trivializationAt]
  simpa using (heq hs u v).symm

/-- **The adapted metric as a `C^k` fibre metric.** For a `C^k` fibre metric `g` on the normal
bundle of a Morse–Bott submanifold, with `f` of class `C^{k+2}` along it and `i` of class
`C^{k+1}`, the fibre metric adapted to the normal Hessian
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.adaptedMetric`) is again `C^k`. -/
def contMDiffAdaptedMetric (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  { inner := (h.adaptedMetric hn g.toRiemannianMetric).inner
    symm := (h.adaptedMetric hn g.toRiemannianMetric).symm
    pos := (h.adaptedMetric hn g.toRiemannianMetric).pos
    isVonNBounded := (h.adaptedMetric hn g.toRiemannianMetric).isVonNBounded
    contMDiff := h.contMDiff_adaptedMetric hn hk hf hdim g }

@[simp]
theorem toRiemannianMetric_contMDiffAdaptedMetric (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    (h.contMDiffAdaptedMetric hn hk hf hdim g).toRiemannianMetric =
      h.adaptedMetric hn g.toRiemannianMetric :=
  (rfl)

/-- The inner product of the `C^k` adapted metric is that of the adapted metric. -/
@[simp]
theorem contMDiffAdaptedMetric_inner (h : i.IsNondegenerateCriticalSubmanifold f)
    (hk : k + 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    (h.contMDiffAdaptedMetric hn hk hf hdim g).inner =
      (h.adaptedMetric hn g.toRiemannianMetric).inner :=
  (rfl)

end Smooth

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
