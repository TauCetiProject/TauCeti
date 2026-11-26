/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.AdaptedMetric
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Geometry.Manifold.Morse.Bott.Tubular
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.LinearAlgebra.BilinearForm.NormalizingTransport
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The normal Hessian of a Morse–Bott submanifold in Sylvester form

Let `i : S → M` be a nondegenerate critical submanifold of a function `f`, with normal bundle `ν`,
normal Hessian `Hess`, and a fibre metric `g` on `ν`. The metric splits each normal space as
`ν⁻ s ⊕ ν⁺ s` into the negative and the positive normal space, with `v = v⁻ + v⁺` and
`v⁻ = P v` for the projection `P` onto `ν⁻` along `ν⁺`
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.negativeNormalProjection`).

This file constructs the canonical automorphism `N` of the normal bundle which carries the normal
Hessian to the positive-minus-negative fibre quadratic form of `g`:

`Hess (N v, N v) = g (v⁺, v⁺) - g (v⁻, v⁻)`

(`IsNondegenerateCriticalSubmanifold.normalHessian_normalHessianNormalization_apply_self`). On each
normal space `N` is the inverse square root `|K|^(-1/2)` of the operator `K` with
`g (K v) w = Hess (v, w)`, the normalizing transport of `Hess` relative to `g`
(`LinearMap.BilinForm.normalizingTransport`). It preserves `ν⁻` and `ν⁺`, on which it carries
`Hess` to `-g` and to `g`, and is the only endomorphism of the normal space with these properties
which is self-adjoint for `Hess` and has `0 ≤ g (N v, v)`. No eigenbasis of the normal Hessian is
chosen, so no smoothly varying eigenvectors are needed: this characterization, with the naturality
of the normalizing transport under linear equivalences
(`LinearMap.BilinForm.normalizingTransport_compl₁₂`), glues the local normalizations in the
normal-bundle trivializations
(`IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_normalHessian_normalization`), which are
the same smooth functions of the pair of forms in every chart. So for a `C^k` fibre metric `g`,
with `f` of class `C^{k+2}` along the submanifold and the embedding of class `C^{k+1}`, `N` is a
`C^k` automorphism of the normal bundle (`contMDiff_normalHessianNormalization` and
`normalHessianNormalizationDiffeomorph`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).

Composing the Morse–Bott lemma on the normal bundle
(`IsNondegenerateCriticalSubmanifold.exists_morseBott_partialDiffeomorph_normalBundle`), which
writes `f` near the submanifold as `f (Θ v) = f (i s) + ½ Hess (v, v)`, with `N` gives the
**parametric Morse lemma in Sylvester form**: there is a `C^k` partial diffeomorphism `Θ` from the
normal bundle to `M`, defined near the whole zero section and sending it to `i`, with

`f (Θ v) = f (i s) + ½ (g (v⁺, v⁺) - g (v⁻, v⁻))`

(`IsNondegenerateCriticalSubmanifold.exists_morseBott_partialDiffeomorph_normalBundle_inner_sub`).
Up to the factor `½`, this is the fibrewise model `c - |u|² + |w|²` of Milnor's handle, written
with the given metric.

The adapted metric `g'` of `g` (`IsNondegenerateCriticalSubmanifold.adaptedMetric`), in which
`Hess (v, v) / 2 = g' (v⁺, v⁺) - g' (v⁻, v⁻)`, is the pull-back of `g` along `N⁻¹ / √2`:
`g' (N u, N v) = g (u, v) / 2`
(`IsNondegenerateCriticalSubmanifold.adaptedMetric_inner_normalHessianNormalization`). So the two
normal forms, through the adapted metric and through `N`, agree up to this rescaling.

## Main definitions

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `normalHessianNormalization g s`: the automorphism `N` of the normal space at `s`.
* `normalHessianNormalizationDiffeomorph`: for a `C^k` fibre metric, `N` as a `C^k` automorphism
  of the total space of the normal bundle.

## Main results

* `normalHessian_normalHessianNormalization_apply_self`:
  `Hess (N v, N v) = g (v⁺, v⁺) - g (v⁻, v⁻)`.
* `eq_normalHessianNormalization`: the characterization of `N`.
* `negativeNormalProjection_normalHessianNormalization`: `N` commutes with the projection onto
  `ν⁻` along `ν⁺`.
* `adaptedMetric_inner_normalHessianNormalization`: `g' (N u, N v) = g (u, v) / 2`.
* `contMDiff_normalHessianNormalization`: for a `C^k` fibre metric, `N` is a `C^k` map of total
  spaces.
* `exists_morseBott_partialDiffeomorph_normalBundle_inner_sub`: the Morse–Bott lemma on the normal
  bundle with the positive-minus-negative fibre quadratic form of a fibre metric.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 2.2.
-/

public section

open Bundle Function Set Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

section Normalization

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E]

section Pointwise

variable [IsManifold I 2 M] (h : i.IsNondegenerateCriticalSubmanifold f)
  (g : RiemannianMetric fun s ↦ i.isImmersion.NormalSpace s hn) {s : S}

/-- **The normalization of the normal Hessian** of a Morse–Bott submanifold relative to a fibre
metric `g`: the automorphism `N` of the normal space at `s` which preserves the negative and the
positive normal spaces and carries the normal Hessian to `-g` on the first and to `g` on the
second, so that `Hess (N v, N v) = g (v⁺, v⁺) - g (v⁻, v⁻)`
(`normalHessian_normalHessianNormalization_apply_self`). It is the inverse square root `|K|^(-1/2)`
of the operator `K` with `g (K v) w = Hess (v, w)`, the normalizing transport of the normal Hessian
relative to `g` (`LinearMap.BilinForm.normalizingTransport`). It is characterized by these
properties together with `0 ≤ g (N v, v)` and self-adjointness for the normal Hessian
(`eq_normalHessianNormalization`). -/
def normalHessianNormalization (s : S) :
    i.isImmersion.NormalSpace s hn ≃ₗ[ℝ] i.isImmersion.NormalSpace s hn :=
  .ofBijective ((h.normalHessian hn s).normalizingTransport (g.inner s).toBilinForm)
    (LinearMap.BilinForm.bijective_normalizingTransport (h.isSymm_normalHessian hn s)
      (h.ker_normalHessian hn s) (g.isSymm_toBilinForm_inner s) (g.pos s))

/-- The normalization of the normal Hessian is the normalizing transport of the normal Hessian
relative to the fibre metric. -/
theorem coe_normalHessianNormalization (s : S) :
    (h.normalHessianNormalization hn g s : Module.End ℝ (i.isImmersion.NormalSpace s hn)) =
      (h.normalHessian hn s).normalizingTransport (g.inner s).toBilinForm :=
  (rfl)

/-- The normalization of the normal Hessian preserves the negative normal space. -/
theorem normalHessianNormalization_apply_mem_negativeNormalSpace
    {v : i.isImmersion.NormalSpace s hn} (hv : v ∈ h.negativeNormalSpace hn g s) :
    h.normalHessianNormalization hn g s v ∈ h.negativeNormalSpace hn g s := by
  rw [IsCriticalSubmanifold.negativeNormalSpace_def] at hv ⊢
  exact LinearMap.BilinForm.normalizingTransport_apply_mem_relativeSpectralSubspace_Iio
    (h.isSymm_normalHessian hn s) (h.ker_normalHessian hn s) (g.isSymm_toBilinForm_inner s)
    (g.pos s) hv

/-- The normalization of the normal Hessian preserves the positive normal space. -/
theorem normalHessianNormalization_apply_mem_positiveNormalSpace
    {v : i.isImmersion.NormalSpace s hn} (hv : v ∈ h.positiveNormalSpace hn g s) :
    h.normalHessianNormalization hn g s v ∈ h.positiveNormalSpace hn g s := by
  rw [IsCriticalSubmanifold.positiveNormalSpace_def] at hv ⊢
  exact LinearMap.BilinForm.normalizingTransport_apply_mem_relativeSpectralSubspace_Ioi
    (h.isSymm_normalHessian hn s) (h.ker_normalHessian hn s) (g.isSymm_toBilinForm_inner s)
    (g.pos s) hv

open LinearMap.BilinForm in
/-- **On the negative normal space the normalization carries the normal Hessian to `-g`.** -/
theorem normalHessian_normalHessianNormalization_of_mem_negativeNormalSpace
    {v : i.isImmersion.NormalSpace s hn} (hv : v ∈ h.negativeNormalSpace hn g s) :
    h.normalHessian hn s (h.normalHessianNormalization hn g s v)
      (h.normalHessianNormalization hn g s v) = -g.inner s v v :=
  apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Iio
    (h.isSymm_normalHessian hn s) (h.ker_normalHessian hn s) (g.isSymm_toBilinForm_inner s)
    (g.pos s) (by rwa [IsCriticalSubmanifold.negativeNormalSpace_def] at hv)

open LinearMap.BilinForm in
/-- **On the positive normal space the normalization carries the normal Hessian to `g`.** -/
theorem normalHessian_normalHessianNormalization_of_mem_positiveNormalSpace
    {v : i.isImmersion.NormalSpace s hn} (hv : v ∈ h.positiveNormalSpace hn g s) :
    h.normalHessian hn s (h.normalHessianNormalization hn g s v)
      (h.normalHessianNormalization hn g s v) = g.inner s v v :=
  apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Ioi
    (h.isSymm_normalHessian hn s) (h.ker_normalHessian hn s) (g.isSymm_toBilinForm_inner s)
    (g.pos s) (by rwa [IsCriticalSubmanifold.positiveNormalSpace_def] at hv)

/-- The normalization of the normal Hessian is self-adjoint for the normal Hessian. -/
theorem normalHessian_normalHessianNormalization_apply_left_eq_right
    (v w : i.isImmersion.NormalSpace s hn) :
    h.normalHessian hn s (h.normalHessianNormalization hn g s v) w =
      h.normalHessian hn s v (h.normalHessianNormalization hn g s w) :=
  LinearMap.BilinForm.apply_normalizingTransport_left_eq_right (g.isSymm_toBilinForm_inner s)
    (g.pos s) v w

/-- The normalization of the normal Hessian is self-adjoint for the fibre metric. -/
theorem inner_normalHessianNormalization_apply_left_eq_right
    (v w : i.isImmersion.NormalSpace s hn) :
    g.inner s (h.normalHessianNormalization hn g s v) w =
      g.inner s v (h.normalHessianNormalization hn g s w) :=
  LinearMap.BilinForm.metric_apply_normalizingTransport_left_eq_right
    (g.isSymm_toBilinForm_inner s) (g.pos s) v w

/-- The normalization of the normal Hessian is positive definite for the fibre metric. -/
theorem inner_normalHessianNormalization_apply_self_pos {v : i.isImmersion.NormalSpace s hn}
    (hv : v ≠ 0) : 0 < g.inner s (h.normalHessianNormalization hn g s v) v :=
  LinearMap.BilinForm.metric_apply_normalizingTransport_self_pos (h.isSymm_normalHessian hn s)
    (h.ker_normalHessian hn s) (g.isSymm_toBilinForm_inner s) (g.pos s) hv

/-- **Characterization of the normalization of the normal Hessian.** An endomorphism `L` of the
normal space at `s` with `0 ≤ g (L v, v)` for all `v`, which is self-adjoint for the normal
Hessian, maps the negative and the positive normal spaces into themselves and carries the normal
Hessian to `-g` on the first and to `g` on the second, is the normalization of the normal Hessian.
-/
theorem eq_normalHessianNormalization {L : Module.End ℝ (i.isImmersion.NormalSpace s hn)}
    (hpos : ∀ v, 0 ≤ g.inner s (L v) v)
    (hHess : ∀ v w, h.normalHessian hn s (L v) w = h.normalHessian hn s v (L w))
    (hneg : ∀ v ∈ h.negativeNormalSpace hn g s, L v ∈ h.negativeNormalSpace hn g s ∧
      h.normalHessian hn s (L v) (L v) = -g.inner s v v)
    (hposS : ∀ v ∈ h.positiveNormalSpace hn g s, L v ∈ h.positiveNormalSpace hn g s ∧
      h.normalHessian hn s (L v) (L v) = g.inner s v v) :
    L = h.normalHessianNormalization hn g s := by
  simp only [IsCriticalSubmanifold.negativeNormalSpace_def,
    IsCriticalSubmanifold.positiveNormalSpace_def] at hneg hposS
  exact LinearMap.BilinForm.eq_normalizingTransport_of_mem_relativeSpectralSubspace
    (h.isSymm_normalHessian hn s) (h.ker_normalHessian hn s) (g.isSymm_toBilinForm_inner s)
    (g.pos s) hpos hHess hneg hposS

/-- **The normalization commutes with the projection onto the negative normal space** along the
positive one, since it preserves both spaces. -/
theorem negativeNormalProjection_normalHessianNormalization
    (v : i.isImmersion.NormalSpace s hn) :
    h.negativeNormalProjection hn g s (h.normalHessianNormalization hn g s v) =
      h.normalHessianNormalization hn g s (h.negativeNormalProjection hn g s v) := by
  refine h.negativeNormalProjection_apply_eq_of_mem_of_sub_mem hn g
    (h.normalHessianNormalization_apply_mem_negativeNormalSpace hn g
      (h.negativeNormalProjection_apply_mem hn g v)) ?_
  rw [← map_sub]
  exact h.normalHessianNormalization_apply_mem_positiveNormalSpace hn g
    (h.sub_negativeNormalProjection_apply_mem hn g v)

/-- On two vectors of a subspace on which `Hess (N v, N v) = ε g (v, v)`, polarization gives
`Hess (N v, N w) = ε g (v, w)`. -/
private theorem normalHessian_normalHessianNormalization_polarize
    {V : Submodule ℝ (i.isImmersion.NormalSpace s hn)} {ε : ℝ}
    (hV : ∀ v ∈ V, h.normalHessian hn s (h.normalHessianNormalization hn g s v)
      (h.normalHessianNormalization hn g s v) = ε * g.inner s v v)
    {v w : i.isImmersion.NormalSpace s hn} (hv : v ∈ V) (hw : w ∈ V) :
    h.normalHessian hn s (h.normalHessianNormalization hn g s v)
      (h.normalHessianNormalization hn g s w) = ε * g.inner s v w := by
  have := hV _ (V.add_mem hv hw)
  have hsym := (h.isSymm_normalHessian hn s).eq (h.normalHessianNormalization hn g s v)
    (h.normalHessianNormalization hn g s w)
  simp only [map_add, LinearMap.add_apply, add_apply, hV v hv, hV w hw, g.symm s w v] at this hsym
  linear_combination this / 2 + hsym / 2

/-- **The normal Hessian in Sylvester form.** The normalization `N` of the normal Hessian relative
to a fibre metric `g` carries the normal Hessian to the positive-minus-negative fibre quadratic
form of `g`: `Hess (N v, N v) = g (v⁺, v⁺) - g (v⁻, v⁻)`, where `v⁻ = P v` is the component of `v`
in the negative normal space and `v⁺ = v - P v` that in the positive normal space. -/
theorem normalHessian_normalHessianNormalization_apply_self (v : i.isImmersion.NormalSpace s hn) :
    h.normalHessian hn s (h.normalHessianNormalization hn g s v)
        (h.normalHessianNormalization hn g s v) =
      g.inner s (v - h.negativeNormalProjection hn g s v)
          (v - h.negativeNormalProjection hn g s v) -
        g.inner s (h.negativeNormalProjection hn g s v) (h.negativeNormalProjection hn g s v) := by
  rw [h.normalHessian_apply_eq_normalHessian_negativeNormalProjection_add hn g,
    h.negativeNormalProjection_normalHessianNormalization hn g, ← map_sub,
    h.normalHessian_normalHessianNormalization_of_mem_negativeNormalSpace hn g
      (h.negativeNormalProjection_apply_mem hn g v),
    h.normalHessian_normalHessianNormalization_of_mem_positiveNormalSpace hn g
      (h.sub_negativeNormalProjection_apply_mem hn g v)]
  ring

/-- **The adapted metric is the pull-back of the fibre metric along `N⁻¹ / √2`.** For the
normalization `N` of the normal Hessian relative to `g` and the adapted metric `g'` of `g`,
`g' (N u, N v) = g (u, v) / 2`. -/
theorem adaptedMetric_inner_normalHessianNormalization (u v : i.isImmersion.NormalSpace s hn) :
    (h.adaptedMetric hn g).inner s (h.normalHessianNormalization hn g s u)
        (h.normalHessianNormalization hn g s v) = g.inner s u v / 2 := by
  set P := h.negativeNormalProjection hn g s
  set N := h.normalHessianNormalization hn g s
  have hneg (w : i.isImmersion.NormalSpace s hn) := h.negativeNormalProjection_apply_mem hn g w
  have hpos (w : i.isImmersion.NormalSpace s hn) := h.sub_negativeNormalProjection_apply_mem hn g w
  -- `N` commutes with `P`, so the components of `N u` are the images of those of `u`.
  have hsub (w : i.isImmersion.NormalSpace s hn) : N w - P (N w) = N (w - P w) := by
    rw [h.negativeNormalProjection_normalHessianNormalization hn g, map_sub]
  have hNneg := normalHessian_normalHessianNormalization_polarize hn h g
    (V := h.negativeNormalSpace hn g s) (ε := -1) (fun w hw ↦ by
      rw [h.normalHessian_normalHessianNormalization_of_mem_negativeNormalSpace hn g hw]
      ring) (hneg u) (hneg v)
  have hNpos := normalHessian_normalHessianNormalization_polarize hn h g
    (V := h.positiveNormalSpace hn g s) (ε := 1) (fun w hw ↦ by
      rw [h.normalHessian_normalHessianNormalization_of_mem_positiveNormalSpace hn g hw]
      ring) (hpos u) (hpos v)
  rw [adaptedMetric_inner, hsub, hsub, h.negativeNormalProjection_normalHessianNormalization hn g,
    h.negativeNormalProjection_normalHessianNormalization hn g, hNneg, hNpos,
    h.inner_eq_inner_negativeNormalProjection_add hn g u v]
  ring

/-- **Compatibility with the normal-bundle trivializations.** Let `e` be a linear trivialization
of the normal bundle at `s`, in which the fibre metric `g` reads as the form `G` on the fibre model
`P`. An operator `Ψ` of `P` which is positive definite for `G`, self-adjoint for the normal Hessian
read in `e`, preserves the relative spectral subspaces of that form with respect to `G` and carries
it to `-G` on the negative one and to `G` on the positive one, reads the normalization of the
normal Hessian in `e`. -/
private theorem symm_apply_eq_normalHessianNormalization_apply {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [TopologicalSpace (TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn)]
    (e : Trivialization P (π P fun s ↦ i.isImmersion.NormalSpace s hn)) [e.IsLinear ℝ]
    (hs : s ∈ e.baseSet) {G : P →L[ℝ] P →L[ℝ] ℝ}
    (hGg : ∀ u v, G u v = g.inner s (e.symm s u) (e.symm s v)) {Ψ : P →L[ℝ] P}
    (hpos : ∀ u, u ≠ 0 → 0 < G (Ψ u) u)
    (hHess : ∀ u v, h.normalHessian hn s (e.symm s (Ψ u)) (e.symm s v) =
      h.normalHessian hn s (e.symm s u) (e.symm s (Ψ v)))
    (hneg : ∀ u ∈ G.toBilinForm.relativeSpectralSubspace
        ((h.normalHessian hn s).compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)) (Iio 0),
      Ψ u ∈ G.toBilinForm.relativeSpectralSubspace
        ((h.normalHessian hn s).compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)) (Iio 0) ∧
      h.normalHessian hn s (e.symm s (Ψ u)) (e.symm s (Ψ u)) = -G u u)
    (hposS : ∀ u ∈ G.toBilinForm.relativeSpectralSubspace
        ((h.normalHessian hn s).compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)) (Ioi 0),
      Ψ u ∈ G.toBilinForm.relativeSpectralSubspace
        ((h.normalHessian hn s).compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)) (Ioi 0) ∧
      h.normalHessian hn s (e.symm s (Ψ u)) (e.symm s (Ψ u)) = G u u) (u : P) :
    e.symm s (Ψ u) = h.normalHessianNormalization hn g s (e.symm s u) := by
  set φ := (e.linearEquivAt ℝ s hs).symm
  have hφ (w : P) : φ w = e.symm s w := Trivialization.linearEquivAt_symm_apply ..
  have hsymm : e.symmₗ ℝ s = (φ : P →ₗ[ℝ] i.isImmersion.NormalSpace s hn) :=
    LinearMap.ext fun w ↦ by rw [e.symmₗ_apply hs, LinearEquiv.coe_coe, hφ]
  have hGφ : G.toBilinForm = (g.inner s).toBilinForm.compl₁₂ (φ : P →ₗ[ℝ] _) φ := by
    ext w w'
    simp [hGg, hφ]
  have : FiniteDimensional ℝ P := φ.symm.finiteDimensional
  -- `Ψ` is the normalizing transport of the normal Hessian relative to `g`, both read in `e`, so by
  -- naturality it is the normalization read in `e`.
  have hΨ : (Ψ : Module.End ℝ P) = (φ.symm : _ →ₗ[ℝ] P) ∘ₗ
      (h.normalHessianNormalization hn g s : Module.End ℝ (i.isImmersion.NormalSpace s hn)) ∘ₗ
        (φ : P →ₗ[ℝ] _) := by
    rw [coe_normalHessianNormalization, ← LinearMap.BilinForm.normalizingTransport_compl₁₂
      (h.isSymm_normalHessian hn s) (h.ker_normalHessian hn s) (g.isSymm_toBilinForm_inner s)
      (g.pos s), ← hGφ, ← hsymm]
    refine LinearMap.BilinForm.eq_normalizingTransport_of_mem_relativeSpectralSubspace
      (q := (h.normalHessian hn s).compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)) (h := G.toBilinForm)
      ⟨fun _ _ ↦ (h.isSymm_normalHessian hn s).eq _ _⟩
      (hsymm ▸ LinearMap.BilinForm.ker_compl₁₂_eq_bot φ (h.ker_normalHessian hn s))
      (hGφ ▸ ⟨fun _ _ ↦ (g.isSymm_toBilinForm_inner s).eq _ _⟩)
      (fun w hw ↦ by simpa [hGg, ← hφ] using g.pos s _ ((map_ne_zero_iff _ φ.injective).mpr hw))
      (fun w ↦ ?_) (fun w w' ↦ by simpa [e.symmₗ_apply hs] using hHess w w')
      (fun w hw ↦ by simpa [e.symmₗ_apply hs] using hneg w hw)
      (fun w hw ↦ by simpa [e.symmₗ_apply hs] using hposS w hw)
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact (hpos w hw).le
  have hu := congr(φ ($hΨ u))
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at hu
  rwa [hφ, hφ] at hu

end Pointwise

section Smooth

variable [FiniteDimensional ℝ E'] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold J (k + 1) S]

/-- In the preferred normal-bundle trivialization at `s₀`, the normalization of the normal Hessian
relative to a `C^k` fibre metric reads as a `C^k` family of operators of the fibre model. The
local normalizations of `exists_contMDiffOn_normalHessian_normalization` are the readings of the
global one, by the characterization and the naturality of the normalizing transport. -/
private theorem exists_contMDiffOn_normalHessianNormalization_trivializationAt
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    let e := trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀
    ∃ Ψ : S → P →L[ℝ] P, ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k Ψ e.baseSet ∧
      ∀ s ∈ e.baseSet, ∀ u, e.symm s (Ψ s u) =
        h.normalHessianNormalization hn g.toRiemannianMetric s (e.symm s u) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  set e := trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀
  -- The metric read in the trivialization.
  set G : S → P →L[ℝ] P →L[ℝ] ℝ := fun s ↦
    ((g.inner s).toLinearMap₁₂.compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)).toContinuousBilinearMap
  have hG : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k G e.baseSet :=
    e.contMDiffOn_compl₁₂_symmₗ g.contMDiff.contMDiffOn
  have hGg (s : S) (hs : s ∈ e.baseSet) (u v : P) :
      G s u v = g.toRiemannianMetric.inner s (e.symm s u) (e.symm s v) := by
    simp only [G, LinearMap.toContinuousBilinearMap_apply, LinearMap.compl₁₂_apply,
      ContinuousLinearMap.toLinearMap₁₂_apply, e.symmₗ_apply hs]
    -- The underlying metric of `g` has the inner products of `g`, by definition.
    rfl
  have hinj {s : S} (hs : s ∈ e.baseSet) {u : P} (hu : u ≠ 0) : e.symm s u ≠ 0 := by
    rw [← Trivialization.linearEquivAt_symm_apply (R := ℝ) e s hs]
    exact (map_ne_zero_iff _ (e.linearEquivAt ℝ s hs).symm.injective).mpr hu
  obtain ⟨Ψ, hΨ, hΨs⟩ := h.exists_contMDiffOn_normalHessian_normalization hn
    (le_self_add.trans hk) hf hdim s₀ hG
    (fun s hs u v ↦ by rw [hGg s hs, hGg s hs, g.toRiemannianMetric.symm])
    (fun s hs u hu ↦ by rw [hGg s hs]; exact g.toRiemannianMetric.pos s _ (hinj hs hu))
  have hbase (s : S) (hs : s ∈ e.baseSet) :
      s ∈ e.baseSet ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet :=
    ⟨hs, by simpa [e] using hs⟩
  refine ⟨Ψ, hΨ.mono fun s hs ↦ hbase s hs, fun s hs u ↦ ?_⟩
  -- The local normalization reads the normalization, by characterization and naturality.
  have hΨs' := hΨs s (hbase s hs)
  simp only [← normalSpaceFiberBundle_trivializationAt] at hΨs'
  obtain ⟨-, -, hGΨ, hQΨ, hnegΨ, hposΨ, -⟩ := hΨs'
  exact h.symm_apply_eq_normalHessianNormalization_apply hn g.toRiemannianMetric e hs
    (hGg s hs) hGΨ hQΨ hnegΨ hposΨ u

/-- **The normalization of the normal Hessian is a `C^k` automorphism of the normal bundle.** Let
`i` be a nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of
class `C^{k+1}`, and let `g` be a `C^k` fibre metric on its normal bundle, with fibre model `P`.
Then the normalization `normalHessianNormalization g` of the normal Hessian, applied fibre by fibre,
is a `C^k` map of total spaces. In the trivialization at any point it reads `(s, y) ↦ (s, Ψ s y)`
for the `C^k` family `Ψ` of local normalizations of
`exists_contMDiffOn_normalHessian_normalization`. -/
theorem contMDiff_normalHessianNormalization
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) k
      (fun w : TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) ↦
        TotalSpace.mk' P (E := fun s ↦ i.isImmersion.NormalSpace s hn) w.proj
          (h.normalHessianNormalization hn g.toRiemannianMetric w.proj w.snd)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  intro w₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨(Bundle.contMDiff_proj _).contMDiffAt, ?_⟩
  obtain ⟨Ψ, hΨ, hΨs⟩ :=
    exists_contMDiffOn_normalHessianNormalization_trivializationAt hn h hk hf hdim g w₀.proj
  set e := trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) w₀.proj
  have hw₀ : w₀.proj ∈ e.baseSet := mem_baseSet_trivializationAt P _ w₀.proj
  have hΨw : ContMDiffAt (J.prod 𝓘(ℝ, P)) 𝓘(ℝ, P →L[ℝ] P) k (fun w ↦ Ψ w.proj) w₀ :=
    (hΨ.contMDiffAt (e.open_baseSet.mem_nhds hw₀)).comp w₀ (Bundle.contMDiff_proj _).contMDiffAt
  have he : ContMDiffAt (J.prod 𝓘(ℝ, P)) 𝓘(ℝ, P) k (fun w ↦ (e w).2) w₀ :=
    ((e.contMDiffOn (IB := J) (n := k)).contMDiffAt
      (e.open_source.mem_nhds (e.mem_source.mpr hw₀))).snd
  refine (hΨw.clm_apply he).congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj P _).continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds hw₀)] with w hw
  have hy : w.snd = e.symm w.proj (e w).2 := (e.symm_proj_apply w hw).symm
  rw [hy, ← hΨs w.proj hw]
  exact congr_arg Prod.snd (e.apply_mk_symm hw _)

/-- **The normalization of the normal Hessian as a `C^k` automorphism of the normal bundle.** For
a `C^k` fibre metric `g` on the normal bundle, this is the `C^k` diffeomorphism of the total space
which is the normalization `normalHessianNormalization g` of the normal Hessian on each fibre
(`contMDiff_normalHessianNormalization`). It carries the normal Hessian to the
positive-minus-negative fibre quadratic form of `g`
(`normalHessian_normalHessianNormalization_apply_self`). -/
def normalHessianNormalizationDiffeomorph
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) ≃ₘ^k⟮J.prod 𝓘(ℝ, P), J.prod 𝓘(ℝ, P)⟯
      TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  bundleDiffeomorph
    (fun s ↦ (h.normalHessianNormalization hn g.toRiemannianMetric s).toContinuousLinearEquiv)
    (h.contMDiff_normalHessianNormalization hn hk hf hdim g)

/-- The normalization of the normal Hessian as an automorphism of the normal bundle keeps the base
point and applies `normalHessianNormalization g` in the fibre. -/
@[simp]
theorem normalHessianNormalizationDiffeomorph_apply
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (v : TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    h.normalHessianNormalizationDiffeomorph hn hk hf hdim g v =
      ⟨v.proj, h.normalHessianNormalization hn g.toRiemannianMetric v.proj v.snd⟩ :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  bundleDiffeomorph_apply _ _ v

/-- The inverse of the normalization of the normal Hessian as an automorphism of the normal bundle
keeps the base point and applies the inverse of `normalHessianNormalization g` in the fibre. -/
@[simp]
theorem normalHessianNormalizationDiffeomorph_symm_apply
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (v : TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    (h.normalHessianNormalizationDiffeomorph hn hk hf hdim g).symm v =
      ⟨v.proj, (h.normalHessianNormalization hn g.toRiemannianMetric v.proj).symm v.snd⟩ :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  bundleDiffeomorph_symm_apply _ _ v

end Smooth

end Normalization

section MorseBottLemma

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The Morse–Bott lemma on the normal bundle in Sylvester form.** Let `i : S → M` be a
nondegenerate critical submanifold of `f`, for a smooth embedding of a nonempty manifold into a
Hausdorff, second-countable, finite-dimensional, boundaryless manifold, let `f` be `C^{k+2}`,
`1 ≤ k ≤ ∞`, on an open neighbourhood `O` of the image of `i`, and let `g` be a `C^k` fibre metric
on the normal bundle. Then there is a `C^k` partial diffeomorphism `Θ` from the total space of the
normal bundle to `M`, whose source contains the whole zero section, which sends the zero section to
`i` and has image in `O`, such that

`f (Θ v) = f (i s) + ½ (g (v⁺, v⁺) - g (v⁻, v⁻))`

for every `v` in its source over `s`, where `v⁻ = P v` is the component of `v` in the negative
normal space relative to `g` and `v⁺ = v - P v` that in the positive normal space. It is the
normal form `exists_morseBott_partialDiffeomorph_normalBundle` composed with the normalization of
the normal Hessian (`normalHessianNormalizationDiffeomorph`). -/
theorem exists_morseBott_partialDiffeomorph_normalBundle_inner_sub
    (h : i.IsNondegenerateCriticalSubmanifold f) [SecondCountableTopology M] [Nonempty S]
    [FiniteDimensional ℝ E'] [J.Boundaryless] [IsManifold J ∞ S]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {k : ℕ∞} (hk : k ≠ 0) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    {O : Set M} (hO : IsOpen O) (hiO : range i ⊆ O) (hf : ContMDiffOn I 𝓘(ℝ) (k + 2) f O)
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I
        (TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn)) M k,
      (∀ s, zeroSection P (fun s ↦ i.isImmersion.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.isImmersion.NormalSpace s hn) s) = i s) ∧ Θ.target ⊆ O ∧
      ∀ x ∈ Θ.source, f (Θ x) = f (i x.proj) + 2⁻¹ *
        (g.toRiemannianMetric.inner x.proj
            (x.snd - h.negativeNormalProjection hn g.toRiemannianMetric x.proj x.snd)
            (x.snd - h.negativeNormalProjection hn g.toRiemannianMetric x.proj x.snd) -
          g.toRiemannianMetric.inner x.proj
            (h.negativeNormalProjection hn g.toRiemannianMetric x.proj x.snd)
            (h.negativeNormalProjection hn g.toRiemannianMetric x.proj x.snd)) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have hk2 : (k : ℕ∞ω) + 2 ≤ ∞ := by
    rw [← WithTop.coe_ofNat, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 le_top
  have hk1 : (k : ℕ∞ω) + 1 ≤ ∞ := by
    rw [← WithTop.coe_one, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 le_top
  have : IsManifold I ((k : ℕ∞ω) + 2) M := .of_le hk2
  have : IsManifold J ((k : ℕ∞ω) + 1) S := .of_le hk1
  have hf' (s : S) : ContMDiffAt I 𝓘(ℝ) ((k : ℕ∞ω) + 2) f (i s) :=
    hf.contMDiffAt (hO.mem_nhds (hiO (mem_range_self s)))
  obtain ⟨Θ, hzero, hΘz, hΘO, hΘf⟩ :=
    h.exists_morseBott_partialDiffeomorph_normalBundle hn hk hdim hO hiO hf
  set D := h.normalHessianNormalizationDiffeomorph hn hk1 hf' hdim g
  have hD (x : TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn) :
      D x = ⟨x.proj, h.normalHessianNormalization hn g.toRiemannianMetric x.proj x.snd⟩ :=
    h.normalHessianNormalizationDiffeomorph_apply hn hk1 hf' hdim g x
  have hDz (s : S) : D (zeroSection P (fun s ↦ i.isImmersion.NormalSpace s hn) s) =
      zeroSection P (fun s ↦ i.isImmersion.NormalSpace s hn) s := by
    rw [hD]
    simp only [zeroSection]
    exact congrArg _ (h.normalHessianNormalization hn g.toRiemannianMetric s).map_zero
  refine ⟨D.toPartialDiffeomorph.trans Θ, fun s ↦ ?_, fun s ↦ ?_, ?_, fun x hx ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    exact ⟨by simp, by simpa [Diffeomorph.coe_toPartialDiffeomorph, hDz] using hzero s⟩
  · rw [PartialDiffeomorph.coe_trans, comp_apply, Diffeomorph.coe_toPartialDiffeomorph, hDz, hΘz]
  · rw [PartialDiffeomorph.trans_target]
    exact inter_subset_left.trans hΘO
  · rw [PartialDiffeomorph.trans_source] at hx
    have hx' : D x ∈ Θ.source := by simpa [Diffeomorph.coe_toPartialDiffeomorph] using hx.2
    rw [PartialDiffeomorph.coe_trans, comp_apply, Diffeomorph.coe_toPartialDiffeomorph,
      hΘf (D x) hx', hD,
      h.normalHessian_normalHessianNormalization_apply_self hn g.toRiemannianMetric]

end MorseBottLemma

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
