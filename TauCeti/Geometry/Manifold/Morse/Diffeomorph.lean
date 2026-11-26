/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Lemma
public import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence

/-!
# Morse charts under diffeomorphisms

Let `σ : M → M'` be a diffeomorphism between boundaryless manifolds and `f'` a function on `M'`,
and put `f = f' ∘ σ`. Then `σ` matches the critical points of `f` with those of `f'`, preserving
the Morse indices, and a Morse chart `φ` for `f'` at `σ x` pulls back to the Morse chart `φ ∘ σ`
for `f` at `x`, with the same coordinates and weights. If a vector field `X'` on `M'` is the linear
field `z ↦ (-wᵢ zᵢ)ᵢ` in `φ` and `σ` carries `X` to `X'`, then `X` is the same linear field in
`φ ∘ σ`.

These are the chart-level facts used to transport the Morse complex along `σ`
(`TauCeti/Geometry/Manifold/Morse/Boundary/Diffeomorph.lean`).

## Main definitions

* `TauCeti.criticalPointsEquivOfComp`: the critical points of `f' ∘ σ` are those of `f'`, moved
  by `σ⁻¹`.
* `TauCeti.MorseChart.pullback`: the pullback `φ ∘ σ` of a Morse chart along a diffeomorphism.

## Main results

* `TauCeti.manifoldMorseIndex_symm_apply_eq_of_comp`: the Morse index of `f` at `σ⁻¹ q` is that of
  `f'` at a critical point `q`.
* `TauCeti.MorseChart.manifoldMorseIndex_eq_of_comp`: the Morse index of `f` at `x` is that of
  `f'` at `σ x`.
* `TauCeti.MorseChart.manifoldMorseIndex_criticalPointsEquivOfComp_symm`: the same, read along the
  bijection of critical points.
* `TauCeti.MorseChart.coord_mfderiv_pullback`: linear fields pull back to linear fields.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M']
  {f : M → ℝ} {f' : M' → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {X' : (x : M') → TangentSpace 𝓘(ℝ, E) x} {σ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M'}

variable (hf : f' ∘ σ = f)

/-- The bijection between the critical points of `f` and those of `f'` given by `σ`, when
`f' ∘ σ = f`: `σ` is a local diffeomorphism, so `x` is a critical point of `f' ∘ σ` exactly when
`σ x` is a critical point of `f'`. -/
@[expose]
def criticalPointsEquivOfComp : criticalPoints 𝓘(ℝ, E) f ≃ criticalPoints 𝓘(ℝ, E) f' :=
  σ.toEquiv.subtypeEquiv fun x ↦ by
    rw [← hf]
    exact (σ.isLocalDiffeomorph x).mem_criticalPoints_comp_iff (by simp)

/-- The bijection of critical points is `σ`. -/
@[simp]
theorem coe_criticalPointsEquivOfComp_apply (p : criticalPoints 𝓘(ℝ, E) f) :
    (criticalPointsEquivOfComp hf p : M') = σ p :=
  rfl

/-- The inverse of the bijection of critical points is `σ⁻¹`. -/
@[simp]
theorem coe_criticalPointsEquivOfComp_symm_apply (p' : criticalPoints 𝓘(ℝ, E) f') :
    ((criticalPointsEquivOfComp hf).symm p' : M) = σ.symm p' :=
  rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E) ∞ M']

include hf in
/-- **The bijection of critical points preserves Morse indices.** If `f' ∘ σ = f` and `f'` is `C²`
at a critical point `q` of `f'`, then the Morse index of `f` at `σ⁻¹ q` is the Morse index of `f'`
at `q`. -/
theorem manifoldMorseIndex_symm_apply_eq_of_comp {q : M'} (hf' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f' q)
    (hq : q ∈ criticalPoints 𝓘(ℝ, E) f') :
    manifoldMorseIndex 𝓘(ℝ, E) f (σ.symm q) = manifoldMorseIndex 𝓘(ℝ, E) f' q := by
  rw [← hf]
  have h := (σ.isLocalDiffeomorph (σ.symm q)).manifoldMorseIndex_comp (by simp)
    (by rwa [σ.apply_symm_apply]) (by rwa [σ.apply_symm_apply])
  rwa [σ.apply_symm_apply] at h

namespace MorseChart

variable {x : M}

include hf in
/-- **Morse indices under a diffeomorphism.** If `f' ∘ σ = f` and `φ` is a Morse chart for `f'` at
`σ x`, then the Morse index of `f` at `x` is the Morse index of `f'` at `σ x`. -/
theorem manifoldMorseIndex_eq_of_comp (φ : MorseChart E f' (σ x)) :
    manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f' (σ x) := by
  rw [← hf]
  exact (σ.isLocalDiffeomorph x).manifoldMorseIndex_comp (by simp)
    ((φ.contMDiffAt φ.mem_source).of_le (by simp))
    (mem_criticalPoints_iff_mfderiv_eq_zero.2 ((φ.mfderiv_eq_zero_iff φ.mem_source).2 rfl))

include hf in
/-- **Morse indices along the bijection of critical points.** If `f' ∘ σ = f` and `φ` is a Morse
chart for `f'` at a critical point `q`, then the Morse index of `f` at the critical point `σ⁻¹ q`
is the Morse index of `f'` at `q`. -/
theorem manifoldMorseIndex_criticalPointsEquivOfComp_symm {q : criticalPoints 𝓘(ℝ, E) f'}
    (φ : MorseChart E f' q) :
    manifoldMorseIndex 𝓘(ℝ, E) f ((criticalPointsEquivOfComp hf).symm q) =
      manifoldMorseIndex 𝓘(ℝ, E) f' q := by
  obtain ⟨p, rfl⟩ := (criticalPointsEquivOfComp hf).surjective q
  rw [Equiv.symm_apply_apply]
  exact φ.manifoldMorseIndex_eq_of_comp hf

/-- **The pullback of a Morse chart along a diffeomorphism.** If `f' ∘ σ = f`, a Morse chart `φ`
for `f'` at `σ x` gives the Morse chart `φ ∘ σ` for `f` at `x`, with the same coordinates and
weights. -/
-- The body is exposed and reducible: the types of the orientations and frames of the pulled-back
-- chart depend on its weights, which must reduce to those of `φ`, also during rewriting, for the
-- transport lemmas to be stated and used.
@[expose, reducible]
noncomputable def pullback (φ : MorseChart E f' (σ x)) : MorseChart E f x where
  toChart := σ.toHomeomorph.transOpenPartialHomeomorph φ.toChart
  mem_maximalAtlas := σ.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl φ.mem_maximalAtlas
  mem_source := φ.mem_source
  apply_self := φ.apply_self
  coord := φ.coord
  weight := φ.weight
  weight_eq_neg_one_or_eq_one := φ.weight_eq_neg_one_or_eq_one
  ncard_weight_neg := by rw [φ.ncard_weight_neg, φ.manifoldMorseIndex_eq_of_comp hf]
  eq_quadratic y hy := by
    rw [← hf, comp_apply, comp_apply, φ.eq_quadratic (σ y) hy,
      Homeomorph.transOpenPartialHomeomorph_apply, comp_apply, Diffeomorph.coe_toHomeomorph]

variable (φ : MorseChart E f' (σ x))

/-- The chart of the pullback is the chart `φ ∘ σ`. -/
@[simp]
theorem coe_pullback_toChart : ⇑(φ.pullback hf).toChart = φ.toChart ∘ σ :=
  rfl

/-- The source of the pullback is the preimage of the source. -/
@[simp]
theorem pullback_source : (φ.pullback hf).toChart.source = σ ⁻¹' φ.toChart.source :=
  rfl

/-- The target of the pullback is the target. -/
@[simp]
theorem pullback_target : (φ.pullback hf).toChart.target = φ.toChart.target :=
  rfl

/-- The pullback keeps the coordinates. -/
@[simp]
theorem pullback_coord : (φ.pullback hf).coord = φ.coord :=
  rfl

/-- The pullback keeps the weights. -/
@[simp]
theorem pullback_weight : (φ.pullback hf).weight = φ.weight :=
  rfl

include hf in
/-- The Morse indices of `f'` at `σ p` and `σ q`, centres of Morse charts, differ by one when
those of `f` at `p` and `q` do. -/
theorem manifoldMorseIndex_eq_add_one_of_comp {p q : M} (φp : MorseChart E f' (σ p))
    (φq : MorseChart E f' (σ q))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    manifoldMorseIndex 𝓘(ℝ, E) f' (σ p) = manifoldMorseIndex 𝓘(ℝ, E) f' (σ q) + 1 := by
  rw [← φp.manifoldMorseIndex_eq_of_comp hf, ← φq.manifoldMorseIndex_eq_of_comp hf]
  exact hpq

variable {φ}

/-- **Linear fields pull back.** If `σ` carries `X` to `X'` and `X'` is the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, then `X` is the same linear field in the pullback of
`φ`. -/
theorem coord_mfderiv_pullback (hσX : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X y) = X' (σ y))
    (hφ : ∀ y ∈ φ.toChart.source,
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X' y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) :
    ∀ y ∈ (φ.pullback hf).toChart.source,
      (φ.pullback hf).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.pullback hf).toChart y (X y)) =
        fun i ↦ -((φ.pullback hf).weight i *
          (φ.pullback hf).coord ((φ.pullback hf).toChart y) i) := by
  intro y hy
  rw [coe_pullback_toChart, σ.mfderiv_comp_diffeomorph (by simp), ContinuousLinearMap.comp_apply,
    hσX]
  exact hφ (σ y) hy

end MorseChart

end TauCeti
