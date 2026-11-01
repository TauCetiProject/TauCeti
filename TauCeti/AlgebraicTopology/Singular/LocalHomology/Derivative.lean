/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Homotopy.Affine
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding

/-!
# Differentiable maps act on local homology by the sign of their Jacobian

Let `E` be a finite-dimensional real normed space, `U ⊆ E` a neighbourhood of a point `x`, and
`f : E → E` a map that is continuous on `U` and differentiable at `x`, with derivative
`f' = Df(x)` of nonzero determinant. If `x` is the only point of `U` sent to `f x`, then `f` is a
map of pairs `(U, U ∖ {x}) ⟶ (E, E ∖ {f x})`. The map it induces on local homology
`Hₖ(U, U ∖ {x}) ⟶ Hₖ(E, E ∖ {f x})` is `sign (det f')` times the map induced by the translation
`y ↦ f x + (y - x)`, in every degree and for every coefficient object
(`TauCeti.localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt`). By excision
`Hₖ(U, U ∖ {x})` is the local homology of `E` at `x`, which the translation identifies with the
local homology at `f x`. So `f` carries the local orientations of `E` at `x` to the corresponding
local orientations at `f x` when `det f' > 0`, and to their negatives when `det f' < 0`. Only
differentiability at the single point `x` is used.

This is the local degree of a map at a regular point. It compares the local homology orientations
of a smooth manifold with the orientations of its tangent spaces: a transition map between charts
acts on local homology by the sign of its Jacobian determinant.

The comparison has two halves.

* **Linearization.** A map `f : E → F` between real normed spaces, differentiable at `x` with an
  antilipschitz derivative `f'`, induces the same map on local homology at `x` as its affine
  linearization `y ↦ f x + f' (y - x)`
  (`TauCeti.localHomologyMap_domRestrict_eq_affine_of_hasFDerivAt`). On a ball about `x` where the
  remainder `f y - f x - f' (y - x)` is at most a small multiple of `‖y - x‖`, the straight-line
  homotopy from `f` to its linearization never takes the value `f x` away from `x`, because
  `‖f' v‖` is bounded below by a multiple of `‖v‖`. Excision replaces `U` by that ball.
* **The linear part.** The affine map `y ↦ c + f' (y - x)` is a translation, then `f'`, then a
  translation, and `f'` acts on the local homology at the origin by `sign (det f')`
  (`TauCeti.singularHomologyMap_continuousLinearMap_compl_zero`). This gives
  `TauCeti.localHomologyMap_affine_eq_sign_det_smul`.

## Main results

* `TauCeti.localHomologyMap_affine_eq_sign_det_smul`: an affine map with linear part `f'` acts on
  local homology by `sign (det f')`, relative to the translation.
* `TauCeti.localHomologyMap_domRestrict_eq_affine_of_hasFDerivAt`: a map differentiable at `x`
  with antilipschitz derivative induces the same map on local homology as its affine
  linearization.
* `TauCeti.localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt`: a map differentiable at
  `x` with derivative of nonzero determinant acts on local homology by the sign of that
  determinant.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (local degree) and Section 3.3 (local orientations).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section Affine

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Affine maps act on local homology by the sign of their determinant.** Let `U ⊆ E` contain
`x`, let `c : E`, and let `f'` be a continuous linear map with `det f' ≠ 0`. The map
`Hₖ(U, U ∖ {x}) ⟶ Hₖ(E, E ∖ {c})` induced by the affine map `y ↦ c + f' (y - x)` is `sign (det f')`
times the map induced by the translation `y ↦ c + (y - x)`. -/
theorem localHomologyMap_affine_eq_sign_det_smul {U : Set E} {x : E} (hx : x ∈ U) (c : E)
    {f' : E →L[ℝ] E} (hdet : f'.det ≠ 0) (k : ℕ) :
    localHomologyMap R (⟨fun y : U ↦ c + f' (y - x), by fun_prop⟩ : C(U, E))
        (S := {⟨x, hx⟩}) (T := {c}) (by
          rintro _ hy
          exact Subtype.ext <| sub_eq_zero.1 <|
            (f'.toContinuousLinearEquivOfDetNeZero hdet).map_eq_zero_iff.1 (add_eq_left.1 hy)) k =
      (SignType.sign f'.det : ℤ) •
        localHomologyMap R (⟨fun y : U ↦ c + (y - x), by fun_prop⟩ : C(U, E))
          (S := {⟨x, hx⟩}) (T := {c}) (by
            rintro _ hy
            exact Subtype.ext <| sub_eq_zero.1 (add_eq_left.1 hy)) k := by
  -- The affine map is `y ↦ y - x`, then `f'`, then `z ↦ c + z`; the translation omits `f'`.
  let σ : C(U, E) := ⟨fun y ↦ (y : E) - x, by fun_prop⟩
  let τ : C(E, E) := ⟨fun z ↦ c + z, by fun_prop⟩
  have hσ : σ ⁻¹' {0} ⊆ {⟨x, hx⟩} := fun y hy ↦ Subtype.ext (sub_eq_zero.1 hy)
  have hτ : τ ⁻¹' {c} ⊆ {0} := fun z hz ↦ add_eq_left.1 hz
  have hf' : (f' : C(E, E)) ⁻¹' {0} ⊆ {0} := fun z hz ↦
    (f'.toContinuousLinearEquivOfDetNeZero hdet).map_eq_zero_iff.1 hz
  have hlin : localHomologyMap R (f' : C(E, E)) hf' k = (SignType.sign f'.det : ℤ) • 𝟙 _ := by
    rw [localHomologyMap_def]
    exact singularHomologyMap_continuousLinearMap_compl_zero R f' _ k
  calc _ = localHomologyMap R σ hσ k ≫ localHomologyMap R (f' : C(E, E)) hf' k ≫
          localHomologyMap R τ hτ k := by
        rw [localHomologyMap_comp, localHomologyMap_comp]
        -- The composite `τ ∘ f' ∘ σ` is the affine map, pointwise by definition.
        congr 1
    _ = (SignType.sign f'.det : ℤ) • (localHomologyMap R σ hσ k ≫ localHomologyMap R τ hτ k) := by
        rw [hlin, Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul]
    _ = _ := by
        rw [localHomologyMap_comp]
        -- The composite `τ ∘ σ` is the translation, pointwise by definition.
        congr 2

end Affine

section Linearization

variable {E F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- If the remainder `f y - f x - f' (y - x)` is at most `ε * ‖y - x‖`, where `‖v‖ ≤ C * ‖f' v‖`
for all `v` and `C * ε < 1`, then for `y ≠ x` no point of the segment from `f y` to
`f x + f' (y - x)` is `f x`. -/
private lemma segment_ne_of_norm_remainder_le {f : E → F} {f' : E →L[ℝ] F} {x y : E} {C ε : ℝ}
    (hC : ∀ v, ‖v‖ ≤ C * ‖f' v‖) (hC0 : 0 ≤ C) (hCε : C * ε < 1)
    (hy : ‖f y - f x - f' (y - x)‖ ≤ ε * ‖y - x‖) (hyx : y ≠ x) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : (1 - t) • f y + t • (f x + f' (y - x)) ≠ f x := by
  intro h
  -- The point of the segment is `f x + f' (y - x) + (1 - t) • (f y - f x - f' (y - x))`.
  have hsum : f' (y - x) + (1 - t) • (f y - f x - f' (y - x)) = 0 := by
    rw [← sub_eq_zero.2 h]
    module
  have hle : ‖f' (y - x)‖ ≤ ε * ‖y - x‖ := by
    rw [eq_neg_of_add_eq_zero_left hsum, norm_neg, norm_smul, Real.norm_of_nonneg (by linarith)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans hy
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  have := (hC (y - x)).trans (mul_le_mul_of_nonneg_left hle hC0)
  nlinarith

/-- **A map with antilipschitz derivative induces the same map on local homology as its affine
linearization.** Let `U ⊆ E` be a neighbourhood of `x` and `f : E → F` a map continuous on `U` and
differentiable at `x`, with an antilipschitz derivative `f'`, such that `x` is the only point of `U`
sent to `f x`. Then `f` and its affine linearization `y ↦ f x + f' (y - x)` induce the same map
`Hₖ(U, U ∖ {x}) ⟶ Hₖ(F, F ∖ {f x})`. -/
theorem localHomologyMap_domRestrict_eq_affine_of_hasFDerivAt {f : E → F} {f' : E →L[ℝ] F} {x : E}
    {U : Set E} (hU : U ∈ 𝓝 x) (hfU : ContinuousOn f U) (hf : HasFDerivAt f f' x) {K : NNReal}
    (hf' : AntilipschitzWith K f') (hfx : ∀ y ∈ U, f y = f x → y = x) (k : ℕ) :
    localHomologyMap R (⟨U.domRestrict f, hfU.domRestrict⟩ : C(U, F))
        (S := {⟨x, mem_of_mem_nhds hU⟩}) (T := {f x}) (by
          rintro y hy
          exact Subtype.ext (hfx y y.2 hy)) k =
      localHomologyMap R (⟨fun y : U ↦ f x + f' (y - x), by fun_prop⟩ : C(U, F))
        (S := {⟨x, mem_of_mem_nhds hU⟩}) (T := {f x}) (by
          rintro _ hy
          exact Subtype.ext <| sub_eq_zero.1 <| hf'.injective <|
            (add_eq_left.1 hy).trans (map_zero f').symm) k := by
  have hx := mem_of_mem_nhds hU
  have hC : ∀ v, ‖v‖ ≤ K * ‖f' v‖ := fun v ↦ by simpa using hf'.le_mul_dist 0 v
  -- On a ball `B` about `x` inside `U`, the remainder is at most `ε * ‖y - x‖` with `K * ε < 1`.
  set ε : ℝ := (2 * (K + 1))⁻¹
  have hε : 0 < ε := by positivity
  have hKε : (K : ℝ) * ε < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by positivity)]
    linarith [K.coe_nonneg]
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU (hf.isLittleO.def hε))
  have hBU : ball x r ⊆ U := fun y hy ↦ (hrU hy).1
  have hxB : x ∈ ball x r := mem_ball_self hr
  -- The inclusion of `B` into `U` is an open embedding, so it induces an isomorphism on local
  -- homology at `x` by excision.
  let ι : C(ball x r, U) := ⟨inclusion hBU, continuous_inclusion hBU⟩
  have hιx : ι ⁻¹' {⟨x, hx⟩} = {⟨x, hxB⟩} := by
    ext y
    simp [ι, Subtype.ext_iff]
  have := isIso_localHomologyMap R ι
    (IsOpenEmbedding.inclusion hBU (isOpen_ball.preimage continuous_subtype_val)) hιx
    isClosed_singleton (by simp [ι, hr]) k
  rw [← cancel_epi (localHomologyMap R ι hιx.subset k), localHomologyMap_comp,
    localHomologyMap_comp]
  -- On `B`, the straight-line homotopy from `f` to its linearization avoids `f x` off `x`.
  refine localHomologyMap_eq_of_homotopy R (ContinuousMap.Homotopy.affine _ _)
    (fun t y hy ↦ ?_) _ _ k
  rw [ContinuousMap.Homotopy.affine_apply, AffineMap.lineMap_apply_module]
  exact segment_ne_of_norm_remainder_le hC K.coe_nonneg hKε (hrU y.2).2
    (fun h ↦ hy (Subtype.ext h)) t.2.1 t.2.2

end Linearization

section Jacobian

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A map with invertible derivative acts on local homology by the sign of its Jacobian.** Let
`U ⊆ E` be a neighbourhood of `x` and `f : E → E` a map continuous on `U` and differentiable at `x`,
with derivative `f'` of nonzero determinant, such that `x` is the only point of `U` sent to `f x`.
Then the map `Hₖ(U, U ∖ {x}) ⟶ Hₖ(E, E ∖ {f x})` induced by `f` is `sign (det f')` times the map
induced by the translation `y ↦ f x + (y - x)`. -/
theorem localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt {f : E → E} {f' : E →L[ℝ] E}
    {x : E} {U : Set E} (hU : U ∈ 𝓝 x) (hfU : ContinuousOn f U) (hf : HasFDerivAt f f' x)
    (hdet : f'.det ≠ 0) (hfx : ∀ y ∈ U, f y = f x → y = x) (k : ℕ) :
    localHomologyMap R (⟨U.domRestrict f, hfU.domRestrict⟩ : C(U, E))
        (S := {⟨x, mem_of_mem_nhds hU⟩}) (T := {f x}) (by
          rintro y hy
          exact Subtype.ext (hfx y y.2 hy)) k =
      (SignType.sign f'.det : ℤ) •
        localHomologyMap R (⟨fun y : U ↦ f x + (y - x), by fun_prop⟩ : C(U, E))
          (S := {⟨x, mem_of_mem_nhds hU⟩}) (T := {f x}) (by
            rintro _ hy
            exact Subtype.ext <| sub_eq_zero.1 (add_eq_left.1 hy)) k := by
  rw [localHomologyMap_domRestrict_eq_affine_of_hasFDerivAt R hU hfU hf
    (f'.toContinuousLinearEquivOfDetNeZero hdet).antilipschitzWith hfx k]
  exact localHomologyMap_affine_eq_sign_det_smul R _ _ hdet k

end Jacobian

end TauCeti
