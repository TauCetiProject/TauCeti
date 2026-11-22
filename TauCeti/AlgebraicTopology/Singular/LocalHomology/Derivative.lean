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
public import TauCeti.Analysis.Normed.Operator.Basic

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
  `TauCeti.localHomologyMap_affine_eq_sign_det_smul` in `LocalHomology/Linear.lean`.

## Main results

* `TauCeti.localHomologyMap_domRestrict_eq_affine_of_hasFDerivAt`: a map differentiable at `x`
  with antilipschitz derivative induces the same map on local homology as its affine
  linearization.
* `TauCeti.localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt`: a map differentiable at
  `x` with derivative of nonzero determinant acts on local homology by the sign of that
  determinant.

The chart-composition law
`OpenPartialHomeomorph.localHomologyMap_chart_comp_eq_sign_det_smul` expresses the same
comparison in arbitrary source and target charts, for every coefficient object and degree.

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

section Linearization

variable {E F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

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
          exact Subtype.ext (hfx y y.property hy)) k =
      localHomologyMap R (⟨fun y : U ↦ f x + f' (y - x), by fun_prop⟩ : C(U, F))
        (S := {⟨x, mem_of_mem_nhds hU⟩}) (T := {f x}) (by
          rintro _ hy
          exact Subtype.ext <| sub_eq_zero.1 <| hf'.injective <|
            (add_eq_left.1 hy).trans (map_zero f').symm) k := by
  have hx := mem_of_mem_nhds hU
  have hC := f'.bound_of_antilipschitz hf'
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
    (IsOpenEmbedding.inclusion hBU (isOpen_ball.preimage continuous_subtypeVal)) hιx
    isClosed_singleton (by simp [ι, hr]) k
  rw [← cancel_epi (localHomologyMap R ι hιx.subset k), localHomologyMap_comp,
    localHomologyMap_comp]
  -- On `B`, the straight-line homotopy from `f` to its linearization avoids `f x` off `x`.
  refine localHomologyMap_eq_of_homotopy R (ContinuousMap.Homotopy.affine _ _)
    (fun t y hy ↦ ?_) _ _ k
  have hfι : (⟨U.domRestrict f, hfU.domRestrict⟩ : C(U, F)).comp ι y = f y := by
    simp only [ι, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Set.domRestrict_apply]
  have hrem : ‖f y - f x - f' (y - x)‖ ≤ ε * ‖(y : E) - x‖ := (hrU y.property).2
  -- The point of the segment is `f x + f' (y - x) + (1 - t) • (f y - f x - f' (y - x))`.
  have hseg : (1 - (t : ℝ)) • f y + (t : ℝ) • (f x + f' (y - x)) - f x =
      f' (y - x) + (1 - (t : ℝ)) • (f y - f x - f' (y - x)) := by
    module
  rw [ContinuousMap.Homotopy.affine_apply, AffineMap.lineMap_apply_module, hfι]
  refine fun h ↦ f'.apply_add_ne_zero_of_forall_norm_le hC hKε
    (sub_ne_zero.2 fun h ↦ hy (Subtype.ext h)) ?_
    (hseg.symm.trans (sub_eq_zero.2 (Set.mem_singleton_iff.1 h)))
  rw [norm_smul, Real.norm_of_nonneg (by linarith [t.property.2])]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [t.property.1])).trans hrem

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
          exact Subtype.ext (hfx y y.property hy)) k =
      (SignType.sign f'.det : ℤ) •
        localHomologyMap R (⟨fun y : U ↦ f x + (y - x), by fun_prop⟩ : C(U, E))
          (S := {⟨x, mem_of_mem_nhds hU⟩}) (T := {f x}) (by
            rintro _ hy
            exact Subtype.ext <| sub_eq_zero.1 (add_eq_left.1 hy)) k := by
  rw [localHomologyMap_domRestrict_eq_affine_of_hasFDerivAt R hU hfU hf
    (f'.toContinuousLinearEquivOfDetNeZero hdet).antilipschitzWith hfx k]
  exact localHomologyMap_affine_eq_sign_det_smul R _ _ hdet k

end Jacobian

section Charts

variable {M N E : Type w} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In source and target charts, the map of local homology at an isolated point of a fibre is
the sign of the coordinate derivative times the map induced by the translated source chart.
This is an identity of morphisms in every degree and for every coefficient object. -/
theorem _root_.OpenPartialHomeomorph.localHomologyMap_chart_comp_eq_sign_det_smul
    (φ : OpenPartialHomeomorph M E) (χ : OpenPartialHomeomorph N E) (R : A) (f : C(M, N))
    {a : M} {U : Set M} (hUo : IsOpen U) (haU : a ∈ U) (hUφ : U ⊆ φ.source)
    (hUχ : ∀ x ∈ U, f x ∈ χ.source) (hU : ∀ x ∈ U, f x = f a → x = a)
    {f' : E →L[ℝ] E} (hf : HasFDerivAt (χ ∘ f ∘ φ.symm) f' (φ a))
    (hdet : f'.det ≠ 0) (k : ℕ) :
    let fχ := (f.restrictPreimage χ.source).comp (ContinuousMap.inclusion hUχ)
    let φU := φ.sourceRestrict.comp (ContinuousMap.inclusion hUφ)
    let b := (χ ∘ f ∘ φ.symm) (φ a)
    let T : C(E, E) := ⟨fun y ↦ b + (y - φ a), by fun_prop⟩
    localHomologyMap R fχ (S := {⟨a, haU⟩})
        (T := ContinuousMap.subtypeVal χ.source ⁻¹' {f a})
        (fun x hx ↦ Subtype.ext (hU x x.property hx)) k ≫
      localHomologyMap R χ.sourceRestrict
        (S := ContinuousMap.subtypeVal χ.source ⁻¹' {f a}) (T := {b})
        (fun x hx ↦ χ.sourceRestrict_preimage (hUχ a haU) (by
          simpa only [b, Function.comp_apply, φ.left_inv (hUφ haU)] using hx)) k =
      (SignType.sign f'.det : ℤ) •
        (localHomologyMap R φU (S := {⟨a, haU⟩}) (T := {φ a})
          (fun x hx ↦ Subtype.ext (φ.sourceRestrict_preimage (hUφ haU) hx)) k ≫
        localHomologyMap R T (S := {φ a}) (T := {b})
          (fun y hy ↦ sub_eq_zero.1 (add_eq_left.1 hy)) k) := by
  dsimp only
  generalize_proofs
  rw [localHomologyMap_comp, localHomologyMap_comp]
  let V : Set E := φ.target ∩ φ.symm ⁻¹' U
  have hmem {x : M} (hx : x ∈ U) : φ x ∈ V :=
    ⟨φ.map_source (hUφ hx), by simpa only [Set.mem_preimage, φ.left_inv (hUφ hx)]⟩
  have hV : V ∈ 𝓝 (φ a) :=
    (φ.isOpen_inter_preimage_symm hUo).mem_nhds (hmem haU)
  have hcont : ContinuousOn (χ ∘ f ∘ φ.symm) V :=
    χ.continuousOn.comp (f.continuous.comp_continuousOn
      (φ.continuousOn_symm.mono inter_subset_left)) fun y hy ↦ hUχ _ hy.2
  have hinj : ∀ y ∈ V, (χ ∘ f ∘ φ.symm) y = (χ ∘ f ∘ φ.symm) (φ a) → y = φ a := by
    intro y hy heq
    simp only [Function.comp_apply, φ.left_inv (hUφ haU)] at heq
    rw [← φ.right_inv hy.1, hU _ hy.2 (χ.injOn (hUχ _ hy.2) (hUχ a haU) heq)]
  let m : C(U, V) := ⟨fun x ↦ ⟨φ x, hmem x.property⟩,
    (φ.continuousOn.comp_continuous continuous_subtypeVal fun x ↦ hUφ x.property).subtype_mk _⟩
  have hm : m ⁻¹' {⟨φ a, mem_of_mem_nhds hV⟩} ⊆ {⟨a, haU⟩} := fun x hx ↦
    Subtype.ext (φ.injOn (hUφ x.property) (hUφ haU) (congrArg Subtype.val hx))
  have key := localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt R hV hcont hf hdet
    hinj k
  let τ : C(V, E) := ⟨V.domRestrict (χ ∘ f ∘ φ.symm), hcont.domRestrict⟩
  let t : C(V, E) := ⟨fun y ↦ (χ ∘ f ∘ φ.symm) (φ a) + (y - φ a), by fun_prop⟩
  have hτ₀ : τ ⁻¹' {(χ ∘ f ∘ φ.symm) (φ a)} ⊆ {⟨φ a, mem_of_mem_nhds hV⟩} := fun y hy ↦
    Subtype.ext (hinj y y.property hy)
  have ht₀ : t ⁻¹' {(χ ∘ f ∘ φ.symm) (φ a)} ⊆ {⟨φ a, mem_of_mem_nhds hV⟩} := fun y hy ↦
    Subtype.ext (sub_eq_zero.1 (add_eq_left.1 hy))
  have key' : localHomologyMap R τ hτ₀ k =
      (SignType.sign f'.det : ℤ) • localHomologyMap R t ht₀ k := by
    exact key
  have hτ : χ.sourceRestrict.comp
      ((f.restrictPreimage χ.source).comp (ContinuousMap.inclusion hUχ)) = τ.comp m := by
    ext x
    simp [τ, m, χ.sourceRestrict_apply, φ.left_inv (hUφ x.property), ContinuousMap.inclusion]
  have ht : (⟨fun y ↦ (χ ∘ f ∘ φ.symm) (φ a) + (y - φ a), by fun_prop⟩ : C(E, E)).comp
      (φ.sourceRestrict.comp (ContinuousMap.inclusion hUφ)) = t.comp m := by
    ext x
    simp [t, m, φ.sourceRestrict_apply, ContinuousMap.inclusion]
  rw [localHomologyMap_congr R hτ, localHomologyMap_congr R ht,
    ← localHomologyMap_comp R m τ hm hτ₀ k,
    ← localHomologyMap_comp R m t hm ht₀ k, key', Preadditive.comp_zsmul]

end Charts

end TauCeti
