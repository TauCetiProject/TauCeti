/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable

import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Standard invariant bilinear forms on Cartan realizations

Let `A : SymmetrizableDatum I` be a symmetrizable generalized Cartan matrix with symmetrizer
`d i > 0` (`d i * a i j = d j * a j i`), and let `R` be a realization of `A.cartan` in a vector
space `H` over a field `K` of characteristic zero, with simple coroots `hᵢ ∈ H` and simple roots
`αᵢ ∈ H*` satisfying `αⱼ(hᵢ) = a i j`.

Following Kac, a **standard invariant form** on `R` (`TauCeti.CartanRealization.InvariantForm A R`)
is a symmetric bilinear form `(·, ·)` on `H` satisfying `(hᵢ, h) = αᵢ(h) / d i` for all `i : I`
and `h ∈ H`. This normalization determines the form whenever either argument lies in the coroot
span `H'`: in particular `(hᵢ, hⱼ) = a j i / d i = a i j / d j`, the coroot span `H'` and the
Cartan center `Z(H) = ⋂ᵢ ker αᵢ` are automatically orthogonal, and the radical `ker (·, ·)` lies
in `Z(H)` and meets `H'` trivially.

Consequently, on a minimal realization (`R.IsMinimal`, where `Z(H) ⊆ H'`), **every** standard
invariant form is automatically nondegenerate (**Kac's Lemma 2.1**). Given any complement `W` to
`H'`, Kac's formula constructs the unique standard invariant form vanishing on `W × W`
(`InvariantForm.ofCompl`). On non-minimal realizations with `2 |I| < dim H`, however, every
complement `W` meets `Z(H)` nontrivially and `ofCompl` is degenerate
(`InvariantForm.not_nondegenerate_ofCompl_of_two_mul_card_lt_finrank`); nondegenerate extensions and
isometric classification on minimal vs. non-minimal realizations are developed in
`TauCeti.LinearAlgebra.Matrix.Cartan.Realization.InvariantForm.Uniqueness`, and the induced dual
form on `H*` is developed in `TauCeti.LinearAlgebra.Matrix.Cartan.Realization.InvariantForm.Dual`.

## Main definitions

* `TauCeti.CartanRealization.InvariantForm`: a symmetric bilinear form on `H` satisfying
  `(hᵢ, h) = αᵢ(h) / d i`.
* `TauCeti.CartanRealization.InvariantForm.reflectionIsometryEquiv`: simple reflections on `H`
  bundled as isometric equivalences of any standard invariant form.
* `TauCeti.CartanRealization.InvariantForm.map`,
  `TauCeti.CartanRealization.InvariantForm.restrict`: transport along linear equivalences and
  restriction to sub-realizations.
* `TauCeti.CartanRealization.InvariantForm.ofCompl`: Kac's standard invariant form associated to a
  complement `W` of `R.corootSpan`, characterized by vanishing on `W × W`.

## Main results

* `TauCeti.CartanRealization.InvariantForm.form_eq_of_mem_corootSpan_left`: any two standard
  invariant forms agree whenever an argument lies in `R.corootSpan`.
* `TauCeti.CartanRealization.InvariantForm.disjoint_ker_form_corootSpan`,
  `TauCeti.CartanRealization.InvariantForm.ker_form_le_cartanCenter`: the radical lies in the
  Cartan center and meets the coroot span trivially.
* `TauCeti.CartanRealization.InvariantForm.nondegenerate_of_isMinimal`: **Kac's Lemma 2.1**, every
  standard invariant form on a minimal realization is nondegenerate.
* `TauCeti.CartanRealization.InvariantForm.isOrthogonal_reflection`: invariance of `B.form` under
  simple reflections `Module.reflection`.
* `TauCeti.CartanRealization.InvariantForm.eq_ofCompl_iff`: `B = ofCompl A R hW` if and only if
  `B.form` vanishes on `W × W`.
* `TauCeti.CartanRealization.InvariantForm.not_nondegenerate_ofCompl_of_two_mul_card_lt_finrank`:
  degeneracy of `ofCompl` for every complement `W` whenever `2 |I| < finrank K H`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §2.1 (Lemma 2.1 and eqs. (2.1.1)–(2.1.4)) and §3.9.
-/

public section

open Module
open scoped Matrix

namespace TauCeti.CartanRealization

section DiagonalPairing

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : SymmetrizableDatum I}
  (R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H)

/-- Each simple root evaluates to `2` on its own simple coroot, supplying the reflection hypothesis
for `Module.reflection` on `H`. -/
theorem root_coroot_self (i : I) : R.root i (R.coroot i) = 2 := by
  simp

/-- Evaluation at the `i`-th simple coroot sends the `i`-th simple root to `2`, supplying the
reflection hypothesis for `Module.reflection` on `Module.Dual K H`. -/
theorem eval_coroot_root_self (i : I) : Dual.eval K H (R.coroot i) (R.root i) = 2 :=
  R.root_coroot_self i

end DiagonalPairing

/-- A **standard invariant bilinear form** on a Cartan realization `R` of a symmetrizable datum `A`
over a characteristic-zero field `K`: a symmetric bilinear form on `H` satisfying
`form (R.coroot i) h = R.root i h / A.symmetrizer i` for all `i : I` and `h : H`. -/
structure InvariantForm {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (A : SymmetrizableDatum I)
    (R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H) where
  /-- The underlying bilinear form on the ambient space of the realization. -/
  form : LinearMap.BilinForm K H
  /-- The bilinear form is symmetric. -/
  isSymm : form.IsSymm
  /-- Pairing a simple coroot on the left evaluates the simple root divided by the symmetrizer:
  `(hᵢ, h) = αᵢ(h) / d i`. -/
  form_coroot : ∀ i h, form (R.coroot i) h = R.root i h / A.symmetrizer i

namespace InvariantForm

attribute [simp] form_coroot

section Basic

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : SymmetrizableDatum I} {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}
  (B : InvariantForm A R)

@[ext]
theorem ext {B₁ B₂ : InvariantForm A R} (h : ∀ x y, B₁.form x y = B₂.form x y) : B₁ = B₂ := by
  cases B₁; cases B₂; congr; ext x y; exact h x y

/-- A standard invariant form is determined by its underlying bilinear form. -/
theorem form_injective : Function.Injective (InvariantForm.form (A := A) (R := R)) :=
  fun _ _ h ↦ ext fun x y ↦ LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- Pairing a simple coroot on the right evaluates the simple root divided by the symmetrizer. -/
@[simp]
theorem form_coroot_right (h : H) (i : I) :
    B.form h (R.coroot i) = R.root i h / A.symmetrizer i := by
  rw [B.isSymm.eq, B.form_coroot]

/-- Division-free form of the defining identity on the left: `d i * (hᵢ, h) = αᵢ(h)`. -/
theorem symmetrizer_mul_form_coroot (i : I) (h : H) :
    (A.symmetrizer i : K) * B.form (R.coroot i) h = R.root i h := by
  have hd : (A.symmetrizer i : K) ≠ 0 := Nat.cast_ne_zero.mpr (A.symmetrizer_ne_zero i)
  rw [B.form_coroot, mul_div_cancel₀ _ hd]

/-- Division-free form of the defining identity on the right: `d i * (h, hᵢ) = αᵢ(h)`. -/
theorem symmetrizer_mul_form_coroot_right (h : H) (i : I) :
    (A.symmetrizer i : K) * B.form h (R.coroot i) = R.root i h := by
  rw [B.isSymm.eq, B.symmetrizer_mul_form_coroot]

/-- On two simple coroots, `(hᵢ, hⱼ) = a j i / d i`. -/
theorem form_coroot_coroot' (i j : I) :
    B.form (R.coroot i) (R.coroot j) = (A.cartan j i : K) / A.symmetrizer i := by
  rw [B.form_coroot, R.root_coroot, Matrix.map_apply]

/-- On two simple coroots, `(hᵢ, hⱼ) = a i j / d j`. -/
theorem form_coroot_coroot (i j : I) :
    B.form (R.coroot i) (R.coroot j) = (A.cartan i j : K) / A.symmetrizer j := by
  rw [B.form_coroot_right, R.root_coroot, Matrix.map_apply]

/-- The squared norm of the `i`-th simple coroot is `2 / d i`. -/
theorem form_coroot_self (i : I) : B.form (R.coroot i) (R.coroot i) = 2 / A.symmetrizer i := by simp

/-- Every simple coroot is non-isotropic for a standard invariant form. -/
theorem form_coroot_self_ne_zero (i : I) : B.form (R.coroot i) (R.coroot i) ≠ 0 := by
  rw [B.form_coroot_self]
  exact div_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (A.symmetrizer_ne_zero i))

/-! ### Uniqueness on the coroot span and orthogonality with the Cartan center -/

/-- Any two standard invariant forms agree whenever their left argument lies in `R.corootSpan`. -/
theorem form_eq_of_mem_corootSpan_left (B₁ B₂ : InvariantForm A R) {x : H}
    (hx : x ∈ R.corootSpan) (y : H) : B₁.form x y = B₂.form x y := by
  rw [R.corootSpan_def] at hx
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    rw [B₁.form_coroot, B₂.form_coroot]
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | smul c _ _ ih => simp [ih]

/-- Any two standard invariant forms agree whenever their right argument lies in `R.corootSpan`. -/
theorem form_eq_of_mem_corootSpan_right (B₁ B₂ : InvariantForm A R) (x : H) {y : H}
    (hy : y ∈ R.corootSpan) : B₁.form x y = B₂.form x y := by
  rw [B₁.isSymm.eq, B₂.isSymm.eq, form_eq_of_mem_corootSpan_left B₁ B₂ hy x]

/-- When the simple coroots span `H` (for instance on a minimal realization of a nonsingular
matrix), there is at most one standard invariant form on `R`. -/
theorem eq_of_corootSpan_eq_top (hR : R.corootSpan = ⊤) (B₁ B₂ : InvariantForm A R) :
    B₁ = B₂ :=
  ext fun x y ↦ form_eq_of_mem_corootSpan_left B₁ B₂ (x := x) (hR ▸ Submodule.mem_top) y

/-- Vectors in `R.corootSpan` pair to zero on the left with vectors in `R.cartanCenter`. -/
theorem form_eq_zero_of_mem_corootSpan_of_mem_cartanCenter {x z : H}
    (hx : x ∈ R.corootSpan) (hz : z ∈ R.cartanCenter) : B.form x z = 0 := by
  rw [R.corootSpan_def] at hx
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    simp [(R.mem_cartanCenter_iff z).mp hz i]
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | smul c _ _ ih => simp [ih]

/-- Vectors in `R.cartanCenter` pair to zero on the left with vectors in `R.corootSpan`. -/
theorem form_eq_zero_of_mem_cartanCenter_of_mem_corootSpan {z x : H}
    (hz : z ∈ R.cartanCenter) (hx : x ∈ R.corootSpan) : B.form z x = 0 := by
  rw [B.isSymm.eq, B.form_eq_zero_of_mem_corootSpan_of_mem_cartanCenter hx hz]

/-- The Cartan center is orthogonal to the coroot span under any standard invariant form. -/
theorem cartanCenter_le_orthogonal_corootSpan :
    R.cartanCenter ≤ B.form.orthogonal R.corootSpan :=
  fun _ hz _ hx ↦ B.form_eq_zero_of_mem_corootSpan_of_mem_cartanCenter hx hz

/-- The coroot span is orthogonal to the Cartan center under any standard invariant form. -/
theorem corootSpan_le_orthogonal_cartanCenter :
    R.corootSpan ≤ B.form.orthogonal R.cartanCenter :=
  fun _ hx _ hz ↦ B.form_eq_zero_of_mem_cartanCenter_of_mem_corootSpan hz hx

/-- The central part of the coroot span is totally isotropic for every standard invariant form. -/
theorem form_eq_zero_of_mem_cartanCenter_inf_corootSpan {c₁ c₂ : H}
    (hc₁ : c₁ ∈ R.cartanCenter ⊓ R.corootSpan) (hc₂ : c₂ ∈ R.cartanCenter ⊓ R.corootSpan) :
    B.form c₁ c₂ = 0 :=
  B.form_eq_zero_of_mem_corootSpan_of_mem_cartanCenter hc₁.2 hc₂.1

/-! ### The radical and Kac's Lemma 2.1 -/

/-- The radical of any standard invariant form is contained in the Cartan center. -/
theorem ker_form_le_cartanCenter : LinearMap.ker B.form ≤ R.cartanCenter := by
  intro x hx
  rw [R.mem_cartanCenter_iff]
  intro i
  have h0 : B.form x (R.coroot i) = 0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) (R.coroot i)
  rw [← B.symmetrizer_mul_form_coroot_right x i, h0, mul_zero]

/-- The radical of any standard invariant form meets the coroot span trivially, with no finiteness
assumption on `I` or `H`. -/
theorem disjoint_ker_form_corootSpan : Disjoint (LinearMap.ker B.form) R.corootSpan := by
  rw [Submodule.disjoint_def]
  intro x hx hspan
  rw [R.corootSpan_def, ← Finsupp.range_linearCombination, LinearMap.mem_range] at hspan
  obtain ⟨c, rfl⟩ := hspan
  -- Pairing `∑ c i • hᵢ` against arbitrary `y` exhibits `∑ (c i / d i) • αᵢ = 0` in `Dual K H`.
  have hrel : ∑ i ∈ c.support, (c i / A.symmetrizer i) • R.root i = 0 := by
    ext y
    have hy : B.form (Finsupp.linearCombination K R.coroot c) y = 0 :=
      LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, LinearMap.sum_apply] at hy
    simpa [div_mul_eq_mul_div, mul_div_assoc] using hy
  have hc0 : c = 0 := by
    ext i
    by_cases hi : i ∈ c.support
    · have hdiv := linearIndependent_iff'.mp R.root_linearIndependent c.support
        (fun j ↦ c j / A.symmetrizer j) hrel i hi
      exact (div_eq_zero_iff.mp hdiv).resolve_right
        (Nat.cast_ne_zero.mpr (A.symmetrizer_ne_zero i))
    · exact Finsupp.notMem_support_iff.mp hi
  simp [hc0]

/-- Because `B.form` is symmetric, nondegeneracy is equivalent to triviality of its left kernel,
without assuming finite dimensionality. -/
theorem nondegenerate_form_iff_ker_eq_bot :
    B.form.Nondegenerate ↔ LinearMap.ker B.form = ⊥ :=
  B.isSymm.isRefl.nondegenerate_iff_separatingLeft.trans LinearMap.separatingLeft_iff_ker_eq_bot

/-- Whenever the Cartan center is contained in the coroot span, every standard invariant form on `R`
is nondegenerate. -/
theorem nondegenerate_of_cartanCenter_le_corootSpan (h : R.cartanCenter ≤ R.corootSpan) :
    B.form.Nondegenerate := by
  rw [B.nondegenerate_form_iff_ker_eq_bot, ← le_bot_iff]
  exact fun x hx ↦ B.disjoint_ker_form_corootSpan.le_bot ⟨hx, h (B.ker_form_le_cartanCenter hx)⟩

/-- **Kac's Lemma 2.1**: on a minimal realization, every standard invariant form is automatically
nondegenerate. -/
theorem nondegenerate_of_isMinimal [Fintype I] (hR : R.IsMinimal) : B.form.Nondegenerate :=
  B.nondegenerate_of_cartanCenter_le_corootSpan (R.isMinimal_iff_cartanCenter_le_corootSpan.mp hR)

/-- Evaluating a standard invariant form on a coroot linear combination on the left. -/
theorem form_corootMap_left [Fintype I] (c : I → K) (h : H) :
    B.form (R.corootMap c) h = ∑ i, (c i / A.symmetrizer i) * R.root i h := by
  simp [corootMap_apply, LinearMap.sum_apply, div_mul_eq_mul_div, mul_div_assoc]

/-- Evaluating a standard invariant form on a coroot linear combination on the right. -/
theorem form_corootMap_right [Fintype I] (h : H) (c : I → K) :
    B.form h (R.corootMap c) = ∑ i, (c i / A.symmetrizer i) * R.root i h := by
  rw [B.isSymm.eq, B.form_corootMap_left]

/-! ### Invariance under simple reflections on `H` -/

/-- Every standard invariant form is preserved by the simple reflection
`h ↦ h - αᵢ(h) • hᵢ` (`Module.reflection (R.root_coroot_self i)`). -/
theorem isOrthogonal_reflection (i : I) :
    B.form.IsOrthogonal (Module.reflection (R.root_coroot_self i)) := by
  intro x y
  simp only [Module.reflection_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, B.form_coroot, B.form_coroot_right, R.root_coroot_self i, div_eq_mul_inv]
  ring

/-- The simple reflection on `H` bundled as an isometric equivalence of `B.form`. -/
noncomputable def reflectionIsometryEquiv (i : I) : B.form.IsometryEquiv B.form :=
  { Module.reflection (R.root_coroot_self i) with map_app' := B.isOrthogonal_reflection i }

@[simp]
theorem reflectionIsometryEquiv_toLinearEquiv (i : I) :
    (B.reflectionIsometryEquiv i).toLinearEquiv = Module.reflection (R.root_coroot_self i) := (rfl)

@[simp]
theorem reflectionIsometryEquiv_apply (i : I) (h : H) :
    B.reflectionIsometryEquiv i h = Module.reflection (R.root_coroot_self i) h := (rfl)

/-! ### Transport and restriction -/

/-- Transport a standard invariant form along a linear equivalence of ambient spaces. -/
noncomputable def map {H' : Type*} [AddCommGroup H'] [Module K H'] (e : H ≃ₗ[K] H') :
    InvariantForm A (R.map e) where
  form := B.form.congr e
  isSymm := ⟨fun x y ↦ B.isSymm.eq (e.symm x) (e.symm y)⟩
  form_coroot i h := by simp

@[simp]
theorem map_form {H' : Type*} [AddCommGroup H'] [Module K H'] (e : H ≃ₗ[K] H') :
    (B.map e).form = B.form.congr e := (rfl)

theorem map_form_apply {H' : Type*} [AddCommGroup H'] [Module K H'] (e : H ≃ₗ[K] H') (x y : H') :
    (B.map e).form x y = B.form (e.symm x) (e.symm y) := (rfl)

/-- A linear equivalence `e : H ≃ₗ[K] H'` is an isometric equivalence from `B.form` to
`(B.map e).form`. -/
noncomputable def isometryEquivMap {H' : Type*} [AddCommGroup H'] [Module K H'] (e : H ≃ₗ[K] H') :
    B.form.IsometryEquiv (B.map e).form :=
  { e with map_app' := fun x y ↦ by simp }

@[simp]
theorem isometryEquivMap_toLinearEquiv {H' : Type*} [AddCommGroup H'] [Module K H']
    (e : H ≃ₗ[K] H') : (B.isometryEquivMap e).toLinearEquiv = e := (rfl)

@[simp]
theorem isometryEquivMap_apply {H' : Type*} [AddCommGroup H'] [Module K H']
    (e : H ≃ₗ[K] H') (x : H) : B.isometryEquivMap e x = e x := (rfl)

/-- Restrict a standard invariant form to a sub-realization. -/
def restrict (M : Submodule K H) (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤) :
    InvariantForm A (R.restrict M hc hs) where
  form := B.form.restrict M
  isSymm := B.isSymm.restrict M
  form_coroot i m := by simp [LinearMap.BilinForm.restrict_apply]

theorem restrict_form (M : Submodule K H) (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤) :
    (B.restrict M hc hs).form = B.form.restrict M := (rfl)

@[simp]
theorem restrict_form_apply (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (x y : M) :
    (B.restrict M hc hs).form x y = B.form x y := by
  simp [restrict_form, LinearMap.BilinForm.restrict_apply]

end Basic

/-! ### Kac's complement construction -/

section OfCompl

section Fintype

variable {I K H : Type*} [Fintype I] [Field K] [AddCommGroup H] [Module K H]

/-- Equivalence `(I → K) ≃ₗ[K] R.corootSpan` induced by `R.corootMap`. -/
private noncomputable def corootEquiv {A : Matrix I I K} (R : CartanRealization A H) :
    (I → K) ≃ₗ[K] R.corootSpan :=
  (LinearEquiv.ofInjective R.corootMap R.corootMap_injective).trans
    (LinearEquiv.ofEq _ _ R.range_corootMap)

/-- Coordinate projection `H →ₗ[K] (I → K)` onto `R.corootSpan` along a complement `W`. -/
private noncomputable def corootProj {A : Matrix I I K} (R : CartanRealization A H)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) : H →ₗ[K] (I → K) :=
  (corootEquiv R).symm.toLinearMap ∘ₗ R.corootSpan.projectionOnto W hW

private theorem corootMap_corootProj {A : Matrix I I K} (R : CartanRealization A H)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x : H) :
    R.corootMap (corootProj R hW x) = R.corootSpan.projection W hW x := by
  simp [corootProj, corootEquiv]

private theorem corootProj_coroot {A : Matrix I I K} [DecidableEq I] (R : CartanRealization A H)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (i : I) :
    corootProj R hW (R.coroot i) = Pi.single i 1 := by
  apply R.corootMap_injective
  rw [corootMap_corootProj,
    Submodule.projection_apply_of_mem_left hW (R.coroot_mem_corootSpan i),
    R.corootMap_single, one_smul]

private theorem corootProj_of_mem_right {A : Matrix I I K} (R : CartanRealization A H)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) {w : H} (hw : w ∈ W) :
    corootProj R hW w = 0 := by
  apply R.corootMap_injective
  rw [corootMap_corootProj, Submodule.projection_apply_of_mem_right hW hw, map_zero]

/-- One-sided bilinear helper `Φ(x, y) = ∑ᵢ (corootProj x i / d i) * αᵢ(y)` used to build
`ofCompl`. -/
private noncomputable def corootHalfForm (A : SymmetrizableDatum I)
    (R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) : LinearMap.BilinForm K H :=
  ∑ i, (LinearMap.proj i ∘ₗ corootProj R hW).smulRight ((A.symmetrizer i : K)⁻¹ • R.root i)

private theorem corootHalfForm_apply (A : SymmetrizableDatum I)
    (R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x y : H) :
    corootHalfForm A R hW x y =
      ∑ i, (corootProj R hW x i / A.symmetrizer i) * R.root i y := by
  simp [corootHalfForm, div_eq_mul_inv, mul_assoc]

private theorem corootHalfForm_corootMap_symm [CharZero K] (A : SymmetrizableDatum I)
    (R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x y : H) :
    corootHalfForm A R hW x (R.corootMap (corootProj R hW y)) =
      corootHalfForm A R hW y (R.corootMap (corootProj R hW x)) := by
  simp only [corootHalfForm_apply, corootMap_apply, map_sum, map_smul, smul_eq_mul, root_coroot,
    Matrix.map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hd_i : (A.symmetrizer i : K) ≠ 0 := Nat.cast_ne_zero.mpr (A.symmetrizer_ne_zero i)
  have hd_j : (A.symmetrizer j : K) ≠ 0 := Nat.cast_ne_zero.mpr (A.symmetrizer_ne_zero j)
  have hsymm : (A.symmetrizer i : K) * A.cartan i j = A.symmetrizer j * A.cartan j i := by
    exact_mod_cast A.symmetrizes i j
  have hdiv : (A.cartan i j : K) / A.symmetrizer j = (A.cartan j i : K) / A.symmetrizer i := by
    rw [div_eq_div_iff hd_j hd_i]
    linear_combination hsymm
  calc
    corootProj R hW y j * (corootProj R hW x i / A.symmetrizer i * A.cartan j i) =
        corootProj R hW x i * corootProj R hW y j * ((A.cartan j i : K) / A.symmetrizer i) := by
      ring
    _ = corootProj R hW x i * corootProj R hW y j * ((A.cartan i j : K) / A.symmetrizer j) := by
      rw [← hdiv]
    _ = corootProj R hW x i * (corootProj R hW y j / A.symmetrizer j * A.cartan i j) := by
      ring

/-- Kac's standard invariant form associated to a choice of complement `W` to `R.corootSpan`:
on `x = h₁ + w₁` and `y = h₂ + w₂` (`h₁, h₂ ∈ R.corootSpan`, `w₁, w₂ ∈ W`), it satisfies
`(hᵢ, h) = αᵢ(h) / d i` and vanishes on `W × W`. -/
noncomputable def ofCompl [CharZero K] (A : SymmetrizableDatum I)
    (R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) : InvariantForm A R where
  form := corootHalfForm A R hW + LinearMap.flip (corootHalfForm A R hW) -
    (corootHalfForm A R hW).comp LinearMap.id (R.corootSpan.projection W hW)
  isSymm := ⟨fun x y ↦ by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.flip_apply,
      LinearMap.BilinForm.comp_apply, LinearMap.id_apply, ← corootMap_corootProj]
    rw [corootHalfForm_corootMap_symm]
    ring⟩
  form_coroot i y := by
    have hsym := corootHalfForm_corootMap_symm A R hW y (R.coroot i)
    rw [corootMap_corootProj, corootMap_corootProj,
      Submodule.projection_apply_of_mem_left hW (R.coroot_mem_corootSpan i)] at hsym
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.flip_apply,
      LinearMap.BilinForm.comp_apply, LinearMap.id_apply, hsym, add_sub_cancel_right]
    classical
    simp [corootHalfForm_apply, corootProj_coroot, Pi.single_apply, div_eq_inv_mul]

section

variable [CharZero K] {A : SymmetrizableDatum I}
  {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}

/-- `ofCompl A R hW` vanishes when both arguments lie in the chosen complement `W`. -/
theorem ofCompl_form_eq_zero {W : Submodule K H} (hW : IsCompl R.corootSpan W) {w₁ w₂ : H}
    (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W) :
    (ofCompl A R hW).form w₁ w₂ = 0 := by
  simp [ofCompl, corootHalfForm_apply, corootProj_of_mem_right R hW hw₁,
    corootProj_of_mem_right R hW hw₂]

/-- The restriction of `(ofCompl A R hW).form` to the chosen complement `W` is zero. -/
@[simp]
theorem ofCompl_form_restrict_eq_zero {W : Submodule K H} (hW : IsCompl R.corootSpan W) :
    (ofCompl A R hW).form.restrict W = 0 :=
  LinearMap.ext₂ fun w₁ w₂ ↦ ofCompl_form_eq_zero hW w₁.2 w₂.2

/-- `ofCompl A R hW` is the **unique** standard invariant form on `R` vanishing on `W × W`. -/
theorem eq_ofCompl_of_form_eq_zero (B : InvariantForm A R) {W : Submodule K H}
    (hW : IsCompl R.corootSpan W) (hB : ∀ w₁ ∈ W, ∀ w₂ ∈ W, B.form w₁ w₂ = 0) :
    B = ofCompl A R hW := by
  ext x y
  set hx := R.corootSpan.projection W hW x
  set hy := R.corootSpan.projection W hW y
  have hhx : hx ∈ R.corootSpan := Submodule.projection_apply_mem hW x
  have hhy : hy ∈ R.corootSpan := Submodule.projection_apply_mem hW y
  have hwx : x - hx ∈ W := Submodule.sub_projection_mem hW x
  have hwy : y - hy ∈ W := Submodule.sub_projection_mem hW y
  rw [(add_sub_cancel hx x).symm, (add_sub_cancel hy y).symm]
  simp only [map_add, LinearMap.add_apply,
    form_eq_of_mem_corootSpan_left B (ofCompl A R hW) hhx,
    form_eq_of_mem_corootSpan_right B (ofCompl A R hW) _ hhy,
    hB _ hwx _ hwy, ofCompl_form_eq_zero hW hwx hwy]

/-- A standard invariant form equals `ofCompl A R hW` if and only if its restriction to `W`
vanishes. -/
theorem eq_ofCompl_iff (B : InvariantForm A R) {W : Submodule K H}
    (hW : IsCompl R.corootSpan W) :
    B = ofCompl A R hW ↔ B.form.restrict W = 0 := by
  refine ⟨fun h ↦ h ▸ ofCompl_form_restrict_eq_zero hW, fun h ↦ ?_⟩
  refine eq_ofCompl_of_form_eq_zero B hW fun w₁ hw₁ w₂ hw₂ ↦ ?_
  simpa [LinearMap.BilinForm.restrict_apply] using
    LinearMap.congr_fun (LinearMap.congr_fun h ⟨w₁, hw₁⟩) ⟨w₂, hw₂⟩

/-- Every central vector lying in the chosen complement `W` belongs to the radical of
`ofCompl A R hW`. -/
theorem cartanCenter_inf_le_ker_ofCompl {W : Submodule K H} (hW : IsCompl R.corootSpan W) :
    R.cartanCenter ⊓ W ≤ LinearMap.ker (ofCompl A R hW).form := by
  rintro x ⟨hxc, hxw⟩
  rw [LinearMap.mem_ker]; ext y
  simp [ofCompl, corootHalfForm_apply, corootProj_of_mem_right R hW hxw,
    (R.mem_cartanCenter_iff x).mp hxc]

/-- If the chosen complement `W` meets `R.cartanCenter` nontrivially, Kac's complement form
`ofCompl A R hW` is degenerate. -/
theorem not_nondegenerate_ofCompl_of_cartanCenter_inf_ne_bot {W : Submodule K H}
    (hW : IsCompl R.corootSpan W) (h : R.cartanCenter ⊓ W ≠ ⊥) :
    ¬ (ofCompl A R hW).form.Nondegenerate := by
  rw [(ofCompl A R hW).nondegenerate_form_iff_ker_eq_bot]
  exact fun hker ↦ h (le_bot_iff.mp (hker ▸ cartanCenter_inf_le_ker_ofCompl hW))

/-- Whenever `2 * |I| < finrank K H` (for example `A₁` enlarged to `ℚ³`), every complement `W` to
`R.corootSpan` meets `R.cartanCenter` nontrivially, so Kac's complement construction `ofCompl` is
degenerate for **every** choice of `W`. -/
theorem not_nondegenerate_ofCompl_of_two_mul_card_lt_finrank [FiniteDimensional K H]
    {W : Submodule K H} (hW : IsCompl R.corootSpan W)
    (hdim : 2 * Fintype.card I < finrank K H) :
    ¬ (ofCompl A R hW).form.Nondegenerate := by
  apply not_nondegenerate_ofCompl_of_cartanCenter_inf_ne_bot hW
  intro hbot
  have h1 := Submodule.finrank_add_eq_of_isCompl hW
  rw [R.finrank_corootSpan] at h1
  have h2 := R.finrank_cartanCenter_add_card
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq R.cartanCenter W
  have h4 : finrank K ↥(R.cartanCenter ⊔ W) ≤ finrank K H := Submodule.finrank_le _
  rw [hbot, finrank_bot] at h3
  omega

end

end Fintype

/-- Every Cartan realization of a finite symmetrizable datum over a characteristic-zero field
admits at least one standard invariant form (by choosing any complement to `R.corootSpan`). -/
theorem nonempty {I K H : Type*} [Finite I] [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (A : SymmetrizableDatum I) (R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H) :
    Nonempty (InvariantForm A R) := by
  let := Fintype.ofFinite I
  obtain ⟨_, hW⟩ := Submodule.exists_isCompl R.corootSpan
  exact ⟨ofCompl A R hW⟩

end OfCompl

end InvariantForm

end TauCeti.CartanRealization

end
