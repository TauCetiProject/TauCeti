/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.CentralSplitting

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Normalized bilinear forms on a Cartan realization

Let `R` be a realization of a square matrix `A` over a field `K`, with simple coroots `hᵢ` in `H`
and simple roots `αᵢ` in its dual, and let `d` be a family of scalars, typically the symmetrizer
of a symmetrizable generalized Cartan matrix, so that `dᵢ aᵢⱼ = dⱼ aⱼᵢ`. A bilinear form on `H` is
*normalized* by `d` when `(dᵢ hᵢ, h) = αᵢ(h)` for every node and every `h ∈ H`, that is
`(hᵢ, h) = αᵢ(h) / dᵢ`. This is the restriction to the Cartan subalgebra of the standard invariant
form of a symmetrizable Kac–Moody algebra, and it is the input from which that invariant form,
the identification `ν : H ≃ H*` and the form `(αᵢ, αⱼ) = dᵢ aᵢⱼ` on `H*` are built.

The values of a normalized form are prescribed on `H' × H`, where `H'` is the coroot span. For a
complement `C` of `H'`, Kac's recipe sets `(C, C) = 0`; `complementForm` is the resulting form.
It is symmetric because `dᵢ aᵢⱼ = dⱼ aⱼᵢ`, and it is the only symmetric normalized form vanishing
on `C × C`. The recipe exists for every realization, but it is nondegenerate only for a minimal
one: on a minimal realization, every symmetric normalized form is nondegenerate (Kac, Lemma 2.1),
although the symmetrized matrix `(dᵢ aᵢⱼ)` alone is degenerate whenever `A` is singular.

A normalized form is not unique, since its values on `C × C` are free. On a minimal realization
it is unique up to isometry: any two symmetric normalized forms are related by a linear
automorphism of `H` fixing every simple root and coroot. In particular the recipe does not depend
on the complement up to such an isometry. On a non-minimal realization the recipe is degenerate,
but a nondegenerate symmetric normalized form still exists: extend one on a minimal
sub-realization by any nondegenerate form on a central complement.

## Main definitions

* `TauCeti.CartanRealization.IsNormalizedForm`: `B (dᵢ hᵢ) = αᵢ` for every node `i`.
* `TauCeti.CartanRealization.complementForm`: Kac's normalized form attached to a complement
  of the coroot span.

## Main results

* `TauCeti.CartanRealization.IsNormalizedForm.apply_coroot`: `(hᵢ, ·) = dᵢ⁻¹ αᵢ`.
* `TauCeti.CartanRealization.IsNormalizedForm.symmetrizes`: a symmetric normalized form forces
  `dᵢ aᵢⱼ = dⱼ aⱼᵢ`.
* `TauCeti.CartanRealization.isSymm_complementForm` and
  `TauCeti.CartanRealization.eq_complementForm`: the recipe is symmetric, and it is the only
  symmetric normalized form vanishing on the complement.
* `TauCeti.CartanRealization.IsNormalizedForm.nondegenerate`: on a minimal realization every
  symmetric normalized form is nondegenerate.
* `TauCeti.CartanRealization.IsNormalizedForm.exists_isometryEquiv_map_eq_self`: on a minimal
  realization two symmetric normalized forms are isometric through an automorphism fixing the
  simple roots and coroots.
* `TauCeti.CartanRealization.exists_isNormalizedForm`: every realization carries a
  nondegenerate symmetric normalized form.
* `TauCeti.CartanRealization.IsNormalizedForm.toDual_symm_root` and
  `TauCeti.CartanRealization.IsNormalizedForm.apply_toDual_symm_root_root`: `ν⁻¹(αᵢ) = dᵢ hᵢ`,
  and the transported form on the dual is `(αᵢ, αⱼ) = dᵢ aᵢⱼ`.
* `TauCeti.CartanRealization.IsNormalizedForm.isOrthogonal_reflection`: a symmetric normalized
  form is invariant under each simple reflection `h ↦ h - αᵢ(h) hᵢ`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §2.1 (the form on `𝔥` attached
  to a complement of `𝔥'`, Lemma 2.1, and the map `ν`) and §3.9 (invariance under the simple
  reflections).
-/

public section

open Module

namespace TauCeti.CartanRealization

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I K}
  (R : CartanRealization A H)

/-! ### Normalized forms -/

/-- A bilinear form `B` on the ambient space of a realization is *normalized* by a family `d` of
scalars when `B (dᵢ hᵢ) = αᵢ` for every node `i`, that is `(hᵢ, h) = αᵢ(h) / dᵢ` for every `h`.
Every `dᵢ` is then nonzero (`TauCeti.CartanRealization.IsNormalizedForm.ne_zero`). For a
symmetrizable generalized Cartan matrix, `d` is the symmetrizer. -/
def IsNormalizedForm (d : I → K) (B : LinearMap.BilinForm K H) : Prop :=
  ∀ i, B (d i • R.coroot i) = R.root i

variable {R} {d : I → K} {B : LinearMap.BilinForm K H}

/-- Unfolding `TauCeti.CartanRealization.IsNormalizedForm`. -/
theorem isNormalizedForm_iff :
    R.IsNormalizedForm d B ↔ ∀ i, B (d i • R.coroot i) = R.root i :=
  Iff.rfl

namespace IsNormalizedForm

variable (hB : R.IsNormalizedForm d B)
include hB

/-- A normalized form pairs `dᵢ hᵢ` with every vector through the simple root `αᵢ`. -/
theorem apply_smul_coroot (i : I) (h : H) : B (d i • R.coroot i) h = R.root i h := by
  rw [hB i]

/-- The normalizing family has no zero entry, since the simple roots are nonzero. -/
theorem ne_zero (i : I) : d i ≠ 0 := by
  intro h
  apply R.root_linearIndependent.ne_zero i
  rw [← hB i, h, zero_smul, map_zero]

/-- A normalized form pairs `hᵢ` through `dᵢ⁻¹ αᵢ`. -/
theorem apply_coroot (i : I) : B (R.coroot i) = (d i)⁻¹ • R.root i := by
  rw [← hB i, map_smul, smul_smul, inv_mul_cancel₀ (hB.ne_zero i), one_smul]

/-- The Gram matrix of a normalized form on the simple coroots: `(hᵢ, hⱼ) = aⱼᵢ / dᵢ`. -/
theorem apply_coroot_coroot (i j : I) : B (R.coroot i) (R.coroot j) = (d i)⁻¹ * A j i := by
  rw [hB.apply_coroot, LinearMap.smul_apply, root_coroot, smul_eq_mul]

/-- A symmetric normalized form exists only if `d` symmetrizes the matrix: `dᵢ aᵢⱼ = dⱼ aⱼᵢ`. -/
theorem symmetrizes (hs : B.IsSymm) (i j : I) : d i * A i j = d j * A j i := by
  have h := hs.eq (d i • R.coroot i) (d j • R.coroot j)
  rw [hB i, hB j, map_smul, map_smul, root_coroot, root_coroot, smul_eq_mul, smul_eq_mul] at h
  exact h.symm

/-- The coroot span is orthogonal to the Cartan center for a normalized form. -/
theorem apply_eq_zero_of_mem_cartanCenter {x z : H} (hx : x ∈ R.corootSpan)
    (hz : z ∈ R.cartanCenter) : B x z = 0 := by
  rw [corootSpan_def] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp [hB.apply_coroot, (R.mem_cartanCenter_iff z).mp hz]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-- A normalized form pairs the coroot combination `∑ cᵢ hᵢ` through `∑ (cᵢ / dᵢ) αᵢ`. -/
theorem apply_corootMap [Fintype I] (c : I → K) :
    B (R.corootMap c) = ∑ i, (c i / d i) • R.root i := by
  simp [corootMap_apply, hB.apply_coroot, smul_smul, div_eq_mul_inv]

/-- On a minimal realization every symmetric normalized form is nondegenerate [Kac, Lemma 2.1]. -/
theorem nondegenerate [Fintype I] (hs : B.IsSymm) (hR : R.IsMinimal) : B.Nondegenerate := by
  -- A vector in the radical is killed by every simple root, so it is central; minimality puts it
  -- in the coroot span, where the independence of the simple roots forces it to vanish.
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hs.isRefl).mpr
    (LinearMap.separatingLeft_iff_linear_nontrivial.mpr fun x hx => ?_)
  have hc : x ∈ R.cartanCenter := (R.mem_cartanCenter_iff x).mpr fun i => by
    rw [← hB.apply_smul_coroot, hs.eq, hx, LinearMap.zero_apply]
  obtain ⟨c, rfl⟩ := (R.mem_corootSpan_iff x).mp
    (R.isMinimal_iff_cartanCenter_le_corootSpan.mp hR hc)
  rw [hB.apply_corootMap] at hx
  have hc0 : c = 0 := funext fun i => by
    have := Fintype.linearIndependent_iff.mp R.root_linearIndependent _ hx i
    rwa [div_eq_zero_iff, or_iff_left (hB.ne_zero i)] at this
  rw [hc0, map_zero]

/-! ### The identification `ν : H ≃ H*` -/

/-- The identification `ν` of `H` with its dual given by a nondegenerate normalized form sends
`dᵢ hᵢ` to the simple root: `ν⁻¹(αᵢ) = dᵢ hᵢ`. -/
theorem toDual_symm_root [FiniteDimensional K H] (hnd : B.Nondegenerate) (i : I) :
    (B.toDual hnd).symm (R.root i) = d i • R.coroot i := by
  rw [LinearEquiv.symm_apply_eq]
  ext h
  rw [LinearMap.BilinForm.toDual_def, hB.apply_smul_coroot]

/-- The form transported to the dual pairs a simple root with a functional `μ` through its value
on the simple coroot: `(αᵢ, μ) = dᵢ μ(hᵢ)`. -/
theorem apply_toDual_symm_root [FiniteDimensional K H] (hs : B.IsSymm) (hnd : B.Nondegenerate)
    (i : I) (μ : Dual K H) :
    B ((B.toDual hnd).symm (R.root i)) ((B.toDual hnd).symm μ) = d i * μ (R.coroot i) := by
  rw [hB.toDual_symm_root hnd, map_smul, LinearMap.smul_apply, hs.eq,
    LinearMap.BilinForm.apply_toDual_symm_apply, smul_eq_mul]

/-- The form transported to the dual has Gram matrix `(αᵢ, αⱼ) = dᵢ aᵢⱼ` on the simple roots,
the symmetrized matrix. -/
theorem apply_toDual_symm_root_root [FiniteDimensional K H] (hs : B.IsSymm)
    (hnd : B.Nondegenerate) (i j : I) :
    B ((B.toDual hnd).symm (R.root i)) ((B.toDual hnd).symm (R.root j)) = d i * A i j := by
  rw [hB.apply_toDual_symm_root hs hnd, root_coroot]

/-! ### Invariance under the simple reflections -/

/-- A symmetric normalized form is invariant under the simple reflection
`h ↦ h - αᵢ(h) hᵢ` of a node with `αᵢ(hᵢ) = 2`. -/
theorem isOrthogonal_reflection (hs : B.IsSymm) {i : I} (h2 : R.root i (R.coroot i) = 2) :
    B.IsOrthogonal (Module.reflection h2) := by
  intro x y
  have hx : B x (R.coroot i) = (d i)⁻¹ * R.root i x := by
    rw [hs.eq, hB.apply_coroot, LinearMap.smul_apply, smul_eq_mul]
  simp only [Module.reflection_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hx, hB.apply_coroot, h2]
  ring

end IsNormalizedForm

/-! ### Kac's recipe on a complement of the coroot span -/

section Complement

variable (R) (d) {C : Submodule K H} (hC : IsCompl R.corootSpan C)

/-- The simple coroots, as a basis of their span. -/
private noncomputable def corootBasis : Basis I K R.corootSpan :=
  (Basis.span R.coroot_linearIndependent).map (LinearEquiv.ofEq _ _ R.corootSpan_def.symm)

private theorem coe_corootBasis (i : I) : (R.corootBasis i : H) = R.coroot i := by
  rw [corootBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]

/-- The functional part of Kac's recipe: it sends `hᵢ` to `dᵢ⁻¹ αᵢ` and vanishes on the
complement `C`. -/
private noncomputable def complementDual : H →ₗ[K] Dual K H :=
  LinearMap.ofIsCompl hC (R.corootBasis.constr K fun i => (d i)⁻¹ • R.root i) 0

private theorem complementDual_coroot (i : I) :
    complementDual R d hC (R.coroot i) = (d i)⁻¹ • R.root i := by
  rw [← R.coe_corootBasis i, complementDual, LinearMap.ofIsCompl_apply_left, Basis.constr_basis]

private theorem complementDual_of_mem {x : H} (hx : x ∈ C) : complementDual R d hC x = 0 :=
  LinearMap.ofIsCompl_apply_right hC (v := ⟨x, hx⟩)

/-- Kac's normalized form attached to a complement `C` of the coroot span: the bilinear form with
`(hᵢ, h) = αᵢ(h) / dᵢ` for every `h` and `(x, y) = 0` for `x, y ∈ C`. It is normalized when every
`dᵢ` is nonzero (`TauCeti.CartanRealization.isNormalizedForm_complementForm`), and symmetric when
moreover `dᵢ aᵢⱼ = dⱼ aⱼᵢ` (`TauCeti.CartanRealization.isSymm_complementForm`). -/
noncomputable def complementForm : LinearMap.BilinForm K H :=
  complementDual R d hC + (complementDual R d hC).flip ∘ₗ C.projection R.corootSpan hC.symm

private theorem complementForm_apply (x y : H) :
    R.complementForm d hC x y =
      complementDual R d hC x y + complementDual R d hC y (C.projection R.corootSpan hC.symm x) :=
  (rfl)

/-- Kac's recipe pairs `hᵢ` through `dᵢ⁻¹ αᵢ`. -/
@[simp]
theorem complementForm_coroot (i : I) :
    R.complementForm d hC (R.coroot i) = (d i)⁻¹ • R.root i := by
  ext y
  rw [complementForm_apply, (Submodule.projection_apply_eq_zero_iff _).mpr
    (R.coroot_mem_corootSpan i), map_zero, add_zero, complementDual_coroot]

/-- Kac's recipe vanishes on the complement. -/
theorem complementForm_apply_of_mem {x y : H} (hx : x ∈ C) (hy : y ∈ C) :
    R.complementForm d hC x y = 0 := by
  rw [complementForm_apply, Submodule.projection_apply_of_mem_left _ hx,
    complementDual_of_mem _ _ _ hx, complementDual_of_mem _ _ _ hy, LinearMap.zero_apply,
    LinearMap.zero_apply, add_zero]

/-- Kac's recipe pairs a vector `x` of the complement with `hᵢ` through `αᵢ(x) / dᵢ`. -/
theorem complementForm_apply_coroot_of_mem {x : H} (hx : x ∈ C) (i : I) :
    R.complementForm d hC x (R.coroot i) = (d i)⁻¹ * R.root i x := by
  rw [complementForm_apply, Submodule.projection_apply_of_mem_left _ hx,
    complementDual_of_mem _ _ _ hx, complementDual_coroot, LinearMap.zero_apply, zero_add,
    LinearMap.smul_apply, smul_eq_mul]

/-- Kac's recipe is normalized when every `dᵢ` is nonzero. -/
theorem isNormalizedForm_complementForm (hd : ∀ i, d i ≠ 0) :
    R.IsNormalizedForm d (R.complementForm d hC) := fun i => by
  rw [map_smul, complementForm_coroot, smul_smul, mul_inv_cancel₀ (hd i), one_smul]

variable {R}

include hC in
/-- Two bilinear forms agreeing on pairs of simple coroots and of vectors of a complement of the
coroot span are equal. -/
private theorem bilinForm_ext {B₁ B₂ : LinearMap.BilinForm K H}
    (h₁ : ∀ i j, B₁ (R.coroot i) (R.coroot j) = B₂ (R.coroot i) (R.coroot j))
    (h₂ : ∀ i, ∀ y ∈ C, B₁ (R.coroot i) y = B₂ (R.coroot i) y)
    (h₃ : ∀ x ∈ C, ∀ j, B₁ x (R.coroot j) = B₂ x (R.coroot j))
    (h₄ : ∀ x ∈ C, ∀ y ∈ C, B₁ x y = B₂ x y) : B₁ = B₂ := by
  have hspan : Submodule.span K (Set.range R.coroot ∪ C) = ⊤ := by
    rw [Submodule.span_union, Submodule.span_eq, ← corootSpan_def, hC.sup_eq_top]
  refine LinearMap.ext_on hspan fun x hx => LinearMap.ext_on hspan fun y hy => ?_
  rcases hx with ⟨i, rfl⟩ | hx <;> rcases hy with ⟨j, rfl⟩ | hy
  exacts [h₁ i j, h₂ i y hy, h₃ x hx j, h₄ x hx y hy]

variable (R)

/-- Kac's recipe is symmetric when `d` is a family of nonzero scalars symmetrizing the
matrix. -/
theorem isSymm_complementForm (hd : ∀ i, d i ≠ 0) (hs : ∀ i j, d i * A i j = d j * A j i) :
    (R.complementForm d hC).IsSymm := by
  suffices h : R.complementForm d hC = (R.complementForm d hC).flip from
    ⟨fun x y => DFunLike.congr_fun (DFunLike.congr_fun h x) y⟩
  refine bilinForm_ext hC (fun i j => ?_) (fun i y hy => ?_) (fun x hx j => ?_)
    (fun x hx y hy => ?_)
  · rw [LinearMap.BilinForm.flip_apply, complementForm_coroot,
      complementForm_coroot, LinearMap.smul_apply, LinearMap.smul_apply, root_coroot,
      root_coroot, smul_eq_mul, smul_eq_mul]
    field_simp [hd i, hd j]
    linear_combination -hs i j
  · rw [LinearMap.BilinForm.flip_apply, complementForm_coroot,
      complementForm_apply_coroot_of_mem _ _ _ hy, LinearMap.smul_apply, smul_eq_mul]
  · rw [LinearMap.BilinForm.flip_apply, complementForm_coroot,
      complementForm_apply_coroot_of_mem _ _ _ hx, LinearMap.smul_apply, smul_eq_mul]
  · rw [LinearMap.BilinForm.flip_apply,
      complementForm_apply_of_mem _ _ _ hx hy, complementForm_apply_of_mem _ _ _ hy hx]

variable {R d}

/-- Kac's recipe is the only symmetric normalized form vanishing on the complement. -/
theorem eq_complementForm (hB : R.IsNormalizedForm d B) (hs : B.IsSymm)
    (hBC : ∀ x ∈ C, ∀ y ∈ C, B x y = 0) : B = R.complementForm d hC := by
  refine bilinForm_ext hC (fun i j => ?_) (fun i y _ => ?_) (fun x hx j => ?_)
    (fun x hx y hy => ?_)
  · rw [hB.apply_coroot, complementForm_coroot]
  · rw [hB.apply_coroot, complementForm_coroot]
  · rw [hs.eq, hB.apply_coroot, complementForm_apply_coroot_of_mem _ _ _ hx,
      LinearMap.smul_apply, smul_eq_mul]
  · rw [hBC x hx y hy, complementForm_apply_of_mem _ _ _ hx hy]

end Complement

/-! ### Uniqueness up to isometry and existence -/

section Isometry

variable [Fintype I]

/-- On a minimal realization, any two symmetric normalized forms are isometric through a linear
automorphism of the ambient space fixing every simple root and coroot. -/
theorem IsNormalizedForm.exists_isometryEquiv_map_eq_self [NeZero (2 : K)] (hR : R.IsMinimal)
    {B₁ B₂ : LinearMap.BilinForm K H} (hB₁ : R.IsNormalizedForm d B₁)
    (hB₂ : R.IsNormalizedForm d B₂) (hs₁ : B₁.IsSymm) (hs₂ : B₂.IsSymm) :
    ∃ e : B₂.IsometryEquiv B₁, R.map (e : H ≃ₗ[K] H) = R := by
  -- The automorphism is `id + c`, where `c x` is `B₁`-dual to half of `(B₂ - B₁)(x, ·)`. The
  -- difference `B₂ - B₁` vanishes on the coroot span, so `c` takes values in the Cartan center,
  -- hence in the coroot span by minimality, and kills the coroot span; thus `c ∘ c = 0`.
  have := hR.finiteDimensional
  have hnd := hB₁.nondegenerate hs₁ hR
  have hDs : (B₂ - B₁).IsSymm := hs₂.sub hs₁
  -- The difference of the two forms vanishes on the coroot span.
  have hDH : ∀ x ∈ R.corootSpan, (B₂ - B₁) x = 0 := by
    intro x hx
    rw [corootSpan_def] at hx
    refine (Submodule.span_le (p := LinearMap.ker (B₂ - B₁)).mpr ?_ hx :)
    rintro _ ⟨i, rfl⟩
    simp [hB₁.apply_coroot, hB₂.apply_coroot]
  let c : H →ₗ[K] H := (B₁.toDual hnd).symm.toLinearMap ∘ₗ ((2 : K)⁻¹ • (B₂ - B₁))
  have hc : ∀ x y, B₁ (c x) y = (2 : K)⁻¹ * (B₂ - B₁) x y := fun x y => by
    simp [c]
  have hcC : ∀ x, c x ∈ R.cartanCenter := fun x => (R.mem_cartanCenter_iff _).mpr fun i => by
    rw [← hB₁.apply_smul_coroot, hs₁.eq, hc, hDs.eq,
      hDH _ (Submodule.smul_mem _ _ (R.coroot_mem_corootSpan i)), LinearMap.zero_apply, mul_zero]
  have hcH : ∀ x, c x ∈ R.corootSpan :=
    fun x => R.isMinimal_iff_cartanCenter_le_corootSpan.mp hR (hcC x)
  have hc0 : ∀ x ∈ R.corootSpan, c x = 0 := fun x hx => by
    simp [c, hDH x hx]
  let e : H ≃ₗ[K] H := LinearEquiv.ofLinearMap (LinearMap.id + c) (LinearMap.id - c)
    (LinearMap.ext fun x => by simp [hc0 _ (hcH x)])
    (LinearMap.ext fun x => by simp [hc0 _ (hcH x)])
  have he : ∀ x, e x = x + c x := fun x => by simp [e]
  have hiso : ∀ x y, B₁ (e x) (e y) = B₂ x y := by
    intro x y
    have h2 : (2 : K)⁻¹ * (B₂ - B₁) x y + (2 : K)⁻¹ * (B₂ - B₁) x y = (B₂ - B₁) x y := by
      rw [← two_mul, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
    simp only [he, map_add, LinearMap.add_apply]
    rw [hB₁.apply_eq_zero_of_mem_cartanCenter (hcH x) (hcC y), hc x y, hs₁.eq x (c y), hc y x,
      hDs.eq y x]
    rw [LinearMap.sub_apply, LinearMap.sub_apply] at h2 ⊢
    linear_combination h2
  refine ⟨⟨e, hiso⟩, ?_⟩
  ext i h
  · rw [map_coroot, he, hc0 _ (R.coroot_mem_corootSpan i), add_zero]
  · have hsymm : e.symm h = h - c h := by simp [e]
    rw [map_root_apply, hsymm, map_sub, (R.mem_cartanCenter_iff _).mp (hcC h), sub_zero]

/-- On a minimal realization, Kac's recipe does not depend on the complement up to an isometry
fixing every simple root and coroot. -/
theorem exists_isometryEquiv_complementForm [NeZero (2 : K)] (hR : R.IsMinimal)
    (hd : ∀ i, d i ≠ 0) (hs : ∀ i j, d i * A i j = d j * A j i) {C₁ C₂ : Submodule K H}
    (h₁ : IsCompl R.corootSpan C₁) (h₂ : IsCompl R.corootSpan C₂) :
    ∃ e : (R.complementForm d h₁).IsometryEquiv (R.complementForm d h₂),
      R.map (e : H ≃ₗ[K] H) = R :=
  (R.isNormalizedForm_complementForm d h₂ hd).exists_isometryEquiv_map_eq_self hR
    (R.isNormalizedForm_complementForm d h₁ hd) (R.isSymm_complementForm d h₂ hd hs)
    (R.isSymm_complementForm d h₁ hd hs)

end Isometry

section Existence

variable [Finite I]

/-- Every realization carries a nondegenerate symmetric normalized form, for any family of
nonzero scalars symmetrizing the matrix. -/
theorem exists_isNormalizedForm (hd : ∀ i, d i ≠ 0) (hs : ∀ i j, d i * A i j = d j * A j i) :
    ∃ B : LinearMap.BilinForm K H, R.IsNormalizedForm d B ∧ B.IsSymm ∧ B.Nondegenerate := by
  classical
  let := Fintype.ofFinite I
  -- Split `H = M ⊕ Z` with `M` a minimal sub-realization and `Z` central. Take Kac's recipe on
  -- `M`, the form of a basis on `Z`, and their orthogonal sum.
  obtain ⟨M, Z, hc, hsM, hmin, hMZ, hZ⟩ := R.exists_isMinimal_restrict_isCompl
  set S := R.restrict M hc hsM
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S.corootSpan
  have hBM := S.isNormalizedForm_complementForm d hC hd
  have hsBM := S.isSymm_complementForm d hC hd hs
  let b := Basis.ofVectorSpace K Z
  let BZ : LinearMap.BilinForm K Z := b.toDual
  have hsZ : BZ.IsSymm := (LinearMap.BilinForm.isSymm_iff_basis b).mpr fun i j => by
    simp [BZ, Basis.toDual_apply, eq_comm]
  have hndZ : BZ.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hsZ.isRefl).mpr
      (LinearMap.separatingLeft_iff_linear_nontrivial.mpr b.toDual_inj)
  let e := Submodule.prodEquivOfIsCompl M Z hMZ
  have hsP := LinearMap.BilinForm.isSymm_prod_iff.mpr ⟨hsBM, hsZ⟩
  refine ⟨LinearMap.BilinForm.congr e ((S.complementForm d hC).prod BZ), fun i => ?_,
    ⟨fun x y => by rw [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.congr_apply,
      hsP.eq]⟩,
    (LinearMap.BilinForm.nondegenerate_prod_iff.mpr
      ⟨hBM.nondegenerate hsBM hmin, hndZ⟩).congr e⟩
  have he : e.symm (R.coroot i) = (S.coroot i, 0) := by
    rw [← R.coe_restrict_coroot M hc hsM i]
    exact Submodule.prodEquivOfIsCompl_symm_apply_left M Z hMZ _
  ext y
  have hy : R.root i (e.symm y).2 = 0 := (R.mem_cartanCenter_iff _).mp (hZ (e.symm y).2.2) i
  have hdec : ((e.symm y).1 : H) + (e.symm y).2 = y := by
    rw [← Submodule.coe_prodEquivOfIsCompl' M Z hMZ, LinearEquiv.apply_symm_apply]
  rw [map_smul, LinearMap.smul_apply, LinearMap.BilinForm.congr_apply, he,
    LinearMap.BilinForm.prod_apply, map_zero, LinearMap.zero_apply, add_zero,
    ← LinearMap.smul_apply, ← map_smul, hBM i, restrict_root_apply]
  calc R.root i (e.symm y).1 = R.root i (((e.symm y).1 : H) + (e.symm y).2) := by
        rw [map_add, hy, add_zero]
    _ = R.root i y := by rw [hdec]

end Existence

end TauCeti.CartanRealization
