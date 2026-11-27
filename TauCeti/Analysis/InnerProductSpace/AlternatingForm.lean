/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Alternating forms on a real inner product space

The fibres of the bundle of differential `k`-forms are the continuous alternating maps
`V [⋀^Fin k]→L[ℝ] ℝ` on a tangent space `V`. On a finite-dimensional real inner product space
they are identified with the exterior power `⋀ᵏ V`: an element `x` gives the form
`v ↦ ⟪x, v₁ ∧ ⋯ ∧ vₖ⟫`. This is `TauCeti.alternatingFormEquiv`. On a wedge of vectors it is the
wedge of the covectors `⟪uⱼ, ·⟫` in the determinant normalization,
`(u₁ ∧ ⋯ ∧ uₖ)(v₁, …, vₖ) = det ⟪uⱼ, vᵢ⟫`.

The identification carries the exterior product to the wedge product of forms,
`ContinuousAlternatingMap.wedge`, normalized by `1 / (k! l!)` as in Lee's *Introduction to Smooth
Manifolds*. It carries the contraction by `⟪u, ·⟫` to the interior product
`ContinuousAlternatingMap.curryLeft` by `u`. Transporting the inner product of `⋀ᵏ V`, given on
wedges by Gram determinants, defines the pointwise inner product of `k`-forms,
`TauCeti.alternatingFormInner`. For an orthonormal basis `(eᵢ)` it is
`⟨α, β⟩ = ∑_{i₁ < ⋯ < iₖ} α(e_{i₁}, …, e_{iₖ}) β(e_{i₁}, …, e_{iₖ})`, so the increasing wedges of
the dual coframe are orthonormal. For an arbitrary basis `b`, with dual basis `b*` for the inner
product, a form is represented by `∑ α(b_{i₁}, …, b_{iₖ}) b*_{i₁} ∧ ⋯ ∧ b*_{iₖ}`
(`Module.Basis.alternatingFormEquiv_symm_eq_sum`).

## Main definitions

* `TauCeti.alternatingFormEquiv`: the linear equivalence `⋀ᵏ V ≃ₗ[ℝ] V [⋀^Fin k]→L[ℝ] ℝ`.
* `TauCeti.alternatingFormInner`: the Gram inner product of alternating `k`-forms.
* `TauCeti.wedgeCovector`: exterior multiplication `α ↦ ⟪u, ·⟫ ∧ α` of forms by a covector.
* `TauCeti.wedgeCovectorₗ`: the same exterior multiplication as a linear map of the covector
  `u ↦ ε_u`.

## Main results

* `TauCeti.alternatingFormEquiv_wedge`: the identification carries `x ∧ y` to the wedge of forms.
* `TauCeti.alternatingFormEquiv_koszulDifferential`: it carries the contraction by `⟪u, ·⟫` to
  the interior product by `u`.
* `TauCeti.alternatingFormEquiv_wedgeLeft_apply`: it carries exterior multiplication by `u` to
  the wedge with the covector `⟪u, ·⟫`.
* `TauCeti.curryLeftFlipL_wedgeCovector_add`: the anticommutation relation
  `ι_u (⟪w, ·⟫ ∧ α) + ⟪w, ·⟫ ∧ ι_u α = ⟪u, w⟫ α` of the interior product and exterior
  multiplication, with its degree-zero and top-degree forms
  `TauCeti.curryLeftFlipL_wedgeCovector_zero` and
  `TauCeti.wedgeCovector_curryLeftFlipL_of_eq_finrank`.
* `TauCeti.alternatingFormEquiv_symm_alternatizeUncurryFin`: the alternation of a linear map to
  `k`-forms is `∑ᵢ eⁱ ∧ f(eᵢ)` in an orthonormal frame.
* `TauCeti.alternatingFormEquiv_ιMulti_twoVectorContraction`: on two-forms, the interior product
  by `u` is the covector of the contraction `u ⌟ x`.
* `LinearIsometry.alternatingFormEquiv_map`: musical identification commutes with isometries.
* `ContinuousAlternatingMap.abs_alternatingFormInner_le_sqrt_mul_sqrt`: the Cauchy–Schwarz
  inequality `|⟨α, β⟩| ≤ √⟨α, α⟩ √⟨β, β⟩` for the inner product of forms.
* `TauCeti.alternatingFormInner_eq_sum`: the inner product of forms in an orthonormal basis.
* `Module.Basis.alternatingFormEquiv_symm_eq_sum`: the element of `⋀ᵏ V` representing a form, in
  an arbitrary basis.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti

variable (V) in
/-- The identification of the exterior power `⋀ᵏ V` of a finite-dimensional real inner product
space with the continuous alternating `k`-forms on `V`: `x` is sent to the form
`v ↦ ⟪x, v₁ ∧ ⋯ ∧ vₖ⟫`. -/
def alternatingFormEquiv (k : ℕ) : ⋀[ℝ]^k V ≃ₗ[ℝ] V [⋀^Fin k]→L[ℝ] ℝ :=
  (LinearEquiv.ofBijective (innerₗ (⋀[ℝ]^k V)) bijective_innerₗ).trans
    (alternatingMapLinearEquiv.symm.trans AlternatingMap.toContinuousAlternatingMap)

/-- The form of `x ∈ ⋀ᵏ V` evaluates on `(v₁, …, vₖ)` as `⟪x, v₁ ∧ ⋯ ∧ vₖ⟫`. -/
@[simp]
theorem alternatingFormEquiv_apply {k : ℕ} (x : ⋀[ℝ]^k V) (v : Fin k → V) :
    alternatingFormEquiv V k x v = ⟪x, ιMulti ℝ k v⟫ := by
  simp [alternatingFormEquiv]

/-- The element of `⋀ᵏ V` representing a form `α` pairs with `v₁ ∧ ⋯ ∧ vₖ` to `α v`. -/
@[simp]
theorem inner_alternatingFormEquiv_symm_ιMulti {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ)
    (v : Fin k → V) : ⟪(alternatingFormEquiv V k).symm α, ιMulti ℝ k v⟫ = α v := by
  rw [← alternatingFormEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The form of a wedge of vectors `u₁ ∧ ⋯ ∧ uₖ` is the wedge of the covectors `⟪uⱼ, ·⟫` in the
determinant normalization: its value on `(v₁, …, vₖ)` is `det ⟪uⱼ, vᵢ⟫`. -/
theorem alternatingFormEquiv_ιMulti_apply {k : ℕ} (u v : Fin k → V) :
    alternatingFormEquiv V k (ιMulti ℝ k u) v = (Matrix.of fun i j ↦ ⟪u j, v i⟫).det := by
  rw [alternatingFormEquiv_apply, inner_ιMulti_ιMulti]

/-- The form of a wedge of vectors `u₁ ∧ ⋯ ∧ uₖ` vanishes on every frame `v` having a vector `vᵢ`
orthogonal to every `uⱼ`. -/
theorem alternatingFormEquiv_ιMulti_apply_eq_zero_of_forall_inner_eq_zero {k : ℕ} (u v : Fin k → V)
    {i : Fin k} (h : ∀ j, ⟪u j, v i⟫ = 0) : alternatingFormEquiv V k (ιMulti ℝ k u) v = 0 := by
  rw [alternatingFormEquiv_ιMulti_apply]
  exact Matrix.det_eq_zero_of_row_eq_zero i fun j ↦ by simp [h]

/-- The form of a wedge of vectors is the alternatization of the product of the covectors
`⟪uⱼ, ·⟫`. -/
private theorem alternatingFormEquiv_ιMulti_toAlternatingMap {k : ℕ} (u : Fin k → V) :
    (alternatingFormEquiv V k (ιMulti ℝ k u)).toAlternatingMap =
      ((MultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compLinearMap
        fun i ↦ innerₗ V (u i)).alternatization := by
  ext v
  simp [inner_ιMulti_ιMulti, Matrix.det_apply, MultilinearMap.alternatization_apply]

/-- The wedge-product formula on wedges of vectors: both sides are alternatizations of products
of covectors, by `ContinuousAlternatingMap.pairedWedge_toAlternatingMap_of_eq_alternatization`. -/
private theorem alternatingFormEquiv_ιMulti_append {k l : ℕ} (u : Fin k → V) (w : Fin l → V) :
    alternatingFormEquiv V (k + l) (ιMulti ℝ (k + l) (Fin.append u w)) =
      (alternatingFormEquiv V k (ιMulti ℝ k u)).wedge
        (alternatingFormEquiv V l (ιMulti ℝ l w)) := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousAlternatingMap.wedge_def,
    ContinuousAlternatingMap.pairedWedge_toAlternatingMap_of_eq_alternatization _ _
      (alternatingFormEquiv_ιMulti_toAlternatingMap u)
      (alternatingFormEquiv_ιMulti_toAlternatingMap w),
    alternatingFormEquiv_ιMulti_toAlternatingMap]
  -- The product of the covectors of `u` and of `w`, read on `Fin (k + l)`, is the product of the
  -- covectors of the concatenation.
  congr 1
  ext v
  simp [Fin.prod_univ_add]

/-- **The exterior product is the wedge product of forms**: the form of `x ∧ y` is the wedge of
the forms of `x ∈ ⋀ᵏ V` and `y ∈ ⋀ˡ V`, with the normalization of
`ContinuousAlternatingMap.wedge`. -/
theorem alternatingFormEquiv_wedge {k l : ℕ} (x : ⋀[ℝ]^k V) (y : ⋀[ℝ]^l V) :
    alternatingFormEquiv V (k + l) (exteriorPower.wedge ℝ V k l x y) =
      (alternatingFormEquiv V k x).wedge (alternatingFormEquiv V l y) := by
  -- Both sides are bilinear in `(x, y)`, so it suffices to compare them on wedges of vectors.
  let B : ⋀[ℝ]^k V →ₗ[ℝ] ⋀[ℝ]^l V →ₗ[ℝ] V [⋀^Fin (k + l)]→L[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y ↦ (alternatingFormEquiv V k x).wedge (alternatingFormEquiv V l y))
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
  have key :
      (exteriorPower.wedge ℝ V k l).compr₂ (alternatingFormEquiv V (k + l)).toLinearMap = B := by
    refine exteriorPower.linearMap_ext (R := ℝ) (M := V) (n := k)
      (AlternatingMap.ext fun u ↦ exteriorPower.linearMap_ext (R := ℝ) (M := V) (n := l)
        (AlternatingMap.ext fun w ↦ ?_))
    simp [B, alternatingFormEquiv_ιMulti_append]
  exact LinearMap.congr_fun₂ key x y

/-- **Contraction is the interior product**: the form of the contraction `ι_u x` of
`x ∈ ⋀ᵏ⁺¹ V` by `⟪u, ·⟫` is the interior product of the form of `x` by `u`. -/
theorem alternatingFormEquiv_koszulDifferential (u : V) {k : ℕ} (x : ⋀[ℝ]^(k + 1) V) :
    alternatingFormEquiv V k (koszulDifferential (innerₗ V u) k x) =
      (alternatingFormEquiv V (k + 1) x).curryLeft u := by
  ext v
  rw [alternatingFormEquiv_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    alternatingFormEquiv_apply, real_inner_comm, ← inner_wedgeLeft_eq_inner_koszulDifferential,
    real_inner_comm, ExteriorAlgebra.wedgeLeft_ιMulti]
  -- `Matrix.vecCons`, used by `curryLeft`, is by definition `Fin.cons`.
  rfl

/-- Elements of exterior powers of propositionally equal degrees which agree in the exterior
algebra have forms which agree after reindexing their arguments. -/
private theorem alternatingFormEquiv_apply_comp_cast {a b : ℕ} (h : a = b) (x : ⋀[ℝ]^a V)
    (y : ⋀[ℝ]^b V) (hxy : (x : ExteriorAlgebra ℝ V) = y) (v : Fin b → V) :
    alternatingFormEquiv V a x (v ∘ Fin.cast h) = alternatingFormEquiv V b y v := by
  subst h
  obtain rfl : x = y := Subtype.ext hxy
  simp

/-- **Exterior multiplication is the wedge with a covector**: the form of `u ∧ x` for
`x ∈ ⋀ᵏ V` is the wedge `⟪u, ·⟫ ∧ α` of the covector of `u` with the form `α` of `x`, whose degree
`1 + k` is identified with `k + 1` by `Fin.cast`. -/
theorem alternatingFormEquiv_wedgeLeft_apply (u : V) {k : ℕ} (x : ⋀[ℝ]^k V)
    (v : Fin (k + 1) → V) :
    alternatingFormEquiv V (k + 1) (ExteriorAlgebra.wedgeLeft u k x) v =
      (ContinuousAlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ u)).wedge
        (alternatingFormEquiv V k x) (v ∘ Fin.cast (Nat.add_comm 1 k)) := by
  have hu : ContinuousAlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ u) =
      alternatingFormEquiv V 1 (ιMulti ℝ 1 ![u]) := by
    ext v
    simp [inner_ιMulti_ιMulti]
  rw [hu, ← alternatingFormEquiv_wedge, alternatingFormEquiv_apply_comp_cast]
  simp [ExteriorAlgebra.ιMulti_apply]

/-- **The interior product of a two-form**: the interior product by `u` of the form of
`x ∈ ⋀² V` is the covector of the contraction `u ⌟ x`. -/
theorem alternatingFormEquiv_ιMulti_twoVectorContraction (x : ⋀[ℝ]^2 V) (u : V) :
    alternatingFormEquiv V 1 (ιMulti ℝ 1 ![twoVectorContraction x u]) =
      (alternatingFormEquiv V 2 x).curryLeft u := by
  ext v
  have hv : Matrix.vecCons u v = ![u, v 0] := funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  simp [inner_ιMulti_ιMulti, hv]

/-- The form of `u ∧ w` is the wedge `⟪u, ·⟫ ∧ ⟪w, ·⟫` of the covectors of `u` and `w`. -/
theorem alternatingFormEquiv_ιMulti_pair (u w : V) :
    alternatingFormEquiv V 2 (ιMulti ℝ 2 ![u, w]) =
      (ContinuousAlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ u)).wedge
        (alternatingFormEquiv V 1 (ιMulti ℝ 1 ![w])) := by
  ext v
  have h := alternatingFormEquiv_wedgeLeft_apply u (ιMulti ℝ 1 ![w]) v
  rw [ExteriorAlgebra.wedgeLeft_ιMulti] at h
  simpa using h

/-! ### Exterior multiplication and the interior product on forms -/

section WedgeCovector

open ContinuousAlternatingMap (curryLeftFlipL curryLeftFlipL_apply_apply)

/-- **Exterior multiplication by a covector**: the map `α ↦ ⟪u, ·⟫ ∧ α` from `k`-forms to
`(k + 1)`-forms, read through the identification of forms with the exterior powers as exterior
multiplication by `u` (`TauCeti.alternatingFormEquiv_wedgeLeft_apply`). -/
def wedgeCovector (u : V) (k : ℕ) :
    (V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((alternatingFormEquiv V (k + 1)).toLinearMap ∘ₗ
    ExteriorAlgebra.wedgeLeft u k ∘ₗ (alternatingFormEquiv V k).symm.toLinearMap)

/-- Unfolding `TauCeti.wedgeCovector` through the identification of forms with the exterior
powers. -/
theorem wedgeCovector_apply (u : V) (k : ℕ) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeCovector u k α = alternatingFormEquiv V (k + 1)
      (ExteriorAlgebra.wedgeLeft u k ((alternatingFormEquiv V k).symm α)) :=
  (rfl)

/-- Exterior multiplication by `⟪u, ·⟫` on the form of `x` is the form of `u ∧ x`. -/
@[simp]
theorem wedgeCovector_alternatingFormEquiv (u : V) (k : ℕ) (x : ⋀[ℝ]^k V) :
    wedgeCovector u k (alternatingFormEquiv V k x) =
      alternatingFormEquiv V (k + 1) (ExteriorAlgebra.wedgeLeft u k x) := by
  rw [wedgeCovector_apply, LinearEquiv.symm_apply_apply]

/-- **Exterior multiplication as a linear map of the covector**: the map `u ↦ ε_u`, where
`ε_u = TauCeti.wedgeCovector u k` is exterior multiplication by `⟪u, ·⟫` on `k`-forms. -/
def wedgeCovectorₗ (k : ℕ) :
    V →ₗ[ℝ] (V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    ((alternatingFormEquiv V k).arrowCongr (alternatingFormEquiv V (k + 1))).toLinearMap ∘ₗ
      ExteriorAlgebra.wedgeLeftₗ ℝ V k

@[simp]
theorem wedgeCovectorₗ_apply (k : ℕ) (u : V) : wedgeCovectorₗ k u = wedgeCovector u k := by
  ext α : 1
  simp only [wedgeCovectorₗ, LinearMap.comp_apply, ExteriorAlgebra.wedgeLeftₗ_apply,
    LinearEquiv.coe_coe, LinearMap.coe_toContinuousLinearMap', LinearEquiv.arrowCongr_apply,
    wedgeCovector_apply]

/-- Exterior multiplication by a covector is additive in the covector:
`ε_{u + w} = ε_u + ε_w`. -/
@[simp]
theorem wedgeCovector_add (u w : V) (k : ℕ) :
    wedgeCovector (u + w) k = wedgeCovector u k + wedgeCovector w k := by
  simpa only [wedgeCovectorₗ_apply] using (wedgeCovectorₗ k).map_add u w

/-- Exterior multiplication by a covector is homogeneous in the covector: `ε_{c u} = c ε_u`. -/
@[simp]
theorem wedgeCovector_smul (c : ℝ) (u : V) (k : ℕ) :
    wedgeCovector (c • u) k = c • wedgeCovector u k := by
  simpa only [wedgeCovectorₗ_apply] using (wedgeCovectorₗ k).map_smul c u

/-- Exterior multiplication by the zero covector vanishes: `ε_0 = 0`. -/
@[simp]
theorem wedgeCovector_zero (k : ℕ) : wedgeCovector (0 : V) k = 0 := by
  simpa only [wedgeCovectorₗ_apply] using (wedgeCovectorₗ (V := V) k).map_zero

/-- Exterior multiplication by a covector is odd in the covector: `ε_{-u} = -ε_u`. -/
@[simp]
theorem wedgeCovector_neg (u : V) (k : ℕ) : wedgeCovector (-u) k = -wedgeCovector u k := by
  simpa only [wedgeCovectorₗ_apply] using map_neg (wedgeCovectorₗ k) u

/-- Exterior multiplication by a covector is subtractive in the covector:
`ε_{u - w} = ε_u - ε_w`. -/
@[simp]
theorem wedgeCovector_sub (u w : V) (k : ℕ) :
    wedgeCovector (u - w) k = wedgeCovector u k - wedgeCovector w k := by
  simpa only [wedgeCovectorₗ_apply] using map_sub (wedgeCovectorₗ k) u w

/-- **Exterior multiplication by a covector in an orthonormal frame**:
`ε_u = ∑ᵢ ⟪eᵢ, u⟫ ε_{eᵢ}`. -/
theorem wedgeCovector_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (u : V)
    (k : ℕ) : wedgeCovector u k = ∑ i, ⟪b i, u⟫ • wedgeCovector (b i) k := by
  simpa only [map_sum, map_smul, wedgeCovectorₗ_apply] using
    congrArg (wedgeCovectorₗ k) (b.sum_repr' u).symm

/-- The interior product by `u` of the form of `x` is the form of the contraction of `x` by
`⟪u, ·⟫`. -/
theorem curryLeftFlipL_alternatingFormEquiv (u : V) (k : ℕ) (x : ⋀[ℝ]^(k + 1) V) :
    curryLeftFlipL (n := k) u (alternatingFormEquiv V (k + 1) x) =
      alternatingFormEquiv V k (koszulDifferential (innerₗ V u) k x) := by
  rw [curryLeftFlipL_apply_apply, alternatingFormEquiv_koszulDifferential]

/-- **The anticommutation relation** `ι_u (⟪w, ·⟫ ∧ α) + ⟪w, ·⟫ ∧ ι_u α = ⟪u, w⟫ α` of the
interior product and exterior multiplication on forms of positive degree. -/
theorem curryLeftFlipL_wedgeCovector_add (u w : V) (k : ℕ) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    curryLeftFlipL (n := k + 1) u (wedgeCovector w (k + 1) α) +
      wedgeCovector w k (curryLeftFlipL (n := k) u α) = ⟪u, w⟫ • α := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V (k + 1)).surjective α
  have h := LinearMap.congr_fun (wedgeLeft_comp_koszulDifferential_add (innerₗ V u) w k) a
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    innerₗ_apply_apply] at h
  rw [wedgeCovector_alternatingFormEquiv, curryLeftFlipL_alternatingFormEquiv,
    curryLeftFlipL_alternatingFormEquiv, wedgeCovector_alternatingFormEquiv, ← map_add, ← map_smul]
  exact congrArg _ ((add_comm _ _).trans h)

/-- **The anticommutation relation on functions**: `ι_u (⟪w, ·⟫ ∧ α) = ⟪u, w⟫ α` for `0`-forms. -/
theorem curryLeftFlipL_wedgeCovector_zero (u w : V) (α : V [⋀^Fin 0]→L[ℝ] ℝ) :
    curryLeftFlipL (n := 0) u (wedgeCovector w 0 α) = ⟪u, w⟫ • α := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V 0).surjective α
  have h := LinearMap.congr_fun (koszulDifferential_comp_wedgeLeft_zero (innerₗ V u) w) a
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    innerₗ_apply_apply] at h
  rw [wedgeCovector_alternatingFormEquiv, curryLeftFlipL_alternatingFormEquiv, h, map_smul]

/-- **The anticommutation relation in the top degree**: `⟪w, ·⟫ ∧ ι_u α = ⟪u, w⟫ α` for forms of
degree `k + 1 = dim V`, since there are no nonzero forms of degree above the dimension. -/
theorem wedgeCovector_curryLeftFlipL_of_eq_finrank (u w : V) {k : ℕ}
    (hk : k + 1 = finrank ℝ V) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    wedgeCovector w k (curryLeftFlipL (n := k) u α) = ⟪u, w⟫ • α := by
  rw [← curryLeftFlipL_wedgeCovector_add,
    (wedgeCovector w (k + 1) α).eq_zero_of_finrank_lt (by rw [Fintype.card_fin]; omega),
    map_zero, zero_add]

/-- **Alternation in an orthonormal frame**: the alternation `f ↦ ∑ⱼ (-1)ʲ f(vⱼ)(v̂ⱼ)` of a
linear map `f` from `V` to `k`-forms is `∑ᵢ eⁱ ∧ f(eᵢ)`, read on the elements of the exterior
powers representing the forms. -/
theorem alternatingFormEquiv_symm_alternatizeUncurryFin {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {k : ℕ} (f : V →L[ℝ] V [⋀^Fin k]→L[ℝ] ℝ) :
    (alternatingFormEquiv V (k + 1)).symm (ContinuousAlternatingMap.alternatizeUncurryFin f) =
      ∑ i, ExteriorAlgebra.wedgeLeft (b i) k ((alternatingFormEquiv V k).symm (f (b i))) := by
  rw [LinearEquiv.symm_apply_eq]
  ext v
  -- Each summand pairs `eᵢ ∧ aᵢ` with `v₀ ∧ ⋯ ∧ vₖ`, which contracts `⟪eᵢ, ·⟫` into one `vⱼ`.
  have h (i : ι) : alternatingFormEquiv V (k + 1)
      (ExteriorAlgebra.wedgeLeft (b i) k ((alternatingFormEquiv V k).symm (f (b i)))) v =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * (⟪b i, v j⟫ * f (b i) (j.removeNth v)) := by
    rw [alternatingFormEquiv_apply, inner_wedgeLeft_eq_inner_koszulDifferential,
      koszulDifferential_ιMulti, inner_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_right, ← alternatingFormEquiv_apply, LinearEquiv.apply_symm_apply,
      innerₗ_apply_apply]
    ring
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, map_sum,
    ContinuousAlternatingMap.sum_apply, Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- Summing over the frame reassembles `vⱼ = ∑ᵢ ⟪eᵢ, vⱼ⟫ eᵢ`.
  conv_lhs => rw [← b.sum_repr' (v j)]
  simp only [map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Finset.mul_sum]

/-- **Exterior multiplication as an alternation**: the alternation of `v ↦ ⟪u, v⟫ α` is the
exterior product `⟪u, ·⟫ ∧ α = ε_u α`. -/
theorem alternatizeUncurryFin_innerSL_smulRight (u : V) {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ u).smulRight α) =
      wedgeCovector u k α := by
  set b := stdOrthonormalBasis ℝ V
  apply (alternatingFormEquiv V (k + 1)).symm.injective
  rw [alternatingFormEquiv_symm_alternatizeUncurryFin b, wedgeCovector_eq_sum b,
    sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_comm,
    smul_apply, map_smul, map_smul, map_smul, wedgeCovector_apply,
    LinearEquiv.symm_apply_apply]

end WedgeCovector

variable (V) in
/-- The pointwise inner product of alternating `k`-forms, transported from the inner product of
`⋀ᵏ V` along `TauCeti.alternatingFormEquiv`. On wedges of covectors it is the Gram determinant,
and in an orthonormal basis it is computed by `TauCeti.alternatingFormInner_eq_sum`. -/
def alternatingFormInner (k : ℕ) : LinearMap.BilinForm ℝ (V [⋀^Fin k]→L[ℝ] ℝ) :=
  (innerₗ (⋀[ℝ]^k V)).compl₁₂ (alternatingFormEquiv V k).symm.toLinearMap
    (alternatingFormEquiv V k).symm.toLinearMap

/-- The inner product of two forms is the inner product of the elements of `⋀ᵏ V` representing
them. -/
theorem alternatingFormInner_apply {k : ℕ} (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner V k α β =
      ⟪(alternatingFormEquiv V k).symm α, (alternatingFormEquiv V k).symm β⟫ := by
  simp [alternatingFormInner]

/-- The identification `⋀ᵏ V ≃ₗ[ℝ] V [⋀^Fin k]→L[ℝ] ℝ` is an isometry for the inner product of
forms. -/
@[simp]
theorem alternatingFormInner_alternatingFormEquiv {k : ℕ} (x y : ⋀[ℝ]^k V) :
    alternatingFormInner V k (alternatingFormEquiv V k x) (alternatingFormEquiv V k y) =
      ⟪x, y⟫ := by
  simp [alternatingFormInner_apply]

/-- The inner product of forms is symmetric. -/
theorem alternatingFormInner_comm {k : ℕ} (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner V k α β = alternatingFormInner V k β α := by
  rw [alternatingFormInner_apply, alternatingFormInner_apply, real_inner_comm]

/-- The inner product of forms is positive semidefinite. -/
theorem alternatingFormInner_self_nonneg {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    0 ≤ alternatingFormInner V k α α := by
  rw [alternatingFormInner_apply]
  exact real_inner_self_nonneg

/-- The inner product of forms is definite. -/
@[simp]
theorem alternatingFormInner_self_eq_zero {k : ℕ} {α : V [⋀^Fin k]→L[ℝ] ℝ} :
    alternatingFormInner V k α α = 0 ↔ α = 0 := by
  rw [alternatingFormInner_apply, inner_self_eq_zero, LinearEquiv.map_eq_zero_iff]

/-- The Hilbert norm `√⟨α, α⟩` of a form is the norm of the element of `⋀ᵏ V` representing it. -/
theorem _root_.ContinuousAlternatingMap.sqrt_alternatingFormInner_self {k : ℕ}
    (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    √(alternatingFormInner V k α α) = ‖(alternatingFormEquiv V k).symm α‖ := by
  rw [alternatingFormInner_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **Cauchy–Schwarz for forms**: `|⟨α, β⟩| ≤ √⟨α, α⟩ √⟨β, β⟩`. -/
theorem _root_.ContinuousAlternatingMap.abs_alternatingFormInner_le_sqrt_mul_sqrt {k : ℕ}
    (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    |alternatingFormInner V k α β| ≤
      √(alternatingFormInner V k α α) * √(alternatingFormInner V k β β) := by
  rw [alternatingFormInner_apply, ContinuousAlternatingMap.sqrt_alternatingFormInner_self,
    ContinuousAlternatingMap.sqrt_alternatingFormInner_self]
  exact abs_real_inner_le_norm _ _

/-- **The inner product of forms in an orthonormal basis**: if `(eᵢ)` is an orthonormal basis of
`V` indexed by a linear order, then `⟨α, β⟩ = ∑ α(e_{i₁}, …, e_{iₖ}) β(e_{i₁}, …, e_{iₖ})`, the sum
running over the increasing `k`-tuples `i₁ < ⋯ < iₖ`. Equivalently, the increasing wedges of the
dual coframe are orthonormal. -/
theorem alternatingFormInner_eq_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ V) {k : ℕ} (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner V k α β =
      ∑ s : powersetCard ι k, α (b ∘ powersetCard.ofFinEmbEquiv.symm s) *
        β (b ∘ powersetCard.ofFinEmbEquiv.symm s) := by
  rw [alternatingFormInner_apply, ← (b.exteriorPower k).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hs : b.exteriorPower k s = ιMulti ℝ k (b ∘ powersetCard.ofFinEmbEquiv.symm s) := by
    rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.toBasis_exteriorPower, basis_apply,
      ιMulti_family, OrthonormalBasis.coe_toBasis]
  rw [hs, real_inner_comm ((alternatingFormEquiv V k).symm β),
    inner_alternatingFormEquiv_symm_ιMulti, inner_alternatingFormEquiv_symm_ιMulti]

/-- **The inner product of `0`-forms** is the product of their values: a `0`-form is a constant,
evaluated on the empty tuple `v`. -/
theorem alternatingFormInner_zero_apply (α β : V [⋀^Fin 0]→L[ℝ] ℝ) (v : Fin 0 → V) :
    alternatingFormInner V 0 α β = α v * β v := by
  rw [alternatingFormInner_eq_sum (stdOrthonormalBasis ℝ V)]
  simp only [Subsingleton.elim _ v, Finset.sum_const, Finset.card_univ]
  simp

end TauCeti

namespace LinearIsometry

open TauCeti

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The musical identification of exterior powers with alternating forms commutes with
linear isometric embeddings: pulling back the form of the image recovers the original form. -/
@[simp]
theorem alternatingFormEquiv_map (e : V →ₗᵢ[ℝ] W) {k : ℕ} (a : ⋀[ℝ]^k V) :
    (alternatingFormEquiv W k (exteriorPower.map k e.toLinearMap a)).compContinuousLinearMap
        e.toContinuousLinearMap =
      alternatingFormEquiv V k a := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, alternatingFormEquiv_apply]
  simpa [exteriorPower.map_apply_ιMulti] using
    exteriorPower.inner_map_map e a (ιMulti ℝ k v)

end LinearIsometry

namespace Module.Basis

open TauCeti

variable {ι : Type*} [LinearOrder ι]

/-- The wedges of the dual basis `b*` and the coordinates of `⋀ᵏ V` in the basis induced by `b`:
`⟪b*_{i₁} ∧ ⋯ ∧ b*_{iₖ}, w₁ ∧ ⋯ ∧ wₖ⟫` is the coordinate of `w₁ ∧ ⋯ ∧ wₖ` at
`{i₁ < ⋯ < iₖ}`. -/
theorem inner_ιMulti_dualBasis [Finite ι] (b : Basis ι ℝ V) {k : ℕ} (s : powersetCard ι k)
    (w : Fin k → V) :
    ⟪ιMulti ℝ k (LinearMap.BilinForm.dualBasis (innerₗ V) nondegenerate_inner b ∘
        powersetCard.ofFinEmbEquiv.symm s), ιMulti ℝ k w⟫ =
      (b.exteriorPower k).repr (ιMulti ℝ k w) s := by
  have := Fintype.ofFinite ι
  rw [inner_ιMulti_ιMulti, basis_repr_apply, ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  simp [inner_dualBasis_left]

/-- **A form in an arbitrary basis**: the element of `⋀ᵏ V` representing a form `α` is
`∑ α(b_{i₁}, …, b_{iₖ}) b*_{i₁} ∧ ⋯ ∧ b*_{iₖ}`, the sum running over the increasing `k`-tuples
`i₁ < ⋯ < iₖ`, where `b*` is the dual basis of `b` for the inner product. -/
theorem alternatingFormEquiv_symm_eq_sum [Fintype ι] (b : Basis ι ℝ V) {k : ℕ}
    (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    (alternatingFormEquiv V k).symm α = ∑ s : powersetCard ι k,
      α (b ∘ powersetCard.ofFinEmbEquiv.symm s) •
        ιMulti ℝ k (LinearMap.BilinForm.dualBasis (innerₗ V) nondegenerate_inner b ∘
          powersetCard.ofFinEmbEquiv.symm s) := by
  classical
  -- Both sides have the same inner product with each basis vector `b_{t₁} ∧ ⋯ ∧ b_{tₖ}`.
  refine InnerProductSpace.ext_inner_left_basis (b.exteriorPower k) fun t ↦ ?_
  have ht : b.exteriorPower k t = ιMulti ℝ k (b ∘ powersetCard.ofFinEmbEquiv.symm t) := by
    rw [basis_apply, ιMulti_family]
  simp only [inner_sum, real_inner_smul_right]
  simp_rw [real_inner_comm _ (b.exteriorPower k t)]
  conv_rhs => enter [2, s]; rw [ht, inner_ιMulti_dualBasis, ← ht, Basis.repr_self,
    Finsupp.single_apply]
  rw [ht, inner_alternatingFormEquiv_symm_ιMulti]
  simp

end Module.Basis
