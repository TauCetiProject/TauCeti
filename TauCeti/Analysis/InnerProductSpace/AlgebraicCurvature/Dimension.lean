/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Symmetric
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
import TauCeti.LinearAlgebra.Multilinear.SectionalPolarization

/-!
# Polarization and dimension of algebraic curvature tensors

Every four-tensor `r : FourTensor V` on a real normed space curries to a four-fold linear map
`toLinearMap₄ r : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ`; in finite dimension this currying is a linear
equivalence (`toLinearMap₄Equiv`) inverse to `ofLinearMap₄`. Through `toLinearMap₄`, sectional
polarization (`LinearMap.eq_of_cyclic_eq_zero`) transfers to `FourTensor V`: an algebraic curvature
tensor is uniquely determined by its sectional values `r(u, v, u, v)` on linearly independent pairs
`u, v`. In particular, on a space of dimension at most `1`, every algebraic curvature tensor
vanishes.

On a finite-dimensional real normed space `V` of dimension `n`, the algebraic curvature tensors fit
into the split exact sequence

`0 → algebraicCurvatureSubmodule V → pairSymmetricSubmodule V → V [⋀^Fin 4]→ₗ[ℝ] ℝ → 0`

(`Besse, Section 1.G`), where `pairSymmetricSubmodule V` consists of the four-tensors antisymmetric
in each pair and symmetric under swapping the two pairs, and the right-hand map is the Bianchi
alternator `(u, v, z, w) ↦ r(u, v, z, w) + r(v, z, u, w) + r(z, u, v, w)` with section
`ω ↦ (1/3) ω`. Descending to the exterior square identifies `pairSymmetricSubmodule V` with the
symmetric bilinear forms on `⋀[ℝ]^2 V`, of dimension `binom(n, 2) * (binom(n, 2) + 1) / 2`, while
four-forms have dimension `binom(n, 4)`. Subtracting gives

`Module.finrank ℝ (algebraicCurvatureSubmodule V) = n ^ 2 * (n ^ 2 - 1) / 12`

without requiring an inner product on `V`. For `n = 2, 3, 4` this dimension is `1, 6, 20`. When `V`
carries an inner product and `n = 2`, the nonzero constant-curvature tensor spans this
one-dimensional space, so every algebraic curvature tensor equals `(Scal / 2) • constantCurvature V`
and has Ricci tensor `(Scal / 2) g`.

## Main definitions

* `TauCeti.FourTensor.toLinearMap₄` and `TauCeti.FourTensor.toLinearMap₄Equiv`: currying a
  four-tensor into a four-fold linear map, and the finite-dimensional linear equivalence with
  inverse `ofLinearMap₄`.
* `TauCeti.FourTensor.IsPairSymmetric` and `TauCeti.FourTensor.pairSymmetricSubmodule`: four-tensors
  antisymmetric in each pair and symmetric under pair interchange.
* `TauCeti.FourTensor.pairSymmetricEquivSymmBilin`: linear equivalence between pair-symmetric
  four-tensors on `V` and symmetric bilinear forms on `⋀[ℝ]^2 V`.
* `TauCeti.FourTensor.bianchiAlternatingMap`: the Bianchi cyclic sum from pair-symmetric
  four-tensors onto alternating four-forms.

## Main results

* `TauCeti.FourTensor.IsAlgebraicCurvature.eq_of_apply_self_eq` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.eq_of_apply_self_eq_of_linearIndependent`: sectional
  polarization for algebraic curvature tensors.
* `TauCeti.FourTensor.IsAlgebraicCurvature.eq_zero_of_finrank_le_one`: every algebraic curvature
  tensor vanishes in dimension at most `1`.
* `TauCeti.FourTensor.finrank_algebraicCurvatureSubmodule`:
  `Module.finrank ℝ (algebraicCurvatureSubmodule V) = n ^ 2 * (n ^ 2 - 1) / 12`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.eq_smul_constantCurvature_of_finrank_eq_two`: in
  dimension `2`, `r = (scalar r / 2) • constantCurvature V`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7 and 8.
-/

public section

open LinearMap (BilinForm)
open scoped InnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Curry a continuous four-tensor into a four-fold linear map. -/
def toLinearMap₄ : FourTensor V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun r :=
    LinearMap.mk₂ ℝ
      (fun u v ↦ LinearMap.mk₂ ℝ
        (fun z w ↦ r ![u, v, z, w])
        (fun _ _ _ ↦ apply_add_third ..)
        (fun t _ _ ↦ by simpa only [smul_eq_mul] using apply_smul_third r u v _ _ t)
        (fun _ _ _ ↦ apply_add_fourth ..)
        (fun t _ _ ↦ by simpa only [smul_eq_mul] using apply_smul_fourth r u v _ _ t))
      (fun _ _ _ ↦ by ext; exact apply_add_first ..)
      (fun t u v ↦ by ext z w; simpa only [LinearMap.mk₂_apply, LinearMap.smul_apply,
        smul_eq_mul] using apply_smul_first r v z w u t)
      (fun _ _ _ ↦ by ext; exact apply_add_second ..)
      (fun t u v ↦ by ext z w; simpa only [LinearMap.mk₂_apply, LinearMap.smul_apply,
        smul_eq_mul] using apply_smul_second r u z w v t)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Evaluation of `toLinearMap₄ r` on four vectors. -/
@[simp]
theorem toLinearMap₄_apply (r : FourTensor V) (u v z w : V) :
    toLinearMap₄ r u v z w = r ![u, v, z, w] :=
  (rfl)

/-- Currying a four-tensor into a four-fold linear map is injective. -/
theorem toLinearMap₄_injective : Function.Injective (toLinearMap₄ (V := V)) := by
  intro r₁ r₂ h
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm]
  exact congr($h (m 0) (m 1) (m 2) (m 3))

/-- An algebraic curvature tensor vanishes on `(u, v, u, v)` when `u` and `v` are linearly
dependent. -/
theorem IsAlgebraicCurvature.apply_self_eq_zero_of_not_linearIndependent {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {u v : V} (huv : ¬LinearIndependent ℝ ![u, v]) :
    r ![u, v, u, v] = 0 := by
  have h := LinearMap.apply_apply_apply_apply_eq_zero_of_not_linearIndependent (T := toLinearMap₄ r)
    (two_ne_zero : (2 : ℝ) ≠ 0) (fun x y z w ↦ hr.antisymm_first x y z w) huv
  simp only [toLinearMap₄_apply] at h
  rw [hr.antisymm_last u v u v, h, neg_zero]

/-- **Sectional polarization**: two algebraic curvature tensors agreeing on `(u, v, u, v)` for all
`u, v` are equal. -/
theorem IsAlgebraicCurvature.eq_of_apply_self_eq {r₁ r₂ : FourTensor V}
    (hr₁ : IsAlgebraicCurvature r₁) (hr₂ : IsAlgebraicCurvature r₂)
    (h : ∀ u v, r₁ ![u, v, u, v] = r₂ ![u, v, u, v]) : r₁ = r₂ := by
  refine toLinearMap₄_injective <| LinearMap.eq_of_cyclic_eq_zero
    (IsRegular.of_ne_zero' (by norm_num : (6 : ℝ) ≠ 0)).left
    hr₁.antisymm_first hr₁.antisymm_last hr₁.cyclic_eq_zero
    hr₂.antisymm_first hr₂.antisymm_last hr₂.cyclic_eq_zero fun x y ↦ ?_
  simp only [toLinearMap₄_apply]
  rw [hr₁.antisymm_last x y y x, hr₂.antisymm_last x y y x, h x y]

/-- **Sectional polarization on planes**: two algebraic curvature tensors agreeing on `(u, v, u, v)`
for every linearly independent pair `u, v` are equal. -/
theorem IsAlgebraicCurvature.eq_of_apply_self_eq_of_linearIndependent {r₁ r₂ : FourTensor V}
    (hr₁ : IsAlgebraicCurvature r₁) (hr₂ : IsAlgebraicCurvature r₂)
    (h : ∀ u v, LinearIndependent ℝ ![u, v] → r₁ ![u, v, u, v] = r₂ ![u, v, u, v]) :
    r₁ = r₂ := by
  refine hr₁.eq_of_apply_self_eq hr₂ fun u v ↦ ?_
  by_cases huv : LinearIndependent ℝ ![u, v]
  · exact h u v huv
  · rw [hr₁.apply_self_eq_zero_of_not_linearIndependent huv,
      hr₂.apply_self_eq_zero_of_not_linearIndependent huv]

/-- A four-tensor is *pair-symmetric* if it is antisymmetric in its first pair and in its last pair
of arguments and unchanged when the two pairs are swapped, without imposing the first Bianchi
identity. -/
structure IsPairSymmetric (r : FourTensor V) : Prop where
  /-- Antisymmetry in the first pair of arguments. -/
  antisymm_first : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]
  /-- Antisymmetry in the last pair of arguments. -/
  antisymm_last : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]
  /-- Symmetry under interchanging the two pairs of arguments. -/
  swap_pairs : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]

/-- Every algebraic curvature tensor is pair-symmetric. -/
theorem IsAlgebraicCurvature.isPairSymmetric {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsPairSymmetric r :=
  ⟨hr.antisymm_first, hr.antisymm_last, hr.swap_pairs⟩

variable (V) in
/-- The submodule of pair-symmetric four-tensors on `V`. -/
def pairSymmetricSubmodule : Submodule ℝ (FourTensor V) where
  carrier := {r | IsPairSymmetric r}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {r q} hr hq := by
    refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;> simp only [add_apply]
    · rw [hr.antisymm_first, hq.antisymm_first, neg_add]
    · rw [hr.antisymm_last, hq.antisymm_last, neg_add]
    · rw [hr.swap_pairs, hq.swap_pairs]
  smul_mem' c r hr := by
    refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
      simp only [smul_apply, smul_eq_mul]
    · rw [hr.antisymm_first, mul_neg]
    · rw [hr.antisymm_last, mul_neg]
    · rw [hr.swap_pairs]

/-- Membership in `pairSymmetricSubmodule V` is `IsPairSymmetric`. -/
@[simp]
theorem mem_pairSymmetricSubmodule {r : FourTensor V} :
    r ∈ pairSymmetricSubmodule V ↔ IsPairSymmetric r :=
  (Iff.rfl)

private theorem isPairSymmetric_self_first {r : FourTensor V} (hr : IsPairSymmetric r)
    (x z w : V) : r ![x, x, z, w] = 0 :=
  CharZero.eq_neg_self_iff.mp (hr.antisymm_first x x z w)

private theorem isPairSymmetric_self_last {r : FourTensor V} (hr : IsPairSymmetric r)
    (u v z : V) : r ![u, v, z, z] = 0 :=
  CharZero.eq_neg_self_iff.mp (hr.antisymm_last u v z z)

private theorem isPairSymmetric_toLinearMap₄_self_first {r : FourTensor V}
    (hr : IsPairSymmetric r) (x z w : V) : toLinearMap₄ r x x z w = 0 :=
  isPairSymmetric_self_first hr x z w

private theorem isPairSymmetric_toLinearMap₄_isAlt {r : FourTensor V}
    (hr : IsPairSymmetric r) (u v : V) : (toLinearMap₄ r u v).IsAlt :=
  isPairSymmetric_self_last hr u v

private def bianchiMultilinear (r : FourTensor V) :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin 4 ↦ V) ℝ :=
  MultilinearMap.mk'
    (fun m ↦ r ![m 0, m 1, m 2, m 3] + r ![m 1, m 2, m 0, m 3] + r ![m 2, m 0, m 1, m 3])
    (fun m i x y ↦ by
      fin_cases i <;>
        simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Function.update_self,
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
          apply_add_first, apply_add_second, apply_add_third, apply_add_fourth] <;>
        ring)
    (fun m i c x ↦ by
      fin_cases i <;>
        simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Function.update_self,
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
          apply_smul_first, apply_smul_second, apply_smul_third, apply_smul_fourth,
          RingHom.id_apply, smul_eq_mul] <;>
        ring)

private theorem bianchiMultilinear_apply (r : FourTensor V) (m : Fin 4 → V) :
    bianchiMultilinear r m =
      r ![m 0, m 1, m 2, m 3] + r ![m 1, m 2, m 0, m 3] + r ![m 2, m 0, m 1, m 3] :=
  (rfl)

private theorem bianchiMultilinear_map_eq_zero_of_lt {r : FourTensor V} (hr : IsPairSymmetric r)
    (m : Fin 4 → V) {i j : Fin 4} (hm : m i = m j) (hij : i < j) :
    bianchiMultilinear r m = 0 := by
  rw [bianchiMultilinear_apply]
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | (
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at hm ⊢
    rw [hm])
  · rw [isPairSymmetric_self_first hr, hr.antisymm_first (m 2) (m 1)]
    ring
  · rw [isPairSymmetric_self_first hr, hr.antisymm_first (m 1) (m 2)]
    ring
  · rw [isPairSymmetric_self_last hr, hr.swap_pairs (m 2) (m 3), hr.antisymm_first (m 1) (m 3)]
    ring
  · rw [isPairSymmetric_self_first hr, hr.antisymm_first (m 2) (m 0)]
    ring
  · rw [isPairSymmetric_self_last hr, hr.swap_pairs (m 0) (m 3), hr.antisymm_first (m 3) (m 2)]
    ring
  · rw [isPairSymmetric_self_last hr, hr.swap_pairs (m 3) (m 0), hr.antisymm_last (m 1) (m 3)]
    ring

private theorem bianchiMultilinear_map_eq_zero_of_eq {r : FourTensor V} (hr : IsPairSymmetric r)
    (m : Fin 4 → V) (i j : Fin 4) (hm : m i = m j) (hij : i ≠ j) :
    bianchiMultilinear r m = 0 := by
  rcases hij.lt_or_gt with hlt | hlt
  · exact bianchiMultilinear_map_eq_zero_of_lt hr m hm hlt
  · exact bianchiMultilinear_map_eq_zero_of_lt hr m hm.symm hlt

/-- The Bianchi cyclic sum `m ↦ r(m₀, m₁, m₂, m₃) + r(m₁, m₂, m₀, m₃) + r(m₂, m₀, m₁, m₃)` as a
linear map from pair-symmetric four-tensors to alternating four-forms on `V`. -/
def bianchiAlternatingMap : pairSymmetricSubmodule V →ₗ[ℝ] V [⋀^Fin 4]→ₗ[ℝ] ℝ where
  toFun r :=
    { toMultilinearMap := bianchiMultilinear r.1
      map_eq_zero_of_eq' m i j hm hij :=
        bianchiMultilinear_map_eq_zero_of_eq (mem_pairSymmetricSubmodule.mp r.2) m i j hm hij }
  map_add' r q := by
    ext m
    simp only [AlternatingMap.coe_mk, bianchiMultilinear_apply, Submodule.coe_add, add_apply]
    ring
  map_smul' c r := by
    ext m
    simp only [AlternatingMap.coe_mk, bianchiMultilinear_apply, SetLike.val_smul, smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- Evaluation of `bianchiAlternatingMap`. -/
@[simp]
theorem bianchiAlternatingMap_apply (r : pairSymmetricSubmodule V) (m : Fin 4 → V) :
    bianchiAlternatingMap r m =
      r.1 ![m 0, m 1, m 2, m 3] + r.1 ![m 1, m 2, m 0, m 3] + r.1 ![m 2, m 0, m 1, m 3] :=
  (rfl)

/-- The kernel of `bianchiAlternatingMap` inside `pairSymmetricSubmodule V` is precisely
`algebraicCurvatureSubmodule V`. -/
theorem ker_bianchiAlternatingMap :
    LinearMap.ker (bianchiAlternatingMap (V := V)) =
      (algebraicCurvatureSubmodule V).comap (pairSymmetricSubmodule V).subtype := by
  ext ⟨r, hr⟩
  replace hr := mem_pairSymmetricSubmodule.mp hr
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    mem_algebraicCurvatureSubmodule, AlternatingMap.ext_iff, bianchiAlternatingMap_apply,
    zero_apply]
  refine ⟨fun h ↦
    ⟨hr.antisymm_first, hr.antisymm_last, hr.swap_pairs, fun u v z w ↦ h ![u, v, z, w]⟩,
    fun h m ↦ h.cyclic_eq_zero (m 0) (m 1) (m 2) (m 3)⟩

private def exteriorBilinOfPairSymmetric (r : pairSymmetricSubmodule V) :
    BilinForm ℝ (⋀[ℝ]^2 V) :=
  (toLinearMap₄ r.1).exteriorSquareBilinear
    (isPairSymmetric_toLinearMap₄_self_first (mem_pairSymmetricSubmodule.mp r.2))
    (isPairSymmetric_toLinearMap₄_isAlt (mem_pairSymmetricSubmodule.mp r.2))

private theorem isSymm_exteriorBilinOfPairSymmetric (r : pairSymmetricSubmodule V) :
    (exteriorBilinOfPairSymmetric r).IsSymm :=
  ⟨fun a b ↦ by
    have hr := mem_pairSymmetricSubmodule.mp r.2
    have hflip := LinearMap.flip_exteriorSquareBilinear (toLinearMap₄ r.1)
      (isPairSymmetric_toLinearMap₄_self_first hr)
      (isPairSymmetric_toLinearMap₄_isAlt hr) hr.swap_pairs
    exact (LinearMap.congr_fun₂ hflip a b).symm⟩

end NormedSpace

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- On a finite-dimensional space, currying identifies `FourTensor V` with four-fold linear maps,
inverse to `ofLinearMap₄`. -/
def toLinearMap₄Equiv : FourTensor V ≃ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  { toLinearMap₄ with
    invFun := ofLinearMap₄
    left_inv r := by
      ext m
      rw [LinearMap.toFun_eq_coe, ofLinearMap₄_apply, toLinearMap₄_apply]
      congr 1
      funext i; fin_cases i <;> rfl
    right_inv T := by
      ext u v z w
      simp }

/-- `toLinearMap₄Equiv` evaluates `r` on the four vector arguments. -/
@[simp]
theorem toLinearMap₄Equiv_apply (r : FourTensor V) (u v z w : V) :
    toLinearMap₄Equiv r u v z w = r ![u, v, z, w] :=
  (rfl)

/-- The inverse of `toLinearMap₄Equiv` is `ofLinearMap₄`. -/
@[simp]
theorem toLinearMap₄Equiv_symm_apply (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    toLinearMap₄Equiv.symm T = ofLinearMap₄ T :=
  (rfl)

/-- The inverse of `toLinearMap₄Equiv` as a linear map is `ofLinearMap₄`. -/
@[simp]
theorem toLinearMap₄Equiv_symm_toLinearMap :
    (toLinearMap₄Equiv (V := V)).symm.toLinearMap = ofLinearMap₄ :=
  (rfl)

/-- On a space of dimension at most `1`, every algebraic curvature tensor is zero. -/
theorem IsAlgebraicCurvature.eq_zero_of_finrank_le_one {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 1) : r = 0 := by
  refine hr.eq_of_apply_self_eq_of_linearIndependent
    (mem_algebraicCurvatureSubmodule.mp (algebraicCurvatureSubmodule V).zero_mem)
    fun u v huv ↦ False.elim ?_
  have hcard := huv.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

/-- On a space of dimension at most `1`, `algebraicCurvatureSubmodule V` is trivial. -/
theorem algebraicCurvatureSubmodule_eq_bot_of_finrank_le_one (hdim : Module.finrank ℝ V ≤ 1) :
    algebraicCurvatureSubmodule V = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hr ↦
    (mem_algebraicCurvatureSubmodule.mp hr).eq_zero_of_finrank_le_one hdim

private def fourTensorOfExteriorBilin (B : BilinForm ℝ (⋀[ℝ]^2 V)) : FourTensor V :=
  ofLinearMap₄ <| MultilinearMap.toBilinMap
    ((TauCeti.BilinForm.ofExteriorSquareDual.comp B).compMultilinearMap
      (exteriorPower.ιMulti ℝ 2).toMultilinearMap)

private theorem fourTensorOfExteriorBilin_apply (B : BilinForm ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    fourTensorOfExteriorBilin B ![u, v, z, w] =
      B (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) := by
  simp [fourTensorOfExteriorBilin]

private theorem isPairSymmetric_fourTensorOfExteriorBilin
    (B : LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V)) :
    IsPairSymmetric (fourTensorOfExteriorBilin B.1) := by
  have hswap (x y : V) : exteriorPower.ιMulti ℝ 2 ![x, y] =
      -exteriorPower.ιMulti ℝ 2 ![y, x] := by
    simpa [Equiv.swap_apply_def] using
      (exteriorPower.ιMulti ℝ 2).map_swap ![y, x] (by decide : (0 : Fin 2) ≠ 1)
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [fourTensorOfExteriorBilin_apply]
  · rw [hswap u v, map_neg, LinearMap.neg_apply]
  · rw [hswap z w, map_neg]
  · exact (LinearMap.BilinForm.mem_symmSubmodule.mp B.2).eq _ _

/-- Descending a pair-symmetric four-tensor to the exterior square identifies
`pairSymmetricSubmodule V` with the symmetric bilinear forms on `⋀[ℝ]^2 V`. -/
def pairSymmetricEquivSymmBilin :
    pairSymmetricSubmodule V ≃ₗ[ℝ] LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V) where
  toFun r :=
    ⟨exteriorBilinOfPairSymmetric r,
      LinearMap.BilinForm.mem_symmSubmodule.mpr (isSymm_exteriorBilinOfPairSymmetric r)⟩
  invFun B :=
    ⟨fourTensorOfExteriorBilin B.1,
      mem_pairSymmetricSubmodule.mpr (isPairSymmetric_fourTensorOfExteriorBilin B)⟩
  map_add' r q := Subtype.ext <| by
    dsimp only [Submodule.coe_add, exteriorBilinOfPairSymmetric]
    rw [LinearMap.exteriorSquareBilinear_eq_iff]
    intro v w
    simp [LinearMap.exteriorSquareBilinear_ιMulti_ιMulti]
  map_smul' c r := Subtype.ext <| by
    dsimp only [SetLike.val_smul, RingHom.id_apply, exteriorBilinOfPairSymmetric]
    rw [LinearMap.exteriorSquareBilinear_eq_iff]
    intro v w
    simp [LinearMap.exteriorSquareBilinear_ιMulti_ιMulti]
  left_inv r := Subtype.ext <| toLinearMap₄_injective <| by
    ext u v z w
    rw [toLinearMap₄_apply, fourTensorOfExteriorBilin_apply]
    exact LinearMap.exteriorSquareBilinear_ιMulti_ιMulti _ _ _ ![u, v] ![z, w]
  right_inv B := Subtype.ext <| by
    dsimp only [exteriorBilinOfPairSymmetric]
    rw [LinearMap.exteriorSquareBilinear_eq_iff]
    intro v w
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
    rw [toLinearMap₄_apply, fourTensorOfExteriorBilin_apply]
    conv_lhs => rw [hv, hw]

/-- Evaluation of `pairSymmetricEquivSymmBilin` on pure wedges `u ∧ v` and `z ∧ w`. -/
@[simp]
theorem pairSymmetricEquivSymmBilin_apply_ιMulti (r : pairSymmetricSubmodule V) (u v z w : V) :
    (pairSymmetricEquivSymmBilin r).1 (exteriorPower.ιMulti ℝ 2 ![u, v])
        (exteriorPower.ιMulti ℝ 2 ![z, w]) =
      r.1 ![u, v, z, w] :=
  LinearMap.exteriorSquareBilinear_ιMulti_ιMulti _ _ _ ![u, v] ![z, w]

/-- Evaluation of `pairSymmetricEquivSymmBilin.symm` on four vectors via pure wedges. -/
@[simp]
theorem pairSymmetricEquivSymmBilin_symm_apply
    (B : LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    (pairSymmetricEquivSymmBilin.symm B).1 ![u, v, z, w] =
      B.1 (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) :=
  fourTensorOfExteriorBilin_apply B.1 u v z w

/-- `bianchiAlternatingMap` is surjective: `(1/3) • ω` is an explicit right inverse on alternating
four-forms. -/
theorem bianchiAlternatingMap_surjective :
    Function.Surjective (bianchiAlternatingMap (V := V)) := by
  intro ω
  let rω : FourTensor V :=
    (1 / 3 : ℝ) •
      { ω.toMultilinearMap with cont := ω.toMultilinearMap.continuous_of_finiteDimensional }
  have hrω_apply (m : Fin 4 → V) : rω m = (1 / 3 : ℝ) * ω m := rfl
  have hswap (m : Fin 4 → V) {i j : Fin 4} (hij : i ≠ j) : ω (m ∘ Equiv.swap i j) = -ω m :=
    ω.map_swap m hij
  have h01 (a b c d : V) : ω ![b, a, c, d] = -ω ![a, b, c, d] := by
    have : (![a, b, c, d] ∘ Equiv.swap (0 : Fin 4) 1) = ![b, a, c, d] := by
      funext k; fin_cases k <;> rfl
    rw [← this]; exact hswap _ (by decide)
  have h12 (a b c d : V) : ω ![a, c, b, d] = -ω ![a, b, c, d] := by
    have : (![a, b, c, d] ∘ Equiv.swap (1 : Fin 4) 2) = ![a, c, b, d] := by
      funext k; fin_cases k <;> rfl
    rw [← this]; exact hswap _ (by decide)
  have h23 (a b c d : V) : ω ![a, b, d, c] = -ω ![a, b, c, d] := by
    have : (![a, b, c, d] ∘ Equiv.swap (2 : Fin 4) 3) = ![a, b, d, c] := by
      funext k; fin_cases k <;> rfl
    rw [← this]; exact hswap _ (by decide)
  have hrω_mem : IsPairSymmetric rω := by
    refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;> simp only [hrω_apply]
    · rw [h01 v u z w]; ring
    · rw [h23 u v w z]; ring
    · rw [h12 u z v w, h01 z u v w, h23 z u w v, h12 z w u v]; ring
  refine ⟨⟨rω, mem_pairSymmetricSubmodule.mpr hrω_mem⟩, ?_⟩
  ext m
  have hm : ![m 0, m 1, m 2, m 3] = m := by funext k; fin_cases k <;> rfl
  simp only [bianchiAlternatingMap_apply, hrω_apply]
  rw [h12 (m 1) (m 0) (m 2) (m 3), h01 (m 0) (m 1) (m 2) (m 3),
    h01 (m 0) (m 2) (m 1) (m 3), h12 (m 0) (m 1) (m 2) (m 3), hm]
  ring

private theorem choose_symm_sub_choose_four {n d : ℕ}
    (hrk : n.choose 4 + d = n.choose 2 * (n.choose 2 + 1) / 2) :
    d = n ^ 2 * (n ^ 2 - 1) / 12 := by
  match n with
  | 0 | 1 | 2 | 3 => norm_num [Nat.choose] at hrk ⊢; omega
  | m + 4 =>
    have hs3 : m + 4 - 3 = m + 1 := by omega
    have hs2 : m + 4 - 2 = m + 2 := by omega
    have hs1 : m + 4 - 1 = m + 3 := by omega
    have hc4 : 24 * (m + 4).choose 4 = (m + 4) * (m + 3) * (m + 2) * (m + 1) := by
      have h := (Nat.descFactorial_eq_factorial_mul_choose (m + 4) 4).symm
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, hs3, hs2, hs1, Nat.sub_zero] at h
      norm_num [Nat.factorial] at h
      rw [h]; ring
    have hc2 : 2 * (m + 4).choose 2 = (m + 4) * (m + 3) := by
      have h := (Nat.descFactorial_eq_factorial_mul_choose (m + 4) 2).symm
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, hs1, Nat.sub_zero] at h
      norm_num [Nat.factorial] at h
      rw [h]; ring
    have hp : 2 * ((m + 4).choose 2 * ((m + 4).choose 2 + 1) / 2) =
        (m + 4).choose 2 * ((m + 4).choose 2 + 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_succ_self _).two_dvd
    have h24 : 24 * ((m + 4).choose 4 + d) =
        12 * (2 * ((m + 4).choose 2 * ((m + 4).choose 2 + 1) / 2)) := by omega
    rw [hp] at h24
    have hpoly : 12 * ((m + 4).choose 2 * ((m + 4).choose 2 + 1)) =
        3 * (2 * (m + 4).choose 2) * (2 * (m + 4).choose 2 + 2) := by ring
    rw [hpoly, hc2] at h24
    have hsq : (m + 3) * (m + 5) + 1 = (m + 4) ^ 2 := by ring
    have hsq' : (m + 4) ^ 2 - 1 = (m + 3) * (m + 5) := by omega
    have hident : 3 * ((m + 4) * (m + 3)) * ((m + 4) * (m + 3) + 2) =
        (m + 4) * (m + 3) * (m + 2) * (m + 1) +
          2 * ((m + 4) ^ 2 * ((m + 3) * (m + 5))) := by ring
    rw [hsq']
    omega

/-- **Dimension of the space of algebraic curvature tensors**: on an `n`-dimensional real normed
space `V`, `Module.finrank ℝ (algebraicCurvatureSubmodule V) = n ^ 2 * (n ^ 2 - 1) / 12`. -/
theorem finrank_algebraicCurvatureSubmodule :
    Module.finrank ℝ (algebraicCurvatureSubmodule V) =
      Module.finrank ℝ V ^ 2 * (Module.finrank ℝ V ^ 2 - 1) / 12 := by
  have hle : algebraicCurvatureSubmodule V ≤ pairSymmetricSubmodule V :=
    fun _ hr ↦ (mem_algebraicCurvatureSubmodule.mp hr).isPairSymmetric
  have hrk := LinearMap.finrank_range_add_finrank_ker (K := ℝ) (V := pairSymmetricSubmodule V)
    (V₂ := V [⋀^Fin 4]→ₗ[ℝ] ℝ) (bianchiAlternatingMap (V := V))
  rw [LinearMap.range_eq_top.mpr bianchiAlternatingMap_surjective, finrank_top,
    ker_bianchiAlternatingMap, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
    (exteriorPower.alternatingMapLinearEquiv (R := ℝ) (M := V) (n := 4)).finrank_eq,
    Subspace.dual_finrank_eq, exteriorPower.finrank_eq,
    pairSymmetricEquivSymmBilin.finrank_eq,
    LinearMap.BilinForm.finrank_symmSubmodule,
    exteriorPower.finrank_eq] at hrk
  exact choose_symm_sub_choose_four hrk

/-- For `dim V = 2`, the space of algebraic curvature tensors is `1`-dimensional. -/
theorem finrank_algebraicCurvatureSubmodule_of_finrank_eq_two (hdim : Module.finrank ℝ V = 2) :
    Module.finrank ℝ (algebraicCurvatureSubmodule V) = 1 := by
  rw [finrank_algebraicCurvatureSubmodule, hdim]; norm_num

/-- For `dim V = 3`, the space of algebraic curvature tensors is `6`-dimensional. -/
theorem finrank_algebraicCurvatureSubmodule_of_finrank_eq_three (hdim : Module.finrank ℝ V = 3) :
    Module.finrank ℝ (algebraicCurvatureSubmodule V) = 6 := by
  rw [finrank_algebraicCurvatureSubmodule, hdim]; norm_num

/-- For `dim V = 4`, the space of algebraic curvature tensors is `20`-dimensional. -/
theorem finrank_algebraicCurvatureSubmodule_of_finrank_eq_four (hdim : Module.finrank ℝ V = 4) :
    Module.finrank ℝ (algebraicCurvatureSubmodule V) = 20 := by
  rw [finrank_algebraicCurvatureSubmodule, hdim]; norm_num

end FiniteDimensional

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **In dimension `2`, every algebraic curvature tensor is `(Scal / 2)` times the
constant-curvature tensor**: `algebraicCurvatureSubmodule V` has dimension `1` and is spanned by
`constantCurvature V`, whose scalar contraction is `2`. -/
theorem IsAlgebraicCurvature.eq_smul_constantCurvature_of_finrank_eq_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V = 2) :
    r = (scalar r / 2) • constantCurvature V := by
  let c₀ : algebraicCurvatureSubmodule V :=
    ⟨constantCurvature V,
      mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature⟩
  have hscal₀ : scalar (constantCurvature V) = 2 := by
    rw [scalar_constantCurvature, hdim]
    norm_num
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have : scalar (constantCurvature V) = 0 := by
      simpa [c₀] using congrArg (fun x : algebraicCurvatureSubmodule V ↦ scalar x.1) h0
    linarith
  have hfin : Module.finrank ℝ (algebraicCurvatureSubmodule V) = 1 :=
    finrank_algebraicCurvatureSubmodule_of_finrank_eq_two hdim
  obtain ⟨k, hk⟩ := (finrank_eq_one_iff_of_ne_zero' c₀ hc₀).mp hfin
    ⟨r, mem_algebraicCurvatureSubmodule.mpr hr⟩
  have hkr : r = k • constantCurvature V := (congrArg Subtype.val hk).symm
  have hk_val : k = scalar r / 2 := by
    have := congrArg scalar hkr
    rw [map_smul, hscal₀, smul_eq_mul] at this
    linarith
  rwa [← hk_val]

/-- In dimension `2`, every algebraic curvature tensor is Einstein with `Ric = (Scal / 2) g`. -/
theorem IsAlgebraicCurvature.ricci_eq_half_scalar_smul_innerₗ_of_finrank_eq_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V = 2) :
    ricci r = (scalar r / 2) • innerₗ V := by
  conv_lhs => rw [hr.eq_smul_constantCurvature_of_finrank_eq_two hdim]
  rw [map_smul, ricci_constantCurvature, hdim]
  norm_num

end InnerProductSpace

end TauCeti.FourTensor
