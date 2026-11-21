/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Symmetric
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
import TauCeti.LinearAlgebra.ExteriorPower.Square
import TauCeti.LinearAlgebra.Multilinear.SectionalPolarization

/-!
# Polarization and dimension of algebraic curvature tensors

Through `toLinearMap₄`, sectional polarization transfers to `FourTensor V`: an algebraic curvature
tensor is uniquely determined by its sectional values `r(u, v, u, v)` on linearly independent pairs.
In dimension at most `1`, every first-pair antisymmetric four-tensor vanishes.

On an `n`-dimensional real normed space `V`, algebraic curvature tensors fit into the short exact
sequence (`Besse, Section 1.G`)

`0 → algebraicCurvatureSubmodule V → bivectorSymmetricSubmodule V → V [⋀^Fin 4]→ₗ[ℝ] ℝ → 0`,

identifying `bivectorSymmetricSubmodule V` with symmetric bilinear forms on `⋀[ℝ]^2 V` and yielding
`Module.finrank ℝ (algebraicCurvatureSubmodule V) = n ^ 2 * (n ^ 2 - 1) / 12` (`1, 6, 20` for
`n = 2, 3, 4`). When `V` is a `2`-dimensional real inner product space, every pair-antisymmetric
four-tensor equals `(Scal / 2) • constantCurvature V` and satisfies `Ric = (Scal / 2) g`.

## Main definitions

* `TauCeti.FourTensor.IsBivectorSymmetric`, `TauCeti.FourTensor.bivectorSymmetricSubmodule`,
  `TauCeti.FourTensor.ofExteriorSquareBilin`,
  `TauCeti.FourTensor.bivectorSymmetricEquivSymmBilin`, and
  `TauCeti.FourTensor.bianchiAlternatingMap`.

## Main results

* `TauCeti.FourTensor.IsAlgebraicCurvature.eq_of_apply_self_eq`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.eq_of_apply_self_eq_of_linearIndependent`,
  `TauCeti.FourTensor.eq_zero_of_finrank_le_one_of_antisymm_first`,
  `TauCeti.FourTensor.kulkarniNomizu_eq_zero_of_finrank_le_one`,
  `TauCeti.FourTensor.isBivectorSymmetric_ofExteriorSquareBilin_iff`,
  `TauCeti.FourTensor.finrank_algebraicCurvatureSubmodule`, and
  `TauCeti.FourTensor.eq_smul_constantCurvature_of_finrank_eq_two_of_antisymm`.

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

/-- A first-pair antisymmetric four-tensor vanishes when its first two arguments are dependent. -/
theorem apply_eq_zero_of_not_linearIndependent_of_antisymm_first {r : FourTensor V} {u v : V}
    (huv : ¬LinearIndependent ℝ ![u, v])
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) (z w : V) : r ![u, v, z, w] = 0 := by
  have hAlt : (toLinearMap₄ r).IsAlt := fun a ↦ LinearMap.ext₂ fun c d ↦ by
    rw [toLinearMap₄_apply]; exact CharZero.eq_neg_self_iff.mp (h₁ a a c d)
  simpa using congr($(AlternatingMap.map_linearDependent (K := ℝ) (N := V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    hAlt.toAlternatingMap ![u, v] huv) z w)

/-- An algebraic curvature tensor vanishes on `(u, v, u, v)` for linearly dependent `u, v`. -/
theorem IsAlgebraicCurvature.apply_self_eq_zero_of_not_linearIndependent {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {u v : V} (huv : ¬LinearIndependent ℝ ![u, v]) :
    r ![u, v, u, v] = 0 :=
  apply_eq_zero_of_not_linearIndependent_of_antisymm_first huv hr.antisymm_first u v

/-- **Sectional polarization**: algebraic curvature tensors agreeing on all `(u, v, u, v)` agree. -/
theorem IsAlgebraicCurvature.eq_of_apply_self_eq {r₁ r₂ : FourTensor V}
    (hr₁ : IsAlgebraicCurvature r₁) (hr₂ : IsAlgebraicCurvature r₂)
    (h : ∀ u v, r₁ ![u, v, u, v] = r₂ ![u, v, u, v]) : r₁ = r₂ :=
  toLinearMap₄_injective <| LinearMap.eq_of_cyclic_eq_zero
    (IsRegular.of_ne_zero' (by norm_num : (6 : ℝ) ≠ 0)).left
    (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using hr₁.antisymm_first ..)
    (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using hr₁.antisymm_last ..)
    (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using hr₁.cyclic_eq_zero ..)
    (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using hr₂.antisymm_first ..)
    (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using hr₂.antisymm_last ..)
    (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using hr₂.cyclic_eq_zero ..)
    fun _ _ ↦ by simp only [toLinearMap₄_apply]; rw [hr₁.antisymm_last, hr₂.antisymm_last, h]

/-- **Sectional polarization**: agreeing on linearly independent `(u, v, u, v)` suffices. -/
theorem IsAlgebraicCurvature.eq_of_apply_self_eq_of_linearIndependent {r₁ r₂ : FourTensor V}
    (hr₁ : IsAlgebraicCurvature r₁) (hr₂ : IsAlgebraicCurvature r₂)
    (h : ∀ u v, LinearIndependent ℝ ![u, v] → r₁ ![u, v, u, v] = r₂ ![u, v, u, v]) : r₁ = r₂ :=
  hr₁.eq_of_apply_self_eq hr₂ fun u v ↦ (em _).elim (h u v) fun huv ↦ by
    rw [hr₁.apply_self_eq_zero_of_not_linearIndependent huv,
      hr₂.apply_self_eq_zero_of_not_linearIndependent huv]

/-- Pair-antisymmetric, pair-interchange-symmetric four-tensors (symmetric forms on `⋀[ℝ]^2 V`). -/
structure IsBivectorSymmetric (r : FourTensor V) : Prop where
  /-- Antisymmetry in the first pair of arguments. -/
  antisymm_first : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]
  /-- Antisymmetry in the last pair of arguments. -/
  antisymm_last : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]
  /-- Symmetry under interchanging the two pairs of arguments. -/
  swap_pairs : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]

/-- Every algebraic curvature tensor is bivector-symmetric. -/
theorem IsAlgebraicCurvature.isBivectorSymmetric {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsBivectorSymmetric r := ⟨hr.antisymm_first, hr.antisymm_last, hr.swap_pairs⟩

variable (V) in
/-- The submodule of bivector-symmetric four-tensors on `V`. -/
def bivectorSymmetricSubmodule : Submodule ℝ (FourTensor V) where
  carrier := {r | IsBivectorSymmetric r}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' hr hq := ⟨fun _ _ _ _ ↦ by simp only [add_apply]; rw [hr.antisymm_first,
      hq.antisymm_first, neg_add],
    fun _ _ _ _ ↦ by simp only [add_apply]; rw [hr.antisymm_last, hq.antisymm_last, neg_add],
    fun _ _ _ _ ↦ by simp only [add_apply]; rw [hr.swap_pairs, hq.swap_pairs]⟩
  smul_mem' _ _ hr := ⟨fun _ _ _ _ ↦ by simp only [smul_apply, smul_eq_mul]; rw [hr.antisymm_first,
      mul_neg],
    fun _ _ _ _ ↦ by simp only [smul_apply, smul_eq_mul]; rw [hr.antisymm_last, mul_neg],
    fun _ _ _ _ ↦ by simp only [smul_apply, smul_eq_mul]; rw [hr.swap_pairs]⟩

/-- Membership in `bivectorSymmetricSubmodule V` is `IsBivectorSymmetric`. -/
@[simp] theorem mem_bivectorSymmetricSubmodule {r : FourTensor V} :
    r ∈ bivectorSymmetricSubmodule V ↔ IsBivectorSymmetric r := (Iff.rfl)

private theorem isBivectorSymmetric_self_first {r : FourTensor V} (hr : IsBivectorSymmetric r)
    (x z w : V) : r ![x, x, z, w] = 0 := CharZero.eq_neg_self_iff.mp (hr.antisymm_first x x z w)

private theorem isBivectorSymmetric_self_last {r : FourTensor V} (hr : IsBivectorSymmetric r)
    (u v z : V) : r ![u, v, z, z] = 0 := CharZero.eq_neg_self_iff.mp (hr.antisymm_last u v z z)

private def bianchiMultilinear (r : FourTensor V) :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin 4 ↦ V) ℝ :=
  MultilinearMap.mk'
    (fun m ↦ r ![m 0, m 1, m 2, m 3] + r ![m 1, m 2, m 0, m 3] + r ![m 2, m 0, m 1, m 3])
    (fun _ i _ _ ↦ by fin_cases i <;>
      simp [apply_add_first, apply_add_second, apply_add_third, apply_add_fourth] <;> ring)
    (fun _ i _ _ ↦ by fin_cases i <;>
      simp [apply_smul_first, apply_smul_second, apply_smul_third, apply_smul_fourth] <;> ring)

private theorem bianchiMultilinear_map_eq_zero_of_lt {r : FourTensor V}
    (hr : IsBivectorSymmetric r) (m : Fin 4 → V) {i j : Fin 4} (hm : m i = m j) (hij : i < j) :
    bianchiMultilinear r m = 0 := by
  simp only [bianchiMultilinear, MultilinearMap.mk'_apply]
  have hf := isBivectorSymmetric_self_first hr; have hl := isBivectorSymmetric_self_last hr
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | (
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at hm ⊢; rw [hm])
  · rw [hf, hr.antisymm_first (m 2) (m 1)]; ring
  · rw [hf, hr.antisymm_first (m 1) (m 2)]; ring
  · rw [hl, hr.swap_pairs (m 2) (m 3), hr.antisymm_first (m 1) (m 3)]; ring
  · rw [hf, hr.antisymm_first (m 2) (m 0)]; ring
  · rw [hl, hr.swap_pairs (m 0) (m 3), hr.antisymm_first (m 3) (m 2)]; ring
  · rw [hl, hr.swap_pairs (m 3) (m 0), hr.antisymm_last (m 1) (m 3)]; ring

/-- The Bianchi cyclic sum as a linear map from `bivectorSymmetricSubmodule V` to four-forms. -/
def bianchiAlternatingMap : bivectorSymmetricSubmodule V →ₗ[ℝ] V [⋀^Fin 4]→ₗ[ℝ] ℝ where
  toFun r :=
    { toMultilinearMap := bianchiMultilinear r.val
      map_eq_zero_of_eq' m _ _ hm hij := hij.lt_or_gt.elim
        (bianchiMultilinear_map_eq_zero_of_lt (mem_bivectorSymmetricSubmodule.mp r.property) m hm)
        (bianchiMultilinear_map_eq_zero_of_lt (mem_bivectorSymmetricSubmodule.mp r.property) m
            hm.symm) }
  map_add' _ _ := AlternatingMap.ext fun _ ↦ by simp [bianchiMultilinear]; ring
  map_smul' _ _ := AlternatingMap.ext fun _ ↦ by simp [bianchiMultilinear]; ring

/-- Evaluation of `bianchiAlternatingMap`. -/
@[simp] theorem bianchiAlternatingMap_apply (r : bivectorSymmetricSubmodule V) (m : Fin 4 → V) :
    bianchiAlternatingMap r m =
      r.val ![m 0, m 1, m 2, m 3] + r.val ![m 1, m 2, m 0, m 3] + r.val ![m 2, m 0, m 1, m 3] :=
          (rfl)

/-- The kernel of `bianchiAlternatingMap` is `algebraicCurvatureSubmodule V`. -/
theorem ker_bianchiAlternatingMap :
    LinearMap.ker (bianchiAlternatingMap (V := V)) =
      (algebraicCurvatureSubmodule V).comap (bivectorSymmetricSubmodule V).subtype := by
  ext ⟨r, hr⟩; replace hr := mem_bivectorSymmetricSubmodule.mp hr
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    mem_algebraicCurvatureSubmodule, AlternatingMap.ext_iff, bianchiAlternatingMap_apply,
    zero_apply]
  exact ⟨fun h ↦ ⟨hr.antisymm_first, hr.antisymm_last, hr.swap_pairs, fun u v z w ↦ h ![u, v, z,
      w]⟩,
    fun h m ↦ h.cyclic_eq_zero (m 0) (m 1) (m 2) (m 3)⟩

private theorem isBivectorSymmetric_toLinearMap₄_isAlt {r : FourTensor V}
    (hr : IsBivectorSymmetric r) (u v : V) : (toLinearMap₄ r u v).IsAlt := fun z ↦ by
  rw [toLinearMap₄_apply]; exact isBivectorSymmetric_self_last hr u v z

private def exteriorBilinOfBivectorSymmetric (r : bivectorSymmetricSubmodule V) :
    BilinForm ℝ (⋀[ℝ]^2 V) :=
  let hr := mem_bivectorSymmetricSubmodule.mp r.property
  (toLinearMap₄ r.val).exteriorSquareBilinear
    (fun _ _ _ ↦ by rw [toLinearMap₄_apply]; exact isBivectorSymmetric_self_first hr ..)
    (isBivectorSymmetric_toLinearMap₄_isAlt hr)

private theorem isSymm_exteriorBilinOfBivectorSymmetric (r : bivectorSymmetricSubmodule V) :
    (exteriorBilinOfBivectorSymmetric r).IsSymm :=
  ⟨fun a b ↦ (LinearMap.congr_fun₂ (LinearMap.flip_exteriorSquareBilinear (toLinearMap₄ r.val) _ _
    (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using r.property.swap_pairs ..)) a b).symm⟩

end NormedSpace

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- On a space of dimension at most `1`, every first-pair antisymmetric four-tensor is zero. -/
theorem eq_zero_of_finrank_le_one_of_antisymm_first {r : FourTensor V}
    (hdim : Module.finrank ℝ V ≤ 1)
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) : r = 0 :=
  toLinearMap₄_injective <| by
    ext u v z w; rw [toLinearMap₄_apply, map_zero]
    exact apply_eq_zero_of_not_linearIndependent_of_antisymm_first
      (fun h ↦ by simpa using h.fintype_card_le_finrank.trans hdim) h₁ z w

/-- On a space of dimension at most `1`, every algebraic curvature tensor is zero. -/
theorem IsAlgebraicCurvature.eq_zero_of_finrank_le_one {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 1) : r = 0 :=
  eq_zero_of_finrank_le_one_of_antisymm_first hdim hr.antisymm_first

/-- On a space of dimension at most `1`, `algebraicCurvatureSubmodule V` is trivial. -/
theorem algebraicCurvatureSubmodule_eq_bot_of_finrank_le_one (hdim : Module.finrank ℝ V ≤ 1) :
    algebraicCurvatureSubmodule V = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hr ↦
    (mem_algebraicCurvatureSubmodule.mp hr).eq_zero_of_finrank_le_one hdim

/-- On a space of dimension at most `1`, every Kulkarni–Nomizu four-tensor vanishes. -/
theorem kulkarniNomizu_eq_zero_of_finrank_le_one (hdim : Module.finrank ℝ V ≤ 1)
    (h k : BilinForm ℝ V) : kulkarniNomizu h k = 0 :=
  eq_zero_of_finrank_le_one_of_antisymm_first hdim (kulkarniNomizu_antisymm_first h k)

/-- Pullback of a bilinear form on `⋀[ℝ]^2 V` to a four-tensor on `V`, defined by
`ofExteriorSquareBilin B ![u, v, z, w] = B (u ∧ v) (z ∧ w)`. -/
def ofExteriorSquareBilin : BilinForm ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun B := ofLinearMap₄ <| MultilinearMap.toBilinMap
    ((TauCeti.BilinForm.ofExteriorSquareDual.comp B).compMultilinearMap
      (exteriorPower.ιMulti ℝ 2).toMultilinearMap)
  map_add' _ _ := ext_vec fun _ _ _ _ ↦ by simp
  map_smul' _ _ := ext_vec fun _ _ _ _ ↦ by simp

/-- Evaluation of `ofExteriorSquareBilin B` on four vectors via pure wedges. -/
@[simp] theorem ofExteriorSquareBilin_apply (B : BilinForm ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorSquareBilin B ![u, v, z, w] =
      B (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) := by
  simp [ofExteriorSquareBilin]

/-- `ofExteriorSquareBilin B` is bivector-symmetric if and only if `B` is symmetric. -/
@[simp] theorem isBivectorSymmetric_ofExteriorSquareBilin_iff {B : BilinForm ℝ (⋀[ℝ]^2 V)} :
    IsBivectorSymmetric (ofExteriorSquareBilin B) ↔ B.IsSymm := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩⟩
  · have hflip : B.flip = B :=
      exteriorPower.linearMap_ext_ιMulti_two fun u v ↦
        exteriorPower.linearMap_ext_ιMulti_two fun z w ↦ by
          rw [LinearMap.BilinForm.flip_apply, ← ofExteriorSquareBilin_apply,
            ← ofExteriorSquareBilin_apply]
          exact h.swap_pairs z w u v
    exact ⟨fun x y ↦ LinearMap.congr_fun₂ hflip y x⟩
  · simp only [ofExteriorSquareBilin_apply]
    rw [exteriorPower.ιMulti_two_swap v u, map_neg, LinearMap.neg_apply]
  · simp only [ofExteriorSquareBilin_apply]
    rw [exteriorPower.ιMulti_two_swap w z, map_neg]
  · simp only [ofExteriorSquareBilin_apply]
    exact h.eq _ _

/-- Linear equivalence from `bivectorSymmetricSubmodule V` to symmetric forms on `⋀[ℝ]^2 V`. -/
def bivectorSymmetricEquivSymmBilin :
    bivectorSymmetricSubmodule V ≃ₗ[ℝ] LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V) where
  toFun r := ⟨exteriorBilinOfBivectorSymmetric r,
    LinearMap.BilinForm.mem_symmSubmodule.mpr (isSymm_exteriorBilinOfBivectorSymmetric r)⟩
  invFun B := ⟨ofExteriorSquareBilin B.val,
    mem_bivectorSymmetricSubmodule.mpr (isBivectorSymmetric_ofExteriorSquareBilin_iff.mpr
      (LinearMap.BilinForm.mem_symmSubmodule.mp B.property))⟩
  map_add' _ _ := Subtype.ext <| (LinearMap.exteriorSquareBilinear_eq_iff ..).mpr fun _ _ ↦ by
    simp [exteriorBilinOfBivectorSymmetric, LinearMap.exteriorSquareBilinear_ιMulti_ιMulti]
  map_smul' _ _ := Subtype.ext <| (LinearMap.exteriorSquareBilinear_eq_iff ..).mpr fun _ _ ↦ by
    simp [exteriorBilinOfBivectorSymmetric, LinearMap.exteriorSquareBilinear_ιMulti_ιMulti]
  left_inv r := Subtype.ext <| toLinearMap₄_injective <| by
    ext u v z w; simp only [toLinearMap₄_apply, ofExteriorSquareBilin_apply]
    exact (LinearMap.exteriorSquareBilinear_ιMulti_ιMulti
      (toLinearMap₄ r.val) _ _ ![u, v] ![z, w]).trans (toLinearMap₄_apply r.val u v z w)
  right_inv _ := Subtype.ext <| (LinearMap.exteriorSquareBilinear_eq_iff ..).mpr fun v w ↦ by
    rw [toLinearMap₄_apply, ofExteriorSquareBilin_apply, ← FinVec.etaExpand_eq v,
      ← FinVec.etaExpand_eq w]; rfl

/-- Evaluation of `bivectorSymmetricEquivSymmBilin` on pure wedges `u ∧ v` and `z ∧ w`. -/
@[simp] theorem bivectorSymmetricEquivSymmBilin_apply_ιMulti (r : bivectorSymmetricSubmodule V)
    (u v z w : V) :
    (bivectorSymmetricEquivSymmBilin r).val (exteriorPower.ιMulti ℝ 2 ![u, v])
        (exteriorPower.ιMulti ℝ 2 ![z, w]) = r.val ![u, v, z, w] :=
  (LinearMap.exteriorSquareBilinear_ιMulti_ιMulti (toLinearMap₄ r.val) _ _ ![u, v] ![z, w]).trans
    (toLinearMap₄_apply r.val u v z w)

/-- Evaluation of `bivectorSymmetricEquivSymmBilin.symm` on four vectors via pure wedges. -/
@[simp] theorem bivectorSymmetricEquivSymmBilin_symm_apply
    (B : LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    (bivectorSymmetricEquivSymmBilin.symm B).val ![u, v, z, w] =
      B.val (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) :=
  ofExteriorSquareBilin_apply B.val u v z w

/-- `bianchiAlternatingMap` is surjective onto alternating four-forms. -/
theorem bianchiAlternatingMap_surjective :
    Function.Surjective (bianchiAlternatingMap (V := V)) := fun ω ↦ by
  let rω : FourTensor V := (1 / 3 : ℝ) •
    { ω.toMultilinearMap with cont := ω.toMultilinearMap.continuous_of_finiteDimensional }
  have hrω (m : Fin 4 → V) : rω m = (1 / 3 : ℝ) * ω m := rfl
  have h01 (a b c d : V) : ω ![b, a, c, d] = -ω ![a, b, c, d] := by
    convert ω.map_swap ![a, b, c, d] (by decide : (0 : Fin 4) ≠ 1) using 2
    funext k; fin_cases k <;> rfl
  have h12 (a b c d : V) : ω ![a, c, b, d] = -ω ![a, b, c, d] := by
    convert ω.map_swap ![a, b, c, d] (by decide : (1 : Fin 4) ≠ 2) using 2
    funext k; fin_cases k <;> rfl
  have h23 (a b c d : V) : ω ![a, b, d, c] = -ω ![a, b, c, d] := by
    convert ω.map_swap ![a, b, c, d] (by decide : (2 : Fin 4) ≠ 3) using 2
    funext k; fin_cases k <;> rfl
  refine ⟨⟨rω, mem_bivectorSymmetricSubmodule.mpr
    ⟨fun _ _ _ _ ↦ by simp only [hrω]; rw [h01]; ring,
     fun _ _ _ _ ↦ by simp only [hrω]; rw [h23]; ring,
     fun u v z w ↦ by
       simp only [hrω]; rw [h12 u z v w, h01 z u v w, h23 z u w v, h12 z w u v]; ring⟩⟩,
    AlternatingMap.ext fun m ↦ ?_⟩
  have hm : ![m 0, m 1, m 2, m 3] = m := FinVec.etaExpand_eq m
  simp only [bianchiAlternatingMap_apply, hrω]
  rw [h12 (m 1) (m 0) (m 2) (m 3), h01 (m 0) (m 1) (m 2) (m 3),
    h01 (m 0) (m 2) (m 1) (m 3), h12 (m 0) (m 1) (m 2) (m 3), hm]; ring

private theorem choose_symm_sub_choose_four {n d : ℕ}
    (hrk : n.choose 4 + d = n.choose 2 * (n.choose 2 + 1) / 2) :
    d = n ^ 2 * (n ^ 2 - 1) / 12 := by
  match n with
  | 0 | 1 | 2 | 3 => norm_num [Nat.choose] at hrk ⊢; omega
  | m + 4 =>
    have hc4 : 24 * (m + 4).choose 4 = (m + 4) * (m + 3) * (m + 2) * (m + 1) := by
      have h := (Nat.descFactorial_eq_factorial_mul_choose (m + 4) 4).symm
      simp [Nat.factorial, Nat.add_sub_assoc] at h; linarith
    have hc2 : 2 * (m + 4).choose 2 = (m + 4) * (m + 3) := by
      have h := (Nat.descFactorial_eq_factorial_mul_choose (m + 4) 2).symm
      simp [Nat.factorial] at h; linarith
    have hp := Nat.mul_div_cancel' (Nat.even_mul_succ_self ((m + 4).choose 2)).two_dvd
    have h24 : 24 * ((m + 4).choose 4 + d) =
        12 * (2 * ((m + 4).choose 2 * ((m + 4).choose 2 + 1) / 2)) := by omega
    have h12 : 12 * ((m + 4).choose 2 * ((m + 4).choose 2 + 1)) =
        3 * (2 * (m + 4).choose 2) * (2 * (m + 4).choose 2 + 2) := by ring
    rw [hp, h12, hc2] at h24
    have hident : 3 * ((m + 4) * (m + 3)) * ((m + 4) * (m + 3) + 2) =
        (m + 4) * (m + 3) * (m + 2) * (m + 1) + 2 * ((m + 4) ^ 2 * ((m + 3) * (m + 5))) := by ring
    rw [show (m + 4) ^ 2 - 1 = (m + 3) * (m + 5) from Nat.sub_eq_of_eq_add (by ring)]; omega

/-- **Dimension of `algebraicCurvatureSubmodule V`**: `n ^ 2 * (n ^ 2 - 1) / 12`. -/
theorem finrank_algebraicCurvatureSubmodule :
    Module.finrank ℝ (algebraicCurvatureSubmodule V) =
      Module.finrank ℝ V ^ 2 * (Module.finrank ℝ V ^ 2 - 1) / 12 := by
  have hle : algebraicCurvatureSubmodule V ≤ bivectorSymmetricSubmodule V :=
    fun _ hr ↦ (mem_algebraicCurvatureSubmodule.mp hr).isBivectorSymmetric
  have hrk := LinearMap.finrank_range_add_finrank_ker (K := ℝ) (V := bivectorSymmetricSubmodule V)
    (V₂ := V [⋀^Fin 4]→ₗ[ℝ] ℝ) (bianchiAlternatingMap (V := V))
  rw [LinearMap.range_eq_top.mpr bianchiAlternatingMap_surjective, finrank_top,
    ker_bianchiAlternatingMap, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
    (exteriorPower.alternatingMapLinearEquiv (R := ℝ) (M := V) (n := 4)).finrank_eq,
    Subspace.dual_finrank_eq, exteriorPower.finrank_eq, bivectorSymmetricEquivSymmBilin.finrank_eq,
    LinearMap.BilinForm.finrank_symmSubmodule, exteriorPower.finrank_eq] at hrk
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

/-- The Ricci contraction of a bivector-symmetric four-tensor is symmetric. -/
theorem IsBivectorSymmetric.isSymm_ricci {r : FourTensor V} (hr : IsBivectorSymmetric r) :
    (ricci r).IsSymm := isSymm_ricci_of_swap_pairs hr.swap_pairs

/-- In dimension `2`, every pair-antisymmetric `r` is `(scalar r / 2) • constantCurvature V`. -/
theorem eq_smul_constantCurvature_of_finrank_eq_two_of_antisymm {r : FourTensor V}
    (hdim : Module.finrank ℝ V = 2)
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    r = (scalar r / 2) • constantCurvature V := by
  let b : OrthonormalBasis (Fin 2) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  have h1s (x z w : V) : r ![x, x, z, w] = 0 := CharZero.eq_neg_self_iff.mp (h₁ x x z w)
  have h2s (u v z : V) : r ![u, v, z, z] = 0 := CharZero.eq_neg_self_iff.mp (h₂ u v z z)
  have hscal : scalar r = 2 * r ![b 0, b 1, b 0, b 1] := by
    rw [scalar_apply_orthonormalBasis b, Fin.sum_univ_two]
    simp only [Fin.sum_univ_two, h1s, h₁ (b 1) (b 0), h₂ _ _ (b 1) (b 0)]; ring
  refine toLinearMap₄_injective <|
    b.toBasis.ext fun i ↦ b.toBasis.ext fun j ↦ b.toBasis.ext fun k ↦ b.toBasis.ext fun l ↦ ?_
  simp only [OrthonormalBasis.coe_toBasis, map_smul, LinearMap.smul_apply, toLinearMap₄_apply,
    constantCurvature_apply, smul_eq_mul, orthonormal_iff_ite.mp b.orthonormal]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [h1s, h2s, h₁ (b 1) (b 0), h₂ _ _ (b 1) (b 0), hscal, ↓reduceIte, Fin.zero_eta,
      Fin.mk_one, Fin.reduceEq] <;> ring

/-- In dimension `2`, every algebraic curvature `r` is `(scalar r / 2) • constantCurvature V`. -/
theorem IsAlgebraicCurvature.eq_smul_constantCurvature_of_finrank_eq_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V = 2) :
    r = (scalar r / 2) • constantCurvature V :=
  eq_smul_constantCurvature_of_finrank_eq_two_of_antisymm hdim hr.antisymm_first hr.antisymm_last

/-- In dimension `2`, every pair-antisymmetric four-tensor satisfies `Ric = (Scal / 2) g`. -/
theorem ricci_eq_half_scalar_smul_innerₗ_of_finrank_eq_two_of_antisymm {r : FourTensor V}
    (hdim : Module.finrank ℝ V = 2)
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    ricci r = (scalar r / 2) • innerₗ V := by
  conv_lhs => rw [eq_smul_constantCurvature_of_finrank_eq_two_of_antisymm hdim h₁ h₂]
  rw [map_smul, ricci_constantCurvature, hdim]; norm_num

/-- In dimension `2`, every algebraic curvature tensor satisfies `Ric = (Scal / 2) g`. -/
theorem IsAlgebraicCurvature.ricci_eq_half_scalar_smul_innerₗ_of_finrank_eq_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V = 2) :
    ricci r = (scalar r / 2) • innerₗ V :=
  ricci_eq_half_scalar_smul_innerₗ_of_finrank_eq_two_of_antisymm hdim hr.antisymm_first
      hr.antisymm_last

end InnerProductSpace

end TauCeti.FourTensor
