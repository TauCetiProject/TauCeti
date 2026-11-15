/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.Analysis.InnerProductSpace.Nondegenerate
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Square
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.LinearAlgebra.BilinearForm.Squares
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear

/-!
# Curvature operators and the dimension of curvature space

On a finite-dimensional real inner product space `V`, every algebraic curvature tensor
`r ∈ algebraicCurvatureSubmodule V` corresponds to a symmetric endomorphism
`curvatureOperator r : Module.End ℝ (⋀[ℝ]^2 V)` characterized by
`⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`, with left inverse `ofExteriorEnd`.
Passing from four-tensors to operators on `⋀[ℝ]^2 V` unlocks spectral curvature conditions (such as
positive or nonnegative curvature operator) and diagonalizes the Ricci–Weyl curvature decomposition
into endomorphism blocks.

The image of `curvatureOperator` is `bianchiEndSubmodule V`, the submodule of symmetric
endomorphisms of `⋀[ℝ]^2 V` satisfying the first Bianchi identity, yielding a linear equivalence
`algebraicCurvatureEquivBianchiEnd` taking `constantCurvature V` to `LinearMap.id` and operator
trace to half the scalar curvature (`trace_curvatureOperator`). On a finite-dimensional real inner
product space `V`, `TauCeti.wedgeEnd A B` (normalized so `wedgeEnd id id = id`) pairs on pure wedges
as half the Kulkarni–Nomizu product of `⟪A ·, ·⟫` and `⟪B ·, ·⟫`, identifying Kulkarni–Nomizu
tensors with symmetric wedge products of Riesz endomorphisms.

Finally, for any real normed space `V` of `n := Module.finrank ℝ V`, `algebraicCurvatureSubmodule V`
has `Module.finrank` equal to `n ^ 2 * (n ^ 2 - 1) / 12` (both `0` in infinite dimension). When
`Module.finrank ℝ V = 2` on a real inner product space, sectional polarization forces every
skew-pair (hence every algebraic curvature) four-tensor to equal
`(scalar r / 2) • constantCurvature V`.

## Main definitions

* `TauCeti.FourTensor.curvatureOperator`: symmetric endomorphism of `⋀[ℝ]^2 V` representing `r` via
  `⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`.
* `TauCeti.FourTensor.ofExteriorEnd`: four-tensor `(u, v, z, w) ↦ ⟪R (u ∧ v), z ∧ w⟫` induced by an
  endomorphism `R` of `⋀[ℝ]^2 V`.
* `TauCeti.FourTensor.IsBianchiEnd`, `TauCeti.FourTensor.bianchiEndSubmodule`: predicate and
  submodule of symmetric endomorphisms of `⋀[ℝ]^2 V` satisfying the first Bianchi identity.
* `TauCeti.FourTensor.algebraicCurvatureEquivBianchiEnd`: linear equivalence
  `algebraicCurvatureSubmodule V ≃ₗ[ℝ] bianchiEndSubmodule V`.

## Main statements

* `TauCeti.FourTensor.isAlgebraicCurvature_ofExteriorEnd_iff`,
  `TauCeti.FourTensor.ofExteriorEnd_curvatureOperator`,
  `TauCeti.FourTensor.curvatureOperator_ofExteriorEnd`: Bianchi characterization and round-trips
  between `curvatureOperator` and `ofExteriorEnd`.
* `TauCeti.FourTensor.scalar_ofExteriorEnd`, `TauCeti.FourTensor.trace_curvatureOperator`:
  `scalar (ofExteriorEnd R) = 2 * trace R` and `trace (curvatureOperator r) = scalar r.1 / 2`.
* `TauCeti.FourTensor.inner_wedgeEnd_ιMulti`, `TauCeti.FourTensor.ofExteriorEnd_wedgeEnd`,
  `TauCeti.FourTensor.curvatureOperator_kulkarniNomizu`: comparison of `wedgeEnd` and
  `kulkarniNomizu`.
* `TauCeti.FourTensor.finrank_bianchiEndSubmodule`,
  `TauCeti.FourTensor.finrank_algebraicCurvatureSubmodule`: rank formula
  `n ^ 2 * (n ^ 2 - 1) / 12` for `n = Module.finrank ℝ V`.
* `TauCeti.FourTensor.eq_smul_constantCurvature_of_finrank_eq_two`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.eq_smul_constantCurvature_of_finrank_eq_two`: in
  dimension `2`, every skew-pair (hence algebraic curvature) tensor is
  `(scalar r / 2) • constantCurvature V`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Sections 1.G and 1.H.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 7–8.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. (2) 167 (2008), 1079–1097, Section 1.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

/-! ### Bivector curvature operators and the self-adjoint Bianchi subspace -/

section Operator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private structure IsPairSymm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (r : FourTensor W) : Prop where
  antisymm_first : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]
  antisymm_last : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]
  swap_pairs : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]
private def pairSymmSubmodule (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] :
    Submodule ℝ (FourTensor W) where
  carrier := {r | IsPairSymm r}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' hr hq := ⟨fun _ _ _ _ ↦ by rw [add_apply, add_apply, hr.antisymm_first,
      hq.antisymm_first, neg_add],
    fun _ _ _ _ ↦ by rw [add_apply, add_apply, hr.antisymm_last, hq.antisymm_last, neg_add],
    fun _ _ _ _ ↦ by rw [add_apply, add_apply, hr.swap_pairs, hq.swap_pairs]⟩
  smul_mem' _ _ hr := ⟨fun _ _ _ _ ↦ by rw [smul_apply, smul_apply, hr.antisymm_first, smul_neg],
    fun _ _ _ _ ↦ by rw [smul_apply, smul_apply, hr.antisymm_last, smul_neg],
    fun _ _ _ _ ↦ by rw [smul_apply, smul_apply, hr.swap_pairs]⟩
omit [FiniteDimensional ℝ V] in
private theorem sub_isCurv (r : algebraicCurvatureSubmodule V) : IsAlgebraicCurvature r.1 :=
  mem_algebraicCurvatureSubmodule.mp r.2
private def toPairSymm : algebraicCurvatureSubmodule V →ₗ[ℝ] pairSymmSubmodule V where
  toFun r := ⟨r.1, (sub_isCurv r).antisymm_first, (sub_isCurv r).antisymm_last,
    (sub_isCurv r).swap_pairs⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def pairSymmToBilin (r : pairSymmSubmodule V) : BilinForm ℝ (⋀[ℝ]^2 V) :=
  r.1.toLinearMap₄.exteriorSquareBilinear
    (fun u z w ↦ by simpa using apply_self_first_of_antisymm r.2.antisymm_first u z w)
    (fun u v z ↦ by simpa using apply_self_last_of_antisymm r.2.antisymm_last u v z)
omit [FiniteDimensional ℝ V] in
@[simp] private theorem pairSymmToBilin_ιMulti (r : pairSymmSubmodule V) (u v : Fin 2 → V) :
    pairSymmToBilin r (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
      r.1 ![u 0, u 1, v 0, v 1] := by
  simpa [pairSymmToBilin] using
    LinearMap.exteriorSquareBilinear_ιMulti_ιMulti r.1.toLinearMap₄ _ _ u v
private def ofExteriorBilin : BilinForm ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun B :=
    let w := (exteriorPower.ιMulti ℝ 2 (M := V)).toMultilinearMap.toBilinMap
    ofLinearMap₄ <| LinearMap.mk₂ ℝ (fun u v ↦ w.compr₂ (B (w u v)))
      (fun _ _ _ ↦ by ext; simp [w, map_add]) (fun _ _ _ ↦ by ext; simp [w, map_smul])
      (fun _ _ _ ↦ by ext; simp [w, map_add]) (fun _ _ _ ↦ by ext; simp [w, map_smul])
  map_add' _ _ := toLinearMap₄_injective <| by ext; simp
  map_smul' _ _ := toLinearMap₄_injective <| by ext; simp
@[simp] private theorem ofExteriorBilin_apply (B : BilinForm ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorBilin B ![u, v, z, w] =
      B (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) := by
  simp [ofExteriorBilin]
omit [FiniteDimensional ℝ V] in
private theorem bilin_ext_ιMulti {B₁ B₂ : BilinForm ℝ (⋀[ℝ]^2 V)}
    (h : ∀ u v z w, B₁ (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) =
      B₂ (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w])) : B₁ = B₂ :=
  exteriorPower.linearMap_ext <| AlternatingMap.ext fun u ↦
    exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
      rw [← FinVec.etaExpand_eq u, ← FinVec.etaExpand_eq v]; exact h (u 0) (u 1) (v 0) (v 1)
private def pairSymmEquivSymmBilin :
    pairSymmSubmodule V ≃ₗ[ℝ] TauCeti.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V) where
  toFun r := ⟨pairSymmToBilin r, TauCeti.BilinForm.mem_symmSubmodule.mpr
    ⟨fun x y ↦ congr($(LinearMap.flip_exteriorSquareBilinear _ _ _
      (fun u v z w ↦ by simpa using r.2.swap_pairs u v z w)) y x)⟩⟩
  map_add' _ _ := Subtype.ext <| bilin_ext_ιMulti fun _ _ _ _ ↦ by simp
  map_smul' _ _ := Subtype.ext <| bilin_ext_ιMulti fun _ _ _ _ ↦ by simp
  invFun B := ⟨ofExteriorBilin B.1, ⟨fun u v z w ↦ by simp [exteriorPower.ιMulti_two_swap v u],
    fun u v z w ↦ by simp [exteriorPower.ιMulti_two_swap w z],
    fun _ _ _ _ ↦ by simpa using (TauCeti.BilinForm.mem_symmSubmodule.mp B.2).eq _ _⟩⟩
  left_inv _ := Subtype.ext <| toLinearMap₄_injective <| by ext; simp [ofExteriorBilin_apply]
  right_inv _ := Subtype.ext <| bilin_ext_ιMulti fun _ _ _ _ ↦ by simp
private theorem inner_symmComp (B : BilinForm ℝ (⋀[ℝ]^2 V)) (a b : ⋀[ℝ]^2 V) :
    ⟪B.symmCompOfNondegenerate (innerₗ (⋀[ℝ]^2 V)) TauCeti.nondegenerate_inner a, b⟫ = B a b :=
  B.symmCompOfNondegenerate_left_apply TauCeti.nondegenerate_inner b a

/-- The curvature operator on `⋀[ℝ]^2 V` associated with an algebraic curvature tensor `r`,
characterized by `⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`. -/
def curvatureOperator : algebraicCurvatureSubmodule V →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) where
  toFun r := (pairSymmEquivSymmBilin (toPairSymm r)).1.symmCompOfNondegenerate (innerₗ _)
    TauCeti.nondegenerate_inner
  map_add' _ _ := exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp [inner_add_left, inner_symmComp]
  map_smul' _ _ := exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp [real_inner_smul_left, inner_symmComp]

/-- Pairing `curvatureOperator r` on pure wedges `u ∧ v` and `z ∧ w` recovers `r ![u, v, z, w]`. -/
@[simp] theorem inner_curvatureOperator_ιMulti (r : algebraicCurvatureSubmodule V) (u v z w : V) :
    ⟪curvatureOperator r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r.1 ![u, v, z, w] :=
  (inner_symmComp (pairSymmEquivSymmBilin (toPairSymm r)).1 _ _).trans
    (pairSymmToBilin_ιMulti (toPairSymm r) ![u, v] ![z, w])

/-- `curvatureOperator r` is uniquely characterized by its pairings on decomposable bivectors. -/
theorem curvatureOperator_eq_iff (r : algebraicCurvatureSubmodule V)
    (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureOperator r = A ↔ ∀ u v z w : V,
      ⟪A (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ =
        r.1 ![u, v, z, w] :=
  ⟨fun h ↦ h ▸ inner_curvatureOperator_ιMulti r, fun h ↦
    exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
      rw [inner_curvatureOperator_ιMulti, h]⟩

/-- Passing from an algebraic curvature tensor to its curvature operator is injective. -/
theorem curvatureOperator_injective : Function.Injective (curvatureOperator (V := V)) :=
  fun _ _ h ↦ Subtype.ext <| toLinearMap₄_injective <| by
    ext u v z w; simpa only [toLinearMap₄_apply, inner_curvatureOperator_ιMulti] using
      congr(⟪$h (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫)
/-- `curvatureOperator r` vanishes if and only if `r = 0`. -/
@[simp] theorem curvatureOperator_eq_zero_iff {r : algebraicCurvatureSubmodule V} :
    curvatureOperator r = 0 ↔ r = 0 := map_eq_zero_iff _ curvatureOperator_injective
/-- The curvature operator of `constantCurvature V` is the identity on `⋀[ℝ]^2 V`. -/
@[simp] theorem curvatureOperator_constantCurvature :
    curvatureOperator ⟨constantCurvature V,
      mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature⟩ =
      LinearMap.id :=
  (curvatureOperator_eq_iff _ _).mpr fun _ _ _ _ ↦ by simp [exteriorPower.inner_ιMulti_two]

/-- The curvature operator of an algebraic curvature tensor is symmetric on `⋀[ℝ]^2 V`. -/
theorem isSymmetric_curvatureOperator (r : algebraicCurvatureSubmodule V) :
    (curvatureOperator r).IsSymmetric := fun a b ↦ by
  have hsymm := TauCeti.BilinForm.mem_symmSubmodule.mp (pairSymmEquivSymmBilin (toPairSymm r)).2
  dsimp only [curvatureOperator, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_symmComp, real_inner_comm _ a, inner_symmComp]; exact hsymm.eq a b

/-- An endomorphism of `⋀[ℝ]^2 V` is a *Bianchi endomorphism* if it is symmetric for the Gram inner
product and its pure-bivector pairings satisfy the first Bianchi identity. -/
structure IsBianchiEnd (R : Module.End ℝ (⋀[ℝ]^2 V)) : Prop where
  /-- Symmetry with respect to the Gram inner product on `⋀[ℝ]^2 V`. -/
  isSymmetric : R.IsSymmetric
  /-- The first Bianchi identity on decomposable bivectors. -/
  cyclic_eq_zero : ∀ u v z w : V,
    ⟪R (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ +
      ⟪R (exteriorPower.ιMulti ℝ 2 ![v, z]), exteriorPower.ιMulti ℝ 2 ![u, w]⟫ +
      ⟪R (exteriorPower.ιMulti ℝ 2 ![z, u]), exteriorPower.ιMulti ℝ 2 ![v, w]⟫ = 0

variable (V) in
/-- The submodule of symmetric endomorphisms of `⋀[ℝ]^2 V` satisfying the first Bianchi identity. -/
def bianchiEndSubmodule : Submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V)) where
  carrier := {R | IsBianchiEnd R}
  zero_mem' := ⟨LinearMap.IsSymmetric.zero, fun _ _ _ _ ↦ by simp⟩
  add_mem' hR hS := ⟨hR.isSymmetric.add hS.isSymmetric, fun u v z w ↦ by
    simp only [LinearMap.add_apply, inner_add_left]
    linear_combination hR.cyclic_eq_zero u v z w + hS.cyclic_eq_zero u v z w⟩
  smul_mem' c _ hR := ⟨hR.isSymmetric.smul (conj_trivial c), fun u v z w ↦ by
    simp only [LinearMap.smul_apply, real_inner_smul_left]
    linear_combination c * hR.cyclic_eq_zero u v z w⟩

/-- Membership in `bianchiEndSubmodule V` is `IsBianchiEnd`. -/
@[simp] theorem mem_bianchiEndSubmodule {R : Module.End ℝ (⋀[ℝ]^2 V)} :
    R ∈ bianchiEndSubmodule V ↔ IsBianchiEnd R := Iff.rfl
/-- The identity endomorphism on `⋀[ℝ]^2 V` lies in the Bianchi subspace. -/
theorem isBianchiEnd_id : IsBianchiEnd (LinearMap.id : Module.End ℝ (⋀[ℝ]^2 V)) :=
  ⟨LinearMap.IsSymmetric.id, fun u v z w ↦ by
    simp only [LinearMap.id_apply, exteriorPower.inner_ιMulti_two,
      real_inner_comm v u, real_inner_comm z u, real_inner_comm z v]; ring⟩
/-- Every algebraic curvature tensor induces a Bianchi endomorphism on `⋀[ℝ]^2 V`. -/
theorem isBianchiEnd_curvatureOperator (r : algebraicCurvatureSubmodule V) :
    IsBianchiEnd (curvatureOperator r) :=
  ⟨isSymmetric_curvatureOperator r, fun u v z w ↦ by
    simpa only [inner_curvatureOperator_ιMulti] using (sub_isCurv r).cyclic_eq_zero u v z w⟩

/-- Reconstruct a four-tensor from an endomorphism of `⋀[ℝ]^2 V` via pure-bivector pairings:
`(u, v, z, w) ↦ ⟪R (u ∧ v), z ∧ w⟫`. -/
def ofExteriorEnd : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun R := ofExteriorBilin (innerₗ (⋀[ℝ]^2 V) ∘ₗ R)
  map_add' _ _ := toLinearMap₄_injective <| by ext; simp
  map_smul' _ _ := toLinearMap₄_injective <| by ext; simp

/-- `ofExteriorEnd R` evaluates on `(u, v, z, w)` to `⟪R (u ∧ v), z ∧ w⟫`. -/
@[simp] theorem ofExteriorEnd_apply (R : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd R ![u, v, z, w] =
      ⟪R (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ := by
  simp [ofExteriorEnd]
/-- Reconstructing a four-tensor from an endomorphism of `⋀[ℝ]^2 V` is injective. -/
theorem ofExteriorEnd_injective : Function.Injective (ofExteriorEnd (V := V)) :=
  fun _ _ h ↦ exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    simpa only [ofExteriorEnd_apply] using congr($h ![u, v, z, w])
/-- `ofExteriorEnd R` vanishes if and only if `R = 0`. -/
@[simp] theorem ofExteriorEnd_eq_zero_iff {R : Module.End ℝ (⋀[ℝ]^2 V)} :
    ofExteriorEnd R = 0 ↔ R = 0 := map_eq_zero_iff _ ofExteriorEnd_injective
/-- Pairing pure bivectors against the identity on `⋀[ℝ]^2 V` gives `constantCurvature V`. -/
@[simp] theorem ofExteriorEnd_id :
    ofExteriorEnd (LinearMap.id : Module.End ℝ (⋀[ℝ]^2 V)) = constantCurvature V :=
  toLinearMap₄_injective <| by ext u v z w; simp [exteriorPower.inner_ιMulti_two]
/-- Applying `ofExteriorEnd` to `curvatureOperator r` recovers `r.1`. -/
@[simp] theorem ofExteriorEnd_curvatureOperator (r : algebraicCurvatureSubmodule V) :
    ofExteriorEnd (curvatureOperator r) = r.1 :=
  toLinearMap₄_injective <| by ext u v z w; simp
/-- Taking `curvatureOperator` of `ofExteriorEnd R` (when it is a curvature tensor) recovers `R`. -/
@[simp] theorem curvatureOperator_ofExteriorEnd (R : Module.End ℝ (⋀[ℝ]^2 V))
    (hr : ofExteriorEnd R ∈ algebraicCurvatureSubmodule V) :
    curvatureOperator ⟨ofExteriorEnd R, hr⟩ = R :=
  (curvatureOperator_eq_iff _ R).mpr fun u v z w ↦ (ofExteriorEnd_apply R u v z w).symm

/-- A Bianchi endomorphism of `⋀[ℝ]^2 V` defines an algebraic curvature tensor via
`ofExteriorEnd`. -/
theorem IsBianchiEnd.isAlgebraicCurvature_ofExteriorEnd {R : Module.End ℝ (⋀[ℝ]^2 V)}
    (hR : IsBianchiEnd R) : IsAlgebraicCurvature (ofExteriorEnd R) where
  antisymm_first u v z w := by simp [exteriorPower.ιMulti_two_swap v u]
  antisymm_last u v z w := by simp [exteriorPower.ιMulti_two_swap w z]
  swap_pairs u v z w := by simp only [ofExteriorEnd_apply]; rw [hR.isSymmetric, real_inner_comm]
  cyclic_eq_zero u v z w := by simp [hR.cyclic_eq_zero u v z w]

/-- `ofExteriorEnd R` is an algebraic curvature tensor iff `R` is a Bianchi endomorphism. -/
@[simp] theorem isAlgebraicCurvature_ofExteriorEnd_iff {R : Module.End ℝ (⋀[ℝ]^2 V)} :
    IsAlgebraicCurvature (ofExteriorEnd R) ↔ IsBianchiEnd R := by
  refine ⟨fun h ↦ ⟨?_, fun u v z w ↦ by simpa using h.cyclic_eq_zero u v z w⟩,
    IsBianchiEnd.isAlgebraicCurvature_ofExteriorEnd⟩
  have hbil : innerₗ (⋀[ℝ]^2 V) ∘ₗ R = (innerₗ (⋀[ℝ]^2 V) ∘ₗ R).flip :=
    bilin_ext_ιMulti fun u v z w ↦ by simpa using h.swap_pairs u v z w
  exact fun x y ↦ by simpa [real_inner_comm] using congr($hbil x y)

variable (V) in
/-- **Algebraic curvature tensors correspond to symmetric Bianchi endomorphisms of `⋀[ℝ]^2 V`.**
The forward map is `curvatureOperator` and the inverse is `ofExteriorEnd`. -/
def algebraicCurvatureEquivBianchiEnd :
    algebraicCurvatureSubmodule V ≃ₗ[ℝ] bianchiEndSubmodule V where
  toFun r := ⟨curvatureOperator r, isBianchiEnd_curvatureOperator r⟩
  map_add' r q := Subtype.ext (curvatureOperator.map_add r q)
  map_smul' c r := Subtype.ext (curvatureOperator.map_smul c r)
  invFun R := ⟨ofExteriorEnd R.1,
    mem_algebraicCurvatureSubmodule.mpr R.2.isAlgebraicCurvature_ofExteriorEnd⟩
  left_inv r := Subtype.ext (ofExteriorEnd_curvatureOperator r)
  right_inv R := Subtype.ext (curvatureOperator_ofExteriorEnd R.1 _)

/-- `algebraicCurvatureEquivBianchiEnd` acts as `curvatureOperator`. -/
@[simp] theorem coe_algebraicCurvatureEquivBianchiEnd_apply (r : algebraicCurvatureSubmodule V) :
    (algebraicCurvatureEquivBianchiEnd V r : Module.End ℝ (⋀[ℝ]^2 V)) = curvatureOperator r := (rfl)
/-- `algebraicCurvatureEquivBianchiEnd.symm` acts as `ofExteriorEnd`. -/
@[simp] theorem coe_algebraicCurvatureEquivBianchiEnd_symm_apply (R : bianchiEndSubmodule V) :
    (algebraicCurvatureEquivBianchiEnd V |>.symm R : FourTensor V) = ofExteriorEnd R.1 := (rfl)
/-- The image of `curvatureOperator` in `Module.End ℝ (⋀[ℝ]^2 V)` is `bianchiEndSubmodule V`. -/
theorem range_curvatureOperator :
    LinearMap.range (curvatureOperator (V := V)) = bianchiEndSubmodule V := by
  ext R; refine ⟨fun ⟨r, hr⟩ ↦ hr ▸ isBianchiEnd_curvatureOperator r, fun hR ↦
    ⟨(algebraicCurvatureEquivBianchiEnd V).symm ⟨R, hR⟩,
      congrArg Subtype.val ((algebraicCurvatureEquivBianchiEnd V).apply_symm_apply ⟨R, hR⟩)⟩⟩

private theorem sum_inner_ιMulti_smul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (y : ⋀[ℝ]^2 V) :
    ∑ j, ∑ i, ⟪y, exteriorPower.ιMulti ℝ 2 ![b i, b j]⟫ •
      exteriorPower.ιMulti ℝ 2 ![b i, b j] = (2 : ℝ) • y := by
  refine exteriorPower.ext_inner_ιMulti_two fun u v ↦ ?_
  let w := (exteriorPower.ιMulti ℝ 2 (M := V)).toMultilinearMap.toBilinMap
  have hw (x z : V) :
      ∑ j, ∑ i, (⟪b i, x⟫ * ⟪b j, z⟫) * ⟪y, exteriorPower.ιMulti ℝ 2 ![b i, b j]⟫ =
        ⟪y, exteriorPower.ιMulti ℝ 2 ![x, z]⟫ := by
    have hlin : ∑ j, ∑ i, (⟪b i, x⟫ * ⟪b j, z⟫) • w (b i) (b j) = w x z := by
      conv_rhs => rw [← b.sum_repr' x, ← b.sum_repr' z]
      simp_rw [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_smul,
        mul_comm ⟪b _, z⟫]
    have h := congr(⟪y, $hlin⟫); dsimp only [w] at h
    simpa only [inner_sum, real_inner_smul_right, MultilinearMap.toBilinMap_apply,
      AlternatingMap.coe_multilinearMap] using h
  simp_rw [sum_inner, real_inner_smul_left, exteriorPower.inner_ιMulti_two, mul_sub,
    Finset.sum_sub_distrib, mul_comm ⟪y, _⟫]
  rw [hw u v, hw v u, exteriorPower.ιMulti_two_swap v u, inner_neg_right]; ring

/-- The scalar contraction of `ofExteriorEnd R` is twice the trace of `R` on `⋀[ℝ]^2 V`. -/
@[simp] theorem scalar_ofExteriorEnd (R : Module.End ℝ (⋀[ℝ]^2 V)) :
    scalar (ofExteriorEnd R) = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) R := by
  let b := stdOrthonormalBasis ℝ V
  let B := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  rw [scalar_apply_orthonormalBasis b, R.trace_eq_sum_inner B]
  have hexp (i j) : ofExteriorEnd R ![b i, b j, b i, b j] =
      ∑ a, ⟪R (⟪B a, exteriorPower.ιMulti ℝ 2 ![b i, b j]⟫ •
        exteriorPower.ιMulti ℝ 2 ![b i, b j]), B a⟫ := by
    rw [ofExteriorEnd_apply]
    set w := exteriorPower.ιMulti ℝ 2 ![b i, b j]
    nth_rw 2 [← B.sum_repr' w]
    simp_rw [inner_sum, real_inner_smul_right, map_smul, real_inner_smul_left]
  simp_rw [hexp]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [← sum_inner, ← map_sum, sum_inner_ιMulti_smul b, map_smul, real_inner_smul_left,
    real_inner_comm _ (B _), ← Finset.mul_sum]

/-- The trace of `curvatureOperator r` on `⋀[ℝ]^2 V` is half the scalar contraction of `r`. -/
@[simp] theorem trace_curvatureOperator (r : algebraicCurvatureSubmodule V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureOperator r) = scalar r.1 / 2 := by
  have h := scalar_ofExteriorEnd (curvatureOperator r)
  rw [ofExteriorEnd_curvatureOperator] at h; linarith

/-- Orthogonal equivariance of `curvatureOperator` under a linear isometric equivalence
`e : W ≃ₗᵢ[ℝ] V`, expressed via `pullbackAlgebraicCurvature`. -/
theorem curvatureOperator_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V)
    (r : algebraicCurvatureSubmodule V) :
    curvatureOperator (pullbackAlgebraicCurvature e.toLinearIsometry.toContinuousLinearMap r) =
      (e.toLinearEquiv.exteriorPower 2).symm.conj (curvatureOperator r) := by
  rw [curvatureOperator_eq_iff]; intro u v z w
  have hcancel (y : ⋀[ℝ]^2 V) : exteriorPower.map 2 e.toLinearIsometry.toLinearMap
      ((e.toLinearEquiv.exteriorPower 2).symm y) = y :=
    (e.toLinearEquiv.exteriorPower 2).apply_symm_apply y
  have hf (x : ⋀[ℝ]^2 W) : e.toLinearEquiv.exteriorPower 2 x =
      exteriorPower.map 2 e.toLinearIsometry.toLinearMap x := rfl
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_symm, ← exteriorPower.inner_map_map e.toLinearIsometry, hcancel, hf,
    exteriorPower.map_apply_ιMulti_two, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, inner_curvatureOperator_ιMulti,
    coe_pullbackAlgebraicCurvature_apply]
  exact
    (compContinuousLinearMap_apply_vec r.1 e.toLinearIsometry.toContinuousLinearMap u v z w).symm

/-! ### Comparison of `wedgeEnd` with the Kulkarni–Nomizu product -/

/-- Pairing `wedgeEnd A B (u ∧ v)` with `z ∧ w` gives half the Kulkarni–Nomizu four-tensor of the
bilinear forms `(x, y) ↦ ⟪A x, y⟫` and `(x, y) ↦ ⟪B x, y⟫`. -/
theorem inner_wedgeEnd_ιMulti (A B : Module.End ℝ V) (u v z w : V) :
    ⟪wedgeEnd A B (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ =
      (1 / 2 : ℝ) * kulkarniNomizu (innerₗ V ∘ₗ A) (innerₗ V ∘ₗ B) ![u, v, z, w] := by
  simp only [wedgeEnd_apply_ιMulti, smul_add, inner_add_left, real_inner_smul_left,
    exteriorPower.inner_ιMulti_two, kulkarniNomizu_apply, LinearMap.comp_apply,
    innerₗ_apply_apply]; ring

/-- The four-tensor induced by `wedgeEnd A B` is half the Kulkarni–Nomizu four-tensor of
`⟪A ·, ·⟫` and `⟪B ·, ·⟫`. -/
@[simp] theorem ofExteriorEnd_wedgeEnd (A B : Module.End ℝ V) :
    ofExteriorEnd (wedgeEnd A B) = (1 / 2 : ℝ) • kulkarniNomizu (innerₗ V ∘ₗ A) (innerₗ V ∘ₗ B) :=
  toLinearMap₄_injective <| by ext u v z w; simp only [toLinearMap₄_apply, ofExteriorEnd_apply,
    smul_apply, smul_eq_mul, inner_wedgeEnd_ιMulti]

/-- The symmetric wedge product of two symmetric endomorphisms lies in `bianchiEndSubmodule V`. -/
theorem isBianchiEnd_wedgeEnd {A B : Module.End ℝ V} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    IsBianchiEnd (wedgeEnd A B) := by
  rw [← isAlgebraicCurvature_ofExteriorEnd_iff, ofExteriorEnd_wedgeEnd]
  exact mem_algebraicCurvatureSubmodule.mp <| (algebraicCurvatureSubmodule V).smul_mem (1 / 2 : ℝ)
    (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_kulkarniNomizu
      ⟨fun x y ↦ by simp [hA x y, real_inner_comm]⟩ ⟨fun x y ↦ by simp [hB x y, real_inner_comm]⟩))

/-- For symmetric bilinear forms `h` and `k`, the curvature operator of `kulkarniNomizu h k` is
`2 • wedgeEnd A B`, where `A` and `B` are the Riesz endomorphisms representing `h` and `k`. -/
theorem curvatureOperator_kulkarniNomizu {h k : BilinForm ℝ V} (hh : h.IsSymm) (hk : k.IsSymm) :
    curvatureOperator ⟨kulkarniNomizu h k,
      mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_kulkarniNomizu hh hk)⟩ =
      (2 : ℝ) • wedgeEnd (h.symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner)
        (k.symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner) := by
  rw [curvatureOperator_eq_iff]; intro u v z w
  have H (b : BilinForm ℝ V) :
      innerₗ V ∘ₗ b.symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner = b :=
    LinearMap.ext₂ fun x y ↦ b.symmCompOfNondegenerate_left_apply TauCeti.nondegenerate_inner y x
  rw [LinearMap.smul_apply, real_inner_smul_left, inner_wedgeEnd_ιMulti, H h, H k]; ring

/-! ### Dimension formula and two-dimensional classification -/

private theorem finrank_pairSymmSubmodule : Module.finrank ℝ (pairSymmSubmodule V) =
    Nat.multichoose ((Module.finrank ℝ V).choose 2) 2 := by
  rw [(pairSymmEquivSymmBilin (V := V)).finrank_eq, TauCeti.BilinForm.finrank_symmSubmodule,
    exteriorPower.finrank_eq]
omit [FiniteDimensional ℝ V] in
private theorem cyclic_eq_zero_of_eq (r : FourTensor V) (hr : IsPairSymm r)
    (m : Fin 4 → V) {i j : Fin 4} (hm : m i = m j) (hij : i ≠ j) :
    r ![m 0, m 1, m 2, m 3] + r ![m 1, m 2, m 0, m 3] + r ![m 2, m 0, m 1, m 3] = 0 := by
  wlog hlt : i < j generalizing i j
  · exact this hm.symm hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  have f0 : (⟨0, by decide⟩ : Fin 4) = 0 := rfl
  have f1 : (⟨1, by decide⟩ : Fin 4) = 1 := rfl
  have f2 : (⟨2, by decide⟩ : Fin 4) = 2 := rfl
  have f3 : (⟨3, by decide⟩ : Fin 4) = 3 := rfl
  fin_cases i <;> fin_cases j <;> try exact absurd hlt (by decide)
  all_goals simp only [f0, f1, f2, f3] at hm; rw [hm]
  · linear_combination hr.antisymm_first (m 1) (m 1) (m 2) (m 3) / 2 +
      hr.antisymm_first (m 1) (m 2) (m 1) (m 3)
  · linear_combination hr.antisymm_first (m 2) (m 1) (m 2) (m 3) +
      hr.antisymm_first (m 2) (m 2) (m 1) (m 3) / 2
  · linear_combination hr.swap_pairs (m 3) (m 1) (m 2) (m 3) +
      hr.antisymm_last (m 2) (m 3) (m 1) (m 3) + hr.antisymm_last (m 1) (m 2) (m 3) (m 3) / 2
  · linear_combination hr.antisymm_first (m 0) (m 2) (m 2) (m 3) +
      hr.antisymm_first (m 2) (m 2) (m 0) (m 3) / 2
  · linear_combination hr.antisymm_last (m 0) (m 3) (m 2) (m 3) +
      hr.swap_pairs (m 3) (m 2) (m 0) (m 3) + hr.antisymm_last (m 2) (m 0) (m 3) (m 3) / 2
  · linear_combination hr.antisymm_last (m 0) (m 1) (m 3) (m 3) / 2 +
      hr.antisymm_last (m 1) (m 3) (m 0) (m 3) + hr.swap_pairs (m 3) (m 0) (m 1) (m 3)
private def cyc₁ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
private def cyc₂ : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 0 1
private def bianchiAlternating : pairSymmSubmodule V →ₗ[ℝ] (V [⋀^Fin 4]→ₗ[ℝ] ℝ) where
  toFun r :=
    { toMultilinearMap := r.1.toMultilinearMap + r.1.toMultilinearMap.domDomCongr cyc₁ +
        r.1.toMultilinearMap.domDomCongr cyc₂
      map_eq_zero_of_eq' := fun m _ _ hm hij ↦ by
        have hm0 : r.1 m = r.1 ![m 0, m 1, m 2, m 3] := congrArg r.1 (FinVec.etaExpand_eq m).symm
        have hm1 : (fun i ↦ m (cyc₁ i)) = ![m 1, m 2, m 0, m 3] := by funext k; fin_cases k <;> rfl
        have hm2 : (fun i ↦ m (cyc₂ i)) = ![m 2, m 0, m 1, m 3] := by funext k; fin_cases k <;> rfl
        simpa [hm0, hm1, hm2] using cyclic_eq_zero_of_eq r.1 r.2 m hm hij }
  map_add' _ _ := by ext m; simp; ring
  map_smul' _ _ := by ext m; simp; ring
omit [FiniteDimensional ℝ V] in
@[simp] private theorem bianchiAlternating_apply (r : pairSymmSubmodule V) (m : Fin 4 → V) :
    bianchiAlternating r m = r.1 m + r.1 (fun i ↦ m (cyc₁ i)) + r.1 (fun i ↦ m (cyc₂ i)) := rfl
omit [FiniteDimensional ℝ V] in
private theorem bianchiAlternating_apply_vec (r : pairSymmSubmodule V) (u v z w : V) :
    bianchiAlternating r ![u, v, z, w] =
      r.1 ![u, v, z, w] + r.1 ![v, z, u, w] + r.1 ![z, u, v, w] := by
  have hm1 : (fun i ↦ (![u, v, z, w] : Fin 4 → V) (cyc₁ i)) = ![v, z, u, w] := by
    funext k; fin_cases k <;> rfl
  have hm2 : (fun i ↦ (![u, v, z, w] : Fin 4 → V) (cyc₂ i)) = ![z, u, v, w] := by
    funext k; fin_cases k <;> rfl
  rw [bianchiAlternating_apply, hm1, hm2]
private def alternatingToPairSymm : (V [⋀^Fin 4]→ₗ[ℝ] ℝ) →ₗ[ℝ] pairSymmSubmodule V where
  toFun ω := ⟨(AlternatingMap.toContinuousAlternatingMap ω).toContinuousMultilinearMap,
    ⟨fun u v z w ↦ by
        have h : (![v, u, z, w] : Fin 4 → V) ∘ Equiv.swap 0 1 = ![u, v, z, w] := by
          funext k; fin_cases k <;> rfl
        have hs := ω.map_swap ![v, u, z, w] (i := 0) (j := 1) (by decide)
        rw [h] at hs; simpa using hs,
      fun u v z w ↦ by
        have h : (![u, v, w, z] : Fin 4 → V) ∘ Equiv.swap 2 3 = ![u, v, z, w] := by
          funext k; fin_cases k <;> rfl
        have hs := ω.map_swap ![u, v, w, z] (i := 2) (j := 3) (by decide)
        rw [h] at hs; simpa using hs,
      fun u v z w ↦ by
        let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
        have h : (![z, w, u, v] : Fin 4 → V) ∘ σ = ![u, v, z, w] := by funext k; fin_cases k <;> rfl
        have hp := ω.map_perm ![z, w, u, v] σ
        rw [h, (by decide : Equiv.Perm.sign σ = 1), one_smul] at hp; simpa using hp⟩⟩
  map_add' _ _ := Subtype.ext <| by ext; simp
  map_smul' _ _ := Subtype.ext <| by ext; simp
@[simp] private theorem coe_alternatingToPairSymm_apply (ω : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (m : Fin 4 → V) :
    (alternatingToPairSymm ω : FourTensor V) m = ω m := by simp [alternatingToPairSymm]
private theorem bianchiAlternating_surjective :
    Function.Surjective (bianchiAlternating (V := V)) := fun ω ↦
  ⟨(1 / 3 : ℝ) • alternatingToPairSymm ω, by
    ext m; simp only [map_smul, smul_apply, bianchiAlternating_apply,
      coe_alternatingToPairSymm_apply, smul_eq_mul]
    rw [← Function.comp_def m cyc₁, ← Function.comp_def m cyc₂, ω.map_perm m cyc₁,
      ω.map_perm m cyc₂, (by decide : Equiv.Perm.sign cyc₁ = 1),
      (by decide : Equiv.Perm.sign cyc₂ = 1), one_smul]; ring⟩
private def kerBianchiEquivAlgebraicCurvature :
    LinearMap.ker (bianchiAlternating (V := V)) ≃ₗ[ℝ] algebraicCurvatureSubmodule V where
  toFun r := ⟨r.1.1, mem_algebraicCurvatureSubmodule.mpr ⟨r.1.2.antisymm_first,
    r.1.2.antisymm_last, r.1.2.swap_pairs, fun u v z w ↦ by
      simpa only [bianchiAlternating_apply_vec, zero_apply] using
        congr($(LinearMap.mem_ker.mp r.2) ![u, v, z, w])⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun r := ⟨toPairSymm r, LinearMap.mem_ker.mpr <| by
    ext m; have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
    rw [hm, bianchiAlternating_apply_vec, zero_apply]; exact (sub_isCurv r).cyclic_eq_zero ..⟩
  left_inv _ := rfl
  right_inv _ := rfl
private theorem choose_four_helper (m : ℕ) :
    24 * (m + 3).choose 4 = (m + 3) * (m + 2) * (m + 1) * m := by
  have h := (Nat.descFactorial_eq_factorial_mul_choose (m + 3) 4).symm
  simp [Nat.descFactorial_succ, Nat.factorial] at h; linear_combination h
private theorem sq_mul_sq_sub_one_div_twelve (k : ℕ) :
    ((k + 3) ^ 2 * ((k + 3) ^ 2 - 1)) / 12 = (k + 4).choose 4 + (k + 5).choose 4 := by
  have hsub : (k + 3) ^ 2 - 1 = (k + 4) * (k + 2) := by
    have : (k + 3) ^ 2 = (k + 4) * (k + 2) + 1 := by ring
    omega
  have hmul : (k + 3) ^ 2 * ((k + 4) * (k + 2)) = 12 * ((k + 4).choose 4 + (k + 5).choose 4) :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
      (by linear_combination -choose_four_helper (k + 1) - choose_four_helper (k + 2))
  rw [hsub, hmul, Nat.mul_div_right _ (by decide : 0 < 12)]
private theorem choose_four_add_div_twelve (n : ℕ) :
    n.choose 4 + n ^ 2 * (n ^ 2 - 1) / 12 = Nat.multichoose (n.choose 2) 2 := by
  rcases n with _ | _ | _ | k <;> try (rw [Nat.multichoose_eq]; decide)
  rw [sq_mul_sq_sub_one_div_twelve]
  refine Nat.eq_of_mul_eq_mul_left (by decide : 0 < 24) ?_
  have hc2 : 2 * (k + 3).choose 2 = (k + 3) * (k + 2) := by
    have h := (Nat.descFactorial_eq_factorial_mul_choose (k + 3) 2).symm
    simp [Nat.descFactorial_succ, Nat.factorial] at h; linear_combination h
  have hmc : 2 * Nat.multichoose ((k + 3).choose 2) 2 =
      ((k + 3).choose 2 + 1) * (k + 3).choose 2 := by
    rw [Nat.multichoose_eq, show (k + 3).choose 2 + 2 - 1 = (k + 3).choose 2 + 1 by omega]
    have h := (Nat.descFactorial_eq_factorial_mul_choose ((k + 3).choose 2 + 1) 2).symm
    simp [Nat.descFactorial_succ, Nat.factorial] at h; linear_combination h
  have h24r : 24 * Nat.multichoose ((k + 3).choose 2) 2 =
      3 * (2 * (k + 3).choose 2 + 2) * (2 * (k + 3).choose 2) := by linear_combination 12 * hmc
  rw [h24r, hc2]
  linear_combination choose_four_helper k + choose_four_helper (k + 1) + choose_four_helper (k + 2)
private theorem finrank_algebraicCurvatureSubmodule_of_inner :
    Module.finrank ℝ (algebraicCurvatureSubmodule V) =
      (Module.finrank ℝ V) ^ 2 * ((Module.finrank ℝ V) ^ 2 - 1) / 12 := by
  let eAlt : (V [⋀^Fin 4]→ₗ[ℝ] ℝ) ≃ₗ[ℝ] ⋀[ℝ]^4 V :=
    (exteriorPower.alternatingMapLinearEquiv (R := ℝ) (M := V) (N := ℝ) (n := 4)).trans
      (Module.finBasis ℝ (⋀[ℝ]^4 V)).toDualEquiv.symm
  have hker := LinearMap.finrank_ker_eq_sub_of_surjective (K := ℝ) (M := pairSymmSubmodule V)
    (N := ⋀[ℝ]^4 V) (eAlt.toLinearMap ∘ₗ bianchiAlternating (V := V))
    (eAlt.surjective.comp bianchiAlternating_surjective)
  rwa [eAlt.ker_comp, kerBianchiEquivAlgebraicCurvature.finrank_eq, finrank_pairSymmSubmodule,
    exteriorPower.finrank_eq, ← choose_four_add_div_twelve, Nat.add_sub_cancel_left] at hker

/-- The subspace `bianchiEndSubmodule V` of symmetric Bianchi endomorphisms of `⋀[ℝ]^2 V` has
dimension `n ^ 2 * (n ^ 2 - 1) / 12`. -/
theorem finrank_bianchiEndSubmodule : Module.finrank ℝ (bianchiEndSubmodule V) =
    (Module.finrank ℝ V) ^ 2 * ((Module.finrank ℝ V) ^ 2 - 1) / 12 := by
  rw [← (algebraicCurvatureEquivBianchiEnd V).finrank_eq,
    finrank_algebraicCurvatureSubmodule_of_inner]

/-- **In dimension `2`, every four-tensor antisymmetric in its first and last pairs of arguments is
`(Scal / 2)` times the constant-curvature tensor.** -/
theorem eq_smul_constantCurvature_of_finrank_eq_two (hn : Module.finrank ℝ V = 2) {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    r = (scalar r / 2) • constantCurvature V := by
  set b := (stdOrthonormalBasis ℝ V).reindex (finCongr hn)
  let k := r ![b 0, b 1, b 0, b 1]
  have hrk : r = k • constantCurvature V := by
    have hf0 : (⟨0, by decide⟩ : Fin 2) = 0 := rfl
    have hf1 : (⟨1, by decide⟩ : Fin 2) = 1 := rfl
    apply toLinearMap₄_injective
    refine b.toBasis.ext fun i ↦ b.toBasis.ext fun j ↦ b.toBasis.ext fun p ↦
      b.toBasis.ext fun q ↦ ?_
    simp only [OrthonormalBasis.coe_toBasis, toLinearMap₄_apply, smul_apply, smul_eq_mul,
      constantCurvature_apply]
    by_cases hij : i = j
    · rw [hij]; ring_nf; linarith [hr₁ (b j) (b j) (b p) (b q)]
    by_cases hpq : p = q
    · rw [hpq]; ring_nf; linarith [hr₂ (b i) (b j) (b q) (b q)]
    fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
    all_goals fin_cases p <;> fin_cases q <;> try exact absurd rfl hpq
    all_goals simp only [hf0, hf1, orthonormal_iff_ite.mp b.orthonormal, ↓reduceIte,
      (by decide : (0 : Fin 2) ≠ 1), (by decide : (1 : Fin 2) ≠ 0)]
    · ring
    · linarith [hr₂ (b 0) (b 1) (b 1) (b 0)]
    · linarith [hr₁ (b 1) (b 0) (b 0) (b 1)]
    · linarith [hr₁ (b 1) (b 0) (b 1) (b 0), hr₂ (b 0) (b 1) (b 1) (b 0)]
  have hscal : scalar r = 2 * k := by
    rw [hrk, map_smul, scalar_constantCurvature, hn, smul_eq_mul]; norm_num; ring
  rwa [show k = scalar r / 2 by linarith] at hrk

/-- **In dimension `2`, every algebraic curvature tensor is `(Scal / 2)` times the
constant-curvature tensor.** -/
theorem IsAlgebraicCurvature.eq_smul_constantCurvature_of_finrank_eq_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V = 2) :
    r = (scalar r / 2) • constantCurvature V :=
  FourTensor.eq_smul_constantCurvature_of_finrank_eq_two hn hr.antisymm_first hr.antisymm_last

end Operator

section Dimension

private theorem lt_curv_dim_succ_three (m : ℕ) :
    m < (m + 3) ^ 2 * ((m + 3) ^ 2 - 1) / 12 := by
  have hsq : (m + 3) ^ 2 - 1 = (m + 4) * (m + 2) := by
    have : (m + 3) ^ 2 = (m + 4) * (m + 2) + 1 := by ring
    omega
  rw [hsq, show (m + 3) ^ 2 * ((m + 4) * (m + 2)) =
    m ^ 4 + 12 * m ^ 3 + 53 * m ^ 2 + 102 * m + 72 by ring]
  omega

private theorem exists_retraction_euclideanSpace {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {n : ℕ} {v : Fin n → V} (hv : LinearIndependent ℝ v) :
    ∃ (P : V →L[ℝ] EuclideanSpace ℝ (Fin n)) (J : EuclideanSpace ℝ (Fin n) → V),
      ∀ x, P (J x) = x := by
  classical
  let p : Submodule ℝ V := Submodule.span ℝ (Set.range v)
  let bp : Module.Basis (Fin n) ℝ p := Module.Basis.span hv
  have : FiniteDimensional ℝ p := Module.Finite.of_basis bp
  choose φ hφ using fun i : Fin n ↦
    exists_extension_norm_eq p (bp.coord i).toContinuousLinearMap
  let eE : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  refine ⟨eE.symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi φ),
    fun x ↦ (bp.equivFun.symm (eE x) : V), fun x ↦ eE.injective <| funext fun i ↦ ?_⟩
  simp [-Module.Basis.equivFun_symm_apply, (hφ i).1, ← bp.equivFun_apply]

/-- **Dimension of the space of algebraic curvature tensors.** On any real normed space `V` of
`finrank` `n`, `algebraicCurvatureSubmodule V` has `finrank` `n ^ 2 * (n ^ 2 - 1) / 12` (both sides
being `0` when `V` is infinite-dimensional). -/
theorem finrank_algebraicCurvatureSubmodule {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Module.finrank ℝ (algebraicCurvatureSubmodule V) =
      (Module.finrank ℝ V) ^ 2 * ((Module.finrank ℝ V) ^ 2 - 1) / 12 := by
  by_cases hV : FiniteDimensional ℝ V
  · let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
      ((Module.finBasis ℝ V).equivFun.trans
        (EuclideanSpace.equiv _ ℝ).toLinearEquiv.symm).toContinuousLinearEquiv
    rw [(algebraicCurvatureSubmoduleCongr e).toLinearEquiv.finrank_eq,
      finrank_algebraicCurvatureSubmodule_of_inner, finrank_euclideanSpace_fin]
  · have hnot : ¬ FiniteDimensional ℝ (algebraicCurvatureSubmodule V) := fun _ ↦ by
      let b := Module.Basis.ofVectorSpace ℝ V
      have : Infinite (Module.Basis.ofVectorSpaceIndex ℝ V) :=
        not_finite_iff_infinite.mp fun _ ↦ hV (Module.Finite.of_basis b)
      let m := Module.finrank ℝ (algebraicCurvatureSubmodule V)
      obtain ⟨P, J, hPJ⟩ := exists_retraction_euclideanSpace
        (v := fun k : Fin (m + 3) ↦ b (Infinite.natEmbedding _ k))
        (b.linearIndependent.comp _ ((Infinite.natEmbedding _).injective.comp Fin.val_injective))
      have hle := LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (pullbackAlgebraicCurvature P).toLinearMap from
          pullbackAlgebraicCurvature_injective P hPJ)
      rw [finrank_algebraicCurvatureSubmodule_of_inner, finrank_euclideanSpace_fin] at hle
      exact not_lt_of_ge hle (lt_curv_dim_succ_three m)
    rw [Module.finrank_of_infinite_dimensional hnot, Module.finrank_of_infinite_dimensional hV]; rfl

end Dimension

end TauCeti.FourTensor
