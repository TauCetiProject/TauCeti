/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Dimension
public import TauCeti.Analysis.InnerProductSpace.BilinearForm.End
public import TauCeti.LinearAlgebra.ExteriorPower.SymmetricProduct
import Mathlib.Tactic.Ring
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Algebraic curvature tensors as operators on bivectors

On a finite-dimensional real inner product space `V`, every `r : FourTensor V` induces a bivector
operator `curvatureEndomorphism r : Module.End ℝ (⋀[ℝ]^2 V)` via `TauCeti.bilinFormToEnd`, and
every endomorphism `T : Module.End ℝ (⋀[ℝ]^2 V)` induces a pair-antisymmetric four-tensor
`TauCeti.FourTensor.ofExteriorEnd T` with `ofExteriorEnd T ![u, v, z, w] = ⟪T (u ∧ v), z ∧ w⟫`.
For any pair-antisymmetric `r`, `⟪curvatureEndomorphism r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`.
Restricting these two-sided inverses to `algebraicCurvatureSubmodule V` gives the linear
equivalence `curvatureEndomorphismEquiv` onto `algebraicCurvatureEndomorphismSubmodule V`
(`Sym²_B(⋀²V)`), with `finrank = n²(n² - 1) / 12`.

Under this dictionary, `curvatureEndomorphism (kulkarniNomizu h k) =
2 • exteriorPower.symmMap₂ (bilinFormToEnd h) (bilinFormToEnd k)`, and for any pair-antisymmetric
`r`, `2 * tr(curvatureEndomorphism r ∘ symmMap₂ A id) = bilinFormTrace ((ricci r).compLeft A)`.

## Main definitions

* `TauCeti.FourTensor.curvatureEndomorphism`, `TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism`,
  `TauCeti.FourTensor.algebraicCurvatureEndomorphismSubmodule`, `TauCeti.FourTensor.ofExteriorEnd`,
  and `TauCeti.FourTensor.curvatureEndomorphismEquiv`.

## Main results

* `TauCeti.FourTensor.inner_curvatureEndomorphism_ιMulti_of_antisymm`,
  `TauCeti.FourTensor.isSymmetric_curvatureEndomorphism_of_swap_pairs`,
  `TauCeti.FourTensor.isAlgebraicCurvature_ofExteriorEnd_iff`,
  `TauCeti.FourTensor.curvatureEndomorphism_ofExteriorEnd`,
  `TauCeti.FourTensor.ofExteriorEnd_curvatureEndomorphism_of_antisymm`,
  `TauCeti.FourTensor.coe_curvatureEndomorphismEquiv_symm`,
  `TauCeti.FourTensor.curvatureEndomorphism_kulkarniNomizu`,
  `TauCeti.FourTensor.curvatureEndomorphism_kulkarniNomizu_innerₗ_comp`,
  `TauCeti.FourTensor.curvatureEndomorphism_constantCurvature`,
  `TauCeti.FourTensor.two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id_of_antisymm`,
  `TauCeti.FourTensor.scalar_eq_two_mul_trace_curvatureEndomorphism_of_antisymm`,
  `ContinuousLinearMap.curvatureEndomorphism_compContinuousLinearMap`,
  `ContinuousLinearMap.inner_curvatureEndomorphism_compContinuousLinearMap`, and
  `LinearIsometryEquiv.map_comp_curvatureEndomorphism_compContinuousLinearMap`.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. 167 (2008), 1079–1097, Section 2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def pairAltLinearMap₄ (r : FourTensor V) : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  let T : V →ₗ[ℝ] V →ₗ[ℝ] BilinForm ℝ V := toLinearMap₄ r
  let S := T + (-1 : ℝ) • T.compr₂ LinearMap.BilinForm.flipHom.toLinearMap
  (1 / 4 : ℝ) • (S + (-1 : ℝ) • S.flip)

private theorem pairAltLinearMap₄_apply (r : FourTensor V) (u v z w : V) :
    pairAltLinearMap₄ r u v z w =
      (1 / 4 : ℝ) * (r ![u, v, z, w] - r ![u, v, w, z] - r ![v, u, z, w] + r ![v, u, w, z]) := by
  simp [pairAltLinearMap₄]; ring

private theorem pairAltLinearMap₄_isAlt (r : FourTensor V) (u v : V) :
    (pairAltLinearMap₄ r u v).IsAlt := fun _ ↦ by rw [pairAltLinearMap₄_apply]; ring

private def exteriorCurvatureForm (r : FourTensor V) : BilinForm ℝ (⋀[ℝ]^2 V) :=
  (pairAltLinearMap₄ r).exteriorSquareBilinear
    (fun _ _ _ ↦ by rw [pairAltLinearMap₄_apply]; ring) (pairAltLinearMap₄_isAlt r)

variable [FiniteDimensional ℝ V]

/-- The bivector endomorphism of `r : FourTensor V`, pairing as the pair-antisymmetrization of `r`
on pure wedges (agreeing with `r ![u, v, z, w]` when `r` is pair-antisymmetric). -/
def curvatureEndomorphism : FourTensor V →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) where
  toFun r := bilinFormToEnd (exteriorCurvatureForm r)
  map_add' _ _ := exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp [inner_add_left, exteriorCurvatureForm, pairAltLinearMap₄_apply]; ring
  map_smul' _ _ := exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp [real_inner_smul_left, exteriorCurvatureForm, pairAltLinearMap₄_apply]; ring

private theorem curvatureEndomorphism_apply (r : FourTensor V) :
    curvatureEndomorphism r = bilinFormToEnd (exteriorCurvatureForm r) := rfl

/-- Pure-wedge pairing of `curvatureEndomorphism r` for an arbitrary four-tensor `r`. -/
theorem inner_curvatureEndomorphism_ιMulti (r : FourTensor V) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ =
      (1 / 4 : ℝ) * (r ![u, v, z, w] - r ![u, v, w, z] - r ![v, u, z, w] + r ![v, u, w, z]) := by
  simp [curvatureEndomorphism_apply, exteriorCurvatureForm, pairAltLinearMap₄_apply]

/-- Pure-wedge pairing of `curvatureEndomorphism r` for pair-antisymmetric `r`. -/
theorem inner_curvatureEndomorphism_ιMulti_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] := by
  rw [inner_curvatureEndomorphism_ιMulti, h₂ u v w z, h₁ v u z w, h₁ v u w z, h₂ u v w z]; ring

/-- Pure-wedge pairing of `curvatureEndomorphism r` for bivector-symmetric `r`. -/
theorem IsBivectorSymmetric.inner_curvatureEndomorphism_ιMulti {r : FourTensor V}
    (hr : IsBivectorSymmetric r) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  inner_curvatureEndomorphism_ιMulti_of_antisymm hr.antisymm_first hr.antisymm_last u v z w

/-- Pure-wedge pairing of `curvatureEndomorphism r` for an algebraic curvature tensor `r`. -/
theorem IsAlgebraicCurvature.inner_curvatureEndomorphism_ιMulti {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  hr.isBivectorSymmetric.inner_curvatureEndomorphism_ιMulti u v z w

/-- If a four-tensor is symmetric under pair interchange, its bivector operator is symmetric. -/
theorem isSymmetric_curvatureEndomorphism_of_swap_pairs {r : FourTensor V}
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) :
    (curvatureEndomorphism r).IsSymmetric := by
  rw [curvatureEndomorphism_apply, isSymmetric_bilinFormToEnd_iff]
  exact ⟨fun a b ↦ (LinearMap.congr_fun₂ (LinearMap.flip_exteriorSquareBilinear
    (pairAltLinearMap₄ r) _ _ fun u v z w ↦ by
      simp only [pairAltLinearMap₄_apply, hswap u v z w, hswap u v w z, hswap v u z w,
        hswap v u w z]; ring) a b).symm⟩

/-- The bivector endomorphism of a bivector-symmetric four-tensor is symmetric. -/
theorem IsBivectorSymmetric.isSymmetric_curvatureEndomorphism {r : FourTensor V}
    (hr : IsBivectorSymmetric r) : (curvatureEndomorphism r).IsSymmetric :=
  isSymmetric_curvatureEndomorphism_of_swap_pairs hr.swap_pairs

/-- The bivector endomorphism of an algebraic curvature tensor is symmetric. -/
theorem IsAlgebraicCurvature.isSymmetric_curvatureEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (curvatureEndomorphism r).IsSymmetric :=
  hr.isBivectorSymmetric.isSymmetric_curvatureEndomorphism

/-- The bivector endomorphism of an algebraic curvature tensor satisfies the first Bianchi law. -/
theorem IsAlgebraicCurvature.curvatureEndomorphism_cyclic_eq_zero {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ +
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![v, z]), exteriorPower.ιMulti ℝ 2 ![u, w]⟫ +
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![z, u]), exteriorPower.ιMulti ℝ 2 ![v, w]⟫ =
      0 := by
  simp only [hr.inner_curvatureEndomorphism_ιMulti]; exact hr.cyclic_eq_zero u v z w

/-- Predicate characterizing bivector operators `L ∈ Sym²_B(⋀²V)`: symmetric and Bianchi. -/
structure IsAlgebraicCurvatureEndomorphism (L : Module.End ℝ (⋀[ℝ]^2 V)) : Prop where
  /-- Self-adjointness with respect to the Gram inner product on `⋀[ℝ]^2 V`. -/
  isSymmetric : L.IsSymmetric
  /-- The first Bianchi identity on pure wedges. -/
  cyclic_eq_zero : ∀ u v z w,
    ⟪L (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ +
    ⟪L (exteriorPower.ιMulti ℝ 2 ![v, z]), exteriorPower.ιMulti ℝ 2 ![u, w]⟫ +
    ⟪L (exteriorPower.ιMulti ℝ 2 ![z, u]), exteriorPower.ιMulti ℝ 2 ![v, w]⟫ = 0

variable (V) in
/-- The submodule `Sym²_B(⋀²V)` of self-adjoint Bianchi endomorphisms of `⋀[ℝ]^2 V`. -/
def algebraicCurvatureEndomorphismSubmodule : Submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V)) where
  carrier := {L | IsAlgebraicCurvatureEndomorphism L}
  zero_mem' := ⟨LinearMap.IsSymmetric.zero, fun _ _ _ _ ↦ by simp⟩
  add_mem' h₁ h₂ := ⟨h₁.isSymmetric.add h₂.isSymmetric, fun u v z w ↦ by
    simp only [LinearMap.add_apply, inner_add_left]
    linear_combination h₁.cyclic_eq_zero u v z w + h₂.cyclic_eq_zero u v z w⟩
  smul_mem' c _ h := ⟨LinearMap.IsSymmetric.smul (star_trivial c) h.isSymmetric, fun u v z w ↦ by
    simp only [LinearMap.smul_apply, real_inner_smul_left]
    linear_combination c * h.cyclic_eq_zero u v z w⟩

/-- Membership in `algebraicCurvatureEndomorphismSubmodule V`. -/
@[simp] theorem mem_algebraicCurvatureEndomorphismSubmodule {L : Module.End ℝ (⋀[ℝ]^2 V)} :
    L ∈ algebraicCurvatureEndomorphismSubmodule V ↔ IsAlgebraicCurvatureEndomorphism L := (Iff.rfl)

/-- The four-tensor `(u, v, z, w) ↦ ⟪T (u ∧ v), z ∧ w⟫` associated to an endomorphism `T` of the
exterior square `⋀[ℝ]^2 V`. With this convention the identity on `⋀[ℝ]^2 V` maps to
`constantCurvature V`. -/
def ofExteriorEnd : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V :=
  fourTensorOfExteriorBilin.comp TauCeti.bilinFormToEnd.symm.toLinearMap

/-- Evaluation of the four-tensor associated to an endomorphism of `⋀[ℝ]^2 V`. -/
@[simp]
theorem ofExteriorEnd_apply (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] =
      ⟪T (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ := by
  simp [ofExteriorEnd]

/-- The four-tensor of an endomorphism of `⋀[ℝ]^2 V` is antisymmetric in its first pair. -/
theorem ofExteriorEnd_antisymm_first (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] = -ofExteriorEnd T ![v, u, z, w] := by
  rw [ofExteriorEnd_apply, ofExteriorEnd_apply, exteriorPower.ιMulti_two_swap v u, map_neg,
    inner_neg_left]

/-- The four-tensor of an endomorphism of `⋀[ℝ]^2 V` is antisymmetric in its last pair. -/
theorem ofExteriorEnd_antisymm_last (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd T ![u, v, z, w] = -ofExteriorEnd T ![u, v, w, z] := by
  rw [ofExteriorEnd_apply, ofExteriorEnd_apply, exteriorPower.ιMulti_two_swap w z, inner_neg_right]

/-- Pair-interchange symmetry of `ofExteriorEnd T` is equivalent to symmetry of `T` on
`⋀[ℝ]^2 V`. -/
theorem ofExteriorEnd_swap_pairs_iff (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    (∀ u v z w, ofExteriorEnd T ![u, v, z, w] = ofExteriorEnd T ![z, w, u, v]) ↔
      T.IsSymmetric := by
  refine ⟨fun h a b ↦ ?_, fun h u v z w ↦ by
    simp only [ofExteriorEnd_apply]; rw [h, real_inner_comm]⟩
  have hbil : (innerₗ (⋀[ℝ]^2 V)).compl₁₂ T LinearMap.id = (innerₗ (⋀[ℝ]^2 V)).compl₂ T :=
    exteriorPower.linearMap_ext_ιMulti_two fun u v ↦
      exteriorPower.linearMap_ext_ιMulti_two fun z w ↦ by
        simp only [LinearMap.compl₁₂_apply, LinearMap.compl₂_apply, LinearMap.id_apply,
          innerₗ_apply_apply]
        rw [real_inner_comm (T (exteriorPower.ιMulti ℝ 2 ![z, w]))]
        simpa only [ofExteriorEnd_apply] using h u v z w
  simpa using LinearMap.congr_fun₂ hbil a b

/-- `ofExteriorEnd T` is an algebraic curvature tensor iff `IsAlgebraicCurvatureEndomorphism T`. -/
@[simp]
theorem isAlgebraicCurvature_ofExteriorEnd_iff (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    IsAlgebraicCurvature (ofExteriorEnd T) ↔ IsAlgebraicCurvatureEndomorphism T :=
  ⟨fun h ↦ ⟨(ofExteriorEnd_swap_pairs_iff T).mp h.swap_pairs, fun u v z w ↦ by
      simpa only [ofExteriorEnd_apply] using h.cyclic_eq_zero u v z w⟩,
   fun h ↦ ⟨ofExteriorEnd_antisymm_first T, ofExteriorEnd_antisymm_last T,
     (ofExteriorEnd_swap_pairs_iff T).mpr h.isSymmetric, fun u v z w ↦ by
       simpa only [ofExteriorEnd_apply] using h.cyclic_eq_zero u v z w⟩⟩

/-- `curvatureEndomorphism` is a left inverse to `ofExteriorEnd`. -/
@[simp]
theorem curvatureEndomorphism_ofExteriorEnd (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureEndomorphism (ofExteriorEnd T) = T :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    rw [inner_curvatureEndomorphism_ιMulti_of_antisymm (ofExteriorEnd_antisymm_first T)
      (ofExteriorEnd_antisymm_last T), ofExteriorEnd_apply]

/-- On pair-antisymmetric four-tensors, `ofExteriorEnd` and `curvatureEndomorphism` are inverses. -/
theorem ofExteriorEnd_curvatureEndomorphism_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    ofExteriorEnd (curvatureEndomorphism r) = r := by
  refine ext_vec fun u v z w ↦ ?_
  rw [ofExteriorEnd_apply, inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂]

/-- On bivector-symmetric four-tensors, `ofExteriorEnd (curvatureEndomorphism r) = r`. -/
@[simp]
theorem IsBivectorSymmetric.ofExteriorEnd_curvatureEndomorphism {r : FourTensor V}
    (hr : IsBivectorSymmetric r) :
    ofExteriorEnd (curvatureEndomorphism r) = r :=
  ofExteriorEnd_curvatureEndomorphism_of_antisymm hr.antisymm_first hr.antisymm_last

/-- On algebraic curvature tensors, `ofExteriorEnd (curvatureEndomorphism r) = r`. -/
@[simp]
theorem IsAlgebraicCurvature.ofExteriorEnd_curvatureEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ofExteriorEnd (curvatureEndomorphism r) = r :=
  hr.isBivectorSymmetric.ofExteriorEnd_curvatureEndomorphism

/-- Linear equivalence `algebraicCurvatureSubmodule V ≃ₗ[ℝ] Sym²_B(⋀²V)`. -/
def curvatureEndomorphismEquiv :
    algebraicCurvatureSubmodule V ≃ₗ[ℝ] algebraicCurvatureEndomorphismSubmodule V where
  toFun r := ⟨curvatureEndomorphism r.val, mem_algebraicCurvatureEndomorphismSubmodule.mpr
    ⟨(mem_algebraicCurvatureSubmodule.mp r.property).isSymmetric_curvatureEndomorphism,
      (mem_algebraicCurvatureSubmodule.mp r.property).curvatureEndomorphism_cyclic_eq_zero⟩⟩
  invFun L := ⟨ofExteriorEnd L.val, mem_algebraicCurvatureSubmodule.mpr
    ((isAlgebraicCurvature_ofExteriorEnd_iff L.val).mpr L.property)⟩
  map_add' r q := Subtype.ext (map_add curvatureEndomorphism r.val q.val)
  map_smul' c r := Subtype.ext (map_smul curvatureEndomorphism c r.val)
  left_inv r := Subtype.ext
    (mem_algebraicCurvatureSubmodule.mp r.property).ofExteriorEnd_curvatureEndomorphism
  right_inv L := Subtype.ext (curvatureEndomorphism_ofExteriorEnd L.val)

/-- Evaluation of `curvatureEndomorphismEquiv` is `curvatureEndomorphism`. -/
@[simp] theorem coe_curvatureEndomorphismEquiv (r : algebraicCurvatureSubmodule V) :
    (curvatureEndomorphismEquiv r : Module.End ℝ (⋀[ℝ]^2 V)) = curvatureEndomorphism r.val := (rfl)

/-- The inverse of `curvatureEndomorphismEquiv` recovers `ofExteriorEnd`. -/
@[simp] theorem coe_curvatureEndomorphismEquiv_symm
    (L : algebraicCurvatureEndomorphismSubmodule V) :
    (curvatureEndomorphismEquiv.symm L).val = ofExteriorEnd L.val := (rfl)

/-- Evaluation of `curvatureEndomorphismEquiv.symm` on four vectors via pure wedges. -/
theorem curvatureEndomorphismEquiv_symm_apply
    (L : algebraicCurvatureEndomorphismSubmodule V) (u v z w : V) :
    (curvatureEndomorphismEquiv.symm L).val ![u, v, z, w] =
      ⟪L.val (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ := by
  rw [coe_curvatureEndomorphismEquiv_symm, ofExteriorEnd_apply]

/-- `Sym²_B(⋀²V)` has dimension `n ^ 2 * (n ^ 2 - 1) / 12`. -/
theorem finrank_algebraicCurvatureEndomorphismSubmodule :
    Module.finrank ℝ (algebraicCurvatureEndomorphismSubmodule V) =
      Module.finrank ℝ V ^ 2 * (Module.finrank ℝ V ^ 2 - 1) / 12 :=
  curvatureEndomorphismEquiv.finrank_eq.symm.trans finrank_algebraicCurvatureSubmodule

/-- **Dictionary**: `curvatureEndomorphism (kulkarniNomizu h k) = 2 • symmMap₂ h♯ k♯`. -/
theorem curvatureEndomorphism_kulkarniNomizu (h k : BilinForm ℝ V) :
    curvatureEndomorphism (kulkarniNomizu h k) =
      (2 : ℝ) • exteriorPower.symmMap₂ (bilinFormToEnd h) (bilinFormToEnd k) :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    simp [inner_curvatureEndomorphism_ιMulti, kulkarniNomizu_apply, inner_add_left,
      exteriorPower.inner_ιMulti_two]; ring

/-- Lowering endomorphisms `A, B` and taking `kulkarniNomizu` gives `2 • symmMap₂ A B`. -/
theorem curvatureEndomorphism_kulkarniNomizu_innerₗ_comp (A B : Module.End ℝ V) :
    curvatureEndomorphism (kulkarniNomizu ((innerₗ V).comp A) ((innerₗ V).comp B)) =
      (2 : ℝ) • exteriorPower.symmMap₂ A B := by
  rw [curvatureEndomorphism_kulkarniNomizu, A.bilinFormToEnd_innerₗ_comp,
    B.bilinFormToEnd_innerₗ_comp]

/-- The constant-curvature four-tensor acts on `⋀[ℝ]^2 V` as the identity endomorphism. -/
@[simp] theorem curvatureEndomorphism_constantCurvature :
    curvatureEndomorphism (constantCurvature V) = LinearMap.id :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    rw [isAlgebraicCurvature_constantCurvature.inner_curvatureEndomorphism_ιMulti,
      LinearMap.id_apply, constantCurvature_apply, exteriorPower.inner_ιMulti_two]

/-- For pair-antisymmetric `r`, `2 * tr(R ∘ₗ symmMap₂ A id) = tr((ricci r).compLeft A)`. -/
theorem two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (A : Module.End ℝ V) :
    2 * LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism r ∘ₗ exteriorPower.symmMap₂ A LinearMap.id) =
      bilinFormTrace ((ricci r).compLeft A) := by
  let b := stdOrthonormalBasis ℝ V
  rw [← b.sum_inner_ιMulti_two_eq_two_mul_trace, bilinFormTrace_eq_sum _ b]
  have hterm (i j : Fin (Module.finrank ℝ V)) :
      ⟪(curvatureEndomorphism r ∘ₗ exteriorPower.symmMap₂ A LinearMap.id)
          (exteriorPower.ιMulti ℝ 2 ![b i, b j]), exteriorPower.ιMulti ℝ 2 ![b i, b j]⟫ =
        (1 / 2 : ℝ) * (r ![b j, A (b i), b j, b i] + r ![b i, A (b j), b i, b j]) := by
    simp only [LinearMap.comp_apply, exteriorPower.symmMap₂_apply_ιMulti, LinearMap.id_apply,
      map_smul, map_add, real_inner_smul_left, inner_add_left,
      inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂, invOf_eq_inv]
    rw [h₁ (A (b i)) (b j), h₂ (b j) (A (b i))]; ring
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j ↦ r ![b i, A (b j), b i, b j])]
  simp_rw [LinearMap.BilinForm.compLeft_apply, ← ricci_apply_orthonormalBasis b]; ring

/-- Bivector-symmetric specialization of the `symmMap₂ A id` trace identity. -/
theorem IsBivectorSymmetric.two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id
    {r : FourTensor V} (hr : IsBivectorSymmetric r) (A : Module.End ℝ V) :
    2 * LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism r ∘ₗ exteriorPower.symmMap₂ A LinearMap.id) =
      bilinFormTrace ((ricci r).compLeft A) :=
  two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id_of_antisymm hr.antisymm_first
      hr.antisymm_last A

/-- Algebraic-curvature specialization of the `symmMap₂ A id` trace identity. -/
theorem IsAlgebraicCurvature.two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (A : Module.End ℝ V) :
    2 * LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism r ∘ₗ exteriorPower.symmMap₂ A LinearMap.id) =
      bilinFormTrace ((ricci r).compLeft A) :=
  hr.isBivectorSymmetric.two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id A

/-- For pair-antisymmetric `r`, `scalar r = 2 * tr(curvatureEndomorphism r)`. -/
theorem scalar_eq_two_mul_trace_curvatureEndomorphism_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureEndomorphism r) := by
  simpa [scalar_apply] using
    (two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id_of_antisymm h₁ h₂ LinearMap.id).symm

/-- For bivector-symmetric `r`, `scalar r = 2 * tr(curvatureEndomorphism r)`. -/
theorem IsBivectorSymmetric.scalar_eq_two_mul_trace_curvatureEndomorphism {r : FourTensor V}
    (hr : IsBivectorSymmetric r) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureEndomorphism r) :=
  scalar_eq_two_mul_trace_curvatureEndomorphism_of_antisymm hr.antisymm_first hr.antisymm_last

/-- For an algebraic curvature tensor `r`, `scalar r = 2 * tr(curvatureEndomorphism r)`. -/
theorem IsAlgebraicCurvature.scalar_eq_two_mul_trace_curvatureEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureEndomorphism r) :=
  hr.isBivectorSymmetric.scalar_eq_two_mul_trace_curvatureEndomorphism

end TauCeti.FourTensor

namespace ContinuousLinearMap

open TauCeti TauCeti.FourTensor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- Pulling back a four-tensor along a continuous linear map `f : W →L[ℝ] V` pulls back
`curvatureEndomorphism` via `LinearMap.adjoint (exteriorPower.map 2 f.toLinearMap)`. -/
theorem curvatureEndomorphism_compContinuousLinearMap (f : W →L[ℝ] V) (r : FourTensor V) :
    curvatureEndomorphism (r.compContinuousLinearMap fun _ ↦ f) =
      LinearMap.adjoint (exteriorPower.map 2 f.toLinearMap) ∘ₗ curvatureEndomorphism r ∘ₗ
        exteriorPower.map 2 f.toLinearMap :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      exteriorPower.map_apply_ιMulti_two, inner_curvatureEndomorphism_ιMulti,
      compContinuousLinearMap_apply_vec, ContinuousLinearMap.coe_coe]

/-- The bivector form of the pullback of a four-tensor along `f : W →L[ℝ] V` evaluates the bivector
form of `r` on the images under `exteriorPower.map 2 f`. -/
theorem inner_curvatureEndomorphism_compContinuousLinearMap (f : W →L[ℝ] V) (r : FourTensor V)
    (ω ω' : ⋀[ℝ]^2 W) :
    ⟪curvatureEndomorphism (r.compContinuousLinearMap fun _ ↦ f) ω, ω'⟫ =
      ⟪curvatureEndomorphism r (exteriorPower.map 2 f.toLinearMap ω),
        exteriorPower.map 2 f.toLinearMap ω'⟫ := by
  rw [f.curvatureEndomorphism_compContinuousLinearMap, LinearMap.comp_apply,
    LinearMap.adjoint_inner_left, LinearMap.comp_apply]

end ContinuousLinearMap

namespace LinearIsometryEquiv

open TauCeti TauCeti.FourTensor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- `curvatureEndomorphism` is equivariant under linear isometric equivalences. -/
theorem map_comp_curvatureEndomorphism_compContinuousLinearMap
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    exteriorPower.map 2 e.toLinearIsometry.toLinearMap ∘ₗ
        curvatureEndomorphism
          (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      curvatureEndomorphism r ∘ₗ exteriorPower.map 2 e.toLinearIsometry.toLinearMap := by
  have hadj : exteriorPower.map 2 e.toLinearIsometry.toLinearMap ∘ₗ
      LinearMap.adjoint (exteriorPower.map 2 e.toLinearIsometry.toLinearMap) = LinearMap.id :=
    exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ z w ↦ by
      have hzw : exteriorPower.ιMulti ℝ 2 ![z, w] =
          exteriorPower.map 2 e.toLinearIsometry.toLinearMap
            (exteriorPower.ιMulti ℝ 2 ![e.symm z, e.symm w]) := by
        rw [exteriorPower.map_apply_ιMulti_two]; simp
      rw [LinearMap.comp_apply, hzw, exteriorPower.inner_map_map e.toLinearIsometry,
        LinearMap.adjoint_inner_left, ← hzw, LinearMap.id_apply]
  rw [e.toLinearIsometry.toContinuousLinearMap.curvatureEndomorphism_compContinuousLinearMap,
    LinearIsometry.toLinearMap_toContinuousLinearMap, ← LinearMap.comp_assoc,
    ← LinearMap.comp_assoc, hadj, LinearMap.id_comp]

end LinearIsometryEquiv
