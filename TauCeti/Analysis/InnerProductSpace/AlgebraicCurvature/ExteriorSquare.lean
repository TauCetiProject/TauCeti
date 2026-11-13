/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Dimension
public import TauCeti.LinearAlgebra.ExteriorPower.SymmetricProduct
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear

/-!
# Algebraic curvature tensors as operators on bivectors

On a finite-dimensional real inner product space `V`, every four-tensor `r : FourTensor V` induces a
bivector endomorphism `curvatureEndomorphism r : Module.End ℝ (⋀[ℝ]^2 V)` by antisymmetrizing `r` in
its first and last pairs of arguments, descending to a bilinear form on `⋀[ℝ]^2 V`, and raising the
second index with Mathlib's Gram inner product on `⋀[ℝ]^2 V`. Whenever `r` is already antisymmetric
in each pair—in particular when `r` is an algebraic curvature tensor or a Kulkarni–Nomizu
product—the pairing on pure wedges is

`⟪curvatureEndomorphism r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`,

matching the sign and slot convention of `CovariantDerivative.curvatureEndomorphism`.

Pair-interchange symmetry makes `curvatureEndomorphism r` self-adjoint (`LinearMap.IsSymmetric`),
and the first Bianchi identity becomes vanishing of the cyclic wedge sum. Restricting to
`algebraicCurvatureSubmodule V` yields a linear equivalence `curvatureEndomorphismEquiv` onto the
submodule `algebraicCurvatureEndomorphismSubmodule V` of self-adjoint endomorphisms of `⋀[ℝ]^2 V`
satisfying the first Bianchi identity (`Sym²_B(⋀²V)`), which therefore also has dimension
`n ^ 2 * (n ^ 2 - 1) / 12`.

Under this dictionary, the Kulkarni–Nomizu product of two endomorphism-lowered bilinear forms
corresponds to twice `exteriorPower.symmMap₂`:

`curvatureEndomorphism (kulkarniNomizu ((innerₗ V).comp A) ((innerₗ V).comp B)) =
  2 • exteriorPower.symmMap₂ A B`,

so `curvatureEndomorphism (constantCurvature V) = LinearMap.id`. Moreover, the scalar contraction is
twice the operator trace on `⋀[ℝ]^2 V`, and tracing `curvatureEndomorphism r` against
`exteriorPower.symmMap₂ A LinearMap.id` contracts the Ricci form against `A`.

## Main definitions

* `TauCeti.FourTensor.curvatureEndomorphism`: the bivector operator `FourTensor V →ₗ[ℝ]
  Module.End ℝ (⋀[ℝ]^2 V)`.
* `TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism` and
  `TauCeti.FourTensor.algebraicCurvatureEndomorphismSubmodule`: self-adjoint operators on `⋀[ℝ]^2 V`
  satisfying the first Bianchi identity.
* `TauCeti.FourTensor.curvatureEndomorphismEquiv`: linear equivalence between
  `algebraicCurvatureSubmodule V` and `algebraicCurvatureEndomorphismSubmodule V`.

## Main results

* `TauCeti.FourTensor.IsPairSymmetric.inner_curvatureEndomorphism_ιMulti` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.inner_curvatureEndomorphism_ιMulti`: pure-wedge pairing
  formula.
* `TauCeti.FourTensor.curvatureEndomorphism_kulkarniNomizu` and
  `TauCeti.FourTensor.curvatureEndomorphism_constantCurvature`: dictionary with
  `exteriorPower.symmMap₂` and `LinearMap.id`.
* `TauCeti.FourTensor.IsPairSymmetric.scalar_eq_two_mul_trace_curvatureEndomorphism` and
  `TauCeti.FourTensor.IsPairSymmetric.two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id`:
  bivector trace formulas for scalar and Ricci contractions.
* `TauCeti.FourTensor.map_curvatureEndomorphism_compContinuousLinearMap`: `O(n)`-equivariance.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def pairAltLinearMap₄ (r : FourTensor V) : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ
      (fun z w ↦ (1 / 4 : ℝ) *
        (r ![u, v, z, w] - r ![u, v, w, z] - r ![v, u, z, w] + r ![v, u, w, z]))
      (fun _ _ _ ↦ by simp only [apply_add_third, apply_add_fourth]; ring)
      (fun _ _ _ ↦ by simp only [apply_smul_third, apply_smul_fourth, smul_eq_mul]; ring)
      (fun _ _ _ ↦ by simp only [apply_add_third, apply_add_fourth]; ring)
      (fun _ _ _ ↦ by simp only [apply_smul_third, apply_smul_fourth, smul_eq_mul]; ring))
    (fun _ _ _ ↦ by
      ext; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_first,
        apply_add_second]; ring)
    (fun _ _ _ ↦ by
      ext; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, apply_smul_first,
        apply_smul_second, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by
      ext; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_first,
        apply_add_second]; ring)
    (fun _ _ _ ↦ by
      ext; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, apply_smul_first,
        apply_smul_second, smul_eq_mul]; ring)

private theorem pairAltLinearMap₄_apply (r : FourTensor V) (u v z w : V) :
    pairAltLinearMap₄ r u v z w =
      (1 / 4 : ℝ) * (r ![u, v, z, w] - r ![u, v, w, z] - r ![v, u, z, w] + r ![v, u, w, z]) :=
  (rfl)

private theorem pairAltLinearMap₄_self_first (r : FourTensor V) (x z w : V) :
    pairAltLinearMap₄ r x x z w = 0 := by
  rw [pairAltLinearMap₄_apply]; ring

private theorem pairAltLinearMap₄_isAlt (r : FourTensor V) (u v : V) :
    (pairAltLinearMap₄ r u v).IsAlt := fun z ↦ by
  rw [pairAltLinearMap₄_apply]; ring

private def exteriorCurvatureForm (r : FourTensor V) : BilinForm ℝ (⋀[ℝ]^2 V) :=
  (pairAltLinearMap₄ r).exteriorSquareBilinear
    (pairAltLinearMap₄_self_first r) (pairAltLinearMap₄_isAlt r)

variable [FiniteDimensional ℝ V]

private def curvatureEndomorphismAux (r : FourTensor V) : Module.End ℝ (⋀[ℝ]^2 V) :=
  (InnerProductSpace.toDual ℝ (⋀[ℝ]^2 V)).symm.toLinearEquiv.toLinearMap ∘ₗ
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ exteriorCurvatureForm r)

private theorem inner_curvatureEndomorphismAux (r : FourTensor V) (a b : ⋀[ℝ]^2 V) :
    ⟪curvatureEndomorphismAux r a, b⟫ = exteriorCurvatureForm r a b := by
  simp [curvatureEndomorphismAux, InnerProductSpace.toDual_symm_apply]

/-- The bivector endomorphism attached to a four-tensor `r : FourTensor V`. When `r` is
antisymmetric in its first and in its last pair of arguments, it is uniquely characterized by
`⟪curvatureEndomorphism r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`. -/
def curvatureEndomorphism : FourTensor V →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) where
  toFun := curvatureEndomorphismAux
  map_add' r q := exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    simp only [LinearMap.add_apply, inner_add_left, inner_curvatureEndomorphismAux,
      exteriorCurvatureForm, LinearMap.exteriorSquareBilinear_ιMulti_ιMulti,
      pairAltLinearMap₄_apply, add_apply]
    ring
  map_smul' c r := exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    simp only [RingHom.id_apply, LinearMap.smul_apply, real_inner_smul_left,
      inner_curvatureEndomorphismAux, exteriorCurvatureForm,
      LinearMap.exteriorSquareBilinear_ιMulti_ιMulti, pairAltLinearMap₄_apply, smul_apply,
      smul_eq_mul]
    ring

/-- On general four-tensors, `curvatureEndomorphism r` pairs pure wedges via the pair-antisymmetric
part of `r`. -/
theorem inner_curvatureEndomorphism_ιMulti (r : FourTensor V) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ =
      (1 / 4 : ℝ) * (r ![u, v, z, w] - r ![u, v, w, z] - r ![v, u, z, w] + r ![v, u, w, z]) := by
  simp only [curvatureEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, inner_curvatureEndomorphismAux]
  exact (LinearMap.exteriorSquareBilinear_ιMulti_ιMulti _ _ _ ![u, v] ![z, w]).trans
    (pairAltLinearMap₄_apply r u v z w)

/-- When `r` is antisymmetric in its first and last pairs of arguments, `curvatureEndomorphism r`
pairs `u ∧ v` and `z ∧ w` to `r ![u, v, z, w]`. -/
theorem inner_curvatureEndomorphism_ιMulti_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] := by
  rw [inner_curvatureEndomorphism_ιMulti, h₂ u v w z, h₁ v u z w, h₁ v u w z, h₂ u v w z]
  ring

/-- For a pair-symmetric four-tensor `r`, `⟪curvatureEndomorphism r (u ∧ v), z ∧ w⟫ =
r ![u, v, z, w]`. -/
theorem IsPairSymmetric.inner_curvatureEndomorphism_ιMulti {r : FourTensor V}
    (hr : IsPairSymmetric r) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  inner_curvatureEndomorphism_ιMulti_of_antisymm hr.antisymm_first hr.antisymm_last u v z w

/-- For an algebraic curvature tensor `r`, `⟪curvatureEndomorphism r (u ∧ v), z ∧ w⟫ =
r ![u, v, z, w]`. -/
theorem IsAlgebraicCurvature.inner_curvatureEndomorphism_ιMulti {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] :=
  hr.isPairSymmetric.inner_curvatureEndomorphism_ιMulti u v z w

/-- The bivector endomorphism of a pair-symmetric four-tensor is symmetric (self-adjoint). -/
theorem IsPairSymmetric.isSymmetric_curvatureEndomorphism {r : FourTensor V}
    (hr : IsPairSymmetric r) : (curvatureEndomorphism r).IsSymmetric := fun a b ↦ by
  have key (u z : Fin 2 → V) :
      ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 u), exteriorPower.ιMulti ℝ 2 z⟫ =
        ⟪exteriorPower.ιMulti ℝ 2 u, curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 z)⟫ := by
    have hu : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    have hz : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
    rw [hu, hz, real_inner_comm (curvatureEndomorphism r _),
      hr.inner_curvatureEndomorphism_ιMulti, hr.inner_curvatureEndomorphism_ιMulti]
    exact hr.swap_pairs _ _ _ _
  have ha : a ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, rfl⟩ := ha
    have hb : b ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ 2)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb => obtain ⟨z, rfl⟩ := hb; exact key u z
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, inner_add_right, hx, hy]
    | smul c x _ hx => simp only [map_smul, real_inner_smul_right, hx]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, inner_add_left, hx, hy]
  | smul c x _ hx => simp only [map_smul, real_inner_smul_left, hx]

/-- The bivector endomorphism of an algebraic curvature tensor is symmetric (self-adjoint). -/
theorem IsAlgebraicCurvature.isSymmetric_curvatureEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (curvatureEndomorphism r).IsSymmetric :=
  hr.isPairSymmetric.isSymmetric_curvatureEndomorphism

/-- The bivector endomorphism of an algebraic curvature tensor satisfies the first Bianchi
identity on pure wedges. -/
theorem IsAlgebraicCurvature.curvatureEndomorphism_cyclic_eq_zero {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v z w : V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ +
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![v, z]),
      exteriorPower.ιMulti ℝ 2 ![u, w]⟫ +
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![z, u]),
      exteriorPower.ιMulti ℝ 2 ![v, w]⟫ = 0 := by
  simp only [hr.inner_curvatureEndomorphism_ιMulti]
  exact hr.cyclic_eq_zero u v z w

/-- Predicate characterizing the bivector operators `L ∈ End(⋀²V)` arising from algebraic curvature
tensors (`Sym²_B(⋀²V)`): `L` is symmetric and satisfies the first Bianchi identity. -/
structure IsAlgebraicCurvatureEndomorphism (L : Module.End ℝ (⋀[ℝ]^2 V)) : Prop where
  /-- Self-adjointness with respect to the Gram inner product on `⋀[ℝ]^2 V`. -/
  isSymmetric : L.IsSymmetric
  /-- The first Bianchi identity on pure wedges. -/
  cyclic_eq_zero : ∀ u v z w,
    ⟪L (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ +
    ⟪L (exteriorPower.ιMulti ℝ 2 ![v, z]), exteriorPower.ιMulti ℝ 2 ![u, w]⟫ +
    ⟪L (exteriorPower.ιMulti ℝ 2 ![z, u]), exteriorPower.ιMulti ℝ 2 ![v, w]⟫ = 0

variable (V) in
/-- The submodule `Sym²_B(⋀²V)` of self-adjoint endomorphisms of `⋀[ℝ]^2 V` satisfying the first
Bianchi identity. -/
def algebraicCurvatureEndomorphismSubmodule : Submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V)) where
  carrier := {L | IsAlgebraicCurvatureEndomorphism L}
  zero_mem' := ⟨fun _ _ ↦ by simp, fun _ _ _ _ ↦ by simp⟩
  add_mem' {L₁ L₂} h₁ h₂ :=
    ⟨h₁.isSymmetric.add h₂.isSymmetric, fun u v z w ↦ by
      simp only [LinearMap.add_apply, inner_add_left]
      linear_combination h₁.cyclic_eq_zero u v z w + h₂.cyclic_eq_zero u v z w⟩
  smul_mem' c L h :=
    ⟨fun a b ↦ by
      simp only [LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
        h.isSymmetric a b],
      fun u v z w ↦ by
        simp only [LinearMap.smul_apply, real_inner_smul_left]
        linear_combination c * h.cyclic_eq_zero u v z w⟩

/-- Membership in `algebraicCurvatureEndomorphismSubmodule V` is
`IsAlgebraicCurvatureEndomorphism`. -/
@[simp]
theorem mem_algebraicCurvatureEndomorphismSubmodule {L : Module.End ℝ (⋀[ℝ]^2 V)} :
    L ∈ algebraicCurvatureEndomorphismSubmodule V ↔ IsAlgebraicCurvatureEndomorphism L :=
  (Iff.rfl)

private def fourTensorOfEndomorphism (L : Module.End ℝ (⋀[ℝ]^2 V)) : FourTensor V :=
  ofLinearMap₄ <| MultilinearMap.toBilinMap
    ((TauCeti.BilinForm.ofExteriorSquareDual.comp ((innerₗ (⋀[ℝ]^2 V)).comp L)).compMultilinearMap
      (exteriorPower.ιMulti ℝ 2).toMultilinearMap)

private theorem fourTensorOfEndomorphism_apply (L : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    fourTensorOfEndomorphism L ![u, v, z, w] =
      ⟪L (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ := by
  simp [fourTensorOfEndomorphism]

private theorem isAlgebraicCurvature_fourTensorOfEndomorphism {L : Module.End ℝ (⋀[ℝ]^2 V)}
    (hL : IsAlgebraicCurvatureEndomorphism L) :
    IsAlgebraicCurvature (fourTensorOfEndomorphism L) := by
  have hswap (x y : V) : exteriorPower.ιMulti ℝ 2 ![x, y] =
      -exteriorPower.ιMulti ℝ 2 ![y, x] := by
    simpa [Equiv.swap_apply_def] using
      (exteriorPower.ιMulti ℝ 2).map_swap ![y, x] (by decide : (0 : Fin 2) ≠ 1)
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [fourTensorOfEndomorphism_apply]
  · rw [hswap u v, map_neg, inner_neg_left]
  · rw [hswap z w, inner_neg_right]
  · rw [hL.isSymmetric, real_inner_comm]
  · exact hL.cyclic_eq_zero u v z w

/-- `curvatureEndomorphism` restricts to a canonical linear equivalence between
`algebraicCurvatureSubmodule V` and `algebraicCurvatureEndomorphismSubmodule V`. -/
def curvatureEndomorphismEquiv :
    algebraicCurvatureSubmodule V ≃ₗ[ℝ] algebraicCurvatureEndomorphismSubmodule V where
  toFun r :=
    ⟨curvatureEndomorphism r.1, mem_algebraicCurvatureEndomorphismSubmodule.mpr
      ⟨(mem_algebraicCurvatureSubmodule.mp r.2).isSymmetric_curvatureEndomorphism,
        (mem_algebraicCurvatureSubmodule.mp r.2).curvatureEndomorphism_cyclic_eq_zero⟩⟩
  invFun L :=
    ⟨fourTensorOfEndomorphism L.1, mem_algebraicCurvatureSubmodule.mpr
      (isAlgebraicCurvature_fourTensorOfEndomorphism
        (mem_algebraicCurvatureEndomorphismSubmodule.mp L.2))⟩
  map_add' r q := Subtype.ext (map_add curvatureEndomorphism r.1 q.1)
  map_smul' c r := Subtype.ext (map_smul curvatureEndomorphism c r.1)
  left_inv r := Subtype.ext <| toLinearMap₄_injective <| by
    ext u v z w
    rw [toLinearMap₄_apply, fourTensorOfEndomorphism_apply, toLinearMap₄_apply]
    exact (mem_algebraicCurvatureSubmodule.mp r.2).inner_curvatureEndomorphism_ιMulti u v z w
  right_inv L := Subtype.ext <| exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    have hL := isAlgebraicCurvature_fourTensorOfEndomorphism
      (mem_algebraicCurvatureEndomorphismSubmodule.mp L.2)
    dsimp only
    rw [hL.inner_curvatureEndomorphism_ιMulti, fourTensorOfEndomorphism_apply]

/-- Evaluation of `curvatureEndomorphismEquiv` is `curvatureEndomorphism`. -/
@[simp]
theorem coe_curvatureEndomorphismEquiv (r : algebraicCurvatureSubmodule V) :
    (curvatureEndomorphismEquiv r : Module.End ℝ (⋀[ℝ]^2 V)) = curvatureEndomorphism r.1 :=
  (rfl)

/-- Evaluation of `curvatureEndomorphismEquiv.symm` on four vectors via pure wedges. -/
@[simp]
theorem curvatureEndomorphismEquiv_symm_apply
    (L : algebraicCurvatureEndomorphismSubmodule V) (u v z w : V) :
    (curvatureEndomorphismEquiv.symm L).1 ![u, v, z, w] =
      ⟪L.1 (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ :=
  fourTensorOfEndomorphism_apply L.1 u v z w

/-- The space `Sym²_B(⋀²V)` of algebraic curvature operators on bivectors has dimension
`n ^ 2 * (n ^ 2 - 1) / 12`. -/
theorem finrank_algebraicCurvatureEndomorphismSubmodule :
    Module.finrank ℝ (algebraicCurvatureEndomorphismSubmodule V) =
      Module.finrank ℝ V ^ 2 * (Module.finrank ℝ V ^ 2 - 1) / 12 :=
  curvatureEndomorphismEquiv.finrank_eq.symm.trans finrank_algebraicCurvatureSubmodule

/-- **Dictionary between `kulkarniNomizu` and `exteriorPower.symmMap₂`**: lowering two endomorphisms
`A, B` with the inner product and taking their Kulkarni–Nomizu product gives `2 • (A ∧ B)` on
`⋀[ℝ]^2 V`. -/
theorem curvatureEndomorphism_kulkarniNomizu (A B : Module.End ℝ V) :
    curvatureEndomorphism (kulkarniNomizu ((innerₗ V).comp A) ((innerₗ V).comp B)) =
      (2 : ℝ) • exteriorPower.symmMap₂ A B := by
  refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  have h₁ : ∀ a b c d,
      kulkarniNomizu ((innerₗ V).comp A) ((innerₗ V).comp B) ![a, b, c, d] =
        -kulkarniNomizu ((innerₗ V).comp A) ((innerₗ V).comp B) ![b, a, c, d] := by
    intro a b c d; simp only [kulkarniNomizu_apply_eq]
    exact LinearMap.BilinForm.kulkarniNomizu_antisymm_first _ _ a b d c
  have h₂ : ∀ a b c d,
      kulkarniNomizu ((innerₗ V).comp A) ((innerₗ V).comp B) ![a, b, c, d] =
        -kulkarniNomizu ((innerₗ V).comp A) ((innerₗ V).comp B) ![a, b, d, c] := by
    intro a b c d; simp only [kulkarniNomizu_apply_eq]
    exact LinearMap.BilinForm.kulkarniNomizu_antisymm_last _ _ a b d c
  rw [inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂, kulkarniNomizu_apply]
  simp only [LinearMap.smul_apply, exteriorPower.symmMap₂_apply_ιMulti, real_inner_smul_left,
    inner_add_left, exteriorPower.inner_ιMulti_two, LinearMap.comp_apply, innerₗ_apply_apply,
    invOf_eq_inv]
  ring

/-- The constant-curvature four-tensor acts on `⋀[ℝ]^2 V` as the identity endomorphism. -/
@[simp]
theorem curvatureEndomorphism_constantCurvature :
    curvatureEndomorphism (constantCurvature V) = LinearMap.id :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    rw [isAlgebraicCurvature_constantCurvature.inner_curvatureEndomorphism_ιMulti,
      LinearMap.id_apply, constantCurvature_apply, exteriorPower.inner_ιMulti_two]

/-- The scalar contraction of a pair-symmetric four-tensor is twice the trace of its bivector
endomorphism on `⋀[ℝ]^2 V`. -/
theorem IsPairSymmetric.scalar_eq_two_mul_trace_curvatureEndomorphism {r : FourTensor V}
    (hr : IsPairSymmetric r) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureEndomorphism r) := by
  let b := stdOrthonormalBasis ℝ V
  rw [← b.sum_inner_ιMulti_two_eq_two_mul_trace, scalar_apply_orthonormalBasis b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  exact (hr.inner_curvatureEndomorphism_ιMulti (b i) (b j) (b i) (b j)).symm

/-- The scalar contraction of an algebraic curvature tensor is twice the trace of its bivector
endomorphism on `⋀[ℝ]^2 V`. -/
theorem IsAlgebraicCurvature.scalar_eq_two_mul_trace_curvatureEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    scalar r = 2 * LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureEndomorphism r) :=
  hr.isPairSymmetric.scalar_eq_two_mul_trace_curvatureEndomorphism

/-- Twice the trace of `curvatureEndomorphism r ∘ₗ symmMap₂ A id` on `⋀[ℝ]^2 V` equals the
orthonormal contraction `∑ i, ricci r (A (b i)) (b i)`. -/
theorem IsPairSymmetric.two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) {r : FourTensor V}
    (hr : IsPairSymmetric r) (A : Module.End ℝ V) :
    2 * LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism r ∘ₗ exteriorPower.symmMap₂ A LinearMap.id) =
      ∑ i, ricci r (A (b i)) (b i) := by
  rw [← b.sum_inner_ιMulti_two_eq_two_mul_trace]
  have hterm (i j : ι) :
      ⟪(curvatureEndomorphism r ∘ₗ exteriorPower.symmMap₂ A LinearMap.id)
          (exteriorPower.ιMulti ℝ 2 ![b i, b j]), exteriorPower.ιMulti ℝ 2 ![b i, b j]⟫ =
        (1 / 2 : ℝ) * (r ![b j, A (b i), b j, b i] + r ![b i, A (b j), b i, b j]) := by
    simp only [LinearMap.comp_apply, exteriorPower.symmMap₂_apply_ιMulti, LinearMap.id_apply,
      map_smul, map_add, real_inner_smul_left, inner_add_left,
      hr.inner_curvatureEndomorphism_ιMulti, invOf_eq_inv]
    rw [hr.antisymm_first (A (b i)) (b j), hr.antisymm_last (b j) (A (b i))]
    ring
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j ↦ r ![b i, A (b j), b i, b j])]
  simp_rw [← ricci_apply_orthonormalBasis b]
  ring

/-- `curvatureEndomorphism` is equivariant under linear isometric equivalences. -/
theorem map_curvatureEndomorphism_compContinuousLinearMap {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    exteriorPower.map 2 e.toLinearIsometry.toLinearMap ∘ₗ
        curvatureEndomorphism
          (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      curvatureEndomorphism r ∘ₗ exteriorPower.map 2 e.toLinearIsometry.toLinearMap := by
  refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  let z' := e.symm z
  let w' := e.symm w
  have hzw : exteriorPower.ιMulti ℝ 2 ![z, w] =
      exteriorPower.map 2 e.toLinearIsometry.toLinearMap (exteriorPower.ιMulti ℝ 2 ![z', w']) := by
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
    funext i; fin_cases i <;> simp [z', w']
  rw [hzw]
  simp only [LinearMap.comp_apply]
  rw [exteriorPower.inner_map_map e.toLinearIsometry]
  simp only [exteriorPower.map_apply_ιMulti]
  have hpair (x y : W) : (e.toLinearIsometry.toLinearMap ∘ ![x, y]) = ![e x, e y] := by
    funext i; fin_cases i <;> rfl
  rw [hpair u v, hpair z' w', inner_curvatureEndomorphism_ιMulti,
    inner_curvatureEndomorphism_ιMulti]
  simp only [compContinuousLinearMap_apply_vec]
  simp [z', w']

end TauCeti.FourTensor
