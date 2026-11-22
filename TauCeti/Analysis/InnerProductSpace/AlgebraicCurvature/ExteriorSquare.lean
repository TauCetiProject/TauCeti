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
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.SymmetricProduct
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Algebraic curvature tensors as operators on bivectors

On a finite-dimensional real inner product space `V`, every `r : FourTensor V` induces a bivector
operator `curvatureEndomorphism r : Module.End ℝ (⋀[ℝ]^2 V)` via `TauCeti.bilinFormToEnd`. For any
pair-antisymmetric `r`, `⟪curvatureEndomorphism r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`. Restricting
to `algebraicCurvatureSubmodule V` gives a linear equivalence `curvatureEndomorphismEquiv` onto
`algebraicCurvatureEndomorphismSubmodule V` (`Sym²_B(⋀²V)`), with `finrank = n²(n² - 1) / 12`.

Under this dictionary, `curvatureEndomorphism (kulkarniNomizu h k) =
2 • exteriorPower.symmMap₂ (bilinFormToEnd h) (bilinFormToEnd k)`, and for any pair-antisymmetric
`r`, `2 * tr(curvatureEndomorphism r ∘ symmMap₂ A id) = bilinFormTrace ((ricci r).compLeft A)`.

## Main definitions

* `TauCeti.FourTensor.curvatureEndomorphism`, `TauCeti.FourTensor.ofBivectorEnd`,
  `TauCeti.FourTensor.bivectorSymmetricEquivSelfAdjoint`,
  `TauCeti.FourTensor.bianchiEndAlternatingMap`,
  `TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism`,
  `TauCeti.FourTensor.algebraicCurvatureEndomorphismSubmodule`, and
  `TauCeti.FourTensor.curvatureEndomorphismEquiv`.

## Main results

* `TauCeti.FourTensor.inner_curvatureEndomorphism_ιMulti_of_antisymm`,
  `TauCeti.FourTensor.curvatureEndomorphism_ext_iff_inner_ιMulti_two_of_antisymm`,
  `TauCeti.FourTensor.isBivectorSymmetric_ofBivectorEnd_iff`,
  `TauCeti.FourTensor.curvatureEndomorphism_ofBivectorEnd`,
  `TauCeti.FourTensor.coe_bivectorSymmetricEquivSelfAdjoint`,
  `TauCeti.FourTensor.coe_bivectorSymmetricEquivSelfAdjoint_symm`,
  `TauCeti.FourTensor.bianchiEndAlternatingMap_apply`,
  `TauCeti.FourTensor.bianchiEndAlternatingMap_surjective`,
  `TauCeti.FourTensor.ker_bianchiEndAlternatingMap`,
  `TauCeti.FourTensor.coe_curvatureEndomorphismEquiv`,
  `TauCeti.FourTensor.coe_curvatureEndomorphismEquiv_symm`,
  `TauCeti.FourTensor.isSymmetric_curvatureEndomorphism_of_swap_pairs`,
  `TauCeti.FourTensor.curvatureEndomorphism_kulkarniNomizu`,
  `TauCeti.FourTensor.curvatureEndomorphism_kulkarniNomizu_innerₗ_comp`,
  `TauCeti.FourTensor.curvatureEndomorphism_constantCurvature`,
  `TauCeti.FourTensor.ricci_eq_sum_inner_curvatureEndomorphism_of_antisymm`,
  `TauCeti.FourTensor.two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id_of_antisymm`,
  `TauCeti.FourTensor.scalar_eq_two_mul_trace_curvatureEndomorphism_of_antisymm`,
  `ContinuousLinearMap.curvatureEndomorphism_compContinuousLinearMap`, and
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

/-- For a pair-antisymmetric four-tensor `r`, `curvatureEndomorphism r` is uniquely determined by
its inner products on pure wedges. -/
theorem curvatureEndomorphism_ext_iff_inner_ιMulti_two_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z])
    (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureEndomorphism r = T ↔
      ∀ u v z w : V, ⟪T (exteriorPower.ιMulti ℝ 2 ![u, v]),
        exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r ![u, v, z, w] := by
  refine ⟨fun h u v z w ↦ h ▸ inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂ u v z w,
    fun h ↦ exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_⟩
  rw [inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂, h]

/-- The pair-antisymmetric four-tensor associated to any endomorphism `T` of `⋀[ℝ]^2 V`,
defined by `ofBivectorEnd T ![u, v, z, w] = ⟪T (u ∧ v), z ∧ w⟫`. -/
def ofBivectorEnd : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V :=
  ofExteriorSquareBilin.comp bilinFormToEnd.symm.toLinearMap

/-- Evaluation of `ofBivectorEnd T` on `(u, v, z, w)`. -/
@[simp]
theorem ofBivectorEnd_apply (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofBivectorEnd T ![u, v, z, w] =
      ⟪T (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ := by
  simp [ofBivectorEnd]

/-- Every four-tensor in the image of `ofBivectorEnd` is antisymmetric in its first pair. -/
theorem ofBivectorEnd_antisymm_first (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofBivectorEnd T ![u, v, z, w] = -ofBivectorEnd T ![v, u, z, w] :=
  ofExteriorSquareBilin_antisymm_first _ u v z w

/-- Every four-tensor in the image of `ofBivectorEnd` is antisymmetric in its last pair. -/
theorem ofBivectorEnd_antisymm_last (T : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofBivectorEnd T ![u, v, z, w] = -ofBivectorEnd T ![u, v, w, z] :=
  ofExteriorSquareBilin_antisymm_last _ u v z w

/-- `ofBivectorEnd T` is bivector-symmetric if and only if `T` is symmetric. -/
@[simp]
theorem isBivectorSymmetric_ofBivectorEnd_iff {T : Module.End ℝ (⋀[ℝ]^2 V)} :
    IsBivectorSymmetric (ofBivectorEnd T) ↔ T.IsSymmetric := by
  rw [ofBivectorEnd, LinearMap.comp_apply, LinearEquiv.coe_coe,
    isBivectorSymmetric_ofExteriorSquareBilin_iff, ← isSymmetric_bilinFormToEnd_iff,
    LinearEquiv.apply_symm_apply]

/-- `curvatureEndomorphism` is a left inverse to `ofBivectorEnd`. -/
@[simp]
theorem curvatureEndomorphism_ofBivectorEnd (T : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureEndomorphism (ofBivectorEnd T) = T := by
  rw [curvatureEndomorphism_ext_iff_inner_ιMulti_two_of_antisymm
    (ofBivectorEnd_antisymm_first T) (ofBivectorEnd_antisymm_last T)]
  intro u v z w
  rw [ofBivectorEnd_apply]

/-- `ofBivectorEnd` is injective. -/
theorem ofBivectorEnd_injective : Function.Injective (ofBivectorEnd (V := V)) :=
  Function.LeftInverse.injective curvatureEndomorphism_ofBivectorEnd

/-- On pair-antisymmetric four-tensors, `ofBivectorEnd ∘ curvatureEndomorphism` is the identity. -/
theorem ofBivectorEnd_curvatureEndomorphism_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    ofBivectorEnd (curvatureEndomorphism r) = r := by
  refine ext_vec fun u v z w ↦ ?_
  rw [ofBivectorEnd_apply, inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂]

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

/-- Linear equivalence between `bivectorSymmetricSubmodule V` and the submodule of self-adjoint
endomorphisms of `⋀[ℝ]^2 V`. -/
def bivectorSymmetricEquivSelfAdjoint :
    bivectorSymmetricSubmodule V ≃ₗ[ℝ] selfAdjoint.submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V)) :=
  bivectorSymmetricEquivSymmBilin.trans <|
    (bilinFormToEnd (E := ⋀[ℝ]^2 V)).ofSubmodules
      (LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V))
      (selfAdjoint.submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V))) <| by
    ext T
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, LinearMap.BilinForm.mem_symmSubmodule]
    refine ⟨?_, fun hT ↦ ⟨bilinFormToEnd.symm T, ?_, LinearEquiv.apply_symm_apply _ T⟩⟩
    · rintro ⟨B, hB, rfl⟩
      exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp (isSymmetric_bilinFormToEnd_iff.mpr hB)
    · rw [← isSymmetric_bilinFormToEnd_iff, LinearEquiv.apply_symm_apply]
      exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr hT

/-- Evaluation of `bivectorSymmetricEquivSelfAdjoint` is `curvatureEndomorphism`. -/
@[simp] theorem coe_bivectorSymmetricEquivSelfAdjoint (r : bivectorSymmetricSubmodule V) :
    (bivectorSymmetricEquivSelfAdjoint r : Module.End ℝ (⋀[ℝ]^2 V)) =
      curvatureEndomorphism r.val :=
  exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
    simp only [bivectorSymmetricEquivSelfAdjoint, LinearEquiv.trans_apply,
      LinearEquiv.ofSubmodules_apply, LinearMap.BilinForm.inner_bilinFormToEnd_left,
      bivectorSymmetricEquivSymmBilin_apply_ιMulti,
      (mem_bivectorSymmetricSubmodule.mp r.property).inner_curvatureEndomorphism_ιMulti]

/-- Evaluation of `bivectorSymmetricEquivSelfAdjoint.symm` is `ofBivectorEnd`. -/
@[simp] theorem coe_bivectorSymmetricEquivSelfAdjoint_symm
    (L : selfAdjoint.submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V))) :
    (bivectorSymmetricEquivSelfAdjoint.symm L : FourTensor V) = ofBivectorEnd L.val := by
  have h : curvatureEndomorphism (bivectorSymmetricEquivSelfAdjoint.symm L : FourTensor V) =
      L.val := by
    rw [← coe_bivectorSymmetricEquivSelfAdjoint, LinearEquiv.apply_symm_apply]
  have hr := mem_bivectorSymmetricSubmodule.mp (bivectorSymmetricEquivSelfAdjoint.symm L).property
  rw [← ofBivectorEnd_curvatureEndomorphism_of_antisymm hr.antisymm_first hr.antisymm_last, h]

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

/-- `ofBivectorEnd T` is an algebraic curvature tensor if and only if `T` is a symmetric Bianchi
endomorphism of `⋀[ℝ]^2 V`. -/
@[simp]
theorem isAlgebraicCurvature_ofBivectorEnd_iff {T : Module.End ℝ (⋀[ℝ]^2 V)} :
    IsAlgebraicCurvature (ofBivectorEnd T) ↔ IsAlgebraicCurvatureEndomorphism T := by
  refine ⟨fun h ↦ ⟨isBivectorSymmetric_ofBivectorEnd_iff.mp h.isBivectorSymmetric,
      fun u v z w ↦ by simpa only [ofBivectorEnd_apply] using h.cyclic_eq_zero u v z w⟩,
    fun h ↦ ?_⟩
  have hsym := isBivectorSymmetric_ofBivectorEnd_iff.mpr h.isSymmetric
  exact ⟨hsym.antisymm_first, hsym.antisymm_last, hsym.swap_pairs, fun u v z w ↦ by
    simpa only [ofBivectorEnd_apply] using h.cyclic_eq_zero u v z w⟩

/-- The Bianchi cyclic sum as a linear map from self-adjoint bivector endomorphisms to
four-forms. -/
def bianchiEndAlternatingMap :
    selfAdjoint.submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V)) →ₗ[ℝ] V [⋀^Fin 4]→ₗ[ℝ] ℝ :=
  bianchiAlternatingMap.comp bivectorSymmetricEquivSelfAdjoint.symm.toLinearMap

/-- Evaluation of `bianchiEndAlternatingMap`. -/
@[simp] theorem bianchiEndAlternatingMap_apply
    (L : selfAdjoint.submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V))) (m : Fin 4 → V) :
    bianchiEndAlternatingMap L m =
      ⟪L.val (exteriorPower.ιMulti ℝ 2 ![m 0, m 1]), exteriorPower.ιMulti ℝ 2 ![m 2, m 3]⟫ +
      ⟪L.val (exteriorPower.ιMulti ℝ 2 ![m 1, m 2]), exteriorPower.ιMulti ℝ 2 ![m 0, m 3]⟫ +
      ⟪L.val (exteriorPower.ιMulti ℝ 2 ![m 2, m 0]), exteriorPower.ιMulti ℝ 2 ![m 1, m 3]⟫ := by
  simp [bianchiEndAlternatingMap]

/-- `bianchiEndAlternatingMap` is surjective onto alternating four-forms. -/
theorem bianchiEndAlternatingMap_surjective :
    Function.Surjective (bianchiEndAlternatingMap (V := V)) :=
  bianchiAlternatingMap_surjective.comp bivectorSymmetricEquivSelfAdjoint.symm.surjective

/-- The kernel of `bianchiEndAlternatingMap` is the comap of
`algebraicCurvatureEndomorphismSubmodule V` along the inclusion of
`selfAdjoint.submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V))`. -/
theorem ker_bianchiEndAlternatingMap :
    LinearMap.ker (bianchiEndAlternatingMap (V := V)) =
      (algebraicCurvatureEndomorphismSubmodule V).comap
        (selfAdjoint.submodule ℝ (Module.End ℝ (⋀[ℝ]^2 V))).subtype := by
  rw [bianchiEndAlternatingMap, LinearMap.ker_comp, ker_bianchiAlternatingMap]
  ext L
  simp [coe_bivectorSymmetricEquivSelfAdjoint_symm]

/-- Linear equivalence `algebraicCurvatureSubmodule V ≃ₗ[ℝ] Sym²_B(⋀²V)`. -/
def curvatureEndomorphismEquiv :
    algebraicCurvatureSubmodule V ≃ₗ[ℝ] algebraicCurvatureEndomorphismSubmodule V where
  toFun r := ⟨curvatureEndomorphism r.val, mem_algebraicCurvatureEndomorphismSubmodule.mpr
    ⟨(mem_algebraicCurvatureSubmodule.mp r.property).isSymmetric_curvatureEndomorphism,
      (mem_algebraicCurvatureSubmodule.mp r.property).curvatureEndomorphism_cyclic_eq_zero⟩⟩
  invFun L := ⟨ofBivectorEnd L.val, mem_algebraicCurvatureSubmodule.mpr
    (isAlgebraicCurvature_ofBivectorEnd_iff.mpr
      (mem_algebraicCurvatureEndomorphismSubmodule.mp L.property))⟩
  map_add' r q := Subtype.ext (map_add curvatureEndomorphism r.val q.val)
  map_smul' c r := Subtype.ext (map_smul curvatureEndomorphism c r.val)
  left_inv r := Subtype.ext <|
    have hr := mem_algebraicCurvatureSubmodule.mp r.property
    ofBivectorEnd_curvatureEndomorphism_of_antisymm hr.antisymm_first hr.antisymm_last
  right_inv L := Subtype.ext (curvatureEndomorphism_ofBivectorEnd L.val)

/-- Evaluation of `curvatureEndomorphismEquiv` is `curvatureEndomorphism`. -/
@[simp] theorem coe_curvatureEndomorphismEquiv (r : algebraicCurvatureSubmodule V) :
    (curvatureEndomorphismEquiv r : Module.End ℝ (⋀[ℝ]^2 V)) = curvatureEndomorphism r.val := (rfl)

/-- Evaluation of `curvatureEndomorphismEquiv.symm` is `ofBivectorEnd`. -/
@[simp] theorem coe_curvatureEndomorphismEquiv_symm
    (L : algebraicCurvatureEndomorphismSubmodule V) :
    (curvatureEndomorphismEquiv.symm L : FourTensor V) = ofBivectorEnd L.val := (rfl)

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
    rw [inner_curvatureEndomorphism_ιMulti_of_antisymm (kulkarniNomizu_antisymm_first h k)
        (kulkarniNomizu_antisymm_last h k),
      kulkarniNomizu_apply, LinearMap.smul_apply, real_inner_smul_left,
      exteriorPower.inner_symmMap₂_ιMulti_two]
    simp only [LinearMap.BilinForm.inner_bilinFormToEnd_left]
    ring

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

/-- In an orthonormal basis, the Ricci contraction of a pair-antisymmetric four-tensor is the
sum of `curvatureEndomorphism r` pairings over `b i ∧ u` and `b i ∧ v`. -/
theorem ricci_eq_sum_inner_curvatureEndomorphism_of_antisymm {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v : V) :
    ricci r u v = ∑ i, ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![b i, u]),
      exteriorPower.ιMulti ℝ 2 ![b i, v]⟫ := by
  rw [ricci_apply_orthonormalBasis b]
  exact Finset.sum_congr rfl fun i _ ↦
    (inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂ (b i) u (b i) v).symm

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
