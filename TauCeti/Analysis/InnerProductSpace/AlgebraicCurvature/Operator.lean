/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.Analysis.InnerProductSpace.Nondegenerate
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.InnerProductSpace.BilinearForm
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
import TauCeti.LinearAlgebra.ExteriorPower.Square
import TauCeti.LinearAlgebra.Multilinear.SectionalPolarization
import TauCeti.LinearAlgebra.SymmetricPower.Basis
import TauCeti.LinearAlgebra.TensorSquare

/-!
# Curvature operators, symmetric wedge products, and the dimension of curvature space

On a finite-dimensional real inner product space `V`, every algebraic curvature tensor
`r ∈ algebraicCurvatureSubmodule V` descends to a symmetric endomorphism
`curvatureOperator r : Module.End ℝ (⋀[ℝ]^2 V)` characterized on pure bivectors by
`⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`. Its image is the subspace
`bianchiEndSubmodule V` of symmetric endomorphisms satisfying the first Bianchi identity, giving a
linear equivalence `algebraicCurvatureEquivBianchiEnd` that sends `constantCurvature V` to `id`.

For endomorphisms `A, B : Module.End K V` over a field `K`, the *symmetric wedge product*
`TauCeti.wedgeEnd A B : Module.End K (⋀[K]^2 V)` acts on pure wedges by
`2⁻¹ • (A u ∧ B v + B u ∧ A v)`, with `wedgeEnd A A = exteriorPower.map 2 A` when `2 ≠ 0`. On `V`,
pairing `wedgeEnd A B` against `z ∧ w` yields half the Kulkarni–Nomizu tensor of `⟪A ·, ·⟫` and
`⟪B ·, ·⟫`.

Finally, the cyclic Bianchi map from pair-symmetric skew-pair four-tensors onto alternating
four-forms `V [⋀^Fin 4]→ₗ[ℝ] ℝ` is surjective with kernel `algebraicCurvatureSubmodule V`, giving
`Module.finrank ℝ (algebraicCurvatureSubmodule V) = (dim V)² ((dim V)² - 1) / 12` and, in dimension
`2`, `r = (scalar r / 2) • constantCurvature V`.

## Main definitions

* `TauCeti.wedgeEnd`: the symmetric wedge product of two endomorphisms on `⋀[K]^2 V`.
* `TauCeti.FourTensor.toLinearMap₄`, `TauCeti.FourTensor.linearMap₄Equiv`: currying four-tensors.
* `TauCeti.FourTensor.curvatureOperator`, `TauCeti.FourTensor.IsBianchiEnd`,
  `TauCeti.FourTensor.bianchiEndSubmodule`, `TauCeti.FourTensor.algebraicCurvatureEquivBianchiEnd`.

## Main statements

* `TauCeti.FourTensor.IsAlgebraicCurvature.eq_of_apply_self_eq`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.eq_of_apply_self_eq_of_linearIndependent`.
* `TauCeti.wedgeEnd_self`, `TauCeti.wedgeEnd_id`, `TauCeti.FourTensor.inner_wedgeEnd_ιMulti`,
  `TauCeti.FourTensor.curvatureOperator_kulkarniNomizu`.
* `TauCeti.FourTensor.finrank_algebraicCurvatureSubmodule`,
  `TauCeti.FourTensor.finrank_bianchiEndSubmodule`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.eq_smul_constantCurvature_of_finrank_eq_two`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Sections 1.G and 1.H.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 7–8.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. (2) 167 (2008), 1079–1097, Section 1.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace TensorProduct

noncomputable section

namespace TauCeti

private theorem vec2_eta {α : Type*} (v : Fin 2 → α) : v = ![v 0, v 1] := by
  funext i; fin_cases i <;> rfl

/-! ### Symmetric wedge product of endomorphisms on the exterior square -/

section WedgeEnd

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def wedgeBilin (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun u v ↦ exteriorPower.ιMulti R 2 ![u, v])
    (fun u₁ u₂ v ↦ by
      have h0 (x : M) : Function.update (![u₁, v] : Fin 2 → M) 0 x = ![x, v] := by
        funext i; fin_cases i <;> rfl
      simpa only [h0] using (exteriorPower.ιMulti R 2).map_update_add ![u₁, v] 0 u₁ u₂)
    (fun c u v ↦ exteriorPower.ιMulti_two_smul_left u v c)
    exteriorPower.ιMulti_two_add_right
    (fun c u v ↦ exteriorPower.ιMulti_two_smul_right u v c)

@[simp]
private theorem wedgeBilin_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (u v : M) : wedgeBilin R M u v = exteriorPower.ιMulti R 2 ![u, v] :=
  (rfl)

private theorem ιMulti_two_swap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (u v : M) : exteriorPower.ιMulti R 2 ![v, u] = -exteriorPower.ιMulti R 2 ![u, v] := by
  have h : (![v, u] : Fin 2 → M) = ![u, v] ∘ Equiv.swap 0 1 := by funext i; fin_cases i <;> rfl
  rw [h, (exteriorPower.ιMulti R 2).map_swap ![u, v] (by decide)]

private theorem isAlt_wedgeEndAux (A B : Module.End K V) :
    ((wedgeBilin K V).compl₁₂ A B + (wedgeBilin K V).compl₁₂ B A).IsAlt := fun u ↦ by
  simp [LinearMap.compl₁₂_apply, ιMulti_two_swap (B u) (A u)]

private def wedgeEndAux (A B : Module.End K V) : Module.End K (⋀[K]^2 V) :=
  (2 : K)⁻¹ • exteriorPower.alternatingMapLinearEquiv (isAlt_wedgeEndAux A B).toAlternatingMap

private theorem wedgeEndAux_ιMulti_eq_wedgeBilin (A B : Module.End K V) (u v : V) :
    wedgeEndAux A B (exteriorPower.ιMulti K 2 ![u, v]) =
      (2 : K)⁻¹ • (wedgeBilin K V (A u) (B v) + wedgeBilin K V (B u) (A v)) := by
  simp [wedgeEndAux, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    LinearMap.IsAlt.toAlternatingMap_apply]

/-- The symmetric wedge product of two endomorphisms `A, B : Module.End K V` on `⋀[K]^2 V`,
characterized on pure wedges by `wedgeEnd A B (u ∧ v) = 2⁻¹ • (A u ∧ B v + B u ∧ A v)`. -/
def wedgeEnd : Module.End K V →ₗ[K] Module.End K V →ₗ[K] Module.End K (⋀[K]^2 V) :=
  LinearMap.mk₂ K wedgeEndAux
    (fun _ _ _ ↦ exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
      rw [vec2_eta v]
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
        wedgeEndAux_ιMulti_eq_wedgeBilin, map_add, smul_add]; abel)
    (fun c _ _ ↦ exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
      rw [vec2_eta v]
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
        wedgeEndAux_ιMulti_eq_wedgeBilin, map_smul, smul_add, smul_comm (2 : K)⁻¹ c])
    (fun _ _ _ ↦ exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
      rw [vec2_eta v]
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
        wedgeEndAux_ιMulti_eq_wedgeBilin, map_add, smul_add]; abel)
    (fun c _ _ ↦ exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
      rw [vec2_eta v]
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
        wedgeEndAux_ιMulti_eq_wedgeBilin, map_smul, smul_add, smul_comm (2 : K)⁻¹ c])

/-- On a pure wedge `u ∧ v`, `wedgeEnd A B` evaluates to `2⁻¹ • (A u ∧ B v + B u ∧ A v)`. -/
@[simp]
theorem wedgeEnd_apply_ιMulti (A B : Module.End K V) (u v : V) :
    wedgeEnd A B (exteriorPower.ιMulti K 2 ![u, v]) =
      (2 : K)⁻¹ • (exteriorPower.ιMulti K 2 ![A u, B v] +
        exteriorPower.ιMulti K 2 ![B u, A v]) := by
  change wedgeEndAux A B _ = _; rw [wedgeEndAux_ιMulti_eq_wedgeBilin]; rfl

/-- The symmetric wedge product of endomorphisms is commutative. -/
theorem wedgeEnd_comm (A B : Module.End K V) : wedgeEnd A B = wedgeEnd B A :=
  exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
    rw [vec2_eta v]; simp [add_comm]

/-- When `2 ≠ 0`, the symmetric wedge product of an endomorphism `A` with itself is the induced
exterior-square map `exteriorPower.map 2 A`. -/
@[simp]
theorem wedgeEnd_self [NeZero (2 : K)] (A : Module.End K V) :
    wedgeEnd A A = exteriorPower.map 2 A :=
  exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
    rw [vec2_eta v]
    simp only [LinearMap.compAlternatingMap_apply, wedgeEnd_apply_ιMulti,
      exteriorPower.map_apply_ιMulti_two, ← two_smul K, smul_smul,
      inv_mul_cancel₀ (NeZero.ne (2 : K)), one_smul]

/-- When `2 ≠ 0`, the symmetric wedge product of the identity endomorphism with itself is the
identity on `⋀[K]^2 V`. -/
theorem wedgeEnd_id [NeZero (2 : K)] :
    wedgeEnd (LinearMap.id : Module.End K V) LinearMap.id = LinearMap.id := by
  rw [wedgeEnd_self, exteriorPower.map_id]

end WedgeEnd

namespace FourTensor

private theorem vec4_eta {α : Type*} (m : Fin 4 → α) : m = ![m 0, m 1, m 2, m 3] := by
  funext i; fin_cases i <;> rfl

/-! ### Currying and polarization of four-tensors -/

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem sub_isCurv (r : algebraicCurvatureSubmodule V) : IsAlgebraicCurvature r.1 :=
  mem_algebraicCurvatureSubmodule.mp r.2

/-- Curry a continuous four-tensor into an algebraic four-linear form:
`r.toLinearMap₄ u v z w = r ![u, v, z, w]`. -/
def toLinearMap₄ : FourTensor V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun r :=
    LinearMap.mk₂ ℝ
      (fun u v ↦ LinearMap.mk₂ ℝ (fun z w ↦ r ![u, v, z, w])
        (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)
        (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..))
      (fun _ _ _ ↦ by ext; exact apply_add_first ..)
      (fun _ _ _ ↦ by ext; exact apply_smul_first ..)
      (fun _ _ _ ↦ by ext; exact apply_add_second ..)
      (fun _ _ _ ↦ by ext; exact apply_smul_second ..)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `toLinearMap₄` evaluates `r` on the four vector arguments. -/
@[simp]
theorem toLinearMap₄_apply (r : FourTensor V) (u v z w : V) :
    r.toLinearMap₄ u v z w = r ![u, v, z, w] :=
  (rfl)

/-- Currying a four-tensor into a four-linear form is injective. -/
theorem toLinearMap₄_injective : Function.Injective (toLinearMap₄ (V := V)) := fun _ _ h ↦ by
  ext m; rw [vec4_eta m]; exact congr($h (m 0) (m 1) (m 2) (m 3))

@[simp]
theorem toLinearMap₄_eq_zero_iff {r : FourTensor V} : r.toLinearMap₄ = 0 ↔ r = 0 :=
  map_eq_zero_iff _ toLinearMap₄_injective

/-- An algebraic curvature tensor vanishes when its first two arguments coincide. -/
theorem IsAlgebraicCurvature.self_first {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (u z w : V) : r ![u, u, z, w] = 0 := by linarith [hr.antisymm_first u u z w]

/-- An algebraic curvature tensor vanishes when its last two arguments coincide. -/
theorem IsAlgebraicCurvature.self_last {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (u v z : V) : r ![u, v, z, z] = 0 := by linarith [hr.antisymm_last u v z z]

/-- **Polarization of algebraic curvature tensors.** Two algebraic curvature tensors with the same
sectional-numerator values `r ![u, v, u, v]` for all `u, v` are equal. -/
theorem IsAlgebraicCurvature.eq_of_apply_self_eq {r₁ r₂ : FourTensor V}
    (hr₁ : IsAlgebraicCurvature r₁) (hr₂ : IsAlgebraicCurvature r₂)
    (h : ∀ u v : V, r₁ ![u, v, u, v] = r₂ ![u, v, u, v]) : r₁ = r₂ := by
  refine toLinearMap₄_injective (LinearMap.eq_of_cyclic_eq_zero (IsRegular.of_ne_zero'
    (by norm_num : (6 : ℝ) ≠ 0)).left hr₁.antisymm_first hr₁.antisymm_last hr₁.cyclic_eq_zero
    hr₂.antisymm_first hr₂.antisymm_last hr₂.cyclic_eq_zero fun u v ↦ ?_)
  simp only [toLinearMap₄_apply, hr₁.antisymm_last u v v u, hr₂.antisymm_last u v v u, h u v]

/-- **Plane polarization of algebraic curvature tensors.** Two algebraic curvature tensors agreeing
on `r ![u, v, u, v]` for every linearly independent pair `(u, v)` are equal. -/
theorem IsAlgebraicCurvature.eq_of_apply_self_eq_of_linearIndependent {r₁ r₂ : FourTensor V}
    (hr₁ : IsAlgebraicCurvature r₁) (hr₂ : IsAlgebraicCurvature r₂)
    (h : ∀ u v : V, LinearIndependent ℝ ![u, v] → r₁ ![u, v, u, v] = r₂ ![u, v, u, v]) :
    r₁ = r₂ := by
  refine toLinearMap₄_injective (LinearMap.eq_of_cyclic_eq_zero_of_linearIndependent
    (by norm_num : (6 : ℝ) ≠ 0) hr₁.antisymm_first hr₁.antisymm_last hr₁.cyclic_eq_zero
    hr₂.antisymm_first hr₂.antisymm_last hr₂.cyclic_eq_zero fun u v huv ↦ ?_)
  simp only [toLinearMap₄_apply, hr₁.antisymm_last u v v u, hr₂.antisymm_last u v v u, h u v huv]

/-- On a space of dimension at most `1`, every algebraic curvature tensor vanishes. -/
theorem IsAlgebraicCurvature.eq_zero_of_finrank_le_one [FiniteDimensional ℝ V]
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≤ 1) : r = 0 :=
  hr.eq_of_apply_self_eq_of_linearIndependent
    (mem_algebraicCurvatureSubmodule.mp (algebraicCurvatureSubmodule V).zero_mem)
    fun _ _ huv ↦ absurd huv.fintype_card_le_finrank (by simp; omega)

end NormedSpace

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

@[simp]
theorem ofLinearMap₄_toLinearMap₄ (r : FourTensor V) : ofLinearMap₄ r.toLinearMap₄ = r := by
  ext m; rw [ofLinearMap₄_apply, toLinearMap₄_apply, ← vec4_eta m]

@[simp]
theorem toLinearMap₄_ofLinearMap₄ (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (ofLinearMap₄ T).toLinearMap₄ = T := by ext; simp

/-- On a finite-dimensional real normed space, continuous four-tensors are linearly equivalent to
curried four-linear forms. -/
def linearMap₄Equiv : FourTensor V ≃ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :=
  LinearEquiv.ofLinearMap toLinearMap₄ ofLinearMap₄
    (LinearMap.ext toLinearMap₄_ofLinearMap₄) (LinearMap.ext ofLinearMap₄_toLinearMap₄)

@[simp]
theorem linearMap₄Equiv_apply (r : FourTensor V) : linearMap₄Equiv r = r.toLinearMap₄ :=
  (rfl)

@[simp]
theorem linearMap₄Equiv_symm_apply (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    linearMap₄Equiv.symm T = ofLinearMap₄ T :=
  (rfl)

end FiniteDimensional

/-! ### Bivector curvature operators and the self-adjoint Bianchi subspace -/

section Operator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private def exteriorBilinForm (r : algebraicCurvatureSubmodule V) : BilinForm ℝ (⋀[ℝ]^2 V) :=
  r.1.toLinearMap₄.exteriorSquareBilinear (sub_isCurv r).self_first
    (fun u v z ↦ (sub_isCurv r).self_last u v z)

omit [FiniteDimensional ℝ V] in
@[simp]
private theorem exteriorBilinForm_ιMulti (r : algebraicCurvatureSubmodule V) (u v : Fin 2 → V) :
    exteriorBilinForm r (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
      r.1 ![u 0, u 1, v 0, v 1] :=
  LinearMap.exteriorSquareBilinear_ιMulti_ιMulti _ _ _ u v

private theorem inner_symmComp (B : BilinForm ℝ (⋀[ℝ]^2 V)) (a b : ⋀[ℝ]^2 V) :
    ⟪B.symmCompOfNondegenerate (innerₗ (⋀[ℝ]^2 V)) TauCeti.nondegenerate_inner a, b⟫ = B a b :=
  B.symmCompOfNondegenerate_left_apply TauCeti.nondegenerate_inner b a

/-- The curvature operator on `⋀[ℝ]^2 V` associated with an algebraic curvature tensor `r`,
characterized by `⟪curvatureOperator r (u ∧ v), z ∧ w⟫ = r ![u, v, z, w]`. -/
def curvatureOperator : algebraicCurvatureSubmodule V →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) where
  toFun r := (exteriorBilinForm r).symmCompOfNondegenerate (innerₗ _) TauCeti.nondegenerate_inner
  map_add' _ _ := exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp [inner_add_left, inner_symmComp]
  map_smul' _ _ := exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by
    simp [real_inner_smul_left, inner_symmComp]

/-- Pairing `curvatureOperator r` on pure wedges `u ∧ v` and `z ∧ w` recovers `r ![u, v, z, w]`. -/
@[simp]
theorem inner_curvatureOperator_ιMulti (r : algebraicCurvatureSubmodule V) (u v z w : V) :
    ⟪curvatureOperator r (exteriorPower.ιMulti ℝ 2 ![u, v]),
      exteriorPower.ιMulti ℝ 2 ![z, w]⟫ = r.1 ![u, v, z, w] :=
  (inner_symmComp (exteriorBilinForm r) _ _).trans (exteriorBilinForm_ιMulti r ![u, v] ![z, w])

/-- `curvatureOperator r` is uniquely characterized by its pairings on decomposable bivectors. -/
theorem curvatureOperator_eq_iff (r : algebraicCurvatureSubmodule V)
    (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    curvatureOperator r = A ↔
      ∀ u v z w : V,
        ⟪A (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ =
          r.1 ![u, v, z, w] :=
  ⟨fun h ↦ h ▸ inner_curvatureOperator_ιMulti r, fun h ↦
    exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ by
      rw [inner_curvatureOperator_ιMulti, h]⟩

/-- Passing from an algebraic curvature tensor to its curvature operator on `⋀[ℝ]^2 V` is
injective. -/
theorem curvatureOperator_injective : Function.Injective (curvatureOperator (V := V)) :=
  fun _ _ h ↦ Subtype.ext <| by
    ext m; rw [vec4_eta m]
    simpa only [inner_curvatureOperator_ιMulti] using
      congr(⟪$h (exteriorPower.ιMulti ℝ 2 ![m 0, m 1]), exteriorPower.ιMulti ℝ 2 ![m 2, m 3]⟫)

@[simp]
theorem curvatureOperator_eq_zero_iff {r : algebraicCurvatureSubmodule V} :
    curvatureOperator r = 0 ↔ r = 0 :=
  map_eq_zero_iff _ curvatureOperator_injective

/-- The curvature operator of `constantCurvature V` is the identity on `⋀[ℝ]^2 V`. -/
@[simp]
theorem curvatureOperator_constantCurvature :
    curvatureOperator
        ⟨constantCurvature V,
          mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature⟩ =
      LinearMap.id := by
  rw [curvatureOperator_eq_iff]; intro u v z w; simp [exteriorPower.inner_ιMulti_two]

/-- The curvature operator of an algebraic curvature tensor is symmetric with respect to the Gram
inner product on `⋀[ℝ]^2 V`. -/
theorem isSymmetric_curvatureOperator (r : algebraicCurvatureSubmodule V) :
    (curvatureOperator r).IsSymmetric := fun a b ↦ by
  have hflip := LinearMap.flip_exteriorSquareBilinear r.1.toLinearMap₄ (sub_isCurv r).self_first
    (fun u v z ↦ (sub_isCurv r).self_last u v z) (sub_isCurv r).swap_pairs
  dsimp only [curvatureOperator, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_symmComp, real_inner_comm _ a, inner_symmComp]
  exact congr($hflip b a)

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

@[simp]
theorem mem_bianchiEndSubmodule {R : Module.End ℝ (⋀[ℝ]^2 V)} :
    R ∈ bianchiEndSubmodule V ↔ IsBianchiEnd R :=
  Iff.rfl

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

private def ofExteriorBilin : BilinForm ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun B := ofLinearMap₄ <|
    LinearMap.mk₂ ℝ (fun u v ↦ (wedgeBilin ℝ V).compr₂ (B (wedgeBilin ℝ V u v)))
      (fun _ _ _ ↦ by ext; simp [map_add]) (fun _ _ _ ↦ by ext; simp [map_smul])
      (fun _ _ _ ↦ by ext; simp [map_add]) (fun _ _ _ ↦ by ext; simp [map_smul])
  map_add' _ _ := toLinearMap₄_injective <| by ext; simp
  map_smul' _ _ := toLinearMap₄_injective <| by ext; simp

@[simp]
private theorem ofExteriorBilin_apply (B : BilinForm ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorBilin B ![u, v, z, w] =
      B (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) := by
  simp [ofExteriorBilin]

/-- Reconstruct a four-tensor from an endomorphism of `⋀[ℝ]^2 V` by pairing pure bivectors:
`(u, v, z, w) ↦ ⟪R (u ∧ v), z ∧ w⟫`. -/
def ofExteriorEnd : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun R := ofExteriorBilin (innerₗ (⋀[ℝ]^2 V) ∘ₗ R)
  map_add' _ _ := toLinearMap₄_injective <| by ext; simp
  map_smul' _ _ := toLinearMap₄_injective <| by ext; simp

@[simp]
theorem ofExteriorEnd_apply (R : Module.End ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorEnd R ![u, v, z, w] =
      ⟪R (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ := by
  simp [ofExteriorEnd]

/-- A Bianchi endomorphism of `⋀[ℝ]^2 V` defines an algebraic curvature tensor via
`ofExteriorEnd`. -/
theorem IsBianchiEnd.isAlgebraicCurvature_ofExteriorEnd {R : Module.End ℝ (⋀[ℝ]^2 V)}
    (hR : IsBianchiEnd R) : IsAlgebraicCurvature (ofExteriorEnd R) where
  antisymm_first u v z w := by simp [ιMulti_two_swap v u]
  antisymm_last u v z w := by simp [ιMulti_two_swap w z]
  swap_pairs u v z w := by simp only [ofExteriorEnd_apply]; rw [hR.isSymmetric, real_inner_comm]
  cyclic_eq_zero u v z w := by simp [hR.cyclic_eq_zero u v z w]

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
  left_inv _ := Subtype.ext <| toLinearMap₄_injective <| by ext; simp
  right_inv _ := Subtype.ext <| exteriorPower.linearMap_ext_inner_ιMulti_two fun _ _ _ _ ↦ by simp

@[simp]
theorem coe_algebraicCurvatureEquivBianchiEnd_apply (r : algebraicCurvatureSubmodule V) :
    (algebraicCurvatureEquivBianchiEnd V r : Module.End ℝ (⋀[ℝ]^2 V)) = curvatureOperator r :=
  (rfl)

@[simp]
theorem coe_algebraicCurvatureEquivBianchiEnd_symm_apply (R : bianchiEndSubmodule V) :
    (algebraicCurvatureEquivBianchiEnd V |>.symm R : FourTensor V) = ofExteriorEnd R.1 :=
  (rfl)

/-- The image of `curvatureOperator` in `Module.End ℝ (⋀[ℝ]^2 V)` is `bianchiEndSubmodule V`. -/
theorem range_curvatureOperator :
    LinearMap.range (curvatureOperator (V := V)) = bianchiEndSubmodule V := by
  ext R; refine ⟨fun ⟨r, hr⟩ ↦ hr ▸ isBianchiEnd_curvatureOperator r, fun hR ↦
    ⟨(algebraicCurvatureEquivBianchiEnd V).symm ⟨R, hR⟩,
      congrArg Subtype.val ((algebraicCurvatureEquivBianchiEnd V).apply_symm_apply ⟨R, hR⟩)⟩⟩

/-- Orthogonal equivariance of `curvatureOperator` under a linear isometric equivalence
`e : W ≃ₗᵢ[ℝ] V`. -/
theorem curvatureOperator_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V)
    (r : algebraicCurvatureSubmodule V) :
    curvatureOperator
        ⟨r.1.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap,
          compContinuousLinearMap_mem_algebraicCurvatureSubmodule r.2 _⟩ =
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
    LinearIsometryEquiv.coe_toLinearIsometry, inner_curvatureOperator_ιMulti]
  exact
    (compContinuousLinearMap_apply_vec r.1 e.toLinearIsometry.toContinuousLinearMap u v z w).symm

/-! ### Comparison of `wedgeEnd` with the Kulkarni–Nomizu product -/

/-- Pairing `wedgeEnd A B (u ∧ v)` with `z ∧ w` gives half the Kulkarni–Nomizu four-tensor of the
bilinear forms `(x, y) ↦ ⟪A x, y⟫` and `(x, y) ↦ ⟪B x, y⟫`. -/
theorem inner_wedgeEnd_ιMulti (A B : Module.End ℝ V) (u v z w : V) :
    ⟪wedgeEnd A B (exteriorPower.ιMulti ℝ 2 ![u, v]), exteriorPower.ιMulti ℝ 2 ![z, w]⟫ =
      (1 / 2 : ℝ) * kulkarniNomizu (innerₗ V ∘ₗ A) (innerₗ V ∘ₗ B) ![u, v, z, w] := by
  simp only [wedgeEnd_apply_ιMulti, smul_add, inner_add_left, real_inner_smul_left,
    exteriorPower.inner_ιMulti_two, kulkarniNomizu_apply, LinearMap.comp_apply, innerₗ_apply_apply]
  ring

/-- The four-tensor induced by `wedgeEnd A B` is half the Kulkarni–Nomizu four-tensor of
`⟪A ·, ·⟫` and `⟪B ·, ·⟫`. -/
@[simp]
theorem ofExteriorEnd_wedgeEnd (A B : Module.End ℝ V) :
    ofExteriorEnd (wedgeEnd A B) =
      (1 / 2 : ℝ) • kulkarniNomizu (innerₗ V ∘ₗ A) (innerₗ V ∘ₗ B) := by
  ext m; rw [vec4_eta m, ofExteriorEnd_apply, smul_apply, smul_eq_mul, inner_wedgeEnd_ιMulti]

/-- The symmetric wedge product of two symmetric endomorphisms is symmetric on `⋀[ℝ]^2 V` and
satisfies the first Bianchi identity. -/
theorem isBianchiEnd_wedgeEnd {A B : Module.End ℝ V} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    IsBianchiEnd (wedgeEnd A B) := by
  have hAs : LinearMap.BilinForm.IsSymm (innerₗ V ∘ₗ A) :=
    ⟨fun x y ↦ by simp [hA x y, real_inner_comm]⟩
  have hBs : LinearMap.BilinForm.IsSymm (innerₗ V ∘ₗ B) :=
    ⟨fun x y ↦ by simp [hB x y, real_inner_comm]⟩
  let r : algebraicCurvatureSubmodule V :=
    ⟨_, (algebraicCurvatureSubmodule V).smul_mem (1 / 2 : ℝ)
      (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_kulkarniNomizu hAs hBs))⟩
  have h : curvatureOperator r = wedgeEnd A B :=
    (curvatureOperator_eq_iff r _).mpr fun u v z w ↦ by
      simp only [r, smul_apply, smul_eq_mul, inner_wedgeEnd_ιMulti]
  exact h ▸ isBianchiEnd_curvatureOperator r

/-- For symmetric bilinear forms `h` and `k`, the curvature operator of `kulkarniNomizu h k` is
`2 • wedgeEnd A B`, where `A` and `B` are the Riesz endomorphisms representing `h` and `k`. -/
theorem curvatureOperator_kulkarniNomizu {h k : BilinForm ℝ V} (hh : h.IsSymm) (hk : k.IsSymm) :
    curvatureOperator
        ⟨kulkarniNomizu h k,
          mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_kulkarniNomizu hh hk)⟩ =
      (2 : ℝ) • wedgeEnd
        (h.symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner)
        (k.symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner) := by
  rw [curvatureOperator_eq_iff]; intro u v z w
  have H (b : BilinForm ℝ V) :
      innerₗ V ∘ₗ b.symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner = b :=
    LinearMap.ext₂ fun x y ↦ b.symmCompOfNondegenerate_left_apply TauCeti.nondegenerate_inner y x
  rw [LinearMap.smul_apply, real_inner_smul_left, inner_wedgeEnd_ιMulti, H h, H k]; ring

/-! ### The Bianchi exact sequence and the dimension formula -/

private structure IsPairSymm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : FourTensor V) : Prop where
  antisymm_first : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]
  antisymm_last : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]
  swap_pairs : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]

private def pairSymmSubmodule (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Submodule ℝ (FourTensor V) where
  carrier := {r | IsPairSymm r}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' hr hq :=
    ⟨fun u v z w ↦ by simp only [add_apply]; rw [hr.antisymm_first, hq.antisymm_first, neg_add],
      fun u v z w ↦ by simp only [add_apply]; rw [hr.antisymm_last, hq.antisymm_last, neg_add],
      fun u v z w ↦ by simp only [add_apply]; rw [hr.swap_pairs, hq.swap_pairs]⟩
  smul_mem' c r hr :=
    ⟨fun u v z w ↦ by simp only [smul_apply, smul_eq_mul]; rw [hr.antisymm_first, mul_neg],
      fun u v z w ↦ by simp only [smul_apply, smul_eq_mul]; rw [hr.antisymm_last, mul_neg],
      fun u v z w ↦ by simp only [smul_apply, smul_eq_mul]; rw [hr.swap_pairs]⟩

omit [FiniteDimensional ℝ V] in
private theorem IsPairSymm.self_first {r : FourTensor V} (hr : IsPairSymm r) (u z w : V) :
    r.toLinearMap₄ u u z w = 0 := by
  simp only [toLinearMap₄_apply]; linarith [hr.antisymm_first u u z w]

omit [FiniteDimensional ℝ V] in
private theorem IsPairSymm.self_last {r : FourTensor V} (hr : IsPairSymm r) (u v z : V) :
    r.toLinearMap₄ u v z z = 0 := by
  simp only [toLinearMap₄_apply]; linarith [hr.antisymm_last u v z z]

private def pairSymmToBilin (r : pairSymmSubmodule V) : BilinForm ℝ (⋀[ℝ]^2 V) :=
  r.1.toLinearMap₄.exteriorSquareBilinear r.2.self_first r.2.self_last

omit [FiniteDimensional ℝ V] in
@[simp]
private theorem pairSymmToBilin_ιMulti (r : pairSymmSubmodule V) (u v : Fin 2 → V) :
    pairSymmToBilin r (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
      r.1 ![u 0, u 1, v 0, v 1] :=
  LinearMap.exteriorSquareBilinear_ιMulti_ιMulti _ _ _ u v

private def symmBilinSubmodule (W : Type*) [AddCommGroup W] [Module ℝ W] :
    Submodule ℝ (BilinForm ℝ W) where
  carrier := {B | B.IsSymm}
  zero_mem' := ⟨fun _ _ ↦ rfl⟩
  add_mem' h₁ h₂ := ⟨fun x y ↦ by simp [h₁.eq x y, h₂.eq x y]⟩
  smul_mem' _ _ h := ⟨fun x y ↦ by simp [h.eq x y]⟩

private def pairSymmEquivSymmBilin :
    pairSymmSubmodule V ≃ₗ[ℝ] symmBilinSubmodule (⋀[ℝ]^2 V) where
  toFun r := ⟨pairSymmToBilin r,
    ⟨fun x y ↦ congr($(LinearMap.flip_exteriorSquareBilinear _ _ _ r.2.swap_pairs) y x)⟩⟩
  map_add' _ _ := Subtype.ext <| exteriorPower.linearMap_ext <| AlternatingMap.ext fun _ ↦
    exteriorPower.linearMap_ext <| AlternatingMap.ext fun _ ↦ by simp
  map_smul' _ _ := Subtype.ext <| exteriorPower.linearMap_ext <| AlternatingMap.ext fun _ ↦
    exteriorPower.linearMap_ext <| AlternatingMap.ext fun _ ↦ by simp
  invFun B := ⟨ofExteriorBilin B.1,
    ⟨fun u v z w ↦ by simp [ιMulti_two_swap v u], fun u v z w ↦ by simp [ιMulti_two_swap w z],
      fun u v z w ↦ by simp only [ofExteriorBilin_apply]; exact B.2.eq _ _⟩⟩
  left_inv _ := Subtype.ext <| toLinearMap₄_injective <| by ext; simp [ofExteriorBilin_apply]
  right_inv _ := Subtype.ext <| exteriorPower.linearMap_ext <| AlternatingMap.ext fun u ↦
    exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply]
      rw [pairSymmToBilin_ιMulti, ofExteriorBilin_apply, ← vec2_eta u, ← vec2_eta v]

private theorem finrank_symmBilinSubmodule (W : Type*) [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] :
    Module.finrank ℝ (symmBilinSubmodule W) = Nat.multichoose (Module.finrank ℝ W) 2 := by
  let eT : W ⊗[ℝ] W ≃ₗ[ℝ] BilinForm ℝ W := TauCeti.BilinForm.ofTensorEquiv
  have hmem (t : W ⊗[ℝ] W) : eT t ∈ symmBilinSubmodule W ↔ t ∈ TauCeti.symmetricTensors ℝ W := by
    change (eT t).IsSymm ↔ _; rw [TauCeti.BilinForm.ofTensorEquiv_apply,
      TauCeti.BilinForm.isSymm_ofTensor_iff]
  let eS : TauCeti.symmetricTensors ℝ W ≃ₗ[ℝ] symmBilinSubmodule W :=
    { toFun := fun t ↦ ⟨eT t.1, (hmem t.1).mpr t.2⟩
      map_add' := fun t₁ t₂ ↦ Subtype.ext (eT.map_add t₁.1 t₂.1)
      map_smul' := fun c t ↦ Subtype.ext (eT.map_smul c t.1)
      invFun := fun B ↦ ⟨eT.symm B.1, (hmem _).mp (by simp [eT, B.2])⟩
      left_inv := fun t ↦ Subtype.ext (eT.symm_apply_apply t.1)
      right_inv := fun B ↦ Subtype.ext (eT.apply_symm_apply B.1) }
  rw [← eS.finrank_eq, (TauCeti.symmetricTensorsEquivSymmetricPower ℝ W).finrank_eq,
    SymmetricPower.finrank_eq]

private theorem finrank_pairSymmSubmodule :
    Module.finrank ℝ (pairSymmSubmodule V) =
      Nat.multichoose ((Module.finrank ℝ V).choose 2) 2 := by
  rw [(pairSymmEquivSymmBilin (V := V)).finrank_eq, finrank_symmBilinSubmodule,
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

private abbrev cyc₁ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
private abbrev cyc₂ : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 0 1

private def bianchiAlternating : pairSymmSubmodule V →ₗ[ℝ] (V [⋀^Fin 4]→ₗ[ℝ] ℝ) where
  toFun r :=
    { r.1.toMultilinearMap + r.1.toMultilinearMap.domDomCongr cyc₁ +
        r.1.toMultilinearMap.domDomCongr cyc₂ with
      map_eq_zero_of_eq' := fun m _ _ hm hij ↦ by
        have hm0 : r.1 m = r.1 ![m 0, m 1, m 2, m 3] := congrArg r.1 (vec4_eta m)
        have hm1 : (m ∘ cyc₁) = ![m 1, m 2, m 0, m 3] := by funext k; fin_cases k <;> rfl
        have hm2 : (m ∘ cyc₂) = ![m 2, m 0, m 1, m 3] := by funext k; fin_cases k <;> rfl
        change r.1 m + r.1 (m ∘ cyc₁) + r.1 (m ∘ cyc₂) = 0
        rw [hm0, hm1, hm2]
        exact cyclic_eq_zero_of_eq r.1 r.2 m hm hij }
  map_add' r q := by
    ext m; change (r.1 m + q.1 m) + (r.1 (m ∘ cyc₁) + q.1 (m ∘ cyc₁)) +
      (r.1 (m ∘ cyc₂) + q.1 (m ∘ cyc₂)) =
      (r.1 m + r.1 (m ∘ cyc₁) + r.1 (m ∘ cyc₂)) + (q.1 m + q.1 (m ∘ cyc₁) + q.1 (m ∘ cyc₂)); ring
  map_smul' c r := by
    ext m; change c * r.1 m + c * r.1 (m ∘ cyc₁) + c * r.1 (m ∘ cyc₂) =
      c * (r.1 m + r.1 (m ∘ cyc₁) + r.1 (m ∘ cyc₂)); ring

omit [FiniteDimensional ℝ V] in
private theorem bianchiAlternating_apply_vec (r : pairSymmSubmodule V) (u v z w : V) :
    bianchiAlternating r ![u, v, z, w] =
      r.1 ![u, v, z, w] + r.1 ![v, z, u, w] + r.1 ![z, u, v, w] := by
  have hm1 : (![u, v, z, w] : Fin 4 → V) ∘ cyc₁ = ![v, z, u, w] := by funext k; fin_cases k <;> rfl
  have hm2 : (![u, v, z, w] : Fin 4 → V) ∘ cyc₂ = ![z, u, v, w] := by funext k; fin_cases k <;> rfl
  change r.1 ![u, v, z, w] + r.1 (![u, v, z, w] ∘ cyc₁) + r.1 (![u, v, z, w] ∘ cyc₂) = _
  rw [hm1, hm2]

private def alternatingToPairSymm : (V [⋀^Fin 4]→ₗ[ℝ] ℝ) →ₗ[ℝ] pairSymmSubmodule V where
  toFun ω :=
    ⟨{ ω.toMultilinearMap with cont := ω.toMultilinearMap.continuous_of_finiteDimensional },
      ⟨fun u v z w ↦ by
          have h : (![v, u, z, w] : Fin 4 → V) = ![u, v, z, w] ∘ Equiv.swap 0 1 := by
            funext k; fin_cases k <;> rfl
          change ω _ = -ω _; rw [h, ω.map_swap _ (by decide), neg_neg],
        fun u v z w ↦ by
          have h : (![u, v, w, z] : Fin 4 → V) = ![u, v, z, w] ∘ Equiv.swap 2 3 := by
            funext k; fin_cases k <;> rfl
          change ω _ = -ω _; rw [h, ω.map_swap _ (by decide), neg_neg],
        fun u v z w ↦ by
          let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
          have h : (![z, w, u, v] : Fin 4 → V) = ![u, v, z, w] ∘ σ := by
            funext k; fin_cases k <;> rfl
          have hs : Equiv.Perm.sign σ = 1 := by decide
          change ω _ = ω _; rw [h, ω.map_perm, hs, one_smul]⟩⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

private theorem bianchiAlternating_surjective :
    Function.Surjective (bianchiAlternating (V := V)) := fun ω ↦ by
  refine ⟨(1 / 3 : ℝ) • alternatingToPairSymm ω, ?_⟩
  ext m; rw [map_smul, smul_apply]
  have hs1 : Equiv.Perm.sign cyc₁ = 1 := by decide
  have hs2 : Equiv.Perm.sign cyc₂ = 1 := by decide
  change (1 / 3 : ℝ) * (ω m + ω (m ∘ cyc₁) + ω (m ∘ cyc₂)) = ω m
  rw [ω.map_perm m cyc₁, ω.map_perm m cyc₂, hs1, hs2, one_smul]; ring

private def kerBianchiEquivAlgebraicCurvature :
    LinearMap.ker (bianchiAlternating (V := V)) ≃ₗ[ℝ] algebraicCurvatureSubmodule V where
  toFun r := ⟨r.1.1, mem_algebraicCurvatureSubmodule.mpr ⟨r.1.2.antisymm_first,
    r.1.2.antisymm_last, r.1.2.swap_pairs, fun u v z w ↦ by
      simpa only [bianchiAlternating_apply_vec, zero_apply] using
        congr($(LinearMap.mem_ker.mp r.2) ![u, v, z, w])⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun r := ⟨⟨r.1, ⟨(sub_isCurv r).antisymm_first, (sub_isCurv r).antisymm_last,
      (sub_isCurv r).swap_pairs⟩⟩,
    LinearMap.mem_ker.mpr <| by
      ext m; rw [vec4_eta m, bianchiAlternating_apply_vec]
      exact (sub_isCurv r).cyclic_eq_zero ..⟩
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
  have hmul : (k + 3) ^ 2 * ((k + 4) * (k + 2)) =
      12 * ((k + 4).choose 4 + (k + 5).choose 4) := by
    refine Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) ?_
    linear_combination -choose_four_helper (k + 1) - choose_four_helper (k + 2)
  rw [hsub, hmul, Nat.mul_div_right _ (by decide : 0 < 12)]

private theorem choose_four_add_div_twelve (n : ℕ) :
    n.choose 4 + n ^ 2 * (n ^ 2 - 1) / 12 = Nat.multichoose (n.choose 2) 2 := by
  rcases n with _ | _ | _ | k
  · rw [Nat.multichoose_eq]; decide
  · rw [Nat.multichoose_eq]; decide
  · rw [Nat.multichoose_eq]; decide
  · rw [sq_mul_sq_sub_one_div_twelve]
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
        3 * (2 * (k + 3).choose 2 + 2) * (2 * (k + 3).choose 2) := by
      linear_combination 12 * hmc
    rw [h24r, hc2]
    linear_combination choose_four_helper k + choose_four_helper (k + 1) +
      choose_four_helper (k + 2)

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
theorem finrank_bianchiEndSubmodule :
    Module.finrank ℝ (bianchiEndSubmodule V) =
      (Module.finrank ℝ V) ^ 2 * ((Module.finrank ℝ V) ^ 2 - 1) / 12 := by
  rw [← (algebraicCurvatureEquivBianchiEnd V).finrank_eq,
    finrank_algebraicCurvatureSubmodule_of_inner]

/-- **In dimension `2`, every algebraic curvature tensor is `(Scal / 2)` times the
constant-curvature tensor.** -/
theorem IsAlgebraicCurvature.eq_smul_constantCurvature_of_finrank_eq_two
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V = 2) :
    r = (scalar r / 2) • constantCurvature V := by
  let b := (stdOrthonormalBasis ℝ V).reindex (finCongr hn)
  let i₀ : bianchiEndSubmodule V := ⟨LinearMap.id, isBianchiEnd_id⟩
  have hi_ne : i₀ ≠ 0 := fun h ↦ by
    have hval : ⟪(i₀.1 : Module.End ℝ (⋀[ℝ]^2 V)) (exteriorPower.ιMulti ℝ 2 ![b 0, b 1]),
        exteriorPower.ιMulti ℝ 2 ![b 0, b 1]⟫ = 1 := by
      simp [i₀, b.orthonormal.1, b.orthonormal.2 (by decide : (0 : Fin 2) ≠ 1)]
    rw [congrArg Subtype.val h] at hval; simp at hval
  have htop : Submodule.span ℝ {i₀} = ⊤ :=
    Submodule.eq_top_of_finrank_eq (K := ℝ) (V := bianchiEndSubmodule V)
      (S := Submodule.span ℝ {i₀}) (by
        rw [finrank_span_singleton (K := ℝ) (V := bianchiEndSubmodule V) hi_ne,
          finrank_bianchiEndSubmodule, hn]; decide)
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (htop.symm ▸ Submodule.mem_top :
    algebraicCurvatureEquivBianchiEnd V ⟨r, mem_algebraicCurvatureSubmodule.mpr hr⟩ ∈ _)
  have hop : curvatureOperator ⟨r, mem_algebraicCurvatureSubmodule.mpr hr⟩ =
      curvatureOperator (k • ⟨constantCurvature V,
        mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature⟩) := by
    rw [map_smul, curvatureOperator_constantCurvature]; exact (congrArg Subtype.val hk).symm
  have hrk : r = k • constantCurvature V := congrArg Subtype.val (curvatureOperator_injective hop)
  have hscal : scalar r = 2 * k := by
    rw [hrk, map_smul, scalar_constantCurvature, hn]; norm_num; ring
  rwa [show k = scalar r / 2 by linarith] at hrk

end Operator

section Dimension

private theorem lt_curv_dim_succ_three (m : ℕ) :
    m < (m + 3) ^ 2 * ((m + 3) ^ 2 - 1) / 12 := by
  have hsq : (m + 3) ^ 2 - 1 = (m + 4) * (m + 2) := by
    have : (m + 3) ^ 2 = (m + 4) * (m + 2) + 1 := by ring
    omega
  rw [hsq, show (m + 3) ^ 2 * ((m + 4) * (m + 2)) =
    m ^ 4 + 12 * m ^ 3 + 53 * m ^ 2 + 102 * m + 72 by ring]; omega

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
  change φ i (bp.equivFun.symm (eE x) : V) = eE x i
  rw [(hφ i).1]; exact congr_fun (bp.equivFun.apply_symm_apply (eE x)) i

private def pullbackAlgebraicCurvature {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (P : V →L[ℝ] W) :
    algebraicCurvatureSubmodule W →ₗ[ℝ] algebraicCurvatureSubmodule V where
  toFun r := ⟨r.1.compContinuousLinearMap fun _ ↦ P,
    compContinuousLinearMap_mem_algebraicCurvatureSubmodule r.2 _⟩
  map_add' _ _ := Subtype.ext <| by ext; rfl
  map_smul' _ _ := Subtype.ext <| by ext; rfl

private theorem pullbackAlgebraicCurvature_injective {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (P : V →L[ℝ] W)
    {J : W → V} (hPJ : ∀ x, P (J x) = x) :
    Function.Injective (pullbackAlgebraicCurvature P) := fun _ _ hrq ↦
  Subtype.ext <| ContinuousMultilinearMap.ext fun m ↦ by
    simpa [pullbackAlgebraicCurvature, ContinuousMultilinearMap.compContinuousLinearMap_apply, hPJ]
      using congr($(congrArg Subtype.val hrq) (fun i ↦ J (m i)))

private def algebraicCurvatureSubmoduleCongr {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃L[ℝ] W) :
    algebraicCurvatureSubmodule V ≃ₗ[ℝ] algebraicCurvatureSubmodule W :=
  LinearEquiv.ofLinearMap (pullbackAlgebraicCurvature e.symm.toContinuousLinearMap)
    (pullbackAlgebraicCurvature e.toContinuousLinearMap)
    (LinearMap.ext fun _ ↦ Subtype.ext <| by
      ext; simp [pullbackAlgebraicCurvature,
        ContinuousMultilinearMap.compContinuousLinearMap_apply])
    (LinearMap.ext fun _ ↦ Subtype.ext <| by
      ext; simp [pullbackAlgebraicCurvature,
        ContinuousMultilinearMap.compContinuousLinearMap_apply])

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
    rw [(algebraicCurvatureSubmoduleCongr e).finrank_eq,
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
        (pullbackAlgebraicCurvature_injective P hPJ)
      rw [finrank_algebraicCurvatureSubmodule_of_inner, finrank_euclideanSpace_fin] at hle
      exact not_lt_of_ge hle (lt_curv_dim_succ_three m)
    rw [Module.finrank_of_infinite_dimensional hnot, Module.finrank_of_infinite_dimensional hV]; rfl

end Dimension

end FourTensor

end TauCeti
