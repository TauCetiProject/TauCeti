/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.Instances.Unitary.Special
public import TauCeti.Topology.Grassmannian.SphereBundle.SpecialUnitary
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Householder

/-!
# The smooth sphere bundle `SU(n) → SU(1 + n) → S^(2n+1)`

The evaluation map `A ↦ A e₀` from `SU(1 + n)` to the unit sphere `S^(2n+1)` of `ℂ^(1 + n)`
(`TauCeti.specialUnitarySphereMap`) is a locally trivial bundle with fibre `SU(n)`, embedded by
`B ↦ diag(1, B)` (`TauCeti.exists_trivialization_specialUnitarySphereMap`). This file shows that it
is a smooth fibre bundle: it has an atlas of trivializations that are diffeomorphisms for the Lie
group structures of `SU(1 + n)` and `SU(n)` and the manifold structure of the sphere. For `n = 2`
this is the bundle `SU(2) → SU(3) → S⁵`. The map itself is smooth for every `n`
(`TauCeti.contMDiff_specialUnitarySphereMap`), and the block embedding `SU(n) → SU(1 + n)` is smooth
(`Matrix.specialUnitaryGroup.contMDiff_fromBlocksOne`).

The charts come from explicit smooth local sections. A unit vector `y` with `y₀ ≠ 0` has the phase
`ω = y₀ / |y₀|`, and `u = ω e₀ + y` satisfies `uᴴ u = 2 + 2 |y₀|`. The Householder reflection
`R = 1 - (1 + |y₀|)⁻¹ u uᴴ` in `u` sends `-ω e₀` to `y`, because `⟪-ω e₀, y⟫ = -|y₀|` is real,
and it has determinant `-1`. The diagonal matrix `D = diag(-ω, conj ω, 1, …, 1)` sends `e₀` to
`-ω e₀` and also has determinant `-1`. So `R D` is a special unitary matrix with first column `y`.
Its coefficients involve `ω` and `(1 + |y₀|)⁻¹` only, so it depends smoothly on `y` on the open set
`y₀ ≠ 0`, which contains `e₀`. Translating by `g ∈ SU(1 + n)` gives the section
`p ↦ g R(gᴴ p) D(gᴴ p)` over the open set `⟪g e₀, p⟫ ≠ 0` of the sphere. The chart of such a
section `s` sends `A` to `(A e₀, s(A e₀)⁻¹ A)`, read in `SU(n)` through its lower right block
(`Subgroup.localSectionTrivializationOfCosetFibers`), and its inverse sends `(p, B)` to
`s(p) diag(1, B)`. Both are smooth, because the group operations of `SU(1 + n)` are.

The smooth bundle structure is the input for pulling a Morse function on the sphere back to a
Morse–Bott function on `SU(1 + n)` whose critical manifolds are the fibres over its critical
points.

## Main definitions

* `TauCeti.specialUnitarySphereTrivialization g`: the smooth chart over `⟪g e₀, p⟫ ≠ 0`, with fibre
  `SU(n)`.
* `TauCeti.specialUnitarySphereAtlas n`: an atlas of these charts, one around each point of the
  sphere.

## Main results

* `TauCeti.contMDiff_specialUnitarySphereMap`: `A ↦ A e₀` is smooth.
* `TauCeti.contMDiffOn_specialUnitarySphereTrivialization`,
  `TauCeti.contMDiffOn_specialUnitarySphereTrivialization_symm`: the charts are diffeomorphisms
  between their source and target.
* `TauCeti.isContMDiff_specialUnitarySphereAtlas`: the atlas is smooth.
* `TauCeti.contMDiffFiberBundle_specialUnitarySphereAtlas`: the fibres of `A ↦ A e₀` form a smooth
  fibre bundle over `S^(2n+1)` with fibre `SU(n)`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (the fibre bundles
  `SU(n) → SU(n + 1) → S^(2n+1)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7 (local
  cross-sections of the coset spaces of the classical groups).
-/

public section

noncomputable section

open Matrix Metric Set
open scoped Manifold ContDiff InnerProductSpace Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti

open finiteOrthonormalFrame

variable {n : ℕ}

/-! ### A special unitary matrix with prescribed first column -/

/-- The phase `y₀ / |y₀|` of the first coordinate of `y`. -/
private def sphereSectionPhase (y : EuclideanSpace ℂ (Fin (1 + n))) : ℂ := ‖y 0‖⁻¹ • y 0

/-- The axis `ω e₀ + y` of the Householder reflection, for the phase `ω` of `y₀`. -/
private def sphereSectionAxis (y : EuclideanSpace ℂ (Fin (1 + n))) : Fin (1 + n) → ℂ :=
  sphereSectionPhase y • Pi.single 0 1 + WithLp.ofLp y

/-- The diagonal entries `(-ω, conj ω, 1, …, 1)`, for the phase `ω` of `y₀`. -/
private def sphereSectionDiag [NeZero n] (y : EuclideanSpace ℂ (Fin (1 + n))) : Fin (1 + n) → ℂ :=
  Function.update (Function.update 1 (Fin.natAdd 1 0) (star (sphereSectionPhase y))) 0
    (-sphereSectionPhase y)

/-- The diagonal matrix `diag(-ω, conj ω, 1, …, 1)` followed by the Householder reflection in the
axis `ω e₀ + y`: for a unit vector `y` with `y₀ ≠ 0` it is a special unitary matrix with first
column `y`. -/
private def sphereSectionMatrix [NeZero n] (y : EuclideanSpace ℂ (Fin (1 + n))) :
    Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ :=
  (1 - (1 + ‖y 0‖)⁻¹ • vecMulVec (sphereSectionAxis y) (star (sphereSectionAxis y))) *
    diagonal (sphereSectionDiag y)

variable {y : EuclideanSpace ℂ (Fin (1 + n))}

private theorem natAdd_one_zero_ne_zero [NeZero n] :
    (Fin.natAdd 1 (0 : Fin n) : Fin (1 + n)) ≠ 0 :=
  fun h ↦ by simpa using congrArg Fin.val h

private theorem star_sphereSectionPhase_mul_self (h0 : y 0 ≠ 0) :
    star (sphereSectionPhase y) * sphereSectionPhase y = 1 := by
  have : (‖y 0‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  simp only [sphereSectionPhase, Complex.real_smul, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  rw [mul_mul_mul_comm, Complex.conj_mul']
  push_cast
  field_simp

private theorem star_sphereSectionPhase_mul (h0 : y 0 ≠ 0) :
    star (sphereSectionPhase y) * y 0 = ‖y 0‖ := by
  have : (‖y 0‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  simp only [sphereSectionPhase, Complex.real_smul, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  rw [mul_assoc, Complex.conj_mul']
  push_cast
  field_simp

private theorem star_mul_sphereSectionPhase (h0 : y 0 ≠ 0) :
    star (y 0) * sphereSectionPhase y = ‖y 0‖ := by
  rw [← star_star (sphereSectionPhase y), ← star_mul, star_sphereSectionPhase_mul h0,
    Complex.star_def, Complex.conj_ofReal]

/-- The Hermitian square of the axis `ω e₀ + y` of a unit vector `y` is `2 + 2 |y₀|`. -/
private theorem star_sphereSectionAxis_dotProduct_self (hy : ‖y‖ = 1) (h0 : y 0 ≠ 0) :
    star (sphereSectionAxis y) ⬝ᵥ sphereSectionAxis y = algebraMap ℝ ℂ (2 + 2 * ‖y 0‖) := by
  have hyy : star (WithLp.ofLp y) ⬝ᵥ WithLp.ofLp y = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hy]
    simp
  simp only [sphereSectionAxis, star_add, add_dotProduct, dotProduct_add, hyy, star_smul,
    smul_dotProduct, dotProduct_smul, Pi.star_single, star_one, single_dotProduct,
    dotProduct_single, one_mul, mul_one, smul_eq_mul, Complex.coe_algebraMap]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  push_cast
  linear_combination star_sphereSectionPhase_mul h0 + star_mul_sphereSectionPhase h0 +
    star_sphereSectionPhase_mul_self h0

private theorem reflection_mem_unitary (hy : ‖y‖ = 1) (h0 : y 0 ≠ 0) :
    1 - (1 + ‖y 0‖)⁻¹ • vecMulVec (sphereSectionAxis y) (star (sphereSectionAxis y)) ∈
      unitary (Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) := by
  refine one_sub_smul_vecMulVec_mem_unitary (star_sphereSectionAxis_dotProduct_self hy h0) ?_
  have : (1 + ‖y 0‖) ≠ 0 := by positivity
  field_simp

private theorem det_reflection (hy : ‖y‖ = 1) (h0 : y 0 ≠ 0) :
    (1 - (1 + ‖y 0‖)⁻¹ • vecMulVec (sphereSectionAxis y) (star (sphereSectionAxis y))).det =
      -1 := by
  rw [← smul_vecMulVec, det_one_sub_vecMulVec, dotProduct_smul,
    star_sphereSectionAxis_dotProduct_self hy h0]
  have : (1 + (‖y 0‖ : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (1 + ‖y 0‖) ≠ 0)
  rw [Complex.coe_algebraMap, Complex.real_smul]
  push_cast
  field_simp
  ring

private theorem diagonal_sphereSectionDiag_mem_unitary [NeZero n] (h0 : y 0 ≠ 0) :
    diagonal (sphereSectionDiag y) ∈ unitary (Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) := by
  have h1 : starRingEnd ℂ (sphereSectionPhase y) * sphereSectionPhase y = 1 :=
    star_sphereSectionPhase_mul_self h0
  rw [diagonal_mem_unitary, Unitary.mem_iff]
  constructor <;> ext i <;>
    simp only [sphereSectionDiag, Pi.mul_apply, Pi.star_apply, Function.update_apply,
      Pi.one_apply] <;>
    split_ifs <;> simp [h1, mul_comm (sphereSectionPhase y)]

private theorem det_diagonal_sphereSectionDiag [NeZero n] (h0 : y 0 ≠ 0) :
    (diagonal (sphereSectionDiag y)).det = -1 := by
  rw [det_diagonal, sphereSectionDiag, Finset.prod_update_of_mem (Finset.mem_univ _),
    Finset.prod_update_of_mem (by simpa using natAdd_one_zero_ne_zero (n := n))]
  simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
  rw [neg_mul, mul_comm, star_sphereSectionPhase_mul_self h0]

private theorem sphereSectionMatrix_mem_specialUnitaryGroup [NeZero n] (hy : ‖y‖ = 1)
    (h0 : y 0 ≠ 0) : sphereSectionMatrix y ∈ specialUnitaryGroup (Fin (1 + n)) ℂ := by
  rw [mem_specialUnitaryGroup_iff]
  refine ⟨mul_mem (reflection_mem_unitary hy h0) (diagonal_sphereSectionDiag_mem_unitary h0), ?_⟩
  rw [sphereSectionMatrix, det_mul, det_reflection hy h0, det_diagonal_sphereSectionDiag h0]
  norm_num

/-- The first column of the section matrix of `y` is `y`: the diagonal factor sends `e₀` to
`-ω e₀`, and the reflection sends `-ω e₀` to `y`. -/
private theorem sphereSectionMatrix_mulVec_single_zero [NeZero n] (h0 : y 0 ≠ 0) :
    sphereSectionMatrix y *ᵥ Pi.single 0 1 = WithLp.ofLp y := by
  have hD : diagonal (sphereSectionDiag y) *ᵥ Pi.single 0 1 =
      Pi.single 0 (-sphereSectionPhase y) := by
    rw [diagonal_mulVec_single, sphereSectionDiag, Function.update_self, mul_one]
  -- The only computation: the axis pairs with `-ω e₀` to `-(1 + |y₀|)`.
  have ha : star (sphereSectionAxis y) 0 * -sphereSectionPhase y = -(1 + (‖y 0‖ : ℂ)) := by
    simp only [sphereSectionAxis, Pi.star_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one, star_add]
    linear_combination (-1 : ℂ) * star_sphereSectionPhase_mul_self h0 -
      star_mul_sphereSectionPhase h0
  have hc : (1 + ‖y 0‖)⁻¹ • (-(1 + (‖y 0‖ : ℂ))) = -1 := by
    have : (1 + (‖y 0‖ : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (1 + ‖y 0‖) ≠ 0)
    rw [Complex.real_smul]
    push_cast
    field_simp
  rw [sphereSectionMatrix, ← mulVec_mulVec, hD, one_sub_smul_vecMulVec_mulVec, dotProduct_single,
    op_smul_eq_smul, ha, ← smul_assoc, hc, neg_one_smul, sub_neg_eq_add, sphereSectionAxis]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [hi]

private theorem sphereSectionMatrix_apply [NeZero n] (i k : Fin (1 + n)) :
    sphereSectionMatrix y i k =
      ((1 : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) i k -
        (1 + ‖y 0‖)⁻¹ • (sphereSectionAxis y i * star (sphereSectionAxis y k))) *
          sphereSectionDiag y k := by
  simp [sphereSectionMatrix, mul_diagonal, vecMulVec_apply]

/-- The section matrix depends smoothly on `y` where `y₀ ≠ 0`: its entries are built from the
coordinates of `y`, their conjugates, the phase `y₀ / |y₀|` and `(1 + |y₀|)⁻¹`. -/
private theorem contDiffOn_sphereSectionMatrix [NeZero n] :
    ContDiffOn ℝ ∞ (sphereSectionMatrix (n := n)) {y | y 0 ≠ 0} := by
  set s : Set (EuclideanSpace ℂ (Fin (1 + n))) := {y | y 0 ≠ 0}
  have hcoord (i : Fin (1 + n)) : ContDiff ℝ ∞ fun y : EuclideanSpace ℂ (Fin (1 + n)) ↦ y i :=
    contDiff_piLp_apply (𝕜 := ℝ) 2
  have hnorm : ContDiffOn ℝ ∞ (fun y : EuclideanSpace ℂ (Fin (1 + n)) ↦ ‖y 0‖) s :=
    fun y hy ↦ ((contDiffAt_norm ℝ hy).comp y (hcoord 0).contDiffAt).contDiffWithinAt
  have hphase : ContDiffOn ℝ ∞ (sphereSectionPhase (n := n)) s :=
    (hnorm.inv fun _ hy ↦ norm_ne_zero_iff.2 hy).smul (hcoord 0).contDiffOn
  have hc : ContDiffOn ℝ ∞ (fun y : EuclideanSpace ℂ (Fin (1 + n)) ↦ (1 + ‖y 0‖)⁻¹) s :=
    (contDiffOn_const.add hnorm).inv fun _ _ ↦ by positivity
  have hstar {f : EuclideanSpace ℂ (Fin (1 + n)) → ℂ} (hf : ContDiffOn ℝ ∞ f s) :
      ContDiffOn ℝ ∞ (fun y ↦ star (f y)) s :=
    Complex.conjCLE.contDiff.comp_contDiffOn hf
  have haxis (i : Fin (1 + n)) : ContDiffOn ℝ ∞ (fun y ↦ sphereSectionAxis y i) s := by
    simp only [sphereSectionAxis, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (hphase.mul contDiffOn_const).add (hcoord i).contDiffOn
  have hdiag (k : Fin (1 + n)) : ContDiffOn ℝ ∞ (fun y ↦ sphereSectionDiag y k) s := by
    simp only [sphereSectionDiag, Function.update_apply, Pi.one_apply]
    split_ifs
    · exact hphase.neg
    · exact hstar hphase
    · exact contDiffOn_const
  have hentries : ContDiffOn ℝ ∞ (fun y i k ↦ sphereSectionMatrix (n := n) y i k) s := by
    refine contDiffOn_pi.2 fun i ↦ contDiffOn_pi.2 fun k ↦ ?_
    simp only [sphereSectionMatrix_apply]
    exact (contDiffOn_const.sub (hc.smul ((haxis i).mul (hstar (haxis k))))).mul (hdiag k)
  exact ((ofLinearEquiv ℝ : (Fin (1 + n) → Fin (1 + n) → ℂ) ≃ₗ[ℝ] _).toLinearMap
    |>.toContinuousLinearMap).contDiff.comp_contDiffOn hentries

/-! ### Smoothness of `A ↦ A e₀` -/

/-- The evaluation map `A ↦ A e₀` from `SU(1 + n)` to the unit sphere `S^(2n+1)` of `ℂ^(1 + n)` is
smooth. -/
theorem contMDiff_specialUnitarySphereMap :
    ContMDiff (specialUnitaryGroup.model (Fin (1 + n)) ℂ) (𝓡 (2 * n + 1)) ∞
      (specialUnitarySphereMap (𝕜 := ℂ) n) := by
  let L : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ →ₗ[ℝ] EuclideanSpace ℂ (Fin (1 + n)) :=
    { toFun M := WithLp.toLp 2 (M.col 0)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have h : ContMDiff (specialUnitaryGroup.model (Fin (1 + n)) ℂ)
      𝓘(ℝ, EuclideanSpace ℂ (Fin (1 + n))) ∞ fun A : specialUnitaryGroup (Fin (1 + n)) ℂ ↦ L A :=
    L.toContinuousLinearMap.contDiff.contMDiff.comp specialUnitaryGroup.contMDiff_val
  have hL (A : specialUnitaryGroup (Fin (1 + n)) ℂ) :
      L A = (specialUnitarySphereMap n A : EuclideanSpace ℂ (Fin (1 + n))) :=
    (coe_specialUnitarySphereMap A).symm
  convert h.codRestrict_sphere fun A ↦ hL A ▸ (specialUnitarySphereMap n A).property using 1
  ext A : 2
  exact (hL A).symm

/-! ### Smooth local sections over the sphere -/

/-- The vector `g⁻¹ x = gᴴ x`. -/
private def sphereRotate (g : specialUnitaryGroup (Fin (1 + n)) ℂ)
    (x : EuclideanSpace ℂ (Fin (1 + n))) : EuclideanSpace ℂ (Fin (1 + n)) :=
  UnitaryGroup.toLinearIsometryEquiv ⟨star (g : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ),
    Unitary.star_mem g.property.1⟩ x

/-- The first coordinate of `gᴴ x` is `⟪g e₀, x⟫`. -/
private theorem sphereRotate_apply_zero (g : specialUnitaryGroup (Fin (1 + n)) ℂ)
    (x : EuclideanSpace ℂ (Fin (1 + n))) :
    sphereRotate g x 0 = ⟪(specialUnitarySphereMap n g : EuclideanSpace ℂ (Fin (1 + n))), x⟫_ℂ := by
  rw [sphereRotate, UnitaryGroup.toLinearIsometryEquiv_apply, coe_specialUnitarySphereMap,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [mulVec, dotProduct, mul_comm]

private theorem norm_sphereRotate (g : specialUnitaryGroup (Fin (1 + n)) ℂ)
    (x : EuclideanSpace ℂ (Fin (1 + n))) : ‖sphereRotate g x‖ = ‖x‖ :=
  LinearIsometryEquiv.norm_map _ x

private theorem contDiff_sphereRotate (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    ContDiff ℝ ∞ (sphereRotate g) :=
  (UnitaryGroup.toLinearIsometryEquiv ⟨star (g : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ),
    Unitary.star_mem g.property.1⟩).toContinuousLinearEquiv.contDiff.restrict_scalars ℝ

/-- The domain `⟪g e₀, p⟫ ≠ 0` of the local section through `g`. -/
private def sphereSectionDomain (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    Set (sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1) :=
  {p | ⟪(specialUnitarySphereMap n g : EuclideanSpace ℂ (Fin (1 + n))), p⟫_ℂ ≠ 0}

private theorem isOpen_sphereSectionDomain (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    IsOpen (sphereSectionDomain g) :=
  isOpen_ne_fun (continuous_const.inner continuous_subtypeVal) continuous_const

private theorem mem_sphereSectionDomain (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    specialUnitarySphereMap n g ∈ sphereSectionDomain g := by
  rw [sphereSectionDomain, mem_ofPred_eq, inner_self_eq_norm_sq_to_K, norm_eq_of_mem_sphere]
  simp

variable [NeZero n]

open Classical in
/-- The local section `p ↦ g R(gᴴ p) D(gᴴ p)` of `A ↦ A e₀` over `⟪g e₀, p⟫ ≠ 0`, extended
by `1`. -/
private def sphereLocalSection (g : specialUnitaryGroup (Fin (1 + n)) ℂ)
    (p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1) : specialUnitaryGroup (Fin (1 + n)) ℂ :=
  if hp : p ∈ sphereSectionDomain g then
    g * ⟨sphereSectionMatrix (sphereRotate g p), sphereSectionMatrix_mem_specialUnitaryGroup
      (by rw [norm_sphereRotate, norm_eq_of_mem_sphere]) (by rwa [sphereRotate_apply_zero])⟩
  else 1

private theorem coe_sphereLocalSection {g : specialUnitaryGroup (Fin (1 + n)) ℂ}
    {p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1} (hp : p ∈ sphereSectionDomain g) :
    (sphereLocalSection g p : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) =
      g * sphereSectionMatrix (sphereRotate g p) := by
  simp [sphereLocalSection, hp]

private theorem specialUnitarySphereMap_sphereLocalSection
    {g : specialUnitaryGroup (Fin (1 + n)) ℂ} {p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1}
    (hp : p ∈ sphereSectionDomain g) : specialUnitarySphereMap n (sphereLocalSection g p) = p := by
  have h0 : sphereRotate g p 0 ≠ 0 := by rwa [sphereRotate_apply_zero]
  ext1
  rw [coe_specialUnitarySphereMap, coe_sphereLocalSection hp, ← mulVec_single_one,
    ← mulVec_mulVec, sphereSectionMatrix_mulVec_single_zero h0, sphereRotate,
    UnitaryGroup.toLinearIsometryEquiv_apply, WithLp.ofLp_toLp, mulVec_mulVec]
  rw [Unitary.mul_star_self_of_mem g.property.1, one_mulVec, WithLp.toLp_ofLp]

private theorem contMDiffOn_sphereLocalSection (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    ContMDiffOn (𝓡 (2 * n + 1)) (specialUnitaryGroup.model (Fin (1 + n)) ℂ) ∞
      (sphereLocalSection g) (sphereSectionDomain g) := by
  rw [specialUnitaryGroup.contMDiffOn_iff]
  have h : ContDiffOn ℝ ∞ (fun y ↦ (g : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) *
      sphereSectionMatrix (sphereRotate g y)) {y | sphereRotate g y 0 ≠ 0} :=
    contDiffOn_const.mul (contDiffOn_sphereSectionMatrix.comp (contDiff_sphereRotate g).contDiffOn
      fun _ hy ↦ hy)
  refine (h.contMDiffOn.comp contMDiff_coe_sphere.contMDiffOn fun p hp ↦ ?_).congr
    fun p hp ↦ coe_sphereLocalSection hp
  rw [mem_preimage, mem_ofPred_eq, sphereRotate_apply_zero]
  exact hp

/-! ### The smooth charts -/

/-- **A smooth chart of `SU(n) → SU(1 + n) → S^(2n+1)`** over the open set `⟪g e₀, p⟫ ≠ 0` of the
sphere, for `g ∈ SU(1 + n)`. For the smooth local section `s` of `A ↦ A e₀` through `g` over this
set, it sends `A` to `(A e₀, B)`, where `diag(1, B) = s(A e₀)⁻¹ A`, and its inverse sends `(p, B)`
to `s(p) diag(1, B)`. -/
def specialUnitarySphereTrivialization (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    Bundle.Trivialization (specialUnitaryGroup (Fin n) ℂ) (specialUnitarySphereMap (𝕜 := ℂ) n) :=
  (Subgroup.localSectionTrivializationOfCosetFibers
    (specialUnitaryStabilizer ℂ (Nat.le_add_right 1 n)) (continuous_specialUnitarySphereMap ℂ n)
    (fun _ _ ↦ specialUnitarySphereMap_eq_specialUnitarySphereMap_iff) (sphereSectionDomain g)
    (isOpen_sphereSectionDomain g) (sphereLocalSection g)
    (contMDiffOn_sphereLocalSection g).continuousOn
    fun _ hp ↦ specialUnitarySphereMap_sphereLocalSection hp).transFiberHomeomorph
    (specialUnitaryStabilizerHomeomorph ℂ 1 n).symm

/-- The chart through `g` lives over the points `p` of the sphere with `⟪g e₀, p⟫ ≠ 0`. -/
@[simp]
theorem specialUnitarySphereTrivialization_baseSet (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    (specialUnitarySphereTrivialization g).baseSet =
      {p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1 |
        ⟪(specialUnitarySphereMap n g : EuclideanSpace ℂ (Fin (1 + n))), p⟫_ℂ ≠ 0} :=
  Subgroup.localSectionTrivializationOfCosetFibers_baseSet

/-- The chart through `g` is defined at `g e₀`. -/
theorem mem_specialUnitarySphereTrivialization_baseSet (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    specialUnitarySphereMap n g ∈ (specialUnitarySphereTrivialization g).baseSet := by
  rw [specialUnitarySphereTrivialization_baseSet]
  exact mem_sphereSectionDomain g

/-- The chart `A ↦ (A e₀, B)`, with `diag(1, B) = s(A e₀)⁻¹ A`, is smooth on its source. -/
theorem contMDiffOn_specialUnitarySphereTrivialization (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    ContMDiffOn (specialUnitaryGroup.model (Fin (1 + n)) ℂ)
      ((𝓡 (2 * n + 1)).prod (specialUnitaryGroup.model (Fin n) ℂ)) ∞
      (specialUnitarySphereTrivialization g) (specialUnitarySphereTrivialization g).source := by
  set e := specialUnitarySphereTrivialization g
  have hsrc : e.source = specialUnitarySphereMap n ⁻¹' sphereSectionDomain g := by
    rw [e.source_eq, specialUnitarySphereTrivialization_baseSet]
    rfl
  have h₁ : ContMDiffOn (specialUnitaryGroup.model (Fin (1 + n)) ℂ) (𝓡 (2 * n + 1)) ∞
      (fun A ↦ (e A).1) e.source :=
    contMDiff_specialUnitarySphereMap.contMDiffOn.congr fun A hA ↦ e.coe_fst hA
  -- The fibre coordinate of `A` is the lower right block of `s(A e₀)⁻¹ A`.
  let S : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun M := M.submatrix (Fin.natAdd 1) (Fin.natAdd 1)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hs : ContMDiffOn (specialUnitaryGroup.model (Fin (1 + n)) ℂ)
      (specialUnitaryGroup.model (Fin (1 + n)) ℂ) ∞
      (fun A ↦ (sphereLocalSection g (specialUnitarySphereMap n A))⁻¹ * A) e.source := by
    rw [hsrc]
    exact ((contMDiffOn_sphereLocalSection g).comp contMDiff_specialUnitarySphereMap.contMDiffOn
      fun _ hA ↦ hA).inv.mul contMDiffOn_id
  have h₂ : ContMDiffOn (specialUnitaryGroup.model (Fin (1 + n)) ℂ)
      (specialUnitaryGroup.model (Fin n) ℂ) ∞ (fun A ↦ (e A).2) e.source := by
    rw [specialUnitaryGroup.contMDiffOn_iff]
    refine (S.toContinuousLinearMap.contDiff.contMDiff.comp_contMDiffOn
      (specialUnitaryGroup.contMDiff_val.comp_contMDiffOn hs)).congr fun A hA ↦ ?_
    rw [hsrc] at hA
    simp only [e, specialUnitarySphereTrivialization,
      Bundle.Trivialization.transFiberHomeomorph_apply,
      coe_specialUnitaryStabilizerHomeomorph_symm_apply, Function.comp_apply]
    rw [Subgroup.localSectionTrivializationOfCosetFibers_fiberCoordinate
      (π := specialUnitarySphereMap (𝕜 := ℂ) n) (U := sphereSectionDomain g) (g := A) hA]
    rfl
  exact h₁.prodMk h₂

/-- The inverse chart `(p, B) ↦ s(p) diag(1, B)` is smooth on its source. -/
theorem contMDiffOn_specialUnitarySphereTrivialization_symm
    (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    ContMDiffOn ((𝓡 (2 * n + 1)).prod (specialUnitaryGroup.model (Fin n) ℂ))
      (specialUnitaryGroup.model (Fin (1 + n)) ℂ) ∞
      (specialUnitarySphereTrivialization g).toOpenPartialHomeomorph.symm
      (specialUnitarySphereTrivialization g).target := by
  rw [(specialUnitarySphereTrivialization g).target_eq]
  -- The inverse chart is `(p, B) ↦ s(p) * diag(1, B)` by definition.
  refine (((contMDiffOn_sphereLocalSection g).comp contMDiffOn_fst
    fun _ hp ↦ by simpa [sphereSectionDomain] using (mem_prod.1 hp).1).mul
    ((specialUnitaryGroup.contMDiff_fromBlocksOne 1 n).comp contMDiff_snd).contMDiffOn).congr
    fun x _ ↦ ?_
  refine (Subgroup.localSectionTrivializationOfCosetFibers_symm_apply
    (x.1, specialUnitaryStabilizerHomeomorph ℂ 1 n x.2)).trans ?_
  rw [coe_specialUnitaryStabilizerHomeomorph_apply]
  rfl

/-! ### The smooth bundle -/

variable (n) in
/-- An atlas of smooth charts of `SU(n) → SU(1 + n) → S^(2n+1)`: around `p` it takes the chart
`TauCeti.specialUnitarySphereTrivialization g` through a chosen `g` with `g e₀ = p`. -/
def specialUnitarySphereAtlas :
    MapFiber.Atlas (specialUnitaryGroup (Fin n) ℂ) (specialUnitarySphereMap (𝕜 := ℂ) n) where
  trivAt p := specialUnitarySphereTrivialization (surjective_specialUnitarySphereMap p).choose
  mem_baseSet_trivAt p := by
    simpa only [(surjective_specialUnitarySphereMap p).choose_spec] using
      mem_specialUnitarySphereTrivialization_baseSet
        (surjective_specialUnitarySphereMap (𝕜 := ℂ) p).choose

/-- The charts of `TauCeti.specialUnitarySphereAtlas` are diffeomorphisms onto their images. -/
theorem isContMDiff_specialUnitarySphereAtlas :
    (specialUnitarySphereAtlas n).IsContMDiff ∞ (𝓡 (2 * n + 1))
      (specialUnitaryGroup.model (Fin n) ℂ) (specialUnitaryGroup.model (Fin (1 + n)) ℂ) where
  contMDiffOn_trivAt _ := contMDiffOn_specialUnitarySphereTrivialization _
  contMDiffOn_trivAt_symm _ := contMDiffOn_specialUnitarySphereTrivialization_symm _

/-- **`SU(n) → SU(1 + n) → S^(2n+1)` is a smooth fibre bundle.** For `n ≥ 1`, the fibres of
`A ↦ A e₀` form a smooth fibre bundle over the sphere `S^(2n+1)` with fibre `SU(n)`. For `n = 2`
this is `SU(2) → SU(3) → S⁵`. -/
theorem contMDiffFiberBundle_specialUnitarySphereAtlas :
    letI := (specialUnitarySphereAtlas n).fiberBundle
    ContMDiffFiberBundle ∞ (specialUnitaryGroup (Fin n) ℂ)
      (MapFiber (specialUnitarySphereMap (𝕜 := ℂ) n)) (𝓡 (2 * n + 1))
      (specialUnitaryGroup.model (Fin n) ℂ) :=
  MapFiber.Atlas.contMDiffFiberBundle isContMDiff_specialUnitarySphereAtlas

end TauCeti
