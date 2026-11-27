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
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Householder
public import TauCeti.Topology.Grassmannian.SphereBundle.SpecialUnitary
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Matrix.UnitaryGroup.Householder
import TauCeti.Topology.FiberBundle.Trivialization

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
`-ω e₀` and also has determinant `-1`. So `R D` is a special unitary matrix with first column `y`
(`Matrix.householderSpecialUnitary`).
Its coefficients involve `ω` and `(1 + |y₀|)⁻¹` only, so it depends smoothly on `y` on the open set
`y₀ ≠ 0`, which contains `e₀` (`Matrix.contDiffOn_householderSpecialUnitary`). Translating by
`g ∈ SU(1 + n)` gives the section `p ↦ g R(gᴴ p) D(gᴴ p)` over the open set `⟪g e₀, p⟫ ≠ 0` of the
sphere (`TauCeti.specialUnitarySphereLocalSection`). The chart of such a
section `s` sends `A` to `(A e₀, s(A e₀)⁻¹ A)`, read in `SU(n)` through its lower right block
(`Subgroup.localSectionTrivializationOfCosetFibers`), and its inverse sends `(p, B)` to
`s(p) diag(1, B)`. Both are smooth, because the group operations of `SU(1 + n)` are.

The smooth bundle structure is the input for pulling a Morse function on the sphere back to a
Morse–Bott function on `SU(1 + n)` whose critical manifolds are the fibres over its critical
points.

## Main definitions

* `TauCeti.specialUnitarySphereLocalSection g`: the smooth local section of `A ↦ A e₀` over
  `⟪g e₀, p⟫ ≠ 0`.
* `TauCeti.specialUnitarySphereTrivialization g`: the smooth chart over `⟪g e₀, p⟫ ≠ 0`, with fibre
  `SU(n)`.
* `TauCeti.specialUnitarySphereAtlas n`: an atlas of these charts, one around each point of the
  sphere.

## Main results

* `TauCeti.contMDiff_specialUnitarySphereMap`: `A ↦ A e₀` is smooth.
* `TauCeti.specialUnitarySphereMap_specialUnitarySphereLocalSection`,
  `TauCeti.contMDiffOn_specialUnitarySphereLocalSection`: the local sections are smooth sections.
* `TauCeti.specialUnitarySphereTrivialization_symm_apply`,
  `TauCeti.coe_specialUnitarySphereTrivialization_apply_snd`: the inverse chart is
  `(p, B) ↦ s(p) diag(1, B)`, and the fibre coordinate of `A` is the lower right block of
  `s(A e₀)⁻¹ A`.
* `TauCeti.contMDiffOn_specialUnitarySphereTrivialization`,
  `TauCeti.contMDiffOn_specialUnitarySphereTrivialization_symm`: the charts are diffeomorphisms
  between their source and target.
* `TauCeti.specialUnitarySphereTrivialization_symm_apply_mul`: the inverse charts intertwine right
  multiplication on `SU(n)` with right multiplication by `diag(1, C)` on `SU(1 + n)`.
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

private theorem natAdd_one_zero_ne_zero [NeZero n] :
    (Fin.natAdd 1 (0 : Fin n) : Fin (1 + n)) ≠ 0 :=
  fun h ↦ by simpa using congrArg Fin.val h

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

/-- Over the domain of the local section through `g`, the first coordinate of `gᴴ p` is nonzero. -/
private theorem sphereRotate_apply_zero_ne_zero {g : specialUnitaryGroup (Fin (1 + n)) ℂ}
    {p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1} (hp : p ∈ sphereSectionDomain g) :
    sphereRotate g p 0 ≠ 0 := by
  rwa [sphereRotate_apply_zero]

/-- On the sphere, `gᴴ p` is a unit vector. -/
private theorem star_ofLp_sphereRotate_dotProduct (g : specialUnitaryGroup (Fin (1 + n)) ℂ)
    (p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1) :
    star (WithLp.ofLp (sphereRotate g p)) ⬝ᵥ WithLp.ofLp (sphereRotate g p) = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    norm_sphereRotate, norm_eq_of_mem_sphere]
  simp

private theorem ofLp_sphereRotate (g : specialUnitaryGroup (Fin (1 + n)) ℂ)
    (x : EuclideanSpace ℂ (Fin (1 + n))) :
    WithLp.ofLp (sphereRotate g x) =
      star (g : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) *ᵥ WithLp.ofLp x := by
  rw [sphereRotate, UnitaryGroup.toLinearIsometryEquiv_apply, WithLp.ofLp_toLp]

variable [NeZero n]

open Classical in
/-- **A smooth local section of `A ↦ A e₀`** over the open set `⟪g e₀, p⟫ ≠ 0` of the sphere, for
`g ∈ SU(1 + n)`. It sends `p` to `g R D`, where `R D = Matrix.householderSpecialUnitary` is the
special unitary matrix with first column `gᴴ p` built from a Householder reflection `R` and a
diagonal phase correction `D`. Outside this set it is `1`. -/
def specialUnitarySphereLocalSection (g : specialUnitaryGroup (Fin (1 + n)) ℂ)
    (p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1) : specialUnitaryGroup (Fin (1 + n)) ℂ :=
  if hp : p ∈ sphereSectionDomain g then
    g * ⟨householderSpecialUnitary 0 (Fin.natAdd 1 0) (WithLp.ofLp (sphereRotate g p)),
      householderSpecialUnitary_mem_specialUnitaryGroup (star_ofLp_sphereRotate_dotProduct g p)
        (sphereRotate_apply_zero_ne_zero hp) natAdd_one_zero_ne_zero⟩
  else 1

private theorem coe_specialUnitarySphereLocalSection_of_mem
    {g : specialUnitaryGroup (Fin (1 + n)) ℂ} {p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1}
    (hp : p ∈ sphereSectionDomain g) :
    (specialUnitarySphereLocalSection g p : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) =
      g * householderSpecialUnitary 0 (Fin.natAdd 1 0) (WithLp.ofLp (sphereRotate g p)) := by
  simp [specialUnitarySphereLocalSection, hp]

/-- Over `⟪g e₀, p⟫ ≠ 0`, the local section through `g` is `g R D`, for the special unitary matrix
`R D = Matrix.householderSpecialUnitary` with first column `gᴴ p`. -/
theorem coe_specialUnitarySphereLocalSection {g : specialUnitaryGroup (Fin (1 + n)) ℂ}
    {p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1}
    (hp : ⟪(specialUnitarySphereMap n g : EuclideanSpace ℂ (Fin (1 + n))), p⟫_ℂ ≠ 0) :
    (specialUnitarySphereLocalSection g p : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) =
      g * householderSpecialUnitary 0 (Fin.natAdd 1 0)
        (star (g : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) *ᵥ
          WithLp.ofLp (p : EuclideanSpace ℂ (Fin (1 + n)))) := by
  rw [coe_specialUnitarySphereLocalSection_of_mem hp, ofLp_sphereRotate]

/-- Over `⟪g e₀, p⟫ ≠ 0`, the local section through `g` is a section of `A ↦ A e₀`. -/
theorem specialUnitarySphereMap_specialUnitarySphereLocalSection
    {g : specialUnitaryGroup (Fin (1 + n)) ℂ} {p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1}
    (hp : ⟪(specialUnitarySphereMap n g : EuclideanSpace ℂ (Fin (1 + n))), p⟫_ℂ ≠ 0) :
    specialUnitarySphereMap n (specialUnitarySphereLocalSection g p) = p := by
  -- The Householder factor sends `e₀` to `gᴴ p`.
  have hcol : householderSpecialUnitary 0 (Fin.natAdd 1 0) (WithLp.ofLp (sphereRotate g p)) *ᵥ
      Pi.single 0 1 = star (g : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) *ᵥ
        WithLp.ofLp (p : EuclideanSpace ℂ (Fin (1 + n))) := by
    rw [householderSpecialUnitary_mulVec_single (sphereRotate_apply_zero_ne_zero hp),
      ofLp_sphereRotate]
  -- So the section sends `e₀` to `g gᴴ p = p`.
  ext1
  rw [coe_specialUnitarySphereMap, coe_specialUnitarySphereLocalSection_of_mem hp,
    ← mulVec_single_one, ← mulVec_mulVec, hcol]
  simp [mulVec_mulVec, Unitary.mul_star_self_of_mem g.property.1]

private theorem contMDiffOn_specialUnitarySphereLocalSection_sphereSectionDomain
    (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    ContMDiffOn (𝓡 (2 * n + 1)) (specialUnitaryGroup.model (Fin (1 + n)) ℂ) ∞
      (specialUnitarySphereLocalSection g) (sphereSectionDomain g) := by
  rw [specialUnitaryGroup.contMDiffOn_iff]
  set s : Set (EuclideanSpace ℂ (Fin (1 + n))) := {y | sphereRotate g y 0 ≠ 0}
  -- The Householder factor is smooth entrywise, hence for the operator norm on matrices.
  have hE : ContDiffOn ℝ ∞ (fun y k l ↦
      householderSpecialUnitary 0 (Fin.natAdd 1 0) (WithLp.ofLp (sphereRotate g y)) k l) s :=
    contDiffOn_pi.2 fun k ↦ contDiffOn_pi.2 fun l ↦
      (contDiffOn_householderSpecialUnitary_apply 0 _ k l).comp
        (PiLp.contDiff_ofLp.comp (contDiff_sphereRotate g)).contDiffOn fun _ hy ↦ hy
  have hH : ContDiffOn ℝ ∞ (fun y ↦
      householderSpecialUnitary 0 (Fin.natAdd 1 0) (WithLp.ofLp (sphereRotate g y))) s :=
    ((ofLinearEquiv ℝ : (Fin (1 + n) → Fin (1 + n) → ℂ) ≃ₗ[ℝ] _).toLinearMap
      |>.toContinuousLinearMap).contDiff.comp_contDiffOn hE
  refine ((contDiffOn_const.mul hH).contMDiffOn.comp contMDiff_coe_sphere.contMDiffOn
    fun p hp ↦ ?_).congr fun p hp ↦ coe_specialUnitarySphereLocalSection_of_mem hp
  exact sphereRotate_apply_zero_ne_zero hp

/-- The local section through `g` is smooth on `⟪g e₀, p⟫ ≠ 0`. -/
theorem contMDiffOn_specialUnitarySphereLocalSection (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    ContMDiffOn (𝓡 (2 * n + 1)) (specialUnitaryGroup.model (Fin (1 + n)) ℂ) ∞
      (specialUnitarySphereLocalSection g)
      {p | ⟪(specialUnitarySphereMap n g : EuclideanSpace ℂ (Fin (1 + n))), p⟫_ℂ ≠ 0} :=
  contMDiffOn_specialUnitarySphereLocalSection_sphereSectionDomain g

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
    (isOpen_sphereSectionDomain g) (specialUnitarySphereLocalSection g)
    (contMDiffOn_specialUnitarySphereLocalSection_sphereSectionDomain g).continuousOn
    fun _ hp ↦ specialUnitarySphereMap_specialUnitarySphereLocalSection hp).transFiberHomeomorph
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

/-- The inverse of the chart through `g` sends `(p, B)` to `s(p) diag(1, B)`, for the local section
`s = TauCeti.specialUnitarySphereLocalSection g`. -/
theorem specialUnitarySphereTrivialization_symm_apply
    (g : specialUnitaryGroup (Fin (1 + n)) ℂ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1 × specialUnitaryGroup (Fin n) ℂ) :
    (specialUnitarySphereTrivialization g).toOpenPartialHomeomorph.symm x =
      specialUnitarySphereLocalSection g x.1 * specialUnitaryGroup.fromBlocksOne ℂ 1 n x.2 := by
  rw [specialUnitarySphereTrivialization, Bundle.Trivialization.transFiberHomeomorph_symm_apply,
    Homeomorph.symm_symm, Subgroup.localSectionTrivializationOfCosetFibers_symm_apply,
    coe_specialUnitaryStabilizerHomeomorph_apply]

/-- **The inverse charts are equivariant**: the inverse of the chart through `g` intertwines right
multiplication by `C` on the fibre `SU(n)` with right multiplication by `diag(1, C)` on
`SU(1 + n)`. -/
theorem specialUnitarySphereTrivialization_symm_apply_mul
    (g : specialUnitaryGroup (Fin (1 + n)) ℂ) (p : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1)
    (B C : specialUnitaryGroup (Fin n) ℂ) :
    (specialUnitarySphereTrivialization g).toOpenPartialHomeomorph.symm (p, B * C) =
      (specialUnitarySphereTrivialization g).toOpenPartialHomeomorph.symm (p, B) *
        specialUnitaryGroup.fromBlocksOne ℂ 1 n C := by
  rw [specialUnitarySphereTrivialization_symm_apply, specialUnitarySphereTrivialization_symm_apply,
    map_mul, mul_assoc]

/-- On its source, the chart through `g` sends `A` to `(A e₀, B)`, where `B` is the lower right
block of `s(A e₀)⁻¹ A`, for the local section `s = TauCeti.specialUnitarySphereLocalSection g`. -/
theorem coe_specialUnitarySphereTrivialization_apply_snd {g : specialUnitaryGroup (Fin (1 + n)) ℂ}
    {A : specialUnitaryGroup (Fin (1 + n)) ℂ}
    (hA : A ∈ (specialUnitarySphereTrivialization g).source) :
    (((specialUnitarySphereTrivialization g A).2 : specialUnitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) =
      (((specialUnitarySphereLocalSection g (specialUnitarySphereMap n A))⁻¹ * A :
        specialUnitaryGroup (Fin (1 + n)) ℂ) : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ).submatrix
        (Fin.natAdd 1) (Fin.natAdd 1) := by
  rw [Bundle.Trivialization.mem_source, specialUnitarySphereTrivialization_baseSet] at hA
  simp only [specialUnitarySphereTrivialization, Bundle.Trivialization.transFiberHomeomorph_apply,
    coe_specialUnitaryStabilizerHomeomorph_symm_apply]
  rw [Subgroup.localSectionTrivializationOfCosetFibers_fiberCoordinate
    (π := specialUnitarySphereMap (𝕜 := ℂ) n) (U := sphereSectionDomain g) (g := A) hA]

/-- The chart `A ↦ (A e₀, B)`, with `diag(1, B) = s(A e₀)⁻¹ A`, is smooth on its source. -/
theorem contMDiffOn_specialUnitarySphereTrivialization (g : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    ContMDiffOn (specialUnitaryGroup.model (Fin (1 + n)) ℂ)
      ((𝓡 (2 * n + 1)).prod (specialUnitaryGroup.model (Fin n) ℂ)) ∞
      (specialUnitarySphereTrivialization g) (specialUnitarySphereTrivialization g).source := by
  set e := specialUnitarySphereTrivialization g
  have hsrc : e.source = specialUnitarySphereMap n ⁻¹' sphereSectionDomain g := by
    rw [e.source_eq, specialUnitarySphereTrivialization_baseSet, sphereSectionDomain]
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
      (fun A ↦ (specialUnitarySphereLocalSection g (specialUnitarySphereMap n A))⁻¹ * A)
      e.source := by
    rw [hsrc]
    exact ((contMDiffOn_specialUnitarySphereLocalSection g).comp
      contMDiff_specialUnitarySphereMap.contMDiffOn fun _ hA ↦ hA).inv.mul contMDiffOn_id
  have h₂ : ContMDiffOn (specialUnitaryGroup.model (Fin (1 + n)) ℂ)
      (specialUnitaryGroup.model (Fin n) ℂ) ∞ (fun A ↦ (e A).2) e.source := by
    rw [specialUnitaryGroup.contMDiffOn_iff]
    refine (S.toContinuousLinearMap.contDiff.contMDiff.comp_contMDiffOn
      (specialUnitaryGroup.contMDiff_val.comp_contMDiffOn hs)).congr fun A hA ↦ ?_
    rw [coe_specialUnitarySphereTrivialization_apply_snd hA]
    -- The right side is `S` applied to the same matrix; `S` is the structure literal above, whose
    -- application `simp [S]` and `LinearMap.coe_mk` do not reduce, so close by its definition.
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
  -- The inverse chart is `(p, B) ↦ s(p) * diag(1, B)`.
  refine (((contMDiffOn_specialUnitarySphereLocalSection_sphereSectionDomain g).comp
    contMDiffOn_fst fun _ hp ↦ by simpa [sphereSectionDomain] using (mem_prod.1 hp).1).mul
    ((specialUnitaryGroup.contMDiff_fromBlocksOne 1 n).comp contMDiff_snd).contMDiffOn).congr
    fun x _ ↦ specialUnitarySphereTrivialization_symm_apply g x

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
