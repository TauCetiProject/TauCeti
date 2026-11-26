/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.TestFunction.BoxCurrent
import Mathlib.Algebra.Group.Subgroup.Finsupp
import Mathlib.Analysis.Calculus.FDeriv.Affine
import TauCeti.Analysis.Normed.Module.Alternating.TopDegree

/-!
# Coordinate boxes and the cubes of a cubical grid as currents in `ℝⁿ`

For an injection `I : Fin k ↪ Fin n` of coordinate indices, a point `x ∈ ℝⁿ` and side lengths
`r : Fin k → ℝ`, the **coordinate box** with corner `x` spanned by the directions `e_{I j}` is

`{x + ∑ⱼ sⱼ e_{I j} | 0 ≤ sⱼ ≤ rⱼ}`,

oriented by the frame `e_{I 0}, …, e_{I (k-1)}`. Its oriented current `[[x; I, r]]`
(`TauCeti.coordBoxCurrent`) is the `k`-current on test `k`-forms on an open set `Ω ⊆ ℝⁿ`

`[[x; I, r]] ω = ∫_{[0, r]} ω(x + ∑ⱼ sⱼ e_{I j})(e_{I 0}, …, e_{I (k-1)}) ds`,

the pushforward of the top-dimensional box current `[[0, r]]` of `ℝᵏ` (`TauCeti.boxCurrent`) along
the affine isometric embedding `TauCeti.coordPlaneMap I x : s ↦ x + ∑ⱼ sⱼ e_{I j}`.

Composing `coordPlaneMap I x` with the face maps of the box (`TauCeti.boxFaceMap`) gives coordinate
planes of one dimension less, so the boundary formula of `[[0, r]]` pushes forward to the
**cubical boundary formula**: for `r ≥ 0`,

`∂ [[x; I, r]] = ∑ⱼ (-1)ʲ ([[x + rⱼ e_{I j}; I ∘ δⱼ, r ∘ δⱼ]] - [[x; I ∘ δⱼ, r ∘ δⱼ]])`,

where `δⱼ = Fin.succAbove j` and `∂ T = T ∘ d`. The current is supported in the box, it has mass
at most the `k`-volume `∏ⱼ rⱼ` of the box, and it is a normal current; in dimension zero it is the
Dirac current at `x`.

For a side length `ε` the **cubes of the cubical grid** of side `ε` are the coordinate boxes with
corner on the lattice `εℤⁿ` and all sides equal to `ε` (`TauCeti.gridCubeCurrent`). Their faces
are again grid cubes, so the integer combinations of grid cubes (`TauCeti.cubicalGridChains`), the
integral chains of the cubical grid, are closed under the boundary. These are the polyhedral
chains onto which the deformation theorem of Federer and Fleming pushes integral currents; this
file supplies their boundary formula, supports and mass bounds.

## Main declarations

* `TauCeti.coordPlaneMap I x`: the affine isometric embedding `s ↦ x + ∑ⱼ sⱼ e_{I j}`.
* `TauCeti.coordPlaneMap_succAboveEmb`: the face maps of the box are coordinate plane maps.
* `TauCeti.coordPlaneMap_comp_boxFaceMap`: a coordinate plane composed with a face map of the
  box is a coordinate plane of one dimension less.
* `TauCeti.coordProj I`, `TauCeti.planeProj I x`: the coordinate projection and the affine
  projection onto a coordinate plane, left inverses of the linear part of `coordPlaneMap I x` and
  of `coordPlaneMap I x` itself.
* `TauCeti.coordForm I`: the coordinate form `dx^I`, with
  `TauCeti.compContinuousLinearMap_contLinear_coordPlaneMap_comp_coordProj` writing a form
  restricted to the plane as its coefficient times `dx^I`.
* `TauCeti.coordBoxCurrent I x r Ω`: the oriented current `[[x; I, r]]` of a coordinate box.
* `TauCeti.coordBoxCurrent_apply`: its value as an integral over `[0, r]`.
* `TauCeti.coordBoxCurrent_comp_extDerivCLM`: the cubical boundary formula.
* `TauCeti.dsupport_coordBoxCurrent_subset`, `TauCeti.isCompact_dsupport_coordBoxCurrent`,
  `TauCeti.mass_coordBoxCurrent_le`, `TauCeti.isNormal_coordBoxCurrent`: support, mass and
  normality.
* `TauCeti.gridCubeCurrent ε I z Ω`: the oriented grid cube with corner `εz`, `z ∈ ℤⁿ`.
* `TauCeti.gridCubeCurrent_comp_extDerivCLM`: the boundary of a grid cube is an alternating sum of
  grid cubes.
* `TauCeti.cubicalGridChains ε Ω k`: the integral cubical grid `k`-chains of side `ε`, with the
  explicit description `TauCeti.mem_cubicalGridChains_iff`.
* `TauCeti.comp_extDerivCLM_mem_cubicalGridChains`: grid chains are closed under the boundary.
* `TauCeti.isNormal_of_mem_cubicalGridChains`,
  `TauCeti.isCompact_dsupport_of_mem_cubicalGridChains`: grid chains are normal currents with
  compact support.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.8 (oriented intervals and cubes) and §4.2.6–4.2.9
  (the cubical subdivision of `ℝⁿ` and the deformation theorem).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §4 (the deformation theorem
  and the cubical decomposition of `ℝⁿ`).
-/

public section

open MeasureTheory Set TopologicalSpace TestFunction Distribution WithLp
open scoped Distributions ENNReal

namespace TauCeti

variable {k n : ℕ}

section CoordPlaneMap

/-- The affine map `ℝᵏ → ℝⁿ`, `s ↦ x + ∑ⱼ sⱼ e_{I j}`, parametrizing the coordinate `k`-plane
through `x` spanned by the directions `e_{I j}` (`TauCeti.coordPlaneMap_apply`). -/
noncomputable def coordPlaneMap (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin k) →ᴬ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearIsometry.piLpExtendByZero 2 ℝ ℝ I).toContinuousLinearMap.toContinuousAffineMap +
    ContinuousAffineMap.const ℝ _ x

/-- `coordPlaneMap I x s` adds `sⱼ` to the `I j`-th coordinate of `x`. -/
theorem coordPlaneMap_apply (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin k)) :
    coordPlaneMap I x s = x + toLp 2 (Function.extend I (ofLp s) 0) := by
  ext m
  simp [coordPlaneMap, add_comm]

/-- The linear part of `coordPlaneMap I x` extends vectors by zero along `I`. -/
theorem contLinear_coordPlaneMap (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    (coordPlaneMap I x).contLinear =
      (LinearIsometry.piLpExtendByZero 2 ℝ ℝ I).toContinuousLinearMap := by
  simp [coordPlaneMap]

/-- The linear part of `coordPlaneMap I x` sends the `j`-th axis to the `I j`-th axis. -/
@[simp]
theorem contLinear_coordPlaneMap_single (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin k) (a : ℝ) :
    (coordPlaneMap I x).contLinear (EuclideanSpace.single j a) = EuclideanSpace.single (I j) a := by
  rw [contLinear_coordPlaneMap]
  exact LinearIsometry.piLpExtendByZero_apply_single I j a

/-- The linear part of a coordinate plane map has operator norm at most one. -/
theorem norm_contLinear_coordPlaneMap_le_one (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖(coordPlaneMap I x).contLinear‖ ≤ 1 := by
  rw [contLinear_coordPlaneMap]
  exact LinearIsometry.norm_toContinuousLinearMap_le _

/-- A coordinate plane map preserves distances. -/
theorem isometry_coordPlaneMap (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    Isometry (coordPlaneMap I x) := by
  have h : ⇑(coordPlaneMap I x) = (· + x) ∘ LinearIsometry.piLpExtendByZero 2 ℝ ℝ I := by
    ext s m
    simp [coordPlaneMap]
  rw [h]
  exact (isometry_add_right x).comp (LinearIsometry.piLpExtendByZero 2 ℝ ℝ I).isometry

/-- Preimages of compact sets under `coordPlaneMap I x` are compact, so it is proper from all of
`ℝᵏ` and pulls test forms back to test forms. -/
theorem isCompact_inter_preimage_coordPlaneMap (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    IsCompact (((⊤ : Opens (EuclideanSpace ℝ (Fin k))) : Set (EuclideanSpace ℝ (Fin k))) ∩
      coordPlaneMap I x ⁻¹' K) := by
  simpa using (isometry_coordPlaneMap I x).isClosedEmbedding.isCompact_preimage hK

/-- In dimension zero the coordinate plane through `x` is the point `x`. -/
@[simp]
theorem coordPlaneMap_finZero (I : Fin 0 ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin 0)) : coordPlaneMap I x s = x := by
  rw [coordPlaneMap_apply, Subsingleton.elim (ofLp s) 0]
  ext m
  simp

/-- The face maps of the box are the coordinate plane maps through `t eᵢ` spanned by the
directions other than `eᵢ`. -/
theorem coordPlaneMap_succAboveEmb (i : Fin (k + 1)) (t : ℝ) :
    coordPlaneMap i.succAboveEmb (EuclideanSpace.single i t) = boxFaceMap i t := by
  ext s m
  refine i.succAboveCases ?_ (fun l ↦ ?_) m
  · simp [coordPlaneMap_apply]
  · simp [coordPlaneMap_apply, Fin.succAbove_ne, Fin.succAbove_right_injective.extend_apply]

/-- **Faces of coordinate planes**: inserting `t` as the `j`-th parameter of the coordinate plane
through `x` spanned by `e_{I 0}, …, e_{I k}` gives the coordinate plane through `x + t e_{I j}`
spanned by the remaining directions `e_{I (j.succAbove l)}`. -/
theorem coordPlaneMap_comp_boxFaceMap (I : Fin (k + 1) ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin (k + 1)) (t : ℝ) :
    (coordPlaneMap I x).comp (boxFaceMap j t) =
      coordPlaneMap (j.succAboveEmb.trans I) (x + EuclideanSpace.single (I j) t) := by
  ext s m
  simp only [ContinuousAffineMap.comp_apply, coordPlaneMap_apply, boxFaceMap_apply,
    PiLp.add_apply, PiLp.single_apply, add_assoc]
  congr 1
  by_cases hm : ∃ l, I l = m
  · obtain ⟨l, rfl⟩ := hm
    rw [I.injective.extend_apply]
    refine j.succAboveCases ?_ (fun l ↦ ?_) l
    · have hj : ¬∃ l, (j.succAboveEmb.trans I) l = I j := by
        rintro ⟨l, hl⟩
        exact j.succAbove_ne l (I.injective hl)
      rw [Function.extend_apply' _ _ _ hj]
      simp
    · have hne : I (j.succAbove l) ≠ I j := fun h ↦ j.succAbove_ne l (I.injective h)
      simp only [Fin.insertNth_apply_succAbove, hne, ite_false, zero_add]
      exact ((j.succAboveEmb.trans I).injective.extend_apply (ofLp s) 0 l).symm
  · have hm' : ¬∃ l, (j.succAboveEmb.trans I) l = m := fun ⟨l, hl⟩ ↦ hm ⟨_, hl⟩
    have hne : m ≠ I j := fun h ↦ hm ⟨j, h.symm⟩
    rw [Function.extend_apply' _ _ _ hm, Function.extend_apply' _ _ _ hm']
    simp [hne]

/-! ### Coordinate projections and coordinate forms -/

/-- The coordinate projection `v ↦ (v (I j))ⱼ`, a left inverse of the linear part of
`TauCeti.coordPlaneMap I x` (`TauCeti.coordProj_contLinear_coordPlaneMap`). -/
noncomputable def coordProj (I : Fin k ↪ Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun j ↦ EuclideanSpace.proj (I j)

@[simp]
theorem coordProj_apply (I : Fin k ↪ Fin n) (v : EuclideanSpace ℝ (Fin n)) (j : Fin k) :
    coordProj I v j = v (I j) := by
  simp [coordProj]

/-- The coordinate projection is a left inverse of the linear part of a coordinate plane map. -/
theorem coordProj_contLinear_coordPlaneMap (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (s : EuclideanSpace ℝ (Fin k)) :
    coordProj I ((coordPlaneMap I x).contLinear s) = s := by
  ext j
  simp [contLinear_coordPlaneMap, I.injective.extend_apply]

/-- The directions of a coordinate plane lie in the span of `e_{I 0}, …, e_{I (k-1)}`. -/
theorem contLinear_coordPlaneMap_mem_span (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin k)) :
    (coordPlaneMap I x).contLinear v ∈
      Submodule.span ℝ (range fun j ↦ EuclideanSpace.single (I j) (1 : ℝ)) := by
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨fun j ↦ v j, ?_⟩
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.sum_repr v]
  simp [map_sum, map_smul, contLinear_coordPlaneMap_single]

/-- The affine projection `y ↦ (y - x)_I` onto the coordinates of the plane, a left inverse of
`TauCeti.coordPlaneMap I x` (`TauCeti.planeProj_coordPlaneMap`). -/
noncomputable def planeProj (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →ᴬ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (coordProj I).toContinuousAffineMap - ContinuousAffineMap.const ℝ _ (coordProj I x)

theorem planeProj_apply (I : Fin k ↪ Fin n) (x y : EuclideanSpace ℝ (Fin n)) :
    planeProj I x y = coordProj I (y - x) := by
  simp [planeProj]

/-- The linear part of the projection onto a coordinate plane is the coordinate projection. -/
@[simp]
theorem contLinear_planeProj (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    (planeProj I x).contLinear = coordProj I := by
  ext v
  simp [planeProj]

@[simp]
theorem planeProj_coordPlaneMap (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin k)) :
    planeProj I x (coordPlaneMap I x s) = s := by
  ext j
  simp [planeProj_apply, coordPlaneMap_apply, I.injective.extend_apply]

/-- The coordinate `k`-form `dx^I`: the determinant of the coordinates indexed by `I`. -/
noncomputable def coordForm (I : Fin k ↪ Fin n) :
    EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ :=
  (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.continuousDet.compContinuousLinearMap (coordProj I)

/-- The coordinate form `dx^I` evaluates to the determinant of the coordinates indexed by `I`. -/
theorem coordForm_apply (I : Fin k ↪ Fin n) (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    coordForm I v = (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.det (coordProj I ∘ v) := by
  rw [coordForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Module.Basis.continuousDet_apply]

/-- The coordinate form `dx^I` is one on `e_{I 0}, …, e_{I (k-1)}`. -/
@[simp]
theorem coordForm_apply_single (I : Fin k ↪ Fin n) :
    coordForm I (fun j ↦ EuclideanSpace.single (I j) 1) = 1 := by
  have h : (coordProj I ∘ fun j ↦ EuclideanSpace.single (I j) (1 : ℝ)) =
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis := by
    funext j
    ext i
    simp [I.injective.eq_iff, eq_comm]
  rw [coordForm_apply, h, Module.Basis.det_self]

/-- Projecting onto a coordinate plane turns a `k`-form into the multiple of `dx^I` by its
coefficient on `e_{I 0}, …, e_{I (k-1)}`. -/
theorem compContinuousLinearMap_contLinear_coordPlaneMap_comp_coordProj (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (α : EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) :
    α.compContinuousLinearMap ((coordPlaneMap I x).contLinear ∘L coordProj I) =
      α (fun j ↦ EuclideanSpace.single (I j) 1) • coordForm I := by
  ext v
  set b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have h := (α.compContinuousLinearMap (coordPlaneMap I x).contLinear).apply_eq_det_mul b
    (coordProj I ∘ v)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp,
    ContinuousAlternatingMap.smul_apply, coordForm, smul_eq_mul]
  have hb : (coordPlaneMap I x).contLinear ∘ b = fun j ↦ EuclideanSpace.single (I j) 1 := by
    funext j
    simp only [Function.comp_apply, b, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply, contLinear_coordPlaneMap_single]
  rw [Function.comp_assoc, h, hb, mul_comm, Module.Basis.continuousDet_apply]

end CoordPlaneMap

section CoordBoxCurrent

/-- The **oriented current of a coordinate box** `[[x; I, r]]`: the pushforward of the box current
`[[0, r]]` of `ℝᵏ` along `s ↦ x + ∑ⱼ sⱼ e_{I j}`, a `k`-current on test `k`-forms on an open set
`Ω ⊆ ℝⁿ`. It integrates `ω(x + ∑ⱼ sⱼ e_{I j})(e_{I 0}, …, e_{I (k-1)})` over `s ∈ [0, r]`
(`TauCeti.coordBoxCurrent_apply`). -/
noncomputable def coordBoxCurrent (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  boxCurrent 0 r ⊤ ∘L pullbackCLM (coordPlaneMap I x) (coordPlaneMap I x).contDiff.contDiffOn
    (fun _ hK _ ↦ isCompact_inter_preimage_coordPlaneMap I x hK)

/-- `[[x; I, r]]` is the pushforward of the box current `[[0, r]]` of `ℝᵏ` along the coordinate
plane map `TauCeti.coordPlaneMap I x`. -/
theorem coordBoxCurrent_def (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    coordBoxCurrent I x r Ω =
      boxCurrent 0 r ⊤ ∘L pullbackCLM (coordPlaneMap I x) (coordPlaneMap I x).contDiff.contDiffOn
        (fun _ hK _ ↦ isCompact_inter_preimage_coordPlaneMap I x hK) :=
  (rfl)

/-- `[[x; I, r]]` integrates the coefficient of a test form on `e_{I 0}, …, e_{I (k-1)}` over the
box. -/
theorem coordBoxCurrent_apply (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n)))
    (ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)) :
    coordBoxCurrent I x r Ω ω =
      ∫ s in Icc 0 r, ω (coordPlaneMap I x (toLp 2 s)) fun j ↦ EuclideanSpace.single (I j) 1 := by
  rw [coordBoxCurrent, ContinuousLinearMap.comp_apply, boxCurrent_apply]
  congr 1
  funext s
  rw [pullbackCLM_apply_of_mem _ (Opens.mem_top _),
    ContinuousAffineMap.fderiv, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  simp only [Function.comp_def, contLinear_coordPlaneMap_single]

/-- A coordinate box with a nonpositive side length defines the zero current. -/
theorem coordBoxCurrent_eq_zero_of_nonpos (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    {r : Fin k → ℝ} (j : Fin k) (hj : r j ≤ 0) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    coordBoxCurrent I x r Ω = 0 := by
  rw [coordBoxCurrent, boxCurrent_eq_zero_of_le j hj, ContinuousLinearMap.zero_comp]

/-- **Dimension zero**: `[[x; I, r]]` is the Dirac current at `x`. -/
@[simp]
theorem coordBoxCurrent_apply_finZero (I : Fin 0 ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin 0 → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n)))
    (ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin 0]→L[ℝ] ℝ)) :
    coordBoxCurrent I x r Ω ω = ω x ![] := by
  rw [coordBoxCurrent, ContinuousLinearMap.comp_apply, boxCurrent_apply_finZero,
    pullbackCLM_apply_of_mem _ (Opens.mem_top _),
    ContinuousAlternatingMap.compContinuousLinearMap_apply, coordPlaneMap_finZero]
  exact congrArg _ (Subsingleton.elim _ _)

/-- `[[x; I, r]]` is compatible with restriction: on a test form extended by zero from a smaller
open set `Ω'`, the current `[[x; I, r]]` on `Ω` is the current `[[x; I, r]]` on `Ω'`. -/
@[simp]
theorem coordBoxCurrent_monoCLM (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) {Ω Ω' : Opens (EuclideanSpace ℝ (Fin n))} (h : Ω' ≤ Ω)
    (ω : 𝓓(Ω', EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)) :
    coordBoxCurrent I x r Ω (monoCLM ℝ ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)) =
      coordBoxCurrent I x r Ω' ω := by
  simp [coordBoxCurrent_apply, monoCLM_apply, h]

/-- Pushing the face `[[0 ∘ δⱼ, r']]` of a box at height `t` forward along a coordinate plane map
gives the coordinate box current through `x + t e_{I j}`. -/
private theorem boxCurrent_comp_pullbackCLM_boxFaceMap_comp_pullbackCLM_coordPlaneMap
    (I : Fin (k + 1) ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) (j : Fin (k + 1)) (t : ℝ)
    {x' : EuclideanSpace ℝ (Fin n)} (hx' : x + EuclideanSpace.single (I j) t = x')
    (r' : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    (boxCurrent ((0 : Fin (k + 1) → ℝ) ∘ j.succAbove) r' ⊤ ∘L
        pullbackCLM (boxFaceMap j t) (boxFaceMap j t).contDiff.contDiffOn
          (fun _ hK _ ↦ isCompact_inter_preimage_boxFaceMap j t hK)) ∘L
      pullbackCLM (coordPlaneMap I x) (coordPlaneMap I x).contDiff.contDiffOn
        (fun _ hK _ ↦ isCompact_inter_preimage_coordPlaneMap I x hK) =
      coordBoxCurrent (j.succAboveEmb.trans I) x' r' Ω := by
  subst hx'
  have hmap : ⇑(coordPlaneMap I x) ∘ ⇑(boxFaceMap j t) =
      ⇑(coordPlaneMap (j.succAboveEmb.trans I) (x + EuclideanSpace.single (I j) t)) := by
    rw [← coordPlaneMap_comp_boxFaceMap, ContinuousAffineMap.coe_comp]
  have hcomp := pullbackCLM_comp (k := k) (F := ℝ) (Ω := ⊤) (Ω' := ⊤) (Ω'' := Ω)
    (Φ := boxFaceMap j t) (hΦ := (boxFaceMap j t).contDiff.contDiffOn)
    (hΦp := fun _ hK _ ↦ isCompact_inter_preimage_boxFaceMap j t hK)
    (coordPlaneMap I x).contDiff.contDiffOn
    (fun _ hK _ ↦ isCompact_inter_preimage_coordPlaneMap I x hK)
    (by rw [hmap]; exact (coordPlaneMap _ _).contDiff.contDiffOn)
    (fun _ hK _ ↦ by rw [hmap]; exact isCompact_inter_preimage_coordPlaneMap _ _ hK)
    (mapsTo_univ _ _)
  rw [ContinuousLinearMap.comp_assoc, ← hcomp, Pi.zero_comp, coordBoxCurrent]
  -- The two pullbacks are along the maps identified by `hmap`, so they agree.
  congr 2

/-- **The boundary of a coordinate box**: for `r ≥ 0`,
`∂ [[x; I, r]] = ∑ⱼ (-1)ʲ ([[x + rⱼ e_{I j}; I ∘ δⱼ, r ∘ δⱼ]] - [[x; I ∘ δⱼ, r ∘ δⱼ]])`, where
`∂ T = T ∘ d` and `δⱼ = Fin.succAbove j`: the faces `sⱼ = rⱼ` and `sⱼ = 0` of the box, with the
orientation signs of the cubical boundary operator. -/
theorem coordBoxCurrent_comp_extDerivCLM (I : Fin (k + 1) ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) {r : Fin (k + 1) → ℝ} (hr : 0 ≤ r)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    coordBoxCurrent I x r Ω ∘L extDerivCLM =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) •
        (coordBoxCurrent (j.succAboveEmb.trans I) (x + EuclideanSpace.single (I j) (r j))
            (r ∘ j.succAbove) Ω -
          coordBoxCurrent (j.succAboveEmb.trans I) x (r ∘ j.succAbove) Ω) := by
  rw [coordBoxCurrent, ContinuousLinearMap.comp_pullbackCLM_comp_extDerivCLM,
    boxCurrent_comp_extDerivCLM hr]
  ext ω
  simp only [ContinuousLinearMap.comp_apply, sum_apply, smul_apply, sub_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← boxCurrent_comp_pullbackCLM_boxFaceMap_comp_pullbackCLM_coordPlaneMap I x j (r j) rfl,
    ← boxCurrent_comp_pullbackCLM_boxFaceMap_comp_pullbackCLM_coordPlaneMap I x j
      ((0 : Fin (k + 1) → ℝ) j)      (by simp)]
  simp only [ContinuousLinearMap.comp_apply]

/-- The coordinate box `{x + ∑ⱼ sⱼ e_{I j} | 0 ≤ sⱼ ≤ rⱼ}` is compact. -/
theorem isCompact_coordPlaneMap_image_Icc (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) : IsCompact (coordPlaneMap I x '' (ofLp ⁻¹' Icc 0 r)) :=
  ((PiLp.homeomorph 2 _).isCompact_preimage.2 isCompact_Icc).image (coordPlaneMap I x).continuous

/-- The support of `[[x; I, r]]` lies in the box `{x + ∑ⱼ sⱼ e_{I j} | 0 ≤ sⱼ ≤ rⱼ}`. -/
theorem dsupport_coordBoxCurrent_subset (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    dsupport (coordBoxCurrent I x r Ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) → ℝ) ⊆
      coordPlaneMap I x '' (ofLp ⁻¹' Icc 0 r) := by
  rw [coordBoxCurrent, ContinuousLinearMap.coe_comp]
  refine (dsupport_comp_pullbackCLM_subset _).trans ?_
  rw [(isCompact_coordPlaneMap_image_Icc I x r).isClosed.closure_subset_iff]
  exact image_mono (inter_subset_right.trans (dsupport_boxCurrent_subset 0 r ⊤))

/-- The support of `[[x; I, r]]` is compact. -/
theorem isCompact_dsupport_coordBoxCurrent (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    IsCompact
      (dsupport (coordBoxCurrent I x r Ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) → ℝ)) :=
  (isCompact_coordPlaneMap_image_Icc I x r).of_isClosed_subset isClosed_dsupport
    (dsupport_coordBoxCurrent_subset I x r Ω)

/-- **The mass of a coordinate box**: `M([[x; I, r]]) ≤ ∏ⱼ rⱼ`, the `k`-volume of the box. -/
theorem mass_coordBoxCurrent_le (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    mass (coordBoxCurrent I x r Ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) → ℝ) ≤
      ∏ j, ENNReal.ofReal (r j) := by
  rw [coordBoxCurrent, ContinuousLinearMap.coe_comp]
  refine (mass_comp_pullbackCLM_le _ (L := 1) fun s _ ↦ ?_).trans ?_
  · rw [ContinuousAffineMap.fderiv]
    exact norm_contLinear_coordPlaneMap_le_one I x
  · simpa [Real.volume_Icc_pi] using mass_boxCurrent_le 0 r ⊤

/-- **The coordinate box is a normal current**: `[[x; I, r]]` and its boundary have finite
mass. -/
theorem isNormal_coordBoxCurrent (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    IsNormal (coordBoxCurrent I x r Ω) :=
  (isNormal_boxCurrent 0 r ⊤).comp_pullbackCLM (L := 1) fun s _ ↦ by
    rw [ContinuousAffineMap.fderiv]
    exact norm_contLinear_coordPlaneMap_le_one I x

end CoordBoxCurrent

section Grid

/-- The **oriented cube of the cubical grid of side `ε`** with corner `εz`, `z ∈ ℤⁿ`, spanned by
the directions `e_{I 0}, …, e_{I (k-1)}`: the coordinate box current `[[εz; I, (ε, …, ε)]]` on test
`k`-forms on `Ω ⊆ ℝⁿ`. -/
noncomputable def gridCubeCurrent (ε : ℝ) (I : Fin k ↪ Fin n) (z : Fin n → ℤ)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  coordBoxCurrent I (toLp 2 fun m ↦ ε * z m) (fun _ ↦ ε) Ω

theorem gridCubeCurrent_def (ε : ℝ) (I : Fin k ↪ Fin n) (z : Fin n → ℤ)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    gridCubeCurrent ε I z Ω = coordBoxCurrent I (toLp 2 fun m ↦ ε * z m) (fun _ ↦ ε) Ω :=
  (rfl)

/-- Moving the corner `εz` of a grid cube by `ε` along the `i`-th axis moves `z` by one. -/
private theorem toLp_mul_add_single (ε : ℝ) (z : Fin n → ℤ) (i : Fin n) :
    (toLp 2 fun m ↦ ε * z m) + EuclideanSpace.single i ε =
      toLp 2 fun m ↦ ε * ((z + Pi.single i 1 : Fin n → ℤ) m : ℝ) := by
  ext m
  by_cases hm : m = i
  · subst hm
    simp [mul_add]
  · simp [hm]

/-- **The boundary of a grid cube**: for `ε ≥ 0`, `∂ Q = ∑ⱼ (-1)ʲ (Q⁺ⱼ - Q⁻ⱼ)`, where `Q⁻ⱼ` and
`Q⁺ⱼ` are the grid cubes spanned by the directions `e_{I (j.succAbove l)}` with corners `εz` and
`ε(z + e_{I j})`. -/
theorem gridCubeCurrent_comp_extDerivCLM {ε : ℝ} (hε : 0 ≤ ε) (I : Fin (k + 1) ↪ Fin n)
    (z : Fin n → ℤ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    gridCubeCurrent ε I z Ω ∘L extDerivCLM =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) •
        (gridCubeCurrent ε (j.succAboveEmb.trans I) (z + Pi.single (I j) 1) Ω -
          gridCubeCurrent ε (j.succAboveEmb.trans I) z Ω) := by
  simp only [gridCubeCurrent_def, coordBoxCurrent_comp_extDerivCLM I _ (fun _ ↦ hε) Ω,
    toLp_mul_add_single, Function.comp_def]

/-- The support of a grid cube lies in the cube `{εz + ∑ⱼ sⱼ e_{I j} | 0 ≤ sⱼ ≤ ε}`. -/
theorem dsupport_gridCubeCurrent_subset (ε : ℝ) (I : Fin k ↪ Fin n) (z : Fin n → ℤ)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    dsupport (gridCubeCurrent ε I z Ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) → ℝ) ⊆
      coordPlaneMap I (toLp 2 fun m ↦ ε * z m) '' (ofLp ⁻¹' Icc 0 fun _ ↦ ε) :=
  dsupport_coordBoxCurrent_subset _ _ _ Ω

/-- **The mass of a grid cube**: `M(Q) ≤ εᵏ`. -/
theorem mass_gridCubeCurrent_le (ε : ℝ) (I : Fin k ↪ Fin n) (z : Fin n → ℤ)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    mass (gridCubeCurrent ε I z Ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) → ℝ) ≤
      ENNReal.ofReal ε ^ k := by
  simpa [gridCubeCurrent_def] using mass_coordBoxCurrent_le I (toLp 2 fun m ↦ ε * z m) (fun _ ↦ ε) Ω

/-- A grid cube is a normal current. -/
theorem isNormal_gridCubeCurrent (ε : ℝ) (I : Fin k ↪ Fin n) (z : Fin n → ℤ)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : IsNormal (gridCubeCurrent ε I z Ω) :=
  isNormal_coordBoxCurrent _ _ _ Ω

/-- The **integral cubical grid `k`-chains of side `ε`**: the additive subgroup of `k`-currents on
`Ω ⊆ ℝⁿ` generated by the oriented grid cubes `TauCeti.gridCubeCurrent ε I z Ω`, that is, their
finite integer combinations (`TauCeti.mem_cubicalGridChains_iff`). -/
noncomputable def cubicalGridChains (ε : ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    AddSubgroup (𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
  AddSubgroup.closure (range fun c : (Fin k ↪ Fin n) × (Fin n → ℤ) ↦ gridCubeCurrent ε c.1 c.2 Ω)

/-- Grid cubes are grid chains. -/
theorem gridCubeCurrent_mem_cubicalGridChains (ε : ℝ) (I : Fin k ↪ Fin n) (z : Fin n → ℤ)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    gridCubeCurrent ε I z Ω ∈ cubicalGridChains ε Ω k :=
  AddSubgroup.subset_closure ⟨(I, z), rfl⟩

/-- A current is a grid chain exactly when it is a finite integer combination
`∑_c a_c • Q_c` of grid cubes. -/
theorem mem_cubicalGridChains_iff {ε : ℝ} {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {T : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ} :
    T ∈ cubicalGridChains ε Ω k ↔
      ∃ a : (Fin k ↪ Fin n) × (Fin n → ℤ) →₀ ℤ,
        T = a.sum fun c m ↦ m • gridCubeCurrent ε c.1 c.2 Ω :=
  AddSubgroup.mem_closure_range_iff

/-- **Grid chains are closed under the boundary**: the boundary `∂ T = T ∘ d` of an integral
cubical grid `(k + 1)`-chain of side `ε` is an integral cubical grid `k`-chain. -/
theorem comp_extDerivCLM_mem_cubicalGridChains {ε : ℝ}
    {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {T : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : T ∈ cubicalGridChains ε Ω (k + 1)) :
    T ∘L extDerivCLM ∈ cubicalGridChains ε Ω k := by
  refine (AddSubgroup.closure_le ((cubicalGridChains ε Ω k).comap
    (AddMonoidHom.mk' (· ∘L extDerivCLM) fun S S' ↦ ContinuousLinearMap.add_comp S S' _))).2 ?_ hT
  rintro _ ⟨⟨I, z⟩, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.mk'_apply]
  dsimp only
  rcases lt_or_ge ε 0 with hε | hε
  · -- Cubes of positive dimension with a negative side are zero.
    rw [gridCubeCurrent_def, coordBoxCurrent_eq_zero_of_nonpos I _ 0 hε.le,
      ContinuousLinearMap.zero_comp]
    exact zero_mem _
  rw [gridCubeCurrent_comp_extDerivCLM hε]
  refine AddSubgroup.sum_mem _ fun j _ ↦ ?_
  have hsub := AddSubgroup.sub_mem _
    (gridCubeCurrent_mem_cubicalGridChains ε (j.succAboveEmb.trans I) (z + Pi.single (I j) 1) Ω)
    (gridCubeCurrent_mem_cubicalGridChains ε (j.succAboveEmb.trans I) z Ω)
  rcases neg_one_pow_eq_or ℝ (j : ℕ) with h | h <;> rw [h]
  · rwa [one_smul]
  · have h' := AddSubgroup.zsmul_mem _ hsub (-1)
    rwa [← Int.cast_smul_eq_zsmul ℝ, Int.cast_neg, Int.cast_one] at h'

/-- **Grid chains are normal currents.** -/
theorem isNormal_of_mem_cubicalGridChains {ε : ℝ} {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {T : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : T ∈ cubicalGridChains ε Ω k) : IsNormal T := by
  have h : cubicalGridChains ε Ω k ≤
      (normalCurrentSubmodule ℝ ℝ Ω k).toAddSubgroup :=
    AddSubgroup.closure_le _ |>.2 <| by
      rintro _ ⟨⟨I, z⟩, rfl⟩
      exact mem_normalCurrentSubmodule.2 (isNormal_gridCubeCurrent ε I z Ω)
  exact mem_normalCurrentSubmodule.1 ((Submodule.mem_toAddSubgroup _).1 (h hT))

/-- **Grid chains have compact support**: the support of a grid chain lies in the union of the
finitely many cubes it is made of. -/
theorem isCompact_dsupport_of_mem_cubicalGridChains {ε : ℝ}
    {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {T : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : T ∈ cubicalGridChains ε Ω k) : IsCompact (dsupport (T : _ → ℝ)) := by
  induction hT using AddSubgroup.closure_induction with
  | mem _ h =>
    obtain ⟨⟨I, z⟩, rfl⟩ := h
    exact isCompact_dsupport_coordBoxCurrent _ _ _ Ω
  | zero => simp [dsupport_zero]
  | add S T _ _ hS hT =>
    exact (hS.union hT).of_isClosed_subset isClosed_dsupport
      (dsupport_add_subset (S : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) → ℝ) T)
  | neg T _ hT =>
    have h : dsupport (⇑(-T)) = dsupport T := dsupport_neg _
    rwa [h]

/-- **The mass of a grid chain**: `M(∑_c a_c • Q_c) ≤ (∑_c |a_c|) εᵏ`. -/
theorem mass_finsuppSum_gridCubeCurrent_le (ε : ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n)))
    (a : (Fin k ↪ Fin n) × (Fin n → ℤ) →₀ ℤ) :
    mass (a.sum (fun c m ↦ m • gridCubeCurrent ε c.1 c.2 Ω) :
        𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) → ℝ) ≤
      (∑ c ∈ a.support, ‖a c‖ₑ) * ENNReal.ofReal ε ^ k := by
  simp only [Finsupp.sum, Finset.sum_mul]
  refine (mass_sum_le _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
  rw [← Int.cast_smul_eq_zsmul ℝ, mass_smul]
  gcongr
  · simp [← ofReal_norm, Int.norm_eq_abs]
  · exact mass_gridCubeCurrent_le ε c.1 c.2 Ω

end Grid

end TauCeti
