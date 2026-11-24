/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Topology.Algebra.Module.Equiv.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix
import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# Bounded-convergence continuity and inversion on finite coordinate spaces

On a finite coordinate space `ι → 𝕜` over a nontrivially normed field `𝕜`, neither
bounded-convergence continuity nor continuous inversion of linear equivalences requires
`CompleteSpace 𝕜`:
* `TauCeti.piRingContinuousLinearEquiv` packages the bounded-convergence continuous linear
  equivalence `((ι → 𝕜) →L[𝕜] G) ≃L[𝕜] (ι → G)` for a finite index type `ι` and a topological
  `𝕜`-module `G`, yielding `TauCeti.continuousWithinAt_pi_clm_iff_apply_single_one`,
  `TauCeti.continuousAt_pi_clm_iff_apply_single_one`,
  `TauCeti.continuousOn_pi_clm_iff_apply_single_one`, and
  `TauCeti.continuous_pi_clm_iff_apply_single_one`;
* `ContinuousLinearMap.isInvertible_of_bijective_pi` equips any bijective continuous linear map
  `M →L[R] (κ → R)` from a topological `R`-module `M` into a finite coordinate space `κ → R`
  with a continuous inverse;
* `ContinuousAt.pi_clm_inverse`, `ContinuousWithinAt.pi_clm_inverse`, and
  `ContinuousOn.pi_clm_inverse` prove that for a continuous family
  `T : Y → (ι → 𝕜) →L[𝕜] (κ → 𝕜)` of continuous linear maps between finite coordinate spaces,
  `y ↦ (T y).inverse` is continuous wherever `T` is bijective.
-/

public section

open scoped Topology

section EvalBasis

namespace TauCeti

/-- For a finite index type `ι` over a nontrivially normed field `𝕜` and a topological `𝕜`-module
`G`, evaluating at the standard basis vectors `Pi.single i 1` gives a continuous linear equivalence
between `(ι → 𝕜) →L[𝕜] G` (with the bounded-convergence topology) and `ι → G` without requiring
`CompleteSpace 𝕜`. -/
noncomputable def piRingContinuousLinearEquiv (𝕜 ι G : Type*) [NontriviallyNormedField 𝕜]
    [Finite ι] [DecidableEq ι] [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [Module 𝕜 G] [ContinuousSMul 𝕜 G] : ((ι → 𝕜) →L[𝕜] G) ≃L[𝕜] (ι → G) :=
  letI := Fintype.ofFinite ι
  let e := LinearEquiv.piRing 𝕜 G ι 𝕜
  let rankOne (i : ι) : G →L[𝕜] ((ι → 𝕜) →L[𝕜] G) :=
    ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i).precomp G).comp
      ContinuousLinearMap.toSpanSingletonCLE.toContinuousLinearMap
  { toFun L := e L.toLinearMap
    map_add' L₁ L₂ := e.map_add L₁.toLinearMap L₂.toLinearMap
    map_smul' c L := e.map_smul c L.toLinearMap
    invFun g := ⟨e.symm g, (e.symm g).continuous_on_pi⟩
    left_inv L := ContinuousLinearMap.ext fun v ↦ DFunLike.congr_fun (e.left_inv L.toLinearMap) v
    right_inv := e.right_inv
    continuous_toFun := continuous_pi fun i ↦ continuous_eval_const (Pi.single i 1)
    continuous_invFun :=
      (continuous_finsetSum Finset.univ fun i _ ↦
        (rankOne i).continuous.comp (continuous_apply i)).congr
        fun g ↦ ContinuousLinearMap.ext fun v ↦ by
          simp [rankOne, e] }

section

variable {𝕜 ι Y G : Type*} [NontriviallyNormedField 𝕜] [Finite ι] [TopologicalSpace Y]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [Module 𝕜 G] [ContinuousSMul 𝕜 G]

/-- `TauCeti.piRingContinuousLinearEquiv` evaluates a continuous linear map on `Pi.single i 1`. -/
@[simp] theorem piRingContinuousLinearEquiv_apply [DecidableEq ι]
    (L : (ι → 𝕜) →L[𝕜] G) (i : ι) :
    piRingContinuousLinearEquiv 𝕜 ι G L i = L (Pi.single i 1) :=
  letI := Fintype.ofFinite ι
  LinearEquiv.piRing_apply (S := 𝕜) L.toLinearMap i

/-- The inverse of `TauCeti.piRingContinuousLinearEquiv` expands a vector in the standard basis. -/
@[simp] theorem piRingContinuousLinearEquiv_symm_apply {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : κ → G) (v : κ → 𝕜) :
    (piRingContinuousLinearEquiv 𝕜 κ G).symm g v = ∑ i : κ, v i • g i := by
  -- `piRingContinuousLinearEquiv` only assumes `[Finite κ]` and uses `Fintype.ofFinite κ`
  -- internally, whereas the RHS sum uses the caller's `[Fintype κ]` instance.
  let _ := Fintype.ofFinite κ
  refine (LinearEquiv.piRing_symm_apply (S := 𝕜) g v).trans ?_
  congr!

/-- Over a nontrivially normed field `𝕜` and a finite index type `ι`, a family
`T : Y → (ι → 𝕜) →L[𝕜] G` into a topological `𝕜`-module `G` is continuous within `s` at `y₀` if
and only if each basis evaluation `y ↦ T y (Pi.single i 1)` is continuous within `s` at `y₀`. -/
theorem continuousWithinAt_pi_clm_iff_apply_single_one [DecidableEq ι]
    {T : Y → (ι → 𝕜) →L[𝕜] G} {s : Set Y} {y₀ : Y} :
    ContinuousWithinAt T s y₀ ↔
      ∀ i : ι, ContinuousWithinAt (fun y ↦ T y (Pi.single i 1)) s y₀ :=
  (piRingContinuousLinearEquiv 𝕜 ι G).toHomeomorph.isInducing.continuousWithinAt_iff.trans
    continuousWithinAt_pi

/-- Over a nontrivially normed field `𝕜` and a finite index type `ι`, a family
`T : Y → (ι → 𝕜) →L[𝕜] G` into a topological `𝕜`-module `G` is continuous at `y₀` if and only if
each basis evaluation `y ↦ T y (Pi.single i 1)` is continuous at `y₀`. -/
theorem continuousAt_pi_clm_iff_apply_single_one [DecidableEq ι]
    {T : Y → (ι → 𝕜) →L[𝕜] G} {y₀ : Y} :
    ContinuousAt T y₀ ↔ ∀ i : ι, ContinuousAt (fun y ↦ T y (Pi.single i 1)) y₀ :=
  (piRingContinuousLinearEquiv 𝕜 ι G).toHomeomorph.isInducing.continuousAt_iff.trans continuousAt_pi

/-- Over a nontrivially normed field `𝕜` and a finite index type `ι`, a family
`T : Y → (ι → 𝕜) →L[𝕜] G` into a topological `𝕜`-module `G` is continuous on `s` if and only if
each basis evaluation `y ↦ T y (Pi.single i 1)` is continuous on `s`. -/
theorem continuousOn_pi_clm_iff_apply_single_one [DecidableEq ι]
    {T : Y → (ι → 𝕜) →L[𝕜] G} {s : Set Y} :
    ContinuousOn T s ↔ ∀ i : ι, ContinuousOn (fun y ↦ T y (Pi.single i 1)) s :=
  (piRingContinuousLinearEquiv 𝕜 ι G).toHomeomorph.isInducing.continuousOn_iff.trans continuousOn_pi

/-- Over a nontrivially normed field `𝕜` and a finite index type `ι`, a family
`T : Y → (ι → 𝕜) →L[𝕜] G` into a topological `𝕜`-module `G` is continuous if and only if each
basis evaluation `y ↦ T y (Pi.single i 1)` is continuous. -/
theorem continuous_pi_clm_iff_apply_single_one [DecidableEq ι] {T : Y → (ι → 𝕜) →L[𝕜] G} :
    Continuous T ↔ ∀ i : ι, Continuous fun y ↦ T y (Pi.single i 1) :=
  (piRingContinuousLinearEquiv 𝕜 ι G).toHomeomorph.isInducing.continuous_iff.trans continuous_pi_iff

end

end TauCeti

end EvalBasis

section Inverse

/-- Any bijective continuous linear map from a topological `R`-module `M` (with continuous addition
and scalar multiplication) into a finite coordinate space `κ → R` has a continuous inverse. -/
theorem ContinuousLinearMap.isInvertible_of_bijective_pi {R M κ : Type*}
    [Semiring R] [TopologicalSpace R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M] [Finite κ]
    {f : M →L[R] (κ → R)} (hf : Function.Bijective f) : f.IsInvertible := by
  let e := LinearEquiv.ofBijective f.toLinearMap hf
  exact .of_inverse (g := ⟨e.symm.toLinearMap, LinearMap.continuous_on_pi _⟩)
    (ext e.apply_symm_apply) (ext e.symm_apply_apply)

private theorem eventually_isInvertible_pi_clm_within {𝕜 ι κ Y : Type*}
    [NontriviallyNormedField 𝕜] [Finite ι] [Finite κ] [TopologicalSpace Y]
    {T : Y → (ι → 𝕜) →L[𝕜] (κ → 𝕜)} {s : Set Y} {y₀ : Y}
    (hT : ContinuousWithinAt T s y₀) (hbij : Function.Bijective (T y₀)) :
    ∀ᶠ y in 𝓝[s] y₀, (T y).IsInvertible := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  have hcard : Fintype.card ι = Fintype.card κ := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      (LinearEquiv.ofBijective (T y₀).toLinearMap hbij).finrank_eq
  let e : (κ → 𝕜) ≃L[𝕜] (ι → 𝕜) :=
    ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : ι ↦ 𝕜) (Fintype.equivOfCardEq hcard).symm
  let S : Y → (κ → 𝕜) →L[𝕜] (κ → 𝕜) := fun y ↦ (T y).comp (e : (κ → 𝕜) →L[𝕜] (ι → 𝕜))
  have hS : ContinuousWithinAt S s y₀ :=
    ((e : (κ → 𝕜) →L[𝕜] (ι → 𝕜)).precomp (κ → 𝕜)).continuous.continuousAt.comp_continuousWithinAt hT
  let M : Y → Matrix κ κ 𝕜 := fun y ↦ LinearMap.toMatrix' (S y).toLinearMap
  have hM : ContinuousWithinAt M s y₀ := continuousWithinAt_pi.2 fun i ↦
    continuousWithinAt_pi.2 fun j ↦ (continuous_apply i).continuousAt.comp_continuousWithinAt
      ((TauCeti.continuousWithinAt_pi_clm_iff_apply_single_one.1 hS) j)
  have hMN₀ : M y₀ * LinearMap.toMatrix' (S y₀).inverse.toLinearMap = 1 := by
    have hcomp : (S y₀).toLinearMap.comp (S y₀).inverse.toLinearMap = LinearMap.id :=
      congrArg ContinuousLinearMap.toLinearMap
        ((S y₀).isInvertible_of_bijective_pi (hbij.comp e.bijective)).self_comp_inverse
    rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id]
  have hdet₀ : (M y₀).det ≠ 0 :=
    left_ne_zero_of_mul_eq_one (by rw [← Matrix.det_mul, hMN₀, Matrix.det_one])
  have hev_det : ∀ᶠ y in 𝓝[s] y₀, (M y).det ≠ 0 :=
    (continuous_id.matrix_det.continuousAt.comp_continuousWithinAt hM).eventually_ne hdet₀
  have hSM (y : Y) (v : κ → 𝕜) : S y v = (M y).mulVec v :=
    DFunLike.congr_fun (Matrix.toLin'_toMatrix' (S y).toLinearMap).symm v
  refine hev_det.mono fun y hy ↦ (T y).isInvertible_of_bijective_pi ?_
  have hleft : Function.LeftInverse (fun v ↦ (M y)⁻¹.mulVec v) (S y) := fun v ↦ by
    simp [hSM y, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (M y) hy.isUnit]
  have hright : Function.RightInverse (fun v ↦ (M y)⁻¹.mulVec v) (S y) := fun v ↦ by
    simp [hSM y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (M y) hy.isUnit]
  exact (e.bijective.of_comp_iff (f := T y)).1 ⟨hleft.injective, hright.surjective⟩

section Pointwise

variable {𝕜 ι κ Y : Type*} [NontriviallyNormedField 𝕜] [Finite ι] [Finite κ] [TopologicalSpace Y]
  {T : Y → (ι → 𝕜) →L[𝕜] (κ → 𝕜)} {s : Set Y} {y₀ : Y}

/-- If `T : Y → (ι → 𝕜) →L[𝕜] (κ → 𝕜)` between finite coordinate spaces over a nontrivially normed
field `𝕜` is continuous within `s` at `y₀` and `T y₀` is bijective, then `y ↦ (T y).inverse` is
continuous within `s` at `y₀` without requiring `CompleteSpace 𝕜`. -/
theorem ContinuousWithinAt.pi_clm_inverse (hT : ContinuousWithinAt T s y₀)
    (hbij : Function.Bijective (T y₀)) :
    ContinuousWithinAt (fun y ↦ (T y).inverse) s y₀ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  exact hT.clm_inverse_of_eventually_isInvertible ((T y₀).isInvertible_of_bijective_pi hbij)
    (eventually_isInvertible_pi_clm_within hT hbij)

/-- If `T : Y → (ι → 𝕜) →L[𝕜] (κ → 𝕜)` between finite coordinate spaces over a nontrivially normed
field `𝕜` is continuous at `y₀` and `T y₀` is bijective, then `y ↦ (T y).inverse` is continuous at
`y₀` without requiring `CompleteSpace 𝕜`. -/
theorem ContinuousAt.pi_clm_inverse (hT : ContinuousAt T y₀) (hbij : Function.Bijective (T y₀)) :
    ContinuousAt (fun y ↦ (T y).inverse) y₀ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  exact hT.clm_inverse_of_eventually_isInvertible
    (nhdsWithin_univ (a := y₀) ▸
      eventually_isInvertible_pi_clm_within ((continuousWithinAt_univ T y₀).2 hT) hbij)

/-- Along a family `T : Y → (ι → 𝕜) →L[𝕜] (κ → 𝕜)` between finite coordinate spaces over a
nontrivially normed field `𝕜` that is continuous on `s` and bijective at every point of `s`,
`y ↦ (T y).inverse` is continuous on `s`. -/
theorem ContinuousOn.pi_clm_inverse (hT : ContinuousOn T s)
    (hbij : ∀ y ∈ s, Function.Bijective (T y)) :
    ContinuousOn (fun y ↦ (T y).inverse) s :=
  fun y hy ↦ (hT y hy).pi_clm_inverse (hbij y hy)

end Pointwise

end Inverse
