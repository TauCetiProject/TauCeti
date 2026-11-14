/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Coordinates
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Analysis.Calculus.ContDiff.Matrix
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Kronecker

/-!
# Exterior powers of coordinate operators

For a continuous linear operator `g` between coordinate spaces over a normed field,
`g.exteriorPowerCoords j` is its `j`th exterior power read in the coordinates
`exteriorPower.piEquiv`, that is, the `j`th compound matrix of `g`, as a continuous linear
operator between the coordinate spaces of dimensions `m.choose j` and `n.choose j`. The
construction preserves identities and composition, and it depends continuously on the
operator (`ContinuousLinearMap.continuous_exteriorPowerCoords`), even by a `C^k` or analytic map
(`ContinuousLinearMap.contDiff_exteriorPowerCoords`), since its matrix entries are minors of the
matrix of `g`. It can therefore be applied to continuous, smooth or holomorphic families of
transition matrices. For an endomorphism of `Fin m → 𝕜` the compound matrix in the top degree `m`
is multiplication by the determinant (`ContinuousLinearMap.exteriorPowerCoords_self`).

In degrees zero and one the compound matrices are identified explicitly, through the continuous
coordinate equivalences `exteriorPower.piZeroContinuousEquiv` with the coordinate line and
`exteriorPower.piOneContinuousEquiv` with the original coordinate space.

For concatenated coordinate spaces `Fin (a + d) → 𝕜`, `TauCeti.exteriorPower.piProdInlL` and
`TauCeti.exteriorPower.piProdProjL` are the continuous bidegree-`(p, q)` Künneth inclusions and
projections between `Fin (a.choose p * d.choose q) → 𝕜` and `Fin ((a + d).choose n) → 𝕜`. They
resolve the identity over `p + q = n` and intertwine compound matrices of block-diagonal operators
(`TauCeti.splitCoords`) with Kronecker products (`ContinuousLinearMap.kronecker`) of compound
matrices.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {l m n : ℕ}

/-- The `j`th exterior power of an operator between coordinate spaces, read in the coordinates
`exteriorPower.piEquiv`: the `j`th compound matrix of the operator. -/
noncomputable def exteriorPowerCoords (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (Fin (m.choose j) → 𝕜) →L[𝕜] (Fin (n.choose j) → 𝕜) :=
  ⟨(g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)).exteriorPowerCoords j, LinearMap.continuous_on_pi _⟩

@[simp] theorem coe_exteriorPowerCoords (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (g.exteriorPowerCoords j : (Fin (m.choose j) → 𝕜) →ₗ[𝕜] (Fin (n.choose j) → 𝕜)) =
      (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)).exteriorPowerCoords j := (rfl)

@[simp] theorem exteriorPowerCoords_apply (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (v : Fin (m.choose j) → 𝕜) :
    g.exteriorPowerCoords j v = (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)).exteriorPowerCoords j v :=
  (rfl)

@[simp] theorem exteriorPowerCoords_id (j m : ℕ) :
    (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)).exteriorPowerCoords j =
      ContinuousLinearMap.id 𝕜 (Fin (m.choose j) → 𝕜) :=
  coe_injective (LinearMap.exteriorPowerCoords_id j m)

@[simp] theorem exteriorPowerCoords_comp (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (f : (Fin l → 𝕜) →L[𝕜] (Fin m → 𝕜)) :
    (g.comp f).exteriorPowerCoords j = (g.exteriorPowerCoords j).comp (f.exteriorPowerCoords j) :=
  coe_injective (LinearMap.exteriorPowerCoords_comp j (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜))
    (f : (Fin l → 𝕜) →ₗ[𝕜] (Fin m → 𝕜)))

/-- In the top degree, the compound matrix of an endomorphism of `Fin m → 𝕜` is multiplication
by its determinant on the coordinate line `Fin (m.choose m) → 𝕜`. -/
@[simp] theorem exteriorPowerCoords_self (g : (Fin m → 𝕜) →L[𝕜] (Fin m → 𝕜)) :
    g.exteriorPowerCoords m = g.det • ContinuousLinearMap.id 𝕜 (Fin (m.choose m) → 𝕜) :=
  coe_injective (LinearMap.exteriorPowerCoords_self (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin m → 𝕜)))

/-- The compound matrix as a sum of rank-one operators: its column at `t` is the vector of the
`j × j` minors of `g` with columns selected by the subset enumerated by `t`. -/
private theorem exteriorPowerCoords_eq_sum (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    g.exteriorPowerCoords j = ∑ t, smulRightL 𝕜 _ _ (proj t : (Fin (m.choose j) → 𝕜) →L[𝕜] 𝕜)
      (fun s ↦ (Matrix.of fun i k : Fin j ↦ g
        (Pi.single (Set.powersetCard.ofFinEmbEquiv.symm
          ((Set.powersetCard.finChooseEquiv m j).symm t) i) 1)
        (Set.powersetCard.ofFinEmbEquiv.symm
          ((Set.powersetCard.finChooseEquiv n j).symm s) k)).det) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp_rw [map_sum, map_smul, sum_apply, smulRightL_apply_apply, smulRight_apply, proj_apply]
  refine Finset.sum_congr rfl fun t _ ↦ congrArg _ (funext fun s ↦ ?_)
  rw [exteriorPowerCoords_apply, LinearMap.exteriorPowerCoords_single_apply]
  simp only [coe_coe]

/-- The compound matrix depends continuously on the operator. -/
theorem continuous_exteriorPowerCoords (j m n : ℕ) :
    Continuous (exteriorPowerCoords j : ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) → _) := by
  simp_rw [funext (exteriorPowerCoords_eq_sum j)]
  refine continuous_finsetSum _ fun t _ ↦ (smulRightL 𝕜 _ _
    (proj t : (Fin (m.choose j) → 𝕜) →L[𝕜] 𝕜)).continuous.comp' (continuous_pi fun s ↦ ?_)
  refine Continuous.matrix_det (continuous_matrix fun i k ↦ ?_)
  simp only [Matrix.of_apply]
  exact (continuous_apply _).comp
    (continuous_eval_const (F := (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) (Pi.single _ 1))

/-- The compound matrix depends on the operator by a `C^k` map for every `k`, including analytic
regularity, since its entries are minors of the matrix of the operator. -/
theorem contDiff_exteriorPowerCoords (j m n : ℕ) {k : WithTop ℕ∞} :
    ContDiff 𝕜 k (exteriorPowerCoords j : ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) → _) := by
  simp_rw [funext (exteriorPowerCoords_eq_sum j)]
  refine ContDiff.sum fun t _ ↦ ?_
  apply ContDiff.continuousLinearMap_comp
  refine contDiff_pi.2 fun s ↦ ContDiff.matrix_det fun i l ↦ ?_
  simp only [Matrix.of_apply]
  exact (contDiff_apply 𝕜 (F' := fun _ : Fin n ↦ 𝕜) _).comp
    (contDiff_id.clm_apply contDiff_const)

end ContinuousLinearMap

namespace exteriorPower

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {m n : ℕ}

/-- `exteriorPower.piZeroEquiv` as a continuous linear equivalence. -/
noncomputable def piZeroContinuousEquiv (m : ℕ) : (Fin (m.choose 0) → 𝕜) ≃L[𝕜] (Fin 1 → 𝕜) :=
  { toLinearEquiv := piZeroEquiv m
    continuous_toFun := (piZeroEquiv m).toLinearMap.continuous_on_pi
    continuous_invFun := (piZeroEquiv m).symm.toLinearMap.continuous_on_pi }

@[simp] theorem coe_piZeroContinuousEquiv (m : ℕ) :
    (piZeroContinuousEquiv 𝕜 m : (Fin (m.choose 0) → 𝕜) ≃ₗ[𝕜] (Fin 1 → 𝕜)) = piZeroEquiv m :=
  (rfl)

variable {𝕜} in
/-- In degree zero, every compound matrix is the identity of the coordinate line. -/
theorem piZeroContinuousEquiv_comp_exteriorPowerCoords (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (piZeroContinuousEquiv 𝕜 n : (Fin (n.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)).comp
      (g.exteriorPowerCoords 0) = piZeroContinuousEquiv 𝕜 m := by
  ext v : 1
  exact piZeroEquiv_exteriorPowerCoords (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) v

/-- `exteriorPower.piOneEquiv` as a continuous linear equivalence. -/
noncomputable def piOneContinuousEquiv (m : ℕ) : (Fin (m.choose 1) → 𝕜) ≃L[𝕜] (Fin m → 𝕜) :=
  { toLinearEquiv := piOneEquiv m
    continuous_toFun := (piOneEquiv m).toLinearMap.continuous_on_pi
    continuous_invFun := (piOneEquiv m).symm.toLinearMap.continuous_on_pi }

@[simp] theorem coe_piOneContinuousEquiv (m : ℕ) :
    (piOneContinuousEquiv 𝕜 m : (Fin (m.choose 1) → 𝕜) ≃ₗ[𝕜] (Fin m → 𝕜)) = piOneEquiv m :=
  (rfl)

variable {𝕜} in
/-- In degree one, the compound matrix of `g` is `g`, read in
`exteriorPower.piOneContinuousEquiv`. -/
theorem piOneContinuousEquiv_comp_exteriorPowerCoords (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (piOneContinuousEquiv 𝕜 n : (Fin (n.choose 1) → 𝕜) →L[𝕜] (Fin n → 𝕜)).comp
      (g.exteriorPowerCoords 1) =
      g.comp (piOneContinuousEquiv 𝕜 m : (Fin (m.choose 1) → 𝕜) →L[𝕜] (Fin m → 𝕜)) := by
  ext v : 1
  exact piOneEquiv_exteriorPowerCoords (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) v

end exteriorPower

namespace TauCeti.exteriorPower

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- `TauCeti.exteriorPower.piProdInl` as a continuous linear operator between coordinate spaces. -/
noncomputable def piProdInlL (a d p q n : ℕ) (h : p + q = n) :
    (Fin (a.choose p * d.choose q) → 𝕜) →L[𝕜] (Fin ((a + d).choose n) → 𝕜) :=
  ⟨piProdInl 𝕜 a d p q n h, (piProdInl 𝕜 a d p q n h).continuous_on_pi⟩

/-- `TauCeti.exteriorPower.piProdProj` as a continuous linear operator between coordinate spaces. -/
noncomputable def piProdProjL (a d p q n : ℕ) :
    (Fin ((a + d).choose n) → 𝕜) →L[𝕜] (Fin (a.choose p * d.choose q) → 𝕜) :=
  ⟨piProdProj 𝕜 a d p q n, (piProdProj 𝕜 a d p q n).continuous_on_pi⟩

@[simp]
theorem coe_piProdInlL (a d p q n : ℕ) (h : p + q = n) :
    (piProdInlL 𝕜 a d p q n h :
      (Fin (a.choose p * d.choose q) → 𝕜) →ₗ[𝕜] (Fin ((a + d).choose n) → 𝕜)) =
      piProdInl 𝕜 a d p q n h :=
  (rfl)

@[simp]
theorem coe_piProdProjL (a d p q n : ℕ) :
    (piProdProjL 𝕜 a d p q n :
      (Fin ((a + d).choose n) → 𝕜) →ₗ[𝕜] (Fin (a.choose p * d.choose q) → 𝕜)) =
      piProdProj 𝕜 a d p q n :=
  (rfl)

@[simp]
theorem piProdInlL_apply (a d p q n : ℕ) (h : p + q = n) (v : Fin (a.choose p * d.choose q) → 𝕜) :
    piProdInlL 𝕜 a d p q n h v = piProdInl 𝕜 a d p q n h v :=
  (rfl)

@[simp]
theorem piProdProjL_apply (a d p q n : ℕ) (v : Fin ((a + d).choose n) → 𝕜) :
    piProdProjL 𝕜 a d p q n v = piProdProj 𝕜 a d p q n v :=
  (rfl)

variable {𝕜}

/-- `piProdProjL` is left inverse to `piProdInlL` in matching bidegree. -/
@[simp]
theorem piProdProjL_comp_piProdInlL_self (a d p q n : ℕ) (h : p + q = n) :
    (piProdProjL 𝕜 a d p q n).comp (piProdInlL 𝕜 a d p q n h) =
      ContinuousLinearMap.id 𝕜 (Fin (a.choose p * d.choose q) → 𝕜) :=
  ContinuousLinearMap.coe_injective (piProdProj_comp_piProdInl_self a d p q n h)

/-- `piProdProjL` vanishes on the image of `piProdInlL` in any differing bidegree. -/
theorem piProdProjL_comp_piProdInlL_of_ne {a d p' q' p q n : ℕ} (h : p + q = n)
    (hne : p ≠ p' ∨ q ≠ q') :
    (piProdProjL 𝕜 a d p' q' n).comp (piProdInlL 𝕜 a d p q n h) = 0 :=
  ContinuousLinearMap.coe_injective (piProdProj_comp_piProdInl_of_ne h hne)

/-- The continuous Künneth projections and inclusions resolve the identity of
`Fin ((a + d).choose n) → 𝕜`. -/
theorem sum_piProdInlL_comp_piProdProjL (a d n : ℕ) :
    ∑ i : Fin (n + 1),
      (piProdInlL 𝕜 a d i (n - i) n (by omega)).comp (piProdProjL 𝕜 a d i (n - i) n) =
    ContinuousLinearMap.id 𝕜 (Fin ((a + d).choose n) → 𝕜) := by
  apply ContinuousLinearMap.coe_injective
  simpa only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_comp,
    coe_piProdInlL, coe_piProdProjL, ContinuousLinearMap.coe_id] using
    sum_piProdInl_comp_piProdProj (R := 𝕜) a d n

/-- In the top degree `a + d`, `piProdInlL` and `piProdProjL` in bidegree `(a, d)` are two-sided
inverses. -/
@[simp]
theorem piProdInlL_comp_piProdProjL_top (a d : ℕ) :
    (piProdInlL 𝕜 a d a d (a + d) rfl).comp (piProdProjL 𝕜 a d a d (a + d)) =
      ContinuousLinearMap.id 𝕜 (Fin ((a + d).choose (a + d)) → 𝕜) :=
  ContinuousLinearMap.coe_injective (piProdInl_comp_piProdProj_top a d)

private theorem toLinearMap_splitCoords_blockDiag {a a' d d' : ℕ}
    (f : (Fin a → 𝕜) →L[𝕜] (Fin a' → 𝕜)) (g : (Fin d → 𝕜) →L[𝕜] (Fin d' → 𝕜)) :
    (((splitCoords (𝕜 := 𝕜) a' d').symm.toContinuousLinearMap.comp
      ((f.prodMap g).comp (splitCoords (𝕜 := 𝕜) a d).toContinuousLinearMap)) :
        (Fin (a + d) → 𝕜) →ₗ[𝕜] (Fin (a' + d') → 𝕜)) =
      (LinearEquiv.piFinAppend 𝕜 𝕜 a' d').symm.toLinearMap ∘ₗ
        (f : (Fin a → 𝕜) →ₗ[𝕜] (Fin a' → 𝕜)).prodMap (g : (Fin d → 𝕜) →ₗ[𝕜] (Fin d' → 𝕜)) ∘ₗ
        (LinearEquiv.piFinAppend 𝕜 𝕜 a d).toLinearMap := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.coe_prodMap,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap, splitCoords_apply, splitCoords_symm_apply,
    LinearEquiv.piFinAppend_apply, LinearEquiv.piFinAppend_symm_apply, LinearMap.prodMap_apply]

/-- `piProdInlL` intertwines the Kronecker product of compound matrices with the compound matrix
of a block-diagonal operator formed with `splitCoords`. -/
theorem exteriorPowerCoords_splitCoords_comp_piProdInlL {a a' d d' : ℕ}
    (f : (Fin a → 𝕜) →L[𝕜] (Fin a' → 𝕜)) (g : (Fin d → 𝕜) →L[𝕜] (Fin d' → 𝕜))
    (p q n : ℕ) (h : p + q = n) :
    (((splitCoords (𝕜 := 𝕜) a' d').symm.toContinuousLinearMap.comp
        ((f.prodMap g).comp (splitCoords (𝕜 := 𝕜) a d).toContinuousLinearMap)).exteriorPowerCoords
        n).comp (piProdInlL 𝕜 a d p q n h) =
      (piProdInlL 𝕜 a' d' p q n h).comp
        ((f.exteriorPowerCoords p).kronecker (g.exteriorPowerCoords q)) := by
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_exteriorPowerCoords, toLinearMap_splitCoords_blockDiag,
    coe_piProdInlL, ContinuousLinearMap.toLinearMap_kronecker_eq]
  exact exteriorPowerCoords_piFinAppend_comp_piProdInl
    (f : (Fin a → 𝕜) →ₗ[𝕜] (Fin a' → 𝕜)) (g : (Fin d → 𝕜) →ₗ[𝕜] (Fin d' → 𝕜)) p q n h

/-- `piProdProjL` intertwines the compound matrix of a block-diagonal operator formed with
`splitCoords` with the Kronecker product of compound matrices. -/
theorem piProdProjL_comp_exteriorPowerCoords_splitCoords {a a' d d' : ℕ}
    (f : (Fin a → 𝕜) →L[𝕜] (Fin a' → 𝕜)) (g : (Fin d → 𝕜) →L[𝕜] (Fin d' → 𝕜))
    (p q n : ℕ) :
    (piProdProjL 𝕜 a' d' p q n).comp
        (((splitCoords (𝕜 := 𝕜) a' d').symm.toContinuousLinearMap.comp
          ((f.prodMap g).comp
            (splitCoords (𝕜 := 𝕜) a d).toContinuousLinearMap)).exteriorPowerCoords n) =
      ((f.exteriorPowerCoords p).kronecker (g.exteriorPowerCoords q)).comp
        (piProdProjL 𝕜 a d p q n) := by
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_exteriorPowerCoords, toLinearMap_splitCoords_blockDiag,
    coe_piProdProjL, ContinuousLinearMap.toLinearMap_kronecker_eq]
  simp only [LinearMap.comp_assoc]
  exact piProdProj_comp_exteriorPowerCoords_piFinAppend
    (f : (Fin a → 𝕜) →ₗ[𝕜] (Fin a' → 𝕜)) (g : (Fin d → 𝕜) →ₗ[𝕜] (Fin d' → 𝕜)) p q n

end TauCeti.exteriorPower
