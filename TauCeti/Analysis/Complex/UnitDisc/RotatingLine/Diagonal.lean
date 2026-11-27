/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.DiagonalBoundary
public import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Fredholm
import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Analysis.Fredholm.Pi
import TauCeti.LinearAlgebra.Pi.Map

/-!
# The Cauchy–Riemann operator with a diagonal boundary condition in higher rank

Let `D` be the open unit disc, `0 < α < 1`, `ι` a finite index type and `k : ι → ℤ`. On the
closed subspace `X_k` of `C^{1,α}(D, ι → ℂ)` of the maps whose continuous extension to the closed
disc takes boundary values in the diagonal totally real subspaces `⊕ᵢ e^{i kᵢ θ/2} ℝ`
(`TauCeti.rotatingLinePiSubspace`), consider the Cauchy–Riemann operator

`∂/∂(conj z) : X_k → C^{0,α}(D, ι → ℂ)` (`TauCeti.rotatingLinePiConjWirtingerDerivL`).

This is the Hölder realization of the Cauchy–Riemann operator on the trivial bundle `D × ℂ^ι`
with the boundary loop `⊕ᵢ e^{i kᵢ θ/2} ℝ`, the direct sum of the rotating real lines of Maslov
indices `kᵢ`, of Maslov index `μ = ∑ i, k i`.

The operator acts coordinatewise. The coordinates identify `X_k` with the product of the rank-one
subspaces `X_{k i}` (`TauCeti.rotatingLinePiSubspaceEquiv`) and `C^{0,α}(D, ι → ℂ)` with the
product of the spaces `C^{0,α}(D)` (`TauCeti.HolderSpace.piEquivL`), and through these
isomorphisms the operator is the product of the rank-one operators
`TauCeti.rotatingLineConjWirtingerDerivL (k i)`
(`TauCeti.piEquivL_comp_rotatingLinePiConjWirtingerDerivL`). Hence:

* **Fredholm property and index.** The operator is Fredholm exactly when each rank-one operator
  is (`TauCeti.isFredholm_rotatingLinePiConjWirtingerDerivL_iff`), and then its index is the sum
  of their indices (`TauCeti.index_rotatingLinePiConjWirtingerDerivL_eq_sum`). These hold for
  every `k`.
* **The kernel.** For `0 < α ≤ 1` and every `k`, the values on the closed disc identify the kernel
  with the space `TauCeti.unitDiscCauchyRiemannKernelPi k` of maps holomorphic on the open disc,
  continuous on its closure and satisfying the diagonal boundary condition
  (`TauCeti.rotatingLinePiConjWirtingerDerivKerEquiv`), of real dimension `∑ i, (k i + 1).toNat`
  (`TauCeti.finrank_ker_rotatingLinePiConjWirtingerDerivL`).
* **The Riemann–Roch formula on the disc.** When every `k i ≥ -1` the operator is onto
  (`TauCeti.rotatingLinePiConjWirtingerDerivL_surjective`), so it is Fredholm
  (`TauCeti.isFredholm_rotatingLinePiConjWirtingerDerivL`) of index
  `n + ∑ i, k i = n χ(D) + μ`, for `n` the cardinality of `ι`
  (`TauCeti.index_rotatingLinePiConjWirtingerDerivL`). For `k = 0` this is the index `n` of the
  disc with boundary condition `(ℂⁿ, ℝⁿ)`, and for the normalization `k = 3` the index `4 n`.

## Main declarations

* `TauCeti.rotatingLinePiConjWirtingerDerivL`: the operator `∂/∂(conj z) : X_k → C^{0,α}`.
* `TauCeti.piEquivL_comp_rotatingLinePiConjWirtingerDerivL`: it is the product of the rank-one
  operators.
* `TauCeti.isFredholm_rotatingLinePiConjWirtingerDerivL_iff`,
  `TauCeti.index_rotatingLinePiConjWirtingerDerivL_eq_sum`: the Fredholm property and the index
  in terms of the rank-one operators.
* `TauCeti.rotatingLinePiConjWirtingerDerivKerEquiv`,
  `TauCeti.finrank_ker_rotatingLinePiConjWirtingerDerivL`: the kernel and its dimension.
* `TauCeti.rotatingLinePiConjWirtingerDerivL_surjective`,
  `TauCeti.isFredholm_rotatingLinePiConjWirtingerDerivL`,
  `TauCeti.index_rotatingLinePiConjWirtingerDerivL`: surjectivity, the Fredholm property and the
  index `n + ∑ i, k i` when every `k i ≥ -1`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (Theorem C.1.10, the Riemann–Roch theorem for
  discs, reduced in its proof to the diagonal boundary conditions `⊕ᵢ e^{i kᵢ θ/2} ℝ` and to rank
  one, Theorem C.4.1).
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric Module Set CkHolderSpaceOn
open scoped NNReal

variable {ι : Type*} [Fintype ι] {k : ι → ℤ} {α : ℝ≥0}

/-! ### The operator -/

variable (k α) in
/-- The Cauchy–Riemann operator `u ↦ ∂u/∂(conj z)` on the closed subspace `X_k` of
`C^{1,α}(D, ι → ℂ)` of the maps with boundary values in `⊕ᵢ e^{i kᵢ θ/2} ℝ`, with values in
`C^{0,α}(D, ι → ℂ)`, for the open unit disc `D`. -/
def rotatingLinePiConjWirtingerDerivL :
    rotatingLinePiSubspace k α →L[ℝ] HolderSpace α (unitBallOpens ℂ) (ι → ℂ) :=
  conjWirtingerDerivL α (unitBallOpens ℂ) (ι → ℂ) ∘L (rotatingLinePiSubspace k α).subtypeL

/-- The operator `TauCeti.rotatingLinePiConjWirtingerDerivL` is the Cauchy–Riemann operator of
`C^{1,α}(D, ι → ℂ)` on the elements of `X_k`. -/
@[simp]
theorem rotatingLinePiConjWirtingerDerivL_apply (u : rotatingLinePiSubspace k α) :
    rotatingLinePiConjWirtingerDerivL k α u = conjWirtingerDerivL α (unitBallOpens ℂ) (ι → ℂ) u :=
  (rfl)

/-- **The operator acts coordinatewise.** The `i`-th coordinate of `∂u/∂(conj z)` is the
Cauchy–Riemann derivative of the `i`-th coordinate of `u`. -/
theorem rotatingLineConjWirtingerDerivL_rotatingLinePiSubspaceEquiv_apply [DecidableEq ι]
    (u : rotatingLinePiSubspace k α) (i : ι) :
    rotatingLineConjWirtingerDerivL (k i) α (rotatingLinePiSubspaceEquiv k α u i) =
      HolderSpace.compLeftL (.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i)
        (rotatingLinePiConjWirtingerDerivL k α u) := by
  rw [rotatingLineConjWirtingerDerivL_apply, rotatingLinePiConjWirtingerDerivL_apply,
    coe_rotatingLinePiSubspaceEquiv_apply]
  exact conjWirtingerDerivL_compLeftL (.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i) u.val

/-- **The operator is the product of the rank-one operators.** Through the coordinate isomorphisms
`TauCeti.rotatingLinePiSubspaceEquiv` of `X_k` and `TauCeti.HolderSpace.piEquivL` of
`C^{0,α}(D, ι → ℂ)`, the Cauchy–Riemann operator on `X_k` is the product of the Cauchy–Riemann
operators on the rank-one subspaces `X_{k i}`. -/
theorem piEquivL_comp_rotatingLinePiConjWirtingerDerivL [DecidableEq ι] :
    (HolderSpace.piEquivL α (unitBallOpens ℂ) ℂ ι :
        HolderSpace α (unitBallOpens ℂ) (ι → ℂ) →L[ℝ] _) ∘L rotatingLinePiConjWirtingerDerivL k α =
      ContinuousLinearMap.piMap (fun i ↦ rotatingLineConjWirtingerDerivL (k i) α) ∘L
        (rotatingLinePiSubspaceEquiv k α : rotatingLinePiSubspace k α →L[ℝ] _) :=
  ContinuousLinearMap.ext fun u ↦ funext fun i ↦ by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      HolderSpace.piEquivL_apply, ContinuousLinearMap.coe_piMap', Pi.map_apply]
    exact (rotatingLineConjWirtingerDerivL_rotatingLinePiSubspaceEquiv_apply u i).symm

/-! ### Fredholm property and index in terms of the rank-one operators -/

/-- **The Fredholm property in terms of rank one.** The Cauchy–Riemann operator on `X_k` is
Fredholm exactly when, for every coordinate `i`, the Cauchy–Riemann operator on the rank-one
subspace `X_{k i}` is Fredholm. -/
theorem isFredholm_rotatingLinePiConjWirtingerDerivL_iff :
    (rotatingLinePiConjWirtingerDerivL k α).IsFredholm ↔
      ∀ i, (rotatingLineConjWirtingerDerivL (k i) α).IsFredholm := by
  classical
  rw [ContinuousLinearMap.isFredholm_iff_of_comp_eq _ _
    piEquivL_comp_rotatingLinePiConjWirtingerDerivL, ContinuousLinearMap.isFredholm_piMap_iff]

/-- **The index is additive over the coordinates.** If the Cauchy–Riemann operator on each
rank-one subspace `X_{k i}` is Fredholm, the index of the Cauchy–Riemann operator on `X_k` is the
sum of their indices. -/
theorem index_rotatingLinePiConjWirtingerDerivL_eq_sum
    (h : ∀ i, (rotatingLineConjWirtingerDerivL (k i) α).IsFredholm) :
    (rotatingLinePiConjWirtingerDerivL k α).index =
      ∑ i, (rotatingLineConjWirtingerDerivL (k i) α).index := by
  classical
  have := fun i ↦ (h i).finite_ker
  have := fun i ↦ (h i).finite_coker
  rw [← ContinuousLinearMap.index_equiv_comp _ (HolderSpace.piEquivL α (unitBallOpens ℂ) ℂ ι),
    piEquivL_comp_rotatingLinePiConjWirtingerDerivL, ContinuousLinearMap.index_comp_equiv,
    ContinuousLinearMap.index_piMap]

/-! ### The kernel -/

variable [DecidableEq ι] in
/-- The kernel of the Cauchy–Riemann operator on `X_k` is the product of the kernels of the
rank-one operators on the subspaces `X_{k i}`, by taking coordinates. -/
private def rotatingLinePiConjWirtingerDerivKerPiEquiv :
    (rotatingLinePiConjWirtingerDerivL k α).ker ≃ₗ[ℝ]
      ∀ i, (rotatingLineConjWirtingerDerivL (k i) α).ker where
  toFun u i := ⟨rotatingLinePiSubspaceEquiv k α u i, by
    have hu : rotatingLinePiConjWirtingerDerivL k α u = 0 := u.property
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      rotatingLineConjWirtingerDerivL_rotatingLinePiSubspaceEquiv_apply, hu, map_zero]⟩
  invFun v := ⟨(rotatingLinePiSubspaceEquiv k α).symm fun i ↦ v i, by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine HolderSpace.ext_compLeftL_proj fun i ↦ ?_
    rw [← rotatingLineConjWirtingerDerivL_rotatingLinePiSubspaceEquiv_apply,
      ContinuousLinearEquiv.apply_symm_apply, map_zero]
    exact (v i).property⟩
  map_add' _ _ := funext fun _ ↦ Subtype.ext (by simp)
  map_smul' _ _ := funext fun _ ↦ Subtype.ext (by simp)
  left_inv u := Subtype.ext ((rotatingLinePiSubspaceEquiv k α).symm_apply_apply u)
  right_inv v := funext fun i ↦ Subtype.ext (by
    simp only [ContinuousLinearEquiv.apply_symm_apply])

/-- The coordinates of an element of the kernel. -/
private theorem coe_rotatingLinePiConjWirtingerDerivKerPiEquiv_apply [DecidableEq ι]
    (u : (rotatingLinePiConjWirtingerDerivL k α).ker) (i : ι) :
    ((rotatingLinePiConjWirtingerDerivKerPiEquiv u i : rotatingLineSubspace (k i) α) :
        CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ) =
      compLeftL (.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i) u.val.val :=
  coe_rotatingLinePiSubspaceEquiv_apply u.val i

variable (k α) in
/-- **The kernel is the space of holomorphic solutions.** For `0 < α ≤ 1`, the values on the
closed unit disc identify the kernel of the Cauchy–Riemann operator on `X_k` with the space
`TauCeti.unitDiscCauchyRiemannKernelPi k` of maps `D → ι → ℂ` holomorphic on the open disc,
continuous on its closure, with boundary values in `⊕ᵢ e^{i kᵢ θ/2} ℝ`. -/
def rotatingLinePiConjWirtingerDerivKerEquiv (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (rotatingLinePiConjWirtingerDerivL k α).ker ≃ₗ[ℝ] unitDiscCauchyRiemannKernelPi k :=
  haveI := Classical.decEq ι
  rotatingLinePiConjWirtingerDerivKerPiEquiv ≪≫ₗ
    LinearEquiv.piCongrRight (fun i ↦ rotatingLineConjWirtingerDerivKerEquiv (k i) α hα0 hα1) ≪≫ₗ
      (unitDiscCauchyRiemannKernelPiEquiv k).symm

/-- The isomorphism `TauCeti.rotatingLinePiConjWirtingerDerivKerEquiv` sends an element of the
kernel to the values of its continuous extension on the closed disc. -/
@[simp]
theorem rotatingLinePiConjWirtingerDerivKerEquiv_apply (hα0 : 0 < α) (hα1 : α ≤ 1)
    (u : (rotatingLinePiConjWirtingerDerivL k α).ker) (z : closedBall (0 : ℂ) 1) :
    (rotatingLinePiConjWirtingerDerivKerEquiv k α hα0 hα1 u : closedBall (0 : ℂ) 1 → ι → ℂ) z =
      ((u : rotatingLinePiSubspace k α) :
        CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)).closureExtend z := by
  funext i
  simp only [rotatingLinePiConjWirtingerDerivKerEquiv, LinearEquiv.trans_apply,
    unitDiscCauchyRiemannKernelPiEquiv_symm_apply, LinearEquiv.piCongrRight_apply,
    rotatingLineConjWirtingerDerivKerEquiv_apply,
    coe_rotatingLinePiConjWirtingerDerivKerPiEquiv_apply]
  exact closureExtend_compLeftL (convex_unitBallOpens ℂ) (.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) i)
    u.val.val (mem_closure_unitBallOpens.2 (mem_closedBall_zero_iff.1 z.property))

/-- **The dimension of the kernel.** For `0 < α ≤ 1`, the kernel of the Cauchy–Riemann operator on
`X_k` has real dimension `∑ i, (k i + 1).toNat`. -/
theorem finrank_ker_rotatingLinePiConjWirtingerDerivL (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finrank ℝ (rotatingLinePiConjWirtingerDerivL k α).ker = ∑ i, (k i + 1).toNat :=
  (rotatingLinePiConjWirtingerDerivKerEquiv k α hα0 hα1).finrank_eq.trans
    (finrank_unitDiscCauchyRiemannKernelPi k)

/-! ### The Riemann–Roch formula on the disc -/

/-- **Surjectivity for Maslov indices at least `-1`.** If `k i ≥ -1` for every `i` and
`0 < α < 1`, every `α`-Hölder forcing `f : D → ι → ℂ` is `∂u/∂(conj z)` for some
`u ∈ C^{1,α}(D, ι → ℂ)` with boundary values in `⊕ᵢ e^{i kᵢ θ/2} ℝ`. -/
theorem rotatingLinePiConjWirtingerDerivL_surjective (hk : ∀ i, -1 ≤ k i) (hα0 : 0 < α)
    (hα1 : α < 1) : Function.Surjective (rotatingLinePiConjWirtingerDerivL k α) := by
  classical
  set Ψ := HolderSpace.piEquivL α (unitBallOpens ℂ) ℂ ι
  -- After the coordinate isomorphisms, the operator is a product of surjective operators.
  have h : Function.Surjective
      ((Ψ : HolderSpace α (unitBallOpens ℂ) (ι → ℂ) →L[ℝ] ι → HolderSpace α (unitBallOpens ℂ) ℂ) ∘L
        rotatingLinePiConjWirtingerDerivL k α) := by
    rw [piEquivL_comp_rotatingLinePiConjWirtingerDerivL]
    exact (Function.Surjective.piMap fun i ↦
      rotatingLineConjWirtingerDerivL_surjective (hk i) hα0 hα1).comp
        (rotatingLinePiSubspaceEquiv k α).surjective
  intro f
  obtain ⟨u, hu⟩ := h (Ψ f)
  exact ⟨u, Ψ.injective hu⟩

/-- **The Cauchy–Riemann operator with a diagonal boundary condition is Fredholm.** If `k i ≥ -1`
for every `i` and `0 < α < 1`, the operator `∂/∂(conj z) : X_k → C^{0,α}(D, ι → ℂ)` is a Fredholm
operator. -/
theorem isFredholm_rotatingLinePiConjWirtingerDerivL (hk : ∀ i, -1 ≤ k i) (hα0 : 0 < α)
    (hα1 : α < 1) : (rotatingLinePiConjWirtingerDerivL k α).IsFredholm :=
  isFredholm_rotatingLinePiConjWirtingerDerivL_iff.2 fun i ↦
    isFredholm_rotatingLineConjWirtingerDerivL (hk i) hα0 hα1

/-- **The Riemann–Roch formula on the disc for a diagonal boundary condition.** If `k i ≥ -1` for
every `i` and `0 < α < 1`, the Fredholm index of `∂/∂(conj z) : X_k → C^{0,α}(D, ι → ℂ)` is
`n + ∑ i, k i = n χ(D) + μ`, for the rank `n` of `ℂ^ι`, the Euler characteristic `χ(D) = 1` and
the Maslov index `μ = ∑ i, k i` of the boundary loop `⊕ᵢ e^{i kᵢ θ/2} ℝ`. -/
theorem index_rotatingLinePiConjWirtingerDerivL (hk : ∀ i, -1 ≤ k i) (hα0 : 0 < α)
    (hα1 : α < 1) :
    (rotatingLinePiConjWirtingerDerivL k α).index = Fintype.card ι + ∑ i, k i := by
  rw [index_rotatingLinePiConjWirtingerDerivL_eq_sum fun i ↦
      isFredholm_rotatingLineConjWirtingerDerivL (hk i) hα0 hα1,
    Finset.sum_congr rfl fun i _ ↦ index_rotatingLineConjWirtingerDerivL (hk i) hα0 hα1,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_one, add_comm]

end TauCeti
