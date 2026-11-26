/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.DirectSum
public import TauCeti.Analysis.Fredholm.DeterminantLine.Naturality
public import TauCeti.Analysis.Fredholm.Involution
public import TauCeti.Analysis.Normed.Operator.Eigenspace
public import TauCeti.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Determinant lines of operators commuting with involutions

Let `σE` and `σF` be continuous linear involutions of `E` and `F`, and let `T : E →L F` intertwine
them, `T ∘ σE = σF ∘ T`. Splitting `E` and `F` into the `±1`-eigenspaces of the involutions
(`ContinuousLinearMap.equivEigenspaceProd`) conjugates `T` to the direct sum `T₊ ⊕ T₋` of its
restrictions `T₊` and `T₋` to the `1`- and `-1`-eigenspaces
(`ContinuousLinearMap.equivEigenspaceProd_comp`). So `T` is Fredholm exactly when `T₊` and `T₋`
are (`ContinuousLinearMap.isFredholm_iff_isFredholm_restrictEigenspace_one_and_neg_one`), and its
determinant line is the tensor product of theirs,

`det T ≃ det T₊ ⊗ det T₋`  (`ContinuousLinearMap.detLineEigenspaceEquiv`):

the transport along the splitting (`LinearMap.detLineCongr`), followed by the direct sum
isomorphism `LinearMap.detLineProdMapEquiv`, normalized by the sign
`(-1) ^ (dim coker T₊ * dim coker T₋)`. Cokernel dimensions jump along families of operators, and
with this sign the direct sum isomorphism carries continuous orientations to continuous
orientations (`TauCeti.IsDetLineCoherentOn.prodMap`).

This file shows that the splitting is compatible with orientation transport and with the
orientations of bijective operators.

* **Orientation transport.** Let `T t` be a path of Fredholm operators intertwining the same
  involutions, continuous between `a` and `b`. Its restrictions are continuous paths of Fredholm
  operators (`ContinuousOn.restrictEigenspace`). Transporting along `T` the orientation of `det T a`
  that splits as the orientations of `v₀ ∈ det T₊ a` and `v₀' ∈ det T₋ a` gives the orientation
  of `det T b` that splits as their transports along `T₊` and `T₋`
  (`TauCeti.detLineOrientationTransport_detLineEigenspaceEquiv_symm`). The proof transports the
  orientation along the constant splitting (`TauCeti.detLineOrientationTransport_map_detLineCongr`)
  and splits the transport along the direct sum
  (`TauCeti.detLineOrientationTransport_prodMap`).
* **Bijective operators.** If `T` is bijective, so are `T₊` and `T₋`
  (`ContinuousLinearMap.restrictEigenspace_bijective`), all cokernels vanish, and reading the
  split element `v ⊗ v'` of `det T` in the trivialization given by bijectivity
  (`LinearMap.detLineEquivOfBijective`) gives the product of the readings of `v` and `v'`
  (`ContinuousLinearMap.detLineEquivOfBijective_detLineEigenspaceEquiv_symm_tmul`).
* **Signs.** Together: when `T b` is bijective, the sign of an orientation transported along `T`
  from a split orientation at `a` is the product of the signs of the orientations transported along
  `T₊` and `T₋` (`TauCeti.sign_detLineEquivOfBijective_eq_mul_of_detLineOrientationTransport`).

In Taubes's count of pseudoholomorphic curves the determinant signs of the normal operators of a
square-zero torus twisted by its real sign characters label the torus. On the double cover of the
torus cut out by a sign character `ι`, the deck transformation is an involution commuting with
the normal operator of the cover, and its `±1`-eigenspaces are the sections twisted by the
restriction of a character `χ` and by `χ + ι`. The sign of the operator on the cover is therefore
the product of the signs of the two twisted operators, once the reference orientations at the
starting point of the path split in the same way.

## Main definitions

* `ContinuousLinearMap.detLineEigenspaceEquiv`: `det T ≃ det T₊ ⊗ det T₋` for an operator
  commuting with involutions.

## Main results

* `ContinuousLinearMap.detLineEigenspaceEquiv_symm_tmul`: the inverse isomorphism on pure tensors.
* `ContinuousLinearMap.detLineCongr_detLineEigenspaceEquiv_symm_tmul`: read along the splitting,
  it is the normalized direct sum in the determinant line of `T₊ ⊕ T₋`.
* `ContinuousLinearMap.detLineEquivOfBijective_detLineEigenspaceEquiv_symm_tmul`: for bijective
  operators the trivializations given by bijectivity multiply.
* `TauCeti.detLineOrientationTransport_detLineEigenspaceEquiv_symm`: orientation transport
  commutes with the splitting.
* `TauCeti.sign_detLineEquivOfBijective_eq_mul_of_detLineOrientationTransport`: transported
  signs multiply.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

noncomputable section

open Module Module.End TensorProduct Set

namespace ContinuousLinearMap

section Splitting

variable {𝕜 E F : Type*} [Field 𝕜] [NeZero (2 : 𝕜)]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] {σE : E →L[𝕜] E} {σF : F →L[𝕜] F}

variable (T : E →L[𝕜] F) (hσE : Function.Involutive σE) (hσF : Function.Involutive σF)
  (hT : T.comp σE = σF.comp T)
  [FiniteDimensional 𝕜 (T.restrictEigenspace hT 1).ker]
  [FiniteDimensional 𝕜 (T.restrictEigenspace hT (-1)).ker]
  [FiniteDimensional 𝕜 (eigenspace (σF : End 𝕜 F) 1 ⧸ (T.restrictEigenspace hT 1).range)]
  [FiniteDimensional 𝕜 (eigenspace (σF : End 𝕜 F) (-1) ⧸ (T.restrictEigenspace hT (-1)).range)]

/-- **The determinant line of an operator commuting with involutions.** If `T` intertwines the
involutions `σE` and `σF`, its determinant line is the tensor product of the determinant lines of
its restrictions `T₊` and `T₋` to the `1`- and `-1`-eigenspaces: the transport along the
splitting of `E` and `F` by the involutions, followed by the direct sum isomorphism
`LinearMap.detLineProdMapEquiv` and the sign `(-1) ^ (dim coker T₊ * dim coker T₋)`. With this
sign the isomorphism is compatible with orientation transport along families
(`TauCeti.detLineOrientationTransport_detLineEigenspaceEquiv_symm`). -/
def detLineEigenspaceEquiv :
    (T : E →ₗ[𝕜] F).detLine ≃ₗ[𝕜]
      (T.restrictEigenspace hT 1 : eigenspace (σE : End 𝕜 E) 1 →ₗ[𝕜]
          eigenspace (σF : End 𝕜 F) 1).detLine ⊗[𝕜]
        (T.restrictEigenspace hT (-1) : eigenspace (σE : End 𝕜 E) (-1) →ₗ[𝕜]
          eigenspace (σF : End 𝕜 F) (-1)).detLine :=
  ((T : E →ₗ[𝕜] F).detLineCongr (equivEigenspaceProd σE hσE).toLinearEquiv
      (equivEigenspaceProd σF hσF).toLinearEquiv
      (prodMap_comp_equivEigenspaceProd T hσE hσF hT)).trans
    ((LinearMap.detLineProdMapEquiv _ _).trans (LinearEquiv.smulOfUnit
      ((-1 : 𝕜ˣ) ^ (finrank 𝕜 (eigenspace (σF : End 𝕜 F) 1 ⧸ (T.restrictEigenspace hT 1).range) *
        finrank 𝕜 (eigenspace (σF : End 𝕜 F) (-1) ⧸ (T.restrictEigenspace hT (-1)).range)))))

/-- `ContinuousLinearMap.detLineEigenspaceEquiv` is the transport along the splitting, followed by
the direct sum isomorphism and the sign `(-1) ^ (dim coker T₊ * dim coker T₋)`. -/
theorem detLineEigenspaceEquiv_def :
    detLineEigenspaceEquiv T hσE hσF hT =
      ((T : E →ₗ[𝕜] F).detLineCongr (equivEigenspaceProd σE hσE).toLinearEquiv
          (equivEigenspaceProd σF hσF).toLinearEquiv
          (prodMap_comp_equivEigenspaceProd T hσE hσF hT)).trans
        ((LinearMap.detLineProdMapEquiv _ _).trans (LinearEquiv.smulOfUnit
          ((-1 : 𝕜ˣ) ^
            (finrank 𝕜 (eigenspace (σF : End 𝕜 F) 1 ⧸ (T.restrictEigenspace hT 1).range) *
              finrank 𝕜 (eigenspace (σF : End 𝕜 F) (-1) ⧸
                (T.restrictEigenspace hT (-1)).range))))) :=
  (rfl)

/-- The inverse of `ContinuousLinearMap.detLineEigenspaceEquiv` on pure tensors: the normalized
direct sum of `v` and `v'`, transported back along the splitting. -/
theorem detLineEigenspaceEquiv_symm_tmul
    (v : (T.restrictEigenspace hT 1 : eigenspace (σE : End 𝕜 E) 1 →ₗ[𝕜]
      eigenspace (σF : End 𝕜 F) 1).detLine)
    (v' : (T.restrictEigenspace hT (-1) : eigenspace (σE : End 𝕜 E) (-1) →ₗ[𝕜]
      eigenspace (σF : End 𝕜 F) (-1)).detLine) :
    (detLineEigenspaceEquiv T hσE hσF hT).symm (v ⊗ₜ v') =
      ((T : E →ₗ[𝕜] F).detLineCongr (equivEigenspaceProd σE hσE).toLinearEquiv
          (equivEigenspaceProd σF hσF).toLinearEquiv
          (prodMap_comp_equivEigenspaceProd T hσE hσF hT)).symm
        ((-1 : 𝕜) ^ (finrank 𝕜 (eigenspace (σF : End 𝕜 F) 1 ⧸ (T.restrictEigenspace hT 1).range) *
            finrank 𝕜 (eigenspace (σF : End 𝕜 F) (-1) ⧸ (T.restrictEigenspace hT (-1)).range)) •
          (LinearMap.detLineProdMapEquiv (T.restrictEigenspace hT 1 :
            eigenspace (σE : End 𝕜 E) 1 →ₗ[𝕜] eigenspace (σF : End 𝕜 F) 1)
            (T.restrictEigenspace hT (-1) :
              eigenspace (σE : End 𝕜 E) (-1) →ₗ[𝕜] eigenspace (σF : End 𝕜 F) (-1))).symm
            (v ⊗ₜ v')) := by
  rw [LinearEquiv.symm_apply_eq, detLineEigenspaceEquiv_def]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.map_smul,
    LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv_apply, Units.smul_def, smul_smul]
  -- The two signs `(-1) ^ (dim coker T₊ * dim coker T₋)` cancel.
  simp [← mul_pow]

/-- Read along the splitting by the involutions (`LinearMap.detLineCongr` along
`ContinuousLinearMap.equivEigenspaceProd`), the element of `det T` corresponding to `v ⊗ v'` is
the normalized direct sum `(-1) ^ (dim coker T₊ * dim coker T₋) • (v ⊕ v')` in the determinant line
of the direct sum `T₊ ⊕ T₋`. -/
theorem detLineCongr_detLineEigenspaceEquiv_symm_tmul
    (v : (T.restrictEigenspace hT 1 : eigenspace (σE : End 𝕜 E) 1 →ₗ[𝕜]
      eigenspace (σF : End 𝕜 F) 1).detLine)
    (v' : (T.restrictEigenspace hT (-1) : eigenspace (σE : End 𝕜 E) (-1) →ₗ[𝕜]
      eigenspace (σF : End 𝕜 F) (-1)).detLine) :
    (T : E →ₗ[𝕜] F).detLineCongr (equivEigenspaceProd σE hσE).toLinearEquiv
        (equivEigenspaceProd σF hσF).toLinearEquiv (prodMap_comp_equivEigenspaceProd T hσE hσF hT)
        ((detLineEigenspaceEquiv T hσE hσF hT).symm (v ⊗ₜ v')) =
      (-1 : 𝕜) ^ (finrank 𝕜 (eigenspace (σF : End 𝕜 F) 1 ⧸ (T.restrictEigenspace hT 1).range) *
          finrank 𝕜 (eigenspace (σF : End 𝕜 F) (-1) ⧸ (T.restrictEigenspace hT (-1)).range)) •
        (LinearMap.detLineProdMapEquiv (T.restrictEigenspace hT 1 :
          eigenspace (σE : End 𝕜 E) 1 →ₗ[𝕜] eigenspace (σF : End 𝕜 F) 1)
          (T.restrictEigenspace hT (-1) :
            eigenspace (σE : End 𝕜 E) (-1) →ₗ[𝕜] eigenspace (σF : End 𝕜 F) (-1))).symm
          (v ⊗ₜ v') := by
  rw [detLineEigenspaceEquiv_symm_tmul, LinearEquiv.apply_symm_apply]

/-- **Bijective operators.** If `T` is bijective, so are its restrictions `T₊` and `T₋`
(`ContinuousLinearMap.restrictEigenspace_bijective`), and reading the element of `det T`
corresponding to `v ⊗ v'` in the trivialization given by bijectivity
(`LinearMap.detLineEquivOfBijective`) gives the product of the readings of `v` and `v'`. So the
orientation given by bijectivity splits as the orientations given by bijectivity. -/
theorem detLineEquivOfBijective_detLineEigenspaceEquiv_symm_tmul (hb : Function.Bijective T)
    (v : (T.restrictEigenspace hT 1 : eigenspace (σE : End 𝕜 E) 1 →ₗ[𝕜]
      eigenspace (σF : End 𝕜 F) 1).detLine)
    (v' : (T.restrictEigenspace hT (-1) : eigenspace (σE : End 𝕜 E) (-1) →ₗ[𝕜]
      eigenspace (σF : End 𝕜 F) (-1)).detLine) :
    (T : E →ₗ[𝕜] F).detLineEquivOfBijective hb ((detLineEigenspaceEquiv T hσE hσF hT).symm
        (v ⊗ₜ v')) =
      (T.restrictEigenspace hT 1 : eigenspace (σE : End 𝕜 E) 1 →ₗ[𝕜]
          eigenspace (σF : End 𝕜 F) 1).detLineEquivOfBijective
          (restrictEigenspace_bijective hb hT 1) v *
        (T.restrictEigenspace hT (-1) : eigenspace (σE : End 𝕜 E) (-1) →ₗ[𝕜]
          eigenspace (σF : End 𝕜 F) (-1)).detLineEquivOfBijective
          (restrictEigenspace_bijective hb hT (-1)) v' := by
  have hc : finrank 𝕜 (eigenspace (σF : End 𝕜 F) 1 ⧸ (T.restrictEigenspace hT 1).range) = 0 :=
    LinearMap.finrank_quotient_range_eq_zero_of_surjective (restrictEigenspace_bijective hb hT 1).2
  rw [detLineEigenspaceEquiv_symm_tmul, show (-1 : 𝕜) ^ (finrank 𝕜 (eigenspace (σF : End 𝕜 F) 1 ⧸
      (T.restrictEigenspace hT 1).range) * finrank 𝕜 (eigenspace (σF : End 𝕜 F) (-1) ⧸
        (T.restrictEigenspace hT (-1)).range)) = 1 by simp [hc], one_smul,
    LinearMap.detLineCongr_symm, LinearMap.detLineCongr_eq_detLineCongrKerCoker,
    LinearMap.detLineEquivOfBijective_detLineCongrKerCoker
      ((restrictEigenspace_bijective hb hT 1).prodMap (restrictEigenspace_bijective hb hT (-1))),
    LinearMap.detLineEquivOfBijective_detLineProdMapEquiv_symm_tmul]

end Splitting

end ContinuousLinearMap

namespace TauCeti

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {σE : E →L[ℝ] E} {σF : F →L[ℝ] F}
  {T : ℝ → E →L[ℝ] F} {a b : ℝ}

omit [CompleteSpace E] [CompleteSpace F] in
/-- The ray form of `ContinuousLinearMap.detLineCongr_detLineEigenspaceEquiv_symm_tmul`, with the
direct sum `T₊ ⊕ T₋` written as a continuous linear map, as orientation transport along the direct
sum (`TauCeti.detLineOrientationTransport_prodMap`) states it. -/
private theorem ray_map_detLineCongr_detLineEigenspaceEquiv_symm_tmul (T : E →L[ℝ] F)
    (hσE : Function.Involutive σE) (hσF : Function.Involutive σF) (hT : T.comp σE = σF.comp T)
    [FiniteDimensional ℝ (T.restrictEigenspace hT 1).ker]
    [FiniteDimensional ℝ (T.restrictEigenspace hT (-1)).ker]
    [FiniteDimensional ℝ (eigenspace (σF : End ℝ F) 1 ⧸ (T.restrictEigenspace hT 1).range)]
    [FiniteDimensional ℝ (eigenspace (σF : End ℝ F) (-1) ⧸ (T.restrictEigenspace hT (-1)).range)]
    {v : (T.restrictEigenspace hT 1 : eigenspace (σE : End ℝ E) 1 →ₗ[ℝ]
      eigenspace (σF : End ℝ F) 1).detLine}
    {v' : (T.restrictEigenspace hT (-1) : eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ]
      eigenspace (σF : End ℝ F) (-1)).detLine} (hv : v ≠ 0) (hv' : v' ≠ 0) :
    Module.Ray.map ((T : E →ₗ[ℝ] F).detLineCongr (g := ((T.restrictEigenspace hT 1).prodMap
        (T.restrictEigenspace hT (-1)) :
          eigenspace (σE : End ℝ E) 1 × eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ]
            eigenspace (σF : End ℝ F) 1 × eigenspace (σF : End ℝ F) (-1)))
        (equivEigenspaceProd σE hσE).toLinearEquiv (equivEigenspaceProd σF hσF).toLinearEquiv
        (prodMap_comp_equivEigenspaceProd T hσE hσF hT))
      (rayOfNeZero ℝ ((detLineEigenspaceEquiv T hσE hσF hT).symm (v ⊗ₜ v'))
        ((LinearEquiv.map_ne_zero_iff _).2 (tmul_ne_zero hv hv'))) =
      rayOfNeZero ℝ ((-1 : ℝ) ^
          (finrank ℝ (eigenspace (σF : End ℝ F) 1 ⧸ (T.restrictEigenspace hT 1).range) *
            finrank ℝ (eigenspace (σF : End ℝ F) (-1) ⧸ (T.restrictEigenspace hT (-1)).range)) •
        (LinearMap.detLineProdMapEquiv (T.restrictEigenspace hT 1 :
          eigenspace (σE : End ℝ E) 1 →ₗ[ℝ] eigenspace (σF : End ℝ F) 1)
          (T.restrictEigenspace hT (-1) :
            eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ] eigenspace (σF : End ℝ F) (-1))).symm
          (v ⊗ₜ v') :
        ((T.restrictEigenspace hT 1).prodMap (T.restrictEigenspace hT (-1)) :
          eigenspace (σE : End ℝ E) 1 × eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ]
            eigenspace (σF : End ℝ F) 1 × eigenspace (σF : End ℝ F) (-1)).detLine)
        (LinearMap.neg_one_pow_smul_detLineProdMapEquiv_symm_tmul_ne_zero
          (T.restrictEigenspace hT 1 :
            eigenspace (σE : End ℝ E) 1 →ₗ[ℝ] eigenspace (σF : End ℝ F) 1)
          (T.restrictEigenspace hT (-1) :
            eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ] eigenspace (σF : End ℝ F) (-1)) _ hv hv') := by
  rw [Module.Ray.map_apply]
  -- `ContinuousLinearMap.coe_prodMap` holds by `rfl`: the transport along the splitting with target
  -- the coerced direct sum of continuous linear maps, as in `TauCeti.detLineOrientationTransport`,
  -- is the one of `ContinuousLinearMap.detLineCongr_detLineEigenspaceEquiv_symm_tmul`.
  exact (ray_eq_iff _ _).2 (detLineCongr_detLineEigenspaceEquiv_symm_tmul T hσE hσF hT v v' ▸ .rfl)

/-- **Orientation transport commutes with the splitting by involutions.** Let `T` be a path of
operators intertwining the involutions `σE` and `σF`, continuous and Fredholm between `a` and `b`,
and let the orientations of `v₀` and `v₀'` be transported along its restrictions `T₊` and `T₋` to
the `1`- and `-1`-eigenspaces to those of `u` and `u'`. Then along `T` the orientation of the
element of `det T a` corresponding to `v₀ ⊗ v₀'` is transported to that of the element of
`det T b` corresponding to `u ⊗ u'` (`ContinuousLinearMap.detLineEigenspaceEquiv`). -/
theorem detLineOrientationTransport_detLineEigenspaceEquiv_symm (hσE : Function.Involutive σE)
    (hσF : Function.Involutive σF) (hTσ : ∀ t, (T t).comp σE = σF.comp (T t))
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    [FiniteDimensional ℝ ((T a).restrictEigenspace (hTσ a) 1).ker]
    [FiniteDimensional ℝ ((T a).restrictEigenspace (hTσ a) (-1)).ker]
    [FiniteDimensional ℝ
      (eigenspace (σF : End ℝ F) 1 ⧸ ((T a).restrictEigenspace (hTσ a) 1).range)]
    [FiniteDimensional ℝ
      (eigenspace (σF : End ℝ F) (-1) ⧸ ((T a).restrictEigenspace (hTσ a) (-1)).range)]
    [FiniteDimensional ℝ ((T b).restrictEigenspace (hTσ b) 1).ker]
    [FiniteDimensional ℝ ((T b).restrictEigenspace (hTσ b) (-1)).ker]
    [FiniteDimensional ℝ
      (eigenspace (σF : End ℝ F) 1 ⧸ ((T b).restrictEigenspace (hTσ b) 1).range)]
    [FiniteDimensional ℝ
      (eigenspace (σF : End ℝ F) (-1) ⧸ ((T b).restrictEigenspace (hTσ b) (-1)).range)]
    {v₀ : ((T a).restrictEigenspace (hTσ a) 1 : eigenspace (σE : End ℝ E) 1 →ₗ[ℝ]
      eigenspace (σF : End ℝ F) 1).detLine}
    {v₀' : ((T a).restrictEigenspace (hTσ a) (-1) : eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ]
      eigenspace (σF : End ℝ F) (-1)).detLine}
    {u : ((T b).restrictEigenspace (hTσ b) 1 : eigenspace (σE : End ℝ E) 1 →ₗ[ℝ]
      eigenspace (σF : End ℝ F) 1).detLine}
    {u' : ((T b).restrictEigenspace (hTσ b) (-1) : eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ]
      eigenspace (σF : End ℝ F) (-1)).detLine}
    (hv₀ : v₀ ≠ 0) (hv₀' : v₀' ≠ 0) (hu : u ≠ 0) (hu' : u' ≠ 0)
    (htr : detLineOrientationTransport a b (hT.restrictEigenspace hTσ 1)
      (fun t ht ↦ ((isFredholm_iff_isFredholm_restrictEigenspace_one_and_neg_one (T t) hσE hσF
        (hTσ t)).1 (hF t ht)).1) (rayOfNeZero ℝ v₀ hv₀) = rayOfNeZero ℝ u hu)
    (htr' : detLineOrientationTransport a b (hT.restrictEigenspace hTσ (-1))
      (fun t ht ↦ ((isFredholm_iff_isFredholm_restrictEigenspace_one_and_neg_one (T t) hσE hσF
        (hTσ t)).1 (hF t ht)).2) (rayOfNeZero ℝ v₀' hv₀') = rayOfNeZero ℝ u' hu') :
    detLineOrientationTransport a b hT hF
        (rayOfNeZero ℝ ((detLineEigenspaceEquiv (T a) hσE hσF (hTσ a)).symm (v₀ ⊗ₜ v₀'))
          ((LinearEquiv.map_ne_zero_iff _).2 (tmul_ne_zero hv₀ hv₀'))) =
      rayOfNeZero ℝ ((detLineEigenspaceEquiv (T b) hσE hσF (hTσ b)).symm (u ⊗ₜ u'))
        ((LinearEquiv.map_ne_zero_iff _).2 (tmul_ne_zero hu hu')) := by
  have hFp (t : ℝ) (ht : t ∈ uIcc a b) :=
    ((isFredholm_iff_isFredholm_restrictEigenspace_one_and_neg_one (T t) hσE hσF
      (hTσ t)).1 (hF t ht)).1
  have hFm (t : ℝ) (ht : t ∈ uIcc a b) :=
    ((isFredholm_iff_isFredholm_restrictEigenspace_one_and_neg_one (T t) hσE hσF
      (hTσ t)).1 (hF t ht)).2
  -- Orientation transport along the direct sum of the restrictions splits.
  have hsum := detLineOrientationTransport_prodMap (hT.restrictEigenspace hTσ 1)
    (hT.restrictEigenspace hTσ (-1)) hFp hFm hv₀ hv₀' hu hu' htr htr'
  -- The constant splitting by the involutions conjugates `T` to that direct sum.
  have hnat := detLineOrientationTransport_map_detLineCongr (T := T)
    (S := fun t ↦ ((T t).restrictEigenspace (hTσ t) 1).prodMap
      ((T t).restrictEigenspace (hTσ t) (-1)))
    (e₁ := fun _ ↦ equivEigenspaceProd σE hσE) (e₂ := fun _ ↦ equivEigenspaceProd σF hσF) hT hF
    ((hT.restrictEigenspace hTσ 1).prod_mapL ℝ (hT.restrictEigenspace hTσ (-1)))
    (fun t ht ↦ (hFp t ht).prodMap (hFm t ht)) continuousOn_const continuousOn_const
    (fun t ↦ prodMap_comp_equivEigenspaceProd (T t) hσE hσF (hTσ t))
    (rayOfNeZero ℝ ((detLineEigenspaceEquiv (T a) hσE hσF (hTσ a)).symm (v₀ ⊗ₜ v₀'))
      ((LinearEquiv.map_ne_zero_iff _).2 (tmul_ne_zero hv₀ hv₀')))
  -- Read along the splitting, the orientations at `a` and `b` are normalized direct sums.
  rw [ray_map_detLineCongr_detLineEigenspaceEquiv_symm_tmul (T a) hσE hσF (hTσ a) hv₀ hv₀'] at hnat
  exact (Module.Ray.map _).injective (hnat.symm.trans (hsum.trans
    (ray_map_detLineCongr_detLineEigenspaceEquiv_symm_tmul (T b) hσE hσF (hTσ b) hu hu').symm))

/-- **Transported signs multiply.** In the situation of
`TauCeti.detLineOrientationTransport_detLineEigenspaceEquiv_symm`, let `T b` be bijective. Every
element `x` of the determinant line of `T b` in the orientation transported along `T` from the
split orientation of `v₀ ⊗ v₀'` reads, in the trivialization given by bijectivity
(`LinearMap.detLineEquivOfBijective`), with the product of the signs of the readings of `u` and
`u'`, in the orientations transported along the restrictions `T₊` and `T₋`. -/
theorem sign_detLineEquivOfBijective_eq_mul_of_detLineOrientationTransport
    (hσE : Function.Involutive σE) (hσF : Function.Involutive σF)
    (hTσ : ∀ t, (T t).comp σE = σF.comp (T t)) (hT : ContinuousOn T (uIcc a b))
    (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    [FiniteDimensional ℝ ((T a).restrictEigenspace (hTσ a) 1).ker]
    [FiniteDimensional ℝ ((T a).restrictEigenspace (hTσ a) (-1)).ker]
    [FiniteDimensional ℝ
      (eigenspace (σF : End ℝ F) 1 ⧸ ((T a).restrictEigenspace (hTσ a) 1).range)]
    [FiniteDimensional ℝ
      (eigenspace (σF : End ℝ F) (-1) ⧸ ((T a).restrictEigenspace (hTσ a) (-1)).range)]
    [FiniteDimensional ℝ ((T b).restrictEigenspace (hTσ b) 1).ker]
    [FiniteDimensional ℝ ((T b).restrictEigenspace (hTσ b) (-1)).ker]
    [FiniteDimensional ℝ
      (eigenspace (σF : End ℝ F) 1 ⧸ ((T b).restrictEigenspace (hTσ b) 1).range)]
    [FiniteDimensional ℝ
      (eigenspace (σF : End ℝ F) (-1) ⧸ ((T b).restrictEigenspace (hTσ b) (-1)).range)]
    {v₀ : ((T a).restrictEigenspace (hTσ a) 1 : eigenspace (σE : End ℝ E) 1 →ₗ[ℝ]
      eigenspace (σF : End ℝ F) 1).detLine}
    {v₀' : ((T a).restrictEigenspace (hTσ a) (-1) : eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ]
      eigenspace (σF : End ℝ F) (-1)).detLine}
    {u : ((T b).restrictEigenspace (hTσ b) 1 : eigenspace (σE : End ℝ E) 1 →ₗ[ℝ]
      eigenspace (σF : End ℝ F) 1).detLine}
    {u' : ((T b).restrictEigenspace (hTσ b) (-1) : eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ]
      eigenspace (σF : End ℝ F) (-1)).detLine}
    (hv₀ : v₀ ≠ 0) (hv₀' : v₀' ≠ 0) (hu : u ≠ 0) (hu' : u' ≠ 0)
    (htr : detLineOrientationTransport a b (hT.restrictEigenspace hTσ 1)
      (fun t ht ↦ ((isFredholm_iff_isFredholm_restrictEigenspace_one_and_neg_one (T t) hσE hσF
        (hTσ t)).1 (hF t ht)).1) (rayOfNeZero ℝ v₀ hv₀) = rayOfNeZero ℝ u hu)
    (htr' : detLineOrientationTransport a b (hT.restrictEigenspace hTσ (-1))
      (fun t ht ↦ ((isFredholm_iff_isFredholm_restrictEigenspace_one_and_neg_one (T t) hσE hσF
        (hTσ t)).1 (hF t ht)).2) (rayOfNeZero ℝ v₀' hv₀') = rayOfNeZero ℝ u' hu')
    (hb : Function.Bijective (T b)) {x : (T b : E →ₗ[ℝ] F).detLine} (hx : x ≠ 0)
    (hxo : rayOfNeZero ℝ x hx = detLineOrientationTransport a b hT hF
      (rayOfNeZero ℝ ((detLineEigenspaceEquiv (T a) hσE hσF (hTσ a)).symm (v₀ ⊗ₜ v₀'))
        ((LinearEquiv.map_ne_zero_iff _).2 (tmul_ne_zero hv₀ hv₀')))) :
    SignType.sign ((T b : E →ₗ[ℝ] F).detLineEquivOfBijective hb x) =
      SignType.sign (((T b).restrictEigenspace (hTσ b) 1 : eigenspace (σE : End ℝ E) 1 →ₗ[ℝ]
          eigenspace (σF : End ℝ F) 1).detLineEquivOfBijective
          (restrictEigenspace_bijective hb (hTσ b) 1) u) *
        SignType.sign (((T b).restrictEigenspace (hTσ b) (-1) :
          eigenspace (σE : End ℝ E) (-1) →ₗ[ℝ]
            eigenspace (σF : End ℝ F) (-1)).detLineEquivOfBijective
          (restrictEigenspace_bijective hb (hTσ b) (-1)) u') := by
  rw [detLineOrientationTransport_detLineEigenspaceEquiv_symm hσE hσF hTσ hT hF hv₀ hv₀' hu hu' htr
    htr', ray_eq_iff] at hxo
  obtain ⟨r, hr, hrx⟩ := SameRay.exists_pos_left (R := ℝ) (M := (T b : E →ₗ[ℝ] F).detLine) hxo hx
    ((LinearEquiv.map_ne_zero_iff (detLineEigenspaceEquiv (T b) hσE hσF (hTσ b)).symm).2
      (tmul_ne_zero hu hu'))
  rw [← eq_inv_smul_iff₀ hr.ne'] at hrx
  rw [hrx, LinearEquiv.map_smul, detLineEquivOfBijective_detLineEigenspaceEquiv_symm_tmul,
    smul_eq_mul, sign_mul, sign_mul, sign_pos (inv_pos.2 hr), one_mul]


end TauCeti
