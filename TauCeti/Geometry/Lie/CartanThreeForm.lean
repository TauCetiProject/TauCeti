/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.CartanThreeForm
public import TauCeti.Geometry.Lie.LeftInvariantForm
public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Manifold.DeRham.Integration.Homotopy
import TauCeti.Geometry.Lie.Adjoint.Compact
import TauCeti.Geometry.Lie.Interior

/-!
# Homomorphisms detected by the Cartan three-form

Let `φ : K → G` be a smooth homomorphism of finite-dimensional real Lie groups, with `K` compact
of dimension `n + 1`, and let `α` be an alternating `(n + 1)`-form on the Lie algebra `𝔤` of `G`
that is a Chevalley–Eilenberg cocycle with trivial coefficients. Its left-invariant extension
`α^L` is a closed form on `G` (`TauCeti.isClosed_leftInvariantSmoothForm_iff`), and `φ` pulls it
back to the left-invariant top form `(α ∘ dφ)^L` on `K`
(`TauCeti.mpullback_leftInvariantSmoothForm`). If `α ∘ dφ ≠ 0`, this top form vanishes nowhere,
so it orients `K` and has positive integral for that orientation
(`TauCeti.integralTopForm_leftInvariantForm_pos`). Integrals of pullbacks of closed forms only
depend on the homotopy class of the map, and vanish along constant maps, so `φ` is not
null-homotopic
(`ContMDiffMonoidMorphism.not_nullhomotopic_of_compContinuousLinearMap_ne_zero`).

The cocycle used to detect the third homotopy group of compact Lie groups is the Cartan
three-form `ω(X, Y, Z) = B(X, ⁅Y, Z⁆)` of a bilinear form `B` on `𝔤` invariant under the adjoint
action, such as the Killing form (`LinearMap.BilinMap.cartanThreeForm`). For a three-dimensional
compact `K` with `⁅y, z⁆ = x` in its Lie algebra, the pulled-back form takes the value
`B(dφ x, dφ x)` on `(x, y, z)`, since `dφ` preserves brackets. So `φ` is not null-homotopic as
soon as `B(dφ x, dφ x) ≠ 0`
(`ContMDiffMonoidMorphism.not_nullhomotopic_of_lie_eq_of_apply_ne_zero`). This is how a
homomorphism `SU(2) → G` attached to a root of a compact semisimple group `G` is shown to be a
map out of the three-sphere `SU(2)` that is not null-homotopic: on the basis `e₁, e₂, e₃` of
`𝔰𝔲(2)` with `⁅e₂, e₃⁆ = e₁`, the negative-definite Killing form of `G` takes a negative value at
`dφ e₁`.

When `G` is compact, its Lie algebra carries a positive-definite invariant form `B`
(`TauCeti.Lie.exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace`), and
`B(dφ x, dφ x) > 0` as soon as `dφ x ≠ 0`. So a smooth homomorphism out of a compact
three-dimensional Lie group whose Lie algebra is not abelian is not null-homotopic once its
differential is injective (`ContMDiffMonoidMorphism.not_nullhomotopic_of_injective_lieMap`): take
`x = ⁅y, z⁆ ≠ 0`. This applies to every homomorphism `SU(2) → G` with injective differential, for
instance to the inclusions of the two factors of `SU(2) × SU(2)`.

## Main results

* `ContMDiffMonoidMorphism.not_nullhomotopic_of_compContinuousLinearMap_ne_zero`: a smooth
  homomorphism out of a compact Lie group of positive dimension that pulls some Lie algebra
  cocycle of top degree back to a nonzero form is not null-homotopic.
* `ContMDiffMonoidMorphism.not_nullhomotopic_of_lie_eq_of_apply_ne_zero`: a smooth homomorphism
  out of a compact three-dimensional Lie group along which the Cartan three-form of an invariant
  form pulls back nonzero is not null-homotopic.
* `ContMDiffMonoidMorphism.not_nullhomotopic_of_injective_lieMap`: a smooth homomorphism with
  injective differential from a compact three-dimensional Lie group with non-abelian Lie algebra
  to a compact Lie group is not null-homotopic.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, proof of Proposition 6.31.
* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, §1.
* E. Meinrenken, *Lie groups and Lie algebras*, lecture notes, §§8 and 12.
-/

public section

noncomputable section

open LinearMap TauCeti TauCeti.LieModule.Cohomology
open scoped Manifold ContDiff

namespace ContMDiffMonoidMorphism

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup J ∞ K]
  [CompactSpace K] {n : ℕ}

/-- **Lie algebra cocycles detect homotopically nontrivial homomorphisms.** Let `φ : K → G` be a
smooth homomorphism of finite-dimensional real Lie groups, with `K` compact of dimension
`n + 1`. If a Chevalley–Eilenberg `(n + 1)`-cocycle `α` on the Lie algebra of `G`, with trivial
real coefficients, pulls back along the differential `dφ` at the identity to a nonzero form, then
`φ` is not null-homotopic. -/
theorem not_nullhomotopic_of_compContinuousLinearMap_ne_zero
    (φ : ContMDiffMonoidMorphism J I ∞ K G) (hk : Module.finrank ℝ F = n + 1)
    {α : GroupLieAlgebra I G [⋀^Fin (n + 1)]→L[ℝ] ℝ}
    (hα : trivialD ℝ (GroupLieAlgebra I G) ℝ (n + 1) α = 0)
    (hne : α.compContinuousLinearMap (φ.toMonoidHom.groupLieAlgebraMap J I) ≠ 0) :
    ¬(φ : C(K, G)).Nullhomotopic := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space K := J.t2Space_of_lieGroup ∞
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  refine not_nullhomotopic_of_integralTopForm_mpullback_ne_zero
    (Manifold.Orientation.ofTopForm hk _
      (isSmoothForm_leftInvariantForm (m := 0) (n := 1) (zero_add 1).le _)
      (leftInvariantForm_apply_ne_zero hne)) φ.contMDiff_toFun
    (φ := leftInvariantSmoothForm I G ℝ (n + 1) α) ?_ ?_
  · rw [mem_closedForms, leftInvariantSmoothForm_val, mextDeriv_leftInvariantForm_eq_zero_iff]
    exact hα
  · rw [ContinuousMap.coe_ofClass, leftInvariantSmoothForm_val,
      mpullback_leftInvariantForm φ (by simp)]
    exact (integralTopForm_leftInvariantForm_pos hk hne).ne'

/-- **The Cartan three-form detects homotopically nontrivial homomorphisms.** Let `φ : K → G` be a
smooth homomorphism of finite-dimensional real Lie groups, with `K` compact of dimension
`3`, and `B` a bilinear form on the Lie algebra of `G` invariant under the adjoint action. If
`⁅y, z⁆ = x` in the Lie algebra of `K` and `B(dφ x, dφ x) ≠ 0`, then `φ` is not null-homotopic: the
Cartan three-form `B(·, ⁅·, ·⁆)` pulls back along `dφ` to a form taking the value `B(dφ x, dφ x)`
on `(x, y, z)`. -/
theorem not_nullhomotopic_of_lie_eq_of_apply_ne_zero (φ : ContMDiffMonoidMorphism J I ∞ K G)
    (hk : Module.finrank ℝ F = 3) (B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G))
    (hB : ∀ x y z : GroupLieAlgebra I G, B ⁅x, y⁆ z = -B y ⁅x, z⁆)
    {x y z : GroupLieAlgebra J K} (hxyz : ⁅y, z⁆ = x)
    (hx : B (φ.toMonoidHom.groupLieAlgebraMap J I x)
      (φ.toMonoidHom.groupLieAlgebraMap J I x) ≠ 0) :
    ¬(φ : C(K, G)).Nullhomotopic := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  refine φ.not_nullhomotopic_of_compContinuousLinearMap_ne_zero hk
    (α := AlternatingMap.toContinuousAlternatingMap (B.cartanThreeForm hB))
    BilinMap.trivialD_cartanThreeForm fun h ↦ hx ?_
  -- Evaluate the pulled-back Cartan three-form on `(x, y, z)`: since `dφ` preserves brackets,
  -- it takes the value `B(dφ x, dφ ⁅y, z⁆) = B(dφ x, dφ x)` there.
  have hv := congrArg (fun f ↦ f ![x, y, z]) h
  simpa [Matrix.cons_val_zero, Matrix.cons_val_one, ← φ.groupLieAlgebraMap_lie, hxyz] using hv

/-- **Homomorphisms with injective differential out of a non-abelian three-dimensional compact Lie
group are detected by the Cartan three-form.** Let `φ : K → G` be a smooth homomorphism of compact
finite-dimensional real Lie groups, with `K` of dimension `3` and non-abelian Lie algebra. If the
differential `lieMap φ` is injective, then `φ` is not null-homotopic: for a positive-definite
invariant form `B` on the Lie algebra of `G` and `⁅y, z⁆ = x ≠ 0` in the Lie algebra of `K`, the
Cartan three-form of `B` pulls back to a form taking the value `B(dφ x, dφ x) > 0` on
`(x, y, z)`. -/
theorem not_nullhomotopic_of_injective_lieMap [FiniteDimensional ℝ F] [CompactSpace G]
    (φ : ContMDiffMonoidMorphism J I ∞ K G) (hk : Module.finrank ℝ F = 3)
    (hK : ¬IsLieAbelian (LeftInvariantDerivation J K)) (hφ : Function.Injective (lieMap φ)) :
    ¬(φ : C(K, G)).Nullhomotopic := by
  obtain ⟨B, hinv, -, hpos, -⟩ :=
    Lie.exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  obtain ⟨y, z, hyz⟩ : ∃ y z : LeftInvariantDerivation J K, ⁅y, z⁆ ≠ 0 := by
    by_contra! h
    exact hK ⟨fun y z ↦ h y z⟩
  -- The Lie algebras as tangent spaces at the identity, where the Cartan three-form lives.
  let eG := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)
  let eK := leftInvariantDerivationLieEquivGroupLieAlgebra (I := J) (G := K)
    (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)
  let B' : LinearMap.BilinForm ℝ (GroupLieAlgebra I G) :=
    B.compl₁₂ eG.symm.toLinearEquiv.toLinearMap eG.symm.toLinearEquiv.toLinearMap
  refine φ.not_nullhomotopic_of_lie_eq_of_apply_ne_zero hk B' (fun x y z ↦ ?_)
    (x := eK ⁅y, z⁆) (y := eK y) (z := eK z) (LieEquiv.map_lie _ _ _).symm ?_
  · simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv,
      LieEquiv.map_lie]
    exact hinv _ _ _
  · simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv,
      eG, eK, leftInvariantDerivationLieEquivGroupLieAlgebra_symm_groupLieAlgebraMap]
    exact (hpos _ ((map_ne_zero_iff _ hφ).mpr hyz)).ne'

end ContMDiffMonoidMorphism
