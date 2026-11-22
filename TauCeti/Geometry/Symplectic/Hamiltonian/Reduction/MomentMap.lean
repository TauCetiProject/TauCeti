/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction

/-!
# Moment maps of symmetries descend to reduced spaces

Symplectic reduction produces a manifold `Z` with smooth maps `i : Z → M` into a manifold with a
two-form `σ` and `p : Z → Q` onto a manifold with a two-form `η`, such that `p^* η = i^* σ`. For
Marsden–Weinstein–Meyer reduction, `Z = μ⁻¹(c)` is a regular level of a moment map of a group `G`,
`i` its inclusion, `p : Z → Z / G_c` the orbit projection and `η` the reduced symplectic form
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`).

A second symmetry of `(M, σ)` which commutes with the reduction acts on the reduced space
(`TauCeti.SmoothForm.exists_comp_eq_and_mpullback_eq_of_smul`). This file shows that its moment map
descends too. Let `ν : M → 𝔤*` be a moment map of an infinitesimal action `a : ξ ↦ ξ_M` for `σ`,
and let `b : ξ ↦ ξ_Q` be an infinitesimal action on `Q` related to `a` through `Z`: for each `ξ`
and `z`, some tangent vector `Y` of `Z` at `z` satisfies `di Y = ξ_M(i z)` and `dp Y = ξ_Q(p z)`.
If `ν ∘ i = ν' ∘ p` and `p` is surjective with surjective differentials, then

`ι_{ξ_Q} η = d⟨ν', ξ⟩`

on `Q`, that is, `ν'` is a moment map of `b` for `η`
(`TauCeti.SmoothTwoForm.IsMomentMap.of_mpullback_eq`): both sides evaluate on `dp v` to
`σ(ξ_M(i z), di v) = d⟨ν ∘ i, ξ⟩(v)`. The **moment cocycle** `σ(ξ_M, ζ_M) - ν_{⁅ξ, ζ⁆}` of `ν`
descends in the same way (`TauCeti.SmoothTwoForm.momentCocycle_eq_of_mpullback_eq`), so the
reduced moment map is infinitesimally equivariant wherever `ν` is along `i`.

When `p` is a surjective submersion out of a boundaryless manifold, the smoothness of `ν'` is
automatic, and a moment map `ν` with `ν ∘ i` constant on the fibres of `p` determines a unique
reduced moment map `ν'` with `ν' ∘ p = ν ∘ i`
(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_comp_eq_and_isMomentMap`).

For a Lie group `L` acting smoothly on `M`, `Z` and `Q`, with `i` and `p` equivariant, the
fundamental vector fields of `Z` supply the lifts, and coadjoint equivariance descends as well:
a group-level moment map `ν` of the action on `(M, σ)` with `ν ∘ i = ν' ∘ p` makes `ν'` a
group-level moment map of the action on `(Q, η)`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.of_mpullback_eq`). If the fibres of `p` are the
orbits of an action of a group `K` on `Z`, as for the stabilizer `K = G_c` acting on a level, it
suffices that `ν ∘ i` is `K`-invariant
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_comp_eq_and_isEquivariantMomentMap`).
For the restriction to a level of an action of `L` on `M` commuting with that of `G` and preserving
`μ`, this holds when `ν` is invariant under `G_c`.

None of these statements needs `σ` or `η` to be closed or nondegenerate, nor `i` to be an
immersion.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.of_mpullback_eq`: moment maps descend along reduction data.
* `TauCeti.SmoothTwoForm.momentCocycle_eq_of_mpullback_eq`: the moment cocycle descends.
* `TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_comp_eq_and_isMomentMap`: a moment map whose
  restriction is constant on the fibres of a surjective submersion induces a unique reduced
  moment map.
* `TauCeti.SmoothTwoForm.IsMomentMap.differential_mfderiv_eq_of_comp_eq`: the differential of a
  reduced moment map.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.of_mpullback_eq`: group-level moment maps descend
  along equivariant reduction data.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_comp_eq_and_isEquivariantMomentMap`:
  the reduced group-level moment map of a symmetry commuting with the reduction.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* J.-P. Ortega, T. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics 222,
  Birkhäuser, 2004, Section 6.1 (residual symmetries of reduced spaces).
-/

public section

noncomputable section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M E' H' Q E₀ H₀ Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace Z] [ChartedSpace H₀ Z] [IsManifold I₀ ∞ Z]
  {σ : SmoothTwoForm I M} {η : SmoothTwoForm J Q} {i : Z → M} {p : Z → Q}

/-! ### Moment maps of infinitesimal actions -/

section Infinitesimal

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] {a : InfinitesimalAction 𝔤 I M}
  {b : InfinitesimalAction 𝔤 J Q} {ν : M → Module.Dual ℝ 𝔤} {ν' : Q → Module.Dual ℝ 𝔤}

/-- **The moment cocycle descends.** Let `p^* η = i^* σ`, and let the infinitesimal actions `a`
on `M` and `b` on `Q` be related at `z`: each `ξ_M(i z)` and `ξ_Q(p z)` are the images under `di`
and `dp` of one tangent vector of `Z`. If `ν (i z) = ν' (p z)`, the cocycles
`σ(ξ_M, ζ_M) - ν_{⁅ξ, ζ⁆}` of `ν` at `i z` and of `ν'` at `p z` agree. -/
theorem momentCocycle_eq_of_mpullback_eq (hi : ContMDiff I₀ I ∞ i) (hp : ContMDiff I₀ J ∞ p)
    (hpi : SmoothForm.mpullback p hp η = SmoothForm.mpullback i hi σ) {z : Z}
    (hlift : ∀ ξ, ∃ Y : TangentSpace I₀ z,
      mfderiv I₀ I i z Y = a ξ (i z) ∧ mfderiv I₀ J p z Y = b ξ (p z))
    (hνν' : ν (i z) = ν' (p z)) :
    η.momentCocycle b ν' (p z) = σ.momentCocycle a ν (i z) := by
  refine DFunLike.ext _ _ fun ξ ↦ LinearMap.ext fun ζ ↦ ?_
  obtain ⟨Y, hiY, hpY⟩ := hlift ξ
  obtain ⟨Y', hiY', hpY'⟩ := hlift ζ
  -- `η(ξ_Q, ζ_Q) = η(dp Y, dp Y') = (p^* η)(Y, Y') = (i^* σ)(Y, Y') = σ(ξ_M, ζ_M)`.
  rw [momentCocycle_apply, momentCocycle_apply, ← hpY, ← hpY', ← SmoothForm.eval₂_mpullback p hp,
    hpi, SmoothForm.eval₂_mpullback, hiY, hiY', hνν']

namespace IsMomentMap

/-- **Moment maps descend to reduced spaces.** Let `p^* η = i^* σ`, where `p` is surjective with
surjective differentials, and let `ν` be a moment map of an infinitesimal action `a` on `M`. Let
`b` be an infinitesimal action on `Q` related to `a` through `Z`: for every `ξ` and `z`, some
tangent vector `Y` of `Z` at `z` has `di Y = ξ_M(i z)` and `dp Y = ξ_Q(p z)`. Then every map
`ν' : Q → 𝔤*` with smooth components and `ν ∘ i = ν' ∘ p` is a moment map of `b` for `η`. -/
theorem of_mpullback_eq (hν : σ.IsMomentMap a ν) (hi : ContMDiff I₀ I ∞ i)
    (hp : ContMDiff I₀ J ∞ p) (hpi : SmoothForm.mpullback p hp η = SmoothForm.mpullback i hi σ)
    (hsurj : Surjective p) (hdp : ∀ z, Surjective (mfderiv I₀ J p z))
    (hlift : ∀ ξ z, ∃ Y : TangentSpace I₀ z,
      mfderiv I₀ I i z Y = a ξ (i z) ∧ mfderiv I₀ J p z Y = b ξ (p z))
    (hν' : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun q ↦ ν' q ξ) (hνν' : ν ∘ i = ν' ∘ p) :
    η.IsMomentMap b ν' where
  contMDiff := hν'
  isHamiltonianVectorField ξ := isHamiltonianVectorField_iff.2 fun q w ↦ by
    obtain ⟨z, rfl⟩ := hsurj q
    obtain ⟨v, rfl⟩ := hdp z w
    obtain ⟨Y, hiY, hpY⟩ := hlift ξ z
    have hcomp : (fun x ↦ ν x ξ) ∘ i = (fun q ↦ ν' q ξ) ∘ p :=
      funext fun z ↦ congrArg (· ξ) (congrFun hνν' z)
    rw [← hpY]
    exact eval₂_mfderiv_eq_mvfderiv_of_mpullback_eq hi hp hpi (hν.isHamiltonianVectorField ξ) hcomp
      (hν.mdifferentiableAt ξ (i z)) ((hν' ξ).mdifferentiableAt (by simp)) hiY v

/-- **Moment maps descend along a surjective submersion.** Let `p^* η = i^* σ`, where `p` is a
surjective smooth submersion out of a boundaryless manifold, let `ν` be a moment map of an
infinitesimal action `a` on `M`, and let `b` be an infinitesimal action on `Q` related to `a`
through `Z`. Then every map `ν'` with `ν ∘ i = ν' ∘ p` is a moment map of `b` for `η`; its
smoothness is automatic. -/
theorem of_comp_eq [I₀.Boundaryless] (hν : σ.IsMomentMap a ν) (hi : ContMDiff I₀ I ∞ i)
    (hp : IsSubmersion I₀ J ∞ p)
    (hpi : SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi σ)
    (hsurj : Surjective p)
    (hlift : ∀ ξ z, ∃ Y : TangentSpace I₀ z,
      mfderiv I₀ I i z Y = a ξ (i z) ∧ mfderiv I₀ J p z Y = b ξ (p z))
    (hνν' : ν ∘ i = ν' ∘ p) :
    η.IsMomentMap b ν' := by
  refine hν.of_mpullback_eq hi hp.contMDiff hpi hsurj (fun z ↦ hp.surjective_mfderiv (by simp) z)
    hlift (fun ξ ↦ (hp.contMDiff_comp_iff hsurj le_rfl).1 ?_) hνν'
  -- The component `ν'_ξ ∘ p = ν_ξ ∘ i` is smooth, so `ν'_ξ` is smooth.
  have hcomp : (fun q ↦ ν' q ξ) ∘ p = (fun x ↦ ν x ξ) ∘ i :=
    funext fun z ↦ congrArg (· ξ) (congrFun hνν' z).symm
  rw [hcomp]
  exact (hν.contMDiff ξ).comp hi

omit [IsManifold I₀ ∞ Z] in
/-- **Differentials of related moment maps.** If `ν` and `ν'` are moment maps on `M` and on `Q`
with `ν' ∘ p = ν ∘ i`, then their differentials agree along `Z`:
`dν'_(p z) (dp v) = dν_(i z) (di v)` for every tangent vector `v` of `Z` at `z`. For the moment
map of a symmetry descended to a reduced space, this computes the differential of the reduced
moment map. -/
theorem differential_mfderiv_eq_of_comp_eq (hν : σ.IsMomentMap a ν) (hν' : η.IsMomentMap b ν')
    (hi : MDifferentiable I₀ I i) (hp : MDifferentiable I₀ J p) (hνν' : ν' ∘ p = ν ∘ i) (z : Z)
    (v : TangentSpace I₀ z) :
    hν'.differential (p z) (mfderiv I₀ J p z v) = hν.differential (i z) (mfderiv I₀ I i z v) := by
  ext ξ
  have hcomp : (fun q ↦ ν' q ξ) ∘ p = (fun x ↦ ν x ξ) ∘ i :=
    funext fun z ↦ congrArg (· ξ) (congrFun hνν' z)
  rw [differential_apply, differential_apply,
    ← mvfderiv_comp_apply z (hν'.mdifferentiableAt ξ (p z)) (hp z), hcomp,
    mvfderiv_comp_apply z (hν.mdifferentiableAt ξ (i z)) (hi z)]

/-- **The reduced moment map.** Let `p^* η = i^* σ`, where `p` is a surjective smooth submersion
out of a boundaryless manifold, let `ν` be a moment map of an infinitesimal action `a` on `M`, and
let `b` be an infinitesimal action on `Q` related to `a` through `Z`. If `ν ∘ i` is constant on the
fibres of `p`, there is a unique map `ν'` with `ν' ∘ p = ν ∘ i`, and it is a moment map of `b` for
`η`. -/
theorem existsUnique_comp_eq_and_isMomentMap [I₀.Boundaryless] (hν : σ.IsMomentMap a ν)
    (hi : ContMDiff I₀ I ∞ i) (hp : IsSubmersion I₀ J ∞ p)
    (hpi : SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi σ)
    (hsurj : Surjective p)
    (hlift : ∀ ξ z, ∃ Y : TangentSpace I₀ z,
      mfderiv I₀ I i z Y = a ξ (i z) ∧ mfderiv I₀ J p z Y = b ξ (p z))
    (hfib : FactorsThrough (ν ∘ i) p) :
    ∃! ν' : Q → Module.Dual ℝ 𝔤, ν' ∘ p = ν ∘ i ∧ η.IsMomentMap b ν' := by
  have hcomp : (ν ∘ i ∘ surjInv hsurj) ∘ p = ν ∘ i :=
    funext fun z ↦ hfib (surjInv_eq hsurj (p z))
  exact ⟨ν ∘ i ∘ surjInv hsurj, ⟨hcomp, hν.of_comp_eq hi hp hpi hsurj hlift hcomp.symm⟩,
    fun ν' hν' ↦ hsurj.injective_comp_right (hν'.1.trans hcomp.symm)⟩

end IsMomentMap

end Infinitesimal

/-! ### Group-level moment maps -/

section Group

variable {EL HL L : Type*} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [CompleteSpace EL]
  [TopologicalSpace HL] {IL : ModelWithCorners ℝ EL HL} [TopologicalSpace L] [ChartedSpace HL L]
  [Group L] [LieGroup IL (minSmoothness ℝ 3) L] [CompleteSpace E] [CompleteSpace E']
  [MulAction L M] [ContMDiffSMul IL I ∞ L M] [MulAction L Z] [ContMDiffSMul IL I₀ ∞ L Z]
  [MulAction L Q] [ContMDiffSMul IL J ∞ L Q]
  {ν : M → Module.Dual ℝ (GroupLieAlgebra IL L)} {ν' : Q → Module.Dual ℝ (GroupLieAlgebra IL L)}

omit [IsManifold I₀ ∞ Z] in
/-- The fundamental vector field of `Z` lifts those of `M` and `Q` along equivariant maps `i` and
`p`: it is sent to `ξ_M(i z)` by `di` and to `ξ_Q(p z)` by `dp`. -/
private theorem exists_mfderiv_eq_fundamental (hi : ContMDiff I₀ I ∞ i) (hp : ContMDiff I₀ J ∞ p)
    (hiL : ∀ (l : L) z, i (l • z) = l • i z) (hpL : ∀ (l : L) z, p (l • z) = l • p z)
    (ξ : GroupLieAlgebra IL L) (z : Z) :
    ∃ Y : TangentSpace I₀ z,
      mfderiv I₀ I i z Y = InfinitesimalAction.fundamental IL L I M ξ (i z) ∧
        mfderiv I₀ J p z Y = InfinitesimalAction.fundamental IL L J Q ξ (p z) := by
  have horbit : MDifferentiableAt IL I₀ (fun l : L ↦ l • z) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (I := IL) (I' := I₀) (n := ∞) z).mdifferentiableAt
      (by simp)
  refine ⟨fundamentalVectorField I₀ ξ z, ?_, ?_⟩ <;> rw [InfinitesimalAction.fundamental_apply]
  · exact mfderiv_fundamentalVectorField_of_map_smul ((hi z).mdifferentiableAt (by simp)) horbit
      (fun l ↦ hiL l z) ξ
  · exact mfderiv_fundamentalVectorField_of_map_smul ((hp z).mdifferentiableAt (by simp)) horbit
      (fun l ↦ hpL l z) ξ

namespace IsEquivariantMomentMap

/-- **Group-level moment maps descend to reduced spaces.** Let a Lie group `L` act smoothly on
`M`, `Z` and `Q`, with `i` and `p` equivariant, and let `p^* η = i^* σ`, where `p` is surjective
with surjective differentials. If `ν` is a group-level moment map of the action on `(M, σ)`, then
every map `ν'` with smooth components and `ν ∘ i = ν' ∘ p` is a group-level moment map of the action
on `(Q, η)`. -/
theorem of_mpullback_eq (hν : σ.IsEquivariantMomentMap ν) (hi : ContMDiff I₀ I ∞ i)
    (hp : ContMDiff I₀ J ∞ p) (hpi : SmoothForm.mpullback p hp η = SmoothForm.mpullback i hi σ)
    (hsurj : Surjective p) (hdp : ∀ z, Surjective (mfderiv I₀ J p z))
    (hiL : ∀ (l : L) z, i (l • z) = l • i z) (hpL : ∀ (l : L) z, p (l • z) = l • p z)
    (hν' : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun q ↦ ν' q ξ) (hνν' : ν ∘ i = ν' ∘ p) :
    η.IsEquivariantMomentMap ν' where
  toIsMomentMap := hν.toIsMomentMap.of_mpullback_eq hi hp hpi hsurj hdp
    (exists_mfderiv_eq_fundamental hi hp hiL hpL) hν' hνν'
  apply_smul l q := by
    obtain ⟨z, rfl⟩ := hsurj q
    have h (z : Z) : ν (i z) = ν' (p z) := congrFun hνν' z
    -- `ν'(l • p z) = ν'(p (l • z)) = ν(i (l • z)) = ν(l • i z) = Ad*_l ν(i z) = Ad*_l ν'(p z)`.
    rw [← hpL, ← h, hiL, hν.apply_smul, h]

/-- **The reduced group-level moment map of a commuting symmetry.** Let a Lie group `L` act
smoothly on `M`, `Z` and `Q`, with `i` and `p` equivariant, and let `p^* η = i^* σ`, where `p` is a
surjective smooth submersion out of a boundaryless manifold whose fibres are the orbits of an action
of a group `K` on `Z`. If `ν` is a group-level moment map of the action of `L` on `(M, σ)` and
`ν ∘ i` is `K`-invariant, there is a unique map `ν'` with `ν' ∘ p = ν ∘ i`, and it is a group-level
moment map of the action of `L` on `(Q, η)`.

For the restriction to a level `Z = μ⁻¹(c)` of a symmetry commuting with the action of `G` and
preserving `μ`, with `K = G_c` acting on `Z` by restriction and `p` the orbit projection, the
`K`-invariance of `ν ∘ i` holds when `ν` is invariant under `G_c`. -/
theorem existsUnique_comp_eq_and_isEquivariantMomentMap [I₀.Boundaryless] {K : Type*} [SMul K Z]
    (hν : σ.IsEquivariantMomentMap ν) (hi : ContMDiff I₀ I ∞ i) (hp : IsSubmersion I₀ J ∞ p)
    (hpi : SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi σ)
    (hsurj : Surjective p) (hiL : ∀ (l : L) z, i (l • z) = l • i z)
    (hpL : ∀ (l : L) z, p (l • z) = l • p z) (hfib : ∀ z z', p z = p z' → ∃ k : K, k • z = z')
    (hνK : ∀ (k : K) z, ν (i (k • z)) = ν (i z)) :
    ∃! ν' : Q → Module.Dual ℝ (GroupLieAlgebra IL L),
      ν' ∘ p = ν ∘ i ∧ η.IsEquivariantMomentMap ν' := by
  have hfib' : FactorsThrough (ν ∘ i) p := fun z z' hzz' ↦ by
    obtain ⟨k, rfl⟩ := hfib z z' hzz'
    exact (hνK k z).symm
  obtain ⟨ν', ⟨hcomp, hν'⟩, huniq⟩ :=
    hν.toIsMomentMap.existsUnique_comp_eq_and_isMomentMap hi hp hpi hsurj
      (exists_mfderiv_eq_fundamental hi hp.contMDiff hiL hpL) hfib'
  exact ⟨ν', ⟨hcomp, hν.of_mpullback_eq hi hp.contMDiff hpi hsurj
      (fun z ↦ hp.surjective_mfderiv (by simp) z) hiL hpL hν'.contMDiff hcomp.symm⟩,
    fun ν'' hν'' ↦ huniq ν'' ⟨hν''.1, hν''.2.toIsMomentMap⟩⟩

end IsEquivariantMomentMap

end Group

end SmoothTwoForm

end TauCeti
