/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Manifold.Descent

import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The reduced symplectic form of a level of a moment map

Let `μ : M → 𝔤*` be a moment map, in the convention `ι_{Z_M} σ = d⟨μ, Z⟩`, for a symplectic form
`σ` on `M`, and let `c ∈ 𝔤*` with coadjoint stabilizer `𝔤_c = {Z | ⁅Z, c⁆ = 0}`. The
Marsden–Weinstein–Meyer theorem says that the restriction of `σ` to the level `μ⁻¹(c)` descends to
a symplectic form on the quotient of the level by the stabilizer `G_c`. This file proves the
descent for **level data** supplied as maps, independently of how the level and its quotient are
constructed:

* a manifold `Z` with a smooth map `i : Z → M` into the level, `μ ∘ i = c`, whose tangent images
  are the tangent spaces `ker dμ` of the level, and along which the cocycle
  `σ(Z_M, Z'_M) - μ_{⁅Z, Z'⁆}` of `μ` vanishes;
* a surjective smooth submersion `p : Z → Q` whose vertical tangent vectors are those sent by
  `di` into the stabilizer orbit directions `𝔤_c · i(z)`;
* an action of `K` on `Z` by smooth maps over `p`, transitive on the fibres of `p` and preserving
  `i^* σ`.

For the regular level `Z = μ⁻¹(c)` of a coadjoint-equivariant moment map of a Lie group `G` acting
by symplectomorphisms, with `G_c` acting freely and properly on `Z`, the inclusion `i`, the orbit
projection `p : Z → Z / G_c` and `K = G_c` are such data. The same data describe other smooth
pieces of levels with their tangent descriptions.

The form `i^* σ` is closed, and it is basic for `p`
(`TauCeti.SmoothTwoForm.IsMomentMap.isBasic_mpullback`): the vertical vectors of `p` are null
directions of `i^* σ`, because `σ(Z_M, u) = ⟨dμ u, Z⟩` vanishes for `u` tangent to the level, and
`K` compares the points of a fibre. Its null directions are exactly the vertical directions of `p`,
since the null directions of `σ` on `ker dμ` are `𝔤_c · i(z)`
(`TauCeti.SmoothTwoForm.IsMomentMap.ker_bilinFormAt_mpullback`). So its descent is the
**reduced symplectic form**: there is a unique symplectic form `ω_red` on
`Q` with `p^* ω_red = i^* σ`
(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`). Where the
action is locally free and `i` is an immersion, `Q` has dimension `dim M - dim 𝔤 - dim 𝔤_c`
(`TauCeti.SmoothTwoForm.IsMomentMap.finrank_add_finrank_add_finrank_lieAnnihilator`).

For a group-level moment map `μ` of a Lie group `G` acting by symplectomorphisms, the cocycle of
`μ` vanishes and `K` may act through any map `φ : K → G` with `i (k • z) = φ k • i z`, such as the
inclusion of the stabilizer `G_c`; invariance of `i^* σ` is then automatic
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`).

The reduced form computes the reduced Hamiltonian dynamics of
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction`, whose hypothesis is `p^* ω_red = i^* σ`.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.isBasic_mpullback`: `i^* σ` is basic for `p`.
* `TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`: the
  reduced symplectic form exists and is unique.
* `TauCeti.SmoothTwoForm.IsMomentMap.finrank_add_finrank_add_finrank_lieAnnihilator`: the
  reduced dimension `dim Q + dim 𝔤 + dim 𝔤_c = dim M`.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`:
  the reduced symplectic form of a group-level moment map.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* K. Meyer, *Symmetries and integrals in mechanics*, in *Dynamical Systems* (M. Peixoto, ed.),
  Academic Press, 1973, 259–273.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the proof of the Marsden–Weinstein–Meyer theorem).
-/

public section

noncomputable section

open Function Manifold Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {J : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold J ∞ Z]
  {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold JQ ∞ Q]
  {i : Z → M} {p : Z → Q} {c : Module.Dual ℝ 𝔤}

omit [FiniteDimensional ℝ E] [IsManifold JQ ∞ Q] in
/-- **The restricted form on a level is basic.** Let `i : Z → M` be a smooth map into a level of a
moment map `μ`, in the sense that its tangent images lie in `ker dμ`, and let `p : Z → Q` be a
differentiable map whose vertical tangent vectors are sent by `di` into the orbit directions
`𝔤 · i(z)`. If `K` acts on `Z` by smooth maps over `p`, transitively on the fibres of `p` and
preserving `i^* σ`, then `i^* σ` is basic for `p`. The vertical vectors are null directions of
`i^* σ` because `σ(Z_M, u) = ⟨dμ u, Z⟩` vanishes for `u` tangent to the level. -/
theorem isBasic_mpullback {K : Type*} [SMul K Z] (h : σ.IsMomentMap a μ) (hi : ContMDiff J I ∞ i)
    (hrange : ∀ z, LinearMap.range (mfderiv J I i z).toLinearMap ≤
      LinearMap.ker (h.differential (i z)))
    (hp : MDifferentiable J JQ p)
    (hker : ∀ z, (mfderiv J JQ p z).ker ≤
      (a.orbitTangent (i z)).comap (mfderiv J I i z).toLinearMap)
    (hK : ∀ k : K, ContMDiff J J ∞ fun z : Z ↦ k • z) (hpK : ∀ (k : K) z, p (k • z) = p z)
    (hfib : ∀ z z', p z = p z' → ∃ k : K, k • z = z')
    (hinv : ∀ k : K, SmoothForm.mpullback (fun z : Z ↦ k • z) (hK k)
      (SmoothForm.mpullback i hi σ) = SmoothForm.mpullback i hi σ) :
    RoughForm.IsBasic (V := ℝ) JQ p (SmoothForm.mpullback i hi σ).1 := by
  refine RoughForm.isBasic_of_mpullback_eq hp (fun k ↦ (hK k).mdifferentiable (by simp))
    (fun k ↦ funext (hpK k)) (fun z z' hzz' ↦ .inr (hfib z z' hzz')) (fun z v j hj ↦ ?_)
    fun k ↦ by simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val (hinv k)
  -- A vertical vector `u` is sent by `di` to an orbit direction `Z_M`, and `σ(Z_M, di w)` is
  -- `⟨dμ (di w), Z⟩ = 0`.
  have hnull (u w : TangentSpace J z) (hu : mfderiv J JQ p z u = 0) :
      SmoothBundleForm.eval₂ (SmoothForm.mpullback i hi σ) z u w = 0 := by
    obtain ⟨Z, hZ⟩ := (a.mem_orbitTangent_iff _).1 (hker z hu)
    rw [ContinuousLinearMap.coe_coe] at hZ
    rw [SmoothForm.eval₂_mpullback, ← hZ, ← h.differential_apply_eq_eval₂]
    exact LinearMap.congr_fun (hrange z ⟨w, rfl⟩) Z
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv, ← SmoothBundleForm.eval₂_apply]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · exact hnull _ _ hj
  · rw [SmoothBundleForm.eval₂_swap, hnull _ _ hj, neg_zero]

/-- **The reduced symplectic form.** Let `σ` be a symplectic form on `M` with a moment map `μ`,
let `i : Z → M` parametrize a level `μ = c` on which the cocycle of `μ` vanishes, with tangent
images `ker dμ`, and let `p : Z → Q` be a surjective smooth submersion out of a boundaryless
manifold whose vertical tangent vectors are exactly those sent by `di` into the stabilizer orbit
directions `𝔤_c · i(z)`. If `K` acts on `Z` by smooth maps over `p`, transitively on the fibres
of `p` and preserving `i^* σ`, then there is a unique symplectic form `ω_red` on `Q` with
`p^* ω_red = i^* σ`. -/
theorem existsUnique_isSymplectic_mpullback_eq_mpullback [J.Boundaryless] {K : Type*} [SMul K Z]
    (h : σ.IsMomentMap a μ) (hσ : σ.IsSymplectic) (hi : ContMDiff J I ∞ i)
    (hμi : ∀ z, μ (i z) = c) (hc : ∀ z, σ.momentCocycle a μ (i z) = 0)
    (hrange : ∀ z, LinearMap.range (mfderiv J I i z).toLinearMap =
      LinearMap.ker (h.differential (i z)))
    (hp : IsSubmersion J JQ ∞ p) (hsurj : Surjective p)
    (hker : ∀ z, (mfderiv J JQ p z).ker =
      ((lieAnnihilator ℝ 𝔤 c).toSubmodule.map (a.eval (i z))).comap
        (mfderiv J I i z).toLinearMap)
    (hK : ∀ k : K, ContMDiff J J ∞ fun z : Z ↦ k • z) (hpK : ∀ (k : K) z, p (k • z) = p z)
    (hfib : ∀ z z', p z = p z' → ∃ k : K, k • z = z')
    (hinv : ∀ k : K, SmoothForm.mpullback (fun z : Z ↦ k • z) (hK k)
      (SmoothForm.mpullback i hi σ) = SmoothForm.mpullback i hi σ) :
    ∃! η : SmoothTwoForm JQ Q,
      η.IsSymplectic ∧ SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi σ :=
  existsUnique_isSymplectic_mpullback_eq hp hsurj (hσ.isClosed.mpullback i hi)
    (h.isBasic_mpullback hi (fun z ↦ (hrange z).le) (hp.contMDiff.mdifferentiable (by simp))
      (fun z ↦ (hker z).le.trans (Submodule.comap_mono
        (LinearMap.map_le_range.trans_eq (a.orbitTangent_eq_range _).symm))) hK hpK hfib hinv)
    fun z ↦ by
      rw [h.ker_bilinFormAt_mpullback hi (hσ.isNondegenerate.nondegenerate_bilinFormAt (i z))
        (hc z) (hrange z), hμi z, hker z]

omit [IsManifold J ∞ Z] [IsManifold JQ ∞ Q] in
/-- **The dimension of the reduced space.** In the setting of
`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`, at a point
`z` where `σ` is nondegenerate at `i z`, `i` is an immersion and the action is locally free, the
model space of `Q` has dimension `dim M - dim 𝔤 - dim 𝔤_c`. -/
theorem finrank_add_finrank_add_finrank_lieAnnihilator (h : σ.IsMomentMap a μ) {z : Z}
    (hσx : (σ.bilinFormAt (i z)).Nondegenerate) (hμi : μ (i z) = c)
    (hc : σ.momentCocycle a μ (i z) = 0)
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = LinearMap.ker (h.differential (i z)))
    (hinj : Injective (mfderiv J I i z)) (hfree : a.isotropy (i z) = ⊥)
    (hp : Surjective (mfderiv J JQ p z))
    (hker : (mfderiv J JQ p z).ker =
      ((lieAnnihilator ℝ 𝔤 c).toSubmodule.map (a.eval (i z))).comap
        (mfderiv J I i z).toLinearMap) :
    finrank ℝ EQ + finrank ℝ 𝔤 + finrank ℝ (lieAnnihilator ℝ 𝔤 c) = finrank ℝ E := by
  subst hμi
  set di := (mfderiv J I i z).toLinearMap
  have hdi : Injective di := hinj
  -- The tangent space of `Z` is identified with `ker dμ` by `di`.
  have hZ : finrank ℝ EZ = finrank ℝ (LinearMap.ker (h.differential (i z))) := by
    rw [← hrange, LinearMap.finrank_range_of_inj hdi, finrank_tangentSpace]
  have : FiniteDimensional ℝ (TangentSpace J z) :=
    FiniteDimensional.of_injective (V₂ := TangentSpace I (i z)) di hdi
  -- The vertical tangent space of `p` is identified with `𝔤_c · i(z)`, hence with `𝔤_c`.
  have hS : (lieAnnihilator ℝ 𝔤 (μ (i z))).toSubmodule.map (a.eval (i z)) ≤
      LinearMap.range di := by
    rw [hrange, ← h.orbitTangent_inf_ker_differential hc]
    exact inf_le_right
  have hvert : finrank ℝ (mfderiv J JQ p z).ker = finrank ℝ (lieAnnihilator ℝ 𝔤 (μ (i z))) := by
    rw [hker, (Submodule.equivMapOfInjective _ hdi
      (((lieAnnihilator ℝ 𝔤 (μ (i z))).toSubmodule.map (a.eval (i z))).comap di)).finrank_eq,
      Submodule.map_comap_eq_of_le hS]
    exact (Submodule.equivMapOfInjective _ ((a.isotropy_eq_bot_iff _).1 hfree) _).finrank_eq.symm
  -- Rank–nullity for `dp` and for `dμ`.
  have hrn := LinearMap.finrank_range_add_finrank_ker (mfderiv J JQ p z).toLinearMap
  rw [LinearMap.range_eq_top.2 hp, finrank_top, finrank_tangentSpace,
    finrank_tangentSpace] at hrn
  have hlev := h.finrank_ker_differential_add_finrank hσx hfree
  omega

end IsMomentMap

namespace IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {J : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold J ∞ Z]
  {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold JQ ∞ Q]
  {i : Z → M} {p : Z → Q} {c : Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The reduced symplectic form of a group-level moment map.** Let a Lie group `G` act on `M` by
symplectomorphisms of `σ`, with coadjoint-equivariant moment map `μ`. Let `i : Z → M` parametrize
a level `μ = c` with tangent images `ker dμ`, and let `p : Z → Q` be a surjective smooth
submersion out of a boundaryless manifold whose vertical tangent vectors are exactly those sent by
`di` into the stabilizer orbit directions `𝔤_c · i(z)`. Let `K` act on `Z` by smooth maps over
`p`, transitively on the fibres of `p`, through a map `φ : K → G` with
`i (k • z) = φ k • i z`; for `Z = μ⁻¹(c)` and `Q = Z / G_c`, take `K = G_c` and `φ` the
inclusion. Then there is a unique symplectic form `ω_red` on `Q` with `p^* ω_red = i^* σ`. -/
theorem existsUnique_isSymplectic_mpullback_eq_mpullback [J.Boundaryless] {K : Type*} [SMul K Z]
    (h : σ.IsEquivariantMomentMap μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hi : ContMDiff J I' ∞ i) (hμi : ∀ z, μ (i z) = c)
    (hrange : ∀ z, LinearMap.range (mfderiv J I' i z).toLinearMap =
      LinearMap.ker (h.differential (i z)))
    (hp : IsSubmersion J JQ ∞ p) (hsurj : Surjective p)
    (hker : ∀ z, (mfderiv J JQ p z).ker =
      ((lieAnnihilator ℝ (GroupLieAlgebra I G) c).toSubmodule.map
        ((InfinitesimalAction.fundamental I G I' M).eval (i z))).comap
        (mfderiv J I' i z).toLinearMap)
    (hK : ∀ k : K, ContMDiff J J ∞ fun z : Z ↦ k • z) (hpK : ∀ (k : K) z, p (k • z) = p z)
    (hfib : ∀ z z', p z = p z' → ∃ k : K, k • z = z') (φ : K → G)
    (hφ : ∀ (k : K) z, i (k • z) = φ k • i z) :
    ∃! η : SmoothTwoForm JQ Q,
      η.IsSymplectic ∧ SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi σ := by
  refine h.toIsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback hσ hi hμi
    (fun z ↦ h.momentCocycle_eq_zero (i z)) hrange hp hsurj hker hK hpK hfib fun k ↦ ?_
  -- `i ∘ (k • ·) = (φ k • ·) ∘ i`, and `φ k` preserves `σ`.
  have hg : ContMDiff I' I' ∞ fun x : M ↦ φ k • x :=
    ContMDiffSMul.contMDiff_const_smul (I := I) (φ k)
  calc SmoothForm.mpullback (fun z : Z ↦ k • z) (hK k) (SmoothForm.mpullback i hi σ)
      = SmoothForm.mpullback (i ∘ fun z : Z ↦ k • z) (hi.comp (hK k)) σ :=
        SmoothForm.mpullback_mpullback _ _ (hK k) hi σ
    _ = SmoothForm.mpullback ((fun x : M ↦ φ k • x) ∘ i) (hg.comp hi) σ :=
        Subtype.ext (by simp only [SmoothForm.coe_mpullback, funext (hφ k), Function.comp_def])
    _ = SmoothForm.mpullback i hi (SmoothForm.mpullback (fun x : M ↦ φ k • x) hg σ) :=
        (SmoothForm.mpullback_mpullback _ _ hi hg σ).symm
    _ = SmoothForm.mpullback i hi σ := by rw [hG]

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
