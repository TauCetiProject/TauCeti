/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm

/-!
# The reduced symplectic form of a group-level moment map

Let a Lie group `G` act on a manifold `M` by symplectomorphisms of `σ`, with a
coadjoint-equivariant moment map `μ`. Given level data `i : Z → M`, `p : Z → Q` as in
`TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm`, the restriction `i^* σ` descends
to a unique symplectic form `ω_red` on `Q` with `p^* ω_red = i^* σ`. Here the cocycle of `μ`
vanishes, and a group `K` acting on `Z` may act through any map `φ : K → G` with
`i (k • z) = φ k • i z`, such as the inclusion of the stabilizer `G_c`; invariance of `i^* σ`
under `K` is then automatic.

## Main results

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

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

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
  {i : Z → M} {p : Z → Q}

/-- **The reduced symplectic form of a group-level moment map.** Let a Lie group `G` act on `M` by
symplectomorphisms of `σ`, with coadjoint-equivariant moment map `μ`. Let `i : Z → M` parametrize
pieces of levels of `μ`, with tangent images `ker dμ`, and let `p : Z → Q` be a surjective smooth
submersion out of a boundaryless manifold whose vertical tangent vectors at `z` are exactly those
sent by `di` into the stabilizer orbit directions `𝔤_c · i(z)`, for `c = μ (i z)`. Let `K` act
on `Z` by smooth maps over `p`, transitively on the fibres of `p`, through a map `φ : K → G` with
`i (k • z) = φ k • i z`; for `Z = μ⁻¹(c)` and `Q = Z / G_c`, take `K = G_c` and `φ` the
inclusion. Then there is a unique symplectic form `ω_red` on `Q` with `p^* ω_red = i^* σ`. -/
theorem existsUnique_isSymplectic_mpullback_eq_mpullback [J.Boundaryless] {K : Type*} [SMul K Z]
    (h : σ.IsEquivariantMomentMap μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hi : ContMDiff J I' ∞ i)
    (hrange : ∀ z, LinearMap.range (mfderiv J I' i z).toLinearMap =
      LinearMap.ker (h.differential (i z)))
    (hp : IsSubmersion J JQ ∞ p) (hsurj : Surjective p)
    (hker : ∀ z, (mfderiv J JQ p z).ker =
      ((lieAnnihilator ℝ (GroupLieAlgebra I G) (μ (i z))).toSubmodule.map
        ((InfinitesimalAction.fundamental I G I' M).eval (i z))).comap
        (mfderiv J I' i z).toLinearMap)
    (hK : ∀ k : K, ContMDiff J J ∞ fun z : Z ↦ k • z) (hpK : ∀ (k : K) z, p (k • z) = p z)
    (hfib : ∀ z z', p z = p z' → ∃ k : K, k • z = z') (φ : K → G)
    (hφ : ∀ (k : K) z, i (k • z) = φ k • i z) :
    ∃! η : SmoothTwoForm JQ Q,
      η.IsSymplectic ∧ SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi σ := by
  refine h.toIsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback hσ hi
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
