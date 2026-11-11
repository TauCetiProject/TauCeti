/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Manifold.Descent

/-!
# The reduced symplectic form on a quotient of a moment-map level

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a Lie algebra `𝔤` on a
manifold `M` with a two-form `σ` (`TauCeti.SmoothTwoForm.IsMomentMap`). Let `g : N → M` be a
smooth map whose tangent image at every point `p` lies in the kernel of `dμ` at `g p`, such as the
inclusion of a level `μ⁻¹(c)`. Let `π : N → Q` be a differentiable map whose fibres are the orbits
of maps `p ↦ k • p` of a family `K` acting on `N` and on `M`, such that `g` is equivariant and `σ`
is invariant. This is the shape of the orbit projection `μ⁻¹(c) → μ⁻¹(c) / G_c` of
Marsden–Weinstein–Meyer reduction, for the stabilizer `G_c` of `c` under a coadjoint-equivariant
moment map, acting freely and properly on the level.

By the moment map identity `σ(Z_M, v) = dμ_Z(v)`, the vectors that `dg_p` sends into the orbit
directions `𝔤 · g p` are null directions of `g^* σ`. When the vertical vectors of `π` are among
them, `g^* σ` is basic for `π` (`TauCeti.SmoothTwoForm.IsMomentMap.isBasic_mpullback`): it is
invariant under `K` because `σ` is and `g` is equivariant, and it vanishes on vertical vectors.

Now let `σ` be symplectic, that is closed and nondegenerate, let the tangent image of `g` be
exactly the kernel of `dμ`, as for a regular level, and let the cocycle of `μ` vanish at the
points `g p`. Then the null directions of `g^* σ` at `p` are the vectors that `dg_p` sends into
the stabilizer directions `𝔤_{μ(g p)} · g p`
(`TauCeti.SmoothTwoForm.IsMomentMap.ker_bilinFormAt_mpullback`). When `π` is moreover a surjective
smooth submersion whose vertical vectors are exactly these null directions, `g^* σ` descends to a
unique symplectic form `ω_red` on `Q` with `π^* ω_red = g^* σ`
(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`). This is
the reduced symplectic form of the Marsden–Weinstein–Meyer theorem, here for any quotient
submersion with these properties.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.isBasic_mpullback`: the restriction of the form to a level is
  basic for a quotient whose vertical vectors are orbit directions.
* `TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`: existence
  and uniqueness of the reduced symplectic form.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the proof of the Marsden–Weinstein–Meyer theorem).
-/

public section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  (h : σ.IsMomentMap a μ)
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {E'' H'' Q : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {J' : ModelWithCorners ℝ E'' H''} [TopologicalSpace Q] [ChartedSpace H'' Q]
  {K : Type*} [SMul K N] [SMul K M] [ContMDiffConstSMul J ∞ K N] [ContMDiffConstSMul I ∞ K M]
  {g : N → M} (hg : ContMDiff J I ∞ g) {π : N → Q}

include h

/-- **The form on a level is basic for its quotient.** Let `g : N → M` be a smooth map whose
tangent image at every `p` lies in the kernel of `dμ` at `g p`. Let `π : N → Q` be a
differentiable map whose fibres are the orbits of `K`, where `g` is `K`-equivariant and `σ` is
`K`-invariant. If every vertical vector of `π` at `p` is sent by `dg_p` into the orbit directions
`𝔤 · g p`, then `g^* σ` is basic for `π`. -/
theorem isBasic_mpullback
    (hrange : ∀ p, LinearMap.range (mfderiv J I g p).toLinearMap ≤
      LinearMap.ker (h.differential (g p)))
    (hgK : ∀ (k : K) (p : N), g (k • p) = k • g p)
    (hσK : ∀ k : K, SmoothForm.mpullback (k • ·) (contMDiff_const_smul k) σ = σ)
    (hπ : MDifferentiable J J' π) (hπK : ∀ (k : K) (p : N), π (k • p) = π p)
    (hKπ : ∀ p p', π p = π p' → ∃ k : K, k • p = p')
    (hvert : ∀ p, (mfderiv J J' π p).ker ≤
      (a.orbitTangent (g p)).comap (mfderiv J I g p).toLinearMap) :
    RoughForm.IsBasic (V := ℝ) (k := 2) J' π (SmoothForm.mpullback g hg σ).1 := by
  refine SmoothTwoForm.isBasic_of_mpullback_eq hπ (τ := fun k : K ↦ (k • ·))
    contMDiff_const_smul (fun k ↦ funext (hπK k)) (fun p p' hpp' ↦ .inr (hKπ p p' hpp'))
    (fun k ↦ ?_) fun p v hv ↦ ?_
  · -- `g^* σ` is invariant, as `g ∘ (k • ·) = (k • ·) ∘ g` and `σ` is invariant.
    rw [SmoothForm.mpullback_mpullback]
    conv_rhs => rw [← hσK k, SmoothForm.mpullback_mpullback]
    simp only [comp_def, hgK]
  · -- If `dg_p v = Z_M(g p)`, then `σ(dg_p v, dg_p w) = dμ_Z(dg_p w) = 0` by the moment map
    -- identity, as `dg_p w` is tangent to the level.
    obtain ⟨Z, hZ⟩ := (a.mem_orbitTangent_iff (g p)).1 (hvert p hv)
    ext w
    have hw := LinearMap.congr_fun (hrange p ⟨w, rfl⟩) Z
    rw [ContinuousLinearMap.coe_coe, h.differential_apply_eq_eval₂, hZ] at hw
    rw [SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback]
    exact hw

/-- **The reduced symplectic form.** Let `σ` be symplectic, and let `g : N → M` be a smooth map
whose tangent image at every `p` is the kernel of `dμ` at `g p`, where the cocycle of the moment
map vanishes, such as the inclusion of a regular level `μ⁻¹(c)`. Let `π : N → Q` be a surjective
smooth submersion out of a manifold whose model has no boundary, whose fibres are the orbits of
`K`, where `g` is `K`-equivariant and `σ` is `K`-invariant. If the vertical vectors of `π` at `p`
are exactly the vectors that `dg_p` sends into the stabilizer directions `𝔤_{μ(g p)} · g p`, then
there is exactly one symplectic form `ω_red` on `Q` with `π^* ω_red = g^* σ`. -/
theorem existsUnique_isSymplectic_mpullback_eq_mpullback [FiniteDimensional ℝ E]
    [IsManifold J' ∞ Q] [J.Boundaryless] (hσ : σ.IsSymplectic)
    (hc : ∀ p, σ.momentCocycle a μ (g p) = 0)
    (hrange : ∀ p, LinearMap.range (mfderiv J I g p).toLinearMap =
      LinearMap.ker (h.differential (g p)))
    (hgK : ∀ (k : K) (p : N), g (k • p) = k • g p)
    (hσK : ∀ k : K, SmoothForm.mpullback (k • ·) (contMDiff_const_smul k) σ = σ)
    (hπ : IsSubmersion J J' ∞ π) (hsurj : Surjective π) (hπK : ∀ (k : K) (p : N), π (k • p) = π p)
    (hKπ : ∀ p p', π p = π p' → ∃ k : K, k • p = p')
    (hvert : ∀ p, (mfderiv J J' π p).ker =
      ((lieAnnihilator ℝ 𝔤 (μ (g p))).toSubmodule.map (a.eval (g p))).comap
        (mfderiv J I g p).toLinearMap) :
    ∃! η : SmoothTwoForm J' Q,
      η.IsSymplectic ∧ SmoothForm.mpullback π hπ.contMDiff η = SmoothForm.mpullback g hg σ := by
  have hσx p := hσ.isNondegenerate.nondegenerate_bilinFormAt (g p)
  refine SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq hπ hsurj (hσ.isClosed.mpullback g hg)
    (h.isBasic_mpullback hg (fun p ↦ (hrange p).le) hgK hσK
      (hπ.contMDiff.mdifferentiable (by simp)) hπK hKπ fun p ↦ (hvert p).le.trans
        (Submodule.comap_mono (a.orbitTangent_eq_range (g p) ▸ LinearMap.map_le_range))) fun p ↦ ?_
  rw [h.ker_bilinFormAt_mpullback hg (hσx p) (hc p) (hrange p), hvert p]

end TauCeti.SmoothTwoForm.IsMomentMap
