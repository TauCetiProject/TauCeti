/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.LieGroup
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Manifold.Prod
import TauCeti.Geometry.Lie.InvariantVectorField.Basic

/-!
# The shifting identity for the form on `G × μ⁻¹(c)`

Let a Lie group `G` act smoothly by symplectomorphisms on `(M, σ)`, with coadjoint-equivariant
moment map `μ : M → 𝔤*`, and fix `c ∈ 𝔤*`. In orbit reduction one compares the level
`Z = μ⁻¹(c)` with the preimage `μ⁻¹(O)` of the coadjoint orbit `O = G · c` through the action
map

`a : G × Z → M`, `a(g, z) = g • z`,

whose image is `μ⁻¹(O)`. The coadjoint orbit carries the Kirillov–Kostant–Souriau form `ω_KKS`,
and its pullback along the orbit map `g ↦ Ad*_g c` is the left-invariant Kirillov form `σ_c` of
`c` on `G` (`Module.Dual.leftInvariantKirillovForm`), which pairs the left-invariant vector fields
of `ξ` and `η` to `c ⁅ξ, η⁆`. This file proves the **shifting identity**

`a^* σ = pr_G^* σ_c + pr_Z^* (i^* σ)`

on `G × Z`, for the inclusion `i : Z → M`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm`).
It is stated for any smooth map `i : Z → M` from a manifold into the level, so it applies to the
regular level `μ⁻¹(c)` with its submanifold atlas, and needs neither a regular value nor
nondegeneracy of `σ`.

The quotient `Y_O = G ×_{G_c} Z` of `G × Z` by `h · (g, z) = (g h⁻¹, h • z)` maps to the reduced
space `Q = Z / G_c` by `q_Y [g, z] = [z]`, to `M` by `i_Y [g, z] = g • z` and to `O` by
`pr_Y [g, z] = [g]`. Since the reduced form satisfies `π^* ω_red = i^* σ`, pulling the identity
`q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS` back along the quotient map `G × Z → Y_O` gives exactly
the shifting identity above, so the identity on `Y_O` is equivalent to it whenever pullback along
that quotient map is injective, as for a surjective submersion.

The computation is pointwise. A tangent vector of `G × Z` at `(g, z)` is a pair of the left
translate of some `ξ ∈ 𝔤` and a tangent vector `v` of `Z`, and the action map sends it to
`d(g •)(ξ_M + v)`, where `v` is read in `T_z M`
(`TauCeti.mfderiv_smul_mulInvariantVectorField`). As `g` preserves `σ`,

`σ(d(g •)(ξ_M + v), d(g •)(η_M + w)) = σ(ξ_M, η_M) + σ(ξ_M, w) - σ(η_M, v) + σ(v, w)`.

The moment map identity `σ(ξ_M, w) = ⟨dμ(w), ξ⟩` kills the two cross terms when `v` and `w` are
tangent to the level, and infinitesimal equivariance gives `σ(ξ_M, η_M) = μ(z) ⁅ξ, η⁆ = c ⁅ξ, η⁆`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.eval₂_mfderiv_smul_add_fundamentalVectorField`).

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `eval₂_mfderiv_smul_add_fundamentalVectorField`: the pointwise identity
  `σ(d(g •)(ξ_M + v), d(g •)(η_M + w)) = μ(x) ⁅ξ, η⁆ + σ(v, w)` for `v`, `w` in `ker dμ_x`.
* `mpullback_smul_eq_prod_leftInvariantKirillovForm`: the shifting identity
  `a^* σ = pr_G^* σ_c + pr_Z^* (i^* σ)` on `G × Z`.
* `mpullback_smul_prodMk_prod_neg_leftInvariantKirillovForm`: equivalently, the map
  `(g, z) ↦ (g • i z, g)` pulls `pr_M^* σ - pr_G^* σ_c` on `M × G` back to `pr_Z^* (i^* σ)`, the
  form of the shifting construction on `M × O⁻` read on `G × Z`.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (the shifting trick).
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The shifting identity at a point.** Let `g` act by a symplectomorphism and let `v`, `w` be
tangent to the level of `μ` through `x`, that is in the kernel of `dμ_x`. Then
`σ(d(g •)(ξ_M + v), d(g •)(η_M + w)) = μ(x) ⁅ξ, η⁆ + σ(v, w)`: the orbit directions pair through
the Kirillov form of `μ(x)`, and they are `σ`-orthogonal to the level. -/
theorem eval₂_mfderiv_smul_add_fundamentalVectorField (h : σ.IsEquivariantMomentMap μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (x : M) (ξ η : GroupLieAlgebra I G) {v w : TangentSpace I' x}
    (hv : h.toIsMomentMap.differential x v = 0) (hw : h.toIsMomentMap.differential x w = 0) :
    σ.eval₂ (g • x)
        (mfderiv I' I' (fun y : M ↦ g • y) x (fundamentalVectorField I' ξ x + v))
        (mfderiv I' I' (fun y : M ↦ g • y) x (fundamentalVectorField I' η x + w)) =
      μ x ⁅ξ, η⁆ + σ.eval₂ x v w := by
  -- The cross terms are `⟨dμ_x w, ξ⟩` and `-⟨dμ_x v, η⟩`.
  have hcross (ζ : GroupLieAlgebra I G) {u : TangentSpace I' x}
      (hu : h.toIsMomentMap.differential x u = 0) :
      σ.eval₂ x (fundamentalVectorField I' ζ x) u = 0 := by
    rw [← InfinitesimalAction.fundamental_apply, ← h.toIsMomentMap.differential_apply_eq_eval₂,
      hu, LinearMap.zero_apply]
  have horbit : σ.eval₂ x (fundamentalVectorField I' ξ x) (fundamentalVectorField I' η x) =
      μ x ⁅ξ, η⁆ := by
    simpa only [InfinitesimalAction.fundamental_apply] using
      momentCocycle_eq_zero_iff.1 (h.momentCocycle_eq_zero x) ξ η
  rw [← SmoothForm.eval₂_mpullback _ (ContMDiffSMul.contMDiff_const_smul (I := I) g), hg,
    SmoothBundleForm.eval₂_add_left, SmoothBundleForm.eval₂_add_right,
    SmoothBundleForm.eval₂_add_right, horbit, hcross ξ hw,
    SmoothBundleForm.eval₂_swap σ x v, hcross η hv, neg_zero, add_zero, zero_add]

variable {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners ℝ EZ HZ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z]
  [IsManifold IZ ∞ Z] {i : Z → M}

/-- **The shifting identity.** Let `G` act by symplectomorphisms of `(M, σ)` with
coadjoint-equivariant moment map `μ`, and let `i : Z → M` be a smooth map into the level
`μ⁻¹(c)`, such as the inclusion of a regular level. The action map `a(g, z) = g • i z` on `G × Z`
pulls `σ` back to `pr_G^* σ_c + pr_Z^* (i^* σ)`, where `σ_c` is the left-invariant Kirillov form
of `c`, the pullback of the Kirillov–Kostant–Souriau form of the coadjoint orbit of `c` along
`g ↦ Ad*_g c`. -/
theorem mpullback_smul_eq_prod_leftInvariantKirillovForm (h : σ.IsEquivariantMomentMap μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hi : ContMDiff IZ I' ∞ i) {c : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hic : ∀ z, μ (i z) = c) :
    SmoothForm.mpullback (fun p : G × Z ↦ p.1 • i p.2)
        (contMDiff_fst.smul (hi.comp contMDiff_snd)) σ =
      SmoothTwoForm.prod c.leftInvariantKirillovForm (SmoothForm.mpullback i hi σ) := by
  refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
  obtain ⟨g, z⟩ := p
  have ha : MDifferentiableAt (I.prod IZ) I' (fun p : G × Z ↦ p.1 • i p.2) (g, z) :=
    (contMDiff_fst.smul (hi.comp contMDiff_snd) :
      ContMDiff (I.prod IZ) I' ∞ fun p : G × Z ↦ p.1 • i p.2).mdifferentiableAt (by simp)
  have hsmul : MDifferentiableAt I' I' (fun y : M ↦ g • y) (i z) :=
    (ContMDiffSMul.contMDiff_const_smul (I := I) (n := ∞) g).mdifferentiableAt (by simp)
  -- The action map sends `(X^L_ξ(g), u)` to `d(g •)(ξ_M + di u)`.
  have hda (u : TangentSpace (I.prod IZ) (g, z)) {ξ : GroupLieAlgebra I G}
      (hξ : mulInvariantVectorField ξ g = u.1) :
      mfderiv (I.prod IZ) I' (fun p : G × Z ↦ p.1 • i p.2) (g, z) u =
        mfderiv I' I' (fun y : M ↦ g • y) (i z)
          (fundamentalVectorField I' ξ (i z) + mfderiv IZ I' i z u.2) := by
    rw [mfderiv_prod_eq_add_apply ha, map_add]
    dsimp only
    rw [← hξ, mfderiv_smul_mulInvariantVectorField]
    congr 1
    exact mfderiv_comp_apply_of_eq z hsmul (hi.mdifferentiableAt (by simp)) rfl _
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (I := I) (g := g) v.1
  obtain ⟨η, hη⟩ := exists_mulInvariantVectorField_eq (I := I) (g := g) w.1
  rw [SmoothForm.eval₂_mpullback, eval₂_prod, hda v hξ, hda w hη]
  refine (h.eval₂_mfderiv_smul_add_fundamentalVectorField (hG g) (i z) ξ η
    (h.toIsMomentMap.differential_mfderiv_eq_zero hi hic z v.2)
    (h.toIsMomentMap.differential_mfderiv_eq_zero hi hic z w.2)).trans ?_
  rw [hic z, SmoothForm.eval₂_mpullback, Manifold.tangentSpaceProdEquiv_apply,
    Manifold.tangentSpaceProdEquiv_apply, ← hξ, ← hη,
    c.eval₂_leftInvariantKirillovForm_mulInvariantVectorField]

/-- **The shifting identity on `M × G`.** With the hypotheses of
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm`,
the map `(g, z) ↦ (g • i z, g)` from `G × Z` to `M × G` pulls the product form
`pr_M^* σ - pr_G^* σ_c` back to `pr_Z^* (i^* σ)`. Its image lies over the zero level of the
shifting moment map `(x, g) ↦ μ x - Ad*_g c`, and on `M × O⁻` this is the identity
`q_O^* ω_red = pr_M^* σ - pr_O^* ω_KKS` read on `G × Z`. -/
theorem mpullback_smul_prodMk_prod_neg_leftInvariantKirillovForm
    (h : σ.IsEquivariantMomentMap μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hi : ContMDiff IZ I' ∞ i) {c : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hic : ∀ z, μ (i z) = c) :
    SmoothForm.mpullback (fun p : G × Z ↦ (p.1 • i p.2, p.1))
        ((contMDiff_fst.smul (hi.comp contMDiff_snd)).prodMk contMDiff_fst)
        (SmoothTwoForm.prod σ (-c.leftInvariantKirillovForm)) =
      SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback i hi σ) := by
  have ha : ContMDiff (I.prod IZ) I' ∞ fun p : G × Z ↦ p.1 • i p.2 :=
    contMDiff_fst.smul (hi.comp contMDiff_snd)
  refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
  have hmain := congrArg (fun φ ↦ SmoothBundleForm.eval₂ φ p v w)
    (h.mpullback_smul_eq_prod_leftInvariantKirillovForm hG hi hic)
  rw [SmoothForm.eval₂_mpullback, eval₂_prod, SmoothForm.eval₂_mpullback,
    Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_apply] at hmain
  -- The derivative of `(g, z) ↦ (g • i z, g)` is `u ↦ (da u, u.1)`.
  have hd (u : TangentSpace (I.prod IZ) p) :
      Manifold.tangentSpaceProdEquiv (p.1 • i p.2, p.1)
          (mfderiv (I.prod IZ) (I'.prod I) (fun p : G × Z ↦ (p.1 • i p.2, p.1)) p u) =
        (mfderiv (I.prod IZ) I' (fun p : G × Z ↦ p.1 • i p.2) p u, u.1) := by
    rw [Manifold.tangentSpaceProdEquiv_apply,
      mfderiv_prodMk (ha.mdifferentiableAt (by simp)) mdifferentiableAt_fst, mfderiv_fst]
    -- `ContinuousLinearMap.prod_apply` does not rewrite here, since `T_p (G × Z)` is not
    -- syntactically `E × EZ`; the two sides agree by unfolding `prod` and `fst`.
    rfl
  rw [SmoothForm.eval₂_mpullback, eval₂_prod, SmoothBundleForm.eval₂_neg,
    SmoothForm.eval₂_mpullback_snd, hd, hd, Manifold.tangentSpaceProdEquiv_apply,
    Manifold.tangentSpaceProdEquiv_apply]
  dsimp only
  rw [hmain, add_neg_cancel_comm, SmoothForm.eval₂_mpullback]

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
