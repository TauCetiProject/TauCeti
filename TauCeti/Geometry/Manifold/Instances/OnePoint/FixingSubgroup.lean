/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup.Basic
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Diffeomorphisms of the projective line fixing at most two points

The Möbius transformations fixing two distinct points `p` and `q` of the projective line
`OnePoint 𝕜` form an infinite group: moving `p` to `0` and `q` to `∞`, they are the dilations
`z ↦ c * z` with `c ≠ 0`. Since `GL(2, 𝕜)` acts 2-transitively
(`OnePoint.instIsMultiplyPretransitiveGL`) and analytically (`OnePoint.instContMDiffConstSMul`) on
the projective line, any manifold diffeomorphic to `OnePoint 𝕜` has infinitely many
self-diffeomorphisms fixing any given set of at most two points.

For a component of a marked nodal curve biholomorphic to the Riemann sphere, this is why the
component has infinitely many automorphisms fixing its special points when it carries at most two
of them, so that such a component is unstable.

## Main results

* `Diffeomorph.infinite_fixingSubgroup_of_encard_le_two`: if `M` is `C^n` diffeomorphic to
  `OnePoint 𝕜`, the `C^n` self-diffeomorphisms of `M` fixing a set of at most two points form an
  infinite group.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2, for the Möbius transformations of the Riemann sphere.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

section Dilation

variable [DecidableEq 𝕜]

/-- The dilation `z ↦ c * z` of the projective line, for `c ≠ 0`. -/
private def dilation (c : ({0}ᶜ : Set 𝕜)) : GL (Fin 2) 𝕜 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(c : 𝕜), 0; 0, 1]
    (by simpa using mem_compl_singleton_iff.mp c.2)

private theorem dilation_smul_coe (c : ({0}ᶜ : Set 𝕜)) (z : 𝕜) :
    dilation c • (z : OnePoint 𝕜) = ((c * z : 𝕜) : OnePoint 𝕜) := by
  rw [OnePoint.smul_some_eq_ite]
  simp [dilation, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem dilation_smul_infty (c : ({0}ᶜ : Set 𝕜)) :
    dilation c • (OnePoint.infty : OnePoint 𝕜) = OnePoint.infty :=
  OnePoint.smul_infty_eq_self_iff.mpr (by simp [dilation, Matrix.GeneralLinearGroup.mkOfDetNeZero])

end Dilation

/-- **Infinitely many diffeomorphisms fix at most two points of the projective line.** If `M` is
`C^n` diffeomorphic to the projective line `OnePoint 𝕜`, then the `C^n` self-diffeomorphisms of
`M` fixing every point of a set `s` with at most two points form an infinite group. They include
the Möbius transformations conjugate to dilations whose two fixed points contain the image of
`s`. -/
theorem infinite_fixingSubgroup_of_encard_le_two [ProperSpace 𝕜]
    (e : M ≃ₘ^n⟮I, 𝓘(𝕜)⟯ OnePoint 𝕜) {s : Set M} (hs : s.encard ≤ 2) :
    Infinite (fixingSubgroup (I := I) (n := n) s) := by
  classical
  -- Möbius transformations are analytic, hence `C^n`.
  have : ContMDiffConstSMul 𝓘(𝕜) n (GL (Fin 2) 𝕜) (OnePoint 𝕜) :=
    ⟨fun g ↦ (contMDiff_const_smul (I := 𝓘(𝕜)) (n := ω) g).of_le le_top⟩
  -- Move two distinct points containing `e '' s` to `0` and `∞`.
  obtain ⟨_, hsub, -, h2⟩ := exists_superset_subset_encard_eq (subset_univ (e '' s))
    ((e.injective.encard_image s).le.trans hs)
    (Order.add_one_le_of_lt (one_lt_encard_iff_nontrivial.mpr nontrivial_univ))
  obtain ⟨p, q, hpq, rfl⟩ := encard_eq_two.mp h2
  obtain ⟨g, hg0, hgInf⟩ := MulAction.is_two_pretransitive_iff.mp
    OnePoint.instIsMultiplyPretransitiveGL (OnePoint.coe_ne_infty (0 : 𝕜)) hpq
  -- The conjugated dilations `g ∘ (z ↦ c * z) ∘ g⁻¹` fix `p` and `q`.
  let h (c : ({0}ᶜ : Set 𝕜)) : GL (Fin 2) 𝕜 := g * dilation c * g⁻¹
  have hfix (c : ({0}ᶜ : Set 𝕜)) {y : OnePoint 𝕜} (hy : y ∈ ({p, q} : Set (OnePoint 𝕜))) :
      h c • y = y := by
    rcases hy with rfl | rfl
    · rw [← hg0]
      simp [h, mul_smul, dilation_smul_coe]
    · rw [← hgInf]
      simp [h, mul_smul, dilation_smul_infty]
  let φ (c : ({0}ᶜ : Set 𝕜)) : fixingSubgroup (I := I) (n := n) s :=
    ⟨(e.trans (constSmul 𝓘(𝕜) n (h c))).trans e.symm, mem_fixingSubgroup_of_forall fun x hx ↦ by
      simp [hfix c (hsub (mem_image_of_mem e hx))]⟩
  -- The dilation factor is read off from the image of `e.symm (g • 1)`.
  have hφ (c : ({0}ᶜ : Set 𝕜)) :
      (φ c : M ≃ₘ^n⟮I, I⟯ M) (e.symm (g • ((1 : 𝕜) : OnePoint 𝕜))) =
        e.symm (g • ((c : 𝕜) : OnePoint 𝕜)) := by
    simp [φ, h, mul_smul, dilation_smul_coe]
  have : Infinite ({0}ᶜ : Set 𝕜) := (finite_singleton (0 : 𝕜)).infinite_compl.to_subtype
  refine Infinite.of_injective φ fun c c' hcc' ↦ Subtype.ext ?_
  have := congrArg (fun f : fixingSubgroup (I := I) (n := n) s ↦
    (f : M ≃ₘ^n⟮I, I⟯ M) (e.symm (g • ((1 : 𝕜) : OnePoint 𝕜)))) hcc'
  simpa only [hφ, EmbeddingLike.apply_eq_iff_eq, smul_left_cancel_iff,
    OnePoint.coe_injective.eq_iff] using this

end Diffeomorph
