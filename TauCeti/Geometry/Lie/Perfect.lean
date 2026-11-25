/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Solvable
public import TauCeti.Geometry.Lie.Subgroup.Image

import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.Geometry.Lie.AutomaticSmoothness
import TauCeti.Geometry.Lie.Subgroup.Commutative
import TauCeti.Geometry.Manifold.Algebra.TypeTags

/-!
# Connected Lie groups with perfect Lie algebra

A Lie algebra `𝔤` is *perfect* when `⁅𝔤, 𝔤⁆ = 𝔤`, that is, when its first derived ideal
`LieAlgebra.derivedSeries ℝ 𝔤 1` is everything. Lie algebras with nondegenerate Killing form, such
as the Lie algebra of a compact semisimple group, are perfect
(`TauCeti.derivedSeries_one_eq_top_of_isKilling`). A connected finite-dimensional real Lie group
`G` with perfect Lie algebra admits no nontrivial continuous homomorphism to a commutative Lie
group, and in particular none to the additive group of `ℝ`.

The reason is that the Lie map of a homomorphism `φ : G → G'` is a Lie algebra homomorphism into
the Lie algebra of `G'`, which is abelian when `G'` is commutative
(`TauCeti.Lie.isLieAbelian_of_isMulCommutative`), so it kills `⁅𝔤, 𝔤⁆ = 𝔤`. A smooth homomorphism
with zero Lie map from a connected group is trivial
(`ContMDiffMonoidMorphism.toMonoidHom_eq_one_iff_lieMap_eq_zero`), and continuous homomorphisms of
Lie groups are smooth (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`). For `ℝ`, the type tag
`Multiplicative ℝ` is a commutative Lie group (`Multiplicative.lieGroup`).

This is the Lie-theoretic half of Weyl's theorem that the universal cover of a compact semisimple
Lie group is compact. Its group-theoretic half extends every homomorphism to `ℝ` from a discrete
central subgroup with compact quotient, by averaging over the quotient, to a continuous
homomorphism defined on the whole group; when the Lie algebra is perfect that extension is trivial,
so the subgroup has no homomorphism to `ℝ` but the trivial one.

## Main results

* `ContMDiffMonoidMorphism.toMonoidHom_eq_one_of_derivedSeries_one_eq_top`: a smooth homomorphism
  from a connected Lie group with perfect Lie algebra to a commutative Lie group is trivial.
* `MonoidHom.eq_one_of_continuous_of_derivedSeries_one_eq_top`: the same for continuous
  homomorphisms.
* `MonoidHom.eq_one_of_continuous_of_derivedSeries_one_eq_top_real`: a connected Lie group with
  perfect Lie algebra has no nontrivial continuous homomorphism to `ℝ`.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V (Weyl's theorem on compact semisimple groups).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 20.
-/

public section

open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [FiniteDimensional ℝ E] [PreconnectedSpace G]

section CommutativeTarget

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [LieGroup I' ∞ G'] [FiniteDimensional ℝ E'] [IsMulCommutative G']

/-- **A connected Lie group with perfect Lie algebra has no nontrivial smooth homomorphism to a
commutative Lie group.** -/
theorem ContMDiffMonoidMorphism.toMonoidHom_eq_one_of_derivedSeries_one_eq_top
    (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (h : LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I G) 1 = ⊤) :
    φ.toMonoidHom = 1 :=
  let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
  φ.toMonoidHom_eq_one_iff_lieMap_eq_zero.mpr ((lieMap φ).eq_zero_of_derivedSeries_one_eq_top h)

variable (I') in
include I' in
/-- **A connected Lie group with perfect Lie algebra has no nontrivial continuous homomorphism to
a commutative Lie group.** -/
theorem MonoidHom.eq_one_of_continuous_of_derivedSeries_one_eq_top (f : G →* G')
    (hf : Continuous f) (h : LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I G) 1 = ⊤) :
    f = 1 := by
  let φ := ContinuousMonoidHom.toContMDiffMonoidMorphism I I' ⟨f, hf⟩
  ext g
  -- `φ.toMonoidHom g` is `φ g`, and `⟨f, hf⟩ g` is `f g`, by the definitions of the coercions of
  -- smooth and of continuous monoid morphisms, for which Mathlib has no rewrite lemmas.
  have h₁ : φ g = 1 := DFunLike.congr_fun (φ.toMonoidHom_eq_one_of_derivedSeries_one_eq_top h) g
  rw [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism] at h₁
  exact h₁

end CommutativeTarget

/-- **A connected Lie group with perfect Lie algebra has no nontrivial continuous homomorphism to
`ℝ`.** -/
theorem MonoidHom.eq_one_of_continuous_of_derivedSeries_one_eq_top_real
    (f : G →* Multiplicative ℝ) (hf : Continuous f)
    (h : LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I G) 1 = ⊤) :
    f = 1 :=
  f.eq_one_of_continuous_of_derivedSeries_one_eq_top 𝓘(ℝ, ℝ) hf h
