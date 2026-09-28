/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.CoarseQuotient
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity
public import TauCeti.GroupTheory.GroupAction.Stabilizer

/-!
# Ramification of the orbit projection of a Fuchsian group

Let `Γ ≤ PSL(2, ℝ)` act properly discontinuously on the upper half-plane, as every discrete
subgroup does, so that the coarse orbit quotient `Γ \ ℍ` is a Riemann surface and the orbit
projection `ℍ → Γ \ ℍ` is holomorphic. This file computes the ramification index of that
projection: its local multiplicity at `z` is the order `m` of the stabilizer of `z`
(`Subgroup.localMultiplicity_quotientMk`). So the projection is unramified exactly at the points
of the free locus, and ramifies exactly at the elliptic points, where its local model is the
cyclic quotient map `u ↦ u ^ m`.

The ramification formula for descent follows: a holomorphic map `F` on `Γ \ ℍ` and its pullback
to the upper half-plane satisfy
`localMultiplicity (F ∘ π) z = m * localMultiplicity F (π z)`
(`Subgroup.localMultiplicity_comp_quotientMk`). Read from right to left, this computes the local
multiplicity of an invariant holomorphic map upstairs from that of its unique descent
(`Subgroup.existsUnique_mdifferentiable_quotientMk`) downstairs. Both sides are local
multiplicities: `localMultiplicity F q` is the vanishing order of the chart representative of `F`
recentred at `F q`, not the order of vanishing of `F` itself, so the formula says nothing on its
own about the zeros of `F`. When `F` is nonconstant near the orbit of `z` these two multiplicities
are the ramification indices of `F` and of `F ∘ π`; when `F` is constant there both sides vanish.

## Main declarations

* `Subgroup.localMultiplicity_quotientMk`: the local multiplicity of the orbit projection at `z`
  is the order of the stabilizer of `z`.
* `Subgroup.localMultiplicity_quotientMk_eq_one_iff` and
  `Subgroup.one_lt_localMultiplicity_quotientMk_iff`: the projection is unramified exactly at a
  point with trivial stabilizer and ramified exactly at an elliptic point.
* `Subgroup.exists_injOn_nhds_quotientMk_iff_stabilizer_eq_bot`: the projection is locally
  injective, hence a local homeomorphism, exactly at such a point.
* `Subgroup.localMultiplicity_comp_quotientMk`: the local multiplicity of a holomorphic map on
  `Γ \ ℍ` is multiplied by the stabilizer order when it is pulled back to the upper half-plane.

## References

* Hershel Farkas and Irwin Kra, *Riemann Surfaces*, Graduate Texts in Mathematics 71, Springer,
  second edition, 1992, Chapter I §§4–5.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §§3–4.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.4.
-/

public noncomputable section

open Filter IsManifold Metric MulAction Set TauCeti TauCeti.RiemannSurface Topology UpperHalfPlane

open scoped ContDiff Manifold MatrixGroups

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- **The orbit projection of a Fuchsian group has ramification index the stabilizer order.** Its
local multiplicity at `z` is the order of the stabilizer of `z`. -/
@[simp]
theorem localMultiplicity_quotientMk (z : ℍ) :
    localMultiplicity (Quotient.mk (orbitRel Γ ℍ)) z = Nat.card (stabilizer Γ z) := by
  have : Finite (stabilizer Γ z) :=
    (ProperlyDiscontinuousSMul.finite_stabilizer z).to_subtype
  obtain ⟨ε, hε, hopen⟩ := exists_pos_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z
  have hsource : Quotient.mk (orbitRel Γ ℍ) z ∈
      (stabilizerBallQuotientChart hε hopen).source :=
    (mem_stabilizerBallQuotientChart_source_iff hε hopen).2 ⟨1, by simpa using hε⟩
  have hmax : stabilizerBallQuotientChart hε hopen ∈
      maximalAtlas 𝓘(ℂ) 1 (orbitRel.Quotient Γ ℍ) :=
    subset_maximalAtlas (stabilizerBallQuotientChart_mem_atlas Γ hε hopen)
  have hπ : ∀ᶠ y in 𝓝 z, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Quotient.mk (orbitRel Γ ℍ)) y :=
    .of_forall (mdifferentiable_quotientMk Γ)
  have hchart : ∀ᶠ q in 𝓝 (Quotient.mk (orbitRel Γ ℍ) z),
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (stabilizerBallQuotientChart hε hopen) q :=
    (((stabilizerBallQuotientChart hε hopen).open_source).eventually_mem hsource).mono
      fun _ hy ↦ (contMDiffAt_of_mem_maximalAtlas hmax hy).mdifferentiableAt one_ne_zero
  have hdisc : ∀ᶠ y in 𝓝 z, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (discCoordinate z) y :=
    .of_forall (mdifferentiable_discCoordinate z)
  have hpow : ∀ᶠ u in 𝓝 (discCoordinate z z),
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun u : ℂ ↦ u ^ Nat.card (stabilizer Γ z)) u :=
    .of_forall fun _ ↦
      mdifferentiableAt_iff_differentiableAt.2 (differentiable_pow _ _)
  -- Composing the projection with a chart leaves the local multiplicity unchanged.
  have hcomp : localMultiplicity
      (stabilizerBallQuotientChart hε hopen ∘ Quotient.mk (orbitRel Γ ℍ)) z
      = localMultiplicity (Quotient.mk (orbitRel Γ ℍ)) z := by
    rw [localMultiplicity_comp hchart hπ,
      localMultiplicity_eq_one_of_mem_maximalAtlas hmax hsource, one_mul]
  -- On the hyperbolic disc about `z` that composition is the `m`-th power of the disc coordinate.
  have hmodel : (stabilizerBallQuotientChart hε hopen ∘ Quotient.mk (orbitRel Γ ℍ)) =ᶠ[𝓝 z]
      (fun u : ℂ ↦ u ^ Nat.card (stabilizer Γ z)) ∘ discCoordinate z := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with τ hτ
    exact stabilizerBallQuotientChart_mk hε hopen (mem_ball.1 hτ)
  rw [← hcomp, localMultiplicity_congr hmodel, localMultiplicity_comp hpow hdisc,
    discCoordinate_self, localMultiplicity_pow_zero,
    (localMultiplicity_eq_one_iff hdisc).2 ⟨univ, univ_mem, (discCoordinate_injective z).injOn⟩,
    mul_one]

/-- The orbit projection has positive local multiplicity: it is nowhere locally constant. -/
theorem localMultiplicity_quotientMk_pos (z : ℍ) :
    0 < localMultiplicity (Quotient.mk (orbitRel Γ ℍ)) z := by
  have : Finite (stabilizer Γ z) :=
    (ProperlyDiscontinuousSMul.finite_stabilizer z).to_subtype
  rw [localMultiplicity_quotientMk]
  exact Nat.card_pos

/-- The ramification index of the orbit projection depends only on the orbit. -/
-- Not `@[simp]`: as for `TauCeti.card_stabilizer_smul`, whether the value at `g • z` is in normal
-- form depends on which form of the point the ambient goal presents.
theorem localMultiplicity_quotientMk_smul (g : Γ) (z : ℍ) :
    localMultiplicity (Quotient.mk (orbitRel Γ ℍ)) (g • z)
      = localMultiplicity (Quotient.mk (orbitRel Γ ℍ)) z := by
  rw [localMultiplicity_quotientMk, localMultiplicity_quotientMk, card_stabilizer_smul]

/-- **The orbit projection is unramified exactly on the free locus**: its local multiplicity at
`z` is one exactly when the stabilizer of `z` is trivial, that is, when `z` lies in
`TauCeti.freeLocus Γ ℍ`. -/
-- Not `@[simp]`: `Subgroup.localMultiplicity_quotientMk` already rewrites the left-hand side, so a
-- `simp` lemma of this shape could never fire and `simpNF` rejects it.
theorem localMultiplicity_quotientMk_eq_one_iff (z : ℍ) :
    localMultiplicity (Quotient.mk (orbitRel Γ ℍ)) z = 1 ↔ stabilizer Γ z = ⊥ := by
  rw [localMultiplicity_quotientMk, Subgroup.card_eq_one]

/-- **The orbit projection is locally injective exactly on the free locus.** Near an elliptic
point every neighbourhood contains a pair of distinct points of one stabilizer orbit, so the
projection is not a local homeomorphism, hence not a covering map, there. -/
@[simp]
theorem exists_injOn_nhds_quotientMk_iff_stabilizer_eq_bot (z : ℍ) :
    (∃ U ∈ 𝓝 z, InjOn (Quotient.mk (orbitRel Γ ℍ)) U) ↔ stabilizer Γ z = ⊥ := by
  rw [← localMultiplicity_eq_one_iff (.of_forall (mdifferentiable_quotientMk Γ)),
    localMultiplicity_quotientMk_eq_one_iff]

/-- **The orbit projection ramifies exactly at the elliptic points**: its local multiplicity at
`z` exceeds one exactly when the stabilizer of `z` is nontrivial. -/
-- Not `@[simp]`, for the same reason as `Subgroup.localMultiplicity_quotientMk_eq_one_iff`.
theorem one_lt_localMultiplicity_quotientMk_iff (z : ℍ) :
    1 < localMultiplicity (Quotient.mk (orbitRel Γ ℍ)) z ↔ stabilizer Γ z ≠ ⊥ := by
  have hpos := localMultiplicity_quotientMk_pos Γ z
  rw [ne_eq, ← localMultiplicity_quotientMk_eq_one_iff]
  omega

/-- **The ramification formula for descent.** Pulling a holomorphic map on the coarse quotient back
to the upper half-plane multiplies its local multiplicity by the order of the stabilizer. Applied
to the unique descent of an invariant holomorphic map
(`Subgroup.existsUnique_mdifferentiable_quotientMk`), this computes the local multiplicity of the
map upstairs from that of its descent downstairs. Recall that the local multiplicity of `F` at `q`
is the vanishing order of the chart representative of `F` recentred at `F q`, so this is a
statement about local multiplicities, not about the zeros of `F`; they are the ramification indices
of `F` and of `F ∘ π` when `F` is nonconstant near the orbit of `z`, and both are `0` when `F` is
constant there. -/
theorem localMultiplicity_comp_quotientMk {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) 1 Y] {F : orbitRel.Quotient Γ ℍ → Y} {z : ℍ}
    (hF : ∀ᶠ q in 𝓝 (Quotient.mk (orbitRel Γ ℍ) z), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F q) :
    localMultiplicity (F ∘ Quotient.mk (orbitRel Γ ℍ)) z
      = Nat.card (stabilizer Γ z) * localMultiplicity F (Quotient.mk (orbitRel Γ ℍ) z) := by
  rw [localMultiplicity_comp hF (.of_forall (mdifferentiable_quotientMk Γ)),
    localMultiplicity_quotientMk, mul_comm]

end Subgroup
