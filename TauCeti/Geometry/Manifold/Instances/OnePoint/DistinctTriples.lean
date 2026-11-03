/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.ContinuousSMul
public import TauCeti.Topology.Compactification.OnePoint.MultipleTransitivity
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.Topology.Algebra.Group.SigmaCompact
import TauCeti.Topology.Algebra.Matrix.SpecialLinearGroup
import TauCeti.Topology.Constructions.Pi

/-!
# `PSL(2, ℂ)` is the space of ordered triples of distinct points of the Riemann sphere

Over an algebraically closed field `𝕜`, exactly one element of `PSL(2, 𝕜)` carries `0`, `1`, `∞`
to three given pairwise distinct points of the projective line `OnePoint 𝕜`
(`OnePoint.existsUnique_psl_smul_zero_one_infty_eq`). So for every ordered triple `b` of distinct
points, the orbit map `g ↦ (g • b 0, g • b 1, g • b 2)` is a bijection from `PSL(2, 𝕜)` onto the
ordered triples of distinct points, the injective maps `Fin 3 → OnePoint 𝕜`. This file shows that
when `𝕜` is moreover a proper normed field, such as `ℂ`, this bijection is a homeomorphism, for
the quotient topology of `PSL(2, 𝕜) = SL(2, 𝕜) ⧸ {±1}` and the subspace topology of the triples in
`Fin 3 → OnePoint 𝕜` (`OnePoint.pslHomeomorphDistinctTriples`).

For the Riemann sphere this identifies the automorphism group `PSL(2, ℂ)` with the space of ordered
triples of distinct points, the identification through which automorphisms of a genus-zero domain
are normalized by fixing three marked points; in particular the transformation carrying `0`, `1`,
`∞` to a given triple depends continuously on the triple.

The orbit map is continuous because the Möbius action is jointly continuous
(`OnePoint.instContinuousSMulPSL`). Its inverse is continuous by the open mapping theorem for
group actions (`isOpenMap_smul_of_sigmaCompact`): `PSL(2, 𝕜)` is σ-compact, as a quotient of the
closed subgroup `SL(2, 𝕜)` of the σ-compact space of matrices, and the triples form an open subset
of the compact Hausdorff space `Fin 3 → OnePoint 𝕜`, hence a locally compact Hausdorff, and so
Baire, space on which the group acts transitively.

## Main definitions

* `OnePoint.zeroOneInftyTriple`: the ordered triple `(0, 1, ∞)`.
* `OnePoint.pslHomeomorphDistinctTriples`: for an ordered triple `b` of distinct points, the
  homeomorphism `g ↦ (g • b 0, g • b 1, g • b 2)` from `PSL(2, 𝕜)` onto the ordered triples of
  distinct points.

## Main results

* `OnePoint.pslHomeomorphDistinctTriples_apply_coe`: the homeomorphism moves each point of `b`.
* `OnePoint.pslHomeomorphDistinctTriples_symm_smul` and
  `OnePoint.pslHomeomorphDistinctTriples_symm_eq_iff`: its inverse sends a triple `p` to the unique
  element of `PSL(2, 𝕜)` carrying `b` to `p`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2 (the Möbius transformations of the Riemann sphere).
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Theorem 3.2.2 (sharp triple transitivity).
-/

public section

open Function Topology
open scoped MatrixGroups

namespace OnePoint

open Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable (𝕜) in
/-- The ordered triple `(0, 1, ∞)` of distinct points of the projective line. -/
def zeroOneInftyTriple : {p : Fin 3 → OnePoint 𝕜 // Injective p} :=
  ⟨![((0 : 𝕜) : OnePoint 𝕜), ((1 : 𝕜) : OnePoint 𝕜), ∞], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The points of the ordered triple `(0, 1, ∞)`. -/
@[simp]
theorem coe_zeroOneInftyTriple :
    ((zeroOneInftyTriple 𝕜 : {p : Fin 3 → OnePoint 𝕜 // Injective p}) : Fin 3 → OnePoint 𝕜) =
      ![((0 : 𝕜) : OnePoint 𝕜), ((1 : 𝕜) : OnePoint 𝕜), ∞] :=
  (rfl)

variable [DecidableEq 𝕜]

/-- `PSL(2, 𝕜)` acts on the ordered triples of distinct points by moving each point. This is the
action whose orbit map is `OnePoint.pslHomeomorphDistinctTriples`. -/
@[instance_reducible]
private noncomputable def distinctTriplesMulAction :
    MulAction PSL(2, 𝕜) {p : Fin 3 → OnePoint 𝕜 // Injective p} where
  smul g p := ⟨g • (p : Fin 3 → OnePoint 𝕜), (MulAction.injective g).comp p.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

attribute [local instance] distinctTriplesMulAction

private theorem coe_smul_distinctTriple (g : PSL(2, 𝕜))
    (p : {p : Fin 3 → OnePoint 𝕜 // Injective p}) :
    ((g • p : {p : Fin 3 → OnePoint 𝕜 // Injective p}) : Fin 3 → OnePoint 𝕜) =
      g • (p : Fin 3 → OnePoint 𝕜) :=
  (rfl)

variable [IsAlgClosed 𝕜]

/-- Over an algebraically closed field, some element of `PSL(2, 𝕜)` carries the ordered triple
`(0, 1, ∞)` to any given ordered triple of distinct points, and it is unique. -/
private theorem existsUnique_smul_zeroOneInftyTriple_eq
    (p : {p : Fin 3 → OnePoint 𝕜 // Injective p}) :
    ∃! g : PSL(2, 𝕜), g • zeroOneInftyTriple 𝕜 = p := by
  have hp (i j : Fin 3) (hij : i ≠ j) : p.1 i ≠ p.1 j := p.2.ne hij
  obtain ⟨g, hg, hu⟩ := existsUnique_psl_smul_zero_one_infty_eq
    (hp 0 1 (by decide)) (hp 0 2 (by decide)) (hp 1 2 (by decide))
  -- An equality of triples is the equality of their three points.
  have key (h : PSL(2, 𝕜)) : h • zeroOneInftyTriple 𝕜 = p ↔
      h • ((0 : 𝕜) : OnePoint 𝕜) = p.1 0 ∧ h • ((1 : 𝕜) : OnePoint 𝕜) = p.1 1 ∧
        h • (∞ : OnePoint 𝕜) = p.1 2 := by
    rw [Subtype.ext_iff, coe_smul_distinctTriple, funext_iff]
    refine ⟨fun hh ↦ ⟨by simpa using hh 0, by simpa using hh 1, by simpa using hh 2⟩, ?_⟩
    rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> simpa
  exact ⟨g, (key g).2 hg, fun h hh ↦ hu h ((key h).1 hh)⟩

/-- The orbit map of an ordered triple of distinct points is bijective. -/
private theorem bijective_smul_distinctTriple (b : {p : Fin 3 → OnePoint 𝕜 // Injective p}) :
    Bijective fun g : PSL(2, 𝕜) ↦ g • b := by
  obtain ⟨k, hk, -⟩ := existsUnique_smul_zeroOneInftyTriple_eq b
  refine ⟨fun g h hgh ↦ ?_, fun p ↦ ?_⟩
  · -- Both `g * k` and `h * k` carry `(0, 1, ∞)` to the same triple.
    have := (existsUnique_smul_zeroOneInftyTriple_eq (g • b)).unique (y₁ := g * k) (y₂ := h * k)
      (by rw [mul_smul, hk]) (by rw [mul_smul, hk]; exact hgh.symm)
    exact mul_right_cancel this
  · obtain ⟨l, hl, -⟩ := existsUnique_smul_zeroOneInftyTriple_eq p
    exact ⟨l * k⁻¹, by simp only [mul_smul, ← hk, inv_smul_smul, hl]⟩

variable [ProperSpace 𝕜]

/-- **`PSL(2, 𝕜)` is homeomorphic to the space of ordered triples of distinct points of the
projective line**, over a proper algebraically closed normed field such as `ℂ`. For an ordered
triple `b` of distinct points, the homeomorphism sends `g` to `(g • b 0, g • b 1, g • b 2)`; the
inverse sends a triple `p` to the unique element of `PSL(2, 𝕜)` carrying `b` to `p`, which
therefore depends continuously on `p`. For `b = (0, 1, ∞)` this identifies the automorphism group
of the Riemann sphere with its ordered triples of distinct points. -/
noncomputable def pslHomeomorphDistinctTriples (b : {p : Fin 3 → OnePoint 𝕜 // Injective p}) :
    PSL(2, 𝕜) ≃ₜ {p : Fin 3 → OnePoint 𝕜 // Injective p} :=
  haveI : ContinuousSMul PSL(2, 𝕜) {p : Fin 3 → OnePoint 𝕜 // Injective p} :=
    IsEmbedding.subtypeVal.isInducing.continuousSMul continuous_id
      fun {g p} ↦ coe_smul_distinctTriple g p
  haveI : MulAction.IsPretransitive PSL(2, 𝕜) {p : Fin 3 → OnePoint 𝕜 // Injective p} :=
    ⟨fun p q ↦ ⟨_, ((bijective_smul_distinctTriple p).2 q).choose_spec⟩⟩
  -- The triples form an open subset of a compact Hausdorff space, so a Baire space.
  haveI : LocallyCompactSpace {p : Fin 3 → OnePoint 𝕜 // Injective p} :=
    (TauCeti.isOpen_setOf_injective (X := OnePoint 𝕜) (κ := Fin 3)).locallyCompactSpace
  (Equiv.ofBijective _ (bijective_smul_distinctTriple b)).toHomeomorphOfContinuousOpen
    (continuous_id.smul continuous_const) (isOpenMap_smul_of_sigmaCompact b)

/-- The homeomorphism `OnePoint.pslHomeomorphDistinctTriples b` moves each point of `b`. -/
@[simp]
theorem pslHomeomorphDistinctTriples_apply_coe (b : {p : Fin 3 → OnePoint 𝕜 // Injective p})
    (g : PSL(2, 𝕜)) (i : Fin 3) :
    (pslHomeomorphDistinctTriples b g : Fin 3 → OnePoint 𝕜) i = g • (b : Fin 3 → OnePoint 𝕜) i :=
  (rfl)

/-- The inverse of `OnePoint.pslHomeomorphDistinctTriples b` sends a triple `p` to an element of
`PSL(2, 𝕜)` carrying each point of `b` to the corresponding point of `p`. -/
@[simp]
theorem pslHomeomorphDistinctTriples_symm_smul (b p : {p : Fin 3 → OnePoint 𝕜 // Injective p})
    (i : Fin 3) :
    (pslHomeomorphDistinctTriples b).symm p • (b : Fin 3 → OnePoint 𝕜) i =
      (p : Fin 3 → OnePoint 𝕜) i := by
  rw [← pslHomeomorphDistinctTriples_apply_coe, Homeomorph.apply_symm_apply]

/-- The inverse of `OnePoint.pslHomeomorphDistinctTriples b` sends a triple `p` to the unique
element of `PSL(2, 𝕜)` carrying `b` to `p`. -/
theorem pslHomeomorphDistinctTriples_symm_eq_iff
    (b p : {p : Fin 3 → OnePoint 𝕜 // Injective p}) (g : PSL(2, 𝕜)) :
    (pslHomeomorphDistinctTriples b).symm p = g ↔
      ∀ i, g • (b : Fin 3 → OnePoint 𝕜) i = (p : Fin 3 → OnePoint 𝕜) i := by
  rw [Homeomorph.symm_apply_eq, Subtype.ext_iff, funext_iff]
  simp only [pslHomeomorphDistinctTriples_apply_coe, eq_comm]

end OnePoint
