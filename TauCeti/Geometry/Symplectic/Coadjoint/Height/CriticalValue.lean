/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Perfect
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.Geometry.Lie.Adjoint.Compact
import TauCeti.Topology.Algebra.Module.Baire

/-!
# Regular heights with distinct critical values

Let `G` be a compact Lie group with Lie algebra `𝔤`, let `B` be a separating invariant form on
`𝔤`, and let `𝔤 = t + Σ F_i` be a root-plane decomposition over an abelian subspace `t`, with
roots `α_i`. For `ν ∈ 𝔤*` let `O = G ⧸ G_ν` be its coadjoint orbit, with orbit map `μ : O → 𝔤*`,
and for `X ∈ t` let `f_X = ⟨μ, X⟩` be the height of `X`. When `X` is regular, `α_i(X) ≠ 0` for
every root, `f_X` is a Morse function, and its critical points are the points of `O` lying over
`t`:

`Crit(f_X) = μ⁻¹(B t)`

(`TauCeti.IsRootPlaneDecomposition.criticalPoints_eq_preimage_orbitMap_coadjointRepresentation`).
This finite set `C` does not depend on the regular element `X`, but the critical values do: at the
point `x ∈ C` with `μ x = B q`, `q ∈ t`, the value is `f_X(x) = B(q, X)`. So the critical points
over `q ≠ q'` share their value exactly when `B(q - q', X) = 0`, which can happen for regular `X`.

This file proves that this happens only on finitely many hyperplanes of `t`. The roots of a
root-plane decomposition with a regular element are nonzero, and the planes `F_i` are then
`B`-orthogonal to `t`, so `B` stays separating on `t`
(`TauCeti.IsRootPlaneDecomposition.exists_mem_apply_ne_zero`). Hence for `q ≠ q'` in `t` the
functional `X ↦ B(q - q', X)` on `t` is nonzero, and the regular elements whose height has
pairwise distinct critical values are the points of `t` at which finitely many nonzero linear
functionals, the roots and these differences, all take nonzero values. They form a dense open
subset of `t`
(`IsRootPlaneDecomposition.isOpen_setOf_injOn_orbitMap_coadjointRepresentation_apply`,
`IsRootPlaneDecomposition.dense_setOf_injOn_orbitMap_coadjointRepresentation_apply`), so
every nonempty open subset of `t`, such as an open Weyl chamber, contains an element whose height
is a Morse function with pairwise distinct critical values
(`IsRootPlaneDecomposition.exists_mem_isMorse_and_injOn_orbitMap_coadjointRepresentation_apply`).
In particular every coadjoint orbit of a compact Lie group carries such a height
(`Module.Dual.exists_isMorse_and_injOn_orbitMap_coadjointRepresentation_apply`), from the
root-plane decomposition of `TauCeti.exists_isRootPlaneDecomposition_groupLieAlgebra`. Each critical
level of such a height contains exactly one critical point, which is what building the orbit from
the sublevel sets of `f_X` one handle at a time needs.

## Main results

In the namespace `TauCeti.IsRootPlaneDecomposition`:

* `isOpen_setOf_injOn_orbitMap_coadjointRepresentation_apply`,
  `dense_setOf_injOn_orbitMap_coadjointRepresentation_apply`: the regular elements of `t` whose
  height has pairwise distinct critical values form a dense open subset of `t`.
* `exists_mem_isMorse_and_injOn_orbitMap_coadjointRepresentation_apply`: every nonempty open
  subset of `t` contains such an element.

In the namespace `Module.Dual`:

* `exists_isMorse_and_injOn_orbitMap_coadjointRepresentation_apply`: every coadjoint orbit of a
  compact Lie group carries a Morse height with pairwise distinct critical values.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II.
-/

public section

open Module Manifold Set TauCeti TauCeti.Lie
open scoped Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

namespace TauCeti.IsRootPlaneDecomposition

variable {ν : Module.Dual ℝ (GroupLieAlgebra I G)} {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {ι : Type*} {t : Submodule ℝ (GroupLieAlgebra I G)} {α : ι → Dual ℝ t}
  {F : ι → Submodule ℝ (GroupLieAlgebra I G)} {J : (i : ι) → Module.End ℝ (F i)}

/-- The regular elements of `t` whose height has pairwise distinct critical values are the points
at which finitely many nonzero continuous functionals on `t` do not vanish: the roots, and the
differences `X ↦ B(q - q', X)` for the points `q ≠ q'` of `t` lying under two critical points. -/
private theorem exists_finite_setOf_injOn_eq [Finite ι] [CompactSpace G]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft) (hα : ∀ i, α i ≠ 0) :
    ∃ s : Set (t →L[ℝ] ℝ), s.Finite ∧ (∀ φ ∈ s, φ ≠ 0) ∧
      {X : t | (∀ i, α i X ≠ 0) ∧
        InjOn (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)
          (criticalPoints
            𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
            fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)} =
        {X | ∀ φ ∈ s, φ X ≠ 0} := by
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  -- A regular element exists, so the part of the orbit over `t` is the critical set of a Morse
  -- height on a compact orbit, hence finite.
  obtain ⟨X₀, hX₀⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists α fun i ↦
    not_forall.1 fun h ↦ hα i (LinearMap.ext h)
  have hK : ((coadjointRepresentation ℝ I G).orbitMap ν ⁻¹'
      (B '' (t : Set (GroupLieAlgebra I G)))).Finite := by
    rw [← hD.criticalPoints_eq_preimage_orbitMap_coadjointRepresentation hB hsep hX₀]
    exact (hD.isMorse_orbitMap_coadjointRepresentation_apply hB hsep hX₀).finite_criticalPoints
  set K := (coadjointRepresentation ℝ I G).orbitMap ν ⁻¹' (B '' (t : Set (GroupLieAlgebra I G)))
  have : Finite K := hK.to_subtype
  -- Each point of `K` lies over a point `q y` of `t`.
  choose q hqt hq using fun y : K ↦ y.property
  let ℓ (p : K × K) : t →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((B ((q p.1 : GroupLieAlgebra I G) - q p.2)).domRestrict t)
  have hℓ (p : K × K) (X : t) :
      ℓ p X = (coadjointRepresentation ℝ I G).orbitMap ν p.1 X -
        (coadjointRepresentation ℝ I G).orbitMap ν p.2 X := by
    simp [ℓ, hq]
  -- On `K`, the height of `X` is injective exactly when `ℓ p X ≠ 0` for every pair `p` of
  -- distinct points.
  have hinjOn (X : t) : InjOn (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) K ↔
      ∀ p ∈ {p : K × K | p.1 ≠ p.2}, ℓ p X ≠ 0 := by
    simp only [mem_ofPred_eq, hℓ, sub_ne_zero]
    refine ⟨fun h p hp heq ↦ hp (Subtype.ext (h p.1.property p.2.property heq)), fun h y hy y' hy'
      heq ↦ by_contra fun hne ↦ h (⟨y, hy⟩, ⟨y', hy'⟩) (fun h' ↦ hne (congrArg Subtype.val h'))
        heq⟩
  refine ⟨range (fun i ↦ LinearMap.toContinuousLinearMap (α i)) ∪ ℓ '' {p | p.1 ≠ p.2},
    (finite_range _).union ((toFinite _).image _), ?_, ?_⟩
  · rintro φ (⟨i, rfl⟩ | ⟨p, hp, rfl⟩)
    · simpa using hα i
    · -- Distinct points of the orbit lie over distinct points of `t`, and `B` is separating on `t`.
      have hne : (q p.1 : GroupLieAlgebra I G) - q p.2 ≠ 0 := by
        rw [sub_ne_zero]
        refine fun h ↦ hp (Subtype.ext ((coadjointRepresentation ℝ I G).orbitMap_injective ν ?_))
        rw [← hq, ← hq, h]
      obtain ⟨H, hH, hBH⟩ := hD.exists_mem_apply_ne_zero hB hsep hα
        (sub_mem (hqt p.1) (hqt p.2)) hne
      intro h0
      exact hBH (by simpa [ℓ] using congrArg (fun φ : t →L[ℝ] ℝ ↦ φ ⟨H, hH⟩) h0)
  · ext X
    simp only [mem_ofPred_eq, forall_mem_union, forall_mem_range, forall_mem_image]
    refine ⟨fun ⟨hX, hX'⟩ ↦ ⟨fun i ↦ by simpa using hX i, (hinjOn X).1 ?_⟩, fun ⟨hX, hX'⟩ ↦ ?_⟩
    · rwa [hD.criticalPoints_eq_preimage_orbitMap_coadjointRepresentation hB hsep hX] at hX'
    · have hX : ∀ i, α i X ≠ 0 := fun i ↦ by simpa using hX i
      refine ⟨hX, ?_⟩
      rw [hD.criticalPoints_eq_preimage_orbitMap_coadjointRepresentation hB hsep hX]
      exact (hinjOn X).2 hX'

/-- **Regular heights with distinct critical values form an open set.** In a root-plane
decomposition of the Lie algebra of a compact Lie group for a separating invariant form, the
regular elements `X ∈ t` whose height `f_X` takes pairwise distinct values at its critical points
on the coadjoint orbit of `ν` form an open subset of `t`. -/
theorem isOpen_setOf_injOn_orbitMap_coadjointRepresentation_apply [Finite ι] [CompactSpace G]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft) :
    IsOpen {X : t | (∀ i, α i X ≠ 0) ∧
      InjOn (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)
        (criticalPoints
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)} := by
  by_cases hα : ∀ i, α i ≠ 0
  · obtain ⟨s, hs, -, hseq⟩ := hD.exists_finite_setOf_injOn_eq (ν := ν) hB hsep hα
    rw [hseq, show {X : t | ∀ φ ∈ s, φ X ≠ 0} = ⋂ φ ∈ s, {X | φ X ≠ 0} by ext; simp]
    exact hs.isOpen_biInter fun φ _ ↦ isOpen_ne_fun φ.continuous continuous_const
  · -- A vanishing root leaves no regular element.
    obtain ⟨i, hi⟩ := not_forall_not.1 hα
    convert isOpen_empty using 1
    exact eq_empty_of_forall_notMem fun X ⟨hX, _⟩ ↦ hX i (by simp [hi])

/-- **Regular heights with distinct critical values are dense.** In a root-plane decomposition of
the Lie algebra of a compact Lie group for a separating invariant form, with nonzero roots, the
regular elements `X ∈ t` whose height `f_X` takes pairwise distinct values at its critical points
on the coadjoint orbit of `ν` are dense in `t`. They avoid finitely many hyperplanes of `t`: the
kernels of the roots and of the functionals `X ↦ B(q - q', X)` for the points `q ≠ q'` of `t` lying
under two critical points. -/
theorem dense_setOf_injOn_orbitMap_coadjointRepresentation_apply [Finite ι] [CompactSpace G]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft) (hα : ∀ i, α i ≠ 0) :
    Dense {X : t | (∀ i, α i X ≠ 0) ∧
      InjOn (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)
        (criticalPoints
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)} := by
  obtain ⟨s, hs, hs0, hseq⟩ := hD.exists_finite_setOf_injOn_eq (ν := ν) hB hsep hα
  have : Finite s := hs.to_subtype
  rw [hseq]
  simpa using ContinuousLinearMap.dense_setOf_forall_apply_ne_zero
    (f := fun φ : s ↦ (φ : t →L[ℝ] ℝ)) fun φ ↦ hs0 φ φ.property

/-- **Morse heights with distinct critical values in every open set.** In a root-plane
decomposition of the Lie algebra of a compact Lie group for a separating invariant form, with
nonzero roots, every nonempty open subset `U` of `t`, such as an open Weyl chamber, contains an
element `X` whose height `f_X` is a Morse function on the coadjoint orbit of `ν` taking pairwise
distinct values at its critical points. -/
theorem exists_mem_isMorse_and_injOn_orbitMap_coadjointRepresentation_apply [Finite ι]
    [CompactSpace G] (hD : IsRootPlaneDecomposition B t α F J)
    (hB : B.lieInvariant (GroupLieAlgebra I G)) (hsep : B.SeparatingLeft) (hα : ∀ i, α i ≠ 0)
    {U : Set t} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ X ∈ U,
      IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) ∧
      InjOn (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)
        (criticalPoints
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) := by
  obtain ⟨X, hXU, hX, hinj⟩ := Dense.inter_open_nonempty
    (hD.dense_setOf_injOn_orbitMap_coadjointRepresentation_apply (ν := ν) hB hsep hα) U hU hne
  exact ⟨X, hXU, hD.isMorse_orbitMap_coadjointRepresentation_apply hB hsep hX, hinj⟩

end TauCeti.IsRootPlaneDecomposition

namespace Module.Dual

/-- **Coadjoint orbits carry Morse heights with distinct critical values.** For a compact Lie
group `G` and `ν ∈ 𝔤*`, some height `f_X = ⟨μ, X⟩` is a Morse function on the coadjoint orbit
`G ⧸ G_ν` taking pairwise distinct values at its critical points. -/
theorem exists_isMorse_and_injOn_orbitMap_coadjointRepresentation_apply [CompactSpace G]
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    ∃ X : GroupLieAlgebra I G,
      IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) ∧
      InjOn (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)
        (criticalPoints
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) := by
  obtain ⟨B, t, r, α, F, J, hD, -, hB, hsep, X₀, hX₀⟩ :=
    exists_isRootPlaneDecomposition_groupLieAlgebra (I := I) (G := G)
  obtain ⟨X, -, hX⟩ := hD.exists_mem_isMorse_and_injOn_orbitMap_coadjointRepresentation_apply
    (ν := ν) hB hsep (fun i hi ↦ hX₀ i (by simp [hi])) isOpen_univ univ_nonempty
  exact ⟨X, hX⟩

end Module.Dual
