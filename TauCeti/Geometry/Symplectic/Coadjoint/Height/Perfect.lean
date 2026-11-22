/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Height.RootPlane
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Perfect
import TauCeti.Algebra.Lie.InvariantForm.RootPlane.Decomposition
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.Geometry.Manifold.Morse.FundamentalGroup

/-!
# Betti numbers of coadjoint orbits of compact Lie groups

Let `G` be a compact Lie group with Lie algebra `𝔤 = GroupLieAlgebra I G`, let `ν ∈ 𝔤*`, and let
`O = G ⧸ G_ν` be its coadjoint orbit, with the Kirillov–Kostant–Souriau form and the orbit map
`μ : O → 𝔤*`, a moment map for the action of `G`. For `X ∈ 𝔤` the height `f_X = ⟨μ, X⟩` is a
component of `μ`. Following Bott, this file computes the Betti numbers of `O` from these heights.

* `𝔤` carries an `Ad`-invariant inner product `B`. For a maximal abelian subspace `t` of `𝔤`, the
  real root planes of `t` form a root-plane decomposition `𝔤 = t + Σ E_k`, and `t` contains a
  regular element `X`, at which no root vanishes
  (`TauCeti.exists_isRootPlaneDecomposition`). The height of a regular element is a Morse function
  on every coadjoint orbit
  (`TauCeti.IsRootPlaneDecomposition.isMorse_orbitMap_coadjointRepresentation_apply`), with
  critical points the points of the orbit lying over `t`. So every coadjoint orbit of a compact
  Lie group carries a Morse height
  (`Module.Dual.exists_isMorse_orbitMap_coadjointRepresentation_apply`).
* As a component of a moment map for a compact group acting by symplectomorphisms, a height has
  even Morse index at every critical point
  (`TauCeti.SmoothTwoForm.IsMomentMap.even_manifoldMorseIndex`).
  By the lacunary principle every Morse height is therefore a perfect Morse function, for every
  division ring of coefficients `k`
  (`Module.Dual.isPerfectMorse_orbitMap_coadjointRepresentation_apply`): the Betti number
  `bⱼ(O; k)` is the number of critical points of index `j`
  (`Module.Dual.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard`).

Hence, for every coadjoint orbit `O` of a compact Lie group and every division ring `k`:

* the odd Betti numbers of `O` vanish
  (`Module.Dual.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_zero_of_odd`);
* the sum of the Betti numbers of `O` is the number of critical points of any Morse height
  (`Module.Dual.sum_bettiNumber_quotient_stabilizer_coadjointRepresentation`), for instance the
  number of points of `O` lying over `t` for a regular `X ∈ t`;
* if `G` is connected, `O` is simply connected
  (`Module.Dual.simplyConnectedSpace_quotient_stabilizer_coadjointRepresentation`), since no
  height has a critical point of index one.

For instance, the flag manifolds `G/T` of compact connected Lie groups, the complex projective
spaces and the Grassmannians are coadjoint orbits. The identification of the points of `O` over
`t` with a Weyl group orbit `W ν`, and the freeness of the integral homology, which needs the
even-cell structure itself, are not proved here.

## Main results

* `TauCeti.IsRootPlaneDecomposition.isMorse_orbitMap_coadjointRepresentation_apply`: the height of
  a regular element of `t` is a Morse function on every coadjoint orbit.
* `Module.Dual.exists_isMorse_orbitMap_coadjointRepresentation_apply`: a coadjoint orbit of a
  compact Lie group carries a Morse height.
* `Module.Dual.isPerfectMorse_orbitMap_coadjointRepresentation_apply`: Morse heights are perfect.
* `Module.Dual.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_zero_of_odd`: odd Betti
  numbers vanish.
* `Module.Dual.sum_bettiNumber_quotient_stabilizer_coadjointRepresentation`: the total Betti number
  is the number of critical points of a Morse height.
* `Module.Dual.simplyConnectedSpace_quotient_stabilizer_coadjointRepresentation`: coadjoint orbits
  of compact connected Lie groups are simply connected.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II.
-/

public section

open Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

universe u

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type u} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-! ### Morse heights -/

namespace TauCeti.IsRootPlaneDecomposition

variable {ν : Module.Dual ℝ (GroupLieAlgebra I G)} {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {ι : Type*} {t : Submodule ℝ (GroupLieAlgebra I G)} {α : ι → Dual ℝ t}
  {F : ι → Submodule ℝ (GroupLieAlgebra I G)} {J : (i : ι) → Module.End ℝ (F i)} {X : t}

/-- **The height of a regular torus element is a Morse function.** In a root-plane decomposition of
`𝔤` for a separating invariant form `B`, if no root vanishes at `X ∈ t`, the height `f_X` is a
Morse function on every coadjoint orbit. -/
theorem isMorse_orbitMap_coadjointRepresentation_apply [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft) (hX : ∀ i, α i X ≠ 0) :
    IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X :=
  isMorseOn_univ.1 <| isMorseOn_iff_criticalPoints.2
    ⟨(ν.isEquivariantMomentMap_coadjointOrbitForm.contMDiff X).contMDiffOn, fun _ _ hx ↦
      hD.isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply hB hsep hX hx⟩

end TauCeti.IsRootPlaneDecomposition

namespace Module.Dual

variable (ν : Module.Dual ℝ (GroupLieAlgebra I G))

/-- **Coadjoint orbits of compact Lie groups carry Morse heights.** For a compact Lie group `G` and
`ν ∈ 𝔤*`, some height `f_X = ⟨μ, X⟩` is a Morse function on the coadjoint orbit `G ⧸ G_ν`: the
height of any regular element of a maximal abelian subspace of `𝔤`. -/
theorem exists_isMorse_orbitMap_coadjointRepresentation_apply [CompactSpace G] :
    ∃ X : GroupLieAlgebra I G,
      IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X := by
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  have : T2Space G := I.t2Space_of_lieGroup ∞
  obtain ⟨b, hsymm, hpos, hinv⟩ :=
    exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant (I := I) (G := G)
  -- An `Ad`-invariant inner product, and a regular element of a maximal abelian subspace for it.
  have hB : b.toBilinForm.lieInvariant (GroupLieAlgebra I G) :=
    lieInvariant_of_adjoint_invariant hinv
  have hsep : b.toBilinForm.SeparatingLeft := fun x hx ↦ by
    by_contra h
    exact (hpos x h).ne' (hx x)
  obtain ⟨t, r, α, F, J, hD, -, X, hX⟩ :=
    TauCeti.exists_isRootPlaneDecomposition (B := b.toBilinForm)
      (LinearMap.BilinForm.isSymm_def.2 hsymm) hpos hB
  exact ⟨X, hD.isMorse_orbitMap_coadjointRepresentation_apply hB hsep hX⟩

/-! ### Perfection and Betti numbers -/

/-- `G` acts on its coadjoint orbit by symplectomorphisms, read on tangent vectors. -/
private theorem eval₂_coadjointOrbitForm_mfderiv_smul (a : G)
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
    (u v : TangentSpace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) x) :
    ν.coadjointOrbitForm.eval₂ (a • x) (mfderiv _ _ (a • ·) x u) (mfderiv _ _ (a • ·) x v) =
      ν.coadjointOrbitForm.eval₂ x u v := by
  have h := congrArg (fun τ ↦ SmoothBundleForm.eval₂ τ x u v)
    (ν.mpullback_smul_coadjointOrbitForm a (ContMDiffSMul.contMDiff_const_smul (I := I) a))
  simpa only [SmoothForm.eval₂_mpullback] using h

variable [CompactSpace G] {X : GroupLieAlgebra I G}

/-- **Heights on coadjoint orbits have even Morse indices.** On a coadjoint orbit of a compact Lie
group, the Morse index of a height at each of its critical points is even, as for every component
of a moment map of a compact group acting by symplectomorphisms. -/
theorem even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply
    {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν}
    (hx : x ∈ criticalPoints
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) :
    Even (manifoldMorseIndex
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x) := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : IsClosed ((coadjointRepresentation ℝ I G).stabilizer ν : Set G) :=
    isClosed_stabilizer_coadjointRepresentation I ν
  exact ν.isEquivariantMomentMap_coadjointOrbitForm.toIsMomentMap.even_manifoldMorseIndex
    ν.isSymplectic_coadjointOrbitForm.isNondegenerate ν.eval₂_coadjointOrbitForm_mfderiv_smul hx

variable (k : Type u) [DivisionRing k]

/-- **Morse heights on coadjoint orbits are perfect.** On a coadjoint orbit of a compact Lie group,
every height which is a Morse function is a perfect Morse function, for every division ring of
coefficients: its Morse indices are even. -/
theorem isPerfectMorse_orbitMap_coadjointRepresentation_apply
    (hX : IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) :
    IsPerfectMorse
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) k
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : IsClosed ((coadjointRepresentation ℝ I G).stabilizer ν : Set G) :=
    isClosed_stabilizer_coadjointRepresentation I ν
  exact hX.isPerfectMorse_of_even fun _ ↦
    ν.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply

/-- **Betti numbers of a coadjoint orbit count critical points.** For a Morse height `f_X` on a
coadjoint orbit `O` of a compact Lie group, the Betti number `bⱼ(O; k)` is the number of critical
points of `f_X` of index `j`, for every division ring `k`. -/
theorem bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard
    (hX : IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) (j : ℕ) :
    bettiNumber k (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) j =
      {x ∈ criticalPoints
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) |
        manifoldMorseIndex
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x = j}.ncard := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : IsClosed ((coadjointRepresentation ℝ I G).stabilizer ν : Set G) :=
    isClosed_stabilizer_coadjointRepresentation I ν
  have hc := (ν.isPerfectMorse_orbitMap_coadjointRepresentation_apply k hX).criticalCount_eq j
  rw [criticalCount_def,
    ← (hX.finite_criticalPoints.subset (Set.sep_subset _ _)).cast_ncard_eq] at hc
  rw [bettiNumber_def]
  exact_mod_cast hc.symm

/-- **Odd Betti numbers of coadjoint orbits vanish.** For a coadjoint orbit `O` of a compact Lie
group, `bⱼ(O; k) = 0` for every odd `j` and every division ring `k`. -/
theorem bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_zero_of_odd {j : ℕ}
    (hj : Odd j) : bettiNumber k (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) j = 0 := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : IsClosed ((coadjointRepresentation ℝ I G).stabilizer ν : Set G) :=
    isClosed_stabilizer_coadjointRepresentation I ν
  obtain ⟨X, hX⟩ := ν.exists_isMorse_orbitMap_coadjointRepresentation_apply
  exact hX.bettiNumber_eq_zero_of_odd
    (fun _ ↦ ν.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply) hj

/-- **The total Betti number of a coadjoint orbit.** For a Morse height `f_X` on a coadjoint orbit
`O` of a compact Lie group, the sum of the Betti numbers of `O` is the number of critical points of
`f_X`, for every division ring `k`. -/
theorem sum_bettiNumber_quotient_stabilizer_coadjointRepresentation
    (hX : IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) :
    ∑ j ∈ Finset.range
        (finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) +
          1),
        bettiNumber k (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) j =
      (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)).ncard := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : IsClosed ((coadjointRepresentation ℝ I G).stabilizer ν : Set G) :=
    isClosed_stabilizer_coadjointRepresentation I ν
  have hs := (ν.isPerfectMorse_orbitMap_coadjointRepresentation_apply k hX
    ).sum_bettiNumber_eq_totalCriticalCount
  rw [totalCriticalCount_def, ← hX.finite_criticalPoints.cast_ncard_eq] at hs
  exact_mod_cast hs

/-- **Coadjoint orbits of compact connected Lie groups are simply connected.** No height has a
critical point of index one, as its indices are even, so a Morse height attaches no one-cell. -/
theorem simplyConnectedSpace_quotient_stabilizer_coadjointRepresentation [ConnectedSpace G] :
    SimplyConnectedSpace (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : IsClosed ((coadjointRepresentation ℝ I G).stabilizer ν : Set G) :=
    isClosed_stabilizer_coadjointRepresentation I ν
  have : ConnectedSpace (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
    QuotientGroup.mk_surjective.connectedSpace continuous_quot_mk
  obtain ⟨X, hX⟩ := ν.exists_isMorse_orbitMap_coadjointRepresentation_apply
  exact hX.simplyConnectedSpace_of_manifoldMorseIndex_ne_one hX.contMDiff.continuous.isProperMap
    (isCompact_range hX.contMDiff.continuous).bddBelow fun _ hp h1 ↦
      Nat.not_even_one (h1 ▸ ν.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply hp)

end Module.Dual
