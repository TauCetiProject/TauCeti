/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Symplectic.Coadjoint.Height.RootPlane
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Perfect
import TauCeti.Algebra.Lie.InvariantForm.RootPlane.Decomposition
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.Geometry.Manifold.Morse.EulerCharacteristic
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
  (`Module.Dual.sum_bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard`), for
  instance the number of points of `O` lying over `t` for a regular `X ∈ t`;
* so is the Euler characteristic of `O`, since no index is odd
  (`Module.Dual.eulerChar_quotient_stabilizer_coadjointRepresentation_eq_ncard`);
* if `G` is connected, `O` is simply connected
  (`Module.Dual.simplyConnectedSpace_quotient_stabilizer_coadjointRepresentation`), since no
  height has a critical point of index one.

For instance, the flag manifolds `G/T` of compact connected Lie groups, the complex projective
spaces and the Grassmannians are coadjoint orbits. The points of `O` over `t` are counted by the
Weyl group in `TauCeti.Geometry.Symplectic.Coadjoint.Height.Weyl`, and the integral homology of `O`
is shown to be free and concentrated in even degrees in
`TauCeti.Geometry.Symplectic.Coadjoint.Height.Integral`.

## Main results

* `TauCeti.IsRootPlaneDecomposition.isMorse_orbitMap_coadjointRepresentation_apply`: the height of
  a regular element of `t` is a Morse function on every coadjoint orbit.
* `Module.Dual.exists_isMorse_orbitMap_coadjointRepresentation_apply`: a coadjoint orbit of a
  compact Lie group carries a Morse height.
* `Module.Dual.isPerfectMorse_orbitMap_coadjointRepresentation_apply`: Morse heights are perfect.
* `Module.Dual.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_zero_of_odd`: odd Betti
  numbers vanish.
* `Module.Dual.sum_bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard`: the total
  Betti number is the number of critical points of a Morse height.
* `Module.Dual.eulerChar_quotient_stabilizer_coadjointRepresentation_eq_ncard`: so is the Euler
  characteristic.
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
  isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type u} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-! ### Morse heights -/

namespace TauCeti.IsRootPlaneDecomposition

variable {ν : Module.Dual ℝ (GroupLieAlgebra I G)} {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {ι : Type*} {t : Submodule ℝ (GroupLieAlgebra I G)} {α : ι → Dual ℝ t}
  {F : ι → Submodule ℝ (GroupLieAlgebra I G)} {J : (i : ι) → Module.End ℝ (F i)} {X : t}

/-- **The height of a regular element of `t` is a Morse function.** In a root-plane decomposition of
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
`ν ∈ 𝔤*`, some height `f_X = ⟨μ, X⟩` is a Morse function on the coadjoint orbit `G ⧸ G_ν`. For
the height of a regular element of a root-plane decomposition, see
`TauCeti.IsRootPlaneDecomposition.isMorse_orbitMap_coadjointRepresentation_apply`. -/
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
  exact ν.isEquivariantMomentMap_coadjointOrbitForm.toIsMomentMap.even_manifoldMorseIndex
    ν.isSymplectic_coadjointOrbitForm.isNondegenerate
    (fun g ↦ (ν.isSymplecticMap_smul_coadjointOrbitForm g).apply) hx

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
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact ν.isEquivariantMomentMap_coadjointOrbitForm.toIsMomentMap.isPerfectMorse
    ν.isSymplectic_coadjointOrbitForm.isNondegenerate
    (fun g ↦ (ν.isSymplecticMap_smul_coadjointOrbitForm g).apply) k hX

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
          (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x = j}.ncard :=
  (ν.isPerfectMorse_orbitMap_coadjointRepresentation_apply k hX).bettiNumber_eq_ncard j

/-- **Odd Betti numbers of coadjoint orbits vanish.** For a coadjoint orbit `O` of a compact Lie
group, `bⱼ(O; k) = 0` for every odd `j` and every division ring `k`. -/
theorem bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_zero_of_odd {j : ℕ}
    (hj : Odd j) : bettiNumber k (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) j = 0 := by
  obtain ⟨X, hX⟩ := ν.exists_isMorse_orbitMap_coadjointRepresentation_apply
  exact hX.bettiNumber_eq_zero_of_odd
    (fun _ ↦ ν.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply) hj

/-- **The total Betti number of a coadjoint orbit.** For a Morse height `f_X` on a coadjoint orbit
`O` of a compact Lie group, the sum of the Betti numbers of `O` is the number of critical points of
`f_X`, for every division ring `k`. -/
theorem sum_bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard
    (hX : IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) :
    ∑ j ∈ Finset.range
        (finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) +
          1),
        bettiNumber k (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) j =
      (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)).ncard :=
  (ν.isPerfectMorse_orbitMap_coadjointRepresentation_apply k hX).sum_bettiNumber_eq_ncard

/-- **The Euler characteristic of a coadjoint orbit counts critical points.** For a Morse height
`f_X` on a coadjoint orbit `O` of a compact Lie group, `χ(O)` is the number of critical points of
`f_X`: all its Morse indices are even, so no critical point is counted negatively. -/
theorem eulerChar_quotient_stabilizer_coadjointRepresentation_eq_ncard
    [FiniteCWType (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)]
    (hX : IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) :
    eulerChar (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) =
      (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)).ncard :=
  hX.eulerChar_eq_ncard_criticalPoints_of_even fun _ ↦
    ν.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply

/-- **Coadjoint orbits of compact connected Lie groups are simply connected.** For a compact
connected Lie group `G` and `ν ∈ 𝔤*`, the coadjoint orbit `G ⧸ G_ν` is simply connected. -/
theorem simplyConnectedSpace_quotient_stabilizer_coadjointRepresentation [ConnectedSpace G] :
    SimplyConnectedSpace (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) := by
  have : ConnectedSpace (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
    QuotientGroup.mk_surjective.connectedSpace continuous_quot_mk
  -- A Morse height has no critical point of index one, as its indices are even, so it attaches
  -- no one-cell.
  obtain ⟨X, hX⟩ := ν.exists_isMorse_orbitMap_coadjointRepresentation_apply
  exact hX.simplyConnectedSpace_of_manifoldMorseIndex_ne_one hX.contMDiff.continuous.isProperMap
    (isCompact_range hX.contMDiff.continuous).bddBelow fun _ hp h1 ↦
      Nat.not_even_one (h1 ▸ ν.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply hp)

end Module.Dual
