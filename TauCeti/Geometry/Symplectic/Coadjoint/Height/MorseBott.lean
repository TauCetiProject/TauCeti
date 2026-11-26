/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Degenerate
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.MorseBott

/-!
# The critical orbits of a height are Morse–Bott submanifolds

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱`, let `B` be an
`Ad`-invariant bilinear form on `𝔤` with trivial left radical, and let `O = G ⧸ G_ν` be the
coadjoint orbit of `ν = B (e μ)` for `μ ∈ 𝔱`, with orbit map `Φ`. For `X ∈ 𝔱` the critical set of
the height `f_X(x) = Φ x (e X)` is the union of the finitely many orbits of the adjoint stabilizer
`Z_G(X)` through the Weyl group points
(`TauCeti.Lie.criticalPoints_eq_iUnion_orbit_normalizerQuotientToCoadjointOrbit`,
`TauCeti.Lie.finite_image_orbit_criticalPoints`). This file shows that each of these orbits is a
**Morse–Bott critical submanifold** of `f_X`: an embedded submanifold of critical points along
which the kernel of the Hessian of `f_X` is exactly the tangent space
(`TauCeti.Lie.exists_isNondegenerateCriticalSubmanifold_orbit_stabilizer`). Its tangent space at
each point is the space of tangent vectors fixed by the closure `T_X` of `{exp (t X) | t ∈ ℝ}`.

No regularity of `X` is assumed. For regular `X` the orbits are the Weyl group points and `f_X` is
a Morse function, while for `X = 0` the height is constant and its only critical orbit is the whole
of `O`. For instance, on the full flag manifold of `U(3)` and `X = diag(i, i, 0)`, the critical set
consists of three copies of `ℂP¹`, orbits of `Z_G(X) = U(2) × U(1)`.

The height `f_X` is the component along `e X` of the moment map `Φ` of the action of `G` on `O`,
and `Z_G(X)` is a closed subgroup of `G` commuting with `T_X`: it is the centralizer of `T_X`
(`stabilizer_continuousAdjointRepresentation_eq_centralizer_closedOneParameterSubgroup`, in the
`TauCeti.Lie` namespace). The statement is therefore the case of the coadjoint orbit and its
Kirillov–Kostant–Souriau form of the fact that the finitely many orbits of such a subgroup on the
critical set of a moment map component are Morse–Bott critical submanifolds
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_isNondegenerateCriticalSubmanifold_orbit`).

## Main results

* `TauCeti.Lie.exists_isNondegenerateCriticalSubmanifold_orbit_stabilizer`: the `Z_G(X)`-orbit of
  a critical point of `f_X` is a Morse–Bott critical submanifold of `f_X`.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* J. J. Duistermaat, J. A. C. Kolk and V. S. Varadarajan, *Functions, flows and oscillatory
  integrals on flag manifolds and conjugacy classes in real semisimple Lie groups*, Compositio
  Math. 49 (1983), 309–398, Section 3.
-/

public section

noncomputable section

open Function Module Manifold Set TopologicalSpace Topology TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G] {T : Subgroup G} [IsMulCommutative T]
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}

/-- **The critical orbits of a height are Morse–Bott critical submanifolds.** Let `T` be a maximal
torus of a compact Lie group, `B` an invariant form with trivial left radical, and `μ`, `X` in the
Lie algebra `𝔱` of `T`. Let `p` be a critical point of the height `f_X` on the coadjoint orbit `O`
of `B (e μ)`, let `d` be the dimension of the space of tangent vectors at `p` fixed by the closure
`T_X` of `{exp (t X) | t ∈ ℝ}`, and let `L` be a subspace of the model of `O` of dimension `d`.
Then the part `O^{T_X}_d` of the fixed set of `T_X` is a smooth manifold modelled on `L` whose
inclusion into `O` is a smooth embedding, the orbit of `p` under the adjoint stabilizer `Z_G(X)` is
an open subset `U` of `O^{T_X}_d`, and the inclusion of `U` into `O` is a nondegenerate critical
submanifold of `f_X`, whose tangent space at each point is the space of tangent vectors fixed by
`T_X`. -/
theorem exists_isNondegenerateCriticalSubmanifold_orbit_stabilizer (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {p : G ⧸ (coadjointRepresentation ℝ I G).stabilizer
      (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint μ))}
    (hp : p ∈ criticalPoints
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))))
      (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ)) y
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint X)))
    {d : ℕ} (hd : finrank ℝ (fixedTangentSubspace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))))
      (closedOneParameterSubgroup (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
        (G := G) BoundarylessManifold.isInteriorPoint X)) p) = d)
    {L : Submodule ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
      (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint μ))))}
    (hL : finrank ℝ L = d) :
    ∃ (_ : ChartedSpace L (fixedPointsOfFinrank
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (closedOneParameterSubgroup (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
          (G := G) BoundarylessManifold.isInteriorPoint X))
        (G ⧸ (coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))) d))
      (_ : IsManifold 𝓘(ℝ, L) ∞ (fixedPointsOfFinrank
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (closedOneParameterSubgroup (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
          (G := G) BoundarylessManifold.isInteriorPoint X))
        (G ⧸ (coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))) d))
      (hi : IsSmoothEmbedding 𝓘(ℝ, L)
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)))) ∞
        (Subtype.val : fixedPointsOfFinrank
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ))))
          (closedOneParameterSubgroup (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
            (G := G) BoundarylessManifold.isInteriorPoint X))
          (G ⧸ (coadjointRepresentation ℝ I G).stabilizer
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ))) d → _))
      (U : Opens (fixedPointsOfFinrank
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (closedOneParameterSubgroup (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
          (G := G) BoundarylessManifold.isInteriorPoint X))
        (G ⧸ (coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))) d)),
      range (Subtype.val ∘ (Subtype.val : U → _)) =
          MulAction.orbit
            ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
              (X : LeftInvariantDerivation I G)) p ∧
        SmoothEmbedding.IsNondegenerateCriticalSubmanifold
          ((SmoothEmbedding.ofIsSmoothEmbedding _ hi).compLocalDiffeomorph (Subtype.val : U → _)
            isLocalDiffeomorph_subtype_val IsEmbedding.subtypeVal)
          (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ)) y
            (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint X)) ∧
        ∀ y : U, LinearMap.range (mfderiv 𝓘(ℝ, L)
            𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
              (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
                BoundarylessManifold.isInteriorPoint μ))))
            (Subtype.val ∘ (Subtype.val : U → _)) y).toLinearMap =
          fixedTangentSubspace
            𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
              (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
                BoundarylessManifold.isInteriorPoint μ))))
            (closedOneParameterSubgroup (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
              (G := G) BoundarylessManifold.isInteriorPoint X))
            ((Subtype.val ∘ (Subtype.val : U → _)) y) :=
  -- `Z_G(X)` is a closed subgroup commuting with `T_X`, with finitely many critical orbits.
  (Dual.isEquivariantMomentMap_coadjointOrbitForm (B (leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := I) (G := G) BoundarylessManifold.isInteriorPoint μ))).toIsMomentMap
    |>.exists_isNondegenerateCriticalSubmanifold_orbit
      (Dual.isSymplectic_coadjointOrbitForm (B (leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := I) (G := G) BoundarylessManifold.isInteriorPoint μ))).isNondegenerate
      (isClosed_stabilizer_continuousAdjointRepresentation (X : LeftInvariantDerivation I G))
      (stabilizer_continuousAdjointRepresentation_eq_centralizer_closedOneParameterSubgroup
        (X : LeftInvariantDerivation I G)).le
      (finite_image_orbit_criticalPoints hT hB hsep μ X) hp hd hL

end TauCeti.Lie
