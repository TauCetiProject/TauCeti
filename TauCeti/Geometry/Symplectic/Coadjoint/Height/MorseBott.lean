/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Degenerate
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.MorseBott
import TauCeti.Geometry.Lie.Adjoint.Representation.Stabilizer
import TauCeti.Geometry.Lie.Subgroup.Torus.Stabilizer
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Critical orbits of heights on coadjoint orbits are Morse–Bott

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱`, let `B` be an
`Ad`-invariant bilinear form on `𝔤` with trivial left radical, and let `O = G ⧸ G_ν` be the
coadjoint orbit of `ν = B (e μ)` for `μ ∈ 𝔱`, with its Kirillov–Kostant–Souriau form and orbit map
`Φ`. For `X ∈ 𝔱` the height `f_X(x) = Φ x (e X)` is a component of the moment map `Φ`. Its
critical set is the finite union of the orbits `Z_G(X) · [n_w]` of the Weyl group points under the
adjoint stabilizer `Z_G(X) = {k | Ad_k X = X}`
(`TauCeti.Lie.criticalPoints_eq_iUnion_orbit_normalizerQuotientToCoadjointOrbit`), indexed by the
double cosets `W_X \ W / W_μ`. For a degenerate `X`, for instance `X = 0` or `X` on a wall, these
orbits have positive dimension. This file proves that each of them is a Morse–Bott critical
submanifold of `f_X`.

* **The critical orbits are open and closed in the critical set**
  (`TauCeti.Lie.isClopen_preimage_val_orbit_criticalPoints`). Each orbit is compact, as the image
  of the closed subgroup `Z_G(X)` of the compact group `G`, and the critical set is the union of
  finitely many of them (`TauCeti.Lie.finite_image_orbit_criticalPoints`), so the complement of
  one orbit in the critical set is closed. When `G` is connected, so is `Z_G(X)`
  (`TauCeti.Lie.isConnected_stabilizer_adjointRepresentation`), and the critical orbits are then
  exactly the connected components of the critical set
  (`TauCeti.Lie.orbit_eq_connectedComponentIn_criticalPoints`).
* **The critical orbits are Morse–Bott**
  (`TauCeti.Lie.exists_isNondegenerateCriticalSubmanifold_orbit_criticalPoints`). The critical
  set of the moment map component `f_X` is the fixed set `O^{T_X}` of the closure
  `T_X = closure {exp (t X) | t ∈ ℝ}`, and a part of `O^{T_X}` which is open in it and on which the
  fixed tangent subspace of `T_X` has constant dimension is a nondegenerate critical submanifold
  of `f_X`, by
  `exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank_of_compactSpace`
  in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`. An element `k` of `Z_G(X)` commutes with
  `T_X` (`TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup`),
  so the diffeomorphism `k •` of `O` preserves the dimension of the fixed tangent subspaces
  (`Diffeomorph.apply_mem_fixedPointsOfFinrank_iff`), which is therefore constant on each critical
  orbit. So each critical orbit is a smooth manifold whose inclusion into `O` is a smooth embedding,
  whose tangent spaces are the fixed tangent subspaces of `T_X`, and along which the kernel of the
  Hessian of `f_X` is exactly the tangent space.

For `X = 0` the stabilizer `Z_G(X)` is all of `G`, the height is constant and the whole orbit `O`
is a single critical orbit. For a regular `X` the critical orbits are the Weyl group points, and
the Morse–Bott condition is the Morse condition
(`TauCeti.IsRootPlaneDecomposition.isMorse_orbitMap_coadjointRepresentation_apply`). On the full
flag manifold of `U(3)` and `X = diag(i, i, 0)` there are `|S₂ \ S₃| = 3` critical orbits, each a
copy of `ℂP¹`.

## Main results

* `TauCeti.Lie.orbit_subset_criticalPoints`: `Z_G(X)` preserves the critical set of `f_X`.
* `TauCeti.Lie.isClopen_preimage_val_orbit_criticalPoints`: the `Z_G(X)`-orbit of a critical
  point of `f_X` is open and closed in the critical set.
* `TauCeti.Lie.orbit_eq_connectedComponentIn_criticalPoints`: for a connected group, the
  `Z_G(X)`-orbits of critical points are the connected components of the critical set.
* `TauCeti.Lie.exists_isNondegenerateCriticalSubmanifold_orbit_criticalPoints`: the `Z_G(X)`-orbit
  of a critical point of `f_X` is a Morse–Bott critical submanifold of `f_X`.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* J. J. Duistermaat, J. A. C. Kolk and V. S. Varadarajan, *Functions, flows and oscillatory
  integrals on flag manifolds and conjugacy classes in real semisimple Lie groups*, Compositio
  Math. 49 (1983), 309–398, Section 3.
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the components of the moment map are Morse–Bott functions).
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  ContMDiffMul.boundarylessManifold isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {T : Subgroup G} [IsMulCommutative T] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}

/-- **The adjoint stabilizer preserves the critical set of a height.** Let `T` be a maximal torus
of a compact Lie group, `B` an invariant form with trivial left radical, and `μ`, `X` in the Lie
algebra `𝔱` of `T`. The orbit of a critical point of the height `f_X` on the coadjoint orbit of
`B (e μ)` under the adjoint stabilizer `Z_G(X)` consists of critical points. -/
theorem orbit_subset_criticalPoints [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer
      (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint μ))}
    (hx : x ∈ criticalPoints
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))))
      (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ)) y
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint X))) :
    MulAction.orbit
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)) x ⊆
      criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X)) := by
  -- The critical set is a union of orbits, one of which is the orbit of `x`.
  rw [criticalPoints_eq_iUnion_orbit_normalizerQuotientToCoadjointOrbit hT hB hsep μ
    X.property] at hx ⊢
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
  rw [MulAction.orbit_eq_iff.2 hw]
  exact Set.subset_iUnion
    (fun w ↦ MulAction.orbit _ (normalizerQuotientToCoadjointOrbit B hB μ w)) w

/-- **The critical orbits of a height are open and closed in its critical set.** Let `T` be a
maximal torus of a compact Lie group, `B` an invariant form with trivial left radical, and `μ`,
`X` in the Lie algebra `𝔱` of `T`. The orbit of a critical point of the height `f_X` on the
coadjoint orbit of `B (e μ)` under the adjoint stabilizer `Z_G(X)` is open and closed in the
critical set of `f_X`. -/
theorem isClopen_preimage_val_orbit_criticalPoints [CompactSpace G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (x : criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X))) :
    IsClopen ((↑) ⁻¹' MulAction.orbit
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)) (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ))) :
      Set (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X)))) := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- The critical set is the union of finitely many orbits of `Z_G(X)`, which are compact since
  -- `Z_G(X)` is a closed subgroup of the compact group `G`.
  have := isCompact_iff_compactSpace.1 (isClosed_stabilizer_continuousAdjointRepresentation
    (X : LeftInvariantDerivation I G)).isCompact
  exact isClopen_preimage_val_orbit_of_finite (finite_image_orbit_criticalPoints hT hB hsep μ X)
    (fun y _ ↦ (isCompact_orbit y).isClosed) x

/-- **The critical orbits of a height are the connected components of its critical set.** Let `T`
be a maximal torus of a compact connected Lie group, `B` an invariant form with trivial left
radical, and `μ`, `X` in the Lie algebra `𝔱` of `T`. The orbit of a critical point `x` of the
height `f_X` on the coadjoint orbit of `B (e μ)` under the adjoint stabilizer `Z_G(X)` is the
connected component of `x` in the critical set of `f_X`. -/
theorem orbit_eq_connectedComponentIn_criticalPoints [CompactSpace G] [ConnectedSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer
      (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint μ))}
    (hx : x ∈ criticalPoints
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))))
      (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ)) y
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint X))) :
    MulAction.orbit
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)) x =
      connectedComponentIn (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ))))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y
          (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint X))) x := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  refine subset_antisymm ?_ ?_
  · -- The orbit of the connected group `Z_G(X)` is a connected set of critical points.
    have hZ : IsConnected
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G) : Set G) := by
      rw [stabilizer_continuousAdjointRepresentation_eq_stabilizer_adjointRepresentation]
      exact isConnected_stabilizer_adjointRepresentation _
    have := Subtype.connectedSpace hZ
    exact (isConnected_range (continuous_subtypeVal.smul continuous_const)).isPreconnected
      |>.subset_connectedComponentIn (MulAction.mem_orbit_self x)
        (orbit_subset_criticalPoints hT hB hsep μ X hx)
  · -- The orbit is open and closed in the critical set, so it contains the component of `x`.
    rw [connectedComponentIn_eq_image hx]
    rintro _ ⟨y, hy, rfl⟩
    exact (isClopen_preimage_val_orbit_criticalPoints hT hB hsep μ X ⟨x, hx⟩)
      |>.connectedComponent_subset (MulAction.mem_orbit_self x) hy

/-- **The critical orbits of a height are Morse–Bott.** Let `T` be a maximal torus of a compact
Lie group, `B` an invariant form with trivial left radical, and `μ`, `X` in the Lie algebra `𝔱` of
`T`, and let `x` be a critical point of the height `f_X` on the coadjoint orbit of `B (e μ)`. For
every subspace `L` of the model whose dimension is that of the tangent vectors at `x` fixed by
the closure `T_X` of `{exp (t X) | t ∈ ℝ}`, the orbit of `x` under the adjoint stabilizer
`Z_G(X)` is a smooth manifold modelled on `L` whose inclusion into the coadjoint orbit is a smooth
embedding and a nondegenerate critical submanifold of `f_X`, with tangent image at each point the
fixed tangent subspace of `T_X`. -/
theorem exists_isNondegenerateCriticalSubmanifold_orbit_criticalPoints [CompactSpace G]
    [IsTopologicalGroup G] (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (μ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer
      (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint μ))}
    (hx : x ∈ criticalPoints
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))))
      (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ)) y
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint X)))
    {L : Submodule ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
      (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint μ))))}
    (hL : Module.finrank ℝ L = Module.finrank ℝ (fixedTangentSubspace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))))
      (closedOneParameterSubgroup (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint X)) x)) :
    ∃ C : ChartedSpace L (MulAction.orbit
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)) x), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (MulAction.orbit
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)) x) ∧
        ∃ hi : IsSmoothEmbedding 𝓘(ℝ, L)
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
            (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
              BoundarylessManifold.isInteriorPoint μ)))) ∞
          (Subtype.val : MulAction.orbit
            ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
              (X : LeftInvariantDerivation I G)) x →
            G ⧸ (coadjointRepresentation ℝ I G).stabilizer
              (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
                BoundarylessManifold.isInteriorPoint μ))),
          (SmoothEmbedding.ofIsSmoothEmbedding _ hi).IsNondegenerateCriticalSubmanifold
              (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap
                (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
                  BoundarylessManifold.isInteriorPoint μ)) y
                (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
                  BoundarylessManifold.isInteriorPoint X)) ∧
            ∀ y : MulAction.orbit
                ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
                  (X : LeftInvariantDerivation I G)) x,
              LinearMap.range (mfderiv 𝓘(ℝ, L)
                𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
                  (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
                    BoundarylessManifold.isInteriorPoint μ)))) Subtype.val y).toLinearMap =
                fixedTangentSubspace
                  𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
                    (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
                      BoundarylessManifold.isInteriorPoint μ))))
                  (closedOneParameterSubgroup (leftInvariantDerivationLieEquivGroupLieAlgebra
                    (I := I) (G := G) BoundarylessManifold.isInteriorPoint X))
                  (y : G ⧸ (coadjointRepresentation ℝ I G).stabilizer
                    (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
                      BoundarylessManifold.isInteriorPoint μ))) := by
  have hopen := (isClopen_preimage_val_orbit_criticalPoints hT hB hsep μ X ⟨x, hx⟩).isOpen
  set ν := B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint μ)
  set ξ := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint X
  have h := (Module.Dual.isEquivariantMomentMap_coadjointOrbitForm ν).toIsMomentMap
  have hσ := (Module.Dual.isSymplectic_coadjointOrbitForm ν).isNondegenerate
  have hcrit := h.criticalPoints_eq_fixedPoints hσ ξ
  have : ContMDiffConstSMul 𝓘(ℝ, Subgroup.QuotientModelSpace I
      ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞ G
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
    ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
  refine h.exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank_of_compactSpace
    hσ hL ?_ ?_
  · -- An element `k` of `Z_G(X)` commutes with `T_X`, so `k •` preserves the dimension of the
    -- fixed tangent subspaces of `T_X`, which is therefore constant on the orbit.
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    rw [stabilizer_continuousAdjointRepresentation_eq_stabilizer_adjointRepresentation,
      stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup] at hk
    have hkx := ((Diffeomorph.constSmul 𝓘(ℝ, Subgroup.QuotientModelSpace I
      ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞ k).apply_mem_fixedPointsOfFinrank_iff
      (by simp) fun g ↦ .of_forall fun y ↦ by
        simp only [Function.comp_apply, Diffeomorph.constSmul_apply, Subgroup.smul_def, smul_smul,
          Subgroup.mem_centralizer_iff.1 hk g g.property]).2
      (mem_fixedPointsOfFinrank.2 ⟨hcrit ▸ hx, rfl⟩)
    rwa [Diffeomorph.constSmul_apply] at hkx
  · -- The orbit is open in the critical set, the fixed set of `T_X`.
    rwa [← hcrit]

end TauCeti.Lie
