/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
public import TauCeti.AlgebraicTopology.Sphere.PointedMap
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.EilenbergMacLane
public import TauCeti.Geometry.Lie.Adjoint.Compact
public import TauCeti.Geometry.Lie.CartanThreeForm
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Classification
public import TauCeti.Geometry.Lie.Exponential.Commute
public import TauCeti.Geometry.Lie.Integration
public import TauCeti.Geometry.Lie.ModelTransport
public import TauCeti.RepresentationTheory.SU2.LieGroup
import TauCeti.Analysis.Complex.Circle.Torsion

/-!
# The torus criterion for compact Lie groups

A compact connected Lie group is aspherical exactly when it is a torus `(S¹)ʳ`
(`TauCeti.Lie.isAspherical_iff_exists_continuousMulEquiv_torus`).

A torus is aspherical, so the content is the converse. It rests on a homomorphism detected by the
Cartan three-form. Let `G` be a compact Lie group whose Lie algebra `𝔤` is not abelian. Then `𝔤`
contains a copy of `so(3) ≅ 𝔰𝔲(2)` (`TauCeti.Lie.exists_injective_lieHom_soThree_of_compactSpace`).
Since `SU(2)` is simply connected, the inclusion `𝔰𝔲(2) → 𝔤` integrates to a smooth homomorphism
`φ : SU(2) → G` (`LieHom.integrate`) with injective differential. Transport a positive-definite
invariant form of `𝔤` to the tangent space at the identity. Its Cartan three-form
`B(·, ⁅·, ·⁆)` pulls back along `dφ` to a nonzero form on the three-dimensional `𝔰𝔲(2)`: on
`y, z` with `⁅y, z⁆ = x ≠ 0` it takes the value `B(dφ x, dφ x) > 0`. So `φ` is not null-homotopic
(`ContMDiffMonoidMorphism.not_nullhomotopic_of_lie_eq_of_apply_ne_zero`,
`TauCeti.Lie.exists_not_nullhomotopic_of_not_isLieAbelian`).

Since `SU(2)` is the three-sphere (`TauCeti.SU2.homeomorphSphere`), `φ` is a map `S³ → G` that is
not null-homotopic. So `π₃(G)` is nontrivial, and `G` is not aspherical
(`TauCeti.Lie.not_isAspherical_of_not_isLieAbelian`). Conversely, the Lie algebra of an aspherical
compact Lie group is abelian. If `G` is moreover connected, it is then commutative, and so a
torus (`TauCeti.nonempty_continuousMulEquiv_pi_circle`).

This route detects a copy of `SU(2)` inside `G` directly. It does not pass through the finite
covering `T × K → G` by a torus and a simply connected semisimple group.

The Lie group structure is needed. The product `ℕ → S¹` of countably many circles is a compact
connected commutative topological group, and it is aspherical, but it is not a torus: it has
infinitely many elements of order two, while `(S¹)ʳ` has only finitely many
(`Circle.not_exists_continuousMulEquiv_pi_fin`). So the criterion fails for it
(`TauCeti.Lie.not_forall_isAspherical_iff_exists_continuousMulEquiv_torus`).

The integration of Lie-algebra homomorphisms (`LieHom.integrate`) is available for Lie groups
modelled without boundary on a finite-dimensional space in the lowest universe, so the statement
about `SU(2) → G` carries these hypotheses. The later statements hold for every model with
corners on such a space: a Lie group is also a Lie group modelled on the vector space itself,
with the same topology, group and Lie algebra (`TauCeti.BoundarylessModel.interiorLieEquiv`). As
for `TauCeti.SU2.embeddedLieSubgroupData`, `GL(2, ℂ)` carries the operator-norm topology of
matrices.

## Main results

* `TauCeti.Lie.exists_not_nullhomotopic_of_not_isLieAbelian`: a compact Lie group with
  non-abelian Lie algebra receives a smooth homomorphism from `SU(2)` that is not
  null-homotopic.
* `TauCeti.Lie.not_isAspherical_of_not_isLieAbelian`: a compact Lie group with non-abelian Lie
  algebra is not aspherical.
* `TauCeti.Lie.isLieAbelian_of_isAspherical`: an aspherical compact Lie group has abelian Lie
  algebra.
* `TauCeti.Lie.isMulCommutative_of_isAspherical`: an aspherical compact connected Lie group is
  commutative.
* `TauCeti.Lie.isAspherical_iff_exists_continuousMulEquiv_torus`: **the torus criterion**.
* `TauCeti.Lie.not_forall_isAspherical_iff_exists_continuousMulEquiv_torus`: the criterion fails
  for the compact connected group `ℕ → S¹`, which is not a Lie group.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and the proof of
  Proposition 6.31).
* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, §1.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter V.
-/

public section

noncomputable section

open Metric LieAlgebra
open scoped ContDiff Manifold

namespace TauCeti

namespace Lie

-- Use the operator-norm topology under which `GL(2, ℂ)` is a Lie group, as in
-- `TauCeti.RepresentationTheory.SU2.LieGroup`.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

open scoped Matrix.Norms.Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [TopologicalSpace G] [Group G] [CompactSpace G]

/-- **A compact Lie group with non-abelian Lie algebra receives an essential `SU(2)`.** If the Lie
algebra of a compact Lie group `G` is not abelian, some smooth homomorphism `SU(2) → G` is not
null-homotopic. It integrates an injective homomorphism `𝔰𝔲(2) ≅ so(3) → 𝔤`, and the Cartan
three-form of a positive-definite invariant form of `𝔤` detects it. -/
theorem exists_not_nullhomotopic_of_not_isLieAbelian {H : Type} [TopologicalSpace H]
    [ChartedSpace H G] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [LieGroup I ∞ G]
    (hG : ¬IsLieAbelian (LeftInvariantDerivation I G)) :
    ∃ φ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
        (GLSpecialUnitary (Fin 2) ℂ) G,
      ¬(φ : C(GLSpecialUnitary (Fin 2) ℂ, G)).Nullhomotopic := by
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology G := ChartedSpace.secondCountable_of_sigmaCompact H G
  obtain ⟨f, hf⟩ := exists_injective_lieHom_soThree_of_compactSpace (I := I) (G := G) hG
  let ψ := f.comp (suTwoLieEquivSoThree.toLieHom.comp SU2.nativeLieEquiv.toLieHom)
  have hψ : Function.Injective ψ :=
    hf.comp (suTwoLieEquivSoThree.injective.comp SU2.nativeLieEquiv.injective)
  refine ⟨ψ.integrate, ?_⟩
  obtain ⟨B, hinv, -, hpos, -⟩ :=
    exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  -- The Lie algebras as tangent spaces at the identity, where the Cartan three-form lives.
  let eG := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)
  let eK := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule)) (G := GLSpecialUnitary (Fin 2) ℂ)
    (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)
  let B' : LinearMap.BilinForm ℝ (GroupLieAlgebra I G) :=
    B.compl₁₂ eG.symm.toLinearEquiv.toLinearMap eG.symm.toLinearEquiv.toLinearMap
  -- Two elements of `𝔰𝔲(2)` with nonzero bracket: `-iσ₂/2` and `-iσ₃/2`, whose bracket is `-iσ₁/2`.
  let Y := SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 1 1))
  let Z := SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 2 1))
  have hYZ : ⁅Y, Z⁆ ≠ 0 := by
    rw [← LieEquiv.map_lie, lie_suTwoEquiv]
    refine (map_ne_zero_iff _ SU2.nativeLieEquiv.symm.injective).mpr
      ((map_ne_zero_iff _ suTwoEquiv.injective).mpr fun h ↦ ?_)
    have h0 := congrFun h 0
    simp [cross_apply] at h0
  refine ψ.integrate.not_nullhomotopic_of_lie_eq_of_apply_ne_zero SU2.finrank_lieAlgebra B'
    (fun x y z ↦ ?_) (x := eK ⁅Y, Z⁆) (y := eK Y) (z := eK Z) (LieEquiv.map_lie _ _ _).symm ?_
  · simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv,
      LieEquiv.map_lie]
    exact hinv _ _ _
  · -- The differential of `ψ.integrate` is `ψ`, read in the tangent spaces at the identity.
    have hmap : ψ.integrate.toMonoidHom.groupLieAlgebraMap _ I (eK ⁅Y, Z⁆) = eG (ψ ⁅Y, Z⁆) := by
      have h := leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap ψ.integrate ⁅Y, Z⁆
      rw [LieHom.lieMap_integrate] at h
      rw [MonoidHom.groupLieAlgebraMap_apply]
      exact h.symm
    rw [hmap]
    simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv,
      LieEquiv.symm_apply_apply]
    exact (hpos _ ((map_ne_zero_iff ψ hψ).mpr hYZ)).ne'

variable {H : Type*} [TopologicalSpace H] [ChartedSpace H G]

section Transport

attribute [local instance] BoundarylessModel.interiorChartedSpace

/-- **A compact Lie group with non-abelian Lie algebra is not aspherical.** Read on a
boundaryless model, it receives a homomorphism from `SU(2) ≅ S³` that is not null-homotopic
(`TauCeti.Lie.exists_not_nullhomotopic_of_not_isLieAbelian`), so its third homotopy group is
nontrivial. -/
theorem not_isAspherical_of_not_isLieAbelian {I : ModelWithCorners ℝ E H} [LieGroup I ∞ G]
    (hG : ¬IsLieAbelian (LeftInvariantDerivation I G)) (g : G) : ¬IsAspherical G g := by
  intro hasph
  -- Pass to the copy of `G` modelled on `E`, whose Lie algebra is that of `G`.
  have hG' : ¬IsLieAbelian (LeftInvariantDerivation 𝓘(ℝ, E) (BoundarylessModel I G)) :=
    fun h ↦ hG ((BoundarylessModel.interiorLieEquiv I (M := G)).injective.isLieAbelian h)
  obtain ⟨φ, hφ⟩ := exists_not_nullhomotopic_of_not_isLieAbelian hG'
  -- Read `φ` as a map out of `S³`; it is null-homotopic since `π₃` vanishes.
  let f : C(sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, BoundarylessModel I G) :=
    (φ : C(GLSpecialUnitary (Fin 2) ℂ, BoundarylessModel I G)).comp
      ⟨SU2.homeomorphSphere.symm, SU2.homeomorphSphere.symm.continuous⟩
  have hf := ContinuousMap.nullhomotopic_of_subsingleton_homotopyGroup (n := 3) f
    ((hasph.of_homotopyEquiv (BoundarylessModel.homeomorph I G).toHomotopyEquiv
      _).subsingleton_homotopyGroup 1)
  have hφf : (φ : C(GLSpecialUnitary (Fin 2) ℂ, BoundarylessModel I G)) =
      f.comp ⟨SU2.homeomorphSphere, SU2.homeomorphSphere.continuous⟩ := by
    ext k
    exact congrArg φ (SU2.homeomorphSphere.symm_apply_apply k).symm
  exact hφ (hφf ▸ hf.comp_left _)

end Transport

/-- **An aspherical compact Lie group has abelian Lie algebra.** -/
theorem isLieAbelian_of_isAspherical {I : ModelWithCorners ℝ E H} [LieGroup I ∞ G] {g : G}
    (hG : IsAspherical G g) : IsLieAbelian (LeftInvariantDerivation I G) :=
  not_not.mp fun h ↦ not_isAspherical_of_not_isLieAbelian h g hG

variable (I : ModelWithCorners ℝ E H) [LieGroup I ∞ G]

include I in
/-- **An aspherical compact connected Lie group is commutative**: its Lie algebra is abelian
(`TauCeti.Lie.isLieAbelian_of_isAspherical`), and a connected Lie group with abelian Lie algebra
is commutative (`TauCeti.Lie.isMulCommutative_of_isLieAbelian`). -/
theorem isMulCommutative_of_isAspherical [PreconnectedSpace G] {g : G} (hG : IsAspherical G g) :
    IsMulCommutative G :=
  have := isLieAbelian_of_isAspherical (I := I) hG
  isMulCommutative_of_isLieAbelian I

include I in
/-- **The torus criterion.** A compact connected Lie group is aspherical, at any base point,
exactly when it is isomorphic, as a topological group, to a torus `(S¹)ʳ`. An aspherical one is
commutative (`TauCeti.Lie.isMulCommutative_of_isAspherical`), hence a torus
(`TauCeti.nonempty_continuousMulEquiv_pi_circle`); every torus is aspherical
(`Circle.isAspherical_pi`). -/
theorem isAspherical_iff_exists_continuousMulEquiv_torus [ConnectedSpace G] {g : G} :
    IsAspherical G g ↔ ∃ r : ℕ, Nonempty (G ≃ₜ* (Fin r → Circle)) := by
  refine ⟨fun hG ↦ ?_, fun ⟨r, ⟨e⟩⟩ ↦ ?_⟩
  · have := isMulCommutative_of_isAspherical I hG
    exact ⟨_, nonempty_continuousMulEquiv_pi_circle (I := I)⟩
  · exact (Circle.isAspherical_pi 1).of_homotopyEquiv e.toHomeomorph.symm.toHomotopyEquiv g

/-- **The torus criterion needs the Lie group hypothesis.** The product `ℕ → S¹` of countably many
circles is a compact connected commutative topological group which is aspherical
(`Circle.isAspherical_pi`) but not isomorphic to any torus `(S¹)ʳ`
(`Circle.not_exists_continuousMulEquiv_pi_fin`). So the equivalence of
`TauCeti.Lie.isAspherical_iff_exists_continuousMulEquiv_torus` fails for compact connected
commutative topological groups in general. -/
theorem not_forall_isAspherical_iff_exists_continuousMulEquiv_torus :
    ¬∀ (G : Type) [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [CompactSpace G]
      [ConnectedSpace G] (g : G), IsAspherical G g ↔ ∃ r : ℕ, Nonempty (G ≃ₜ* (Fin r → Circle)) :=
  fun h ↦ Circle.not_exists_continuousMulEquiv_pi_fin
    ((h (ℕ → Circle) 1).1 (Circle.isAspherical_pi 1))

end Lie

end TauCeti
