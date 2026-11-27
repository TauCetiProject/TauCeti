/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Poincare
public import TauCeti.Geometry.Lie.Subgroup.Weyl.OrbitSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Field.ULift
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Closed Weyl chambers parametrize coadjoint orbits

Let `T` be a maximal torus of a compact connected Lie group `G`, with Lie algebra `𝔱` and Weyl
group `W = N(T) / T`, let `B` be an `Ad`-invariant form with trivial left radical on `𝔤`, and let
`𝔤 = t + Σ F_i` be a root-plane decomposition over the image `t` of `𝔱`, with planes of dimension
two and roots `α_i : t → ℝ`. For an element `X ∈ t` at which no root vanishes, the **closed Weyl
chamber** of `X` is the closed convex cone

`C_X = {p ∈ t | α_i(p) α_i(X) ≥ 0 for every i}`

of the points at which no root has the sign opposite to its sign at `X`. Taking as positive the
roots that are positive at `X`, it is the dominant chamber `{p | α(p) ≥ 0 for every positive
root α}`; it contains every point at which all roots vanish, such as the centre of `𝔤` read in
`t`.

This file proves that `C_X` is a strict fundamental domain for the Weyl group. Unqualified names
below are in the namespace `TauCeti.IsRootPlaneDecomposition`.

* **Every Weyl orbit meets the closed chamber exactly once.** For `μ ∈ 𝔱`, exactly one point of
  the Weyl orbit `W μ`, read in `t`, lies in `C_X`
  (`existsUnique_mem_range_weylOrbitPoint_and_forall_nonneg`).

The proof is Bott's: the height `f_{-X}` is a perfect Morse function on the coadjoint orbit
`O_μ` of `B (e μ)`, and its critical points of index zero are the points `p ∈ W μ` at which no
root has the sign it has at `-X`
(`bettiNumber_quotient_stabilizer_coadjointRepresentation_two_mul_eq_ncard`). Their number is
the Betti number `b_0(O_μ)`, which is `1` because `O_μ` is a quotient of the connected group `G`.
Connectedness of `G` is needed: for the disconnected group `O(2)`, with maximal torus `SO(2)`,
there are no roots, so the closed chamber is all of `𝔱 = ℝ`, while the Weyl group
`O(2) / SO(2)` acts on `𝔱` by `-1`. So the Weyl orbit `{μ, -μ}` of `μ ≠ 0` meets the chamber
twice, and the coadjoint orbit `O(2) / SO(2)` of a nonzero covector has two points.

Since two elements of `t` lie in one coadjoint orbit exactly when they are related by the Weyl
group (`TauCeti.Lie.IsMaximalTorus.orbitRel_coadjointRepresentation_iff`), and every coadjoint
orbit meets `t` (`TauCeti.Lie.IsMaximalTorus.exists_coadjointRepresentation_apply_eq`), this gives:

* **Every coadjoint orbit meets the closed chamber exactly once.** For every `ν ∈ 𝔤*` there is
  exactly one `p ∈ C_X` with `B p` in the coadjoint orbit of `ν`
  (`existsUnique_forall_nonneg_and_orbitRel_coadjointRepresentation`).
* **The chamber quotient homeomorphism.** `p ↦ G · B p` is a homeomorphism from `C_X` onto the
  coadjoint orbit space `𝔤* / Ad* G` (`chamberCoadjointOrbitHomeomorph`). It is a continuous
  bijection, and it is proper: `p ↦ B p` is an injective linear map out of the finite-dimensional
  space `t`, hence a closed embedding, and the orbit map of the compact group `G` is proper
  (`Representation.isProperMap_orbitRel_mk`).

The chamber depends on `X` only through the signs of the roots at `X`, that is, through the open
chamber containing `X`. Every invariant inner product on `𝔤` admits a root-plane decomposition over
the Lie algebra of a maximal torus together with a regular element
(`TauCeti.Lie.IsMaximalTorus.exists_isRootPlaneDecomposition`), so these statements apply to every
compact connected Lie group.

## Main results

All in the namespace `TauCeti.IsRootPlaneDecomposition`:

* `existsUnique_mem_range_weylOrbitPoint_and_forall_nonneg`: every Weyl orbit in `t` meets the
  closed chamber of a regular element in exactly one point.
* `existsUnique_forall_nonneg_and_orbitRel_coadjointRepresentation`: every coadjoint orbit
  contains the covector `B p` of exactly one point `p` of the closed chamber.
* `eq_of_forall_nonneg_of_orbitRel_coadjointRepresentation`: two points of the closed chamber in
  one coadjoint orbit are equal.
* `chamberCoadjointOrbitHomeomorph`: the homeomorphism `C_X ≃ₜ 𝔤* / Ad* G`.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter V, §2 (Weyl chambers as fundamental domains).
* M. M. Alexandrino and R. G. Bettiol, *Lie Groups and Geometric Aspects of Isometric Actions*,
  Springer, 2015, Theorem 4.31.
-/

public section

noncomputable section

open Function Module Manifold Topology TauCeti TauCeti.Lie
open scoped Manifold ContDiff Finset

universe u

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  isClosed_stabilizer_coadjointRepresentation

namespace TauCeti.IsRootPlaneDecomposition

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type u} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [CompactSpace G] [ConnectedSpace G]
  {T : Subgroup G} [IsMulCommutative T] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {ι : Type*} [Finite ι] {t : Submodule ℝ (GroupLieAlgebra I G)} {α : ι → Dual ℝ t}
  {F : ι → Submodule ℝ (GroupLieAlgebra I G)} {J : (i : ι) → End ℝ (F i)}

/-- Evaluation at the identity, the Lie algebra isomorphism from left-invariant derivations to the
tangent Lie algebra `𝔤` on which the coadjoint representation is defined. -/
local notation "evalOne" => leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
  (BoundarylessManifold.isInteriorPoint (x := (1 : G)))

/-- **Every Weyl orbit meets a closed Weyl chamber exactly once.** In a root-plane decomposition
`𝔤 = t + Σ F_i` with planes of dimension two over the image `t` of the Lie algebra of a maximal
torus `T` of a compact connected Lie group, for an invariant form `B` with trivial left radical and
`X ∈ t` at which no root vanishes, the Weyl orbit of every `μ ∈ 𝔱`, read in `t`, contains exactly
one point `p` of the closed chamber of `X`: `α_i(p) α_i(X) ≥ 0` for every root `α_i`. -/
theorem existsUnique_mem_range_weylOrbitPoint_and_forall_nonneg
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (evalOne).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0) :
    ∃! p : t, p ∈ Set.range (weylOrbitPoint ht μ) ∧ ∀ i, 0 ≤ α i p * α i X := by
  have := Fintype.ofFinite ι
  -- The coadjoint orbit `O_μ` is a connected manifold, so it is path connected and `b₀(O_μ) = 1`.
  set O := G ⧸ (coadjointRepresentation ℝ I G).stabilizer
    (B (evalOne (μ : LeftInvariantDerivation I G)))
  have : ConnectedSpace O := QuotientGroup.mk_surjective.connectedSpace continuous_quot_mk
  have : LocallyPathConnectedSpace O := ChartedSpace.locallyPathConnectedSpace
    (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer
      (B (evalOne (μ : LeftInvariantDerivation I G))))) _
  have : PathConnectedSpace O := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  -- The perfect Morse height `f_{-X}` has as many minima as the orbit has path components, one,
  -- and its minima are the points of the Weyl orbit at which no root has the sign it has at `-X`.
  have hb := hD.bettiNumber_quotient_stabilizer_coadjointRepresentation_two_mul_eq_ncard
    (ULift.{u} ℚ) hT hB hsep hF ht μ (X := -X) (fun i ↦ by simpa using hX i) 0
  rw [mul_zero, bettiNumber_zero, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩,
    eq_comm, Set.ncard_eq_one] at hb
  obtain ⟨p, hp⟩ := hb
  have hiff (q : t) : #{i | 0 < α i q * α i (-X)} = 0 ↔ ∀ i, 0 ≤ α i q * α i X := by
    simp [Finset.filter_eq_empty_iff]
  refine ⟨p, ?_, fun q hq ↦ ?_⟩
  · have hpmem := Set.mem_singleton p
    rw [← hp] at hpmem
    exact ⟨hpmem.1, (hiff p).mp hpmem.2⟩
  · have hqmem : q ∈ ({q : t | q ∈ Set.range (weylOrbitPoint ht μ) ∧
        #{i | 0 < α i q * α i (-X)} = 0}) := ⟨hq.1, (hiff q).mpr hq.2⟩
    rwa [hp] at hqmem

/-- **Every coadjoint orbit meets a closed Weyl chamber exactly once.** In a root-plane
decomposition `𝔤 = t + Σ F_i` with planes of dimension two over the image `t` of the Lie algebra of
a maximal torus of a compact connected Lie group, for an invariant form `B` with trivial left
radical and `X ∈ t` at which no root vanishes, every covector `ν ∈ 𝔤*` lies in the coadjoint orbit
of `B p` for exactly one point `p` of the closed chamber of `X`. -/
theorem existsUnique_forall_nonneg_and_orbitRel_coadjointRepresentation
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (evalOne).toLinearEquiv.toLinearMap)
    {X : t} (hX : ∀ i, α i X ≠ 0) (ν : Dual ℝ (GroupLieAlgebra I G)) :
    ∃! p : t, (∀ i, 0 ≤ α i p * α i X) ∧
      (coadjointRepresentation ℝ I G).orbitRel ν (B p) := by
  -- Points of `t` are the images `e Y` of elements `Y ∈ 𝔱`.
  have hmem (p : t) : ∃ Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      evalOne (Y : LeftInvariantDerivation I G) = p := by
    obtain ⟨Y, hY, hYp⟩ := (ht ▸ p.property : (p : GroupLieAlgebra I G) ∈
      (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map (evalOne).toLinearEquiv.toLinearMap)
    exact ⟨⟨Y, hY⟩, hYp⟩
  -- The covector of a Weyl orbit point of `μ` is in the coadjoint orbit of the covector of `μ`.
  have hweyl (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (w : T.normalizerQuotient) :
      (coadjointRepresentation ℝ I G).orbitRel (B (evalOne (μ : LeftInvariantDerivation I G)))
        (B (weylOrbitPoint ht μ w)) := by
    rw [coe_weylOrbitPoint, hT.orbitRel_coadjointRepresentation_iff hB hsep]
    exact (Representation.orbitRel_apply _).mpr ⟨w⁻¹, by simp⟩
  obtain ⟨g, Y, hY, hgν⟩ := hT.exists_coadjointRepresentation_apply_eq hB hsep ν
  have hν : (coadjointRepresentation ℝ I G).orbitRel ν (B (evalOne Y)) :=
    (Representation.orbitRel_apply _).mpr ⟨g⁻¹, by rw [← hgν, Representation.inv_self_apply]⟩
  obtain ⟨p, ⟨⟨w, rfl⟩, hpX⟩, huniq⟩ :=
    hD.existsUnique_mem_range_weylOrbitPoint_and_forall_nonneg hT hB hsep hF ht ⟨Y, hY⟩ hX
  refine ⟨weylOrbitPoint ht ⟨Y, hY⟩ w, ⟨hpX, ?_⟩, fun q ⟨hqX, hq⟩ ↦ huniq q ⟨?_, hqX⟩⟩
  · exact (coadjointRepresentation ℝ I G).orbitRel.trans hν (hweyl ⟨Y, hY⟩ w)
  · -- `q = e Z` with `B (e Z)` in the coadjoint orbit of `B (e Y)`, so `Z` is a Weyl translate
    -- of `Y`.
    obtain ⟨Z, hZ⟩ := hmem q
    have hYZ : (coadjointRepresentation ℝ I G).orbitRel
        (B (evalOne (⟨Y, hY⟩ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)))
        (B (evalOne (Z : LeftInvariantDerivation I G))) :=
      (coadjointRepresentation ℝ I G).orbitRel.trans
        ((coadjointRepresentation ℝ I G).orbitRel.symm hν) (hZ ▸ hq)
    obtain ⟨v, hv⟩ := (Representation.orbitRel_apply _).mp
      ((hT.orbitRel_coadjointRepresentation_iff hB hsep _ _).mp hYZ)
    refine ⟨v⁻¹, Subtype.ext ?_⟩
    rw [coe_weylOrbitPoint, ← hZ, ← hv, Representation.inv_self_apply]

/-- **Two points of a closed Weyl chamber in one coadjoint orbit are equal.** In a root-plane
decomposition `𝔤 = t + Σ F_i` with planes of dimension two over the image `t` of the Lie algebra of
a maximal torus of a compact connected Lie group, for an invariant form `B` with trivial left
radical and `X ∈ t` at which no root vanishes, two points `p` and `q` of the closed chamber of `X`
whose covectors `B p` and `B q` lie in one coadjoint orbit are equal. -/
theorem eq_of_forall_nonneg_of_orbitRel_coadjointRepresentation
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (evalOne).toLinearEquiv.toLinearMap)
    {X : t} (hX : ∀ i, α i X ≠ 0) {p q : t} (hp : ∀ i, 0 ≤ α i p * α i X)
    (hq : ∀ i, 0 ≤ α i q * α i X) (hpq : (coadjointRepresentation ℝ I G).orbitRel (B p) (B q)) :
    p = q := by
  obtain ⟨r, -, hr⟩ :=
    hD.existsUnique_forall_nonneg_and_orbitRel_coadjointRepresentation hT hB hsep hF ht hX (B p)
  exact (hr p ⟨hp, (coadjointRepresentation ℝ I G).orbitRel.refl _⟩).trans (hr q ⟨hq, hpq⟩).symm

variable [TopologicalSpace (Dual ℝ (GroupLieAlgebra I G))]
  [IsModuleTopology ℝ (Dual ℝ (GroupLieAlgebra I G))]

/-- **The chamber quotient homeomorphism.** In a root-plane decomposition `𝔤 = t + Σ F_i` with
planes of dimension two over the image `t` of the Lie algebra of a maximal torus of a compact
connected Lie group, for an invariant form `B` with trivial left radical and `X ∈ t` at which no
root vanishes, `p ↦ G · B p` is a homeomorphism from the closed chamber of `X` onto the coadjoint
orbit space `𝔤* / Ad* G`, for the module topology on `𝔤*`. -/
def chamberCoadjointOrbitHomeomorph
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (evalOne).toLinearEquiv.toLinearMap)
    {X : t} (hX : ∀ i, α i X ≠ 0) :
    {p : t // ∀ i, 0 ≤ α i p * α i X} ≃ₜ Quotient (coadjointRepresentation ℝ I G).orbitRel :=
  have := IsModuleTopology.isTopologicalAddGroup ℝ (Dual ℝ (GroupLieAlgebra I G))
  have := ModuleTopology.t2Space (Module.finBasis ℝ (Dual ℝ (GroupLieAlgebra I G)))
  -- The covector map `t → 𝔤*` is an injective linear map out of a finite-dimensional space.
  have hBt : IsClosedEmbedding (B ∘ₗ t.subtype) :=
    LinearMap.isClosedEmbedding_of_injective <| LinearMap.ker_eq_bot.mpr fun p q hpq ↦
      Subtype.ext <| LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hsep) hpq
  -- The closed chamber is closed in `t`.
  have hC : IsClosed {p : t | ∀ i, 0 ≤ α i p * α i X} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const
      ((α i).continuous_of_finiteDimensional.mul continuous_const)
  have hp : IsProperMap fun p : {p : t // ∀ i, 0 ≤ α i p * α i X} ↦
      Quotient.mk (coadjointRepresentation ℝ I G).orbitRel (B p) :=
    ((Representation.isProperMap_orbitRel_mk _ continuous_coadjointRepresentation_apply).comp
      hBt.isProperMap).comp hC.isClosedEmbedding_subtypeVal.isProperMap
  have hbij : Bijective fun p : {p : t // ∀ i, 0 ≤ α i p * α i X} ↦
      Quotient.mk (coadjointRepresentation ℝ I G).orbitRel (B p) := by
    refine ⟨fun p q hpq ↦ Subtype.ext ?_, fun y ↦ ?_⟩
    · exact hD.eq_of_forall_nonneg_of_orbitRel_coadjointRepresentation hT hB hsep hF ht hX
        p.property q.property (Quotient.exact hpq)
    · induction y using Quotient.inductionOn' with | h ν => ?_
      obtain ⟨p, ⟨hpX, hpν⟩, -⟩ :=
        hD.existsUnique_forall_nonneg_and_orbitRel_coadjointRepresentation hT hB hsep hF ht hX ν
      exact ⟨⟨p, hpX⟩, (Quotient.sound' hpν).symm⟩
  (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousClosed hp.continuous hp.isClosedMap

/-- The homeomorphism `chamberCoadjointOrbitHomeomorph` sends a point `p` of the closed chamber
to the coadjoint orbit of `B p`. -/
@[simp]
theorem chamberCoadjointOrbitHomeomorph_apply
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft) (hF : ∀ i, finrank ℝ (F i) = 2)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (evalOne).toLinearEquiv.toLinearMap)
    {X : t} (hX : ∀ i, α i X ≠ 0) (p : {p : t // ∀ i, 0 ≤ α i p * α i X}) :
    hD.chamberCoadjointOrbitHomeomorph hT hB hsep hF ht hX p =
      Quotient.mk (coadjointRepresentation ℝ I G).orbitRel (B p) :=
  (rfl)

end TauCeti.IsRootPlaneDecomposition
