/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus.OrbitType
public import TauCeti.Geometry.Lie.Subgroup.Weyl.Finite
public import TauCeti.Geometry.Lie.Subgroup.Weyl.OrbitSpace
public import TauCeti.RepresentationTheory.ReflectingHyperplane.FundamentalDomain
import TauCeti.Geometry.Lie.Subgroup.Torus.Root.Reflection
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The closed Weyl chamber of a compact connected Lie group

Let `T` be a maximal torus of a compact connected Lie group `G`, with Lie algebra `𝔱`, let `B` be
an invariant inner product on the Lie algebra `𝔤` of `G`, and let `𝔤 = 𝔱 + E₁ + ⋯ + E_r` be a
decomposition into `𝔱` and nonzero root planes with nonzero real roots `α₁, …, α_r ∈ 𝔱*`
(`TauCeti.IsRootPlaneDecomposition`). For a regular element `X₀ ∈ 𝔱`, one at which no root
vanishes, the **closed Weyl chamber** of `X₀` is

`C = {X ∈ 𝔱 | α_i(X) α_i(X₀) ≥ 0 for every i}` (`TauCeti.closedChamber α X₀`),

the set of points lying weakly on the side of `X₀` of every root hyperplane `ker α_i`.

This file proves that `C` is a strict fundamental domain for the Weyl group `W = N(T) / T` acting
on `𝔱`: every Weyl orbit meets `C` in exactly one point
(`TauCeti.Lie.IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_weylAdjointRepresentation`).
It follows from `TauCeti.Lie.IsMaximalTorus.weylOrbitHomeomorph` and
`TauCeti.Lie.IsMaximalTorus.weylCoadjointOrbitHomeomorph` that `C` parametrizes the adjoint and the
coadjoint orbits: the inclusion `C ⊆ 𝔤` induces homeomorphisms

`C ≃ₜ 𝔤 / Ad G` (`TauCeti.Lie.IsMaximalTorus.closedChamberHomeomorph`) and
`C ≃ₜ 𝔤* / Ad* G` (`TauCeti.Lie.IsMaximalTorus.closedChamberCoadjointHomeomorph`),

the second through `X ↦ B'(X, ·)` for an invariant form `B'` with trivial radical. In particular
every coadjoint orbit contains exactly one covector `B'(X, ·)` with `X ∈ C`
(`TauCeti.Lie.IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_coadjointRepresentation`).

The proof applies the fundamental-domain theorem
`Representation.existsUnique_mem_closedChamber_orbitRel` for finite groups containing reflections,
whose hypotheses hold for the Weyl group:

* `W` is finite (`TauCeti.Lie.IsMaximalTorus.finite_normalizerQuotient`);
* for every root `α_i`, some element of `W` acts on `𝔱` by the reflection along a coroot
  `B`-orthogonal to `ker α_i`, represented by the exponential of a root vector
  (`TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_reflection`);
* only the identity of `W` fixes a regular `X`, because the adjoint stabilizer of a regular element
  of `𝔱` in the connected group `G` is `T` itself
  (`TauCeti.IsRootPlaneDecomposition.stabilizer_continuousAdjointRepresentation_eq_iff`,
  `TauCeti.Lie.IsMaximalTorus.eq_one_of_weylAdjointRepresentation_apply_eq_self`).

No root system structure on the real roots is needed: the argument does not use that `W` permutes
the roots, nor a base or a positive system.

## Main results

* `TauCeti.Lie.IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_weylAdjointRepresentation`:
  every Weyl orbit in `𝔱` meets the closed chamber of a regular element exactly once.
* `TauCeti.Lie.IsMaximalTorus.eq_one_of_weylAdjointRepresentation_apply_eq_self`: the Weyl group
  acts freely on the regular elements of `𝔱`.
* `TauCeti.Lie.IsMaximalTorus.weylClosedChamberHomeomorph`: the closed chamber is homeomorphic to
  the Weyl orbit space `𝔱 / W`.
* `TauCeti.Lie.IsMaximalTorus.closedChamberHomeomorph`: the closed chamber is homeomorphic to the
  adjoint orbit space.
* `TauCeti.Lie.IsMaximalTorus.closedChamberCoadjointHomeomorph`,
  `TauCeti.Lie.IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_coadjointRepresentation`:
  the closed chamber parametrizes the coadjoint orbits.

## References

* M. M. Alexandrino and R. G. Bettiol, *Lie Groups and Geometric Aspects of Isometric Actions*,
  Springer, 2015, Theorem 4.31.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, § 2.
-/

public section

open Module (Dual)
open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [CompactSpace G] [ConnectedSpace G]
  {T : Subgroup G} [IsMulCommutative T]
  {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
  {ι : Type*} [Finite ι] {α : ι → Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
  {V : ι → Submodule ℝ (LeftInvariantDerivation I G)} {J : (i : ι) → Module.End ℝ (V i)}
  {X₀ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

local instance instFiniteDimensionalLeftInvariantDerivationChamber :
    FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-! ### The hypotheses of the fundamental-domain theorem -/

omit [CompactSpace G] [ConnectedSpace G] [IsMulCommutative T] [Finite ι] in
/-- The restriction of a positive definite form to `𝔱` is positive definite. -/
private theorem restrict_apply_self_pos (hBp : B.toQuadraticMap.PosDef)
    (v : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (hv : v ≠ 0) :
    0 < B.restrict _ v v :=
  hBp (v : LeftInvariantDerivation I G) (by simpa using hv)

omit [ConnectedSpace G] [Finite ι] in
/-- Every root reflection is realized by the Weyl group, along a coroot orthogonal to the root
hyperplane. -/
private theorem exists_weylAdjointRepresentation_eq_reflection_of_decomposition
    (hT : IsMaximalTorus T) (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (i : ι) :
    ∃ (c : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (hc : α i c = 2),
      (∀ X, α i X = 0 → B.restrict _ X c = 0) ∧
      ∃ w, T.weylAdjointRepresentation (I := I) w = (Module.reflection hc).toLinearMap := by
  obtain ⟨c, hc, hcB, -, n, hn, -⟩ :=
    hT.exists_weylAdjointRepresentation_eq_reflection hBs hBp hB (hD.isRootPlane i) (hα i) (hV i)
  exact ⟨c, hc, hcB, n, hn⟩

/-- **The Weyl group acts freely on the regular elements of `𝔱`.** Let `T` be a maximal torus of
a compact connected Lie group, let `B` be an invariant inner product on `𝔤`, and let
`𝔤 = 𝔱 + Σ E_i` be a root-plane decomposition with nonzero planes and nonzero roots `α_i`. Only the
identity of the Weyl group `N(T) / T` fixes an element `X ∈ 𝔱` at which no root vanishes. -/
theorem IsMaximalTorus.eq_one_of_weylAdjointRepresentation_apply_eq_self (hT : IsMaximalTorus T)
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (w : T.normalizerQuotient)
    (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (hX : ∀ i, α i X ≠ 0)
    (hwX : T.weylAdjointRepresentation (I := I) w X = X) : w = 1 := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  -- A representative `n` fixes `X`, so it lies in the adjoint stabilizer of `X`, which is `T`.
  have hstab := hD.stabilizer_continuousAdjointRepresentation_eq_iff hT.isTorus rfl hB
    (LinearMap.BilinForm.separatingLeft_of_anisotropic hBp.anisotropic) hα hV X |>.2 hX
  have hn : (n : G) ∈
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (X : LeftInvariantDerivation I G) := by
    rw [Representation.mem_stabilizer, ContRepresentation.toRepresentation_apply,
      continuousAdjointRepresentation_apply, ← Subgroup.coe_weylAdjointRepresentation_mk_apply, hwX]
  rw [hstab] at hn
  exact (T.normalizerQuotientMk_eq_one_iff n).2 hn

/-! ### The closed chamber as a fundamental domain of the Weyl group -/

/-- **The closed Weyl chamber is a strict fundamental domain for the Weyl group.** Let `T` be a
maximal torus of a compact connected Lie group, with Lie algebra `𝔱`, let `B` be an invariant inner
product on `𝔤`, and let `𝔤 = 𝔱 + Σ E_i` be a root-plane decomposition with nonzero planes and
nonzero roots `α_i`. For a regular `X₀ ∈ 𝔱`, every orbit of the Weyl group `N(T) / T` in `𝔱` meets
the closed chamber `{X | α_i(X) α_i(X₀) ≥ 0}` of `X₀` in exactly one point. -/
theorem IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_weylAdjointRepresentation
    (hT : IsMaximalTorus T) (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (hX₀ : ∀ i, α i X₀ ≠ 0)
    (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    ∃! Y, Y ∈ closedChamber α X₀ ∧ (T.weylAdjointRepresentation (I := I)).orbitRel Y X :=
  have := hT.finite_normalizerQuotient I
  (T.weylAdjointRepresentation (I := I)).existsUnique_mem_closedChamber_orbitRel
    (restrict_apply_self_pos hBp)
    (exists_weylAdjointRepresentation_eq_reflection_of_decomposition hT hBs hBp hB hD hα
      hV)
    (hT.eq_one_of_weylAdjointRepresentation_apply_eq_self hBp hB hD hα hV) hX₀ X

/-- **The closed Weyl chamber parametrizes the Weyl orbits in `𝔱`.** Under the hypotheses of
`TauCeti.Lie.IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_weylAdjointRepresentation`,
sending a point of the closed chamber of `X₀` to its Weyl orbit is a homeomorphism from the closed
chamber onto the orbit space `𝔱 / W`. -/
noncomputable def IsMaximalTorus.weylClosedChamberHomeomorph (hT : IsMaximalTorus T)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (hX₀ : ∀ i, α i X₀ ≠ 0) :
    closedChamber α X₀ ≃ₜ Quotient (T.weylAdjointRepresentation (I := I)).orbitRel :=
  have := hT.finite_normalizerQuotient I
  (T.weylAdjointRepresentation (I := I)).closedChamberHomeomorph (restrict_apply_self_pos hBp)
    (exists_weylAdjointRepresentation_eq_reflection_of_decomposition hT hBs hBp hB hD hα hV)
    (hT.eq_one_of_weylAdjointRepresentation_apply_eq_self hBp hB hD hα hV) hX₀
    (fun _ ↦ LinearMap.continuous_of_finiteDimensional _)
    (fun _ ↦ LinearMap.continuous_of_finiteDimensional _)

/-- The homeomorphism `TauCeti.Lie.IsMaximalTorus.weylClosedChamberHomeomorph` sends a point of
the closed chamber to its Weyl orbit. -/
@[simp]
theorem IsMaximalTorus.weylClosedChamberHomeomorph_apply (hT : IsMaximalTorus T)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (hX₀ : ∀ i, α i X₀ ≠ 0) (X : closedChamber α X₀) :
    hT.weylClosedChamberHomeomorph hBs hBp hB hD hα hV hX₀ X =
      Quotient.mk (T.weylAdjointRepresentation (I := I)).orbitRel
        (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) := by
  simp [weylClosedChamberHomeomorph]

/-- **The closed Weyl chamber parametrizes the adjoint orbits.** Under the hypotheses of
`TauCeti.Lie.IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_weylAdjointRepresentation`,
sending a point of the closed chamber of `X₀` to its adjoint orbit is a homeomorphism from the
closed chamber onto the adjoint orbit space `𝔤 / Ad G`. -/
noncomputable def IsMaximalTorus.closedChamberHomeomorph (hT : IsMaximalTorus T) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (hX₀ : ∀ i, α i X₀ ≠ 0) :
    closedChamber α X₀ ≃ₜ
      Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel :=
  (hT.weylClosedChamberHomeomorph hBs hBp hB hD hα hV hX₀).trans hT.weylOrbitHomeomorph

/-- The homeomorphism `TauCeti.Lie.IsMaximalTorus.closedChamberHomeomorph` sends a point of the
closed chamber to its adjoint orbit. -/
@[simp]
theorem IsMaximalTorus.closedChamberHomeomorph_apply (hT : IsMaximalTorus T) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (hX₀ : ∀ i, α i X₀ ≠ 0) (X : closedChamber α X₀) :
    hT.closedChamberHomeomorph hBs hBp hB hD hα hV hX₀ X =
      Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        ((X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) : LeftInvariantDerivation I G) := by
  simp [closedChamberHomeomorph]

/-! ### The closed chamber and the coadjoint orbits -/

section Coadjoint

/-- Evaluation at the identity, the Lie algebra isomorphism from left-invariant derivations to the
tangent Lie algebra `𝔤` on which the coadjoint representation is defined. -/
local notation "evalOne" => leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
  (BoundarylessManifold.isInteriorPoint (x := (1 : G)))

variable {B' : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}

/-- **Every coadjoint orbit contains exactly one covector of the closed Weyl chamber.** Under the
hypotheses of
`TauCeti.Lie.IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_weylAdjointRepresentation`,
let `B'` be an invariant form with trivial left radical on the tangent Lie algebra `𝔤`. Then every
covector `ν ∈ 𝔤*` lies in the coadjoint orbit of `B'(X, ·)` for exactly one `X` in the closed
chamber of `X₀`. -/
theorem IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_coadjointRepresentation
    (hT : IsMaximalTorus T) (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (hX₀ : ∀ i, α i X₀ ≠ 0)
    (hB' : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B')
    (hB's : LinearMap.SeparatingLeft B') (ν : Dual ℝ (GroupLieAlgebra I G)) :
    ∃! Y, Y ∈ closedChamber α X₀ ∧ (coadjointRepresentation ℝ I G).orbitRel
      (B' (evalOne (Y : LeftInvariantDerivation I G))) ν := by
  set r := (coadjointRepresentation ℝ I G).orbitRel
  obtain ⟨g, X, hX, hgX⟩ := hT.exists_coadjointRepresentation_apply_eq hB' hB's ν
  -- The covector `ν` is coadjoint to `B'(X, ·)` with `X ∈ 𝔱`.
  have hνX : r (B' (evalOne X)) ν := (Representation.orbitRel_apply _).2 ⟨g, hgX⟩
  obtain ⟨Y, ⟨hY, hYX⟩, huniq⟩ :=
    hT.existsUnique_mem_closedChamber_orbitRel_weylAdjointRepresentation hBs hBp hB hD hα hV hX₀
      ⟨X, hX⟩
  refine ⟨Y, ⟨hY, r.iseqv.trans
    ((hT.orbitRel_coadjointRepresentation_iff hB' hB's Y ⟨X, hX⟩).2 hYX) hνX⟩,
    fun Y' ⟨hY', hY'ν⟩ ↦ huniq Y' ⟨hY', ?_⟩⟩
  exact (hT.orbitRel_coadjointRepresentation_iff hB' hB's Y' ⟨X, hX⟩).1
    (r.iseqv.trans hY'ν (r.iseqv.symm hνX))

variable [TopologicalSpace (Dual ℝ (GroupLieAlgebra I G))]
  [IsModuleTopology ℝ (Dual ℝ (GroupLieAlgebra I G))]

/-- **The closed Weyl chamber parametrizes the coadjoint orbits.** Under the hypotheses of
`TauCeti.Lie.IsMaximalTorus.existsUnique_mem_closedChamber_orbitRel_weylAdjointRepresentation`,
let `B'` be an invariant form with trivial left radical on the tangent Lie algebra `𝔤`. Sending a
point `X` of the closed chamber of `X₀` to the coadjoint orbit of `B'(X, ·)` is a homeomorphism
from the closed chamber onto the coadjoint orbit space `𝔤* / Ad* G`, for the module topology on
`𝔤*`. -/
noncomputable def IsMaximalTorus.closedChamberCoadjointHomeomorph (hT : IsMaximalTorus T)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (hX₀ : ∀ i, α i X₀ ≠ 0)
    (hB' : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B')
    (hB's : LinearMap.SeparatingLeft B') :
    closedChamber α X₀ ≃ₜ Quotient (coadjointRepresentation ℝ I G).orbitRel :=
  (hT.weylClosedChamberHomeomorph hBs hBp hB hD hα hV hX₀).trans
    (hT.weylCoadjointOrbitHomeomorph hB' hB's)

/-- The homeomorphism `TauCeti.Lie.IsMaximalTorus.closedChamberCoadjointHomeomorph` sends a point
`X` of the closed chamber to the coadjoint orbit of `B'(X, ·)`. -/
@[simp]
theorem IsMaximalTorus.closedChamberCoadjointHomeomorph_apply (hT : IsMaximalTorus T)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (hX₀ : ∀ i, α i X₀ ≠ 0)
    (hB' : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B')
    (hB's : LinearMap.SeparatingLeft B') (X : closedChamber α X₀) :
    hT.closedChamberCoadjointHomeomorph hBs hBp hB hD hα hV hX₀ hB' hB's X =
      Quotient.mk (coadjointRepresentation ℝ I G).orbitRel
        (B' (evalOne ((X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
          LeftInvariantDerivation I G))) := by
  simp [closedChamberCoadjointHomeomorph]

end Coadjoint

end TauCeti.Lie
