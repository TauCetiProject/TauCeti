/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.Height.TangentModel
public import TauCeti.Geometry.Symplectic.Coadjoint.Height.InvariantForm

/-!
# Morse indices of heights on coadjoint orbits at torus points

Let `G` be a real Lie group with Lie algebra `𝔤 = GroupLieAlgebra I G`, let `O = G ⧸ G_ν` be the
coadjoint orbit of `ν ∈ 𝔤*` with orbit map `μ : O → 𝔤*`, and let `f_X = ⟨μ, X⟩` be the height of
`X ∈ 𝔤`. For an invariant bilinear form `B` on `𝔤` and `μ x = B q`, the Morse index of `f_X` at a
critical point `x` is the negative index of the height Hessian
`h_(q,X)(A, C) = -B(⁅A, q⁆, ⁅C, X⁆)` (`LinearMap.BilinForm.heightHessian`) and, for a
separating `B`, `x` is nondegenerate exactly when the kernel of `h_(q,X)` is the centralizer of `q`
(`TauCeti.Geometry.Symplectic.Coadjoint.Height.InvariantForm`). This file evaluates these
statements in a root-plane decomposition.

Now let `𝔤` carry a root-plane decomposition `𝔤 = t + Σ E_i` (`TauCeti.IsRootPlaneDecomposition`),
as the Lie algebra of a compact group does for the Lie algebra `t` of a maximal torus, and let
`q, X ∈ t`. The height Hessian is diagonal in the planes, so on the orbit manifold, in the
namespace `TauCeti.IsRootPlaneDecomposition`:

* the Morse index of `f_X` at `x` is `Σ dim E_i` over the planes with `α_i(q) α_i(X) > 0`
  (`manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_sum`), that is
  **`index_x(f_X) = 2 #{i | α_i(q) α_i(X) > 0}`** for planes of dimension two
  (`manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_two_mul_card`);
* for nonzero planes, `x` is a nondegenerate critical point exactly when `α_i(X) ≠ 0` for every
  root with `α_i(q) ≠ 0`
  (`isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff`).

For a **regular** `X ∈ t`, with `α_i(X) ≠ 0` for every root, the critical points of `f_X` are the
points of the orbit lying over `t`, those with `q ∈ t`
(`mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_mem`,
`criticalPoints_eq_preimage_orbitMap_coadjointRepresentation`), and every one of them is
nondegenerate, so `f_X` is a Morse function on every coadjoint orbit when `B` is separating
(`isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply`). This is the index
formula behind Bott's computation of the homology of flag manifolds and, more generally, of the
coadjoint orbits of compact Lie groups.

## Main results

* `manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_two_mul_card`, in the namespace
  `TauCeti.IsRootPlaneDecomposition`: the Morse index at a torus point counts the root planes
  with `α_i(q) α_i(X) > 0`.
* `criticalPoints_eq_preimage_orbitMap_coadjointRepresentation`, in the namespace
  `TauCeti.IsRootPlaneDecomposition`: the critical set of the height of a regular element of `t`
  is the part of the orbit lying over `t`.
* `isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply`, in the namespace
  `TauCeti.IsRootPlaneDecomposition`: the height of a regular element of `t` is a Morse function
  on every coadjoint orbit.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II (coadjoint orbits and their height functions).
* J. J. Duistermaat, J. A. C. Kolk and V. S. Varadarajan, *Functions, flows and oscillatory
  integrals on flag manifolds and conjugacy classes in real semisimple Lie groups*, Compositio
  Math. 49 (1983), 309–398.
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie QuadraticMap
open scoped Manifold ContDiff Finset

/-! ### Heights at torus points -/

namespace TauCeti.IsRootPlaneDecomposition

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {ν : Module.Dual ℝ (GroupLieAlgebra I G)} {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν}
  {ι : Type*} {t : Submodule ℝ (GroupLieAlgebra I G)} {α : ι → Dual ℝ t}
  {F : ι → Submodule ℝ (GroupLieAlgebra I G)} {J : (i : ι) → Module.End ℝ (F i)} {X : t}

/-- **The Morse index of a height at a torus point.** In a root-plane decomposition of `𝔤` for an
invariant form `B`, if `μ x = B q` with `q ∈ t`, then for `X ∈ t` the Morse index of the height
`f_X` at `x` is the sum of the dimensions of the root planes with `α_i(q) α_i(X) > 0`. -/
theorem manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_sum [Fintype ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    {q : t} (hq : (coadjointRepresentation ℝ I G).orbitMap ν x = B q) :
    manifoldMorseIndex
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x =
      ∑ i with 0 < α i q * α i X, finrank ℝ (F i) := by
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [Module.Dual.manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_sigNeg hB hq
      (hD.lie_eq_zero X.property q.property),
    hD.sigNeg_toQuadraticMap_heightHessian]

/-- **The Morse index of a height at a torus point, for planes of dimension two.** In a root-plane
decomposition of `𝔤` for an invariant form `B` whose planes have dimension two, as for the Lie
algebra of a compact group, if `μ x = B q` with `q ∈ t`, then for `X ∈ t` the Morse index of the
height `f_X` at `x` is `2 #{i | α_i(q) α_i(X) > 0}`. -/
theorem manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_two_mul_card [Fintype ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hF : ∀ i, finrank ℝ (F i) = 2) {q : t}
    (hq : (coadjointRepresentation ℝ I G).orbitMap ν x = B q) :
    manifoldMorseIndex
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x =
      2 * #{i | 0 < α i q * α i X} := by
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [Dual.manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_sigNeg hB hq
      (hD.lie_eq_zero X.property q.property),
    hD.sigNeg_toQuadraticMap_heightHessian_eq_two_mul_card hF]

/-- **Nondegenerate critical points of a height at a torus point.** In a root-plane decomposition
of `𝔤` with nonzero planes, for a separating invariant form `B`, if `μ x = B q` with `q ∈ t`, then
for `X ∈ t` the point `x` is a nondegenerate critical point of the height `f_X` exactly when
`α_i(X) ≠ 0` for every root with `α_i(q) ≠ 0`. -/
theorem isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft) (hF : ∀ i, F i ≠ ⊥) {q : t}
    (hq : (coadjointRepresentation ℝ I G).orbitMap ν x = B q) :
    IsManifoldNondegenerateCriticalPoint
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x ↔
      ∀ i, α i q ≠ 0 → α i X ≠ 0 := by
  rw [Dual.isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff_ker
      hB hsep hq (hD.lie_eq_zero X.property q.property),
    hD.ker_heightHessian_eq_ker_ad_iff hF]

/-- **The critical points of a regular height.** In a root-plane decomposition of `𝔤` for a
separating invariant form `B`, let `X ∈ t` be regular, `α_i(X) ≠ 0` for every root. If
`μ x = B q`, then `x` is a critical point of the height `f_X` exactly when `q ∈ t`: the critical
set of `f_X` is the part of the orbit lying over `t`. -/
theorem mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_mem [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft) (hX : ∀ i, α i X ≠ 0) {q : GroupLieAlgebra I G}
    (hq : (coadjointRepresentation ℝ I G).orbitMap ν x = B q) :
    x ∈ criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) ↔
      q ∈ t := by
  rw [Module.Dual.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_lie_eq_zero hB
    hsep hq]
  exact ⟨hD.mem_of_lie_eq_zero hB hsep hX, hD.lie_eq_zero X.property⟩

/-- **The critical set of a regular height.** In a root-plane decomposition of `𝔤` for a
separating invariant form `B`, let `X ∈ t` be regular, `α_i(X) ≠ 0` for every root. Then the
critical points of the height `f_X` on the coadjoint orbit of `ν` are the points `x` with
`μ x ∈ B t`. In particular the critical set is the same for every regular `X`. -/
theorem criticalPoints_eq_preimage_orbitMap_coadjointRepresentation [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft) (hX : ∀ i, α i X ≠ 0) :
    criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) =
      (coadjointRepresentation ℝ I G).orbitMap ν ⁻¹' (B '' (t : Set (GroupLieAlgebra I G))) := by
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  have hinj : Function.Injective B :=
    LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hsep)
  -- In finite dimensions the injective map `q ↦ B q` to the dual is onto.
  have hsurj := (B.linearEquivOfInjective hinj Subspace.dual_finrank_eq.symm).surjective
  ext x
  obtain ⟨q, hq⟩ := hsurj ((coadjointRepresentation ℝ I G).orbitMap ν x)
  rw [LinearMap.linearEquivOfInjective_apply] at hq
  rw [hD.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_mem hB hsep hX hq.symm,
    Set.mem_preimage, ← hq, hinj.mem_set_image, SetLike.mem_coe]

/-- **The height of a regular torus element is a Morse function.** In a root-plane decomposition of
`𝔤` for a separating invariant form `B`, let `X ∈ t` be regular, `α_i(X) ≠ 0` for every root.
Then every critical point of the height `f_X` on every coadjoint orbit is nondegenerate. -/
theorem isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hsep : B.SeparatingLeft) (hX : ∀ i, α i X ≠ 0)
    (hx : x ∈ criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)) :
    IsManifoldNondegenerateCriticalPoint
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x := by
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  -- In finite dimension `B` is nondegenerate, so `μ x = B q` for some `q`, which regularity puts
  -- in `t`.
  have hBn := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  set q := (B.toDual hBn).symm ((coadjointRepresentation ℝ I G).orbitMap ν x)
  have hq : (coadjointRepresentation ℝ I G).orbitMap ν x = B q := by
    ext η
    rw [← LinearMap.BilinForm.toDual_def hBn, LinearEquiv.apply_symm_apply]
  have hqt := (hD.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_mem hB hsep hX
    hq).1 hx
  rw [Dual.isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff_ker
      hB hsep hq (hD.lie_eq_zero X.property hqt)]
  exact hD.ker_heightHessian_eq_ker_ad ⟨q, hqt⟩ X fun i _ ↦ hX i

end TauCeti.IsRootPlaneDecomposition
