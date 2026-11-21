/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.RootPlane
public import TauCeti.Geometry.Lie.Subgroup.Torus
import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.RootPlane

/-!
# The real root planes of a maximal torus

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱` inside the Lie algebra
`𝔤` of left-invariant derivations, and let `B` be an invariant inner product on `𝔤`, for instance
the one obtained by averaging over `G` (`TauCeti.Lie.exists_isSymm_bilinForm_Ad_invariant` with
`TauCeti.Lie.lieInvariant_of_isInvariantForm`). This file proves the **real root decomposition**

`𝔤 = 𝔱 ⊕ E₁ ⊕ ⋯ ⊕ E_r`

into `𝔱` and pairwise `B`-orthogonal two-dimensional real root planes `E_k`, on each of which
every `H ∈ 𝔱` acts by `ad H = α_k(H) J_k` for a nonzero real root `α_k ∈ 𝔱*` and a `B`-skew
complex structure `J_k` (`TauCeti.Lie.IsMaximalTorus.exists_isInternal_isRootPlane`).

This is the root-plane decomposition of a commutative subspace
(`TauCeti.exists_isInternal_isRootPlane`) for `t = 𝔱`: the centralizer of `𝔱` in `𝔤` is `𝔱` itself,
because the Lie algebra of a maximal torus is a maximal abelian subalgebra
(`TauCeti.Lie.IsMaximalTorus.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero`).

## Main results

* `TauCeti.Lie.IsMaximalTorus.iInf_ker_ad_eq`: the centralizer of the Lie algebra of a maximal
  torus is that Lie algebra.
* `TauCeti.Lie.IsMaximalTorus.exists_isInternal_isRootPlane`: the real root decomposition of the
  Lie algebra of a compact Lie group with respect to a maximal torus.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter IV, § 1 and Chapter V, § 1.
-/

public section

noncomputable section

open Module (Dual finrank)
open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [CompactSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The centralizer of the Lie algebra of a maximal torus is that Lie algebra**: a left-invariant
derivation commutes with every element of `𝔱` exactly when it lies in `𝔱`. -/
theorem IsMaximalTorus.iInf_ker_ad_eq {T : Subgroup G} (hT : IsMaximalTorus T) :
    ⨅ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
        LinearMap.ker (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X) =
      (lieSubalgebraOfSubgroup (I := I) T).toSubmodule := by
  have := hT.isTorus.isMulCommutative
  ext Y
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LieAlgebra.ad_apply,
    LieSubalgebra.mem_toSubmodule, Subtype.forall]
  exact ⟨fun h ↦ hT.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero fun X hX ↦ by
      rw [← lie_skew, h X hX, neg_zero],
    fun hY X hX ↦ lie_eq_zero_of_mem_lieSubalgebraOfSubgroup hX hY⟩

/-- **Real root decomposition of a compact Lie algebra.** For a maximal torus `T` of a compact Lie
group `G` and a symmetric positive definite invariant form `B` on its Lie algebra `𝔤`, the Lie
algebra is the internal direct sum of the Lie algebra `𝔱` of `T` and finitely many pairwise
`B`-orthogonal two-dimensional root planes `E_k`, orthogonal to `𝔱`, on which every `H ∈ 𝔱` acts by
`ad H = α_k(H) J_k` for a nonzero root `α_k`. -/
theorem IsMaximalTorus.exists_isInternal_isRootPlane {T : Subgroup G} (hT : IsMaximalTorus T)
    {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)} (hB : B.IsSymm)
    (hpos : ∀ X, X ≠ 0 → 0 < B X X) (hinv : B.lieInvariant (LeftInvariantDerivation I G)) :
    ∃ (r : ℕ) (α : Fin r → Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
      (V : Fin r → Submodule ℝ (LeftInvariantDerivation I G))
      (J : (k : Fin r) → Module.End ℝ (V k)),
      DirectSum.IsInternal (fun o : Option (Fin r) ↦
        o.elim (lieSubalgebraOfSubgroup (I := I) T).toSubmodule V) ∧
      (∀ k, IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule (α k) (V k) (J k)) ∧
      (∀ k, α k ≠ 0) ∧ (∀ k, finrank ℝ (V k) = 2) ∧
      (∀ k, V k ≤ B.orthogonal (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) ∧
      Pairwise fun k l ↦ V k ≤ B.orthogonal (V l) := by
  have := hT.isTorus.isMulCommutative
  have : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  obtain ⟨r, α, V, J, hint, hroot, hne, hrank, hC, hV⟩ :=
    TauCeti.exists_isInternal_isRootPlane hB hpos hinv fun X hX Y hY ↦
      lie_eq_zero_of_mem_lieSubalgebraOfSubgroup (K := T) hX hY
  rw [hT.iInf_ker_ad_eq] at hint hC
  exact ⟨r, α, V, J, hint, hroot, hne, hrank, hC, hV⟩

end TauCeti.Lie
