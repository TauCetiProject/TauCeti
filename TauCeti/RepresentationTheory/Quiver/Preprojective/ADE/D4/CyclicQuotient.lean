/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.SelfInjective
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.CyclicQuotient

/-!
# A positive-degree cyclic class in type `D₄` in characteristic two

The closed walk `1 → 0 → 1 → 2 → 1` in the Bourbaki-labelled doubled `D₄` diagram survives
modulo additive commutators in characteristic two. It has path degree four. Its nonzero cyclic
class detects the bad characteristic of type `D` in the Hochschild calculations underlying
zigzag intrinsic formality.

The existing Frobenius functional of `D₄` becomes symmetric when `2 = 0`: its Gram matrix on
the walk basis is symmetric up to signs, and those signs disappear. Consequently it kills
commutators, whereas its value on the displayed walk is one. Over a field, this gives the exact
criterion: the degree-four piece lies in the commutator submodule if and only if `2 ≠ 0`.
Equivalently, the commutator submodule is the augmentation kernel exactly outside
characteristic two. No Hochschild comparison or intrinsic-formality conclusion is asserted here.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the cyclic quotient and bad characteristics.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

attribute [local instance] d4NeighborSetFintype

variable (k : Type*)

local notation "Q" => DoubledQuiver zigzagD4Graph
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "W" => signlessWord k zigzagD4Graph
local notation "φ" => signlessPreprojectiveD4FrobeniusFunctional k

section CommRing

variable [CommRing k]

/-- The Frobenius functional takes the closed degree-four walk through leaves `0` and `2`
to one, over every commutative coefficient ring. -/
private theorem signlessPreprojectiveD4FrobeniusFunctional_cyclicWord :
    φ (W [1, 2, 1, 0, 1]) = 1 := by
  rw [signlessPreprojectiveD4FrobeniusFunctional_signlessWord k _ (by decide) (by decide)]
  norm_num [List.reverse_cons]

/-- The detecting closed walk is homogeneous of path degree four. -/
theorem signlessWord_D4_cyclicWord_mem_grade_four :
    W [1, 2, 1, 0, 1] ∈ signlessPreprojectiveGrade k Q 4 := by
  simp only [signlessWord_cons_cons, signlessWord_singleton]
  have he : signlessPreprojectiveMk k Q (vertexIdempotent k (vertex zigzagD4Graph 1)) ∈
      signlessPreprojectiveGrade k Q 0 :=
    signlessPreprojectiveMk_mem_grade k Q (vertexIdempotent_mem_grade_zero _)
  exact mul_mem_signlessPreprojectiveGrade k Q
    (signlessArrow_mem_signlessPreprojectiveGrade_one k _ _)
    (mul_mem_signlessPreprojectiveGrade k Q
      (signlessArrow_mem_signlessPreprojectiveGrade_one k _ _)
      (mul_mem_signlessPreprojectiveGrade k Q
        (signlessArrow_mem_signlessPreprojectiveGrade_one k _ _)
        (mul_mem_signlessPreprojectiveGrade k Q
          (signlessArrow_mem_signlessPreprojectiveGrade_one k _ _) he)))

/-- In characteristic two, the closed walk through leaves `0` and `2` is not a sum of
commutators. This is stronger than its nonvanishing in the algebra itself. -/
theorem signlessWord_D4_cyclicWord_not_mem_commutatorSubmodule [Nontrivial k]
    (h2 : (2 : k) = 0) : W [1, 2, 1, 0, 1] ∉ commutatorSubmodule k Π := by
  intro hw
  have hker := (commutatorSubmodule_le_ker_iff (φ)).2
    (isSymmetricFrobeniusFunctional_signlessPreprojectiveD4FrobeniusFunctional k h2).apply_mul_comm
  have hzero := LinearMap.mem_ker.mp (hker hw)
  rw [signlessPreprojectiveD4FrobeniusFunctional_cyclicWord] at hzero
  exact one_ne_zero hzero

/-- The cyclic class of the explicit degree-four closed walk is nonzero when `2 = 0`. -/
theorem mkQ_signlessWord_D4_cyclicWord_ne_zero [Nontrivial k] (h2 : (2 : k) = 0) :
    (commutatorSubmodule k Π).mkQ (W [1, 2, 1, 0, 1]) ≠ 0 := by
  intro h
  exact signlessWord_D4_cyclicWord_not_mem_commutatorSubmodule k h2
    ((Submodule.Quotient.mk_eq_zero _).mp h)

private theorem d4Path_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (x : Quiver.TotalPath Q) (hx : 0 < x.2.2.length) :
    signlessPreprojectiveMk k Q (ofPath x) ∈ commutatorSubmodule k Π := by
  -- Transport the graph and its neighbourhood enumerations together: the quotient carrier
  -- retains those enumerations, so rewriting the graph alone is not type correct.
  have key : ∀ (G : SimpleGraph (Fin 4)), G = diagramGraph (DynkinType.D 4).cartanMatrix →
      ∀ [inst : ∀ v, Fintype (G.neighborSet v)] (x : Quiver.TotalPath (DoubledQuiver G)),
        0 < x.2.2.length → signlessPreprojectiveMk k _ (ofPath x) ∈
          commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
    rintro G rfl inst
    have hi : inst = forkNeighborSetFintype (diagramGraph (DynkinType.D 4).cartanMatrix) :=
      Subsingleton.elim _ _
    cases hi
    exact signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k h2
  exact key zigzagD4Graph zigzagD4Graph_eq_diagramGraph x hx

end CommRing

section Field

variable {k} [Field k]

/-- Over a field, the degree-four cyclic quotient of `D₄` vanishes exactly outside
characteristic two. -/
theorem signlessPreprojectiveGrade_D4_four_le_commutatorSubmodule_iff :
    signlessPreprojectiveGrade k Q 4 ≤ commutatorSubmodule k Π ↔ (2 : k) ≠ 0 := by
  refine ⟨fun h h2 => ?_, fun h2 => ?_⟩
  · exact signlessWord_D4_cyclicWord_not_mem_commutatorSubmodule k h2
      (h (signlessWord_D4_cyclicWord_mem_grade_four k))
  · exact signlessPreprojectiveGrade_le_commutatorSubmodule k
      (d4Path_mem_commutatorSubmodule k (isUnit_iff_ne_zero.mpr h2)) (by decide)

/-- Over a field, the commutator submodule of `D₄` equals the augmentation kernel exactly
outside characteristic two. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_D4_eq_ker_iff :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := Q) k).toLinearMap ↔
        (2 : k) ≠ 0 := by
  refine ⟨fun h => ?_, fun h2 => ?_⟩
  · intro h2
    apply signlessWord_D4_cyclicWord_not_mem_commutatorSubmodule k h2
    rw [h, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    simp only [signlessWord_cons_cons, map_mul]
    have hadj : zigzagD4Graph.Adj 2 1 := by decide
    rw [signlessArrow_of_adj k hadj,
      signlessPreprojectiveAugmentation_ofArrow, zero_mul]
  · exact commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
      (d4Path_mem_commutatorSubmodule k (isUnit_iff_ne_zero.mpr h2))

end Field

end TauCeti
