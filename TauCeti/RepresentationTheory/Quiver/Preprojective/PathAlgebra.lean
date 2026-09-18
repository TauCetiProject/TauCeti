/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Symmetrify
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Orientation

/-!
# The path algebra inside the preprojective algebra

Let `Q` be a finite quiver. Its path algebra `kQ` maps to the additive preprojective algebra
`Π_k(Q)`, by including `Q` in the doubled quiver `Quiver.Symmetrify Q` and passing to the quotient.
In the other direction, killing every formal reverse `a*` is an algebra homomorphism from the
doubled path algebra onto `kQ` which kills both backtracks `a a*` and `a* a` of every arrow, hence
the preprojective relator; so it descends to

```text
Π_k(Q) → kQ,
```

and this is a retraction of the first map. Thus `kQ` is simultaneously a subalgebra and a quotient
algebra of `Π_k(Q)`.

The quotient statement bounds `Π_k(Q)` from below: if `Π_k(Q)` is a finite module over a nonzero
commutative ring then so is `kQ`, and `Q` has no oriented cycle. Since `Π_k(Q)` does not depend on
the orientation of `Q` (`TauCeti.reorientPreprojectiveAlgebraEquiv`), the same holds for every
reorientation `TauCeti.Reorient Q σ` of `Q`. A cycle of the underlying multigraph of `Q` — a loop,
a pair of parallel arrows, or a cycle through distinct vertices — becomes an oriented cycle after
turning some of its arrows around. Consequently the preprojective algebra of a quiver whose
underlying graph is not a forest is not a finite module; this includes every quiver of affine type
`Ã_n`.

## Main definitions

* `TauCeti.pathAlgebraToPreprojective`: the algebra homomorphism `kQ →ₐ[k] Π_k(Q)`.
* `TauCeti.preprojectiveToPathAlgebra`: the algebra homomorphism `Π_k(Q) →ₐ[k] kQ` killing the
  formal reverses.

## Main results

* `TauCeti.preprojectiveToPathAlgebra_comp_pathAlgebraToPreprojective`: **the second is a
  retraction of the first**, so that `TauCeti.pathAlgebraToPreprojective_injective` and
  `TauCeti.preprojectiveToPathAlgebra_surjective` hold.
* `TauCeti.isAcyclic_of_module_finite_preprojectiveAlgebra`: a quiver whose preprojective algebra is
  a finite module has no oriented cycle.
* `TauCeti.isAcyclic_reorient_of_module_finite_preprojectiveAlgebra`: **no reorientation of such a
  quiver has an oriented cycle**, and `TauCeti.not_module_finite_preprojectiveAlgebra_of_length_pos`
  is the same statement read from a cycle of a reorientation.

## References

The inclusion of `kQ` in `Π_k(Q)` and the quotient map killing the reverse arrows are standard; see
W. Crawley-Boevey, *Lectures on representations of quivers*, and C. M. Ringel, *The preprojective
algebra of a quiver*, in *Algebras and Modules II*, CMS Conf. Proc. 24 (1998).
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Retraction

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- The algebra homomorphism `kQ →ₐ[k] Π_k(Q)` sending a path of `Q` to the class of the same path
in the doubled quiver. -/
noncomputable def pathAlgebraToPreprojective : pathAlgebra k Q →ₐ[k] preprojectiveAlgebra k Q :=
  (preprojectiveMk k Q).comp (mapAlgHom k Symmetrify.of symmetrify_of_obj_bijective)

/-- The map `kQ →ₐ[k] Π_k(Q)` sends a path of `Q` to the class of the same path in the doubled
quiver. -/
@[simp]
theorem pathAlgebraToPreprojective_ofPath (x : Quiver.TotalPath Q) :
    pathAlgebraToPreprojective k Q (ofPath x) =
      preprojectiveMk k Q (ofPath (Symmetrify.of.mapTotalPath x)) := by
  rw [pathAlgebraToPreprojective, AlgHom.comp_apply, mapAlgHom_ofPath]

/-- The map `kQ →ₐ[k] Π_k(Q)` sends an arrow of `Q` to the class of the same arrow. Deliberately
not a `simp` lemma, `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already rewriting its left-hand side. -/
theorem pathAlgebraToPreprojective_ofArrow {a b : Q} (f : a ⟶ b) :
    pathAlgebraToPreprojective k Q (ofArrow f) =
      preprojectiveMk k Q (ofArrow (Symmetrify.of.map f)) := by
  rw [pathAlgebraToPreprojective, AlgHom.comp_apply, mapAlgHom_ofArrow]

/-- Killing the formal reverses kills the preprojective relator: each summand is a difference of
two backtracks, and every backtrack traverses a formal reverse. -/
private theorem symmetrifyRetraction_preprojectiveRelator :
    symmetrifyRetraction k (preprojectiveRelator k Q) = 0 := by
  simp only [preprojectiveRelator_def, ← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem,
    ← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem, map_sum, map_sub, map_mul,
    symmetrifyRetraction_ofArrow_reverse_of, mul_zero, zero_mul, sub_self,
    Finset.sum_const_zero]

/-- The algebra homomorphism `Π_k(Q) →ₐ[k] kQ` which fixes the vertex idempotents and the arrows of
`Q` and kills every formal reverse. It is the descent of
`TauCeti.PathAlgebra.symmetrifyRetraction` to the preprojective algebra. -/
noncomputable def preprojectiveToPathAlgebra : preprojectiveAlgebra k Q →ₐ[k] pathAlgebra k Q :=
  preprojectiveLift (symmetrifyRetraction k) (symmetrifyRetraction_preprojectiveRelator k Q)

/-- On the class of a doubled path, the retraction `Π_k(Q) →ₐ[k] kQ` is
`TauCeti.PathAlgebra.symmetrifyRetraction`. -/
@[simp]
theorem preprojectiveToPathAlgebra_preprojectiveMk (x : pathAlgebra k (Symmetrify Q)) :
    preprojectiveToPathAlgebra k Q (preprojectiveMk k Q x) = symmetrifyRetraction k x :=
  preprojectiveLift_preprojectiveMk _ _ x

/-- **`kQ` is a retract of `Π_k(Q)`**: the map killing the formal reverses is a left inverse of the
map `kQ →ₐ[k] Π_k(Q)`. -/
@[simp]
theorem preprojectiveToPathAlgebra_comp_pathAlgebraToPreprojective :
    (preprojectiveToPathAlgebra k Q).comp (pathAlgebraToPreprojective k Q) =
      AlgHom.id k (pathAlgebra k Q) :=
  algHom_ext k fun x => by
    rw [AlgHom.comp_apply, pathAlgebraToPreprojective_ofPath,
      preprojectiveToPathAlgebra_preprojectiveMk, symmetrifyRetraction_ofPath_mapTotalPath_of,
      AlgHom.id_apply]

/-- The retraction `Π_k(Q) →ₐ[k] kQ` undoes the map `kQ →ₐ[k] Π_k(Q)`. -/
@[simp]
theorem preprojectiveToPathAlgebra_pathAlgebraToPreprojective (x : pathAlgebra k Q) :
    preprojectiveToPathAlgebra k Q (pathAlgebraToPreprojective k Q x) = x := by
  rw [← AlgHom.comp_apply, preprojectiveToPathAlgebra_comp_pathAlgebraToPreprojective,
    AlgHom.id_apply]

/-- **The path algebra `kQ` embeds in the preprojective algebra `Π_k(Q)`.** -/
theorem pathAlgebraToPreprojective_injective :
    Function.Injective (pathAlgebraToPreprojective k Q) :=
  Function.LeftInverse.injective (preprojectiveToPathAlgebra_pathAlgebraToPreprojective k Q)

/-- **The path algebra `kQ` is a quotient of the preprojective algebra `Π_k(Q)`.** -/
theorem preprojectiveToPathAlgebra_surjective :
    Function.Surjective (preprojectiveToPathAlgebra k Q) :=
  Function.RightInverse.surjective (preprojectiveToPathAlgebra_pathAlgebraToPreprojective k Q)

end Retraction

/-! ### Finite preprojective algebras come from forests -/

section Finiteness

variable (k : Type w) {Q : Type u} [CommRing k] [Nontrivial k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **A quiver whose preprojective algebra is a finite module has no oriented cycle**: the path
algebra is a quotient of the preprojective algebra, hence finite as well. -/
theorem isAcyclic_of_module_finite_preprojectiveAlgebra
    (h : Module.Finite k (preprojectiveAlgebra k Q)) : Quiver.IsAcyclic Q :=
  isAcyclic_of_module_finite_pathAlgebra k Q
    (Module.Finite.of_surjective (preprojectiveToPathAlgebra k Q).toLinearMap
      (preprojectiveToPathAlgebra_surjective k Q))

/-- **A quiver whose preprojective algebra is a finite module has a forest as underlying
multigraph**: no reorientation of it has an oriented cycle. In particular it has no loop, no two
arrows joining the same pair of vertices, and no cycle through distinct vertices. -/
theorem isAcyclic_reorient_of_module_finite_preprojectiveAlgebra
    (h : Module.Finite k (preprojectiveAlgebra k Q)) (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) :
    Quiver.IsAcyclic (Reorient Q σ) :=
  isAcyclic_of_module_finite_preprojectiveAlgebra k
    (Module.Finite.equiv (reorientPreprojectiveAlgebraEquiv k σ).symm.toLinearEquiv)

/-- **The preprojective algebra of a quiver with a cycle is not a finite module**: if some
reorientation of `Q` has an oriented cycle of positive length, then `Π_k(Q)` is not a finite
`k`-module. Taking `σ` to turn no arrow around covers an oriented cycle of `Q` itself. -/
theorem not_module_finite_preprojectiveAlgebra_of_length_pos (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)
    {a : Reorient Q σ} (p : Path a a) (hp : 0 < p.length) :
    ¬ Module.Finite k (preprojectiveAlgebra k Q) := fun h =>
  (isAcyclic_reorient_of_module_finite_preprojectiveAlgebra k h σ).not_length_pos p hp

end Finiteness

end TauCeti
