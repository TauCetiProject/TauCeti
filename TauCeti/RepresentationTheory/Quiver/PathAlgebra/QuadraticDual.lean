/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading

/-!
# Quadratic duality for path algebras

A quadratic algebra presented on a quiver `Q` is `kQ / (R)` for a space `R` of `k`-linear
combinations of paths of length two. Its **quadratic dual** is presented on the opposite quiver by
the orthogonal complement `R^⊥` of `R` for the pairing which makes the paths of length two an
orthonormal family: the arrow space of the opposite quiver is dual to the arrow space of `Q`
through the dual basis of the arrows, and the induced pairing of length-two paths is the diagonal
one.

The path algebra of the opposite quiver is the opposite algebra `(kQ)ᵐᵒᵖ`, and this file uses the
latter directly, so that the orthogonal complement `R^⊥` is a space of length-two elements of `kQ`
and the dual algebra is

```text
(kQ)ᵐᵒᵖ / (op R^⊥).
```

Working on the opposite side is not a convention that can be dropped: a length-two path `b a` of
`Q`, read later-factor-first, pairs with the dual arrows in the order `a* b*`, which is a path of
the opposite quiver. For a quiver with an involutive reversal of arrows the two sides are
identified by `TauCeti.PathAlgebra.reverseOpAlgEquiv`, and the dual algebra can then be presented
back on `Q` itself.

The pairing is defined on the whole path algebra, not just on its degree-two piece: it is the
pairing of `TauCeti.pathAlgebraBasis` with itself, so the coordinate of an element on a path is its
pairing with that path. Restricting the orthogonality condition to degree two is what
`TauCeti.PathAlgebra.quadraticOrthogonal` does.

## Implementation notes

`TauCeti.PathAlgebra.pathPairing` is `Module.Basis.toDual` of the path basis with the decidable
equality of paths fixed classically. Fixing it is what keeps `DecidableEq (Quiver.TotalPath Q)` out
of the signatures below, which no quiver supplies; the pairing itself does not depend on the
choice.

Duality here is taken through the path basis: `R^⊥` is the annihilator of `R` inside the
degree-two part of `kQ` itself, and the degree-one part of `(kQ)ᵐᵒᵖ` is the span of the dual
arrows. That span is *all* of the dual of the arrow module exactly when the quiver has finitely
many arrows, `[∀ a b : Q, Finite (a ⟶ b)]` on top of the `[Finite Q]` the path algebra already
asks for: a free module is identified with its full linear dual by its dual basis only in finite
rank. With infinitely many arrows the full dual is a product of which the opposite quiver spans
only the direct sum, so the construction below is then the graded (dual-basis) variant rather than
the classical quadratic dual, and a biduality statement `(A^!)^! = A` — which this file does not
make — would have to assume the arrows finite. The definitions themselves are stated for an
arbitrary quiver and carry no finiteness beyond what the path algebra needs, as
`Submodule.dualAnnihilator` carries none; the quivers they are applied to, the doubled quivers of
finite simple graphs, have finitely many arrows.

## Main definitions

* `TauCeti.PathAlgebra.pathPairing`: the pairing of the path algebra with itself for which the
  paths are an orthonormal family.
* `TauCeti.PathAlgebra.quadraticOrthogonal`: the orthogonal complement `R^⊥` inside the degree-two
  piece.
* `TauCeti.PathAlgebra.quadraticDualIdeal` and `TauCeti.PathAlgebra.quadraticDual`: the relation
  ideal of the quadratic dual inside `(kQ)ᵐᵒᵖ`, and the quadratic dual algebra, with quotient map
  `TauCeti.PathAlgebra.quadraticDualMk` and universal property
  `TauCeti.PathAlgebra.quadraticDualLift`.

## Main results

* `TauCeti.PathAlgebra.pathPairing_apply_ofPath` and
  `TauCeti.PathAlgebra.pathPairing_ofPath_apply`: pairing with a path reads off the coordinate on
  it.
* `TauCeti.PathAlgebra.mem_quadraticOrthogonal_span_iff`: orthogonality to a spanning set of
  relations suffices.

## References

Quadratic duality of quadratic algebras over a semisimple base, in the form used for quiver
algebras, follows A. Polishchuk and L. Positselski, *Quadratic algebras*, Chapter 1, Section 2.
-/

public section

namespace TauCeti

open _root_.Quiver MulOpposite

universe u v w

namespace PathAlgebra

/-! ### The pairing of the path basis with itself -/

section Pairing

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q]

/-- The pairing of the path algebra with itself for which the paths of `Q` are an orthonormal
family: `⟨f, g⟩` is the sum over the paths `x` of the product of the coordinates of `f` and `g` on
`x`. It is the pairing which identifies the degree-two part of the path algebra with its own dual
space, and so computes the relations of a quadratic dual. -/
noncomputable def pathPairing : pathAlgebra k Q →ₗ[k] Module.Dual k (pathAlgebra k Q) :=
  letI : DecidableEq (Quiver.TotalPath Q) := Classical.decEq _
  (pathAlgebraBasis k Q).toDual

variable {k Q}

/-- Pairing with a path reads off the coordinate on that path. -/
@[simp]
theorem pathPairing_apply_ofPath (f : pathAlgebra k Q) (x : Quiver.TotalPath Q) :
    pathPairing k Q f (ofPath x) = (pathAlgebraBasis k Q).repr f x := by
  let : DecidableEq (Quiver.TotalPath Q) := Classical.decEq _
  simpa only [pathPairing, coe_pathAlgebraBasis] using
    (pathAlgebraBasis k Q).toDual_apply_left f x

/-- The pairing is symmetric on the path basis: pairing a path with an element reads off the
coordinate of that element on the path. -/
@[simp]
theorem pathPairing_ofPath_apply (x : Quiver.TotalPath Q) (g : pathAlgebra k Q) :
    pathPairing k Q (ofPath x) g = (pathAlgebraBasis k Q).repr g x := by
  let : DecidableEq (Quiver.TotalPath Q) := Classical.decEq _
  simpa only [pathPairing, coe_pathAlgebraBasis] using
    (pathAlgebraBasis k Q).toDual_apply_right x g

end Pairing

/-! ### The orthogonal complement of a space of quadratic relations -/

section Orthogonal

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q]

/-- The **orthogonal complement of a space of quadratic relations**: the degree-two elements of the
path algebra pairing to zero with every element of `R`. It is the relation space of the quadratic
dual, read on the path algebra of `Q` rather than of its opposite. -/
noncomputable def quadraticOrthogonal (R : Submodule k (pathAlgebra k Q)) :
    Submodule k (pathAlgebra k Q) :=
  grade k Q 2 ⊓ Submodule.comap (pathPairing k Q) R.dualAnnihilator

variable {k Q}

/-- Membership of the orthogonal complement: degree two, and orthogonality to every relation. -/
theorem mem_quadraticOrthogonal_iff {R : Submodule k (pathAlgebra k Q)}
    {f : pathAlgebra k Q} :
    f ∈ quadraticOrthogonal k Q R ↔ f ∈ grade k Q 2 ∧ ∀ g ∈ R, pathPairing k Q f g = 0 := by
  simp only [quadraticOrthogonal, Submodule.mem_inf, Submodule.mem_comap,
    Submodule.mem_dualAnnihilator]

/-- **Orthogonality to a spanning set of relations suffices**: for a relation space presented by
generators, only the generators have to be tested. -/
theorem mem_quadraticOrthogonal_span_iff {S : Set (pathAlgebra k Q)} {f : pathAlgebra k Q} :
    f ∈ quadraticOrthogonal k Q (Submodule.span k S) ↔
      f ∈ grade k Q 2 ∧ ∀ g ∈ S, pathPairing k Q f g = 0 := by
  rw [mem_quadraticOrthogonal_iff]
  refine and_congr_right fun _ =>
    ⟨fun h g hg => h g (Submodule.subset_span hg), fun h g hg => ?_⟩
  exact Submodule.span_le.2 (fun y hy => LinearMap.mem_ker.2 (h y hy)) hg

/-- The orthogonal complement consists of degree-two elements. -/
theorem quadraticOrthogonal_le_grade_two (R : Submodule k (pathAlgebra k Q)) :
    quadraticOrthogonal k Q R ≤ grade k Q 2 :=
  inf_le_left

/-- The orthogonal complement is antitone in the space of relations. -/
theorem quadraticOrthogonal_antitone :
    Antitone (quadraticOrthogonal k Q) := fun _ _ h =>
  inf_le_inf_left _ (Submodule.comap_mono (Submodule.dualAnnihilator_anti h))

end Orthogonal

/-! ### The quadratic dual algebra -/

section Dual

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Finite Q]
  (R : Submodule k (pathAlgebra k Q))

/-- The relation ideal of the quadratic dual: the two-sided ideal of the opposite path algebra
generated by the orthogonal complement of `R`. -/
noncomputable def quadraticDualIdeal : TwoSidedIdeal (pathAlgebra k Q)ᵐᵒᵖ :=
  TwoSidedIdeal.span (op '' (quadraticOrthogonal k Q R : Set (pathAlgebra k Q)))

/-- The dual relation ideal is the two-sided span of the orthogonal complement. -/
theorem quadraticDualIdeal_eq_span :
    quadraticDualIdeal k Q R =
      TwoSidedIdeal.span (op '' (quadraticOrthogonal k Q R : Set (pathAlgebra k Q))) := by
  rw [quadraticDualIdeal]

variable {k Q R}

/-- Every orthogonal relation lies in the dual relation ideal. -/
theorem op_mem_quadraticDualIdeal {f : pathAlgebra k Q} (hf : f ∈ quadraticOrthogonal k Q R) :
    op f ∈ quadraticDualIdeal k Q R :=
  TwoSidedIdeal.subset_span ⟨f, hf, rfl⟩

variable (k Q R)

/-- The **quadratic dual algebra** of the quadratic algebra `kQ / (R)`: the opposite path algebra
modulo the orthogonal complement of `R`. The dual relations are read through the path basis; see
the implementation notes for the finiteness of the arrows under which this is the classical
quadratic dual rather than its graded variant. -/
noncomputable abbrev quadraticDual : Type _ :=
  (pathAlgebra k Q)ᵐᵒᵖ ⧸ (quadraticDualIdeal k Q R).asIdeal

/-- The quotient map onto the quadratic dual algebra. -/
noncomputable def quadraticDualMk : (pathAlgebra k Q)ᵐᵒᵖ →ₐ[k] quadraticDual k Q R :=
  Ideal.Quotient.mkₐ k _

theorem quadraticDualMk_apply (f : (pathAlgebra k Q)ᵐᵒᵖ) :
    quadraticDualMk k Q R f = Ideal.Quotient.mk (quadraticDualIdeal k Q R).asIdeal f := by
  rw [quadraticDualMk, Ideal.Quotient.mkₐ_eq_mk]

theorem quadraticDualMk_surjective : Function.Surjective (quadraticDualMk k Q R) :=
  Ideal.Quotient.mk_surjective

@[simp]
theorem quadraticDualMk_eq_zero_iff {f : (pathAlgebra k Q)ᵐᵒᵖ} :
    quadraticDualMk k Q R f = 0 ↔ f ∈ quadraticDualIdeal k Q R := by
  rw [quadraticDualMk_apply, Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal]

variable {k Q R}

/-- **The defining relations of the quadratic dual**: every orthogonal relation dies in it. -/
@[simp]
theorem quadraticDualMk_op_eq_zero {f : pathAlgebra k Q} (hf : f ∈ quadraticOrthogonal k Q R) :
    quadraticDualMk k Q R (op f) = 0 :=
  (quadraticDualMk_eq_zero_iff k Q R).2 (op_mem_quadraticDualIdeal hf)

end Dual

/-! ### The universal property of the quadratic dual -/

section Lift

variable {k : Type w} {Q : Type u} {B : Type*} [CommRing k] [Quiver.{v} Q] [Finite Q]
  [Semiring B] [Algebra k B] {R : Submodule k (pathAlgebra k Q)}
  (f : (pathAlgebra k Q)ᵐᵒᵖ →ₐ[k] B)

/-- An algebra map out of the opposite path algebra which kills every orthogonal relation kills the
dual relation ideal. -/
theorem quadraticDualIdeal_le_ker
    (hf : ∀ x ∈ quadraticOrthogonal k Q R, f (op x) = 0) :
    quadraticDualIdeal k Q R ≤ TwoSidedIdeal.ker f := by
  rw [quadraticDualIdeal_eq_span]
  refine TwoSidedIdeal.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (TwoSidedIdeal.mem_ker f).2 (hf x hx)

/-- **The universal property of the quadratic dual**: an algebra map out of the opposite path
algebra which kills every orthogonal relation descends to the quadratic dual. -/
noncomputable def quadraticDualLift (hf : ∀ x ∈ quadraticOrthogonal k Q R, f (op x) = 0) :
    quadraticDual k Q R →ₐ[k] B :=
  Ideal.Quotient.liftₐ _ f fun _ ha =>
    (TwoSidedIdeal.mem_ker f).1 (quadraticDualIdeal_le_ker f hf (TwoSidedIdeal.mem_asIdeal.1 ha))

/-- The lift descends `f`: composing it with the quotient map recovers `f`. -/
theorem quadraticDualLift_comp_quadraticDualMk
    (hf : ∀ x ∈ quadraticOrthogonal k Q R, f (op x) = 0) :
    (quadraticDualLift f hf).comp (quadraticDualMk k Q R) = f := by
  rw [quadraticDualLift, quadraticDualMk, Ideal.Quotient.liftₐ_comp]

/-- Pointwise, the lift sends the quadratic dual class of `x` to `f x`. -/
@[simp]
theorem quadraticDualLift_quadraticDualMk (hf : ∀ x ∈ quadraticOrthogonal k Q R, f (op x) = 0)
    (x : (pathAlgebra k Q)ᵐᵒᵖ) :
    quadraticDualLift f hf (quadraticDualMk k Q R x) = f x :=
  AlgHom.congr_fun (quadraticDualLift_comp_quadraticDualMk f hf) x

/-- The lift is the only algebra map whose composite with the quotient map is `f`. -/
theorem quadraticDualLift_unique (hf : ∀ x ∈ quadraticOrthogonal k Q R, f (op x) = 0)
    (g : quadraticDual k Q R →ₐ[k] B) (hg : g.comp (quadraticDualMk k Q R) = f) :
    g = quadraticDualLift f hf := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := quadraticDualMk_surjective k Q R y
  rw [quadraticDualLift_quadraticDualMk, ← hg, AlgHom.comp_apply]

end Lift

end PathAlgebra

end TauCeti
