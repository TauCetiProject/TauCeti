/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Diagonal orbits and stabilizer orbits

If `G` acts transitively on `Y`, fixing a point `y : Y` identifies the diagonal orbit space
of `X × Y` with the orbit space of `X` under the stabilizer of `y`. This is useful for replacing
an object with a moving marked point by an object whose mark is fixed once and for all.

The forward map is canonical: it sends the stabilizer orbit of `x` to the diagonal orbit of
`(x, y)`. Its injectivity does not require transitivity. Transitivity supplies surjectivity;
the inverse sends the orbit of `(x, g • y)` to the stabilizer orbit of `g⁻¹ • x`.

The diagonal action on `X × Y` is free when the action on the first factor is
(`TauCeti.isCancelSMul_prod`).

When every orbit of every point stabilizer on `S` is finite (`TauCeti.FiniteStabilizerOrbits`),
injectivity of the forward map shows that each diagonal orbit of `S × S` meets every row and every
column in finitely many points.
-/

public section

namespace TauCeti.MulAction

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

/-- Attach a fixed mark `y` to a stabilizer orbit, giving a diagonal orbit. -/
def orbitRelQuotientStabilizerMap (y : Y) :
    MulAction.orbitRel.Quotient (MulAction.stabilizer G y) X →
      MulAction.orbitRel.Quotient G (X × Y) :=
  Quotient.map' (fun x => (x, y)) fun _ _ ⟨g, hg⟩ =>
    ⟨g, Prod.ext (by simpa [Subgroup.smul_def] using hg) (MulAction.mem_stabilizer_iff.mp
        g.property)⟩

@[simp]
theorem orbitRelQuotientStabilizerMap_mk (y : Y) (x : X) :
    orbitRelQuotientStabilizerMap (G := G) y (Quotient.mk'' x) = Quotient.mk'' (x, y) :=
  (rfl)

/-- Fixing the mark identifies stabilizer orbits faithfully with diagonal orbits. -/
theorem orbitRelQuotientStabilizerMap_injective (y : Y) :
    Function.Injective (orbitRelQuotientStabilizerMap (G := G) (X := X) y) := by
  rintro ⟨x⟩ ⟨x'⟩ h
  obtain ⟨g, hg⟩ := Quotient.exact' h
  refine Quotient.sound' ⟨⟨g, MulAction.mem_stabilizer_iff.mpr (congrArg Prod.snd hg)⟩, ?_⟩
  simpa [Subgroup.smul_def] using congrArg Prod.fst hg

/-- Every diagonal orbit admits a representative with mark `y` when the marking action is
transitive. -/
theorem orbitRelQuotientStabilizerMap_surjective [MulAction.IsPretransitive G Y] (y : Y) :
    Function.Surjective (orbitRelQuotientStabilizerMap (G := G) (X := X) y) := by
  rintro ⟨x, z⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G y z
  exact ⟨Quotient.mk'' (g⁻¹ • x), Quotient.sound' ⟨g⁻¹, by simp⟩⟩

/-- Stabilizer orbits with a fixed mark are exactly diagonal orbits with a moving mark. -/
noncomputable def orbitRelQuotientStabilizerEquiv [MulAction.IsPretransitive G Y] (y : Y) :
    MulAction.orbitRel.Quotient (MulAction.stabilizer G y) X ≃
      MulAction.orbitRel.Quotient G (X × Y) :=
  Equiv.ofBijective (orbitRelQuotientStabilizerMap y)
    ⟨orbitRelQuotientStabilizerMap_injective y, orbitRelQuotientStabilizerMap_surjective y⟩

@[simp]
theorem orbitRelQuotientStabilizerEquiv_mk [MulAction.IsPretransitive G Y] (y : Y) (x : X) :
    orbitRelQuotientStabilizerEquiv (G := G) y (Quotient.mk'' x) = Quotient.mk'' (x, y) :=
  (rfl)

@[simp]
theorem orbitRelQuotientStabilizerEquiv_symm_mk [MulAction.IsPretransitive G Y]
    (y : Y) (x : X) :
    (orbitRelQuotientStabilizerEquiv (G := G) y).symm (Quotient.mk'' (x, y)) =
      Quotient.mk'' x := by
  rw [Equiv.symm_apply_eq, orbitRelQuotientStabilizerEquiv_mk]

/-- Move the mark back to `y` by applying the inverse translator to the object as well. -/
@[simp]
theorem orbitRelQuotientStabilizerEquiv_symm_mk_smul [MulAction.IsPretransitive G Y]
    (y : Y) (x : X) (g : G) :
    (orbitRelQuotientStabilizerEquiv (G := G) y).symm (Quotient.mk'' (x, g • y)) =
      Quotient.mk'' (g⁻¹ • x) := by
  rw [Equiv.symm_apply_eq, orbitRelQuotientStabilizerEquiv_mk]
  exact Quotient.sound' ⟨g, by simp⟩

end TauCeti.MulAction

namespace TauCeti

open _root_.MulAction

section FiniteStabilizerOrbits

variable (G S : Type*) [Group G] [MulAction G S]

/-- Every orbit of every point stabilizer is finite: for all `x y : S`, the orbit of `y` under the
stabilizer of `x` is finite. This holds when `G` is a topological group and every point stabilizer
is compact and open (`TauCeti.FiniteStabilizerOrbits.of_isCompact_of_isOpen`). -/
class FiniteStabilizerOrbits : Prop where
  finite_orbit (x y : S) : (orbit (stabilizer G x) y).Finite

variable {G S} [FiniteStabilizerOrbits G S]

/-- The points `t` with `(t, s)` in a given diagonal orbit form a finite set: they lie in one orbit
of the stabilizer of `s`. -/
theorem FiniteStabilizerOrbits.finite_setOf_mk_left_eq (s : S)
    (q : Quotient (orbitRel G (S × S))) :
    {t | Quotient.mk (orbitRel G (S × S)) (t, s) = q}.Finite := by
  rcases Set.eq_empty_or_nonempty {t | Quotient.mk (orbitRel G (S × S)) (t, s) = q} with
    h | ⟨t₀, ht₀⟩
  · simp [h]
  refine (FiniteStabilizerOrbits.finite_orbit (G := G) s t₀).subset fun t ht ↦ ?_
  have hst : MulAction.orbitRelQuotientStabilizerMap (G := G) s (Quotient.mk'' t) =
      MulAction.orbitRelQuotientStabilizerMap s (Quotient.mk'' t₀) := by
    simpa using ht.trans ht₀.symm
  exact Quotient.exact' (MulAction.orbitRelQuotientStabilizerMap_injective s hst)

/-- The points `y` with `(x, y)` in a given diagonal orbit form a finite set, by swapping
coordinates. -/
theorem FiniteStabilizerOrbits.finite_setOf_mk_right_eq (x : S)
    (q : Quotient (orbitRel G (S × S))) :
    {y | Quotient.mk (orbitRel G (S × S)) (x, y) = q}.Finite :=
  (finite_setOf_mk_left_eq x (Quotient.map' (s₁ := orbitRel G (S × S))
    (s₂ := orbitRel G (S × S)) Prod.swap (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩) q)).subset
    fun _ hy ↦ by subst hy; rw [Set.mem_ofPred_eq, Quotient.map'_mk'', Prod.swap_prod_mk]

end FiniteStabilizerOrbits

/-- **A diagonal action is free when it is free on the first factor** and left-cancellative on
the second, as every group action is: an element of `G` fixing a pair fixes its first coordinate.
-/
@[to_additive /-- **A diagonal additive action is free when it is free on the first factor** and
left-cancellative on the second. -/]
instance isCancelSMul_prod {G X Y : Type*} [SMul G X] [SMul G Y] [IsCancelSMul G X]
    [IsLeftCancelSMul G Y] : IsCancelSMul G (X × Y) where
  left_cancel' g _ _ h := Prod.ext (IsCancelSMul.left_cancel g _ _ (congrArg Prod.fst h))
    (IsLeftCancelSMul.left_cancel g _ _ (congrArg Prod.snd h))
  right_cancel' g g' x hx := IsCancelSMul.right_cancel g g' x.1 (congrArg Prod.fst hx)

end TauCeti
