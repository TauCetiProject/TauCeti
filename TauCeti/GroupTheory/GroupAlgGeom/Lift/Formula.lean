/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic
public import TauCeti.ModelTheory.Algebra.Group.SystemFormula
public import TauCeti.ModelTheory.Positive
import TauCeti.GroupTheory.FreeGroup.Commuting

/-!
# Compatible formulas and lifts of formulas to the generic point

Let `H` be a group receiving the coefficients `G` through `ι : G →* H`, let `S ⊆ G[X]` be a system
of equations, and let `Φ(X, Y)` be a first-order formula of the group language with coefficient
names `A`, the names being read in `G` through `c : A → G`.

* `Φ` is *compatible* with `S` over `H` when every solution `v` of `S` in `H` extends to a tuple
  `(v, w)` at which `Φ` holds in `H`: the algebraic set `V_H(S)` is the projection of the truth
  set of `Φ ∧ S = 1`.
* `Φ` admits an *`S`-lift* when `∃ Y, Φ(μ, Y)` holds in the coordinate group `G_{R(S)}`, where
  `μ : X → G_{R(S)}` is the generic point of `S` and the names are read through the coefficients
  of `G_{R(S)}`.

For the formula of a finite system of equations, with or without one inequation, these are the
notions of `TauCeti.GroupAlgGeom.Lift.IsCompatible`, `TauCeti.GroupAlgGeom.Lift.IsCompatibleNe`,
`TauCeti.GroupAlgGeom.Lift.HasLift` and `TauCeti.GroupAlgGeom.Lift.HasLiftNe` for the images of
the equations in `G[X ⊔ Y]`.

Evaluation at a solution of `S` is a homomorphism from `G_{R(S)}` to `H` sending the generic
point to the solution; it is surjective when `ι` is, for instance when `H = G`. Positive formulas,
built from equations by conjunction, disjunction and both quantifiers, are preserved by surjective
homomorphisms (`FirstOrder.Language.BoundedFormula.IsPositive.realize_comp_of_surjective`), so a
positive formula with an `S`-lift is compatible with `S`. This fails for formulas with
inequations: over a nontrivial group, `y = x ∧ y ≠ 1` admits the lift `y = x` to the generic point
of the empty system, but it is not compatible with it, as it fails over `x = 1`. It also fails
without surjectivity: over the trivial coefficient group the coordinate group of `x = 1` is
trivial, so the positive formula `∀ z, z = 1` admits a lift, while it fails in every nontrivial
`H`. Conversely, compatibility does not give a lift, even for positive formulas: over a free group
on a nonempty set the formula `x = z² ∨ y = z² ∨ x y = z²` is compatible with `[x, y] = 1`, since
one of `x`, `y` and `x y` is a square at every commuting pair, but none of them is a square at the
generic point.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.IsCompatibleFormula ι S c Φ`: `Φ` is compatible with `S` over `H`.
* `TauCeti.GroupAlgGeom.Lift.HasLiftFormula ι S c Φ`: `Φ` admits an `S`-lift.

## Main results

* `TauCeti.GroupAlgGeom.Lift.HasLiftFormula.isCompatibleFormula`: over a surjective coefficient
  map, a positive formula with an `S`-lift is compatible with `S`.
* `TauCeti.GroupAlgGeom.Lift.HasLiftFormula.isCompatibleFormula_toFormula`: over every
  coefficient map, the formula of a system of equations with an `S`-lift is compatible with `S`.
* `TauCeti.GroupAlgGeom.Lift.isCompatibleFormula_toFormula_iff_isCompatibleNe`,
  `TauCeti.GroupAlgGeom.Lift.hasLiftFormula_toFormula_iff_hasLiftNe` and their versions without
  inequation: the formula of a system has the same compatibility and lifts as the system.
* `TauCeti.GroupAlgGeom.Lift.hasLiftFormula_diagonal`,
  `TauCeti.GroupAlgGeom.Lift.not_isCompatibleFormula_diagonal`: a formula with an inequation can
  have an `S`-lift without being compatible with `S`.
* `TauCeti.GroupAlgGeom.Lift.isCompatibleFormula_commutator_sq`,
  `TauCeti.GroupAlgGeom.Lift.not_hasLiftFormula_commutator_sq`: a positive formula compatible with
  `[x, y] = 1` without an `S`-lift.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §6, Definitions 25 and 26.
* O. Kharlampovich, A. Myasnikov, *Algebraic geometry over free groups: lifting solutions into
  generic points*, Contemp. Math. 378 (2005), Introduction.
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

open FirstOrder FirstOrder.Language Monoid.Coprod

variable {G H X Y A : Type*} [Group G] [Group H]

section Defs

variable (ι : G →* H) (S : Set (GX G X)) (c : A → G) (Φ : Language.group[[A]].Formula (X ⊕ Y))

/-- The formula `Φ(X, Y)` of the group language with coefficient names `A`, read through
`c : A → G`, is compatible with `S(X) = 1` over `H`: every solution `v` of `S` in `H` extends to a
tuple `(v, w)` at which `Φ` holds in `H`, the names being interpreted by `ι ∘ c`. -/
def IsCompatibleFormula : Prop :=
  ∀ v ∈ V ι S, ∃ w : Y → H,
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ι ∘ c)
    Φ.Realize (Sum.elim v w)

/-- The formula `Φ(X, Y)` admits an `S`-lift, a lift to the generic point of `S`: the formula
`∃ Y, Φ(μ, Y)` holds in the coordinate group `G_{R(S)}`, where `μ` is the generic point of `S`
and the names are interpreted through the coefficients of `G_{R(S)}`. Unlike the sources, which
define lifts only of compatible formulas, compatibility is not part of this predicate. -/
def HasLiftFormula : Prop :=
  ∃ w : Y → CoordGroup ι S,
    letI : Language.group.Structure (CoordGroup ι S) := TauCeti.Group.structureOfGroup _
    letI : (Language.constantsOn A).Structure (CoordGroup ι S) :=
      Language.constantsOn.structure (CoordGroup.coeff ι S ∘ c)
    Φ.Realize (Sum.elim (CoordGroup.genericPoint ι S) w)

end Defs

variable {ι : G →* H} {S : Set (GX G X)} {c : A → G} {Φ : Language.group[[A]].Formula (X ⊕ Y)}

/-- Compatibility of a formula, unfolded: every solution of `S` in `H` extends to a tuple at
which the formula holds in `H`. -/
theorem isCompatibleFormula_iff :
    IsCompatibleFormula ι S c Φ ↔ ∀ v ∈ V ι S, ∃ w : Y → H,
      letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
      letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ι ∘ c)
      Φ.Realize (Sum.elim v w) :=
  Iff.rfl

/-- An `S`-lift of a formula, unfolded: a tuple of the coordinate group of `S` at which the
formula holds together with the generic point. -/
theorem hasLiftFormula_iff :
    HasLiftFormula ι S c Φ ↔ ∃ w : Y → CoordGroup ι S,
      letI : Language.group.Structure (CoordGroup ι S) := TauCeti.Group.structureOfGroup _
      letI : (Language.constantsOn A).Structure (CoordGroup ι S) :=
        Language.constantsOn.structure (CoordGroup.coeff ι S ∘ c)
      Φ.Realize (Sum.elim (CoordGroup.genericPoint ι S) w) :=
  Iff.rfl

/-- Every formula is compatible with a system that has no solution in `H`. -/
theorem isCompatibleFormula_of_V_eq_empty (hS : V ι S = ∅) : IsCompatibleFormula ι S c Φ :=
  fun v hv => by simp [hS] at hv

/-- When the coordinate group of `S` is trivial, every positive formula admits an `S`-lift. -/
theorem hasLiftFormula_of_subsingleton [Subsingleton (CoordGroup ι S)] (hΦ : Φ.IsPositive) :
    HasLiftFormula ι S c Φ := by
  let : Language.group.Structure (CoordGroup ι S) := TauCeti.Group.structureOfGroup _
  let : (Language.constantsOn A).Structure (CoordGroup ι S) :=
    Language.constantsOn.structure (CoordGroup.coeff ι S ∘ c)
  exact ⟨fun _ => 1, hΦ.realize_of_subsingleton _ _⟩

/-- **Lifts specialise to compatibility for positive formulas.** Over a surjective coefficient map,
for instance over `H = G`, a positive formula with an `S`-lift is compatible with `S`: evaluating
at a solution of `S` is a surjective homomorphism from the coordinate group of `S` to `H`, and
positive formulas are preserved by surjective homomorphisms. For the formula of a system of
equations, which is not positive in this syntactic sense as it contains `⊤`, the same holds over
every coefficient map (`HasLiftFormula.isCompatibleFormula_toFormula`). -/
theorem HasLiftFormula.isCompatibleFormula (hι : Function.Surjective ι) (hΦ : Φ.IsPositive)
    (h : HasLiftFormula ι S c Φ) : IsCompatibleFormula ι S c Φ := by
  let : Language.group.Structure (CoordGroup ι S) := TauCeti.Group.structureOfGroup _
  let : (Language.constantsOn A).Structure (CoordGroup ι S) :=
    Language.constantsOn.structure (CoordGroup.coeff ι S ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ι ∘ c)
  obtain ⟨w, hw⟩ := h
  intro v hv
  let f := CoordGroup.evalGHom v hv
  -- Evaluation at `v` is a homomorphism of structures with names, onto since it extends `ι`.
  let F := MonoidHom.coeffGroupLanguageHom (f : CoordGroup ι S →* H) (CoordGroup.coeff ι S ∘ c)
    (ι ∘ c) fun a => f.map_coeff (c a)
  have hF : ⇑F = f := by simp [F]
  have hFs : Function.Surjective F := hF ▸ fun k => by
    obtain ⟨g, rfl⟩ := hι k
    exact ⟨CoordGroup.coeff ι S g, f.map_coeff g⟩
  refine ⟨f ∘ w, ?_⟩
  have hFw := hΦ.realize_comp_of_surjective hFs hw
  rw [hF, Sum.comp_elim, CoordGroup.evalGHom_comp_genericPoint] at hFw
  -- A formula has no bound variables, so any two assignments of them agree.
  exact (congrArg (BoundedFormula.Realize Φ _) (Subsingleton.elim _ _)).mp hFw

/-! ### Systems of equations and inequations -/

/-- The formula of a finite system of equations `E = 1` of the group language with coefficient
names is compatible with `S` exactly when the system of the images of the equations in
`G[X ⊔ Y]` is. -/
theorem isCompatibleFormula_toFormula_iff_isCompatible (E : List (FreeGroup ((X ⊕ Y) ⊕ A))) :
    IsCompatibleFormula ι S c (EqIneqSystem.toFormula ⟨E, []⟩) ↔
      IsCompatible ι S (EqIneqSystem.toGX (X ⊕ Y) c '' {e | e ∈ E}) := by
  simp [isCompatibleFormula_iff, isCompatible_iff, EqIneqSystem.isSolution_iff,
    ← EqIneqSystem.eval_toGX]

/-- The formula of a finite system of equations `E = 1` and one inequation `W ≠ 1` is compatible
with `S` exactly when the images of the equations and of the inequation in `G[X ⊔ Y]` are. -/
theorem isCompatibleFormula_toFormula_iff_isCompatibleNe (E : List (FreeGroup ((X ⊕ Y) ⊕ A)))
    (W : FreeGroup ((X ⊕ Y) ⊕ A)) :
    IsCompatibleFormula ι S c (EqIneqSystem.toFormula ⟨E, [W]⟩) ↔
      IsCompatibleNe ι S (EqIneqSystem.toGX (X ⊕ Y) c '' {e | e ∈ E})
        (EqIneqSystem.toGX (X ⊕ Y) c W) := by
  simp [isCompatibleFormula_iff, isCompatibleNe_iff, EqIneqSystem.isSolution_iff,
    ← EqIneqSystem.eval_toGX]

/-- The formula of a finite system of equations `E = 1` admits an `S`-lift exactly when the system
of the images of the equations in `G[X ⊔ Y]` does. -/
theorem hasLiftFormula_toFormula_iff_hasLift (E : List (FreeGroup ((X ⊕ Y) ⊕ A))) :
    HasLiftFormula ι S c (EqIneqSystem.toFormula ⟨E, []⟩) ↔
      HasLift ι S (EqIneqSystem.toGX (X ⊕ Y) c '' {e | e ∈ E}) := by
  simp [hasLiftFormula_iff, hasLift_iff, EqIneqSystem.isSolution_iff,
    ← EqIneqSystem.eval_toGX]

/-- The formula of a finite system of equations `E = 1` and one inequation `W ≠ 1` admits an
`S`-lift exactly when the images of the equations and of the inequation in `G[X ⊔ Y]` do. -/
theorem hasLiftFormula_toFormula_iff_hasLiftNe (E : List (FreeGroup ((X ⊕ Y) ⊕ A)))
    (W : FreeGroup ((X ⊕ Y) ⊕ A)) :
    HasLiftFormula ι S c (EqIneqSystem.toFormula ⟨E, [W]⟩) ↔
      HasLiftNe ι S (EqIneqSystem.toGX (X ⊕ Y) c '' {e | e ∈ E})
        (EqIneqSystem.toGX (X ⊕ Y) c W) := by
  simp [hasLiftFormula_iff, hasLiftNe_iff, EqIneqSystem.isSolution_iff,
    ← EqIneqSystem.eval_toGX]

/-- The formula of a finite system of equations with an `S`-lift is compatible with `S`, over
every coefficient map: a solution at the generic point specialises to a solution at each solution
of `S` (`HasLift.isCompatible`). -/
theorem HasLiftFormula.isCompatibleFormula_toFormula {E : List (FreeGroup ((X ⊕ Y) ⊕ A))}
    (h : HasLiftFormula ι S c (EqIneqSystem.toFormula ⟨E, []⟩)) :
    IsCompatibleFormula ι S c (EqIneqSystem.toFormula ⟨E, []⟩) :=
  (isCompatibleFormula_toFormula_iff_isCompatible E).2
    ((hasLiftFormula_toFormula_iff_hasLift E).1 h).isCompatible

/-! ### Examples -/

section Examples

open Term
open scoped commutatorElement

/-- Over a nontrivial group, the formula `y = x ∧ y ≠ 1` admits the lift `y = x` to the generic
point of the empty system. -/
theorem hasLiftFormula_diagonal [Nontrivial H] (ι : G →* H) (c : A → G) :
    HasLiftFormula ι (∅ : Set (GX G Unit)) c
      ((var (Sum.inr ()) : Language.group[[A]].Term (Unit ⊕ Unit)).equal (var (Sum.inl ())) ⊓
        ∼((var (Sum.inr ())).equal 1)) := by
  let : Language.group.Structure (CoordGroup ι (∅ : Set (GX G Unit))) :=
    TauCeti.Group.structureOfGroup _
  let : (Language.constantsOn A).Structure (CoordGroup ι (∅ : Set (GX G Unit))) :=
    Language.constantsOn.structure (CoordGroup.coeff ι ∅ ∘ c)
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  refine hasLiftFormula_iff.2 ⟨fun _ => CoordGroup.genericPoint ι ∅ (), ?_⟩
  simpa using CoordGroup.genericPoint_ne_one_iff.2 ⟨fun _ => h, by simp, hh⟩

/-- The formula `y = x ∧ y ≠ 1` is not compatible with the empty system: it fails over the
solution `x = 1`. With `hasLiftFormula_diagonal`, a formula containing an inequation may admit an
`S`-lift without being compatible with `S`. -/
theorem not_isCompatibleFormula_diagonal (ι : G →* H) (c : A → G) :
    ¬IsCompatibleFormula ι (∅ : Set (GX G Unit)) c
      ((var (Sum.inr ()) : Language.group[[A]].Term (Unit ⊕ Unit)).equal (var (Sum.inl ())) ⊓
        ∼((var (Sum.inr ())).equal 1)) := by
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ι ∘ c)
  intro h
  obtain ⟨w, hw⟩ := h (fun _ => 1) (by simp)
  simp at hw

/-- Surjectivity of the coefficient map cannot be dropped from
`HasLiftFormula.isCompatibleFormula`: over the trivial coefficient group, the coordinate group of
`x = 1` is trivial, so the positive formula `∀ z, z = 1` admits a lift to its generic point, but it
is not compatible with `x = 1` over the group `ℤ/2`. -/
example :
    let Φ : Language.group[[Empty]].Formula (Unit ⊕ Empty) :=
      ((&0 : Language.group[[Empty]].Term ((Unit ⊕ Empty) ⊕ Fin 1)).bdEqual 1).all
    HasLiftFormula (1 : Unit →* Multiplicative (ZMod 2)) {inr (FreeGroup.of ())} Empty.elim Φ ∧
      ¬IsCompatibleFormula (1 : Unit →* Multiplicative (ZMod 2)) {inr (FreeGroup.of ())}
        Empty.elim Φ := by
  intro Φ
  -- Every word vanishes at the only solution `x = 1`, so the coordinate group is trivial.
  have : Subsingleton (CoordGroup (1 : Unit →* Multiplicative (ZMod 2))
      {(inr (FreeGroup.of ()) : GX Unit Unit)}) :=
    CoordGroup.subsingleton_iff.2 fun v hv => by
      obtain rfl : v = 1 := funext fun _ => by simpa using hv
      exact eval_one_one
  refine ⟨hasLiftFormula_of_subsingleton (BoundedFormula.isPositive_bdEqual _ _).all, fun h => ?_⟩
  let : Language.group.Structure (Multiplicative (ZMod 2)) := TauCeti.Group.structureOfGroup _
  let : (Language.constantsOn Empty).Structure (Multiplicative (ZMod 2)) :=
    Language.constantsOn.structure ((1 : Unit →* Multiplicative (ZMod 2)) ∘ Empty.elim)
  obtain ⟨w, hw⟩ := h (fun _ => 1) (by simp)
  have h10 : (1 : ZMod 2) = 0 := by
    simpa [Φ, Formula.Realize, Fin.snoc] using hw (Multiplicative.ofAdd 1)
  exact absurd h10 (by decide)

open FreeGroup in
/-- Over a free group, the positive formula `x = z² ∨ y = z² ∨ x y = z²` is compatible with the
equation `[x, y] = 1`: one of `x`, `y` and `x y` is a square at every commuting pair. -/
theorem isCompatibleFormula_commutator_sq {α : Type*} (c : A → FreeGroup α) :
    IsCompatibleFormula (.id (FreeGroup α))
      {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆} c
      ((var (Sum.inl false) : Language.group[[A]].Term (Bool ⊕ Unit)).equal
          (var (Sum.inr ()) * var (Sum.inr ())) ⊔
        (var (Sum.inl true)).equal (var (Sum.inr ()) * var (Sum.inr ())) ⊔
        (var (Sum.inl false) * var (Sum.inl true) : Language.group[[A]].Term (Bool ⊕ Unit)).equal
          (var (Sum.inr ()) * var (Sum.inr ()))) := by
  let : Language.group.Structure (FreeGroup α) := TauCeti.Group.structureOfGroup _
  let : (Language.constantsOn A).Structure (FreeGroup α) :=
    Language.constantsOn.structure (MonoidHom.id (FreeGroup α) ∘ c)
  intro v hv
  obtain ⟨z, hz⟩ := IsFreeGroup.exists_eq_sq_of_commute (mem_V_commutator_iff.1 hv)
  refine ⟨fun _ => z, ?_⟩
  simpa [sq, or_assoc] using hz

open FreeGroup in
/-- Over a free group on a nonempty set, the positive formula `x = z² ∨ y = z² ∨ x y = z²` admits
no lift to the generic point of `[x, y] = 1`, although it is compatible with it
(`isCompatibleFormula_commutator_sq`): compatibility does not imply the existence of a lift. -/
theorem not_hasLiftFormula_commutator_sq {α : Type*} [Nonempty α] (c : A → FreeGroup α) :
    ¬HasLiftFormula (.id (FreeGroup α))
      {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆} c
      ((var (Sum.inl false) : Language.group[[A]].Term (Bool ⊕ Unit)).equal
          (var (Sum.inr ()) * var (Sum.inr ())) ⊔
        (var (Sum.inl true)).equal (var (Sum.inr ()) * var (Sum.inr ())) ⊔
        (var (Sum.inl false) * var (Sum.inl true) : Language.group[[A]].Term (Bool ⊕ Unit)).equal
          (var (Sum.inr ()) * var (Sum.inr ()))) := by
  rintro ⟨w, hw⟩
  refine not_exists_genericPoint_eq_sq ⟨w (), ?_⟩
  simpa [sq, or_assoc] using hw

end Examples

end TauCeti.GroupAlgGeom.Lift
