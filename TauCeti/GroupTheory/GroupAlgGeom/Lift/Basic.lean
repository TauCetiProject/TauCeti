/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic

/-!
# Compatible equations and lifts to the generic point

Let `H` be a group receiving the coefficients `G` through `ι : G →* H`, let `S ⊆ G[X]` be a system
of equations and let `T ⊆ G[X ⊔ Y]` be a system in the variables `X` and further variables `Y`.

* `T` is *compatible* with `S` over `H` when every solution `v` of `S` in `H` extends to a
  solution `(v, w)` of `T` in `H`: the algebraic set `V_H(S)` is the projection of `V_H(S ∪ T)`.
* `T` admits an *`S`-lift* (a lift to the generic point of `S`) when `T(μ, Y) = 1` has a solution
  in the coordinate group `G_{R(S)}`, where `μ : X → G_{R(S)}` is the generic point of `S`, the
  tuple of the images of the variables. Such a solution is a *formal solution* of `T`.
* `T` admits a *complete `S`-lift* when it admits an `S`-lift and, for every inequation `W ≠ 1`
  such that `T = 1 ∧ W ≠ 1` is compatible with `S`, the system `T(μ, Y) = 1 ∧ W(μ, Y) ≠ 1` has a
  solution in `G_{R(S)}`.
* A family `Θ` of solutions of `S` is *generic* when every single equation `t(X, Y) = 1` such
  that `t(θ, Y) = 1` is solvable in `H` for every `θ ∈ Θ` admits a complete `S`-lift.

Evaluating at a solution of `S` specialises a formal solution, so an `S`-lift of a system of
equations forces compatibility (`HasLift.isCompatible`). This can fail once an inequation is
present: over a nontrivial group and the empty system, `y = x ∧ y ≠ 1` has the solution `y = x`
at the generic point but no solution at `x = 1` (`hasLiftNe_diagonal`,
`not_isCompatibleNe_diagonal`). In the other direction, over a free group `F` on a nonempty set
the formula `x = z² ∨ y = z² ∨ x y = z²` holds at every solution of `[x, y] = 1` in `F`
(`mem_V_commutator_iff`, `IsFreeGroup.exists_eq_sq_of_commute`), but not at the generic point of
`[x, y] = 1` (`not_exists_genericPoint_eq_sq`). Over a non-abelian free group a disjunction of
equations is equivalent to a single equation; with that encoding, which is not formalized here,
this example gives an equation compatible with `[x, y] = 1` without an `S`-lift. With an
inequation such an example is immediate: over a nontrivial group, `[y, x] = 1 ∧ y ≠ 1` is
compatible with every system, taking `y = x` over a solution with `x ≠ 1` and any `y ≠ 1` over
one with `x = 1`, but it admits an `S`-lift only when the coordinate group of `S` is nontrivial
(`isCompatibleNe_commutator_iff`, `hasLiftNe_commutator_iff`). This fails for the equation
`x = 1` over the trivial coefficient group.

The definitions follow the sources, which take `H = G` and assume that `S` has a solution. For a
system `S` without solutions the coordinate group is trivial, so every system of equations is
compatible with `S` and admits an `S`-lift (`isCompatible_of_V_eq_empty`,
`hasLift_of_V_eq_empty`), while no system admits a complete `S`-lift
(`not_hasCompleteLift_of_V_eq_empty`).

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.IsCompatible ι S T`,
  `TauCeti.GroupAlgGeom.Lift.IsCompatibleNe ι S T W`: compatibility with `S` of the system
  `T = 1`, respectively of `T = 1 ∧ W ≠ 1`.
* `TauCeti.GroupAlgGeom.Lift.HasLift ι S T`, `TauCeti.GroupAlgGeom.Lift.HasLiftNe ι S T W`:
  solvability at the generic point of `S` of `T = 1`, respectively of `T = 1 ∧ W ≠ 1`.
* `TauCeti.GroupAlgGeom.Lift.HasCompleteLift ι S T`: `T` admits a complete `S`-lift.
* `TauCeti.GroupAlgGeom.Lift.IsGenericFamily ι S Θ`: `Θ` is a generic family of solutions of `S`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.HasLift.isCompatible`: a system of equations with an `S`-lift is
  compatible with `S`.
* `TauCeti.GroupAlgGeom.Lift.hasLift_of_mem_V_inl`: a solution of `T` in `G[X]` at the tuple of
  variables gives an `S`-lift for every `S`.
* `TauCeti.GroupAlgGeom.Lift.hasCompleteLift_iff_of_ne`: when some coefficient is nontrivial in
  `H`, a complete `S`-lift is compatibility together with the lifting of every compatible
  inequation.
* `TauCeti.GroupAlgGeom.Lift.hasCompleteLift_of_subsingleton`: over a trivial group every system
  admits a complete lift, no inequation being compatible.
* `TauCeti.GroupAlgGeom.Lift.IsCompatible.hasCompleteLift_of_V_eq_singleton`,
  `TauCeti.GroupAlgGeom.Lift.isGenericFamily_singleton`: if `S` has a unique solution in `G`, every
  system compatible with `S` admits a complete `S`-lift, and the solution is a generic family.
* `TauCeti.GroupAlgGeom.Lift.isGenericFamily_empty_iff`: the empty family is generic exactly over
  a trivial group.
* `TauCeti.GroupAlgGeom.Lift.hasLift_sq_eq_sq`,
  `TauCeti.GroupAlgGeom.Lift.not_isCompatible_empty_sq`: `y² = x²` lifts over every system, while
  `y² = x` is not compatible with the empty system over a free group.
* `TauCeti.GroupAlgGeom.Lift.hasLift_range_mul_inv`: the system `y = u_y(X)`, for words
  `u_y ∈ G[X]`, admits an `S`-lift for every system `S`.
* `TauCeti.GroupAlgGeom.Lift.isCompatibleNe_commutator_iff`,
  `TauCeti.GroupAlgGeom.Lift.hasLiftNe_commutator_iff`: the system `[y, x] = 1 ∧ y ≠ 1` is
  compatible with `S` exactly when `H` is nontrivial, and admits an `S`-lift exactly when the
  coordinate group of `S` is nontrivial.
* `TauCeti.GroupAlgGeom.Lift.not_exists_genericPoint_eq_sq`: over a free group on a nonempty set,
  none of `x`, `y` and `x y` is a square at the generic point of `[x, y] = 1`, while one of them is
  a square at every solution (`IsFreeGroup.exists_eq_sq_of_commute`).

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §6, Definitions 24–27, and §7.6, Definition 44.
* O. Kharlampovich, A. Myasnikov, *Algebraic geometry over free groups: lifting solutions into
  generic points*, Contemp. Math. 378 (2005), Introduction and §2.
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

open Monoid.Coprod

variable {G H X Y : Type*} [Group G] [Group H]

/-! ### Compatibility -/

section Defs

variable (ι : G →* H) (S : Set (GX G X)) (T : Set (GX G (X ⊕ Y))) (W : GX G (X ⊕ Y))

/-- The system of equations `T(X, Y) = 1` is compatible with `S(X) = 1` over `H`: every solution
`v` of `S` in `H` extends to a solution `(v, w)` of `T` in `H`. -/
def IsCompatible : Prop :=
  ∀ v ∈ V ι S, ∃ w : Y → H, Sum.elim v w ∈ V ι T

/-- The system `T(X, Y) = 1 ∧ W(X, Y) ≠ 1` is compatible with `S(X) = 1` over `H`: every solution
`v` of `S` in `H` extends to a solution `(v, w)` of `T` in `H` at which `W` does not vanish. -/
def IsCompatibleNe : Prop :=
  ∀ v ∈ V ι S, ∃ w : Y → H, Sum.elim v w ∈ V ι T ∧ eval ι (Sum.elim v w) W ≠ 1

/-- The system of equations `T(X, Y) = 1` admits an `S`-lift, a lift to the generic point of
`S`: the system `T(μ, Y) = 1` has a solution in the coordinate group `G_{R(S)}`, where `μ` is
the generic point of `S`. -/
def HasLift : Prop :=
  ∃ w : Y → CoordGroup ι S,
    Sum.elim (CoordGroup.genericPoint ι S) w ∈ V (CoordGroup.coeff ι S) T

/-- The system `T(X, Y) = 1 ∧ W(X, Y) ≠ 1` admits an `S`-lift: the system
`T(μ, Y) = 1 ∧ W(μ, Y) ≠ 1` has a solution in the coordinate group `G_{R(S)}`, where `μ` is the
generic point of `S`. -/
def HasLiftNe : Prop :=
  ∃ w : Y → CoordGroup ι S,
    Sum.elim (CoordGroup.genericPoint ι S) w ∈ V (CoordGroup.coeff ι S) T ∧
      eval (CoordGroup.coeff ι S) (Sum.elim (CoordGroup.genericPoint ι S) w) W ≠ 1

/-- The system of equations `T(X, Y) = 1` admits a complete `S`-lift: it admits an `S`-lift, and
so does `T = 1 ∧ W ≠ 1` for every inequation `W ≠ 1` such that `T = 1 ∧ W ≠ 1` is compatible
with `S`. The `S`-lift of `T` itself is part of the definition: it does not follow from the
second condition when no inequation is compatible. -/
def HasCompleteLift : Prop :=
  HasLift ι S T ∧ ∀ W : GX G (X ⊕ Y), IsCompatibleNe ι S T W → HasLiftNe ι S T W

/-- A family `Θ` of solutions of `S` in `H` is generic: every single equation `t(X, Y) = 1`, in
finitely many further variables `Y`, such that `t(θ, Y) = 1` is solvable in `H` for every `θ ∈ Θ`
admits a complete `S`-lift. -/
def IsGenericFamily (Θ : Set (X → H)) : Prop :=
  Θ ⊆ V ι S ∧ ∀ (n : ℕ) (t : GX G (X ⊕ Fin n)),
    (∀ v ∈ Θ, ∃ w : Fin n → H, eval ι (Sum.elim v w) t = 1) → HasCompleteLift ι S {t}

end Defs

variable {ι : G →* H} {S : Set (GX G X)} {T T' : Set (GX G (X ⊕ Y))} {W : GX G (X ⊕ Y)}

theorem isCompatible_iff :
    IsCompatible ι S T ↔ ∀ v ∈ V ι S, ∃ w : Y → H, Sum.elim v w ∈ V ι T :=
  Iff.rfl

theorem isCompatibleNe_iff :
    IsCompatibleNe ι S T W ↔
      ∀ v ∈ V ι S, ∃ w : Y → H, Sum.elim v w ∈ V ι T ∧ eval ι (Sum.elim v w) W ≠ 1 :=
  Iff.rfl

/-- Dropping the inequation preserves compatibility. -/
theorem IsCompatibleNe.isCompatible (h : IsCompatibleNe ι S T W) : IsCompatible ι S T :=
  fun v hv => (h v hv).imp fun _ => And.left

/-- A subsystem of a compatible system is compatible. -/
theorem IsCompatible.mono (h : IsCompatible ι S T) (hT : T' ⊆ T) : IsCompatible ι S T' :=
  fun v hv => (h v hv).imp fun _ hw => V_antitone ι hT hw

/-- The empty system is compatible with every system. -/
@[simp]
theorem isCompatible_empty : IsCompatible ι S (∅ : Set (GX G (X ⊕ Y))) :=
  fun _ _ => ⟨fun _ => 1, by simp⟩

/-- Every system is compatible with a system that has no solution in `H`. -/
theorem isCompatible_of_V_eq_empty (hS : V ι S = ∅) : IsCompatible ι S T :=
  fun v hv => by simp [hS] at hv

/-- A compatible system of equations stays compatible when the inequation `a ≠ 1` is added, for
a coefficient `a` that is nontrivial in `H`. -/
theorem IsCompatible.isCompatibleNe_inl (h : IsCompatible ι S T) {a : G} (ha : ι a ≠ 1) :
    IsCompatibleNe ι S T (inl a) :=
  fun v hv => (h v hv).imp fun _ hw => ⟨hw, by simpa using ha⟩

/-- The equation `a = 1`, for a coefficient `a` that is nontrivial in `H`, is not compatible
with a system that has a solution in `H`. -/
theorem not_isCompatible_singleton_inl {a : G} (ha : ι a ≠ 1) (hS : (V ι S).Nonempty) :
    ¬IsCompatible ι S ({inl a} : Set (GX G (X ⊕ Y))) := by
  obtain ⟨v, hv⟩ := hS
  intro h
  obtain ⟨w, hw⟩ := h v hv
  exact (V_singleton_inl_eq_empty ha).subset hw

/-- Over a trivial group no inequation is compatible. -/
theorem not_isCompatibleNe_of_subsingleton [Subsingleton H] : ¬IsCompatibleNe ι S T W := by
  intro h
  obtain ⟨w, -, hw⟩ := h (fun _ => 1) (mem_V.2 fun _ _ => Subsingleton.elim _ _)
  exact hw (Subsingleton.elim _ _)

/-! ### Lifts to the generic point -/

theorem hasLift_iff :
    HasLift ι S T ↔ ∃ w : Y → CoordGroup ι S,
      Sum.elim (CoordGroup.genericPoint ι S) w ∈ V (CoordGroup.coeff ι S) T :=
  Iff.rfl

theorem hasLiftNe_iff :
    HasLiftNe ι S T W ↔ ∃ w : Y → CoordGroup ι S,
      Sum.elim (CoordGroup.genericPoint ι S) w ∈ V (CoordGroup.coeff ι S) T ∧
        eval (CoordGroup.coeff ι S) (Sum.elim (CoordGroup.genericPoint ι S) w) W ≠ 1 :=
  Iff.rfl

/-- Dropping the inequation preserves the existence of a lift. -/
theorem HasLiftNe.hasLift (h : HasLiftNe ι S T W) : HasLift ι S T :=
  h.imp fun _ => And.left

/-- A subsystem of a system with an `S`-lift has an `S`-lift. -/
theorem HasLift.mono (h : HasLift ι S T) (hT : T' ⊆ T) : HasLift ι S T' :=
  h.imp fun _ hw => V_antitone _ hT hw

/-- The empty system admits an `S`-lift for every system `S`. -/
@[simp]
theorem hasLift_empty : HasLift ι S (∅ : Set (GX G (X ⊕ Y))) :=
  ⟨fun _ => 1, by simp⟩

/-- A system of equations with an `S`-lift is compatible with `S`. -/
theorem HasLift.isCompatible (h : HasLift ι S T) : IsCompatible ι S T := by
  obtain ⟨w, hw⟩ := h
  intro v hv
  -- Evaluation at `v` maps the solution at the generic point to a solution over `v`.
  refine ⟨CoordGroup.evalGHom v hv ∘ w, ?_⟩
  simpa [Sum.comp_elim] using (CoordGroup.evalGHom v hv).comp_mem_V hw

/-- A solution `Y(X)` of `T` in `G[X]` at the tuple of variables gives an `S`-lift of `T` for
every system `S`. -/
theorem hasLift_of_mem_V_inl {w : Y → GX G X}
    (hw : Sum.elim (fun x => inr (FreeGroup.of x)) w ∈ V (inl : G →* GX G X) T) :
    HasLift ι S T := by
  have h := (evalGHom (CoordGroup.coeff ι S) (CoordGroup.genericPoint ι S)).comp_mem_V hw
  have hμ : ⇑(evalGHom (CoordGroup.coeff ι S) (CoordGroup.genericPoint ι S)) ∘
      (fun x => inr (FreeGroup.of x)) = CoordGroup.genericPoint ι S :=
    funext fun x => by simp
  rw [Sum.comp_elim, hμ] at h
  exact ⟨_, h⟩

/-- When the coordinate group of `S` is trivial, for instance over a trivial group, every system
of equations admits an `S`-lift. -/
theorem hasLift_of_subsingleton [Subsingleton (CoordGroup ι S)] : HasLift ι S T :=
  ⟨fun _ => 1, mem_V.2 fun _ _ => Subsingleton.elim _ _⟩

/-- Every system of equations admits an `S`-lift when `S` has no solution in `H`. -/
theorem hasLift_of_V_eq_empty (hS : V ι S = ∅) : HasLift ι S T :=
  have := CoordGroup.subsingleton_of_V_eq_empty hS
  hasLift_of_subsingleton

/-- When the coordinate group of `S` is trivial, no inequation admits an `S`-lift. -/
theorem not_hasLiftNe_of_subsingleton [Subsingleton (CoordGroup ι S)] : ¬HasLiftNe ι S T W :=
  fun ⟨_, _, hw⟩ => hw (Subsingleton.elim _ _)

/-! ### Complete lifts -/

theorem hasCompleteLift_iff :
    HasCompleteLift ι S T ↔
      HasLift ι S T ∧ ∀ W : GX G (X ⊕ Y), IsCompatibleNe ι S T W → HasLiftNe ι S T W :=
  Iff.rfl

theorem HasCompleteLift.hasLift (h : HasCompleteLift ι S T) : HasLift ι S T :=
  h.1

theorem HasCompleteLift.hasLiftNe (h : HasCompleteLift ι S T) (hW : IsCompatibleNe ι S T W) :
    HasLiftNe ι S T W :=
  h.2 W hW

theorem HasCompleteLift.isCompatible (h : HasCompleteLift ι S T) : IsCompatible ι S T :=
  h.hasLift.isCompatible

/-- When some coefficient `a` is nontrivial in `H`, a system admits a complete `S`-lift if and
only if it is compatible with `S` and every compatible extension of it by an inequation admits
an `S`-lift. -/
theorem hasCompleteLift_iff_of_ne {a : G} (ha : ι a ≠ 1) :
    HasCompleteLift ι S T ↔
      IsCompatible ι S T ∧ ∀ W : GX G (X ⊕ Y), IsCompatibleNe ι S T W → HasLiftNe ι S T W :=
  -- The `S`-lift of the system itself is the one of its extension by `a ≠ 1`.
  ⟨fun h => ⟨h.isCompatible, h.2⟩,
    fun h => ⟨(h.2 _ (h.1.isCompatibleNe_inl ha)).hasLift, h.2⟩⟩

/-- No system admits a complete `S`-lift when `S` has no solution in `H`. -/
theorem not_hasCompleteLift_of_V_eq_empty (hS : V ι S = ∅) : ¬HasCompleteLift ι S T := fun h =>
  -- The coordinate group of `S` is trivial, while every inequation is compatible with `S`.
  have := CoordGroup.subsingleton_of_V_eq_empty hS
  not_hasLiftNe_of_subsingleton (h.hasLiftNe (W := 1) fun v hv => by simp [hS] at hv)

/-- Over a trivial group every system of equations admits a complete lift. -/
theorem hasCompleteLift_of_subsingleton [Subsingleton H] : HasCompleteLift ι S T :=
  ⟨hasLift_of_subsingleton, fun _ hW => (not_isCompatibleNe_of_subsingleton hW).elim⟩

/-- If `S` has a unique solution in `G`, every system compatible with `S` over `G` admits a
complete `S`-lift. -/
theorem IsCompatible.hasCompleteLift_of_V_eq_singleton {S : Set (GX G X)} {T : Set (GX G (X ⊕ Y))}
    {g : X → G} (hS : V (.id G) S = {g}) (h : IsCompatible (.id G) S T) :
    HasCompleteLift (.id G) S T := by
  have hg : g ∈ V (.id G) S := hS ▸ Set.mem_singleton g
  -- The coefficient map `G → G_{R(S)}` is an injective `G`-homomorphism sending `g` to the
  -- generic point, so every solution over `g` of `T`, with or without an inequation, gives a
  -- solution at the generic point.
  let φ : GHom (.id G) (CoordGroup.coeff (.id G) S) := ⟨CoordGroup.coeff (.id G) S, fun _ => rfl⟩
  have hφ : Function.Injective φ := CoordGroup.coeff_injective Function.injective_id ⟨g, hg⟩
  have hμ : φ ∘ g = CoordGroup.genericPoint (.id G) S :=
    (CoordGroup.genericPoint_eq_coeff_comp (by simp [hS])).symm
  have key (w : Y → G) :
      φ ∘ Sum.elim g w = Sum.elim (CoordGroup.genericPoint (.id G) S) (φ ∘ w) := by
    rw [Sum.comp_elim, hμ]
  refine ⟨?_, fun W hW => ?_⟩
  · obtain ⟨w, hw⟩ := h g hg
    exact ⟨φ ∘ w, key w ▸ φ.comp_mem_V hw⟩
  · obtain ⟨w, hw, hne⟩ := hW g hg
    refine ⟨φ ∘ w, key w ▸ φ.comp_mem_V hw, ?_⟩
    rwa [← key, ← map_eval, map_ne_one_iff φ hφ]

/-! ### Generic families of solutions -/

section GenericFamily

variable {Θ Θ' : Set (X → H)}

theorem isGenericFamily_iff :
    IsGenericFamily ι S Θ ↔ Θ ⊆ V ι S ∧ ∀ (n : ℕ) (t : GX G (X ⊕ Fin n)),
      (∀ v ∈ Θ, ∃ w : Fin n → H, eval ι (Sum.elim v w) t = 1) → HasCompleteLift ι S {t} :=
  Iff.rfl

/-- A generic family of solutions of `S` consists of solutions of `S`. -/
theorem IsGenericFamily.subset_V (h : IsGenericFamily ι S Θ) : Θ ⊆ V ι S :=
  h.1

/-- An equation solvable over every member of a generic family admits a complete lift. -/
theorem IsGenericFamily.hasCompleteLift (h : IsGenericFamily ι S Θ) {n : ℕ}
    {t : GX G (X ⊕ Fin n)} (ht : ∀ v ∈ Θ, ∃ w : Fin n → H, eval ι (Sum.elim v w) t = 1) :
    HasCompleteLift ι S {t} :=
  h.2 n t ht

/-- A family of solutions containing a generic family is generic. -/
theorem IsGenericFamily.mono (h : IsGenericFamily ι S Θ) (hΘ : Θ ⊆ Θ') (hΘ' : Θ' ⊆ V ι S) :
    IsGenericFamily ι S Θ' :=
  ⟨hΘ', fun _ _ ht => h.hasCompleteLift fun v hv => ht v (hΘ hv)⟩

/-- The family of all solutions of `S` is generic if and only if every single equation
compatible with `S` admits a complete `S`-lift. -/
theorem isGenericFamily_V_iff :
    IsGenericFamily ι S (V ι S) ↔ ∀ (n : ℕ) (t : GX G (X ⊕ Fin n)),
      IsCompatible ι S {t} → HasCompleteLift ι S {t} := by
  simp [IsGenericFamily, IsCompatible]

/-- If `S` has a unique solution `g` in `G`, the family consisting of `g` is generic. -/
theorem isGenericFamily_singleton {S : Set (GX G X)} {g : X → G} (hS : V (.id G) S = {g}) :
    IsGenericFamily (.id G) S {g} := by
  rw [← hS, isGenericFamily_V_iff]
  exact fun _ _ ht => ht.hasCompleteLift_of_V_eq_singleton hS

/-- For the one-variable equation `x = 1` over `G`, the family consisting of its solution
`x = 1` is generic. -/
theorem isGenericFamily_singleton_one :
    IsGenericFamily (.id G) ({inr (FreeGroup.of ())} : Set (GX G Unit)) {fun _ => 1} :=
  isGenericFamily_singleton <| by
    ext v
    simp [funext_iff, Unique.forall_iff]

/-- The empty family of solutions of `S` is generic if and only if `H` is trivial. -/
theorem isGenericFamily_empty_iff : IsGenericFamily ι S ∅ ↔ Subsingleton H := by
  refine ⟨fun h => ?_, fun _ => ⟨Set.empty_subset _, fun _ _ _ => hasCompleteLift_of_subsingleton⟩⟩
  -- Genericity of the empty family gives every single equation a complete `S`-lift.
  have hc {n : ℕ} (t : GX G (X ⊕ Fin n)) : HasCompleteLift ι S {t} := h.hasCompleteLift (by simp)
  -- The equations `a = 1` and `x = 1` are then compatible with `S`, so every solution of `S` is
  -- trivial with trivial coefficients, and the coordinate group of `S` is trivial.
  have : Subsingleton (CoordGroup ι S) := CoordGroup.subsingleton_iff.2 fun v hv =>
    hom_ext (MonoidHom.ext fun a => by
        obtain ⟨w, hw⟩ := (hc (n := 0) (inl a)).isCompatible v hv
        simpa using hw)
      (FreeGroup.ext_hom _ _ fun x => by
        obtain ⟨w, hw⟩ := (hc (n := 0) (inr (FreeGroup.of (Sum.inl x)))).isCompatible v hv
        simpa using hw)
  -- So for `h₀ ≠ 1` the compatible inequation `y ≠ 1`, with `y = h₀`, has no `S`-lift.
  refine subsingleton_of_forall_eq 1 fun h₀ => by_contra fun hh₀ => not_hasLiftNe_of_subsingleton <|
    (hc (n := 1) 1).hasLiftNe (W := inr (FreeGroup.of (Sum.inr 0))) <|
      isCompatibleNe_iff.2 fun v _ => ⟨fun _ => h₀, by simp, by simpa using hh₀⟩

/-- Over a nontrivial group the empty family of solutions is not generic. -/
theorem not_isGenericFamily_empty [Nontrivial H] : ¬IsGenericFamily ι S ∅ :=
  fun h => not_subsingleton H (isGenericFamily_empty_iff.1 h)

end GenericFamily

/-! ### Examples -/

section Examples

open FreeGroup
open scoped commutatorElement

/-- The equation `y² = x²` admits the lift `y = x` to the generic point of every system. -/
theorem hasLift_sq_eq_sq (ι : G →* H) (S : Set (GX G X)) (x : X) (y : Y) :
    HasLift ι S
      {(inr (of (Sum.inr y)) : GX G (X ⊕ Y)) ^ 2 * (inr (of (Sum.inl x)) ^ 2)⁻¹} :=
  hasLift_of_mem_V_inl (w := fun _ => inr (of x)) (by simp)

/-- The equations `y = u_y(X)`, for words `u_y ∈ G[X]`, admit the lift `y = u_y` to the generic
point of every system. -/
theorem hasLift_range_mul_inv (ι : G →* H) (S : Set (GX G X)) (u : Y → GX G X) :
    HasLift ι S (Set.range fun y : Y => (inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) *
      (Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inl) (u y))⁻¹) :=
  hasLift_of_mem_V_inl (w := u) <| mem_V.2 fun _ ⟨y, hy⟩ => by simp [← hy]

/-- The equation `y² = x` is compatible with the empty system over `H` if and only if every
element of `H` is a square. -/
theorem isCompatible_empty_sq_iff (ι : G →* H) :
    IsCompatible ι (∅ : Set (GX G Unit))
        {(inr (of (Sum.inr ())) : GX G (Unit ⊕ Unit)) ^ 2 * (inr (of (Sum.inl ())))⁻¹} ↔
      ∀ h : H, IsSquare h := by
  simp only [isSquare_iff_exists_sq]
  refine ⟨fun h a => ?_, fun h v _ => ?_⟩
  · obtain ⟨w, hw⟩ := h (fun _ => a) (by simp)
    exact ⟨w (), (mul_inv_eq_one.1 (by simpa using hw)).symm⟩
  · obtain ⟨r, hr⟩ := h (v ())
    exact ⟨fun _ => r, by simp [hr]⟩

/-- Over a free group on a nonempty set, the equation `y² = x` is not compatible with the empty
system. -/
theorem not_isCompatible_empty_sq {α : Type*} [Nonempty α] :
    ¬IsCompatible (.id (FreeGroup α)) (∅ : Set (GX (FreeGroup α) Unit))
      {(inr (of (Sum.inr ())) : GX (FreeGroup α) (Unit ⊕ Unit)) ^ 2 *
        (inr (of (Sum.inl ())))⁻¹} := by
  obtain ⟨a⟩ := ‹Nonempty α›
  exact fun h => not_isSquare_of a ((isCompatible_empty_sq_iff _).1 h (of a))

/-- Over a nontrivial group, the system `y = x ∧ y ≠ 1` has the solution `y = x` at the generic
point of the empty system. -/
theorem hasLiftNe_diagonal [Nontrivial H] (ι : G →* H) :
    HasLiftNe ι (∅ : Set (GX G Unit))
      {(inr (of (Sum.inr ())) : GX G (Unit ⊕ Unit)) * (inr (of (Sum.inl ())))⁻¹}
      (inr (of (Sum.inr ()))) := by
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  refine ⟨fun _ => CoordGroup.genericPoint ι ∅ (), by simp, ?_⟩
  suffices (inr (of ()) : GX G Unit) ∉ Rad ι ∅ by
    simpa [CoordGroup.genericPoint_apply, QuotientGroup.eq_one_iff]
  exact fun hmem => hh (by simpa using mem_Rad.1 hmem (fun _ => h) (by simp))

/-- The system `y = x ∧ y ≠ 1` is not compatible with the empty system. Together with
`hasLiftNe_diagonal`, this shows that a lift of a system with an inequation does not force
compatibility. -/
theorem not_isCompatibleNe_diagonal (ι : G →* H) :
    ¬IsCompatibleNe ι (∅ : Set (GX G Unit))
      {(inr (of (Sum.inr ())) : GX G (Unit ⊕ Unit)) * (inr (of (Sum.inl ())))⁻¹}
      (inr (of (Sum.inr ()))) := by
  intro h
  obtain ⟨w, hw, hne⟩ := h (fun _ => 1) (by simp)
  exact hne (by simpa using hw)

private theorem exists_sumElim_commutator_iff {K : Type*} [Group K] {κ : G →* K} {p : X → K} {x : X}
    {y : Y} :
    (∃ w : Y → K, Sum.elim p w ∈
        V κ {⁅(inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)), inr (FreeGroup.of (Sum.inl x))⁆} ∧
      eval κ (Sum.elim p w) (inr (FreeGroup.of (Sum.inr y))) ≠ 1) ↔ Nontrivial K := by
  refine ⟨fun ⟨w, _, hw⟩ => nontrivial_of_ne _ _ (by simpa using hw), fun _ => ?_⟩
  -- Over the point `p`, take `y = p x` when `p x ≠ 1`, and any `y ≠ 1` otherwise.
  by_cases hp : p x = 1
  · obtain ⟨c, hc⟩ := exists_ne (1 : K)
    exact ⟨fun _ => c, mem_V_commutator_iff.2 (by simp [hp]), by simpa using hc⟩
  · exact ⟨fun _ => p x, mem_V_commutator_iff.2 (by simp), by simpa using hp⟩

/-- The system `[y, x] = 1 ∧ y ≠ 1` is compatible with a system `S` if and only if `H` is
nontrivial: over a solution with `x ≠ 1` take `y = x`, and over a solution with `x = 1` any
`y ≠ 1`. -/
theorem isCompatibleNe_commutator_iff {ι : G →* H} {S : Set (GX G X)} {x : X} {y : Y} :
    IsCompatibleNe ι S
        {⁅(inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)), inr (FreeGroup.of (Sum.inl x))⁆}
        (inr (FreeGroup.of (Sum.inr y))) ↔ Nontrivial H := by
  refine ⟨fun h => not_subsingleton_iff_nontrivial.1 fun _ => not_isCompatibleNe_of_subsingleton h,
    fun _ => isCompatibleNe_iff.2 fun _ _ => exists_sumElim_commutator_iff.2 ‹_›⟩

/-- The system `[y, x] = 1 ∧ y ≠ 1` has a solution at the generic point of `S` if and only if the
coordinate group of `S` is nontrivial. -/
theorem hasLiftNe_commutator_iff {ι : G →* H} {S : Set (GX G X)} {x : X} {y : Y} :
    HasLiftNe ι S
        {⁅(inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)), inr (FreeGroup.of (Sum.inl x))⁆}
        (inr (FreeGroup.of (Sum.inr y))) ↔ Nontrivial (CoordGroup ι S) :=
  hasLiftNe_iff.trans exists_sumElim_commutator_iff

/-- For the empty system over a nontrivial group, with generic point `μ`: the system
`[y, x] = 1 ∧ y ≠ 1` is compatible, also over the solutions with `x = 1`, and `y = x` is a lift,
as the point `(μ, y = μ x)` solves `[y, x] = 1` and `μ x ≠ 1`. -/
example [Nontrivial H] (ι : G →* H) (x : X) :
    let μ := CoordGroup.genericPoint ι (∅ : Set (GX G X))
    IsCompatibleNe ι (∅ : Set (GX G X))
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX G (X ⊕ Unit)), inr (FreeGroup.of (Sum.inl x))⁆}
        (inr (FreeGroup.of (Sum.inr ()))) ∧
      Sum.elim μ (fun _ : Unit => μ x) ∈ V (CoordGroup.coeff ι ∅)
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX G (X ⊕ Unit)), inr (FreeGroup.of (Sum.inl x))⁆} ∧
      eval (CoordGroup.coeff ι ∅) (Sum.elim μ (fun _ : Unit => μ x))
        (inr (FreeGroup.of (Sum.inr ()))) ≠ 1 := by
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  refine ⟨isCompatibleNe_commutator_iff.2 ‹_›, mem_V_commutator_iff.2 (by simp), ?_⟩
  simpa using CoordGroup.genericPoint_ne_one_iff.2 ⟨fun _ => h, by simp, hh⟩

/-- Over the trivial coefficient group and a nontrivial group `H`, the system `[y, x] = 1 ∧ y ≠ 1`
is compatible with the equation `x = 1` but has no lift to its generic point: the only solution
of `x = 1` is trivial, so its coordinate group is trivial. -/
example [Nontrivial H] (κ : Unit →* H) :
    IsCompatibleNe κ {(inr (FreeGroup.of ()) : GX Unit Unit)}
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX Unit (Unit ⊕ Unit)),
          inr (FreeGroup.of (Sum.inl ()))⁆} (inr (FreeGroup.of (Sum.inr ()))) ∧
      ¬HasLiftNe κ {(inr (FreeGroup.of ()) : GX Unit Unit)}
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX Unit (Unit ⊕ Unit)),
          inr (FreeGroup.of (Sum.inl ()))⁆} (inr (FreeGroup.of (Sum.inr ()))) := by
  refine ⟨isCompatibleNe_commutator_iff.2 ‹_›, ?_⟩
  -- Every word vanishes at the only solution `x = 1`, so the coordinate group is trivial.
  obtain rfl : κ = 1 := Subsingleton.elim _ _
  have : Subsingleton (CoordGroup (1 : Unit →* H) {(inr (FreeGroup.of ()) : GX Unit Unit)}) :=
    CoordGroup.subsingleton_iff.2 fun v hv => by
      obtain rfl : v = 1 := funext fun _ => by simpa using hv
      exact eval_one_one
  exact not_hasLiftNe_of_subsingleton

/-- Over a free group on a nonempty set, none of `x`, `y` and `x y` is a square in the coordinate
group of the equation `[x, y] = 1`. -/
theorem not_exists_genericPoint_eq_sq {α : Type*} [Nonempty α] :
    ¬∃ z : CoordGroup (.id (FreeGroup α))
        {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆},
      CoordGroup.genericPoint _ _ false = z ^ 2 ∨ CoordGroup.genericPoint _ _ true = z ^ 2 ∨
        CoordGroup.genericPoint _ _ false * CoordGroup.genericPoint _ _ true = z ^ 2 := by
  obtain ⟨a⟩ := ‹Nonempty α›
  have hsq (z : FreeGroup α) : of a ≠ z ^ 2 := fun h => not_isSquare_of a ⟨z, h.trans (sq z)⟩
  -- The points `(a, 1)` and `(1, a)` solve `[x, y] = 1`.
  have h₁ : (fun b => cond b 1 (of a)) ∈ V (.id (FreeGroup α))
      {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆} :=
    mem_V_commutator_iff.2 (by simp)
  have h₂ : (fun b => cond b (of a) 1) ∈ V (.id (FreeGroup α))
      {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆} :=
    mem_V_commutator_iff.2 (by simp)
  rintro ⟨z, hz | hz | hz⟩
  · exact hsq _ (by simpa using congrArg (CoordGroup.evalGHom _ h₁) hz)
  · exact hsq _ (by simpa using congrArg (CoordGroup.evalGHom _ h₂) hz)
  · exact hsq _ (by simpa using congrArg (CoordGroup.evalGHom _ h₁) hz)

end Examples

end TauCeti.GroupAlgGeom.Lift
