/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homotopy

/-!
# The loop-space shift for higher homotopy groups

`GenLoop.homotopic_iff_joined` identifies homotopy of generalized loops relative to the cube
boundary with path connectedness in `Ω^ N X x`. The payoff, proved here, is that *any*
homeomorphism between generalized-loop spaces preserves and reflects homotopy, hence descends to
a bijection of homotopy groups. Two of Mathlib's homeomorphisms are then put to work.

* `GenLoop.congr`, reindexing the cube along an equivalence `M ≃ N` of index types, gives
  `HomotopyGroup.congrEquiv` and its multiplicative form.
* `GenLoop.genLoopGenLoopEquiv : Ω^ M (Ω^ N X x) const ≃ₜ Ω^ (M ⊕ N) X x`, currying a cube in
  `M ⊕ N` directions into an `M`-cube of `N`-cubes, gives the **loop-space shift**
  `π_M (Ω^ N X x) ≃* π_(M ⊕ N) X x`. Specialised to `N` a singleton and Mathlib's loop space
  `Ω X x = Path x x`, this is the classical `π_(n + 1)(Ω X) ≅ π_(n + 2)(X)`.

Taking the outer index type empty instead of nonempty turns the same correspondence into a
statement about path components: `HomotopyGroup N X x` is the set of path components of
`Ω^ N X x`, which for `N` a singleton says that the path components of `Ω X x` are the
fundamental group of `X` at `x`.

Multiplicativity is checked by hand in both cases: the product on `HomotopyGroup N X x` is
computed by `HomotopyGroup.mul_spec` as the class of a concatenation `GenLoop.transAt i` in an
arbitrary cube direction `i`, and both homeomorphisms carry a concatenation in direction `i` to a
concatenation in the matching direction.

## Main declarations

* `GenLoop.homotopic_homeomorph_iff`: a homeomorphism of generalized-loop spaces preserves and
  reflects homotopy.
* `HomotopyGroup.congrEquiv`, `HomotopyGroup.congrMulEquiv`: reindexing the cube directions
  along `M ≃ N`.
* `HomotopyGroup.zerothHomotopyEquiv`: **`π_N(X, x)` is the set of path components of
  `Ω^ N X x`**, with `HomotopyGroup.zerothHomotopyLoopSpaceEquivFundamentalGroup` the
  degree-zero shift `π_0(Ω X) ≅ π_1(X)`.
* `HomotopyGroup.loopSpaceEquiv`, `HomotopyGroup.loopSpaceMulEquiv`: **the loop-space shift
  `π_M (Ω^ N X x) const ≃* π_(M ⊕ N) X x`.**
* `HomotopyGroup.piLoopSpaceMulEquiv`, `HomotopyGroup.pathLoopSpaceMulEquiv`: its `π_n` forms,
  the latter for Mathlib's loop space `Ω X x`.

## References

The loop-space shift is the cubical form of the standard isomorphism
`π_n(Ω X) ≅ π_(n + 1)(X)`; see Hatcher, *Algebraic Topology*, Section 4.1.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {M N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- A homeomorphism between spaces of generalized loops preserves and reflects homotopy
relative to the cube boundary: both are path connectedness, which a homeomorphism transports
in both directions. -/
@[simp]
theorem homotopic_homeomorph_iff (φ : Ω^ M X x ≃ₜ Ω^ N Y y) {p q : Ω^ M X x} :
    _root_.GenLoop.Homotopic (φ p) (φ q) ↔ _root_.GenLoop.Homotopic p q := by
  rw [homotopic_iff_joined, homotopic_iff_joined]
  refine ⟨fun h => ?_, fun h => h.map φ.continuous⟩
  simpa using h.map φ.symm.continuous

/-! ### Reindexing the cube directions -/

section Congr

@[simp]
theorem congr_apply (e : M ≃ N) (p : Ω^ M X x) (t : I^N) :
    _root_.GenLoop.congr x e p t = p fun m => t (e m) :=
  rfl

variable [DecidableEq M] [DecidableEq N]

/-- Reindexing carries a concatenation in the cube direction `i` to a concatenation in the
direction `e i`. -/
@[simp]
theorem congr_transAt (e : M ≃ N) (i : M) (p q : Ω^ M X x) :
    _root_.GenLoop.congr x e (_root_.GenLoop.transAt i p q) =
      _root_.GenLoop.transAt (e i) (_root_.GenLoop.congr x e p)
        (_root_.GenLoop.congr x e q) := by
  refine _root_.GenLoop.ext _ _ fun t => ?_
  simp only [congr_apply, _root_.GenLoop.transAt, _root_.GenLoop.coe_copy]
  have hupd : ∀ s : I, (fun m => Function.update t (e i) s (e m)) =
      Function.update (fun m => t (e m)) i s := by
    intro s
    funext m
    simp [Function.update_apply]
  split_ifs <;> rw [hupd]

end Congr

/-! ### Currying the cube directions -/

section Sum

@[simp]
theorem genLoopGenLoopEquiv_apply (p : Ω^ M (Ω^ N X x) _root_.GenLoop.const) (y : I^(M ⊕ N)) :
    _root_.GenLoop.genLoopGenLoopEquiv x p y =
      p (fun m => y (Sum.inl m)) fun n => y (Sum.inr n) :=
  rfl

variable [DecidableEq M] [DecidableEq N]

/-- Currying carries a concatenation in the cube direction `i` of the outer cube to a
concatenation in the direction `Sum.inl i`. -/
@[simp]
theorem genLoopGenLoopEquiv_transAt (i : M) (p q : Ω^ M (Ω^ N X x) _root_.GenLoop.const) :
    _root_.GenLoop.genLoopGenLoopEquiv x (_root_.GenLoop.transAt i p q) =
      _root_.GenLoop.transAt (Sum.inl i) (_root_.GenLoop.genLoopGenLoopEquiv x p)
        (_root_.GenLoop.genLoopGenLoopEquiv x q) := by
  refine _root_.GenLoop.ext _ _ fun y => ?_
  simp only [genLoopGenLoopEquiv_apply, _root_.GenLoop.transAt, _root_.GenLoop.coe_copy]
  have hinl : ∀ s : I, (fun m => Function.update y (Sum.inl i) s (Sum.inl m)) =
      Function.update (fun m => y (Sum.inl m)) i s := by
    intro s
    funext m
    simp [Function.update_apply]
  have hinr : ∀ s : I, (fun n => Function.update y (Sum.inl i) s (Sum.inr n)) =
      fun n => y (Sum.inr n) := by
    intro s
    funext n
    simp
  split_ifs <;> rw [hinl, hinr]

end Sum

end GenLoop

namespace HomotopyGroup

variable {M N X : Type*} [TopologicalSpace X] {x : X}

/-! ### Reindexing the cube directions -/

/-- An equivalence `M ≃ N` of index types reindexes the cube directions, and so identifies the
homotopy groups indexed by `M` and by `N`. -/
def congrEquiv (e : M ≃ N) : HomotopyGroup M X x ≃ HomotopyGroup N X x :=
  Quotient.congr (_root_.GenLoop.congr x e).toEquiv fun _ _ =>
    (GenLoop.homotopic_homeomorph_iff _).symm

@[simp]
theorem congrEquiv_mk (e : M ≃ N) (p : Ω^ M X x) :
    congrEquiv e (⟦p⟧ : HomotopyGroup M X x) = ⟦_root_.GenLoop.congr x e p⟧ :=
  by rw [congrEquiv.eq_1]; rfl

/-- In positive dimensions, reindexing the cube directions along `e : M ≃ N` is an isomorphism
of homotopy groups. -/
def congrMulEquiv [DecidableEq M] [DecidableEq N] [Nonempty M] [Nonempty N]
    (e : M ≃ N) : HomotopyGroup M X x ≃* HomotopyGroup N X x where
  toEquiv := congrEquiv e
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [Equiv.toFun_as_coe,
      _root_.HomotopyGroup.mul_spec (i := Classical.arbitrary M), congrEquiv_mk,
      GenLoop.congr_transAt]
    exact (_root_.HomotopyGroup.mul_spec (i := e (Classical.arbitrary M))).symm

@[simp]
theorem congrMulEquiv_apply [DecidableEq M] [DecidableEq N] [Nonempty M] [Nonempty N]
    (e : M ≃ N) (a : HomotopyGroup M X x) : congrMulEquiv e a = congrEquiv e a :=
  by rw [congrMulEquiv.eq_1]; rfl

@[simp]
theorem congrMulEquiv_mk [DecidableEq M] [DecidableEq N] [Nonempty M] [Nonempty N]
    (e : M ≃ N) (p : Ω^ M X x) :
    congrMulEquiv e (⟦p⟧ : HomotopyGroup M X x) =
      ⟦_root_.GenLoop.congr x e p⟧ :=
  (congrMulEquiv_apply e _).trans (congrEquiv_mk e p)

/-! ### Homotopy groups as path components of the loop space -/

/-- **The homotopy group `π_N(X, x)` is the set of path components of the space of
`N`-dimensional generalized loops.** This is `GenLoop.homotopic_iff_joined` read on the
quotient. -/
def zerothHomotopyEquiv :
    ZerothHomotopy (Ω^ N X x) ≃ HomotopyGroup N X x :=
  Quotient.congr (Equiv.refl _) fun _ _ => GenLoop.homotopic_iff_joined.symm

@[simp]
theorem zerothHomotopyEquiv_mk (p : Ω^ N X x) :
    zerothHomotopyEquiv (⟦p⟧ : ZerothHomotopy (Ω^ N X x)) = ⟦p⟧ :=
  by rw [zerothHomotopyEquiv.eq_1]; rfl

/-- **The path components of Mathlib's loop space `Ω X x` are the fundamental group of `X`
at `x`**: the degree-zero case of the loop-space shift. -/
noncomputable def zerothHomotopyLoopSpaceEquivFundamentalGroup :
    ZerothHomotopy (Ω X x) ≃ FundamentalGroup X x :=
  (_root_.HomotopyGroup.pi0EquivZerothHomotopy (X := Ω X x) (x := Path.refl x)).symm.trans <|
    (homeomorphEquivOfEq (N := Fin 0) (GenLoop.homeomorphOfUnique (Fin 1))
      (GenLoop.homeomorphOfUnique_const (Fin 1))).symm.trans <|
      (_root_.homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) _).trans <|
        zerothHomotopyEquiv.trans (_root_.homotopyGroupEquivFundamentalGroupOfUnique (Fin 1))

@[simp]
theorem zerothHomotopyLoopSpaceEquivFundamentalGroup_mk (p : Ω X x) :
    zerothHomotopyLoopSpaceEquivFundamentalGroup
        (⟦p⟧ : ZerothHomotopy (Ω X x)) = (⟦p⟧ : FundamentalGroup X x) :=
  by rw [zerothHomotopyLoopSpaceEquivFundamentalGroup.eq_1]; rfl

/-! ### The loop-space shift -/

/-- **The loop-space shift.** Currying identifies the homotopy group indexed by `M` of the space
of `N`-dimensional generalized loops, based at the constant loop, with the homotopy group of `X`
indexed by `M ⊕ N`. -/
def loopSpaceEquiv :
    HomotopyGroup M (Ω^ N X x) _root_.GenLoop.const ≃ HomotopyGroup (M ⊕ N) X x :=
  Quotient.congr (_root_.GenLoop.genLoopGenLoopEquiv x).toEquiv fun _ _ =>
    (GenLoop.homotopic_homeomorph_iff _).symm

@[simp]
theorem loopSpaceEquiv_mk (p : Ω^ M (Ω^ N X x) _root_.GenLoop.const) :
    loopSpaceEquiv (⟦p⟧ : HomotopyGroup M (Ω^ N X x) _root_.GenLoop.const) =
      ⟦_root_.GenLoop.genLoopGenLoopEquiv x p⟧ :=
  by rw [loopSpaceEquiv.eq_1]; rfl

/-- **The loop-space shift is an isomorphism of groups** in positive dimensions:
`π_M (Ω^ N X x) ≃* π_(M ⊕ N) X x`. -/
def loopSpaceMulEquiv [DecidableEq M] [DecidableEq N] [Nonempty M] :
    HomotopyGroup M (Ω^ N X x) _root_.GenLoop.const ≃* HomotopyGroup (M ⊕ N) X x where
  toEquiv := loopSpaceEquiv
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [Equiv.toFun_as_coe,
      _root_.HomotopyGroup.mul_spec (i := Classical.arbitrary M), loopSpaceEquiv_mk,
      GenLoop.genLoopGenLoopEquiv_transAt]
    exact (_root_.HomotopyGroup.mul_spec (i := Sum.inl (Classical.arbitrary M))).symm

@[simp]
theorem loopSpaceMulEquiv_apply [DecidableEq M] [DecidableEq N] [Nonempty M]
    (a : HomotopyGroup M (Ω^ N X x) _root_.GenLoop.const) :
    loopSpaceMulEquiv a = loopSpaceEquiv a :=
  by rw [loopSpaceMulEquiv.eq_1]; rfl

@[simp]
theorem loopSpaceMulEquiv_mk [DecidableEq M] [DecidableEq N] [Nonempty M]
    (p : Ω^ M (Ω^ N X x) _root_.GenLoop.const) :
    loopSpaceMulEquiv
        (⟦p⟧ : HomotopyGroup M (Ω^ N X x) _root_.GenLoop.const) =
      ⟦_root_.GenLoop.genLoopGenLoopEquiv x p⟧ :=
  (loopSpaceMulEquiv_apply _).trans (loopSpaceEquiv_mk p)

/-- The loop-space shift in the `π_n` notation: `π_(m + 1)` of the space of `n`-dimensional
generalized loops is `π_(m + 1 + n)` of the space itself. -/
noncomputable def piLoopSpaceMulEquiv (m n : ℕ) :
    π_ (m + 1) (Ω^ (Fin n) X x) _root_.GenLoop.const ≃* π_ (m + 1 + n) X x :=
  loopSpaceMulEquiv.trans (congrMulEquiv finSumFinEquiv)

@[simp]
theorem piLoopSpaceMulEquiv_apply (m n : ℕ)
    (a : π_ (m + 1) (Ω^ (Fin n) X x) _root_.GenLoop.const) :
    piLoopSpaceMulEquiv m n a = congrMulEquiv finSumFinEquiv (loopSpaceMulEquiv a) :=
  by rw [piLoopSpaceMulEquiv.eq_1]; rfl

@[simp]
theorem piLoopSpaceMulEquiv_mk (m n : ℕ)
    (p : Ω^ (Fin (m + 1)) (Ω^ (Fin n) X x) _root_.GenLoop.const) :
    piLoopSpaceMulEquiv m n
        (⟦p⟧ : π_ (m + 1) (Ω^ (Fin n) X x) _root_.GenLoop.const) =
      ⟦_root_.GenLoop.congr x finSumFinEquiv
        (_root_.GenLoop.genLoopGenLoopEquiv x p)⟧ :=
  (piLoopSpaceMulEquiv_apply m n _).trans <|
    (congrArg (fun a : HomotopyGroup (Fin (m + 1) ⊕ Fin n) X x => congrMulEquiv finSumFinEquiv a)
      (loopSpaceMulEquiv_mk p)).trans
        (congrMulEquiv_mk finSumFinEquiv (_root_.GenLoop.genLoopGenLoopEquiv x p))

/-- **The homotopy groups of the loop space are the higher homotopy groups of the space**:
`π_(m + 1)(Ω X, refl x) ≃* π_(m + 2)(X, x)`. -/
noncomputable def pathLoopSpaceMulEquiv (m : ℕ) :
    π_ (m + 1) (Ω X x) (Path.refl x) ≃* π_ (m + 2) X x :=
  (homeomorphMulEquivOfEq (N := Fin (m + 1)) (GenLoop.homeomorphOfUnique (Fin 1))
    (GenLoop.homeomorphOfUnique_const (Fin 1))).symm.trans (piLoopSpaceMulEquiv m 1)

@[simp]
theorem pathLoopSpaceMulEquiv_apply (m : ℕ) (a : π_ (m + 1) (Ω X x) (Path.refl x)) :
    pathLoopSpaceMulEquiv m a =
      piLoopSpaceMulEquiv m 1
        ((homeomorphMulEquivOfEq (N := Fin (m + 1)) (GenLoop.homeomorphOfUnique (Fin 1))
          (GenLoop.homeomorphOfUnique_const (Fin 1))).symm a) :=
  by rw [pathLoopSpaceMulEquiv.eq_1]; rfl

@[simp]
theorem pathLoopSpaceMulEquiv_mk (m : ℕ)
    (p : Ω^ (Fin (m + 1)) (Ω X x) (Path.refl x)) :
    pathLoopSpaceMulEquiv m (⟦p⟧ : π_ (m + 1) (Ω X x) (Path.refl x)) =
      ⟦_root_.GenLoop.congr x finSumFinEquiv
        (_root_.GenLoop.genLoopGenLoopEquiv x
          (_root_.GenLoop.map
            ⟨(GenLoop.homeomorphOfUnique (Fin 1)).symm,
              (GenLoop.homeomorphOfUnique (Fin 1)).symm.continuous⟩
            ((GenLoop.homeomorphOfUnique (Fin 1)).symm_apply_eq.mpr
              (GenLoop.homeomorphOfUnique_const (Fin 1)).symm) p))⟧ :=
  (pathLoopSpaceMulEquiv_apply m _).trans <|
    (congrArg (fun a : HomotopyGroup (Fin (m + 1)) (Ω^ (Fin 1) X x) _root_.GenLoop.const =>
        piLoopSpaceMulEquiv m 1 a)
      ((homeomorphMulEquivOfEq_symm_apply _ _ _).trans (map_mk _ _ p))).trans
        (piLoopSpaceMulEquiv_mk m 1 _)

end HomotopyGroup
