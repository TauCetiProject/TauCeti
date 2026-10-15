/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.GenLoop.Loop
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

Read on the quotient instead of on representatives, the same correspondence is a statement
about path components: `HomotopyGroup N X x` is the set of path components of `Ω^ N X x`. For
`N` a singleton this says that two loops at `x` are joined in `Ω X x` exactly when they are
homotopic, so the path components of `Ω X x` are the fundamental group of `X` at `x`.

Multiplicativity is checked by hand in both cases: the product on `HomotopyGroup N X x` is
computed by `HomotopyGroup.mul_spec` as the class of a concatenation `GenLoop.transAt i` in an
arbitrary cube direction `i`, and both homeomorphisms carry a concatenation in direction `i` to a
concatenation in the matching direction.

## Main declarations

* `GenLoop.homotopic_homeomorph_iff`: a homeomorphism of generalized-loop spaces preserves and
  reflects homotopy.
* `HomotopyGroup.congrEquiv`, `HomotopyGroup.congrMulEquiv`: reindexing the cube directions
  along `M ≃ N`, natural in the space by `HomotopyGroup.map_congrEquiv`.
* `HomotopyGroup.zerothHomotopyEquiv`: **`π_N(X, x)` is the set of path components of
  `Ω^ N X x`**, with `Path.joined_iff_homotopic` its one-dimensional form and
  `HomotopyGroup.zerothHomotopyLoopSpaceEquivFundamentalGroup` the degree-zero shift
  `π_0(Ω X) ≅ π_1(X)`.
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

@[simp]
theorem congrEquiv_symm_mk (e : M ≃ N) (q : Ω^ N X x) :
    (congrEquiv e).symm (⟦q⟧ : HomotopyGroup N X x) = ⟦_root_.GenLoop.congr x e.symm q⟧ :=
  by rw [congrEquiv.eq_1]; rfl

/-- Reindexing the cube directions commutes with the maps induced by based continuous maps. -/
@[simp]
theorem map_congrEquiv {Y : Type*} [TopologicalSpace Y] {y : Y} (f : C(X, Y)) (hf : f x = y)
    (e : M ≃ N) (a : HomotopyGroup M X x) :
    map f hf (congrEquiv e a) = congrEquiv e (map f hf a) := by
  induction a using Quotient.inductionOn
  rw [congrEquiv_mk, map_mk, map_mk, congrEquiv_mk]
  -- both generalized loops are `f ∘ p ∘ (t ↦ t ∘ e)`
  refine congrArg _ (_root_.GenLoop.ext _ _ fun t => ?_)
  simp only [_root_.GenLoop.congr_apply, _root_.GenLoop.map_apply]

/-- In positive dimensions, reindexing the cube directions along `e : M ≃ N` is an isomorphism
of homotopy groups. The target index type inherits its nonemptiness, hence its group structure,
from `e`; that is what the `letI` in the statement records. -/
def congrMulEquiv [DecidableEq M] [DecidableEq N] [Nonempty M] (e : M ≃ N) :
    letI : Nonempty N := e.nonempty_congr.mp ‹_›
    HomotopyGroup M X x ≃* HomotopyGroup N X x :=
  letI : Nonempty N := e.nonempty_congr.mp ‹_›
  { toEquiv := congrEquiv e
    map_mul' := fun a b => Quotient.inductionOn₂ a b fun p q => by
      simp only [Equiv.toFun_as_coe,
        _root_.HomotopyGroup.mul_spec (i := Classical.arbitrary M), congrEquiv_mk,
        GenLoop.congr_transAt]
      exact (_root_.HomotopyGroup.mul_spec (i := e (Classical.arbitrary M))).symm }

@[simp]
theorem congrMulEquiv_apply [DecidableEq M] [DecidableEq N] [Nonempty M]
    (e : M ≃ N) (a : HomotopyGroup M X x) : congrMulEquiv e a = congrEquiv e a :=
  by rw [congrMulEquiv.eq_1]; rfl

@[simp]
theorem congrMulEquiv_symm_apply [DecidableEq M] [DecidableEq N] [Nonempty M]
    (e : M ≃ N) (b : HomotopyGroup N X x) :
    letI : Nonempty N := e.nonempty_congr.mp ‹_›
    (congrMulEquiv e).symm b = (congrEquiv e).symm b :=
  by rw [congrMulEquiv.eq_1]; rfl

@[simp]
theorem congrMulEquiv_mk [DecidableEq M] [DecidableEq N] [Nonempty M]
    (e : M ≃ N) (p : Ω^ M X x) :
    congrMulEquiv e (⟦p⟧ : HomotopyGroup M X x) =
      ⟦_root_.GenLoop.congr x e p⟧ :=
  (congrMulEquiv_apply e _).trans (congrEquiv_mk e p)

@[simp]
theorem congrMulEquiv_symm_mk [DecidableEq M] [DecidableEq N] [Nonempty M]
    (e : M ≃ N) (q : Ω^ N X x) :
    letI : Nonempty N := e.nonempty_congr.mp ‹_›
    (congrMulEquiv e).symm (⟦q⟧ : HomotopyGroup N X x) =
      ⟦_root_.GenLoop.congr x e.symm q⟧ :=
  (congrMulEquiv_symm_apply e _).trans (congrEquiv_symm_mk e q)

/-- In positive dimensions, reindexing the cube directions commutes with the maps induced by
based continuous maps. -/
theorem _root_.ContinuousMap.map_congrMulEquiv [DecidableEq M] [DecidableEq N] [Nonempty M]
    {Y : Type*} [TopologicalSpace Y] {y : Y} (f : C(X, Y)) (hf : f x = y) (e : M ≃ N)
    (a : HomotopyGroup M X x) :
    map f hf (congrMulEquiv e a) = congrMulEquiv e (map f hf a) := by
  rw [congrMulEquiv_apply, congrMulEquiv_apply]
  exact map_congrEquiv f hf e a

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

@[simp]
theorem zerothHomotopyEquiv_symm_mk (p : Ω^ N X x) :
    zerothHomotopyEquiv.symm (⟦p⟧ : HomotopyGroup N X x) =
      (⟦p⟧ : ZerothHomotopy (Ω^ N X x)) :=
  by rw [zerothHomotopyEquiv.eq_1]; rfl

/-- Mathlib's homeomorphism `Ω^ N X x ≃ₜ X` for empty `N` evaluates a zero-dimensional
generalized loop at the unique point of the cube. -/
@[simp]
theorem _root_.genLoopHomeoOfIsEmpty_apply [IsEmpty N] (p : Ω^ N X x) :
    genLoopHomeoOfIsEmpty N x p = p 0 :=
  rfl

/-- Mathlib's bijection between the homotopy group indexed by an empty type and the path
components of `X` sends the class of a zero-dimensional generalized loop to the path component of
its value. -/
@[simp]
theorem _root_.homotopyGroupEquivZerothHomotopyOfIsEmpty_mk [IsEmpty N] (p : Ω^ N X x) :
    homotopyGroupEquivZerothHomotopyOfIsEmpty N x (⟦p⟧ : HomotopyGroup N X x) =
      ZerothHomotopy.mk (p 0) :=
  rfl

/-- **Two loops at `x` are joined by a path in the loop space exactly when they are homotopic.**
This is `GenLoop.homotopic_iff_joined` for a singleton index type, carried across the
homeomorphism `GenLoop.homeomorphOfUnique` onto Mathlib's loop space `Ω X x`. -/
theorem _root_.Path.joined_iff_homotopic {p q : Ω X x} : Joined p q ↔ p.Homotopic q := by
  set φ := GenLoop.homeomorphOfUnique (X := X) (x := x) (Fin 1)
  have hcoe : ∀ r : Ω^ (Fin 1) X x, genLoopEquivOfUnique (Fin 1) r = φ r := fun r =>
    Path.ext (funext fun t => (GenLoop.homeomorphOfUnique_apply (Fin 1) r t).symm)
  have key : _root_.GenLoop.Homotopic (φ.symm p) (φ.symm q) ↔ Joined p q := by
    rw [GenLoop.homotopic_iff_joined]
    exact ⟨fun h => by simpa using h.map φ.continuous, fun h => h.map φ.symm.continuous⟩
  rw [← key, ← GenLoop.homotopic_genLoopEquivOfUnique_iff, hcoe, hcoe,
    Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- **The path components of Mathlib's loop space `Ω X x` are the fundamental group of `X`
at `x`**: the degree-zero case of the loop-space shift. Both sides are quotients of `Ω X x`, by
path connectedness and by homotopy respectively, and `Path.joined_iff_homotopic` says the two
relations agree. -/
def zerothHomotopyLoopSpaceEquivFundamentalGroup :
    ZerothHomotopy (Ω X x) ≃ FundamentalGroup X x :=
  Quotient.congr (Equiv.refl (Ω X x)) fun _ _ => Path.joined_iff_homotopic

@[simp]
theorem zerothHomotopyLoopSpaceEquivFundamentalGroup_mk (p : Ω X x) :
    zerothHomotopyLoopSpaceEquivFundamentalGroup (⟦p⟧ : ZerothHomotopy (Ω X x)) =
      (Path.Homotopic.Quotient.mk p : FundamentalGroup X x) :=
  by rw [zerothHomotopyLoopSpaceEquivFundamentalGroup.eq_1]; rfl

@[simp]
theorem zerothHomotopyLoopSpaceEquivFundamentalGroup_symm_mk (p : Ω X x) :
    zerothHomotopyLoopSpaceEquivFundamentalGroup.symm
        (Path.Homotopic.Quotient.mk p : FundamentalGroup X x) =
      (⟦p⟧ : ZerothHomotopy (Ω X x)) :=
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

@[simp]
theorem loopSpaceEquiv_symm_mk (q : Ω^ (M ⊕ N) X x) :
    loopSpaceEquiv.symm (⟦q⟧ : HomotopyGroup (M ⊕ N) X x) =
      ⟦(_root_.GenLoop.genLoopGenLoopEquiv x).symm q⟧ :=
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

@[simp]
theorem loopSpaceMulEquiv_symm_apply [DecidableEq M] [DecidableEq N] [Nonempty M]
    (b : HomotopyGroup (M ⊕ N) X x) :
    loopSpaceMulEquiv.symm b = loopSpaceEquiv.symm b :=
  by rw [loopSpaceMulEquiv.eq_1]; rfl

@[simp]
theorem loopSpaceMulEquiv_symm_mk [DecidableEq M] [DecidableEq N] [Nonempty M]
    (q : Ω^ (M ⊕ N) X x) :
    loopSpaceMulEquiv.symm (⟦q⟧ : HomotopyGroup (M ⊕ N) X x) =
      ⟦(_root_.GenLoop.genLoopGenLoopEquiv x).symm q⟧ :=
  (loopSpaceMulEquiv_symm_apply _).trans (loopSpaceEquiv_symm_mk q)

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

@[simp]
theorem piLoopSpaceMulEquiv_symm_apply (m n : ℕ) (b : π_ (m + 1 + n) X x) :
    (piLoopSpaceMulEquiv m n).symm b =
      loopSpaceMulEquiv.symm ((congrMulEquiv finSumFinEquiv).symm b) :=
  by rw [piLoopSpaceMulEquiv.eq_1]; rfl

@[simp]
theorem piLoopSpaceMulEquiv_symm_mk (m n : ℕ) (q : Ω^ (Fin (m + 1 + n)) X x) :
    (piLoopSpaceMulEquiv m n).symm (⟦q⟧ : π_ (m + 1 + n) X x) =
      ⟦(_root_.GenLoop.genLoopGenLoopEquiv x).symm
        (_root_.GenLoop.congr x finSumFinEquiv.symm q)⟧ :=
  (piLoopSpaceMulEquiv_symm_apply m n _).trans <|
    (congrArg (fun a : HomotopyGroup (Fin (m + 1) ⊕ Fin n) X x => loopSpaceMulEquiv.symm a)
      (congrMulEquiv_symm_mk finSumFinEquiv q)).trans
        (loopSpaceMulEquiv_symm_mk _)

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

@[simp]
theorem pathLoopSpaceMulEquiv_symm_apply (m : ℕ) (b : π_ (m + 2) X x) :
    (pathLoopSpaceMulEquiv m).symm b =
      homeomorphMulEquivOfEq (N := Fin (m + 1)) (GenLoop.homeomorphOfUnique (Fin 1))
        (GenLoop.homeomorphOfUnique_const (Fin 1)) ((piLoopSpaceMulEquiv m 1).symm b) :=
  by rw [pathLoopSpaceMulEquiv.eq_1]; rfl

@[simp]
theorem pathLoopSpaceMulEquiv_symm_mk (m : ℕ) (q : Ω^ (Fin (m + 2)) X x) :
    (pathLoopSpaceMulEquiv m).symm (⟦q⟧ : π_ (m + 2) X x) =
      ⟦_root_.GenLoop.map
        ⟨GenLoop.homeomorphOfUnique (Fin 1), (GenLoop.homeomorphOfUnique (Fin 1)).continuous⟩
        (GenLoop.homeomorphOfUnique_const (Fin 1))
        ((_root_.GenLoop.genLoopGenLoopEquiv x).symm
          (_root_.GenLoop.congr x finSumFinEquiv.symm q))⟧ :=
  (pathLoopSpaceMulEquiv_symm_apply m _).trans <|
    (congrArg (fun a : HomotopyGroup (Fin (m + 1)) (Ω^ (Fin 1) X x) _root_.GenLoop.const =>
        homeomorphMulEquivOfEq (N := Fin (m + 1)) (GenLoop.homeomorphOfUnique (Fin 1))
          (GenLoop.homeomorphOfUnique_const (Fin 1)) a)
      (piLoopSpaceMulEquiv_symm_mk m 1 q)).trans <|
      (homeomorphMulEquivOfEq_apply _ _ _).trans (map_mk _ _ _)

section Natural

variable {Y : Type*} [TopologicalSpace Y] {y : Y}

/-- The shift `loopSpaceEquiv` is natural: it commutes with the maps induced on homotopy sets by a
based map `f` and by any map `F` of cube-loop spaces that postcomposes with `f`. -/
theorem _root_.ContinuousMap.loopSpaceEquiv_map (f : C(X, Y)) (hf : f x = y)
    (F : C(Ω^ N X x, Ω^ N Y y)) (hFf : ∀ γ t, F γ t = f (γ t))
    (a : HomotopyGroup M (Ω^ N X x) _root_.GenLoop.const) :
    loopSpaceEquiv (map F (GenLoop.ext _ _ fun t => (hFf _ t).trans hf) a) =
      map f hf (loopSpaceEquiv a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [map_mk, loopSpaceEquiv_mk, loopSpaceEquiv_mk, map_mk]
    refine congrArg _ (GenLoop.ext _ _ fun t => ?_)
    simp [hFf]

/-- The `π_n` form of the shift is natural, for any map `F` of cube-loop spaces that postcomposes
with `f`. -/
theorem _root_.ContinuousMap.piLoopSpaceMulEquiv_map (f : C(X, Y)) (hf : f x = y) (m n : ℕ)
    (F : C(Ω^ (Fin n) X x, Ω^ (Fin n) Y y)) (hFf : ∀ γ t, F γ t = f (γ t))
    (a : π_ (m + 1) (Ω^ (Fin n) X x) _root_.GenLoop.const) :
    piLoopSpaceMulEquiv m n (map F (GenLoop.ext _ _ fun t => (hFf _ t).trans hf) a) =
      map f hf (piLoopSpaceMulEquiv m n a) := by
  rw [piLoopSpaceMulEquiv_apply, piLoopSpaceMulEquiv_apply, loopSpaceMulEquiv_apply,
    loopSpaceMulEquiv_apply]
  exact (congrArg (congrMulEquiv finSumFinEquiv) (f.loopSpaceEquiv_map hf F hFf a)).trans
    (f.map_congrMulEquiv hf finSumFinEquiv _).symm

/-- The shift `pathLoopSpaceMulEquiv` is natural: it commutes with the maps induced on homotopy
groups by a based map `f` and by any map `F` of loop spaces that postcomposes loops with `f`. -/
theorem _root_.ContinuousMap.pathLoopSpaceMulEquiv_map (f : C(X, Y)) (hf : f x = y)
    (F : C(Ω X x, Ω Y y)) (hFf : ∀ γ t, F γ t = f (γ t)) (m : ℕ)
    (a : π_ (m + 1) (Ω X x) (Path.refl x)) :
    pathLoopSpaceMulEquiv m (map F (Path.ext (funext fun t => (hFf _ t).trans hf)) a) =
      map f hf (pathLoopSpaceMulEquiv m a) := by
  -- the loop space `Ω X x` is `Ω^ (Fin 1) X x` through `homeomorphOfUnique`, under which `F`
  -- becomes the postcomposition with `f` on cube loops
  let F' : C(Ω^ (Fin 1) X x, Ω^ (Fin 1) Y y) :=
    ⟨_root_.GenLoop.map f hf, _root_.GenLoop.continuous_map f hf⟩
  rw [pathLoopSpaceMulEquiv_apply, pathLoopSpaceMulEquiv_apply]
  have key : (homeomorphMulEquivOfEq (N := Fin (m + 1)) (GenLoop.homeomorphOfUnique (Fin 1))
      (GenLoop.homeomorphOfUnique_const (Fin 1))).symm
        (map F (Path.ext (funext fun t => (hFf _ t).trans hf)) a) =
      map (y := (_root_.GenLoop.const : Ω^ (Fin 1) Y y)) F'
        (_root_.GenLoop.map_const f hf)
        ((homeomorphMulEquivOfEq (N := Fin (m + 1)) (GenLoop.homeomorphOfUnique (Fin 1))
          (GenLoop.homeomorphOfUnique_const (Fin 1))).symm a) := by
    induction a using Quotient.inductionOn with
    | h p =>
      refine congrArg (Quotient.mk _) (GenLoop.ext _ _ fun t => GenLoop.ext _ _ fun s => ?_)
      simp [F', hFf]
  rw [key]
  exact f.piLoopSpaceMulEquiv_map hf m 1 F' (fun p t => _root_.GenLoop.map_apply f hf p t) _

end Natural

end HomotopyGroup
