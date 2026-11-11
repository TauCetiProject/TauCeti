/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HSpaces
public import TauCeti.Topology.Homotopy.GenLoop.Loop
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product
import TauCeti.Topology.Homotopy.GenLoop.Homotopic
import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt

/-!
# The loop product on the homotopy groups of a loop space

The loop space `Ω X x = Path x x` is an H-space under concatenation of loops (Mathlib's
`HSpace (Path x x)`, with multiplication `γ ⋀ δ = γ.trans δ`). This file shows that this
multiplication induces the group law of the homotopy groups of `Ω X x`: for a nonempty type `N`
and classes `c` and `d` in `π_N(Ω X x, refl x)`, the class of the pointwise concatenation of
representatives is `c * d` (`HomotopyGroup.map_hmul_prod`). Consequently, for based maps
`f : Y → Ω X x` and `g : Z → Ω X x`, the map `(w, z) ↦ f w ⋀ g z` sends the product class of `a`
and `c` to `f_* a * g_* c` (`HomotopyGroup.map_hmul_comp_prodMap`).

The proof curries the path parameter of `Ω X x` into an extra cube direction. Here that direction
is the coordinate `none` of the cube `I^(Option N)`: the homeomorphism
`GenLoop.genLoopLoopOptionHomeomorph : Ω^ N (Ω X x) (refl x) ≃ₜ Ω^ (Option N) X x` sends a cube of
loops `p` to the cube `t ↦ p (t ∘ some) (t none)`. Under it, a concatenation in the cube direction
`i` becomes a concatenation in the direction `some i`, while the pointwise concatenation of loops
becomes a concatenation in the direction `none`. The class of a concatenation of generalized loops
does not depend on the direction (`HomotopyGroup.transAt_indep`), so both represent a product of
the two classes. Mathlib's `HomotopyGroup.mul_spec` reads a concatenation as the product in the
opposite order, which does not matter here: `π_(Option N)(X, x)` has at least two cube directions,
so it is commutative.

The induced isomorphism `HomotopyGroup.loopSpaceOptionMulEquiv : π_N(Ω X x) ≃* π_(Option N)(X)` is
the loop-space shift in the indexing of the boundary map of a Serre fibration
(`TauCeti.TopCat.fibrationBoundary`), whose lifting direction is also `none`.

## Main declarations

* `GenLoop.genLoopLoopOptionHomeomorph`: `Ω^ N (Ω X x) (refl x) ≃ₜ Ω^ (Option N) X x`.
* `HomotopyGroup.loopSpaceOptionMulEquiv`: the loop-space shift
  `π_N(Ω X x, refl x) ≃* π_(Option N)(X, x)`, natural in `X`
  (`ContinuousMap.loopSpaceOptionEquiv_map`).
* `HomotopyGroup.map_hmul_prod`: loop concatenation induces the product of `π_N(Ω X x, refl x)`.
* `HomotopyGroup.map_hmul_comp_prodMap`: the map `(w, z) ↦ f w ⋀ g z` sends the product class of
  `a` and `c` to `f_* a * g_* c`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1 (the loop-space
  shift `π_n(Ω X) ≅ π_(n+1)(X)`) and Section 3.C (H-spaces).
-/

public section

open scoped unitInterval Topology Topology.Homotopy HSpaces

namespace GenLoop

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

section Option

/-- The reindexing `N ⊕ Fin 1 ≃ Option N` sending the extra direction to `none`. -/
private def sumFinOneEquivOption (N : Type*) : N ⊕ Fin 1 ≃ Option N :=
  (Equiv.sumCongr (Equiv.refl N) (Equiv.equivPUnit (Fin 1) : Fin 1 ≃ PUnit.{1})).trans
    (Equiv.optionEquivSumPUnit N).symm

variable (x) in
/-- Currying the path parameter of the loop space `Ω X x` into the cube direction `none`: cube
loops in the directions `N` of `Ω X x`, based at the constant loop, are cube loops of `X` in the
directions `Option N`. -/
def genLoopLoopOptionHomeomorph (N : Type*) : Ω^ N (Ω X x) (Path.refl x) ≃ₜ Ω^ (Option N) X x :=
  (genLoopLoopSumHomeomorph x N).trans (_root_.GenLoop.congr x (sumFinOneEquivOption N))

variable (x) in
/-- The direction `none` of `genLoopLoopOptionHomeomorph` is the path parameter. -/
@[simp]
theorem genLoopLoopOptionHomeomorph_apply {N : Type*} (p : Ω^ N (Ω X x) (Path.refl x))
    (t : I^(Option N)) :
    genLoopLoopOptionHomeomorph x N p t = p (fun i => t (some i)) (t none) := by
  rw [genLoopLoopOptionHomeomorph, Homeomorph.trans_apply, congr_apply,
    genLoopLoopSumHomeomorph_apply]
  rfl

variable (x) in
/-- The homeomorphism `genLoopLoopOptionHomeomorph` is based. -/
@[simp]
theorem genLoopLoopOptionHomeomorph_const (N : Type*) :
    genLoopLoopOptionHomeomorph x N (GenLoop.const : Ω^ N (Ω X x) (Path.refl x)) =
      GenLoop.const :=
  _root_.GenLoop.ext _ _ fun t => by simp

/-- **Naturality of `genLoopLoopOptionHomeomorph`**: it commutes with the maps induced on cube
loops by a based continuous map `f : X → Y`, and by any map `F` of loop spaces that postcomposes
loops with `f`. -/
theorem _root_.ContinuousMap.genLoopLoopOptionHomeomorph_map (f : C(X, Y)) (hf : f x = y)
    (F : C(Ω X x, Ω Y y)) (hFf : ∀ γ t, F γ t = f (γ t)) {N : Type*}
    (p : Ω^ N (Ω X x) (Path.refl x)) :
    genLoopLoopOptionHomeomorph y N (map F (Path.ext (funext fun t => (hFf _ t).trans hf)) p) =
      map f hf (genLoopLoopOptionHomeomorph x N p) :=
  _root_.GenLoop.ext _ _ fun t => by simp [hFf]

variable {N : Type*} [DecidableEq N]

/-- `genLoopLoopOptionHomeomorph` carries a concatenation in the cube direction `i` to a
concatenation in the direction `some i`. -/
theorem genLoopLoopOptionHomeomorph_transAt (i : N) (p q : Ω^ N (Ω X x) (Path.refl x)) :
    genLoopLoopOptionHomeomorph x N (_root_.GenLoop.transAt i p q) =
      _root_.GenLoop.transAt (some i) (genLoopLoopOptionHomeomorph x N p)
        (genLoopLoopOptionHomeomorph x N q) := by
  refine _root_.GenLoop.ext _ _ fun t => ?_
  -- Restricting `t` to the directions `some j` commutes with updating the direction `i`.
  have hupd (s : I) : (fun j => Function.update t (some i) s (some j)) =
      Function.update (fun j => t (some j)) i s := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [genLoopLoopOptionHomeomorph_apply]
  rcases le_or_gt (t (some i) : ℝ) (1 / 2) with h | h
  · rw [transAt_apply_of_le i p q (t := fun j => t (some j)) h (a := ⟨_, _⟩) rfl,
      transAt_apply_of_le (some i) _ _ h (a := ⟨2 * t (some i), _⟩) rfl,
      genLoopLoopOptionHomeomorph_apply, hupd, Function.update_of_ne (Option.some_ne_none i).symm]
    · exact (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(t (some i)).2.1, h⟩
  · rw [transAt_apply_of_lt i p q (t := fun j => t (some j)) h (a := ⟨_, _⟩) rfl,
      transAt_apply_of_lt (some i) _ _ h (a := ⟨2 * t (some i) - 1, _⟩) rfl,
      genLoopLoopOptionHomeomorph_apply, hupd, Function.update_of_ne (Option.some_ne_none i).symm]
    · exact unitInterval.two_mul_sub_one_mem_iff.2 ⟨h.le, (t (some i)).2.2⟩

/-- `genLoopLoopOptionHomeomorph` carries the pointwise concatenation of two cube loops of loops,
`t ↦ p t ⋀ q t`, to the concatenation of their images in the direction `none`. -/
theorem genLoopLoopOptionHomeomorph_map_hmul_prod (p q : Ω^ N (Ω X x) (Path.refl x)) :
    genLoopLoopOptionHomeomorph x N
        (map (x := (Path.refl x, Path.refl x)) (y := Path.refl x) HSpace.hmul HSpace.hmul_e_e
          (prod p q)) =
      _root_.GenLoop.transAt none (genLoopLoopOptionHomeomorph x N p)
        (genLoopLoopOptionHomeomorph x N q) := by
  refine _root_.GenLoop.ext _ _ fun t => ?_
  have hupd (s : I) : (fun j => Function.update t none s (some j)) = fun j => t (some j) := by
    funext j
    simp
  rw [genLoopLoopOptionHomeomorph_apply, map_apply, prod_apply]
  change ((p fun j => t (some j)).trans (q fun j => t (some j))) (t none) = _
  rw [Path.trans_apply]
  split_ifs with h
  · rw [transAt_apply_of_le none _ _ h (a := ⟨2 * t none, _⟩) rfl,
      genLoopLoopOptionHomeomorph_apply, hupd, Function.update_self]
  · rw [transAt_apply_of_lt none _ _ (not_le.1 h) (a := ⟨2 * t none - 1, _⟩) rfl,
      genLoopLoopOptionHomeomorph_apply, hupd, Function.update_self]

end Option

end GenLoop

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- **The loop-space shift in the direction `none`**: the bijection
`π_N(Ω X x, refl x) ≃ π_(Option N)(X, x)` induced by the homeomorphism
`GenLoop.genLoopLoopOptionHomeomorph`, which curries the path parameter of the loop space into the
cube direction `none`. -/
def loopSpaceOptionEquiv :
    HomotopyGroup N (Ω X x) (Path.refl x) ≃ HomotopyGroup (Option N) X x :=
  Quotient.congr (GenLoop.genLoopLoopOptionHomeomorph x N).toEquiv fun _ _ =>
    (Homeomorph.genLoopHomotopic_iff _).symm

@[simp]
theorem loopSpaceOptionEquiv_mk (p : Ω^ N (Ω X x) (Path.refl x)) :
    loopSpaceOptionEquiv (⟦p⟧ : HomotopyGroup N (Ω X x) (Path.refl x)) =
      ⟦GenLoop.genLoopLoopOptionHomeomorph x N p⟧ := by
  rw [loopSpaceOptionEquiv.eq_1]; rfl

/-- **Naturality of the loop-space shift**: `loopSpaceOptionEquiv` commutes with the maps induced
on homotopy groups by a based map `f : X → Y` and by any map `F` of loop spaces that postcomposes
loops with `f`. -/
theorem _root_.ContinuousMap.loopSpaceOptionEquiv_map (f : C(X, Y)) (hf : f x = y)
    (F : C(Ω X x, Ω Y y)) (hFf : ∀ γ t, F γ t = f (γ t))
    (a : HomotopyGroup N (Ω X x) (Path.refl x)) :
    loopSpaceOptionEquiv (map F (Path.ext (funext fun t => (hFf _ t).trans hf)) a) =
      map f hf (loopSpaceOptionEquiv a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [map_mk, loopSpaceOptionEquiv_mk, loopSpaceOptionEquiv_mk, map_mk,
      f.genLoopLoopOptionHomeomorph_map hf F hFf]

variable [DecidableEq N] [Nonempty N]

/-- **The loop-space shift in the direction `none` is an isomorphism of groups**:
`π_N(Ω X x, refl x) ≃* π_(Option N)(X, x)`. -/
def loopSpaceOptionMulEquiv :
    HomotopyGroup N (Ω X x) (Path.refl x) ≃* HomotopyGroup (Option N) X x where
  toEquiv := loopSpaceOptionEquiv
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [Equiv.toFun_as_coe, mul_spec (i := Classical.arbitrary N), loopSpaceOptionEquiv_mk,
      GenLoop.genLoopLoopOptionHomeomorph_transAt]
    exact (mul_spec (i := some (Classical.arbitrary N))).symm

@[simp]
theorem loopSpaceOptionMulEquiv_apply (a : HomotopyGroup N (Ω X x) (Path.refl x)) :
    loopSpaceOptionMulEquiv a = loopSpaceOptionEquiv a :=
  (rfl)

theorem loopSpaceOptionMulEquiv_mk (p : Ω^ N (Ω X x) (Path.refl x)) :
    loopSpaceOptionMulEquiv (⟦p⟧ : HomotopyGroup N (Ω X x) (Path.refl x)) =
      ⟦GenLoop.genLoopLoopOptionHomeomorph x N p⟧ :=
  loopSpaceOptionEquiv_mk p

/-- **Loop concatenation induces the group law on the homotopy groups of the loop space.** The
H-space multiplication `γ ⋀ δ = γ.trans δ` of `Ω X x` sends the product class of `c` and `d` to
`c * d` in `π_N(Ω X x, refl x)`. -/
theorem map_hmul_prod (c d : HomotopyGroup N (Ω X x) (Path.refl x)) :
    map (x := (Path.refl x, Path.refl x)) (y := Path.refl x) HSpace.hmul HSpace.hmul_e_e
      (prod c d) = c * d := by
  apply loopSpaceOptionMulEquiv.injective
  rw [_root_.map_mul]
  induction c, d using Quotient.inductionOn₂ with
  | h p q =>
    simp only [prod_mk, map_mk, loopSpaceOptionMulEquiv_mk,
      GenLoop.genLoopLoopOptionHomeomorph_map_hmul_prod]
    exact (mul_spec (i := none)).symm.trans (mul_comm _ _)

/-- **Concatenation of the values of two maps into a loop space.** For based maps
`f : Y → Ω X x` and `g : Z → Ω X x`, the map `(w, z) ↦ f w ⋀ g z` sends the product class of `a`
and `c` to `f_* a * g_* c` in `π_N(Ω X x, refl x)`. -/
theorem map_hmul_comp_prodMap {Z : Type*} [TopologicalSpace Z] {z : Z} (f : C(Y, Ω X x))
    (g : C(Z, Ω X x)) (hf : f y = Path.refl x) (hg : g z = Path.refl x) (a : HomotopyGroup N Y y)
    (c : HomotopyGroup N Z z) :
    map (HSpace.hmul.comp (f.prodMap g))
        (by rw [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, Prod.map_apply, hf, hg]
            exact HSpace.hmul_e_e)
        (prod a c) =
      map f hf a * map g hg c := by
  rw [← map_hmul_prod]
  induction a, c using Quotient.inductionOn₂ with
  | h p q =>
    simp only [map_mk, prod_mk]
    exact congrArg _ (GenLoop.ext _ _ fun t => by simp)

end HomotopyGroup
