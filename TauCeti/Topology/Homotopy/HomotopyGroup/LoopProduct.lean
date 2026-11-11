/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HSpaces
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product
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
loops `p` to the cube `t ↦ p (t ∘ some) (t none)`. It induces the group isomorphism
`HomotopyGroup.loopSpaceOptionMulEquiv : π_N(Ω X x) ≃* π_(Option N)(X)`, and it carries the
pointwise concatenation of loops to a concatenation in the direction `none`. The class of a
concatenation of generalized loops does not depend on the direction
(`HomotopyGroup.transAt_indep`), so this represents the product of the two classes. Mathlib's
`HomotopyGroup.mul_spec` reads a concatenation as the product in the opposite order, which does
not matter here: `π_(Option N)(X, x)` has at least two cube directions, so it is commutative.

## Main declarations

* `GenLoop.genLoopLoopOptionHomeomorph_map_hmul_prod`: the pointwise concatenation of cube loops of
  loops becomes a concatenation in the direction `none`.
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

variable {N : Type*} [DecidableEq N]

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
  -- Mathlib's `HSpace (Path x x)` instance defines `hmul` as `fun ρ => ρ.1.trans ρ.2`, with no
  -- unfolding lemma, so the H-space product is exposed definitionally.
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

variable [DecidableEq N] [Nonempty N]

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
