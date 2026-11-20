/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Ring

/-!
# Directed colimits of commutative rings

Basic API for Mathlib's directed colimit `Ring.DirectLimit G f` of commutative rings `G i`.

The canonical maps into the colimit are compatible with the transition maps as ring homomorphisms,
and two elements of stages have the same image in the colimit if and only if they agree at a
common later stage. When the transition maps `f i j` agree pointwise with maps `F i j` of some
class of ring homomorphisms (for instance `A`-algebra maps), `Ring.DirectLimit G f` is isomorphic
as a ring to Mathlib's generic directed colimit `DirectLimit G F`, compatibly with the canonical
maps from the stages. For ring homomorphisms `F = f` this is Mathlib's
`Ring.DirectLimit.ringEquiv`; for `A`-algebra maps `F` it identifies `Ring.DirectLimit G f` with a
colimit that carries the `A`-algebra structure.

## Main results

* `TauCeti.Ring.DirectLimit.of_comp_f`: the canonical maps into the colimit are compatible with
  the transition maps.
* `TauCeti.Ring.DirectLimit.of_eq_of_iff`: two elements of stages have the same image in the
  colimit if and only if they agree at a common later stage.
* `TauCeti.Ring.DirectLimit.ringEquivOfEq`: the ring isomorphism between `Ring.DirectLimit G f`
  and the generic colimit `DirectLimit G F` when `F i j` agrees pointwise with `f i j`, with its
  values on stage elements in both directions (`ringEquivOfEq_of`, `ringEquivOfEq_symm_mk`).
-/

public section

namespace TauCeti.Ring.DirectLimit

open _root_.Ring.DirectLimit

section Ring

variable {ι : Type*} [Preorder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j}

/-- The canonical maps into a direct limit are compatible with the transition maps. -/
@[simp]
theorem of_comp_f {i j : ι} (hij : i ≤ j) :
    (of G (f · · ·) j).comp (f i j hij) = of G (f · · ·) i :=
  RingHom.ext fun _ ↦ of_f _ _

/-- Two elements of stages of a directed system of commutative rings have the same image in the
direct limit if and only if they agree at a common later stage. -/
theorem of_eq_of_iff [IsDirectedOrder ι] [DirectedSystem G (f · · ·)] {i j : ι} {x : G i}
    {y : G j} :
    of G (f · · ·) i x = of G (f · · ·) j y ↔
      ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k, f i k hik x = f j k hjk y := by
  have : Nonempty ι := ⟨i⟩
  -- Pass to the generic colimit, a quotient by `DirectLimit.setoid`, whose relation says that
  -- two elements of stages agree at a common later stage.
  rw [← (ringEquiv G f).injective.eq_iff, ringEquiv_of, ringEquiv_of, Quotient.eq]
  unfold _root_.DirectLimit.setoid
  rfl

end Ring

section RingHomClass

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] {G : ι → Type*}
  [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i → G j} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), RingHomClass (T h) (G i) (G j)]
  {F : ∀ i j (h : i ≤ j), T h} [DirectedSystem G (F · · ·)]
  (hF : ∀ i j hij x, F i j hij x = f i j hij x)

/-- If the transition maps `f i j` of a directed system of commutative rings agree pointwise with
maps `F i j` of some class of ring homomorphisms, then `Ring.DirectLimit G f` is isomorphic, as a
ring, to the generic directed colimit `DirectLimit G F`. The isomorphism sends the image of an
element of a stage under `Ring.DirectLimit.of` to its image under `DirectLimit.Ring.of`
(`ringEquivOfEq_of`). For ring homomorphisms `F = f` this is `Ring.DirectLimit.ringEquiv`. -/
noncomputable def ringEquivOfEq : _root_.Ring.DirectLimit G f ≃+* _root_.DirectLimit G F :=
  .ofRingHom
    (lift G f _ (_root_.DirectLimit.Ring.of G F) fun i j hij x ↦ by
      rw [← hF]
      exact _root_.DirectLimit.Ring.of_f hij x)
    (_root_.DirectLimit.Ring.lift G F _ (of G f) fun i j hij x ↦ by
      rw [hF]
      exact of_f hij x)
    (by ext; simp) (by ext; simp)

@[simp]
theorem ringEquivOfEq_of {i : ι} (x : G i) :
    ringEquivOfEq hF (of G f i x) = _root_.DirectLimit.Ring.of G F i x := by
  simp [ringEquivOfEq]

@[simp]
theorem ringEquivOfEq_symm_mk (x : Σ i, G i) :
    (ringEquivOfEq hF).symm ⟦x⟧ = of G f x.1 x.2 := by
  rw [RingEquiv.symm_apply_eq, ringEquivOfEq_of, _root_.DirectLimit.Ring.of_apply]

end RingHomClass

end TauCeti.Ring.DirectLimit
