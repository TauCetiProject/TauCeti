/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Ring
import TauCeti.Algebra.Colimit.CommonStage

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
* `Ring.DirectLimit.ringEquivIntOfIsEmpty`: over an empty index set the colimit is `ℤ`.
* `TauCeti.isDomain_of_directed`: a directed colimit of domains, possibly noncommutative,
  described elementwise, is a domain.
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

/-- Over an empty index set, `Ring.DirectLimit G f` is `ℤ`. -/
noncomputable def Ring.DirectLimit.ringEquivIntOfIsEmpty {ι : Type*} [Preorder ι] {G : ι → Type*}
    [∀ i, CommRing (G i)] [IsEmpty ι]
    (f : ∀ i j, i ≤ j → G i →+* G j) : ℤ ≃+* Ring.DirectLimit G fun i j h ↦ f i j h :=
  RingEquiv.ofRingHom (Int.castRingHom _)
    (Ring.DirectLimit.lift G _ ℤ (fun i ↦ isEmptyElim i) fun i ↦ isEmptyElim i)
    (Ring.DirectLimit.hom_ext (h := fun i ↦ isEmptyElim i)) (RingHom.ext_int _ _)

namespace TauCeti

/-- **A directed colimit of domains is a domain.** Here `R` is the colimit of
the `G i` along `φ`: every element of `R` comes from some `G i`, and an element of `G i` sent to
`0` in `R` is sent to `0` in some `G j`. -/
theorem isDomain_of_directed {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {G : ι → Type*}
    [∀ i, Ring (G i)] {R : Type*} [Ring R] (f : ∀ i j, i ≤ j → G i →+* G j) (φ : ∀ i, G i →+* R)
    (hf : ∀ i j h x, φ j (f i j h x) = φ i x) (hsurj : ∀ x : R, ∃ i y, φ i y = x)
    (hker : ∀ i y, φ i y = 0 → ∃ j h, f i j h y = 0) [∀ i, IsDomain (G i)] :
    IsDomain R := by
  classical
  -- `1 ≠ 0` in `R`: otherwise `1` would vanish in some domain `G j`.
  have : Nontrivial R := by
    refine ⟨0, 1, fun h ↦ ?_⟩
    obtain ⟨i, -⟩ := hsurj 0
    obtain ⟨j, hij, hj⟩ := hker i 1 (by rw [map_one, h])
    exact one_ne_zero (by rwa [map_one] at hj)
  have : NoZeroDivisors R := ⟨fun {a b} hab ↦ by
    obtain ⟨i, g, hg⟩ := DirectLimit.exists_lift (t := fun i j h ↦ f i j h) (φ := fun i ↦ φ i)
      hf hsurj {a, b}
    obtain ⟨x, rfl⟩ : ∃ x, φ i x = a := ⟨g a, hg a (by simp)⟩
    obtain ⟨y, rfl⟩ : ∃ y, φ i y = b := ⟨g b, hg b (by simp)⟩
    obtain ⟨j, hij, h⟩ := hker i (x * y) (by rw [map_mul, hab])
    rw [map_mul, mul_eq_zero] at h
    rw [← hf i j hij x, ← hf i j hij y]
    exact h.imp (fun h ↦ by rw [h, map_zero]) fun h ↦ by rw [h, map_zero]⟩
  exact NoZeroDivisors.to_isDomain R

end TauCeti
