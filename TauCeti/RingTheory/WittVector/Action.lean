/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import TauCeti.RingTheory.WittVector.Frobenius

/-!
# Group actions on Witt vectors

Let a monoid `G` act on a commutative ring `R` by ring endomorphisms. Then `G` acts on the
`p`-typical Witt vectors `W(R)` by ring endomorphisms, `g` acting by the map `W(g)` of Witt vectors
induced by `g`, that is coordinatewise. For instance the absolute Galois group of `ℚ_p` acts this
way on `A_inf = W(O_C♭)` and on `W(C♭)`, through its action on the tilt.

Since `W(g)` is natural in `g`, this action commutes with the Witt-vector Frobenius `φ`, and with
its inverse when `R` is perfect of characteristic `p`. Hence the monoid `ℕ × G` (with `ℕ` written
multiplicatively) acts on `W(R)` by ring endomorphisms, `(n, g)` acting by `φ ^ n ∘ g`.

## Main definitions

* `WittVector.mulSemiringAction`: the action of `G` on `W(R)` by ring endomorphisms.
* `WittVector.frobeniusPowSMulHom`: the action of `ℕ × G` on `W(R)`, `(n, g) ↦ φ ^ n ∘ g`, as a
  monoid homomorphism to the ring endomorphisms of `W(R)`.

## Main results

* `WittVector.coeff_smul`: `G` acts on Witt coordinates.
* `WittVector.smul_teichmuller`: `g • [r] = [g • r]`.
* `WittVector.frobenius_smul`, `WittVector.frobeniusEquiv_smul`,
  `WittVector.frobeniusEquiv_symm_smul`: the action commutes with Frobenius and its inverse.
* `WittVector.map_smul_of_map_smul`: an equivariant ring homomorphism `f` induces an equivariant
  map `W(f)`.
-/

public section

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {G R : Type*} [Monoid G] [CommRing R] [MulSemiringAction G R]

/-- A monoid acting on `R` by ring endomorphisms acts on the Witt vectors `W(R)` by ring
endomorphisms: `g` acts by the map `W(g)` of Witt vectors induced by `g`, that is on every Witt
coordinate. -/
noncomputable instance mulSemiringAction : MulSemiringAction G (WittVector p R) :=
  MulSemiringAction.compHom (WittVector p R)
    ({ toFun g := map (MulSemiringAction.toRingHom G R g)
       map_one' := RingHom.ext fun x ↦ ext fun n ↦ by simp [map_coeff]
       map_mul' g h := RingHom.ext fun x ↦ ext fun n ↦ by simp [map_coeff, mul_smul] } :
      G →* (WittVector p R →+* WittVector p R))

theorem smul_def (g : G) (x : WittVector p R) :
    g • x = map (MulSemiringAction.toRingHom G R g) x :=
  (rfl)

/-- `G` acts on the Witt coordinates. -/
@[simp]
theorem coeff_smul (g : G) (x : WittVector p R) (n : ℕ) : (g • x).coeff n = g • x.coeff n :=
  map_coeff _ x n

/-- `g • [r] = [g • r]` on Teichmüller representatives. -/
@[simp]
theorem smul_teichmuller (g : G) (r : R) : g • teichmuller p r = teichmuller p (g • r) :=
  map_teichmuller _ _ r

/-- The action of `G` commutes with the Witt-vector Frobenius. -/
@[simp]
theorem frobenius_smul (g : G) (x : WittVector p R) : frobenius (g • x) = g • frobenius x :=
  (map_frobenius _ x).symm

/-- `W(f)` intertwines the actions of `G` on `W(R)` and `W(S)` when the ring homomorphism `f`
intertwines the actions on `R` and `S`. -/
theorem map_smul_of_map_smul {S : Type*} [CommRing S] [MulSemiringAction G S] {f : R →+* S}
    (hf : ∀ (g : G) (r : R), f (g • r) = g • f r) (g : G) (x : WittVector p R) :
    map f (g • x) = g • map f x :=
  ext fun n ↦ by simp [map_coeff, hf]

section Perfect

variable [CharP R p] [PerfectRing R p]

/-- The action of `G` commutes with the Witt-vector Frobenius of a perfect ring. -/
@[simp]
theorem frobeniusEquiv_smul (g : G) (x : WittVector p R) :
    frobeniusEquiv p R (g • x) = g • frobeniusEquiv p R x :=
  (map_frobeniusEquiv _ x).symm

/-- The action of `G` commutes with the inverse of the Witt-vector Frobenius of a perfect ring. -/
@[simp]
theorem frobeniusEquiv_symm_smul (g : G) (x : WittVector p R) :
    (frobeniusEquiv p R).symm (g • x) = g • (frobeniusEquiv p R).symm x :=
  (map_frobeniusEquiv_symm _ x).symm

end Perfect

variable (p G R) in
/-- **The action of `ℕ × G` on `W(R)`**: the monoid `ℕ × G`, with `ℕ` written multiplicatively,
acts on `W(R)` by ring endomorphisms, `(n, g)` acting by `φ ^ n ∘ g` with `φ` the Witt-vector
Frobenius. This is an action because `φ` commutes with the action of `G`. -/
noncomputable def frobeniusPowSMulHom :
    Multiplicative ℕ × G →* (WittVector p R →+* WittVector p R) :=
  MonoidHom.noncommCoprod (powersHom _ frobenius)
    { toFun g := MulSemiringAction.toRingHom G (WittVector p R) g
      map_one' := RingHom.ext (one_smul G)
      map_mul' g h := RingHom.ext (mul_smul g h) }
    fun n g ↦ RingHom.ext fun x ↦ by
      simpa [RingHom.coe_pow] using Function.Commute.iterate_left
        (f := frobenius) (g := (g • ·)) (frobenius_smul g) n.toAdd x

/-- `(n, g) ∈ ℕ × G` acts on `W(R)` by `φ ^ n ∘ g`. -/
@[simp]
theorem frobeniusPowSMulHom_apply (n : ℕ) (g : G) (x : WittVector p R) :
    frobeniusPowSMulHom p G R (Multiplicative.ofAdd n, g) x = frobenius^[n] (g • x) := by
  -- `noncommCoprod` multiplies the two images, here the composite of `φ ^ n` and `g`
  have h : frobeniusPowSMulHom p G R (Multiplicative.ofAdd n, g) =
      frobenius ^ n * MulSemiringAction.toRingHom G (WittVector p R) g := (rfl)
  simp [h, RingHom.coe_pow]

end WittVector
