/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeltaRing.Free

/-!
# Checks for free `δ`-rings

These examples exercise the free `δ`-ring `FreeDeltaRing p S = ℤ[x_{s,n}]`. Its Frobenius sends
`x_{s,0}` to `x_{s,0} ^ p + p * x_{s,1}`. At `p = 2`, the `δ`-map `FreeDeltaRing 2 Unit → ℤ`
with `x_0 ↦ 2` sends `x_1 = δ x_0` to `δ 2 = -1`. Every function on the generators `x_{s,0}`
extends to exactly one `δ`-map. The free `δ`-ring on the empty type is `ℤ`. The free `δ`-ring on
one generator is strictly bigger than the free ring `ℤ[x]`, since `x_1 = δ x_0` is not a
polynomial in `x_0`.
-/

public section

namespace TauCeti.Examples

open DeltaRing FreeDeltaRing

variable (p : ℕ) [Fact p.Prime]

-- The Frobenius of the free `δ`-ring sends `x_{s,0}` to `x_{s,0} ^ p + p * x_{s,1}`.
example {S : Type*} (s : S) :
    frobenius p (FreeDeltaRing p S) (X s 0) = X s 0 ^ p + (p : FreeDeltaRing p S) * X s 1 :=
  frobenius_X s 0

-- At `p = 2`, the `δ`-map `FreeDeltaRing 2 Unit → ℤ` with `x_0 ↦ 2` sends `x_1` to `-1`.
example : (lift 2 Unit ℤ fun _ => 2).val (X () 1) = -1 := by
  simp

-- Every function on the generators `x_{s,0}` extends to exactly one `δ`-map.
example {S B : Type*} [CommRing B] [DeltaRing p B] (x : S → B) :
    ∃! f : FreeDeltaRing p S →+* B, IsDeltaMap p f ∧ ∀ s, f (X s 0) = x s := by
  refine ⟨(lift p S B x).val, ⟨(lift p S B x).property, fun s => by simp⟩, ?_⟩
  rintro f ⟨hf, hfx⟩
  exact isDeltaMap_ext hf (lift p S B x).property fun s => by simp [hfx]

-- The free `δ`-ring on the empty type is `ℤ`: the structure map `ℤ → FreeDeltaRing p Empty` is
-- bijective.
example : Function.Bijective (Int.castRingHom (FreeDeltaRing p Empty)) := by
  have h : Int.castRingHom (FreeDeltaRing p Empty) =
      ((equivMvPolynomial p Empty).symm.toRingHom.comp
        (MvPolynomial.isEmptyRingEquiv ℤ (Empty × ℕ)).symm.toRingHom) :=
    RingHom.ext_int _ _
  rw [h]
  exact ((MvPolynomial.isEmptyRingEquiv ℤ (Empty × ℕ)).symm.trans
    (equivMvPolynomial p Empty).symm).bijective

-- The free `δ`-ring on one generator is bigger than the free ring `ℤ[x]`: `x_1 = δ x_0` is not in
-- the image of `ℤ[x] → FreeDeltaRing p Unit`, `x ↦ x_0`. Two ring maps to `ℤ` agree on that image
-- but differ on `x_1`.
example : X () 1 ∉ Set.range (Polynomial.eval₂RingHom (Int.castRingHom (FreeDeltaRing p Unit))
    (X () 0)) := by
  rintro ⟨q, hq⟩
  let ev (c : ℤ) : FreeDeltaRing p Unit →+* ℤ :=
    (MvPolynomial.eval fun i : Unit × ℕ => if i.2 = 0 then 0 else c).comp
      (equivMvPolynomial p Unit).toRingHom
  have hev (c : ℤ) : ev c (X () 1) = c := by simp [ev]
  have hq' (c : ℤ) : ev c (X () 1) = q.eval 0 := by
    rw [← hq, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, RingHom.ext_int
      ((ev c).comp (Int.castRingHom _)) (RingHom.id ℤ), Polynomial.eval₂_id]
    simp [ev]
  have := (hev 0).symm.trans ((hq' 0).trans ((hq' 1).symm.trans (hev 1)))
  exact zero_ne_one this

end TauCeti.Examples
