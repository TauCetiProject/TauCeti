/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Bijectivity across two interlocking exact triangles

Consider two exact triangles meeting at a group `I`:

```text
  B --a--> W --b--> I --c--> B
  I --d--> P --e--> K --f--> I
```

where `b`, `c`, `d`, `f` are monoid homomorphisms, `K` is a monoid, and `W`, `P`, `B` are
`MulOneClass`es (with `a` and `e` arbitrary functions). If the composite `d.comp b : W →* P` is
bijective, then so is `c.comp f : K →* B`.

## Main results

* `Function.MulExact.bijective_comp_of_two_triangles`: the multiplicative version.
* `Function.Exact.bijective_comp_of_two_triangles`: the additive version.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cohomology/ProjectiveLine/TiltedLineFormula.lean` (`TotalH.bijective_of_two_triangles`).
-/

public section

namespace Function

/-- Let `B → W → I → B` (with maps `a`, `b`, `c`) and `I → P → K → I` (with maps `d`, `e`, `f`)
be two exact triangles meeting at a group `I`, where `b`, `c`, `d`, `f` are monoid homomorphisms
and `K` is a monoid. If `d.comp b : W →* P` is bijective, then `c.comp f : K →* B` is bijective. -/
@[to_additive
  /-- Let `B → W → I → B` (with maps `a`, `b`, `c`) and `I → P → K → I` (with maps `d`, `e`, `f`)
  be two exact triangles meeting at an additive group `I`, where `b`, `c`, `d`, `f` are additive
  monoid homomorphisms and `K` is an additive monoid. If `d.comp b : W →+ P` is bijective, then
  `c.comp f : K →+ B` is bijective. -/]
theorem MulExact.bijective_comp_of_two_triangles {K P I W B : Type*}
    [Monoid K] [MulOneClass P] [Group I] [MulOneClass W] [MulOneClass B]
    {a : B → W} {b : W →* I} {c : I →* B} {d : I →* P} {e : P → K} {f : K →* I}
    (hab : MulExact a b) (hbc : MulExact b c) (hca : MulExact c a)
    (hde : MulExact d e) (hef : MulExact e f) (hfd : MulExact f d)
    (h_bij : Bijective (d.comp b)) :
    Bijective (c.comp f) := by
  obtain ⟨h_inj, h_surj⟩ := h_bij
  have h_e_one : ∀ p, e p = 1 :=
    h_surj.forall.2 fun w ↦ hde.apply_apply_eq_one (b w)
  have h_one_of_db (w : W) (hw : d (b w) = 1) : w = 1 :=
    h_inj (by simpa [MonoidHom.comp_apply] using hw)
  have h_d_inv {x : I} (hx : d x = 1) : d x⁻¹ = 1 := calc
    d x⁻¹ = 1 * d x⁻¹ := (one_mul _).symm
    _ = d x * d x⁻¹ := by rw [hx]
    _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  constructor
  · intro x y hxy
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hxy
    have h_cf : c (f x * (f y)⁻¹) = 1 := by
      rw [map_mul, hxy, ← map_mul, mul_inv_cancel, map_one]
    obtain ⟨w, hw⟩ := (hbc _).1 h_cf
    have h_dbw : d (b w) = 1 := by
      rw [hw, map_mul, hfd.apply_apply_eq_one x, h_d_inv (hfd.apply_apply_eq_one y), one_mul]
    obtain rfl : w = 1 := h_one_of_db w h_dbw
    have h_eq : f x = f y := mul_inv_eq_one.1 (by simpa [map_one] using hw.symm)
    obtain ⟨z, hz⟩ := (hfd (f x)⁻¹).1 (h_d_inv (hfd.apply_apply_eq_one x))
    have h_zx : z * x = 1 := by
      obtain ⟨p, hp⟩ := (hef (z * x)).1 (by rw [map_mul, hz, inv_mul_cancel])
      exact hp.symm.trans (h_e_one p)
    have h_yz : y * z = 1 := by
      obtain ⟨p, hp⟩ := (hef (y * z)).1 (by rw [map_mul, ← h_eq, hz, mul_inv_cancel])
      exact hp.symm.trans (h_e_one p)
    exact (calc y = y * (z * x) := by rw [h_zx, mul_one]
      _ = (y * z) * x := (mul_assoc y z x).symm
      _ = x := by rw [h_yz, one_mul]).symm
  · intro y
    obtain ⟨r, rfl⟩ : ∃ r : I, c r = y :=
      (hca y).1 (h_one_of_db (a y) (by rw [hab.apply_apply_eq_one y, map_one]))
    obtain ⟨w, hw⟩ : ∃ w : W, d (b w) = d r := h_surj (d r)
    have h_dr : d (r * (b w)⁻¹) = 1 := by
      rw [map_mul, ← hw, ← map_mul, mul_inv_cancel, map_one]
    obtain ⟨x, hx⟩ := (hfd (r * (b w)⁻¹)).1 h_dr
    have h_c_inv : c (b w)⁻¹ = 1 := calc
      c (b w)⁻¹ = 1 * c (b w)⁻¹ := (one_mul _).symm
      _ = c (b w) * c (b w)⁻¹ := by rw [hbc.apply_apply_eq_one w]
      _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    refine ⟨x, ?_⟩
    rw [MonoidHom.comp_apply, hx, map_mul, h_c_inv, mul_one]

end Function
