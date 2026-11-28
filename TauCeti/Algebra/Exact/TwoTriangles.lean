/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

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

The injectivity and surjectivity diagram chases are also exposed separately as
`Function.MulExact.injective_comp_of_two_triangles` and `Function.MulExact.surjective_comp`,
together with their additive counterparts (`Function.Exact.*`).

## Main results

* `Function.MulExact.injective_comp_of_two_triangles` and
  `Function.Exact.injective_comp_of_two_triangles`: injectivity of `c.comp f`.
* `Function.MulExact.surjective_comp` and `Function.Exact.surjective_comp`: surjectivity of `c ∘ f`.
* `Function.MulExact.bijective_comp_of_two_triangles` and
  `Function.Exact.bijective_comp_of_two_triangles`: bijectivity of `c.comp f`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cohomology/ProjectiveLine/TiltedLineFormula.lean` (`TotalH.bijective_of_two_triangles`).
-/

public section

namespace Function

@[to_additive]
private theorem map_inv_eq_one_of_eq_one {G M : Type*} [Group G] [MulOneClass M]
    (g : G →* M) {x : G} (hx : g x = 1) : g x⁻¹ = 1 :=
  (eq_one_iff_eq_one_of_mul_eq_one (map_mul_eq_one g (mul_inv_cancel x))).mp hx

@[to_additive]
private theorem map_mul_inv_eq_one_of_eq {G M : Type*} [Group G] [MulOneClass M]
    (g : G →* M) {x y : G} (hxy : g x = g y) : g (x * y⁻¹) = 1 := by
  rw [map_mul, hxy]
  exact map_mul_eq_one g (mul_inv_cancel y)

/-- Injectivity half of the two-triangle diagram chase: if `B → W → I → B` (at `I`) and
`I → P → K → I` are exact and `d.comp b : W →* P` is bijective, then `c.comp f : K →* B` is
injective. -/
@[to_additive
  /-- Injectivity half of the two-triangle diagram chase: if `B → W → I → B` (at `I`) and
  `I → P → K → I` are exact and `d.comp b : W →+ P` is bijective, then `c.comp f : K →+ B` is
  injective. -/]
theorem MulExact.injective_comp_of_two_triangles {K P I W B : Type*}
    [Monoid K] [MulOneClass P] [Group I] [MulOneClass W] [MulOneClass B]
    {b : W →* I} {c : I →* B} {d : I →* P} {e : P → K} {f : K →* I}
    (hbc : MulExact b c) (hde : MulExact d e) (hef : MulExact e f) (hfd : MulExact f d)
    (h_bij : Bijective (d.comp b)) :
    Injective (c.comp f) := by
  obtain ⟨h_inj, h_surj⟩ := h_bij
  have h_e_one : ∀ p, e p = 1 :=
    h_surj.forall.2 fun w ↦ hde.apply_apply_eq_one (b w)
  intro x y hxy
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hxy
  obtain ⟨w, hw⟩ := (hbc _).1 (map_mul_inv_eq_one_of_eq c hxy)
  have h_dbw : d (b w) = 1 := by
    simp [hw, hfd.apply_apply_eq_one, map_inv_eq_one_of_eq_one]
  obtain rfl : w = 1 := (map_eq_one_iff (d.comp b) h_inj).mp h_dbw
  have h_eq : f x = f y := mul_inv_eq_one.1 (by simpa [map_one] using hw.symm)
  obtain ⟨z, hz⟩ := (hfd (f x)⁻¹).1 (map_inv_eq_one_of_eq_one d (hfd.apply_apply_eq_one x))
  have h_zx : z * x = 1 := by
    obtain ⟨p, hp⟩ := (hef (z * x)).1 (by simp [hz])
    exact hp.symm.trans (h_e_one p)
  have h_yz : y * z = 1 := by
    obtain ⟨p, hp⟩ := (hef (y * z)).1 (by simp [← h_eq, hz])
    exact hp.symm.trans (h_e_one p)
  exact (left_inv_eq_right_inv h_yz h_zx).symm

/-- Surjectivity half of the two-triangle diagram chase: if `c : I →* B` is surjective, kills the
image of `b : W → I`, `MulExact f d`, and `d ∘ b` is surjective, then `c ∘ f : K → B` is
surjective. -/
@[to_additive
  /-- Surjectivity half of the two-triangle diagram chase: if `c : I →+ B` is surjective, kills
  the image of `b : W → I`, `Exact f d`, and `d ∘ b` is surjective, then `c ∘ f : K → B` is
  surjective. -/]
theorem MulExact.surjective_comp {K P I W B : Type*}
    [Group I] [MulOneClass P] [MulOneClass B]
    {b : W → I} {c : I →* B} {d : I →* P} {f : K → I}
    (hc : Surjective c) (hcb : ∀ w, c (b w) = 1) (hfd : MulExact f d)
    (hdb : Surjective (d ∘ b)) :
    Surjective (c ∘ f) := by
  intro y
  obtain ⟨r, rfl⟩ := hc y
  obtain ⟨w, hw⟩ := hdb (d r)
  obtain ⟨x, hx⟩ := (hfd (r * (b w)⁻¹)).1 (map_mul_inv_eq_one_of_eq d hw.symm)
  exact ⟨x, by simp [hx, map_inv_eq_one_of_eq_one c (hcb w)]⟩

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
  refine ⟨MulExact.injective_comp_of_two_triangles hbc hde hef hfd h_bij, ?_⟩
  refine MulExact.surjective_comp (fun y ↦ (hca y).1 ?_) hbc.apply_apply_eq_one hfd h_bij.2
  exact (map_eq_one_iff (d.comp b) h_bij.1).mp (by simp [hab.apply_apply_eq_one])

end Function
