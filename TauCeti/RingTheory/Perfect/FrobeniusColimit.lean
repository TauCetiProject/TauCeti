/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.FieldTheory.IsPerfectClosure
public import TauCeti.Algebra.Category.Ring.FilteredColimits
public import TauCeti.Algebra.CharP.Frobenius.PowRingHom

/-!
# The colimit of a ring along its `p`-th power map

Let `p` be a prime and `R` a commutative ring in which `p` vanishes. The *Frobenius tower* of `R`
is the sequence `R → R → R → ⋯` whose transition maps are the `p`-th power map `x ↦ x ^ p`
(`TauCeti.powRingHom`). Its colimit is a perfect ring, and the colimit maps from `R` are
`p`-radical: the colimit is the perfection of `R`, with the `n`-th copy of `R` playing the role of
`R ^ (1 / p ^ n)`.

This is the construction behind Mathlib's `PerfectClosure`, which however asks for `CharP R p`
and so excludes the zero ring. The colimit here only needs `p = 0` in `R` and is functorial in
`R`, which is what the rings of sections of a scheme over `𝔽_p`, among them the zero ring of
sections over the empty open, require.

## Main definitions

* `CommRingCat.frobeniusTower R p h`: the sequence `R → R → ⋯` along `x ↦ x ^ p`.
* `CommRingCat.frobeniusTowerMap f hR hS`: the map of Frobenius towers induced by a ring map.

## Main results

* `CommRingCat.frobeniusTower_map_apply`: the transition map from stage `m` to stage `n` is
  `x ↦ x ^ p ^ (n - m)`.
* `CommRingCat.isPRadical_ι_app_of_isColimit`: every colimit map of the Frobenius tower is
  `p`-radical.
* `CommRingCat.perfectRing_of_isColimit`: the colimit of the Frobenius tower is a perfect ring.
-/

public section

open CategoryTheory Limits

universe u

namespace CommRingCat

variable (R : CommRingCat.{u}) (p : ℕ) [hp : Fact p.Prime] (h : (p : R) = 0)

-- The tower is reducible, so that each of its stages is `R` for unification, including in the
-- modules gluing the perfections of the rings of sections of a scheme.
/-- The *Frobenius tower* `R → R → R → ⋯` of a ring `R` in which the prime `p` vanishes: the
transition map from stage `m` to stage `n ≥ m` is the `p ^ (n - m)`-th power map, the
`(n - m)`-th iterate of `x ↦ x ^ p`. -/
noncomputable abbrev frobeniusTower : ℕ ⥤ CommRingCat.{u} where
  obj _ := R
  map {m n} _ := ofHom (TauCeti.powRingHom R p h ^ (n - m))
  map_id m := by
    rw [Nat.sub_self, pow_zero]
    rfl
  map_comp {l m n} f g := by
    rw [← ofHom_comp, ← RingHom.mul_def, ← pow_add, Nat.sub_add_sub_cancel (leOfHom g) (leOfHom f)]

variable {R p h}

/-- The transition map of the Frobenius tower from stage `m` to stage `n ≥ m` is the
`p ^ (n - m)`-th power map. -/
theorem frobeniusTower_map_apply {m n : ℕ} (f : m ⟶ n) (x : R) :
    (frobeniusTower R p h).map f x = x ^ p ^ (n - m) :=
  (congrFun (RingHom.coe_pow _ (n - m)) x).trans <| by
    rw [show ⇑(TauCeti.powRingHom R p h) = (· ^ p) from funext (TauCeti.powRingHom_apply h),
      pow_iterate]

variable {S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (hR : (p : R) = 0) (hS : (p : S) = 0)
  (hT : (p : T) = 0)

/-- The map of Frobenius towers induced by a ring map `f : R ⟶ S`: it is `f` at every stage, which
commutes with the `p`-th power maps. -/
noncomputable def frobeniusTowerMap : frobeniusTower R p hR ⟶ frobeniusTower S p hS where
  app _ := f
  naturality m n i := by
    ext x
    exact (congrArg f.hom (frobeniusTower_map_apply i x)).trans
      ((map_pow f.hom x _).trans (frobeniusTower_map_apply i (f.hom x)).symm)

/-- The map of Frobenius towers induced by `f` is `f` at every stage. -/
@[simp]
theorem frobeniusTowerMap_app (n : ℕ) : (frobeniusTowerMap f hR hS).app n = f := (rfl)

@[simp]
theorem frobeniusTowerMap_id : frobeniusTowerMap (𝟙 R) hR hR = 𝟙 (frobeniusTower R p hR) := (rfl)

@[simp, reassoc]
theorem frobeniusTowerMap_comp :
    frobeniusTowerMap (f ≫ g) hR hT = frobeniusTowerMap f hR hS ≫ frobeniusTowerMap g hS hT :=
  (rfl)

variable {c : Cocone (frobeniusTower R p h)} (hc : IsColimit c)

/-- An element at stage `n` of the colimit of the Frobenius tower is the `p ^ k`-th power of the
same element at stage `n + k`. -/
private theorem ι_app_pow (n k : ℕ) (x : R) :
    c.ι.app (n + k) x ^ p ^ k = c.ι.app n x := by
  have hw := ConcreteCategory.congr_hom (c.w (homOfLE (Nat.le_add_right n k))) x
  rwa [CommRingCat.comp_apply, frobeniusTower_map_apply, Nat.add_sub_cancel_left, map_pow] at hw

include hc

/-- **The colimit maps of the Frobenius tower are `p`-radical.** -/
theorem isPRadical_ι_app_of_isColimit (n : ℕ) : IsPRadical (c.ι.app n).hom p where
  pow_mem' x := by
    obtain ⟨m, y, rfl⟩ := Concrete.isColimit_exists_rep _ hc x
    -- `y` at stage `m` is `y ^ p ^ n` at stage `m + n`, whose `p ^ m`-th power is at stage `n`.
    refine ⟨m, y ^ p ^ n, (ι_app_pow (c := c) n m _).symm.trans ?_⟩
    rw [← ι_app_pow (c := c) m n y, map_pow, Nat.add_comm m n]
  ker_le' x hx := by
    rw [RingHom.mem_ker] at hx
    obtain ⟨k, f, g, hk⟩ := (Concrete.isColimit_rep_eq_iff_exists _ hc (i := n) (j := n) x 0).1
      (hx.trans (map_zero _).symm)
    rw [frobeniusTower_map_apply, map_zero] at hk
    exact mem_pNilradical.2 ⟨_, hk⟩

/-- **The colimit of the Frobenius tower is a perfect ring.** -/
theorem perfectRing_of_isColimit : PerfectRing c.pt p := by
  refine ⟨⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩⟩
  · obtain ⟨m, x, rfl⟩ := Concrete.isColimit_exists_rep _ hc x
    obtain ⟨n, y, rfl⟩ := Concrete.isColimit_exists_rep _ hc y
    -- `x ^ p` and `y ^ p` agree at some stage `k`, so `x` and `y` agree at stage `k + 1`.
    replace hxy : c.ι.app m (x ^ p) = c.ι.app n (y ^ p) := by simpa only [map_pow] using hxy
    obtain ⟨k, f, g, hk⟩ := (Concrete.isColimit_rep_eq_iff_exists _ hc _ _).1 hxy
    have hm := leOfHom f
    have hn := leOfHom g
    refine (Concrete.isColimit_rep_eq_iff_exists _ hc _ _).2
      ⟨k + 1, homOfLE (hm.trans k.le_succ), homOfLE (hn.trans k.le_succ), ?_⟩
    rw [frobeniusTower_map_apply, frobeniusTower_map_apply, ← pow_mul, ← pow_mul, ← pow_succ',
      ← pow_succ'] at hk
    rwa [frobeniusTower_map_apply, frobeniusTower_map_apply, Nat.succ_sub hm, Nat.succ_sub hn]
  · obtain ⟨n, x, rfl⟩ := Concrete.isColimit_exists_rep _ hc x
    exact ⟨c.ι.app (n + 1) x, by simpa using ι_app_pow (c := c) n 1 x⟩

end CommRingCat
