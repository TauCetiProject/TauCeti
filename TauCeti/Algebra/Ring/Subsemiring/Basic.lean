/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-! # Subsemirings containing the kernel and centralizer factorization

For a subsemiring containing the kernel of a ring homomorphism, membership can be
tested in its image, and pulling back that image recovers the original subsemiring.

Every ring homomorphism `g : R →+* K` from a commutative semiring into a possibly
non-commutative semiring factors through the center of the centralizer of `Set.range g`
(`RingHom.toCenterCentralizer`), preserving units of elements mapped to units in `K`
(`RingHom.isUnit_toCenterCentralizer`).
-/

public section

namespace Subsemiring

variable {A B : Type*} [Ring A] [Ring B]

/-- A subsemiring containing the kernel contains every lift of each image point. -/
theorem mem_map_iff_mem_of_ker_subset {f : A →+* B} {P : Subsemiring A}
    (hker : (RingHom.ker f : Set A) ⊆ P) {x : A} : f x ∈ P.map f ↔ x ∈ P := by
  rw [mem_map]
  refine ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  have hk : x - y ∈ P := hker (RingHom.mem_ker.mpr (by rw [map_sub, hxy, sub_self]))
  simpa using P.add_mem hy hk

/-- Pulling back the image recovers a subsemiring containing the kernel. -/
@[simp] theorem comap_map_eq_of_ker_subset {f : A →+* B} {P : Subsemiring A}
    (hker : (RingHom.ker f : Set A) ⊆ P) : (P.map f).comap f = P := by
  ext x
  exact mem_map_iff_mem_of_ker_subset hker

end Subsemiring

namespace RingHom

variable {R K : Type*} [CommSemiring R] [Semiring K]

/-- Factor a ring homomorphism `g : R →+* K` from a commutative semiring into a possibly
non-commutative semiring `K` through the center of the centralizer of `Set.range g`. -/
def toCenterCentralizer (g : R →+* K) :
    R →+* Subsemiring.center (Subsemiring.centralizer (Set.range g)) :=
  (g.codRestrict (Subsemiring.centralizer (Set.range g)) fun a ↦
    Subsemiring.mem_centralizer_iff.mpr fun _ ⟨b, hb⟩ ↦ by
      rw [← hb, ← map_mul, mul_comm b a, map_mul]).codRestrict
    (Subsemiring.center (Subsemiring.centralizer (Set.range g))) fun a ↦
      Subsemiring.mem_center_iff.mpr fun ⟨_, hc⟩ ↦
        Subtype.ext (Subsemiring.mem_centralizer_iff.mp hc (g a) ⟨a, rfl⟩).symm

/-- Coercing `g.toCenterCentralizer a` back to `K` gives `g a`. -/
@[simp]
theorem toCenterCentralizer_apply (g : R →+* K) (a : R) :
    (((g.toCenterCentralizer a : Subsemiring.center (Subsemiring.centralizer (Set.range g))) :
      Subsemiring.centralizer (Set.range g)) : K) = g a := by
  rw [toCenterCentralizer, codRestrict_apply, codRestrict_apply]

/-- If `g x` is a unit in `K`, then `g.toCenterCentralizer x` is a unit in the center of the
centralizer of `Set.range g`. -/
theorem isUnit_toCenterCentralizer (g : R →+* K) {x : R} (hg : IsUnit (g x)) :
    IsUnit (g.toCenterCentralizer x) := by
  have hinv_mem : ((hg.unit⁻¹ : Kˣ) : K) ∈ Subsemiring.centralizer (Set.range g) :=
    Subsemiring.mem_centralizer_iff.mpr fun _ ⟨b, hb⟩ ↦ by
      have hcomm : Commute (g b) (hg.unit : K) := by
        rw [commute_iff_eq, IsUnit.unit_spec, ← map_mul, mul_comm b x, map_mul]
      rw [← hb]
      exact hcomm.units_inv_right.eq
  refine ⟨⟨g.toCenterCentralizer x, ⟨⟨((hg.unit⁻¹ : Kˣ) : K), hinv_mem⟩,
      Subsemiring.mem_center_iff.mpr fun ⟨c, hc⟩ ↦ Subtype.ext <| by
        have hcomm : Commute (hg.unit : K) c := by
          rw [commute_iff_eq, IsUnit.unit_spec]
          exact Subsemiring.mem_centralizer_iff.mp hc (g x) ⟨x, rfl⟩
        exact hcomm.units_inv_left.eq.symm⟩,
    Subtype.ext (Subtype.ext <| by simp [hg.mul_val_inv]),
    Subtype.ext (Subtype.ext <| by simp [hg.val_inv_mul])⟩, rfl⟩

end RingHom
