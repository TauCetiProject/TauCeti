/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Ring.Ordering.Extension
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.SimpleRing.Basic

/-! # Restriction and transport of ring preorderings

A preordering `P` of a commutative ring `B` restricts along any ring homomorphism `f : A →+* B`
to the preordering `P.comap f` of `A`, consisting of the elements whose image lies in `P`.
Conversely, a preordering `P` of `A` is transported along a surjective ring homomorphism
`f : A →+* B` whose kernel lies in `P` to its image `P.map hf hker`. Both operations preserve
orderings, and they are mutually inverse between preorderings of `B` and preorderings of `A`
containing the kernel.

For fields, `comap` is the restriction of orders along field embeddings: if `P` is an
ordering of `L` and `f : K →+* L`, then `f` is strictly monotone for the orders of
`P.comap f` and `P`, and among orders of `K` compatible with addition, that of `P.comap f` is
the only one with this property. Transport along a field isomorphism is `map` along the
underlying ring equivalence, whose kernel is trivial.

## Main declarations

* `RingPreordering.comap`: the restriction of a preordering along a ring homomorphism.
* `RingPreordering.map`: the image of a preordering along a surjective ring homomorphism whose
  kernel it contains.
* `RingPreordering.comap_map_eq`, `RingPreordering.map_comap_eq`: the two operations are inverse.
* `RingPreordering.strictMono_iff_nonneg_iff_mem_comap`: an order of `K` makes a field
  embedding `f : K →+* L` strictly monotone for the order of an ordering `P` of `L` exactly
  when its nonnegative elements are those of `P.comap f`.
* `RingPreordering.strictMono_comap`: `f` is strictly monotone for the orders of `P.comap f`
  and `P`.

## References

* T. Y. Lam, *An introduction to real algebra*, Rocky Mountain J. Math. 14 (1984), §1.
-/

public section

namespace RingPreordering

section CommRing

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- The restriction of a preordering `P` of `B` along a ring homomorphism `f : A →+* B`: the
elements of `A` whose image lies in `P`. -/
def comap (f : A →+* B) (P : RingPreordering B) : RingPreordering A :=
  mk' (f ⁻¹' P)
    (fun hx hy ↦ by simpa only [Set.mem_preimage, SetLike.mem_coe, map_add] using add_mem hx hy)
    (fun hx hy ↦ by simpa only [Set.mem_preimage, SetLike.mem_coe, map_mul] using mul_mem hx hy)
    (fun x ↦ by simpa only [Set.mem_preimage, SetLike.mem_coe, map_mul] using P.mul_self_mem (f x))
    (by simpa only [Set.mem_preimage, SetLike.mem_coe, map_neg, map_one] using P.neg_one_notMem)

@[simp] theorem mem_comap {f : A →+* B} {P : RingPreordering B} {x : A} :
    x ∈ P.comap f ↔ f x ∈ P := (Iff.rfl)

@[simp, norm_cast] theorem coe_comap (f : A →+* B) (P : RingPreordering B) :
    (P.comap f : Set A) = f ⁻¹' P := (rfl)

@[simp] theorem comap_id (P : RingPreordering A) : P.comap (RingHom.id A) = P := (rfl)

theorem comap_comap (P : RingPreordering C) (g : B →+* C) (f : A →+* B) :
    (P.comap g).comap f = P.comap (g.comp f) := (rfl)

@[gcongr] theorem comap_mono (f : A →+* B) {P Q : RingPreordering B} (h : P ≤ Q) :
    P.comap f ≤ Q.comap f := fun _ hx ↦ h hx

theorem supportAddSubgroup_comap (f : A →+* B) (P : RingPreordering B) :
    (P.comap f).supportAddSubgroup = P.supportAddSubgroup.comap f.toAddMonoidHom := by
  ext x
  simp [mem_supportAddSubgroup]

instance (f : A →+* B) (P : RingPreordering B) [P.HasIdealSupport] :
    (P.comap f).HasIdealSupport := by
  rw [hasIdealSupport_iff]
  intro x a ha hna
  simpa using (hasIdealSupport_iff.mp ‹_›) (f x) (f a) ha (by simpa using hna)

@[simp] theorem support_comap (f : A →+* B) (P : RingPreordering B) [P.HasIdealSupport] :
    (P.comap f).support = Ideal.comap f P.support := by
  ext x
  simp [mem_support]

/-- The restriction of an ordering is an ordering. -/
instance (f : A →+* B) (P : RingPreordering B) [P.IsOrdering] : (P.comap f).IsOrdering :=
  isOrdering_iff.mpr fun a b h ↦ by
    simpa using (isOrdering_iff.mp ‹_›) (f a) (f b) (by simpa using h)

/-- The image of a preordering `P` of `A` along a surjective ring homomorphism `f : A →+* B`
whose kernel is contained in `P`. -/
def map {f : A →+* B} (hf : Function.Surjective f) {P : RingPreordering A}
    (hker : (RingHom.ker f : Set A) ⊆ P) : RingPreordering B :=
  mk' (f '' P)
    (by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, add_mem hx hy, map_add f x y⟩)
    (by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x * y, mul_mem hx hy, map_mul f x y⟩)
    (fun y ↦ by
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨x * x, P.mul_self_mem x, map_mul f x x⟩)
    (by
      rintro ⟨x, hx, hfx⟩
      -- `-(x + 1)` lies in the kernel, hence in `P`, and adding `x` gives `-1 ∈ P`.
      have hk : -(x + 1) ∈ P := hker <| RingHom.mem_ker.mpr <| by simp [hfx]
      exact P.neg_one_notMem (by simpa using add_mem hx hk))

section map

variable {f : A →+* B} (hf : Function.Surjective f) {P : RingPreordering A}
  (hker : (RingHom.ker f : Set A) ⊆ P)

theorem mem_map {y : B} : y ∈ P.map hf hker ↔ ∃ x ∈ P, f x = y := (Iff.rfl)

@[simp, norm_cast] theorem coe_map : (P.map hf hker : Set B) = f '' P := (rfl)

/-- An element lies in `P` exactly when its image lies in the image of `P`, since the kernel
of `f` is contained in `P`. -/
@[simp] theorem mem_map_iff_mem {x : A} : f x ∈ P.map hf hker ↔ x ∈ P := by
  rw [mem_map]
  refine ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  have hk : x - y ∈ P := hker (RingHom.mem_ker.mpr (by rw [map_sub, hxy, sub_self]))
  simpa using add_mem hy hk

/-- Restricting the image of `P` recovers `P`. -/
@[simp] theorem comap_map_eq : (P.map hf hker).comap f = P := by
  refine SetLike.ext fun x ↦ ?_
  rw [mem_comap, mem_map_iff_mem]

/-- The kernel of a ring homomorphism lies in the restriction of every preordering. -/
theorem ker_subset_comap (f : A →+* B) (Q : RingPreordering B) :
    (RingHom.ker f : Set A) ⊆ Q.comap f := fun x hx ↦ by
  simp [RingHom.mem_ker.mp hx]

/-- Every preordering of `B` is the image of its restriction along a surjection. -/
@[simp] theorem map_comap_eq (Q : RingPreordering B) :
    (Q.comap f).map hf (ker_subset_comap f Q) = Q := by
  refine SetLike.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hf y
  rw [mem_map_iff_mem, mem_comap]

/-- The image of an ordering is an ordering. -/
instance [P.IsOrdering] : (P.map hf hker).IsOrdering :=
  isOrdering_iff.mpr fun a b h ↦ by
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    rw [← map_mul, ← map_neg, mem_map_iff_mem] at h
    simpa using (isOrdering_iff.mp ‹_›) x y h

end map

end CommRing

section Field

variable {K L : Type*} [Field K] [Field L]

/-- **Restriction of orders along field embeddings.** Let `P` be an ordering of `L`, and order
`L` by it. An order on `K` compatible with addition makes a ring homomorphism `f : K →+* L`
strictly monotone exactly when its nonnegative elements are those of `P.comap f`. In particular
such an order is determined by `f` and `P`. -/
theorem strictMono_iff_nonneg_iff_mem_comap [LinearOrder K] [IsOrderedAddMonoid K]
    (f : K →+* L) (P : RingPreordering L) [P.IsOrdering] :
    letI := linearOrder P
    StrictMono f ↔ ∀ x, 0 ≤ x ↔ x ∈ P.comap f := by
  let := linearOrder P
  have := isStrictOrderedRing P
  refine ⟨fun hf x ↦ ?_, fun h ↦ ?_⟩
  · rw [mem_comap, ← nonneg_iff P, ← map_zero f]
    exact hf.le_iff_le.symm
  · refine ((monotone_iff_map_nonneg f).mpr fun x hx ↦ ?_).strictMono_of_injective f.injective
    exact (nonneg_iff P _).mpr ((h x).mp hx)

/-- The order of the restricted ordering `P.comap f` makes `f` strictly monotone. -/
theorem strictMono_comap (f : K →+* L) (P : RingPreordering L) [P.IsOrdering] :
    letI := linearOrder (P.comap f)
    letI := linearOrder P
    StrictMono f := by
  let := linearOrder (P.comap f)
  have := isStrictOrderedRing (P.comap f)
  exact (strictMono_iff_nonneg_iff_mem_comap f P).mpr (nonneg_iff (P.comap f))

end Field

end RingPreordering
