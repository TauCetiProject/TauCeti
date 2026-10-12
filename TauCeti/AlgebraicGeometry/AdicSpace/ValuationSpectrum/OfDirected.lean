/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic

/-!
# Points of the valuation spectrum of a directed union of images

Let `R` be a commutative ring and `fᵢ : Bᵢ → R` a family of ring homomorphisms whose images form
a directed family of subrings covering `R`, as for the canonical maps into a filtered colimit of
rings. A family of points `wᵢ ∈ Spv Bᵢ` that is compatible in the sense that

```text
fᵢ a = fⱼ a',  fᵢ b = fⱼ b',  a ≤_{wᵢ} b   ⟹   a' ≤_{wⱼ} b'
```

glues to a unique point `w ∈ Spv R` whose pullback along each `fᵢ` is `wᵢ`: to compare two
elements of `R`, lift both to a common `Bᵢ` and compare the lifts with `wᵢ`.

This is how a valuation on a stalk is assembled from valuations on the rings of sections over
the neighbourhoods of a point.

## Main definitions

* `TauCeti.ValuationSpectrum.ofDirected`: the glued point of `Spv R`.

## Main results

* `TauCeti.ValuationSpectrum.vle_ofDirected_iff`: two elements lifted to a common `Bᵢ` compare as
  their lifts do for `wᵢ`.
* `TauCeti.ValuationSpectrum.comap_ofDirected`: the glued point pulls back to `wᵢ` along `fᵢ`.
* `TauCeti.ValuationSpectrum.eq_ofDirected`: it is the only point of `Spv R` with this property.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {R : Type*} [CommRing R] {ι : Type*} {B : ι → Type*} [∀ i, CommRing (B i)]
  {f : ∀ i, B i →+* R}

/-- Three elements of a directed union of images lie in a common image. -/
private theorem exists_eq_eq_eq_of_directed (hdir : Directed (· ≤ ·) fun i ↦ (f i).range)
    (hcover : ∀ r, ∃ i, r ∈ (f i).range) (r₁ r₂ r₃ : R) :
    ∃ i, ∃ a₁ a₂ a₃ : B i, f i a₁ = r₁ ∧ f i a₂ = r₂ ∧ f i a₃ = r₃ := by
  obtain ⟨i₁, h₁⟩ := hcover r₁
  obtain ⟨i₂, h₂⟩ := hcover r₂
  obtain ⟨i₃, h₃⟩ := hcover r₃
  obtain ⟨j, hj₁, hj₂⟩ := hdir i₁ i₂
  obtain ⟨k, hkj, hk₃⟩ := hdir j i₃
  obtain ⟨a₁, ha₁⟩ := hkj (hj₁ h₁)
  obtain ⟨a₂, ha₂⟩ := hkj (hj₂ h₂)
  obtain ⟨a₃, ha₃⟩ := hk₃ h₃
  exact ⟨k, a₁, a₂, a₃, ha₁, ha₂, ha₃⟩

variable (f) (w : ∀ i, Spv (B i))

/-- The comparison relation of the glued point: `r ≤ s` when some `Bᵢ` contains lifts `a` of `r`
and `b` of `s` with `a ≤ b` for `wᵢ`. -/
private def OfDirectedRel (r s : R) : Prop :=
  ∃ i, ∃ a b : B i, f i a = r ∧ f i b = s ∧ (w i).toValuativeRel.vle a b

variable {w}
  (hcompat : ∀ i j (a b : B i) (a' b' : B j), f i a = f j a' → f i b = f j b' →
    (w i).toValuativeRel.vle a b → (w j).toValuativeRel.vle a' b')

include hcompat in
private theorem ofDirectedRel_iff {i : ι} {a b : B i} {r s : R} (ha : f i a = r)
    (hb : f i b = s) : OfDirectedRel f w r s ↔ (w i).toValuativeRel.vle a b :=
  ⟨fun ⟨j, a', b', ha', hb', h⟩ ↦ hcompat j i a' b' a b (ha'.trans ha.symm) (hb'.trans hb.symm) h,
    fun h ↦ ⟨i, a, b, ha, hb, h⟩⟩

variable (hdir : Directed (· ≤ ·) fun i ↦ (f i).range) (hcover : ∀ r, ∃ i, r ∈ (f i).range)

/-- **The point glued from a compatible family on a directed union of images.** Two elements of
`R` are compared by lifting them to a common `Bᵢ` and comparing the lifts with `wᵢ`; the
compatibility hypothesis makes the answer independent of the lifts. -/
noncomputable def ofDirected : Spv R :=
  ⟨{ vle := OfDirectedRel f w
     vle_total x y := by
       obtain ⟨i, a, b, -, rfl, rfl, -⟩ := exists_eq_eq_eq_of_directed hdir hcover x y 0
       exact ((w i).toValuativeRel.vle_total a b).imp
         (fun h ↦ ⟨i, a, b, rfl, rfl, h⟩) fun h ↦ ⟨i, b, a, rfl, rfl, h⟩
     vle_trans {z y x} hxy hyz := by
       obtain ⟨i, a, b, c, rfl, rfl, rfl⟩ := exists_eq_eq_eq_of_directed hdir hcover x y z
       rw [ofDirectedRel_iff f hcompat rfl rfl] at hxy hyz ⊢
       exact (w i).toValuativeRel.vle_trans hxy hyz
     vle_add {x y z} hxz hyz := by
       obtain ⟨i, a, b, c, rfl, rfl, rfl⟩ := exists_eq_eq_eq_of_directed hdir hcover x y z
       rw [ofDirectedRel_iff f hcompat rfl rfl] at hxz hyz
       rw [← map_add, ofDirectedRel_iff f hcompat rfl rfl]
       exact (w i).toValuativeRel.vle_add hxz hyz
     mul_vle_mul_left {x y} hxy z := by
       obtain ⟨i, a, b, c, rfl, rfl, rfl⟩ := exists_eq_eq_eq_of_directed hdir hcover x y z
       rw [ofDirectedRel_iff f hcompat rfl rfl] at hxy
       rw [← map_mul, ← map_mul, ofDirectedRel_iff f hcompat rfl rfl]
       exact (w i).toValuativeRel.mul_vle_mul_left hxy c
     vle_mul_cancel {x y z} hz hxy := by
       obtain ⟨i, a, b, c, rfl, rfl, rfl⟩ := exists_eq_eq_eq_of_directed hdir hcover x y z
       rw [← map_zero (f i), ofDirectedRel_iff f hcompat rfl rfl] at hz
       rw [← map_mul, ← map_mul, ofDirectedRel_iff f hcompat rfl rfl] at hxy
       rw [ofDirectedRel_iff f hcompat rfl rfl]
       exact (w i).toValuativeRel.vle_mul_cancel hz hxy
     not_vle_one_zero := by
       obtain ⟨i, -⟩ := hcover 0
       rw [← map_one (f i), ← map_zero (f i), ofDirectedRel_iff f hcompat rfl rfl]
       exact (w i).toValuativeRel.not_vle_one_zero
     vle_mul_comm {x y} := by
       obtain ⟨i, a, b, -, rfl, rfl, -⟩ := exists_eq_eq_eq_of_directed hdir hcover x y 0
       rw [← map_mul, ← map_mul, ofDirectedRel_iff f hcompat rfl rfl]
       exact (w i).toValuativeRel.vle_mul_comm }⟩

/-- **Comparison in the glued point** of two elements lifted to a common `Bᵢ` is comparison of
the lifts for `wᵢ`. -/
theorem vle_ofDirected_iff {i : ι} {a b : B i} {r s : R} (ha : f i a = r) (hb : f i b = s) :
    (ofDirected f hcompat hdir hcover).toValuativeRel.vle r s ↔
      (w i).toValuativeRel.vle a b :=
  ofDirectedRel_iff f hcompat ha hb

/-- **The glued point restricts to the given points**: its pullback along `fᵢ` is `wᵢ`. -/
@[simp]
theorem comap_ofDirected (i : ι) : comap (f i) (ofDirected f hcompat hdir hcover) = w i :=
  ext' fun a b ↦ by rw [comap_vle, vle_ofDirected_iff f hcompat hdir hcover rfl rfl]

/-- **Uniqueness of the glued point**: a point of `Spv R` whose pullback along every `fᵢ` is `wᵢ`
is `ofDirected`. -/
theorem eq_ofDirected {v : Spv R} (hv : ∀ i, comap (f i) v = w i) :
    v = ofDirected f hcompat hdir hcover :=
  ext' fun r s ↦ by
    obtain ⟨i, a, b, -, rfl, rfl, -⟩ := exists_eq_eq_eq_of_directed hdir hcover r s 0
    rw [vle_ofDirected_iff f hcompat hdir hcover rfl rfl, ← hv i, comap_vle]

end TauCeti.ValuationSpectrum
