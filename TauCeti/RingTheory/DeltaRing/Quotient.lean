/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.RingTheory.DeltaRing.Basic

/-!
# Quotients of δ-rings by δ-stable ideals

Let `A` be a `δ`-ring and `I` an ideal of `A`. If `δ` maps `I` into `I`, then `δ` descends to a
`δ`-structure on `A ⧸ I` making the quotient map a `δ`-map. Conversely, if some `δ`-structure on
`A ⧸ I` makes the quotient map a `δ`-map, then `δ` maps `I` into `I`, and that structure is the
descended one (Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.9).

## Main definitions

* `TauCeti.DeltaRing.quotient`: the `δ`-structure on `A ⧸ I` for a `δ`-stable ideal `I`.

## Main results

* `TauCeti.DeltaRing.isDeltaMap_quotient_mk`: the quotient map is a `δ`-map.
* `TauCeti.DeltaRing.eq_of_isDeltaMap_of_surjective`: a surjective ring homomorphism determines
  the `δ`-structure on its target making it a `δ`-map.
* `TauCeti.DeltaRing.existsUnique_isDeltaMap_quotient_mk_iff`: `δ` maps `I` into `I` if and only if
  there is a unique `δ`-structure on `A ⧸ I` making the quotient map a `δ`-map.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Lemma 2.9.
-/

public section

namespace TauCeti

namespace DeltaRing

variable {p : ℕ} {A : Type*} [CommRing A]

/-- A surjective ring homomorphism out of a `δ`-ring determines the `δ`-structure on its target
for which it is a `δ`-map. -/
theorem eq_of_isDeltaMap_of_surjective {B : Type*} [CommRing B] [DeltaRing p A]
    {f : A →+* B} (hf : Function.Surjective f) {δ₁ δ₂ : DeltaRing p B}
    (h₁ : @IsDeltaMap p A _ B _ _ δ₁ f) (h₂ : @IsDeltaMap p A _ B _ _ δ₂ f) : δ₁ = δ₂ := by
  ext y
  obtain ⟨x, rfl⟩ := hf y
  exact (@IsDeltaMap.map_delta p A _ B _ _ δ₁ f h₁ x).symm.trans
    (@IsDeltaMap.map_delta p A _ B _ _ δ₂ f h₂ x)

section Quotient

variable [DeltaRing p A] {I : Ideal A}

/-- If `δ` maps `I` into `I`, then `δ x - δ y ∈ I` whenever `x - y ∈ I`. -/
theorem delta_sub_delta_mem (hI : ∀ x ∈ I, delta p x ∈ I) {x y : A} (h : x - y ∈ I) :
    delta p x - delta p y ∈ I := by
  have hx : delta p x - delta p y = delta p (x - y) + addCorrection p (x - y) y := by
    have h' := delta_add (p := p) (x - y) y
    rw [sub_add_cancel] at h'
    rw [h']
    ring
  rw [hx]
  exact I.add_mem (hI _ h) (addCorrection_mem_of_mem_left y h)

variable (I) in
/-- The `δ`-structure on `A ⧸ I` induced by `δ`, for an ideal `I` with `δ I ⊆ I` (Bhatt and
Scholze, *Prisms and prismatic cohomology*, Lemma 2.9). -/
@[instance_reducible]
def quotient (hI : ∀ x ∈ I, delta p x ∈ I) : DeltaRing p (A ⧸ I) where
  delta := Quotient.lift (fun a ↦ Ideal.Quotient.mk I (delta p a)) fun _ _ h ↦
    Ideal.Quotient.eq.mpr <| delta_sub_delta_mem hI <| Ideal.Quotient.eq.mp <| Quotient.sound h
  delta_zero := by
    rw [← map_zero (Ideal.Quotient.mk I)]
    exact congrArg (Ideal.Quotient.mk I) delta_zero
  delta_one := by
    rw [← map_one (Ideal.Quotient.mk I)]
    exact (congrArg (Ideal.Quotient.mk I) delta_one).trans (map_zero _)
  delta_add x y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_add]
    exact (congrArg (Ideal.Quotient.mk I) (delta_add a b)).trans
      (by simp only [map_add, map_addCorrection]; rfl)
  delta_mul x y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul]
    exact (congrArg (Ideal.Quotient.mk I) (delta_mul a b)).trans
      (by simp only [map_add, map_mul, map_pow, map_natCast]; rfl)

/-- The `δ`-operation of `quotient I hI` on the class of `x` is the class of `δ x`. -/
theorem delta_quotient_mk (hI : ∀ x ∈ I, delta p x ∈ I) (x : A) :
    @delta p (A ⧸ I) _ (quotient I hI) (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I (delta p x) :=
  (rfl)

/-- The quotient map is a `δ`-map for `quotient I hI`. -/
theorem isDeltaMap_quotient_mk (hI : ∀ x ∈ I, delta p x ∈ I) :
    @IsDeltaMap p A _ (A ⧸ I) _ _ (quotient I hI) (Ideal.Quotient.mk I) :=
  letI := quotient I hI
  ⟨fun x => (delta_quotient_mk hI x).symm⟩

/-- If some `δ`-structure on `A ⧸ I` makes the quotient map a `δ`-map, then `δ` maps `I` into
`I`. -/
theorem delta_mem_of_isDeltaMap_quotient_mk {d : DeltaRing p (A ⧸ I)}
    (h : @IsDeltaMap p A _ (A ⧸ I) _ _ d (Ideal.Quotient.mk I)) {x : A} (hx : x ∈ I) :
    delta p x ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, h.map_delta, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    @delta_zero p _ _ d]

variable (I) in
/-- `δ` maps `I` into `I` if and only if there is a unique `δ`-structure on `A ⧸ I` for which the
quotient map is a `δ`-map (Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.9). -/
theorem existsUnique_isDeltaMap_quotient_mk_iff :
    (∀ x ∈ I, delta p x ∈ I) ↔
      ∃! d : DeltaRing p (A ⧸ I), @IsDeltaMap p A _ (A ⧸ I) _ _ d (Ideal.Quotient.mk I) := by
  refine ⟨fun hI => ⟨quotient I hI, isDeltaMap_quotient_mk hI, fun d hd =>
    eq_of_isDeltaMap_of_surjective Ideal.Quotient.mk_surjective hd (isDeltaMap_quotient_mk hI)⟩,
    fun ⟨d, hd, _⟩ _ hx => delta_mem_of_isDeltaMap_quotient_mk hd hx⟩

end Quotient

end DeltaRing

end TauCeti
