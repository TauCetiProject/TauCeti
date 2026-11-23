/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.DeltaRing.isDeltaMap_quotient_lift`: a `δ`-map killing `I` induces a `δ`-map on
  `A ⧸ I`.
* `TauCeti.DeltaRing.existsUnique_isDeltaMap_quotient_mk_iff`: there is a unique `δ`-structure on
  `A ⧸ I` making the quotient map a `δ`-map if and only if `δ` maps `I` into `I`. Uniqueness is
  `TauCeti.DeltaRing.eq_of_isDeltaMap_of_surjective`: at most one `δ`-structure on the target of a
  surjective ring homomorphism makes it a `δ`-map.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Lemma 2.9.
-/

public section

namespace TauCeti

namespace DeltaRing

variable {p : ℕ} {A : Type*} [CommRing A]

section Quotient

variable [DeltaRing p A] {I : Ideal A}

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
@[simp]
theorem delta_quotient_mk (hI : ∀ x ∈ I, delta p x ∈ I) (x : A) :
    @delta p (A ⧸ I) _ (quotient I hI) (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I (delta p x) :=
  (rfl)

/-- The quotient map is a `δ`-map for `quotient I hI`. -/
theorem isDeltaMap_quotient_mk (hI : ∀ x ∈ I, delta p x ∈ I) :
    @IsDeltaMap p A _ (A ⧸ I) _ _ (quotient I hI) (Ideal.Quotient.mk I) :=
  letI := quotient I hI
  ⟨fun x => (delta_quotient_mk hI x).symm⟩

/-- The Frobenius of `quotient I hI` on the class of `x` is the class of `φ x`. -/
@[simp]
theorem frobenius_quotient_mk [Fact p.Prime] (hI : ∀ x ∈ I, delta p x ∈ I) (x : A) :
    @frobenius p (A ⧸ I) _ _ (quotient I hI) (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I (frobenius p A x) := by
  let := quotient I hI
  rw [frobenius_apply, frobenius_apply, delta_quotient_mk, map_add, map_mul, map_pow,
    map_natCast]

/-- A `δ`-map `f : A →+* B` vanishing on `I` induces a `δ`-map `A ⧸ I →+* B` for
`quotient I hI`. -/
theorem isDeltaMap_quotient_lift {B : Type*} [CommRing B] [DeltaRing p B]
    (hI : ∀ x ∈ I, delta p x ∈ I) {f : A →+* B} (hf : IsDeltaMap p f) (hfI : ∀ a ∈ I, f a = 0) :
    @IsDeltaMap p (A ⧸ I) _ B _ (quotient I hI) _ (Ideal.Quotient.lift I f hfI) := by
  let := quotient I hI
  refine ⟨fun x => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [delta_quotient_mk, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, hf.map_delta]

/-- If some `δ`-structure on `A ⧸ I` makes the quotient map a `δ`-map, then `δ` maps `I` into
`I`. -/
theorem delta_mem_of_isDeltaMap_quotient_mk {d : DeltaRing p (A ⧸ I)}
    (h : @IsDeltaMap p A _ (A ⧸ I) _ _ d (Ideal.Quotient.mk I)) {x : A} (hx : x ∈ I) :
    delta p x ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, h.map_delta, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    @delta_zero p _ _ d]

variable (I) in
/-- There is a unique `δ`-structure on `A ⧸ I` for which the quotient map is a `δ`-map if and only
if `δ` maps `I` into `I` (Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.9). -/
theorem existsUnique_isDeltaMap_quotient_mk_iff :
    (∃! d : DeltaRing p (A ⧸ I), @IsDeltaMap p A _ (A ⧸ I) _ _ d (Ideal.Quotient.mk I)) ↔
      ∀ x ∈ I, delta p x ∈ I := by
  refine ⟨fun ⟨d, hd, _⟩ _ hx => delta_mem_of_isDeltaMap_quotient_mk hd hx, fun hI =>
    ⟨quotient I hI, isDeltaMap_quotient_mk hI, fun d hd =>
      eq_of_isDeltaMap_of_surjective Ideal.Quotient.mk_surjective hd (isDeltaMap_quotient_mk hI)⟩⟩

end Quotient

end DeltaRing

end TauCeti
