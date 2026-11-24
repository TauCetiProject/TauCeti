/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Idempotent
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Primitive idempotents in adically complete algebras

Let `R` be a commutative ring, `I` an ideal of `R`, `S` an `R`-algebra, possibly noncommutative,
and `f : S →+* T` a ring homomorphism, such as the reduction `O[G] → k[G]` of the group algebra of
a finite group over a complete discrete valuation ring `O` with residue field `k`. If `S` is
`I`-adically Hausdorff and the kernel of `f` lies in `I • S`, an idempotent `e` of `S` is primitive
when `f e` is. If `S` is `I`-adically complete and `f` is surjective with kernel exactly `I • S`,
the converse holds too, so `e` is primitive exactly when `f e` is, and, together with
`IsAdicComplete.exists_isIdempotentElem_eq`, every primitive idempotent of `T` is the image of a
primitive idempotent of `S`.

A decomposition of `e` maps to a decomposition of `f e`, and a summand mapping to `0` is an
idempotent in `I • S`, hence `0`, because an idempotent lies in every `I ^ n • S`
(`IsHausdorff.eq_zero_of_isIdempotentElem_of_mem`). Conversely, an idempotent `ε` of the corner
ring of `f e` is the image of some `x`, hence of `e x e`, which is idempotent modulo `I • S` and
lies in the corner ring `eSe`; its Newton lift stays in `eSe`
(`IsAdicComplete.exists_isIdempotentElem_sub_mem_of_mul_eq`), so primitivity of `e` makes the lift,
and with it `ε`, equal to `0` or to `e`.

## Main results

* `TauCeti.isPrimitiveIdempotent_of_map_of_isHausdorff`: for `S` `I`-adically Hausdorff and the
  kernel of `f` contained in `I • S`, an idempotent whose image is primitive is primitive.
* `TauCeti.IsPrimitiveIdempotent.map_of_isAdicComplete`: for `S` `I`-adically complete and `f`
  surjective with kernel `I • S`, the image of a primitive idempotent is primitive.
* `TauCeti.isPrimitiveIdempotent_map_iff`: under the same hypotheses, an idempotent of `S` is
  primitive exactly when its image in `T` is.
* `TauCeti.exists_isPrimitiveIdempotent_eq`: primitive idempotents lift along `f` under the same
  hypotheses.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 9.4.3.
-/

public section

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (I : Ideal R)

namespace TauCeti

variable {I} {T : Type*} [Ring T] (f : S →+* T)

/-- **A primitive image comes from a primitive idempotent.** If the kernel of `f : S →+* T` lies
in `I • S` and `S` is `I`-adically Hausdorff, an idempotent of `S` whose image is primitive is
primitive. -/
theorem isPrimitiveIdempotent_of_map_of_isHausdorff [IsHausdorff I S]
    (hf : ∀ x, f x = 0 → x ∈ I • (⊤ : Submodule R S)) {e : S} (he : IsIdempotentElem e)
    (h : IsPrimitiveIdempotent (f e)) : IsPrimitiveIdempotent e :=
  IsPrimitiveIdempotent.of_map_of_forall f he
    (fun _ hx h0 ↦ IsHausdorff.eq_zero_of_isIdempotentElem_of_mem I hx (hf _ h0)) h

/-- **Primitivity survives reduction.** If `S` is `I`-adically complete and `f : S →+* T` is
surjective with kernel `I • S`, the image of a primitive idempotent is primitive. -/
theorem IsPrimitiveIdempotent.map_of_isAdicComplete [IsAdicComplete I S]
    (hf : ∀ x, f x = 0 ↔ x ∈ I • (⊤ : Submodule R S)) (hsurj : Function.Surjective f) {e : S}
    (he : IsPrimitiveIdempotent e) : IsPrimitiveIdempotent (f e) := by
  have hee := he.isIdempotentElem.eq
  refine isPrimitiveIdempotent_of_eq_zero_or_eq (he.isIdempotentElem.map f)
    (fun h0 ↦ he.ne_zero (IsHausdorff.eq_zero_of_isIdempotentElem_of_mem I he.isIdempotentElem
      ((hf _).mp h0))) fun ε hε hfε hεf ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj ε
  -- `e * x * e` lies in the corner ring `eSe`, maps to `f x` and is idempotent modulo `I • S`.
  have hfx : f (e * x * e) = f x := by rw [map_mul, map_mul, hfε, hεf]
  obtain ⟨e₁, he₁, hsub, hee₁, he₁e⟩ := IsAdicComplete.exists_isIdempotentElem_sub_mem_of_mul_eq
    I ((hf _).mp (by rw [map_sub, map_mul, hfx, hε.eq, sub_self])) (c := e) (d := e)
    (by rw [← mul_assoc, ← mul_assoc, hee]) (by rw [mul_assoc, hee])
  have hfe₁ : f e₁ = f x := by rw [← hfx, ← sub_eq_zero, ← map_sub, (hf _).mpr hsub]
  rw [← hfe₁]
  exact (he.eq_zero_or_eq he₁ hee₁ he₁e).imp (fun h ↦ by rw [h, map_zero]) fun h ↦ by rw [h]

/-- **An idempotent is primitive exactly when its reduction is.** For an `I`-adically complete
`R`-algebra `S` and a surjective ring homomorphism `f : S →+* T` with kernel `I • S`, such as the
reduction `O[G] → k[G]`, an idempotent `e` of `S` is primitive if and only if `f e` is. -/
theorem isPrimitiveIdempotent_map_iff [IsAdicComplete I S]
    (hf : ∀ x, f x = 0 ↔ x ∈ I • (⊤ : Submodule R S)) (hsurj : Function.Surjective f) {e : S}
    (he : IsIdempotentElem e) : IsPrimitiveIdempotent (f e) ↔ IsPrimitiveIdempotent e :=
  ⟨isPrimitiveIdempotent_of_map_of_isHausdorff f (fun x ↦ (hf x).mp) he,
    IsPrimitiveIdempotent.map_of_isAdicComplete f hf hsurj⟩

/-- **Primitive idempotents lift.** For an `I`-adically complete `R`-algebra `S` and a surjective
ring homomorphism `f : S →+* T` with kernel `I • S`, every primitive idempotent of `T` is the image
of a primitive idempotent of `S`. -/
theorem exists_isPrimitiveIdempotent_eq [IsAdicComplete I S]
    (hf : ∀ x, f x = 0 ↔ x ∈ I • (⊤ : Submodule R S)) (hsurj : Function.Surjective f) {ε : T}
    (hε : IsPrimitiveIdempotent ε) : ∃ e : S, IsPrimitiveIdempotent e ∧ f e = ε := by
  obtain ⟨e, he, rfl⟩ :=
    IsAdicComplete.exists_isIdempotentElem_eq I f hf (hsurj ε) hε.isIdempotentElem
  exact ⟨e, (isPrimitiveIdempotent_map_iff f hf hsurj he).mp hε, rfl⟩

end TauCeti
