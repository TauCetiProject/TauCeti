/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Big.NonUnital
public import TauCeti.RingTheory.WittVector.Big.Verschiebung

/-!
# The big Witt Verschiebung over nonunital rings

For a nonunital commutative ring `R`, the Verschiebung
`V_n : W_{S/n}(R) → W_S(R)` of `NonUnitalBigWittVector` is the restriction of the Verschiebung of
the big Witt ring of the integral unitization `ℤ ⊕ R`. The Verschiebung commutes with the
coefficient map to `W_S(ℤ)`, so it preserves the augmentation kernel. On coordinates it is again
`(V_n x)_{n e} = x_e`, with zeros at the indices not divisible by `n`, and on ghost components
`w_{n k}(V_n x) = n • w_k(x)`.

## Main definitions

* `TauCeti.NonUnitalBigWittVector.verschiebung n`: the additive Verschiebung
  `W_{S/n}(R) →+ W_S(R)` on nonunital coefficients.

## Main results

* `TauCeti.NonUnitalBigWittVector.coordinates_verschiebung`: the coordinates of `V_n x`.
* `TauCeti.NonUnitalBigWittVector.ghostComponent_verschiebung_mul` and
  `TauCeti.NonUnitalBigWittVector.ghostComponent_verschiebung_of_not_dvd`: its ghost components.
* `TauCeti.NonUnitalBigWittVector.verschiebung_map`,
  `TauCeti.NonUnitalBigWittVector.restrict_verschiebung`,
  `TauCeti.NonUnitalBigWittVector.verschiebung_one` and
  `TauCeti.NonUnitalBigWittVector.verschiebung_verschiebung`: naturality, restriction,
  `V_1 = id` and `V_a V_b = V_{a b}`.
* `TauCeti.NonUnitalBigWittVector.unitalEquiv_verschiebung`: agreement with the Verschiebung of
  `BigWittVector` on unital rings.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Acta Math. 214 (2015), §1, Lemma 1.5.
* F. Wagner, *q-Witt vectors and q-Hodge complexes*, §2.6,
  <https://arxiv.org/abs/2410.23078v5>.
-/

public section

noncomputable section

namespace TauCeti.NonUnitalBigWittVector

open BigWitt

variable {S T : TruncationSet} {R A : Type*} [NonUnitalCommRing R] [NonUnitalCommRing A]

/-- The coordinates of the Verschiebung, before additivity is available. -/
private def verschiebungFun (n : ℕ) (x : NonUnitalBigWittVector (S / n) R) :
    NonUnitalBigWittVector S R :=
  mk fun m ↦ if n ∣ (m : ℕ) then coordinates x (m / n) else 0

private theorem toBigWitt_verschiebungFun (n : ℕ) (x : NonUnitalBigWittVector (S / n) R) :
    toBigWitt (verschiebungFun n x) =
      BigWittVector.verschiebung (R := Unitization ℤ R) n (toBigWitt x) := by
  refine BigWittVector.ext fun m ↦ ?_
  by_cases hm : m ∈ S
  · rw [coeff_toBigWitt _ ⟨m, hm⟩, verschiebungFun, coeff_mk,
      BigWittVector.coeff_verschiebung, coordinates_toBigWitt]
    split_ifs <;> simp
  · rw [BigWittVector.coeff_eq_zero_of_notMem _ m hm, BigWittVector.coeff_eq_zero_of_notMem _ m hm]

/-- The big Witt Verschiebung `V_n : W_{S/n}(R) →+ W_S(R)` over a nonunital commutative ring.
Its coordinates are `(V_n x)_{n e} = x_e`, with zeros at the indices not divisible by `n`; it is
the restriction of the Verschiebung of the big Witt ring of the integral unitization
(`toBigWitt_verschiebung`). -/
def verschiebung (n : ℕ) : NonUnitalBigWittVector (S / n) R →+ NonUnitalBigWittVector S R where
  toFun := verschiebungFun n
  map_zero' := toBigWitt_injective (by rw [toBigWitt_verschiebungFun, map_zero, map_zero, map_zero])
  map_add' x y := toBigWitt_injective (by
    rw [map_add, toBigWitt_verschiebungFun, toBigWitt_verschiebungFun, toBigWitt_verschiebungFun,
      map_add, map_add])

/-- The kernel inclusion carries the Verschiebung to the Verschiebung of the unitization. -/
@[simp]
theorem toBigWitt_verschiebung (n : ℕ) (x : NonUnitalBigWittVector (S / n) R) :
    toBigWitt (verschiebung n x) =
      BigWittVector.verschiebung (R := Unitization ℤ R) n (toBigWitt x) :=
  toBigWitt_verschiebungFun n x

/-- The coordinates of the Verschiebung, extended by zero outside the truncation set. -/
theorem coordinates_verschiebung (n : ℕ) (x : NonUnitalBigWittVector (S / n) R) (m : ℕ) :
    coordinates (verschiebung n x) m = if n ∣ m then coordinates x (m / n) else 0 := by
  apply Unitization.inr_injective (R := ℤ)
  have h := congrFun (coordinates_toBigWitt (verschiebung n x)) m
  rw [toBigWitt_verschiebung, BigWittVector.coeff_verschiebung, coordinates_toBigWitt] at h
  split_ifs at h ⊢ <;> simpa using h.symm

/-- The Verschiebung moves the coordinate of index `e` to index `n * e`. -/
@[simp]
theorem coeff_verschiebung_mul (n : ℕ) (x : NonUnitalBigWittVector (S / n) R) (e : S / n) :
    coeff (verschiebung n x) ⟨n * e, TruncationSet.mem_div.mp e.property⟩ = coeff x e := by
  apply Unitization.inr_injective (R := ℤ)
  rw [← coeff_toBigWitt, ← coeff_toBigWitt, toBigWitt_verschiebung,
    BigWittVector.coeff_verschiebung_mul]

/-- The coordinates of the Verschiebung at indices not divisible by `n` vanish. -/
@[simp]
theorem coeff_verschiebung_of_not_dvd (n : ℕ) (x : NonUnitalBigWittVector (S / n) R) {m : S}
    (h : ¬n ∣ m) : coeff (verschiebung n x) m = 0 := by
  apply Unitization.inr_injective (R := ℤ)
  rw [← coeff_toBigWitt, toBigWitt_verschiebung,
    BigWittVector.coeff_verschiebung_of_not_dvd n _ h, Unitization.inr_zero]

/-- The ghost components of the Verschiebung at multiples of `n`:
`w_{n k}(V_n x) = n • w_k(x)`. -/
@[simp]
theorem ghostComponent_verschiebung_mul (n : ℕ) (x : NonUnitalBigWittVector (S / n) R)
    (k : S / n) :
    ghostComponent ⟨n * k, TruncationSet.mem_div.mp k.property⟩ (verschiebung n x) =
      n • ghostComponent k x := by
  apply Unitization.inr_injective (R := ℤ)
  rw [← ghostMap_toBigWitt, toBigWitt_verschiebung, BigWittVector.ghostMap_verschiebung_mul,
    ghostMap_toBigWitt, Unitization.inr_smul, nsmul_eq_mul]

/-- The ghost components of the Verschiebung vanish at indices not divisible by `n`. -/
@[simp]
theorem ghostComponent_verschiebung_of_not_dvd (n : ℕ) (x : NonUnitalBigWittVector (S / n) R)
    {m : S} (h : ¬n ∣ m) : ghostComponent m (verschiebung n x) = 0 := by
  apply Unitization.inr_injective (R := ℤ)
  rw [← ghostMap_toBigWitt, toBigWitt_verschiebung,
    BigWittVector.ghostMap_verschiebung_of_not_dvd n _ h, Unitization.inr_zero]

/-- The Verschiebung commutes with nonunital coefficient homomorphisms. -/
@[simp]
theorem verschiebung_map (n : ℕ) (f : R →ₙ+* A) (x : NonUnitalBigWittVector (S / n) R) :
    verschiebung n (map f x) = map f (verschiebung n x) :=
  toBigWitt_injective (by
    rw [toBigWitt_verschiebung, toBigWitt_map, toBigWitt_map, toBigWitt_verschiebung,
      BigWittVector.verschiebung_map])

/-- The Verschiebung commutes with restriction to smaller truncation sets. -/
theorem restrict_verschiebung (n : ℕ) (h : T ≤ S) (x : NonUnitalBigWittVector (S / n) R) :
    restrict h (verschiebung n x) =
      verschiebung n (restrict (TruncationSet.div_le_div h n) x) :=
  toBigWitt_injective (by
    rw [toBigWitt_restrict, toBigWitt_verschiebung, toBigWitt_verschiebung, toBigWitt_restrict,
      BigWittVector.restrict_verschiebung])

/-- The Verschiebung at index one is the identity, with its source presented as `S / 1`. -/
@[simp]
theorem verschiebung_one (x : NonUnitalBigWittVector (S / 1) R) :
    verschiebung 1 x = restrict (TruncationSet.div_one S).ge x :=
  toBigWitt_injective (by
    rw [toBigWitt_verschiebung, toBigWitt_restrict, BigWittVector.verschiebung_one])

/-- Successive Verschiebung maps multiply their indices: `V_a V_b = V_{a b}`, with the source of
`V_a V_b` presented as `S / a / b`. -/
theorem verschiebung_verschiebung (a b : ℕ) (x : NonUnitalBigWittVector (S / a / b) R) :
    verschiebung a (verschiebung b x) =
      verschiebung (a * b) (restrict (TruncationSet.div_div S a b).ge x) :=
  toBigWitt_injective (by
    rw [toBigWitt_verschiebung, toBigWitt_verschiebung, toBigWitt_verschiebung, toBigWitt_restrict,
      BigWittVector.verschiebung_verschiebung])

/-- The Verschiebung at index zero is zero, because its source truncation set is empty. -/
@[simp]
theorem verschiebung_zero (x : NonUnitalBigWittVector (S / 0) R) : verschiebung 0 x = 0 :=
  toBigWitt_injective (by
    rw [toBigWitt_verschiebung, BigWittVector.verschiebung_zero, map_zero])

/-- Every Verschiebung is injective. -/
theorem verschiebung_injective (n : ℕ) :
    Function.Injective
      (verschiebung n : NonUnitalBigWittVector (S / n) R → NonUnitalBigWittVector S R) :=
  fun x y h ↦ toBigWitt_injective (BigWittVector.verschiebung_injective (R := Unitization ℤ R) n
    (by rw [← toBigWitt_verschiebung, ← toBigWitt_verschiebung, h]))

/-- On a unital ring, the comparison with `BigWittVector` carries the nonunital Verschiebung to
the unital one. -/
@[simp]
theorem unitalEquiv_verschiebung {C : Type*} [CommRing C] (n : ℕ)
    (x : NonUnitalBigWittVector (S / n) C) :
    unitalEquiv (verschiebung n x) = BigWittVector.verschiebung n (unitalEquiv x) := by
  apply unitalEquiv.symm.injective
  ext m
  obtain ⟨m, hm⟩ := m
  rw [RingEquiv.symm_apply_apply, coeff_unitalEquiv_symm, BigWittVector.coeff_verschiebung]
  split_ifs with h
  · obtain ⟨e, rfl⟩ := h
    have he : e ∈ S / n := TruncationSet.mem_div.mpr hm
    rw [Nat.mul_div_cancel_left e (Nat.pos_of_mul_pos_right (S.pos_of_mem hm)),
      coeff_unitalEquiv x ⟨e, he⟩]
    exact coeff_verschiebung_mul n x ⟨e, he⟩
  · exact coeff_verschiebung_of_not_dvd n x (m := ⟨m, hm⟩) h

end TauCeti.NonUnitalBigWittVector
