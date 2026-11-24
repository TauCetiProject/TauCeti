/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Frobenius

/-!
# The map `ℤ_p → 𝕎 R` for a ring `R` of characteristic `p`

Mathlib identifies the `p`-adic integers with the Witt vectors of `𝔽_p`
(`WittVector.fromPadicInt : ℤ_[p] →+* 𝕎 (ZMod p)`). For a ring `R` of characteristic `p`, the
unique ring homomorphism `ZMod p → R` induces `𝕎 (ZMod p) → 𝕎 R`, and composing gives the
structure map `ℤ_[p] → 𝕎 R` (`TauCeti.WittVector.padicIntHom`). For `R = 𝒪_F` this is the
structure map `ℤ_p → A_inf`, the ring map underlying the projection of `Spa(A_inf, A_inf)`, and of
the period domain of the Fargues–Fontaine curve inside it, to `Spa(ℤ_p, ℤ_p)`.

The map is natural in `R`, so the Witt-vector Frobenius, which in characteristic `p` is the map
induced by the Frobenius of `R`, fixes it: Frobenius is a map over `ℤ_p`. Like every ring
homomorphism out of `ℤ_[p]`, the map is continuous for every adic topology on `𝕎 R` defined by an
ideal containing `p`, such as the `(p, [ϖ])`-adic topology of `A_inf`
(`PadicInt.continuous_of_isAdic`, in `TauCeti.RingTheory.Huber.Padic.Basic`).

## Main definitions

* `TauCeti.WittVector.padicIntHom`: the ring homomorphism `ℤ_[p] → 𝕎 R`.

## Main results

* `TauCeti.WittVector.padicIntHom_zmod`: for `R = ZMod p` it is `WittVector.fromPadicInt`.
* `TauCeti.WittVector.padicIntHom_injective`: it is injective.
* `TauCeti.WittVector.instCharZero`: Witt vectors of a ring of characteristic `p` have
  characteristic zero.
* `TauCeti.WittVector.map_comp_padicIntHom`, `TauCeti.WittVector.map_padicIntHom`: it is natural
  in `R`.
* `TauCeti.WittVector.frobenius_comp_padicIntHom`, `TauCeti.WittVector.frobenius_padicIntHom`:
  Frobenius fixes it.
-/

public section

namespace TauCeti.WittVector

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]

local notation "𝕎" => _root_.WittVector p

/-- **The structure map `ℤ_p → 𝕎 R`** of the Witt vectors of a ring `R` of characteristic `p`:
Mathlib's identification `ℤ_[p] ≅ 𝕎 (ZMod p)` followed by the map of Witt vectors induced by the
unique ring homomorphism `ZMod p → R`. -/
noncomputable def padicIntHom : ℤ_[p] →+* 𝕎 R :=
  (map (ZMod.castHom (dvd_refl p) R)).comp (fromPadicInt p)

/-- The Witt-vector coefficients of the image of a `p`-adic integer are the images in `R` of its
coefficients in `𝕎 (ZMod p)`. -/
theorem coeff_padicIntHom (x : ℤ_[p]) (n : ℕ) :
    (padicIntHom p R x).coeff n = ZMod.castHom (dvd_refl p) R ((fromPadicInt p x).coeff n) := by
  simp [padicIntHom, map_coeff]

/-- For `R = ZMod p` the structure map is Mathlib's `WittVector.fromPadicInt`. -/
theorem padicIntHom_zmod : padicIntHom p (ZMod p) = fromPadicInt p := by
  ext x n
  simp [coeff_padicIntHom]

/-- The structure map `ℤ_[p] → 𝕎 R` is injective: `R` is nontrivial, so `ZMod p → R` is injective,
and so is the map it induces on Witt vectors. -/
theorem padicIntHom_injective : Function.Injective (padicIntHom p R) :=
  have := CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).one_lt.ne'
  (map_injective _ (ZMod.castHom (dvd_refl p) R).injective).comp
    (_root_.WittVector.equiv p).symm.injective

/-- The Witt vectors of a ring of characteristic `p` have characteristic zero, since `ℤ_[p]`
injects into them. -/
instance instCharZero : CharZero (𝕎 R) :=
  charZero_of_injective_ringHom (padicIntHom_injective p R)

variable {R} in
/-- **Naturality**: the map of Witt vectors induced by a ring homomorphism `R → S` of rings of
characteristic `p` carries the structure map of `𝕎 R` to that of `𝕎 S`. -/
@[simp]
theorem map_comp_padicIntHom {S : Type*} [CommRing S] [CharP S p] (f : R →+* S) :
    (map f).comp (padicIntHom p R) = padicIntHom p S := by
  ext x n
  rw [RingHom.comp_apply, map_coeff, coeff_padicIntHom, coeff_padicIntHom, ← RingHom.comp_apply,
    RingHom.ext_zmod (f.comp _) (ZMod.castHom (dvd_refl p) S)]

variable {R} in
/-- Naturality of the structure map, applied to a `p`-adic integer. -/
@[simp]
theorem map_padicIntHom {S : Type*} [CommRing S] [CharP S p] (f : R →+* S) (x : ℤ_[p]) :
    map f (padicIntHom p R x) = padicIntHom p S x :=
  congr($(map_comp_padicIntHom p f) x)

/-- **Frobenius is a map over `ℤ_p`**: the Witt-vector Frobenius of `𝕎 R`, which is induced by the
Frobenius of `R`, fixes the structure map `ℤ_[p] → 𝕎 R`. -/
@[simp]
theorem frobenius_comp_padicIntHom : frobenius.comp (padicIntHom p R) = padicIntHom p R := by
  rw [frobenius_eq_map_frobenius, map_comp_padicIntHom]

/-- Frobenius fixes the image of every `p`-adic integer under the structure map. -/
@[simp]
theorem frobenius_padicIntHom (x : ℤ_[p]) : frobenius (padicIntHom p R x) = padicIntHom p R x :=
  congr($(frobenius_comp_padicIntHom p R) x)

end TauCeti.WittVector
