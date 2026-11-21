/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement

/-!
# Product decomposition and character extension for complementary subgroups

Given complementary subgroups `P` and `H` (`P.IsComplement' H`) of a commutative group `G`:

* `Subgroup.IsComplement'.prodMulEquiv`: the canonical multiplicative isomorphism `P × H ≃* G`
  sending `(p, h)` to `(p : G) * (h : G)`.
* `Subgroup.IsComplement'.extendChar`: given any commutative monoid `O` and homomorphisms
  `φ : P →* Oˣ` and `χ : H →* Oˣ`, the unique homomorphism `G →* Oˣ` sending
  `(p : G) * (h : G)` to `φ p * χ h`.
-/

public section

namespace Subgroup.IsComplement'

section ProdMulEquiv

variable {G : Type*} [CommGroup G] {P H : Subgroup G}

/-- The multiplicative isomorphism `P × H ≃* G` induced by complementary subgroups
`P.IsComplement' H` in a commutative group `G`. -/
noncomputable def prodMulEquiv (hPH : P.IsComplement' H) : P × H ≃* G :=
  MulEquiv.ofBijective (P.subtype.coprod H.subtype) <| by
    convert (Subgroup.isComplement_iff_bijective P H).mp hPH using 1
    ext ⟨p, h⟩
    simp [MonoidHom.coprod_apply]

/-- `prodMulEquiv` sends `(p, h)` to `(p : G) * (h : G)`. -/
@[simp]
theorem prodMulEquiv_apply (hPH : P.IsComplement' H) (p : P) (h : H) :
    hPH.prodMulEquiv (p, h) = (p : G) * (h : G) := by
  simp [prodMulEquiv]

/-- The inverse of `prodMulEquiv` sends `(p : G) * (h : G)` to `(p, h)`. -/
@[simp]
theorem prodMulEquiv_symm_mul (hPH : P.IsComplement' H) (p : P) (h : H) :
    hPH.prodMulEquiv.symm ((p : G) * (h : G)) = (p, h) :=
  (MulEquiv.symm_apply_eq hPH.prodMulEquiv).mpr (hPH.prodMulEquiv_apply p h).symm

end ProdMulEquiv

section ExtendChar

variable {O G : Type*} [CommMonoid O] [CommGroup G] {P H : Subgroup G}

/-- Given complementary subgroups `P` and `H` of a commutative group `G`, combine characters
`φ : P →* Oˣ` and `χ : H →* Oˣ` into the unique character `G →* Oˣ` sending `p * h ↦ φ(p) χ(h)`. -/
noncomputable def extendChar (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) : G →* Oˣ :=
  (φ.coprod χ).comp hPH.prodMulEquiv.symm.toMonoidHom

/-- `extendChar hPH φ χ` sends `(p : G) * (h : G)` to `φ p * χ h`. -/
theorem extendChar_mul (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) (p : P) (h : H) :
    hPH.extendChar φ χ ((p : G) * (h : G)) = φ p * χ h := by
  simp [extendChar]

/-- Evaluating `extendChar hPH φ χ` at `(p : G)` for `p : P` gives `φ p`. -/
@[simp]
theorem extendChar_coe_left (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) (p : P) :
    hPH.extendChar φ χ (p : G) = φ p := by
  simpa using hPH.extendChar_mul φ χ p 1

/-- Evaluating `extendChar hPH φ χ` at `(h : G)` for `h : H` gives `χ h`. -/
@[simp]
theorem extendChar_coe_right (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) (h : H) :
    hPH.extendChar φ χ (h : G) = χ h := by
  simpa using hPH.extendChar_mul φ χ 1 h

/-- Restricting `extendChar hPH φ χ` to `P` recovers `φ`. -/
@[simp]
theorem extendChar_comp_left (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) :
    (hPH.extendChar φ χ).comp P.subtype = φ :=
  MonoidHom.ext fun p ↦ by simp

/-- Restricting `extendChar hPH φ χ` to `H` recovers `χ`. -/
@[simp]
theorem extendChar_comp_right (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ) :
    (hPH.extendChar φ χ).comp H.subtype = χ :=
  MonoidHom.ext fun h ↦ by simp

/-- Every character of `G` is `extendChar` of its restrictions to `P` and `H`. -/
@[simp]
theorem extendChar_comp_self (hPH : P.IsComplement' H) (ψ : G →* Oˣ) :
    hPH.extendChar (ψ.comp P.subtype) (ψ.comp H.subtype) = ψ :=
  MonoidHom.ext fun g ↦ by
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.prodMulEquiv.surjective g
    rw [prodMulEquiv_apply]
    simp

end ExtendChar

end Subgroup.IsComplement'
