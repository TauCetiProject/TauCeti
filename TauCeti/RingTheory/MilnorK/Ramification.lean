/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MilnorK.Residue

/-!
# Residues of Milnor K-theory along a ramified extension

Let `E / F` be a field extension, `v` a valuation on `F` and `w` a valuation on `E` extending it
with ramification index `e`, that is `ord_w r = e · ord_v r` for `r ∈ F`, so that there is a
residue-field embedding `ι : k_v → k_w`. Fix `t ∈ Fˣ` and `s ∈ Eˣ` of order one, and let
`c ∈ k_wˣ` be the reduced unit part of `t` relative to `s`, that is `t = u s ^ e` with `u ∈ 𝒪_wˣ`
reducing to `c`. Serre's maps `d_t : K_*ᴹ(F) → L(k_v)` and `d_s : K_*ᴹ(E) → L(k_w)` are related by

`d_s(res_{E/F} x) = Φ(d_t x)`, where `Φ(a + b Π) = ι a + ι b ({c} + e Π)`.

Reading off the two components gives the **ramification formula for the higher residue**

`∂_w(res_{E/F} x) = e · ι(∂_v x)`

in every degree, and the transformation rule `λ_s(res_{E/F} x) = ι(λ_t x) + ι(∂_v x) {c}` of the
specializations. Since Weibel's residue is `(-1) ^ (n - 1) ∂` on `K_nᴹ` over both fields, the
residue formula reads the same in his normalization. No finiteness of `E / F` is assumed, so the
formula applies for instance to completions. In degree two, where the residue is the tame symbol,
it is the ramification formula `Valuation.tameSymbol_map_algebraMap`.

When `w` is trivial on `F`, which is not a valuation extension with positive ramification index,
`d_s(res_{E/F} x)` has no `Π`-component, so every class from `F` has residue zero at `w`.

## Main results

* `Valuation.serreMap_map_algebraMap`: `d_s ∘ res_{E/F} = Φ ∘ d_t`, with `Φ` written as
  `SerreAlgebra.rescale e ∘ SerreAlgebra.shift c⁻¹ ∘ SerreAlgebra.map ι`.
* `Valuation.milnorResidue_map_algebraMap`: `∂_w(res_{E/F} x) = e · ι(∂_v x)`.
* `Valuation.milnorSpecialization_map_algebraMap`: `λ_s(res_{E/F} x) = ι(λ_t x) + ι(∂_v x) {c}`.
* `Valuation.milnorResidue_map_of_forall_ord_eq_zero`: if `ord_w` vanishes on the image of
  `Fˣ`, then `∂_w(res_{E/F} x) = 0`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Exercise III.7.8 and Remark III.6.3.1.
-/

public section

open TauCeti MilnorK

open scoped WithZero

namespace Valuation

variable {F E : Type*} [Field F] [Field E]

section Extension

variable [Algebra F E] (v : Valuation F ℤᵐ⁰) (w : Valuation E ℤᵐ⁰) [v.HasExtension w]
  (t : Fˣ) (ht : v.ord (t : F) = 1) (s : Eˣ) (hs : w.ord (s : E) = 1)

/-- **Serre's map along a ramified extension.** Let `w` extend `v` along `E / F` with
`ord_w r = e · ord_v r` for `r ∈ F`, and let `t ∈ Fˣ` and `s ∈ Eˣ` have order one. Then Serre's map
`d_s` of a class from `F` is obtained from `d_t` by applying the residue-field embedding
`ι : k_v → k_w` and sending `Π` to `{c} + e Π`, where `c` is the reduced unit part of `t` relative
to `s`. -/
theorem serreMap_map_algebraMap {e : ℤ} (h : ∀ r : F, w.ord (algebraMap F E r) = e * v.ord r)
    (x : MilnorK F) :
    w.serreMap s hs (MilnorK.map (algebraMap F E) x) =
      SerreAlgebra.rescale e (SerreAlgebra.shift
        (w.unitPartResidue s hs (Units.map (algebraMap F E : F →* E) t))⁻¹
        (SerreAlgebra.map (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
          (IsLocalRing.ResidueField w.valuationSubring)) (v.serreMap t ht x))) := by
  suffices H : (w.serreMap s hs).comp (MilnorK.map (algebraMap F E)) =
      ((SerreAlgebra.rescale e).comp ((SerreAlgebra.shift
        (w.unitPartResidue s hs (Units.map (algebraMap F E : F →* E) t))⁻¹).toRingHom.comp
        (SerreAlgebra.map _))).comp (v.serreMap t ht) from RingHom.congr_fun H x
  refine MilnorK.ringHom_ext fun f ↦ ?_
  ext
  · simp [v.unitPartResidue_map_algebraMap w t ht s hs f, zsmul_eq_mul]
  · simp [h, mul_comm e]

/-- **The ramification formula for the higher residue** (Weibel, *K-book*, Exercise III.7.8). Let
`w` extend `v` along `E / F` with `ord_w r = e · ord_v r` for `r ∈ F`. Then for every class `x` of
`K_*ᴹ(F)`, the residue at `w` of its image in `K_*ᴹ(E)` is `e` times the image of `∂_v x` under the
residue-field embedding `k_v → k_w`. No finiteness of `E / F` is assumed. -/
theorem milnorResidue_map_algebraMap {e : ℤ}
    (h : ∀ r : F, w.ord (algebraMap F E r) = e * v.ord r) (x : MilnorK F) :
    w.milnorResidue s hs (MilnorK.map (algebraMap F E) x) =
      e • MilnorK.map (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
        (IsLocalRing.ResidueField w.valuationSubring)) (v.milnorResidue t ht x) := by
  rw [milnorResidue_apply, v.serreMap_map_algebraMap w t ht s hs h, milnorResidue_apply]
  simp

/-- **Specializations along a valuation extension.** Let `w` extend `v` along `E / F`, and let
`t ∈ Fˣ` and `s ∈ Eˣ` have order one. Then for every class `x` of `K_*ᴹ(F)`,
`λ_s(res_{E/F} x) = ι(λ_t x) + ι(∂_v x) {c}`, where `ι : k_v → k_w` is the residue-field embedding
and `c` is the reduced unit part of `t` relative to `s`. -/
theorem milnorSpecialization_map_algebraMap (x : MilnorK F) :
    w.milnorSpecialization s hs (MilnorK.map (algebraMap F E) x) =
      MilnorK.map (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
          (IsLocalRing.ResidueField w.valuationSubring)) (v.milnorSpecialization t ht x) +
        MilnorK.map (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
          (IsLocalRing.ResidueField w.valuationSubring)) (v.milnorResidue t ht x) *
          ofUnit (w.unitPartResidue s hs (Units.map (algebraMap F E : F →* E) t)) := by
  -- Both sides are the `Π`-free parts of ring homomorphisms out of `K_*ᴹ(F)`, which agree on the
  -- degree-one classes; the order of the image enters only through the `Π`-coefficients.
  suffices H : (w.milnorSpecialization s hs).comp (MilnorK.map (algebraMap F E)) =
      (SerreAlgebra.fstHom.comp ((SerreAlgebra.shift
        (w.unitPartResidue s hs (Units.map (algebraMap F E : F →* E) t))⁻¹).toRingHom.comp
        (SerreAlgebra.map _))).comp (v.serreMap t ht) by
    simpa [milnorSpecialization_apply, milnorResidue_apply] using RingHom.congr_fun H x
  refine MilnorK.ringHom_ext fun f ↦ ?_
  simp [v.unitPartResidue_map_algebraMap w t ht s hs f, zsmul_eq_mul]

end Extension

/-- **Residues of classes from a subfield on which the valuation is trivial.** If `φ : F → E` is a
ring homomorphism and `ord_w` vanishes on `φ(Fˣ)`, then the residue at `w` of the image of every
class of `K_*ᴹ(F)` is zero: Serre's map `d_s` sends such images to `K_*ᴹ(k_w)`, with no
`Π`-component. -/
theorem milnorResidue_map_of_forall_ord_eq_zero (φ : F →+* E) (w : Valuation E ℤᵐ⁰) (s : Eˣ)
    (hs : w.ord (s : E) = 1) (h : ∀ r : Fˣ, w.ord (φ r) = 0) (x : MilnorK F) :
    w.milnorResidue s hs (MilnorK.map φ x) = 0 := by
  suffices H : (w.serreMap s hs).comp (MilnorK.map φ) =
      SerreAlgebra.C.comp ((w.milnorSpecialization s hs).comp (MilnorK.map φ)) by
    rw [milnorResidue_apply, ← RingHom.comp_apply, H]
    simp
  refine MilnorK.ringHom_ext fun f ↦ ?_
  simp [h]

end Valuation
