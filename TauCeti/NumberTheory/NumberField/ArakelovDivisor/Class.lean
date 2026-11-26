/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.Isometry
public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.OfHermitianLine
public import TauCeti.NumberTheory.NumberField.HermitianBundle.TensorProduct

import TauCeti.RingTheory.FractionalIdeal.Operations

/-!
# The class of a hermitian line in the compactified Picard group

Every hermitian line `(E, h)` over the ring of integers `𝓞 K` of a number field (a hermitian
metric on an invertible `𝓞 K`-module) is isometric to the line `O(D)` of an Arakelov divisor `D`
(`TauCeti.ArakelovDivisor.exists_isometryEquiv_hermitianMetric`), and `O(D)`, `O(D')` are isometric
exactly when `D` and `D'` have the same class
(`TauCeti.ArakelovPicardGroup.mk_eq_mk_iff_nonempty_isometryEquiv`). So the class of `D` in the
compactified Picard group `Pic^(𝓞 K) = Div^(𝓞 K) / {principal}` depends only on `(E, h)`; this
file names it `TauCeti.HermitianMetric.arakelovClass h`.

The map `(E, h) ↦ [D]` identifies isometry classes of hermitian lines with `Pic^(𝓞 K)`: two lines
have the same class exactly when they are isometric
(`TauCeti.HermitianMetric.arakelovClass_eq_arakelovClass_iff`), every class is the class of a line
(`TauCeti.ArakelovDivisor.arakelovClass_hermitianMetric`), and the degree of the class is the
Arakelov degree of the line (`TauCeti.HermitianMetric.degree_arakelovClass`). The group law of
`Pic^(𝓞 K)` is the tensor product of lines (`TauCeti.HermitianMetric.arakelovClass_tmul`), with
the trivial line `Ō_K` as identity (`TauCeti.HermitianMetric.arakelovClass_trivial`).

## Main definitions

* `TauCeti.HermitianMetric.arakelovClass`: the class in `Pic^(𝓞 K)` of a hermitian line.

## Main results

* `TauCeti.HermitianMetric.arakelovClass_eq_mk_of_isometryEquiv`: if `(E, h) ≃ O(D)`, its class
  is `[D]`.
* `TauCeti.HermitianMetric.arakelovClass_eq_mk_iff`: for a hermitian line, `[(E, h)] = [D]` iff
  `(E, h) ≃ O(D)`.
* `TauCeti.HermitianMetric.arakelovClass_eq_arakelovClass_iff`: two hermitian lines have the same
  class iff they are isometric.
* `TauCeti.HermitianMetric.IsometryEquiv.arakelovClass_eq`: isometric lines have the same class.
* `TauCeti.ArakelovDivisor.arakelovClass_hermitianMetric`: the class of `O(D)` is `[D]`; hence
  every class is the class of a hermitian line.
* `TauCeti.HermitianMetric.degree_arakelovClass`: the degree of the class of `(E, h)` is the
  degree of `(E, h)` computed with any nonzero section.
* `TauCeti.ArakelovDivisor.nonempty_isometryEquiv_tmul_hermitianMetric`:
  `O(D) ⊗ O(D') ≅ O(D + D')`, by multiplication.
* `TauCeti.HermitianMetric.arakelovClass_tmul`: the class of `L ⊗ M` is the sum of the classes.
* `TauCeti.HermitianMetric.arakelovClass_trivial`: the class of the trivial line `Ō_K` is `0`.

## References

* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.1–1.2,
  Proposition 1.1 and Corollaire.
-/

public noncomputable section

open NumberField
open scoped nonZeroDivisors TensorProduct

namespace TauCeti

namespace HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [AddCommGroup F] [Module (𝓞 K) F] (h : HermitianMetric K E) (h' : HermitianMetric K F)

open Classical in
/-- The **class of a hermitian line in the compactified Picard group**: the class `[D]` of any
Arakelov divisor `D` with `(E, h)` isometric to `O(D)`. It does not depend on `D`
(`TauCeti.HermitianMetric.arakelovClass_eq_mk_of_isometryEquiv`); every hermitian metric on an
invertible module is isometric to some `O(D)`. If there is no such `D`, the value is `0`. -/
def arakelovClass : ArakelovPicardGroup K :=
  if hD : ∃ D : ArakelovDivisor K, Nonempty (IsometryEquiv h D.hermitianMetric) then
    ArakelovPicardGroup.mk K hD.choose
  else 0

variable {h} in
/-- If `(E, h)` is isometric to `O(D)`, its class is `[D]`. -/
theorem arakelovClass_eq_mk_of_isometryEquiv {D : ArakelovDivisor K}
    (e : IsometryEquiv h D.hermitianMetric) : h.arakelovClass = ArakelovPicardGroup.mk K D := by
  have hD : ∃ D : ArakelovDivisor K, Nonempty (IsometryEquiv h D.hermitianMetric) := ⟨D, ⟨e⟩⟩
  simp only [arakelovClass, hD, ↓reduceDIte]
  rw [ArakelovPicardGroup.mk_eq_mk_iff_nonempty_isometryEquiv]
  exact ⟨hD.choose_spec.some.symm.trans e⟩

/-- A hermitian line is isometric to `O(D)` for `D` any divisor in its class. -/
theorem exists_isometryEquiv_arakelovClass [Module.Invertible (𝓞 K) E] :
    ∃ D : ArakelovDivisor K, h.arakelovClass = ArakelovPicardGroup.mk K D ∧
      Nonempty (IsometryEquiv h D.hermitianMetric) := by
  obtain ⟨D, ⟨e⟩⟩ := ArakelovDivisor.exists_isometryEquiv_hermitianMetric h
  exact ⟨D, arakelovClass_eq_mk_of_isometryEquiv e, ⟨e⟩⟩

/-- For a hermitian line, `[(E, h)] = [D]` exactly when `(E, h)` is isometric to `O(D)`. -/
theorem arakelovClass_eq_mk_iff [Module.Invertible (𝓞 K) E] {D : ArakelovDivisor K} :
    h.arakelovClass = ArakelovPicardGroup.mk K D ↔
      Nonempty (IsometryEquiv h D.hermitianMetric) := by
  refine ⟨fun hD ↦ ?_, fun ⟨e⟩ ↦ arakelovClass_eq_mk_of_isometryEquiv e⟩
  obtain ⟨D₀, hD₀, ⟨e₀⟩⟩ := h.exists_isometryEquiv_arakelovClass
  obtain ⟨e⟩ := ArakelovPicardGroup.mk_eq_mk_iff_nonempty_isometryEquiv.mp (hD₀.symm.trans hD)
  exact ⟨e₀.trans e⟩

/-- **Two hermitian lines have the same class exactly when they are isometric.** -/
theorem arakelovClass_eq_arakelovClass_iff [Module.Invertible (𝓞 K) E]
    [Module.Invertible (𝓞 K) F] :
    h.arakelovClass = h'.arakelovClass ↔ Nonempty (IsometryEquiv h h') := by
  obtain ⟨D, hD, ⟨e⟩⟩ := h'.exists_isometryEquiv_arakelovClass
  rw [hD, arakelovClass_eq_mk_iff]
  exact ⟨fun ⟨e'⟩ ↦ ⟨e'.trans e.symm⟩, fun ⟨e'⟩ ↦ ⟨e'.trans e⟩⟩

variable {h h'} in
/-- Isometric hermitian lines have the same class. -/
theorem IsometryEquiv.arakelovClass_eq (e : IsometryEquiv h h') :
    h.arakelovClass = h'.arakelovClass := by
  by_cases hD : ∃ D : ArakelovDivisor K, Nonempty (IsometryEquiv h D.hermitianMetric)
  · obtain ⟨D, ⟨e₀⟩⟩ := hD
    rw [arakelovClass_eq_mk_of_isometryEquiv e₀,
      arakelovClass_eq_mk_of_isometryEquiv (e.symm.trans e₀)]
  · have hD' : ¬ ∃ D : ArakelovDivisor K, Nonempty (IsometryEquiv h' D.hermitianMetric) :=
      fun ⟨D, ⟨e'⟩⟩ ↦ hD ⟨D, ⟨e.trans e'⟩⟩
    simp only [arakelovClass, hD, hD', ↓reduceDIte]

/-- **The degree of the class of a hermitian line is its Arakelov degree**, computed with any
nonzero section. -/
theorem degree_arakelovClass [Module.Invertible (𝓞 K) E] {s : E} (hs : s ≠ 0) :
    ArakelovPicardGroup.degree K h.arakelovClass = h.sectionDegree s := by
  obtain ⟨D, hD, ⟨e⟩⟩ := h.exists_isometryEquiv_arakelovClass
  have hes : e s ≠ 0 := (map_ne_zero_iff e e.toLinearEquiv.injective).2 hs
  rw [hD, ArakelovPicardGroup.degree_mk, ← D.sectionDegree_hermitianMetric hes,
    IsometryEquiv.sectionDegree_map h e s]

end HermitianMetric

namespace ArakelovDivisor

variable {K : Type*} [Field K] [NumberField K]

/-- **`O(D) ⊗ O(D') ≅ O(D + D')`**: multiplication `x ⊗ y ↦ x y` is an isometry from the tensor
product of the hermitian lines of two Arakelov divisors to the line of their sum. -/
theorem nonempty_isometryEquiv_tmul_hermitianMetric (D D' : ArakelovDivisor K) :
    Nonempty (HermitianMetric.IsometryEquiv (D.hermitianMetric.tmul D'.hermitianMetric)
      (D + D').hermitianMetric) := by
  set L : FractionalIdeal (𝓞 K)⁰ K :=
    (((D + D').finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  have hL0 : L ≠ 0 := Units.ne_zero _
  let ψ := FractionalIdeal.tensorEquivMul D.finitePart⁻¹ D'.finitePart⁻¹ ≪≫ₗ
    LinearEquiv.ofEq _ (L : Submodule (𝓞 K) K) (by rw [← mul_inv, ← finitePart_add])
  have hψ x y : (ψ (x ⊗ₜ y) : K) = x * y := by
    rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      FractionalIdeal.coe_tensorEquivMul_tmul]
  let g := D.hermitianMetric.tmul D'.hermitianMetric
  obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((FractionalIdeal.coeToSubmodule_ne_bot).mpr (Units.ne_zero (D.finitePart⁻¹)))
  obtain ⟨y, hyJ, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((FractionalIdeal.coeToSubmodule_ne_bot).mpr (Units.ne_zero (D'.finitePart⁻¹)))
  set x₀ : L := ψ (⟨x, hxI⟩ ⊗ₜ ⟨y, hyJ⟩)
  have hx₀ : (x₀ : K) ≠ 0 := by
    rw [hψ]
    exact mul_ne_zero hx hy
  -- The pulled-back metric on `L` has the norms of `O(D + D')` at `x₀`, so it is `O(D + D')`.
  have hg : g.comap ψ.symm.toLinearMap ψ.symm.injective = (D + D').hermitianMetric := by
    rw [HermitianMetric.eq_fractionalIdeal hL0 (g.comap ψ.symm.toLinearMap ψ.symm.injective) hx₀,
      hermitianMetric_def]
    congr 1
    funext v
    have hvx : 0 < v x := v.pos_iff.2 hx
    have hvy : 0 < v y := v.pos_iff.2 hy
    have hm : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
    simp only [HermitianMetric.placeNorm_comap, x₀, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, g, HermitianMetric.placeNorm_tmul, placeNorm_hermitianMetric,
      hψ, map_mul, infinitePart_add, Pi.add_apply]
    simp only [ne_eq, hvx.ne', not_false_eq_true, hvy.ne', Real.log_mul, mul_eq_zero,
      Real.exp_ne_zero, or_self, Real.log_exp]
    field_simp
    ring
  exact ⟨hg ▸ g.isometryEquivComap ψ.symm⟩

/-- **The class of `O(D)` is `[D]`.** In particular every class in the compactified Picard group
is the class of a hermitian line. -/
@[simp]
theorem arakelovClass_hermitianMetric (D : ArakelovDivisor K) :
    D.hermitianMetric.arakelovClass = ArakelovPicardGroup.mk K D :=
  HermitianMetric.arakelovClass_eq_mk_of_isometryEquiv (HermitianMetric.IsometryEquiv.refl _)

/-- Every class in the compactified Picard group is the class of the hermitian line `O(D)` of an
Arakelov divisor. -/
theorem exists_arakelovClass_hermitianMetric_eq (c : ArakelovPicardGroup K) :
    ∃ D : ArakelovDivisor K, D.hermitianMetric.arakelovClass = c := by
  obtain ⟨D, rfl⟩ := ArakelovPicardGroup.mk_surjective c
  exact ⟨D, arakelovClass_hermitianMetric D⟩

end ArakelovDivisor

namespace HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [AddCommGroup F] [Module (𝓞 K) F] (h : HermitianMetric K E) (h' : HermitianMetric K F)

/-- **The class of a tensor product of hermitian lines is the sum of the classes.** -/
@[simp]
theorem arakelovClass_tmul [Module.Invertible (𝓞 K) E] [Module.Invertible (𝓞 K) F] :
    (h.tmul h').arakelovClass = h.arakelovClass + h'.arakelovClass := by
  obtain ⟨D, hD, ⟨e⟩⟩ := h.exists_isometryEquiv_arakelovClass
  obtain ⟨D', hD', ⟨e'⟩⟩ := h'.exists_isometryEquiv_arakelovClass
  obtain ⟨t⟩ := ArakelovDivisor.nonempty_isometryEquiv_tmul_hermitianMetric D D'
  rw [arakelovClass_eq_mk_of_isometryEquiv ((e.tmul e').trans t), hD, hD', map_add]

variable (K) in
/-- **The class of the trivial hermitian line `Ō_K` is `0`.** -/
@[simp]
theorem arakelovClass_trivial : (trivial K).arakelovClass = 0 := by
  have h := (tensorLId (trivial K)).arakelovClass_eq
  rwa [arakelovClass_tmul, add_eq_right] at h

end HermitianMetric

end TauCeti
