/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.SelfDuality
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Form
import TauCeti.Geometry.Hodge.Substructure

/-!
# The scaled dual form polarizes the dual Hodge structure

Let `Q` polarize an integral pure Hodge structure `V` of weight `n`. The map
`Q♭ : V → Hom(V, ℤ)`, `x ↦ Q(x, ·)`, is injective with finite cokernel. If a positive integer `a`
kills that cokernel, the integral form `a Q^∨` on `Hom(V, ℤ)`
(`LinearMap.BilinForm.scaledDualForm`), `(ξ, η) ↦ ξ(y_η)` where `Q♭ y_η = a η`, polarizes the dual
Hodge structure `V^*` of weight `-n` (`TauCeti.Hodge.IsPolarization.scaledDualForm`). When `Q` is
a perfect pairing one may take `a = 1`: the dual form `Q^∨` is then an integral, principal
polarization of `V^*` (`TauCeti.Hodge.IsPolarization.scaledDualForm_one`,
`LinearMap.BilinForm.isPerfPair_scaledDualForm_one`).

The proof: the map `η ↦ y_η` is a Hodge morphism `V^*(-n) → V`, since composed with the
self-duality `Q♭` it is multiplication by `a` and self-duality is strict. It is injective, and
`Q(y_ξ, y_η) = a · (a Q^∨)(ξ, η)`. So `Q` pulls back to `a` times the scaled dual form, which
therefore polarizes `V^*(-n)` (`TauCeti.Hodge.IsPolarization.of_smul`); a Tate twist then gives
`V^*`.

## Main results

* `TauCeti.Hodge.IsPolarization.of_smul`: if a positive multiple of a form polarizes a Hodge
  structure, so does the form.
* `TauCeti.Hodge.Polarization.scaledDualHom`: the Hodge morphism `η ↦ y_η` from `V^*(-n)` to `V`.
* `TauCeti.Hodge.IsPolarization.scaledDualForm`: `a Q^∨` polarizes `V^*`.
* `TauCeti.Hodge.IsPolarization.scaledDualForm_one`: for a principal `Q`, `Q^∨` polarizes `V^*`.

## References

* Stanford VIGRE notes, Definitions 1.13–1.14 and Lemma 1.16, pp. 5–6, as cited in the
  AbelianSchemesAndArithmeticModuli roadmap §A5.2.
-/

public section

namespace TauCeti.Hodge

open IsBaseChange
open scoped ComplexOrder

variable {V : Type*} {Vℂ : Type*}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ}
variable {hs : HodgeStructure hℂ n}

namespace IsPolarization

/-- **A form whose positive multiple polarizes is a polarization.** -/
theorem of_smul {Q : LinearMap.BilinForm ℤ V} {a : ℤ} (ha : 0 < a)
    (h : IsPolarization hℂ hs (a • Q)) : IsPolarization hℂ hs Q := by
  have ha' : (a : ℂ) ≠ 0 := Int.cast_ne_zero.mpr ha.ne'
  have hform (x y : Vℂ) : bilinForm hℂ (a • Q) x y = a * bilinForm hℂ Q x y := by
    rw [bilinForm_smul, LinearMap.smul_apply, LinearMap.smul_apply, algebraMap_int_eq,
      eq_intCast, smul_eq_mul]
  refine ⟨fun x y ↦ ?_, ?_, fun p x hx y hy ↦ ?_, fun p x hx hx0 ↦ ?_⟩
  · have := h.symm_weight x y
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ ha.ne' (by rw [this]; ring)
  · refine ⟨fun x hx ↦ h.nondegenerate.1 x fun y ↦ ?_, fun y hy ↦ h.nondegenerate.2 y fun x ↦ ?_⟩
    · simp [hx y]
    · simp [hy x]
  · have := h.orthogonal p x hx y hy
    rw [hform] at this
    exact (mul_eq_zero.mp this).resolve_left ha'
  · have := h.positive p x hx hx0
    rw [hform, mul_left_comm] at this
    have hinv : (0 : ℂ) < ((a : ℝ)⁻¹ : ℝ) :=
      Complex.zero_lt_real.mpr (inv_pos.mpr (by exact_mod_cast ha))
    have key := mul_pos hinv this
    rwa [← mul_assoc, Complex.ofReal_inv, Complex.ofReal_intCast, inv_mul_cancel₀ ha',
      one_mul] at key

end IsPolarization

section Dual

variable [Module.Free ℤ V] [Module.Finite ℤ V]
variable {Q : LinearMap.BilinForm ℤ V} {a : ℤ}

namespace IsPolarization

/-- The flat map `Q♭ : V → Hom(V, ℤ)` of a polarizing form is injective. -/
theorem injective_flat (hQ : IsPolarization hℂ hs Q) : Function.Injective Q :=
  by simpa using (⟨Q, hQ⟩ : Polarization hℂ hs).toDualHom_toIntLinearMap_injective

/-- The map `η ↦ y_η`, with `Q♭ y_η = a η`, as a **Hodge morphism `V^*(-n) → V`**: composed with
the self-duality `Q♭ : V → V^*(-n)` it is multiplication by `a`, and self-duality is strict. -/
noncomputable def scaledDualHom (hQ : IsPolarization hℂ hs Q)
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range Q) :
    HodgeStructure.Hom hs.dualTateTwist hs where
  toIntLinearMap := Q.scaledDualPreimage hQ.injective_flat a ha
  map_mem_F p y hy := by
    let P : Polarization hℂ hs := ⟨Q, hQ⟩
    have hint : P.toDualHom.toIntLinearMap ∘ₗ Q.scaledDualPreimage hQ.injective_flat a ha =
        a • LinearMap.id :=
      LinearMap.ext fun η ↦ by simp [P]
    have hcomplex : P.toDualHom.toLinearMap ∘ₗ
        integralMapToComplex (isBaseChange_dualLatticeMap hℂ) ιℂ
          (Q.scaledDualPreimage hQ.injective_flat a ha) = a • LinearMap.id := by
      rw [HodgeStructure.Hom.toLinearMap_def, ← integralMapToComplex_comp, hint,
        integralMapToComplex_zsmul, integralMapToComplex_id]
    have hmem : a • y ∈ LinearMap.range P.toDualHom.toLinearMap ⊓ hs.dualTateTwist.F p :=
      ⟨⟨_, by simpa using congr($hcomplex y)⟩, zsmul_mem hy a⟩
    rw [P.toDualHom.range_inf_F] at hmem
    obtain ⟨x, hx, hxy⟩ := hmem
    have hgy : integralMapToComplex (isBaseChange_dualLatticeMap hℂ) ιℂ
        (Q.scaledDualPreimage hQ.injective_flat a ha) y = x := by
      refine P.toDualHom_toLinearMap_injective ?_
      rw [hxy]
      simpa using congr($hcomplex y)
    exact hgy ▸ hx

/-- `Q` pulled back along `η ↦ y_η` is `a` times the scaled dual form. -/
theorem comp_scaledDualPreimage (hQ : IsPolarization hℂ hs Q)
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range Q) :
    Q.comp (Q.scaledDualPreimage hQ.injective_flat a ha)
        (Q.scaledDualPreimage hQ.injective_flat a ha) =
      a • Q.scaledDualForm hQ.injective_flat a ha := by
  ext ξ η
  simp [LinearMap.BilinForm.scaledDualForm_apply]

/-- **The scaled dual form polarizes the dual Hodge structure.** If `Q` polarizes `V` and the
positive integer `a` kills the cokernel of `Q♭ : V → Hom(V, ℤ)`, then `a Q^∨` polarizes the dual
Hodge structure `V^*`, of weight `-n`. -/
theorem scaledDualForm (hQ : IsPolarization hℂ hs Q)
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range Q) (ha0 : 0 < a) :
    IsPolarization (isBaseChange_dualLatticeMap hℂ) hs.dual
      (Q.scaledDualForm hQ.injective_flat a ha) := by
  have hinj : Function.Injective (hQ.scaledDualHom ha).toIntLinearMap := fun ξ η h ↦ by
    have := congr(Q $h)
    simp only [scaledDualHom, LinearMap.BilinForm.apply_scaledDualPreimage] at this
    exact smul_right_injective _ ha0.ne' this
  have htwist := (hQ.comp (hQ.scaledDualHom ha) hinj)
  rw [show (hQ.scaledDualHom ha).toIntLinearMap = Q.scaledDualPreimage hQ.injective_flat a ha
    from rfl, hQ.comp_scaledDualPreimage ha] at htwist
  exact (of_smul ha0 htwist).of_F_eq_F_add n (by ring) fun p ↦ by
    rw [HodgeStructure.dualTateTwist_F, add_sub_cancel_right]

/-- **The dual of a principal polarization is a principal polarization.** If `Q` polarizes `V`
and is a perfect pairing, the integral dual form `Q^∨` (the case `a = 1`) polarizes `V^*`; it is a
perfect pairing by `LinearMap.BilinForm.isPerfPair_scaledDualForm_one`. -/
theorem scaledDualForm_one (hQ : IsPolarization hℂ hs Q) [Q.IsPerfPair] :
    IsPolarization (isBaseChange_dualLatticeMap hℂ) hs.dual
      (Q.scaledDualForm (LinearMap.IsPerfPair.bijective_left Q).injective 1
        Q.one_smul_mem_range_of_isPerfPair) :=
  hQ.scaledDualForm Q.one_smul_mem_range_of_isPerfPair one_pos

end IsPolarization

end Dual

end TauCeti.Hodge
