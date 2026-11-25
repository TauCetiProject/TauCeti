/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.Adjoint
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.Fourier.AddCircle

/-!
# The maximal tori of `SU(2)` and `SO(3)` under the double cover

The maximal torus of `SU(2)` is the circle `T = {diag(z, z⁻¹)}`, parametrized by
`TauCeti.SU2.torusHom`. Its image under the double cover `SU(2) → SO(3)`
(`TauCeti.SU2.toSO3`) is the circle of rotations about the axis `e₃ = (0, 0, 1)`, which this file
parametrizes by

`TauCeti.SU2.rotationTorusHom z = !![Re z, Im z, 0; -Im z, Re z, 0; 0, 0, 1]`,

the rotation about `e₃` by the angle `-arg z`. This parametrization is injective, so it is the
circle coordinate of the maximal torus `T' = toSO3(T)` of `SO(3)`, which is also the stabilizer of
`e₃` (`TauCeti.SU2.mem_range_rotationTorusHom_iff`, `TauCeti.SU2.range_rotationTorusHom`). In
these two circle coordinates the double cover restricted to the tori is the squaring map:

`toSO3 (torusHom z) = rotationTorusHom (z ^ 2)` (`TauCeti.SU2.toSO3_torusHom`).

So, read in these circle coordinates, passing from `SU(2)` to `SO(3) = SU(2) ⧸ {±1}` is the
power map `z ↦ z²` of the circle, which changes its character and period lattices by index two.

* **Characters.** A continuous character `z ↦ zᵐ` of `T` descends to a character of `T'`, that is,
  takes equal values at torus elements with the same rotation, exactly when `m` is even
  (`TauCeti.SU2.forall_apply_eq_of_toSO3_torusHom_eq_iff`). Equivalently, by
  `ContinuousMonoidHom.exists_eq_comp_id_pow_iff` for `n = 2`, the characters of `T'` pull back to
  the sublattice `2ℤ` of the character lattice `ℤ` of `T`.
* **Period lattices.** The kernel of the squaring map `z ↦ z²` of the circle is `{±1}`, so its
  Lie map carries the period lattice of the circle onto a sublattice of index two
  (`TauCeti.relIndex_map_lieMap_id_circle_pow_periodLattice` for `n = 2`). This file does not
  treat the Lie map of `toSO3` itself or the period lattices of the subgroups `T` and `T'`.

## Main definitions

* `TauCeti.SU2.rotationTorusHom`: the circle parametrization of the rotations about `e₃`.

## Main results

* `TauCeti.SU2.toSO3_torusHom`: on the maximal tori, the double cover is `z ↦ z²`.
* `TauCeti.SU2.rotationTorusHom_injective`: the rotation parametrization is injective.
* `TauCeti.SU2.mem_range_rotationTorusHom_iff`: the rotations about `e₃` are exactly the rotations
  fixing `e₃`.
* `TauCeti.SU2.range_rotationTorusHom`: they form the image of the maximal torus of `SU(2)`.
* `TauCeti.SU2.forall_apply_eq_of_toSO3_torusHom_eq_iff`: the characters of the maximal torus of
  `SU(2)` that descend to `SO(3)` are the even ones.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 6 (the example `SU(2) → SO(3)`) and Chapter V, § 7 (`SU(2)` and `SO(3)`).
-/

public section

open Matrix

namespace TauCeti

namespace SU2

/-- The rotation about the axis `e₃ = (0, 0, 1)` attached to a point `z` of the circle, by the
angle `-arg z`. -/
private noncomputable def rotationTorusMatrix (z : Circle) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(z : ℂ).re, (z : ℂ).im, 0; -(z : ℂ).im, (z : ℂ).re, 0; 0, 0, 1]

private theorem coe_toSO3_torusHom_eq_rotationTorusMatrix (w : Circle) :
    (toSO3 (torusHom w) : Matrix (Fin 3) (Fin 3) ℝ) = rotationTorusMatrix (w ^ 2) := by
  rw [coe_toSO3_torusHom, rotationTorusMatrix, Circle.coe_pow]

private theorem rotationTorusMatrix_mem (z : Circle) :
    rotationTorusMatrix z ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  -- Write `z = w²`; the matrix is then the rotation `toSO3 (torusHom w)`.
  obtain ⟨w, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [← coe_toSO3_torusHom_eq_rotationTorusMatrix]
  exact (toSO3 (torusHom w)).property

private theorem rotationTorusMatrix_mul (z z' : Circle) :
    rotationTorusMatrix (z * z') = rotationTorusMatrix z * rotationTorusMatrix z' := by
  obtain ⟨w, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  obtain ⟨w', rfl⟩ := z'.exists_pow_nat_eq two_ne_zero
  rw [← mul_pow, ← coe_toSO3_torusHom_eq_rotationTorusMatrix,
    ← coe_toSO3_torusHom_eq_rotationTorusMatrix, ← coe_toSO3_torusHom_eq_rotationTorusMatrix,
    map_mul, map_mul, Submonoid.coe_mul]

/-- The circle parametrization `z ↦ !![Re z, Im z, 0; -Im z, Re z, 0; 0, 0, 1]` of the rotations
of `ℝ³` about the axis `e₃ = (0, 0, 1)`, the rotation about `e₃` by the angle `-arg z`. It is the
maximal torus of `SO(3)` read in its circle coordinate (`TauCeti.SU2.range_rotationTorusHom`). -/
noncomputable def rotationTorusHom : Circle →* specialOrthogonalGroup (Fin 3) ℝ where
  toFun z := ⟨rotationTorusMatrix z, rotationTorusMatrix_mem z⟩
  map_one' := Subtype.ext <| by
    have h := coe_toSO3_torusHom_eq_rotationTorusMatrix 1
    rw [one_pow, map_one, map_one] at h
    exact h.symm
  map_mul' z z' := Subtype.ext (rotationTorusMatrix_mul z z')

@[simp]
theorem coe_rotationTorusHom (z : Circle) :
    (rotationTorusHom z : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(z : ℂ).re, (z : ℂ).im, 0; -(z : ℂ).im, (z : ℂ).re, 0; 0, 0, 1] :=
  (rfl)

theorem continuous_rotationTorusHom : Continuous rotationTorusHom := by
  refine continuous_induced_rng.2 ?_
  have hre : Continuous fun z : Circle ↦ (z : ℂ).re :=
    Complex.continuous_re.comp continuous_subtypeVal
  have him : Continuous fun z : Circle ↦ (z : ℂ).im :=
    Complex.continuous_im.comp continuous_subtypeVal
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp [hre, him, continuous_const]

/-- The rotation parametrization of the maximal torus of `SO(3)` is injective: the first row of the
rotation recovers `z`. -/
theorem rotationTorusHom_injective : Function.Injective rotationTorusHom := fun z w h ↦ by
  have h' := congrArg (fun R : specialOrthogonalGroup (Fin 3) ℝ ↦ (R : Matrix (Fin 3) (Fin 3) ℝ)) h
  simp only [coe_rotationTorusHom] at h'
  exact Circle.ext (Complex.ext (by simpa using congrFun (congrFun h' 0) 0)
    (by simpa using congrFun (congrFun h' 0) 1))

/-- **The double cover on the maximal tori is the squaring map.** The image of the torus element
`diag(z, z⁻¹)` of `SU(2)` in `SO(3)` is the rotation attached to `z²`. -/
@[simp]
theorem toSO3_torusHom (z : Circle) : toSO3 (torusHom z) = rotationTorusHom (z ^ 2) :=
  Subtype.ext (coe_toSO3_torusHom_eq_rotationTorusMatrix z)

/-- **The maximal torus of `SO(3)` is the stabilizer of `e₃`.** A rotation of `ℝ³` is a rotation
about the axis `e₃ = (0, 0, 1)` exactly when it fixes `e₃`. -/
theorem mem_range_rotationTorusHom_iff {R : specialOrthogonalGroup (Fin 3) ℝ} :
    R ∈ rotationTorusHom.range ↔
      (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ Pi.single 2 1 = Pi.single 2 1 := by
  obtain ⟨g, rfl⟩ := toSO3_surjective R
  rw [toSO3_mulVec_single_two_eq_self_iff, mem_torus_iff_exists_torusHom]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
    -- `torusHom w` and `g` have the same rotation, so `torusHom w * g⁻¹ = ±1`.
    set x := torusHom w * g⁻¹ with hx
    have hker : toSO3 x = 1 := by rw [hx, map_mul, map_inv, toSO3_torusHom, hz, mul_inv_cancel]
    have hxg : torusHom w = x * g := by rw [hx, inv_mul_cancel_right]
    rcases (toSO3_eq_one_iff x).1 hker with h | h
    · have hx1 : x = 1 := Subtype.ext h
      exact ⟨w, by rw [hxg, hx1, one_mul]⟩
    · -- Then `torusHom w = -g`, and `torusHom (-w) = -torusHom w = g`.
      have hwg : torusMatrix w = -g := by
        rw [← coe_torusHom, hxg, Submonoid.coe_mul, h, neg_one_mul]
      exact ⟨-w, Subtype.ext (by simp [hwg])⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z ^ 2, (toSO3_torusHom z).symm⟩

/-- **The image of the maximal torus of `SU(2)`** under the double cover is the circle of rotations
about `e₃`. -/
theorem range_rotationTorusHom : rotationTorusHom.range = torus.map toSO3 := by
  ext R
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
    exact ⟨torusHom w, torusHom_mem_torus w, toSO3_torusHom w⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.1 hg
    exact ⟨z ^ 2, (toSO3_torusHom z).symm⟩

/-- **The characters of the maximal torus of `SU(2)` that descend to `SO(3)` are the even ones.**
A continuous character `χ` of the circle, read as a character of the maximal torus of `SU(2)`
through `diag(z, z⁻¹) ↦ z`, takes equal values at any two torus elements with the same image in
`SO(3)` exactly when it is `z ↦ z^(2k)` for an integer `k`. -/
theorem forall_apply_eq_of_toSO3_torusHom_eq_iff (χ : Circle →ₜ* Circle) :
    (∀ z w : Circle, toSO3 (torusHom z) = toSO3 (torusHom w) → χ z = χ w) ↔
      ∃ k : ℤ, ∀ z : Circle, χ z = z ^ (2 * k) := by
  obtain ⟨m, hm, -⟩ := ContinuousMonoidHom.existsUnique_circle_eq_zpow χ
  simp only [toSO3_torusHom, rotationTorusHom_injective.eq_iff]
  constructor
  · intro h
    -- The torus elements `diag(-1, -1)` and `1` have the same rotation, so `(-1)ᵐ = 1`.
    have h1 := h (-1) 1 (by simp)
    rw [hm, hm, _root_.one_zpow] at h1
    obtain ⟨k, hk⟩ : Even m := by
      by_contra hodd
      rw [Int.not_even_iff_odd] at hodd
      exact Circle.neg_ne_self 1 (hodd.neg_one_zpow.symm.trans h1)
    exact ⟨k, fun z ↦ by rw [hm, hk, two_mul]⟩
  · rintro ⟨k, hk⟩ z w hzw
    rw [hk, hk, _root_.zpow_mul, _root_.zpow_mul]
    exact_mod_cast congrArg (· ^ k) hzw

end SU2

end TauCeti
