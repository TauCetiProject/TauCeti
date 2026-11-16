/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Analysis.Complex.Circle

/-!
# The central isogeny of the torus of `U(2)`

The diagonal torus `T ≅ S¹ × S¹` of `U(2)`, `diag(z₁, z₂) ↦ (z₁, z₂)` (`TauCeti.unitaryTorusHom`),
contains the identity component of the centre `Z = {diag(a, a)}` and the torus
`T_ss = {diag(b, b⁻¹)}` of `SU(2)`. Their product map `Z × T_ss → T` is `(a, b) ↦ (a b, a b⁻¹)`
(`TauCeti.unitaryTorusCentralIsogeny`, `TauCeti.unitaryTorusHom_unitaryTorusCentralIsogeny`),
whose kernel is `{(1, 1), (-1, -1)}`. Its effect on period lattices is computed in
`TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Isogeny.UnitaryTorus`.

## Main definitions

* `TauCeti.unitaryTorusCentralIsogeny`: the map `(a, b) ↦ (a b, a b⁻¹)` of `S¹ × S¹`.

## Main results

* `TauCeti.unitaryTorusHom_unitaryTorusCentralIsogeny`: in `U(2)`, the image of `(a, b)` is the
  product of the central matrix `diag(a, a)` and the matrix `diag(b, b⁻¹)` of `SU(2)`.
* `TauCeti.mem_ker_unitaryTorusCentralIsogeny_iff`, `TauCeti.card_ker_unitaryTorusCentralIsogeny`:
  the kernel is `{(1, 1), (-1, -1)}`, of order two.

## References

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori).
-/

public section

namespace TauCeti

/-- The **central isogeny of the torus of `U(2)`**, `(a, b) ↦ (a b, a b⁻¹)`. In the coordinates
`diag(z₁, z₂) ↦ (z₁, z₂)` of the diagonal torus `T` of `U(2)`, it is the multiplication map
`Z × T_ss → T` from the product of the identity component `Z = {diag(a, a)}` of the centre and
the torus `T_ss = {diag(b, b⁻¹)}` of `SU(2)`. -/
noncomputable def unitaryTorusCentralIsogeny : Circle × Circle →ₜ* Circle × Circle :=
  (ContinuousMonoidHom.mul Circle).prod
    ((ContinuousMonoidHom.mul Circle).comp
      ((ContinuousMonoidHom.id Circle).prodMap (ContinuousMonoidHom.inv Circle)))

@[simp]
theorem unitaryTorusCentralIsogeny_apply (p : Circle × Circle) :
    unitaryTorusCentralIsogeny p = (p.1 * p.2, p.1 * p.2⁻¹) :=
  (rfl)

/-- **The central isogeny inside `U(2)`.** The diagonal matrix `diag(a b, a b⁻¹)` of the image of
`(a, b)` is the product of the central matrix `diag(a, a)` (`TauCeti.coe_unitaryTorusHom_const`)
and `diag(b, b⁻¹)`. -/
theorem unitaryTorusHom_unitaryTorusCentralIsogeny (a b : Circle) :
    unitaryTorusHom (Fin 2)
        ![(unitaryTorusCentralIsogeny (a, b)).1, (unitaryTorusCentralIsogeny (a, b)).2] =
      unitaryTorusHom (Fin 2) (fun _ ↦ a) * unitaryTorusHom (Fin 2) ![b, b⁻¹] := by
  rw [← map_mul]
  congr 1
  ext i
  fin_cases i <;> simp

/-- The second factor `diag(b, b⁻¹)` has determinant one, so it lies in `SU(2)`. -/
theorem det_unitaryTorusHom_inv (b : Circle) :
    (unitaryTorusHom (Fin 2) ![b, b⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [coe_unitaryTorusHom, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

/-- The kernel of the central isogeny of the torus of `U(2)` is `{(1, 1), (-1, -1)}`. -/
theorem mem_ker_unitaryTorusCentralIsogeny_iff {p : Circle × Circle} :
    p ∈ unitaryTorusCentralIsogeny.ker ↔ p = 1 ∨ p = (-1, -1) := by
  obtain ⟨a, b⟩ := p
  rw [MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
    unitaryTorusCentralIsogeny_apply]
  constructor
  · intro h
    simp only [Prod.mk_eq_one] at h
    -- `a b = 1` and `a b⁻¹ = 1` force `b = a` and `a² = 1`.
    have hb : b = a := by
      have := h.2
      rw [mul_inv_eq_one] at this
      exact this.symm
    subst hb
    have ha : ((b : ℂ)) * b = 1 := by rw [← Circle.coe_mul, h.1, Circle.coe_one]
    rcases mul_self_eq_one_iff.1 ha with ha | ha
    · exact Or.inl (by ext <;> simp [ha])
    · exact Or.inr (by ext <;> simp [ha])
  · rintro (h | h) <;> simp only [Prod.mk_eq_one, Prod.mk.injEq] at h ⊢
    · simp [h.1, h.2]
    · obtain ⟨rfl, rfl⟩ := h
      simp

/-- The kernel of the central isogeny of the torus of `U(2)` has two elements. -/
theorem card_ker_unitaryTorusCentralIsogeny : Nat.card unitaryTorusCentralIsogeny.ker = 2 := by
  have h : (unitaryTorusCentralIsogeny.ker : Set (Circle × Circle)) = {1, (-1, -1)} := by
    ext p
    rw [SetLike.mem_coe, mem_ker_unitaryTorusCentralIsogeny_iff]
    simp
  have hne : (1 : Circle × Circle) ≠ (-1, -1) := by
    simp [Prod.ext_iff, Circle.ext_iff, eq_comm, CharZero.eq_neg_self_iff]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_pair hne]

end TauCeti
