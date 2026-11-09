/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.OrderFiltration
public import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# Residues on meromorphic germs

The residue descends to a complex-linear functional on meromorphic germs. On germs with
at most a simple pole, its kernel consists exactly of the germs of nonnegative order.
This identifies the one-dimensional obstruction to removing a simple pole.

## References

* Lars V. Ahlfors, *Complex Analysis*, Chapter 4, §3.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.meromorphicGerms

variable {a : ℂ}

/-- The residue as a complex-linear functional on meromorphic germs. -/
def residue (a : ℂ) : meromorphicGerms ℂ a →ₗ[ℂ] ℂ where
  toFun φ := Germ.liftOn φ.1 (fun f ↦ Contour.residue f a)
    fun _ _ h ↦ Contour.residue_congr_nhdsNE h
  map_add' φ ψ := by
    obtain ⟨f, hf, rfl⟩ := exists_mk φ
    obtain ⟨g, hg, rfl⟩ := exists_mk ψ
    rw [← mk_add hf hg, coe_mk, coe_mk, coe_mk]
    exact Contour.residue_add hf hg
  map_smul' c φ := by
    obtain ⟨f, hf, rfl⟩ := exists_mk φ
    rw [← mk_smul c hf, coe_mk, coe_mk]
    exact Contour.residue_const_smul c

/-- Any meromorphic representative computes the residue of its germ. -/
@[simp]
theorem residue_mk (f : ℂ → ℂ) (hf : MeromorphicAt f a) :
    residue a (mk f hf) = Contour.residue f a := by
  simp only [residue, LinearMap.coe_mk, AddHom.coe_mk, coe_mk]
  rfl

/-- The reciprocal coordinate has residue one. -/
@[simp]
theorem residue_coordinate_inv (a : ℂ) : residue a (coordinate a)⁻¹ = 1 := by
  have heq : (coordinate a)⁻¹ = mk (fun z : ℂ ↦ (z - a)⁻¹)
      (Contour.meromorphicAt_sub_inv a) := by
    apply Subtype.ext
    rw [coe_inv, coe_coordinate, coe_mk]
    exact (Germ.coe_inv (fun z : ℂ ↦ z - a)).symm
  rw [heq, residue_mk, Contour.residue_sub_inv]

/-- For an at-most-simple pole, vanishing residue is equivalent to removability. -/
theorem residue_eq_zero_iff_of_mem_orderGE_neg_one (φ : meromorphicGerms ℂ a)
    (hφ : φ ∈ orderGE a (-1)) : residue a φ = 0 ↔ φ ∈ orderGE a 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  rw [residue_mk, mem_orderGE, order_mk, WithTop.coe_zero]
  constructor
  · intro hr
    have hbound : -1 ≤ meromorphicOrderAt f a := by
      have hneg : ((-1 : ℤ) : WithTop ℤ) = -1 := by norm_cast
      simpa only [mem_orderGE, order_mk, hneg] using hφ
    have hlim := Contour.tendsto_sub_mul_nhds_residue hf hbound
    rw [hr] at hlim
    have hid : MeromorphicAt (fun z : ℂ ↦ z - a) a :=
      (MeromorphicAt.id a).sub (.const a a)
    have hpos := (tendsto_zero_iff_meromorphicOrderAt_pos (hid.mul hf)).mp hlim
    rw [meromorphicOrderAt_mul hid hf, meromorphicOrderAt_id_sub_const] at hpos
    cases ho : meromorphicOrderAt f a with
    | top => exact le_top
    | coe j =>
      rw [ho] at hpos
      have hj : 0 < 1 + j := by exact_mod_cast hpos
      exact_mod_cast (by omega : 0 ≤ j)
  · exact Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg

end TauCeti.meromorphicGerms
