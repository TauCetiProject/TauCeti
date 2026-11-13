/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.LaurentChart.Basic

/-!
# Laurent chart inverses in ambient semifields

A faithful chart in a general commutative algebra evaluates inverse coordinates as inverses
of its coordinate units. In an ambient semifield those same values can be written using the
ambient inverse operation. The lemmas here give that normal form without requiring a domain
instance on the coefficient semiring.
-/

public section

namespace TauCeti.LaurentChart

variable {R K K' F G : Type*}

section Semifield
variable [CommSemiring R] [Semifield F] [Algebra R F] [Semifield G] [Algebra R G]

/-- Range membership for an inverse is reflected by ambient algebra transport. -/
@[simp↓]
theorem inv_mem_range_map_iff (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f)
  (z : F) :
    (f z)⁻¹ ∈ (c.map f hf).range ↔ z⁻¹ ∈ c.range := by
  simpa only [map_inv₀] using c.mem_range_map_iff f hf z⁻¹

/-- Inverse range transport cancels an embedded inverse in its algebra normal form. -/
@[simp↓]
theorem mapRange_symm_inv (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) (z
  : F)
    (h : (f z)⁻¹ ∈ (c.map f hf).range) :
    (c.mapRange f hf).symm ⟨(f z)⁻¹, h⟩ =
      ⟨z⁻¹, (c.inv_mem_range_map_iff f hf z).mp h⟩ := by
  simpa only [map_inv₀] using c.mapRange_symm_apply f hf z⁻¹
    (by simpa only [map_inv₀] using h)

/-- Ambient inverse coordinates belong to the Laurent subalgebra. -/
@[simp]
theorem inv_coordinate_mem_range (c : LaurentChart R K F) (i : K) :
    (c.coordinate i)⁻¹ ∈ c.range := by
  simpa only [Units.val_inv_eq_inv_val, val_coordinateUnit] using
    c.inv_coordinateUnit_mem_range i

/-- An ambient inverse coordinate expands as its negative standard-basis monomial. -/
@[simp↓]
theorem laurentExpansion_inv_coordinate (c : LaurentChart R K F) (i : K)
    (h : (c.coordinate i)⁻¹ ∈ c.range) :
    c.laurentExpansion ⟨(c.coordinate i)⁻¹, h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [Units.val_inv_eq_inv_val, val_coordinateUnit] using
    c.laurentExpansion_inv_coordinateUnit i
      (by simpa only [Units.val_inv_eq_inv_val, val_coordinateUnit] using h)

/-- An ambient inverse coordinate has a single negative-basis coefficient. -/
@[simp↓]
theorem coeff_inv_coordinate (c : LaurentChart R K F) (i : K)
    (h : (c.coordinate i)⁻¹ ∈ c.range) :
    c.coeff ⟨(c.coordinate i)⁻¹, h⟩ = Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_inv_coordinate, AddMonoidAlgebra.coeff_single]

/-- An ambient inverse of a retained coordinate expands in the smaller Laurent algebra. -/
@[simp↓]
theorem laurentExpansion_restrict_inv_coordinate (c : LaurentChart R K F) (f : K' ↪ K)
    (i : K') (h : (c.coordinate (f i))⁻¹ ∈ (c.restrict f).range) :
    (c.restrict f).laurentExpansion ⟨(c.coordinate (f i))⁻¹, h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [coordinate_restrict] using (c.restrict f).laurentExpansion_inv_coordinate i
    (by simpa only [coordinate_restrict] using h)

/-- Coefficients at an ambient inverse of a retained coordinate are concentrated at its basis. -/
@[simp↓]
theorem coeff_restrict_inv_coordinate (c : LaurentChart R K F) (f : K' ↪ K)
    (i : K') (h : (c.coordinate (f i))⁻¹ ∈ (c.restrict f).range) :
    (c.restrict f).coeff ⟨(c.coordinate (f i))⁻¹, h⟩ =
      Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_restrict_inv_coordinate, AddMonoidAlgebra.coeff_single]

/-- An ambient inverse reindexed coordinate expands with its new label. -/
@[simp↓]
theorem laurentExpansion_reindex_inv_coordinate (c : LaurentChart R K F) (e : K ≃ K')
    (i : K') (h : (c.coordinate (e.symm i))⁻¹ ∈ (c.reindex e).range) :
    (c.reindex e).laurentExpansion ⟨(c.coordinate (e.symm i))⁻¹, h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [coordinate_reindex] using (c.reindex e).laurentExpansion_inv_coordinate i
    (by simpa only [coordinate_reindex] using h)

/-- The coefficient family of an ambient inverse reindexed coordinate has its new label. -/
@[simp↓]
theorem coeff_reindex_inv_coordinate (c : LaurentChart R K F) (e : K ≃ K')
    (i : K') (h : (c.coordinate (e.symm i))⁻¹ ∈ (c.reindex e).range) :
    (c.reindex e).coeff ⟨(c.coordinate (e.symm i))⁻¹, h⟩ =
      Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_reindex_inv_coordinate, AddMonoidAlgebra.coeff_single]

end Semifield

section Field
variable [CommRing R] [Field F] [Algebra R F]

/-- Constructor-normal ambient inverse coordinates have their negative Laurent monomial. -/
@[simp↓]
theorem laurentExpansion_ofCoordinates_inv_coordinate (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (i : K)
    (h : (x i : F)⁻¹ ∈ (ofCoordinates x hx).range) :
    (ofCoordinates x hx).laurentExpansion ⟨(x i : F)⁻¹, h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [coordinate_ofCoordinates] using
    (ofCoordinates x hx).laurentExpansion_inv_coordinate i
      (by simpa only [coordinate_ofCoordinates] using h)

/-- Constructor-normal ambient inverse coordinates have a single negative coefficient. -/
@[simp↓]
theorem coeff_ofCoordinates_inv_coordinate (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (i : K)
    (h : (x i : F)⁻¹ ∈ (ofCoordinates x hx).range) :
    (ofCoordinates x hx).coeff ⟨(x i : F)⁻¹, h⟩ =
      Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_ofCoordinates_inv_coordinate, AddMonoidAlgebra.coeff_single]

end Field

end TauCeti.LaurentChart
