/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Basic
public import TauCeti.RepresentationTheory.Quiver.SemisimpleQuotient
import TauCeti.RingTheory.Jacobson.MulOpposite

/-!
# The radical of a bound quiver algebra

For an admissible ideal `I` in the path algebra `kQ`, the Jacobson radical of `kQ ⧸ I`
is the image of the arrow ideal. Its semisimple quotient is therefore the product `Q → k`,
with one copy of the base field for each vertex. In particular every bound quiver algebra
is basic. These identifications supply the vertex coordinates for the simple modules and
the radical filtration used in presentations of finite-dimensional algebras.

Unlike the corresponding assertion for `kQ` itself, the radical identification needs no
acyclicity: admissibility makes every image of an element of the arrow ideal nilpotent.
Only the vertex set must be finite; finiteness of the arrow types is not needed here.

The constructions use `TauCeti.PathAlgebra.trivialCoeff` and its kernel computation,
and `TauCeti.IsAdmissibleIdeal.isNilpotent_mk_of_mem_arrowIdeal`.
The mathematical reference is Assem–Simson–Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Chapter II, §2.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

namespace IsAdmissibleIdeal

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Finite Q]
variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

/-- The Jacobson radical of a bound quiver algebra is the image of the arrow ideal. -/
theorem jacobson_eq_map_arrowIdeal (h : IsAdmissibleIdeal I) :
    Ring.jacobson (pathAlgebra k Q ⧸ I) = (arrowIdeal k Q).map (Ideal.Quotient.mk I) := by
  let f := quotientTrivialCoeff h.le_arrowIdeal
  let _ : RingHomSurjective f.toRingHom := ⟨quotientTrivialCoeff_surjective h.le_arrowIdeal⟩
  refine le_antisymm ?_ ?_
  · have hf := Ring.le_comap_jacobson (f := f.toRingHom)
    rw [IsSemisimpleRing.jacobson_eq_bot (Q → k), ← RingHom.ker_eq_comap_bot] at hf
    exact hf.trans_eq (ker_quotientTrivialCoeff h.le_arrowIdeal)
  · intro x hx
    rw [Ring.mem_jacobson_iff_isUnit_one_add_mul_left]
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, hb, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).1 hx
    rw [← map_mul]
    exact (h.isNilpotent_mk_of_mem_arrowIdeal ((arrowIdeal k Q).mul_mem_left a hb)).isUnit_one_add

/-- An element of the path algebra maps into the radical precisely when its trivial
coordinates vanish. -/
@[simp]
theorem mk_mem_jacobson_iff (h : IsAdmissibleIdeal I) (a : pathAlgebra k Q) :
    Ideal.Quotient.mk I a ∈ Ring.jacobson (pathAlgebra k Q ⧸ I) ↔ a ∈ arrowIdeal k Q := by
  rw [h.jacobson_eq_map_arrowIdeal, ← ker_quotientTrivialCoeff h.le_arrowIdeal,
    RingHom.mem_ker, quotientTrivialCoeff_mk, ← RingHom.mem_ker, ker_trivialCoeff]

/-- The semisimple quotient of a bound quiver algebra is one copy of the base field
for each vertex. -/
noncomputable def quotientJacobsonAlgEquiv (h : IsAdmissibleIdeal I) :
    ((pathAlgebra k Q ⧸ I) ⧸ Ring.jacobson (pathAlgebra k Q ⧸ I)) ≃ₐ[k] (Q → k) :=
  (Ideal.quotientEquivAlgOfEq k
    (h.jacobson_eq_map_arrowIdeal.trans (ker_quotientTrivialCoeff h.le_arrowIdeal).symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (quotientTrivialCoeff_surjective h.le_arrowIdeal))

/-- The coordinates on the semisimple quotient are the descended trivial coefficients. -/
@[simp]
theorem quotientJacobsonAlgEquiv_mk (h : IsAdmissibleIdeal I) (x : pathAlgebra k Q ⧸ I) :
    h.quotientJacobsonAlgEquiv (Ideal.Quotient.mk _ x) =
      quotientTrivialCoeff h.le_arrowIdeal x := by
  simp [quotientJacobsonAlgEquiv]

/-- Every bound quiver algebra is basic: its semisimple quotient is a product of fields,
with no matrix blocks of size greater than one. -/
theorem isBasic (h : IsAdmissibleIdeal I) : IsBasic (pathAlgebra k Q ⧸ I) := by
  rw [isBasic_def]
  exact ⟨h.quotientJacobsonAlgEquiv.toRingEquiv.symm.isSemisimpleRing,
    isReduced_of_injective h.quotientJacobsonAlgEquiv h.quotientJacobsonAlgEquiv.injective⟩

/-- The semisimple quotient of a bound quiver algebra has dimension equal to the
number of vertices. -/
theorem finrank_quotient_jacobson (h : IsAdmissibleIdeal I) :
    Module.finrank k ((pathAlgebra k Q ⧸ I) ⧸ Ring.jacobson (pathAlgebra k Q ⧸ I)) =
      Nat.card Q := by
  let := Fintype.ofFinite Q
  rw [h.quotientJacobsonAlgEquiv.toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end IsAdmissibleIdeal

end TauCeti
