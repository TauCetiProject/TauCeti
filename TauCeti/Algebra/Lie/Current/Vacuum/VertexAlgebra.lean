/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Vacuum.VectorField
public import TauCeti.Algebra.Vertex.Reconstruction

/-!
# The vertex algebra structure on the vacuum module

Let `V = U / I₀` be the vacuum module of the residue central extension `ĝ = L((t)) ⊕ R K` of an
invariant symmetric form `Φ` at the central value `a` (`TauCeti.CurrentAlgebra.VacuumModule`), with
vacuum `|0⟩`, translation operator `T = -d/dt` and current fields `J^x(z) = ∑ₙ xₙ z^{-n-1}`. For
`a = 1` and `Φ = -κ` this is the vacuum module `V_κ(𝔤)` of the affine Kac--Moody algebra at
level `κ`.

The current fields are translation covariant, `[T, J^x(z)] = ∂_z J^x(z)`, and mutually local of
order `2`. They also generate `V` from the vacuum: an `R`-submodule containing `|0⟩` and stable
under every mode `xₙ` is all of `V`
(`TauCeti.CurrentAlgebra.eq_top_of_vacuum_mem_of_forall_ncoeff_currentField_apply_mem`). So when
`V` has unique divisibility, for instance over a `ℚ`-algebra, the reconstruction
theorem `TauCeti.existsUnique_formalVertexAxioms` gives a unique formal vertex algebra on `V` with
vacuum `|0⟩`, translation `T` and

`Y(x₋₁|0⟩, z) = J^x(z)`

(`TauCeti.CurrentAlgebra.vacuumFormalVertexAxioms`). This is the **affine vertex algebra**
`V_κ(𝔤)`. Its fields are iterated `n`-th products of current fields,
`Y(xₙ b, z) = J^x(z)₍ₙ₎ Y(b, z)`, so the modes of `Y(x₋₁|0⟩, z)` are the modes `xₙ`, and the
field of every PBW monomial `x¹ₙ₁ ⋯ xᵏₙₖ|0⟩` is obtained from the current fields by `k` such
products.

In particular the products of the generating states `x₋₁|0⟩` in this vertex algebra are the
vacuum module identities of `TauCeti.Algebra.Lie.Current.Vacuum.Basic`:

* `x₀ y₋₁|0⟩ = [x, y]₋₁|0⟩`
  (`TauCeti.CurrentAlgebra.ncoeff_zero_currentField_ncoeff_currentField_vacuum`);
* `x₁ y₋₁|0⟩ = -a Φ(x, y) |0⟩`
  (`TauCeti.CurrentAlgebra.ncoeff_one_currentField_ncoeff_currentField_vacuum`);
* `xₙ y₋₁|0⟩ = 0` for `n ≥ 2`
  (`TauCeti.CurrentAlgebra.ncoeff_currentField_ncoeff_currentField_vacuum_eq_zero_of_two_le`).

With `Φ = -κ` and `a = 1` these are the operator product expansion
`J^x(z) J^y(w) ∼ κ(x, y) / (z - w)² + J^{[x, y]}(w) / (z - w)` of the affine vertex algebra.

## Main definitions

* `TauCeti.CurrentAlgebra.vacuumFormalVertexAxioms`: the affine vertex algebra structure on the
  vacuum module.

## Main results

* `TauCeti.CurrentAlgebra.vacuumFormalVertexAxioms_field_ncoeff_currentField_vacuum`:
  `Y(x₋₁|0⟩, z) = J^x(z)`.
* `TauCeti.CurrentAlgebra.vacuumFormalVertexAxioms_field_ncoeff_currentField_apply`:
  `Y(xₙ b, z) = J^x(z)₍ₙ₎ Y(b, z)`.
* `TauCeti.CurrentAlgebra.eq_vacuumFormalVertexAxioms`: any formal vertex algebra on the vacuum
  module with vacuum `|0⟩`, translation `T` and `Y(x₋₁|0⟩, z) = J^x(z)` is the affine one.

## References

* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4, for the affine
  vertex algebra structure on the vacuum module and its operator product expansion.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §§2.2.4–2.2.5 and Theorem 2.2.2, for
  the vertex algebra `V_κ(𝔤)` obtained from the reconstruction theorem.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.7, for the affine vertex algebras.
-/

public section

noncomputable section

open scoped LaurentSeries VertexOperator
open LieAlgebra TauCeti.UniversalEnvelopingAlgebra VertexOperator
open LieAlgebra.ofTwoCocycle (centralElement)

attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

section Vacuum

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "J" => currentField (envelopingAction (M := VacuumModule Φ hΦ hΦs a) Φ hΦ hΦs a)
  (Iff.mpr (isSmooth_envelopingAction_iff Φ hΦ hΦs a)
    (smoothModules_quotient_orderLeftIdeal Φ hΦ hΦs a 0))

/-! ### The affine vertex algebra -/

variable [HasUniqueDiv (VacuumModule Φ hΦ hΦs a)]

/-- The **affine vertex algebra** structure on the vacuum module: the formal vertex algebra
reconstructed from the current fields, with vacuum `|0⟩`, translation `T = -d/dt` and
`Y(x₋₁|0⟩, z) = J^x(z)`. It exists when the vacuum module has unique divisibility, for instance
over a `ℚ`-algebra. -/
def vacuumFormalVertexAxioms : FormalVertexAxioms R (VacuumModule Φ hΦ hΦs a) :=
  FormalVertexAxioms.ofGeneratingFields (F := J) vacuumTranslation_vacuum
    (fun x n ↦ by
      rw [lie_vacuumTranslation_ncoeff_currentField, ncoeff_derivative, neg_smul]
      ext v
      simp [← Int.cast_smul_eq_zsmul R])
    (fun x y ↦ ⟨2, isLocalOfOrder_currentField_envelopingAction Φ hΦ hΦs a
      (smoothModules_quotient_orderLeftIdeal Φ hΦ hΦs a 0) x y⟩)
    (fun _ hvac hW ↦ eq_top_of_vacuum_mem_of_forall_ncoeff_currentField_apply_mem hvac hW)

/-- The vacuum of the affine vertex algebra is the vacuum vector `|0⟩`. -/
@[simp]
theorem vacuumFormalVertexAxioms_vacuum :
    (vacuumFormalVertexAxioms Φ hΦ hΦs a).vacuum = vacuum Φ hΦ hΦs a :=
  FormalVertexAxioms.ofGeneratingFields_vacuum ..

/-- The translation operator of the affine vertex algebra is `T = -d/dt`. -/
@[simp]
theorem vacuumFormalVertexAxioms_translation :
    (vacuumFormalVertexAxioms Φ hΦ hΦs a).translation = vacuumTranslation Φ hΦ hΦs a :=
  FormalVertexAxioms.ofGeneratingFields_translation ..

-- Not a simp lemma: the simp normal form of a mode `J^x[[n]]` is the action of its current
-- (`ncoeff_currentField`).
/-- The field of the generating state `x₋₁|0⟩` is the current field: `Y(x₋₁|0⟩, z) = J^x(z)`. -/
theorem vacuumFormalVertexAxioms_field_ncoeff_currentField_vacuum (x : L) :
    (vacuumFormalVertexAxioms Φ hΦ hΦs a).field (((J x)[[-1]]) (vacuum Φ hΦ hΦs a)) = J x :=
  FormalVertexAxioms.ofGeneratingFields_field_ncoeff_neg_one_apply_vacuum ..

/-- The fields of the affine vertex algebra are iterated products of current fields:
`Y(xₙ b, z) = J^x(z)₍ₙ₎ Y(b, z)`. -/
theorem vacuumFormalVertexAxioms_field_ncoeff_currentField_apply (x : L) (n : ℤ)
    (b : VacuumModule Φ hΦ hΦs a) :
    (vacuumFormalVertexAxioms Φ hΦ hΦs a).field (((J x)[[n]]) b) =
      nthProduct n (J x) ((vacuumFormalVertexAxioms Φ hΦ hΦs a).field b) :=
  FormalVertexAxioms.ofGeneratingFields_field_ncoeff_apply ..

variable {Φ hΦ hΦs a} in
/-- **Uniqueness of the affine vertex algebra.** A formal vertex algebra on the vacuum module with
vacuum `|0⟩`, translation `T = -d/dt` and `Y(x₋₁|0⟩, z) = J^x(z)` for every `x` is
`vacuumFormalVertexAxioms`. -/
theorem eq_vacuumFormalVertexAxioms {A : FormalVertexAxioms R (VacuumModule Φ hΦ hΦs a)}
    (hvac : A.vacuum = vacuum Φ hΦ hΦs a) (htr : A.translation = vacuumTranslation Φ hΦ hΦs a)
    (hJ : ∀ x : L, A.field (((J x)[[-1]]) (vacuum Φ hΦ hΦs a)) = J x) :
    A = vacuumFormalVertexAxioms Φ hΦ hΦs a :=
  FormalVertexAxioms.eq_ofGeneratingFields _ _ _ _ hvac htr hJ

end Vacuum

/-! ### `ℚ`-algebras -/

variable {R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

/-- Over a `ℚ`-algebra the vacuum module has unique divisibility, so it carries the affine vertex
algebra structure `vacuumFormalVertexAxioms`. -/
instance : HasUniqueDiv (VacuumModule Φ hΦ hΦs a) :=
  letI : Module ℚ (VacuumModule Φ hΦ hΦs a) := Module.compHom _ (algebraMap ℚ R)
  HasUniqueDiv.of_module_rat _

end TauCeti.CurrentAlgebra
