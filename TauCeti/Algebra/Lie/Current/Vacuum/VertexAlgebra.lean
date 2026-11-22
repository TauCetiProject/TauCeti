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
`V` has unique divisibility, for instance over a field of characteristic zero, the reconstruction
theorem `TauCeti.existsUnique_formalVertexAxioms` gives a unique formal vertex algebra on `V` with
vacuum `|0⟩`, translation `T` and

`Y(x₋₁|0⟩, z) = J^x(z)`

(`TauCeti.CurrentAlgebra.vacuumFormalVertexAxioms`). This is the **affine vertex algebra**
`V_κ(𝔤)`. Its fields are iterated `n`-th products of current fields,
`Y(xₙ b, z) = J^x(z)₍ₙ₎ Y(b, z)`, so the modes of `Y(x₋₁|0⟩, z)` are the modes `xₙ`, and the
field of every PBW monomial `x¹ₙ₁ ⋯ xᵏₙₖ|0⟩` is obtained from the current fields by `k` such
products.

The products of the generating states `x₋₁|0⟩` are computed by the commutator relations of `ĝ`:

* `x₀ y₋₁|0⟩ = [x, y]₋₁|0⟩`;
* `x₁ y₋₁|0⟩ = -a Φ(x, y) |0⟩`;
* `xₙ y₋₁|0⟩ = 0` for `n ≥ 2`.

With `Φ = -κ` and `a = 1` these are the operator product expansion
`J^x(z) J^y(w) ∼ κ(x, y) / (z - w)² + J^{[x, y]}(w) / (z - w)` of the affine vertex algebra.
These products hold over every commutative ring and at every central value, including the critical
level and `a = 0`.

## Main definitions

* `TauCeti.CurrentAlgebra.vacuumFormalVertexAxioms`: the affine vertex algebra structure on the
  vacuum module.

## Main results

* `TauCeti.CurrentAlgebra.eq_top_of_vacuum_mem_of_forall_ncoeff_currentField_apply_mem`: the
  vacuum generates the vacuum module under the modes of the current fields.
* `TauCeti.CurrentAlgebra.ncoeff_zero_currentField_ncoeff_currentField_vacuum`,
  `TauCeti.CurrentAlgebra.ncoeff_one_currentField_ncoeff_currentField_vacuum` and
  `TauCeti.CurrentAlgebra.ncoeff_currentField_ncoeff_currentField_vacuum_of_two_le`: the
  nonnegative products of the generating states.
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

/-! ### Generation by the current fields -/

variable {Φ hΦ hΦs a} in
/-- **The vacuum generates the vacuum module under the current modes.** An `R`-submodule of the
vacuum module containing `|0⟩` and stable under every mode `xₙ = J^x[[n]]` is everything. -/
theorem eq_top_of_vacuum_mem_of_forall_ncoeff_currentField_apply_mem
    {W : Submodule R (VacuumModule Φ hΦ hΦs a)} (hvac : vacuum Φ hΦ hΦs a ∈ W)
    (hW : ∀ (x : L) (n : ℤ), ∀ v ∈ W, ((J x)[[n]]) v ∈ W) : W = ⊤ := by
  refine eq_top_iff.2 fun v _ ↦ ?_
  obtain ⟨u, rfl⟩ := exists_smul_vacuum_eq v
  exact smul_mem_of_forall_ncoeff_currentField_apply_mem
    (smoothModules_quotient_orderLeftIdeal Φ hΦ hΦs a 0) hW u hvac

/-! ### Products of the generating states -/

/-- A nonnegative mode on a generating state is its commutator with `y₋₁` on the vacuum:
`xₙ y₋₁|0⟩ = [x, y]ₙ₋₁|0⟩ + δ_{n, 1} (-a Φ(x, y)) |0⟩` for `n ≥ 0`. -/
private theorem ncoeff_currentField_ncoeff_currentField_vacuum_of_nonneg (x y : L) {n : ℤ}
    (hn : 0 ≤ n) :
    ((J x)[[n]]) (((J y)[[-1]]) (vacuum Φ hΦ hΦs a)) =
      ((J ⁅x, y⁆)[[n - 1]]) (vacuum Φ hΦ hΦs a) +
        (if n - 1 = 0 then -(a * Φ x y) else 0) • vacuum Φ hΦ hΦs a := by
  have h := LinearMap.congr_fun (ncoeff_currentField_mul_sub_mul Φ a
    ((isSmooth_envelopingAction_iff Φ hΦ hΦs a).2
      (smoothModules_quotient_orderLeftIdeal Φ hΦ hΦs a 0))
    (envelopingAction_mul_sub_mul Φ hΦ hΦs a) x y n (-1)) (vacuum Φ hΦ hΦs a)
  -- The commutator applied to the vacuum, where `xₙ|0⟩ = 0`.
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, ncoeff_currentField_vacuum_eq_zero x hn,
    map_zero, sub_zero, LinearMap.add_apply, Module.algebraMap_end_apply, ← sub_eq_add_neg] at h
  rw [h]
  split_ifs <;> simp

-- Not a simp lemma: the simp normal form of a mode `J^x[[n]]` is the action of its current
-- (`ncoeff_currentField`).
/-- **The zeroth product of generating states is the bracket:** `x₀ y₋₁|0⟩ = [x, y]₋₁|0⟩`. -/
theorem ncoeff_zero_currentField_ncoeff_currentField_vacuum (x y : L) :
    ((J x)[[0]]) (((J y)[[-1]]) (vacuum Φ hΦ hΦs a)) =
      ((J ⁅x, y⁆)[[-1]]) (vacuum Φ hΦ hΦs a) := by
  simp [ncoeff_currentField_ncoeff_currentField_vacuum_of_nonneg Φ hΦ hΦs a x y le_rfl,
    -ncoeff_currentField]

/-- **The first product of generating states is the level:** `x₁ y₋₁|0⟩ = -a Φ(x, y) |0⟩`.
For `Φ = -κ` and `a = 1` this is `κ(x, y) |0⟩`. -/
theorem ncoeff_one_currentField_ncoeff_currentField_vacuum (x y : L) :
    ((J x)[[1]]) (((J y)[[-1]]) (vacuum Φ hΦ hΦs a)) = -(a * Φ x y) • vacuum Φ hΦ hΦs a := by
  simp [ncoeff_currentField_ncoeff_currentField_vacuum_of_nonneg Φ hΦ hΦs a x y zero_le_one,
    ncoeff_currentField_vacuum_eq_zero _ le_rfl, -ncoeff_currentField]

/-- **The higher products of generating states vanish:** `xₙ y₋₁|0⟩ = 0` for `n ≥ 2`. -/
theorem ncoeff_currentField_ncoeff_currentField_vacuum_of_two_le (x y : L) {n : ℤ}
    (hn : 2 ≤ n) : ((J x)[[n]]) (((J y)[[-1]]) (vacuum Φ hΦ hΦs a)) = 0 := by
  simp [ncoeff_currentField_ncoeff_currentField_vacuum_of_nonneg Φ hΦ hΦs a x y (by omega : 0 ≤ n),
    ncoeff_currentField_vacuum_eq_zero _ (by omega : 0 ≤ n - 1), show n - 1 ≠ 0 by omega,
    -ncoeff_currentField]

/-! ### The affine vertex algebra -/

variable [HasUniqueDiv (VacuumModule Φ hΦ hΦs a)]

/-- The **affine vertex algebra** structure on the vacuum module: the formal vertex algebra
reconstructed from the current fields, with vacuum `|0⟩`, translation `T = -d/dt` and
`Y(x₋₁|0⟩, z) = J^x(z)`. It exists when the vacuum module has unique divisibility, for instance
over a field of characteristic zero. -/
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

/-! ### Fields of characteristic zero -/

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
variable (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)

/-- Over a field of characteristic zero the vacuum module has unique divisibility, so it carries
the affine vertex algebra structure `vacuumFormalVertexAxioms`. -/
instance : HasUniqueDiv (VacuumModule Φ hΦ hΦs a) :=
  .of_isTorsionFree K _

end TauCeti.CurrentAlgebra
