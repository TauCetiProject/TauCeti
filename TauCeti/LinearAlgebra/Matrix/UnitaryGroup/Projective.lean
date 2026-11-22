/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block

/-!
# Unit scalars and the projective unitary group

Over a commutative star ring `R`, every unitary scalar `c ∈ unitary R` gives the unitary matrix
`c • 1`, and these form the central subgroup of unit scalars of `U(n) = Matrix.unitaryGroup n R`
(`Matrix.UnitaryGroup.scalarHom`). The **projective unitary group** is the quotient

`PU(n) = U(n) ⧸ {c • 1 : c ∈ unitary R}`

(`TauCeti.ProjectiveUnitaryGroup n R`). For `R = ℂ` and `n = Fin (k + 1)` it is the group
`PU(k + 1)`, which acts faithfully on complex projective space `CPᵏ` because the unit scalars are
exactly the unitary matrices acting trivially there.

The map `(c, B) ↦ c⁻¹ B = star c • B` is a surjective group morphism
`U(1) × U(n) →* U(n)` (`Matrix.UnitaryGroup.starSMulHom`), whose kernel is the diagonal circle
`{(c, c • 1)}` (`Matrix.UnitaryGroup.ker_starSMulHom`). Hence

`(U(1) × U(n)) ⧸ U(1)_diag ≃* U(n)`

(`Matrix.UnitaryGroup.prodQuotientDiagonalEquiv`). This is the shape of the stabilizer of a point
of `CPᵏ` in `PU(k + 1)`: in `U(k + 1)` that stabilizer is `U(1) × U(k)`, and passing to the
projective group divides it by the unit scalars, embedded diagonally. Correspondingly, the
block-diagonal matrix `diag(c, c • 1)` is the unit scalar `c • 1`
(`Matrix.UnitaryGroup.prodBlockSucc_scalarHom`), so in `PU(k + 1)` the class of `diag(c, B)` is the
class of `diag(1, star c • B)` (`TauCeti.ProjectiveUnitaryGroup.mk_prodBlockSucc`).

Every `1 × 1` unitary matrix is a unit scalar
(`TauCeti.ProjectiveUnitaryGroup.range_scalarHom_fin_one`), so `PU(1)` is trivial
(`TauCeti.ProjectiveUnitaryGroup.instSubsingletonFinOne`).

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

open Matrix

namespace Matrix.UnitaryGroup

variable (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] [StarRing R]

/-- The **unit scalars** `c • 1`, for `c ∈ unitary R`, as a group morphism
`unitary R →* Matrix.unitaryGroup n R`. -/
def scalarHom : unitary R →* unitaryGroup n R where
  toFun c := ⟨scalar n (c : R), by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, scalar_apply, diagonal_conjTranspose,
      diagonal_mul_diagonal]
    simp⟩
  map_one' := Subtype.ext (map_one (scalar n))
  map_mul' c d := Subtype.ext (map_mul (scalar n) (c : R) d)

variable {n R}

/-- The unit scalar of `c` is the scalar matrix `c • 1`. -/
@[simp]
theorem coe_scalarHom (c : unitary R) :
    (scalarHom n R c : Matrix n n R) = scalar n (c : R) :=
  (rfl)

/-- On a nonempty index type, distinct unitary scalars give distinct scalar matrices. -/
theorem scalarHom_injective [Nonempty n] : Function.Injective (scalarHom n R) := fun c d h ↦
  Subtype.ext <| (scalar_inj (n := n)).1 (by simpa using congrArg Subtype.val h)

/-- Unit scalars commute with every unitary matrix. -/
theorem commute_scalarHom (c : unitary R) (A : unitaryGroup n R) :
    Commute (scalarHom n R c) A :=
  Subtype.ext <| scalar_commute (c : R) (fun _ ↦ Commute.all _ _) (A : Matrix n n R)

/-- The unit scalars are central in the unitary group. -/
theorem range_scalarHom_le_center : (scalarHom n R).range ≤ Subgroup.center (unitaryGroup n R) := by
  rintro _ ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.2 fun A ↦ (commute_scalarHom c A).eq.symm

/-- The subgroup of unit scalars is normal, being central. -/
instance normal_range_scalarHom : (scalarHom n R).range.Normal :=
  Subgroup.normal_of_le_center range_scalarHom_le_center

/-- The block-diagonal matrix `diag(c, c • 1)` is the unit scalar `c • 1`. -/
@[simp]
theorem prodBlockSucc_scalarHom {m : ℕ} (c : unitary R) :
    prodBlockSucc R m (c, scalarHom (Fin m) R c) = scalarHom (Fin (m + 1)) R c := by
  refine UnitaryGroup.ext _ _ fun i j ↦ ?_
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j <;>
    simp [scalar_apply, diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

variable (n R) in
/-- The morphism `U(1) × U(n) →* U(n)`, `(c, B) ↦ c⁻¹ B = star c • B`. It is well defined as a
morphism because unit scalars are central. -/
def starSMulHom : unitary R × unitaryGroup n R →* unitaryGroup n R where
  toFun cB := scalarHom n R (star cB.1) * cB.2
  map_one' := by simp
  map_mul' cB cB' := by
    simp only [Prod.fst_mul, Prod.snd_mul, star_mul, map_mul, mul_assoc]
    rw [← mul_assoc (cB.2 : unitaryGroup n R), ← (commute_scalarHom (star cB'.1) cB.2).eq]
    simp only [← mul_assoc]
    rw [(commute_scalarHom (star cB'.1) (scalarHom n R (star cB.1))).eq]

/-- The morphism `U(1) × U(n) →* U(n)` sends `(c, B)` to `star c • B`. -/
@[simp]
theorem starSMulHom_apply (cB : unitary R × unitaryGroup n R) :
    starSMulHom n R cB = scalarHom n R (star cB.1) * cB.2 :=
  (rfl)

/-- The morphism `(c, B) ↦ star c • B` from `U(1) × U(n)` onto `U(n)` is surjective. -/
theorem starSMulHom_surjective : Function.Surjective (starSMulHom n R) :=
  fun B ↦ ⟨(1, B), by simp⟩

/-- **The kernel of `(c, B) ↦ star c • B` is the diagonal circle** `{(c, c • 1)}`, the image of the
diagonal embedding `c ↦ (c, c • 1)` of `U(1)` in `U(1) × U(n)`. -/
theorem ker_starSMulHom :
    (starSMulHom n R).ker = ((MonoidHom.id (unitary R)).prod (scalarHom n R)).range := by
  ext ⟨c, B⟩
  simp only [MonoidHom.mem_ker, starSMulHom_apply, MonoidHom.mem_range, MonoidHom.prod_apply,
    MonoidHom.id_apply, Prod.mk.injEq]
  constructor
  · intro h
    refine ⟨c, rfl, ?_⟩
    rw [← mul_one (scalarHom n R c), ← h, ← mul_assoc, ← map_mul, Unitary.mul_star_self,
      map_one, one_mul]
  · rintro ⟨d, rfl, rfl⟩
    rw [← map_mul, Unitary.star_mul_self, map_one]

/-- The diagonal circle `{(c, c • 1)}` is normal in `U(1) × U(n)`, being a kernel. -/
instance normal_range_prod_scalarHom :
    ((MonoidHom.id (unitary R)).prod (scalarHom n R)).range.Normal :=
  ker_starSMulHom (n := n) (R := R) ▸ MonoidHom.normal_ker _

variable (n R) in
/-- **`(U(1) × U(n)) ⧸ U(1)_diag ≃* U(n)`**: the quotient of `U(1) × U(n)` by the diagonal circle
`{(c, c • 1)}` is `U(n)`, through the class of `(c, B) ↦ star c • B`. -/
noncomputable def prodQuotientDiagonalEquiv :
    (unitary R × unitaryGroup n R) ⧸ ((MonoidHom.id (unitary R)).prod (scalarHom n R)).range ≃*
      unitaryGroup n R :=
  (QuotientGroup.quotientMulEquivOfEq ker_starSMulHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ starSMulHom_surjective)

/-- The isomorphism `(U(1) × U(n)) ⧸ U(1)_diag ≃* U(n)` sends the class of `(c, B)` to
`star c • B`. -/
@[simp]
theorem prodQuotientDiagonalEquiv_mk (cB : unitary R × unitaryGroup n R) :
    prodQuotientDiagonalEquiv n R (cB : (unitary R × unitaryGroup n R) ⧸
        ((MonoidHom.id (unitary R)).prod (scalarHom n R)).range) =
      scalarHom n R (star cB.1) * cB.2 :=
  (rfl)

end Matrix.UnitaryGroup

namespace TauCeti

variable (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] [StarRing R]

/-- The **projective unitary group** `PU(n) = U(n) ⧸ {c • 1 : c ∈ unitary R}`, the quotient of the
unitary group by its subgroup of unit scalars. -/
abbrev ProjectiveUnitaryGroup : Type _ :=
  unitaryGroup n R ⧸ (UnitaryGroup.scalarHom n R).range

namespace ProjectiveUnitaryGroup

variable {R}

/-- The class of `diag(c, B)` in `PU(m + 1)` is the class of `diag(1, star c • B)`. -/
theorem mk_prodBlockSucc {m : ℕ} (cB : unitary R × unitaryGroup (Fin m) R) :
    (UnitaryGroup.prodBlockSucc R m cB : ProjectiveUnitaryGroup (Fin (m + 1)) R) =
      (UnitaryGroup.prodBlockSucc R m (1, UnitaryGroup.starSMulHom (Fin m) R cB) :
        ProjectiveUnitaryGroup (Fin (m + 1)) R) := by
  -- `diag(1, star c • B)` is the product of the unit scalar `star c • 1` with `diag(c, B)`.
  have h : UnitaryGroup.prodBlockSucc R m (1, UnitaryGroup.starSMulHom (Fin m) R cB) =
      UnitaryGroup.scalarHom (Fin (m + 1)) R (star cB.1) * UnitaryGroup.prodBlockSucc R m cB := by
    rw [← UnitaryGroup.prodBlockSucc_scalarHom, ← map_mul]
    congr 1
    exact Prod.ext (Unitary.star_mul_self cB.1).symm (UnitaryGroup.starSMulHom_apply cB)
  rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨_, rfl⟩),
    one_mul]

variable (R) in
/-- Every `1 × 1` unitary matrix is a unit scalar. -/
theorem range_scalarHom_fin_one : (UnitaryGroup.scalarHom (Fin 1) R).range = ⊤ := by
  refine eq_top_iff.2 fun A _ ↦ ⟨⟨(A : Matrix (Fin 1) (Fin 1) R) 0 0, ?_⟩,
    UnitaryGroup.ext _ _ fun i j ↦ ?_⟩
  · have h := congrFun (congrFun (mem_unitaryGroup_iff'.1 A.property) 0) 0
    rw [star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_one, conjTranspose_apply,
      one_apply_eq] at h
    exact Unitary.mem_iff_star_mul_self.2 h
  · fin_cases i; fin_cases j
    simp [scalar_apply]

/-- The projective unitary group `PU(1)` is trivial. -/
instance instSubsingletonFinOne : Subsingleton (ProjectiveUnitaryGroup (Fin 1) R) where
  allEq g h := by
    induction g using QuotientGroup.induction_on with | H A =>
    induction h using QuotientGroup.induction_on with | H B =>
    exact QuotientGroup.eq.2 (range_scalarHom_fin_one R ▸ Subgroup.mem_top _)

end ProjectiveUnitaryGroup

end TauCeti
