/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Center
public import TauCeti.LinearAlgebra.Projectivization.Action

/-!
# The faithful projective action of the symplectic group

The kernel of the action of `Sp₂ₘ(K)` on projective points is precisely its center. Thus the
quotient by the center acts faithfully on the same projective space, in every characteristic.
This supplies the faithful action used in simplicity criteria for projective symplectic groups;
primitivity and perfectness are separate requirements.

The quotient action follows Mathlib's `Projectivization.PSLAction.toPermHom` construction for
the special linear group. The center calculation is the one in `Symplectic/Center`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups*, Chapter 8.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace TauCeti.GLSymplecticFin

variable {m : ℕ} {K : Type*} [Field K]

/-- A symplectic element fixes every projective point exactly when it is central. -/
theorem forall_projective_smul_eq_iff_mem_center (g : GLSymplecticFin m K) :
    (∀ p : ℙ K (Fin (m + m) → K), g • p = p) ↔
      g ∈ Subgroup.center (GLSymplecticFin m K) := by
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := (Projectivization.forall_smul_eq_iff_exists_smul g).mp hg
    have hscalar : (g.val : Matrix _ _ K) = Matrix.scalar (Fin (m + m)) c := by
      ext i j
      have hcol := hc (Pi.single j 1)
      simp only [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec,
        Matrix.mulVec_single_one] at hcol
      simpa only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        Matrix.scalar_apply, Matrix.diagonal_apply, mul_ite, mul_one, mul_zero] using
        congrFun hcol i
    exact mem_center_of_val_eq_scalar hscalar
  · intro hg
    by_cases hm : m = 0
    · subst m
      intro p
      induction p using Projectivization.ind with | _ v hv =>
      exact (hv (funext fun i ↦ Fin.elim0 i)).elim
    obtain ⟨c, hc, -⟩ := (mem_center_iff hm g).mp hg
    apply (Projectivization.forall_smul_eq_iff_exists_smul g).mpr
    refine ⟨c, fun v ↦ ?_⟩
    simp only [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec, hc,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec]

/-- The permutation action on projective points has exactly the symplectic center as kernel. -/
theorem ker_projective_toPermHom :
    (MulAction.toPermHom (GLSymplecticFin m K) (ℙ K (Fin (m + m) → K))).ker =
      Subgroup.center (GLSymplecticFin m K) := by
  ext g
  simp only [MonoidHom.mem_ker, MulAction.toPermHom_apply, Equiv.Perm.ext_iff,
    MulAction.toPerm_apply, Equiv.Perm.one_apply]
  exact forall_projective_smul_eq_iff_mem_center g

/-- The symplectic action on projective space, factored through the quotient by its center. -/
def projectiveToPermHom :
    (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K)) →*
      Equiv.Perm (ℙ K (Fin (m + m) → K)) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) ker_projective_toPermHom.symm.le

/-- On a represented coset, the projective permutation is the original symplectic action. -/
@[simp]
theorem projectiveToPermHom_mk (g : GLSymplecticFin m K) :
    projectiveToPermHom (QuotientGroup.mk g) = MulAction.toPermHom _ _ g :=
  QuotientGroup.lift_mk _ _ g

instance : MulAction (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K))
    (ℙ K (Fin (m + m) → K)) :=
  MulAction.compHom _ projectiveToPermHom

/-- Quotienting by the center does not change how a symplectic element acts on a line. -/
@[simp]
theorem quotient_center_mk_smul (g : GLSymplecticFin m K)
    (p : ℙ K (Fin (m + m) → K)) :
    (QuotientGroup.mk g : GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K)) • p =
      g • p := (rfl)

/-- The projective permutation representation of the central quotient is injective. -/
theorem projectiveToPermHom_injective :
    Function.Injective (projectiveToPermHom (m := m) (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, projectiveToPermHom, QuotientGroup.ker_lift,
    ker_projective_toPermHom, QuotientGroup.map_mk'_self]

instance : FaithfulSMul (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K))
    (ℙ K (Fin (m + m) → K)) where
  eq_of_smul_eq_smul h := projectiveToPermHom_injective (Equiv.ext h)

end TauCeti.GLSymplecticFin
