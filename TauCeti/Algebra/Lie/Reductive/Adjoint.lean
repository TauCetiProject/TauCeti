/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.Submodule.Orthogonal
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Semisimple
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal.Complement

/-!
# Reductivity from closure under adjoints

A finite-dimensional Lie algebra with an anisotropic bilinear form splits orthogonally as its
centre and a semisimple derived algebra if the left adjoint of every inner derivation is again
inner. For a real inner product, a left adjoint is the usual adjoint by symmetry. For example,
in a transpose-stable real matrix Lie algebra with the Frobenius inner product, the adjoint of
`ad X` is `ad Xᵀ`.

The criterion uses orthogonal complements of ideals. It does not require the inner product itself
to be Lie-invariant. See A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Ch. VII §2
for the application to real reductive Lie algebras.
-/

public section

namespace LinearMap.BilinForm

open LieAlgebra LieSubmodule

/-- If the left adjoint of each inner derivation is inner, the derived ideal is right
orthogonal to the centre. -/
theorem derivedSeries_one_le_orthogonal_center_of_exists_adjoint {R L : Type*}
    [CommRing R] [LieRing L] [LieAlgebra R L] (B : LinearMap.BilinForm R L)
    (h : ∀ x : L, ∃ x' : L, ∀ y z : L, B ⁅x', y⁆ z = B y ⁅x, z⁆) :
    derivedSeries R L 1 ≤ (center R L).orthogonalOfExistsAdjoint B h := by
  simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, lie_le_iff, mem_top,
    true_implies]
  intro y z
  rw [mem_orthogonalOfExistsAdjoint_iff]
  intro u hu
  obtain ⟨y', hy'⟩ := h y
  rw [← hy', (LieModule.mem_maxTrivSubmodule R L L u).mp hu y', map_zero, LinearMap.zero_apply]

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  (B : LinearMap.BilinForm K L) (hB : B.toQuadraticMap.Anisotropic)
  (h : ∀ x : L, ∃ x' : L, ∀ y z : L, B ⁅x', y⁆ z = B y ⁅x, z⁆)

include hB h

/-- The centre and the derived ideal are complementary for an anisotropic form with respect to
which the left adjoint of each inner derivation is inner. -/
theorem isCompl_center_derivedSeries_one_of_exists_adjoint :
    IsCompl (center K L) (derivedSeries K L 1) := by
  let D := derivedSeries K L 1
  let J := D.orthogonalOfExistsAdjoint B h
  have hD : IsCompl D J := D.isCompl_orthogonalOfExistsAdjoint B h
    (B.nondegenerate_restrict_of_anisotropic hB D.toSubmodule)
  have hJ : J ≤ center K L := by
    intro x hx
    apply (LieModule.mem_maxTrivSubmodule K L L x).mpr
    intro y
    have hd : ⁅y, x⁆ ∈ D := by
      simpa [D] using lie_mem_lie (I := (⊤ : LieIdeal K L)) (N := (⊤ : LieIdeal K L))
        (mem_top y) (mem_top x)
    exact (LieSubmodule.mem_bot ⁅y, x⁆).mp (hD.disjoint.le_bot ⟨hd, J.lie_mem hx⟩)
  have hdis : Disjoint (center K L) D :=
    ((center K L).isCompl_orthogonalOfExistsAdjoint B h
      (B.nondegenerate_restrict_of_anisotropic hB (center K L).toSubmodule)).disjoint.mono_right
      (B.derivedSeries_one_le_orthogonal_center_of_exists_adjoint h)
  have hEq : J = center K L := by
    symm
    calc
      center K L = (J ⊔ D) ⊓ center K L := by rw [hD.symm.sup_eq_top, top_inf_eq]
      _ = J := by rw [sup_inf_assoc_of_le D hJ, inf_comm D, hdis.eq_bot, sup_bot_eq]
  exact hEq ▸ hD.symm

/-- The derived Lie algebra is semisimple for an anisotropic form with respect to which the
left adjoint of each inner derivation is inner. -/
theorem isSemisimple_derivedSeries_one_of_exists_adjoint :
    LieAlgebra.IsSemisimple K (derivedSeries K L 1) := by
  let D := derivedSeries K L 1
  have hCD := B.isCompl_center_derivedSeries_one_of_exists_adjoint hB h
  let BD : LinearMap.BilinForm K D := B.compl₁₂ D.incl.toLinearMap D.incl.toLinearMap
  have hBD := B.anisotropic_toQuadraticMap_compl₁₂ hB D.incl.toLinearMap D.incl_injective
  have hD (x : D) : ∃ x' : D, ∀ y z : D, BD ⁅x', y⁆ z = BD y ⁅x, z⁆ := by
    obtain ⟨w, hw⟩ := h x
    have hwmem : w ∈ center K L ⊔ D := hCD.sup_eq_top ▸ mem_top w
    obtain ⟨c, hc, d, hd, rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hwmem
    have hc' (y : L) : ⁅c, y⁆ = 0 := by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule K L L c).mp hc y, neg_zero]
    refine ⟨⟨d, hd⟩, fun y z ↦ ?_⟩
    simp only [BD, LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, LieHom.map_lie]
    simpa only [LieIdeal.incl_apply, add_lie, hc', zero_add] using hw (y : L) (z : L)
  let : ComplementedLattice (LieIdeal K D) := ⟨fun I ↦
    ⟨I.orthogonalOfExistsAdjoint BD hD, I.isCompl_orthogonalOfExistsAdjoint BD hD
      (BD.nondegenerate_restrict_of_anisotropic hBD I.toSubmodule)⟩⟩
  exact TauCeti.isSemisimple_of_sSup_atoms_eq_top_of_center_eq_bot sSup_atoms_eq_top
    (D.center_eq_bot_of_isCompl_center hCD)

end LinearMap.BilinForm
