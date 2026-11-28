/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.Solvable.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
import TauCeti.Algebra.Lie.Reductive.Decomposition
import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# Central and derived parts of fixed reductive Lie algebras

An automorphism of a Lie algebra `L` whose centre and derived ideal are complementary
(`L = Z(L) ⊕ [L, L]`) preserves both summands. Consequently a fixed vector has a unique
decomposition into a fixed central vector and a fixed vector of the ambient derived ideal
(`LieEquiv.existsUnique_fixed_center_add_fixed_derivedSeries_of_isCompl`), the fixed subalgebra
splits as the supremum of its central and derived parts
(`LieEquiv.fixedSubalgebra_eq_sup_inf_center_inf_derivedSeries`), and addition gives a Lie algebra
equivalence from the product of these two fixed subalgebras to the full fixed algebra
(`LieEquiv.fixedCenterDerivedEquivOfIsCompl`).

This keeps the fixed central summand separate from a presentation of the remaining fixed
algebra. The latter is the fixed part of the **ambient** derived ideal, not by definition the
derived ideal of the fixed algebra. No finite-order hypothesis on the automorphism is needed.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §19.
-/

public section

open LieAlgebra

namespace LieEquiv

section Ring

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

private noncomputable def fixedSubmoduleLinearEquiv (e : L ≃ₗ⁅R⁆ L) {I : LieIdeal R L}
    (f : I ≃ₗ⁅R⁆ I) (hf : ∀ x : I, (f x : L) = e x) :
    ↥(e.toLieHom.fixedSubalgebra ⊓ I.toLieSubalgebra) ≃ₗ[R]
      Module.End.eigenspace (f.toLinearEquiv : Module.End R I) 1 where
  toFun x := ⟨⟨(x : L), x.property.2⟩, by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact Subtype.ext ((hf _).trans (LieHom.mem_fixedSubalgebra.mp x.property.1))⟩
  invFun s := ⟨(s.val : L),
    ⟨LieHom.mem_fixedSubalgebra.mpr <| by
      simpa [hf] using congrArg Subtype.val
        ((Module.End.mem_eigenspace_iff.mp s.property).trans (one_smul _ _)),
      s.val.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

@[simp]
private theorem coe_fixedSubmoduleLinearEquiv_apply (e : L ≃ₗ⁅R⁆ L) {I : LieIdeal R L}
    (f : I ≃ₗ⁅R⁆ I) (hf : ∀ x : I, (f x : L) = e x)
    (x : ↥(e.toLieHom.fixedSubalgebra ⊓ I.toLieSubalgebra)) :
    ((fixedSubmoduleLinearEquiv e f hf x).val : L) = (x : L) :=
  rfl

private noncomputable def fixedCenterDerivedLinearEquiv (e : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    (↥(e.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ×
      ↥(e.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra)) ≃ₗ[R]
        e.toLieHom.fixedSubalgebra :=
  ((fixedSubmoduleLinearEquiv e e.centerCongr e.coe_centerCongr |>.prodCongr
      (fixedSubmoduleLinearEquiv e (e.derivedSeriesCongr 1) (e.coe_derivedSeriesCongr 1))).trans
    (e.eigenspaceCenterDerivedEquiv h 1)).trans
    (LinearEquiv.ofEq _ e.toLieHom.fixedSubalgebra.toSubmodule
      (by
        rw [Module.End.eigenspace_one_eq_fixedSubmodule]
        ext v
        exact LinearMap.mem_fixedSubmodule_iff.trans LieHom.mem_fixedSubalgebra.symm))

private theorem coe_fixedCenterDerivedLinearEquiv_apply (e : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1))
    (p : ↥(e.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ×
      ↥(e.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra)) :
    ((e.fixedCenterDerivedLinearEquiv h p : e.toLieHom.fixedSubalgebra) : L) =
      (p.1 : L) + p.2 := by
  rw [fixedCenterDerivedLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  simp

/-- When `L = Z(L) ⊕ [L, L]`, addition identifies the fixed algebra with the product of its fixed
central part and the fixed part of the ambient derived ideal. -/
noncomputable def fixedCenterDerivedEquivOfIsCompl (e : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    (↥(e.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ×
      ↥(e.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra)) ≃ₗ⁅R⁆
        e.toLieHom.fixedSubalgebra :=
  LieEquiv.ofBijective
    { __ := (e.fixedCenterDerivedLinearEquiv h).toLinearMap
      map_lie' := by
        intro p q
        ext
        have hz (z : center R L) (y : L) : ⁅y, (z : L)⁆ = 0 :=
          (LieModule.mem_maxTrivSubmodule R L L z).mp z.property y
        have hcross : ⁅(p.1 : L), (q.2 : L)⁆ = 0 := by
          rw [← lie_skew, hz ⟨(p.1 : L), p.1.property.2⟩, neg_zero]
        simp only [LieSubalgebra.coe_bracket, AddHom.toFun_eq_coe,
          LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          e.coe_fixedCenterDerivedLinearEquiv_apply h]
        simp [lie_add, add_lie, hz ⟨(q.1 : L), q.1.property.2⟩, hcross] }
    (e.fixedCenterDerivedLinearEquiv h).bijective

/-- The fixed-part decomposition is addition in the ambient Lie algebra. -/
@[simp]
theorem fixedCenterDerivedEquivOfIsCompl_apply (e : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1))
    (p : ↥(e.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ×
      ↥(e.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra)) :
    (e.fixedCenterDerivedEquivOfIsCompl h p : L) = (p.1 : L) + p.2 :=
  e.coe_fixedCenterDerivedLinearEquiv_apply h p

/-- The inverse decomposition recovers a fixed vector by adding its two components. -/
@[simp]
theorem fixedCenterDerivedEquivOfIsCompl_symm_add (e : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1))
    (x : e.toLieHom.fixedSubalgebra) :
    ((e.fixedCenterDerivedEquivOfIsCompl h |>.symm x).1 : L) +
      (e.fixedCenterDerivedEquivOfIsCompl h |>.symm x).2 = x := by
  rw [← fixedCenterDerivedEquivOfIsCompl_apply e h, LieEquiv.apply_symm_apply]

/-- Every fixed vector has a unique decomposition into a fixed central vector and a fixed
vector in the ambient derived ideal, whenever `L = Z(L) ⊕ [L, L]`. -/
theorem existsUnique_fixed_center_add_fixed_derivedSeries_of_isCompl (e : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) (x : e.toLieHom.fixedSubalgebra) :
    ∃! p : (center R L) × derivedSeries R L 1,
      e p.1 = p.1 ∧ e p.2 = p.2 ∧ (p.1 : L) + p.2 = x := by
  let p := (e.fixedCenterDerivedEquivOfIsCompl h).symm x
  refine ⟨(⟨(p.1 : L), p.1.property.2⟩, ⟨(p.2 : L), p.2.property.2⟩),
    ⟨LieHom.mem_fixedSubalgebra.mp p.1.property.1,
      LieHom.mem_fixedSubalgebra.mp p.2.property.1,
      e.fixedCenterDerivedEquivOfIsCompl_symm_add h x⟩, ?_⟩
  intro q hq
  apply (LieIdeal.prodEquivOfIsCompl (center R L) (derivedSeries R L 1) h).injective
  simpa [p] using hq.2.2.trans (e.fixedCenterDerivedEquivOfIsCompl_symm_add h x).symm

/-- When `L = Z(L) ⊕ [L, L]`, the fixed subalgebra splits as the supremum of its central and
derived parts. -/
theorem fixedSubalgebra_eq_sup_inf_center_inf_derivedSeries (e : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    e.toLieHom.fixedSubalgebra =
      (e.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ⊔
        (e.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  obtain ⟨p, hp, _⟩ := e.existsUnique_fixed_center_add_fixed_derivedSeries_of_isCompl h ⟨x, hx⟩
  have hz : (p.1 : L) ∈ e.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra :=
    ⟨LieHom.mem_fixedSubalgebra.mpr hp.1, p.1.property⟩
  have hd : (p.2 : L) ∈ e.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra :=
    ⟨LieHom.mem_fixedSubalgebra.mpr hp.2.1, p.2.property⟩
  have hadd : (p.1 : L) + p.2 = x := hp.2.2
  rw [← hadd]
  exact LieSubalgebra.add_mem _ (le_sup_left (a := e.toLieHom.fixedSubalgebra ⊓
      (center R L).toLieSubalgebra) hz)
    (le_sup_right (b := e.toLieHom.fixedSubalgebra ⊓
      (derivedSeries R L 1).toLieSubalgebra) hd)

end Ring

end LieEquiv
