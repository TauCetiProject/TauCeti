/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Basic
public import Mathlib.GroupTheory.Index

/-!
# Cusps and finite-index subgroups

A boundary point is parabolic for a finite-index subgroup exactly when it is parabolic for the
larger group. A positive power of a parabolic element fixing the point lies in the smaller
group. Consequently the two groups have the same cusp points, although their cusp orbit sets
can differ. The fibre of the cusp-orbit map is therefore the full boundary-orbit fibre. This
is the projective counterpart of Mathlib's `IsCusp.of_isFiniteRelIndex` for subgroups of
`GL(2, ℝ)`.

The positive-power argument follows `Mathlib/NumberTheory/ModularForms/Cusps.lean`, adapted to
Tau Ceti's effective projective action and cusp-point carrier.
-/

public noncomputable section

open MulAction
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)} [Δ.IsFiniteRelIndex Γ]

/-- A cusp point of a group is a cusp point of every finite-index subgroup. -/
theorem IsCuspPoint.of_isFiniteRelIndex {c : OnePoint ℝ}
    (hc : Γ.IsCuspPoint c) : Δ.IsCuspPoint c := by
  obtain ⟨g, hmem, hg⟩ := isCuspPoint_iff_exists_mem_stabilizer_isParabolic.mp hc
  have hgc : g • c = c := mem_stabilizer_iff.mp hmem
  have hgc' : (g : PSL(2, ℝ)) • c = c := by
    simpa only [Subgroup.smul_def] using hgc
  obtain ⟨n, hn, -, hpow⟩ :=
    Subgroup.exists_pow_mem_of_relIndex_ne_zero Δ.relIndex_ne_zero g.property
  apply isCuspPoint_iff_exists_mem_stabilizer_isParabolic.mpr
  refine ⟨⟨(g : PSL(2, ℝ)) ^ n, hpow.1⟩, ?_, hg.pow hn.ne'⟩
  apply mem_stabilizer_iff.mpr
  have hp (m : ℕ) : (g : PSL(2, ℝ)) ^ m • c = c := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_smul, hgc', ih]
  simpa only [Subgroup.smul_def, Subgroup.coe_mk] using hp n

/-- Finite-index subgroups have exactly the cusp points of the containing group. -/
theorem isCuspPoint_iff_of_isFiniteRelIndex (h : Δ ≤ Γ) {c : OnePoint ℝ} :
    Δ.IsCuspPoint c ↔ Γ.IsCuspPoint c :=
  ⟨IsCuspPoint.mono h, IsCuspPoint.of_isFiniteRelIndex⟩

variable (h : Δ ≤ Γ)

/-- A boundary orbit is a cusp orbit for a finite-index subgroup exactly when its image is a
cusp orbit for the containing group. -/
theorem isCuspOrbit_iff_of_isFiniteRelIndex (q : Δ.BoundaryOrbit) :
    Δ.IsCuspOrbit q ↔ Γ.IsCuspOrbit
      (Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le
        (X := OnePoint ℝ) h) q) := by
  induction q using Quotient.inductionOn' with
  | h c =>
      simp only [TauCeti.Setoid.map_of_le_mk, isCuspOrbit_mk_iff]
      exact isCuspPoint_iff_of_isFiniteRelIndex h

/-- Every cusp orbit of the containing group has a cusp orbit above it for a finite-index
inclusion. -/
theorem cuspOrbitMap_surjective : Function.Surjective (cuspOrbitMap h) := by
  intro C
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  refine ⟨Δ.cuspOrbitMk
    ⟨c, mem_cuspPoints.mpr (IsCuspPoint.of_isFiniteRelIndex
      (mem_cuspPoints.mp c.property))⟩, ?_⟩
  simp

/-- A cusp-orbit fibre is the full boundary-orbit fibre over the same cusp. -/
def cuspOrbitFiberEquivBoundaryOrbitFiber (C : Γ.CuspOrbit) :
    {D : Δ.CuspOrbit // cuspOrbitMap h D = C} ≃
      {q : Δ.BoundaryOrbit //
        Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le
          (X := OnePoint ℝ) h) q = C.1} where
  toFun D := ⟨D.1.1, by simpa only [cuspOrbitMap_val] using congrArg Subtype.val D.2⟩
  invFun q := ⟨⟨q.1, (isCuspOrbit_iff_of_isFiniteRelIndex h q.1).mpr
    (q.2.symm ▸ C.property)⟩, Subtype.ext (by
      simpa only [cuspOrbitMap_val] using q.2)⟩
  left_inv D := by cases D; rfl
  right_inv q := by cases q; rfl

/-- The boundary-orbit equivalence retains the underlying orbit. -/
@[simp]
theorem cuspOrbitFiberEquivBoundaryOrbitFiber_apply (C : Γ.CuspOrbit)
    (D : {D : Δ.CuspOrbit // cuspOrbitMap h D = C}) :
    (cuspOrbitFiberEquivBoundaryOrbitFiber h C D).1 = D.1.1 :=
  (rfl)

end Subgroup
