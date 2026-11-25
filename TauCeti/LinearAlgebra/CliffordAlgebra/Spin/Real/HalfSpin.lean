/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.TorusCharacter
import TauCeti.Algebra.Algebra.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.HalfSpinor
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.RepresentationTheory.Quaternion.Complex

/-!
# Quaternion and `SU(2)` models of the compact four-dimensional half-spin representations

Under `TauCeti.realSpinFourEquivQuaternionUnitaryProd : Spin(4) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ]` and
`TauCeti.realSpinFourEquivSpecialUnitaryProd : Spin(4) ≃* SU(2) × SU(2)`, a positively oriented
orthonormal frame `b` (`hb : b.toBasis.orientation = o`) of `(V, o)` with `Q v = -‖v‖²` factors the
even Clifford actions on `W⁺` and `W⁻` into `ℝ`-algebra homomorphisms from `ℍ[ℝ]`
(`CliffordAlgebra.positiveQuaternionAction`, `CliffordAlgebra.negativeQuaternionAction`), so that
`halfSpinRep` at `b.realSpinGroupEquiv hQ s` acts via the **second** factor on `W⁺` and the
**first** factor on `W⁻`.

On a Hermitian Clifford module of half-spin rank two, both actions intertwine quaternion conjugation
with `LinearMap.adjoint`, admit orthonormal bases realizing the `SU(2)` factors as matrices, yield
closed-form `Spin(4)` and `Spinᶜ(4)` character formulas via `TauCeti.trace_quaternionAlgHom`, and
send `OrthonormalBasis.spinTorus` at `(w₁, w₂)` to the quaternion pair `(w₁ w₂⁻¹, w₁ w₂)` along
`1, k`.

## Main definitions

* `CliffordAlgebra.positiveQuaternionAction`, `CliffordAlgebra.negativeQuaternionAction`:
  `ℝ`-algebra actions of `ℍ[ℝ]` on `W⁺` (second factor) and `W⁻` (first factor).

## Main results

* `CliffordAlgebra.halfSpinRep_one_realSpinGroupEquiv_eq`,
  `CliffordAlgebra.halfSpinRep_neg_one_realSpinGroupEquiv_eq`,
  `CliffordAlgebra.adjoint_positiveQuaternionAction`,
  `CliffordAlgebra.adjoint_negativeQuaternionAction`.
* `CliffordAlgebra.exists_orthonormalBasis_toMatrix_halfSpinRep_one`,
  `CliffordAlgebra.exists_orthonormalBasis_toMatrix_halfSpinRep_neg_one`.
* `CliffordAlgebra.trace_halfSpinRep_one_realSpinGroupEquiv_specialUnitary`,
  `CliffordAlgebra.trace_halfSpinRep_neg_one_realSpinGroupEquiv_specialUnitary`,
  `CliffordAlgebra.trace_spinCGroupHalfSpinRep_one_realSpinCGroupHom`,
  `CliffordAlgebra.trace_spinCGroupHalfSpinRep_neg_one_realSpinCGroupHom`,
  `OrthonormalBasis.coe_realSpinFourEquivQuaternionUnitaryProd_symm_spinTorus`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

open Module Module.End CliffordAlgebra TauCeti
open scoped InnerProductSpace Matrix Quaternion

/-! ### Quaternion factor actions and characters on `W⁺` and `W⁻` -/

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

section Module

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

private def quaternionProdAction (ε : ℂ) :
    ℍ[ℝ] × ℍ[ℝ] →ₐ[ℝ] Module.End ℂ (eigenspace (ρ (chirality Q o)) ε) :=
  (evenHalfSpinAction o ρ ε).comp
    ((b.realEvenCliffordEquiv hQ).toAlgHom.comp
      realCliffordFourZeroEvenEquivQuaternionProd.symm.toAlgHom)

include hQ in
private theorem halfSpinRep_realSpinGroupEquiv_eq_quaternionProdAction (ε : ℂ)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s) =
      quaternionProdAction o hQ b ρ ε
        ((realSpinFourEquivQuaternionUnitaryProd s).fst,
          (realSpinFourEquivQuaternionUnitaryProd s).snd) := by
  rw [coe_realSpinFourEquivQuaternionUnitaryProd_apply,
    evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply, halfSpinRep_apply,
    OrthonormalBasis.spinGroupToEven_realSpinGroupEquiv]
  simp [quaternionProdAction]

include hQ in
private theorem quaternionProdAction_neg_one_one (hb : b.toBasis.orientation = o) (ε : ℂ) :
    quaternionProdAction o hQ b ρ ε (-1, 1) = algebraMap ℂ _ ε := by
  ext ψ
  have hchir : chirality Q o = b.realEvenCliffordEquiv hQ
      (realCliffordFourZeroEvenEquivQuaternionProd.symm (-1, 1)) := by
    rw [realCliffordFourZeroEvenEquivQuaternionProd_symm_neg_one_one, map_neg, map_mul,
      OrthonormalBasis.realEvenCliffordEquiv_ι, OrthonormalBasis.realEvenCliffordEquiv_ι,
      chirality_eq o hQ b hb]
    simp [coe_even_ι_bilin, mul_assoc]
  simp only [quaternionProdAction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    coe_evenHalfSpinAction_apply, ← hchir, mem_eigenspace_iff.mp ψ.property]
  simp [Algebra.algebraMap_eq_smul_one]

include hQ in
private theorem quaternionProdAction_zero_one (hb : b.toBasis.orientation = o) :
    quaternionProdAction o hQ b ρ 1 (0, 1) = 1 := by
  have h01 : ((0, 1) : ℍ[ℝ] × ℍ[ℝ]) = (2 : ℝ)⁻¹ • (1 + (-1, 1)) := by
    ext <;> simp; norm_num
  rw [h01, map_smul, map_add, map_one, quaternionProdAction_neg_one_one o hQ b ρ hb, map_one]
  module

include hQ in
private theorem quaternionProdAction_one_zero (hb : b.toBasis.orientation = o) :
    quaternionProdAction o hQ b ρ (-1) (1, 0) = 1 := by
  have h10 : ((1, 0) : ℍ[ℝ] × ℍ[ℝ]) = (2 : ℝ)⁻¹ • (1 - (-1, 1)) := by
    ext <;> simp; norm_num
  rw [h10, map_smul, map_sub, map_one, quaternionProdAction_neg_one_one o hQ b ρ hb,
    map_neg, map_one]
  module

/-- **The quaternion action on the positive half-spinors `W⁺`** induced by a positively oriented
orthonormal frame `b`: `q : ℍ[ℝ]` acts through the second factor `(0, q)` of
`Cl⁺(4, 0) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]`. -/
def positiveQuaternionAction (hb : b.toBasis.orientation = o) :
    ℍ[ℝ] →ₐ[ℝ] Module.End ℂ (eigenspace (ρ (chirality Q o)) 1) :=
  AlgHom.prodFirst
    ((quaternionProdAction o hQ b ρ 1).comp
      ((AlgHom.snd ℝ ℍ[ℝ] ℍ[ℝ]).prod (AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ])))
    (by simpa using quaternionProdAction_zero_one o hQ b ρ hb)

/-- **The quaternion action on the negative half-spinors `W⁻`** induced by a positively oriented
orthonormal frame `b`: `q : ℍ[ℝ]` acts through the first factor `(q, 0)` of
`Cl⁺(4, 0) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]`. -/
def negativeQuaternionAction (hb : b.toBasis.orientation = o) :
    ℍ[ℝ] →ₐ[ℝ] Module.End ℂ (eigenspace (ρ (chirality Q o)) (-1)) :=
  AlgHom.prodFirst (quaternionProdAction o hQ b ρ (-1))
    (quaternionProdAction_one_zero o hQ b ρ hb)

/-- Unfolding `positiveQuaternionAction` as the even half-spin action at `(0, q)`. -/
theorem positiveQuaternionAction_apply (hb : b.toBasis.orientation = o) (q : ℍ[ℝ]) :
    positiveQuaternionAction o hQ b ρ hb q =
      evenHalfSpinAction o ρ 1
        (b.realEvenCliffordEquiv hQ (realCliffordFourZeroEvenEquivQuaternionProd.symm (0, q))) := by
  simp [positiveQuaternionAction, quaternionProdAction]

/-- Unfolding `negativeQuaternionAction` as the even half-spin action at `(q, 0)`. -/
theorem negativeQuaternionAction_apply (hb : b.toBasis.orientation = o) (q : ℍ[ℝ]) :
    negativeQuaternionAction o hQ b ρ hb q =
      evenHalfSpinAction o ρ (-1)
        (b.realEvenCliffordEquiv hQ (realCliffordFourZeroEvenEquivQuaternionProd.symm (q, 0))) := by
  simp [negativeQuaternionAction, quaternionProdAction]

include hQ in
/-- **Factorization of the positive half-spin representation**: along a positively oriented frame
`b`, `halfSpinRep` on `W⁺` factors through the **second** unit quaternion of compact `Spin(4)`. -/
theorem halfSpinRep_one_realSpinGroupEquiv_eq (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s) =
      positiveQuaternionAction o hQ b ρ hb (realSpinFourEquivQuaternionUnitaryProd s).snd := by
  let φ := (quaternionProdAction o hQ b ρ 1).comp
    ((AlgHom.snd ℝ ℍ[ℝ] ℍ[ℝ]).prod (AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ]))
  have hφ : φ (1, 0) = 1 := by simpa [φ] using quaternionProdAction_zero_one o hQ b ρ hb
  rw [halfSpinRep_realSpinGroupEquiv_eq_quaternionProdAction, positiveQuaternionAction,
    AlgHom.prodFirst_apply, ← AlgHom.map_eq_map_fst φ hφ
      ((realSpinFourEquivQuaternionUnitaryProd s).snd,
        (realSpinFourEquivQuaternionUnitaryProd s).fst)]
  simp [φ]

include hQ in
/-- **Factorization of the negative half-spin representation**: along a positively oriented frame
`b`, `halfSpinRep` on `W⁻` factors through the **first** unit quaternion of compact `Spin(4)`. -/
theorem halfSpinRep_neg_one_realSpinGroupEquiv_eq (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s) =
      negativeQuaternionAction o hQ b ρ hb (realSpinFourEquivQuaternionUnitaryProd s).fst := by
  let φ := quaternionProdAction o hQ b ρ (-1)
  have hφ : φ (1, 0) = 1 := quaternionProdAction_one_zero o hQ b ρ hb
  rw [halfSpinRep_realSpinGroupEquiv_eq_quaternionProdAction, negativeQuaternionAction,
    AlgHom.prodFirst_apply, ← AlgHom.map_eq_map_fst φ hφ
      ((realSpinFourEquivQuaternionUnitaryProd s).fst,
        (realSpinFourEquivQuaternionUnitaryProd s).snd)]

section Characters

include hQ in
/-- **Character of `W⁺` on compact `Spin(4)`** in quaternion coordinates: the trace of `s` acting
on `W⁺` is `Re q₂ · dim_ℂ W⁺`, where `q₂` is the second unit quaternion of `s`. -/
theorem trace_halfSpinRep_one_realSpinGroupEquiv (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s)) =
      (((realSpinFourEquivQuaternionUnitaryProd s).snd : ℍ[ℝ]).re : ℂ) *
        finrank ℂ (eigenspace (ρ (chirality Q o)) 1) := by
  rw [halfSpinRep_one_realSpinGroupEquiv_eq o hQ b ρ hb, trace_quaternionAlgHom]

include hQ in
/-- **Character of `W⁻` on compact `Spin(4)`** in quaternion coordinates: the trace of `s` acting
on `W⁻` is `Re q₁ · dim_ℂ W⁻`, where `q₁` is the first unit quaternion of `s`. -/
theorem trace_halfSpinRep_neg_one_realSpinGroupEquiv (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s)) =
      (((realSpinFourEquivQuaternionUnitaryProd s).fst : ℍ[ℝ]).re : ℂ) *
        finrank ℂ (eigenspace (ρ (chirality Q o)) (-1)) := by
  rw [halfSpinRep_neg_one_realSpinGroupEquiv_eq o hQ b ρ hb, trace_quaternionAlgHom]

include hQ in
/-- **Character of `W⁺` on compact `Spin(4)` in `SU(2)` coordinates**: when `dim_ℂ W⁺ = 2`, the
trace of `halfSpinRep` on `W⁺` is the matrix trace of the **second** `SU(2)` factor. -/
theorem trace_halfSpinRep_one_realSpinGroupEquiv_specialUnitary (hb : b.toBasis.orientation = o)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
    (s : spinGroup (realCliffordForm 4 0)) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s)) =
      ((realSpinFourEquivSpecialUnitaryProd s).snd : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  have hsnd : ((realSpinFourEquivSpecialUnitaryProd s).snd : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).snd :=
    congrArg Prod.snd (coe_realSpinFourEquivSpecialUnitaryProd_apply s)
  rw [trace_halfSpinRep_one_realSpinGroupEquiv o hQ b ρ hb, h₂, hsnd,
    Quaternion.trace_toComplexMatrix]
  push_cast
  ring

include hQ in
/-- **Character of `W⁻` on compact `Spin(4)` in `SU(2)` coordinates**: when `dim_ℂ W⁺ = 2`, the
trace of `halfSpinRep` on `W⁻` is the matrix trace of the **first** `SU(2)` factor. -/
theorem trace_halfSpinRep_neg_one_realSpinGroupEquiv_specialUnitary (hb : b.toBasis.orientation = o)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
    (s : spinGroup (realCliffordForm 4 0)) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s)) =
      ((realSpinFourEquivSpecialUnitaryProd s).fst : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  have hfst : ((realSpinFourEquivSpecialUnitaryProd s).fst : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).fst :=
    congrArg Prod.fst (coe_realSpinFourEquivSpecialUnitaryProd_apply s)
  rw [trace_halfSpinRep_neg_one_realSpinGroupEquiv o hQ b ρ hb,
    finrank_eigenspace_chirality_neg o ρ 1, h₂, hfst, Quaternion.trace_toComplexMatrix]
  push_cast
  ring

include hQ in
/-- **Character of `W⁺` on compact `Spinᶜ(4)`**: at `[s, z]` transported along a positively
oriented frame `b`, the trace on a rank-two `W⁺` is `z` times the trace of the second `SU(2)`
factor of `s`. -/
theorem trace_spinCGroupHalfSpinRep_one_realSpinCGroupHom (hb : b.toBasis.orientation = o)
    (hpos : realCliffordForm 4 0 ≠ 0) (hQ₀ : Q ≠ 0)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
    (s : spinGroup (realCliffordForm 4 0)) (z : Circle) :
    LinearMap.trace ℂ _
        (spinCGroupHalfSpinRep o ρ 1 hQ₀
          (b.realSpinCGroupHom hQ hpos hQ₀ (spinCGroup.mk _ hpos (s, z)))) =
      (z : ℂ) *
        ((realSpinFourEquivSpecialUnitaryProd s).snd : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  rw [OrthonormalBasis.realSpinCGroupHom_mk, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply,
    map_smul, trace_halfSpinRep_one_realSpinGroupEquiv_specialUnitary o hQ b ρ hb h₂, smul_eq_mul]

include hQ in
/-- **Character of `W⁻` on compact `Spinᶜ(4)`**: at `[s, z]` transported along a positively
oriented frame `b`, the trace on `W⁻` (when `dim_ℂ W⁺ = 2`) is `z` times the trace of the first
`SU(2)` factor of `s`. -/
theorem trace_spinCGroupHalfSpinRep_neg_one_realSpinCGroupHom (hb : b.toBasis.orientation = o)
    (hpos : realCliffordForm 4 0 ≠ 0) (hQ₀ : Q ≠ 0)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
    (s : spinGroup (realCliffordForm 4 0)) (z : Circle) :
    LinearMap.trace ℂ _
        (spinCGroupHalfSpinRep o ρ (-1) hQ₀
          (b.realSpinCGroupHom hQ hpos hQ₀ (spinCGroup.mk _ hpos (s, z)))) =
      (z : ℂ) *
        ((realSpinFourEquivSpecialUnitaryProd s).fst : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  rw [OrthonormalBasis.realSpinCGroupHom_mk, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply,
    map_smul, trace_halfSpinRep_neg_one_realSpinGroupEquiv_specialUnitary o hQ b ρ hb h₂,
    smul_eq_mul]

end Characters

end Module

/-! ### Hermitian adjoint compatibility and explicit `SU(2)₋ × SU(2)₊` spinor bases -/

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

include hQ in
/-- On a Hermitian Clifford module, `positiveQuaternionAction` carries quaternion conjugation to
the Hilbert-space adjoint. -/
theorem adjoint_positiveQuaternionAction
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hb : b.toBasis.orientation = o) (q : ℍ[ℝ]) :
    LinearMap.adjoint (positiveQuaternionAction o hQ b ρ hb q) =
      positiveQuaternionAction o hQ b ρ hb (star q) := by
  rw [positiveQuaternionAction_apply, adjoint_evenHalfSpinAction o hρ,
    ← b.realEvenCliffordEquiv_reverseEven hQ,
    realCliffordFourZeroEvenEquivQuaternionProd_symm_reverseEven, Prod.star_def, star_zero,
    ← positiveQuaternionAction_apply]

include hQ in
/-- On a Hermitian Clifford module, `negativeQuaternionAction` carries quaternion conjugation to
the Hilbert-space adjoint. -/
theorem adjoint_negativeQuaternionAction
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hb : b.toBasis.orientation = o) (q : ℍ[ℝ]) :
    LinearMap.adjoint (negativeQuaternionAction o hQ b ρ hb q) =
      negativeQuaternionAction o hQ b ρ hb (star q) := by
  rw [negativeQuaternionAction_apply, adjoint_evenHalfSpinAction o hρ,
    ← b.realEvenCliffordEquiv_reverseEven hQ,
    realCliffordFourZeroEvenEquivQuaternionProd_symm_reverseEven, Prod.star_def, star_zero,
    ← negativeQuaternionAction_apply]

include hQ in
/-- **Orthonormal half-spinor basis for `W⁺`**: on a Hermitian Clifford module of half-spin rank
two, `W⁺` admits an orthonormal basis in which `halfSpinRep` at `b.realSpinGroupEquiv hQ s` has
matrix equal to the **second** `SU(2)` factor `(realSpinFourEquivSpecialUnitaryProd s).snd`. -/
theorem exists_orthonormalBasis_toMatrix_halfSpinRep_one
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hb : b.toBasis.orientation = o)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2) :
    ∃ c : OrthonormalBasis (Fin 2) ℂ (eigenspace (ρ (chirality Q o)) 1),
      ∀ s : spinGroup (realCliffordForm 4 0),
        LinearMap.toMatrix c.toBasis c.toBasis (halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s)) =
          ((realSpinFourEquivSpecialUnitaryProd s).snd : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨c, hc⟩ := exists_orthonormalBasis_toMatrix_eq_toComplexMatrix h₂
    (positiveQuaternionAction o hQ b ρ hb) (adjoint_positiveQuaternionAction o hQ b hρ hb)
  refine ⟨c, fun s ↦ ?_⟩
  rw [halfSpinRep_one_realSpinGroupEquiv_eq o hQ b ρ hb, hc]
  exact (congrArg Prod.snd (coe_realSpinFourEquivSpecialUnitaryProd_apply s)).symm

include hQ in
/-- **Orthonormal half-spinor basis for `W⁻`**: on a Hermitian Clifford module of half-spin rank
two, `W⁻` admits an orthonormal basis in which `halfSpinRep` at `b.realSpinGroupEquiv hQ s` has
matrix equal to the **first** `SU(2)` factor `(realSpinFourEquivSpecialUnitaryProd s).fst`. -/
theorem exists_orthonormalBasis_toMatrix_halfSpinRep_neg_one
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hb : b.toBasis.orientation = o)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2) :
    ∃ c : OrthonormalBasis (Fin 2) ℂ (eigenspace (ρ (chirality Q o)) (-1)),
      ∀ s : spinGroup (realCliffordForm 4 0),
        LinearMap.toMatrix c.toBasis c.toBasis (halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s)) =
          ((realSpinFourEquivSpecialUnitaryProd s).fst : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h₂_neg : finrank ℂ (eigenspace (ρ (chirality Q o)) (-1)) = 2 := by
    rw [finrank_eigenspace_chirality_neg o ρ 1, h₂]
  obtain ⟨c, hc⟩ := exists_orthonormalBasis_toMatrix_eq_toComplexMatrix h₂_neg
    (negativeQuaternionAction o hQ b ρ hb) (adjoint_negativeQuaternionAction o hQ b hρ hb)
  refine ⟨c, fun s ↦ ?_⟩
  rw [halfSpinRep_neg_one_realSpinGroupEquiv_eq o hQ b ρ hb, hc]
  exact (congrArg Prod.fst (coe_realSpinFourEquivSpecialUnitaryProd_apply s)).symm

end Hermitian

end CliffordAlgebra

/-! ### Quaternion-pair coordinates of `OrthonormalBasis.spinTorus` -/

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} (b : OrthonormalBasis (Fin 4) ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

include hQ in
/-- **Quaternion-pair coordinates of `OrthonormalBasis.spinTorus`**: pulling `(w₁, w₂)` back along
`b.realSpinGroupEquiv hQ` into compact `Spin(4) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ]` gives
`re(w₁ w₂⁻¹) + im(w₁ w₂⁻¹) k` in the first factor (which acts on `W⁻`) and
`re(w₁ w₂) + im(w₁ w₂) k` in the second factor (which acts on `W⁺`). -/
theorem coe_realSpinFourEquivQuaternionUnitaryProd_symm_spinTorus (w₁ w₂ : Circle) :
    (((realSpinFourEquivQuaternionUnitaryProd
        ((b.realSpinGroupEquiv hQ).symm (b.spinTorus hQ (w₁, w₂)))).fst : ℍ[ℝ]),
      ((realSpinFourEquivQuaternionUnitaryProd
        ((b.realSpinGroupEquiv hQ).symm (b.spinTorus hQ (w₁, w₂)))).snd : ℍ[ℝ])) =
      (⟨((w₁ * w₂⁻¹ : Circle) : ℂ).re, 0, 0, ((w₁ * w₂⁻¹ : Circle) : ℂ).im⟩,
        ⟨((w₁ * w₂ : Circle) : ℂ).re, 0, 0, ((w₁ * w₂ : Circle) : ℂ).im⟩) := by
  set s := (b.realSpinGroupEquiv hQ).symm (b.spinTorus hQ (w₁, w₂))
  let B₀₁ := (even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) (Pi.single 1 1)
  let B₂₃ := (even.ι (realCliffordForm 4 0)).bilin (Pi.single 2 1) (Pi.single 3 1)
  have hs_even : b.realEvenCliffordEquiv hQ
      (evenUnitaryGroupEvenPart (realCliffordForm 4 0)
        (spinGroupToEvenUnitary (realCliffordForm 4 0) s)) =
      spinGroupToEven Q (b.spinTorus hQ (w₁, w₂)) := by
    rw [evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply,
      ← b.spinGroupToEven_realSpinGroupEquiv hQ s, MulEquiv.apply_symm_apply]
  have htorus : spinGroupToEven Q (b.spinTorus hQ (w₁, w₂)) =
      b.realEvenCliffordEquiv hQ
        ((algebraMap ℝ _ (w₁ : ℂ).re - (w₁ : ℂ).im • B₀₁) *
          (algebraMap ℝ _ (w₂ : ℂ).re - (w₂ : ℂ).im • B₂₃)) := by
    apply Subtype.ext
    rw [coe_spinGroupToEven_apply, b.coe_spinTorus_apply hQ]
    simp [B₀₁, B₂₃, OrthonormalBasis.realEvenCliffordEquiv_ι, coe_even_ι_bilin]
  have hcoord : evenUnitaryGroupEvenPart (realCliffordForm 4 0)
        (spinGroupToEvenUnitary (realCliffordForm 4 0) s) =
      (algebraMap ℝ _ (w₁ : ℂ).re - (w₁ : ℂ).im • B₀₁) *
        (algebraMap ℝ _ (w₂ : ℂ).re - (w₂ : ℂ).im • B₂₃) :=
    (b.realEvenCliffordEquiv hQ).injective (hs_even.trans htorus)
  rw [coe_realSpinFourEquivQuaternionUnitaryProd_apply, hcoord]
  simp only [B₀₁, B₂₃, map_mul, map_sub, map_smul, AlgEquiv.commutes,
    realCliffordFourZeroEvenEquivQuaternionProd_ι]
  apply Prod.ext <;> ext <;>
    simp [Circle.coe_mul, QuaternionAlgebra.mk_mul_mk, Algebra.algebraMap_eq_smul_one]

end OrthonormalBasis

end
