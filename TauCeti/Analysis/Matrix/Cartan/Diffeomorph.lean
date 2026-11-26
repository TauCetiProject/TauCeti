/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan.Closed
public import TauCeti.Geometry.Manifold.Immersion.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Algebra.Star.Unitary
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.Analysis.Matrix.Polar.Deformation
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# The smooth Cartan decomposition of a closed matrix group stable under conjugate transpose

Let `H` be a closed subgroup of `GL(n, 𝕜)`, for `𝕜 = ℝ` or `ℂ`, stable under the conjugate
transpose `g ↦ gᴴ` (the transpose when `𝕜 = ℝ`), and containing the whole exponential line
`exp (t x)` as soon as it contains `exp x`, for Hermitian `x`. The last condition holds when `H` has
finitely many connected components (`Subgroup.expUnit_smul_mem_of_isClosed`), and it is checked
directly for `SL(n, 𝕜)`, `Sp(2n, ℝ)` and the realification of `GL(n, ℂ)`. Write
`K_H = H ∩ U(n)` for the unitary (orthogonal when `𝕜 = ℝ`) elements of `H` and
`𝔭_H = {X | X Hermitian, exp (t X) ∈ H for all real t}` for the Hermitian part of its Lie
algebra (`Subgroup.hermitianLieSubmodule`), a real vector subspace of the matrices. The Cartan
decomposition `Subgroup.cartanHomeomorph` says that `(k, X) ↦ k * exp X` is a homeomorphism
`K_H × 𝔭_H ≃ₜ H`. This file proves that it is a **smooth diffeomorphism**
(`Subgroup.cartanDiffeomorph`): `H` is diffeomorphic to the product of its unitary elements, a
maximal compact subgroup when `H` has finitely many components
(`Subgroup.maximal_isCompact_unitarySubgroup_subgroupOf_of_isClosed`), with a Euclidean space.

The manifold structures on `H` and on `K_H` are arbitrary, subject only to their inclusions into
`GL(n, 𝕜)` being immersions. This holds for the closed-subgroup charts
`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` given by Cartan's closed-subgroup theorem
(through `TauCeti.Lie.EmbeddedLieSubgroupData.isSmoothEmbedding_subtypeVal`), and for any other
structure in which these closed subgroups are embedded submanifolds. The vector space `𝔭_H`
carries its smooth structure as a finite-dimensional real normed space.

The proof restricts the Cartan diffeomorphism `Matrix.GeneralLinearGroup.cartanDiffeomorph` of
`GL(n, 𝕜)` itself. Its inverse sends `g` to its unitary polar factor and to `log √(gᴴ g)`, which
lie in `K_H` and in `𝔭_H` when `g ∈ H`, by `Subgroup.cartanHomeomorph`. A smooth map into
`GL(n, 𝕜)` with values in `H` or in `K_H` is smooth into that subgroup, because the inclusion is an
immersion, and a smooth matrix-valued map with values in the subspace `𝔭_H` is smooth into `𝔭_H`,
through a continuous linear projection onto it.

As for `Matrix.GeneralLinearGroup.cartanDiffeomorph`, the matrices carry the `ℓ²` operator norm:
to use these declarations, open the `Matrix.Norms.L2Operator` scope and enable
`Matrix.l2OpNormedAlgebraReal` as a local instance.

## Main definitions

* `Subgroup.hermitianLieSubmodule H`: the real subspace `𝔭_H` of Hermitian matrices in the Lie
  algebra of `H`.
* `Subgroup.cartanDiffeomorph`: the smooth diffeomorphism `K_H × 𝔭_H ≃ₘ H`, `(k, X) ↦ k * exp X`.

## Main results

* `Subgroup.mem_hermitianLieSubmodule_iff`: for closed `H`, `X ∈ 𝔭_H` exactly when `X` is
  Hermitian and `exp (t X) ∈ H` for every real `t`.
* `Subgroup.val_cartanDiffeomorph_apply`, `Subgroup.coe_cartanDiffeomorph_symm_apply_fst`,
  `Subgroup.coe_cartanDiffeomorph_symm_apply_snd`: the diffeomorphism sends `(k, X)` to
  `k * exp X`, and its inverse sends `g` to its unitary polar factor and to `log √(gᴴ g)`.

## References

* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1.
-/

public section

noncomputable section

open scoped MatrixOrder ContDiff Manifold Matrix.Norms.L2Operator

open Matrix Matrix.GeneralLinearGroup Manifold

namespace Subgroup

attribute [local instance] Matrix.l2OpNormedAlgebraReal TauCeti.normedAlgebraRatOfReal

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

variable (H : Subgroup (GL n 𝕜)) in
/-- The Hermitian part `𝔭_H` of the Lie algebra of a subgroup `H` of `GL n 𝕜`: the Hermitian
matrices of `Subgroup.linearLieSubalgebra H`. For a closed `H` these are the Hermitian matrices
whose exponential line lies in `H` (`Subgroup.mem_hermitianLieSubmodule_iff`). -/
def hermitianLieSubmodule : Submodule ℝ (Matrix n n 𝕜) :=
  selfAdjoint.submodule ℝ (Matrix n n 𝕜) ⊓ H.linearLieSubalgebra.toSubmodule

variable {H : Subgroup (GL n 𝕜)}

/-- A matrix lies in `𝔭_H` exactly when it is Hermitian and lies in the Lie algebra of `H`. -/
theorem mem_hermitianLieSubmodule {X : Matrix n n 𝕜} :
    X ∈ H.hermitianLieSubmodule ↔ IsSelfAdjoint X ∧ X ∈ H.linearLieSubalgebra :=
  Iff.rfl

/-- For a closed subgroup `H` of `GL n 𝕜`, a matrix lies in the Hermitian part `𝔭_H` of the Lie
algebra of `H` exactly when it is Hermitian and its whole exponential line lies in `H`. -/
theorem mem_hermitianLieSubmodule_iff (hH : IsClosed (H : Set (GL n 𝕜))) {X : Matrix n n 𝕜} :
    X ∈ H.hermitianLieSubmodule ↔
      X.IsHermitian ∧ ∀ t : ℝ, ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • X) := by
  rw [mem_hermitianLieSubmodule, forall_exists_mem_coe_eq_exp_smul_iff_mem_linearLieSubalgebra hH,
    ← Matrix.isHermitian_iff_isSelfAdjoint]

/-- The exponential of an element of `𝔭_H` lies in a closed subgroup `H`. -/
private theorem expUnit_mem (hH : IsClosed (H : Set (GL n 𝕜))) (X : H.hermitianLieSubmodule) :
    TauCeti.expUnit (X : Matrix n n 𝕜) ∈ H := by
  simpa only [one_smul] using
    mem_linearLieAlgebra_iff.1 ((H.mem_linearLieSubalgebra_iff hH).1 X.property.2) 1

/-- The unitary elements of a closed subgroup of `GL n 𝕜` form a closed subgroup. -/
theorem isClosed_inf_unitarySubgroup (hH : IsClosed (H : Set (GL n 𝕜))) :
    IsClosed ((H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) : Set (GL n 𝕜)) :=
  hH.inter (TauCeti.isClosed_unitarySubgroup_units (Matrix n n 𝕜))

/-- The Hermitian factor `log √(gᴴ g)` of an element `g` of `H` lies in `𝔭_H`, when `H` is closed,
stable under conjugate transpose and contains the exponential line through each of its positive
elements. -/
private theorem cfc_log_sqrt_mem (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H)
    (hexp : ∀ x : Matrix n n 𝕜, IsSelfAdjoint x → TauCeti.expUnit x ∈ H →
      ∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H) (g : H) :
    cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) ∈
      H.hermitianLieSubmodule := by
  set q := (H.cartanHomeomorph hstar hexp).symm g
  have hq := H.coe_cartanHomeomorph_symm_apply_snd hstar hexp g
  rw [CFC.log] at hq
  rw [← hq]
  exact ⟨q.2.val.property,
    (H.mem_linearLieSubalgebra_iff hH).2 (mem_linearLieAlgebra_iff.2 q.2.property)⟩

/-- The unitary polar factor of an element of `H` lies in `K_H`. -/
private theorem toUnits_polarUnitary_mem_inf (hstar : ∀ g ∈ H, star g ∈ H)
    (hexp : ∀ x : Matrix n n 𝕜, IsSelfAdjoint x → TauCeti.expUnit x ∈ H →
      ∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H) (g : H) :
    Unitary.toUnits (g : GL n 𝕜).polarUnitary ∈ H ⊓ unitarySubgroup (GL n 𝕜) := by
  refine ⟨?_, ?_⟩
  · have h := ((H.cartanHomeomorph hstar hexp).symm g).1.property
    rwa [H.coe_cartanHomeomorph_symm_apply_fst hstar hexp g] at h
  · have h := (unitarySubgroupUnitsEquiv.symm (g : GL n 𝕜).polarUnitary).property
    rwa [TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply] at h

/-- The unitary element of `U(n)` underlying an element of `K_H`. -/
private def toUnitary (k : (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜))) :
    unitaryGroup n 𝕜 :=
  unitarySubgroupUnitsEquiv ⟨k, k.property.2⟩

private theorem toUnits_toUnitary (k : (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜))) :
    Unitary.toUnits (toUnitary k) = k := by
  rw [toUnitary, ← TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply, MulEquiv.symm_apply_apply]

variable (H) in
/-- The Cartan decomposition `(k, X) ↦ k * exp X` of a closed subgroup `H` of `GL n 𝕜` satisfying
the hypotheses of `Subgroup.cartanHomeomorph`, as an equivalence `K_H × 𝔭_H ≃ H`. -/
private def cartanEquiv (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
    (hexp : ∀ x : Matrix n n 𝕜, IsSelfAdjoint x → TauCeti.expUnit x ∈ H →
      ∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H) :
    (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) × H.hermitianLieSubmodule ≃ H where
  toFun p := ⟨(p.1 : GL n 𝕜) * TauCeti.expUnit (p.2 : Matrix n n 𝕜),
    H.mul_mem p.1.property.1 (expUnit_mem hH p.2)⟩
  invFun g := (⟨_, toUnits_polarUnitary_mem_inf hstar hexp g⟩,
    ⟨_, cfc_log_sqrt_mem hH hstar hexp g⟩)
  left_inv p := by
    -- The pair `(k, X)` is the preimage of `k * exp X` under the Cartan decomposition of `GL n 𝕜`.
    have hX : IsSelfAdjoint (p.2 : Matrix n n 𝕜) := p.2.property.1
    have hp : GeneralLinearGroup.cartanHomeomorph n 𝕜 (toUnitary p.1, ⟨p.2, hX⟩) =
        (p.1 : GL n 𝕜) * TauCeti.expUnit (p.2 : Matrix n n 𝕜) := by
      ext : 1
      rw [GeneralLinearGroup.val_cartanHomeomorph_apply, Units.val_mul, TauCeti.expUnit_coe,
        ← Unitary.val_toUnits_apply, toUnits_toUnitary]
    have h := (GeneralLinearGroup.cartanHomeomorph n 𝕜).symm_apply_apply (toUnitary p.1, ⟨p.2, hX⟩)
    rw [hp] at h
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · dsimp only
      rw [← GeneralLinearGroup.cartanHomeomorph_symm_apply_fst, h, toUnits_toUnitary]
    · dsimp only
      rw [← GeneralLinearGroup.coe_cartanHomeomorph_symm_apply_snd, h]
  right_inv g := by
    refine Subtype.ext (Units.ext ?_)
    have h := congrArg (fun g : GL n 𝕜 ↦ (g : Matrix n n 𝕜))
      ((GeneralLinearGroup.cartanHomeomorph n 𝕜).apply_symm_apply (g : GL n 𝕜))
    simp only [GeneralLinearGroup.val_cartanHomeomorph_apply,
      GeneralLinearGroup.cartanHomeomorph_symm_apply_fst,
      GeneralLinearGroup.coe_cartanHomeomorph_symm_apply_snd] at h
    simpa only [Units.val_mul, TauCeti.expUnit_coe, Unitary.val_toUnits_apply] using h

variable {EH EK : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [ChartedSpace EH H]
  [NormedAddCommGroup EK] [NormedSpace ℝ EK]
  [ChartedSpace EK (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜))]

variable (H) in
/-- **The smooth Cartan decomposition of a closed matrix group stable under conjugate transpose.**
Let `H` be a closed subgroup of `GL n 𝕜`, for `𝕜 = ℝ` or `ℂ`, stable under the conjugate transpose
and containing the exponential line `exp (t x)` as soon as it contains `exp x`, for Hermitian `x`.
The last hypothesis holds when `H` has finitely many connected components
(`Subgroup.expUnit_smul_mem_of_isClosed`). Give `H` and its unitary elements
`K_H = H ⊓ unitarySubgroup (GL n 𝕜)` manifold structures for which the inclusions into `GL n 𝕜` are
immersions, such as the closed-subgroup charts. Then `(k, X) ↦ k * exp X` is a smooth
diffeomorphism from `K_H × 𝔭_H` onto `H`, where `𝔭_H` is the Hermitian part of the Lie algebra of
`H` (`Subgroup.hermitianLieSubmodule`). -/
def cartanDiffeomorph (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
    (hexp : ∀ x : Matrix n n 𝕜, IsSelfAdjoint x → TauCeti.expUnit x ∈ H →
      ∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H)
    (hιH : IsImmersion 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞ (fun g : H ↦ (g : GL n 𝕜)))
    (hιK : IsImmersion 𝓘(ℝ, EK) 𝓘(ℝ, Matrix n n 𝕜) ∞
      (fun k : (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) ↦ (k : GL n 𝕜))) :
    ((H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) × H.hermitianLieSubmodule) ≃ₘ^∞⟮
      𝓘(ℝ, EK).prod 𝓘(ℝ, H.hermitianLieSubmodule), 𝓘(ℝ, EH)⟯ H where
  toEquiv := cartanEquiv H hH hstar hexp
  contMDiff_toFun := by
    -- Read in `GL n 𝕜`, the map is `(k, X) ↦ k * exp X`.
    have hexpX : ContMDiff 𝓘(ℝ, H.hermitianLieSubmodule) 𝓘(ℝ, Matrix n n 𝕜) ∞
        (fun X : H.hermitianLieSubmodule ↦ TauCeti.expUnit (X : Matrix n n 𝕜)) := by
      apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
      exact ((NormedSpace.contDiff_exp ℝ).comp
        H.hermitianLieSubmodule.subtypeL.contDiff).contMDiff.congr fun X ↦
          TauCeti.expUnit_coe (X : Matrix n n 𝕜)
    have hGL : ContMDiff (𝓘(ℝ, EK).prod 𝓘(ℝ, H.hermitianLieSubmodule)) 𝓘(ℝ, Matrix n n 𝕜) ∞
        (fun p : (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) ×
            H.hermitianLieSubmodule ↦
          (p.1 : GL n 𝕜) * TauCeti.expUnit (p.2 : Matrix n n 𝕜)) := by
      apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
      exact contDiff_mul.comp_contMDiff
        (((Units.contMDiff_val.comp hιK.contMDiff).comp contMDiff_fst).prodMk_space
          ((Units.contMDiff_val.comp hexpX).comp contMDiff_snd))
    exact (ContMDiff.iff_comp_isImmersion hιH).2
      ⟨hGL.continuous.subtype_mk _, hGL⟩
  contMDiff_invFun := by
    -- The polar unitary factor of `g`, read in `GL n 𝕜`, is smooth, and so is `log √(gᴴ g)`.
    have hU : ContMDiff 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞
        (fun g : H ↦ Unitary.toUnits (g : GL n 𝕜).polarUnitary) :=
      contMDiff_toUnits_polarUnitary.comp hιH.contMDiff
    have hlog : ContMDiff 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞
        (fun g : H ↦ cfc Real.log
          (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜)))) := by
      refine ((selfAdjoint.contDiff_subtype_val ℝ).contMDiff.comp (contMDiff_snd.comp
        ((GeneralLinearGroup.cartanDiffeomorph n 𝕜).symm.contMDiff.comp hιH.contMDiff))).congr
          fun g ↦ ?_
      exact (GeneralLinearGroup.coe_cartanDiffeomorph_symm_apply_snd (g : GL n 𝕜)).symm
    -- A continuous linear projection onto `𝔭_H` makes the Hermitian factor smooth into `𝔭_H`.
    obtain ⟨π, hπ⟩ := Submodule.ClosedComplemented.of_finiteDimensional H.hermitianLieSubmodule
    refine ContMDiff.prodMk ((ContMDiff.iff_comp_isImmersion hιK).2
      ⟨hU.continuous.subtype_mk _, hU⟩) ((π.contDiff.comp_contMDiff hlog).congr fun g ↦ ?_)
    exact (hπ ⟨_, cfc_log_sqrt_mem hH hstar hexp g⟩).symm

variable (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
  (hexp : ∀ x : Matrix n n 𝕜, IsSelfAdjoint x → TauCeti.expUnit x ∈ H →
    ∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H)
  (hιH : IsImmersion 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞ (fun g : H ↦ (g : GL n 𝕜)))
  (hιK : IsImmersion 𝓘(ℝ, EK) 𝓘(ℝ, Matrix n n 𝕜) ∞
    (fun k : (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) ↦ (k : GL n 𝕜)))

/-- The smooth Cartan decomposition of `H` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanDiffeomorph_apply
    (p : (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) × H.hermitianLieSubmodule) :
    ((H.cartanDiffeomorph hH hstar hexp hιH hιK p : GL n 𝕜) : Matrix n n 𝕜) =
      ((p.1 : GL n 𝕜) : Matrix n n 𝕜) * NormedSpace.exp (p.2 : Matrix n n 𝕜) := by
  rw [← TauCeti.expUnit_coe, ← Units.val_mul]
  rfl

/-- The unitary factor of the smooth Cartan decomposition of `g ∈ H` is the polar unitary factor
of `g`. -/
@[simp]
theorem coe_cartanDiffeomorph_symm_apply_fst (g : H) :
    (((H.cartanDiffeomorph hH hstar hexp hιH hιK).symm g).1 : GL n 𝕜) =
      Unitary.toUnits (g : GL n 𝕜).polarUnitary := by
  rfl

/-- The Hermitian factor of the smooth Cartan decomposition of `g ∈ H` is the logarithm of
`√(gᴴ g)`. -/
@[simp]
theorem coe_cartanDiffeomorph_symm_apply_snd (g : H) :
    (((H.cartanDiffeomorph hH hstar hexp hιH hιK).symm g).2 : Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) := by
  rfl

end Subgroup
