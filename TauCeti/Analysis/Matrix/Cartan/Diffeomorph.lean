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

The underlying equivalence is `Subgroup.cartanHomeomorph`, transported along the identifications
of `K_H` and `𝔭_H` with its factor domains. Its smoothness is read off the Cartan diffeomorphism
`Matrix.GeneralLinearGroup.cartanDiffeomorph` of `GL(n, 𝕜)` itself, whose inverse sends `g` to its
unitary polar factor and to `log √(gᴴ g)`. A smooth map into
`GL(n, 𝕜)` with values in `H` or in `K_H` is smooth into that subgroup, because the inclusion is an
immersion, and a smooth matrix-valued map with values in the subspace `𝔭_H` is smooth into `𝔭_H`,
through a continuous linear projection onto it.

As for `Matrix.GeneralLinearGroup.cartanDiffeomorph`, the matrices carry the `ℓ²` operator norm:
to use these declarations, open the `Matrix.Norms.L2Operator` scope and enable
`Matrix.l2OpNormedAlgebraReal` as a local instance.

## Main definitions

* `Subgroup.cartanDiffeomorph`: the smooth diffeomorphism `K_H × 𝔭_H ≃ₘ H`, `(k, X) ↦ k * exp X`.

## Main results

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

variable {H : Subgroup (GL n 𝕜)}

variable (H) in
/-- The unitary elements `K_H` of `H`, viewed as the unitary matrices whose unit lies in `H`: the
unitary factor domain of `Subgroup.cartanHomeomorph`. -/
private def unitaryInfEquiv :
    (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) ≃
      {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ H} where
  toFun k := ⟨unitarySubgroupUnitsEquiv ⟨k, (Subgroup.mem_inf.1 k.property).2⟩, by
    rw [← TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply, MulEquiv.symm_apply_apply]
    exact (Subgroup.mem_inf.1 k.property).1⟩
  invFun u := ⟨Unitary.toUnits u.val, Subgroup.mem_inf.2 ⟨u.property, by
    rw [← TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply]
    exact (unitarySubgroupUnitsEquiv.symm u.val).property⟩⟩
  left_inv k := Subtype.ext <| by
    dsimp only
    rw [← TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply, MulEquiv.symm_apply_apply]
  right_inv u := Subtype.ext <| (unitarySubgroupUnitsEquiv.eq_symm_apply.1 <|
    Subtype.ext (TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply u.val)).symm

/-- The inverse of `unitaryInfEquiv` is the canonical unitary inclusion. -/
private theorem coe_unitaryInfEquiv_symm_apply
    (u : {u : unitaryGroup n 𝕜 // Unitary.toUnits u ∈ H}) :
    ((unitaryInfEquiv H).symm u : GL n 𝕜) = Unitary.toUnits u.val :=
  rfl

/-- For a closed `H`, the Hermitian part `𝔭_H` of the Lie algebra of `H`, viewed as the Hermitian
matrices whose exponential line lies in `H`: the Hermitian factor domain of
`Subgroup.cartanHomeomorph`. -/
private def hermitianLieSubmoduleEquiv (hH : IsClosed (H : Set (GL n 𝕜))) :
    H.hermitianLieSubmodule ≃
      {x : selfAdjoint (Matrix n n 𝕜) //
        ∀ t : ℝ, TauCeti.expUnit (t • (x : Matrix n n 𝕜)) ∈ H} where
  toFun X := ⟨⟨X, (mem_hermitianLieSubmodule.1 X.property).1⟩,
    mem_linearLieAlgebra_iff.1
      ((H.mem_linearLieSubalgebra_iff hH).1 (mem_hermitianLieSubmodule.1 X.property).2)⟩
  invFun x := ⟨x, mem_hermitianLieSubmodule.2 ⟨x.val.property,
    (H.mem_linearLieSubalgebra_iff hH).2 (mem_linearLieAlgebra_iff.2 x.property)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inverse of `hermitianLieSubmoduleEquiv` keeps the underlying matrix. -/
private theorem coe_hermitianLieSubmoduleEquiv_symm_apply (hH : IsClosed (H : Set (GL n 𝕜)))
    (x : {x : selfAdjoint (Matrix n n 𝕜) //
      ∀ t : ℝ, TauCeti.expUnit (t • (x : Matrix n n 𝕜)) ∈ H}) :
    ((hermitianLieSubmoduleEquiv hH).symm x : Matrix n n 𝕜) = x.val :=
  rfl

variable (H) in
/-- The Cartan decomposition `(k, X) ↦ k * exp X` of a closed subgroup `H` of `GL n 𝕜` satisfying
the hypotheses of `Subgroup.cartanHomeomorph`, as an equivalence `K_H × 𝔭_H ≃ H`. -/
private def cartanEquiv (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
    (hexp : ∀ x : Matrix n n 𝕜, IsSelfAdjoint x → TauCeti.expUnit x ∈ H →
      ∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H) :
    (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) × H.hermitianLieSubmodule ≃ H :=
  ((unitaryInfEquiv H).prodCongr (hermitianLieSubmoduleEquiv hH)).trans
    (H.cartanHomeomorph hstar hexp).toEquiv

section CartanEquiv

variable (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
  (hexp : ∀ x : Matrix n n 𝕜, IsSelfAdjoint x → TauCeti.expUnit x ∈ H →
    ∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H)

/-- The Cartan equivalence sends `(k, X)` to `k * exp X`. -/
private theorem coe_cartanEquiv_apply
    (p : (H ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) × H.hermitianLieSubmodule) :
    (cartanEquiv H hH hstar hexp p : GL n 𝕜) =
      (p.1 : GL n 𝕜) * TauCeti.expUnit (p.2 : Matrix n n 𝕜) :=
  Units.ext <| by
    rw [Units.val_mul, TauCeti.expUnit_coe]
    exact Subgroup.val_cartanHomeomorph_apply hstar hexp _

/-- The unitary factor of the inverse Cartan equivalence is the polar unitary factor. -/
private theorem coe_cartanEquiv_symm_apply_fst (g : H) :
    (((cartanEquiv H hH hstar hexp).symm g).1 : GL n 𝕜) =
      Unitary.toUnits (g : GL n 𝕜).polarUnitary := by
  rw [cartanEquiv, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map_fst, coe_unitaryInfEquiv_symm_apply, Homeomorph.coe_symm_toEquiv,
    Subgroup.coe_cartanHomeomorph_symm_apply_fst]

/-- The Hermitian factor of the inverse Cartan equivalence is `log √(gᴴ g)`. -/
private theorem coe_cartanEquiv_symm_apply_snd (g : H) :
    (((cartanEquiv H hH hstar hexp).symm g).2 : Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) := by
  rw [cartanEquiv, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map_snd, coe_hermitianLieSubmoduleEquiv_symm_apply,
    Homeomorph.coe_symm_toEquiv, Subgroup.coe_cartanHomeomorph_symm_apply_snd, CFC.log]

end CartanEquiv

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
    have hGL' : ContMDiff (𝓘(ℝ, EK).prod 𝓘(ℝ, H.hermitianLieSubmodule)) 𝓘(ℝ, Matrix n n 𝕜) ∞
        (fun p ↦ (cartanEquiv H hH hstar hexp p : GL n 𝕜)) :=
      hGL.congr (coe_cartanEquiv_apply hH hstar hexp)
    exact (ContMDiff.iff_comp_isImmersion hιH).2
      ⟨Topology.IsInducing.subtypeVal.continuous_iff.2 hGL'.continuous, hGL'⟩
  contMDiff_invFun := by
    -- The polar unitary factor of `g`, read in `GL n 𝕜`, is smooth, and so is `log √(gᴴ g)`.
    have hU : ContMDiff 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞
        (fun g : H ↦ (((cartanEquiv H hH hstar hexp).symm g).1 : GL n 𝕜)) :=
      (contMDiff_toUnits_polarUnitary.comp hιH.contMDiff).congr
        (coe_cartanEquiv_symm_apply_fst hH hstar hexp)
    have hlog : ContMDiff 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞
        (fun g : H ↦ (((cartanEquiv H hH hstar hexp).symm g).2 : Matrix n n 𝕜)) :=
      ((selfAdjoint.contDiff_subtype_val ℝ).contMDiff.comp (contMDiff_snd.comp
        ((GeneralLinearGroup.cartanDiffeomorph n 𝕜).symm.contMDiff.comp hιH.contMDiff))).congr
          fun g ↦ (coe_cartanEquiv_symm_apply_snd hH hstar hexp g).trans
            (GeneralLinearGroup.coe_cartanDiffeomorph_symm_apply_snd (g : GL n 𝕜)).symm
    -- A continuous linear projection onto `𝔭_H` makes the Hermitian factor smooth into `𝔭_H`.
    obtain ⟨π, hπ⟩ := Submodule.ClosedComplemented.of_finiteDimensional H.hermitianLieSubmodule
    exact ContMDiff.prodMk ((ContMDiff.iff_comp_isImmersion hιK).2
      ⟨Topology.IsInducing.subtypeVal.continuous_iff.2 hU.continuous, hU⟩)
      ((π.contDiff.comp_contMDiff hlog).congr fun g ↦ (hπ _).symm)

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
  exact congrArg Units.val (coe_cartanEquiv_apply hH hstar hexp p)

/-- The unitary factor of the smooth Cartan decomposition of `g ∈ H` is the polar unitary factor
of `g`. -/
@[simp]
theorem coe_cartanDiffeomorph_symm_apply_fst (g : H) :
    (((H.cartanDiffeomorph hH hstar hexp hιH hιK).symm g).1 : GL n 𝕜) =
      Unitary.toUnits (g : GL n 𝕜).polarUnitary :=
  coe_cartanEquiv_symm_apply_fst hH hstar hexp g

/-- The Hermitian factor of the smooth Cartan decomposition of `g ∈ H` is the logarithm of
`√(gᴴ g)`. -/
@[simp]
theorem coe_cartanDiffeomorph_symm_apply_snd (g : H) :
    (((H.cartanDiffeomorph hH hstar hexp hιH hιK).symm g).2 : Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) :=
  coe_cartanEquiv_symm_apply_snd hH hstar hexp g

end Subgroup
