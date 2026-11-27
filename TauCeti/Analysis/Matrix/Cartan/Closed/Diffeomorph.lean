/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan.Closed.Basic
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.Geometry.Manifold.ContMDiff.Submodule
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The smooth Cartan decomposition of a closed matrix group stable under conjugate transpose

Let `H` be a closed subgroup of `GL(n, 𝕜)`, for `𝕜 = ℝ` or `ℂ`, stable under the conjugate
transpose and with finitely many connected components. `Subgroup.cartanHomeomorphOfIsClosed`
identifies `H` topologically with the product of its unitary part `K_H = Subgroup.unitaryPart H`
and the Hermitian part `𝔭_H = Subgroup.hermitianLieSubmodule H` of its Lie algebra, by
`(k, X) ↦ k * exp X`. This file proves that this homeomorphism is a diffeomorphism.

The smooth structures are those of embedded submanifolds: `H` carries any manifold structure for
which the inclusion `H → GL(n, 𝕜)` is a smooth embedding, `K_H`, a subgroup of the unitary group,
any manifold structure for which its inclusion into the native unitary Lie group is a smooth
embedding, and `𝔭_H` is a real vector subspace of the matrices. The closed-subgroup
theorem (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` with
`TauCeti.Lie.EmbeddedLieSubgroupData.isSmoothEmbedding_subtypeVal`) supplies such structures on
`H` and `K_H`.

Both directions reduce to the smooth Cartan decomposition
`Matrix.GeneralLinearGroup.cartanDiffeomorph` of `GL(n, 𝕜)` itself: a map into a smoothly embedded
submanifold is smooth exactly when its composite with the embedding is
(`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`), and a map into the finite-dimensional subspace
`𝔭_H` is smooth when its composite with the inclusion is (`ContMDiff.codRestrict_submodule`).

`Subgroup.cartanDiffeomorph` (in `TauCeti/Analysis/Matrix/Cartan/Diffeomorph.lean`) is the same
diffeomorphism with `K_H` taken as the subgroup `H ⊓ unitarySubgroup (GL n 𝕜)` of `GL n 𝕜` and the
line hypothesis of `Subgroup.cartanHomeomorph` in place of finitely many components; here `K_H` is
the subgroup `Subgroup.unitaryPart H` of the unitary group, with its own smooth structure.

## Main definitions and results

* `Subgroup.cartanDiffeomorphOfIsClosed`: **the smooth Cartan decomposition** `K_H × 𝔭_H ≃ₘ H`, with
  `Subgroup.val_cartanDiffeomorphOfIsClosed_apply`,
  `Subgroup.coe_cartanDiffeomorphOfIsClosed_symm_apply_fst` and
  `Subgroup.coe_cartanDiffeomorphOfIsClosed_symm_apply_snd`.

## References

* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1.
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup Manifold

open scoped ContDiff Manifold MatrixOrder Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal TauCeti.normedAlgebraRatOfReal

namespace Subgroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {H : Subgroup (GL n 𝕜)}

variable {EH EK : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [NormedAddCommGroup EK]
  [NormedSpace ℝ EK] [ChartedSpace EH H] [ChartedSpace EK H.unitaryPart]

/-- The Hermitian factor of the Cartan decomposition of `GL n 𝕜` at `g ∈ H` is the Hermitian factor
of the Cartan decomposition of `H`. -/
private theorem cartanDiffeomorph_symm_apply_snd_eq (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    ((((cartanDiffeomorph n 𝕜).symm g).2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      (((H.cartanHomeomorphOfIsClosed hH hstar hfin).symm g).2 : Matrix n n 𝕜) :=
  (coe_cartanDiffeomorph_symm_apply_snd _).trans
    (coe_cartanHomeomorphOfIsClosed_symm_apply_snd hH hstar hfin g).symm

variable (H) in
/-- **The smooth Cartan decomposition of a closed matrix group stable under the conjugate
transpose.** Let `H` be a closed subgroup of `GL n 𝕜`, for `𝕜 = ℝ` or `ℂ`, stable under the
conjugate transpose and with finitely many connected components. Give `H` a manifold structure for
which its inclusion into `GL n 𝕜` is a smooth embedding, and its unitary part `K_H` one for which
its inclusion into the unitary group is a smooth embedding (for instance the closed-subgroup
structures `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`). Then `(k, X) ↦ k * exp X` is a
diffeomorphism from `K_H × 𝔭_H` onto `H`.

Matrices carry the `ℓ²` operator norm: open the `Matrix.Norms.L2Operator` scope and enable
`Matrix.l2OpNormedAlgebraReal` as a local instance. -/
def cartanDiffeomorphOfIsClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H))
    (hHe : IsSmoothEmbedding 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞ (Subtype.val : H → GL n 𝕜))
    (hKe : IsSmoothEmbedding 𝓘(ℝ, EK) (Unitary.model (Matrix n n 𝕜)) ∞
      (Subtype.val : H.unitaryPart → unitaryGroup n 𝕜)) :
    (H.unitaryPart × H.hermitianLieSubmodule) ≃ₘ^∞⟮
      𝓘(ℝ, EK).prod 𝓘(ℝ, H.hermitianLieSubmodule), 𝓘(ℝ, EH)⟯ H where
  toEquiv := (H.cartanHomeomorphOfIsClosed hH hstar hfin).toEquiv
  contMDiff_toFun := by
    refine hHe.contMDiff_iff_comp.2 ?_
    -- The inclusion of `𝔭_H` into the Hermitian matrices is linear, hence smooth.
    let ι : H.hermitianLieSubmodule →ₗ[ℝ] selfAdjoint (Matrix n n 𝕜) :=
      { toFun X := ⟨X, (mem_hermitianLieSubmodule.1 X.property).1⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    have h := (cartanDiffeomorph n 𝕜).contMDiff.comp ((hKe.contMDiff.comp contMDiff_fst).prodMk
      (ι.toContinuousLinearMap.contDiff.contMDiff.comp contMDiff_snd))
    refine h.congr fun p ↦ Units.ext ?_
    exact (val_cartanHomeomorphOfIsClosed_apply hH hstar hfin p).trans
      (val_cartanDiffeomorph_apply ((p.1 : unitaryGroup n 𝕜), ι p.2)).symm
  contMDiff_invFun := by
    have hsymm := (cartanDiffeomorph n 𝕜).symm.contMDiff.comp hHe.contMDiff
    refine ContMDiff.prodMk ?_ ?_
    · refine hKe.contMDiff_iff_comp.2 ((contMDiff_fst.comp hsymm).congr fun g ↦ ?_)
      exact (coe_cartanHomeomorphOfIsClosed_symm_apply_fst hH hstar hfin g).trans
        (cartanDiffeomorph_symm_apply_fst _).symm
    · -- The Hermitian factor lies in the subspace `𝔭_H`, which is complemented: the matrices are
      -- finite-dimensional.
      refine (((selfAdjoint.contDiff_subtype_val ℝ).contMDiff.comp
        (contMDiff_snd.comp hsymm)).codRestrict_submodule
          (.of_finiteDimensional_quotient (Submodule.isClosed_of_finiteDimensional _))
            fun g ↦ ?_).congr fun g ↦
          Subtype.ext (cartanDiffeomorph_symm_apply_snd_eq hH hstar hfin g).symm
      change ((((cartanDiffeomorph n 𝕜).symm g).2 : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) ∈ H.hermitianLieSubmodule
      rw [cartanDiffeomorph_symm_apply_snd_eq hH hstar hfin]
      exact ((H.cartanHomeomorphOfIsClosed hH hstar hfin).symm g).2.property

variable (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
  (hfin : Finite (ConnectedComponents H))
  (hHe : IsSmoothEmbedding 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞ (Subtype.val : H → GL n 𝕜))
  (hKe : IsSmoothEmbedding 𝓘(ℝ, EK) (Unitary.model (Matrix n n 𝕜)) ∞
    (Subtype.val : H.unitaryPart → unitaryGroup n 𝕜))

/-- The smooth Cartan decomposition has the Cartan homeomorphism as its underlying map. -/
@[simp]
theorem cartanDiffeomorphOfIsClosed_toHomeomorph :
    (H.cartanDiffeomorphOfIsClosed hH hstar hfin hHe hKe).toHomeomorph =
      H.cartanHomeomorphOfIsClosed hH hstar hfin :=
  Homeomorph.ext fun _ ↦ rfl

/-- The smooth Cartan decomposition of `H` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanDiffeomorphOfIsClosed_apply (p : H.unitaryPart × H.hermitianLieSubmodule) :
    ((H.cartanDiffeomorphOfIsClosed hH hstar hfin hHe hKe p : GL n 𝕜) : Matrix n n 𝕜) =
      ((p.1 : unitaryGroup n 𝕜) : Matrix n n 𝕜) * NormedSpace.exp (p.2 : Matrix n n 𝕜) :=
  val_cartanHomeomorphOfIsClosed_apply hH hstar hfin p

/-- The unitary factor of the smooth Cartan decomposition of `g ∈ H` is the polar unitary factor
of `g`. -/
@[simp]
theorem coe_cartanDiffeomorphOfIsClosed_symm_apply_fst (g : H) :
    (((H.cartanDiffeomorphOfIsClosed hH hstar hfin hHe hKe).symm g).1 : unitaryGroup n 𝕜) =
      (g : GL n 𝕜).polarUnitary :=
  coe_cartanHomeomorphOfIsClosed_symm_apply_fst hH hstar hfin g

/-- The Hermitian factor of the smooth Cartan decomposition of `g ∈ H` is the logarithm of
`√(gᴴ g)`. -/
@[simp]
theorem coe_cartanDiffeomorphOfIsClosed_symm_apply_snd (g : H) :
    (((H.cartanDiffeomorphOfIsClosed hH hstar hfin hHe hKe).symm g).2 : Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) :=
  coe_cartanHomeomorphOfIsClosed_symm_apply_snd hH hstar hfin g

end Subgroup
