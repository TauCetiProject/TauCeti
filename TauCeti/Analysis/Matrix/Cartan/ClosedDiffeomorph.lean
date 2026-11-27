/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan.Closed
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Topology.Algebra.Star.Unitary

/-!
# The smooth Cartan decomposition of a closed matrix group stable under conjugate transpose

Let `H` be a closed subgroup of `GL(n, 𝕜)`, for `𝕜 = ℝ` or `ℂ`, stable under the conjugate
transpose and with finitely many connected components. `Subgroup.cartanHomeomorphOfIsClosed`
identifies `H` topologically with the product of `K_H`, the unitary elements of `H`, and `𝔭_H`,
the Hermitian part of the Lie algebra of `H`, by `(k, X) ↦ k * exp X`. This file proves that this
homeomorphism is a diffeomorphism.

The smooth structures are those of embedded submanifolds: `H` carries any manifold structure for
which the inclusion `H → GL(n, 𝕜)` is a smooth embedding, `K_H`, viewed as a subgroup of the unitary
group, any manifold structure for which its inclusion into the native unitary Lie group is a
smooth embedding, and `𝔭_H` is a real vector subspace of the Hermitian matrices. The
closed-subgroup theorem (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` with
`TauCeti.Lie.EmbeddedLieSubgroupData.isSmoothEmbedding_subtypeVal`) supplies such structures on
`H` and `K_H`.

Both directions reduce to the smooth Cartan decomposition
`Matrix.GeneralLinearGroup.cartanDiffeomorph` of `GL(n, 𝕜)` itself: a map into a smoothly embedded
submanifold is smooth exactly when its composite with the embedding is
(`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`), and a map into the vector subspace `𝔭_H` is
smooth when its composite with the inclusion is, through a continuous linear projection onto
`𝔭_H`.

## Main definitions and results

* `Subgroup.hermitianLieSubmodule`: the real subspace `𝔭_H` of Hermitian matrices in the Lie algebra
  `Subgroup.linearLieSubalgebra H`, with `Subgroup.mem_hermitianLieSubmodule_iff` describing it for
  closed `H` as the Hermitian `X` with `exp (t X) ∈ H` for every real `t`.
* `Subgroup.isCompact_unitaryPart`: the unitary part `K_H` of `H` is compact.
* `Subgroup.cartanHomeomorphOfIsClosed'`: the Cartan homeomorphism `K_H × 𝔭_H ≃ₜ H` with `K_H` a
  subgroup of the unitary group and `𝔭_H` a vector subspace.
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

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Subgroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] (H : Subgroup (GL n 𝕜))

/-- The Hermitian part `𝔭_H` of the Lie algebra of a subgroup `H` of `GL n 𝕜`: the Hermitian
matrices in `Subgroup.linearLieSubalgebra H`, as a real subspace of the Hermitian matrices. For
closed `H` these are the Hermitian `X` with `exp (t X) ∈ H` for every real `t`
(`Subgroup.mem_hermitianLieSubmodule_iff`). -/
def hermitianLieSubmodule : Submodule ℝ (selfAdjoint (Matrix n n 𝕜)) where
  carrier := {X | (X : Matrix n n 𝕜) ∈ H.linearLieSubalgebra}
  add_mem' hX hY := H.linearLieSubalgebra.add_mem hX hY
  zero_mem' := H.linearLieSubalgebra.zero_mem
  smul_mem' c _ hX := H.linearLieSubalgebra.smul_mem c hX

variable {H}

/-- Membership in `𝔭_H` is membership of the underlying matrix in the Lie algebra of `H`. -/
theorem mem_hermitianLieSubmodule {X : selfAdjoint (Matrix n n 𝕜)} :
    X ∈ H.hermitianLieSubmodule ↔ (X : Matrix n n 𝕜) ∈ H.linearLieSubalgebra :=
  Iff.rfl

/-- For a closed subgroup `H`, the Hermitian part `𝔭_H` of its Lie algebra consists of the
Hermitian `X` whose whole exponential line `exp (t X)` lies in `H`. -/
theorem mem_hermitianLieSubmodule_iff (hH : IsClosed (H : Set (GL n 𝕜)))
    {X : selfAdjoint (Matrix n n 𝕜)} :
    X ∈ H.hermitianLieSubmodule ↔
      ∀ t : ℝ, ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • (X : Matrix n n 𝕜)) :=
  (forall_exists_mem_coe_eq_exp_smul_iff_mem_linearLieSubalgebra hH _).symm

/-- The unitary part `K_H` of a closed subgroup `H` of `GL n 𝕜` is closed in the unitary group. -/
theorem isClosed_unitaryPart (hH : IsClosed (H : Set (GL n 𝕜))) :
    IsClosed ((H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜) :
      Subgroup (unitaryGroup n 𝕜)) : Set (unitaryGroup n 𝕜)) :=
  hH.preimage Unitary.continuous_toUnits

/-- The unitary part `K_H` of a closed subgroup `H` of `GL n 𝕜` is compact. -/
theorem isCompact_unitaryPart (hH : IsClosed (H : Set (GL n 𝕜))) :
    IsCompact ((H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜) :
      Subgroup (unitaryGroup n 𝕜)) : Set (unitaryGroup n 𝕜)) :=
  (isClosed_unitaryPart hH).isCompact

variable (H) in
/-- **The Cartan decomposition of a closed matrix group stable under the conjugate transpose**,
with its factors as a subgroup `K_H` of the unitary group and a vector subspace `𝔭_H` of the
Hermitian matrices: `Subgroup.cartanHomeomorphOfIsClosed` with its domain rewritten. -/
def cartanHomeomorphOfIsClosed' (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) :
    H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜) × H.hermitianLieSubmodule ≃ₜ H :=
  (((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).prodCongr
    ((Homeomorph.refl _).subtype fun _ ↦ mem_hermitianLieSubmodule_iff hH)).trans
    (H.cartanHomeomorphOfIsClosed hH hstar hfin)

/-- The Cartan decomposition of `H` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanHomeomorphOfIsClosed'_apply (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H))
    (p : H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜) × H.hermitianLieSubmodule) :
    ((H.cartanHomeomorphOfIsClosed' hH hstar hfin p : GL n 𝕜) : Matrix n n 𝕜) =
      ((p.1 : unitaryGroup n 𝕜) : Matrix n n 𝕜) *
        NormedSpace.exp ((p.2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) :=
  val_cartanHomeomorphOfIsClosed_apply hH hstar hfin _

/-- The unitary factor of the Cartan decomposition of `g ∈ H` is the polar unitary factor of
`g`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed'_symm_apply_fst (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    (((H.cartanHomeomorphOfIsClosed' hH hstar hfin).symm g).1 : unitaryGroup n 𝕜) =
      (g : GL n 𝕜).polarUnitary :=
  coe_cartanHomeomorphOfIsClosed_symm_apply_fst hH hstar hfin g

/-- The Hermitian factor of the Cartan decomposition of `g ∈ H` is the logarithm of `√(gᴴ g)`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed'_symm_apply_snd (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    ((((H.cartanHomeomorphOfIsClosed' hH hstar hfin).symm g).2 : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) :=
  coe_cartanHomeomorphOfIsClosed_symm_apply_snd hH hstar hfin g

/-- **`H` is connected exactly when its unitary part `K_H` is**: the Cartan decomposition
identifies `H` with `K_H × 𝔭_H`, and the vector space `𝔭_H` is connected. -/
theorem connectedSpace_iff_connectedSpace_unitaryPart (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) :
    ConnectedSpace H ↔
      ConnectedSpace (H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜)) := by
  let e := H.cartanHomeomorphOfIsClosed' hH hstar hfin
  constructor
  · intro _
    exact (Prod.fst_surjective.comp e.symm.surjective).connectedSpace
      (continuous_fst.comp e.symm.continuous)
  · intro _
    have : ConnectedSpace H.hermitianLieSubmodule :=
      connectedSpace_iff_univ.2 (convex_univ.isConnected Set.univ_nonempty)
    exact e.surjective.connectedSpace e.continuous

/-- The Hermitian part of the Lie algebra of the whole group `GL n 𝕜` is the space of all
Hermitian matrices. -/
@[simp]
theorem hermitianLieSubmodule_top : (⊤ : Subgroup (GL n 𝕜)).hermitianLieSubmodule = ⊤ :=
  eq_top_iff.2 fun X _ ↦ (mem_hermitianLieSubmodule_iff isClosed_univ).2 fun t ↦
    ⟨TauCeti.expUnit (t • (X : Matrix n n 𝕜)), mem_top _, TauCeti.expUnit_coe _⟩

/-! ### Smoothness -/

section Smooth

/-- The Hermitian matrices form a finite-dimensional real vector space. -/
private instance finiteDimensionalSelfAdjointMatrix {m : Type*} [Finite m] :
    FiniteDimensional ℝ (selfAdjoint (Matrix m m 𝕜)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix m m 𝕜)))

variable {EH EK : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [NormedAddCommGroup EK]
  [NormedSpace ℝ EK] [ChartedSpace EH H]
  [ChartedSpace EK (H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜))]

/-- A map into `𝔭_H` is smooth when its composite with the inclusion into the Hermitian matrices
is: compose with a continuous linear projection onto the finite-dimensional subspace `𝔭_H`. -/
private theorem contMDiff_codRestrict_hermitianLieSubmodule {EM HM : Type*}
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {f : M → selfAdjoint (Matrix n n 𝕜)}
    (hf : ContMDiff IM 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) ∞ f)
    (hmem : ∀ x, f x ∈ H.hermitianLieSubmodule) :
    ContMDiff IM 𝓘(ℝ, H.hermitianLieSubmodule) ∞
      (fun x ↦ (⟨f x, hmem x⟩ : H.hermitianLieSubmodule)) := by
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional_quotient
    (Submodule.isClosed_of_finiteDimensional H.hermitianLieSubmodule)
  have hc : ContDiff ℝ ∞ P := by exact ContinuousLinearMap.contDiff _
  have hPf : ContMDiff IM 𝓘(ℝ, H.hermitianLieSubmodule) ∞ (fun x ↦ P (f x)) :=
    hc.contMDiff.comp hf
  exact hPf.congr fun x ↦ (hP ⟨f x, hmem x⟩).symm

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
      (Subtype.val : H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜) →
        unitaryGroup n 𝕜)) :
    (H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜) × H.hermitianLieSubmodule) ≃ₘ^∞⟮
      𝓘(ℝ, EK).prod 𝓘(ℝ, H.hermitianLieSubmodule), 𝓘(ℝ, EH)⟯ H where
  toEquiv := (H.cartanHomeomorphOfIsClosed' hH hstar hfin).toEquiv
  contMDiff_toFun := by
    refine hHe.contMDiff_iff_comp.2 ?_
    have hsub : ContMDiff 𝓘(ℝ, H.hermitianLieSubmodule) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) ∞
        (Subtype.val : H.hermitianLieSubmodule → selfAdjoint (Matrix n n 𝕜)) :=
      have hc : ContDiff ℝ ∞ H.hermitianLieSubmodule.subtypeL := by
        exact ContinuousLinearMap.contDiff _
      hc.contMDiff
    have h := (cartanDiffeomorph n 𝕜).contMDiff.comp
      ((hKe.contMDiff.comp contMDiff_fst).prodMk (hsub.comp contMDiff_snd))
    refine h.congr fun p ↦ Units.ext ?_
    exact (val_cartanHomeomorphOfIsClosed'_apply hH hstar hfin p).trans
      (val_cartanDiffeomorph_apply ((p.1 : unitaryGroup n 𝕜), (p.2 : selfAdjoint _))).symm
  contMDiff_invFun := by
    have hsymm := (cartanDiffeomorph n 𝕜).symm.contMDiff.comp hHe.contMDiff
    refine ContMDiff.prodMk ?_ ?_
    · refine hKe.contMDiff_iff_comp.2 ((contMDiff_fst.comp hsymm).congr fun g ↦ ?_)
      exact (coe_cartanHomeomorphOfIsClosed'_symm_apply_fst hH hstar hfin g).trans
        (cartanDiffeomorph_symm_apply_fst _).symm
    · refine (contMDiff_codRestrict_hermitianLieSubmodule (contMDiff_snd.comp hsymm)
        fun g ↦ ?_).congr fun g ↦ ?_
      · have hX := ((H.cartanHomeomorphOfIsClosed' hH hstar hfin).symm g).2.property
        convert hX using 2
        exact Subtype.ext ((coe_cartanDiffeomorph_symm_apply_snd _).trans
          (coe_cartanHomeomorphOfIsClosed'_symm_apply_snd hH hstar hfin g).symm)
      · exact Subtype.ext <| Subtype.ext <|
          (coe_cartanHomeomorphOfIsClosed'_symm_apply_snd hH hstar hfin g).trans
            (coe_cartanDiffeomorph_symm_apply_snd _).symm

variable (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
  (hfin : Finite (ConnectedComponents H))
  (hHe : IsSmoothEmbedding 𝓘(ℝ, EH) 𝓘(ℝ, Matrix n n 𝕜) ∞ (Subtype.val : H → GL n 𝕜))
  (hKe : IsSmoothEmbedding 𝓘(ℝ, EK) (Unitary.model (Matrix n n 𝕜)) ∞
    (Subtype.val : H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜) → unitaryGroup n 𝕜))

/-- The smooth Cartan decomposition has the Cartan homeomorphism as its underlying map. -/
@[simp]
theorem cartanDiffeomorphOfIsClosed_toHomeomorph :
    (H.cartanDiffeomorphOfIsClosed hH hstar hfin hHe hKe).toHomeomorph =
      H.cartanHomeomorphOfIsClosed' hH hstar hfin :=
  Homeomorph.ext fun _ ↦ rfl

/-- The smooth Cartan decomposition of `H` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanDiffeomorphOfIsClosed_apply
    (p : H.comap (Unitary.toUnits : unitaryGroup n 𝕜 →* GL n 𝕜) × H.hermitianLieSubmodule) :
    ((H.cartanDiffeomorphOfIsClosed hH hstar hfin hHe hKe p : GL n 𝕜) : Matrix n n 𝕜) =
      ((p.1 : unitaryGroup n 𝕜) : Matrix n n 𝕜) *
        NormedSpace.exp ((p.2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) :=
  val_cartanHomeomorphOfIsClosed'_apply hH hstar hfin p

/-- The unitary factor of the smooth Cartan decomposition of `g ∈ H` is the polar unitary factor
of `g`. -/
@[simp]
theorem coe_cartanDiffeomorphOfIsClosed_symm_apply_fst (g : H) :
    (((H.cartanDiffeomorphOfIsClosed hH hstar hfin hHe hKe).symm g).1 : unitaryGroup n 𝕜) =
      (g : GL n 𝕜).polarUnitary :=
  coe_cartanHomeomorphOfIsClosed'_symm_apply_fst hH hstar hfin g

/-- The Hermitian factor of the smooth Cartan decomposition of `g ∈ H` is the logarithm of
`√(gᴴ g)`. -/
@[simp]
theorem coe_cartanDiffeomorphOfIsClosed_symm_apply_snd (g : H) :
    ((((H.cartanDiffeomorphOfIsClosed hH hstar hfin hHe hKe).symm g).2 :
        selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) :=
  coe_cartanHomeomorphOfIsClosed'_symm_apply_snd hH hstar hfin g

end Smooth

end Subgroup
