/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.EulerClass
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Normal.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Topology.VectorBundle.Orientation.Comap
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
import TauCeti.Topology.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv

/-!
# The normal Euler number of a Lagrangian submanifold

Let `f : M → N` be an embedding of an `n`-manifold `M` into a `2n`-manifold `N` with a two-form `σ`
taming an almost complex structure `J`, for instance a symplectic manifold with a compatible `J`,
and suppose that `f` is Lagrangian. At each point `x` the structure `J` identifies the tangent space
of `M` with the normal space `N_x = T_{f x} N ⧸ df_x(T_x M)` of the embedding by

`v ↦ [J df_x v]`

(`TauCeti.SmoothEmbedding.tangentEquivNormalSpaceOfIsLagrangianMap`), since `J` carries the
Lagrangian tangent image to a complement of itself. These fibrewise isomorphisms are continuous on
total spaces (`TauCeti.SmoothEmbedding.continuous_tangentEquivNormalSpaceOfIsLagrangianMap`), so
they form an isomorphism of vector bundles `TM ≅ ν`.

An orientation `o` of `M` and the symplectic orientations of the tangent spaces of `N` induce an
orientation of each normal space: the one which, preceded by `o`, gives the symplectic orientation
(`Orientation.cokerOfExact`). By the linear computation
`TauCeti.SymplecticForm.Tames.cokerOfExact_orientation` it is `(-1) ^ n.choose 2` times the image of
`o` under the identification above. So these normal orientations vary continuously: they form an
orientation of the normal bundle
(`TauCeti.SmoothEmbedding.lagrangianNormalOrientation`,
`TauCeti.SmoothEmbedding.lagrangianNormalOrientation_apply`), and its Euler class is
`(-1) ^ n.choose 2` times the Euler class of `TM`
(`TauCeti.SmoothEmbedding.eulerClass_lagrangianNormalOrientation`). When `M` is compact and
boundaryless, evaluating on the fundamental class and using `e(TM)[M] = χ(M)` gives the **normal
Euler number of a Lagrangian submanifold**

`e(ν)[M] = (-1) ^ n.choose 2 χ(M)`

(`TauCeti.SmoothEmbedding.evalFundamentalClass_eulerClass_lagrangianNormalOrientation`).
For a Lagrangian surface in a symplectic four-manifold the sign is `-1`, so `e(ν)[M] = -χ(M)`
(`SmoothEmbedding.evalFundamentalClass_eulerClass_lagrangianNormalOrientation_of_finrank_eq_two`):
`J` reverses the normal orientation. For an embedded Lagrangian sphere it is `-2`
(`SmoothEmbedding.evalFundamentalClass_eulerClass_lagrangianNormalOrientation_sphere`).
This is the self-intersection number `-2` of a Lagrangian sphere; identifying the normal Euler
number with the homological self-intersection needs a tubular neighbourhood and is not done here.

## Main definitions

* `TauCeti.SmoothEmbedding.tangentEquivNormalSpaceOfIsLagrangianMap`: the identification
  `v ↦ [J df_x v]` of the tangent space of a Lagrangian embedding with its normal space.
* `TauCeti.SmoothEmbedding.lagrangianNormalOrientation`: the orientation of the normal
  bundle induced by an orientation of `M` and the symplectic orientation of `N`.

## Main results

* `TauCeti.SmoothEmbedding.lagrangianNormalOrientation_apply`: its fibres are the induced
  orientations `Orientation.cokerOfExact`.
* `TauCeti.SmoothEmbedding.eulerClass_lagrangianNormalOrientation`:
  `e(ν) = (-1) ^ n.choose 2 e(TM)`.
* `TauCeti.SmoothEmbedding.evalFundamentalClass_eulerClass_lagrangianNormalOrientation`:
  `e(ν)[M] = (-1) ^ n.choose 2 χ(M)` for compact `M`.
* `SmoothEmbedding.evalFundamentalClass_eulerClass_lagrangianNormalOrientation_sphere`: an
  embedded Lagrangian sphere in a symplectic four-manifold has normal Euler number `-2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix E (the self-intersection of a Lagrangian sphere).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), Corollary 11.12 (the Euler number of the tangent bundle).
-/

public section

noncomputable section

open Bundle Module Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

section Fibre

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold I' ∞ N] {n : ℕ∞ω}
  (f : SmoothEmbedding I I' n M N) (hn : n ≠ 0)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [IsManifold I' ∞ N] in
/-- The differential of an embedding followed by the normal projection is a short exact
sequence `0 → T_x M → T_{f x} N → N_x → 0`. -/
theorem exact_mfderiv_normalClass (x : M) :
    Exact (mfderiv I I' f x).toLinearMap (f.isImmersion.normalClass x hn) := by
  rw [LinearMap.exact_iff, Manifold.IsImmersion.normalClass_ker]
  rfl

variable {σ : SmoothTwoForm I' N} {J : SmoothAlmostComplexStructure I' N} (hJ : σ.Tames J)
  (hf : hJ.isNondegenerate.IsLagrangianMap I f)

include hJ hf

omit [FiniteDimensional ℝ E] in
/-- At each point of a Lagrangian embedding, the tangent image is a Lagrangian subspace of the
ambient tangent space, hence maximal totally real for a tamed `J`. -/
theorem isMaximalTotallyReal_tangentRange_of_isLagrangianMap (x : M) :
    IsMaximalTotallyReal (J.almostComplexStructureAt (f x)).toLinearMap
      (f.isImmersion.tangentRange x hn) :=
  (SmoothTwoForm.IsNondegenerate.isLagrangianMap_iff_forall.1 hf x).isMaximalTotallyReal_of_tames
    ((hJ.isNondegenerate.tames_iff).1 hJ (f x))

/-- **The tangent space of a Lagrangian embedding is its normal space.** For a Lagrangian
embedding `f` into a manifold with a two-form taming an almost complex structure `J`, the
identification `v ↦ [J df_x v]` of the tangent space `T_x M` with the normal space
`T_{f x} N ⧸ df_x(T_x M)`. -/
def tangentEquivNormalSpaceOfIsLagrangianMap (x : M) :
    TangentSpace I x ≃L[ℝ] f.isImmersion.NormalSpace x hn :=
  let e : TangentSpace I x ≃ₗ[ℝ] f.isImmersion.NormalSpace x hn :=
    (f.isImmersion.tangentSpaceEquivTangentRange x hn).toLinearEquiv.trans
      ((f.isMaximalTotallyReal_tangentRange_of_isLagrangianMap hn hJ hf x).normalEquiv
        ((J.almostComplexStructureAt (f x)).injective_domRestrict _))
  e.toContinuousLinearEquiv

/-- The identification of the tangent and normal spaces sends `v` to the normal class of
`J df_x v`. -/
@[simp]
theorem tangentEquivNormalSpaceOfIsLagrangianMap_apply (x : M) (v : TangentSpace I x) :
    f.tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf x v =
      f.isImmersion.normalClass x hn (J (f x) (mfderiv I I' f x v)) := by
  -- The identification is by definition `T_x M ≃ range (df_x) ≃ T_{f x} N ⧸ range (df_x)`; `change`
  -- exposes the two factors, which have evaluation lemmas, through the finite-dimensional upgrade.
  change (f.isMaximalTotallyReal_tangentRange_of_isLagrangianMap hn hJ hf x).normalEquiv _
    (f.isImmersion.tangentSpaceEquivTangentRange x hn v) = _
  rw [IsMaximalTotallyReal.normalEquiv_apply, Manifold.IsImmersion.normalClass_apply,
    Manifold.IsImmersion.coe_tangentSpaceEquivTangentRange_apply]
  exact congrArg Submodule.Quotient.mk (J.almostComplexStructureAt_apply (f x) _)

variable {k : ℕ} (hk : finrank ℝ V = k + k)

/-- **The induced normal orientation of a Lagrangian embedding.** The orientation of the normal
space `N_x` induced by an orientation `o` of `T_x M` of dimension `k` and the symplectic orientation
of `T_{f x} N` is `(-1) ^ k.choose 2` times the image of `o` under the identification
`v ↦ [J df_x v]`. -/
theorem cokerOfExact_eq_units_smul_map_tangentEquivNormalSpaceOfIsLagrangianMap (x : M)
    (o : Orientation ℝ (TangentSpace I x) (Fin k)) (hE : finrank ℝ E = k) :
    Orientation.cokerOfExact (f.isImmersion.mfderiv_injective hn x)
        (f.exact_mfderiv_normalClass hn x) (f.isImmersion.normalClass_surjective x hn) o
        ((hJ.isNondegenerate.symplecticFormAt (f x)).orientation hk) hE
        ((f.tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf x).toLinearEquiv.finrank_eq.symm.trans
          hE) =
      (-1 : ℝˣ) ^ k.choose 2 •
        Orientation.map (Fin k)
          (f.tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf x).toLinearEquiv o := by
  set L := f.isImmersion.tangentRange x hn
  set eA := (f.isImmersion.tangentSpaceEquivTangentRange x hn).toLinearEquiv
  have hL := f.isMaximalTotallyReal_tangentRange_of_isLagrangianMap hn hJ hf x
  have hLk : finrank ℝ L = k := eA.finrank_eq.symm.trans hE
  -- Read the sequence `T_x M → T_{f x} N → N_x` through `T_x M ≃ L`, as `L → T_{f x} N → N_x`.
  have hmap := Orientation.map_cokerOfExact (f.isImmersion.mfderiv_injective hn x)
    (f.exact_mfderiv_normalClass hn x) (f.isImmersion.normalClass_surjective x hn)
    L.injective_subtype (LinearMap.exact_subtype_mkQ L) L.mkQ_surjective eA (LinearEquiv.refl ℝ _)
    (LinearEquiv.refl ℝ _)
    (fun u ↦ (f.isImmersion.coe_tangentSpaceEquivTangentRange_apply x hn u).symm)
    (f.isImmersion.normalClass_apply x hn) o
    ((hJ.isNondegenerate.symplecticFormAt (f x)).orientation hk) hE
    ((f.tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf x).toLinearEquiv.finrank_eq.symm.trans
      hE)
  refine (DFunLike.congr_fun (Orientation.map_refl (R := ℝ)
    (M := f.isImmersion.NormalSpace x hn) (Fin k)) _).symm.trans (hmap.trans ?_)
  rw [Orientation.map_refl, Equiv.refl_apply,
    ((hJ.isNondegenerate.tames_iff).1 hJ (f x)).cokerOfExact_orientation hL _ hLk hk,
    ← Orientation.map_trans]
  -- The identification of `T_x M` with `N_x` is by definition the composite of these two maps.
  rfl

end Fibre

section Bundle

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold I' ∞ N] {n : ℕ∞ω}
  (f : SmoothEmbedding I I' n M N) (hn : n ≠ 0)
  {σ : SmoothTwoForm I' N} {J : SmoothAlmostComplexStructure I' N} (hJ : σ.Tames J)
  (hf : hJ.isNondegenerate.IsLagrangianMap I f)

include hJ hf

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- **The identification of the tangent and normal bundles is continuous.** The map
`v ↦ [J df v]` from the tangent bundle of a Lagrangian embedding to its normal bundle, with the
quotient topology of the normal bundle, is continuous. -/
theorem continuous_tangentEquivNormalSpaceOfIsLagrangianMap :
    Continuous fun v : TangentBundle I M ↦
      TotalSpace.mk' P (E := fun x ↦ f.isImmersion.NormalSpace x hn) v.proj
        (f.tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf v.proj v.snd) := by
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have h1 : (0 : ℕ∞ω) + 1 ≤ n := by
    rw [zero_add]
    exact ENat.one_le_iff_ne_zero_withTop.2 hn
  have hfc : ContMDiff I I' 0 f := f.contMDiff.of_le (le_self_add.trans h1)
  -- First `v ↦ J df v`, a vector of the pulled-back ambient tangent bundle, then its normal class.
  have hJtot : ContMDiff I'.tangent I'.tangent 0
      fun p : TangentBundle I' N ↦ TotalSpace.mk' V p.proj (J p.proj p.snd) :=
    J.contMDiff_apply (V := fun p : TangentBundle I' N ↦ p.snd) contMDiff_id
  have hT : ContMDiff I.tangent (I.prod 𝓘(ℝ, V)) 0
      fun v : TangentBundle I M ↦
        TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace I')) v.proj
          (J (f v.proj) (mfderiv I I' f v.proj v.snd)) :=
    (Bundle.Pullback.contMDiff_iff f hfc).2
      ⟨contMDiff_proj _, hJtot.comp (f.contMDiff.contMDiff_tangentMap h1)⟩
  refine ((f.isQuotientMap_normalQuotientMap (K := P) hn).continuous.comp hT.continuous).congr
    fun v ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply, tangentEquivNormalSpaceOfIsLagrangianMap_apply]

variable (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {k : ℕ} (hE : finrank ℝ E = k)
  (hk : finrank ℝ V = k + k) (oM : Manifold.Orientation I M (Fin k))

/-- **The induced normal orientation of a Lagrangian embedding.** For an orientation `oM` of a
`k`-manifold `M` and a Lagrangian embedding into a `2k`-manifold with a two-form `σ` taming an
almost complex structure `J`, the orientation of the normal bundle which, preceded by `oM`, gives
the symplectic orientation of `σ` at every point
(`TauCeti.SmoothEmbedding.lagrangianNormalOrientation_apply`). It is `(-1) ^ k.choose 2` times the
image of `oM` under the identification `v ↦ [J df v]`; its fibres do not depend on `J`. -/
def lagrangianNormalOrientation :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin k) :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  let o := oM.toVectorBundleOrientation.comap (g := ContinuousMap.id M)
    (φ := fun x ↦ (f.tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf x).symm)
    (by rw [Fintype.card_fin, hdim, hk, hE, Nat.add_sub_cancel])
    (continuous_bundle_symm _ (f.continuous_tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf))
  if Even (k.choose 2) then o else -o

/-- **The fibres of the induced normal orientation.** At each point `x`, the induced normal
orientation of a Lagrangian embedding is the orientation of `N_x` which, preceded by the
orientation of `T_x M`, gives the symplectic orientation of `T_{f x} N`. -/
theorem lagrangianNormalOrientation_apply (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.lagrangianNormalOrientation hn hJ hf hdim hE hk oM x =
      Orientation.cokerOfExact (f.isImmersion.mfderiv_injective hn x)
        (f.exact_mfderiv_normalClass hn x) (f.isImmersion.normalClass_surjective x hn)
        (oM.orientationAt x) ((hJ.isNondegenerate.symplecticFormAt (f x)).orientation hk) hE
        ((f.tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf x).toLinearEquiv.finrank_eq.symm.trans
          hE) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [f.cokerOfExact_eq_units_smul_map_tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf hk]
  unfold lagrangianNormalOrientation
  dsimp only
  split_ifs with h
  -- In both cases the transported fibre is the image of `oM` under `(φ x).symm.symm = φ x`. The
  -- double inverse lives over `ContinuousMap.id M x` rather than `x`, so `symm_symm` cannot be
  -- rewritten, and `rfl` closes it by structure eta.
  · rw [h.neg_one_pow, one_smul]
    refine (VectorBundleOrientation.comap_apply _ _ _ x).trans ?_
    rw [Manifold.Orientation.toVectorBundleOrientation_apply]
    rfl
  · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, Module.Ray.neg_units_smul, one_smul]
    refine (VectorBundleOrientation.neg_apply _ x).trans
      (congrArg Neg.neg ((VectorBundleOrientation.comap_apply _ _ _ x).trans ?_))
    rw [Manifold.Orientation.toVectorBundleOrientation_apply]
    rfl

end Bundle

section EulerClass

universe u

variable {E V P : Type u} {H G N : Type*} {M : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold I' ∞ N] {n : ℕ∞ω}
  (f : SmoothEmbedding I I' n M N) (hn : n ≠ 0)
  {σ : SmoothTwoForm I' N} {J : SmoothAlmostComplexStructure I' N} (hJ : σ.Tames J)
  (hf : hJ.isNondegenerate.IsLagrangianMap I f)
  (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {k : ℕ} (hE : finrank ℝ E = k + 1)
  (hk : finrank ℝ V = k + 1 + (k + 1)) (oM : Manifold.Orientation I M (Fin (k + 1)))

include hJ hf

/-- **The normal Euler class of a Lagrangian embedding.** For a Lagrangian embedding of an
oriented `(k + 1)`-manifold `M` into a `2(k + 1)`-manifold with a two-form taming an almost
complex structure, the Euler class of the normal bundle with its induced orientation is
`(-1) ^ (k + 1).choose 2` times the Euler class of the tangent bundle of `M`. -/
theorem eulerClass_lagrangianNormalOrientation :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.lagrangianNormalOrientation hn hJ hf hdim hE hk oM).eulerClass
        (by rw [hdim, hk, hE, Nat.add_sub_cancel]) =
      ((-1 : ℤ) ^ (k + 1).choose 2) • oM.toVectorBundleOrientation.eulerClass hE := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have hc := VectorBundleOrientation.eulerClass_comap_id
    (φ := fun x ↦ (f.tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf x).symm)
    oM.toVectorBundleOrientation hE
    (by rw [hdim, hk, hE, Nat.add_sub_cancel] : finrank ℝ P = k + 1)
    (continuous_bundle_symm _ (f.continuous_tangentEquivNormalSpaceOfIsLagrangianMap hn hJ hf))
  unfold lagrangianNormalOrientation
  dsimp only
  split_ifs with h
  · rw [h.neg_one_pow, one_smul]
    exact hc
  · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, neg_one_zsmul,
      VectorBundleOrientation.eulerClass_neg]
    exact congrArg Neg.neg hc

end EulerClass

section EulerNumber

variable {X V P G N : Type} {M : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace G] {I' : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace X M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, X) ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold I' ∞ N] {n : ℕ∞ω}
  (f : SmoothEmbedding 𝓘(ℝ, X) I' n M N) (hn : n ≠ 0)
  {σ : SmoothTwoForm I' N} {J : SmoothAlmostComplexStructure I' N} (hJ : σ.Tames J)
  (hf : hJ.isNondegenerate.IsLagrangianMap 𝓘(ℝ, X) f)
  (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ X)

include hJ hf

/-- **The normal Euler number of a Lagrangian submanifold.** Let `M` be a compact boundaryless
manifold of dimension `k + 1`, oriented by `oM`, and `f` a Lagrangian embedding of `M` into a
`2(k + 1)`-manifold with a two-form taming an almost complex structure. The Euler class of the
normal bundle of `f`, with the orientation induced by `oM` and the symplectic orientation,
evaluates on the fundamental class of `M` to `(-1) ^ (k + 1).choose 2 χ(M)`. -/
theorem evalFundamentalClass_eulerClass_lagrangianNormalOrientation {k : ℕ}
    (hX : finrank ℝ X = k + 1) (hk : finrank ℝ V = k + 1 + (k + 1))
    (oM : Manifold.Orientation 𝓘(ℝ, X) M (Fin (k + 1))) :
    haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, X)) M
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ((oM.toHomologicalOrientation hX).evalFundamentalClass hX (ModuleCat.of ℤ (ULift.{0} ℤ))
        (ContinuousMap.id M) ((f.lagrangianNormalOrientation hn hJ hf hdim hX hk oM).eulerClass
          (by rw [hdim, hk, hX, Nat.add_sub_cancel]))).down =
      (-1) ^ (k + 1).choose 2 * eulerChar M := by
  have := FiniteCWType.of_isManifold (I := 𝓘(ℝ, X)) M
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [f.eulerClass_lagrangianNormalOrientation hn hJ hf hdim hX hk oM, map_zsmul,
    ULift.smul_down, smul_eq_mul, Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar]

/-- **A Lagrangian surface has normal Euler number `-χ`.** For a Lagrangian embedding of a compact
oriented surface `M` into a four-manifold with a two-form taming an almost complex structure, the
Euler class of the normal bundle, with the orientation induced by the orientation of `M` and the
symplectic orientation, evaluates on the fundamental class of `M` to `-χ(M)`: the identification
`v ↦ [J df v]` of the tangent and normal bundles reverses the orientations. -/
theorem evalFundamentalClass_eulerClass_lagrangianNormalOrientation_of_finrank_eq_two
    (hX : finrank ℝ X = 2) (hk : finrank ℝ V = 2 + 2)
    (oM : Manifold.Orientation 𝓘(ℝ, X) M (Fin 2)) :
    haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, X)) M
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ((oM.toHomologicalOrientation hX).evalFundamentalClass hX (ModuleCat.of ℤ (ULift.{0} ℤ))
        (ContinuousMap.id M) ((f.lagrangianNormalOrientation hn hJ hf hdim hX hk oM).eulerClass
          (by rw [hdim, hk, hX]))).down =
      -eulerChar M := by
  rw [f.evalFundamentalClass_eulerClass_lagrangianNormalOrientation hn hJ hf hdim (k := 1) hX
    hk oM]
  norm_num

end EulerNumber

section Sphere

variable {V P G N : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace G] {I' : ModelWithCorners ℝ V G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold I' ∞ N] {n : ℕ∞ω}
  (f : SmoothEmbedding (𝓡 2) I' n (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) N)
  (hn : n ≠ 0) {σ : SmoothTwoForm I' N} {J : SmoothAlmostComplexStructure I' N} (hJ : σ.Tames J)
  (hf : hJ.isNondegenerate.IsLagrangianMap (𝓡 2) f) (hdim : finrank ℝ P = finrank ℝ V - 2)

include hJ hf

/-- **An embedded Lagrangian sphere has normal Euler number `-2`.** For a Lagrangian embedding of
the two-sphere, with either orientation, into a four-manifold with a two-form taming an almost
complex structure, the Euler class of the normal bundle with its induced orientation evaluates on
the fundamental class of the sphere to `-2`. -/
theorem evalFundamentalClass_eulerClass_lagrangianNormalOrientation_sphere
    (hk : finrank ℝ V = 2 + 2)
    (oM : Manifold.Orientation (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (Fin 2)) :
    letI := f.normalSpaceFiberBundle hn (hdim.trans (by rw [finrank_euclideanSpace_fin]))
    letI := f.normalSpaceVectorBundle hn (hdim.trans (by rw [finrank_euclideanSpace_fin]))
    ((oM.toHomologicalOrientation finrank_euclideanSpace_fin).evalFundamentalClass
        finrank_euclideanSpace_fin (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id _)
        ((f.lagrangianNormalOrientation hn hJ hf
          (hdim.trans (by rw [finrank_euclideanSpace_fin])) finrank_euclideanSpace_fin hk
          oM).eulerClass (by rw [hdim, hk]))).down =
      -2 := by
  rw [f.evalFundamentalClass_eulerClass_lagrangianNormalOrientation_of_finrank_eq_two hn hJ hf
    (hdim.trans (by rw [finrank_euclideanSpace_fin])) finrank_euclideanSpace_fin hk oM,
    eulerChar_sphere (E := EuclideanSpace ℝ (Fin 3)) (n := 2) (by simp)]
  norm_num

end Sphere

end TauCeti.SmoothEmbedding
