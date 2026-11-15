/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Append
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Module
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso

/-!
# Basepoint change of DG local systems

For points `b` and `c` of a space `B`, the normalized cubical chains `C_*(P_{b→c} B)` on the Moore
paths from `b` to `c` form a DG `(C_*(Ω_b B), C_*(Ω_c B))`-bimodule. **Basepoint change**
(`TauCeti.DGLocalSystem.basepointChange`) carries a DG local system `𝓕` at `b`, a right DG module
over `C_*(Ω_b B)`, to the DG local system `𝓕 ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B)` at `c`.

The tensor product here is the ordinary balanced one, and it already computes the derived tensor
product: basepoint change preserves quasi-isomorphisms
(`TauCeti.DGLocalSystem.isQuasiIso_basepointChange_map`). When `b` and `c` are joined by a Moore
path `γ`, the reason is that the path bimodule is, up to homotopy, the free left module on `[γ]`.
The inclusion
`x ↦ x ⊗ [γ]` (`TauCeti.DGLocalSystem.basepointChangeIncl`) has the retraction
`x ⊗ σ ↦ x · (σ ⋆ γ⁻¹)` (`TauCeti.DGLocalSystem.basepointChangeRetract`), and including after
retracting is the right action of the loop `γ⁻¹ ⋆ γ`, homotopic to the identity through the
retracing `1`-chain of `TauCeti.AlgebraicTopology.DGLocalSystem.Path.Append`. These maps are
natural, so a quasi-isomorphism `f` is a homotopy retract of its basepoint change, which is
therefore a quasi-isomorphism (`TauCeti.DGRightModuleCat.IsQuasiIso.of_retract_op_smul`). If
there is no path from `b` to `c`, basepoint change is zero. In particular, for a semi-free
resolution `𝓕' → 𝓕` the induced map from `𝓕' ⊗ C_*(P_{b→c} B)`, a model of the derived tensor
product, to `𝓕 ⊗ C_*(P_{b→c} B)` is a quasi-isomorphism.

Two successive changes of basepoint, from `a` to `b` and from `b` to `c`, compare with the change
from `a` to `c` through the associator and concatenation of paths
(`TauCeti.DGLocalSystem.basepointChangeComp`), naturally in the local system. When `b` and `c`
are joined by a Moore path, the comparison is a quasi-isomorphism
(`TauCeti.DGLocalSystem.isQuasiIso_basepointChangeComp_app`), by the same retraction argument with
appending a path from `b` to `c` in the second tensor factor.

## Main definitions

* `TauCeti.DGLocalSystem.basepointChange R b c`: basepoint change from `b` to `c`.
* `TauCeti.DGLocalSystem.basepointChangeComp R a b c`: the comparison of two successive changes
  of basepoint with the change along the composite.

## Main results

* `TauCeti.DGLocalSystem.isQuasiIso_basepointChange_map`: basepoint change preserves
  quasi-isomorphisms.
* `TauCeti.DGLocalSystem.isQuasiIso_basepointChangeComp_app`: the composite of two changes of
  basepoint is quasi-isomorphic to the change along the composite.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

open NormalizedCubicalChain BalancedTensorProduct

universe uM u v

variable {B : Type u} [TopologicalSpace B] {R : Type v} [CommRing R] {a b c : B}

namespace DGLocalSystem

variable (R) in
/-- **Basepoint change** of DG local systems from `b` to `c`: the ordinary tensor product
`𝓕 ↦ 𝓕 ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B)` with the chains on the Moore paths from `b` to `c`, a DG
local system at `c` through the loops at `c` acting on the end of the paths. -/
abbrev basepointChange (b c : B) :
    DGLocalSystem.{uM} B b R ⥤ DGLocalSystem.{max uM u v} B c R where
  obj 𝓕 := DGRightModuleCat.tensorBimoduleObj 𝓕 (pathChainBimodule B b c R)
  map f := DGRightModuleCat.tensorBimoduleMap f (𝟙 _)
  map_id _ := DGRightModuleCat.tensorBimoduleMap_id _ _
  map_comp f g := by
    rw [← DGRightModuleCat.tensorBimoduleMap_comp, Category.comp_id]

variable (𝓕 : DGLocalSystem.{uM} B b R)

/-- The inclusion `x ↦ x ⊗ [γ]`. -/
def basepointChangeIncl (γ : MoorePathBetween B b c) :
    𝓕 →ₗ[R] (basepointChange R b c).obj 𝓕 :=
  (BalancedTensorProduct.mk R (loopChainAlgebra B b R)).flip (pathChainPoint R γ)

@[simp]
theorem basepointChangeIncl_apply (γ : MoorePathBetween B b c) (x : 𝓕) :
    basepointChangeIncl 𝓕 γ x = tmul R (loopChainAlgebra B b R) x (pathChainPoint R γ) := by
  rw [basepointChangeIncl, LinearMap.flip_apply, mk_apply]

/-- The inclusion is a chain map. -/
theorem differential_basepointChangeIncl (γ : MoorePathBetween B b c) (x : 𝓕) :
    ((basepointChange R b c).obj 𝓕).differential (basepointChangeIncl 𝓕 γ x) =
      basepointChangeIncl 𝓕 γ (𝓕.differential x) := by
  induction x using DirectSum.Decomposition.inductionOn 𝓕.grading with
  | zero => simp
  | @homogeneous p x =>
    rw [basepointChangeIncl_apply, basepointChangeIncl_apply,
      DGRightModuleCat.tensorBimoduleObj_differential_tmul x.2]
    -- The differential of the bundled path bimodule is the cubical boundary by definition.
    erw [cubicalChainModuleDifferential_pathChainPoint]
    rw [tmul_zero, smul_zero, add_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The bilinear pairing `(x, σ) ↦ x · (σ ⋆ γ⁻¹)`. -/
private def basepointChangeRetractBilin (γ : MoorePathBetween B b c) :
    𝓕 →ₗ[R] cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R →ₗ[R] 𝓕 :=
  LinearMap.mk₂ R (fun x σ ↦ op (pathChainToLoopChain R γ σ) • x)
    (fun x y σ ↦ smul_add _ x y) (fun r x σ ↦ smul_comm _ r x)
    (fun x σ τ ↦ by rw [map_add, MulOpposite.op_add, add_smul])
    (fun r x σ ↦ by rw [map_smul, op_smul, smul_assoc])

/-- The retraction `x ⊗ σ ↦ x · (σ ⋆ γ⁻¹)`. -/
def basepointChangeRetract (γ : MoorePathBetween B b c) :
    (basepointChange R b c).obj 𝓕 →ₗ[R] 𝓕 :=
  BalancedTensorProduct.lift (basepointChangeRetractBilin 𝓕 γ) (fun a x σ ↦ by
    simp only [basepointChangeRetractBilin, LinearMap.mk₂_apply, pathChainToLoopChain_smul,
      op_mul, mul_smul])

@[simp]
theorem basepointChangeRetract_tmul (γ : MoorePathBetween B b c) (x : 𝓕)
    (σ : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    basepointChangeRetract 𝓕 γ (tmul R (loopChainAlgebra B b R) x σ) =
      op (pathChainToLoopChain R γ σ) • x := by
  unfold basepointChangeRetract
  exact (lift_tmul _ _ x σ).trans (by rw [basepointChangeRetractBilin, LinearMap.mk₂_apply])

/-- The retraction is a chain map. -/
theorem differential_basepointChangeRetract (γ : MoorePathBetween B b c)
    (z : (basepointChange R b c).obj 𝓕) :
    𝓕.differential (basepointChangeRetract 𝓕 γ z) =
      basepointChangeRetract 𝓕 γ (((basepointChange R b c).obj 𝓕).differential z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht x σ =>
    induction x using DirectSum.Decomposition.inductionOn 𝓕.grading with
    | zero => simp
    | @homogeneous p x =>
      -- Instance search does not find `𝓕.gradedSMul` for the concrete loop algebra, so the
      -- graded scalar action is supplied explicitly.
      have hl := @IsDGRightModule.leibniz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 𝓕.gradedSMul _ _
        𝓕.isDGRightModule _ _ x.2 (pathChainToLoopChain R γ σ)
      rw [DGRightModuleCat.tensorBimoduleObj_differential_tmul x.2, map_add, Units.smul_def,
        map_zsmul, ← Units.smul_def, basepointChangeRetract_tmul, basepointChangeRetract_tmul,
        basepointChangeRetract_tmul, hl]
      -- The differential of the bundled path bimodule is the cubical boundary by definition.
      erw [pathChainToLoopChain_differential]
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | ha z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

/-- Retracting and including again is the right action of the loop `γ⁻¹ ⋆ γ`. -/
theorem basepointChangeIncl_basepointChangeRetract (γ : MoorePathBetween B b c)
    (z : (basepointChange R b c).obj 𝓕) :
    basepointChangeIncl 𝓕 γ (basepointChangeRetract 𝓕 γ z) =
      -- Instance search unfolds the carrier of the abbreviation to a balanced tensor product and
      -- misses its right module structure, so the structure is supplied explicitly.
      letI := ((basepointChange R b c).obj 𝓕).moduleOp
      op (loopChainSymmTrans R γ) • z := by
  let := ((basepointChange R b c).obj 𝓕).moduleOp
  induction z using BalancedTensorProduct.induction_on with
  | ht x σ =>
    rw [basepointChangeRetract_tmul, basepointChangeIncl_apply, balance,
      pathChainToLoopChain_smul_pathChainPoint]
    exact (smul_tmul_right _ _ _ _).symm
  | ha z w hz hw => rw [map_add, map_add, hz, hw, smul_add]

/-- Basepoint change acts on morphisms in the first tensor factor. -/
@[simp]
theorem basepointChange_map_tmul {𝓖 : DGLocalSystem.{uM} B b R} (f : 𝓕 ⟶ 𝓖) (x : 𝓕)
    (σ : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    (basepointChange R b c).map f (tmul R (loopChainAlgebra B b R) x σ) =
      tmul R (loopChainAlgebra B b R) (f x) σ :=
  (DGRightModuleCat.tensorBimoduleMap_tmul f (𝟙 (pathChainBimodule B b c R)) x σ).trans
    (by rw [DGBimoduleCat.id_apply])

/-- The inclusion is natural in the DG local system. -/
theorem basepointChange_map_basepointChangeIncl {𝓖 : DGLocalSystem.{uM} B b R} (f : 𝓕 ⟶ 𝓖)
    (γ : MoorePathBetween B b c) (x : 𝓕) :
    (basepointChange R b c).map f (basepointChangeIncl 𝓕 γ x) = basepointChangeIncl 𝓖 γ (f x) := by
  rw [basepointChangeIncl_apply, basepointChangeIncl_apply, basepointChange_map_tmul]

/-- The retraction is natural in the DG local system. -/
theorem basepointChangeRetract_basepointChange_map {𝓖 : DGLocalSystem.{uM} B b R} (f : 𝓕 ⟶ 𝓖)
    (γ : MoorePathBetween B b c) (z : (basepointChange R b c).obj 𝓕) :
    basepointChangeRetract 𝓖 γ ((basepointChange R b c).map f z) =
      f (basepointChangeRetract 𝓕 γ z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht x σ =>
    rw [basepointChange_map_tmul, basepointChangeRetract_tmul, basepointChangeRetract_tmul,
      map_smul]
  | ha z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

/-- **Basepoint change preserves quasi-isomorphisms.** When `b` and `c` are joined by a Moore path
`γ`, a quasi-isomorphism is a homotopy retract of its basepoint change, through the inclusion
`x ↦ x ⊗ [γ]` and the retraction `x ⊗ σ ↦ x · (σ ⋆ γ⁻¹)`. Otherwise there are no paths from `b`
to `c`, and basepoint change is zero. -/
theorem isQuasiIso_basepointChange_map {𝓕 𝓖 : DGLocalSystem.{uM} B b R} {f : 𝓕 ⟶ 𝓖}
    (hf : DGRightModuleCat.IsQuasiIso f) :
    DGRightModuleCat.IsQuasiIso ((basepointChange R b c).map f) := by
  rcases isEmpty_or_nonempty (MoorePathBetween B b c) with hbc | ⟨⟨γ⟩⟩
  · exact DGRightModuleCat.isQuasiIso_of_subsingleton _
  refine hf.of_retract_op_smul _ (basepointChangeIncl 𝓕 γ) (basepointChangeIncl 𝓖 γ)
    (basepointChangeRetract 𝓕 γ) (basepointChangeRetract 𝓖 γ)
    (cubicalChainDifferential_loopChainRetrace γ) (differential_basepointChangeIncl 𝓕 γ)
    (differential_basepointChangeIncl 𝓖 γ) (differential_basepointChangeRetract 𝓕 γ)
    (differential_basepointChangeRetract 𝓖 γ) (basepointChange_map_basepointChangeIncl 𝓕 f γ)
    (fun z ↦ (basepointChangeRetract_basepointChange_map 𝓕 f γ z).symm)
    (basepointChangeIncl_basepointChangeRetract 𝓕 γ)
    (basepointChangeIncl_basepointChangeRetract 𝓖 γ)

section Comp

variable (𝓕 : DGLocalSystem.{uM} B a R)

/-- Appending a path `γ` from `b` to `c` in the second factor, `x ⊗ σ ↦ x ⊗ (σ ⋆ γ)`. -/
def basepointChangeAppend (γ : MoorePathBetween B b c) :
    (basepointChange R a b).obj 𝓕 →ₗ[R] (basepointChange R a c).obj 𝓕 :=
  BalancedTensorProduct.map LinearMap.id (pathChainAppend R γ a) (fun _ _ ↦ rfl)
    (pathChainAppend_smul γ a)

@[simp]
theorem basepointChangeAppend_tmul (γ : MoorePathBetween B b c) (x : 𝓕)
    (σ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    basepointChangeAppend 𝓕 γ (tmul R (loopChainAlgebra B a R) x σ) =
      tmul R (loopChainAlgebra B a R) x (pathChainAppend R γ a σ) := by
  rw [basepointChangeAppend, BalancedTensorProduct.map_tmul, LinearMap.id_apply]

/-- Appending in the second factor is a chain map. -/
theorem differential_basepointChangeAppend (γ : MoorePathBetween B b c)
    (z : (basepointChange R a b).obj 𝓕) :
    ((basepointChange R a c).obj 𝓕).differential (basepointChangeAppend 𝓕 γ z) =
      basepointChangeAppend 𝓕 γ (((basepointChange R a b).obj 𝓕).differential z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht x σ =>
    induction x using DirectSum.Decomposition.inductionOn 𝓕.grading with
    | zero => simp
    | @homogeneous p x =>
      rw [basepointChangeAppend_tmul, DGRightModuleCat.tensorBimoduleObj_differential_tmul x.2,
        DGRightModuleCat.tensorBimoduleObj_differential_tmul x.2, map_add, map_zsmul_unit,
        basepointChangeAppend_tmul, basepointChangeAppend_tmul]
      -- The differentials of the bundled path bimodules are the cubical boundaries by definition.
      erw [cubicalChainModuleDifferential_pathChainAppend]
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | ha z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

/-- Appending `γ⁻¹` and then `γ` is the right action of the loop `γ⁻¹ ⋆ γ`. -/
theorem basepointChangeAppend_basepointChangeAppend_symm (γ : MoorePathBetween B b c)
    (z : (basepointChange R a c).obj 𝓕) :
    basepointChangeAppend 𝓕 γ (basepointChangeAppend 𝓕 γ.symm z) =
      -- Instance search unfolds the carrier of the abbreviation to a balanced tensor product and
      -- misses its right module structure, so the structure is supplied explicitly.
      letI := ((basepointChange R a c).obj 𝓕).moduleOp
      op (loopChainSymmTrans R γ) • z := by
  let := ((basepointChange R a c).obj 𝓕).moduleOp
  induction z using BalancedTensorProduct.induction_on with
  | ht x σ =>
    rw [basepointChangeAppend_tmul, basepointChangeAppend_tmul,
      pathChainAppend_pathChainAppend_symm]
    exact (smul_tmul_right _ _ _ _).symm
  | ha z w hz hw => rw [map_add, map_add, hz, hw, smul_add]

variable (R) in
/-- The composite of two basepoint changes compared with the change along the composite: the
associator followed by concatenation of paths,
`(𝓕 ⊗ C_*(P_{a→b})) ⊗ C_*(P_{b→c}) → 𝓕 ⊗ C_*(P_{a→c})`. -/
def basepointChangeComp (a b c : B) :
    basepointChange R a b ⋙ basepointChange.{max uM u v} R b c ⟶
      basepointChange.{uM} R a c where
  app 𝓕 := ((DGBimoduleCat.tensorAssoc 𝓕.toScalarBimodule (pathChainBimodule B a b R)
      (pathChainBimodule B b c R)).hom ≫
    DGBimoduleCat.tensorMap (𝟙 _) (pathChainConcat B a b c R)).val
  naturality 𝓕 𝓖 f := by
    apply DGRightModuleCat.tensorBimoduleObj_hom_ext
    intro z τ
    induction z using BalancedTensorProduct.induction_on with
    | ht x σ =>
      rw [DGRightModuleCat.comp_apply, DGRightModuleCat.comp_apply, Functor.comp_map,
        basepointChange_map_tmul, basepointChange_map_tmul]
      -- The components are underlying maps of bimodule morphisms; apply them as such.
      erw [DGBimoduleCat.comp_apply, DGBimoduleCat.comp_apply]
      rw [DGBimoduleCat.tensorAssoc_hom_tmul, DGBimoduleCat.tensorAssoc_hom_tmul,
        DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.id_apply,
        DGBimoduleCat.id_apply, basepointChange_map_tmul]
    | ha z w hz hw => simp only [add_tmul, map_add, hz, hw]

/-- The component of the comparison at `𝓕` is the associator followed by concatenation of
paths, as a morphism of DG bimodules. -/
theorem basepointChangeComp_app :
    (basepointChangeComp R a b c).app 𝓕 =
      ((DGBimoduleCat.tensorAssoc 𝓕.toScalarBimodule (pathChainBimodule B a b R)
          (pathChainBimodule B b c R)).hom ≫
        DGBimoduleCat.tensorMap (𝟙 _) (pathChainConcat B a b c R)).val :=
  (rfl)

/-- **The composite of two basepoint changes is the change along the composite**: the comparison
`(𝓕 ⊗ C_*(P_{a→b})) ⊗ C_*(P_{b→c}) → 𝓕 ⊗ C_*(P_{a→c})` is a quasi-isomorphism when `b` and
`c` are joined by a Moore path. -/
theorem isQuasiIso_basepointChangeComp_app (γ : MoorePathBetween B b c) :
    DGRightModuleCat.IsQuasiIso ((basepointChangeComp R a b c).app 𝓕) := by
  refine (DGRightModuleCat.isQuasiIso_id ((basepointChange R a b).obj 𝓕)).of_retract_op_smul
    ((basepointChangeComp R a b c).app 𝓕)
    (basepointChangeIncl _ γ) (basepointChangeAppend 𝓕 γ) (basepointChangeRetract _ γ)
    (basepointChangeAppend 𝓕 γ.symm) (cubicalChainDifferential_loopChainRetrace γ)
    (differential_basepointChangeIncl _ γ) (differential_basepointChangeAppend 𝓕 γ)
    (differential_basepointChangeRetract _ γ) (differential_basepointChangeAppend 𝓕 γ.symm)
    (fun y ↦ ?_) (fun z ↦ ?_) (basepointChangeIncl_basepointChangeRetract _ γ)
    (basepointChangeAppend_basepointChangeAppend_symm 𝓕 γ)
  · induction y using BalancedTensorProduct.induction_on with
    | ht x σ =>
      rw [basepointChangeIncl_apply, basepointChangeComp_app]
      -- The component is the underlying map of a bimodule morphism; apply it as such.
      erw [DGBimoduleCat.comp_apply]
      rw [DGBimoduleCat.tensorAssoc_hom_tmul, DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.id_apply,
        pathChainConcat_tmul_pathChainPoint, DGRightModuleCat.id_apply, basepointChangeAppend_tmul]
    | ha y w hy hw => rw [map_add, map_add, hy, hw, map_add, map_add]
  · induction z using BalancedTensorProduct.induction_on with
    | ht y τ =>
      induction y using BalancedTensorProduct.induction_on with
      | ht x σ =>
        rw [basepointChangeRetract_tmul, DGRightModuleCat.id_apply, basepointChangeComp_app]
        -- The component is the underlying map of a bimodule morphism, and the right action on
        -- the tensor product is the balanced one; apply them as such.
        erw [DGBimoduleCat.comp_apply, smul_tmul_right]
        rw [DGBimoduleCat.tensorAssoc_hom_tmul, DGBimoduleCat.tensorMap_tmul,
          DGBimoduleCat.id_apply, basepointChangeAppend_tmul, op_pathChainToLoopChain_smul]
      | ha y w hy hw => rw [add_tmul, map_add, map_add, hy, hw, map_add, map_add]
    | ha z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

end Comp

end DGLocalSystem

end TauCeti
