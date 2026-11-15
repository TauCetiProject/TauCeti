/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Bimodule
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Pairing
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Associator

/-!
# Concatenation of the chain bimodules of Moore paths

For points `a`, `b` and `c` of a space `B`, concatenation of Moore paths
`P_{a→b} B × P_{b→c} B → P_{a→c} B` is balanced over the loops at `b` and commutes with the
loops at `a` acting in front and those at `c` acting behind. On normalized cubical chains it
therefore induces a morphism of differential graded `(C_*(Ω_a B), C_*(Ω_c B))`-bimodules

`C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) → C_*(P_{a→c} B)`,

sending `σ ⊗ τ` to the concatenation of the cubes `σ` and `τ`. Since concatenation of Moore paths
is strictly associative, so is this composition of bimodules, through the associator of tensor
products.

The chain bimodule `C_*(P_{b→b'} B)` changes the basepoint of a DG local system from `b` to `b'`,
by derived tensor product. The composition morphism relates two successive changes of basepoint,
along paths from `a` to `b` and from `b` to `c`, to the change along paths from `a` to `c`.

When some path `γ` runs from `a` to `b`, the composition is a quasi-isomorphism of right DG
modules over `C_*(Ω_c B)`. A homotopy inverse is `x ↦ [γ] ⊗ γ⁻¹ x`, where `[γ]` is the point chain
of `γ`. One composite is prepending `γ⁻¹` and then `γ`, homotopic to the identity through the
retracing prism of `TauCeti.pathChainPrependHomotopy`. The other composite sends `m ⊗ n` to
`(γ γ⁻¹ m) ⊗ n`: the chain `γ⁻¹ m` of loops at `b` moves across the tensor sign. It is homotopic
to the identity through the same prism applied to the first factor. Both homotopies are linear
over `C_*(Ω_c B)`, but the inverse is not linear over `C_*(Ω_a B)`.

## Main definitions

* `TauCeti.pathChainConcat B a b c R`: the composition morphism
  `C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)`.

## Main results

* `TauCeti.pathChainConcat_tmul`: on pure tensors, the composition is the pairing of cubical
  chains induced by concatenation of Moore paths.
* `TauCeti.pathChainConcat_tmul_ofCube`: the composition concatenates cubes pointwise.
* `TauCeti.pathChainConcat_assoc`: the composition is associative.
* `TauCeti.isQuasiIso_pathChainConcat`: the composition is a quasi-isomorphism when `a` and `b`
  are joined by a Moore path.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

open NormalizedCubicalChain BalancedTensorProduct

universe u v

variable (B : Type u) [TopologicalSpace B] (a b c d : B) (R : Type v) [CommRing R]

/-- Concatenation of Moore paths, as a continuous map on pairs. -/
private def concatMap :
    C(MoorePathBetween B a b × MoorePathBetween B b c, MoorePathBetween B a c) :=
  ⟨fun p ↦ p.1.trans p.2, MoorePathBetween.continuous_trans⟩

/-- **Concatenation of the chain bimodules of Moore paths**: the morphism of DG
`(C_*(Ω_a B), C_*(Ω_c B))`-bimodules
`C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)` induced by concatenation. -/
def pathChainConcat :
    DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R) ⟶
      pathChainBimodule B a c R :=
  cubicalChainTensorHom (concatMap B a b c)
    (fun _ _ _ ↦ MoorePathBetween.ext (by simp [concatMap, MoorePath.trans_assoc]))
    (fun _ _ _ ↦ MoorePathBetween.ext (by simp [concatMap, MoorePath.trans_assoc]))
    (fun _ _ _ ↦ MoorePathBetween.ext (by simp [concatMap, MoorePath.trans_assoc]))

variable {B a b c d R}

/-- **The composition is the concatenation pairing**: on a pure tensor `m ⊗ n`, it is the
pairing of cubical chains induced by concatenation of Moore paths. -/
@[simp]
theorem pathChainConcat_tmul
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) m n) =
      cubicalChainPairing (MooreLoopSpace B b) (MooreLoopSpace B c) R
        ⟨fun p ↦ p.1.trans p.2, MoorePathBetween.continuous_trans⟩ m n :=
  cubicalChainTensorHom_tmul _ _ _ _ m n

/-- **The composition concatenates cubes**: on cubes `σ` of paths from `a` to `b` and `τ` of
paths from `b` to `c`, it is the cube of the concatenations `σ(s).trans τ(t)`. -/
theorem pathChainConcat_tmul_ofCube {p q : ℕ} (σ : SingularCube (MoorePathBetween B a b) p)
    (τ : SingularCube (MoorePathBetween B b c) q) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R)
        (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p
          (ofCube _ R σ))
        (cubicalChainModuleLof (MoorePathBetween B b c) (MooreLoopSpace B c) R q
          (ofCube _ R τ))) =
      cubicalChainModuleLof (MoorePathBetween B a c) (MooreLoopSpace B c) R (p + q)
        (ofCube _ R ⟨fun x ↦ (σ fun i ↦ x (Fin.castAdd q i)).trans (τ fun j ↦ x (Fin.natAdd p j)),
          by fun_prop⟩) := by
  rw [pathChainConcat_tmul, cubicalChainPairing_lof_lof, crossProduct_ofCube, map_ofCube]
  congr 2
  refine ContinuousMap.ext fun x ↦ ?_
  simp only [ContinuousMap.comp_apply, SingularCube.crossProduct_apply, ContinuousMap.coe_mk]

/-- **The composition of path bimodules is associative**: composing paths from `a` to `b`, from
`b` to `c` and from `c` to `d` in either order gives the same chains, through the associator of
tensor products. -/
theorem pathChainConcat_assoc :
    DGBimoduleCat.tensorMap (pathChainConcat B a b c R) (𝟙 (pathChainBimodule B c d R)) ≫
        pathChainConcat B a c d R =
      (DGBimoduleCat.tensorAssoc _ _ _).hom ≫
        DGBimoduleCat.tensorMap (𝟙 (pathChainBimodule B a b R)) (pathChainConcat B b c d R) ≫
          pathChainConcat B a b d R := by
  apply DGBimoduleCat.tensorObj_hom_ext
  intro z o
  induction z using BalancedTensorProduct.induction_on with
  | ht m n =>
    -- `simp` does not match the generic lemmas about bundled morphisms on these concrete
    -- bimodules, which are abbreviations; rewrite with them instead.
    rw [DGBimoduleCat.comp_apply, DGBimoduleCat.comp_apply, DGBimoduleCat.comp_apply,
      DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.tensorAssoc_hom_tmul,
      DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.id_apply, DGBimoduleCat.id_apply, pathChainConcat,
      pathChainConcat, pathChainConcat, pathChainConcat, cubicalChainTensorHom_tmul,
      cubicalChainTensorHom_tmul, cubicalChainTensorHom_tmul, cubicalChainTensorHom_tmul]
    exact cubicalChainPairing_assoc (f := concatMap B a b c) (g := concatMap B a c d)
      (f' := concatMap B b c d) (g' := concatMap B a b d)
      (fun _ _ _ ↦ MoorePathBetween.trans_assoc _ _ _) m n o
  | ha x y hx hy => simp only [add_tmul, map_add, hx, hy]

/-! ### Concatenation is a quasi-isomorphism -/

section QuasiIso

/-- The point chain `[γ]` of a Moore path. -/
private abbrev pathPointChain (γ : MoorePathBetween B a b) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R :=
  cubicalChainModuleLof _ _ R 0 (ofCube _ R (SingularCube.point γ))

/-- The loop `γ⁻¹ ⋆ δ` at `b` for a path `δ` from `a` to `b`. -/
private def loopOfPath (γ : MoorePathBetween B a b) :
    C(MoorePathBetween B a b, MooreLoopSpace B b) :=
  ((MoorePathBetween.loopHomeomorph b).symm : C(MoorePathBetween B b b, MooreLoopSpace B b)).comp
    (γ.symm.prepend b)

/-- The homotopy inverse of the composition: `x ↦ [γ] ⊗ γ⁻¹ x`. -/
private def concatInv (γ : MoorePathBetween B a b) (c : B) :
    cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R →ₗ[R]
      DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R) :=
  BalancedTensorProduct.mk R (loopChainAlgebra B b R) (pathPointChain γ) ∘ₗ
    cubicalChainModuleLinearMap R (γ.symm.prepend c)

/-- The homotopy inverse on a chain. -/
private theorem concatInv_apply (γ : MoorePathBetween B a b)
    (y : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    concatInv γ c y = tmul R (loopChainAlgebra B b R) (pathPointChain γ)
      (cubicalChainModuleLinearMap R (γ.symm.prepend c) y) := by
  rw [concatInv, LinearMap.comp_apply, mk_apply]

/-- Composing the point chain of `γ` with a chain of paths prepends `γ`. -/
private theorem pathChainConcat_tmul_pathPointChain (γ : MoorePathBetween B a b)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) (pathPointChain γ) n) =
      cubicalChainModuleLinearMap R (γ.prepend c) n := by
  rw [pathChainConcat_tmul, cubicalChainPairing_point_left]
  congr 2
  ext δ : 1
  simp

/-- The loops `γ⁻¹ m` act on the point chain of `γ` as prepending `γ⁻¹` and then `γ`. -/
private theorem op_smul_pathPointChain (γ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    op (cubicalChainSumMap R (loopOfPath γ) (cubicalChainModuleEquiv _ _ R m)) •
        (pathPointChain γ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) =
      cubicalChainModuleLinearMap R ((γ.prepend b).comp (γ.symm.prepend b)) m := by
  rw [op_smul_cubicalChainModuleLof_point, ← LinearMap.comp_apply (cubicalChainSumMap R _),
    ← cubicalChainSumMap_comp]
  have h : ((actMap (MoorePathBetween B a b) (MooreLoopSpace B b)).comp
      ((ContinuousMap.const (MooreLoopSpace B b) γ).prodMk (ContinuousMap.id _))).comp
        (loopOfPath γ) = (γ.prepend b).comp (γ.symm.prepend b) := by
    ext δ : 1
    apply MoorePathBetween.ext
    simp [loopOfPath]
  apply (cubicalChainModuleEquiv _ _ R).injective
  rw [LinearEquiv.apply_symm_apply, cubicalChainModuleEquiv_linearMap, h]

/-- The loops `γ⁻¹ m` act on a chain `n` of paths as `γ⁻¹` prepended to `m ⋆ n`. -/
private theorem cubicalChainSumMap_loopOfPath_smul (γ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    cubicalChainSumMap R (loopOfPath γ) (cubicalChainModuleEquiv _ _ R m) • n =
      cubicalChainModuleLinearMap R (γ.symm.prepend c)
        (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) m n)) := by
  rw [pathChainConcat_tmul, cubicalChainModuleLinearMap_cubicalChainPairing,
    cubicalChainSumMap_smul]
  have h : (leftActMap (MooreLoopSpace B b) (MoorePathBetween B b c)).comp
      ((loopOfPath γ).prodMap (ContinuousMap.id _)) =
        (γ.symm.prepend c).comp ⟨fun p ↦ p.1.trans p.2, MoorePathBetween.continuous_trans⟩ := by
    ext ⟨δ, ε⟩ : 1
    apply MoorePathBetween.ext
    simp [loopOfPath, MoorePath.trans_assoc]
  rw [h]

/-- On a pure tensor, the homotopy inverse after the composition prepends `γ⁻¹` and then `γ` in
the first factor: the loops `γ⁻¹ m` move across the tensor sign. -/
private theorem concatInv_pathChainConcat_tmul (γ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    concatInv γ c (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) m n)) =
      tmul R (loopChainAlgebra B b R)
        (cubicalChainModuleLinearMap R ((γ.prepend b).comp (γ.symm.prepend b)) m) n := by
  rw [concatInv_apply, ← cubicalChainSumMap_loopOfPath_smul,
    ← balance, op_smul_pathPointChain]

/-- The differential of the path chain bimodule is the cubical boundary. -/
private theorem pathChainBimodule_differential (a b : B)
    (z : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    (pathChainBimodule B a b R).differential z = cubicalChainModuleDifferential _ _ R z :=
  (rfl)

/-- The point chain has degree zero. -/
private theorem pathPointChain_mem (γ : MoorePathBetween B a b) :
    (pathPointChain γ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) ∈
      (pathChainBimodule B a b R).grading 0 := by
  simpa using cubicalChainModuleLof_mem (G := MooreLoopSpace B b) (R := R)
    (ofCube (MoorePathBetween B a b) R (SingularCube.point γ))

/-- The homotopy inverse commutes with the differentials. -/
private theorem differential_concatInv (γ : MoorePathBetween B a b)
    (y : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    (DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R)).differential
        (concatInv γ c y) =
      concatInv γ c (cubicalChainModuleDifferential _ _ R y) := by
  rw [concatInv_apply, concatInv_apply, DGBimoduleCat.tensorObj_differential_tmul
    (pathPointChain_mem γ), pathChainBimodule_differential, pathChainBimodule_differential,
    cubicalChainModuleDifferential_lof_zero, zero_tmul, zero_add, Int.negOnePow_zero, one_smul,
    cubicalChainModuleDifferential_linearMap]

/-- The homotopy `h ⊗ 1` on the tensor product, for the homotopy `h` of
`pathChainPrependHomotopy`. -/
private def concatHomotopy (γ : MoorePathBetween B a b) (c : B) :
    Module.End R
      (DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R)) :=
  BalancedTensorProduct.map ((pathChainPrependHomotopy R γ b).restrictScalars R) LinearMap.id
    (fun x m ↦ map_smul (pathChainPrependHomotopy R γ b) (op x) m) (fun _ _ ↦ rfl)

/-- The homotopy `h ⊗ 1` on a pure tensor. -/
private theorem concatHomotopy_tmul (γ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    concatHomotopy γ c (tmul R (loopChainAlgebra B b R) m n) =
      tmul R (loopChainAlgebra B b R) (pathChainPrependHomotopy R γ b m) n :=
  BalancedTensorProduct.map_tmul _ _ _ _ m n

/-- The homotopy inverse after the composition is homotopic to the identity, through `h ⊗ 1`. -/
private theorem concatInv_pathChainConcat (γ : MoorePathBetween B a b)
    (t : DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R)) :
    concatInv γ c (pathChainConcat B a b c R t) =
      t + (DGBimoduleCat.tensorObj _ _).differential (concatHomotopy γ c t) +
        concatHomotopy γ c ((DGBimoduleCat.tensorObj _ _).differential t) := by
  induction t using BalancedTensorProduct.induction_on with
  | ht m n =>
    induction m using cubicalChainModule.induction_on with
    | add m m' hm hm' =>
      simp only [add_tmul, map_add, hm, hm']
      abel
    | lof p x =>
      have hx := cubicalChainModuleLof_mem (G := MooreLoopSpace B b) (R := R) x
      have hs : (-(p : ℤ)).negOnePow = -(-(p : ℤ) - 1).negOnePow := by
        rw [← Int.negOnePow_succ, sub_add_cancel]
      have h := pathChainPrependHomotopy_spec γ b
        (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p x)
      rw [pathChainPrepend_apply, pathChainPrepend_apply, eq_sub_iff_add_eq] at h
      rw [concatInv_pathChainConcat_tmul, concatHomotopy_tmul,
        DGBimoduleCat.tensorObj_differential_tmul (pathChainPrependHomotopy_mem γ b hx),
        DGBimoduleCat.tensorObj_differential_tmul hx, map_add]
      simp only [Units.smul_def, map_zsmul]
      rw [concatHomotopy_tmul, concatHomotopy_tmul, cubicalChainModuleLinearMap_comp,
        LinearMap.comp_apply, ← h, hs]
      simp only [add_tmul, Units.val_neg, neg_smul]
      abel
  | ha x y hx hy =>
    simp only [map_add, hx, hy]
    abel

/-- The composition after the homotopy inverse is homotopic to the identity, through the
retracing prism of `γ`. -/
private theorem pathChainConcat_concatInv (γ : MoorePathBetween B a b)
    (y : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (concatInv γ c y) =
      y + cubicalChainModuleDifferential _ _ R (pathChainPrependHomotopy R γ c y) +
        pathChainPrependHomotopy R γ c (cubicalChainModuleDifferential _ _ R y) := by
  rw [concatInv_apply, pathChainConcat_tmul_pathPointChain, add_assoc,
    pathChainPrependHomotopy_spec, pathChainPrepend_apply, pathChainPrepend_apply,
    add_sub_cancel]

/-- **The composition of path chain bimodules is a quasi-isomorphism**: when some Moore path runs
from `a` to `b`, the morphism `C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)`
induced by concatenation is a quasi-isomorphism of right DG modules over `C_*(Ω_c B)`. -/
theorem isQuasiIso_pathChainConcat (h : Nonempty (MoorePathBetween B a b)) :
    DGRightModuleCat.IsQuasiIso
      (DGBimoduleCat.forgetToRightModuleCat.map (pathChainConcat B a b c R)) := by
  obtain ⟨γ⟩ := h
  -- The bundled graded actions are not global instances.
  have := (DGBimoduleCat.forgetToRightModuleCat.obj
    (DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R))).gradedSMul
  have := (DGBimoduleCat.forgetToRightModuleCat.obj (pathChainBimodule B a c R)).gradedSMul
  exact DGRightModuleHom.isQuasiIso_of_homotopyInverse _ (concatInv γ c) (concatHomotopy γ c)
    ((pathChainPrependHomotopy R γ c).restrictScalars R) (differential_concatInv γ)
    (concatInv_pathChainConcat γ) (pathChainConcat_concatInv γ)

end QuasiIso

end TauCeti

end
