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

When `a` and `b` are joined by a path, the composition is a quasi-isomorphism. For a Moore path `δ`
from `a` to `b`, tensoring behind the `0`-chain `[δ]` and concatenating is prepending `δ`, and
`z ↦ [δ] ⊗ (δ⁻¹ ⋆ z)` is a homotopy inverse: both composites are homotopic to the identity
through the retracing homotopies of `TauCeti.pathChainPrependHomotopy`, the one on the tensor
product acting on its first factor, which is linear over `C_*(Ω_b B)`. The tensor product is
the ordinary one; no flatness of the factors is assumed.

## Main definitions

* `TauCeti.pathChainConcat B a b c R`: the composition morphism
  `C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)`.

## Main results

* `TauCeti.pathChainConcat_tmul`: on pure tensors, the composition is the pairing of cubical
  chains induced by concatenation of Moore paths.
* `TauCeti.pathChainConcat_tmul_ofCube`: the composition concatenates cubes pointwise.
* `TauCeti.pathChainConcat_assoc`: the composition is associative.
* `TauCeti.pathChainConcat_tmul_point`: concatenating behind the `0`-chain of a path is prepending
  that path.
* `TauCeti.isQuasiIso_pathChainConcat`: when `a` and `b` are joined by a path, the composition is
  a quasi-isomorphism.

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

section QuasiIso

open NormalizedCubicalChain (map map_cast)

/-- The `0`-chain of a single path from `a` to `b`. -/
private abbrev pathPointChain (δ : MoorePathBetween B a b) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R :=
  cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
    (ofCube _ R (SingularCube.point δ))

/-- **Concatenating behind a single path is prepending it**: for a path `δ` from `a` to `b`,
the composition sends `[δ] ⊗ n` to `n` with `δ` prepended. -/
theorem pathChainConcat_tmul_point (δ : MoorePathBetween B a b)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R)
        (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
          (ofCube _ R (SingularCube.point δ))) n) =
      pathChainPrepend R δ c n := by
  induction n using cubicalChainModule.induction_on with
  | lof q y =>
    rw [pathChainConcat_tmul, cubicalChainPairing_lof_lof, pathChainPrepend_apply,
      cubicalChainModuleLinearMap_lof, ← cubicalChainModuleLof_cast (Nat.zero_add q),
      ← map_cast, crossProduct_point_left, ← LinearMap.comp_apply (map R _ q) (map R _ q),
      ← NormalizedCubicalChain.map_comp]
    congr 3
    ext z : 1
    simp [MoorePathBetween.prepend_apply]
  | add m m' hm hm' => rw [tmul_add, map_add, hm, hm', map_add]

/-- Prepending the reversal of `δ` to a concatenation and then tensoring behind `[δ]` moves the
retracing prefix onto the first factor, across the loops at `b`. -/
private theorem tmul_point_prepend_symm_pathChainConcat (δ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    tmul R (loopChainAlgebra B b R) (pathPointChain (R := R) δ)
        (pathChainPrepend R δ.symm c
          (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) m n))) =
      tmul R (loopChainAlgebra B b R)
        (pathChainPrepend R δ b (pathChainPrepend R δ.symm b m)) n := by
  -- The continuous map sending a path `γ` from `a` to `b` to the loop `δ⁻¹ ⋆ γ` at `b`.
  let ℓ : C(MoorePathBetween B a b, MooreLoopSpace B b) :=
    ((MoorePathBetween.loopHomeomorph b).symm : C(_, _)).comp (δ.symm.prepend b)
  induction m using cubicalChainModule.induction_on with
  | lof p x =>
    induction n using cubicalChainModule.induction_on with
    | lof q y =>
      -- The left side is the chain `ℓ_* x` of loops at `b` acting on `y`.
      have hl : pathChainPrepend R δ.symm c
          (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R)
            (cubicalChainModuleLof _ (MooreLoopSpace B b) R p x)
            (cubicalChainModuleLof _ (MooreLoopSpace B c) R q y))) =
          cubicalChainLof (MooreLoopSpace B b) R p (map R ℓ p x) •
            cubicalChainModuleLof _ (MooreLoopSpace B c) R q y := by
        have h := NormalizedCubicalChain.map_crossProduct (R := R) ℓ (ContinuousMap.id _) x y
        rw [NormalizedCubicalChain.map_id, LinearMap.id_apply] at h
        rw [pathChainConcat_tmul, cubicalChainPairing_lof_lof, pathChainPrepend_apply,
          cubicalChainModuleLinearMap_lof, lof_smul_cubicalChainModuleLof, leftAct_def, ← h,
          ← LinearMap.comp_apply (map R _ (p + q)) (map R _ (p + q)),
          ← NormalizedCubicalChain.map_comp,
          ← LinearMap.comp_apply (map R _ (p + q)) (map R _ (p + q)),
          ← NormalizedCubicalChain.map_comp]
        congr 3
        ext z : 1
        apply MoorePathBetween.ext
        simp [ℓ, MoorePathBetween.toMoorePath_leftAct, MoorePathBetween.toMoorePath_trans,
          MoorePath.trans_assoc]
      -- The chain `ℓ_* x` acting on `[δ]` prepends `δ` after its reversal.
      have hr : op (cubicalChainLof (MooreLoopSpace B b) R p (map R ℓ p x)) •
          pathPointChain (R := R) δ =
          pathChainPrepend R δ b (pathChainPrepend R δ.symm b
            (cubicalChainModuleLof _ (MooreLoopSpace B b) R p x)) := by
        rw [op_lof_smul_cubicalChainModuleLof, act_def, pathChainPrepend_apply,
          pathChainPrepend_apply, cubicalChainModuleLinearMap_lof, cubicalChainModuleLinearMap_lof,
          ← cubicalChainModuleLof_cast (Nat.zero_add p), ← map_cast, crossProduct_point_left,
          ← LinearMap.comp_apply (map R _ p) (map R _ p), ← NormalizedCubicalChain.map_comp,
          ← LinearMap.comp_apply (map R _ p) (map R _ p), ← NormalizedCubicalChain.map_comp,
          ← LinearMap.comp_apply (map R _ p) (map R _ p), ← NormalizedCubicalChain.map_comp]
        congr 3
        ext z : 1
        apply MoorePathBetween.ext
        simp [ℓ, MoorePathBetween.toMoorePath_rightAct, MoorePathBetween.toMoorePath_trans]
      rw [hl, ← balance, hr]
    | add n n' hn hn' => rw [tmul_add, map_add, map_add, tmul_add, hn, hn', tmul_add]
  | add m m' hm hm' => rw [add_tmul, map_add, map_add, tmul_add, hm, hm', map_add, map_add,
      add_tmul]

/-- The homotopy inverse of the composition, `z ↦ [δ] ⊗ (δ⁻¹ ⋆ z)`. -/
private def concatInverse (δ : MoorePathBetween B a b) :
    cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R →ₗ[R]
      BalancedTensorProduct R (loopChainAlgebra B b R)
        (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
        (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :=
  mk R (loopChainAlgebra B b R) (pathPointChain (R := R) δ) ∘ₗ
    cubicalChainModuleLinearMap R (δ.symm.prepend c)

/-- The homotopy on the tensor product: the inverse homotopy of prepending `δ` after its
reversal, on the first factor, tensored with the identity of the second factor. No Koszul sign
enters, since the homotopy acts on the first factor. -/
private def concatHomotopy (δ : MoorePathBetween B a b) :
    BalancedTensorProduct R (loopChainAlgebra B b R)
        (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
        (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) →ₗ[R]
      BalancedTensorProduct R (loopChainAlgebra B b R)
        (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
        (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :=
  BalancedTensorProduct.map ((pathChainPrependHomotopy R δ b).restrictScalars R) LinearMap.id
    (fun x m ↦ map_smul (pathChainPrependHomotopy R δ b) (op x) m) (fun _ _ ↦ rfl)

/-- The homotopy on the tensor product acts on pure tensors through the first factor. -/
private theorem concatHomotopy_tmul (δ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    concatHomotopy δ (tmul R (loopChainAlgebra B b R) m n) =
      tmul R (loopChainAlgebra B b R) (pathChainPrependHomotopy R δ b m) n :=
  map_tmul _ _ _ _ m n

/-- The homotopy inverse commutes with the differentials, since `[δ]` is a cycle of degree
zero. -/
private theorem differential_concatInverse (δ : MoorePathBetween B a b)
    (y : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    differential (pathChain_isDGBimodule B a b R).isDGRightModule
        (pathChain_isDGBimodule B b c R).toIsDGLeftModule (concatInverse δ y) =
      concatInverse δ (cubicalChainModuleDifferential _ _ R y) := by
  have h0 := cubicalChainModuleLof_mem (G := MooreLoopSpace B b)
    (ofCube (MoorePathBetween B a b) R (SingularCube.point δ))
  rw [Nat.cast_zero, neg_zero] at h0
  simp only [concatInverse, LinearMap.comp_apply, mk_apply]
  rw [differential_tmul_of_mem _ _ h0, cubicalChainModuleDifferential_lof_zero, zero_tmul,
    zero_add, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
    cubicalChainModuleDifferential_linearMap]

/-- The homotopy inverse is a left inverse of the composition up to the homotopy
`concatHomotopy δ`. -/
private theorem concatInverse_pathChainConcat (δ : MoorePathBetween B a b)
    (x : BalancedTensorProduct R (loopChainAlgebra B b R)
      (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
      (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R)) :
    concatInverse δ (pathChainConcat B a b c R x) =
      x + differential (pathChain_isDGBimodule B a b R).isDGRightModule
          (pathChain_isDGBimodule B b c R).toIsDGLeftModule (concatHomotopy δ x) +
        concatHomotopy δ (differential (pathChain_isDGBimodule B a b R).isDGRightModule
          (pathChain_isDGBimodule B b c R).toIsDGLeftModule x) := by
  induction x using BalancedTensorProduct.induction_on with
  | ht m n =>
    simp only [concatInverse, LinearMap.comp_apply, mk_apply]
    rw [← pathChainPrepend_apply, tmul_point_prepend_symm_pathChainConcat]
    induction m using cubicalChainModule.induction_on with
    | lof p x =>
      -- On `x ⊗ n` with `x` of degree `-p`, the Koszul signs of the two terms involving the
      -- differential of `n` cancel, leaving the homotopy on the first factor. This is the
      -- computation of
      -- `BalancedTensorProduct.map_eq_leibnizDifferential_comp_map_add_map_comp_add`, done
      -- here on homogeneous pure tensors because elaborating that lemma at these carriers
      -- exhausts the heartbeat budget in instance unification.
      have hx := cubicalChainModuleLof_mem (G := MooreLoopSpace B b) x
      have hs := pathChainPrependHomotopy_spec δ b
        (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p x)
      rw [eq_sub_iff_add_eq] at hs
      rw [differential_tmul_of_mem _ _ hx, map_add, map_smul]
      simp only [concatHomotopy_tmul]
      rw [differential_tmul_of_mem _ _ (pathChainPrependHomotopy_mem δ b hx), ← hs]
      simp only [add_tmul, Int.negOnePow_sub, Int.negOnePow_one, mul_neg, _root_.mul_one,
        Units.val_neg, Int.cast_neg, neg_smul]
      abel
    | add m m' hm hm' => simp only [map_add, add_tmul, hm, hm']; abel
  | ha x y hx hy => simp only [map_add, hx, hy]; abel

/-- The homotopy inverse is a right inverse of the composition up to the inverse homotopy of
prepending `δ` after its reversal. -/
private theorem pathChainConcat_concatInverse (δ : MoorePathBetween B a b)
    (y : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (concatInverse δ y) =
      y + cubicalChainModuleDifferential _ _ R (pathChainPrependHomotopy R δ c y) +
        pathChainPrependHomotopy R δ c (cubicalChainModuleDifferential _ _ R y) := by
  simp only [concatInverse, LinearMap.comp_apply, mk_apply]
  rw [pathChainConcat_tmul_point, ← pathChainPrepend_apply, add_assoc,
    pathChainPrependHomotopy_spec, add_sub_cancel]

/-- **Concatenation of path chains is a quasi-isomorphism** when `a` and `b` are joined by a
path: the composition `C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)` induces an
isomorphism on cohomology. For a Moore path `δ` from `a` to `b`, a homotopy inverse sends a chain
`z` of paths from `a` to `c` to `[δ] ⊗ (δ⁻¹ ⋆ z)`, where `[δ]` is the `0`-chain of `δ`. -/
theorem isQuasiIso_pathChainConcat (h : Joined a b) :
    DGRightModuleCat.IsQuasiIso
      (DGBimoduleCat.forgetToRightModuleCat.map (pathChainConcat B a b c R)) := by
  let δ : MoorePathBetween B a b := ⟨h.somePath.toMoorePath, by simp, by simp⟩
  -- Instance synthesis does not reach the graded actions stored in the bundled modules through
  -- the algebra structure of the loop chains, so they are supplied as local instances.
  have := (DGBimoduleCat.forgetToRightModuleCat.obj (DGBimoduleCat.tensorObj
    (pathChainBimodule B a b R) (pathChainBimodule B b c R))).gradedSMul
  have := (DGBimoduleCat.forgetToRightModuleCat.obj (pathChainBimodule B a c R)).gradedSMul
  exact DGRightModuleHom.isQuasiIso_of_homotopyInverse _ (concatInverse δ) (concatHomotopy δ)
    ((pathChainPrependHomotopy R δ c).restrictScalars R) (differential_concatInverse δ)
    (concatInverse_pathChainConcat δ) (pathChainConcat_concatInverse δ)

end QuasiIso

end TauCeti

end
