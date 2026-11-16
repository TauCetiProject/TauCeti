/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Bimodule
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Pairing
public import TauCeti.Algebra.Homology.DG.Bimodule.QuasiIso
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Associator
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Homotopy

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

When `a` and `b` are joined by a Moore path, the composition is a quasi-isomorphism of right DG
modules over `C_*(Ω_c B)`. For `c = a` its target is the chains on the loops at `a`, so the
bimodule of paths from `b` back to `a` reverses, up to quasi-isomorphism, the change of basepoint
along the paths from `a` to `b`.

## Main definitions

* `TauCeti.pathChainConcat B a b c R`: the composition morphism
  `C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)`.

## Main results

* `TauCeti.pathChainConcat_tmul`: on pure tensors, the composition is the pairing of cubical
  chains induced by concatenation of Moore paths.
* `TauCeti.pathChainConcat_tmul_ofCube`: the composition concatenates cubes pointwise.
* `TauCeti.pathChainConcat_assoc`: the composition is associative.
* `TauCeti.isQuasiIso_pathChainConcat`: if `a` and `b` are joined by a Moore path, the composition
  is a quasi-isomorphism of right DG modules.

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

/-- Prepending the reversal of `γ` to a path from `a` to `b`, read as a loop at `b`. -/
private def retraceLoop (γ : MoorePathBetween B a b) :
    C(MoorePathBetween B a b, MooreLoopSpace B b) :=
  ((MoorePathBetween.loopHomeomorph b).symm : C(_, _)).comp (γ.symm.prepend b)

/-- The `0`-chain of a single path. -/
private abbrev pathPointChain (γ : MoorePathBetween B a b) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R :=
  cubicalChainModuleLof _ _ R 0 (ofCube _ R (SingularCube.point γ))

/-- Prepending `γ⁻¹` to a concatenation `m ⋆ n` is the left action on `n` of the loops `γ⁻¹ ⋆ m`. -/
private theorem pathChainPrepend_symm_concat (γ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    cubicalChainModuleLinearMap R (γ.symm.prepend c)
        (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) m n)) =
      cubicalChainModuleEquiv _ _ R (cubicalChainModuleLinearMap R (retraceLoop γ) m) • n := by
  rw [pathChainConcat_tmul, cubicalChainModuleLinearMap_cubicalChainPairing,
    cubicalChainModuleEquiv_smul_eq_cubicalChainPairing,
    cubicalChainPairing_cubicalChainModuleLinearMap_left]
  refine congrArg (fun F ↦ cubicalChainPairing _ _ R F m n) (ContinuousMap.ext fun ⟨σ, τ⟩ ↦ ?_)
  exact MoorePathBetween.ext (by simp [retraceLoop, MoorePathBetween.toMoorePath_leftAct,
    MoorePath.trans_assoc])

/-- The loops `γ⁻¹ ⋆ m` act on the point `γ` by prepending `γ⁻¹` and then `γ` to `m`. -/
private theorem op_smul_pathPointChain (γ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    op (cubicalChainModuleEquiv _ _ R (cubicalChainModuleLinearMap R (retraceLoop γ) m)) •
        pathPointChain (R := R) γ =
      pathChainPrepend R γ b (pathChainPrepend R γ.symm b m) := by
  rw [op_cubicalChainModuleEquiv_smul_eq_cubicalChainPairing,
    cubicalChainPairing_cubicalChainModuleLinearMap_right, cubicalChainPairing_lof_point_left,
    pathChainPrepend_apply, pathChainPrepend_apply, ← LinearMap.comp_apply,
    ← cubicalChainModuleLinearMap_comp]
  refine congrArg (fun F ↦ cubicalChainModuleLinearMap R F m) (ContinuousMap.ext fun σ ↦ ?_)
  exact MoorePathBetween.ext (by simp [retraceLoop, MoorePathBetween.toMoorePath_rightAct])

/-- Concatenating the point `γ` with a chain `y` prepends `γ` to `y`. -/
private theorem pathChainConcat_pathPointChain (γ : MoorePathBetween B a b)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) (pathPointChain γ) y) =
      pathChainPrepend R γ c y := by
  rw [pathChainConcat_tmul, cubicalChainPairing_lof_point_left, pathChainPrepend_apply]
  exact congrArg (fun F ↦ cubicalChainModuleLinearMap R F y) (ContinuousMap.ext fun _ ↦ by simp)

/-- Concatenating, prepending `γ⁻¹` and tensoring with the point `γ` is, by the balancing
relation, prepending `γ⁻¹` and then `γ` on the first factor. -/
private theorem tmul_pathPointChain_pathChainPrepend_symm_concat (γ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    tmul R (loopChainAlgebra B b R) (pathPointChain γ) (cubicalChainModuleLinearMap R
        (γ.symm.prepend c) (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) m n))) =
      tmul R (loopChainAlgebra B b R)
        (pathChainPrepend R γ b (pathChainPrepend R γ.symm b m)) n := by
  rw [pathChainPrepend_symm_concat, ← balance, op_smul_pathPointChain]

/-- **Concatenation of path bimodules is a quasi-isomorphism** of right DG modules over
`C_*(Ω_c B)`, as soon as `a` and `b` are joined by a Moore path:
`C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) → C_*(P_{a→c} B)` induces an isomorphism on
cohomology. For `c = a` the target is the chains on the Moore paths from `a` to itself, that is on
the loops at `a`: the bimodule of paths from `b` back to `a` reverses a change of basepoint along
paths from `a` to `b`. The hypothesis cannot be dropped: without a path from `a` to `b` the source
vanishes, while the target need not. -/
theorem isQuasiIso_pathChainConcat (h : Nonempty (MoorePathBetween B a b)) :
    DGRightModuleCat.IsQuasiIso
      (DGBimoduleCat.forgetToRightModuleCat.map (pathChainConcat B a b c R)) := by
  obtain ⟨γ⟩ := h
  -- The homotopy inverse `g : x ↦ γ ⊗ γ⁻¹ x`. One composite is prepending `γ⁻¹` and then `γ`,
  -- contracted by the retracing prism `L` on paths from `a` to `c`; the other is the same
  -- operation `P` on the first tensor factor, contracted by `K = H ⊗ 1` for the retracing prism
  -- `H` on paths from `a` to `b`, which is linear over the loops at `b`.
  let H := pathChainPrependHomotopy R γ b
  let K : DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R) →ₗ[R]
      DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R) :=
    BalancedTensorProduct.map (A := loopChainAlgebra B b R) (H.restrictScalars R) LinearMap.id
      (fun x m ↦ H.map_smul (op x) m) (fun _ _ ↦ rfl)
  let g : pathChainBimodule B a c R →ₗ[R]
      DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R) :=
    (mk R (loopChainAlgebra B b R) (pathPointChain (R := R) γ)) ∘ₗ
      cubicalChainModuleLinearMap (G := MooreLoopSpace B c) R (γ.symm.prepend c)
  refine DGBimoduleCat.isQuasiIso_forgetToRightModuleCat_map_of_homotopyInverse _ g K
    ((pathChainPrependHomotopy R γ c).restrictScalars R) ?_ ?_ ?_
  · -- `g` is a chain map, since the point `γ` is a cycle of degree zero.
    intro y
    have hγ : pathPointChain (R := R) γ ∈ (pathChainBimodule B a b R).grading 0 := by
      simpa using cubicalChainModuleLof_mem (G := MooreLoopSpace B b)
        (ofCube _ R (SingularCube.point γ))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mk_apply, mk_apply,
      DGBimoduleCat.tensorObj_differential_tmul hγ]
    simp [cubicalChainModuleDifferential_linearMap]
  · -- `g ∘ concat` is `P ⊗ 1` for `P` prepending `γ⁻¹` and then `γ`. The retracing prism gives
    -- `P = d H + H d + 1`, which tensors with the identity to `P ⊗ 1 = d K + K d + 1`.
    let P := (pathChainPrepend R γ b).toLinearMap ∘ₗ (pathChainPrepend R γ.symm b).toLinearMap
    have hP := DGBimoduleCat.map_eq_tensorObj_differential_comp_map_add_map_comp_add
      (M := pathChainBimodule B a b R) (M' := pathChainBimodule B a b R)
      (N := pathChainBimodule B b c R) (N' := pathChainBimodule B b c R)
      (f₁ := P.restrictScalars R) (f₂ := LinearMap.id) (k := H.restrictScalars R)
      (g := LinearMap.id)
      (fun x m ↦ P.map_smul (op x) m) (fun _ _ ↦ rfl) (fun x m ↦ H.map_smul (op x) m)
      (fun _ _ ↦ rfl)
      (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
        rw [← sub_eq_add_neg]; exact pathChainPrependHomotopy_mem γ b hx)
      (LinearMap.ext fun x ↦ (eq_sub_iff_add_eq.mp (pathChainPrependHomotopy_spec γ b x)).symm)
      rfl
    rw [BalancedTensorProduct.map_id] at hP
    intro x
    have hgx : g (pathChainConcat B a b c R x) =
        BalancedTensorProduct.map (P.restrictScalars R) LinearMap.id
          (fun x m ↦ P.map_smul (op x) m) (fun _ _ ↦ rfl) x := by
      induction x using BalancedTensorProduct.induction_on with
      | ht m n =>
        rw [LinearMap.comp_apply, mk_apply, tmul_pathPointChain_pathChainPrepend_symm_concat]
        exact (map_tmul (P.restrictScalars R) LinearMap.id _ _ m n).symm
      | ha x y hx hy => simp only [map_add, hx, hy]
    rw [hgx, hP, LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.id_apply]
    exact (add_rotate _ _ _).symm
  · -- `concat ∘ g` is prepending `γ⁻¹` and then `γ`, contracted by the retracing prism.
    intro y
    have h := pathChainPrependHomotopy_spec γ c y
    have hfg : pathChainConcat B a b c R (g y) =
        pathChainPrepend R γ c (pathChainPrepend R γ.symm c y) := by
      rw [LinearMap.comp_apply, mk_apply, pathChainPrepend_apply R γ.symm]
      exact pathChainConcat_pathPointChain γ _
    refine hfg.trans ?_
    rw [add_assoc]
    exact (add_sub_cancel y _).symm.trans (congrArg _ h.symm)

end TauCeti

end
