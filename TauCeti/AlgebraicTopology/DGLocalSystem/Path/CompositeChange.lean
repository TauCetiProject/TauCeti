/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Concatenation

/-!
# Changing the basepoint twice

A DG local system at `a`, a right DG module `M` over the chain algebra `C_*(Ω_a B)`, changes its
basepoint to `b` by tensoring with the chain bimodule `C_*(P_{a→b} B)` of Moore paths from `a`
to `b`. This file compares two successive changes of basepoint, along the paths from `a` to `b`
and then along those from `b` to `c`, with the single change along the paths from `a` to `c`.
Reassociating the tensor products and concatenating the path chains gives a morphism of DG local
systems at `c` (`TauCeti.tensorPathChainConcat`),

`(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B) ⟶ M ⊗ C_*(P_{a→c} B)`, `(m ⊗ σ) ⊗ τ ↦ m ⊗ (σ ⋆ τ)`,

and it is a quasi-isomorphism as soon as `a` and `b` are joined by a Moore path
(`TauCeti.isQuasiIso_tensorPathChainConcat`). So the composite of two changes of basepoint is the
change along the composite, through a specified quasi-isomorphism. For `c = a`, changing the
basepoint to `b` and back gives, up to quasi-isomorphism, the tensor product of `M` with the
chains on the Moore paths from `a` to itself.

The proof shows that both sides are homotopy retracts of `M`, compatibly with the morphism. For a
Moore path `δ` from `a` to `c`, the map `m ⊗ σ ↦ m · ρ_δ(σ)`, where `ρ_δ` appends the reversal
of `δ`, and the map `m ↦ m ⊗ [δ]` back make `M ⊗ C_*(P_{a→c} B)` a homotopy retract of `M`
(`TauCeti.tensorPathChainPoint_tensorPathChainAct`). For Moore paths `γ` from `a` to `b` and `δ`
from `b` to `c`, doing this along `γ` and then along `δ` makes
`(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B)` a homotopy retract of `M` as well. The morphism carries
`(m ⊗ [γ]) ⊗ [δ]` to `m ⊗ [γ ⋆ δ]`, and since reversing a concatenation of Moore paths
concatenates the reversals in the opposite order,
`ρ_{γ ⋆ δ}(σ ⋆ τ) = ρ_γ(σ · ρ_δ(τ))` (`TauCeti.pathChainToLoopChain_trans_pathChainConcat`). A
morphism compatible in this way with two homotopy retractions onto the same module is a
quasi-isomorphism (`TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyRetract`). None of the maps
of the retractions needs to be linear over the loops at `c`.

## Main definitions

* `TauCeti.tensorPathChainConcat`: the composite change of basepoint
  `(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B) ⟶ M ⊗ C_*(P_{a→c} B)`.
* `TauCeti.tensorPathChainConcatNatTrans`: the composite change of basepoint, as a natural
  transformation from changing along `a → b` and then `b → c` to changing along `a → c`.

## Main results

* `TauCeti.tensorPathChainConcat_tmul`: on pure tensors it concatenates the path chains.
* `TauCeti.tensorPathChainConcat_naturality`: the composite change of basepoint is natural in the
  DG local system.
* `TauCeti.pathChainToLoopChain_trans_pathChainConcat`: `ρ_{γ ⋆ δ}(σ ⋆ τ) = ρ_γ(σ · ρ_δ(τ))`.
* `TauCeti.isQuasiIso_tensorPathChainConcat`: if `a` and `b` are joined by a Moore path, the
  composite change of basepoint is a quasi-isomorphism.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

open BalancedTensorProduct DGRightModuleCat

universe u w v

variable {B : Type u} [TopologicalSpace B] {R : Type w} [CommRing R]

section Concatenation

variable {a b c : B}

/-- **Appending the reversal of a concatenation**: `ρ_{γ ⋆ δ}(σ ⋆ τ)` is `ρ_γ(σ · ρ_δ(τ))`, for the
maps `ρ` of `TauCeti.pathChainToLoopChain` and the loops at `b` acting on `σ` from behind. On
paths both sides append `δ⁻¹` and then `γ⁻¹` to `σ ⋆ τ`. -/
theorem pathChainToLoopChain_trans_pathChainConcat (γ : MoorePathBetween B a b)
    (δ : MoorePathBetween B b c)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainToLoopChain R (γ.trans δ)
        (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) x y)) =
      pathChainToLoopChain R γ (op (pathChainToLoopChain R δ y) • x) := by
  -- The loops at `b` act from behind by the pairing induced by the action.
  have hact (α : loopChainAlgebra B b R) :
      cubicalChainModuleEquiv _ _ R (op α • x) =
        cubicalChainSumPairing R (actMap (MoorePathBetween B a b) (MooreLoopSpace B b))
          (cubicalChainModuleEquiv _ _ R x) α := by
    have h := op_cubicalChainModuleEquiv_smul_eq_cubicalChainPairing (R := R)
      ((cubicalChainModuleEquiv (MooreLoopSpace B b) (MooreLoopSpace B b) R).symm α) x
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, cubicalChainModuleEquiv_cubicalChainPairing, LinearEquiv.apply_symm_apply]
  rw [pathChainToLoopChain_apply, pathChainToLoopChain_apply, pathChainToLoopChain_apply, hact,
    pathChainConcat_tmul, cubicalChainModuleEquiv_cubicalChainPairing,
    cubicalChainSumMap_cubicalChainSumPairing
      (g := (MoorePathBetween.loopAppendHomotopyEquiv γ).symm.toFun),
    cubicalChainSumMap_cubicalChainSumPairing_of_comp (h := ContinuousMap.id _)
      (h' := (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun)
      (f' := (MoorePathBetween.loopAppendHomotopyEquiv γ).symm.toFun.comp
        (actMap (MoorePathBetween B a b) (MooreLoopSpace B b))),
    cubicalChainSumMap_id, LinearMap.id_apply]
  intro p q
  ext1
  simp [actMap_apply, MoorePathBetween.toMoorePath_rightAct, MoorePath.trans_assoc,
    MoorePath.symm_trans]

end Concatenation

section CompositeChange

attribute [local instance 100] BalancedTensorProduct.rightModule
  BalancedTensorProduct.rightIsScalarTower

variable {a : B} (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))

/-- **Changing the basepoint twice**: the morphism
`(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B) ⟶ M ⊗ C_*(P_{a→c} B)` of DG local systems at `c`,
`(m ⊗ σ) ⊗ τ ↦ m ⊗ (σ ⋆ τ)`, from the change of basepoint of `M` along the paths from `a` to `b`
and then along the paths from `b` to `c`, to its change along the paths from `a` to `c`. It is
the reassociation of the tensor products followed by the concatenation of path chains. -/
def tensorPathChainConcat (b c : B) :
    tensorBimoduleObj (tensorBimoduleObj M (pathChainBimodule B a b R))
        (pathChainBimodule B b c R) ⟶
      tensorBimoduleObj M (pathChainBimodule B a c R) :=
  DGBimoduleCat.forgetToRightModuleCat.map
    ((DGBimoduleCat.tensorAssoc M.toScalarBimodule (pathChainBimodule B a b R)
        (pathChainBimodule B b c R)).hom ≫
      DGBimoduleCat.tensorMap (𝟙 M.toScalarBimodule) (pathChainConcat B a b c R))

/-- On pure tensors, the composite change of basepoint concatenates the path chains. -/
@[simp]
theorem tensorPathChainConcat_tmul {b c : B} (m : M)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    tensorPathChainConcat M b c (tmul R (loopChainAlgebra B b R)
        (tmul R (loopChainAlgebra B a R) m x : tensorBimoduleObj M (pathChainBimodule B a b R))
          y) =
      tmul R (loopChainAlgebra B a R) m
        (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) x y)) := by
  rw [tensorPathChainConcat, DGBimoduleCat.forgetToRightModuleCat_map]
  -- The bundled bimodule lemmas apply once the morphism is read in the bimodule category.
  refine (DGBimoduleCat.comp_apply _ _ _).trans ?_
  rw [DGBimoduleCat.tensorAssoc_hom_tmul, DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.id_apply]

/-- **Composing changes of basepoint is natural** in the DG local system. -/
theorem tensorPathChainConcat_naturality {N : DGRightModuleCat.{w, max u w, v}
    (loopChain_isDGAlgebra B a R)} (f : M ⟶ N) (b c : B) :
    tensorBimoduleMap (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R)))
          (𝟙 (pathChainBimodule B b c R)) ≫ tensorPathChainConcat N b c =
      tensorPathChainConcat M b c ≫ tensorBimoduleMap f (𝟙 (pathChainBimodule B a c R)) := by
  refine tensorBimoduleObj_hom_ext fun w y ↦ ?_
  induction w using BalancedTensorProduct.induction_on with
  | ht m x =>
    rw [DGRightModuleCat.comp_apply, DGRightModuleCat.comp_apply, tensorBimoduleMap_tmul,
      tensorBimoduleMap_tmul, DGBimoduleCat.id_apply, DGBimoduleCat.id_apply,
      tensorPathChainConcat_tmul, tensorPathChainConcat_tmul, tensorBimoduleMap_tmul,
      DGBimoduleCat.id_apply]
  | ha w w' hw hw' => simp only [add_tmul, map_add, hw, hw']

variable {M} {b c : B}

/-- Following the composite change of basepoint by `m ⊗ σ ↦ m · ρ_{γ ⋆ δ}(σ)` is the map
`n ⊗ τ ↦ n · ρ_δ(τ)` of the change along `δ`, followed by the map `m ⊗ σ ↦ m · ρ_γ(σ)` of the
change along `γ`. -/
theorem tensorPathChainAct_trans_tensorPathChainConcat (γ : MoorePathBetween B a b)
    (δ : MoorePathBetween B b c)
    (z : tensorBimoduleObj (tensorBimoduleObj M (pathChainBimodule B a b R))
      (pathChainBimodule B b c R)) :
    tensorPathChainAct M (γ.trans δ) (tensorPathChainConcat M b c z) =
      tensorPathChainAct M γ
        (tensorPathChainAct (tensorBimoduleObj M (pathChainBimodule B a b R)) δ z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', map_add]
  | ht n y =>
    induction n using BalancedTensorProduct.induction_on with
    | ha n n' hn hn' => rw [add_tmul, map_add, map_add, map_add, hn, hn', map_add]
    | ht m x =>
      rw [tensorPathChainConcat_tmul, tensorPathChainAct_tmul, tensorPathChainAct_tmul,
        smul_tmul_right, tensorPathChainAct_tmul, pathChainToLoopChain_trans_pathChainConcat]

/-- The composite change of basepoint sends `(m ⊗ [γ]) ⊗ [δ]` to `m ⊗ [γ ⋆ δ]`. -/
theorem tensorPathChainConcat_tensorPathChainPoint (γ : MoorePathBetween B a b)
    (δ : MoorePathBetween B b c) (m : M) :
    tensorPathChainConcat M b c
        (tensorPathChainPoint _ δ (tensorPathChainPoint M γ m)) =
      tensorPathChainPoint M (γ.trans δ) m := by
  rw [tensorPathChainPoint_apply, tensorPathChainPoint_apply, tensorPathChainConcat_tmul,
    tensorPathChainPoint_apply, pathChainConcat_tmul]
  simp only [pathChainPoint_def]
  rw [cubicalChainPairing_lof_point_left, cubicalChainModuleLinearMap_lof,
    NormalizedCubicalChain.map_ofCube]
  congr 3
  ext1
  simp

/-- The two changes of basepoint, along `γ` and then along `δ`, make
`(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B)` a homotopy retract of `M`: following
`z ↦ ρ_γ(ρ_δ(z))` by `m ↦ (m ⊗ [γ]) ⊗ [δ]` is homotopic to the identity, through the homotopy
of the second change and the first homotopy carried along the second change. -/
private theorem tensorPathChainPoint_tensorPathChainAct_trans (γ : MoorePathBetween B a b)
    (δ : MoorePathBetween B b c)
    (z : tensorBimoduleObj (tensorBimoduleObj M (pathChainBimodule B a b R))
      (pathChainBimodule B b c R)) :
    let N := tensorBimoduleObj M (pathChainBimodule B a b R)
    let K := tensorPathChainHomotopy N δ +
      tensorPathChainPoint N δ ∘ₗ tensorPathChainHomotopy M γ ∘ₗ tensorPathChainAct N δ
    tensorPathChainPoint N δ (tensorPathChainPoint M γ
        (tensorPathChainAct M γ (tensorPathChainAct N δ z))) =
      z + (tensorBimoduleObj N (pathChainBimodule B b c R)).differential (K z) +
        K ((tensorBimoduleObj N (pathChainBimodule B b c R)).differential z) := by
  intro N K
  have h := tensorPathChainPoint_tensorPathChainAct γ (tensorPathChainAct N δ z)
  rw [differential_tensorPathChainAct] at h
  rw [h, map_add, map_add, tensorPathChainPoint_tensorPathChainAct δ, LinearMap.add_apply,
    LinearMap.add_apply, map_add, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, differential_tensorPathChainPoint]
  abel

variable (M) in
/-- **Changing the basepoint twice is changing it once**: if `a` and `b` are joined by a Moore
path, the composite change of basepoint
`(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B) → M ⊗ C_*(P_{a→c} B)` is a quasi-isomorphism of DG local
systems at `c`. The hypothesis cannot be dropped: without a path from `a` to `b` the source
vanishes, while the target need not. -/
theorem isQuasiIso_tensorPathChainConcat (h : Nonempty (MoorePathBetween B a b)) :
    IsQuasiIso (tensorPathChainConcat M b c) := by
  obtain ⟨γ⟩ := h
  let N := tensorBimoduleObj M (pathChainBimodule B a b R)
  -- Instance search does not see the graded actions on a tensor product through its carrier.
  let := (tensorBimoduleObj N (pathChainBimodule B b c R)).gradedSMul
  let := (tensorBimoduleObj M (pathChainBimodule B a c R)).gradedSMul
  rcases isEmpty_or_nonempty (MoorePathBetween B b c) with hc | ⟨⟨δ⟩⟩
  · -- Without Moore paths from `b` to `c` there are none from `a` to `c`, so both sides vanish.
    have : IsEmpty (MoorePathBetween B a c) := ⟨fun η ↦ hc.false (γ.symm.trans η)⟩
    rw [IsQuasiIso, DGRightModuleHom.isQuasiIso_iff_forall_exists]
    exact fun _ _ _ _ ↦ ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · -- Both sides are homotopy retracts of `M`, compatibly with the composite change.
    refine DGRightModuleHom.isQuasiIso_of_homotopyRetract (tensorPathChainConcat M b c)
      (LinearMap.id : M →ₗ[R] M) (dM₀ := M.differential) (dN₀ := M.differential)
      (fun x y _ hxy ↦ ⟨y, 0, hxy.symm, by rw [map_zero, add_zero, LinearMap.id_apply]⟩)
      (tensorPathChainAct M γ ∘ₗ tensorPathChainAct N δ)
      (tensorPathChainPoint N δ ∘ₗ tensorPathChainPoint M γ)
      (tensorPathChainHomotopy N δ +
        tensorPathChainPoint N δ ∘ₗ tensorPathChainHomotopy M γ ∘ₗ tensorPathChainAct N δ)
      (tensorPathChainAct M (γ.trans δ)) (tensorPathChainPoint M (γ.trans δ))
      (tensorPathChainHomotopy M (γ.trans δ)) (fun z ↦ ?_) (fun m ↦ ?_)
      (differential_tensorPathChainAct _) (differential_tensorPathChainPoint _)
      (tensorPathChainPoint_tensorPathChainAct_trans γ δ)
      (tensorPathChainPoint_tensorPathChainAct _)
      (tensorPathChainAct_trans_tensorPathChainConcat γ δ)
      (tensorPathChainConcat_tensorPathChainPoint γ δ)
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, differential_tensorPathChainAct,
        differential_tensorPathChainAct]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, differential_tensorPathChainPoint,
        differential_tensorPathChainPoint]

end CompositeChange

section Naturality

attribute [local instance 100] BalancedTensorProduct.rightModule
  BalancedTensorProduct.rightIsScalarTower

variable {a : B}

variable (B R)

/-- **The composite change of basepoint as a natural transformation**: changing the basepoint of
DG local systems along the paths from `a` to `b` and then along the paths from `b` to `c` maps to
changing it along the paths from `a` to `c`, by `(m ⊗ σ) ⊗ τ ↦ m ⊗ (σ ⋆ τ)`. -/
def tensorPathChainConcatNatTrans (a b c : B) :
    tensorBimoduleFunctor.{w, max u w, max u w, max u w v, max u w}.flip.obj
          (pathChainBimodule B a b R) ⋙
        tensorBimoduleFunctor.flip.obj (pathChainBimodule B b c R) ⟶
      tensorBimoduleFunctor.flip.obj (pathChainBimodule B a c R) where
  app M := tensorPathChainConcat M b c
  naturality _ _ f := tensorPathChainConcat_naturality _ f b c

/-- The components of `TauCeti.tensorPathChainConcatNatTrans` are
`TauCeti.tensorPathChainConcat`. -/
@[simp]
theorem tensorPathChainConcatNatTrans_app (a b c : B)
    (M : DGRightModuleCat.{w, max u w, max u w v} (loopChain_isDGAlgebra B a R)) :
    (tensorPathChainConcatNatTrans.{u, w, v} B R a b c).app M = tensorPathChainConcat M b c :=
  (rfl)

end Naturality

end TauCeti
