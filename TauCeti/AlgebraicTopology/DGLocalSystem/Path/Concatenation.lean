/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Bimodule
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

## Main definitions

* `TauCeti.pathChainConcat B a b c R`: the composition morphism
  `C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)`.

## Main results

* `TauCeti.pathChainConcat_tmul`: on pure tensors, the composition is the pairing of cubical
  chains induced by concatenation of Moore paths.
* `TauCeti.pathChainConcat_tmul_ofCube`: the composition concatenates cubes pointwise.
* `TauCeti.pathChainConcat_assoc`: the composition is associative.

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

end TauCeti

end
