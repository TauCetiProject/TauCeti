/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.ContravariantForm
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.RepresentationTheory.ContravariantForm

/-!
# Branching and the contravariant form of a rational Weyl module

Let `f` and `h` be intertwiners from rational Weyl modules of `GL n ℂ` to the restriction of a
rational Weyl module `V_l` of `GL (n + 1) ℂ` along the block inclusion. Pulling the contravariant
form `TauCeti.weylForm` of `V_l` back along `f` and `h` gives a contravariant pairing, so Schur's
lemma determines it: the images of nonisomorphic constituents are orthogonal, and two embeddings of
one constituent scale the form.

## Main results

* `TauCeti.weylForm_intertwiningMap_apply_eq_zero`: the images of nonisomorphic constituents are
  orthogonal.
* `TauCeti.exists_forall_weylForm_intertwiningMap_apply_eq`: two embeddings of one constituent pull
  the form back to a scalar multiple of the form of the constituent.
-/

public section

open Representation

namespace TauCeti

variable {n : ℕ} {l : DominantWeight (n + 1)} {m m' : DominantWeight n}

/-- The pairing of `V_m` and `V_m'` obtained from two intertwiners to the restriction of `V_l` is
contravariant. -/
private theorem weylForm_intertwiningMap_contravariant
    (f : IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
    (h : IntertwiningMap (rationalWeylRep ℂ n m')
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) (g : GL (Fin n) ℂ)
    (x : (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
    (y : (weylModuleOfShape ℂ n m'.detShiftShape).toSubmodule) :
    (((weylForm (n + 1) l.detShiftShape).comp f.toLinearMap).compl₂ h.toLinearMap)
        (rationalWeylRep ℂ n m g x) y =
      (((weylForm (n + 1) l.detShiftShape).comp f.toLinearMap).compl₂ h.toLinearMap) x
        (rationalWeylRep ℂ n m' (star g) y) := by
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, IntertwiningMap.coe_toLinearMap,
    IntertwiningMap.isIntertwining, MonoidHom.comp_apply, weylForm_rationalWeylRep_apply,
    glBlockSucc_star]

/-- **Branching summands are orthogonal.** The images of two nonisomorphic constituents `V_m` and
`V_m'` of the restriction of `V_l` to `GL n ℂ` are orthogonal for the contravariant form. -/
theorem weylForm_intertwiningMap_apply_eq_zero (hm : m ≠ m')
    (f : IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
    (h : IntertwiningMap (rationalWeylRep ℂ n m')
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
    (x : (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
    (y : (weylModuleOfShape ℂ n m'.detShiftShape).toSubmodule) :
    weylForm (n + 1) l.detShiftShape (f x) (h y) = 0 := by
  have hE : IsEmpty ((rationalWeylRep ℂ n m').Equiv (rationalWeylRep ℂ n m)) :=
    ⟨fun e ↦ hm ((nonempty_equiv_rationalWeylRep_iff ℂ).mp ⟨e⟩).symm⟩
  have hS := eq_zero_of_isEmpty_equiv (𝕜 := ℂ)
    (V := (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
    (W := (weylModuleOfShape ℂ n m'.detShiftShape).toSubmodule)
    (rationalWeylRep ℂ n m) (rationalWeylRep ℂ n m')
    (B := weylForm n m.detShiftShape)
    (S := ((weylForm (n + 1) l.detShiftShape).comp f.toLinearMap).compl₂ h.toLinearMap)
    (separatingRight_weylForm _) (weylForm_rationalWeylRep_apply m)
    (weylForm_intertwiningMap_contravariant f h) hE
  exact LinearMap.congr_fun₂ hS x y

/-- **An embedding of a branching summand scales the form.** Two intertwiners from `V_m` to the
restriction of `V_l` to `GL n ℂ` pull the contravariant form of `V_l` back to a scalar multiple of
that of `V_m`. -/
theorem exists_forall_weylForm_intertwiningMap_apply_eq
    (f h : IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) :
    ∃ c : ℂ, ∀ x y, weylForm (n + 1) l.detShiftShape (f x) (h y) = c * weylForm n _ x y :=
  exists_forall_apply_eq_mul_apply (𝕜 := ℂ)
    (V := (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule) (rationalWeylRep ℂ n m)
    (B := weylForm n m.detShiftShape)
    (S := ((weylForm (n + 1) l.detShiftShape).comp f.toLinearMap).compl₂ h.toLinearMap)
    (separatingRight_weylForm _) (weylForm_rationalWeylRep_apply m)
    (weylForm_intertwiningMap_contravariant f h)

end TauCeti
