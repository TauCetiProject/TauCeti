/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.HSpaces

/-!
# Prepending a path to the paths of the unit interval

For a fixed path `α` from `x` to `y`, concatenation `γ ↦ α.trans γ` is a continuous map
`Path.prepend α z` from the compact-open space of paths from `y` to `z` to that of paths from
`x` to `z`. Up to homotopy of maps between path spaces, prepending is associative, unital and
depends only on the path-homotopy class of `α`, each homotopy being continuous in the path `γ`.
Consequently prepending `α` is a homotopy equivalence `Path.prependHomotopyEquiv`, with homotopy
inverse prepending the reversed path `α.symm`. Taking `z = y` identifies the loop space `Ω X y`
with the space of paths from `x` to `y`, after choosing `α`. No such identification is canonical:
it depends on the chosen path.

This is the unit-interval counterpart of `TauCeti.MoorePathBetween.prependHomotopyEquiv` for
Moore paths. Unlike the Moore model, concatenation on the unit interval is associative and
unital only up to reparametrization, so the homotopies here are reparametrizations
(`Path.reparamHomotopy`) and Serre's delay homotopy `Path.delayReflLeft`.

## Main definitions

* `Path.prepend α z`: the continuous map `γ ↦ α.trans γ`.
* `Path.reparamHomotopy`: the straight-line homotopy from the identity of a path space to a
  reparametrization.
* `Path.prependHomotopyEquiv α z`: `Path y z ≃ₕ Path x z`, with inverse prepending `α.symm`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public noncomputable section

open unitInterval ContinuousMap

namespace Path

variable {X : Type*} [TopologicalSpace X] {w x y z : X}

/-! ### Reparametrizing the paths of a path space -/

/-- Reparametrizing by a fixed endpoint-preserving map `f : I → I` is continuous on the
compact-open space of paths. -/
@[fun_prop]
theorem continuous_reparam {f : I → I} (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Continuous fun γ : Path x y ↦ γ.reparam f hf hf₀ hf₁ :=
  continuous_uncurry_iff.mp <| continuous_fst.eval (hf.comp continuous_snd)

/-- The straight-line homotopy from the identity of the path space to reparametrization by `f`,
evaluating `Path.Homotopy.reparam γ f` at each time. It is continuous in the path. -/
def reparamHomotopy (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    ContinuousMap.Homotopy (ContinuousMap.id (Path x y))
      ⟨fun γ ↦ γ.reparam f hf hf₀ hf₁, by fun_prop⟩ where
  toFun q := (Homotopy.reparam q.2 f hf hf₀ hf₁).eval q.1
  continuous_toFun := continuous_uncurry_iff.mp <|
    (continuous_snd.comp continuous_fst).eval <| by fun_prop
  map_zero_left γ := by simp
  map_one_left γ := by simp

@[simp]
theorem reparamHomotopy_apply (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
    (s : I) (γ : Path x y) :
    reparamHomotopy f hf hf₀ hf₁ (s, γ) = (Homotopy.reparam γ f hf hf₀ hf₁).eval s := (rfl)

/-! ### Prepending a path -/

/-- Prepending a fixed path `α` from `x` to `y`, as a continuous map from the paths from `y` to
`z` to the paths from `x` to `z`. -/
def prepend (α : Path x y) (z : X) : C(Path y z, Path x z) :=
  ⟨α.trans, by fun_prop⟩

@[simp]
theorem prepend_apply (α : Path x y) (γ : Path y z) : prepend α z γ = α.trans γ := (rfl)

/-- Prepending `q` and then `p` is homotopic to prepending `p.trans q`. -/
theorem homotopic_prepend_comp_prepend (p : Path w x) (q : Path x y) (z : X) :
    ((prepend p z).comp (prepend q z)).Homotopic (prepend (p.trans q) z) := by
  let φ : I → I := fun t ↦ ⟨Homotopy.transAssocReparamAux t, Homotopy.transAssocReparamAux_mem_I t⟩
  have hφ : Continuous φ := by fun_prop
  have hφ₀ : φ 0 = 0 := Subtype.ext Homotopy.transAssocReparamAux_zero
  have hφ₁ : φ 1 = 1 := Subtype.ext Homotopy.transAssocReparamAux_one
  -- `Homotopy.trans_assoc_reparam`: left association reparametrizes right association.
  have h : (⟨fun γ ↦ γ.reparam φ hφ hφ₀ hφ₁, by fun_prop⟩ : C(Path w z, Path w z)).comp
      ((prepend p z).comp (prepend q z)) = prepend (p.trans q) z := by
    ext γ : 1
    exact (Homotopy.trans_assoc_reparam p q γ).symm
  have H := (reparamHomotopy φ hφ hφ₀ hφ₁).compContinuousMap ((prepend p z).comp (prepend q z))
  rw [ContinuousMap.id_comp, h] at H
  exact ⟨H⟩

/-- Prepending depends only on the path-homotopy class of the prepended path. -/
theorem Homotopic.prepend {p p' : Path x y} (h : p.Homotopic p') (z : X) :
    (Path.prepend p z).Homotopic (Path.prepend p' z) := by
  obtain ⟨F⟩ := h
  have hF : Continuous F.eval := continuous_uncurry_iff.mp F.continuous
  exact ⟨{
    toFun q := (F.eval q.1).trans q.2
    continuous_toFun := (hF.comp continuous_fst).path_trans continuous_snd
    map_zero_left γ := by simp
    map_one_left γ := by simp }⟩

/-- Prepending a constant path is homotopic to the identity, by Serre's delay homotopy. -/
theorem homotopic_prepend_refl (x z : X) :
    (prepend (refl x) z).Homotopic (ContinuousMap.id (Path x z)) :=
  ⟨{ toFun q := delayReflLeft q.1 q.2
     continuous_toFun := continuous_delayReflLeft
     map_zero_left γ := delayReflLeft_zero γ
     map_one_left γ := delayReflLeft_one γ }⟩

/-- Prepending a path is a homotopy equivalence, with homotopy inverse prepending its
reversal. -/
def prependHomotopyEquiv (α : Path x y) (z : X) : Path y z ≃ₕ Path x z where
  toFun := prepend α z
  invFun := prepend α.symm z
  left_inv := (homotopic_prepend_comp_prepend α.symm α z).trans <|
    (Homotopic.prepend ⟨(Homotopy.reflSymmTrans α).symm⟩ z).trans (homotopic_prepend_refl y z)
  right_inv := (homotopic_prepend_comp_prepend α α.symm z).trans <|
    (Homotopic.prepend ⟨(Homotopy.reflTransSymm α).symm⟩ z).trans (homotopic_prepend_refl x z)

@[simp]
theorem prependHomotopyEquiv_apply (α : Path x y) (γ : Path y z) :
    prependHomotopyEquiv α z γ = α.trans γ := (rfl)

@[simp]
theorem prependHomotopyEquiv_symm_apply (α : Path x y) (γ : Path x z) :
    (prependHomotopyEquiv α z).symm γ = α.symm.trans γ := (rfl)

end Path
