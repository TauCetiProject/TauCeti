/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.Topology.Homotopy.Product
public import TauCeti.Topology.Homotopy.Path

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
* `Path.Homotopic.cast_map_reparam`: reparametrizing every loop of a loop of loops does not change
  its homotopy class.
* `Path.Homotopic.Quotient.cast_map_trans_prod_refl` and
  `Path.Homotopic.Quotient.cast_map_trans_refl_prod`: concatenating every loop of a loop of loops
  with the constant loop does not change its class.
* `Path.prependHomotopyEquiv α z`: `Path y z ≃ₕ Path x z`, with inverse prepending `α.symm`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public noncomputable section

open unitInterval ContinuousMap

namespace Path

variable {X : Type*} [TopologicalSpace X] {w x y z : X}

/-- Serre's left delay is continuous for a family of paths with varying endpoints. -/
theorem delayReflLeft_continuous_family {A : Type*} [TopologicalSpace A]
    {a b : A → X} (γ : ∀ q, Path (a q) (b q)) (hγ : Continuous ↿γ)
    (s : C(A, I)) : Continuous ↿fun q ↦ delayReflLeft (s q) (γ q) := by
  -- The delay is evaluation at the reflected Serre reparametrization; this also works when
  -- the endpoints vary, where continuity in a single fixed native path space does not apply.
  have h : Continuous (fun q : A × I ↦ γ q.1 (σ (qRight (σ q.2, s q.1)))) :=
    hγ.comp (show Continuous (fun q : A × I ↦ (q.1, σ (qRight (σ q.2, s q.1)))) from by
      fun_prop)
  exact h

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

/-- Reparametrizing every loop of a loop `L` at the constant loop in `Ω X x` by the same map `f`
does not change the homotopy class of `L`: `reparamHomotopy` acts on all loops at once and fixes
the constant loop. -/
theorem Homotopic.cast_map_reparam (L : Path (Path.refl x) (Path.refl x)) {f : I → I}
    (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    ((L.map (continuous_reparam hf hf₀ hf₁)).cast (Path.refl_reparam hf hf₀ hf₁).symm
      (Path.refl_reparam hf hf₀ hf₁).symm).Homotopic L :=
  Homotopic.symm ⟨{
    toFun p := reparamHomotopy f hf hf₀ hf₁ (p.1, L p.2)
    continuous_toFun := (reparamHomotopy f hf hf₀ hf₁).continuous.comp
      (continuous_fst.prodMk (L.continuous.comp continuous_snd))
    map_zero_left s := by simp
    map_one_left s := by simp
    prop' r s hs := by
      -- At the ends `L` is the constant loop, which every reparametrization fixes. The `change`
      -- unfolds the homotopy's value and the cast path at an endpoint, after which the
      -- reparametrized constant loop is the constant loop by definition, closed by `rfl`.
      rcases hs with rfl | hs
      · change reparamHomotopy f hf hf₀ hf₁ (r, L 0) = L 0
        rw [L.source]
        rfl
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        change reparamHomotopy f hf hf₀ hf₁ (r, L 1) = L 1
        rw [L.target]
        rfl }⟩

/-- Concatenating every loop of a loop of loops `L` at the constant loop with the constant loop
does not change its homotopy class. -/
@[simp]
theorem Homotopic.Quotient.cast_map_trans_prod_refl
    (L : Path.Homotopic.Quotient (Path.refl x) (Path.refl x)) :
    ((Path.Homotopic.prod L (Path.Homotopic.Quotient.refl (Path.refl x))).map
      ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, Path.continuous_trans⟩).cast
        Path.refl_trans_refl.symm Path.refl_trans_refl.symm = L := by
  induction L using Path.Homotopic.Quotient.ind with
  | mk L =>
    rw [← Path.Homotopic.Quotient.mk_refl, Path.Homotopic.prod_lift,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    refine Path.Homotopic.Quotient.eq.2 ?_
    convert Path.Homotopic.cast_map_reparam L
      (f := fun t =>
        ⟨Path.Homotopy.transReflReparamAux t, Path.Homotopy.transReflReparamAux_mem_I t⟩)
      (by fun_prop) (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
      (Subtype.ext Path.Homotopy.transReflReparamAux_one) using 1
    ext s : 2
    exact Path.Homotopy.trans_refl_reparam (L s)

/-- Concatenating the constant loop with every loop of a loop of loops `L` at the constant loop
does not change its homotopy class. -/
@[simp]
theorem Homotopic.Quotient.cast_map_trans_refl_prod
    (L : Path.Homotopic.Quotient (Path.refl x) (Path.refl x)) :
    ((Path.Homotopic.prod (Path.Homotopic.Quotient.refl (Path.refl x)) L).map
      ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, Path.continuous_trans⟩).cast
        Path.refl_trans_refl.symm Path.refl_trans_refl.symm = L := by
  induction L using Path.Homotopic.Quotient.ind with
  | mk L =>
    rw [← Path.Homotopic.Quotient.mk_refl, Path.Homotopic.prod_lift,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    refine Path.Homotopic.Quotient.eq.2 ?_
    convert Path.Homotopic.cast_map_reparam L
      (f := fun t => Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))
      (by fun_prop) (Subtype.ext (by norm_num)) (Subtype.ext (by norm_num)) using 1
    ext s : 2
    exact Path.refl_trans_eq_reparam (L s)

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
