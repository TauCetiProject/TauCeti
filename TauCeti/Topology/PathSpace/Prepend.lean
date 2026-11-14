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
(`Path.reparamHomotopy`) and Serre's delay homotopy `Path.delayReflLeft`. In particular the
triple concatenations `(γ₁ ⬝ γ₂) ⬝ γ₃` and `γ₁ ⬝ (γ₂ ⬝ γ₃)` differ by the reparametrization of
Mathlib's `Path.Homotopy.trans_assoc_reparam`, so the straight-line homotopy to it gives the
associativity homotopy `Path.transAssocHomotopy`, continuous in the three paths. Associativity
of prepending (`Path.homotopic_prepend_comp_prepend`) is its restriction to fixed first two paths.

## Main definitions

* `Path.prepend α z`: the continuous map `γ ↦ α.trans γ`.
* `Path.reparamHomotopy`: the straight-line homotopy from the identity of a path space to a
  reparametrization.
* `Path.transAssocHomotopy`: the homotopy, continuous in all three paths, between the two
  triple concatenations `Path x₀ x₁ × Path x₁ x₂ × Path x₂ x₃ → Path x₀ x₃`, and its traces
  `Path.transAssoc γ₁ γ₂ γ₃` in the fundamental groupoid of `Path x₀ x₃`, which are constant at
  the constant paths (`Path.transAssoc_refl`).
* `Path.Homotopic.cast_map_reparam`: reparametrizing every loop of a loop of loops does not change
  its homotopy class.
* `Path.Homotopic.Quotient.cast_map_trans_prod_refl` and
  `Path.Homotopic.Quotient.cast_map_trans_refl_prod`: concatenating every loop of a loop of loops
  with the constant loop does not change its class.
* `Path.prependHomotopyEquiv α z`: `Path y z ≃ₕ Path x z`, with inverse prepending `α.symm`.
* `Path.joined_prependHomotopyEquiv_refl`: prepending `α` to the constant path lands in the path
  component of `α`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public noncomputable section

open unitInterval ContinuousMap

namespace Path

variable {X : Type*} [TopologicalSpace X] {w x y z x₀ x₁ x₂ x₃ : X}

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
    ((L.map (continuous_reparam hf hf₀ hf₁)).cast (refl_reparam hf hf₀ hf₁).symm
      (refl_reparam hf hf₀ hf₁).symm).Homotopic L :=
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
    (L : Homotopic.Quotient (Path.refl x) (Path.refl x)) :
    ((Homotopic.prod L (Homotopic.Quotient.refl (Path.refl x))).map
      ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, continuous_trans⟩).cast
        refl_trans_refl.symm refl_trans_refl.symm = L := by
  induction L using Homotopic.Quotient.ind with
  | mk L =>
    rw [← Homotopic.Quotient.mk_refl, Homotopic.prod_lift,
      ← Homotopic.Quotient.mk_map, ← Homotopic.Quotient.mk_cast]
    refine Homotopic.Quotient.eq.2 ?_
    convert Homotopic.cast_map_reparam L
      (f := fun t =>
        ⟨Homotopy.transReflReparamAux t, Homotopy.transReflReparamAux_mem_I t⟩)
      (by fun_prop) (Subtype.ext Homotopy.transReflReparamAux_zero)
      (Subtype.ext Homotopy.transReflReparamAux_one) using 1
    ext s : 2
    exact Homotopy.trans_refl_reparam (L s)

/-- Concatenating the constant loop with every loop of a loop of loops `L` at the constant loop
does not change its homotopy class. -/
@[simp]
theorem Homotopic.Quotient.cast_map_trans_refl_prod
    (L : Homotopic.Quotient (Path.refl x) (Path.refl x)) :
    ((Homotopic.prod (Homotopic.Quotient.refl (Path.refl x)) L).map
      ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, continuous_trans⟩).cast
        refl_trans_refl.symm refl_trans_refl.symm = L := by
  induction L using Homotopic.Quotient.ind with
  | mk L =>
    rw [← Homotopic.Quotient.mk_refl, Homotopic.prod_lift,
      ← Homotopic.Quotient.mk_map, ← Homotopic.Quotient.mk_cast]
    refine Homotopic.Quotient.eq.2 ?_
    convert Homotopic.cast_map_reparam L
      (f := fun t => Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))
      (by fun_prop) (Subtype.ext (by norm_num)) (Subtype.ext (by norm_num)) using 1
    ext s : 2
    exact refl_trans_eq_reparam (L s)

/-! ### Associativity of concatenation -/

/-- **Concatenation of paths is homotopy associative**: a homotopy, continuous in the three paths,
from `(γ₁, γ₂, γ₃) ↦ (γ₁ ⬝ γ₂) ⬝ γ₃` to `(γ₁, γ₂, γ₃) ↦ γ₁ ⬝ (γ₂ ⬝ γ₃)` as maps
`Path x₀ x₁ × Path x₁ x₂ × Path x₂ x₃ → Path x₀ x₃`. At each triple of paths it is Mathlib's
`Path.Homotopy.transAssoc` (`Path.transAssocHomotopy_apply`). -/
def transAssocHomotopy :
    ContinuousMap.Homotopy
      (⟨fun γ : Path x₀ x₁ × Path x₁ x₂ × Path x₂ x₃ => (γ.1.trans γ.2.1).trans γ.2.2,
        by fun_prop⟩ : C(Path x₀ x₁ × Path x₁ x₂ × Path x₂ x₃, Path x₀ x₃))
      ⟨fun γ => γ.1.trans (γ.2.1.trans γ.2.2), by fun_prop⟩ :=
  (((reparamHomotopy (fun t => ⟨Homotopy.transAssocReparamAux t,
      Homotopy.transAssocReparamAux_mem_I t⟩) (by fun_prop)
      (Subtype.ext Homotopy.transAssocReparamAux_zero)
      (Subtype.ext Homotopy.transAssocReparamAux_one)).compContinuousMap
      ⟨fun γ : Path x₀ x₁ × Path x₁ x₂ × Path x₂ x₃ => γ.1.trans (γ.2.1.trans γ.2.2),
        by fun_prop⟩).symm).cast
    (ContinuousMap.ext fun γ => (Homotopy.trans_assoc_reparam γ.1 γ.2.1 γ.2.2).symm)
    (ContinuousMap.id_comp _)

@[simp]
theorem transAssocHomotopy_apply (θ : I) (γ₁ : Path x₀ x₁) (γ₂ : Path x₁ x₂)
    (γ₃ : Path x₂ x₃) :
    transAssocHomotopy (θ, (γ₁, γ₂, γ₃)) = (Homotopy.transAssoc γ₁ γ₂ γ₃).eval θ := by
  ext t
  simp [transAssocHomotopy, Homotopy.transAssoc]

/-- **The associator of concatenation on path classes**: the class of the trace of
`Path.transAssocHomotopy` at `(γ₁, γ₂, γ₃)`, a path in `Path x₀ x₃` from `(γ₁ ⬝ γ₂) ⬝ γ₃` to
`γ₁ ⬝ (γ₂ ⬝ γ₃)`. -/
def transAssoc (γ₁ : Path x₀ x₁) (γ₂ : Path x₁ x₂) (γ₃ : Path x₂ x₃) :
    (⟨(γ₁.trans γ₂).trans γ₃⟩ : FundamentalGroupoid (Path x₀ x₃)) ⟶ ⟨γ₁.trans (γ₂.trans γ₃)⟩ :=
  ⟦transAssocHomotopy.evalAt (γ₁, γ₂, γ₃)⟧

theorem transAssoc_def (γ₁ : Path x₀ x₁) (γ₂ : Path x₁ x₂) (γ₃ : Path x₂ x₃) :
    transAssoc γ₁ γ₂ γ₃ = ⟦transAssocHomotopy.evalAt (γ₁, γ₂, γ₃)⟧ :=
  (rfl)

/-- At the constant paths the associator is the constant path, transported along
`(c ⬝ c) ⬝ c = c ⬝ (c ⬝ c)`. -/
@[simp]
theorem transAssoc_refl :
    transAssoc (refl x) (refl x) (refl x) =
      CategoryTheory.eqToHom
        (congrArg FundamentalGroupoid.mk (by rw [refl_trans_refl, refl_trans_refl])) := by
  rw [FundamentalGroupoid.eqToHom_eq (by rw [refl_trans_refl, refl_trans_refl])]
  refine congrArg Path.Homotopic.Quotient.mk
    (Path.ext (funext fun θ => Path.ext (funext fun t => ?_)))
  simp [ContinuousMap.Homotopy.evalAt, Homotopy.transAssoc, Homotopy.reparam]
  -- What remains is the reparametrizing homotopy of the constant path, a structure literal
  -- whose value is `x` by definition.
  rfl

/-! ### Prepending a path -/

/-- Prepending a fixed path `α` from `x` to `y`, as a continuous map from the paths from `y` to
`z` to the paths from `x` to `z`. -/
def prepend (α : Path x y) (z : X) : C(Path y z, Path x z) :=
  ⟨α.trans, by fun_prop⟩

@[simp]
theorem prepend_apply (α : Path x y) (γ : Path y z) : prepend α z γ = α.trans γ := (rfl)

/-- Prepending `q` and then `p` is homotopic to prepending `p.trans q`. -/
theorem homotopic_prepend_comp_prepend (p : Path w x) (q : Path x y) (z : X) :
    ((prepend p z).comp (prepend q z)).Homotopic (prepend (p.trans q) z) :=
  ⟨(transAssocHomotopy.compContinuousMap ⟨fun γ ↦ (p, q, γ), by fun_prop⟩).symm⟩

/-- Prepending depends only on the path-homotopy class of the prepended path. -/
theorem Homotopic.prepend {p p' : Path x y} (h : p.Homotopic p') (z : X) :
    (prepend p z).Homotopic (prepend p' z) := by
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

/-- Prepending `α` to the constant path gives a path joined to `α` in the path space, through
the reparametrization of `α.trans (refl y)` back to `α`. -/
theorem joined_prependHomotopyEquiv_refl (α : Path x y) :
    Joined (prependHomotopyEquiv α y (refl y)) α := by
  rw [prependHomotopyEquiv_apply, Homotopy.trans_refl_reparam]
  exact ⟨((reparamHomotopy _ (by fun_prop) (Subtype.ext Homotopy.transReflReparamAux_zero)
    (Subtype.ext Homotopy.transReflReparamAux_one)).evalAt α).symm⟩

end Path
