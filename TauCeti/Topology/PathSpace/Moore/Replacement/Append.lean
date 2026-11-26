/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Between.Append
public import TauCeti.Topology.PathSpace.Moore.From
public import TauCeti.Topology.PathSpace.Moore.Replacement.Basic

/-!
# Moving the fibres of the Moore-path replacement along a path

For a continuous map `p : E → B`, the fibre `F'_a` of the Moore-path replacement of `p` over `a`
consists of the pairs `(e, γ)` of a point `e ∈ E` and a Moore path `γ` from `p e` to `a`. A Moore
path `δ` from `a` to `b` moves it to the fibre over `b`, `(e, γ) ↦ (e, γ ⋆ δ)`
(`TauCeti.MooreReplacement.Fiber.append`). By strict associativity of Moore concatenation, this is
balanced over the loops at `a`, which act on `F'_a` from behind and on the paths from `a` to `b`
in front, and it commutes with the loops at `b` acting from behind. These are the identities that
make it induce a morphism of DG local systems from the basepoint change of `C_*(F'_a)` to
`C_*(F'_b)`.

Appending `δ⁻¹` and then `δ` is homotopic to the identity of `F'_b`, through the growing
retracing loop `δ⁻¹|[0, s] ⋆ (δ⁻¹|[0, s])⁻¹` acting from behind
(`TauCeti.MooreReplacement.Fiber.appendSymmHomotopy`). So appending a fixed path is a homotopy
equivalence between the fibres over its endpoints, for every map `p`
(`TauCeti.MooreReplacement.Fiber.appendHomotopyEquiv`).

A Moore path `δ` starting at `b`, with no condition on its end point, moves a point `(e, γ)` of
`F'_b` into the total space `E'` of the replacement, `(e, γ) ↦ (e, γ ⋆ δ)`
(`TauCeti.MooreReplacement.Fiber.appendFrom`), a point over the end point of `δ`. This is balanced
over the loops at `b`, which act on the Moore paths from `b` in front
(`TauCeti.MooreReplacement.Fiber.act_appendFrom`): it is the map through which a model of the
chains on the paths from `b` is compared with the chains on the total space.

## Main definitions

* `TauCeti.MooreReplacement.Fiber.append`: the point `(e, γ ⋆ δ)` of `F'_b`.
* `TauCeti.MooreReplacement.Fiber.appendMap`: appending, as a continuous map
  `F'_a × P_{a→b} B → F'_b`.
* `TauCeti.MooreReplacement.Fiber.appendPath`: appending a fixed path, as a continuous map
  `F'_a → F'_b`.
* `TauCeti.MooreReplacement.Fiber.appendSymmHomotopy`: the homotopy from the identity of `F'_b` to
  appending `δ⁻¹` and then `δ`.
* `TauCeti.MooreReplacement.Fiber.appendHomotopyEquiv`: `F'_a ≃ₕ F'_b`, by appending `δ`.
* `TauCeti.MooreReplacement.Fiber.appendFrom`: the point `(e, γ ⋆ δ)` of `E'`, for a Moore path
  `δ` from `b`.
* `TauCeti.MooreReplacement.Fiber.appendFromMap`: as a continuous map `F'_b × P_b B → E'`.

## Main results

* `TauCeti.MooreReplacement.Fiber.act_append`: appending is balanced over the loops at `a`.
* `TauCeti.MooreReplacement.Fiber.append_op_smul`: appending commutes with the loops at `b`.
* `TauCeti.MooreReplacement.Fiber.append_append`: appending two paths is appending their
  concatenation.
* `TauCeti.MooreReplacement.Fiber.map_append`: appending commutes with the maps of fibres induced
  by maps over `B`.
* `TauCeti.MooreReplacement.Fiber.act_appendFrom`: appending a path from `b` is balanced over the
  loops at `b`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open scoped NNReal
open unitInterval MulOpposite ContinuousMap

namespace TauCeti.MooreReplacement.Fiber

variable {E E' B : Type*} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {a b c : B}

/-- **Appending a Moore path to a point of the fibre**: a Moore path `δ` from `a` to `b` moves the
point `(e, γ)` of the fibre over `a` to the point `(e, γ ⋆ δ)` of the fibre over `b`. -/
def append (x : Fiber p a) (δ : MoorePathBetween B a b) : Fiber p b :=
  ⟨MooreReplacement.mk x.val.point (x.val.path.trans δ.toMoorePath (by simp))
    (by rw [MoorePath.source_trans, source_path]), by simp⟩

@[simp]
theorem point_append (x : Fiber p a) (δ : MoorePathBetween B a b) :
    (x.append δ).val.point = x.val.point := by
  rw [val_eq_subtypeVal]
  exact point_mk _ _ _

@[simp]
theorem path_append (x : Fiber p a) (δ : MoorePathBetween B a b) :
    (x.append δ).val.path = x.val.path.trans δ.toMoorePath (by simp) := by
  rw [val_eq_subtypeVal]
  exact path_mk _ _ _

/-- Appending is continuous in both variables. -/
theorem continuous_append :
    Continuous fun q : Fiber p a × MoorePathBetween B a b ↦ q.1.append q.2 :=
  (continuous_mk (continuous_point.comp (continuous_val.comp continuous_fst))
    ((continuous_path.comp (continuous_val.comp continuous_fst)).moorePath_trans
      (MoorePathBetween.continuous_toMoorePath.comp continuous_snd) _) _).subtype_mk _

/-- **Appending is balanced over the loops at `a`**: acting by a loop `ω` on `(e, γ)` and then
appending `δ` is appending `ω ⋆ δ`. -/
theorem act_append (x : Fiber p a) (ω : MooreLoopSpace B a) (δ : MoorePathBetween B a b) :
    (x.act ω).append δ = x.append (ω • δ) :=
  ext (MooreReplacement.ext (by simp) (by simp [MoorePath.trans_assoc]))

/-- **Appending commutes with the loops at `b`**: appending `δ ⋆ ω` is appending `δ` and then
acting by `ω`. -/
theorem append_op_smul (x : Fiber p a) (δ : MoorePathBetween B a b) (ω : MooreLoopSpace B b) :
    x.append (op ω • δ) = (x.append δ).act ω :=
  ext (MooreReplacement.ext (by simp) (by simp [MoorePath.trans_assoc]))

/-- Appending two paths in turn is appending their concatenation. -/
theorem append_append (x : Fiber p a) (δ : MoorePathBetween B a b)
    (δ' : MoorePathBetween B b c) : (x.append δ).append δ' = x.append (δ.trans δ') :=
  ext (MooreReplacement.ext (by simp) (by simp [MoorePath.trans_assoc]))

/-- Appending commutes with the maps of fibres induced by maps over `B`. -/
@[simp]
theorem map_append {p' : C(E', B)} (h : C(E, E')) (hh : p'.comp h = p) (x : Fiber p a)
    (δ : MoorePathBetween B a b) : map h hh (x.append δ) = (map h hh x).append δ :=
  ext (MooreReplacement.ext (by simp) (by simp))

variable (p a b) in
/-- Appending, as a continuous map `F'_a × P_{a→b} B → F'_b`. -/
def appendMap : C(Fiber p a × MoorePathBetween B a b, Fiber p b) :=
  ⟨fun q ↦ q.1.append q.2, continuous_append⟩

@[simp]
theorem appendMap_apply (q : Fiber p a × MoorePathBetween B a b) :
    appendMap p a b q = q.1.append q.2 :=
  (rfl)

/-- Appending a fixed Moore path `δ` from `a` to `b`, as a continuous map `F'_a → F'_b`. -/
def appendPath (δ : MoorePathBetween B a b) : C(Fiber p a, Fiber p b) :=
  ⟨fun x ↦ x.append δ, continuous_append.comp (continuous_id.prodMk continuous_const)⟩

@[simp]
theorem appendPath_apply (δ : MoorePathBetween B a b) (x : Fiber p a) :
    appendPath δ x = x.append δ :=
  (rfl)

/-- **The inverse homotopy for appending a path**: on the fibre over `b`, the identity is homotopic
to appending `δ⁻¹` and then `δ`, through the action of the growing retracing loop
`δ⁻¹|[0, s] ⋆ (δ⁻¹|[0, s])⁻¹`. -/
def appendSymmHomotopy (δ : MoorePathBetween B a b) :
    ContinuousMap.Homotopy (.id (Fiber p b))
      ((appendPath δ).comp (appendPath (p := p) δ.symm)) where
  toFun q := q.2.act (δ.symm.retrace (toNNReal q.1 * δ.toMoorePath.length))
  continuous_toFun := continuous_act.comp (continuous_snd.prodMk
    (MoorePathBetween.continuous_retrace.comp (continuous_const.prodMk
      ((toNNReal_continuous.comp continuous_fst).mul continuous_const))))
  map_zero_left x := by simp
  map_one_left x := by
    have hfull : δ.toMoorePath.symm.truncate δ.toMoorePath.length = δ.toMoorePath.symm := by
      simpa only [MoorePath.length_symm] using δ.toMoorePath.symm.truncate_length
    refine ext (MooreReplacement.ext (by simp) ?_)
    simp [hfull, MoorePath.trans_assoc]

@[simp]
theorem appendSymmHomotopy_apply (δ : MoorePathBetween B a b) (s : I) (x : Fiber p b) :
    appendSymmHomotopy δ (s, x) = x.act (δ.symm.retrace (toNNReal s * δ.toMoorePath.length)) :=
  (rfl)

/-- **Appending a path is a homotopy equivalence between fibres**, with inverse appending its
reversal. No fibration hypothesis on `p` is needed. -/
def appendHomotopyEquiv (δ : MoorePathBetween B a b) : Fiber p a ≃ₕ Fiber p b where
  toFun := appendPath δ
  invFun := appendPath δ.symm
  left_inv := ⟨by simpa only [MoorePathBetween.symm_symm] using (appendSymmHomotopy δ.symm).symm⟩
  right_inv := ⟨(appendSymmHomotopy δ).symm⟩

@[simp]
theorem appendHomotopyEquiv_apply (δ : MoorePathBetween B a b) (x : Fiber p a) :
    appendHomotopyEquiv δ x = x.append δ :=
  (rfl)

@[simp]
theorem appendHomotopyEquiv_symm_apply (δ : MoorePathBetween B a b) (x : Fiber p b) :
    (appendHomotopyEquiv δ).symm x = x.append δ.symm :=
  (rfl)

/-! ### Appending a path from the base point -/

/-- **Appending a Moore path from the base point**: a Moore path `δ` starting at `b` moves the point
`(e, γ)` of the fibre over `b` to the point `(e, γ ⋆ δ)` of the total space of the replacement,
which lies over the end point of `δ`. -/
def appendFrom (x : Fiber p b) (δ : MoorePathFrom B b) : MooreReplacement p :=
  MooreReplacement.mk x.val.point (x.val.path.trans δ.toMoorePath (by simp))
    (by rw [MoorePath.source_trans, source_path])

@[simp]
theorem point_appendFrom (x : Fiber p b) (δ : MoorePathFrom B b) :
    (x.appendFrom δ).point = x.val.point :=
  point_mk _ _ _

@[simp]
theorem path_appendFrom (x : Fiber p b) (δ : MoorePathFrom B b) :
    (x.appendFrom δ).path = x.val.path.trans δ.toMoorePath (by simp) :=
  path_mk _ _ _

/-- The point `(e, γ ⋆ δ)` lies over the end point of `δ`. -/
theorem endpoint_appendFrom (x : Fiber p b) (δ : MoorePathFrom B b) :
    endpoint p (x.appendFrom δ) = δ.toMoorePath.target := by
  simp

/-- **Appending a path from `b` is balanced over the loops at `b`**: acting by a loop `ω` on
`(e, γ)` and then appending `δ` is appending `ω ⋆ δ`. -/
theorem act_appendFrom (x : Fiber p b) (ω : MooreLoopSpace B b) (δ : MoorePathFrom B b) :
    (x.act ω).appendFrom δ = x.appendFrom (ω • δ) :=
  MooreReplacement.ext (by simp) (by simp [MoorePath.trans_assoc])

/-- Appending a path from `b` is jointly continuous. -/
theorem continuous_appendFrom :
    Continuous fun q : Fiber p b × MoorePathFrom B b ↦ q.1.appendFrom q.2 :=
  continuous_mk (continuous_point.comp (continuous_val.comp continuous_fst))
    ((continuous_path.comp (continuous_val.comp continuous_fst)).moorePath_trans
      (MoorePathFrom.continuous_toMoorePath.comp continuous_snd) _) _

variable (p b) in
/-- Appending a path from `b`, as a continuous map `F'_b × P_b B → E'`. -/
def appendFromMap : C(Fiber p b × MoorePathFrom B b, MooreReplacement p) :=
  ⟨fun q ↦ q.1.appendFrom q.2, continuous_appendFrom⟩

@[simp]
theorem appendFromMap_apply (q : Fiber p b × MoorePathFrom B b) :
    appendFromMap p b q = q.1.appendFrom q.2 :=
  (rfl)

end TauCeti.MooreReplacement.Fiber
