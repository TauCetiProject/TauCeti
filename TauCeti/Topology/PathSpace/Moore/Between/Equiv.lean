/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Between.Basic
public import TauCeti.Topology.PathSpace.Moore.Truncate
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Concatenation equivalences of Moore path spaces

Prepending a chosen Moore path from `a` to `b` gives a homotopy equivalence from the paths
from `b` to `c` to the paths from `a` to `c`. Its inverse prepends the reversed path.
The inverse homotopies shrink a path followed by its reversal by truncating the outward leg.
Both concatenation maps and the inverse homotopies commute strictly with the right action of
loops at `c`.

In particular, the space of paths from `a` to `b` is right-equivariantly homotopy equivalent
to the Moore loops at `b`, after choosing a path from `a` to `b`. This is the topological input
for the chain bimodules used to change basepoints in DG local systems. No concatenation with
a reversed path is asserted to equal a constant path: its duration is generally nonzero.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open scoped NNReal
open unitInterval MulOpposite ContinuousMap

namespace TauCeti
namespace MoorePathBetween

variable {X : Type*} [TopologicalSpace X] {a b c : X}

/-- Prepend a chosen Moore path. -/
def prepend (γ : MoorePathBetween X a b) (c : X) :
    C(MoorePathBetween X b c, MoorePathBetween X a c) :=
  ⟨γ.trans, continuous_trans.comp (continuous_const.prodMk continuous_id)⟩

@[simp]
theorem prepend_apply (γ : MoorePathBetween X a b) (δ : MoorePathBetween X b c) :
    prepend γ c δ = γ.trans δ := (rfl)

/-- Prepending commutes strictly with the right action at the final endpoint. -/
theorem prepend_op_smul (γ : MoorePathBetween X a b) (δ : MoorePathBetween X b c)
    (ω : MooreLoopSpace X c) :
    prepend γ c (op ω • δ) = op ω • prepend γ c δ :=
  ext (by simp [MoorePath.trans_assoc])

/-- A retracing loop, obtained by truncating the outward leg before returning along it. -/
def retrace (γ : MoorePathBetween X a b) (s : ℝ≥0) : MooreLoopSpace X a where
  toMoorePath := (γ.toMoorePath.truncate s).trans (γ.toMoorePath.truncate s).symm (by simp)
  source_eq := by simp
  target_eq := by simp

/-- The underlying path of the retracing loop. -/
@[simp]
theorem toMoorePath_retrace (γ : MoorePathBetween X a b) (s : ℝ≥0) :
    (γ.retrace s).toMoorePath =
      (γ.toMoorePath.truncate s).trans (γ.toMoorePath.truncate s).symm (by simp) := (rfl)

@[simp]
theorem retrace_zero (γ : MoorePathBetween X a b) : γ.retrace 0 = 1 :=
  MooreLoopSpace.ext (by simp)

/-- Retracing is jointly continuous in the path and the truncation time. -/
@[fun_prop]
theorem continuous_retrace :
    Continuous fun p : MoorePathBetween X a b × ℝ≥0 ↦ p.1.retrace p.2 := by
  apply MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2
  have h := (continuous_toMoorePath (a := a) (b := b)).comp
    (continuous_fst : Continuous (Prod.fst : MoorePathBetween X a b × ℝ≥0 → _))
  have h' := h.moorePath_truncate continuous_snd
  exact h'.moorePath_trans h'.moorePath_symm _

/-- Grow a retracing prefix from duration zero to the full path and its reversal. -/
def prependSymmHomotopy (γ : MoorePathBetween X a b) (c : X) :
    ContinuousMap.Homotopy (.id (MoorePathBetween X a c))
      ((prepend γ c).comp (prepend γ.symm c)) where
  toFun p := leftAct (γ.retrace (toNNReal p.1 * γ.toMoorePath.length)) p.2
  continuous_toFun := continuous_leftAct.comp
    ((continuous_retrace.comp (continuous_const.prodMk
      ((toNNReal_continuous.comp continuous_fst).mul continuous_const))).prodMk continuous_snd)
  map_zero_left δ := by simp
  map_one_left δ := by
    apply ext
    simp [MoorePath.trans_assoc]

/-- The inverse homotopy is given by a retracing prefix acting on the path. -/
@[simp]
theorem prependSymmHomotopy_apply (γ : MoorePathBetween X a b) (s : I)
    (δ : MoorePathBetween X a c) :
    prependSymmHomotopy γ c (s, δ) =
      leftAct (γ.retrace (toNNReal s * γ.toMoorePath.length)) δ := (rfl)

/-- Every intermediate map of the inverse homotopy commutes with the right loop action. -/
theorem prependSymmHomotopy_op_smul (γ : MoorePathBetween X a b) (s : I)
    (δ : MoorePathBetween X a c) (ω : MooreLoopSpace X c) :
    prependSymmHomotopy γ c (s, op ω • δ) =
      op ω • prependSymmHomotopy γ c (s, δ) := by
  simp only [prependSymmHomotopy_apply, op_smul_eq_rightAct]
  exact leftAct_rightAct _ _ _

/-- Prepending a path is a homotopy equivalence, with inverse prepending its reversal. -/
def prependHomotopyEquiv (γ : MoorePathBetween X a b) (c : X) :
    MoorePathBetween X b c ≃ₕ MoorePathBetween X a c where
  toFun := prepend γ c
  invFun := prepend γ.symm c
  left_inv := ⟨by simpa only [symm_symm] using (prependSymmHomotopy γ.symm c).symm⟩
  right_inv := ⟨(prependSymmHomotopy γ c).symm⟩

@[simp]
theorem prependHomotopyEquiv_apply (γ : MoorePathBetween X a b)
    (δ : MoorePathBetween X b c) : prependHomotopyEquiv γ c δ = γ.trans δ := (rfl)

@[simp]
theorem prependHomotopyEquiv_symm_apply (γ : MoorePathBetween X a b)
    (δ : MoorePathBetween X a c) : (prependHomotopyEquiv γ c).symm δ = γ.symm.trans δ := (rfl)

/-- Prepending a chosen path identifies loops at its target with paths between its endpoints,
up to homotopy. -/
def loopPrependHomotopyEquiv (γ : MoorePathBetween X a b) :
    MooreLoopSpace X b ≃ₕ MoorePathBetween X a b :=
  (loopHomeomorph b).toHomotopyEquiv.trans (prependHomotopyEquiv γ b)

@[simp]
theorem loopPrependHomotopyEquiv_apply (γ : MoorePathBetween X a b) (ω : MooreLoopSpace X b) :
    loopPrependHomotopyEquiv γ ω = rightAct γ ω := by
  apply ext
  simp [loopPrependHomotopyEquiv, HomotopyEquiv.trans_apply,
    Homeomorph.coe_toHomotopyEquiv]

/-- The inverse first prepends the reversed path, then regards the result as a loop. -/
@[simp]
theorem toMoorePath_loopPrependHomotopyEquiv_symm (γ : MoorePathBetween X a b)
    (δ : MoorePathBetween X a b) :
    ((loopPrependHomotopyEquiv γ).symm δ).toMoorePath =
      γ.toMoorePath.symm.trans δ.toMoorePath (by simp) := by
  simp [loopPrependHomotopyEquiv, HomotopyEquiv.trans_symm_apply,
    ← Homeomorph.symm_toHomotopyEquiv, Homeomorph.coe_toHomotopyEquiv]

/-- The loop-to-path equivalence commutes strictly with right multiplication by loops. -/
theorem loopPrependHomotopyEquiv_op_smul (γ : MoorePathBetween X a b)
    (ω η : MooreLoopSpace X b) :
    loopPrependHomotopyEquiv γ (op η • ω) = op η • loopPrependHomotopyEquiv γ ω := by
  simp [rightAct_mul]

end MoorePathBetween
end TauCeti
