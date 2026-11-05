/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Between.Equiv

/-!
# Left-equivariant concatenation equivalences of Moore path spaces

Appending a chosen path from `b` to `c` identifies paths from `a` to `b` with paths from
`a` to `c` up to homotopy. Both maps and both inverse homotopies commute strictly with the
left action of Moore loops at `a`. In particular, paths from `a` to `b` are left-equivariantly
homotopy equivalent to loops at `a`.

This is the left-module counterpart of the prepending equivalence. The left variance matters
for free resolutions over loop chains: the free left loop module maps to path chains by
appending a chosen path. The cancellation homotopy grows a retracing suffix, not a prefix;
a reversed path is only an inverse up to homotopy, not under strict Moore concatenation.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open scoped NNReal
open unitInterval ContinuousMap

namespace TauCeti.MoorePathBetween

variable {X : Type*} [TopologicalSpace X] {a b c : X}

/-- Append a chosen Moore path, leaving the initial endpoint unchanged. -/
def append (γ : MoorePathBetween X b c) (a : X) :
    C(MoorePathBetween X a b, MoorePathBetween X a c) :=
  ⟨fun δ ↦ δ.trans γ, continuous_trans.comp (continuous_id.prodMk continuous_const)⟩

@[simp]
theorem append_apply (γ : MoorePathBetween X b c) (δ : MoorePathBetween X a b) :
    append γ a δ = δ.trans γ := (rfl)

/-- Appending commutes strictly with the left loop action. -/
theorem append_smul (γ : MoorePathBetween X b c) (δ : MoorePathBetween X a b)
    (ω : MooreLoopSpace X a) :
    append γ a (ω • δ) = ω • append γ a δ :=
  ext (by simp [MoorePath.trans_assoc])

/-- Grow a retracing suffix from the unit to the reversed path followed by the path. -/
def appendSymmHomotopy (γ : MoorePathBetween X b c) (a : X) :
    ContinuousMap.Homotopy (.id (MoorePathBetween X a c))
      ((append γ a).comp (append γ.symm a)) where
  toFun p := rightAct p.2 (γ.symm.retrace (toNNReal p.1 * γ.toMoorePath.length))
  continuous_toFun := continuous_rightAct.comp
    (continuous_snd.prodMk (continuous_retrace.comp (continuous_const.prodMk
      ((toNNReal_continuous.comp continuous_fst).mul continuous_const))))
  map_zero_left δ := by simp
  map_one_left δ := by
    have hfull : γ.toMoorePath.symm.truncate γ.toMoorePath.length = γ.toMoorePath.symm := by
      simpa only [MoorePath.length_symm] using γ.toMoorePath.symm.truncate_length
    apply ext
    simp [hfull, MoorePath.trans_assoc]

/-- At intermediate times the inverse homotopy appends the truncated retracing loop. -/
@[simp]
theorem appendSymmHomotopy_apply (γ : MoorePathBetween X b c) (s : I)
    (δ : MoorePathBetween X a c) :
    appendSymmHomotopy γ a (s, δ) =
      rightAct δ (γ.symm.retrace (toNNReal s * γ.toMoorePath.length)) := (rfl)

/-- Every map in the inverse homotopy is left-loop-equivariant. -/
theorem appendSymmHomotopy_smul (γ : MoorePathBetween X b c) (s : I)
    (δ : MoorePathBetween X a c) (ω : MooreLoopSpace X a) :
    appendSymmHomotopy γ a (s, ω • δ) = ω • appendSymmHomotopy γ a (s, δ) := by
  simp only [appendSymmHomotopy_apply, smul_eq_leftAct]
  exact (leftAct_rightAct _ _ _).symm

/-- Appending a path is a homotopy equivalence, with inverse appending its reversal.
The inverse homotopies are left-loop-equivariant. -/
def appendHomotopyEquiv (γ : MoorePathBetween X b c) (a : X) :
    MoorePathBetween X a b ≃ₕ MoorePathBetween X a c where
  toFun := append γ a
  invFun := append γ.symm a
  left_inv := ⟨by simpa only [symm_symm] using (appendSymmHomotopy γ.symm a).symm⟩
  right_inv := ⟨(appendSymmHomotopy γ a).symm⟩

@[simp]
theorem appendHomotopyEquiv_apply (γ : MoorePathBetween X b c)
    (δ : MoorePathBetween X a b) : appendHomotopyEquiv γ a δ = δ.trans γ := (rfl)

@[simp]
theorem appendHomotopyEquiv_symm_apply (γ : MoorePathBetween X b c)
    (δ : MoorePathBetween X a c) : (appendHomotopyEquiv γ a).symm δ = δ.trans γ.symm := (rfl)

/-- Appending a chosen path identifies loops at its source with paths between its endpoints,
up to left-loop-equivariant homotopy. -/
def loopAppendHomotopyEquiv (γ : MoorePathBetween X a b) :
    MooreLoopSpace X a ≃ₕ MoorePathBetween X a b :=
  (loopHomeomorph a).toHomotopyEquiv.trans (appendHomotopyEquiv γ a)

@[simp]
theorem loopAppendHomotopyEquiv_apply (γ : MoorePathBetween X a b) (ω : MooreLoopSpace X a) :
    loopAppendHomotopyEquiv γ ω = leftAct ω γ := by
  apply ext
  simp [loopAppendHomotopyEquiv, HomotopyEquiv.trans_apply,
    Homeomorph.coe_toHomotopyEquiv]

/-- The inverse appends the reversed chosen path and regards the result as a loop. -/
@[simp]
theorem toMoorePath_loopAppendHomotopyEquiv_symm (γ : MoorePathBetween X a b)
    (δ : MoorePathBetween X a b) :
    ((loopAppendHomotopyEquiv γ).symm δ).toMoorePath =
      δ.toMoorePath.trans γ.toMoorePath.symm (by simp) := by
  simp [loopAppendHomotopyEquiv, HomotopyEquiv.trans_symm_apply,
    ← Homeomorph.symm_toHomotopyEquiv, Homeomorph.coe_toHomotopyEquiv]

/-- The loop-to-path equivalence commutes strictly with left multiplication by loops. -/
theorem loopAppendHomotopyEquiv_mul (γ : MoorePathBetween X a b)
    (ω η : MooreLoopSpace X a) :
    loopAppendHomotopyEquiv γ (ω * η) = ω • loopAppendHomotopyEquiv γ η := by
  simp [leftAct_mul]

/-- The inverse loop-to-path equivalence also commutes strictly with the left action. -/
theorem loopAppendHomotopyEquiv_symm_smul (γ : MoorePathBetween X a b)
    (ω : MooreLoopSpace X a) (δ : MoorePathBetween X a b) :
    (loopAppendHomotopyEquiv γ).symm (ω • δ) =
      ω * (loopAppendHomotopyEquiv γ).symm δ := by
  apply MooreLoopSpace.ext
  simp [MoorePath.trans_assoc]

end TauCeti.MoorePathBetween
