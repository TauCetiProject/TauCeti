/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore

/-!
# Moore paths between two points

Moore paths from `a` to `b` form a space with a left action of the Moore loops at `a` and a
right action of the Moore loops at `b`, both given by concatenation. The actions are continuous,
strictly associative and unital, and commute. This topological bimodule is the input for the
chain bimodule that transports DG local systems between basepoints.

The right action is represented by an action of the opposite monoid, following the convention for
right DG modules. A Moore path retains its duration, including when its underlying map is constant.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open MulOpposite

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (a b : X)

/-- The space of Moore paths from `a` to `b`, with the subspace topology of all Moore paths. -/
abbrev MoorePathBetween (X : Type*) [TopologicalSpace X] (a b : X) :=
  {γ : MoorePath X // γ.source = a ∧ γ.target = b}

namespace MoorePathBetween

variable {a b}

/-- The underlying Moore path. -/
def toMoorePath (γ : MoorePathBetween X a b) : MoorePath X := γ.val

@[ext]
theorem ext {γ δ : MoorePathBetween X a b} (h : γ.toMoorePath = δ.toMoorePath) : γ = δ :=
  Subtype.ext h

@[simp]
theorem source (γ : MoorePathBetween X a b) : γ.toMoorePath.source = a := γ.property.1

@[simp]
theorem target (γ : MoorePathBetween X a b) : γ.toMoorePath.target = b := γ.property.2

@[fun_prop]
theorem continuous_toMoorePath :
    Continuous (toMoorePath : MoorePathBetween X a b → MoorePath X) :=
  continuous_subtype_val

/-- Concatenate a loop at `a` in front of a path from `a` to `b`. -/
def leftAct (ω : MooreLoopSpace X a) (γ : MoorePathBetween X a b) :
    MoorePathBetween X a b :=
  ⟨ω.toMoorePath.trans γ.toMoorePath (by simp), by simp⟩

/-- Concatenate a loop at `b` after a path from `a` to `b`. -/
def rightAct (γ : MoorePathBetween X a b) (ω : MooreLoopSpace X b) :
    MoorePathBetween X a b :=
  ⟨γ.toMoorePath.trans ω.toMoorePath (by simp), by simp⟩

@[simp]
theorem toMoorePath_leftAct (ω : MooreLoopSpace X a) (γ : MoorePathBetween X a b) :
    (leftAct ω γ).toMoorePath = ω.toMoorePath.trans γ.toMoorePath (by simp) :=
  (rfl)

@[simp]
theorem toMoorePath_rightAct (γ : MoorePathBetween X a b) (ω : MooreLoopSpace X b) :
    (rightAct γ ω).toMoorePath = γ.toMoorePath.trans ω.toMoorePath (by simp) :=
  (rfl)

@[simp]
theorem leftAct_one (γ : MoorePathBetween X a b) : leftAct 1 γ = γ :=
  ext (by simp)

@[simp]
theorem rightAct_one (γ : MoorePathBetween X a b) : rightAct γ 1 = γ :=
  ext (by simp)

@[simp]
theorem leftAct_mul (ω ω' : MooreLoopSpace X a) (γ : MoorePathBetween X a b) :
    leftAct (ω * ω') γ = leftAct ω (leftAct ω' γ) :=
  ext (by simp [MoorePath.trans_assoc])

@[simp]
theorem rightAct_mul (γ : MoorePathBetween X a b) (ω ω' : MooreLoopSpace X b) :
    rightAct γ (ω * ω') = rightAct (rightAct γ ω) ω' :=
  ext (by simp [MoorePath.trans_assoc])

/-- Concatenating at the source commutes with concatenating at the target. -/
theorem leftAct_rightAct (ω : MooreLoopSpace X a) (γ : MoorePathBetween X a b)
    (η : MooreLoopSpace X b) :
    leftAct ω (rightAct γ η) = rightAct (leftAct ω γ) η :=
  ext (by simp [MoorePath.trans_assoc])

/-- The left loop action is jointly continuous. -/
theorem continuous_leftAct :
    Continuous fun p : MooreLoopSpace X a × MoorePathBetween X a b ↦ leftAct p.1 p.2 :=
  ((MooreLoopSpace.continuous_toMoorePath.comp continuous_fst).moorePath_trans
    (continuous_toMoorePath.comp continuous_snd) _).subtype_mk _

/-- The right loop action is jointly continuous. -/
theorem continuous_rightAct :
    Continuous fun p : MoorePathBetween X a b × MooreLoopSpace X b ↦ rightAct p.1 p.2 :=
  ((continuous_toMoorePath.comp continuous_fst).moorePath_trans
    (MooreLoopSpace.continuous_toMoorePath.comp continuous_snd) _).subtype_mk _

/-- The action of loops at the starting point. -/
instance : MulAction (MooreLoopSpace X a) (MoorePathBetween X a b) where
  smul := leftAct
  one_smul := leftAct_one
  mul_smul := leftAct_mul

/-- The right action of loops at the ending point, viewed as an action of the opposite monoid. -/
instance : MulAction (MooreLoopSpace X b)ᵐᵒᵖ (MoorePathBetween X a b) where
  smul ω γ := rightAct γ ω.unop
  one_smul := rightAct_one
  mul_smul ω ω' γ := rightAct_mul γ ω'.unop ω.unop

@[simp]
theorem smul_eq_leftAct (ω : MooreLoopSpace X a) (γ : MoorePathBetween X a b) :
    ω • γ = leftAct ω γ := rfl

@[simp]
theorem op_smul_eq_rightAct (γ : MoorePathBetween X a b) (ω : MooreLoopSpace X b) :
    op ω • γ = rightAct γ ω := rfl

/-- The two loop actions commute. -/
instance : SMulCommClass (MooreLoopSpace X a) (MooreLoopSpace X b)ᵐᵒᵖ
    (MoorePathBetween X a b) where
  smul_comm ω η γ := leftAct_rightAct ω γ η.unop

instance : ContinuousSMul (MooreLoopSpace X a) (MoorePathBetween X a b) :=
  ⟨continuous_leftAct⟩

instance : ContinuousSMul (MooreLoopSpace X b)ᵐᵒᵖ (MoorePathBetween X a b) :=
  ⟨continuous_rightAct.comp (continuous_snd.prodMk (continuous_unop.comp continuous_fst))⟩

end MoorePathBetween

end TauCeti
