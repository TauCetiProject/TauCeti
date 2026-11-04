/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.PathSpace.Moore.Truncate

/-!
# Moore paths from a basepoint

For a point `b` of a space `X`, the **based path space** `P_b X = MoorePathFrom X b` is the space
of Moore paths starting at `b`, with the subspace topology of all Moore paths. Its end point is
free. The Moore loops at `b` act on it from the left by concatenation in front; the action is
continuous, strictly associative and strictly unital, because Moore concatenation is.

The based path space is contractible: truncating a path `γ` at the time `t * length γ` deforms the
constant path of length zero at `b` (at `t = 0`) into `γ` (at `t = 1`), continuously in `γ` and `t`
(`TauCeti.MoorePathFrom.truncateHomotopy`). The contraction fixes the constant path, but it does not
commute with the loop action: truncating `ω · γ` early truncates inside the loop `ω`.

These are the two inputs for the cubical chains of `P_b X`: a left module over the chains of the
Moore loops at `b` with the homology of a point, the module against which free resolutions over
the chains of the loop space are compared in Brown's theory of twisted tensor products.

## Main definitions

* `TauCeti.MoorePathFrom X b`: the Moore paths starting at `b`.
* `TauCeti.MoorePathFrom.refl X b`: the constant path of length zero at `b`.
* `TauCeti.MoorePathFrom.leftAct`: concatenation of a Moore loop at `b` in front of a path.
* `TauCeti.MoorePathFrom.truncateHomotopy`: the homotopy from the constant map at the constant path
  to the identity, by truncation.

## Main results

* The `MulAction` and `ContinuousSMul` instances of the Moore loops at `b` on `P_b X`.
* The `ContractibleSpace` instance on `P_b X`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
-/

public noncomputable section

open scoped unitInterval

namespace TauCeti

/-- The **based path space** `P_b X`: the Moore paths starting at `b`, with the subspace topology
of all Moore paths. -/
abbrev MoorePathFrom (X : Type*) [TopologicalSpace X] (b : X) :=
  {γ : MoorePath X // γ.source = b}

namespace MoorePathFrom

variable {X : Type*} [TopologicalSpace X] {b : X}

/-- The underlying Moore path. -/
def toMoorePath (γ : MoorePathFrom X b) : MoorePath X := γ.val

@[simp]
theorem toMoorePath_mk (γ : MoorePath X) (h : γ.source = b) :
    toMoorePath (b := b) ⟨γ, h⟩ = γ := (rfl)

@[ext]
theorem ext {γ δ : MoorePathFrom X b} (h : γ.toMoorePath = δ.toMoorePath) : γ = δ :=
  Subtype.ext h

@[simp]
theorem source (γ : MoorePathFrom X b) : γ.toMoorePath.source = b := γ.property

@[fun_prop]
theorem continuous_toMoorePath : Continuous (toMoorePath : MoorePathFrom X b → MoorePath X) :=
  continuous_subtype_val

variable (X b) in
/-- The constant path of length zero at `b`, the basepoint of `P_b X`. -/
def refl : MoorePathFrom X b :=
  ⟨MoorePath.refl b, MoorePath.source_refl b⟩

@[simp]
theorem toMoorePath_refl : (refl X b).toMoorePath = MoorePath.refl b := (rfl)

/-! ### The left action of Moore loops -/

/-- Concatenate a Moore loop at `b` in front of a Moore path starting at `b`. -/
def leftAct (ω : MooreLoopSpace X b) (γ : MoorePathFrom X b) : MoorePathFrom X b :=
  ⟨ω.toMoorePath.trans γ.toMoorePath (by simp), by simp⟩

@[simp]
theorem toMoorePath_leftAct (ω : MooreLoopSpace X b) (γ : MoorePathFrom X b) :
    (leftAct ω γ).toMoorePath = ω.toMoorePath.trans γ.toMoorePath (by simp) :=
  (rfl)

@[simp]
theorem leftAct_one (γ : MoorePathFrom X b) : leftAct 1 γ = γ :=
  ext (by simp)

@[simp]
theorem leftAct_mul (ω ω' : MooreLoopSpace X b) (γ : MoorePathFrom X b) :
    leftAct (ω * ω') γ = leftAct ω (leftAct ω' γ) :=
  ext (by simp [MoorePath.trans_assoc])

/-- The left loop action is jointly continuous. -/
theorem continuous_leftAct :
    Continuous fun p : MooreLoopSpace X b × MoorePathFrom X b ↦ leftAct p.1 p.2 :=
  ((MooreLoopSpace.continuous_toMoorePath.comp continuous_fst).moorePath_trans
    (continuous_toMoorePath.comp continuous_snd) _).subtype_mk _

/-- The action of the Moore loops at `b` on the paths from `b`, by concatenation in front. -/
instance : MulAction (MooreLoopSpace X b) (MoorePathFrom X b) where
  smul := leftAct
  one_smul := leftAct_one
  mul_smul := leftAct_mul

@[simp]
theorem smul_eq_leftAct (ω : MooreLoopSpace X b) (γ : MoorePathFrom X b) :
    ω • γ = leftAct ω γ := rfl

instance : ContinuousSMul (MooreLoopSpace X b) (MoorePathFrom X b) :=
  ⟨continuous_leftAct⟩

/-! ### The contraction -/

/-- The **contraction of the based path space** by truncation: at time `t` a path `γ` is truncated
at `t * length γ`. It is a homotopy from the constant map at the constant path of length zero to the
identity. -/
def truncateHomotopy :
    (ContinuousMap.const (MoorePathFrom X b) (refl X b)).Homotopy
      (ContinuousMap.id (MoorePathFrom X b)) where
  toFun p := ⟨p.2.toMoorePath.truncate (unitInterval.toNNReal p.1 * p.2.toMoorePath.length),
    by rw [MoorePath.source_truncate, source]⟩
  continuous_toFun := by fun_prop
  map_zero_left γ := ext (by simp)
  map_one_left γ := ext (by simp)

@[simp]
theorem toMoorePath_truncateHomotopy (t : I) (γ : MoorePathFrom X b) :
    (truncateHomotopy (t, γ)).toMoorePath =
      γ.toMoorePath.truncate (unitInterval.toNNReal t * γ.toMoorePath.length) :=
  (rfl)

/-- The contraction fixes the constant path of length zero at every time. -/
@[simp]
theorem truncateHomotopy_refl (t : I) : truncateHomotopy (t, refl X b) = refl X b :=
  ext (by simp)

/-- **The based path space is contractible.** -/
instance : ContractibleSpace (MoorePathFrom X b) :=
  (contractible_iff_id_nullhomotopic _).2 ⟨refl X b, ⟨truncateHomotopy.symm⟩⟩

end MoorePathFrom

end TauCeti
