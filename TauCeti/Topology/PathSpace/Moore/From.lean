/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.PathSpace.Moore.Between.Basic
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
* `TauCeti.MoorePathFrom.endpoint X b`: the end point, which the left loop action preserves.
* `TauCeti.MoorePathFrom.truncateHomotopy`: the homotopy from the constant map at the constant path
  to the identity, by truncation.
* `TauCeti.MoorePathBetween.toMoorePathFrom`: a Moore path from `b` to `c` as a path from `b`. It is
  an equivariant embedding onto the paths ending at `c`, the fibre of the end point map over `c`.
* `TauCeti.MooreLoopSpace.toMoorePathFrom`: a Moore loop at `b` as a Moore path from `b`, an
  embedding (`TauCeti.MooreLoopSpace.isEmbedding_toMoorePathFrom`) which turns the product of loops
  into the left action (`TauCeti.MooreLoopSpace.toMoorePathFrom_mul`).
* `TauCeti.MoorePathFrom.loopPair X b`: the pair `(P_b X, Ω_b X)` of the based path space and the
  Moore loops, included by `TauCeti.MooreLoopSpace.toMoorePathFrom`.

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
  continuous_subtypeVal

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

/-! ### The end point -/

variable (X b) in
/-- The **end point** of a Moore path from `b`, the projection of the path fibration
`P_b X → X`. -/
def endpoint : C(MoorePathFrom X b, X) :=
  ⟨fun γ ↦ γ.toMoorePath.target, MoorePath.continuous_target.comp continuous_toMoorePath⟩

theorem endpoint_apply (γ : MoorePathFrom X b) : endpoint X b γ = γ.toMoorePath.target :=
  (rfl)

/-- Concatenating a loop in front does not move the end point. -/
@[simp]
theorem endpoint_leftAct (ω : MooreLoopSpace X b) (γ : MoorePathFrom X b) :
    endpoint X b (leftAct ω γ) = endpoint X b γ := by
  simp [endpoint_apply]

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

/-! ### The fibres of the end point map -/

namespace MoorePathBetween

variable {X : Type*} [TopologicalSpace X] {b c : X}

variable (b c) in
/-- A Moore path from `b` to `c`, read as a Moore path from `b`: the inclusion of the fibre over `c`
of the end point map `P_b X → X`. -/
def toMoorePathFrom : C(MoorePathBetween X b c, MoorePathFrom X b) :=
  ⟨fun γ ↦ ⟨γ.toMoorePath, γ.source⟩, continuous_toMoorePath.subtype_mk _⟩

@[simp]
theorem toMoorePath_toMoorePathFrom (γ : MoorePathBetween X b c) :
    (toMoorePathFrom b c γ).toMoorePath = γ.toMoorePath :=
  (rfl)

/-- A Moore path from `b` to `c` ends at `c`. -/
@[simp]
theorem endpoint_toMoorePathFrom (γ : MoorePathBetween X b c) :
    MoorePathFrom.endpoint X b (toMoorePathFrom b c γ) = c :=
  γ.target

/-- The inclusion commutes with the concatenation of loops at `b` in front. -/
theorem toMoorePathFrom_smul (ω : MooreLoopSpace X b) (γ : MoorePathBetween X b c) :
    toMoorePathFrom b c (ω • γ) = ω • toMoorePathFrom b c γ :=
  MoorePathFrom.ext (by simp)

/-- The inclusion commutes with the concatenation of loops at `b` in front, in the form of the
`leftAct` functions. -/
@[simp]
theorem toMoorePathFrom_leftAct (ω : MooreLoopSpace X b) (γ : MoorePathBetween X b c) :
    toMoorePathFrom b c (leftAct ω γ) = MoorePathFrom.leftAct ω (toMoorePathFrom b c γ) :=
  MoorePathFrom.ext (by simp)

/-- The paths from `b` to `c` are the paths from `b` ending at `c`. -/
theorem range_toMoorePathFrom :
    Set.range (toMoorePathFrom b c) = MoorePathFrom.endpoint X b ⁻¹' {c} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun γ ↦ endpoint_toMoorePathFrom γ)
    fun γ hγ ↦ ⟨⟨γ.toMoorePath, γ.source, hγ⟩, MoorePathFrom.ext (by simp)⟩

/-- The paths from `b` to `c` carry the topology induced from the paths from `b`. -/
theorem isEmbedding_toMoorePathFrom : Topology.IsEmbedding (toMoorePathFrom b c) := by
  -- Both are subspaces of the Moore paths, and the inclusion commutes with the two inclusions.
  have h : (Subtype.val ∘ toMoorePathFrom b c : MoorePathBetween X b c → MoorePath X) =
      Subtype.val :=
    funext fun ⟨γ, hγ⟩ ↦ toMoorePath_mk γ hγ
  exact (Topology.IsEmbedding.subtypeVal.of_comp_iff).1 (h ▸ Topology.IsEmbedding.subtypeVal)

end MoorePathBetween

/-! ### Loops as paths -/

namespace MooreLoopSpace

variable {X : Type*} [TopologicalSpace X] {b : X}

/-- A Moore loop at `b`, read as a Moore path starting at `b`. -/
def toMoorePathFrom : C(MooreLoopSpace X b, MoorePathFrom X b) :=
  ⟨fun ω ↦ ⟨ω.toMoorePath, ω.source_eq⟩, continuous_toMoorePath.subtype_mk _⟩

@[simp]
theorem toMoorePath_toMoorePathFrom (ω : MooreLoopSpace X b) :
    (toMoorePathFrom ω).toMoorePath = ω.toMoorePath :=
  MoorePathFrom.toMoorePath_mk _ _

/-- A loop read as a path ends at the base point. -/
@[simp]
theorem endpoint_toMoorePathFrom (ω : MooreLoopSpace X b) :
    MoorePathFrom.endpoint X b (toMoorePathFrom ω) = b := by
  rw [MoorePathFrom.endpoint_apply, toMoorePath_toMoorePathFrom, ω.target_eq]

/-- The loops at `b`, read as paths, are the paths from `b` ending at `b`. -/
theorem range_toMoorePathFrom :
    Set.range (toMoorePathFrom : MooreLoopSpace X b → MoorePathFrom X b) =
      MoorePathFrom.endpoint X b ⁻¹' {b} := by
  ext γ
  refine ⟨?_, fun hγ ↦ ⟨⟨γ.toMoorePath, γ.source, hγ⟩, MoorePathFrom.ext ?_⟩⟩
  · rintro ⟨ω, rfl⟩
    exact endpoint_toMoorePathFrom ω
  · exact toMoorePath_toMoorePathFrom _

/-- Reading loops as paths is an embedding. -/
theorem isEmbedding_toMoorePathFrom :
    Topology.IsEmbedding (toMoorePathFrom : MooreLoopSpace X b → MoorePathFrom X b) :=
  Topology.IsEmbedding.of_comp toMoorePathFrom.continuous MoorePathFrom.continuous_toMoorePath
    (by convert isEmbedding_toMoorePath (X := X) (x := b) using 1
        funext ω
        exact toMoorePath_toMoorePathFrom ω)

/-- Reading loops as paths turns the product of loops into the left action of loops on paths. -/
@[simp]
theorem toMoorePathFrom_mul (ω ω' : MooreLoopSpace X b) :
    toMoorePathFrom (ω * ω') = ω • toMoorePathFrom ω' :=
  MoorePathFrom.ext (by simp [toMoorePath_mul])

/-- Reading loops as paths is the orbit map `ω ↦ ω • refl X b` of the constant path. -/
theorem toMoorePathFrom_eq_smul_refl (ω : MooreLoopSpace X b) :
    toMoorePathFrom ω = ω • MoorePathFrom.refl X b :=
  MoorePathFrom.ext (by simp)

end MooreLoopSpace

namespace MoorePathFrom

variable (X : Type*) [TopologicalSpace X] (b : X)

/-- The pair `(P_b X, Ω_b X)` of the Moore paths from `b` and the Moore loops at `b`, the loops
included as the paths ending at `b` (`TauCeti.MooreLoopSpace.toMoorePathFrom`). -/
abbrev loopPair : TopPair :=
  TopPair.of (TopCat.ofHom (MooreLoopSpace.toMoorePathFrom (X := X) (b := b)))
    MooreLoopSpace.isEmbedding_toMoorePathFrom

end MoorePathFrom

end TauCeti
