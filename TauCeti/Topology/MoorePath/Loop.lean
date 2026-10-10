/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MoorePath.Concat
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Moore loops

The **Moore loops** at a point `b` are the Moore paths from `b` to `b`.  Concatenation makes them a
monoid, strictly associative with the constant loop of duration `0` as unit, and multiplication is
continuous: `MooreLoop X b` is a topological monoid.  The duration is a monoid homomorphism to
`ℝ≥0`; when `X` is a point it is a homeomorphism `MooreLoop X b ≃ₜ ℝ≥0`, which is why the Moore
loop space is not homeomorphic to the fixed-interval loop space `Map_*(S¹, X)`.

The **free Moore loops** are the Moore paths whose two end points agree, with the evaluation at
the base point `FreeLoop X → X`.  The constant loops of duration `0` form a closed embedding
`X → FreeLoop X`, the section of the evaluation.

## Main definitions

* `TauCeti.MooreLoop X b`: the Moore loops at `b`, a topological monoid.
* `TauCeti.MooreLoop.lengthHom`: the duration, as a monoid homomorphism to `Multiplicative ℝ≥0`,
  and its section `TauCeti.MooreLoop.constOfLengthHom` by the constant loops.
* `TauCeti.MooreLoop.lengthHomeomorph`: `MooreLoop X b ≃ₜ ℝ≥0` when `X` is a subsingleton.
* `TauCeti.FreeLoop X`: the free Moore loops, with `basepoint`, `length` and the constant loops
  `const`.

## Main results

* `TauCeti.MooreLoop.instMonoid`, `TauCeti.MooreLoop.instContinuousMul`.
* `TauCeti.FreeLoop.isClosedEmbedding_const`: the constant loops are a closed embedding.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public section

noncomputable section

open NNReal Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- The **Moore loops** at `b`: the Moore paths from `b` to `b`. -/
abbrev MooreLoop (X : Type*) [TopologicalSpace X] (b : X) : Type _ :=
  {γ : MoorePath X // γ.source = b ∧ γ.target = b}

namespace MooreLoop

variable {b : X}

/-- The underlying Moore path of a loop. -/
abbrev toMoorePath (γ : MooreLoop X b) : MoorePath X := γ.1

@[simp]
theorem source_toMoorePath (γ : MooreLoop X b) : γ.toMoorePath.source = b :=
  γ.2.1

@[simp]
theorem target_toMoorePath (γ : MooreLoop X b) : γ.toMoorePath.target = b :=
  γ.2.2

theorem toMoorePath_injective : Function.Injective (toMoorePath : MooreLoop X b → MoorePath X) :=
  Subtype.val_injective

@[ext]
theorem ext {γ δ : MooreLoop X b} (h : γ.toMoorePath = δ.toMoorePath) : γ = δ :=
  toMoorePath_injective h

theorem isEmbedding_toMoorePath : IsEmbedding (toMoorePath : MooreLoop X b → MoorePath X) :=
  IsEmbedding.subtypeVal

theorem continuous_toMoorePath : Continuous (toMoorePath : MooreLoop X b → MoorePath X) :=
  continuous_subtype_val

/-- The duration of a loop. -/
def length (γ : MooreLoop X b) : ℝ≥0 := γ.toMoorePath.length

@[simp]
theorem length_toMoorePath (γ : MooreLoop X b) : γ.toMoorePath.length = γ.length :=
  (rfl)

theorem continuous_length : Continuous (length : MooreLoop X b → ℝ≥0) :=
  MoorePath.continuous_length.comp continuous_toMoorePath

instance : One (MooreLoop X b) := ⟨⟨MoorePath.const b, by simp, by simp⟩⟩

instance : Mul (MooreLoop X b) :=
  ⟨fun γ δ ↦ ⟨γ.toMoorePath.trans δ.toMoorePath (by simp), by simp, by simp⟩⟩

@[simp]
theorem toMoorePath_one : (1 : MooreLoop X b).toMoorePath = MoorePath.const b :=
  (rfl)

@[simp]
theorem toMoorePath_mul (γ δ : MooreLoop X b) :
    (γ * δ).toMoorePath = γ.toMoorePath.trans δ.toMoorePath (by simp) :=
  (rfl)

/-- Moore loops form a monoid under concatenation: strictly associative, with the constant loop as
unit. -/
instance instMonoid : Monoid (MooreLoop X b) where
  mul_assoc γ δ ε := ext (by
    simp only [toMoorePath_mul]
    exact MoorePath.trans_assoc _ _)
  one_mul γ := ext (by
    simp only [toMoorePath_mul, toMoorePath_one]
    exact MoorePath.const_trans _)
  mul_one γ := ext (by
    simp only [toMoorePath_mul, toMoorePath_one]
    exact MoorePath.trans_const _)

@[simp]
theorem length_one : (1 : MooreLoop X b).length = 0 := by
  rw [← length_toMoorePath, toMoorePath_one, MoorePath.length_const]

@[simp]
theorem length_mul (γ δ : MooreLoop X b) : (γ * δ).length = γ.length + δ.length := by
  rw [← length_toMoorePath, toMoorePath_mul, MoorePath.length_trans, length_toMoorePath,
    length_toMoorePath]

/-- The duration, as a monoid homomorphism to `ℝ≥0` written multiplicatively. -/
def lengthHom : MooreLoop X b →* Multiplicative ℝ≥0 where
  toFun γ := Multiplicative.ofAdd γ.length
  map_one' := by simp
  map_mul' _ _ := by simp [ofAdd_add]

@[simp]
theorem lengthHom_apply (γ : MooreLoop X b) : lengthHom γ = Multiplicative.ofAdd γ.length :=
  (rfl)

/-- Concatenation of loops is continuous: `MooreLoop X b` is a topological monoid. -/
instance instContinuousMul : ContinuousMul (MooreLoop X b) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact MoorePath.continuous_trans.comp
      (((continuous_toMoorePath.comp continuous_fst).prodMk
        (continuous_toMoorePath.comp continuous_snd)).subtype_mk fun _ ↦ by simp)

/-- The constant loop at `b` of duration `L`. -/
def constOfLength (L : ℝ≥0) : MooreLoop X b := ⟨MoorePath.constOfLength b L, by simp, by simp⟩

@[simp]
theorem toMoorePath_constOfLength (L : ℝ≥0) :
    (constOfLength L : MooreLoop X b).toMoorePath = MoorePath.constOfLength b L :=
  (rfl)

@[simp]
theorem length_constOfLength (L : ℝ≥0) : (constOfLength L : MooreLoop X b).length = L :=
  MoorePath.length_constOfLength b L

theorem continuous_constOfLength : Continuous (constOfLength : ℝ≥0 → MooreLoop X b) :=
  (MoorePath.continuous_constOfLength.comp
    (Continuous.prodMk continuous_const continuous_id)).subtype_mk _

@[simp]
theorem constOfLength_zero : (constOfLength 0 : MooreLoop X b) = 1 :=
  ext (MoorePath.constOfLength_zero b)

/-- The constant loops form a one-parameter family of monoid elements: durations add. -/
theorem constOfLength_add (L L' : ℝ≥0) :
    (constOfLength (L + L') : MooreLoop X b) = constOfLength L * constOfLength L' :=
  ext (by
    simp only [toMoorePath_mul, toMoorePath_constOfLength]
    exact (MoorePath.constOfLength_trans_constOfLength b L L' _).symm)

/-- The constant loops, as a monoid homomorphism from `ℝ≥0` written multiplicatively; it is a
section of `lengthHom`. -/
def constOfLengthHom : Multiplicative ℝ≥0 →* MooreLoop X b where
  toFun L := constOfLength (Multiplicative.toAdd L)
  map_one' := by simp
  map_mul' _ _ := by simp [constOfLength_add]

@[simp]
theorem constOfLengthHom_apply (L : Multiplicative ℝ≥0) :
    (constOfLengthHom L : MooreLoop X b) = constOfLength (Multiplicative.toAdd L) :=
  (rfl)

theorem lengthHom_comp_constOfLengthHom :
    (lengthHom : MooreLoop X b →* Multiplicative ℝ≥0).comp constOfLengthHom = MonoidHom.id _ :=
  MonoidHom.ext fun _ ↦ by simp

/-- When `X` is a point, the duration is a homeomorphism `MooreLoop X b ≃ₜ ℝ≥0`: the Moore loop
space of a point is `[0, ∞)`, not a point. -/
def lengthHomeomorph [Subsingleton X] : MooreLoop X b ≃ₜ ℝ≥0 where
  toFun := length
  invFun := constOfLength
  left_inv γ := ext (MoorePath.ext (by simp) fun _ _ ↦ Subsingleton.elim _ _)
  right_inv L := length_constOfLength L
  continuous_toFun := continuous_length
  continuous_invFun := continuous_constOfLength

@[simp]
theorem lengthHomeomorph_apply [Subsingleton X] (γ : MooreLoop X b) :
    lengthHomeomorph γ = γ.length :=
  (rfl)

end MooreLoop

/-- The **free Moore loops**: the Moore paths whose end points agree. -/
abbrev FreeLoop (X : Type*) [TopologicalSpace X] : Type _ :=
  {γ : MoorePath X // γ.source = γ.target}

namespace FreeLoop

/-- The underlying Moore path of a free loop. -/
abbrev toMoorePath (γ : FreeLoop X) : MoorePath X := γ.1

theorem source_eq_target (γ : FreeLoop X) : γ.toMoorePath.source = γ.toMoorePath.target :=
  γ.2

theorem toMoorePath_injective : Function.Injective (toMoorePath : FreeLoop X → MoorePath X) :=
  Subtype.val_injective

@[ext]
theorem ext {γ δ : FreeLoop X} (h : γ.toMoorePath = δ.toMoorePath) : γ = δ :=
  toMoorePath_injective h

theorem isEmbedding_toMoorePath : IsEmbedding (toMoorePath : FreeLoop X → MoorePath X) :=
  IsEmbedding.subtypeVal

theorem continuous_toMoorePath : Continuous (toMoorePath : FreeLoop X → MoorePath X) :=
  continuous_subtype_val

/-- The duration of a free loop. -/
def length (γ : FreeLoop X) : ℝ≥0 := γ.toMoorePath.length

@[simp]
theorem length_toMoorePath (γ : FreeLoop X) : γ.toMoorePath.length = γ.length :=
  (rfl)

theorem continuous_length : Continuous (length : FreeLoop X → ℝ≥0) :=
  MoorePath.continuous_length.comp continuous_toMoorePath

/-- The base point of a free loop: its common starting and end point. -/
def basepoint (γ : FreeLoop X) : X := γ.toMoorePath.source

@[simp]
theorem source_toMoorePath (γ : FreeLoop X) : γ.toMoorePath.source = γ.basepoint :=
  (rfl)

@[simp]
theorem target_toMoorePath (γ : FreeLoop X) : γ.toMoorePath.target = γ.basepoint :=
  γ.2.symm

theorem continuous_basepoint : Continuous (basepoint : FreeLoop X → X) :=
  MoorePath.continuous_source.comp continuous_toMoorePath

/-- The constant loop at `x`, of duration `0`. -/
def const (x : X) : FreeLoop X := ⟨MoorePath.const x, by simp⟩

@[simp]
theorem toMoorePath_const (x : X) : (const x).toMoorePath = MoorePath.const x :=
  (rfl)

@[simp]
theorem length_const (x : X) : (const x).length = 0 :=
  MoorePath.length_const x

@[simp]
theorem basepoint_const (x : X) : (const x).basepoint = x :=
  MoorePath.source_const x

theorem continuous_const : Continuous (const : X → FreeLoop X) :=
  MoorePath.continuous_const.subtype_mk _

/-- The constant loops are the loops of duration `0`. -/
theorem range_const : Set.range (const : X → FreeLoop X) = {γ | γ.length = 0} := by
  ext γ
  constructor
  · rintro ⟨x, rfl⟩
    exact MoorePath.length_const x
  · intro h
    exact ⟨γ.basepoint, ext (MoorePath.eq_const_of_length_eq_zero h).symm⟩

/-- The constant loops form a closed embedding `X → FreeLoop X`, the section of `basepoint`. -/
theorem isClosedEmbedding_const : IsClosedEmbedding (const : X → FreeLoop X) where
  toIsEmbedding := IsEmbedding.of_leftInverse (f := basepoint) basepoint_const continuous_basepoint
    continuous_const
  isClosed_range := by
    rw [range_const]
    exact isClosed_eq continuous_length _root_.continuous_const

end FreeLoop

end TauCeti

end
