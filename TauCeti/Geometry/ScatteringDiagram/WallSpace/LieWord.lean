/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Free.Grading
public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Basic
public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic

/-!
# Vanishing of tangent-degree wall Lie words

A bracketed word of wall elements has a recursively determined integral normal.
If all leaf normals annihilate a tangent vector, so does every intermediate normal. A word
with at least two leaves therefore vanishes when all leaf normals annihilate the geometric
direction of its total degree. In particular every such word of zero geometric direction
vanishes, and so does every such word whose direction lies in a real subspace annihilated by
all leaf normals.

Words are Mathlib's `FreeMagma`; their evaluation uses `TauCeti.FreeLieAlgebra.word` and
Mathlib's `FreeLieAlgebra.lift`, rather than a second evaluator. Total degrees use
`FreeMagma.lift` into the multiplicative synonym of the degree monoid.

## Main definitions and results

* `TauCeti.wallWordDegree`, `TauCeti.wallWordNormal`: the total degree and the integral normal
  of a bracketed word with prescribed leaf degrees and leaf normals.
* `TauCeti.DirectedWallSpaces.word_mem_wall`: the evaluation of a word of wall elements lies
  in the wall space of its total degree and normal.
* `TauCeti.DirectedWallSpaces.word_eq_zero_of_normal_direction_eq_zero`,
  `TauCeti.DirectedWallSpaces.word_eq_zero_of_direction_eq_zero`,
  `TauCeti.DirectedWallSpaces.word_eq_zero_of_direction_mem`: the vanishing criteria.

## Attribution

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/LieWord.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0). Original copyright and author
credit are retained. The wall-space law that drives the induction is Definition 1.2 of Leung,
Ma and Young, *Refined scattering diagrams and theta functions from asymptotic analysis of
Maurer-Cartan equations*.
-/

public section

namespace TauCeti

open Multiplicative

variable {Γ Λ R L S : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]

/-- The total degree of a bracketed word whose leaf `s` has degree `d s`. -/
def wallWordDegree (d : S → Γ) (w : FreeMagma S) : Γ :=
  toAdd (FreeMagma.lift (ofAdd ∘ d) w)

/-- A leaf has its prescribed degree. -/
@[simp]
theorem wallWordDegree_of (d : S → Γ) (s : S) : wallWordDegree d (FreeMagma.of s) = d s := (rfl)

/-- Bracketing words adds their total degrees. -/
@[simp]
theorem wallWordDegree_mul (d : S → Γ) (u v : FreeMagma S) :
    wallWordDegree d (u * v) = wallWordDegree d u + wallWordDegree d v := by
  simp [wallWordDegree]

/-- The integral normal of a homogeneous bracketed wall word. -/
def wallWordNormal (ρ : Γ →+ Λ) (d : S → Γ) (m : S → Λ →+ ℤ) : FreeMagma S → (Λ →+ ℤ)
  | .of s => m s
  | .mul u v => wallBracketNormal ρ (wallWordDegree d u) (wallWordDegree d v)
      (wallWordNormal ρ d m u) (wallWordNormal ρ d m v)

/-- A leaf retains its prescribed normal. -/
@[simp]
theorem wallWordNormal_of (ρ : Γ →+ Λ) (d : S → Γ) (m : S → Λ →+ ℤ) (s : S) :
    wallWordNormal ρ d m (FreeMagma.of s) = m s := (rfl)

/-- Bracketing words contracts their normals against each other's total degrees. -/
@[simp]
theorem wallWordNormal_mul (ρ : Γ →+ Λ) (d : S → Γ) (m : S → Λ →+ ℤ) (u v : FreeMagma S) :
    wallWordNormal ρ d m (u * v) = wallBracketNormal ρ (wallWordDegree d u) (wallWordDegree d v)
      (wallWordNormal ρ d m u) (wallWordNormal ρ d m v) := (rfl)

/-- A word normal annihilates every vector annihilated by all leaf normals. -/
theorem wallWordNormal_apply_eq_zero (ρ : Γ →+ Λ) (d : S → Γ) (m : S → Λ →+ ℤ)
    {v : Λ} (hm : ∀ s, m s v = 0) (w : FreeMagma S) : wallWordNormal ρ d m w v = 0 := by
  induction w with
  | ih1 s => exact hm s
  | ih2 u w hu hw => simp [hu, hw]

namespace DirectedWallSpaces

variable [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
  (d : S → Γ) (m : S → Λ →+ ℤ) (a : S → L)

/-- The evaluation of a homogeneous wall word belongs to the wall space with its recursively
specified degree and normal. -/
theorem word_mem_wall (ha : ∀ s, a s ∈ H.wall (d s) (m s)) (w : FreeMagma S) :
    FreeLieAlgebra.lift R a (FreeLieAlgebra.word R w) ∈
      H.wall (wallWordDegree d w) (wallWordNormal ρ d m w) := by
  induction w with
  | ih1 s => simpa using ha s
  | ih2 u v hu hv =>
    simpa only [FreeLieAlgebra.word_mul, LieHom.map_lie, wallWordNormal_mul,
      wallWordDegree_mul] using H.bracket_mem hu hv

/-- A wall Lie word with at least two leaves vanishes if every leaf normal annihilates the
geometric direction of its total degree. -/
theorem word_eq_zero_of_normal_direction_eq_zero (ha : ∀ s, a s ∈ H.wall (d s) (m s))
    (w : FreeMagma S) (hw : 2 ≤ w.length) (hm : ∀ s, m s (ρ (wallWordDegree d w)) = 0) :
    FreeLieAlgebra.lift R a (FreeLieAlgebra.word R w) = 0 := by
  cases w with
  | of s => simp [FreeMagma.length] at hw
  | mul u v =>
    have htotal (s : S) : m s (ρ (wallWordDegree d u + wallWordDegree d v)) = 0 := by
      simpa only [FreeMagma.mul_eq, wallWordDegree_mul] using hm s
    have hnormal (z : FreeMagma S) :
        wallWordNormal ρ d m z (ρ (wallWordDegree d u + wallWordDegree d v)) = 0 :=
      wallWordNormal_apply_eq_zero ρ d m htotal z
    simpa only [FreeMagma.mul_eq, FreeLieAlgebra.word_mul, LieHom.map_lie] using
      H.lie_eq_zero_of_normal_total_eq_zero (H.word_mem_wall d m a ha u)
        (H.word_mem_wall d m a ha v) (hnormal u) (hnormal v)

/-- A wall Lie word with at least two leaves and zero geometric direction vanishes. -/
theorem word_eq_zero_of_direction_eq_zero (ha : ∀ s, a s ∈ H.wall (d s) (m s))
    (w : FreeMagma S) (hw : 2 ≤ w.length) (hdegree : ρ (wallWordDegree d w) = 0) :
    FreeLieAlgebra.lift R a (FreeLieAlgebra.word R w) = 0 :=
  H.word_eq_zero_of_normal_direction_eq_zero d m a ha w hw (by simp [hdegree])

/-- A wall Lie word with at least two leaves vanishes if the image of its total geometric
direction in the real vector space `V` of an integral lattice `i : Λ → V` lies in a real
subspace `W` annihilated by the real extension of every leaf normal. -/
theorem word_eq_zero_of_direction_mem {Λ V : Type*} [AddCommGroup Λ] [AddCommGroup V]
    [Module ℝ V] {i : Λ →+ V} {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}
    (H : DirectedWallSpaces ρ ℒ) (hi : Toric.IsIntegralLattice i) (W : Submodule ℝ V)
    (d : S → Γ) (m : S → Λ →+ ℤ) (a : S → L)
    (hm : ∀ s, ∀ x ∈ W, hi.realCharacter (m s) x = 0)
    (ha : ∀ s, a s ∈ H.wall (d s) (m s)) (w : FreeMagma S) (hw : 2 ≤ w.length)
    (hdegree : i (ρ (wallWordDegree d w)) ∈ W) :
    FreeLieAlgebra.lift R a (FreeLieAlgebra.word R w) = 0 :=
  H.word_eq_zero_of_normal_direction_eq_zero d m a ha w hw fun s => by
    simpa [hi.realCharacter_apply] using hm s _ hdegree

end DirectedWallSpaces

end TauCeti
