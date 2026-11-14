/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Geometry.Convex.Cone.Pointed
public import TauCeti.Combinatorics.Hive.Lattice
public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Fin

/-!
# Hives, gauge symmetries, and dominant-weight boundaries

A normalized **hive** of size `n` with values in a preordered additive commutative monoid `R` is a
function `h : Hive.Vertex n → R` vanishing at `A = (n, 0, 0)` such that on every unit rhombus
`(a, b, c, d)` in perimeter order with obtuse corners `a, c`, `h b + h d ≤ h a + h c`.
For ordered abelian group values, equivalently every unit-rhombus slack
`h a + h c - (h b + h d)` is nonnegative, and every mixed second forward difference
`(h(p + v + w) - h(p + w)) - (h(p + v) - h(p))` along unit lattice steps
`v, w` of inner product `1` is nonpositive. Restricting to unit steps is essential: on `Δ₇` the
hive `h(x, y, z) = 49 - x²` has unit slacks `0` and `2`, yet its mixed second difference at
`(3, 4, 0)` along `(2, -3, 1)` and `(-3, -1, 4)` is `+12`.

Adding a barycentric-affine function `c₀ + x • α + y • β + z • γ` preserves every rhombus slack,
and subtracting the value at `A` normalizes any rhombus-concave function (`Hive.ofRhombusConcave`).
Normalized hives form an `AddCommMonoid` (`IntegerHive n`) and, over an ordered ring, a pointed
cone (`Hive.pointedCone`). Clockwise edge differences along `A → B → C → A` define an ambient
linear map `Hive.boundaryLinear` whose values telescope to zero (`Hive.sum_boundary`) and decrease
weakly along each side (`Hive.boundary_antitone`), making each side of an integer hive a
`TauCeti.DominantWeight`. Rotation shifts sides cyclically; reflection reverses them and applies
`TauCeti.DominantWeight.dual`.

## Main definitions

* `TauCeti.Hive n R`, `TauCeti.IntegerHive n`, `TauCeti.RealHive n`: normalized hives.
* `TauCeti.Hive.rhombusSlack`, `TauCeti.Hive.IsRhombusConcave`, `TauCeti.Hive.ofRhombusConcave`:
  unit-rhombus slacks, unnormalized concavity, and corner normalization.
* `TauCeti.Hive.barycentricLinear`, `TauCeti.Hive.affine`, `TauCeti.Hive.subtriangle`,
  `TauCeti.Hive.pointedCone`: affine gauge maps, affine hives, subtriangles, and the hive cone.
* `TauCeti.Hive.boundaryLinear`, `TauCeti.Hive.boundary`, `TauCeti.Hive.boundaryWeight`,
  `TauCeti.Hive.productBoundary`: clockwise boundary maps.
* `TauCeti.Hive.rotate`, `TauCeti.Hive.reflect`: dihedral symmetries of normalized hives.
* `TauCeti.Hive.counterexampleSeven`, `TauCeti.Hive.exampleTwo`, `TauCeti.Hive.detTwo`: explicit
  rank-`7` and rank-`2` hives.

## Main results

* `TauCeti.Hive.rhombusSlack_add_barycentricLinear`, `TauCeti.Hive.ofRhombusConcave_eq_iff`.
* `TauCeti.Hive.mixedDiff_nonpos_of_isUnitStep`,
  `TauCeti.Hive.counterexampleSeven_nonunit_mixedDiff_pos`.
* `TauCeti.Hive.sum_boundary`, `TauCeti.Hive.boundary_antitone`.
* `TauCeti.Hive.boundary_rotate`, `TauCeti.Hive.boundaryWeight_reflect`,
  `TauCeti.Hive.boundary_injective_two`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2 and
  Appendix 2, Proposition 4.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §2.
-/

public section

open scoped BigOperators

namespace TauCeti

namespace Hive

/-- A lattice function is **rhombus-concave** (an unnormalized hive) if on every unit rhombus the
sum at the obtuse corners is at least the sum at the acute corners. -/
def IsRhombusConcave {n : ℕ} {R : Type*} [Add R] [LE R] (f : Vertex n → R) : Prop :=
  ∀ ⦃a b c d : Vertex n⦄, IsRhombus a b c d → f b + f d ≤ f a + f c

theorem isRhombusConcave_def {n : ℕ} {R : Type*} [Add R] [LE R] (f : Vertex n → R) :
    IsRhombusConcave f ↔ ∀ ⦃a b c d : Vertex n⦄, IsRhombus a b c d → f b + f d ≤ f a + f c :=
  Iff.rfl

instance {n : ℕ} {R : Type*} [Add R] [LE R] [DecidableLE R] (f : Vertex n → R) :
    Decidable (IsRhombusConcave f) :=
  decidable_of_iff _ (isRhombusConcave_def f).symm

section Concavity

variable {n : ℕ} {R : Type*}

/-- Evaluate rhombus concavity on a unit rhombus. -/
theorem IsRhombusConcave.le [Add R] [LE R] {f : Vertex n → R}
    (hf : IsRhombusConcave f) {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    f b + f d ≤ f a + f c := hf hr

/-- Clockwise rotation preserves rhombus concavity. -/
theorem IsRhombusConcave.rotate [Add R] [LE R] {f : Vertex n → R}
    (hf : IsRhombusConcave f) : IsRhombusConcave (fun p => f p.rotate) :=
  fun _ _ _ _ hr => hf hr.rotate

/-- Reflection preserves rhombus concavity. -/
theorem IsRhombusConcave.reflect [Add R] [LE R] {f : Vertex n → R}
    (hf : IsRhombusConcave f) : IsRhombusConcave (fun p => f p.reflect) :=
  fun _ _ _ _ hr => hf hr.reflect

@[simp] theorem isRhombusConcave_rotate_iff [Add R] [LE R] (f : Vertex n → R) :
    IsRhombusConcave (fun p => f p.rotate) ↔ IsRhombusConcave f := by
  refine ⟨fun hf => ?_, IsRhombusConcave.rotate⟩
  simpa only [Vertex.rotate_rotate_rotate] using hf.rotate.rotate

@[simp] theorem isRhombusConcave_reflect_iff [Add R] [LE R] (f : Vertex n → R) :
    IsRhombusConcave (fun p => f p.reflect) ↔ IsRhombusConcave f := by
  refine ⟨fun hf => ?_, IsRhombusConcave.reflect⟩
  simpa only [Vertex.reflect_reflect] using hf.reflect

/-- Restriction to a translated subtriangle preserves rhombus concavity. -/
theorem IsRhombusConcave.subtriangle [Add R] [LE R] {m : ℕ} {f : Vertex (m + n) → R}
    (hf : IsRhombusConcave f) (p : Vertex m) : IsRhombusConcave (fun q => f (p.add q)) :=
  fun _ _ _ _ hr => hf (hr.add p)

@[simp] theorem isRhombusConcave_const [Add R] [Preorder R] (c : R) :
    IsRhombusConcave (fun _ : Vertex n => c) := fun _ _ _ _ _ => le_rfl

@[simp] theorem isRhombusConcave_zero [Add R] [Zero R] [Preorder R] :
    IsRhombusConcave (0 : Vertex n → R) := isRhombusConcave_const 0

/-- Pointwise addition preserves rhombus concavity. -/
theorem IsRhombusConcave.add [AddCommMonoid R] [Preorder R] [IsOrderedAddMonoid R]
    {f g : Vertex n → R} (hf : IsRhombusConcave f) (hg : IsRhombusConcave g) :
    IsRhombusConcave (f + g) := by
  intro a b c d hr
  simpa only [Pi.add_apply, add_add_add_comm] using add_le_add (hf hr) (hg hr)

/-- Adding a constant does not affect rhombus concavity, even for monoid values. -/
@[simp] theorem isRhombusConcave_add_const_iff [AddCommMonoid R] [Preorder R]
    [IsOrderedCancelAddMonoid R] (f : Vertex n → R) (c : R) :
    IsRhombusConcave (fun p => f p + c) ↔ IsRhombusConcave f := by
  constructor <;> intro hf a b c' d hr
  · have hi : (f b + f d) + (c + c) ≤ (f a + f c') + (c + c) := by
      convert hf hr using 1 <;> dsimp only <;> abel
    exact (add_le_add_iff_right _).mp hi
  · convert add_le_add_right (hf hr) (c + c) using 1 <;> dsimp only <;> abel

@[simp] theorem isRhombusConcave_const_add_iff [AddCommMonoid R] [Preorder R]
    [IsOrderedCancelAddMonoid R] (c : R) (f : Vertex n → R) :
    IsRhombusConcave (fun p => c + f p) ↔ IsRhombusConcave f := by
  simpa only [add_comm] using isRhombusConcave_add_const_iff f c

@[simp] theorem isRhombusConcave_sub_const_iff [AddCommGroup R] [Preorder R]
    [IsOrderedAddMonoid R] (f : Vertex n → R) (c : R) :
    IsRhombusConcave (fun p => f p - c) ↔ IsRhombusConcave f := by
  simpa only [sub_eq_add_neg] using isRhombusConcave_add_const_iff f (-c)

end Concavity

end Hive

/-- A normalized **hive** of size `n` with values in a preordered additive commutative monoid `R`:
a function on the triangular lattice `Hive.Vertex n` vanishing at `A = (n, 0, 0)` such that on
every unit rhombus `(a, b, c, d)` in
perimeter order with obtuse corners `a, c`, `value b + value d ≤ value a + value c`. -/
structure Hive (n : ℕ) (R : Type*) [AddCommMonoid R] [Preorder R] where
  /-- The value assigned to each vertex of the triangular lattice. -/
  value : Hive.Vertex n → R
  /-- Hives are normalized to vanish at the top corner `A = (n, 0, 0)`. -/
  value_cornerA' : value (Hive.Vertex.cornerA n) = 0
  /-- Every unit rhombus satisfies the obtuse-corner concavity inequality. -/
  le_of_isRhombus' : ∀ {a b c d : Hive.Vertex n}, Hive.IsRhombus a b c d →
    value b + value d ≤ value a + value c

/-- Normalized integer-valued hives of size `n`, counted by Littlewood–Richardson multiplicities. -/
abbrev IntegerHive (n : ℕ) : Type := Hive n ℤ

/-- Normalized real-valued hives of size `n`, the points of the real hive cone. -/
abbrev RealHive (n : ℕ) : Type := Hive n ℝ

namespace Hive

section Basic

variable {n : ℕ} {R : Type*} [AddCommMonoid R] [Preorder R]

instance instFunLike : FunLike (Hive n R) (Vertex n) R where
  coe := Hive.value
  coe_injective h₁ h₂ heq := by cases h₁; cases h₂; congr

@[simp] theorem value_eq_coe (h : Hive n R) : h.value = ⇑h := (rfl)

@[ext] theorem ext {h₁ h₂ : Hive n R} (H : ∀ p, h₁ p = h₂ p) : h₁ = h₂ := DFunLike.ext h₁ h₂ H

instance [DecidableEq R] : DecidableEq (Hive n R) := fun h₁ h₂ =>
  decidable_of_iff (∀ p, h₁ p = h₂ p) ⟨ext, fun h p => congrArg (· p) h⟩

@[simp] theorem coe_mk (f : Vertex n → R) (hA : f (Vertex.cornerA n) = 0)
    (hr : ∀ {a b c d : Vertex n}, IsRhombus a b c d → f b + f d ≤ f a + f c) :
    ⇑(⟨f, hA, hr⟩ : Hive n R) = f := (rfl)

@[simp] theorem mk_coe (h : Hive n R) (hA : h (Vertex.cornerA n) = 0)
    (hr : ∀ {a b c d : Vertex n}, IsRhombus a b c d → h b + h d ≤ h a + h c) :
    (⟨⇑h, hA, hr⟩ : Hive n R) = h := (rfl)

@[simp] theorem mk_apply (f : Vertex n → R) (hA : f (Vertex.cornerA n) = 0)
    (hr : ∀ {a b c d : Vertex n}, IsRhombus a b c d → f b + f d ≤ f a + f c) (p : Vertex n) :
    (⟨f, hA, hr⟩ : Hive n R) p = f p := (rfl)

/-- Normalized hives vanish at the top corner `A = (n, 0, 0)`. -/
@[simp] theorem apply_cornerA (h : Hive n R) : h (Vertex.cornerA n) = 0 := h.value_cornerA'

/-- On every unit rhombus `(a, b, c, d)` with obtuse corners `a, c`, `h b + h d ≤ h a + h c`. -/
theorem le_of_isRhombus (h : Hive n R) {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    h b + h d ≤ h a + h c := h.le_of_isRhombus' hr

@[simp] theorem isRhombusConcave (h : Hive n R) : IsRhombusConcave (h : Vertex n → R) :=
  fun _ _ _ _ hr => h.le_of_isRhombus hr

end Basic

/-! ### Rhombus slacks, unnormalized hives, and affine gauge transformations -/

section Barycentric

variable {n : ℕ} {R : Type*} [AddCommMonoid R]

/-- A barycentric-affine function `p ↦ c₀ + p.x • α + p.y • β + p.z • γ` on `Vertex n`. -/
def barycentricLinear (c₀ α β γ : R) (p : Vertex n) : R := c₀ + p.x • α + p.y • β + p.z • γ

@[simp] theorem barycentricLinear_apply (c₀ α β γ : R) (p : Vertex n) :
    barycentricLinear c₀ α β γ p = c₀ + p.x • α + p.y • β + p.z • γ := (rfl)

/-- Barycentric-affine functions have equal sums on opposite corners of a unit rhombus. -/
theorem barycentricLinear_midpoint (c₀ α β γ : R)
    {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    barycentricLinear c₀ α β γ a + barycentricLinear c₀ α β γ c =
      barycentricLinear c₀ α β γ b + barycentricLinear c₀ α β γ d := by
  simp only [barycentricLinear_apply]
  calc (c₀ + a.x • α + a.y • β + a.z • γ) + (c₀ + c.x • α + c.y • β + c.z • γ)
      = (c₀ + c₀) + (a.x + c.x) • α + (a.y + c.y) • β + (a.z + c.z) • γ := by
          simp only [add_nsmul]; abel
    _ = (c₀ + c₀) + (b.x + d.x) • α + (b.y + d.y) • β + (b.z + d.z) • γ := by
          rw [hr.midpoint_x, hr.midpoint_y, hr.midpoint_z]
    _ = (c₀ + b.x • α + b.y • β + b.z • γ) + (c₀ + d.x • α + d.y • β + d.z • γ) := by
          simp only [add_nsmul]; abel

@[simp] theorem isRhombusConcave_barycentricLinear [Preorder R] (c₀ α β γ : R) :
    IsRhombusConcave (barycentricLinear c₀ α β γ : Vertex n → R) :=
  fun _ _ _ _ hr => le_of_eq (barycentricLinear_midpoint c₀ α β γ hr).symm

/-- Rhombus concavity is invariant under adding any barycentric-affine function. -/
@[simp] theorem isRhombusConcave_add_barycentricLinear_iff [Preorder R]
    [IsOrderedCancelAddMonoid R] (f : Vertex n → R) (c₀ α β γ : R) :
    IsRhombusConcave (f + barycentricLinear c₀ α β γ) ↔ IsRhombusConcave f := by
  have heq (p q : Vertex n) :
      (f p + barycentricLinear c₀ α β γ p) + (f q + barycentricLinear c₀ α β γ q) =
        (f p + f q) + (barycentricLinear c₀ α β γ p + barycentricLinear c₀ α β γ q) :=
    add_add_add_comm _ _ _ _
  refine forall₄_congr fun a b c d => imp_congr_right fun hr => ?_
  simp only [Pi.add_apply]
  rw [heq, heq, ← barycentricLinear_midpoint c₀ α β γ hr, add_le_add_iff_right]

end Barycentric

section Gauge

variable {n : ℕ} {R : Type*} [AddCommGroup R]

/-- The **rhombus slack** `f a + f c - (f b + f d)` on `(a, b, c, d)` with obtuse corners `a, c`. -/
def rhombusSlack (f : Vertex n → R) (a b c d : Vertex n) : R := f a + f c - (f b + f d)

theorem rhombusSlack_def (f : Vertex n → R) (a b c d : Vertex n) :
    rhombusSlack f a b c d = f a + f c - (f b + f d) := (rfl)

@[simp] theorem rhombusSlack_zero (a b c d : Vertex n) :
    rhombusSlack (0 : Vertex n → R) a b c d = 0 := by simp [rhombusSlack]

theorem rhombusSlack_add (f g : Vertex n → R) (a b c d : Vertex n) :
    rhombusSlack (f + g) a b c d = rhombusSlack f a b c d + rhombusSlack g a b c d := by
  simp only [rhombusSlack, Pi.add_apply]; abel

theorem rhombusSlack_sub (f g : Vertex n → R) (a b c d : Vertex n) :
    rhombusSlack (f - g) a b c d = rhombusSlack f a b c d - rhombusSlack g a b c d := by
  simp only [rhombusSlack, Pi.sub_apply]; abel

theorem rhombusSlack_smul {S : Type*} [DistribSMul S R]
    (c : S) (f : Vertex n → R) (a b c' d : Vertex n) :
    rhombusSlack (c • f) a b c' d = c • rhombusSlack f a b c' d := by
  simp [rhombusSlack, smul_sub, smul_add]

@[simp] theorem rhombusSlack_const (c : R) (a b c' d : Vertex n) :
    rhombusSlack (fun _ => c) a b c' d = 0 := sub_self (c + c)

/-- Every barycentric-affine function has zero slack on every unit rhombus, because opposite
corners share the same midpoint in barycentric coordinates. -/
@[simp] theorem rhombusSlack_barycentricLinear (c₀ α β γ : R)
    {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    rhombusSlack (barycentricLinear c₀ α β γ) a b c d = 0 := by
  exact sub_eq_zero.mpr (barycentricLinear_midpoint c₀ α β γ hr)

/-- Adding a barycentric-affine function leaves all unit-rhombus slacks unchanged. -/
@[simp] theorem rhombusSlack_add_barycentricLinear (f : Vertex n → R) (c₀ α β γ : R)
    {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    rhombusSlack (f + barycentricLinear c₀ α β γ) a b c d = rhombusSlack f a b c d := by
  rw [rhombusSlack_add, rhombusSlack_barycentricLinear c₀ α β γ hr, add_zero]

section Ordered

variable [Preorder R]

variable [IsOrderedAddMonoid R]

/-- Rhombus concavity is equivalent to nonnegativity of every unit-rhombus slack. -/
theorem isRhombusConcave_iff_rhombusSlack_nonneg (f : Vertex n → R) :
    IsRhombusConcave f ↔ ∀ ⦃a b c d : Vertex n⦄, IsRhombus a b c d → 0 ≤ rhombusSlack f a b c d :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => sub_nonneg.symm

theorem rhombusSlack_nonneg (h : Hive n R) {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    0 ≤ rhombusSlack h a b c d := sub_nonneg.mpr (h.le_of_isRhombus hr)

/-- Normalize an unnormalized rhombus-concave function by subtracting its value at `A = (n, 0, 0)`.
-/
def ofRhombusConcave (f : Vertex n → R) (hf : IsRhombusConcave f) : Hive n R where
  value p := f p - f (Vertex.cornerA n)
  value_cornerA' := sub_self _
  le_of_isRhombus' hr := ((isRhombusConcave_sub_const_iff f (f (Vertex.cornerA n))).mpr hf) hr

/-- The labelling underlying normalization. -/
theorem coe_ofRhombusConcave (f : Vertex n → R) (hf : IsRhombusConcave f) :
    ⇑(ofRhombusConcave f hf) = fun p => f p - f (Vertex.cornerA n) := (rfl)

@[simp] theorem ofRhombusConcave_apply (f : Vertex n → R) (hf : IsRhombusConcave f) (p : Vertex n) :
    ofRhombusConcave f hf p = f p - f (Vertex.cornerA n) := (rfl)

@[simp] theorem ofRhombusConcave_coe (h : Hive n R) : ofRhombusConcave h h.isRhombusConcave = h :=
  by ext p; simp

/-- Two unnormalized hives normalize to the same `Hive` iff they differ by an additive constant. -/
theorem ofRhombusConcave_eq_iff {f₁ f₂ : Vertex n → R}
    (hf₁ : IsRhombusConcave f₁) (hf₂ : IsRhombusConcave f₂) :
    ofRhombusConcave f₁ hf₁ = ofRhombusConcave f₂ hf₂ ↔ ∃ c : R, ∀ p, f₁ p = f₂ p + c := by
  refine ⟨fun h => ⟨f₁ (Vertex.cornerA n) - f₂ (Vertex.cornerA n), fun p => ?_⟩, ?_⟩
  · have hp : f₁ p - f₁ (Vertex.cornerA n) = f₂ p - f₂ (Vertex.cornerA n) :=
      congrArg (fun k : Hive n R => k p) h
    calc f₁ p = (f₁ p - f₁ (Vertex.cornerA n)) + f₁ (Vertex.cornerA n) := by abel
      _ = (f₂ p - f₂ (Vertex.cornerA n)) + f₁ (Vertex.cornerA n) := by rw [hp]
      _ = f₂ p + (f₁ (Vertex.cornerA n) - f₂ (Vertex.cornerA n)) := by abel
  · rintro ⟨c, hc⟩; ext p; simp only [ofRhombusConcave_apply, hc]; abel

end Ordered

end Gauge

/-! ### Monoid structure, nonnegative scaling, affine hives, and subtriangle restriction -/

section Algebra

variable {n : ℕ} {R : Type*} [AddCommMonoid R] [Preorder R]

instance : Zero (Hive n R) := ⟨⟨0, rfl, fun hr => isRhombusConcave_zero.le hr⟩⟩
instance : Inhabited (Hive n R) := ⟨0⟩

@[simp] theorem coe_zero : ⇑(0 : Hive n R) = 0 := (rfl)
@[simp] theorem zero_apply (p : Vertex n) : (0 : Hive n R) p = 0 := (rfl)

/-- Nonnegative scalars from a partially ordered semiring act on hives. -/
instance instSMulNonneg {S : Type*} [Semiring S] [PartialOrder S]
    [Module S R] [PosSMulMono S R] : SMul (Nonneg S) (Hive n R) where
  smul c h := ⟨c.1 • ⇑h, by simp, fun hr => by
    simp only [Pi.smul_apply, ← smul_add]
    exact smul_le_smul_of_nonneg_left (h.le_of_isRhombus hr) c.2⟩

@[simp] theorem coe_smul_nonneg {S : Type*} [Semiring S] [PartialOrder S]
    [Module S R] [PosSMulMono S R] (c : Nonneg S) (h : Hive n R) : ⇑(c • h) = c.1 • ⇑h := (rfl)

@[simp] theorem smul_nonneg_apply {S : Type*} [Semiring S] [PartialOrder S]
    [Module S R] [PosSMulMono S R] (c : Nonneg S) (h : Hive n R) (p : Vertex n) :
    (c • h) p = c.1 • h p := (rfl)

/-- Push a hive forward along an order-preserving additive monoid homomorphism. -/
def map {S : Type*} [AddCommMonoid S] [Preorder S] (φ : R →+o S) (h : Hive n R) : Hive n S where
  value p := φ (h p)
  value_cornerA' := by simp
  le_of_isRhombus' hr := by simpa only [map_add] using OrderHomClass.mono φ (h.le_of_isRhombus hr)

@[simp] theorem map_apply {S : Type*} [AddCommMonoid S] [Preorder S]
    (φ : R →+o S) (h : Hive n R) (p : Vertex n) : h.map φ p = φ (h p) := (rfl)

section OrderedAdd

variable [IsOrderedAddMonoid R]

instance : Add (Hive n R) where
  add h₁ h₂ := ⟨h₁ + h₂, by simp, fun hr => (h₁.isRhombusConcave.add h₂.isRhombusConcave).le hr⟩

@[simp] theorem coe_add (h₁ h₂ : Hive n R) : ⇑(h₁ + h₂) = ⇑h₁ + ⇑h₂ := (rfl)
@[simp] theorem add_apply (h₁ h₂ : Hive n R) (p : Vertex n) : (h₁ + h₂) p = h₁ p + h₂ p := (rfl)

instance : SMul ℕ (Hive n R) where
  smul k h := ⟨k • ⇑h, by simp, fun hr => by
    simp only [Pi.smul_apply, ← smul_add]; exact nsmul_le_nsmul_right (h.le_of_isRhombus hr) k⟩

@[simp] theorem coe_nsmul (k : ℕ) (h : Hive n R) : ⇑(k • h) = k • ⇑h := (rfl)
@[simp] theorem nsmul_apply (k : ℕ) (h : Hive n R) (p : Vertex n) : (k • h) p = k • h p := (rfl)

instance : AddCommMonoid (Hive n R) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

/-- Evaluation as an additive monoid homomorphism from `Hive n R` to lattice functions. -/
def coeAddMonoidHom (n : ℕ) (R : Type*) [AddCommMonoid R] [Preorder R] [IsOrderedAddMonoid R] :
    Hive n R →+ (Vertex n → R) := ⟨⟨fun h => ⇑h, rfl⟩, fun _ _ => rfl⟩

@[simp] theorem coeAddMonoidHom_apply (h : Hive n R) : coeAddMonoidHom n R h = ⇑h := (rfl)

end OrderedAdd

/-- Normalized affine hive `p ↦ p.y • β + p.z • γ`, vanishing at `A` with zero slack everywhere. -/
def affine (n : ℕ) (β γ : R) : Hive n R where
  value p := p.y • β + p.z • γ
  value_cornerA' := by simp
  le_of_isRhombus' hr := by
    simpa [barycentricLinear] using isRhombusConcave_barycentricLinear (n := n) (0 : R) 0 β γ hr

/-- The labelling underlying an affine hive. -/
theorem coe_affine (β γ : R) :
    ⇑(affine n β γ) = fun p => p.y • β + p.z • γ := (rfl)

@[simp] theorem affine_apply (β γ : R) (p : Vertex n) : affine n β γ p = p.y • β + p.z • γ := (rfl)

/-- Zero slopes give the zero hive. -/
@[simp] theorem affine_zero : affine n (0 : R) 0 = 0 := by ext p; simp

/-- Addition of affine hives adds their slopes. -/
@[simp] theorem affine_add [IsOrderedAddMonoid R] (u v u' v' : R) :
    affine n (u + u') (v + v') = affine n u v + affine n u' v' := by
  ext p
  simp only [affine_apply, add_apply, nsmul_add]
  abel

end Algebra

section Restriction

variable {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]

@[simp] theorem rhombusSlack_affine (β γ : R) {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    rhombusSlack (affine n β γ) a b c d = 0 := by
  simpa [barycentricLinear, rhombusSlack, affine_apply] using
    rhombusSlack_barycentricLinear (n := n) (0 : R) 0 β γ hr

variable [IsOrderedAddMonoid R]

/-- Restrict a hive on `Δ_{m + k}` to the subtriangle of side `k` translated by `p : Δ_m`,
normalizing at `p.add (cornerA k)`. -/
def subtriangle {m k : ℕ} (h : Hive (m + k) R) (p : Vertex m) : Hive k R :=
  ofRhombusConcave (fun q => h (p.add q)) (h.isRhombusConcave.subtriangle p)

/-- The labelling underlying normalized restriction. -/
theorem coe_subtriangle {m k : ℕ} (h : Hive (m + k) R) (p : Vertex m) :
    ⇑(h.subtriangle p) = fun q => h (p.add q) - h (p.add (Vertex.cornerA k)) := (rfl)

@[simp] theorem subtriangle_apply {m k : ℕ} (h : Hive (m + k) R) (p : Vertex m) (q : Vertex k) :
    h.subtriangle p q = h (p.add q) - h (p.add (Vertex.cornerA k)) := (rfl)

/-- Restriction to a translated subtriangle preserves every unit-rhombus slack. -/
@[simp] theorem rhombusSlack_subtriangle {m k : ℕ} (h : Hive (m + k) R) (p : Vertex m)
    (a b c d : Vertex k) :
    rhombusSlack (h.subtriangle p) a b c d =
      rhombusSlack h (p.add a) (p.add b) (p.add c) (p.add d) := by
  simp only [rhombusSlack, subtriangle_apply]; abel

@[simp] theorem subtriangle_zero {m k : ℕ} (p : Vertex m) :
    (0 : Hive (m + k) R).subtriangle p = 0 := by ext q; simp

@[simp] theorem subtriangle_add {m k : ℕ} (h₁ h₂ : Hive (m + k) R) (p : Vertex m) :
    (h₁ + h₂).subtriangle p = h₁.subtriangle p + h₂.subtriangle p := by
  ext q; simp only [subtriangle_apply, add_apply]; abel

/-- Restriction preserves the slopes of an affine hive. -/
@[simp] theorem subtriangle_affine {m k : ℕ} (u v : R) (p : Vertex m) :
    (affine (m + k) u v).subtriangle p = affine k u v := by
  ext q
  simp only [subtriangle_apply, affine_apply, Vertex.add_y, Vertex.add_z, add_nsmul,
    Vertex.cornerA_y, Vertex.cornerA_z, add_zero]
  abel

/-- Normalization sends every constant labelling to the zero hive. -/
@[simp] theorem ofRhombusConcave_const (c : R) :
    ofRhombusConcave (fun _ : Vertex n => c) (isRhombusConcave_const c) = 0 := by ext p; simp

@[simp] theorem ofRhombusConcave_zero :
    ofRhombusConcave (0 : Vertex n → R) isRhombusConcave_zero = 0 := by ext p; simp

/-- Normalization commutes with pointwise addition. -/
@[simp] theorem ofRhombusConcave_add (f g : Vertex n → R)
    (hf : IsRhombusConcave f) (hg : IsRhombusConcave g) :
    ofRhombusConcave (f + g) (hf.add hg) = ofRhombusConcave f hf + ofRhombusConcave g hg := by
  ext p
  simp only [ofRhombusConcave_apply, add_apply, Pi.add_apply]
  abel

end Restriction

section Cone

variable {n : ℕ}

/-- Embed `IntegerHive n` into `Hive n R` for any ordered ring `R` via `Int.cast`. -/
def ofInt (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] {n : ℕ} :
    IntegerHive n →+ Hive n R where
  toFun h := h.map ⟨⟨⟨Int.cast, Int.cast_zero⟩, Int.cast_add⟩, fun _ _ hle => Int.cast_mono hle⟩
  map_zero' := by ext p; simp
  map_add' _ _ := by ext p; simp

@[simp] theorem ofInt_apply {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    (h : IntegerHive n) (p : Vertex n) : ofInt R h p = (h p : R) := (rfl)

/-- Canonical additive monoid embedding of integer hives into real hives. -/
abbrev toReal {n : ℕ} : IntegerHive n →+ RealHive n := ofInt ℝ

theorem ofInt_injective (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] [CharZero R]
    {n : ℕ} : Function.Injective (ofInt R (n := n)) := fun _ _ heq =>
  ext fun p => Int.cast_injective (congrArg (fun k : Hive n R => k p) heq)

/-- The pointed cone of normalized hives inside `Vertex n → R` over an ordered ring `R`. -/
def pointedCone (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] (n : ℕ) :
    PointedCone R (Vertex n → R) where
  carrier := {f | f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f}
  zero_mem' := ⟨rfl, isRhombusConcave_zero⟩
  add_mem' hf hg := ⟨by simp [hf.1, hg.1], hf.2.add hg.2⟩
  smul_mem' c f hf := ⟨by simp [hf.1], fun {a b c' d} hr => by
    simp only [Pi.smul_apply, ← Nonneg.coe_smul, smul_eq_mul, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hf.2 hr) c.2⟩

@[simp] theorem mem_pointedCone_iff {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    {f : Vertex n → R} : f ∈ pointedCone R n ↔ f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f :=
  Iff.rfl

theorem coe_mem_pointedCone {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    (h : Hive n R) : (h : Vertex n → R) ∈ pointedCone R n := ⟨h.apply_cornerA, h.isRhombusConcave⟩

end Cone

/-! ### Mixed second differences along unit lattice steps -/

section UnitSteps

/-- Along unit lattice edge directions `v, w` of inner product `1`, a hive has nonpositive mixed
second forward difference `(h(p + v + w) - h(p + w)) - (h(p + v) - h(p)) ≤ 0`. -/
theorem mixedDiff_nonpos_of_isUnitStep {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    [IsOrderedAddMonoid R] (h : Hive n R) {p pv pw pvw : Vertex n} {v w : Fin 3 → ℤ}
    (hv : IsUnitStep v) (hw : IsUnitStep w) (hdot : (∑ i, v i * w i) = 1)
    (hpv : HasStep p pv v) (hpw : HasStep p pw w) (hpvw : HasStep p pvw (v + w)) :
    (h pvw - h pw) - (h pv - h p) ≤ 0 := by
  have hle := h.le_of_isRhombus ((isRhombus_of_hasStep_iff hv hw hpv hpw hpvw).mpr hdot)
  calc (h pvw - h pw) - (h pv - h p) = (h p + h pvw) - (h pv + h pw) := by abel
    _ ≤ (h pv + h pw) - (h pv + h pw) := sub_le_sub_right hle _
    _ = 0 := sub_self _

/-- The quadratic hive `h(x, y, z) = 49 - x²` on `Δ₇`: all unit-rhombus slacks are `0` or `2`, yet
non-unit directions of inner product `1` can have positive mixed second difference. -/
def counterexampleSeven : IntegerHive 7 where
  value p := 49 - (p.x : ℤ) ^ 2
  value_cornerA' := by norm_num
  le_of_isRhombus' {a b c d} hr := by
    have hmx : (a.x : ℤ) + c.x = (b.x : ℤ) + d.x := by exact_mod_cast hr.midpoint_x
    set vx : ℤ := (a.x : ℤ) - b.x
    set wx : ℤ := (c.x : ℤ) - b.x
    have hab := hr.side_ab; rw [Vertex.sqDist_def] at hab
    have hbc := hr.side_bc; rw [Vertex.sqDist_comm, Vertex.sqDist_def] at hbc
    have hshort := hr.short; rw [Vertex.sqDist_def] at hshort
    have hvx : -1 ≤ vx ∧ vx ≤ 1 := by
      simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (b := 2) (by decide)).mpr
        (by linarith [sq_nonneg ((a.y : ℤ) - b.y), sq_nonneg ((a.z : ℤ) - b.z)])
    have hwx : -1 ≤ wx ∧ wx ≤ 1 := by
      simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (b := 2) (by decide)).mpr
        (by linarith [sq_nonneg ((c.y : ℤ) - b.y), sq_nonneg ((c.z : ℤ) - b.z)])
    have hdiff : -1 ≤ vx - wx ∧ vx - wx ≤ 1 := by
      rw [show vx - wx = (a.x : ℤ) - c.x by omega]
      simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (a := (a.x : ℤ) - c.x) (b := 2)
        (by decide)).mpr (by linarith [sq_nonneg ((a.y : ℤ) - c.y), sq_nonneg ((a.z : ℤ) - c.z)])
    have hvwx : 0 ≤ vx * wx := by
      rcases (by omega : vx = -1 ∨ vx = 0 ∨ vx = 1) with hv | hv | hv <;> rw [hv] <;> omega
    have hident : ((49 - (a.x : ℤ) ^ 2) + (49 - (c.x : ℤ) ^ 2)) -
        ((49 - (b.x : ℤ) ^ 2) + (49 - (d.x : ℤ) ^ 2)) = 2 * (vx * wx) := by
      rw [show (d.x : ℤ) = a.x + c.x - b.x by omega]; simp only [vx, wx]; ring
    linarith

@[simp] theorem counterexampleSeven_apply (p : Vertex 7) :
    counterexampleSeven p = 49 - (p.x : ℤ) ^ 2 := (rfl)

/-- On `Δ₇`, `counterexampleSeven` has positive mixed second difference `+12` at `p = (3, 4, 0)`
along the non-unit steps `v = (2, -3, 1)` and `w = (-3, -1, 4)` of inner product `1`. -/
theorem counterexampleSeven_nonunit_mixedDiff_pos :
    let p : Vertex 7 := ⟨3, 4, 0, rfl⟩
    let pv : Vertex 7 := ⟨5, 1, 1, rfl⟩
    let pw : Vertex 7 := ⟨0, 3, 4, rfl⟩
    let pvw : Vertex 7 := ⟨2, 0, 5, rfl⟩
    let v : Fin 3 → ℤ := ![2, -3, 1]
    let w : Fin 3 → ℤ := ![-3, -1, 4]
    (∑ i, v i) = 0 ∧ (∑ i, w i) = 0 ∧ (∑ i, v i * w i) = 1 ∧
      HasStep p pv v ∧ HasStep p pw w ∧ HasStep p pvw (v + w) ∧
      (counterexampleSeven pvw - counterexampleSeven pw) -
        (counterexampleSeven pv - counterexampleSeven p) = 12 := by
  refine ⟨by decide, by decide, by decide, hasStep_iff.mpr fun i => ?_,
    hasStep_iff.mpr fun i => ?_, hasStep_iff.mpr fun i => ?_, ?_⟩
  · fin_cases i <;> simp
  · fin_cases i <;> simp
  · fin_cases i <;> simp
  · norm_num [counterexampleSeven_apply]

end UnitSteps

/-! ### Linear boundary restriction and `boundary_antitone` -/

section Boundary

variable {n : ℕ} {R : Type*}

/-- The clockwise edge-difference operator on the ambient space `Vertex n → R`, an `S`-linear map
before restricting to the hive cone. -/
def boundaryLinear (S : Type*) (n : ℕ) (R : Type*) [Semiring S] [AddCommGroup R] [Module S R] :
    (Vertex n → R) →ₗ[S] (Fin 3 → Fin n → R) where
  toFun f s i := f (Vertex.edgePoint n s i.succ) - f (Vertex.edgePoint n s i.castSucc)
  map_add' _ _ := by ext s i; simp only [Pi.add_apply]; abel
  map_smul' _ _ := by ext s i; simp [smul_sub]

@[simp] theorem boundaryLinear_apply (S : Type*) [Semiring S] [AddCommGroup R] [Module S R]
    (f : Vertex n → R) (s : Fin 3) (i : Fin n) :
    boundaryLinear S n R f s i =
      f (Vertex.edgePoint n s i.succ) - f (Vertex.edgePoint n s i.castSucc) := (rfl)

section Ambient

variable [AddCommGroup R] (S : Type*) [Semiring S] [Module S R]

/-- The function underlying the ambient boundary linear map. -/
theorem coe_boundaryLinear :
    ⇑(boundaryLinear S n R) = fun f s i =>
      f (Vertex.edgePoint n s i.succ) - f (Vertex.edgePoint n s i.castSucc) := by
  funext f s i
  exact boundaryLinear_apply S f s i

/-- Rotating a labelling cycles its clockwise boundary sides. -/
@[simp] theorem boundaryLinear_rotate (f : Vertex n → R) :
    boundaryLinear S n R (fun p => f p.rotate) = fun s => boundaryLinear S n R f (s + 1) := by
  funext s i
  simp only [boundaryLinear_apply, Vertex.rotate_edgePoint]

@[simp] theorem boundaryLinear_const (c : R) :
    boundaryLinear S n R (fun _ => c) = 0 := by ext s i; simp

/-- Boundary differences do not depend on the additive gauge. -/
@[simp] theorem boundaryLinear_add_const (f : Vertex n → R) (c : R) :
    boundaryLinear S n R (fun p => f p + c) = boundaryLinear S n R f := by ext s i; simp

@[simp] theorem boundaryLinear_const_add (c : R) (f : Vertex n → R) :
    boundaryLinear S n R (fun p => c + f p) = boundaryLinear S n R f := by ext s i; simp

@[simp] theorem boundaryLinear_sub_const (f : Vertex n → R) (c : R) :
    boundaryLinear S n R (fun p => f p - c) = boundaryLinear S n R f := by ext s i; simp

/-- The ambient boundary commutes with any distributive scalar action. -/
@[simp] theorem boundaryLinear_smul {K : Type*} [DistribSMul K R] (c : K) (f : Vertex n → R) :
    boundaryLinear S n R (c • f) = c • boundaryLinear S n R f := by
  ext s i
  simp only [boundaryLinear_apply, Pi.smul_apply, smul_sub]

end Ambient

/-- Along the first `k` steps of side `s`, the edge differences telescope to
`f(edgePoint n s k) - f(edgePoint n s 0)`. -/
theorem sum_boundaryLinear_lt (S : Type*) [Semiring S] [AddCommGroup R] [Module S R]
    (f : Vertex n → R) (s : Fin 3) (k : ℕ) (hk : k ≤ n) :
    (∑ i : Fin n with i.val < k, boundaryLinear S n R f s i) =
      f (Vertex.edgePoint n s ⟨k, by omega⟩) - f (Vertex.edgePoint n s 0) := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hsplit : ({i : Fin n | i.val < m + 1} : Finset (Fin n)) =
        insert ⟨m, by omega⟩ ({i : Fin n | i.val < m} : Finset (Fin n)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]; omega
    have hnm : (⟨m, by omega⟩ : Fin n) ∉ ({i : Fin n | i.val < m} : Finset (Fin n)) := by simp
    rw [hsplit, Finset.sum_insert hnm, ih (by omega), boundaryLinear_apply, Fin.succ_mk,
      Fin.castSucc_mk]; abel

/-- Along side `s`, the `n` edge differences telescope to the difference of its two corners. -/
theorem sum_boundaryLinear_side (S : Type*) [Semiring S] [AddCommGroup R] [Module S R]
    (f : Vertex n → R) (s : Fin 3) :
    (∑ i : Fin n, boundaryLinear S n R f s i) =
      f (Vertex.edgePoint n s (Fin.last n)) - f (Vertex.edgePoint n s 0) := by
  simpa only [boundaryLinear_apply] using
    Fin.sum_univ_succ_sub_castSucc (fun i => f (Vertex.edgePoint n s i))

/-- The cyclic trace `∑ s, ∑ i, boundaryLinear f s i` vanishes for every lattice function `f`. -/
theorem sum_boundaryLinear (S : Type*) [Semiring S] [AddCommGroup R] [Module S R]
    (f : Vertex n → R) :
    (∑ s : Fin 3, ∑ i : Fin n, boundaryLinear S n R f s i) = 0 := by
  simp only [Fin.sum_univ_three, sum_boundaryLinear_side]
  rw [← Vertex.edgePoint_add_one_zero n 0, ← Vertex.edgePoint_add_one_zero n 1,
    Vertex.edgePoint_zero_zero, Vertex.edgePoint_two_last,
    zero_add, show (1 : Fin 3) + 1 = 2 from rfl]; abel

section HiveBoundary

variable [AddCommGroup R] [Preorder R]

/-- The clockwise cyclic boundary of a hive along `A → B`, `B → C`, and `C → A`. -/
def boundary (h : Hive n R) : Fin 3 → Fin n → R := boundaryLinear ℤ n R h

theorem boundary_def (h : Hive n R) : h.boundary = boundaryLinear ℤ n R h := (rfl)

theorem boundary_apply (h : Hive n R) (s : Fin 3) (i : Fin n) :
    h.boundary s i = h (Vertex.edgePoint n s i.succ) - h (Vertex.edgePoint n s i.castSucc) := (rfl)

@[simp] theorem boundaryLinear_coe (S : Type*) [Semiring S] [Module S R] (h : Hive n R) :
    boundaryLinear S n R h = h.boundary := by ext s i; rw [boundaryLinear_apply, boundary_apply]

/-- Normalization leaves the clockwise boundary unchanged. -/
@[simp] theorem boundary_ofRhombusConcave [IsOrderedAddMonoid R]
    (f : Vertex n → R) (hf : IsRhombusConcave f) :
    (ofRhombusConcave f hf).boundary = boundaryLinear ℤ n R f :=
  boundaryLinear_sub_const ℤ f (f (Vertex.cornerA n))

/-- A subtriangle has the boundary of its translated, unnormalized labelling. -/
@[simp] theorem boundary_subtriangle [IsOrderedAddMonoid R]
    {m : ℕ} (h : Hive (m + n) R) (p : Vertex m) :
    (h.subtriangle p).boundary = boundaryLinear ℤ n R (fun q => h (p.add q)) :=
  boundary_ofRhombusConcave (fun q => h (p.add q)) _

@[simp] theorem boundary_zero : (0 : Hive n R).boundary = 0 := map_zero (boundaryLinear ℤ n R)

@[simp] theorem boundary_add [IsOrderedAddMonoid R] (h₁ h₂ : Hive n R) :
    (h₁ + h₂).boundary = h₁.boundary + h₂.boundary := map_add (boundaryLinear ℤ n R) ⇑h₁ ⇑h₂

@[simp] theorem boundary_nsmul [IsOrderedAddMonoid R] (k : ℕ) (h : Hive n R) :
    (k • h).boundary = k • h.boundary := by ext s i; simp [boundary_apply, smul_sub]

@[simp] theorem boundary_smul_nonneg {S : Type*} [Semiring S] [PartialOrder S]
    [Module S R] [PosSMulMono S R] (c : Nonneg S) (h : Hive n R) :
    (c • h).boundary = c.1 • h.boundary := by ext s i; simp [boundary_apply, smul_sub]

@[simp] theorem boundary_map {S : Type*} [AddCommGroup S] [Preorder S]
    (φ : R →+o S) (h : Hive n R) (s : Fin 3) (i : Fin n) :
    (h.map φ).boundary s i = φ (h.boundary s i) := by simp [boundary_apply, map_sub]

@[simp] theorem boundary_affine (β γ : R) :
    (affine n β γ).boundary = ![fun _ => β, fun _ => γ - β, fun _ => -γ] := by
  ext s i; fin_cases s
  · simp [boundary_apply, affine_apply, add_nsmul]
  · have hsub : n - i.val = (n - (i.val + 1)) + 1 := by omega
    simp [boundary_apply, affine_apply, hsub, add_nsmul]
    abel
  · have hsub : n - i.val = (n - (i.val + 1)) + 1 := by omega
    simp [boundary_apply, affine_apply, hsub, add_nsmul]

/-- The cyclic trace `∑ s, ∑ i, h.boundary s i` of any hive vanishes. -/
@[simp] theorem sum_boundary (h : Hive n R) : (∑ s : Fin 3, ∑ i : Fin n, h.boundary s i) = 0 :=
  sum_boundaryLinear ℤ h

/-- Value of a hive at the `k`-th vertex of side `A → B` (`s = 0`) in terms of its boundary. -/
theorem apply_edgePoint_zero (h : Hive n R) (k : Fin (n + 1)) :
    h (Vertex.edgePoint n 0 k) = ∑ i : Fin n with i.val < k.val, h.boundary 0 i := by
  have ht := sum_boundaryLinear_lt ℤ (⇑h) 0 k.val (Nat.le_of_lt_succ k.isLt)
  rw [boundaryLinear_coe, Fin.eta, Vertex.edgePoint_zero_zero, h.apply_cornerA, sub_zero] at ht
  exact ht.symm

/-- Value of a hive at the `k`-th vertex of side `B → C` (`s = 1`) in terms of its boundary. -/
theorem apply_edgePoint_one (h : Hive n R) (k : Fin (n + 1)) :
    h (Vertex.edgePoint n 1 k) =
      (∑ i : Fin n, h.boundary 0 i) + ∑ i : Fin n with i.val < k.val, h.boundary 1 i := by
  have ht1 := sum_boundaryLinear_lt ℤ (⇑h) 1 k.val (Nat.le_of_lt_succ k.isLt)
  have ht0 := sum_boundaryLinear_side ℤ (⇑h) 0
  rw [boundaryLinear_coe, Fin.eta] at ht1
  rw [boundaryLinear_coe, Vertex.edgePoint_zero_zero, h.apply_cornerA, sub_zero,
    ← Vertex.edgePoint_add_one_zero n 0, zero_add] at ht0
  rw [ht0, ht1]; abel

/-- Value of a hive at the `k`-th vertex of side `C → A` (`s = 2`) in terms of its boundary. -/
theorem apply_edgePoint_two (h : Hive n R) (k : Fin (n + 1)) :
    h (Vertex.edgePoint n 2 k) = -∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i := by
  have hcompl : (∑ i : Fin n with i.val < k.val, h.boundary 2 i) +
      (∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i) = ∑ i : Fin n, h.boundary 2 i := by
    simpa [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < k.val) (h.boundary 2)
  have ht := sum_boundaryLinear_lt ℤ (⇑h) 2 k.val (Nat.le_of_lt_succ k.isLt)
  have hfull := sum_boundaryLinear_side ℤ (⇑h) 2
  rw [boundaryLinear_coe, Fin.eta] at ht
  rw [boundaryLinear_coe, Vertex.edgePoint_two_last, h.apply_cornerA, zero_sub] at hfull
  rw [ht, hfull] at hcompl
  exact eq_neg_of_add_eq_zero_left (by
    calc h (Vertex.edgePoint n 2 k) + ∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i
        = ((h (Vertex.edgePoint n 2 k) - h (Vertex.edgePoint n 2 0)) +
            ∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i) + h (Vertex.edgePoint n 2 0) := by abel
      _ = -h (Vertex.edgePoint n 2 0) + h (Vertex.edgePoint n 2 0) := by rw [hcompl]
      _ = 0 := neg_add_cancel _)

/-- Side `0` edge differences of any rhombus-concave function are antitone. -/
theorem antitone_boundaryLinear_zero_of_isRhombusConcave (S : Type*) [Semiring S] [Module S R]
    [IsOrderedAddMonoid R] {f : Vertex n → R} (hf : IsRhombusConcave f) :
    Antitone (boundaryLinear S n R f 0) := by
  match n with
  | 0 | 1 => exact Subsingleton.antitone _
  | k + 2 =>
    rw [Fin.antitone_iff_succ_le]; intro i
    let t : Vertex k := ⟨k - i.val, i.val, 0, by omega⟩
    have hp₀ : t.add (Vertex.cornerA 2) = Vertex.edgePoint (k + 2) 0 i.castSucc.castSucc := by
      ext <;> simp [t]; omega
    have hp₁ : t.add ⟨1, 1, 0, rfl⟩ = Vertex.edgePoint (k + 2) 0 i.castSucc.succ := by
      ext <;> simp [t]; omega
    have hp₁' : t.add (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate =
        Vertex.edgePoint (k + 2) 0 i.castSucc.succ := by ext <;> simp [t]; omega
    have hp₂ : t.add (Vertex.cornerA 2).rotate = Vertex.edgePoint (k + 2) 0 i.succ.succ := by
      ext <;> simp [t]
    have hq₀ : t.add (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate = t.add ⟨1, 0, 1, rfl⟩ := by ext <;> simp
    have hq₁ : t.add (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate = t.add ⟨0, 1, 1, rfl⟩ := by ext <;> simp
    have h₁ := hf (isRhombus_at_cornerA.add t)
    have h₂ := hf (isRhombus_at_cornerA.rotate.swap_opposite.reverse.add t)
    rw [hp₀, hp₁] at h₁; rw [hp₂, hq₀, hp₁', hq₁] at h₂
    set q₀ := t.add ⟨1, 0, 1, rfl⟩; set q₁ := t.add ⟨0, 1, 1, rfl⟩
    set p₀ := Vertex.edgePoint (k + 2) 0 i.castSucc.castSucc
    set p₁ := Vertex.edgePoint (k + 2) 0 i.castSucc.succ
    set p₂ := Vertex.edgePoint (k + 2) 0 i.succ.succ
    have hconc : f p₀ + f p₂ ≤ f p₁ + f p₁ := le_of_add_le_add_right (a := f q₀ + f q₁) <|
      calc (f p₀ + f p₂) + (f q₀ + f q₁) = (f p₀ + f q₁) + (f p₂ + f q₀) := by abel
        _ ≤ (f p₁ + f q₀) + (f p₁ + f q₁) := add_le_add h₁ h₂
        _ = (f p₁ + f p₁) + (f q₀ + f q₁) := by abel
    rw [boundaryLinear_apply, boundaryLinear_apply, Fin.castSucc_succ]
    calc f p₂ - f p₁ = (f p₀ + f p₂) - (f p₀ + f p₁) := by abel
      _ ≤ (f p₁ + f p₁) - (f p₀ + f p₁) := sub_le_sub_right hconc _
      _ = f p₁ - f p₀ := by abel

/-- Each side of an unnormalized rhombus-concave labelling has antitone differences. -/
theorem IsRhombusConcave.boundaryLinear_antitone (S : Type*) [Semiring S] [Module S R]
    [IsOrderedAddMonoid R] {f : Vertex n → R} (hf : IsRhombusConcave f) (s : Fin 3) :
    Antitone (boundaryLinear S n R f s) := by
  -- The cyclic-shift lemmas use side numerals; fin_cases instead produces Fin constructors.
  -- The change steps identify these indices without unfolding the boundary operator.
  fin_cases s
  · exact antitone_boundaryLinear_zero_of_isRhombusConcave S hf
  · change Antitone (boundaryLinear S n R f 1)
    simpa only [boundaryLinear_rotate, zero_add] using
      antitone_boundaryLinear_zero_of_isRhombusConcave S hf.rotate
  · change Antitone (boundaryLinear S n R f 2)
    have heq : boundaryLinear S n R f 2 =
        boundaryLinear S n R (fun p => f p.rotate.rotate) 0 := by
      calc boundaryLinear S n R f 2 = boundaryLinear S n R (fun p => f p.rotate) 1 :=
            (congrFun (boundaryLinear_rotate S f) 1).symm
        _ = boundaryLinear S n R (fun p => f p.rotate.rotate) 0 :=
            (congrFun (boundaryLinear_rotate S (fun p => f p.rotate)) 0).symm
    rw [heq]
    exact antitone_boundaryLinear_zero_of_isRhombusConcave S hf.rotate.rotate

/-- **Each boundary side of a hive is antitone**: for every hive over an ordered abelian group and
every side `s : Fin 3`, the successive clockwise edge differences `h.boundary s` decrease weakly. -/
theorem boundary_antitone [IsOrderedAddMonoid R] (h : Hive n R) (s : Fin 3) :
    Antitone (h.boundary s) := h.isRhombusConcave.boundaryLinear_antitone ℤ s

end HiveBoundary

@[simp] theorem boundary_ofInt [Ring R] [PartialOrder R] [IsOrderedRing R] (h : IntegerHive n)
    (s : Fin 3) (i : Fin n) : (ofInt R h).boundary s i = (h.boundary s i : R) := by
  simp [boundary_apply]

/-- Side `s` of an integer hive packaged as a `TauCeti.DominantWeight`. -/
def boundaryWeight (h : IntegerHive n) (s : Fin 3) : DominantWeight n :=
  ⟨h.boundary s, h.boundary_antitone s⟩

@[simp] theorem coe_boundaryWeight (h : IntegerHive n) (s : Fin 3) :
    (h.boundaryWeight s : Fin n → ℤ) = h.boundary s := (rfl)

/-- The cyclic boundary `(λ, μ, γ*)` counting the multiplicity of `V_γ` in `V_λ ⊗ V_μ`. -/
def productBoundary (lam μ γ : DominantWeight n) : Fin 3 → Fin n → ℤ := ![lam.1, μ.1, γ.dual.1]

@[simp] theorem productBoundary_zero (lam μ γ : DominantWeight n) :
    productBoundary lam μ γ 0 = lam.1 := (rfl)
@[simp] theorem productBoundary_one (lam μ γ : DominantWeight n) :
    productBoundary lam μ γ 1 = μ.1 := (rfl)
@[simp] theorem productBoundary_two (lam μ γ : DominantWeight n) :
    productBoundary lam μ γ 2 = γ.dual.1 := (rfl)

/-- Cyclic trace zero for `productBoundary lam μ γ` is degree conservation `|λ| + |μ| = |γ|`. -/
theorem sum_productBoundary_eq_zero_iff (lam μ γ : DominantWeight n) :
    (∑ s : Fin 3, ∑ i : Fin n, productBoundary lam μ γ s i) = 0 ↔
      (∑ i, lam.1 i) + (∑ i, μ.1 i) = ∑ i, γ.1 i := by
  simp only [Fin.sum_univ_three, productBoundary_zero, productBoundary_one, productBoundary_two,
    DominantWeight.sum_dual]; omega

end Boundary

/-! ### Dihedral action on normalized hives and boundaries -/

section MonoidSymmetries

variable {n : ℕ} {R : Type*} [AddCommMonoid R] [Preorder R]

/-- Reflection of a normalized hive across `A`: pull back along `Vertex.reflect`. -/
def reflect (h : Hive n R) : Hive n R :=
  ⟨fun p => h p.reflect, by simp, fun hr => h.isRhombusConcave.reflect hr⟩

@[simp] theorem reflect_apply (h : Hive n R) (p : Vertex n) : h.reflect p = h p.reflect := (rfl)
@[simp] theorem reflect_reflect (h : Hive n R) : h.reflect.reflect = h := by ext p; simp

theorem reflect_involutive : Function.Involutive (reflect (n := n) (R := R)) := reflect_reflect
theorem reflect_injective : Function.Injective (reflect (n := n) (R := R)) :=
  reflect_involutive.injective

end MonoidSymmetries

section Symmetries

variable {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]

/-- Clockwise rotation of a normalized hive, re-normalized at `A = (n, 0, 0)`. -/
def rotate [IsOrderedAddMonoid R] (h : Hive n R) : Hive n R :=
  ofRhombusConcave (fun p => h p.rotate) h.isRhombusConcave.rotate

@[simp] theorem rotate_apply [IsOrderedAddMonoid R] (h : Hive n R) (p : Vertex n) :
    h.rotate p = h p.rotate - h (Vertex.cornerA n).rotate := (rfl)

@[simp] theorem rotate_rotate_rotate [IsOrderedAddMonoid R] (h : Hive n R) :
    h.rotate.rotate.rotate = h := by
  ext p; simp only [rotate_apply, Vertex.rotate_rotate_rotate, apply_cornerA]; abel

theorem rotate_injective [IsOrderedAddMonoid R] :
    Function.Injective (rotate (n := n) (R := R)) := fun _ _ heq => by
  simpa using congrArg (fun k : Hive n R => k.rotate.rotate) heq

/-- Rotating a hive cyclically shifts its boundary sides: `h.rotate.boundary s = h.boundary (s+1)`.
-/
@[simp] theorem boundary_rotate [IsOrderedAddMonoid R] (h : Hive n R) (s : Fin 3) :
    h.rotate.boundary s = h.boundary (s + 1) := by
  simp only [rotate, boundary_ofRhombusConcave, boundaryLinear_rotate, boundaryLinear_coe]

@[simp] theorem boundaryWeight_rotate (h : IntegerHive n) (s : Fin 3) :
    h.rotate.boundaryWeight s = h.boundaryWeight (s + 1) := by ext i; simp [coe_boundaryWeight]

@[simp] theorem reflect_rotate_reflect_rotate [IsOrderedAddMonoid R] (h : Hive n R) :
    h.reflect.rotate.reflect.rotate = h := by
  ext p
  have hp : p.rotate.reflect.rotate.reflect = p := by ext <;> simp
  have hA : (Vertex.cornerA n).rotate.reflect.rotate.reflect = Vertex.cornerA n := by ext <;> simp
  simp only [rotate_apply, reflect_apply, hp, hA, apply_cornerA]; abel

/-- Reflecting a hive reverses the side order (`0 ↔ 2`, fixing `1`) and dualizes each side weight.
-/
@[simp] theorem boundary_reflect (h : Hive n R) (s : Fin 3) (i : Fin n) :
    h.reflect.boundary s i = -h.boundary s.rev i.rev := by
  simp only [boundary_apply, reflect_apply, Vertex.reflect_edgePoint, ← Fin.rev_castSucc,
    ← Fin.rev_succ]; abel

@[simp] theorem boundaryWeight_reflect (h : IntegerHive n) (s : Fin 3) :
    h.reflect.boundaryWeight s = (h.boundaryWeight s.rev).dual := by
  ext i; simp [coe_boundaryWeight]

/-- Reflecting and rotating once sends boundary `(λ, μ, γ*)` to `(μ*, λ*, γ**)`. -/
theorem boundary_reflect_rotate_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    h.reflect.rotate.boundary = productBoundary μ.dual lam.dual γ.dual := by
  ext s i; fin_cases s <;> simp [hb]

end Symmetries

/-! ### Small-rank structure and chirality checks -/

section SmallRankMonoid

variable {R : Type*} [AddCommMonoid R] [Preorder R]

/-- At size `0`, the unique normalized hive is `0` with empty boundary. -/
instance uniqueZero : Unique (Hive 0 R) where
  default := 0
  uniq h := ext fun p => by
    have hp : p = Vertex.cornerA 0 := by have := p.sum_eq; ext <;> simp <;> omega
    rw [hp, h.apply_cornerA, zero_apply]

/-- At size `1`, there are no unit rhombi, so normalized hives correspond freely to `(h B, h C)`. -/
def equivOne : Hive 1 R ≃ (R × R) where
  toFun h := (h ⟨0, 1, 0, rfl⟩, h ⟨0, 0, 1, rfl⟩)
  invFun bc := ⟨fun p => if p.y = 1 then bc.1 else if p.z = 1 then bc.2 else 0, by simp,
    fun hr => absurd hr.two_le (by decide)⟩
  left_inv h := ext fun p => by
    have := p.sum_eq
    rcases (by omega : p.x = 1 ∧ p.y = 0 ∧ p.z = 0 ∨ p.x = 0 ∧ p.y = 1 ∧ p.z = 0 ∨
        p.x = 0 ∧ p.y = 0 ∧ p.z = 1) with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
    · rw [show p = Vertex.cornerA 1 by ext <;> simp [hx, hy, hz]]; simp
    · rw [show p = ⟨0, 1, 0, rfl⟩ by ext <;> simp [hx, hy, hz]]; rfl
    · rw [show p = ⟨0, 0, 1, rfl⟩ by ext <;> simp [hx, hy, hz]]; rfl
  right_inv _ := rfl

@[simp] theorem equivOne_apply (h : Hive 1 R) :
    equivOne h = (h ⟨0, 1, 0, rfl⟩, h ⟨0, 0, 1, rfl⟩) := (rfl)

@[simp] theorem equivOne_symm_apply (bc : R × R) (p : Vertex 1) :
    equivOne.symm bc p = if p.y = 1 then bc.1 else if p.z = 1 then bc.2 else 0 := (rfl)

end SmallRankMonoid

section SmallRank

variable {R : Type*} [AddCommGroup R] [Preorder R]

@[simp] theorem boundary_equivOne_symm (b c : R) :
    (equivOne.symm (b, c)).boundary = ![fun _ => b, fun _ => c - b, fun _ => -c] := by
  ext s i; fin_cases i; fin_cases s <;> simp [boundary_apply]

/-- At size `2`, `Δ₂` has no strictly interior vertices, so `boundary` is injective. -/
theorem boundary_injective_two : Function.Injective (boundary (n := 2) (R := R)) := by
  intro h₁ h₂ hb; ext p; have := p.sum_eq
  rcases (by omega : p.z = 0 ∨ p.x = 0 ∨ p.y = 0) with hz | hx | hy
  · rw [show p = Vertex.edgePoint 2 0 ⟨p.y, by omega⟩ by ext <;> simp [hz]; omega,
      apply_edgePoint_zero, apply_edgePoint_zero, hb]
  · rw [show p = Vertex.edgePoint 2 1 ⟨p.z, by omega⟩ by ext <;> simp [hx]; omega,
      apply_edgePoint_one, apply_edgePoint_one, hb]
  · rw [show p = Vertex.edgePoint 2 2 ⟨p.x, by omega⟩ by ext <;> simp [hy]; omega,
      apply_edgePoint_two, apply_edgePoint_two, hb]

/-- Chirality check at size `2`: `isRhombus_at_cornerA` has slack `-(λ₂ + μ₁ + ν₂)`. -/
theorem rhombusSlack_at_cornerA_two (h : Hive 2 R) :
    rhombusSlack h ⟨1, 1, 0, rfl⟩ (Vertex.cornerA 2) ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ =
      -(h.boundary 0 1 + h.boundary 1 0 + h.boundary 2 1) := by
  rw [rhombusSlack_def, h.apply_cornerA,
    show (⟨1, 1, 0, rfl⟩ : Vertex 2) = Vertex.edgePoint 2 0 1 by ext <;> simp,
    show (⟨0, 1, 1, rfl⟩ : Vertex 2) = Vertex.edgePoint 2 1 1 by ext <;> simp,
    show (⟨1, 0, 1, rfl⟩ : Vertex 2) = Vertex.edgePoint 2 2 1 by ext <;> simp,
    apply_edgePoint_zero, apply_edgePoint_one, apply_edgePoint_two,
    show ({i : Fin 2 | i.val < (1 : Fin 3).val} : Finset (Fin 2)) = {0} by decide,
    show ({i : Fin 2 | (1 : Fin 3).val ≤ i.val} : Finset (Fin 2)) = {1} by decide,
    Fin.sum_univ_two]
  simp only [Finset.sum_singleton]; abel

/-- Size-`2` check: clockwise perimeter `(0, 1, 1, 2, 2, 2)` has boundary `((1,0),(1,0),(0,-2))`. -/
def exampleTwo : IntegerHive 2 where
  value p := (if p.x = 2 then 0 else 1) + (if p.z = 0 then 0 else 1)
  value_cornerA' := by simp
  le_of_isRhombus' {a b c d} hr := by
    have hshort := hr.short; rw [Vertex.sqDist_def] at hshort
    have hdx : -1 ≤ (a.x : ℤ) - c.x ∧ (a.x : ℤ) - c.x ≤ 1 := by
      simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (a := (a.x : ℤ) - c.x) (b := 2)
        (by decide)).mpr (by linarith [sq_nonneg ((a.y : ℤ) - c.y), sq_nonneg ((a.z : ℤ) - c.z)])
    have hdz : -1 ≤ (a.z : ℤ) - c.z ∧ (a.z : ℤ) - c.z ≤ 1 := by
      simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (a := (a.z : ℤ) - c.z) (b := 2)
        (by decide)).mpr (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.y : ℤ) - c.y)])
    have := hr.midpoint_x; have := hr.midpoint_z
    have := a.sum_eq; have := b.sum_eq; have := c.sum_eq; have := d.sum_eq; omega

@[simp] theorem exampleTwo_apply (p : Vertex 2) :
    exampleTwo p = (if p.x = 2 then 0 else 1) + (if p.z = 0 then 0 else 1) := (rfl)

theorem boundary_exampleTwo :
    exampleTwo.boundary =
      productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩ := by
  ext s i; fin_cases i <;> fin_cases s <;> simp [boundary_apply]

theorem slacks_exampleTwo :
    rhombusSlack exampleTwo ⟨1, 1, 0, rfl⟩ (Vertex.cornerA 2) ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ = 1 ∧
    rhombusSlack exampleTwo (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate (Vertex.cornerA 2).rotate
      (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate = 0 ∧
    rhombusSlack exampleTwo (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate.rotate
      (Vertex.cornerA 2).rotate.rotate (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate.rotate
      (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate.rotate = 1 := by simp [rhombusSlack_def]

/-- Rank-`2` check for `λ = μ = (1, 0)`, `γ = (1, 1)`: perimeter `(0, 1, 1, 2, 2, 1)`, slacks
`(0, 1, 0)`. -/
def detTwo : IntegerHive 2 where
  value p := (p.z : ℤ) + if p.y = 0 then 0 else 1
  value_cornerA' := by simp
  le_of_isRhombus' {a b c d} hr := by
    have hshort := hr.short; rw [Vertex.sqDist_def] at hshort
    have hbdy : -1 ≤ (a.y : ℤ) - c.y ∧ (a.y : ℤ) - c.y ≤ 1 := by
      simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (a := (a.y : ℤ) - c.y) (b := 2)
        (by decide)).mpr (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.z : ℤ) - c.z)])
    have := hr.midpoint_y; have := hr.midpoint_z
    have := a.sum_eq; have := b.sum_eq; have := c.sum_eq; have := d.sum_eq; omega

@[simp] theorem detTwo_apply (p : Vertex 2) :
    detTwo p = (p.z : ℤ) + if p.y = 0 then 0 else 1 := (rfl)

theorem boundary_detTwo :
    detTwo.boundary =
      productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩ := by
  ext s i; fin_cases i <;> fin_cases s <;> simp [boundary_apply]

theorem slacks_detTwo :
    rhombusSlack detTwo ⟨1, 1, 0, rfl⟩ (Vertex.cornerA 2) ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ = 0 ∧
    rhombusSlack detTwo (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate (Vertex.cornerA 2).rotate
      (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate = 1 ∧
    rhombusSlack detTwo (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate.rotate
      (Vertex.cornerA 2).rotate.rotate (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate.rotate
      (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate.rotate = 0 := by simp [rhombusSlack_def]

/-- Size-`2` non-hive check: setting `1` only at `m_BC = (0, 1, 1)` gives slack `-1` at `A`. -/
theorem not_isRhombusConcave_indicator_mBC :
    let f : Vertex 2 → ℤ := fun p => if p = ⟨0, 1, 1, rfl⟩ then 1 else 0
    rhombusSlack f ⟨1, 1, 0, rfl⟩ (Vertex.cornerA 2) ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ = -1 ∧
      ¬ IsRhombusConcave f := by
  refine ⟨by simp [rhombusSlack_def, Vertex.ext_iff], fun hf => ?_⟩
  have h := hf isRhombus_at_cornerA; simp [Vertex.ext_iff] at h

end SmallRank

end Hive

end TauCeti
