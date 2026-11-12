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
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Hives, gauge symmetries, and dominant-weight boundaries

A normalized **hive** of size `n` with values in a partially ordered abelian group `R` is a
function `h : Hive.Vertex n → R` vanishing at the top corner `A = (n, 0, 0)` such that on every
unit rhombus `(a, b, c, d)` in perimeter order with obtuse corners `a, c`,

`h b + h d ≤ h a + h c`.

Equivalently, every unit-rhombus slack `h a + h c - (h b + h d)` is nonnegative, and every mixed
second forward difference `(h(p + v + w) - h(p + w)) - (h(p + v) - h(p))` along a pair of unit
lattice edge steps `v, w` of inner product `1` is nonpositive. Restricting to *unit* lattice steps
is essential: on `Δ₇` the normalized hive `h(x, y, z) = 49 - x²` has unit-rhombus slacks `0` and
`2`, yet its mixed second difference at `(3, 4, 0)` along the non-unit steps `(2, -3, 1)` and
`(-3, -1, 4)` of inner product `1` is `+12`.

Adding a barycentric-affine function `c₀ + x • α + y • β + z • γ` preserves every rhombus slack;
subtracting the value at `A` normalizes any unnormalized rhombus-concave function to a unique
`Hive`, identifying normalized hives with rhombus-concave functions modulo additive constants.
Normalized hives form an additive commutative monoid (`IntegerHive n` for counting) and, over an
ordered ring, a pointed cone (`PointedCone R (Hive.Vertex n → R)`).

Reading successive edge differences clockwise along the three sides `A → B → C → A` defines an
ambient linear map `Hive.boundaryLinear` before restricting to hives. Its values telescope to zero
around the perimeter (`Hive.sum_boundary`), determine all boundary vertex values from `h(A) = 0`,
and are weakly decreasing along each side (`Hive.boundary_antitone`): the two unit rhombi sharing
the interior unit triangle at an edge point sum to the concavity inequality along that side. Each
side of an integer hive is therefore a `TauCeti.DominantWeight`. Clockwise rotation cyclically
permutes the three boundary sides, while reflection across `A` reverses their order and applies the
contragredient involution `TauCeti.DominantWeight.dual`.

## Main definitions

* `TauCeti.Hive n R`, `TauCeti.IntegerHive n`, `TauCeti.RealHive n`: normalized hives over `R`, `ℤ`,
  and `ℝ`.
* `TauCeti.Hive.rhombusSlack` and `TauCeti.Hive.IsRhombusConcave`: unit-rhombus slacks and the
  unnormalized rhombus-concavity predicate, normalized via `TauCeti.Hive.ofRhombusConcave`.
* `TauCeti.Hive.barycentricLinear` and `TauCeti.Hive.affine`: affine gauge transformations and
  normalized affine hives with zero rhombus slack.
* `TauCeti.Hive.pointedCone`: the pointed cone of normalized hives inside `Hive.Vertex n → R`.
* `TauCeti.Hive.subtriangle`: normalized restriction of a hive to a translated subtriangle.
* `TauCeti.Hive.IsUnitStep` and `TauCeti.Hive.HasStep`: unit lattice edge directions and the
  mixed-difference comparison with `IsRhombus`.
* `TauCeti.Hive.Vertex.edgePoint`, `TauCeti.Hive.boundaryLinear`, and `TauCeti.Hive.boundary`:
  clockwise boundary parameterization and edge-difference maps.
* `TauCeti.Hive.boundaryWeight` and `TauCeti.Hive.productBoundary`: dominant-weight boundary sides
  of an integer hive and the cyclic boundary `(λ, μ, γ*)` for tensor-product multiplicities.
* `TauCeti.Hive.rotate` and `TauCeti.Hive.reflect`: dihedral symmetries of normalized hives.

## Main results

* `TauCeti.Hive.rhombusSlack_add_barycentricLinear` and `TauCeti.Hive.ofRhombusConcave_eq_iff`:
  affine gauge invariance of slacks and characterization of normalization fibres.
* `TauCeti.Hive.isRhombus_of_hasStep_iff` and `TauCeti.Hive.counterexampleSeven`: unit-step
  mixed-difference characterization of rhombi and the `Δ₇` non-unit counterexample.
* `TauCeti.Hive.sum_boundary` and `TauCeti.Hive.boundary_antitone`: zero cyclic trace and
  antitonicity of each boundary side.
* `TauCeti.Hive.boundary_rotate` and `TauCeti.Hive.boundaryWeight_reflect`: action of rotation and
  reflection on boundary weights.

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

/-- A normalized **hive** of size `n` with values in `R`: a function on the triangular lattice
`Hive.Vertex n` vanishing at `A = (n, 0, 0)` such that on every unit rhombus `(a, b, c, d)` in
perimeter order with obtuse corners `a, c`, the obtuse sum `value a + value c` is at least the
acute sum `value b + value d`. -/
structure Hive (n : ℕ) (R : Type*) [AddCommGroup R] [PartialOrder R] where
  /-- The value assigned to each vertex of the triangular lattice. -/
  value : Hive.Vertex n → R
  /-- Hives are normalized to vanish at the top corner `A = (n, 0, 0)`. -/
  value_cornerA' : value (Hive.Vertex.cornerA n) = 0
  /-- Every unit rhombus satisfies the obtuse-corner concavity inequality. -/
  le_of_isRhombus' : ∀ {a b c d : Hive.Vertex n}, Hive.IsRhombus a b c d →
    value b + value d ≤ value a + value c

/-- Normalized integer-valued hives of size `n`, the combinatorial objects counted by
Littlewood–Richardson multiplicities. -/
abbrev IntegerHive (n : ℕ) : Type := Hive n ℤ

/-- Normalized real-valued hives of size `n`, the points of the real hive cone. -/
abbrev RealHive (n : ℕ) : Type := Hive n ℝ

namespace Hive

section Basic

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]

instance instFunLike : FunLike (Hive n R) (Vertex n) R where
  coe := Hive.value
  coe_injective h₁ h₂ heq := by cases h₁; cases h₂; congr

@[simp] theorem value_eq_coe (h : Hive n R) : h.value = ⇑h := (rfl)

@[ext] theorem ext {h₁ h₂ : Hive n R} (H : ∀ p, h₁ p = h₂ p) : h₁ = h₂ :=
  DFunLike.ext h₁ h₂ H

instance [DecidableEq R] : DecidableEq (Hive n R) := fun h₁ h₂ =>
  decidable_of_iff (∀ p, h₁ p = h₂ p) ⟨ext, fun h p => congrArg (· p) h⟩

theorem coe_mk (f : Vertex n → R) (hA : f (Vertex.cornerA n) = 0)
    (hr : ∀ {a b c d : Vertex n}, IsRhombus a b c d → f b + f d ≤ f a + f c) :
    ⇑(⟨f, hA, hr⟩ : Hive n R) = f := (rfl)

@[simp]
theorem mk_apply (f : Vertex n → R) (hA : f (Vertex.cornerA n) = 0)
    (hr : ∀ {a b c d : Vertex n}, IsRhombus a b c d → f b + f d ≤ f a + f c) (p : Vertex n) :
    (⟨f, hA, hr⟩ : Hive n R) p = f p := (rfl)

/-- Normalized hives vanish at the top corner `A = (n, 0, 0)`. -/
@[simp] theorem apply_cornerA (h : Hive n R) : h (Vertex.cornerA n) = 0 := h.value_cornerA'

/-- On every unit rhombus `(a, b, c, d)` with obtuse corners `a, c`, a hive satisfies
`h b + h d ≤ h a + h c`. -/
theorem le_of_isRhombus (h : Hive n R) {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    h b + h d ≤ h a + h c :=
  h.le_of_isRhombus' hr

end Basic

/-! ### Rhombus slacks, unnormalized hives, and affine gauge transformations -/

section Gauge

variable {n : ℕ} {R : Type*}

/-- The **rhombus slack** `f a + f c - (f b + f d)` of a lattice function `f` on a four-tuple
`(a, b, c, d)` with obtuse corners `a, c` and acute corners `b, d`. -/
def rhombusSlack [AddCommGroup R] (f : Vertex n → R) (a b c d : Vertex n) : R :=
  f a + f c - (f b + f d)

theorem rhombusSlack_def [AddCommGroup R] (f : Vertex n → R) (a b c d : Vertex n) :
    rhombusSlack f a b c d = f a + f c - (f b + f d) := (rfl)

@[simp]
theorem rhombusSlack_zero [AddCommGroup R] (a b c d : Vertex n) :
    rhombusSlack (0 : Vertex n → R) a b c d = 0 := by simp [rhombusSlack]

theorem rhombusSlack_add [AddCommGroup R] (f g : Vertex n → R) (a b c d : Vertex n) :
    rhombusSlack (f + g) a b c d = rhombusSlack f a b c d + rhombusSlack g a b c d := by
  simp only [rhombusSlack, Pi.add_apply]; abel

theorem rhombusSlack_sub [AddCommGroup R] (f g : Vertex n → R) (a b c d : Vertex n) :
    rhombusSlack (f - g) a b c d = rhombusSlack f a b c d - rhombusSlack g a b c d := by
  simp only [rhombusSlack, Pi.sub_apply]; abel

theorem rhombusSlack_smul {S : Type*} [Semiring S] [AddCommGroup R] [Module S R]
    (c : S) (f : Vertex n → R) (a b c' d : Vertex n) :
    rhombusSlack (c • f) a b c' d = c • rhombusSlack f a b c' d := by
  simp [rhombusSlack, smul_sub, smul_add]

@[simp]
theorem rhombusSlack_const [AddCommGroup R] (c : R) (a b c' d : Vertex n) :
    rhombusSlack (fun _ => c) a b c' d = 0 :=
  sub_self (c + c)

/-- A lattice function is **rhombus-concave** (an unnormalized hive) if on every unit rhombus the
sum at the obtuse corners is at least the sum at the acute corners. -/
def IsRhombusConcave [AddCommGroup R] [Preorder R] (f : Vertex n → R) : Prop :=
  ∀ ⦃a b c d : Vertex n⦄, IsRhombus a b c d → f b + f d ≤ f a + f c

theorem isRhombusConcave_def [AddCommGroup R] [Preorder R] (f : Vertex n → R) :
    IsRhombusConcave f ↔ ∀ ⦃a b c d : Vertex n⦄, IsRhombus a b c d → f b + f d ≤ f a + f c :=
  Iff.rfl

instance [AddCommGroup R] [Preorder R] [DecidableRel (· ≤ · : R → R → Prop)]
    (f : Vertex n → R) : Decidable (IsRhombusConcave f) :=
  decidable_of_iff _ (isRhombusConcave_def f).symm

/-- Rhombus concavity is equivalent to nonnegativity of every unit-rhombus slack. -/
theorem isRhombusConcave_iff_rhombusSlack_nonneg [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (f : Vertex n → R) :
    IsRhombusConcave f ↔ ∀ ⦃a b c d : Vertex n⦄, IsRhombus a b c d → 0 ≤ rhombusSlack f a b c d :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => sub_nonneg.symm

theorem isRhombusConcave [AddCommGroup R] [PartialOrder R] (h : Hive n R) :
    IsRhombusConcave (h : Vertex n → R) :=
  fun _ _ _ _ hr => h.le_of_isRhombus hr

theorem rhombusSlack_nonneg [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (h : Hive n R) {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    0 ≤ rhombusSlack h a b c d :=
  sub_nonneg.mpr (h.le_of_isRhombus hr)

/-- A barycentric-affine function `p ↦ c₀ + p.x • α + p.y • β + p.z • γ` on `Vertex n`. -/
def barycentricLinear [AddCommGroup R] (c₀ α β γ : R) (p : Vertex n) : R :=
  c₀ + p.x • α + p.y • β + p.z • γ

@[simp]
theorem barycentricLinear_apply [AddCommGroup R] (c₀ α β γ : R) (p : Vertex n) :
    barycentricLinear c₀ α β γ p = c₀ + p.x • α + p.y • β + p.z • γ := (rfl)

/-- Every barycentric-affine function has zero slack on every unit rhombus, because opposite
corners share the same midpoint in barycentric coordinates. -/
@[simp]
theorem rhombusSlack_barycentricLinear [AddCommGroup R] (c₀ α β γ : R)
    {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    rhombusSlack (barycentricLinear c₀ α β γ) a b c d = 0 := by
  have hx : (a.x + c.x) • α = (b.x + d.x) • α := congrArg (· • α) hr.midpoint_x
  have hy : (a.y + c.y) • β = (b.y + d.y) • β := congrArg (· • β) hr.midpoint_y
  have hz : (a.z + c.z) • γ = (b.z + d.z) • γ := congrArg (· • γ) hr.midpoint_z
  simp only [add_nsmul] at hx hy hz
  rw [rhombusSlack_def, barycentricLinear_apply, barycentricLinear_apply,
    barycentricLinear_apply, barycentricLinear_apply]
  calc (c₀ + a.x • α + a.y • β + a.z • γ) + (c₀ + c.x • α + c.y • β + c.z • γ) -
        ((c₀ + b.x • α + b.y • β + b.z • γ) + (c₀ + d.x • α + d.y • β + d.z • γ))
      = ((a.x • α + c.x • α) - (b.x • α + d.x • α)) +
        ((a.y • β + c.y • β) - (b.y • β + d.y • β)) +
        ((a.z • γ + c.z • γ) - (b.z • γ + d.z • γ)) := by abel
    _ = 0 := by rw [hx, hy, hz, sub_self, sub_self, sub_self, add_zero, add_zero]

/-- Adding a barycentric-affine function leaves all unit-rhombus slacks unchanged. -/
@[simp]
theorem rhombusSlack_add_barycentricLinear [AddCommGroup R] (f : Vertex n → R) (c₀ α β γ : R)
    {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    rhombusSlack (f + barycentricLinear c₀ α β γ) a b c d = rhombusSlack f a b c d := by
  rw [rhombusSlack_add, rhombusSlack_barycentricLinear c₀ α β γ hr, add_zero]

/-- Rhombus concavity is invariant under adding any barycentric-affine function. -/
@[simp]
theorem isRhombusConcave_add_barycentricLinear_iff [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (f : Vertex n → R) (c₀ α β γ : R) :
    IsRhombusConcave (f + barycentricLinear c₀ α β γ) ↔ IsRhombusConcave f := by
  simp only [isRhombusConcave_iff_rhombusSlack_nonneg]
  exact forall₄_congr fun _ _ _ _ => imp_congr_right fun hr => by
    rw [rhombusSlack_add_barycentricLinear f c₀ α β γ hr]

theorem isRhombusConcave_barycentricLinear [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (c₀ α β γ : R) :
    IsRhombusConcave (barycentricLinear c₀ α β γ : Vertex n → R) := by
  simpa using (isRhombusConcave_add_barycentricLinear_iff (0 : Vertex n → R) c₀ α β γ).mpr
    fun _ _ _ _ _ => by simp

/-- Normalize an unnormalized rhombus-concave function by subtracting its value at `A = (n, 0, 0)`.
-/
def ofRhombusConcave [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (f : Vertex n → R) (hf : IsRhombusConcave f) : Hive n R where
  value p := f p - f (Vertex.cornerA n)
  value_cornerA' := sub_self _
  le_of_isRhombus' {a b c d} hr := by
    have h := hf hr
    calc (f b - f (Vertex.cornerA n)) + (f d - f (Vertex.cornerA n))
        = (f b + f d) - (f (Vertex.cornerA n) + f (Vertex.cornerA n)) := by abel
      _ ≤ (f a + f c) - (f (Vertex.cornerA n) + f (Vertex.cornerA n)) := sub_le_sub_right h _
      _ = (f a - f (Vertex.cornerA n)) + (f c - f (Vertex.cornerA n)) := by abel

@[simp]
theorem ofRhombusConcave_apply [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (f : Vertex n → R) (hf : IsRhombusConcave f) (p : Vertex n) :
    ofRhombusConcave f hf p = f p - f (Vertex.cornerA n) := (rfl)

@[simp]
theorem ofRhombusConcave_coe [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (h : Hive n R) : ofRhombusConcave h h.isRhombusConcave = h := by
  ext p; simp

/-- Two unnormalized hives normalize to the same `Hive` if and only if they differ by an additive
constant. -/
theorem ofRhombusConcave_eq_iff [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    {f₁ f₂ : Vertex n → R} (hf₁ : IsRhombusConcave f₁) (hf₂ : IsRhombusConcave f₂) :
    ofRhombusConcave f₁ hf₁ = ofRhombusConcave f₂ hf₂ ↔ ∃ c : R, ∀ p, f₁ p = f₂ p + c := by
  constructor
  · intro h
    refine ⟨f₁ (Vertex.cornerA n) - f₂ (Vertex.cornerA n), fun p => ?_⟩
    have hp : f₁ p - f₁ (Vertex.cornerA n) = f₂ p - f₂ (Vertex.cornerA n) :=
      congrArg (fun k : Hive n R => k p) h
    calc f₁ p = (f₁ p - f₁ (Vertex.cornerA n)) + f₁ (Vertex.cornerA n) := by abel
      _ = (f₂ p - f₂ (Vertex.cornerA n)) + f₁ (Vertex.cornerA n) := by rw [hp]
      _ = f₂ p + (f₁ (Vertex.cornerA n) - f₂ (Vertex.cornerA n)) := by abel
  · rintro ⟨c, hc⟩
    ext p
    simp only [ofRhombusConcave_apply, hc]
    abel

end Gauge

/-! ### Monoid structure, nonnegative scaling, affine hives, and subtriangle restriction -/

section Algebra

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]

instance : Zero (Hive n R) where
  zero := ⟨0, rfl, fun _ => by simp⟩

instance : Inhabited (Hive n R) := ⟨0⟩

@[simp] theorem coe_zero : ⇑(0 : Hive n R) = 0 := (rfl)
@[simp] theorem zero_apply (p : Vertex n) : (0 : Hive n R) p = 0 := (rfl)

/-- Nonnegative scalars from a partially ordered semiring act on hives. -/
instance instSMulNonneg {S : Type*} [Semiring S] [PartialOrder S]
    [Module S R] [PosSMulMono S R] : SMul (Nonneg S) (Hive n R) where
  smul c h :=
    ⟨c.1 • ⇑h, by simp, fun {a b c' d} hr => by
      simp only [Pi.smul_apply, ← smul_add]
      exact smul_le_smul_of_nonneg_left (h.le_of_isRhombus hr) c.2⟩

@[simp]
theorem coe_smul_nonneg {S : Type*} [Semiring S] [PartialOrder S]
    [Module S R] [PosSMulMono S R] (c : Nonneg S) (h : Hive n R) :
    ⇑(c • h) = c.1 • ⇑h := (rfl)

@[simp]
theorem smul_nonneg_apply {S : Type*} [Semiring S] [PartialOrder S]
    [Module S R] [PosSMulMono S R] (c : Nonneg S) (h : Hive n R) (p : Vertex n) :
    (c • h) p = c.1 • h p := (rfl)

/-- Push a hive forward along an order-preserving additive monoid homomorphism. -/
def map {S : Type*} [AddCommGroup S] [PartialOrder S] (φ : R →+o S) (h : Hive n R) : Hive n S where
  value p := φ (h p)
  value_cornerA' := by simp
  le_of_isRhombus' hr := by
    simpa only [map_add] using OrderHomClass.mono φ (h.le_of_isRhombus hr)

@[simp]
theorem map_apply {S : Type*} [AddCommGroup S] [PartialOrder S]
    (φ : R →+o S) (h : Hive n R) (p : Vertex n) :
    h.map φ p = φ (h p) := (rfl)

section OrderedAdd

variable [IsOrderedAddMonoid R]

instance : Add (Hive n R) where
  add h₁ h₂ :=
    ⟨h₁ + h₂, by simp, fun {a b c d} hr => by
      simp only [Pi.add_apply]
      calc (h₁ b + h₂ b) + (h₁ d + h₂ d) = (h₁ b + h₁ d) + (h₂ b + h₂ d) := by abel
        _ ≤ (h₁ a + h₁ c) + (h₂ a + h₂ c) :=
            add_le_add (h₁.le_of_isRhombus hr) (h₂.le_of_isRhombus hr)
        _ = (h₁ a + h₂ a) + (h₁ c + h₂ c) := by abel⟩

@[simp] theorem coe_add (h₁ h₂ : Hive n R) : ⇑(h₁ + h₂) = ⇑h₁ + ⇑h₂ := (rfl)
@[simp] theorem add_apply (h₁ h₂ : Hive n R) (p : Vertex n) : (h₁ + h₂) p = h₁ p + h₂ p := (rfl)

instance : SMul ℕ (Hive n R) where
  smul k h :=
    ⟨k • ⇑h, by simp, fun {a b c d} hr => by
      simp only [Pi.smul_apply, ← smul_add]
      exact nsmul_le_nsmul_right (h.le_of_isRhombus hr) k⟩

@[simp] theorem coe_nsmul (k : ℕ) (h : Hive n R) : ⇑(k • h) = k • ⇑h := (rfl)
@[simp] theorem nsmul_apply (k : ℕ) (h : Hive n R) (p : Vertex n) : (k • h) p = k • h p := (rfl)

instance : AddCommMonoid (Hive n R) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

/-- Evaluation as an additive monoid homomorphism from `Hive n R` to lattice functions. -/
def coeAddMonoidHom (n : ℕ) (R : Type*) [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R] :
    Hive n R →+ (Vertex n → R) where
  toFun h := ⇑h
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coeAddMonoidHom_apply (h : Hive n R) : coeAddMonoidHom n R h = ⇑h := (rfl)

/-- Normalized affine hive `p ↦ p.y • β + p.z • γ`, vanishing at `A = (n, 0, 0)` and having zero
rhombus slack everywhere. -/
def affine (n : ℕ) (β γ : R) : Hive n R where
  value p := p.y • β + p.z • γ
  value_cornerA' := by simp
  le_of_isRhombus' hr := by
    have h := isRhombusConcave_barycentricLinear (n := n) (0 : R) 0 β γ hr
    simpa [barycentricLinear] using h

@[simp]
theorem affine_apply (β γ : R) (p : Vertex n) : affine n β γ p = p.y • β + p.z • γ := (rfl)

@[simp]
theorem rhombusSlack_affine (β γ : R) {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    rhombusSlack (affine n β γ) a b c d = 0 := by
  have h := rhombusSlack_barycentricLinear (n := n) (0 : R) 0 β γ hr
  simpa [barycentricLinear, rhombusSlack, affine_apply] using h

/-- Restrict a hive on `Δ_{m + k}` to the subtriangle of side length `k` translated by `p : Δ_m`,
normalizing at its top corner `p.add (cornerA k)`. -/
def subtriangle {m k : ℕ} (h : Hive (m + k) R) (p : Vertex m) : Hive k R :=
  ofRhombusConcave (fun q => h (p.add q)) fun _ _ _ _ hr => h.le_of_isRhombus (hr.add p)

@[simp]
theorem subtriangle_apply {m k : ℕ} (h : Hive (m + k) R) (p : Vertex m) (q : Vertex k) :
    h.subtriangle p q = h (p.add q) - h (p.add (Vertex.cornerA k)) := (rfl)

/-- Restriction to a translated subtriangle preserves every unit-rhombus slack. -/
@[simp]
theorem rhombusSlack_subtriangle {m k : ℕ} (h : Hive (m + k) R) (p : Vertex m)
    (a b c d : Vertex k) :
    rhombusSlack (h.subtriangle p) a b c d =
      rhombusSlack h (p.add a) (p.add b) (p.add c) (p.add d) := by
  simp only [rhombusSlack, subtriangle_apply]; abel

@[simp]
theorem subtriangle_zero {m k : ℕ} (p : Vertex m) :
    (0 : Hive (m + k) R).subtriangle p = 0 := by ext q; simp

theorem subtriangle_add {m k : ℕ} (h₁ h₂ : Hive (m + k) R) (p : Vertex m) :
    (h₁ + h₂).subtriangle p = h₁.subtriangle p + h₂.subtriangle p := by
  ext q; simp only [subtriangle_apply, add_apply]; abel

end OrderedAdd

end Algebra

section Cone

variable {n : ℕ}

/-- Embed `IntegerHive n` into `Hive n R` for any ordered ring `R` via `Int.cast`. -/
def ofInt (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] {n : ℕ} :
    IntegerHive n →+ Hive n R where
  toFun h := h.map
    { toFun := Int.cast
      map_zero' := Int.cast_zero
      map_add' := Int.cast_add
      monotone' := fun _ _ hle => Int.cast_mono hle }
  map_zero' := by ext p; simp
  map_add' _ _ := by ext p; simp

@[simp]
theorem ofInt_apply {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] (h : IntegerHive n)
    (p : Vertex n) : ofInt R h p = (h p : R) := (rfl)

/-- Canonical additive monoid embedding of integer hives into real hives. -/
abbrev toReal {n : ℕ} : IntegerHive n →+ RealHive n := ofInt ℝ

theorem ofInt_injective (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] [CharZero R]
    {n : ℕ} : Function.Injective (ofInt R (n := n)) := by
  intro h₁ h₂ heq
  ext p
  exact Int.cast_injective (congrArg (fun k : Hive n R => k p) heq)

/-- The pointed cone of normalized hives inside `Vertex n → R` over an ordered ring `R`. -/
def pointedCone (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] (n : ℕ) :
    PointedCone R (Vertex n → R) where
  carrier := {f | f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f}
  zero_mem' := ⟨rfl, fun _ _ _ _ _ => by simp⟩
  add_mem' {f g} hf hg := ⟨by simp [hf.1, hg.1], fun {a b c d} hr => by
    simp only [Pi.add_apply]
    calc (f b + g b) + (f d + g d) = (f b + f d) + (g b + g d) := by abel
      _ ≤ (f a + f c) + (g a + g c) := add_le_add (hf.2 hr) (hg.2 hr)
      _ = (f a + g a) + (f c + g c) := by abel⟩
  smul_mem' c f hf := ⟨by simp [hf.1], fun {a b c' d} hr => by
    change c.1 * f b + c.1 * f d ≤ c.1 * f a + c.1 * f c'
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hf.2 hr) c.2⟩

@[simp]
theorem mem_pointedCone_iff {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    {f : Vertex n → R} :
    f ∈ pointedCone R n ↔ f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f :=
  Iff.rfl

theorem coe_mem_pointedCone {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    (h : Hive n R) : (h : Vertex n → R) ∈ pointedCone R n :=
  ⟨h.apply_cornerA, h.isRhombusConcave⟩

end Cone

/-! ### Unit-edge lattice directions and mixed second differences -/

@[elab_as_elim]
private theorem fin3_cases {P : Fin 3 → Prop} (s : Fin 3) (h0 : P 0) (h1 : P 1) (h2 : P 2) : P s :=
  match s with
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2

section UnitSteps

/-- A vector `v : Fin 3 → ℤ` is a **unit lattice edge step** if its coordinates sum to `0` and its
barycentric squared norm is `2` (one `+1`, one `-1`, and one `0`). -/
def IsUnitStep (v : Fin 3 → ℤ) : Prop :=
  (∑ i, v i) = 0 ∧ (∑ i, v i ^ 2) = 2

/-- Vertex `q` is obtained from `p` by translating along `v : Fin 3 → ℤ` in barycentric
coordinates. -/
def HasStep {n : ℕ} (p q : Vertex n) (v : Fin 3 → ℤ) : Prop :=
  ∀ i, (q.coord i : ℤ) = (p.coord i : ℤ) + v i

theorem sqDist_of_hasStep {n : ℕ} {p q : Vertex n} {v : Fin 3 → ℤ} (h : HasStep p q v) :
    p.sqDist q = ∑ i, v i ^ 2 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp only [Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two] at h0 h1 h2
  rw [Vertex.sqDist_def, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- Four lattice points `p`, `pv = p + v`, `pw = p + w`, `pvw = p + v + w` generated by two unit
steps `v, w` form a unit rhombus `(pv, p, pw, pvw)` with obtuse corners `pv, pw` if and only if
`∑ i, v i * w i = 1`. -/
theorem isRhombus_of_hasStep_iff {n : ℕ} {p pv pw pvw : Vertex n} {v w : Fin 3 → ℤ}
    (hv : IsUnitStep v) (hw : IsUnitStep w)
    (hpv : HasStep p pv v) (hpw : HasStep p pw w) (hpvw : HasStep p pvw (v + w)) :
    IsRhombus pv p pw pvw ↔ (∑ i, v i * w i) = 1 := by
  have hpv0 := hpv 0; have hpv1 := hpv 1; have hpv2 := hpv 2
  have hpw0 := hpw 0; have hpw1 := hpw 1; have hpw2 := hpw 2
  have hpvw0 := hpvw 0; have hpvw1 := hpvw 1; have hpvw2 := hpvw 2
  simp only [Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two, Pi.add_apply]
    at hpv0 hpv1 hpv2 hpw0 hpw1 hpw2 hpvw0 hpvw1 hpvw2
  have hv2 : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 2 := by simpa [Fin.sum_univ_three] using hv.2
  have hw2 : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 2 := by simpa [Fin.sum_univ_three] using hw.2
  have hshort : pv.sqDist pw = 4 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2) := by
    rw [Vertex.sqDist_def, hpv0, hpv1, hpv2, hpw0, hpw1, hpw2]
    linear_combination hv2 + hw2
  have hlong : p.sqDist pvw = 4 + 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2) := by
    rw [Vertex.sqDist_def, hpvw0, hpvw1, hpvw2]
    linear_combination hv2 + hw2
  constructor
  · intro hr
    have hs := hr.short
    rw [hshort] at hs
    simpa [Fin.sum_univ_three] using (by omega : v 0 * w 0 + v 1 * w 1 + v 2 * w 2 = 1)
  · intro hdot
    have hdot' : v 0 * w 0 + v 1 * w 1 + v 2 * w 2 = 1 := by
      simpa [Fin.sum_univ_three] using hdot
    refine
      { midpoint_x := by omega
        midpoint_y := by omega
        midpoint_z := by omega
        short := by omega
        long := by omega
        side_ab := by rw [Vertex.sqDist_comm, sqDist_of_hasStep hpv]; exact hv.2
        side_bc := by rw [sqDist_of_hasStep hpw]; exact hw.2
        side_cd := ?_
        side_da := ?_ }
    · have hstep : HasStep pw pvw v := fun i =>
        fin3_cases i (by simp; omega) (by simp; omega) (by simp; omega)
      rw [sqDist_of_hasStep hstep]
      exact hv.2
    · have hstep : HasStep pv pvw w := fun i =>
        fin3_cases i (by simp; omega) (by simp; omega) (by simp; omega)
      rw [Vertex.sqDist_comm, sqDist_of_hasStep hstep]
      exact hw.2

/-- Along unit lattice edge directions `v, w` of inner product `1`, a hive has nonpositive mixed
second forward difference `D_v D_w h(p) = (h(p + v + w) - h(p + w)) - (h(p + v) - h(p)) ≤ 0`. -/
theorem mixedDiff_nonpos_of_isUnitStep {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (h : Hive n R) {p pv pw pvw : Vertex n} {v w : Fin 3 → ℤ}
    (hv : IsUnitStep v) (hw : IsUnitStep w) (hdot : (∑ i, v i * w i) = 1)
    (hpv : HasStep p pv v) (hpw : HasStep p pw w) (hpvw : HasStep p pvw (v + w)) :
    (h pvw - h pw) - (h pv - h p) ≤ 0 := by
  have hr : IsRhombus pv p pw pvw := (isRhombus_of_hasStep_iff hv hw hpv hpw hpvw).mpr hdot
  have hle := h.le_of_isRhombus hr
  calc (h pvw - h pw) - (h pv - h p) = (h p + h pvw) - (h pv + h pw) := by abel
    _ ≤ (h pv + h pw) - (h pv + h pw) := sub_le_sub_right hle _
    _ = 0 := sub_self _

private theorem abs_le_one_of_sq_le_two {z : ℤ} (h : z ^ 2 ≤ 2) : -1 ≤ z ∧ z ≤ 1 := by
  constructor
  · by_contra! hz
    have h4 : 0 ≤ (z + 2) * (z - 2) := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    have h4' : 4 ≤ z ^ 2 := by linear_combination h4
    omega
  · by_contra! hz
    have h4 : 0 ≤ (z - 2) * (z + 2) := mul_nonneg (by omega) (by omega)
    have h4' : 4 ≤ z ^ 2 := by linear_combination h4
    omega

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
    have hvx : -1 ≤ vx ∧ vx ≤ 1 :=
      abs_le_one_of_sq_le_two
        (by linarith [sq_nonneg ((a.y : ℤ) - b.y), sq_nonneg ((a.z : ℤ) - b.z)])
    have hwx : -1 ≤ wx ∧ wx ≤ 1 :=
      abs_le_one_of_sq_le_two
        (by linarith [sq_nonneg ((c.y : ℤ) - b.y), sq_nonneg ((c.z : ℤ) - b.z)])
    have hdiff : -1 ≤ vx - wx ∧ vx - wx ≤ 1 := by
      have heq : vx - wx = (a.x : ℤ) - c.x := by omega
      rw [heq]
      exact abs_le_one_of_sq_le_two
        (by linarith [sq_nonneg ((a.y : ℤ) - c.y), sq_nonneg ((a.z : ℤ) - c.z)])
    have hvwx : 0 ≤ vx * wx := by
      rcases (by omega : vx = -1 ∨ vx = 0 ∨ vx = 1) with hv | hv | hv <;> rw [hv] <;> omega
    have hident :
        ((49 - (a.x : ℤ) ^ 2) + (49 - (c.x : ℤ) ^ 2)) -
          ((49 - (b.x : ℤ) ^ 2) + (49 - (d.x : ℤ) ^ 2)) = 2 * (vx * wx) := by
      have hd : (d.x : ℤ) = a.x + c.x - b.x := by omega
      rw [hd]; simp only [vx, wx]; ring
    linarith

/-- On `Δ₇`, `counterexampleSeven` is a hive, yet at `p = (3, 4, 0)` the non-unit steps
`v = (2, -3, 1)` and `w = (-3, -1, 4)` satisfy `∑ vᵢ wᵢ = 1` and have positive mixed second
difference `+12`. -/
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
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp
  · change ((49 - (2 : ℤ) ^ 2) - (49 - (0 : ℤ) ^ 2)) -
      ((49 - (5 : ℤ) ^ 2) - (49 - (3 : ℤ) ^ 2)) = 12
    norm_num

end UnitSteps

/-! ### Clockwise boundary points, linear boundary restriction, and `boundary_antitone` -/

namespace Vertex

/-- The `k`-th lattice point along side `s` of the clockwise perimeter `A → B → C → A`:
`s = 0` traverses `A → B`, `s = 1` traverses `B → C`, and `s = 2` traverses `C → A`. -/
def edgePoint (n : ℕ) (s : Fin 3) (k : Fin (n + 1)) : Vertex n :=
  match s with
  | ⟨0, _⟩ => ⟨n - k.val, k.val, 0, by omega⟩
  | ⟨1, _⟩ => ⟨0, n - k.val, k.val, by omega⟩
  | ⟨2, _⟩ => ⟨k.val, 0, n - k.val, by omega⟩

@[simp]
theorem edgePoint_zero_x (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 0 k).x = n - k.val := (rfl)
@[simp] theorem edgePoint_zero_y (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 0 k).y = k.val := (rfl)
@[simp] theorem edgePoint_zero_z (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 0 k).z = 0 := (rfl)

@[simp] theorem edgePoint_one_x (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 1 k).x = 0 := (rfl)
@[simp]
theorem edgePoint_one_y (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 1 k).y = n - k.val := (rfl)
@[simp] theorem edgePoint_one_z (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 1 k).z = k.val := (rfl)

@[simp] theorem edgePoint_two_x (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 2 k).x = k.val := (rfl)
@[simp] theorem edgePoint_two_y (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 2 k).y = 0 := (rfl)
@[simp]
theorem edgePoint_two_z (n : ℕ) (k : Fin (n + 1)) : (edgePoint n 2 k).z = n - k.val := (rfl)

@[simp] theorem edgePoint_zero_zero (n : ℕ) : edgePoint n 0 0 = cornerA n := by ext <;> simp

@[simp]
theorem edgePoint_two_last (n : ℕ) : edgePoint n 2 (Fin.last n) = cornerA n := by ext <;> simp

/-- Each side ends where the next clockwise side begins. -/
@[simp]
theorem edgePoint_add_one_zero (n : ℕ) (s : Fin 3) :
    edgePoint n (s + 1) 0 = edgePoint n s (Fin.last n) := by
  fin_cases s <;> ext <;> simp [edgePoint]

/-- Clockwise rotation advances the side index `s` by `1` in `Fin 3`. -/
@[simp]
theorem rotate_edgePoint (n : ℕ) (s : Fin 3) (k : Fin (n + 1)) :
    (edgePoint n s k).rotate = edgePoint n (s + 1) k := by
  fin_cases s <;> ext <;> simp [edgePoint]

/-- Reflection across `A` reverses both the side index (`0 ↔ 2`, fixing `1`) and the position along
each side. -/
@[simp]
theorem reflect_edgePoint (n : ℕ) (s : Fin 3) (k : Fin (n + 1)) :
    (edgePoint n s k).reflect = edgePoint n s.rev k.rev := by
  fin_cases s <;> ext <;> simp [edgePoint, Fin.val_rev] <;> omega

theorem edgePoint_injective (n : ℕ) (s : Fin 3) : Function.Injective (edgePoint n s) := by
  intro j k h
  fin_cases s
  · exact Fin.ext (congrArg Vertex.y h)
  · exact Fin.ext (congrArg Vertex.z h)
  · exact Fin.ext (congrArg Vertex.x h)

end Vertex

section Boundary

variable {n : ℕ} {R : Type*}

/-- The clockwise edge-difference operator on the ambient space of lattice functions
`Vertex n → R`, an `S`-linear map before restricting to the hive cone. -/
def boundaryLinear (S : Type*) (n : ℕ) (R : Type*) [Semiring S] [AddCommGroup R] [Module S R] :
    (Vertex n → R) →ₗ[S] (Fin 3 → Fin n → R) where
  toFun f s i := f (Vertex.edgePoint n s i.succ) - f (Vertex.edgePoint n s i.castSucc)
  map_add' _ _ := by ext s i; simp only [Pi.add_apply]; abel
  map_smul' _ _ := by ext s i; simp [smul_sub]

@[simp]
theorem boundaryLinear_apply (S : Type*) [Semiring S] [AddCommGroup R] [Module S R]
    (f : Vertex n → R) (s : Fin 3) (i : Fin n) :
    boundaryLinear S n R f s i =
      f (Vertex.edgePoint n s i.succ) - f (Vertex.edgePoint n s i.castSucc) := (rfl)

/-- Along the first `k` steps of side `s`, the edge differences of `f` telescope to
`f(edgePoint n s k) - f(edgePoint n s 0)`. -/
theorem sum_boundaryLinear_lt [AddCommGroup R] (f : Vertex n → R) (s : Fin 3) (k : ℕ)
    (hk : k ≤ n) :
    (∑ i : Fin n with i.val < k, boundaryLinear ℤ n R f s i) =
      f (Vertex.edgePoint n s ⟨k, by omega⟩) - f (Vertex.edgePoint n s 0) := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hsplit :
        ({i : Fin n | i.val < m + 1} : Finset (Fin n)) =
          insert ⟨m, by omega⟩ ({i : Fin n | i.val < m} : Finset (Fin n)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotmem : (⟨m, by omega⟩ : Fin n) ∉ ({i : Fin n | i.val < m} : Finset (Fin n)) := by simp
    rw [hsplit, Finset.sum_insert hnotmem, ih (by omega), boundaryLinear_apply]
    have hsucc : (⟨m, by omega⟩ : Fin n).succ = ⟨m + 1, by omega⟩ := rfl
    have hcast : (⟨m, by omega⟩ : Fin n).castSucc = ⟨m, by omega⟩ := rfl
    rw [hsucc, hcast]
    abel

/-- Along side `s`, the `n` edge differences telescope to the difference between the two corners of
that side. -/
theorem sum_boundaryLinear_side [AddCommGroup R] (f : Vertex n → R) (s : Fin 3) :
    (∑ i : Fin n, boundaryLinear ℤ n R f s i) =
      f (Vertex.edgePoint n s (Fin.last n)) - f (Vertex.edgePoint n s 0) := by
  have hall : ({i : Fin n | i.val < n} : Finset (Fin n)) = Finset.univ := by ext i; simp
  simpa [hall, Fin.last] using sum_boundaryLinear_lt f s n le_rfl

/-- The cyclic trace `∑ s, ∑ i, boundaryLinear f s i` vanishes for every lattice function `f`. -/
theorem sum_boundaryLinear [AddCommGroup R] (f : Vertex n → R) :
    (∑ s : Fin 3, ∑ i : Fin n, boundaryLinear ℤ n R f s i) = 0 := by
  simp only [Fin.sum_univ_three, sum_boundaryLinear_side]
  have h01 : Vertex.edgePoint n 1 0 = Vertex.edgePoint n 0 (Fin.last n) :=
    Vertex.edgePoint_add_one_zero n 0
  have h12 : Vertex.edgePoint n 2 0 = Vertex.edgePoint n 1 (Fin.last n) :=
    Vertex.edgePoint_add_one_zero n 1
  rw [h01, h12, Vertex.edgePoint_zero_zero, Vertex.edgePoint_two_last]
  abel

/-- The clockwise cyclic boundary of a hive: `s = 0`, `1`, `2` record the successive edge
differences along `A → B`, `B → C`, and `C → A`. -/
def boundary [AddCommGroup R] [PartialOrder R] (h : Hive n R) : Fin 3 → Fin n → R :=
  boundaryLinear ℤ n R h

theorem boundary_def [AddCommGroup R] [PartialOrder R] (h : Hive n R) :
    h.boundary = boundaryLinear ℤ n R h := (rfl)

theorem boundary_apply [AddCommGroup R] [PartialOrder R] (h : Hive n R) (s : Fin 3) (i : Fin n) :
    h.boundary s i =
      h (Vertex.edgePoint n s i.succ) - h (Vertex.edgePoint n s i.castSucc) := (rfl)

@[simp]
theorem boundary_zero [AddCommGroup R] [PartialOrder R] :
    (0 : Hive n R).boundary = 0 :=
  map_zero (boundaryLinear ℤ n R)

@[simp]
theorem boundary_add [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (h₁ h₂ : Hive n R) : (h₁ + h₂).boundary = h₁.boundary + h₂.boundary :=
  map_add (boundaryLinear ℤ n R) ⇑h₁ ⇑h₂

@[simp]
theorem boundary_nsmul [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (k : ℕ) (h : Hive n R) : (k • h).boundary = k • h.boundary := by
  ext s i; simp [boundary_apply, smul_sub]

@[simp]
theorem boundary_smul_nonneg {S : Type*} [Semiring S] [PartialOrder S]
    [AddCommGroup R] [PartialOrder R] [Module S R] [PosSMulMono S R]
    (c : Nonneg S) (h : Hive n R) :
    (c • h).boundary = c.1 • h.boundary := by
  ext s i; simp [boundary_apply, smul_sub]

@[simp]
theorem boundary_map {S : Type*} [AddCommGroup R] [PartialOrder R] [AddCommGroup S] [PartialOrder S]
    (φ : R →+o S) (h : Hive n R) (s : Fin 3) (i : Fin n) :
    (h.map φ).boundary s i = φ (h.boundary s i) := by
  simp [boundary_apply, map_sub]

@[simp]
theorem boundary_ofInt [Ring R] [PartialOrder R] [IsOrderedRing R] (h : IntegerHive n)
    (s : Fin 3) (i : Fin n) :
    (ofInt R h).boundary s i = (h.boundary s i : R) := by
  simp [boundary_apply]

@[simp]
theorem boundary_affine [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (β γ : R) :
    (affine n β γ).boundary = ![fun _ => β, fun _ => γ - β, fun _ => -γ] := by
  ext s i
  induction s using fin3_cases
  · simp [boundary_apply, affine_apply, add_nsmul]
  · have hsub : n - i.val = (n - (i.val + 1)) + 1 := by omega
    change ((n - (i.val + 1)) • β + (i.val + 1) • γ) - ((n - i.val) • β + i.val • γ) = γ - β
    rw [hsub, add_nsmul, add_nsmul, one_nsmul, one_nsmul]
    abel
  · have hsub : n - i.val = (n - (i.val + 1)) + 1 := by omega
    change (0 • β + (n - (i.val + 1)) • γ) - (0 • β + (n - i.val) • γ) = -γ
    rw [zero_nsmul, zero_add, zero_add, hsub, add_nsmul, one_nsmul]
    abel

/-- The cyclic trace `∑ s, ∑ i, h.boundary s i` of any hive vanishes. -/
@[simp]
theorem sum_boundary [AddCommGroup R] [PartialOrder R] (h : Hive n R) :
    (∑ s : Fin 3, ∑ i : Fin n, h.boundary s i) = 0 :=
  sum_boundaryLinear h

/-- Value of a hive at the `k`-th vertex of side `A → B` (`s = 0`) in terms of its boundary. -/
theorem apply_edgePoint_zero [AddCommGroup R] [PartialOrder R] (h : Hive n R) (k : Fin (n + 1)) :
    h (Vertex.edgePoint n 0 k) = ∑ i : Fin n with i.val < k.val, h.boundary 0 i := by
  have ht := sum_boundaryLinear_lt (⇑h) 0 k.val (Nat.le_of_lt_succ k.isLt)
  rw [Vertex.edgePoint_zero_zero, h.apply_cornerA, sub_zero] at ht
  exact ht.symm

/-- Value of a hive at the `k`-th vertex of side `B → C` (`s = 1`) in terms of its boundary. -/
theorem apply_edgePoint_one [AddCommGroup R] [PartialOrder R] (h : Hive n R) (k : Fin (n + 1)) :
    h (Vertex.edgePoint n 1 k) =
      (∑ i : Fin n, h.boundary 0 i) + ∑ i : Fin n with i.val < k.val, h.boundary 1 i := by
  have ht1 := sum_boundaryLinear_lt (⇑h) 1 k.val (Nat.le_of_lt_succ k.isLt)
  have ht0 := sum_boundaryLinear_side (⇑h) 0
  rw [Vertex.edgePoint_zero_zero, h.apply_cornerA, sub_zero,
    ← Vertex.edgePoint_add_one_zero n 0] at ht0
  change (∑ i : Fin n, h.boundary 0 i) = h (Vertex.edgePoint n 1 0) at ht0
  change (∑ i : Fin n with i.val < k.val, h.boundary 1 i) =
    h (Vertex.edgePoint n 1 k) - h (Vertex.edgePoint n 1 0) at ht1
  rw [ht0, ht1]
  abel

/-- Value of a hive at the `k`-th vertex of side `C → A` (`s = 2`) in terms of its boundary:
integrating backwards from `h(A) = 0`. -/
theorem apply_edgePoint_two [AddCommGroup R] [PartialOrder R] (h : Hive n R) (k : Fin (n + 1)) :
    h (Vertex.edgePoint n 2 k) = -∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i := by
  have hcompl :
      (∑ i : Fin n with i.val < k.val, h.boundary 2 i) +
        (∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i) =
      ∑ i : Fin n, h.boundary 2 i := by
    simpa [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < k.val) (h.boundary 2)
  have ht := sum_boundaryLinear_lt (⇑h) 2 k.val (Nat.le_of_lt_succ k.isLt)
  have hfull := sum_boundaryLinear_side (⇑h) 2
  rw [Vertex.edgePoint_two_last, h.apply_cornerA, zero_sub] at hfull
  change (∑ i : Fin n with i.val < k.val, h.boundary 2 i) =
    h (Vertex.edgePoint n 2 k) - h (Vertex.edgePoint n 2 0) at ht
  change (∑ i : Fin n, h.boundary 2 i) = -h (Vertex.edgePoint n 2 0) at hfull
  rw [ht, hfull] at hcompl
  calc h (Vertex.edgePoint n 2 k)
      = ((h (Vertex.edgePoint n 2 k) - h (Vertex.edgePoint n 2 0)) +
          ∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i) -
        (-h (Vertex.edgePoint n 2 0)) -
        ∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i := by abel
    _ = (-h (Vertex.edgePoint n 2 0)) - (-h (Vertex.edgePoint n 2 0)) -
        ∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i := by rw [hcompl]
    _ = -∑ i : Fin n with k.val ≤ i.val, h.boundary 2 i := by abel

@[simp]
theorem boundaryLinear_coe (S : Type*) [Semiring S] [AddCommGroup R] [PartialOrder R] [Module S R]
    (h : Hive n R) : boundaryLinear S n R h = h.boundary := by
  ext s i
  rw [boundaryLinear_apply, boundary_apply]

/-- Side `0` edge differences of any rhombus-concave function are antitone: at each interior edge
vertex, adding the two unit rhombi sharing the adjacent interior triangle yields concavity along the
edge. -/
theorem antitone_boundaryLinear_zero_of_isRhombusConcave [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] {f : Vertex n → R} (hf : IsRhombusConcave f) :
    Antitone (boundaryLinear ℤ n R f 0) := by
  match n with
  | 0 => exact Subsingleton.antitone _
  | 1 => exact Subsingleton.antitone _
  | k + 2 =>
    rw [Fin.antitone_iff_succ_le]
    intro i
    let t : Vertex k := ⟨k - i.val, i.val, 0, by omega⟩
    have hp₀ : t.add (Vertex.cornerA 2) = Vertex.edgePoint (k + 2) 0 i.castSucc.castSucc := by
      ext <;> simp [t, Vertex.edgePoint]; omega
    have hp₁ : t.add ⟨1, 1, 0, rfl⟩ = Vertex.edgePoint (k + 2) 0 i.castSucc.succ := by
      ext <;> simp [t, Vertex.edgePoint]; omega
    have hp₁' : t.add (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate =
        Vertex.edgePoint (k + 2) 0 i.castSucc.succ := by
      ext <;> simp [t, Vertex.edgePoint]; omega
    have hp₂ : t.add (Vertex.cornerA 2).rotate = Vertex.edgePoint (k + 2) 0 i.succ.succ := by
      ext <;> simp [t, Vertex.edgePoint]
    have hq₀ : t.add (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate = t.add ⟨1, 0, 1, rfl⟩ := by
      ext <;> simp
    have hq₁ : t.add (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate = t.add ⟨0, 1, 1, rfl⟩ := by
      ext <;> simp
    have h₁ := hf (isRhombus_at_cornerA.add t)
    have h₂ := hf (isRhombus_at_cornerA.rotate.swap_opposite.reverse.add t)
    rw [hp₀, hp₁] at h₁
    rw [hp₂, hq₀, hp₁', hq₁] at h₂
    set q₀ := t.add ⟨1, 0, 1, rfl⟩
    set q₁ := t.add ⟨0, 1, 1, rfl⟩
    set p₀ := Vertex.edgePoint (k + 2) 0 i.castSucc.castSucc
    set p₁ := Vertex.edgePoint (k + 2) 0 i.castSucc.succ
    set p₂ := Vertex.edgePoint (k + 2) 0 i.succ.succ
    have hsum : (f p₀ + f p₂) + (f q₀ + f q₁) ≤ (f p₁ + f p₁) + (f q₀ + f q₁) := by
      calc (f p₀ + f p₂) + (f q₀ + f q₁) = (f p₀ + f q₁) + (f p₂ + f q₀) := by abel
        _ ≤ (f p₁ + f q₀) + (f p₁ + f q₁) := add_le_add h₁ h₂
        _ = (f p₁ + f p₁) + (f q₀ + f q₁) := by abel
    have hconc : f p₀ + f p₂ ≤ f p₁ + f p₁ := le_of_add_le_add_right hsum
    change f p₂ - f p₁ ≤ f p₁ - f p₀
    calc f p₂ - f p₁ = (f p₀ + f p₂) - (f p₀ + f p₁) := by abel
      _ ≤ (f p₁ + f p₁) - (f p₀ + f p₁) := sub_le_sub_right hconc _
      _ = f p₁ - f p₀ := by abel

/-- **Each boundary side of a hive is antitone**: for every hive with values in an ordered abelian
group and every side `s : Fin 3`, the successive clockwise edge differences `h.boundary s` decrease
weakly. -/
theorem boundary_antitone [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (h : Hive n R) (s : Fin 3) : Antitone (h.boundary s) := by
  induction s using fin3_cases
  · exact antitone_boundaryLinear_zero_of_isRhombusConcave h.isRhombusConcave
  · have hf₁ : IsRhombusConcave (fun p : Vertex n => h p.rotate) :=
      fun _ _ _ _ hr => h.le_of_isRhombus hr.rotate
    have heq : h.boundary 1 = boundaryLinear ℤ n R (fun p => h p.rotate) 0 := by
      ext i; simp [boundary_apply, boundaryLinear_apply, Vertex.rotate_edgePoint]
    rw [heq]
    exact antitone_boundaryLinear_zero_of_isRhombusConcave hf₁
  · have hf₂ : IsRhombusConcave (fun p : Vertex n => h p.rotate.rotate) :=
      fun _ _ _ _ hr => h.le_of_isRhombus hr.rotate.rotate
    have heq : h.boundary 2 = boundaryLinear ℤ n R (fun p => h p.rotate.rotate) 0 := by
      ext i; simp [boundary_apply, boundaryLinear_apply, Vertex.rotate_edgePoint]
    rw [heq]
    exact antitone_boundaryLinear_zero_of_isRhombusConcave hf₂

/-- Side `s` of an integer hive packaged as a `TauCeti.DominantWeight`. -/
def boundaryWeight (h : IntegerHive n) (s : Fin 3) : DominantWeight n :=
  ⟨h.boundary s, h.boundary_antitone s⟩

@[simp]
theorem coe_boundaryWeight (h : IntegerHive n) (s : Fin 3) :
    (h.boundaryWeight s : Fin n → ℤ) = h.boundary s := (rfl)

/-- The cyclic boundary `(λ, μ, γ*)` whose integer hives count the tensor-product multiplicity of
`V_γ` in `V_λ ⊗ V_μ`. -/
def productBoundary (lam μ γ : DominantWeight n) : Fin 3 → Fin n → ℤ :=
  ![lam.1, μ.1, γ.dual.1]

@[simp] theorem productBoundary_zero (lam μ γ : DominantWeight n) :
    productBoundary lam μ γ 0 = lam.1 := (rfl)

@[simp] theorem productBoundary_one (lam μ γ : DominantWeight n) :
    productBoundary lam μ γ 1 = μ.1 := (rfl)

@[simp] theorem productBoundary_two (lam μ γ : DominantWeight n) :
    productBoundary lam μ γ 2 = γ.dual.1 := (rfl)

/-- Cyclic trace zero for `productBoundary lam μ γ` is central-degree conservation
`|λ| + |μ| = |γ|`. -/
theorem sum_productBoundary_eq_zero_iff (lam μ γ : DominantWeight n) :
    (∑ s : Fin 3, ∑ i : Fin n, productBoundary lam μ γ s i) = 0 ↔
      (∑ i, lam.1 i) + (∑ i, μ.1 i) = ∑ i, γ.1 i := by
  simp only [Fin.sum_univ_three, productBoundary_zero, productBoundary_one, productBoundary_two,
    DominantWeight.sum_dual]
  omega

end Boundary

/-! ### Dihedral action on normalized hives and boundaries -/

section Symmetries

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]

/-- Clockwise rotation of a normalized hive: pull back along `Vertex.rotate` and re-normalize at
`A = (n, 0, 0)`. -/
def rotate [IsOrderedAddMonoid R] (h : Hive n R) : Hive n R :=
  ofRhombusConcave (fun p => h p.rotate) fun _ _ _ _ hr => h.le_of_isRhombus hr.rotate

@[simp]
theorem rotate_apply [IsOrderedAddMonoid R] (h : Hive n R) (p : Vertex n) :
    h.rotate p = h p.rotate - h (Vertex.cornerA n).rotate := (rfl)

/-- Three clockwise rotations return to the original normalized hive. -/
@[simp]
theorem rotate_rotate_rotate [IsOrderedAddMonoid R] (h : Hive n R) :
    h.rotate.rotate.rotate = h := by
  ext p
  simp only [rotate_apply, Vertex.rotate_rotate_rotate, apply_cornerA]
  abel

theorem rotate_injective [IsOrderedAddMonoid R] :
    Function.Injective (rotate (n := n) (R := R)) := by
  intro h₁ h₂ heq
  simpa using congrArg (fun k : Hive n R => k.rotate.rotate) heq

/-- Rotating a hive cyclically shifts its boundary sides:
`(h.rotate).boundary s = h.boundary (s + 1)`. -/
@[simp]
theorem boundary_rotate [IsOrderedAddMonoid R] (h : Hive n R) (s : Fin 3) :
    h.rotate.boundary s = h.boundary (s + 1) := by
  ext i; simp only [boundary_apply, rotate_apply, Vertex.rotate_edgePoint]; abel

@[simp]
theorem boundaryWeight_rotate (h : IntegerHive n) (s : Fin 3) :
    h.rotate.boundaryWeight s = h.boundaryWeight (s + 1) := by
  ext i; simp [coe_boundaryWeight]

/-- Reflection of a normalized hive across `A`: pull back along `Vertex.reflect`, which already
fixes `A = (n, 0, 0)`. -/
def reflect (h : Hive n R) : Hive n R where
  value p := h p.reflect
  value_cornerA' := by simp
  le_of_isRhombus' hr := h.le_of_isRhombus hr.reflect

@[simp] theorem reflect_apply (h : Hive n R) (p : Vertex n) : h.reflect p = h p.reflect := (rfl)

@[simp] theorem reflect_reflect (h : Hive n R) : h.reflect.reflect = h := by ext p; simp

theorem reflect_involutive : Function.Involutive (reflect (n := n) (R := R)) := reflect_reflect

theorem reflect_injective : Function.Injective (reflect (n := n) (R := R)) :=
  reflect_involutive.injective

@[simp]
theorem reflect_rotate_reflect_rotate [IsOrderedAddMonoid R] (h : Hive n R) :
    h.reflect.rotate.reflect.rotate = h := by
  ext p
  have hp : p.rotate.reflect.rotate.reflect = p := by ext <;> simp
  have hA : (Vertex.cornerA n).rotate.reflect.rotate.reflect = Vertex.cornerA n := by
    ext <;> simp
  simp only [rotate_apply, reflect_apply, hp, hA, apply_cornerA]
  abel

/-- Reflecting a hive reverses the order of the sides (`0 ↔ 2`, fixing `1`) and dualizes each side
weight (`w ↦ fun i => -w i.rev`). Thus `(λ, μ, ν)` becomes `(ν*, μ*, λ*)`. -/
@[simp]
theorem boundary_reflect (h : Hive n R) (s : Fin 3) (i : Fin n) :
    h.reflect.boundary s i = -h.boundary s.rev i.rev := by
  simp only [boundary_apply, reflect_apply, Vertex.reflect_edgePoint, ← Fin.rev_castSucc,
    ← Fin.rev_succ]
  abel

@[simp]
theorem boundaryWeight_reflect (h : IntegerHive n) (s : Fin 3) :
    h.reflect.boundaryWeight s = (h.boundaryWeight s.rev).dual := by
  ext i; simp [coe_boundaryWeight]

/-- Reflecting and rotating once sends a hive of boundary `(λ, μ, γ*)` to a hive of boundary
`(μ*, λ*, γ*)`, realizing contragredient duality of tensor-product multiplicities. -/
theorem boundary_reflect_rotate_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    h.reflect.rotate.boundary = productBoundary μ.dual lam.dual γ.dual := by
  ext s i
  induction s using fin3_cases <;> simp [hb]

end Symmetries

/-! ### Small-rank structure and chirality checks -/

section SmallRank

variable {R : Type*} [AddCommGroup R] [PartialOrder R]

/-- At size `0`, the unique normalized hive is `0` with empty boundary. -/
instance uniqueZero : Unique (Hive 0 R) where
  default := 0
  uniq h := by
    ext p
    have hp : p = Vertex.cornerA 0 := by have := p.sum_eq; ext <;> simp <;> omega
    rw [hp, h.apply_cornerA, zero_apply]

/-- At size `1`, there are no unit rhombi, so normalized hives are freely parameterized by their
values `(h B, h C) ∈ R × R`, with boundary `(b, c - b, -c)`. -/
def equivOne : Hive 1 R ≃ (R × R) where
  toFun h := (h ⟨0, 1, 0, rfl⟩, h ⟨0, 0, 1, rfl⟩)
  invFun bc :=
    { value p := if p.y = 1 then bc.1 else if p.z = 1 then bc.2 else 0
      value_cornerA' := by simp
      le_of_isRhombus' hr := absurd hr.two_le (by decide) }
  left_inv h := by
    ext p
    have hs := p.sum_eq
    rcases (by omega : p.x = 1 ∧ p.y = 0 ∧ p.z = 0 ∨
        p.x = 0 ∧ p.y = 1 ∧ p.z = 0 ∨ p.x = 0 ∧ p.y = 0 ∧ p.z = 1) with
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
    · have hp : p = Vertex.cornerA 1 := by ext <;> simp [hx, hy, hz]
      subst hp; simp
    · have hp : p = ⟨0, 1, 0, rfl⟩ := by ext <;> simp [hx, hy, hz]
      subst hp; rfl
    · have hp : p = ⟨0, 0, 1, rfl⟩ := by ext <;> simp [hx, hy, hz]
      subst hp; rfl
  right_inv _ := rfl

@[simp]
theorem equivOne_apply (h : Hive 1 R) :
    equivOne h = (h ⟨0, 1, 0, rfl⟩, h ⟨0, 0, 1, rfl⟩) := (rfl)

@[simp]
theorem equivOne_symm_apply (bc : R × R) (p : Vertex 1) :
    equivOne.symm bc p = if p.y = 1 then bc.1 else if p.z = 1 then bc.2 else 0 := (rfl)

@[simp]
theorem boundary_equivOne_symm (b c : R) :
    (equivOne.symm (b, c)).boundary = ![fun _ => b, fun _ => c - b, fun _ => -c] := by
  ext s i
  fin_cases i
  induction s using fin3_cases <;> simp [boundary_apply, Vertex.edgePoint]

/-- Chirality and sign check at size `2`: the unit rhombus `isRhombus_at_cornerA` with obtuse
corners `m_AB = (1, 1, 0)` and `m_CA = (1, 0, 1)` has slack `-(λ₂ + μ₁ + ν₂)` (in zero-indexed
coordinates, `-(B 0 1 + B 1 0 + B 2 1)`). -/
theorem rhombusSlack_at_cornerA_two (h : Hive 2 R) :
    rhombusSlack h ⟨1, 1, 0, rfl⟩ (Vertex.cornerA 2) ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ =
      -(h.boundary 0 1 + h.boundary 1 0 + h.boundary 2 1) := by
  have hmAB : (⟨1, 1, 0, rfl⟩ : Vertex 2) = Vertex.edgePoint 2 0 1 := rfl
  have hmBC : (⟨0, 1, 1, rfl⟩ : Vertex 2) = Vertex.edgePoint 2 1 1 := rfl
  have hmCA : (⟨1, 0, 1, rfl⟩ : Vertex 2) = Vertex.edgePoint 2 2 1 := rfl
  rw [rhombusSlack_def, h.apply_cornerA, hmAB, hmBC, hmCA,
    apply_edgePoint_zero, apply_edgePoint_one, apply_edgePoint_two]
  have hf0 : ({i : Fin 2 | i.val < (1 : Fin 3).val} : Finset (Fin 2)) = {0} := by decide
  have hf2 : ({i : Fin 2 | (1 : Fin 3).val ≤ i.val} : Finset (Fin 2)) = {1} := by decide
  rw [hf0, hf2, Fin.sum_univ_two]
  simp only [Finset.sum_singleton]
  abel

/-- Size-`2` check: the clockwise perimeter values `(0, 1, 1, 2, 2, 2)` form a normalized integer
hive with boundary `((1, 0), (1, 0), (0, -2)) = productBoundary (1, 0) (1, 0) (2, 0)` and unit
rhombus slacks `1, 0, 1` on the three orientations. -/
def exampleTwo : IntegerHive 2 where
  value p := (if p.x = 2 then 0 else 1) + (if p.z = 0 then 0 else 1)
  value_cornerA' := by simp
  le_of_isRhombus' {a b c d} hr := by
    have hshort := hr.short; rw [Vertex.sqDist_def] at hshort
    have hdx : -1 ≤ (a.x : ℤ) - c.x ∧ (a.x : ℤ) - c.x ≤ 1 :=
      abs_le_one_of_sq_le_two
        (by linarith [sq_nonneg ((a.y : ℤ) - c.y), sq_nonneg ((a.z : ℤ) - c.z)])
    have hdz : -1 ≤ (a.z : ℤ) - c.z ∧ (a.z : ℤ) - c.z ≤ 1 :=
      abs_le_one_of_sq_le_two
        (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.y : ℤ) - c.y)])
    have := hr.midpoint_x; have := hr.midpoint_z
    have := a.sum_eq; have := b.sum_eq; have := c.sum_eq; have := d.sum_eq
    omega

@[simp]
theorem exampleTwo_apply (p : Vertex 2) :
    exampleTwo p = (if p.x = 2 then 0 else 1) + (if p.z = 0 then 0 else 1) := (rfl)

theorem boundary_exampleTwo :
    exampleTwo.boundary =
      productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩ := by
  ext s i
  fin_cases i <;> induction s using fin3_cases <;>
    simp [boundary_apply, productBoundary, Vertex.edgePoint]

theorem slacks_exampleTwo :
    rhombusSlack exampleTwo ⟨1, 1, 0, rfl⟩ (Vertex.cornerA 2) ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ = 1 ∧
    rhombusSlack exampleTwo (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate (Vertex.cornerA 2).rotate
      (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate = 0 ∧
    rhombusSlack exampleTwo (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate.rotate
      (Vertex.cornerA 2).rotate.rotate (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate.rotate
      (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate.rotate = 1 := by
  simp [rhombusSlack_def]

/-- Size-`2` non-hive check: setting `1` at `m_BC = (0, 1, 1)` and `0` everywhere else gives slack
`-1` on `isRhombus_at_cornerA`, so it is not rhombus-concave. -/
theorem not_isRhombusConcave_indicator_mBC :
    let f : Vertex 2 → ℤ := fun p => if p = ⟨0, 1, 1, rfl⟩ then 1 else 0
    rhombusSlack f ⟨1, 1, 0, rfl⟩ (Vertex.cornerA 2) ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ = -1 ∧
      ¬ IsRhombusConcave f := by
  refine ⟨by simp [rhombusSlack_def, Vertex.ext_iff], fun hf => ?_⟩
  have h := hf isRhombus_at_cornerA
  simp [Vertex.ext_iff] at h

end SmallRank

end Hive

end TauCeti
