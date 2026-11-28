/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SphereTree.Comparison
import Mathlib.Tactic.Ring

/-!
# Sphere-tree strata of the unit homotopy families

The unit of the pair-of-pants product is the count of negative PSS planes whose pole meets the
unstable manifold of the fundamental cycle of a Morse function on the target. It is a unit on
either side because of two one-parameter families, the *capping families*: a negative PSS plane is
glued into the first or the second input of the pair of pants along a neck, and the result is a
*capped cylinder*, a cylinder from the remaining input to the output carrying the pole of the
plane as a marked point with its Morse incidence condition. The counts of the family give the
chain homotopy between the product with the plane counts and the continuation map of the cylinders
(`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right` and its
`_left` form). This file computes the expected dimensions of the strata of limits of these families
over the parameters with a finite neck and at the long-neck end, and states which of them have
nonnegative expected dimension when sphere trees are attached, on the classical branch where every
simple sphere has nonnegative first Chern number. The conventions, the reduction to simple spheres
and the counts for pairs of pants, PSS planes and Morse chains are those of
`TauCeti.Geometry.Symplectic.Floer.SphereTree` and
`TauCeti.Geometry.Symplectic.Floer.SphereTree.Comparison`.

**The core of the family.** At a parameter with a finite neck, the curves are capped cylinders from
a capped orbit of grading `μ` to a capped orbit of grading `μ₀`. Unconstrained, in class `A` they
have the expected dimension `μ - μ₀ + 2 c₁(A)` of continuation cylinders: a negative plane, of
expected dimension `n - μ₁ + 2 c₁(A₁)`, glued to a pair of pants, of index
`μ₁ + μ - μ₀ - n + 2 c₁(A₂)`, has index `μ - μ₀ + 2 c₁(A₁ + A₂)`. Meeting at the pole the unstable
manifold of a critical point of Morse index `i` is a condition of codimension `2n - i`. A limit
over such parameters may lose energy at all three of its ends: a chain of Morse trajectories breaks
off before the pole, starting at a critical point of Morse index `h 0`, and chains of Floer
cylinders break off at the input and at the output. Its expected dimension is

`h 0 - 2n + μ - μ₀ + 2 c₁(A) - (k + l + l₀)`

for `k` broken-off Morse trajectories and `l + l₀` broken-off Floer cylinders, the gradings and
Morse indices at which the pieces meet cancelling (`TauCeti.Floer.unitCoreDimension_eq`). For the
fundamental cycle, carried by the critical points of Morse index `2n`, the incidence condition has
codimension zero and the unbroken problem has the index `μ - μ₀ + 2 c₁(A)` of the continuation
cylinders; a broken-off Morse trajectory then starts at such a critical point. Over a face of
dimension `p` of the parameter space (`p = 1` for the interior parameters, `p = 0` at an end point)
the stratum has dimension `p` more.

**The long-neck end.** When the neck becomes infinitely long, the capped cylinder breaks into the
negative plane and a broken pair of pants into whose first or second input the plane is glued,
possibly with Floer cylinders broken off between them. The grading of the capped orbit at which the
plane meets the chain of cylinders at that input cancels, so the expected dimension of the limit
is that of a broken capped cylinder with the same Morse chain and the chains at the other input
and at the output, in the total class, minus one for each Floer cylinder broken off between the
plane and the pair of pants (`TauCeti.Floer.negativePlaneDimension_add_brokenPantsDimension_fst`,
`TauCeti.Floer.negativePlaneDimension_add_brokenPantsDimension_snd`).

**The surviving strata.** On a target where every simple sphere has nonnegative first Chern number
(the positively spherically monotone and spherically `c₁`-zero branches), a stratum with a tree of
simple spheres attached has expected dimension at most two less for each simple sphere
(`TauCeti.Floer.sphereTreeDimension_unitCoreDimension_add_le`). So in a problem of expected
dimension at most one, a stratum has nonnegative expected dimension exactly when it carries no
nonconstant sphere bubble and has at most as many broken-off trajectories and cylinders as the
expected dimension of the problem
(`TauCeti.Floer.sphereTreeDimension_unitCoreDimension_add_nonneg_iff`,
`TauCeti.Floer.sphereTreeDimension_negativePlaneDimension_add_brokenPantsDimension_fst_nonneg_iff`,
`TauCeti.Floer.sphereTreeDimension_negativePlaneDimension_add_brokenPantsDimension_snd_nonneg_iff`).
The unit homotopy has degree `-1`: its rigid counts are capped cylinders of index `-1` at interior
parameters, unbroken and without bubbles. The one-dimensional problem behind its boundary identity
has index `0`; its surviving strata are the unbroken capped cylinders over the interior, those with
a single broken-off Floer cylinder at the input or the output, which give the differentials of the
identity, or a single broken-off Morse trajectory, whose contributions cancel because the
fundamental cycle is a cycle, and at the two end points the capped cylinders compared with the
continuation cylinders and the unbroken configurations of a plane and a pair of pants. None carries
a bubble.

These are statements about expected dimensions; that strata of negative expected dimension are
empty for generic data is not proved here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  PSS maps and the unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 6.1 (simple stable maps and the reduction of a stable
  map) and Theorem 6.6.1 (semipositive targets).
-/

public section

open Finset

namespace TauCeti.Floer

variable {G : Type*} [AddCommMonoid G]

/-! ### The capped cylinders of the family -/

/-- The expected dimension of a broken limit of the capped cylinders of a unit homotopy family at a
fixed parameter with a finite neck, in a target of real dimension `2n`. The capped cylinder runs
from a capped orbit of grading `g (last l)` to a capped orbit of grading `g₀ 0` in the class `A`
relative to the two caps, so that without incidence condition it has the index
`g (last l) - g₀ 0 + 2 c₁(A)` of a continuation cylinder. At its pole it meets the unstable manifold
of a critical point of Morse index `h (last k)`, a condition of codimension `2n - h (last k)`.
Before the pole a chain of `k` Morse trajectories has broken off, running from a critical point of
Morse index `h 0` (`TauCeti.Floer.morseChainDimension`). At its input a chain of `l` Floer
cylinders has broken off, running from the capped generator of grading `g 0` to the capped
cylinder, and at its output a chain of `l₀` Floer cylinders runs from the capped cylinder to the
capped generator of grading `g₀ (last l₀)` (`TauCeti.Floer.cylinderChainDimension`). -/
def unitCoreDimension (n : ℤ) (c : G →+ ℤ) {k l l₀ : ℕ} (h : Fin (k + 1) → ℤ)
    (g : Fin (l + 1) → ℤ) (g₀ : Fin (l₀ + 1) → ℤ) (C : Fin l → G) (C₀ : Fin l₀ → G) (A : G) : ℤ :=
  g (Fin.last l) - g₀ 0 + 2 * c A - (2 * n - h (Fin.last k)) + morseChainDimension h +
    cylinderChainDimension c g C + cylinderChainDimension c g₀ C₀

theorem unitCoreDimension_def (n : ℤ) (c : G →+ ℤ) {k l l₀ : ℕ} (h : Fin (k + 1) → ℤ)
    (g : Fin (l + 1) → ℤ) (g₀ : Fin (l₀ + 1) → ℤ) (C : Fin l → G) (C₀ : Fin l₀ → G) (A : G) :
    unitCoreDimension n c h g g₀ C C₀ A =
      g (Fin.last l) - g₀ 0 + 2 * c A - (2 * n - h (Fin.last k)) + morseChainDimension h +
        cylinderChainDimension c g C + cylinderChainDimension c g₀ C₀ := by
  rw [unitCoreDimension]

/-- **The index of the unit homotopy family.** A broken limit of the capped cylinders of a unit
homotopy family at a fixed parameter, from a critical point of Morse index `h 0` at the pole and a
capped generator of grading `μ = g 0` at the input to a capped generator of grading
`μ₀ = g₀ (last l₀)` at the output, has the expected dimension `h 0 - 2n + μ - μ₀ + 2 c₁(A')` of the
unbroken problem in the total class `A' = A + ∑ C + ∑ C₀`, minus one for each of the `k` Morse
trajectories and `l + l₀` Floer cylinders that have broken off. -/
theorem unitCoreDimension_eq (n : ℤ) (c : G →+ ℤ) {k l l₀ : ℕ} (h : Fin (k + 1) → ℤ)
    (g : Fin (l + 1) → ℤ) (g₀ : Fin (l₀ + 1) → ℤ) (C : Fin l → G) (C₀ : Fin l₀ → G) (A : G) :
    unitCoreDimension n c h g g₀ C C₀ A =
      h 0 - 2 * n + g 0 - g₀ (Fin.last l₀) + 2 * c (A + ∑ j, C j + ∑ j, C₀ j) - (k + l + l₀) := by
  rw [unitCoreDimension, morseChainDimension_eq, cylinderChainDimension_eq,
    cylinderChainDimension_eq, map_add, map_add]
  ring

/-! ### The long-neck end -/

/-- **The long-neck end of the unit homotopy family capping the first input.** At this end the
capped cylinder breaks into a negative PSS plane, with the Morse chain `h` at its pole and class
`A₁` (`TauCeti.Floer.negativePlaneDimension`), and a broken pair of pants in class `A`
(`TauCeti.Floer.brokenPantsDimension`), whose first input chain of `k₁` Floer cylinders starts at
the capped orbit of grading `g₁ 0` at which the plane ends. The grading `g₁ 0` cancels, so the
expected dimension of the limit is that of a broken capped cylinder with the Morse chain `h`, the
second input chain and the output chain of the pair of pants, in the total class
`A + A₁ + ∑ C₁`, minus one for each of the `k₁` cylinders broken off between the plane and the
pair of pants. -/
theorem negativePlaneDimension_add_brokenPantsDimension_fst (n : ℤ) (c : G →+ ℤ)
    {k k₁ k₂ k₀ : ℕ} (h : Fin (k + 1) → ℤ) (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ)
    (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G) (C₀ : Fin k₀ → G) (A A₁ : G) :
    negativePlaneDimension n c h (g₁ 0) A₁ + brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A =
      unitCoreDimension n c h g₂ g₀ C₂ C₀ (A + A₁ + ∑ j, C₁ j) - k₁ := by
  rw [negativePlaneDimension_eq, brokenPantsDimension_eq, unitCoreDimension_eq]
  simp only [map_add]
  ring

/-- **The long-neck end of the unit homotopy family capping the second input.** At this end the
capped cylinder breaks into a negative PSS plane, with the Morse chain `h` at its pole and class
`A₂` (`TauCeti.Floer.negativePlaneDimension`), and a broken pair of pants in class `A`
(`TauCeti.Floer.brokenPantsDimension`), whose second input chain of `k₂` Floer cylinders starts at
the capped orbit of grading `g₂ 0` at which the plane ends. The grading `g₂ 0` cancels, so the
expected dimension of the limit is that of a broken capped cylinder with the Morse chain `h`, the
first input chain and the output chain of the pair of pants, in the total class
`A + A₂ + ∑ C₂`, minus one for each of the `k₂` cylinders broken off between the plane and the
pair of pants. -/
theorem negativePlaneDimension_add_brokenPantsDimension_snd (n : ℤ) (c : G →+ ℤ)
    {k k₁ k₂ k₀ : ℕ} (h : Fin (k + 1) → ℤ) (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ)
    (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G) (C₀ : Fin k₀ → G) (A A₂ : G) :
    negativePlaneDimension n c h (g₂ 0) A₂ + brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A =
      unitCoreDimension n c h g₁ g₀ C₁ C₀ (A + A₂ + ∑ j, C₂ j) - k₂ := by
  rw [negativePlaneDimension_eq, brokenPantsDimension_eq, unitCoreDimension_eq]
  simp only [map_add]
  ring

/-! ### Sphere trees on the unit homotopy families -/

variable {κ P : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq P] {ι : Type*} [Fintype ι]

/-- **Sphere trees on the unit homotopy families.** On a target where every simple sphere has
nonnegative first Chern number, a stratum of limits of a unit homotopy family over a face of
dimension `p` of the parameter space with a finite neck, consisting of a broken capped cylinder with
`k` Morse trajectories and `l + l₀` Floer cylinders broken off and a tree of simple spheres attached
to it, has expected dimension at most `h 0 - 2n + μ - μ₀ + 2 c₁(A') + p - (k + l + l₀) - 2 #κ`,
where `A'` is the total class of the limit, including its bubbles. -/
theorem sphereTreeDimension_unitCoreDimension_add_le (n : ℤ) (c : G →+ ℤ) {k l l₀ : ℕ}
    (h : Fin (k + 1) → ℤ) (g : Fin (l + 1) → ℤ) (g₀ : Fin (l₀ + 1) → ℤ) (C : Fin l → G)
    (C₀ : Fin l₀ → G) (A : G) (p : ℤ) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w)) (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeDimension n (unitCoreDimension n c h g g₀ C C₀ A + p) (fun w => c (B' w))
        parent node root ≤
      h 0 - 2 * n + g 0 - g₀ (Fin.last l₀) + p +
          2 * c (A + ∑ j, C j + ∑ j, C₀ j + ∑ v, B v) - (k + l + l₀) - 2 * Fintype.card κ := by
  rw [unitCoreDimension_eq]
  refine (sphereTreeDimension_le_sub_two_mul_card c
    (ind := fun A' => h 0 - 2 * n + g 0 - g₀ (Fin.last l₀) + 2 * c A' - (k + l + l₀) + p)
    (fun _ _ => by rw [map_add]; ring) (A + ∑ j, C j + ∑ j, C₀ j) hB hm hρ hc parent node
    root).trans_eq ?_
  ring

/-- **The strata of the unit homotopy families over the parameters with a finite neck.** On a
target where every simple sphere has nonnegative first Chern number, consider the limits of a unit
homotopy family over a face of dimension `p` of the parameter space with a finite neck, from a
critical point of Morse index `h 0` and a capped generator of grading `μ = g 0` to a capped
generator of grading `μ₀ = g₀ (last l₀)`, in a total class `A'` for which the stratum with `k`
broken-off Morse trajectories and `l + l₀` broken-off Floer cylinders has expected dimension at most
one. Such a stratum with a tree of simple spheres attached has nonnegative expected dimension
exactly when it has no nonconstant sphere bubble and at most `h 0 - 2n + μ - μ₀ + 2 c₁(A') + p`
trajectories and cylinders have broken off in total. So the rigid counts of the unit homotopy, of
index `-1` at interior parameters, come from unbroken capped cylinders without bubbles, and its
one-dimensional problem, of index `0`, meets at interior parameters only the unbroken strata and
those with a single broken-off trajectory or cylinder. -/
theorem sphereTreeDimension_unitCoreDimension_add_nonneg_iff (n : ℤ) (c : G →+ ℤ) {k l l₀ : ℕ}
    (h : Fin (k + 1) → ℤ) (g : Fin (l + 1) → ℤ) (g₀ : Fin (l₀ + 1) → ℤ) (C : Fin l → G)
    (C₀ : Fin l₀ → G) (A : G) (p : ℤ) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : h 0 - 2 * n + g 0 - g₀ (Fin.last l₀) + p +
        2 * c (A + ∑ j, C j + ∑ j, C₀ j + ∑ v, B v) - (k + l + l₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n (unitCoreDimension n c h g g₀ C C₀ A + p) (fun w => c (B' w))
        parent node root ↔
      IsEmpty κ ∧ (k + l + l₀ : ℤ) ≤ h 0 - 2 * n + g 0 - g₀ (Fin.last l₀) + p +
        2 * c (A + ∑ j, C j + ∑ j, C₀ j + ∑ v, B v) :=
  sphereTreeDimension_nonneg_iff_of_eq_add_two_mul_sub c hB hm hρ hc
    (by rw [unitCoreDimension_eq]; ring) hA parent node root

/-- **The strata at the long-neck end of the unit homotopy family capping the first input.** On a
target where every simple sphere has nonnegative first Chern number, consider the limits of the
unit homotopy family capping the first input at its long-neck end: a negative PSS plane glued into
the first input of a broken pair of pants, as in
`TauCeti.Floer.negativePlaneDimension_add_brokenPantsDimension_fst`, with a tree of simple spheres
attached to any of these pieces. The end point is a face of dimension zero of the parameter space.
If the expected dimension of the core is at most one, the stratum has nonnegative expected dimension
exactly when it has no nonconstant sphere bubble and at most `h 0 - 2n + μ₂ - μ₀ + 2 c₁(A')`
trajectories and cylinders have broken off in total, `A'` being the total class. In the
one-dimensional problem of the unit homotopy, of index `0`, the only such strata are a plane and a
pair of pants meeting at a capped generator, unbroken and without bubbles, whose expected
dimensions add up to zero. -/
theorem sphereTreeDimension_negativePlaneDimension_add_brokenPantsDimension_fst_nonneg_iff
    (n : ℤ) (c : G →+ ℤ) {k k₁ k₂ k₀ : ℕ} (h : Fin (k + 1) → ℤ) (g₁ : Fin (k₁ + 1) → ℤ)
    (g₂ : Fin (k₂ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G)
    (C₀ : Fin k₀ → G) (A A₁ : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : h 0 - 2 * n + g₂ 0 - g₀ (Fin.last k₀) +
        2 * c (A + A₁ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) - (k + k₁ + k₂ + k₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n
        (negativePlaneDimension n c h (g₁ 0) A₁ + brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k + k₁ + k₂ + k₀ : ℤ) ≤ h 0 - 2 * n + g₂ 0 - g₀ (Fin.last k₀) +
        2 * c (A + A₁ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) :=
  sphereTreeDimension_nonneg_iff_of_eq_add_two_mul_sub c hB hm hρ hc
    (by rw [negativePlaneDimension_add_brokenPantsDimension_fst, unitCoreDimension_eq]
        simp only [map_add]
        ring) hA parent node root

/-- **The strata at the long-neck end of the unit homotopy family capping the second input.** On a
target where every simple sphere has nonnegative first Chern number, consider the limits of the
unit homotopy family capping the second input at its long-neck end: a negative PSS plane glued into
the second input of a broken pair of pants, as in
`TauCeti.Floer.negativePlaneDimension_add_brokenPantsDimension_snd`, with a tree of simple spheres
attached to any of these pieces. If the expected dimension of the core is at most one, the stratum
has nonnegative expected dimension exactly when it has no nonconstant sphere bubble and at most
`h 0 - 2n + μ₁ - μ₀ + 2 c₁(A')` trajectories and cylinders have broken off in total, `A'` being the
total class. In the one-dimensional problem of the unit homotopy, of index `0`, the only such strata
are a plane and a pair of pants meeting at a capped generator, unbroken and without bubbles, whose
expected dimensions add up to zero. -/
theorem sphereTreeDimension_negativePlaneDimension_add_brokenPantsDimension_snd_nonneg_iff
    (n : ℤ) (c : G →+ ℤ) {k k₁ k₂ k₀ : ℕ} (h : Fin (k + 1) → ℤ) (g₁ : Fin (k₁ + 1) → ℤ)
    (g₂ : Fin (k₂ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G)
    (C₀ : Fin k₀ → G) (A A₂ : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : h 0 - 2 * n + g₁ 0 - g₀ (Fin.last k₀) +
        2 * c (A + A₂ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) - (k + k₁ + k₂ + k₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n
        (negativePlaneDimension n c h (g₂ 0) A₂ + brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k + k₁ + k₂ + k₀ : ℤ) ≤ h 0 - 2 * n + g₁ 0 - g₀ (Fin.last k₀) +
        2 * c (A + A₂ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) :=
  sphereTreeDimension_nonneg_iff_of_eq_add_two_mul_sub c hB hm hρ hc
    (by rw [negativePlaneDimension_add_brokenPantsDimension_snd, unitCoreDimension_eq]
        simp only [map_add]
        ring) hA parent node root

end TauCeti.Floer
