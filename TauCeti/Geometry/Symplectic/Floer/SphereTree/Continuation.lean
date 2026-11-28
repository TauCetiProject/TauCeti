/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SphereTree
import Mathlib.Tactic.Ring

/-!
# Sphere-tree strata of continuation maps and of the continuation family of pairs of pants

Continuation maps compare the Floer complexes of two Hamiltonians `H` and `H'`, and they are
multiplicative for the pair-of-pants products up to a chain homotopy. Both statements are boundary
counts: of the one-dimensional moduli spaces of continuation cylinders, of the concatenation family
joining the composite of two continuation maps to the identity, and of the family of pairs of pants
with continuation necks joining the two composites `Φ (a ⋆ b)` and `Φ a ⋆' Φ b`. This file computes
the expected dimensions of the strata of limits of these problems that are not already covered by
`TauCeti.Geometry.Symplectic.Floer.SphereTree`, and states which of them have nonnegative expected
dimension when sphere trees are attached, on the classical branch where every simple sphere has
nonnegative first Chern number. The conventions and the reduction to simple spheres are those of
`TauCeti.Geometry.Symplectic.Floer.SphereTree`.

**Broken continuation cylinders.** A continuation cylinder runs from a capped orbit of `H` of
grading `μ` at its positive end to a capped orbit of `H'` of grading `μ'` at its negative end. Its
datum depends on `s`, so it is not taken modulo translation, and in the class `C` relative to the
two caps it has index `μ - μ' + 2 c₁(C)`. A limit of continuation cylinders may lose energy along
both ends: a chain of `k` Floer cylinders of `H` breaks off before it and a chain of `k'` Floer
cylinders of `H'` after it, each taken modulo translation
(`TauCeti.Floer.brokenContinuationDimension`). The gradings telescope, so the broken cylinder has
the index of the unbroken problem between its outer capped generators, in its total class, minus
one for each broken-off Floer cylinder (`TauCeti.Floer.brokenContinuationDimension_eq`).

**The concatenation family.** The homotopy between the composite `Ψ Φ` of the continuation maps
from `H` to `H'` and back and the identity is the count of a one-parameter family of continuation
cylinders from `H` to itself through `H'`. At its long-neck end the cylinder breaks into a
continuation cylinder from `H` to `H'` and one from `H'` to `H`, with Floer cylinders of `H'`
possibly broken off between them, and their expected dimensions add up to the index of the
continuation cylinder from `H` to itself, minus the number of broken-off Floer cylinders
(`TauCeti.Floer.brokenContinuationDimension_add_brokenContinuationDimension`).

**The continuation family of pairs of pants.** Moving continuation necks along the ends of the
pair of pants (`TauCeti.Floer.pairOfPantsContinuationPerturbation`) gives a one-parameter family of
pairs of pants with the end Hamiltonians fixed. Over its interior parameters its limits are broken
pairs of pants, whose strata are those of `TauCeti.Floer.brokenPantsDimension` over a face of
dimension `p = 1` (`TauCeti.Floer.sphereTreeDimension_brokenPantsDimension_add_nonneg_iff`). At
its two long-neck ends the pair of pants breaks into
* a pair of pants of `H` followed by a continuation cylinder from `H` to `H'` at its output, the
  configurations counted by `Φ (a ⋆ b)`
  (`TauCeti.Floer.brokenPantsDimension_add_brokenContinuationDimension`), and
* continuation cylinders from `H` to `H'` at both inputs followed by a pair of pants of `H'`, the
  configurations counted by `Φ a ⋆' Φ b`
  (`brokenContinuationDimension_add_brokenContinuationDimension_add_brokenPantsDimension`).

In each case the gradings of the capped orbits at which the pieces meet cancel, so the expected
dimension is the index `μ₁ + μ₂ - μ₀ - n + 2 c₁(A')` of the pair of pants between the outer capped
generators, in the total class `A'`, minus the number of broken-off Floer cylinders.

**The surviving strata.** On a target where every simple sphere has nonnegative first Chern
number, a stratum with a tree of simple spheres attached loses two dimensions for each simple
sphere. So in a problem of expected dimension at most one, a stratum has nonnegative expected
dimension exactly when it carries no nonconstant sphere bubble and has at most as many broken-off
Floer cylinders as the expected dimension of the problem
(`TauCeti.Floer.sphereTreeDimension_brokenContinuationDimension_add_nonneg_iff` for continuation
cylinders over a face of dimension `p`, and its analogues at the long-neck ends). The rigid
continuation maps come from unbroken continuation cylinders without bubbles; the one-dimensional
moduli spaces behind their chain-map identity end at a single broken-off Floer cylinder; and in
the one-dimensional problems of the two families, of index `0`, the strata at the long-neck ends
are the unbroken composites of rigid pieces meeting at a capped generator, again without bubbles.

These are statements about expected dimensions; that strata of negative expected dimension are
empty for generic data is not proved here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 6.1 (simple stable maps and the reduction of a stable
  map), Theorem 6.6.1 (semipositive targets) and Section 12.1 (the pair-of-pants product and
  continuation maps).
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on continuation maps of semipositive Floer theory.
-/

public section

namespace TauCeti.Floer

variable {G : Type*} [AddCommMonoid G]

/-! ### Broken continuation cylinders -/

/-- The expected dimension of a broken limit of continuation cylinders from `H` to `H'`, before
bubbling. Its continuation cylinder runs from a capped orbit of `H` of grading `g (last k)` to a
capped orbit of `H'` of grading `g' 0`, in the class `C` relative to these caps, so its index is
`g (last k) - g' 0 + 2 c₁(C)`; it is not taken modulo translation. Before it a chain of `k` Floer
cylinders of `H` has broken off, running from the capped generator of grading `g 0`
(`TauCeti.Floer.cylinderChainDimension`), and after it a chain of `k'` Floer cylinders of `H'`
runs to the capped generator of grading `g' (last k')`. -/
def brokenContinuationDimension (c : G →+ ℤ) {k k' : ℕ} (g : Fin (k + 1) → ℤ)
    (g' : Fin (k' + 1) → ℤ) (D : Fin k → G) (D' : Fin k' → G) (C : G) : ℤ :=
  g (Fin.last k) - g' 0 + 2 * c C + cylinderChainDimension c g D + cylinderChainDimension c g' D'

theorem brokenContinuationDimension_def (c : G →+ ℤ) {k k' : ℕ} (g : Fin (k + 1) → ℤ)
    (g' : Fin (k' + 1) → ℤ) (D : Fin k → G) (D' : Fin k' → G) (C : G) :
    brokenContinuationDimension c g g' D D' C =
      g (Fin.last k) - g' 0 + 2 * c C + cylinderChainDimension c g D +
        cylinderChainDimension c g' D' := by
  rw [brokenContinuationDimension]

/-- **The index of a broken continuation cylinder.** The expected dimension of a broken limit of
continuation cylinders is the index `μ - μ' + 2 c₁(C')` of the unbroken problem between the capped
generators of gradings `μ = g 0` and `μ' = g' (last k')`, in the total class
`C' = C + ∑ D + ∑ D'`, minus one for each of the `k + k'` Floer cylinders that have broken off. -/
theorem brokenContinuationDimension_eq (c : G →+ ℤ) {k k' : ℕ} (g : Fin (k + 1) → ℤ)
    (g' : Fin (k' + 1) → ℤ) (D : Fin k → G) (D' : Fin k' → G) (C : G) :
    brokenContinuationDimension c g g' D D' C =
      g 0 - g' (Fin.last k') + 2 * c (C + ∑ j, D j + ∑ j, D' j) - (k + k') := by
  rw [brokenContinuationDimension, cylinderChainDimension_eq, cylinderChainDimension_eq, map_add,
    map_add]
  ring

/-- **The long-neck end of the concatenation family.** The continuation cylinders from `H` to
itself through `H'` break into a broken continuation cylinder from `H` to `H'` and a broken
continuation cylinder from `H'` to `H`: the chain `h` of Floer cylinders of `H'` after the first
ends at the capped generator at which the chain `h'` before the second starts. Their expected
dimensions add up to the index `μ - μ' + 2 c₁(C')` of the continuation cylinder between the outer
capped generators, in the total class `C'`, minus the number of Floer cylinders that have broken
off, including those between the two pieces. -/
theorem brokenContinuationDimension_add_brokenContinuationDimension (c : G →+ ℤ)
    {k l l' k' : ℕ} (g : Fin (k + 1) → ℤ) (h : Fin (l + 1) → ℤ) (h' : Fin (l' + 1) → ℤ)
    (g' : Fin (k' + 1) → ℤ) (D : Fin k → G) (E : Fin l → G) (E' : Fin l' → G)
    (D' : Fin k' → G) (C₁ C₂ : G) (hh : h (Fin.last l) = h' 0) :
    brokenContinuationDimension c g h D E C₁ + brokenContinuationDimension c h' g' E' D' C₂ =
      g 0 - g' (Fin.last k') +
          2 * c (C₁ + C₂ + ∑ j, D j + ∑ j, E j + ∑ j, E' j + ∑ j, D' j) - (k + l + l' + k') := by
  rw [brokenContinuationDimension_eq, brokenContinuationDimension_eq, hh]
  simp only [map_add]
  ring

/-! ### The continuation family of pairs of pants -/

/-- **The long-neck end of the continuation family at the output.** The pair of pants with
continuation necks breaks into a broken pair of pants `P` of `H` and a broken continuation
cylinder from `H` to `H'` at its output: the output chain `h` of `P` ends at the capped generator
at which the chain `h'` before the continuation cylinder starts. These are the configurations
counted by `Φ (a ⋆ b)`. Their expected dimensions add up to the index
`μ₁ + μ₂ - μ₀ - n + 2 c₁(A')` of the pair of pants between the outer capped generators, in the
total class `A'`, minus the number of Floer cylinders that have broken off, including those between
the two pieces. -/
theorem brokenPantsDimension_add_brokenContinuationDimension (n : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k k' k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (h : Fin (k + 1) → ℤ)
    (h' : Fin (k' + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G)
    (D : Fin k → G) (D' : Fin k' → G) (C₀ : Fin k₀ → G) (A C : G)
    (hh : h (Fin.last k) = h' 0) :
    brokenPantsDimension n c g₁ g₂ h C₁ C₂ D A + brokenContinuationDimension c h' g₀ D' C₀ C =
      g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
          2 * c (A + C + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, D j + ∑ j, D' j + ∑ j, C₀ j) -
        (k₁ + k₂ + k + k' + k₀) := by
  rw [brokenPantsDimension_eq, brokenContinuationDimension_eq, hh]
  simp only [map_add]
  ring

/-- **The long-neck end of the continuation family at the inputs.** The pair of pants with
continuation necks breaks into broken continuation cylinders from `H` to `H'` at both inputs and a
broken pair of pants `Q` of `H'`: the chain `hᵢ` of Floer cylinders of `H'` after the continuation
cylinder at the input `i` ends at the capped generator at which the input chain `hᵢ'` of `Q`
starts. These are the configurations counted by `Φ a ⋆' Φ b`. Their expected dimensions add up to
the index `μ₁ + μ₂ - μ₀ - n + 2 c₁(A')` of the pair of pants between the outer capped generators,
in the total class `A'`, minus the number of Floer cylinders that have broken off, including those
between the pieces. -/
theorem brokenContinuationDimension_add_brokenContinuationDimension_add_brokenPantsDimension
    (n : ℤ) (c : G →+ ℤ) {k₁ k₂ l₁ l₂ l₁' l₂' k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ)
    (g₂ : Fin (k₂ + 1) → ℤ) (h₁ : Fin (l₁ + 1) → ℤ) (h₂ : Fin (l₂ + 1) → ℤ)
    (h₁' : Fin (l₁' + 1) → ℤ) (h₂' : Fin (l₂' + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ)
    (D₁ : Fin k₁ → G) (D₂ : Fin k₂ → G) (E₁ : Fin l₁ → G) (E₂ : Fin l₂ → G) (E₁' : Fin l₁' → G)
    (E₂' : Fin l₂' → G) (C₀ : Fin k₀ → G) (C₁ C₂ A : G) (hh₁ : h₁ (Fin.last l₁) = h₁' 0)
    (hh₂ : h₂ (Fin.last l₂) = h₂' 0) :
    brokenContinuationDimension c g₁ h₁ D₁ E₁ C₁ + brokenContinuationDimension c g₂ h₂ D₂ E₂ C₂ +
        brokenPantsDimension n c h₁' h₂' g₀ E₁' E₂' C₀ A =
      g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
          2 * c (C₁ + C₂ + A + ∑ j, D₁ j + ∑ j, D₂ j + ∑ j, E₁ j + ∑ j, E₂ j + ∑ j, E₁' j +
            ∑ j, E₂' j + ∑ j, C₀ j) -
        (k₁ + k₂ + l₁ + l₂ + l₁' + l₂' + k₀) := by
  rw [brokenContinuationDimension_eq, brokenContinuationDimension_eq, brokenPantsDimension_eq,
    hh₁, hh₂]
  simp only [map_add]
  ring

/-! ### The surviving strata -/

variable {κ P : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq P] {ι : Type*} [Fintype ι]

/-- **Sphere trees on broken continuation cylinders.** On a target where every simple sphere has
nonnegative first Chern number, a stratum of limits of continuation cylinders over a face of
dimension `p` of a parameter space, consisting of a broken continuation cylinder with `k + k'`
Floer cylinders broken off at its ends and a tree of simple spheres attached to it, has expected
dimension at most `μ - μ' + 2 c₁(C') - (k + k') + p - 2 #κ`, where `C'` is the total class of the
limit, including its bubbles: one less for each broken-off Floer cylinder and two less for each
simple sphere. -/
theorem sphereTreeDimension_brokenContinuationDimension_add_le (n p : ℤ) (c : G →+ ℤ)
    {k k' : ℕ} (g : Fin (k + 1) → ℤ) (g' : Fin (k' + 1) → ℤ) (D : Fin k → G) (D' : Fin k' → G)
    (C : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w)) (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeDimension n (brokenContinuationDimension c g g' D D' C + p) (fun w => c (B' w))
        parent node root ≤
      g 0 - g' (Fin.last k') + 2 * c (C + ∑ j, D j + ∑ j, D' j + ∑ v, B v) - (k + k') + p -
        2 * Fintype.card κ := by
  rw [brokenContinuationDimension_eq]
  exact sphereTreeDimension_le_sub_two_mul_card c
    (ind := fun C' => g 0 - g' (Fin.last k') + 2 * c C' - (k + k') + p)
    (fun _ _ => by rw [map_add]; ring) _ hB hm hρ hc parent node root

/-- **The strata of continuation maps and their homotopies.** On a target where every simple
sphere has nonnegative first Chern number, consider the limits of continuation cylinders between
capped generators of gradings `μ = g 0` and `μ' = g' (last k')` over a face of dimension `p` of a
parameter space: `p = 0` for the continuation maps themselves, and `p = 1` in the interior of a
one-parameter family of continuation data, such as the concatenation family or a homotopy between
two continuation data. If the stratum with `k + k'` broken-off Floer cylinders has expected
dimension at most one, for instance because the problem has expected dimension
`μ - μ' + 2 c₁(C') + p` at most one in the total class `C'`, the stratum with a tree of simple
spheres attached has nonnegative expected dimension exactly when it has no nonconstant sphere
bubble and at most `μ - μ' + 2 c₁(C') + p` Floer cylinders have broken off. So the rigid
continuation maps come from unbroken continuation cylinders, and the one-dimensional moduli spaces
behind their chain-map identity meet the strata with a single broken-off Floer cylinder, all
without bubbles. -/
theorem sphereTreeDimension_brokenContinuationDimension_add_nonneg_iff (n p : ℤ) (c : G →+ ℤ)
    {k k' : ℕ} (g : Fin (k + 1) → ℤ) (g' : Fin (k' + 1) → ℤ) (D : Fin k → G) (D' : Fin k' → G)
    (C : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g 0 - g' (Fin.last k') + p + 2 * c (C + ∑ j, D j + ∑ j, D' j + ∑ v, B v) - (k + k') ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n (brokenContinuationDimension c g g' D D' C + p) (fun w => c (B' w))
        parent node root ↔
      IsEmpty κ ∧ (k + k' : ℤ) ≤ g 0 - g' (Fin.last k') + p +
        2 * c (C + ∑ j, D j + ∑ j, D' j + ∑ v, B v) :=
  sphereTreeDimension_nonneg_iff_of_eq_add_two_mul_sub c hB hm hρ hc
    (by rw [brokenContinuationDimension_eq]; ring) hA parent node root

/-- **The strata at the long-neck end of the concatenation family.** On a target where every simple
sphere has nonnegative first Chern number, consider the limits of the concatenation family at its
long-neck end: a broken continuation cylinder from `H` to `H'` followed by one from `H'` to `H`, as
in `TauCeti.Floer.brokenContinuationDimension_add_brokenContinuationDimension`, with a tree of
simple spheres attached. The end point is a face of dimension zero of the parameter space. If the
expected dimension of the core is at most one, the stratum has nonnegative expected dimension
exactly when it has no nonconstant sphere bubble and at most `μ - μ' + 2 c₁(C')` Floer cylinders
have broken off. In the one-dimensional problem of the family, of index `0`, the only such strata
are two unbroken continuation cylinders meeting at a capped generator of `H'`, the configurations
counted by `Ψ Φ`. -/
theorem sphereTreeDimension_brokenContinuationDimension_add_brokenContinuationDimension_nonneg_iff
    (n : ℤ) (c : G →+ ℤ) {k l l' k' : ℕ} (g : Fin (k + 1) → ℤ) (h : Fin (l + 1) → ℤ)
    (h' : Fin (l' + 1) → ℤ) (g' : Fin (k' + 1) → ℤ) (D : Fin k → G) (E : Fin l → G)
    (E' : Fin l' → G) (D' : Fin k' → G) (C₁ C₂ : G) (hh : h (Fin.last l) = h' 0)
    {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v))
    (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g 0 - g' (Fin.last k') +
        2 * c (C₁ + C₂ + ∑ j, D j + ∑ j, E j + ∑ j, E' j + ∑ j, D' j + ∑ v, B v) -
          (k + l + l' + k') ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n
        (brokenContinuationDimension c g h D E C₁ + brokenContinuationDimension c h' g' E' D' C₂)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k + l + l' + k' : ℤ) ≤ g 0 - g' (Fin.last k') +
        2 * c (C₁ + C₂ + ∑ j, D j + ∑ j, E j + ∑ j, E' j + ∑ j, D' j + ∑ v, B v) :=
  sphereTreeDimension_nonneg_iff_of_eq_add_two_mul_sub c hB hm hρ hc
    (brokenContinuationDimension_add_brokenContinuationDimension c g h h' g' D E E' D' C₁ C₂ hh)
    hA parent node root

/-- **The strata at the long-neck end of the continuation family at the output.** On a target where
every simple sphere has nonnegative first Chern number, consider the limits of the continuation
family of pairs of pants at its end where a continuation cylinder breaks off at the output: a
broken pair of pants of `H` followed by a broken continuation cylinder from `H` to `H'`, as in
`TauCeti.Floer.brokenPantsDimension_add_brokenContinuationDimension`, with a tree of simple spheres
attached. If the expected dimension of the core is at most one, the stratum has nonnegative
expected dimension exactly when it has no nonconstant sphere bubble and at most
`μ₁ + μ₂ - μ₀ - n + 2 c₁(A')` Floer cylinders have broken off. In the one-dimensional problem of
the family, of index `0`, the only such strata are an unbroken pair of pants and an unbroken
continuation cylinder meeting at a capped generator of `H`. -/
theorem sphereTreeDimension_brokenPantsDimension_add_brokenContinuationDimension_nonneg_iff
    (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k k' k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ)
    (h : Fin (k + 1) → ℤ) (h' : Fin (k' + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G)
    (C₂ : Fin k₂ → G) (D : Fin k → G) (D' : Fin k' → G) (C₀ : Fin k₀ → G) (A C : G)
    (hh : h (Fin.last k) = h' 0) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
        2 * c (A + C + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, D j + ∑ j, D' j + ∑ j, C₀ j + ∑ v, B v) -
          (k₁ + k₂ + k + k' + k₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n
        (brokenPantsDimension n c g₁ g₂ h C₁ C₂ D A + brokenContinuationDimension c h' g₀ D' C₀ C)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k₁ + k₂ + k + k' + k₀ : ℤ) ≤ g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
        2 * c (A + C + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, D j + ∑ j, D' j + ∑ j, C₀ j + ∑ v, B v) :=
  sphereTreeDimension_nonneg_iff_of_eq_add_two_mul_sub c hB hm hρ hc
    (brokenPantsDimension_add_brokenContinuationDimension n c g₁ g₂ h h' g₀ C₁ C₂ D D' C₀ A C hh)
    hA parent node root

/-- **The strata at the long-neck end of the continuation family at the inputs.** On a target where
every simple sphere has nonnegative first Chern number, consider the limits of the continuation
family of pairs of pants at its end where continuation cylinders break off at both inputs: broken
continuation cylinders from `H` to `H'` followed by a broken pair of pants of `H'`, as in
`brokenContinuationDimension_add_brokenContinuationDimension_add_brokenPantsDimension`,
with a tree of simple spheres attached. If the expected dimension of the core is at most one, the
stratum has nonnegative expected dimension exactly when it has no nonconstant sphere bubble and at
most `μ₁ + μ₂ - μ₀ - n + 2 c₁(A')` Floer cylinders have broken off. In the one-dimensional problem
of the family, of index `0`, the only such strata are two unbroken continuation cylinders and an
unbroken pair of pants meeting at capped generators of `H'`. -/
theorem sphereTreeDimension_brokenContinuationDimension_add_add_brokenPantsDimension_nonneg_iff
    (n : ℤ) (c : G →+ ℤ) {k₁ k₂ l₁ l₂ l₁' l₂' k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ)
    (g₂ : Fin (k₂ + 1) → ℤ) (h₁ : Fin (l₁ + 1) → ℤ) (h₂ : Fin (l₂ + 1) → ℤ)
    (h₁' : Fin (l₁' + 1) → ℤ) (h₂' : Fin (l₂' + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ)
    (D₁ : Fin k₁ → G) (D₂ : Fin k₂ → G) (E₁ : Fin l₁ → G) (E₂ : Fin l₂ → G) (E₁' : Fin l₁' → G)
    (E₂' : Fin l₂' → G) (C₀ : Fin k₀ → G) (C₁ C₂ A : G) (hh₁ : h₁ (Fin.last l₁) = h₁' 0)
    (hh₂ : h₂ (Fin.last l₂) = h₂' 0) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
        2 * c (C₁ + C₂ + A + ∑ j, D₁ j + ∑ j, D₂ j + ∑ j, E₁ j + ∑ j, E₂ j + ∑ j, E₁' j +
          ∑ j, E₂' j + ∑ j, C₀ j + ∑ v, B v) - (k₁ + k₂ + l₁ + l₂ + l₁' + l₂' + k₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n
        (brokenContinuationDimension c g₁ h₁ D₁ E₁ C₁ +
            brokenContinuationDimension c g₂ h₂ D₂ E₂ C₂ +
          brokenPantsDimension n c h₁' h₂' g₀ E₁' E₂' C₀ A)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k₁ + k₂ + l₁ + l₂ + l₁' + l₂' + k₀ : ℤ) ≤ g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
        2 * c (C₁ + C₂ + A + ∑ j, D₁ j + ∑ j, D₂ j + ∑ j, E₁ j + ∑ j, E₂ j + ∑ j, E₁' j +
          ∑ j, E₂' j + ∑ j, C₀ j + ∑ v, B v) :=
  sphereTreeDimension_nonneg_iff_of_eq_add_two_mul_sub c hB hm hρ hc
    (brokenContinuationDimension_add_brokenContinuationDimension_add_brokenPantsDimension n c g₁ g₂
      h₁ h₂ h₁' h₂' g₀ D₁ D₂ E₁ E₂ E₁' E₂' C₀ C₁ C₂ A hh₁ hh₂) hA parent node root

end TauCeti.Floer
