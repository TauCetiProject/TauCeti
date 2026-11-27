/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SphereTree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Fin

/-!
# Sphere-tree strata of the PSS comparison family

Multiplicative PSS compares the pair-of-pants product with the Morse quantum product through a
one-parameter family of closed genus-zero curves. Attaching two negative PSS planes to the input
ends of the pair of pants and one positive PSS plane to its output end gives a sphere with three
poles, at which the curves meet the unstable manifolds `W^u(a₁)`, `W^u(a₂)` and the stable
manifold `W^s(a₀)` of critical points of a Morse function on the target. At one end of the family
the Hamiltonian perturbation is switched off, giving the three-point Gromov–Witten problem with
Morse incidence conditions; at the other end the three necks become infinitely long and the curves
break into the pair of pants and the three planes. This file computes the expected dimensions of
the strata of limits of this family over the interior parameters and at the long-neck end, and
states which of them have nonnegative expected dimension when sphere trees are attached, on the
classical branch where every simple sphere has nonnegative first Chern number. The conventions,
the reduction to simple spheres and the count for pairs of pants are those of
`TauCeti.Geometry.Symplectic.Floer.SphereTree`.

**Morse trajectories.** At a pole the curves may lose energy along the gradient flow: a chain of
`k` Morse trajectories breaks off, from a critical point of Morse index `h 0` down to one of Morse
index `h k`. Each trajectory is taken modulo its `ℝ`-translation, so the chain has expected
dimension `h 0 - h k - k` (`TauCeti.Floer.morseChainDimension`,
`TauCeti.Floer.morseChainDimension_eq`).

**The PSS planes.** A negative PSS plane runs from its Morse pole to a capped orbit of grading `μ`
at its negative end. Unconstrained, such planes in class `A` relative to the cap have expected
dimension `n - μ + 2 c₁(A)` in a target of real dimension `2n`, and meeting the unstable manifold
of a critical point of Morse index `i` at the pole is a condition of codimension `2n - i`. With a
chain of Morse trajectories broken off before the pole, from a critical point of Morse index
`h 0`, the expected dimension is `h 0 - n - μ + 2 c₁(A) - k`
(`TauCeti.Floer.negativePlaneDimension_eq`); a rigid plane at `A = 0` sends a critical point of
Morse index `i` to a capped orbit of grading `i - n`, the degree of the PSS map. Dually a positive
PSS plane runs from a capped orbit of grading `μ` to the stable manifold of a critical point, of
codimension equal to its Morse index, and with a Morse chain broken off after the pole it has
expected dimension `μ + n - h k + 2 c₁(A) - k` (`TauCeti.Floer.positivePlaneDimension_eq`).

**The core of the family.** At a parameter where the necks are finite, the curves are maps from a
fixed sphere with three poles, solving an equation perturbed by a Hamiltonian one-form. In class `A`
they have expected dimension `2n + 2 c₁(A)`, and the three incidence conditions cut this down to
`i₁ + i₂ - i₀ - 2n + 2 c₁(A)` for Morse indices `i₁`, `i₂`, `i₀` of the critical points at the
poles. With Morse chains broken off at the poles, starting at the input critical points `a₁`, `a₂`
and ending at the output critical point `a₀`, the expected dimension is
`ind a₁ + ind a₂ - ind a₀ - 2n + 2 c₁(A) - (k₁ + k₂ + k₀)`
(`TauCeti.Floer.comparisonCoreDimension_eq`). Since the PSS planes shift degrees by `-n` and `+n`,
this is the index `μ₁ + μ₂ - μ₀ - n + 2 c₁(A)` of the pair of pants for the gradings
`μ_j = ind a_j - n` of the PSS images, as it must be for the two ends of the family to be counts of
the same degree. Over a face of dimension `p` of the parameter space (`p = 1` for the interior
parameters) the stratum has dimension `p` more.

**The long-neck end.** At the long-neck end the limit is a broken configuration: the two negative
planes, with Floer cylinders breaking off between them and the inputs of the pair of pants, the
pair of pants itself, and the positive plane, with Floer cylinders between the output of the pair
of pants and the plane, and Morse chains at the three poles. The gradings of the capped orbits at
which the pieces meet cancel, so its expected dimension is that of the core in the total class,
minus one for each Floer cylinder that has broken off
(`TauCeti.Floer.comparisonNeckDimension_eq_comparisonCoreDimension`).

**The surviving strata.** On a target where every simple sphere has nonnegative first Chern number
(the positively spherically monotone and spherically `c₁`-zero branches), a stratum with a tree of
simple spheres attached has expected dimension at most two less for each simple sphere
(`TauCeti.Floer.sphereTreeDimension_comparisonCoreDimension_add_le`,
`TauCeti.Floer.sphereTreeDimension_comparisonNeckDimension_le`). So in a problem of expected
dimension at most one, a stratum has nonnegative expected dimension exactly when it carries no
nonconstant sphere bubble and has at most as many broken-off trajectories as the expected dimension
of the problem
(`TauCeti.Floer.sphereTreeDimension_comparisonCoreDimension_add_nonneg_iff`,
`TauCeti.Floer.sphereTreeDimension_comparisonNeckDimension_nonneg_iff`). For the comparison
homotopy, of degree `-1`, the rigid problem over the interior parameters has expected dimension
`0`, and the one-dimensional problem behind its boundary identity has expected dimension `1`:
its surviving strata are the unbroken cores over the interior, those with a single broken-off Morse
trajectory, and at the long-neck end the unbroken configurations of planes and a pair of pants.
None carries a bubble.

The end where the Hamiltonian perturbation vanishes is not covered: there the core solves the
unperturbed Cauchy–Riemann equation for a domain-independent structure, constant and multiply
covered cores occur, and the stable sphere trees in class `A` are the quantum corrections of the
Gromov–Witten problem, which survive. These are statements about expected dimensions; that strata
of negative expected dimension are empty for generic data is not proved here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  PSS maps and the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 6.1 (simple stable maps and the reduction of a stable
  map) and Theorem 6.6.1 (semipositive targets).
-/

public section

open Finset

namespace TauCeti.Floer

/-! ### Morse chains and PSS planes -/

/-- The expected dimension of a chain of `k` Morse trajectories, each taken modulo its
`ℝ`-translation. The trajectory `j` runs from a critical point of Morse index `h j.castSucc` to
one of Morse index `h j.succ`, and these trajectories modulo translation have expected dimension
`h j.castSucc - h j.succ - 1`. -/
def morseChainDimension {k : ℕ} (h : Fin (k + 1) → ℤ) : ℤ :=
  ∑ j : Fin k, (h j.castSucc - h j.succ - 1)

theorem morseChainDimension_def {k : ℕ} (h : Fin (k + 1) → ℤ) :
    morseChainDimension h = ∑ j : Fin k, (h j.castSucc - h j.succ - 1) := by
  rw [morseChainDimension]

/-- The Morse indices along a chain of Morse trajectories telescope: the chain has the expected
dimension `h 0 - h k` of the trajectories from its first to its last critical point, minus one
for each of its `k` trajectories. -/
theorem morseChainDimension_eq {k : ℕ} (h : Fin (k + 1) → ℤ) :
    morseChainDimension h = h 0 - h (Fin.last k) - k := by
  rw [morseChainDimension, ← Fin.sum_univ_castSucc_sub_succ h]
  simp [sum_sub_distrib]

variable {G : Type*} [AddCommMonoid G]

/-- The expected dimension of a broken limit of negative PSS planes, in a target of real dimension
`2n`. The plane meets at its pole the unstable manifold of a critical point of Morse index
`h (last k)` and has its negative end at a capped orbit of grading `μ`, in the class `A` relative
to its cap. The unconstrained planes have expected dimension `n - μ + 2 c₁(A)` and the incidence
condition has codimension `2n - h (last k)`. Before the pole a chain of `k` Morse trajectories has
broken off, running from a critical point of Morse index `h 0`
(`TauCeti.Floer.morseChainDimension`). -/
def negativePlaneDimension (n : ℤ) (c : G →+ ℤ) {k : ℕ} (h : Fin (k + 1) → ℤ) (μ : ℤ) (A : G) :
    ℤ :=
  n - μ + 2 * c A - (2 * n - h (Fin.last k)) + morseChainDimension h

theorem negativePlaneDimension_def (n : ℤ) (c : G →+ ℤ) {k : ℕ} (h : Fin (k + 1) → ℤ) (μ : ℤ)
    (A : G) :
    negativePlaneDimension n c h μ A =
      n - μ + 2 * c A - (2 * n - h (Fin.last k)) + morseChainDimension h := by
  rw [negativePlaneDimension]

/-- **The index of a negative PSS plane.** A broken limit of negative PSS planes from a critical
point of Morse index `h 0` to a capped orbit of grading `μ`, in the class `A`, has the expected
dimension `h 0 - n - μ + 2 c₁(A)` of the unbroken problem, minus one for each of the `k` Morse
trajectories that have broken off. -/
theorem negativePlaneDimension_eq (n : ℤ) (c : G →+ ℤ) {k : ℕ} (h : Fin (k + 1) → ℤ) (μ : ℤ)
    (A : G) :
    negativePlaneDimension n c h μ A = h 0 - n - μ + 2 * c A - k := by
  rw [negativePlaneDimension, morseChainDimension_eq]
  ring

/-- The expected dimension of a broken limit of positive PSS planes, in a target of real dimension
`2n`. The plane has its positive end at a capped orbit of grading `μ` and meets at its pole the
stable manifold of a critical point of Morse index `h 0`, in the class `A` relative to its cap.
The unconstrained planes have expected dimension `n + μ + 2 c₁(A)` and the incidence condition
has codimension `h 0`. After the pole a chain of `k` Morse trajectories has broken off, running to
a critical point of Morse index `h (last k)` (`TauCeti.Floer.morseChainDimension`). -/
def positivePlaneDimension (n : ℤ) (c : G →+ ℤ) (μ : ℤ) {k : ℕ} (h : Fin (k + 1) → ℤ) (A : G) :
    ℤ :=
  n + μ + 2 * c A - h 0 + morseChainDimension h

theorem positivePlaneDimension_def (n : ℤ) (c : G →+ ℤ) (μ : ℤ) {k : ℕ} (h : Fin (k + 1) → ℤ)
    (A : G) :
    positivePlaneDimension n c μ h A = n + μ + 2 * c A - h 0 + morseChainDimension h := by
  rw [positivePlaneDimension]

/-- **The index of a positive PSS plane.** A broken limit of positive PSS planes from a capped
orbit of grading `μ` to a critical point of Morse index `h (last k)`, in the class `A`, has the
expected dimension `μ + n - h (last k) + 2 c₁(A)` of the unbroken problem, minus one for each of
the `k` Morse trajectories that have broken off. -/
theorem positivePlaneDimension_eq (n : ℤ) (c : G →+ ℤ) (μ : ℤ) {k : ℕ} (h : Fin (k + 1) → ℤ)
    (A : G) :
    positivePlaneDimension n c μ h A = μ + n - h (Fin.last k) + 2 * c A - k := by
  rw [positivePlaneDimension, morseChainDimension_eq]
  ring

/-! ### The comparison family -/

/-- The expected dimension of a broken limit of the curves of the PSS comparison family at a fixed
parameter with finite necks, in a target of real dimension `2n`. The curves are maps of class `A`
from a fixed sphere with three poles, whose unconstrained moduli space has expected dimension
`2n + 2 c₁(A)`. At the two input poles they meet the unstable manifolds of critical points of
Morse indices `h₁ (last k₁)` and `h₂ (last k₂)`, conditions of codimensions `2n - h₁ (last k₁)`
and `2n - h₂ (last k₂)`, and at the output pole the stable manifold of a critical point of Morse
index `h₀ 0`, a condition of codimension `h₀ 0`. Chains of Morse trajectories have broken off at
the poles (`TauCeti.Floer.morseChainDimension`): before the input poles, from critical points of
Morse indices `h₁ 0` and `h₂ 0`, and after the output pole, to a critical point of Morse index
`h₀ (last k₀)`. -/
def comparisonCoreDimension (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ} (h₁ : Fin (k₁ + 1) → ℤ)
    (h₂ : Fin (k₂ + 1) → ℤ) (h₀ : Fin (k₀ + 1) → ℤ) (A : G) : ℤ :=
  2 * n + 2 * c A - (2 * n - h₁ (Fin.last k₁)) - (2 * n - h₂ (Fin.last k₂)) - h₀ 0 +
    morseChainDimension h₁ + morseChainDimension h₂ + morseChainDimension h₀

theorem comparisonCoreDimension_def (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ} (h₁ : Fin (k₁ + 1) → ℤ)
    (h₂ : Fin (k₂ + 1) → ℤ) (h₀ : Fin (k₀ + 1) → ℤ) (A : G) :
    comparisonCoreDimension n c h₁ h₂ h₀ A =
      2 * n + 2 * c A - (2 * n - h₁ (Fin.last k₁)) - (2 * n - h₂ (Fin.last k₂)) - h₀ 0 +
        morseChainDimension h₁ + morseChainDimension h₂ + morseChainDimension h₀ := by
  rw [comparisonCoreDimension]

/-- **The index of the comparison family.** A broken limit of the curves of the PSS comparison
family at a fixed parameter, between critical points of Morse indices `i₁ = h₁ 0` and `i₂ = h₂ 0`
at the inputs and `i₀ = h₀ (last k₀)` at the output, in the class `A`, has the expected dimension
`i₁ + i₂ - i₀ - 2n + 2 c₁(A)` of the unbroken problem, minus one for each of the
`k₁ + k₂ + k₀` Morse trajectories that have broken off. -/
theorem comparisonCoreDimension_eq (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ} (h₁ : Fin (k₁ + 1) → ℤ)
    (h₂ : Fin (k₂ + 1) → ℤ) (h₀ : Fin (k₀ + 1) → ℤ) (A : G) :
    comparisonCoreDimension n c h₁ h₂ h₀ A =
      h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n + 2 * c A - (k₁ + k₂ + k₀) := by
  rw [comparisonCoreDimension, morseChainDimension_eq, morseChainDimension_eq,
    morseChainDimension_eq]
  ring

/-- The expected dimension of a broken limit of the PSS comparison family at its long-neck end, in
a target of real dimension `2n`. It consists of two negative PSS planes
(`TauCeti.Floer.negativePlaneDimension`), with Morse chains `h₁` and `h₂` at their poles and
classes `A₁` and `A₂`, a broken pair of pants (`TauCeti.Floer.brokenPantsDimension`) in class `A`,
with the chains of Floer cylinders `C₁`, `C₂` at its inputs and `C₀` at its output, and a positive
PSS plane (`TauCeti.Floer.positivePlaneDimension`) with the Morse chain `h₀` and class `A₀`. The
first negative plane ends at the capped orbit of grading `g₁ 0` at which the chain of cylinders at
the first input starts, and likewise for the second, and the positive plane starts at the capped
orbit of grading `g₀ (last l₀)` at which the chain of cylinders at the output ends. The pieces
meet at nondegenerate orbits, so the expected dimensions add. -/
def comparisonNeckDimension (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ l₁ l₂ l₀ : ℕ}
    (h₁ : Fin (k₁ + 1) → ℤ) (h₂ : Fin (k₂ + 1) → ℤ) (h₀ : Fin (k₀ + 1) → ℤ)
    (g₁ : Fin (l₁ + 1) → ℤ) (g₂ : Fin (l₂ + 1) → ℤ) (g₀ : Fin (l₀ + 1) → ℤ) (C₁ : Fin l₁ → G)
    (C₂ : Fin l₂ → G) (C₀ : Fin l₀ → G) (A A₁ A₂ A₀ : G) : ℤ :=
  negativePlaneDimension n c h₁ (g₁ 0) A₁ + negativePlaneDimension n c h₂ (g₂ 0) A₂ +
    brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A +
      positivePlaneDimension n c (g₀ (Fin.last l₀)) h₀ A₀

theorem comparisonNeckDimension_def (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ l₁ l₂ l₀ : ℕ}
    (h₁ : Fin (k₁ + 1) → ℤ) (h₂ : Fin (k₂ + 1) → ℤ) (h₀ : Fin (k₀ + 1) → ℤ)
    (g₁ : Fin (l₁ + 1) → ℤ) (g₂ : Fin (l₂ + 1) → ℤ) (g₀ : Fin (l₀ + 1) → ℤ) (C₁ : Fin l₁ → G)
    (C₂ : Fin l₂ → G) (C₀ : Fin l₀ → G) (A A₁ A₂ A₀ : G) :
    comparisonNeckDimension n c h₁ h₂ h₀ g₁ g₂ g₀ C₁ C₂ C₀ A A₁ A₂ A₀ =
      negativePlaneDimension n c h₁ (g₁ 0) A₁ + negativePlaneDimension n c h₂ (g₂ 0) A₂ +
        brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A +
          positivePlaneDimension n c (g₀ (Fin.last l₀)) h₀ A₀ := by
  rw [comparisonNeckDimension]

/-- **The long-neck end of the comparison family.** The gradings of the capped orbits at which the
planes, the Floer cylinders and the pair of pants meet cancel, so a broken limit at the long-neck
end has the expected dimension of a broken limit at a parameter with finite necks with the same
Morse chains, in the total class `A' = A + ∑ C₁ + ∑ C₂ + ∑ C₀ + A₁ + A₂ + A₀`, minus one for each
of the `l₁ + l₂ + l₀` Floer cylinders that have broken off. -/
theorem comparisonNeckDimension_eq_comparisonCoreDimension (n : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k₀ l₁ l₂ l₀ : ℕ} (h₁ : Fin (k₁ + 1) → ℤ) (h₂ : Fin (k₂ + 1) → ℤ)
    (h₀ : Fin (k₀ + 1) → ℤ) (g₁ : Fin (l₁ + 1) → ℤ) (g₂ : Fin (l₂ + 1) → ℤ)
    (g₀ : Fin (l₀ + 1) → ℤ) (C₁ : Fin l₁ → G) (C₂ : Fin l₂ → G) (C₀ : Fin l₀ → G)
    (A A₁ A₂ A₀ : G) :
    comparisonNeckDimension n c h₁ h₂ h₀ g₁ g₂ g₀ C₁ C₂ C₀ A A₁ A₂ A₀ =
      comparisonCoreDimension n c h₁ h₂ h₀
          (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + A₁ + A₂ + A₀) - (l₁ + l₂ + l₀) := by
  rw [comparisonNeckDimension, negativePlaneDimension_eq, negativePlaneDimension_eq,
    brokenPantsDimension_eq, positivePlaneDimension_eq, comparisonCoreDimension_eq]
  simp only [map_add]
  ring

/-! ### Sphere trees on the comparison family -/

variable {κ P : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq P] {ι : Type*} [Fintype ι]

/-- **Sphere trees on the comparison family.** On a target where every simple sphere has
nonnegative first Chern number, a stratum of limits of the PSS comparison family over a face of
dimension `p` of the parameter space with finite necks, consisting of a broken limit with
`k₁ + k₂ + k₀` Morse trajectories broken off at its poles and a tree of simple spheres attached to
it, has expected dimension at most `i₁ + i₂ - i₀ - 2n + 2 c₁(A') + p - (k₁ + k₂ + k₀) - 2 #κ`,
where `A'` is the total class of the limit, including its bubbles. -/
theorem sphereTreeDimension_comparisonCoreDimension_add_le (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ}
    (h₁ : Fin (k₁ + 1) → ℤ) (h₂ : Fin (k₂ + 1) → ℤ) (h₀ : Fin (k₀ + 1) → ℤ) (A : G) (p : ℤ)
    {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v))
    (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w))
    (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeDimension n (comparisonCoreDimension n c h₁ h₂ h₀ A + p) (fun w => c (B' w))
        parent node root ≤
      h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n + 2 * c (A + ∑ v, B v) - (k₁ + k₂ + k₀) + p -
        2 * Fintype.card κ := by
  rw [comparisonCoreDimension_eq]
  exact sphereTreeDimension_le_sub_two_mul_card c
    (ind := fun A' => h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n + 2 * c A' - (k₁ + k₂ + k₀) + p)
    (fun _ _ => by rw [map_add]; ring) A hB hm hρ hc parent node root

/-- **The strata of the comparison family over the parameters with finite necks.** On a target
where every simple sphere has nonnegative first Chern number, consider the limits of the PSS
comparison family over a face of dimension `p` of the parameter space with finite necks, between
critical points of Morse indices `i₁ = h₁ 0`, `i₂ = h₂ 0` and `i₀ = h₀ (last k₀)`, in a total class
`A'` for which the stratum with `k₁ + k₂ + k₀` broken-off Morse trajectories has expected dimension
at most one, for instance because the problem has expected dimension
`i₁ + i₂ - i₀ - 2n + 2 c₁(A') + p` at most one. Such a stratum with a tree of simple spheres
attached has nonnegative expected dimension exactly when it has no nonconstant sphere bubble and
at most `i₁ + i₂ - i₀ - 2n + 2 c₁(A') + p` Morse trajectories have broken off. -/
theorem sphereTreeDimension_comparisonCoreDimension_add_nonneg_iff (n : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k₀ : ℕ} (h₁ : Fin (k₁ + 1) → ℤ) (h₂ : Fin (k₂ + 1) → ℤ) (h₀ : Fin (k₀ + 1) → ℤ)
    (A : G) (p : ℤ) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n + 2 * c (A + ∑ v, B v) - (k₁ + k₂ + k₀) + p ≤
      1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n (comparisonCoreDimension n c h₁ h₂ h₀ A + p) (fun w => c (B' w))
        parent node root ↔
      IsEmpty κ ∧
        (k₁ + k₂ + k₀ : ℤ) ≤
          h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n + 2 * c (A + ∑ v, B v) + p := by
  rw [comparisonCoreDimension_eq]
  refine (sphereTreeDimension_nonneg_iff c
    (ind := fun A' => h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n + 2 * c A' - (k₁ + k₂ + k₀) + p)
    (fun _ _ => by rw [map_add]; ring) A hB hm hρ hc hA parent node root).trans
    (and_congr_right fun _ => ?_)
  constructor <;> intro h <;> linarith

/-- **Sphere trees at the long-neck end.** On a target where every simple sphere has nonnegative
first Chern number, a stratum of limits of the PSS comparison family at its long-neck end,
consisting of two negative planes, a broken pair of pants and a positive plane, with
`k₁ + k₂ + k₀` Morse trajectories and `l₁ + l₂ + l₀` Floer cylinders broken off, and a tree of
simple spheres attached to any of these pieces, has expected dimension at most
`i₁ + i₂ - i₀ - 2n + 2 c₁(A') - (k₁ + k₂ + k₀) - (l₁ + l₂ + l₀) - 2 #κ`, where `A'` is the total
class of the limit, including its bubbles. -/
theorem sphereTreeDimension_comparisonNeckDimension_le (n : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k₀ l₁ l₂ l₀ : ℕ} (h₁ : Fin (k₁ + 1) → ℤ) (h₂ : Fin (k₂ + 1) → ℤ)
    (h₀ : Fin (k₀ + 1) → ℤ) (g₁ : Fin (l₁ + 1) → ℤ) (g₂ : Fin (l₂ + 1) → ℤ)
    (g₀ : Fin (l₀ + 1) → ℤ) (C₁ : Fin l₁ → G) (C₂ : Fin l₂ → G) (C₀ : Fin l₀ → G)
    (A A₁ A₂ A₀ : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w)) (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeDimension n (comparisonNeckDimension n c h₁ h₂ h₀ g₁ g₂ g₀ C₁ C₂ C₀ A A₁ A₂ A₀)
        (fun w => c (B' w)) parent node root ≤
      h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n +
          2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + A₁ + A₂ + A₀ + ∑ v, B v) -
            (k₁ + k₂ + k₀) - (l₁ + l₂ + l₀) - 2 * Fintype.card κ := by
  rw [comparisonNeckDimension_eq_comparisonCoreDimension,
    sub_eq_add_neg (comparisonCoreDimension n c h₁ h₂ h₀ _)]
  refine (sphereTreeDimension_comparisonCoreDimension_add_le n c h₁ h₂ h₀ _ _ hB hm hρ hc parent
    node root).trans_eq ?_
  ring

/-- **The strata of the comparison family at its long-neck end.** On a target where every simple
sphere has nonnegative first Chern number, consider the limits of the PSS comparison family at its
long-neck end between critical points of Morse indices `i₁ = h₁ 0`, `i₂ = h₂ 0` and
`i₀ = h₀ (last k₀)`, in a total class `A'` for which the stratum with `k₁ + k₂ + k₀` broken-off
Morse trajectories and `l₁ + l₂ + l₀` broken-off Floer cylinders has expected dimension at most
one, for instance because `i₁ + i₂ - i₀ - 2n + 2 c₁(A')` is at most one. Such a stratum with a
tree of simple spheres attached has nonnegative expected dimension exactly when it has no
nonconstant sphere bubble and at most `i₁ + i₂ - i₀ - 2n + 2 c₁(A')` trajectories and cylinders
have broken off in total. So in a problem of expected dimension zero only the unbroken
configurations of two negative planes, a pair of pants and a positive plane remain. -/
theorem sphereTreeDimension_comparisonNeckDimension_nonneg_iff (n : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k₀ l₁ l₂ l₀ : ℕ} (h₁ : Fin (k₁ + 1) → ℤ) (h₂ : Fin (k₂ + 1) → ℤ)
    (h₀ : Fin (k₀ + 1) → ℤ) (g₁ : Fin (l₁ + 1) → ℤ) (g₂ : Fin (l₂ + 1) → ℤ)
    (g₀ : Fin (l₀ + 1) → ℤ) (C₁ : Fin l₁ → G) (C₂ : Fin l₂ → G) (C₀ : Fin l₀ → G)
    (A A₁ A₂ A₀ : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n +
        2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + A₁ + A₂ + A₀ + ∑ v, B v) -
          (k₁ + k₂ + k₀) - (l₁ + l₂ + l₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n (comparisonNeckDimension n c h₁ h₂ h₀ g₁ g₂ g₀ C₁ C₂ C₀ A A₁ A₂ A₀)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k₁ + k₂ + k₀ + (l₁ + l₂ + l₀) : ℤ) ≤ h₁ 0 + h₂ 0 - h₀ (Fin.last k₀) - 2 * n +
        2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + A₁ + A₂ + A₀ + ∑ v, B v) := by
  rw [comparisonNeckDimension_eq_comparisonCoreDimension,
    sub_eq_add_neg (comparisonCoreDimension n c h₁ h₂ h₀ _)]
  refine (sphereTreeDimension_comparisonCoreDimension_add_nonneg_iff n c h₁ h₂ h₀ _ _ hB hm hρ hc
    (by linarith) parent node root).trans (and_congr_right fun _ => ?_)
  constructor <;> intro h <;> linarith

end TauCeti.Floer
