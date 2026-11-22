/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Order.Module.Pi
import TauCeti.Analysis.Calculus.FDeriv.Monotone
import TauCeti.Analysis.Calculus.FDeriv.TVS
import TauCeti.Analysis.Convex.Extrema

/-!
# Matched actual-derivative outer approximations

For a composed inequality constraint `{x ∈ D | h (g x) ≤ b}` with inner map `g : X → ι → ℝ` and
outer function `h : (ι → ℝ) → ℝ`, a common family of anchor points `a : κ → X` together with
corresponding Fréchet derivatives `Dg i` of `g` at `a i` and `Dh i` of `h` at `g (a i)` induces
three families of affine rows:

* `TauCeti.componentRow`: the inner linearization `Gᵢ(x) = g (a i) + Dg i (x - a i)`,
* `TauCeti.outerRow`: the outer linearization `Hᵢ(y) = h (g (a i)) + Dh i (y - g (a i))`,
* `TauCeti.directRow`: the composed linearization `Cᵢ(x) = h (g (a i)) + (Dh i ∘ Dg i) (x - a i)`.

These define the direct outer approximation `TauCeti.directOA`, the shared-height outer
approximation `TauCeti.sharedOA`, and its refinement `TauCeti.sharedOAOn` imposing exact
equality `y j = Gᵢ(x) j` on a selected set `J` of coordinates.

When `g` maps `D` into `E`, `h` is convex on `E`, each coordinate `g · j` off `J` is convex on `D`,
the component rows are exact on `J`, every anchor `a i` lies in `D` with actual Fréchet derivatives
`Dg i` of `g` at `a i` and `Dh i` of `h` at `g (a i)`, and each `Dh i` is nonnegative on
nonnegative directions vanishing on `J`, the feasible set, the projection of `sharedOAOn J`, and
`directOA` are nested (`TauCeti.affine_coordinate_comparison`). Taking `J = ∅` gives the
monotone-derivative comparison (`TauCeti.analytic_comparison`), and global monotonicity of `h` on
`Set.univ` supplies derivative monotonicity automatically
(`TauCeti.fullspace_analytic_comparison`). All analytic results hold on arbitrary real topological
vector spaces and arbitrary index types.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Math. Program. 103 (2005), 225–249, §2, Theorem 1, pp. 227–228.
* J. Kronqvist, A. Lundell, and T. Westerlund, *Reformulations for utilizing separability when
  solving convex MINLP problems*, J. Global Optim. 71 (2018), 571–592, §3.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

section OuterRow

variable {X ι : Type*}

/-- The affine outer row `h (g a) + Dh (y - g a)` at the image of an anchor `a`. -/
def outerRow (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X) (Dh : (ι → ℝ) →L[ℝ] ℝ)
    (y : ι → ℝ) : ℝ :=
  h (g a) + Dh (y - g a)

/-- Characterization of `outerRow` evaluated at `y`. -/
theorem outerRow_apply (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X) (Dh : (ι → ℝ) →L[ℝ] ℝ)
    (y : ι → ℝ) :
    outerRow g h a Dh y = h (g a) + Dh (y - g a) :=
  (rfl)

@[simp]
theorem outerRow_self (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X) (Dh : (ι → ℝ) →L[ℝ] ℝ) :
    outerRow g h a Dh (g a) = h (g a) := by
  simp [outerRow_apply]

/-- Outer convex support: if `h` is convex on `E` and has Fréchet derivative `Dh` at `g a ∈ E`,
then `outerRow g h a Dh y ≤ h y` for every `y ∈ E`. -/
theorem outerRow_le_of_convexOn {E : Set (ι → ℝ)} {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a : X}
    {Dh : (ι → ℝ) →L[ℝ] ℝ} {y : ι → ℝ} (hhc : ConvexOn ℝ E h) (haE : g a ∈ E) (hyE : y ∈ E)
    (hh : HasFDerivAt h Dh (g a)) :
    outerRow g h a Dh y ≤ h y := by
  rw [outerRow_apply]
  exact hhc.add_le_of_hasFDerivAt haE hh y hyE

end OuterRow

section Algebraic

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [Module ℝ X] {ι κ : Type*}

/-- The affine component row `g a + Dg (x - a)` formed from inner values and a continuous linear
map `Dg`. -/
def componentRow (g : X → ι → ℝ) (a : X) (Dg : X →L[ℝ] (ι → ℝ)) (x : X) : ι → ℝ :=
  g a + Dg (x - a)

/-- The composed direct affine row `h (g a) + (Dh ∘L Dg) (x - a)`. -/
def directRow (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X) (Dg : X →L[ℝ] (ι → ℝ))
    (Dh : (ι → ℝ) →L[ℝ] ℝ) (x : X) : ℝ :=
  h (g a) + (Dh.comp Dg) (x - a)

/-- Points in `D` satisfying every direct row at the common anchor family `a`. -/
def directOA (D : Set X) (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : κ → X)
    (Dg : κ → X →L[ℝ] (ι → ℝ)) (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) : Set X :=
  {x | x ∈ D ∧ ∀ i, directRow g h (a i) (Dg i) (Dh i) x ≤ b}

/-- Pairs `(x, y) ∈ D × E` where a single common height vector `y` dominates every component row
and satisfies every outer row. -/
def sharedOA (D : Set X) (E : Set (ι → ℝ)) (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : κ → X)
    (Dg : κ → X →L[ℝ] (ι → ℝ)) (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) : Set (X × (ι → ℝ)) :=
  {z | z.1 ∈ D ∧ z.2 ∈ E ∧ ∀ i,
    componentRow g (a i) (Dg i) z.1 ≤ z.2 ∧ outerRow g h (a i) (Dh i) z.2 ≤ b}

/-- Pairs `(x, y) ∈ D × E` satisfying all component and outer rows for a common height vector `y`,
with exact equality `y j = componentRow g (a i) (Dg i) x j` on the selected coordinates `J`. -/
def sharedOAOn (J : Set ι) (D : Set X) (E : Set (ι → ℝ)) (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ)
    (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ)) (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    Set (X × (ι → ℝ)) :=
  {z | z.1 ∈ D ∧ z.2 ∈ E ∧ ∀ i,
    componentRow g (a i) (Dg i) z.1 ≤ z.2 ∧
    (∀ j ∈ J, z.2 j = componentRow g (a i) (Dg i) z.1 j) ∧
    outerRow g h (a i) (Dh i) z.2 ≤ b}

@[simp]
theorem componentRow_apply (g : X → ι → ℝ) (a : X) (Dg : X →L[ℝ] (ι → ℝ)) (x : X) (j : ι) :
    componentRow g a Dg x j = g a j + Dg (x - a) j := by
  simp [componentRow]

/-- Characterization of `directRow` evaluated at `x`. -/
theorem directRow_apply (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X) (Dg : X →L[ℝ] (ι → ℝ))
    (Dh : (ι → ℝ) →L[ℝ] ℝ) (x : X) :
    directRow g h a Dg Dh x = h (g a) + Dh (Dg (x - a)) :=
  (rfl)

@[simp]
theorem componentRow_self (g : X → ι → ℝ) (a : X) (Dg : X →L[ℝ] (ι → ℝ)) :
    componentRow g a Dg a = g a := by
  simp [componentRow]

@[simp]
theorem directRow_self (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X) (Dg : X →L[ℝ] (ι → ℝ))
    (Dh : (ι → ℝ) →L[ℝ] ℝ) :
    directRow g h a Dg Dh a = h (g a) := by
  simp [directRow_apply]

/-- Evaluating the outer row at the component row reproduces the direct row. -/
@[simp]
theorem outerRow_componentRow (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X)
    (Dg : X →L[ℝ] (ι → ℝ)) (Dh : (ι → ℝ) →L[ℝ] ℝ) (x : X) :
    outerRow g h a Dh (componentRow g a Dg x) = directRow g h a Dg Dh x := by
  simp [outerRow, componentRow, directRow]

@[simp]
theorem mem_directOA {D : Set X} {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a : κ → X}
    {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ} {x : X} :
    x ∈ directOA D g h a Dg Dh b ↔
      x ∈ D ∧ ∀ i, directRow g h (a i) (Dg i) (Dh i) x ≤ b :=
  (Iff.rfl)

@[simp]
theorem mem_sharedOA {D : Set X} {E : Set (ι → ℝ)} {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ}
    {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ}
    {z : X × (ι → ℝ)} :
    z ∈ sharedOA D E g h a Dg Dh b ↔
      z.1 ∈ D ∧ z.2 ∈ E ∧ ∀ i,
        componentRow g (a i) (Dg i) z.1 ≤ z.2 ∧ outerRow g h (a i) (Dh i) z.2 ≤ b :=
  (Iff.rfl)

@[simp]
theorem mem_sharedOAOn {J : Set ι} {D : Set X} {E : Set (ι → ℝ)} {g : X → ι → ℝ}
    {h : (ι → ℝ) → ℝ} {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ}
    {b : ℝ} {z : X × (ι → ℝ)} :
    z ∈ sharedOAOn J D E g h a Dg Dh b ↔
      z.1 ∈ D ∧ z.2 ∈ E ∧ ∀ i,
        componentRow g (a i) (Dg i) z.1 ≤ z.2 ∧
        (∀ j ∈ J, z.2 j = componentRow g (a i) (Dg i) z.1 j) ∧
        outerRow g h (a i) (Dh i) z.2 ≤ b :=
  (Iff.rfl)

/-- Forgetting the coordinate equalities on `J` embeds `sharedOAOn J` into `sharedOA`. -/
theorem sharedOAOn_subset_sharedOA (J : Set ι) (D : Set X) (E : Set (ι → ℝ))
    (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ))
    (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    sharedOAOn J D E g h a Dg Dh b ⊆ sharedOA D E g h a Dg Dh b := by
  intro z hz
  obtain ⟨hzD, hzE, hrow⟩ := mem_sharedOAOn.1 hz
  exact mem_sharedOA.2 ⟨hzD, hzE, fun i =>
    let ⟨hcomp, _, houter⟩ := hrow i
    ⟨hcomp, houter⟩⟩

/-- With no selected equality coordinates, `sharedOAOn ∅` coincides with `sharedOA`. -/
@[simp]
theorem sharedOAOn_empty (D : Set X) (E : Set (ι → ℝ)) (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ)
    (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ)) (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    sharedOAOn ∅ D E g h a Dg Dh b = sharedOA D E g h a Dg Dh b := by
  ext z
  simp

/-- Enlarging the set of equality coordinates shrinks `sharedOAOn`. -/
theorem sharedOAOn_anti {J' J : Set ι} (hJ : J' ⊆ J) (D : Set X) (E : Set (ι → ℝ))
    (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ))
    (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    sharedOAOn J D E g h a Dg Dh b ⊆ sharedOAOn J' D E g h a Dg Dh b := by
  intro z hz
  obtain ⟨hzD, hzE, hrow⟩ := mem_sharedOAOn.1 hz
  exact mem_sharedOAOn.2 ⟨hzD, hzE, fun i =>
    let ⟨hcomp, heq, houter⟩ := hrow i
    ⟨hcomp, fun j hj => heq j (hJ hj), houter⟩⟩

/-- When all coordinates are selected (`J = Set.univ`), every component row holds with equality. -/
theorem mem_sharedOAOn_univ {D : Set X} {E : Set (ι → ℝ)} {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ}
    {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ}
    {z : X × (ι → ℝ)} :
    z ∈ sharedOAOn Set.univ D E g h a Dg Dh b ↔
      z.1 ∈ D ∧ z.2 ∈ E ∧ ∀ i,
        z.2 = componentRow g (a i) (Dg i) z.1 ∧ outerRow g h (a i) (Dh i) z.2 ≤ b := by
  rw [mem_sharedOAOn]
  refine ⟨fun ⟨hzD, hzE, hrow⟩ => ⟨hzD, hzE, fun i =>
    let ⟨_, heq, houter⟩ := hrow i
    ⟨funext fun j => heq j (mem_univ j), houter⟩⟩,
    fun ⟨hzD, hzE, hrow⟩ => ⟨hzD, hzE, fun i =>
      let ⟨heq, houter⟩ := hrow i
      ⟨heq.ge, fun j _ => congrFun heq j, houter⟩⟩⟩

/-- With no anchors, `directOA` retains the domain `D`. -/
@[simp]
theorem directOA_of_isEmpty [IsEmpty κ] (D : Set X) (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ)
    (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ)) (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    directOA D g h a Dg Dh b = D := by
  ext x
  simp

/-- With no anchors, `sharedOA` is the product `D ×ˢ E`, retaining the height domain `E`. -/
@[simp]
theorem sharedOA_of_isEmpty [IsEmpty κ] (D : Set X) (E : Set (ι → ℝ)) (g : X → ι → ℝ)
    (h : (ι → ℝ) → ℝ) (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ))
    (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    sharedOA D E g h a Dg Dh b = D ×ˢ E := by
  ext z
  simp

/-- With no anchors, `sharedOAOn` is the product `D ×ˢ E`, retaining the height domain `E`. -/
@[simp]
theorem sharedOAOn_of_isEmpty [IsEmpty κ] (J : Set ι) (D : Set X) (E : Set (ι → ℝ))
    (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ))
    (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    sharedOAOn J D E g h a Dg Dh b = D ×ˢ E := by
  ext z
  simp

/-- With zero height coordinates and at least one anchor, every direct row reduces to the scalar
condition `h 0 ≤ b`. -/
theorem directOA_of_isEmpty_coord [IsEmpty ι] [Nonempty κ] (D : Set X) (g : X → ι → ℝ)
    (h : (ι → ℝ) → ℝ) (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ))
    (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    directOA D g h a Dg Dh b = {x ∈ D | h 0 ≤ b} := by
  ext x
  have hrow (i : κ) : directRow g h (a i) (Dg i) (Dh i) x = h 0 := by
    simp [directRow_apply, Subsingleton.elim (g (a i)) 0, Subsingleton.elim (Dg i (x - a i)) 0]
  simp [hrow]

/-- With zero height coordinates and at least one anchor, `sharedOA` retains membership of the
unique height vector in `E` together with `h 0 ≤ b`. -/
theorem sharedOA_of_isEmpty_coord [IsEmpty ι] [Nonempty κ] (D : Set X) (E : Set (ι → ℝ))
    (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ))
    (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    sharedOA D E g h a Dg Dh b = {z | z.1 ∈ D ∧ z.2 ∈ E ∧ h 0 ≤ b} := by
  ext z
  have hrow (i : κ) : outerRow g h (a i) (Dh i) z.2 = h 0 := by
    simp [outerRow_apply, Subsingleton.elim (g (a i)) 0, Subsingleton.elim z.2 0]
  simp [hrow]

/-- Graph witness for `sharedOAOn`: given `x ∈ D`, `g x ∈ E`, component support off `J`, exact
component rows on `J`, and that each outer row at `g x` is at most `b`, the canonical graph point
`(x, g x)` belongs to `sharedOAOn J`. -/
theorem graph_mem_sharedOAOn {J : Set ι} {D : Set X} {E : Set (ι → ℝ)} {g : X → ι → ℝ}
    {h : (ι → ℝ) → ℝ} {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ}
    {b : ℝ} {x : X} (hxD : x ∈ D) (hxE : g x ∈ E)
    (haff : ∀ i, ∀ j ∈ J, componentRow g (a i) (Dg i) x j = g x j)
    (hcomp : ∀ i, ∀ j ∉ J, componentRow g (a i) (Dg i) x j ≤ g x j)
    (houter : ∀ i, outerRow g h (a i) (Dh i) (g x) ≤ b) :
    (x, g x) ∈ sharedOAOn J D E g h a Dg Dh b := by
  refine mem_sharedOAOn.2 ⟨hxD, hxE, fun i => ⟨fun j => ?_, fun j hj => (haff i j hj).symm,
    houter i⟩⟩
  by_cases hj : j ∈ J
  · exact (haff i j hj).le
  · exact hcomp i j hj

/-- Graph witness for `sharedOA`: given `x ∈ D`, `g x ∈ E`, component row bounds at `(x, g x)`,
and that each outer row at `g x` is at most `b`, the graph point `(x, g x)` belongs to
`sharedOA`. -/
theorem graph_mem_sharedOA {D : Set X} {E : Set (ι → ℝ)} {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ}
    {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ} {x : X}
    (hxD : x ∈ D) (hxE : g x ∈ E)
    (hcomp : ∀ i, componentRow g (a i) (Dg i) x ≤ g x)
    (houter : ∀ i, outerRow g h (a i) (Dh i) (g x) ≤ b) :
    (x, g x) ∈ sharedOA D E g h a Dg Dh b :=
  mem_sharedOA.2 ⟨hxD, hxE, fun i => ⟨hcomp i, houter i⟩⟩

/-- Purely algebraic projection containment: if every `Dh i` is nonnegative on nonnegative
directions vanishing on `J`, then the first coordinate of any point in `sharedOAOn J` lies in
`directOA`. No convexity, differentiability, or membership of `componentRow` in `E` is needed. -/
theorem fst_mem_directOA_of_mem_sharedOAOn {J : Set ι} {D : Set X} {E : Set (ι → ℝ)}
    {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)}
    {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ}
    (hD : ∀ i v, 0 ≤ v → (∀ j ∈ J, v j = 0) → 0 ≤ Dh i v)
    {z : X × (ι → ℝ)} (hz : z ∈ sharedOAOn J D E g h a Dg Dh b) :
    z.1 ∈ directOA D g h a Dg Dh b := by
  obtain ⟨hzD, _, hrow⟩ := mem_sharedOAOn.1 hz
  refine mem_directOA.2 ⟨hzD, fun i => ?_⟩
  obtain ⟨hcomp, heq, houter⟩ := hrow i
  set v : ι → ℝ := z.2 - componentRow g (a i) (Dg i) z.1
  have hv0 : 0 ≤ v := sub_nonneg.2 hcomp
  have hvJ : ∀ j ∈ J, v j = 0 := fun j hj => sub_eq_zero.2 (heq j hj)
  have hpos : 0 ≤ Dh i v := hD i v hv0 hvJ
  have hdiff : outerRow g h (a i) (Dh i) z.2 - directRow g h (a i) (Dg i) (Dh i) z.1 = Dh i v := by
    rw [← outerRow_componentRow g h (a i) (Dg i) (Dh i) z.1]
    simp only [outerRow_apply, v, add_sub_add_left_eq_sub, ← map_sub]
    congr 1
    abel
  linarith

/-- Set-level projection containment `Prod.fst '' sharedOAOn J ⊆ directOA` under restricted
directional positivity of each `Dh i`. -/
theorem fst_image_sharedOAOn_subset_directOA {J : Set ι} {D : Set X} {E : Set (ι → ℝ)}
    {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)}
    {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ}
    (hD : ∀ i v, 0 ≤ v → (∀ j ∈ J, v j = 0) → 0 ≤ Dh i v) :
    Prod.fst '' sharedOAOn J D E g h a Dg Dh b ⊆ directOA D g h a Dg Dh b := by
  rintro x ⟨z, hz, rfl⟩
  exact fst_mem_directOA_of_mem_sharedOAOn hD hz

/-- Set-level projection containment `Prod.fst '' sharedOA ⊆ directOA` when every `Dh i` is
monotone. -/
theorem fst_image_sharedOA_subset_directOA {D : Set X} {E : Set (ι → ℝ)} {g : X → ι → ℝ}
    {h : (ι → ℝ) → ℝ} {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)}
    {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ} (hD : ∀ i, Monotone (Dh i)) :
    Prod.fst '' sharedOA D E g h a Dg Dh b ⊆ directOA D g h a Dg Dh b := by
  rw [← sharedOAOn_empty]
  exact fst_image_sharedOAOn_subset_directOA fun i v hv _ =>
    (monotone_iff_map_nonneg _).1 (hD i) v hv

end Algebraic

section Analytic

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] {ι κ : Type*}

/-- Exact component row for a continuous affine component: if coordinate `j` of `g` agrees with a
continuous affine map `f` near `a` and at `x`, and `g` has actual Fréchet derivative `Dg` at `a`,
then `componentRow g a Dg x j = g x j`. -/
theorem componentRow_eq_of_eventuallyEq_continuousAffineMap {g : X → ι → ℝ} {a x : X}
    {Dg : X →L[ℝ] (ι → ℝ)} {j : ι} (f : X →ᴬ[ℝ] ℝ) (hg : HasFDerivAt g Dg a)
    (hnhds : (fun z => g z j) =ᶠ[𝓝 a] f) (hx : g x j = f x) :
    componentRow g a Dg x j = g x j := by
  have heq : (ContinuousLinearMap.proj (R := ℝ) j).comp Dg = f.contLinear :=
    (hg.proj j).unique (f.hasFDerivAt_tvs.congr_of_eventuallyEq hnhds)
  have hDg : Dg (x - a) j = f.contLinear (x - a) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      congrArg (fun L : X →L[ℝ] ℝ => L (x - a)) heq
  have ha : g a j = f a := hnhds.self_of_nhds
  have hsub : f.contLinear (x - a) = f x - f a := by
    simpa only [vsub_eq_sub] using f.contLinear_apply_vsub x a
  rw [componentRow_apply, hDg, ha, hsub, hx]
  ring

/-- Inner component convex support: if `g · j` is convex on `D` and `g` has Fréchet derivative
`Dg` at `a ∈ D`, then `componentRow g a Dg x j ≤ g x j` for every `x ∈ D`. -/
theorem componentRow_le_of_convexOn {D : Set X} {g : X → ι → ℝ} {a x : X}
    {Dg : X →L[ℝ] (ι → ℝ)} {j : ι} (hc : ConvexOn ℝ D (fun z => g z j)) (ha : a ∈ D)
    (hx : x ∈ D) (hg : HasFDerivAt g Dg a) :
    componentRow g a Dg x j ≤ g x j := by
  simpa only [componentRow_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using hc.add_le_of_hasFDerivAt ha (hg.proj j) x hx

/-- Direct-row convex support via the chain rule: if `h ∘ g` is convex on `D` and `g`, `h` have
actual Fréchet derivatives `Dg` at `a ∈ D` and `Dh` at `g a`, then `directRow g h a Dg Dh x ≤
h (g x)` for every `x ∈ D`. -/
theorem directRow_le_of_convexOn_comp {D : Set X} {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a x : X}
    {Dg : X →L[ℝ] (ι → ℝ)} {Dh : (ι → ℝ) →L[ℝ] ℝ} (hc : ConvexOn ℝ D (h ∘ g))
    (ha : a ∈ D) (hx : x ∈ D) (hg : HasFDerivAt g Dg a) (hh : HasFDerivAt h Dh (g a)) :
    directRow g h a Dg Dh x ≤ h (g x) := by
  simpa only [directRow_apply, ContinuousLinearMap.comp_apply, Function.comp_apply] using
    hc.add_le_of_hasFDerivAt ha (hh.comp_tvs hg) x hx

/-- **Matched outer approximation comparison with exact rows on selected coordinates.**
If `g` maps `D` into `E`, component rows are exact on `J`, every component off `J` is convex on
`D`, `h` is convex on `E`, every anchor lies in `D` with actual Fréchet derivatives `Dg i` and
`Dh i`, and each `Dh i` is nonnegative on nonnegative directions vanishing on `J`, then the
original feasible set, the projection of `sharedOAOn J`, and `directOA` are nested. Outer
derivatives may have either sign on coordinates in `J`. -/
theorem affine_coordinate_comparison {J : Set ι} {D : Set X} {E : Set (ι → ℝ)}
    {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a : κ → X}
    {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} (b : ℝ)
    (hgE : MapsTo g D E)
    (haff : ∀ i, ∀ x ∈ D, ∀ j ∈ J, componentRow g (a i) (Dg i) x j = g x j)
    (hc : ∀ j ∉ J, ConvexOn ℝ D (fun x => g x j)) (hhc : ConvexOn ℝ E h)
    (ha : ∀ i, a i ∈ D) (hg : ∀ i, HasFDerivAt g (Dg i) (a i))
    (hh : ∀ i, HasFDerivAt h (Dh i) (g (a i)))
    (hD : ∀ i v, 0 ≤ v → (∀ j ∈ J, v j = 0) → 0 ≤ Dh i v) :
    {x ∈ D | h (g x) ≤ b} ⊆ Prod.fst '' sharedOAOn J D E g h a Dg Dh b ∧
      Prod.fst '' sharedOAOn J D E g h a Dg Dh b ⊆ directOA D g h a Dg Dh b := by
  refine ⟨fun x ⟨hxD, hxb⟩ => ⟨(x, g x), ?_, rfl⟩, fst_image_sharedOAOn_subset_directOA hD⟩
  refine graph_mem_sharedOAOn hxD (hgE hxD) (fun i j hj => haff i x hxD j hj)
    (fun i j hj => componentRow_le_of_convexOn (hc j hj) (ha i) hxD (hg i))
    (fun i => (outerRow_le_of_convexOn hhc (hgE (ha i)) (hgE hxD) (hh i)).trans hxb)

/-- **Matched outer approximation comparison with monotone outer derivatives.**
Specialization of `affine_coordinate_comparison` to `J = ∅`: when `g` maps `D` into `E`, every
component is convex on `D`, `h` is convex on `E`, `g` and `h` have actual Fréchet derivatives
`Dg i` and `Dh i` at anchors `a i ∈ D`, and each outer linear derivative `Dh i` is monotone, the
original feasible set, the projection of `sharedOA`, and `directOA` are nested. Monotonicity of `h`
itself is not assumed. -/
theorem analytic_comparison {D : Set X} {E : Set (ι → ℝ)}
    {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a : κ → X}
    {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} (b : ℝ)
    (hgE : MapsTo g D E)
    (hc : ∀ j, ConvexOn ℝ D (fun x => g x j)) (hhc : ConvexOn ℝ E h)
    (ha : ∀ i, a i ∈ D) (hg : ∀ i, HasFDerivAt g (Dg i) (a i))
    (hh : ∀ i, HasFDerivAt h (Dh i) (g (a i))) (hD : ∀ i, Monotone (Dh i)) :
    {x ∈ D | h (g x) ≤ b} ⊆ Prod.fst '' sharedOA D E g h a Dg Dh b ∧
      Prod.fst '' sharedOA D E g h a Dg Dh b ⊆ directOA D g h a Dg Dh b := by
  simpa only [sharedOAOn_empty] using
    affine_coordinate_comparison (J := ∅) b hgE
      (fun _ _ _ _ hj => hj.elim) (fun j _ => hc j) hhc ha hg hh
      (fun i v hv _ => (monotone_iff_map_nonneg _).1 (hD i) v hv)

/-- **Full-space matched outer approximation comparison.**
Inherits the inner-map convexity, anchor membership in `D`, and Fréchet-derivative hypotheses of
`analytic_comparison` on `E = Set.univ`, while replacing monotonicity of each `Dh i` with global
monotonicity of `h` (together with convexity of `h` on `Set.univ`), which supplies derivative
monotonicity automatically and yields both outer-approximation containments. -/
theorem fullspace_analytic_comparison {D : Set X} {g : X → ι → ℝ}
    {h : (ι → ℝ) → ℝ} {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)}
    {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} (b : ℝ)
    (hm : Monotone h) (hc : ∀ j, ConvexOn ℝ D (fun x => g x j))
    (hhc : ConvexOn ℝ Set.univ h) (ha : ∀ i, a i ∈ D)
    (hg : ∀ i, HasFDerivAt g (Dg i) (a i)) (hh : ∀ i, HasFDerivAt h (Dh i) (g (a i))) :
    {x ∈ D | h (g x) ≤ b} ⊆ Prod.fst '' sharedOA D Set.univ g h a Dg Dh b ∧
      Prod.fst '' sharedOA D Set.univ g h a Dg Dh b ⊆ directOA D g h a Dg Dh b :=
  analytic_comparison b (mapsTo_univ g D) hc hhc ha hg hh
    fun i => (hh i).monotone_of_monotone hm

/-- Weak objective-value ordering across the nested outer approximations of
`affine_coordinate_comparison`: if `f xU` bounds `f` from below on `directOA` (with no
feasibility requirement on `xU`), `zT` is feasible in and minimizes `f ∘ Prod.fst` on
`sharedOAOn J`, and `xS` is feasible in `{x ∈ D | h (g x) ≤ b}` (in particular, any feasible
minimizer), then `f xU ≤ f zT.1 ≤ f xS`. Attainment is not inferred. -/
theorem objective_le_of_affine_coordinate_comparison {β : Type*} [Preorder β] {f : X → β}
    {J : Set ι} {D : Set X} {E : Set (ι → ℝ)} {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a : κ → X}
    {Dg : κ → X →L[ℝ] (ι → ℝ)} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ}
    (hgE : MapsTo g D E)
    (haff : ∀ i, ∀ x ∈ D, ∀ j ∈ J, componentRow g (a i) (Dg i) x j = g x j)
    (hc : ∀ j ∉ J, ConvexOn ℝ D (fun x => g x j)) (hhc : ConvexOn ℝ E h)
    (ha : ∀ i, a i ∈ D) (hg : ∀ i, HasFDerivAt g (Dg i) (a i))
    (hh : ∀ i, HasFDerivAt h (Dh i) (g (a i)))
    (hD : ∀ i v, 0 ≤ v → (∀ j ∈ J, v j = 0) → 0 ≤ Dh i v)
    {xU xS : X} {zT : X × (ι → ℝ)}
    (hminU : IsMinOn f (directOA D g h a Dg Dh b) xU)
    (hzT : zT ∈ sharedOAOn J D E g h a Dg Dh b)
    (hminT : IsMinOn (f ∘ Prod.fst) (sharedOAOn J D E g h a Dg Dh b) zT)
    (hxS : xS ∈ {x ∈ D | h (g x) ≤ b}) :
    f xU ≤ f zT.1 ∧ f zT.1 ≤ f xS := by
  obtain ⟨hST, hTU⟩ := affine_coordinate_comparison b hgE haff hc hhc ha hg hh hD
  obtain ⟨zS, hzS, hfst⟩ := hST hxS
  exact ⟨hminU (hTU ⟨zT, hzT, rfl⟩), hfst ▸ hminT hzS⟩

end Analytic

section Separation

/-- Exact rows on selected coordinates strictly extend the monotone-derivative comparison: there
exist `g : ℝ → Fin 2 → ℝ`, `h : (Fin 2 → ℝ) → ℝ`, an anchor `a : Fin 1 → ℝ`, and actual Fréchet
derivatives `Dg`, `Dh` satisfying all hypotheses of `affine_coordinate_comparison` for `J = {0}` on
`D = Set.univ`, `E = Set.univ` with budget `2` (whose permitted cone `{v : Fin 2 → ℝ | 0 ≤ v ∧
v 0 = 0}` contains the nonzero vector `![0, 1]`), such that `Dh 0` is not monotone and
`Prod.fst '' sharedOA` is not contained in `directOA`, whereas `{x | h (g x) ≤ 2} ⊆
Prod.fst '' sharedOAOn {0} ⊆ directOA`. Witnessed by `g x = ![x, x ^ 2]`, `h y = y 0 ^ 2 + y 1`,
and `a 0 = -1`. -/
theorem exists_affine_coordinate_comparison_not_monotone :
    ∃ (g : ℝ → Fin 2 → ℝ) (h : (Fin 2 → ℝ) → ℝ) (a : Fin 1 → ℝ)
      (Dg : Fin 1 → ℝ →L[ℝ] (Fin 2 → ℝ)) (Dh : Fin 1 → (Fin 2 → ℝ) →L[ℝ] ℝ),
      (∀ i x, ∀ j ∈ ({0} : Set (Fin 2)), componentRow g (a i) (Dg i) x j = g x j) ∧
      (∀ j ∉ ({0} : Set (Fin 2)), ConvexOn ℝ Set.univ (fun x => g x j)) ∧
      ConvexOn ℝ Set.univ h ∧
      (∀ i, HasFDerivAt g (Dg i) (a i)) ∧
      (∀ i, HasFDerivAt h (Dh i) (g (a i))) ∧
      (∀ i v, 0 ≤ v → (∀ j ∈ ({0} : Set (Fin 2)), v j = 0) → 0 ≤ Dh i v) ∧
      (¬ Monotone (Dh 0)) ∧
      (¬ Prod.fst '' sharedOA Set.univ Set.univ g h a Dg Dh 2 ⊆ directOA Set.univ g h a Dg Dh 2) ∧
      ({x : ℝ | h (g x) ≤ 2} ⊆ Prod.fst '' sharedOAOn {0} Set.univ Set.univ g h a Dg Dh 2 ∧
        Prod.fst '' sharedOAOn {0} Set.univ Set.univ g h a Dg Dh 2 ⊆
          directOA Set.univ g h a Dg Dh 2) := by
  let g : ℝ → Fin 2 → ℝ := fun x => ![x, x ^ 2]
  let h : (Fin 2 → ℝ) → ℝ := fun y => y 0 ^ 2 + y 1
  let a : Fin 1 → ℝ := fun _ => -1
  let Dg0 : ℝ →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi
    ![ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ), ContinuousLinearMap.toSpanSingleton ℝ (-2 : ℝ)]
  let Dh0 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (-2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) + ContinuousLinearMap.proj (R := ℝ) 1
  have hg : ∀ i : Fin 1, HasFDerivAt g Dg0 (a i) := fun _ => hasFDerivAt_pi'.2 fun j => by
    fin_cases j
    · simpa [g, Dg0, a] using (hasDerivAt_id' (-1 : ℝ)).hasFDerivAt
    · simpa [g, Dg0, a] using (hasDerivAt_pow 2 (-1 : ℝ)).hasFDerivAt
  have hh : ∀ i : Fin 1, HasFDerivAt h Dh0 (g (a i)) := fun i => by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (-2 : ℝ) (g (a i) 0) := by
      simpa [g, a] using hasDerivAt_pow 2 (g (a i) 0)
    exact (hpow.comp_hasFDerivAt (g (a i)) (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (g (a i)))).add
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (g (a i)))
  have hnotmono : ¬ Monotone Dh0 := fun hm => by
    have h0 := (monotone_iff_map_single_nonneg Dh0).1 hm 0
    norm_num [Dh0] at h0
  have hcomp (i : Fin 1) (x : ℝ) : componentRow g (a i) Dg0 x = ![x, -2 * x - 1] := by
    ext j; fin_cases j <;> simp [componentRow_apply, g, a, Dg0]; ring
  have houter (i : Fin 1) (y : Fin 2 → ℝ) : outerRow g h (a i) Dh0 y = -2 * y 0 + y 1 - 1 := by
    simp only [outerRow_apply, g, h, a, Dh0, add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    ring
  have hnotSub : ¬ Prod.fst '' sharedOA Set.univ Set.univ g h a (fun _ => Dg0) (fun _ => Dh0) 2 ⊆
      directOA Set.univ g h a (fun _ => Dg0) (fun _ => Dh0) 2 := fun hsub => by
    have hmem : ((-2 : ℝ), ![0, 3]) ∈
        sharedOA Set.univ Set.univ g h a (fun _ => Dg0) (fun _ => Dh0) 2 :=
      mem_sharedOA.2 ⟨mem_univ _, mem_univ _, fun i => by
        rw [hcomp i, houter i]
        exact ⟨fun j => by fin_cases j <;> norm_num, by norm_num⟩⟩
    have hdir := (mem_directOA.1 (hsub ⟨((-2 : ℝ), ![0, 3]), hmem, rfl⟩)).2 0
    rw [← outerRow_componentRow, houter 0, hcomp 0] at hdir; norm_num at hdir
  have haff : ∀ i : Fin 1, ∀ x : ℝ, ∀ j ∈ ({0} : Set (Fin 2)),
      componentRow g (a i) Dg0 x j = g x j := fun i x j hj => by
    rw [mem_singleton_iff.1 hj, hcomp i, Matrix.cons_val_zero]
    simp only [g, Matrix.cons_val_zero]
  have hc : ∀ j ∉ ({0} : Set (Fin 2)), ConvexOn ℝ Set.univ (fun x => g x j) := fun j hj => by
    rw [Fin.eq_one_of_ne_zero j (by simpa only [mem_singleton_iff] using hj)]
    simpa [g] using even_two.convexOn_pow (𝕜 := ℝ)
  have hhc : ConvexOn ℝ Set.univ h := by
    simpa [h, Pi.add_def, Function.comp_def] using
      ((even_two.convexOn_pow (𝕜 := ℝ)).comp_linearMap (LinearMap.proj (R := ℝ) 0)).add
        ((LinearMap.proj (R := ℝ) 1).convexOn convex_univ)
  have hD : ∀ _ : Fin 1, ∀ v : Fin 2 → ℝ,
      0 ≤ v → (∀ j ∈ ({0} : Set (Fin 2)), v j = 0) → 0 ≤ Dh0 v :=
    fun _ => (forall_map_nonneg_iff_map_single_nonneg {0} Dh0).2 fun j hj => by
      rw [Fin.eq_one_of_ne_zero j (by simpa only [mem_singleton_iff] using hj)]
      norm_num [Dh0]
  have hcmp := affine_coordinate_comparison (J := ({0} : Set (Fin 2))) 2 (mapsTo_univ g Set.univ)
    (fun i x _ j hj => haff i x j hj) hc hhc (fun _ => mem_univ _) hg hh hD
  exact ⟨g, h, a, fun _ => Dg0, fun _ => Dh0, haff, hc, hhc, hg, hh, hD,
    hnotmono, hnotSub, by simpa using hcmp⟩

end Separation

end TauCeti
