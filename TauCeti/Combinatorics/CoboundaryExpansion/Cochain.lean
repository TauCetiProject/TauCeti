/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.ConjInvariant
public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Orientation
public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Relabel
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Basic.Real.Pointwise
import Mathlib.Tactic.Group

/-!
# Group-valued 1-cochains, gauge distance, and triangle defect

For a finite 2-complex `X : TwoComplex V` and a not-necessarily-abelian group `G`, a 1-cochain
`α : Cochain X G` assigns to each ordered pair of adjacent vertices `(u, v)` an element
`α u v : G` satisfying `α v u = (α u v)⁻¹`, normalized to `1` off the edges of `X`.

Given a `LinearOrder V` and a group norm `ℓ : GroupNorm G`:

* `α.holonomy u v w = α u v * α v w * α w u` is the nonabelian coboundary around `(u, v, w)`;
* `α.defect ℓ` sums `ℓ (α.holonomy u v w)` over increasing triangles `u < v < w`;
* `α.cost ℓ β` sums `ℓ ((β u)⁻¹ * α u v * β v)` over increasing edges `u < v` for a gauge
  `β : V → G`;
* `α.gaugeDist ℓ` is the infimum of `α.cost ℓ β` over all gauges `β : V → G`;
* `α.IsCoboundary` states that some gauge trivializes every edge (`α u v = β u * (β v)⁻¹`).

The gauge group `V → G` acts on the right via `(β • α) u v = (β u)⁻¹ * α u v * β v` on edges, so
`β • (γ • α) = (γ * β) • α`. Edge costs and `gaugeDist` are independent of the chosen linear order
on `V` and invariant under vertex relabellings and gauge transformations for every `GroupNorm`.
When `ℓ` is conjugation invariant (`ℓ.toGroupSeminorm.IsConjInvariant`), `defect` also enjoys all
three invariances, and restricting gauges by `β v₀ = 1` at a base vertex `v₀` preserves
`gaugeDist`. For `[Finite G]`, the infimum defining `gaugeDist` is attained and vanishes precisely
on coboundaries.

## References

* Michael Chapman and Alex Lubotzky, *Stability of homomorphisms, coverings and cocycles II:
  Examples, applications and open problems*
* Julien Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for
  Every k ≥ 4*
-/

public section

open Finset

namespace TauCeti

/-- A `G`-valued 1-cochain on a finite 2-complex `X`: a function on ordered pairs of vertices
that inverts upon reversing each edge and takes value `1` on non-edges. Normalizing off the edges
eliminates unconstrained data, so two cochains are equal iff they agree on adjacent pairs and
`α u u = 1` holds unconditionally. -/
structure Cochain {V : Type*} (X : TwoComplex V) (G : Type*) [Group G] where
  /-- The group element assigned to an ordered pair of vertices `(u, v)`. -/
  toFun : V → V → G
  /-- Reversing an oriented edge inverts its assigned group element. -/
  map_symm' : ∀ u v, X.Adj u v → toFun v u = (toFun u v)⁻¹
  /-- Vertex pairs not spanning an edge of `X` carry `1`. -/
  map_of_not_adj' : ∀ u v, ¬ X.Adj u v → toFun u v = 1

namespace Cochain

section Basic

variable {V W U G H K : Type*} [Group G] [Group H] [Group K] {X Y : TwoComplex V}

attribute [coe] toFun

/-- Coerce a cochain to its underlying edge-evaluation function `V → V → G`. -/
instance : CoeFun (Cochain X G) (fun _ => V → V → G) where
  coe := Cochain.toFun

/-- Coercing an explicit `Cochain` constructor recovers its function field. -/
@[simp]
theorem coe_mk (f : V → V → G) (h₁ h₂) :
    ((⟨f, h₁, h₂⟩ : Cochain X G) : V → V → G) = f := by
  rfl

/-- Two cochains are equal when they agree on all vertex pairs. -/
@[ext]
theorem ext {α₁ α₂ : Cochain X G} (h : ∀ u v, α₁ u v = α₂ u v) : α₁ = α₂ := by
  cases α₁; cases α₂; congr; ext u v; exact h u v

/-- Reversing an oriented edge inverts a cochain's value. -/
theorem map_symm (α : Cochain X G) {u v : V} (h : X.Adj u v) : α v u = (α u v)⁻¹ :=
  α.map_symm' u v h

/-- Reversing an edge written as a 2-element `Finset` inverts a cochain's value. -/
theorem inv_symm [DecidableEq V] (α : Cochain X G) (u v : V)
    (h : ({u, v} : Finset V) ∈ X.edges) : α v u = (α u v)⁻¹ :=
  α.map_symm ((X.pair_mem_edges_iff u v).mp h)

/-- Pairs that do not span an edge carry `1`. -/
theorem map_of_not_adj (α : Cochain X G) {u v : V} (h : ¬ X.Adj u v) : α u v = 1 :=
  α.map_of_not_adj' u v h

/-- Every diagonal pair `(u, u)` carries `1`. -/
@[simp]
theorem apply_self (α : Cochain X G) (u : V) : α u u = 1 :=
  α.map_of_not_adj (X.not_adj_self u)

/-- Two cochains are equal as soon as they agree on adjacent vertex pairs. -/
theorem ext_adj {α₁ α₂ : Cochain X G} (h : ∀ u v, X.Adj u v → α₁ u v = α₂ u v) : α₁ = α₂ := by
  ext u v
  by_cases hadj : X.Adj u v
  · exact h u v hadj
  · rw [α₁.map_of_not_adj hadj, α₂.map_of_not_adj hadj]

/-- Two cochains are equal as soon as they agree on strictly increasing edges `u < v`. -/
theorem ext_lt [LinearOrder V] {α₁ α₂ : Cochain X G}
    (h : ∀ u v, u < v → X.Adj u v → α₁ u v = α₂ u v) : α₁ = α₂ := by
  refine ext_adj fun u v hadj => ?_
  rcases lt_or_gt_of_ne hadj.ne with hlt | hgt
  · exact h u v hlt hadj
  · rw [α₁.map_symm hadj.symm, α₂.map_symm hadj.symm, h v u hgt hadj.symm]

/-- The trivial cochain assigning `1` to every pair. -/
instance : One (Cochain X G) where
  one :=
    { toFun := fun _ _ => 1
      map_symm' := fun _ _ _ => inv_one.symm
      map_of_not_adj' := fun _ _ _ => rfl }

/-- Cochains are inhabited by the trivial cochain `1`. -/
instance : Inhabited (Cochain X G) := ⟨1⟩

/-- The trivial cochain evaluates to `1` everywhere. -/
@[simp]
theorem one_apply (u v : V) : (1 : Cochain X G) u v = 1 := by
  rfl

/-- Construct a cochain from arbitrary values on increasing pairs `u < v`, extending to `v < u`
by inversion and to non-edges by `1`. -/
noncomputable def ofLt [LinearOrder V] (X : TwoComplex V) (f : V → V → G) : Cochain X G where
  toFun u v := open scoped Classical in
    if X.Adj u v then (if u < v then f u v else (f v u)⁻¹) else 1
  map_symm' u v hadj := by
    simp only [hadj, hadj.symm, ↓reduceIte]
    rcases lt_or_gt_of_ne hadj.ne with hlt | hgt
    · simp [hlt, asymm hlt]
    · simp [hgt, asymm hgt]
  map_of_not_adj' u v hnot := by simp [hnot]

/-- On an increasing edge `u < v`, `ofLt X f` takes the prescribed value `f u v`. -/
@[simp]
theorem ofLt_apply_of_lt [LinearOrder V] (f : V → V → G) {u v : V}
    (hlt : u < v) (hadj : X.Adj u v) : ofLt X f u v = f u v := by
  simp [ofLt, hadj, hlt]

/-- On a decreasing edge `v < u`, `ofLt X f` takes the inverted value `(f v u)⁻¹`. -/
@[simp]
theorem ofLt_apply_of_gt [LinearOrder V] (f : V → V → G) {u v : V}
    (hgt : v < u) (hadj : X.Adj u v) : ofLt X f u v = (f v u)⁻¹ := by
  simp [ofLt, hadj, asymm hgt]

/-- Off the edges of `X`, `ofLt X f` evaluates to `1`. -/
@[simp]
theorem ofLt_apply_of_not_adj [LinearOrder V] (f : V → V → G) {u v : V}
    (hnot : ¬ X.Adj u v) : ofLt X f u v = 1 := by
  simp [ofLt, hnot]

/-- Transport a cochain across an equality of two-complexes on the same vertex type without
changing its underlying function. -/
def cast (h : X = Y) (α : Cochain X G) : Cochain Y G where
  toFun := α
  map_symm' _ _ hadj := α.map_symm (h ▸ hadj)
  map_of_not_adj' _ _ hnot := α.map_of_not_adj (h ▸ hnot)

/-- `Cochain.cast` acts as the identity on underlying vertex-pair evaluations. -/
@[simp]
theorem cast_apply (h : X = Y) (α : Cochain X G) (u v : V) : α.cast h u v = α u v := by
  rfl

/-- Casting along `rfl` returns the same cochain. -/
@[simp]
theorem cast_rfl (α : Cochain X G) : α.cast rfl = α := by
  rfl

/-- When `G` is finite, `Cochain X G` is finite even if the ambient vertex type `V` is infinite,
because `X.edges` involves only finitely many vertices. -/
instance [Finite G] : Finite (Cochain X G) := by
  classical
  let S : Finset V := X.edges.biUnion id
  refine Finite.of_injective (fun (α : Cochain X G) (p : S × S) => α p.1.1 p.2.1) ?_
  intro α₁ α₂ h
  refine ext_adj fun u v hadj => ?_
  have he : ({u, v} : Finset V) ∈ X.edges := (X.pair_mem_edges_iff u v).mpr hadj
  have hu : u ∈ S := mem_biUnion.mpr ⟨{u, v}, he, by simp⟩
  have hv : v ∈ S := mem_biUnion.mpr ⟨{u, v}, he, by simp⟩
  exact congr_fun h (⟨u, hu⟩, ⟨v, hv⟩)

/-! ### Gauge action, coboundaries, holonomy, defect, cost, and gauge distance -/

/-- A gauge `β : V → G` acts on a cochain `α` by conjugating edge values:
`(β • α) u v = (β u)⁻¹ * α u v * β v` on edges and `1` off edges. -/
noncomputable instance : SMul (V → G) (Cochain X G) where
  smul β α :=
    { toFun := fun u v => open scoped Classical in
        if X.Adj u v then (β u)⁻¹ * α u v * β v else 1
      map_symm' := fun u v hadj => by
        simp only [hadj, hadj.symm, ↓reduceIte, α.map_symm hadj]
        group
      map_of_not_adj' := fun _ _ hnot => by simp [hnot] }

/-- On an edge, `β • α` evaluates to `(β u)⁻¹ * α u v * β v`. -/
@[simp]
theorem smul_apply_of_adj (β : V → G) (α : Cochain X G) {u v : V} (h : X.Adj u v) :
    (β • α) u v = (β u)⁻¹ * α u v * β v := by
  simp [HSMul.hSMul, SMul.smul, h]

/-- Off the edges of `X`, `β • α` evaluates to `1`. -/
@[simp]
theorem smul_apply_of_not_adj (β : V → G) (α : Cochain X G) {u v : V} (h : ¬ X.Adj u v) :
    (β • α) u v = 1 := by
  simp [HSMul.hSMul, SMul.smul, h]

/-- The trivial gauge `1` acts as the identity on cochains. -/
@[simp]
protected theorem one_smul (α : Cochain X G) : (1 : V → G) • α = α := by
  refine ext_adj fun u v hadj => ?_
  simp [hadj]

/-- Successive gauge transformations compose in right-action order:
`β • (γ • α) = (γ * β) • α`, where `(γ * β) u = γ u * β u`. -/
protected theorem smul_smul (β γ : V → G) (α : Cochain X G) :
    β • (γ • α) = (γ * β) • α := by
  refine ext_adj fun u v hadj => ?_
  simp only [smul_apply_of_adj _ _ hadj, Pi.mul_apply]
  group

/-- A gauge transformation by `β` followed by `β⁻¹` restores the cochain. -/
@[simp]
theorem inv_smul_smul (β : V → G) (α : Cochain X G) : β⁻¹ • (β • α) = α := by
  rw [Cochain.smul_smul, mul_inv_cancel, Cochain.one_smul]

/-- A gauge transformation by `β⁻¹` followed by `β` restores the cochain. -/
@[simp]
theorem smul_inv_smul (β : V → G) (α : Cochain X G) : β • (β⁻¹ • α) = α := by
  rw [Cochain.smul_smul, inv_mul_cancel, Cochain.one_smul]

/-- A cochain is a coboundary when some vertex potential `β : V → G` satisfies
`α u v = β u * (β v)⁻¹` on every edge. -/
def IsCoboundary (α : Cochain X G) : Prop :=
  ∃ β : V → G, ∀ u v, X.Adj u v → α u v = β u * (β v)⁻¹

/-- Unfold `IsCoboundary` to an explicit potential on adjacent vertices. -/
theorem isCoboundary_def (α : Cochain X G) :
    α.IsCoboundary ↔ ∃ β : V → G, ∀ u v, X.Adj u v → α u v = β u * (β v)⁻¹ := by
  rfl

/-- Formulation of `IsCoboundary` in terms of 2-element edge `Finset`s. -/
theorem isCoboundary_iff_pair_mem_edges [DecidableEq V] (α : Cochain X G) :
    α.IsCoboundary ↔
      ∃ β : V → G, ∀ u v, ({u, v} : Finset V) ∈ X.edges → α u v = β u * (β v)⁻¹ := by
  simp [IsCoboundary]

/-- A cochain is a coboundary precisely when some gauge transforms it into `1`. -/
theorem isCoboundary_iff_exists_smul_eq_one (α : Cochain X G) :
    α.IsCoboundary ↔ ∃ β : V → G, β • α = 1 := by
  refine exists_congr fun β => ⟨fun h => ext_adj fun u v hadj => ?_, fun h u v hadj => ?_⟩
  · rw [smul_apply_of_adj _ _ hadj, h u v hadj, one_apply]
    group
  · have huv : (β u)⁻¹ * α u v * β v = 1 := by
      simpa [smul_apply_of_adj _ _ hadj] using congr_fun (congr_fun (congrArg toFun h) u) v
    calc
      α u v = β u * ((β u)⁻¹ * α u v * β v) * (β v)⁻¹ := by group
      _ = β u * (β v)⁻¹ := by rw [huv, mul_one]

/-- The trivial cochain `1` is a coboundary. -/
@[simp]
theorem isCoboundary_one : (1 : Cochain X G).IsCoboundary :=
  (isCoboundary_iff_exists_smul_eq_one 1).mpr ⟨1, Cochain.one_smul 1⟩

/-- Being a coboundary is invariant under gauge transformations. -/
@[simp]
theorem isCoboundary_smul_iff (β : V → G) (α : Cochain X G) :
    (β • α).IsCoboundary ↔ α.IsCoboundary := by
  simp only [isCoboundary_iff_exists_smul_eq_one]
  refine ⟨fun ⟨γ, hγ⟩ => ⟨β * γ, by rwa [← Cochain.smul_smul]⟩,
    fun ⟨γ, hγ⟩ => ⟨β⁻¹ * γ, by rw [← Cochain.smul_smul, inv_smul_smul, hγ]⟩⟩

/-- The holonomy of `α` around an ordered triple `(u, v, w)` is `α u v * α v w * α w u`. -/
def holonomy (α : Cochain X G) (u v w : V) : G :=
  α u v * α v w * α w u

/-- Unfold `holonomy` into the product of the three cyclic edge values. -/
theorem holonomy_def (α : Cochain X G) (u v w : V) :
    α.holonomy u v w = α u v * α v w * α w u := by
  rfl

/-- The holonomy of the trivial cochain `1` is `1`. -/
@[simp]
theorem holonomy_one (u v w : V) : (1 : Cochain X G).holonomy u v w = 1 := by
  simp [holonomy]

/-- `Cochain.cast` preserves holonomies. -/
@[simp]
theorem holonomy_cast (h : X = Y) (α : Cochain X G) (u v w : V) :
    (α.cast h).holonomy u v w = α.holonomy u v w := by
  rfl

/-- The triangle defect `N` of `α` under `ℓ`: the sum of `ℓ (α.holonomy u v w)` over the
increasing triangles `u < v < w` of `X`. -/
noncomputable def defect [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) : ℝ :=
  ∑ p ∈ X.orderedTriangles, ℓ (α.holonomy p.1 p.2.1 p.2.2)

/-- Unfold `defect` as the sum over `X.orderedTriangles`. -/
theorem defect_def [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) :
    α.defect ℓ = ∑ p ∈ X.orderedTriangles, ℓ (α.holonomy p.1 p.2.1 p.2.2) := by
  rfl

/-- On a complex with no triangles, every cochain has defect `0`. -/
theorem defect_of_triangles_eq_empty [LinearOrder V] (hX : X.triangles = ∅)
    (ℓ : GroupNorm G) (α : Cochain X G) : α.defect ℓ = 0 := by
  refine sum_eq_zero fun p hp => ?_
  exfalso
  have ht := (X.mem_orderedTriangles p).mp hp |>.2.2
  simp [hX] at ht

/-- On a finite vertex type, `defect` agrees with summing over `univ.filter`. -/
theorem defect_eq_sum_filter_univ [Fintype V] [LinearOrder V]
    (ℓ : GroupNorm G) (α : Cochain X G) :
    α.defect ℓ =
      ∑ p ∈ univ.filter (fun p : V × V × V =>
          p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles),
        ℓ (α p.1 p.2.1 * α p.2.1 p.2.2 * α p.2.2 p.1) := by
  rw [defect, X.orderedTriangles_eq_filter_univ]
  rfl

/-- The cost of a gauge `β` for `α` under `ℓ`: the sum of `ℓ ((β u)⁻¹ * α u v * β v)` over the
increasing edges `u < v` of `X`. -/
noncomputable def cost [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) : ℝ :=
  ∑ p ∈ X.orderedEdges, ℓ ((β p.1)⁻¹ * α p.1 p.2 * β p.2)

/-- Unfold `cost` as the sum over `X.orderedEdges`. -/
theorem cost_def [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.cost ℓ β = ∑ p ∈ X.orderedEdges, ℓ ((β p.1)⁻¹ * α p.1 p.2 * β p.2) := by
  rfl

/-- On a finite vertex type, `cost` agrees with summing over `univ.filter`. -/
theorem cost_eq_sum_filter_univ [Fintype V] [LinearOrder V]
    (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.cost ℓ β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
        ℓ ((β p.1)⁻¹ * α p.1 p.2 * β p.2) := by
  rw [cost, X.orderedEdges_eq_filter_univ]

/-- The gauge distance `D` from `α` to coboundaries under `ℓ`: the infimum of `α.cost ℓ β` over
all gauges `β : V → G`. -/
noncomputable def gaugeDist [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) : ℝ :=
  ⨅ β : V → G, α.cost ℓ β

/-- Unfold `gaugeDist` as the infimum of `cost` over all gauges. -/
theorem gaugeDist_def [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) :
    α.gaugeDist ℓ = ⨅ β : V → G, α.cost ℓ β := by
  rfl

/-- `Cochain.cast` preserves `defect`. -/
@[simp]
theorem defect_cast [LinearOrder V] (h : X = Y) (ℓ : GroupNorm G) (α : Cochain X G) :
    (α.cast h).defect ℓ = α.defect ℓ := by
  subst h; rfl

/-- `Cochain.cast` preserves `cost`. -/
@[simp]
theorem cost_cast [LinearOrder V] (h : X = Y) (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    (α.cast h).cost ℓ β = α.cost ℓ β := by
  subst h; rfl

/-- `Cochain.cast` preserves `gaugeDist`. -/
@[simp]
theorem gaugeDist_cast [LinearOrder V] (h : X = Y) (ℓ : GroupNorm G) (α : Cochain X G) :
    (α.cast h).gaugeDist ℓ = α.gaugeDist ℓ := by
  subst h; rfl

/-- The defect of any cochain is nonnegative. -/
theorem defect_nonneg [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) :
    0 ≤ α.defect ℓ :=
  sum_nonneg fun _ _ => apply_nonneg ℓ _

/-- The defect of the trivial cochain `1` is `0`. -/
@[simp]
theorem defect_one [LinearOrder V] (ℓ : GroupNorm G) :
    (1 : Cochain X G).defect ℓ = 0 := by
  simp [defect]

/-- Every gauge cost is nonnegative. -/
theorem cost_nonneg [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    0 ≤ α.cost ℓ β :=
  sum_nonneg fun _ _ => apply_nonneg ℓ _

/-- The range of `α.cost ℓ` is bounded below by `0`. -/
theorem bddBelow_range_cost [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) :
    BddBelow (Set.range (α.cost ℓ)) :=
  ⟨0, by rintro _ ⟨β, rfl⟩; exact α.cost_nonneg ℓ β⟩

/-- The gauge distance is at most the cost of any given gauge. -/
theorem gaugeDist_le_cost [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.gaugeDist ℓ ≤ α.cost ℓ β :=
  ciInf_le (α.bddBelow_range_cost ℓ) β

/-- The gauge distance of any cochain is nonnegative. -/
theorem gaugeDist_nonneg [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) :
    0 ≤ α.gaugeDist ℓ :=
  le_ciInf fun β => α.cost_nonneg ℓ β

/-- A lower bound on every gauge cost is a lower bound on `gaugeDist`. -/
theorem le_gaugeDist [LinearOrder V] {ℓ : GroupNorm G} {α : Cochain X G} {r : ℝ}
    (h : ∀ β : V → G, r ≤ α.cost ℓ β) : r ≤ α.gaugeDist ℓ :=
  le_ciInf h

/-- A gauge has cost `0` iff it transforms `α` into `1`. -/
theorem cost_eq_zero_iff [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.cost ℓ β = 0 ↔ β • α = 1 := by
  rw [cost, sum_eq_zero_iff_of_nonneg (fun _ _ => apply_nonneg ℓ _)]
  simp only [Prod.forall, TwoComplex.mem_orderedEdges, map_eq_zero_iff_eq_one, and_imp]
  refine ⟨fun h => ext_lt fun u v hlt hadj => ?_, fun h u v _ hadj => ?_⟩
  · rw [smul_apply_of_adj _ _ hadj, one_apply, h u v hlt hadj]
  · simpa [smul_apply_of_adj _ _ hadj] using congr_fun (congr_fun (congrArg toFun h) u) v

/-- The trivial cochain `1` has cost `0` at gauge `1`. -/
@[simp]
theorem cost_one_one [LinearOrder V] (ℓ : GroupNorm G) :
    (1 : Cochain X G).cost ℓ 1 = 0 := by
  rw [cost_eq_zero_iff, Cochain.one_smul]

/-- Every coboundary has gauge distance `0`. -/
theorem IsCoboundary.gaugeDist_eq_zero [LinearOrder V] {α : Cochain X G}
    (hα : α.IsCoboundary) (ℓ : GroupNorm G) : α.gaugeDist ℓ = 0 := by
  obtain ⟨β, hβ⟩ := (isCoboundary_iff_exists_smul_eq_one α).mp hα
  exact le_antisymm
    ((α.gaugeDist_le_cost ℓ β).trans_eq ((α.cost_eq_zero_iff ℓ β).mpr hβ))
    (α.gaugeDist_nonneg ℓ)

/-- The trivial cochain `1` has gauge distance `0`. -/
@[simp]
theorem gaugeDist_one [LinearOrder V] (ℓ : GroupNorm G) :
    (1 : Cochain X G).gaugeDist ℓ = 0 :=
  isCoboundary_one.gaugeDist_eq_zero ℓ

/-! ### Orientation and relabelling independence -/

/-- Reversing an edge inverts the gauge-twisted edge element, hence preserves its group norm
even without conjugation invariance. -/
theorem norm_inv_mul_mul_symm (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G)
    {u v : V} (hadj : X.Adj u v) :
    ℓ ((β v)⁻¹ * α v u * β u) = ℓ ((β u)⁻¹ * α u v * β v) := by
  have hinv : (β v)⁻¹ * α v u * β u = ((β u)⁻¹ * α u v * β v)⁻¹ := by
    rw [α.map_symm hadj]
    group
  rw [hinv, map_inv_eq_map]

/-- Twice the cost of a gauge equals the unoriented sum over both directions of every edge. -/
theorem two_mul_cost [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    2 * α.cost ℓ β =
      ∑ e ∈ X.edges, ∑ u ∈ e, ∑ v ∈ e.erase u, ℓ ((β u)⁻¹ * α u v * β v) := by
  simpa [cost, two_nsmul, two_mul] using
    X.two_nsmul_sum_orderedEdges (fun u v => ℓ ((β u)⁻¹ * α u v * β v))
      (fun hadj => α.norm_inv_mul_mul_symm ℓ β hadj)

/-- Unoriented edge-sum formula for `cost`. -/
theorem cost_eq_half_sum_edges [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.cost ℓ β =
      (∑ e ∈ X.edges, ∑ u ∈ e, ∑ v ∈ e.erase u, ℓ ((β u)⁻¹ * α u v * β v)) / 2 := by
  linarith [α.two_mul_cost ℓ β]

/-- `cost` does not depend on the `LinearOrder` chosen on `V`. -/
theorem cost_congr_linearOrder (l₁ l₂ : LinearOrder V) (ℓ : GroupNorm G)
    (α : Cochain X G) (β : V → G) :
    @cost V G _ X l₁ ℓ α β = @cost V G _ X l₂ ℓ α β := by
  have h₁ := @two_mul_cost V G _ X l₁ ℓ α β
  have h₂ := @two_mul_cost V G _ X l₂ ℓ α β
  have herase : ∀ (e : Finset V) (u : V),
      @Finset.erase V l₁.toDecidableEq e u = @Finset.erase V l₂.toDecidableEq e u := by
    intro e u; ext x; simp
  simp_rw [herase] at h₁
  linarith

/-- `gaugeDist` does not depend on the `LinearOrder` chosen on `V`. -/
theorem gaugeDist_congr_linearOrder (l₁ l₂ : LinearOrder V) (ℓ : GroupNorm G)
    (α : Cochain X G) :
    @gaugeDist V G _ X l₁ ℓ α = @gaugeDist V G _ X l₂ ℓ α := by
  simp only [gaugeDist, cost_congr_linearOrder l₁ l₂]

/-- Under a conjugation-invariant group norm, cyclically rotating a triangle's vertices preserves
the norm of its holonomy. -/
theorem norm_holonomy_rotate {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (u v w : V) :
    ℓ (α.holonomy v w u) = ℓ (α.holonomy u v w) := by
  simpa [holonomy, mul_assoc] using hℓ.map_mul_comm (α v w * α w u) (α u v)

/-- On any triangle of `X`, reversing the direction of travel inverts the holonomy and therefore
preserves its group norm. -/
theorem norm_holonomy_swap_right (ℓ : GroupNorm G) (α : Cochain X G)
    {t : Finset V} (ht : t ∈ X.triangles) {u v w : V}
    (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t) (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u) :
    ℓ (α.holonomy u w v) = ℓ (α.holonomy u v w) := by
  have hadj_uv : X.Adj u v := X.adj_of_mem_triangles ht hu hv huv
  have hadj_vw : X.Adj v w := X.adj_of_mem_triangles ht hv hw hvw
  have hadj_wu : X.Adj w u := X.adj_of_mem_triangles ht hw hu hwu
  have hinv : α.holonomy u w v = (α.holonomy u v w)⁻¹ := by
    simp only [holonomy, α.map_symm hadj_wu, α.map_symm hadj_vw, α.map_symm hadj_uv]
    group
  rw [hinv, map_inv_eq_map]

/-- Under a conjugation-invariant group norm, six times `defect` equals the unoriented sum of
holonomy norms over all six ordered vertex triples of every triangle. -/
theorem six_mul_defect [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) :
    6 * α.defect ℓ =
      ∑ t ∈ X.triangles, ∑ u ∈ t, ∑ v ∈ t.erase u, ∑ w ∈ (t.erase u).erase v,
        ℓ (α.holonomy u v w) := by
  have h := X.six_nsmul_sum_orderedTriangles (fun u v w => ℓ (α.holonomy u v w))
    (fun {_} _ {u v w} _ _ _ _ _ _ => α.norm_holonomy_rotate hℓ u v w)
    (fun {_} ht {_ _ _} hu hv hw huv hvw hwu =>
      α.norm_holonomy_swap_right ℓ ht hu hv hw huv hvw hwu)
  rw [nsmul_eq_mul] at h
  exact_mod_cast h

/-- Unoriented triangle-sum formula for `defect` under a conjugation-invariant group norm. -/
theorem defect_eq_sixth_sum_triangles [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) :
    α.defect ℓ =
      (∑ t ∈ X.triangles, ∑ u ∈ t, ∑ v ∈ t.erase u, ∑ w ∈ (t.erase u).erase v,
        ℓ (α.holonomy u v w)) / 6 := by
  linarith [α.six_mul_defect hℓ]

/-- Under a conjugation-invariant group norm, `defect` does not depend on the `LinearOrder`
chosen on `V`. -/
theorem defect_congr_linearOrder (l₁ l₂ : LinearOrder V) {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) :
    @defect V G _ X l₁ ℓ α = @defect V G _ X l₂ ℓ α := by
  have h₁ := @six_mul_defect V G _ X l₁ ℓ hℓ α
  have h₂ := @six_mul_defect V G _ X l₂ ℓ hℓ α
  have herase : ∀ (s : Finset V) (u : V),
      @Finset.erase V l₁.toDecidableEq s u = @Finset.erase V l₂.toDecidableEq s u := by
    intro s u; ext x; simp
  simp_rw [herase] at h₁
  linarith

/-- Transport a cochain along a vertex bijection `e : V ≃ W`. -/
def relabel (α : Cochain X G) (e : V ≃ W) : Cochain (X.relabel e) G where
  toFun u v := α (e.symm u) (e.symm v)
  map_symm' u v hadj := α.map_symm ((X.adj_relabel_iff e u v).mp hadj)
  map_of_not_adj' u v hnot := α.map_of_not_adj (mt (X.adj_relabel_iff e u v).mpr hnot)

/-- Evaluating a relabelled cochain pulls back along `e.symm`. -/
@[simp]
theorem relabel_apply (α : Cochain X G) (e : V ≃ W) (u v : W) :
    α.relabel e u v = α (e.symm u) (e.symm v) := by
  rfl

/-- Evaluating `α.relabel e` at mapped vertices `(e u, e v)` recovers `α u v`. -/
theorem relabel_apply_equiv (α : Cochain X G) (e : V ≃ W) (u v : V) :
    α.relabel e (e u) (e v) = α u v := by
  simp

/-- Holonomy of a relabelled cochain at mapped vertices agrees with the original holonomy. -/
@[simp]
theorem holonomy_relabel_equiv (α : Cochain X G) (e : V ≃ W) (u v w : V) :
    (α.relabel e).holonomy (e u) (e v) (e w) = α.holonomy u v w := by
  simp [holonomy]

/-- Relabelling induces an equivalence between cochains on `X` and cochains on `X.relabel e`. -/
def relabelEquiv (X : TwoComplex V) (e : V ≃ W) :
    Cochain X G ≃ Cochain (X.relabel e) G where
  toFun α := α.relabel e
  invFun α' := (α'.relabel e.symm).cast (by simp)
  left_inv α := by ext u v; simp
  right_inv α' := by ext u v; simp

/-- Relabelling a cochain reindexes gauge costs along `e`, regardless of how `V` and `W` are
ordered. -/
theorem cost_relabel [LinearOrder V] [LinearOrder W] (ℓ : GroupNorm G)
    (α : Cochain X G) (e : V ≃ W) (β : W → G) :
    (α.relabel e).cost ℓ β = α.cost ℓ (β ∘ e) := by
  have h₁ := (α.relabel e).two_mul_cost ℓ β
  have h₂ := α.two_mul_cost ℓ (β ∘ e)
  simp only [Function.comp_apply] at h₂
  rw [X.sum_edges_relabel e] at h₁
  have hrhs :
      (∑ s ∈ X.edges, ∑ u ∈ s.map e.toEmbedding, ∑ v ∈ (s.map e.toEmbedding).erase u,
          ℓ ((β u)⁻¹ * α.relabel e u v * β v)) =
        ∑ s ∈ X.edges, ∑ u ∈ s, ∑ v ∈ s.erase u, ℓ ((β (e u))⁻¹ * α u v * β (e v)) := by
    refine sum_congr rfl fun s _ => ?_
    rw [sum_map]
    refine sum_congr rfl fun u _ => ?_
    simp only [Equiv.coe_toEmbedding]
    have herase : (s.map e.toEmbedding).erase (e u) = (s.erase u).map e.toEmbedding := by
      ext y
      simp only [mem_erase, mem_map, Equiv.coe_toEmbedding]
      exact ⟨fun ⟨hne, x, hx, hxy⟩ => ⟨x, ⟨fun hxu => hne (hxy ▸ congrArg e hxu), hx⟩, hxy⟩,
        fun ⟨x, ⟨hxu, hx⟩, hxy⟩ => ⟨hxy ▸ e.injective.ne hxu, x, hx, hxy⟩⟩
    rw [herase, sum_map]
    simp
  rw [hrhs] at h₁
  linarith [h₁, h₂]

/-- Relabelling a cochain preserves its gauge distance. -/
@[simp]
theorem gaugeDist_relabel [LinearOrder V] [LinearOrder W] (ℓ : GroupNorm G)
    (α : Cochain X G) (e : V ≃ W) :
    (α.relabel e).gaugeDist ℓ = α.gaugeDist ℓ := by
  simp only [gaugeDist, cost_relabel]
  exact (Equiv.arrowCongr e (Equiv.refl G)).symm.iInf_congr fun _ => rfl

/-- Under a conjugation-invariant group norm, relabelling a cochain preserves its triangle
defect. -/
theorem defect_relabel [LinearOrder V] [LinearOrder W] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (e : V ≃ W) :
    (α.relabel e).defect ℓ = α.defect ℓ := by
  have h₁ := (α.relabel e).six_mul_defect hℓ
  have h₂ := α.six_mul_defect hℓ
  rw [X.sum_triangles_relabel e] at h₁
  have herase : ∀ (s : Finset V) (u : V),
      (s.map e.toEmbedding).erase (e u) = (s.erase u).map e.toEmbedding := by
    intro s u
    ext y
    simp only [mem_erase, mem_map, Equiv.coe_toEmbedding]
    exact ⟨fun ⟨hne, x, hx, hxy⟩ => ⟨x, ⟨fun hxu => hne (hxy ▸ congrArg e hxu), hx⟩, hxy⟩,
      fun ⟨x, ⟨hxu, hx⟩, hxy⟩ => ⟨hxy ▸ e.injective.ne hxu, x, hx, hxy⟩⟩
  have hrhs :
      (∑ s ∈ X.triangles, ∑ u ∈ s.map e.toEmbedding, ∑ v ∈ (s.map e.toEmbedding).erase u,
          ∑ w ∈ ((s.map e.toEmbedding).erase u).erase v, ℓ ((α.relabel e).holonomy u v w)) =
        ∑ s ∈ X.triangles, ∑ u ∈ s, ∑ v ∈ s.erase u, ∑ w ∈ (s.erase u).erase v,
          ℓ (α.holonomy u v w) := by
    refine sum_congr rfl fun s _ => ?_
    rw [sum_map]
    refine sum_congr rfl fun u _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [herase, sum_map]
    refine sum_congr rfl fun v _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [herase, sum_map]
    simp
  rw [hrhs] at h₁
  linarith

/-- Transport a cochain on `TwoComplex.complete V` to `TwoComplex.complete W` along a bijection
`e : V ≃ W`. -/
noncomputable def relabelComplete [Fintype V] [Fintype W]
    (α : Cochain (TwoComplex.complete V) G) (e : V ≃ W) : Cochain (TwoComplex.complete W) G :=
  (α.relabel e).cast (TwoComplex.relabel_complete e)

/-- Evaluating `relabelComplete` pulls back along `e.symm`. -/
@[simp]
theorem relabelComplete_apply [Fintype V] [Fintype W]
    (α : Cochain (TwoComplex.complete V) G) (e : V ≃ W) (u v : W) :
    α.relabelComplete e u v = α (e.symm u) (e.symm v) := by
  rfl

/-- Relabelling a cochain on the complete complex reindexes gauge costs along `e`. -/
theorem cost_relabelComplete [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain (TwoComplex.complete V) G) (e : V ≃ W) (β : W → G) :
    (α.relabelComplete e).cost ℓ β = α.cost ℓ (β ∘ e) := by
  simp [relabelComplete, cost_relabel]

/-- Relabelling a cochain on the complete complex preserves its gauge distance. -/
@[simp]
theorem gaugeDist_relabelComplete [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain (TwoComplex.complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).gaugeDist ℓ = α.gaugeDist ℓ := by
  simp [relabelComplete]

/-- Under a conjugation-invariant group norm, relabelling a cochain on the complete complex
preserves its triangle defect. -/
theorem defect_relabelComplete [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain (TwoComplex.complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).defect ℓ = α.defect ℓ := by
  simp [relabelComplete, defect_relabel hℓ]

/-! ### Gauge invariance -/

/-- For every group norm `ℓ`, evaluating `cost` on `β • α` at gauge `γ` equals evaluating `cost`
on `α` at the product gauge `β * γ`. -/
@[simp]
theorem cost_smul [LinearOrder V] (ℓ : GroupNorm G) (β : V → G) (α : Cochain X G) (γ : V → G) :
    (β • α).cost ℓ γ = α.cost ℓ (β * γ) := by
  refine sum_congr rfl fun p hp => ?_
  have hadj : X.Adj p.1 p.2 := (X.mem_orderedEdges p).mp hp |>.2
  rw [smul_apply_of_adj _ _ hadj]
  congr 1
  simp only [Pi.mul_apply]
  group

/-- For every group norm `ℓ`, `gaugeDist` is invariant under gauge transformations. -/
@[simp]
theorem gaugeDist_smul [LinearOrder V] (ℓ : GroupNorm G) (β : V → G) (α : Cochain X G) :
    (β • α).gaugeDist ℓ = α.gaugeDist ℓ := by
  simp only [gaugeDist, cost_smul]
  exact (Equiv.mulLeft β).iInf_congr fun _ => rfl

/-- On any triangle of `X`, a gauge transformation `β • α` conjugates the holonomy at the base
vertex `u` by `β u`. -/
theorem holonomy_smul (β : V → G) (α : Cochain X G) {t : Finset V} (ht : t ∈ X.triangles)
    {u v w : V} (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t)
    (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u) :
    (β • α).holonomy u v w = (β u)⁻¹ * α.holonomy u v w * β u := by
  have hadj_uv : X.Adj u v := X.adj_of_mem_triangles ht hu hv huv
  have hadj_vw : X.Adj v w := X.adj_of_mem_triangles ht hv hw hvw
  have hadj_wu : X.Adj w u := X.adj_of_mem_triangles ht hw hu hwu
  simp only [holonomy, smul_apply_of_adj _ _ hadj_uv, smul_apply_of_adj _ _ hadj_vw,
    smul_apply_of_adj _ _ hadj_wu]
  group

/-- Under a conjugation-invariant group norm, `defect` is invariant under gauge transformations. -/
theorem defect_smul [LinearOrder V] {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (β : V → G) (α : Cochain X G) :
    (β • α).defect ℓ = α.defect ℓ := by
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨hlt12, hlt23, ht⟩ := (X.mem_orderedTriangles p).mp hp
  have hlt13 : p.1 < p.2.2 := hlt12.trans hlt23
  rw [holonomy_smul β α ht (by simp) (by simp) (by simp) hlt12.ne hlt23.ne hlt13.ne']
  exact hℓ.map_inv_mul_mul _ _

/-- Every coboundary has trivial holonomy on every triangle, without assuming conjugation
invariance. -/
theorem IsCoboundary.holonomy_eq_one {α : Cochain X G} (hα : α.IsCoboundary)
    {t : Finset V} (ht : t ∈ X.triangles) {u v w : V}
    (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t) (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u) :
    α.holonomy u v w = 1 := by
  obtain ⟨β, hβ⟩ := hα
  have hadj_uv : X.Adj u v := X.adj_of_mem_triangles ht hu hv huv
  have hadj_vw : X.Adj v w := X.adj_of_mem_triangles ht hv hw hvw
  have hadj_wu : X.Adj w u := X.adj_of_mem_triangles ht hw hu hwu
  simp only [holonomy, hβ u v hadj_uv, hβ v w hadj_vw, hβ w u hadj_wu]
  group

/-- Any cochain with a non-identity triangle holonomy is not a coboundary. -/
theorem not_isCoboundary_of_holonomy_ne_one {α : Cochain X G} {t : Finset V}
    (ht : t ∈ X.triangles) {u v w : V} (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t)
    (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u) (hhol : α.holonomy u v w ≠ 1) :
    ¬ α.IsCoboundary :=
  fun hcb => hhol (hcb.holonomy_eq_one ht hu hv hw huv hvw hwu)

/-- Every coboundary has triangle defect `0` under any group norm. -/
theorem IsCoboundary.defect_eq_zero [LinearOrder V] {α : Cochain X G}
    (hα : α.IsCoboundary) (ℓ : GroupNorm G) : α.defect ℓ = 0 := by
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨hlt12, hlt23, ht⟩ := (X.mem_orderedTriangles p).mp hp
  have hlt13 : p.1 < p.2.2 := hlt12.trans hlt23
  rw [hα.holonomy_eq_one ht (by simp) (by simp) (by simp) hlt12.ne hlt23.ne hlt13.ne',
    map_one_eq_zero]

/-- Under a conjugation-invariant group norm, the norm of an increasing triangle's holonomy is at
most the cost of any gauge `β`, since the three gauge-twisted edge elements multiply to a
conjugate of the holonomy. -/
theorem norm_holonomy_le_cost_of_lt [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (β : V → G)
    {u v w : V} (huv : u < v) (hvw : v < w) (ht : ({u, v, w} : Finset V) ∈ X.triangles) :
    ℓ (α.holonomy u v w) ≤ α.cost ℓ β := by
  have huw : u < w := huv.trans hvw
  have hadj_uv : X.Adj u v := X.adj_of_mem_triangles ht (by simp) (by simp) huv.ne
  have hadj_vw : X.Adj v w := X.adj_of_mem_triangles ht (by simp) (by simp) hvw.ne
  have hadj_uw : X.Adj u w := X.adj_of_mem_triangles ht (by simp) (by simp) huw.ne
  have hsub : ({(u, v), (v, w), (u, w)} : Finset (V × V)) ⊆ X.orderedEdges := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact (X.mem_orderedEdges _).mpr ⟨huv, hadj_uv⟩
    · exact (X.mem_orderedEdges _).mpr ⟨hvw, hadj_vw⟩
    · exact (X.mem_orderedEdges _).mpr ⟨huw, hadj_uw⟩
  have hsum_le :
      (∑ p ∈ ({(u, v), (v, w), (u, w)} : Finset (V × V)), ℓ ((β p.1)⁻¹ * α p.1 p.2 * β p.2)) ≤
        α.cost ℓ β :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => apply_nonneg ℓ _
  rw [sum_insert (by simp [huv.ne, hvw.ne]), sum_pair (by simp [huv.ne'])] at hsum_le
  have hprod : ((β u)⁻¹ * α u v * β v) * ((β v)⁻¹ * α v w * β w) * ((β w)⁻¹ * α w u * β u) =
      (β u)⁻¹ * α.holonomy u v w * β u := by
    rw [holonomy]
    group
  have htri1 := map_mul_le_add ℓ
    (((β u)⁻¹ * α u v * β v) * ((β v)⁻¹ * α v w * β w))
    ((β w)⁻¹ * α w u * β u)
  have htri2 := map_mul_le_add ℓ ((β u)⁻¹ * α u v * β v) ((β v)⁻¹ * α v w * β w)
  have hconj : ℓ ((β u)⁻¹ * α.holonomy u v w * β u) = ℓ (α.holonomy u v w) :=
    hℓ.map_inv_mul_mul _ _
  have hwu : ℓ ((β w)⁻¹ * α w u * β u) = ℓ ((β u)⁻¹ * α u w * β w) :=
    α.norm_inv_mul_mul_symm ℓ β hadj_uw
  rw [hprod, hconj, hwu] at htri1
  linarith

/-- Under a conjugation-invariant group norm, the norm of an increasing triangle's holonomy is a
lower bound on `gaugeDist` (for any coefficient group `G`, finite or infinite). -/
theorem norm_holonomy_le_gaugeDist_of_lt [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G)
    {u v w : V} (huv : u < v) (hvw : v < w) (ht : ({u, v, w} : Finset V) ∈ X.triangles) :
    ℓ (α.holonomy u v w) ≤ α.gaugeDist ℓ :=
  le_ciInf fun β => α.norm_holonomy_le_cost_of_lt hℓ β huv hvw ht

/-- Under a conjugation-invariant group norm, multiplying a gauge on the right by a constant group
element conjugates every edge term and hence leaves `cost` unchanged. -/
theorem cost_mul_const [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (β : V → G) (g : G) :
    α.cost ℓ (fun v => β v * g) = α.cost ℓ β := by
  refine sum_congr rfl fun p _ => ?_
  have hconj : (β p.1 * g)⁻¹ * α p.1 p.2 * (β p.2 * g) =
      g⁻¹ * ((β p.1)⁻¹ * α p.1 p.2 * β p.2) * g := by group
  rw [hconj]
  exact hℓ.map_inv_mul_mul _ _

/-- Under a conjugation-invariant group norm, every constant gauge has the same cost as `1`. -/
theorem cost_const [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (g : G) :
    α.cost ℓ (Function.const V g) = α.cost ℓ 1 := by
  simpa [Function.const_def] using α.cost_mul_const hℓ 1 g

/-- Under a conjugation-invariant group norm, restricting gauges to satisfy `β v₀ = 1` at a base
vertex `v₀` does not change the infimum defining `gaugeDist`. -/
theorem gaugeDist_eq_iInf_apply_eq_one [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (v₀ : V) :
    α.gaugeDist ℓ = ⨅ β : {β : V → G // β v₀ = 1}, α.cost ℓ β.1 := by
  have hne : Nonempty {β : V → G // β v₀ = 1} := ⟨⟨1, rfl⟩⟩
  have hbdd : BddBelow (Set.range fun β : {β : V → G // β v₀ = 1} => α.cost ℓ β.1) :=
    ⟨0, by rintro _ ⟨β, rfl⟩; exact α.cost_nonneg ℓ β.1⟩
  refine le_antisymm (le_ciInf fun β => α.gaugeDist_le_cost ℓ β.1) (le_ciInf fun β => ?_)
  let β' : {γ : V → G // γ v₀ = 1} := ⟨fun v => β v * (β v₀)⁻¹, mul_inv_cancel (β v₀)⟩
  exact (ciInf_le hbdd β').trans_eq (α.cost_mul_const hℓ β (β v₀)⁻¹)

/-! ### Finite coefficients -/

/-- When `G` is finite, `α.cost ℓ` takes only finitely many values as the gauge ranges over
`V → G`, since `X.orderedEdges` touches only finitely many vertices. -/
theorem finite_range_cost [LinearOrder V] [Finite G] (ℓ : GroupNorm G) (α : Cochain X G) :
    (Set.range (α.cost ℓ)).Finite := by
  let S : Finset V := X.edges.biUnion id
  let extend : (S → G) → (V → G) := fun γ v => if hv : v ∈ S then γ ⟨v, hv⟩ else 1
  refine (Set.finite_range (fun γ : S → G => α.cost ℓ (extend γ))).subset ?_
  rintro _ ⟨β, rfl⟩
  refine ⟨fun x => β x.1, ?_⟩
  refine sum_congr rfl fun p hp => ?_
  have hadj : X.Adj p.1 p.2 := (X.mem_orderedEdges p).mp hp |>.2
  have he : ({p.1, p.2} : Finset V) ∈ X.edges := (X.pair_mem_edges_iff p.1 p.2).mpr hadj
  have hp1 : p.1 ∈ S := mem_biUnion.mpr ⟨{p.1, p.2}, he, by simp⟩
  have hp2 : p.2 ∈ S := mem_biUnion.mpr ⟨{p.1, p.2}, he, by simp⟩
  simp [extend, hp1, hp2]

/-- For finite `G`, the infimum defining `gaugeDist` is attained by some gauge. -/
theorem exists_cost_eq_gaugeDist [LinearOrder V] [Finite G]
    (ℓ : GroupNorm G) (α : Cochain X G) :
    ∃ β : V → G, α.cost ℓ β = α.gaugeDist ℓ := by
  have hmem : sInf (Set.range (α.cost ℓ)) ∈ Set.range (α.cost ℓ) :=
    (Set.range_nonempty (α.cost ℓ)).csInf_mem (α.finite_range_cost ℓ)
  simpa [gaugeDist, sInf_range] using hmem

/-- For finite `G` and a conjugation-invariant group norm, `gaugeDist` is attained by a gauge
pinned to `1` at any chosen base vertex `v₀`. -/
theorem exists_cost_eq_gaugeDist_and_apply_eq_one [LinearOrder V] [Finite G]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (v₀ : V) :
    ∃ β : V → G, β v₀ = 1 ∧ α.cost ℓ β = α.gaugeDist ℓ := by
  obtain ⟨β, hβ⟩ := α.exists_cost_eq_gaugeDist ℓ
  exact ⟨fun v => β v * (β v₀)⁻¹, mul_inv_cancel (β v₀),
    (α.cost_mul_const hℓ β (β v₀)⁻¹).trans hβ⟩

/-- For finite `G`, a cochain has gauge distance `0` iff it is a coboundary. -/
theorem gaugeDist_eq_zero_iff [LinearOrder V] [Finite G]
    (ℓ : GroupNorm G) (α : Cochain X G) :
    α.gaugeDist ℓ = 0 ↔ α.IsCoboundary := by
  refine ⟨fun h => ?_, fun h => h.gaugeDist_eq_zero ℓ⟩
  obtain ⟨β, hβ⟩ := α.exists_cost_eq_gaugeDist ℓ
  exact (isCoboundary_iff_exists_smul_eq_one α).mpr ⟨β, (α.cost_eq_zero_iff ℓ β).mp (hβ.trans h)⟩

/-- For finite `G`, a cochain has strictly positive gauge distance iff it is not a coboundary. -/
theorem gaugeDist_pos_iff [LinearOrder V] [Finite G]
    (ℓ : GroupNorm G) (α : Cochain X G) :
    0 < α.gaugeDist ℓ ↔ ¬ α.IsCoboundary := by
  rw [← α.gaugeDist_eq_zero_iff ℓ]
  exact ⟨ne_of_gt, fun h => lt_of_le_of_ne (α.gaugeDist_nonneg ℓ) (Ne.symm h)⟩

/-- Over a finite group `G`, any cochain with a non-identity triangle holonomy has strictly
positive gauge distance (without assuming conjugation invariance). -/
theorem gaugeDist_pos_of_holonomy_ne_one [LinearOrder V] [Finite G] (ℓ : GroupNorm G)
    {α : Cochain X G} {t : Finset V} (ht : t ∈ X.triangles) {u v w : V}
    (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t) (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u)
    (hhol : α.holonomy u v w ≠ 1) :
    0 < α.gaugeDist ℓ :=
  (α.gaugeDist_pos_iff ℓ).mpr (α.not_isCoboundary_of_holonomy_ne_one ht hu hv hw huv hvw hwu hhol)

/-- On finite vertex and coefficient types, `gaugeDist` is the `Finset.inf'` of `cost` over all
gauges. -/
theorem gaugeDist_eq_inf'_univ [Fintype V] [LinearOrder V] [Fintype G]
    (ℓ : GroupNorm G) (α : Cochain X G) :
    α.gaugeDist ℓ = univ.inf' univ_nonempty (α.cost ℓ) := by
  refine le_antisymm (le_inf' _ _ fun β _ => α.gaugeDist_le_cost ℓ β) ?_
  obtain ⟨β, hβ⟩ := α.exists_cost_eq_gaugeDist ℓ
  exact (inf'_le (α.cost ℓ) (mem_univ β)).trans_eq hβ

/-- On finite vertex and coefficient types and under a conjugation-invariant group norm,
`gaugeDist` equals the `Finset.inf'` of `cost` over gauges pinned by `β v₀ = 1`. -/
theorem gaugeDist_eq_inf'_filter_eq_one [Fintype V] [LinearOrder V] [Fintype G] [DecidableEq G]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (v₀ : V) :
    α.gaugeDist ℓ =
      (univ.filter fun β : V → G => β v₀ = 1).inf' ⟨1, by simp⟩ (α.cost ℓ) := by
  refine le_antisymm (le_inf' _ _ fun β _ => α.gaugeDist_le_cost ℓ β) ?_
  obtain ⟨β, hβ1, hβ⟩ := α.exists_cost_eq_gaugeDist_and_apply_eq_one hℓ v₀
  exact (inf'_le (α.cost ℓ) (mem_filter.mpr ⟨mem_univ β, hβ1⟩)).trans_eq hβ

/-! ### Positive norm rescaling and change of coefficients -/

/-- Multiplying the group norm by a positive scalar scales `defect` by the same scalar. -/
@[simp]
theorem defect_smulOfPos [LinearOrder V] (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r)
    (α : Cochain X G) :
    α.defect (ℓ.smulOfPos hr) = r * α.defect ℓ := by
  simp [defect, mul_sum]

/-- Multiplying the group norm by a positive scalar scales `cost` by the same scalar. -/
@[simp]
theorem cost_smulOfPos [LinearOrder V] (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r)
    (α : Cochain X G) (β : V → G) :
    α.cost (ℓ.smulOfPos hr) β = r * α.cost ℓ β := by
  simp [cost, mul_sum]

/-- Multiplying the group norm by a positive scalar scales `gaugeDist` by the same scalar. -/
@[simp]
theorem gaugeDist_smulOfPos [LinearOrder V] (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r)
    (α : Cochain X G) :
    α.gaugeDist (ℓ.smulOfPos hr) = r * α.gaugeDist ℓ := by
  simp only [gaugeDist, cost_smulOfPos, ← Real.mul_iInf_of_nonneg hr.le]

/-- Push a cochain forward along a group homomorphism `φ : G →* H`. -/
def map (φ : G →* H) (α : Cochain X G) : Cochain X H where
  toFun u v := φ (α u v)
  map_symm' u v hadj := by rw [α.map_symm hadj, map_inv]
  map_of_not_adj' u v hnot := by rw [α.map_of_not_adj hnot, map_one]

/-- Evaluating `α.map φ` applies `φ` to `α u v`. -/
@[simp]
theorem map_apply (φ : G →* H) (α : Cochain X G) (u v : V) :
    α.map φ u v = φ (α u v) := by
  rfl

/-- Pushing forward along the identity homomorphism is the identity. -/
@[simp]
theorem map_id (α : Cochain X G) : α.map (MonoidHom.id G) = α := by
  ext; rfl

/-- Pushing forward respects composition of group homomorphisms. -/
theorem map_comp (ψ : H →* K) (φ : G →* H) (α : Cochain X G) :
    (α.map φ).map ψ = α.map (ψ.comp φ) := by
  ext; rfl

/-- Pushing forward the trivial cochain `1` yields `1`. -/
@[simp]
theorem map_one (φ : G →* H) : (1 : Cochain X G).map φ = 1 := by
  ext; simp

/-- Pushing forward commutes with gauge transformations. -/
theorem map_smul (φ : G →* H) (β : V → G) (α : Cochain X G) :
    (β • α).map φ = (φ ∘ β) • α.map φ := by
  refine ext_adj fun u v hadj => ?_
  simp [hadj]

/-- Pushing forward maps holonomies through `φ`. -/
@[simp]
theorem holonomy_map (φ : G →* H) (α : Cochain X G) (u v w : V) :
    (α.map φ).holonomy u v w = φ (α.holonomy u v w) := by
  simp [holonomy]

/-- Pushing forward preserves coboundaries. -/
theorem IsCoboundary.map {α : Cochain X G} (hα : α.IsCoboundary) (φ : G →* H) :
    (α.map φ).IsCoboundary := by
  obtain ⟨β, hβ⟩ := (isCoboundary_iff_exists_smul_eq_one α).mp hα
  exact (isCoboundary_iff_exists_smul_eq_one _).mpr
    ⟨φ ∘ β, by rw [← map_smul, hβ, map_one]⟩

/-- If `φ : G →* H` is norm-nonincreasing (`ℓH (φ g) ≤ ℓG g`), pushing forward does not increase
`defect`. -/
theorem defect_map_le [LinearOrder V] {ℓG : GroupNorm G} {ℓH : GroupNorm H}
    (φ : G →* H) (hφ : ∀ g, ℓH (φ g) ≤ ℓG g) (α : Cochain X G) :
    (α.map φ).defect ℓH ≤ α.defect ℓG :=
  sum_le_sum fun p _ => by
    rw [holonomy_map]
    exact hφ _

/-- If `φ : G →* H` is norm-nonincreasing, pushing a gauge forward along `φ` does not increase
`cost`. -/
theorem cost_map_le [LinearOrder V] {ℓG : GroupNorm G} {ℓH : GroupNorm H}
    (φ : G →* H) (hφ : ∀ g, ℓH (φ g) ≤ ℓG g) (α : Cochain X G) (β : V → G) :
    (α.map φ).cost ℓH (φ ∘ β) ≤ α.cost ℓG β :=
  sum_le_sum fun p _ => by
    have hmap : ((φ ∘ β) p.1)⁻¹ * α.map φ p.1 p.2 * (φ ∘ β) p.2 =
        φ ((β p.1)⁻¹ * α p.1 p.2 * β p.2) := by simp
    rw [hmap]
    exact hφ _

/-- If `φ : G →* H` is norm-nonincreasing, pushing forward does not increase `gaugeDist`. -/
theorem gaugeDist_map_le [LinearOrder V] {ℓG : GroupNorm G} {ℓH : GroupNorm H}
    (φ : G →* H) (hφ : ∀ g, ℓH (φ g) ≤ ℓG g) (α : Cochain X G) :
    (α.map φ).gaugeDist ℓH ≤ α.gaugeDist ℓG :=
  le_ciInf fun β => ((α.map φ).gaugeDist_le_cost ℓH (φ ∘ β)).trans (α.cost_map_le φ hφ β)

/-- Along an injective homomorphism `φ : G →* H`, `defect` under `ℓH` agrees with `defect` under
the pulled-back norm `ℓH.comp hφ`. -/
theorem defect_map_comp [LinearOrder V] (ℓH : GroupNorm H) {φ : G →* H}
    (hφ : Function.Injective φ) (α : Cochain X G) :
    (α.map φ).defect ℓH = α.defect (ℓH.comp hφ) := by
  simp [defect]

/-- Along an injective homomorphism `φ : G →* H`, `gaugeDist` in `H` is at most `gaugeDist` under
the pulled-back norm `ℓH.comp hφ` in `G`. -/
theorem gaugeDist_map_le_comp [LinearOrder V] (ℓH : GroupNorm H) {φ : G →* H}
    (hφ : Function.Injective φ) (α : Cochain X G) :
    (α.map φ).gaugeDist ℓH ≤ α.gaugeDist (ℓH.comp hφ) :=
  α.gaugeDist_map_le φ fun g => (ℓH.comp_apply hφ g).ge

/-- Embedding a subgroup-valued cochain into the ambient group preserves `defect` with respect to
the restricted group norm. -/
@[simp]
theorem defect_map_subtype [LinearOrder V] (ℓ : GroupNorm G) (S : Subgroup G)
    (α : Cochain X S) :
    (α.map S.subtype).defect ℓ = α.defect (ℓ.comp S.subtype_injective) :=
  α.defect_map_comp ℓ S.subtype_injective

/-- Embedding a subgroup-valued cochain into the ambient group does not increase `gaugeDist`
relative to the restricted group norm, because ambient gauges may leave `S`. -/
theorem gaugeDist_map_subtype_le [LinearOrder V] (ℓ : GroupNorm G) (S : Subgroup G)
    (α : Cochain X S) :
    (α.map S.subtype).gaugeDist ℓ ≤ α.gaugeDist (ℓ.comp S.subtype_injective) :=
  α.gaugeDist_map_le_comp ℓ S.subtype_injective

/-- If an isometric homomorphic inclusion `φ : G →* H` admits a norm-nonincreasing retraction
`ρ : H →* G`, pushing forward along `φ` preserves `gaugeDist` exactly. -/
theorem gaugeDist_map_eq_of_retract [LinearOrder V] {ℓG : GroupNorm G} {ℓH : GroupNorm H}
    (φ : G →* H) (ρ : H →* G) (hρ_φ : ∀ g, ρ (φ g) = g)
    (hφ : ∀ g, ℓH (φ g) = ℓG g) (hρ : ∀ h, ℓG (ρ h) ≤ ℓH h) (α : Cochain X G) :
    (α.map φ).gaugeDist ℓH = α.gaugeDist ℓG := by
  refine le_antisymm (α.gaugeDist_map_le φ fun g => (hφ g).le) ?_
  have hret : (α.map φ).map ρ = α := by
    ext u v
    exact hρ_φ (α u v)
  simpa [hret] using (α.map φ).gaugeDist_map_le ρ hρ

end Basic

end Cochain

end TauCeti
