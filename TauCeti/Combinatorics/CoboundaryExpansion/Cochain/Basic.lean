/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.ConjInvariant
public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Group-valued 1-cochains, gauge action, and gauge distance

A `G`-valued 1-cochain on a finite two-dimensional complex `X` assigns an element of `G` to each
oriented edge so that reversing an edge inverts the assigned group element, and assigns `1` to
pairs of vertices that do not span an edge. Constraining off-edge values to `1` makes cochains
extensional on oriented edges and makes `Cochain X G` finite whenever `G` is finite.

With respect to a `LinearOrder` on a finite vertex type `V` and a `GroupNorm` `ℓ` on `G`:

* `Cochain.holonomy α u v w` is the product `α u v * α v w * α w u` around an oriented triple;
* `Cochain.defect ℓ α` sums `ℓ (α.holonomy u v w)` over filled triangles `u < v < w`;
* a gauge `β : V → G` acts on the right via `(β • α) u v = (β u)⁻¹ * α u v * β v` on edges, so
  `β • (γ • α) = (γ * β) • α`;
* `Cochain.cost ℓ α β` sums `ℓ ((β u)⁻¹ * α u v * β v)` over edges `u < v`, and
  `Cochain.gaugeDist ℓ α` is the infimum of `cost` over all gauges;
* `Cochain.IsCoboundary α` expresses that some gauge trivializes every edge
  (`α u v = β u * (β v)⁻¹`).

Gauge transformations leave `gaugeDist` unchanged for every group norm, and leave `defect`
unchanged when `ℓ` is conjugation invariant; under conjugation invariance, every filled-triangle
holonomy norm bounds `gaugeDist` from below (`Cochain.norm_holonomy_le_gaugeDist`). For finite
coefficient groups `G`, the gauge-distance infimum is attained, vanishes precisely on coboundaries,
and under a conjugation-invariant norm can be computed over gauges pinned to `1` at any chosen
vertex. Whenever `X` has at least one filled triangle and `G` is nontrivial, a single-edge cochain
witnesses a non-coboundary and (for finite `G` or conjugation-invariant `ℓ`) strictly positive
gauge distance.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles I: equivalence*,
  arXiv:2310.17474v2, Eur. J. Math. 11 (2025), art. 13, §5.1.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, §2.2.
-/

public section

open Finset

namespace TauCeti

open TwoComplex

/-- A `G`-valued 1-cochain on `X`: an assignment of group elements to ordered vertex pairs that
inverts upon edge reversal and takes the value `1` off the edges of `X`. -/
structure Cochain {V : Type*} (X : TwoComplex V) (G : Type*) [Group G] where
  /-- The value on an ordered pair of vertices, trivial off the edges of `X`. -/
  toFun : V → V → G
  /-- Reversing an oriented edge inverts the value. -/
  inv_symm : ∀ u v, X.Adj u v → toFun v u = (toFun u v)⁻¹
  /-- Pairs of vertices that do not span an edge of `X` carry `1`. -/
  apply_eq_one_of_not_adj' : ∀ u v, ¬ X.Adj u v → toFun u v = 1

namespace Cochain

section Carrier

variable {V G : Type*} [Group G] {X : TwoComplex V}

instance : CoeFun (Cochain X G) (fun _ => V → V → G) :=
  ⟨Cochain.toFun⟩

/-- Two cochains are equal when they agree on every oriented edge of `X`. -/
@[ext]
theorem ext {α α' : Cochain X G} (h : ∀ u v, X.Adj u v → α u v = α' u v) : α = α' := by
  cases α with | mk f hf hnot => ?_
  cases α' with | mk f' hf' hnot' => ?_
  congr
  ext u v
  by_cases huv : X.Adj u v
  · exact h u v huv
  · rw [hnot u v huv, hnot' u v huv]

@[grind =]
theorem apply_eq_one_of_not_adj (α : Cochain X G) {u v : V} (h : ¬ X.Adj u v) : α u v = 1 :=
  α.apply_eq_one_of_not_adj' u v h

/-- Reversing any pair of vertices inverts the cochain value, both on edges and off edges (where
both orientations carry `1`). -/
theorem apply_swap (α : Cochain X G) (u v : V) : α v u = (α u v)⁻¹ := by
  by_cases huv : X.Adj u v
  · exact α.inv_symm u v huv
  · rw [α.apply_eq_one_of_not_adj (mt Adj.symm huv), α.apply_eq_one_of_not_adj huv, inv_one]

@[simp, grind =]
theorem apply_self (α : Cochain X G) (u : V) : α u u = 1 :=
  α.apply_eq_one_of_not_adj (X.not_adj_self u)

/-- With a linear order on vertices, a cochain is determined by its values on positively oriented
edges `u < v`. -/
theorem ext_of_lt [LinearOrder V] {α α' : Cochain X G}
    (h : ∀ u v, u < v → X.Adj u v → α u v = α' u v) : α = α' := by
  ext u v huv
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · exact h u v hlt huv
  · exact (huv.ne rfl).elim
  · rw [α.apply_swap v u, α'.apply_swap v u, h v u hgt huv.symm]

/-- The trivial cochain assigning `1` to every pair of vertices. -/
instance : One (Cochain X G) where
  one :=
    { toFun := fun _ _ => 1
      inv_symm := fun _ _ _ => inv_one.symm
      apply_eq_one_of_not_adj' := fun _ _ _ => rfl }

instance : Inhabited (Cochain X G) := ⟨1⟩

@[simp, grind =]
theorem one_apply (u v : V) : (1 : Cochain X G) u v = 1 := (rfl)

/-- Over a trivial coefficient group, `1` is the unique cochain. -/
instance [Subsingleton G] : Unique (Cochain X G) where
  default := 1
  uniq α := by ext u v _; exact Subsingleton.elim _ _

/-- Because `X.edges` is finite and off-edge values are fixed to `1`, `Cochain X G` is finite
whenever `G` is finite, without any finiteness assumption on `V`. -/
instance [Finite G] : Finite (Cochain X G) := by
  classical
  let S : Finset V := X.edges.biUnion id
  refine Finite.of_injective (fun (α : Cochain X G) (u v : S) => α u.1 v.1) ?_
  intro α α' h
  ext u v huv
  obtain ⟨e, he, hu, hv⟩ := huv.exists_mem_edges
  have huS : u ∈ S := mem_biUnion.mpr ⟨e, he, hu⟩
  have hvS : v ∈ S := mem_biUnion.mpr ⟨e, he, hv⟩
  exact congrFun (congrFun h ⟨u, huS⟩) ⟨v, hvS⟩

/-- Build a cochain from an arbitrary function inverted by edge reversal, setting off-edge values
to `1`. -/
noncomputable def ofFn (X : TwoComplex V) (f : V → V → G)
    (hf : ∀ u v, X.Adj u v → f v u = (f u v)⁻¹) : Cochain X G := by
  classical
  exact
    { toFun := fun u v => if X.Adj u v then f u v else 1
      inv_symm := fun u v huv => by simp [huv, huv.symm, hf u v huv]
      apply_eq_one_of_not_adj' := fun u v huv => by simp [huv] }

@[simp, grind =]
theorem ofFn_apply_of_adj {f : V → V → G} (hf : ∀ u v, X.Adj u v → f v u = (f u v)⁻¹)
    {u v : V} (h : X.Adj u v) : ofFn X f hf u v = f u v := by
  classical
  simp [ofFn, h]

@[simp, grind =]
theorem ofFn_apply_of_not_adj {f : V → V → G} (hf : ∀ u v, X.Adj u v → f v u = (f u v)⁻¹)
    {u v : V} (h : ¬ X.Adj u v) : ofFn X f hf u v = 1 :=
  (ofFn X f hf).apply_eq_one_of_not_adj h

/-- Build a cochain from unconstrained values on positively oriented pairs `u < v`. -/
noncomputable def ofLt [LinearOrder V] (X : TwoComplex V) (f : V → V → G) : Cochain X G :=
  ofFn X (fun u v => if u < v then f u v else (f v u)⁻¹) fun u v huv => by
    rcases lt_trichotomy u v with hlt | rfl | hgt
    · simp [hlt, asymm hlt]
    · exact (huv.ne rfl).elim
    · simp [hgt, asymm hgt]

@[simp, grind =]
theorem ofLt_apply_of_lt [LinearOrder V] (f : V → V → G) {u v : V} (h : X.Adj u v)
    (hlt : u < v) : ofLt X f u v = f u v := by
  simp [ofLt, h, hlt]

@[simp, grind =]
theorem ofLt_apply_of_gt [LinearOrder V] (f : V → V → G) {u v : V} (h : X.Adj u v)
    (hgt : v < u) : ofLt X f u v = (f v u)⁻¹ := by
  simp [ofLt, h, asymm hgt]

@[simp, grind =]
theorem ofLt_apply_of_not_adj [LinearOrder V] (f : V → V → G) {u v : V} (h : ¬ X.Adj u v) :
    ofLt X f u v = 1 :=
  (ofLt X f).apply_eq_one_of_not_adj h

/-- The cochain supported on a single edge `(u₀, v₀)`, taking value `g` on `(u₀, v₀)`, `g⁻¹` on
`(v₀, u₀)`, and `1` elsewhere (or `1` everywhere if `u₀` and `v₀` are not adjacent). -/
noncomputable def singleEdge (X : TwoComplex V) (u₀ v₀ : V) (g : G) : Cochain X G := by
  classical
  exact ofFn X
    (fun u v => if u = u₀ ∧ v = v₀ then g else if u = v₀ ∧ v = u₀ then g⁻¹ else 1)
    fun u v huv => by
      by_cases h₁ : u = u₀ ∧ v = v₀
      · rcases h₁ with ⟨rfl, rfl⟩
        simp [huv.ne.symm]
      · by_cases h₂ : u = v₀ ∧ v = u₀
        · rcases h₂ with ⟨rfl, rfl⟩
          simp [huv.ne]
        · have h₁' : ¬ (v = v₀ ∧ u = u₀) := fun ⟨hv, hu⟩ => h₁ ⟨hu, hv⟩
          have h₂' : ¬ (v = u₀ ∧ u = v₀) := fun ⟨hv, hu⟩ => h₂ ⟨hu, hv⟩
          simp [h₁, h₂, h₁', h₂']

@[simp, grind =]
theorem singleEdge_apply_self {u₀ v₀ : V} (h : X.Adj u₀ v₀) (g : G) :
    singleEdge X u₀ v₀ g u₀ v₀ = g := by
  classical
  simp [singleEdge, h]

@[simp, grind =]
theorem singleEdge_apply_swap {u₀ v₀ : V} (h : X.Adj u₀ v₀) (g : G) :
    singleEdge X u₀ v₀ g v₀ u₀ = g⁻¹ := by
  classical
  simp [singleEdge, h.symm, h.ne.symm]

@[simp, grind =]
theorem singleEdge_apply_of_ne {u₀ v₀ u v : V} (g : G)
    (h₁ : ¬ (u = u₀ ∧ v = v₀)) (h₂ : ¬ (u = v₀ ∧ v = u₀)) :
    singleEdge X u₀ v₀ g u v = 1 := by
  classical
  by_cases huv : X.Adj u v <;> simp [singleEdge, huv, h₁, h₂]

@[simp]
theorem singleEdge_of_not_adj {u₀ v₀ : V} (h : ¬ X.Adj u₀ v₀) (g : G) :
    singleEdge X u₀ v₀ g = 1 := by
  ext u v huv
  have h₁ : ¬ (u = u₀ ∧ v = v₀) := by rintro ⟨rfl, rfl⟩; exact h huv
  have h₂ : ¬ (u = v₀ ∧ v = u₀) := by rintro ⟨rfl, rfl⟩; exact h huv.symm
  simp [h₁, h₂]

@[simp]
theorem singleEdge_one (u₀ v₀ : V) : singleEdge X u₀ v₀ (1 : G) = 1 := by
  classical
  ext u v huv
  simp [singleEdge, huv]

/-! ### Gauge action, holonomy, and coboundaries -/

/-- A gauge `β : V → G` acts on cochains by `(β • α) u v = (β u)⁻¹ * α u v * β v` on edges of `X`
and `1` off edges. -/
noncomputable instance : SMul (V → G) (Cochain X G) where
  smul β α :=
    ofFn X (fun u v => (β u)⁻¹ * α u v * β v) fun u v _ => by
      rw [α.apply_swap u v]
      group

@[simp, grind =]
theorem smul_apply_of_adj (β : V → G) (α : Cochain X G) {u v : V} (h : X.Adj u v) :
    (β • α) u v = (β u)⁻¹ * α u v * β v :=
  ofFn_apply_of_adj _ h

@[simp, grind =]
theorem smul_apply_of_not_adj (β : V → G) (α : Cochain X G) {u v : V} (h : ¬ X.Adj u v) :
    (β • α) u v = 1 :=
  (β • α).apply_eq_one_of_not_adj h

/-- On the complete complex, `(β • α) u v = (β u)⁻¹ * α u v * β v` holds for all vertex pairs,
including the diagonal. -/
@[simp, grind =]
theorem smul_apply_complete [Fintype V] (β : V → G) (α : Cochain (complete V) G) (u v : V) :
    (β • α) u v = (β u)⁻¹ * α u v * β v := by
  by_cases huv : u = v
  · subst huv
    simp
  · exact smul_apply_of_adj β α ((adj_complete u v).mpr huv)

@[simp]
protected theorem one_smul (α : Cochain X G) : (1 : V → G) • α = α := by
  ext u v huv
  simp [huv]

/-- Successive gauge transformations compose in reverse order: `β • (γ • α) = (γ * β) • α`. -/
@[simp]
theorem smul_smul_eq_mul_smul (β γ : V → G) (α : Cochain X G) :
    β • (γ • α) = (γ * β) • α := by
  ext u v huv
  simp [huv, mul_assoc]

/-- The holonomy of `α` around the oriented triple `(u, v, w)`. -/
def holonomy (α : Cochain X G) (u v w : V) : G :=
  α u v * α v w * α w u

theorem holonomy_def (α : Cochain X G) (u v w : V) :
    α.holonomy u v w = α u v * α v w * α w u := (rfl)

@[simp]
theorem holonomy_one (u v w : V) : (1 : Cochain X G).holonomy u v w = 1 := by
  simp [holonomy_def]

/-- Under a gauge `β`, the holonomy around three mutually adjacent vertices is conjugated by
`β u`. -/
theorem holonomy_smul (β : V → G) (α : Cochain X G) {u v w : V}
    (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u) :
    (β • α).holonomy u v w = (β u)⁻¹ * α.holonomy u v w * β u := by
  simp only [holonomy_def, smul_apply_of_adj β α huv, smul_apply_of_adj β α hvw,
    smul_apply_of_adj β α hwu]
  group

/-- The holonomy of `singleEdge X u₀ v₀ g` around `(u₀, v₀, w)` for any third vertex `w` is `g`. -/
theorem holonomy_singleEdge {u₀ v₀ w : V} (h : X.Adj u₀ v₀) (hw₁ : w ≠ u₀) (hw₂ : w ≠ v₀)
    (g : G) : (singleEdge X u₀ v₀ g).holonomy u₀ v₀ w = g := by
  simp [holonomy_def, h, h.ne.symm, hw₁, hw₂]

/-- A cochain is a coboundary when some gauge `β : V → G` satisfies `α u v = β u * (β v)⁻¹` on
every edge of `X`. -/
def IsCoboundary (α : Cochain X G) : Prop :=
  ∃ β : V → G, ∀ u v, X.Adj u v → α u v = β u * (β v)⁻¹

theorem isCoboundary_def (α : Cochain X G) :
    α.IsCoboundary ↔ ∃ β : V → G, ∀ u v, X.Adj u v → α u v = β u * (β v)⁻¹ :=
  Iff.rfl

theorem isCoboundary_iff_mem_edges [DecidableEq V] (α : Cochain X G) :
    α.IsCoboundary ↔
      ∃ β : V → G, ∀ u v, ({u, v} : Finset V) ∈ X.edges → α u v = β u * (β v)⁻¹ := by
  simp_rw [isCoboundary_def, adj_iff_pair_mem_edges]

/-- A cochain is a coboundary if and only if some gauge moves it to the trivial cochain `1`. -/
theorem isCoboundary_iff_exists_smul_eq_one (α : Cochain X G) :
    α.IsCoboundary ↔ ∃ β : V → G, β • α = 1 := by
  refine exists_congr fun β => ?_
  rw [Cochain.ext_iff]
  refine forall₂_congr fun u v => imp_congr_right fun huv => ?_
  rw [smul_apply_of_adj β α huv, one_apply]
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc
      α u v = β u * ((β u)⁻¹ * α u v * β v) * (β v)⁻¹ := by group
      _ = β u * (β v)⁻¹ := by rw [h, mul_one]

@[simp]
theorem isCoboundary_one : (1 : Cochain X G).IsCoboundary :=
  (isCoboundary_iff_exists_smul_eq_one 1).mpr ⟨1, Cochain.one_smul 1⟩

@[simp]
theorem isCoboundary_smul_iff (β : V → G) (α : Cochain X G) :
    (β • α).IsCoboundary ↔ α.IsCoboundary := by
  simp only [isCoboundary_iff_exists_smul_eq_one]
  constructor
  · rintro ⟨γ, h⟩
    exact ⟨β * γ, by rwa [← smul_smul_eq_mul_smul]⟩
  · rintro ⟨γ, h⟩
    refine ⟨β⁻¹ * γ, ?_⟩
    rw [smul_smul_eq_mul_smul, ← mul_assoc, mul_inv_cancel, one_mul, h]

/-- Every triangle holonomy of a coboundary is trivial. -/
theorem IsCoboundary.holonomy_eq_one {α : Cochain X G} (hα : α.IsCoboundary)
    {u v w : V} (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u) :
    α.holonomy u v w = 1 := by
  obtain ⟨β, hβ⟩ := hα
  rw [holonomy_def, hβ u v huv, hβ v w hvw, hβ w u hwu]
  group

/-- A cochain with a non-identity holonomy around three mutually adjacent vertices is not a
coboundary. -/
theorem not_isCoboundary_of_holonomy_ne_one {α : Cochain X G} {u v w : V}
    (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u) (h : α.holonomy u v w ≠ 1) :
    ¬ α.IsCoboundary :=
  fun hα => h (hα.holonomy_eq_one huv hvw hwu)

end Carrier

/-! ### Defect, cost, gauge distance, and gauge invariance -/

section MetricQuantities

variable {V G : Type*} [Fintype V] [LinearOrder V] [Group G] {X : TwoComplex V}

/-- The triangle defect of `α` with respect to `ℓ`: the sum of the norm of the holonomy over all
filled triangles read in increasing vertex order `u < v < w`. -/
noncomputable def defect (ℓ : GroupNorm G) (α : Cochain X G) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V × V =>
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles),
    ℓ (α.holonomy p.1 p.2.1 p.2.2)

theorem defect_def (ℓ : GroupNorm G) (α : Cochain X G) :
    α.defect ℓ =
      ∑ p ∈ univ.filter (fun p : V × V × V =>
          p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles),
        ℓ (α.holonomy p.1 p.2.1 p.2.2) := (rfl)

/-- The cost of a gauge `β` against `α`: the sum of `ℓ ((β u)⁻¹ * α u v * β v)` over all edges
read in increasing vertex order `u < v`. -/
noncomputable def cost (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
    ℓ ((β p.1)⁻¹ * α p.1 p.2 * β p.2)

theorem cost_def (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.cost ℓ β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
        ℓ ((β p.1)⁻¹ * α p.1 p.2 * β p.2) := (rfl)

/-- The gauge distance from `α` to the coboundaries: the infimum of `cost` over all gauges. -/
noncomputable def gaugeDist (ℓ : GroupNorm G) (α : Cochain X G) : ℝ :=
  ⨅ β : V → G, α.cost ℓ β

theorem gaugeDist_def (ℓ : GroupNorm G) (α : Cochain X G) :
    α.gaugeDist ℓ = ⨅ β : V → G, α.cost ℓ β := (rfl)

theorem defect_nonneg (ℓ : GroupNorm G) (α : Cochain X G) : 0 ≤ α.defect ℓ :=
  sum_nonneg fun _ _ => apply_nonneg ℓ _

theorem cost_nonneg (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) : 0 ≤ α.cost ℓ β :=
  sum_nonneg fun _ _ => apply_nonneg ℓ _

theorem bddBelow_range_cost (ℓ : GroupNorm G) (α : Cochain X G) :
    BddBelow (Set.range (α.cost ℓ)) :=
  ⟨0, by rintro _ ⟨β, rfl⟩; exact α.cost_nonneg ℓ β⟩

theorem gaugeDist_nonneg (ℓ : GroupNorm G) (α : Cochain X G) : 0 ≤ α.gaugeDist ℓ :=
  Real.iInf_nonneg (α.cost_nonneg ℓ)

theorem gaugeDist_le_cost (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.gaugeDist ℓ ≤ α.cost ℓ β :=
  ciInf_le (α.bddBelow_range_cost ℓ) β

theorem le_gaugeDist_iff (ℓ : GroupNorm G) (α : Cochain X G) {c : ℝ} :
    c ≤ α.gaugeDist ℓ ↔ ∀ β : V → G, c ≤ α.cost ℓ β :=
  le_ciInf_iff (α.bddBelow_range_cost ℓ)

@[simp]
theorem defect_one (ℓ : GroupNorm G) : (1 : Cochain X G).defect ℓ = 0 := by
  simp [defect_def]

@[simp]
theorem cost_one_one (ℓ : GroupNorm G) : (1 : Cochain X G).cost ℓ 1 = 0 := by
  simp [cost_def]

@[simp]
theorem gaugeDist_one (ℓ : GroupNorm G) : (1 : Cochain X G).gaugeDist ℓ = 0 :=
  le_antisymm ((gaugeDist_le_cost ℓ 1 1).trans_eq (cost_one_one ℓ)) (gaugeDist_nonneg ℓ 1)

/-- The cost of a gauge `β` vanishes if and only if `β` trivializes `α`. -/
theorem cost_eq_zero_iff (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.cost ℓ β = 0 ↔ β • α = 1 := by
  rw [cost_def, sum_eq_zero_iff_of_nonneg (fun _ _ => apply_nonneg ℓ _)]
  simp only [mem_filter, mem_univ, true_and, map_eq_zero_iff_eq_one]
  constructor
  · intro h
    refine ext_of_lt fun u v hlt huv => ?_
    rw [smul_apply_of_adj β α huv, one_apply]
    exact h (u, v) ⟨hlt, (X.adj_iff_pair_mem_edges u v).mp huv⟩
  · rintro h ⟨u, v⟩ ⟨_, huv⟩
    have hadj : X.Adj u v := (X.adj_iff_pair_mem_edges u v).mpr huv
    simpa [smul_apply_of_adj β α hadj] using congrFun (congrFun (congrArg toFun h) u) v

/-- Every coboundary has zero defect, even without conjugation invariance of the norm. -/
theorem IsCoboundary.defect_eq_zero {α : Cochain X G} (hα : α.IsCoboundary) (ℓ : GroupNorm G) :
    α.defect ℓ = 0 := by
  rw [defect_def]
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨hlt₁, hlt₂, ht⟩ := (mem_filter.mp hp).2
  have huv : X.Adj p.1 p.2.1 := X.adj_of_mem_triangle ht (by simp) (by simp) hlt₁.ne
  have hvw : X.Adj p.2.1 p.2.2 := X.adj_of_mem_triangle ht (by simp) (by simp) hlt₂.ne
  have hwu : X.Adj p.2.2 p.1 :=
    X.adj_of_mem_triangle ht (by simp) (by simp) (hlt₁.trans hlt₂).ne'
  rw [hα.holonomy_eq_one huv hvw hwu, map_one_eq_zero]

/-- Every coboundary has gauge distance zero. -/
theorem IsCoboundary.gaugeDist_eq_zero {α : Cochain X G} (hα : α.IsCoboundary) (ℓ : GroupNorm G) :
    α.gaugeDist ℓ = 0 := by
  obtain ⟨β, hβ⟩ := (isCoboundary_iff_exists_smul_eq_one α).mp hα
  exact le_antisymm
    ((α.gaugeDist_le_cost ℓ β).trans_eq ((α.cost_eq_zero_iff ℓ β).mpr hβ))
    (α.gaugeDist_nonneg ℓ)

/-- Gauge equivariance of cost: `cost (β • α) γ = cost α (β * γ)`, for every group norm `ℓ`. -/
theorem cost_smul (ℓ : GroupNorm G) (α : Cochain X G) (β γ : V → G) :
    (β • α).cost ℓ γ = α.cost ℓ (β * γ) := by
  rw [cost_def, cost_def]
  refine sum_congr rfl fun p hp => ?_
  have hadj : X.Adj p.1 p.2 := (X.adj_iff_pair_mem_edges p.1 p.2).mpr (mem_filter.mp hp).2.2
  simp [smul_apply_of_adj β α hadj, mul_assoc]

/-- Gauge distance is invariant under the gauge action for every group norm `ℓ`. -/
@[simp]
theorem gaugeDist_smul (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    (β • α).gaugeDist ℓ = α.gaugeDist ℓ := by
  simp_rw [gaugeDist_def, cost_smul]
  exact (Equiv.mulLeft β).iInf_congr fun _ => rfl

/-- Under a conjugation-invariant group norm, the triangle defect is gauge invariant. -/
theorem defect_smul {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (β : V → G) : (β • α).defect ℓ = α.defect ℓ := by
  rw [defect_def, defect_def]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨hlt₁, hlt₂, ht⟩ := (mem_filter.mp hp).2
  have huv : X.Adj p.1 p.2.1 := X.adj_of_mem_triangle ht (by simp) (by simp) hlt₁.ne
  have hvw : X.Adj p.2.1 p.2.2 := X.adj_of_mem_triangle ht (by simp) (by simp) hlt₂.ne
  have hwu : X.Adj p.2.2 p.1 :=
    X.adj_of_mem_triangle ht (by simp) (by simp) (hlt₁.trans hlt₂).ne'
  rw [holonomy_smul β α huv hvw hwu]
  exact hℓ.map_inv_mul_mul (α.holonomy p.1 p.2.1 p.2.2) (β p.1)

/-- Multiplying a gauge on the right by a constant group element conjugates every edge term, so it
preserves `cost` under a conjugation-invariant group norm. -/
theorem cost_mul_const {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (β : V → G) (g : G) :
    α.cost ℓ (fun u => β u * g) = α.cost ℓ β := by
  rw [cost_def, cost_def]
  refine sum_congr rfl fun p _ => ?_
  have h : (β p.1 * g)⁻¹ * α p.1 p.2 * (β p.2 * g) =
      g⁻¹ * ((β p.1)⁻¹ * α p.1 p.2 * β p.2) * g := by group
  rw [h]
  exact hℓ.map_inv_mul_mul _ g

private def orientEdge (a b : V) : V × V :=
  if a < b then (a, b) else (b, a)

/-- Under a conjugation-invariant norm, the holonomy norm around three mutually adjacent vertices
is bounded above by the cost of any gauge `β`. -/
theorem norm_holonomy_le_cost {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (β : V → G) {u v w : V}
    (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u) :
    ℓ (α.holonomy u v w) ≤ α.cost ℓ β := by
  let f : V × V → ℝ := fun p => ℓ ((β p.1)⁻¹ * α p.1 p.2 * β p.2)
  let E := univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges)
  have hmem : ∀ {a b : V}, X.Adj a b → orientEdge a b ∈ E := by
    intro a b hab
    rcases lt_or_gt_of_ne hab.ne with hlt | hgt
    · simp [E, orientEdge, hlt, (X.adj_iff_pair_mem_edges a b).mp hab]
    · simp [E, orientEdge, asymm hgt, hgt, (X.adj_iff_pair_mem_edges b a).mp hab.symm]
  have hpair : ∀ a b : V, ({(orientEdge a b).1, (orientEdge a b).2} : Finset V) = {a, b} := by
    intro a b
    by_cases hlt : a < b <;> simp [orientEdge, hlt, pair_comm]
  have heval : ∀ a b : V, f (orientEdge a b) = ℓ ((β a)⁻¹ * α a b * β b) := by
    intro a b
    by_cases hlt : a < b
    · simp [f, orientEdge, hlt]
    · simp only [f, orientEdge, hlt, ↓reduceIte]
      have hinv : ((β a)⁻¹ * α a b * β b)⁻¹ = (β b)⁻¹ * α b a * β a := by
        rw [α.apply_swap a b]
        group
      rw [← hinv, map_inv_eq_map]
  have hne_adj : ∀ {a b c : V}, a ≠ b → a ≠ c → orientEdge a b ≠ orientEdge b c :=
    fun hab hac h => by
      have hp : ({_, _} : Finset V) = _ := (hpair _ _).symm.trans ((congrArg
        (fun p : V × V => ({p.1, p.2} : Finset V)) h).trans (hpair _ _))
      have ha : _ ∈ ({_, _} : Finset V) := hp ▸ mem_insert_self _ _
      rcases mem_insert.mp ha with rfl | ha'
      · exact hab rfl
      · exact hac (mem_singleton.mp ha')
  have hne₁₂ : orientEdge u v ≠ orientEdge v w := hne_adj huv.ne hwu.ne.symm
  have hne₂₃ : orientEdge v w ≠ orientEdge w u := hne_adj hvw.ne huv.ne.symm
  have hne₁₃ : orientEdge u v ≠ orientEdge w u := (hne_adj hwu.ne hvw.ne.symm).symm
  have hsub : ({orientEdge u v, orientEdge v w, orientEdge w u} : Finset (V × V)) ⊆ E := by
    simp [insert_subset_iff, hmem huv, hmem hvw, hmem hwu]
  have hsum : f (orientEdge u v) + f (orientEdge v w) + f (orientEdge w u) ≤ α.cost ℓ β := by
    calc
      f (orientEdge u v) + f (orientEdge v w) + f (orientEdge w u)
          = ∑ p ∈ {orientEdge u v, orientEdge v w, orientEdge w u}, f p := by
            rw [sum_insert (by simp [hne₁₂, hne₁₃]), sum_pair hne₂₃, add_assoc]
      _ ≤ ∑ p ∈ E, f p := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => apply_nonneg ℓ _
      _ = α.cost ℓ β := rfl
  rw [heval u v, heval v w, heval w u] at hsum
  refine le_trans ?_ hsum
  calc
    ℓ (α.holonomy u v w)
        = ℓ ((β u)⁻¹ * α.holonomy u v w * β u) :=
          (hℓ.map_inv_mul_mul (α.holonomy u v w) (β u)).symm
    _ = ℓ (((β u)⁻¹ * α u v * β v) * ((β v)⁻¹ * α v w * β w) *
          ((β w)⁻¹ * α w u * β u)) := by
          rw [← holonomy_smul β α huv hvw hwu, holonomy_def,
            smul_apply_of_adj β α huv, smul_apply_of_adj β α hvw, smul_apply_of_adj β α hwu]
    _ ≤ ℓ (((β u)⁻¹ * α u v * β v) * ((β v)⁻¹ * α v w * β w)) +
          ℓ ((β w)⁻¹ * α w u * β u) := map_mul_le_add ℓ _ _
    _ ≤ ℓ ((β u)⁻¹ * α u v * β v) + ℓ ((β v)⁻¹ * α v w * β w) +
          ℓ ((β w)⁻¹ * α w u * β u) := add_le_add (map_mul_le_add ℓ _ _) le_rfl

/-- Under a conjugation-invariant norm, the holonomy norm around three mutually adjacent vertices
bounds `gaugeDist` from below. -/
theorem norm_holonomy_le_gaugeDist {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) {u v w : V}
    (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u) :
    ℓ (α.holonomy u v w) ≤ α.gaugeDist ℓ :=
  (α.le_gaugeDist_iff ℓ).mpr fun β => α.norm_holonomy_le_cost hℓ β huv hvw hwu

/-- Under a conjugation-invariant norm, any cochain with a non-identity holonomy around three
mutually adjacent vertices has strictly positive gauge distance, without requiring `G` to be
finite. -/
theorem gaugeDist_pos_of_holonomy_ne_one_of_isConjInvariant {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) {α : Cochain X G} {u v w : V}
    (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u)
    (h : α.holonomy u v w ≠ 1) : 0 < α.gaugeDist ℓ :=
  lt_of_lt_of_le ((apply_nonneg ℓ _).lt_of_ne' (mt (map_eq_zero_iff_eq_one ℓ).mp h))
    (α.norm_holonomy_le_gaugeDist hℓ huv hvw hwu)

/-! ### Pinned gauges and finite coefficient groups -/

/-- Under a conjugation-invariant norm, restricting gauges to take value `1` at a chosen vertex
`v₀` does not change the infimum defining `gaugeDist`. -/
theorem iInf_cost_apply_eq_one {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (v₀ : V) :
    (⨅ β : {β : V → G // β v₀ = 1}, α.cost ℓ β.1) = α.gaugeDist ℓ := by
  have : Nonempty {β : V → G // β v₀ = 1} := ⟨⟨1, rfl⟩⟩
  refine le_antisymm ?_ (le_ciInf fun β => α.gaugeDist_le_cost ℓ β.1)
  refine le_ciInf fun β => ?_
  let β' : {γ : V → G // γ v₀ = 1} := ⟨fun u => β u * (β v₀)⁻¹, mul_inv_cancel (β v₀)⟩
  have hbdd : BddBelow (Set.range fun γ : {γ : V → G // γ v₀ = 1} => α.cost ℓ γ.1) :=
    ⟨0, by rintro _ ⟨γ, rfl⟩; exact α.cost_nonneg ℓ γ.1⟩
  exact (ciInf_le hbdd β').trans_eq (α.cost_mul_const hℓ β (β v₀)⁻¹)

/-- Under a conjugation-invariant norm, `c ≤ α.gaugeDist ℓ` holds if and only if `c ≤ α.cost ℓ β`
for every gauge `β` pinned to `1` at `v₀`. -/
theorem le_gaugeDist_iff_apply_eq_one {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (v₀ : V) {c : ℝ} :
    c ≤ α.gaugeDist ℓ ↔ ∀ β : V → G, β v₀ = 1 → c ≤ α.cost ℓ β := by
  have : Nonempty {β : V → G // β v₀ = 1} := ⟨⟨1, rfl⟩⟩
  have hbdd : BddBelow (Set.range fun γ : {γ : V → G // γ v₀ = 1} => α.cost ℓ γ.1) :=
    ⟨0, by rintro _ ⟨γ, rfl⟩; exact α.cost_nonneg ℓ γ.1⟩
  rw [← α.iInf_cost_apply_eq_one hℓ v₀, le_ciInf_iff hbdd, Subtype.forall]

/-- When `G` is finite, the infimum defining `gaugeDist` is attained by some gauge. -/
theorem exists_cost_eq_gaugeDist [Finite G] (ℓ : GroupNorm G) (α : Cochain X G) :
    ∃ β : V → G, α.cost ℓ β = α.gaugeDist ℓ :=
  exists_eq_ciInf_of_finite

/-- For finite `G`, a cochain has gauge distance zero if and only if it is a coboundary. -/
theorem gaugeDist_eq_zero_iff_isCoboundary [Finite G] (ℓ : GroupNorm G) (α : Cochain X G) :
    α.gaugeDist ℓ = 0 ↔ α.IsCoboundary := by
  constructor
  · intro h0
    obtain ⟨β, hβ⟩ := α.exists_cost_eq_gaugeDist ℓ
    exact (isCoboundary_iff_exists_smul_eq_one α).mpr ⟨β, (α.cost_eq_zero_iff ℓ β).mp (hβ.trans h0)⟩
  · exact fun hα => hα.gaugeDist_eq_zero ℓ

/-- For finite `G`, a cochain has positive gauge distance if and only if it is not a coboundary. -/
theorem gaugeDist_pos_iff_not_isCoboundary [Finite G] (ℓ : GroupNorm G) (α : Cochain X G) :
    0 < α.gaugeDist ℓ ↔ ¬ α.IsCoboundary := by
  rw [← gaugeDist_eq_zero_iff_isCoboundary ℓ α]
  exact (α.gaugeDist_nonneg ℓ).lt_iff_ne'

/-- For finite `G`, any cochain with a non-identity holonomy around three mutually adjacent
vertices has positive gauge distance. -/
theorem gaugeDist_pos_of_holonomy_ne_one [Finite G] (ℓ : GroupNorm G) {α : Cochain X G}
    {u v w : V} (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u)
    (h : α.holonomy u v w ≠ 1) : 0 < α.gaugeDist ℓ :=
  (α.gaugeDist_pos_iff_not_isCoboundary ℓ).mpr (not_isCoboundary_of_holonomy_ne_one huv hvw hwu h)

/-- For finite `G` and conjugation-invariant `ℓ`, some optimal gauge takes value `1` at `v₀`. -/
theorem exists_apply_eq_one_and_cost_eq_gaugeDist [Finite G] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (v₀ : V) :
    ∃ β : V → G, β v₀ = 1 ∧ α.cost ℓ β = α.gaugeDist ℓ := by
  have : Nonempty {β : V → G // β v₀ = 1} := ⟨⟨1, rfl⟩⟩
  obtain ⟨⟨β, hβ₀⟩, hβ⟩ :=
    exists_eq_ciInf_of_finite (f := fun γ : {γ : V → G // γ v₀ = 1} => α.cost ℓ γ.1)
  exact ⟨β, hβ₀, hβ.trans (α.iInf_cost_apply_eq_one hℓ v₀)⟩

end MetricQuantities

end Cochain

/-! ### Existence of non-coboundaries and positive-gauge-distance witnesses -/

section Existence

private theorem exists_holonomy_ne_one_of_triangles_nonempty {V G : Type*} [Group G]
    [Nontrivial G] {X : TwoComplex V} (htri : X.triangles.Nonempty) :
    ∃ (α : Cochain X G) (u v w : V),
      X.Adj u v ∧ X.Adj v w ∧ X.Adj w u ∧ α.holonomy u v w ≠ 1 := by
  obtain ⟨t, ht⟩ := htri
  obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw⟩ := X.exists_vertices_of_mem_triangles ht
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hadj_uv : X.Adj u v := X.adj_of_mem_triangle ht hu hv huv
  refine ⟨Cochain.singleEdge X u v g, u, v, w, hadj_uv,
    X.adj_of_mem_triangle ht hv hw hvw, X.adj_of_mem_triangle ht hw hu huw.symm, ?_⟩
  rwa [Cochain.holonomy_singleEdge hadj_uv huw.symm hvw.symm g]

/-- Whenever `X` has at least one filled triangle and `G` is nontrivial, `X` admits a 1-cochain
that is not a coboundary: supporting a non-identity element on one edge of that triangle gives a
non-identity holonomy. -/
theorem exists_not_isCoboundary_of_triangles_nonempty {V G : Type*} [Group G] [Nontrivial G]
    {X : TwoComplex V} (htri : X.triangles.Nonempty) :
    ∃ α : Cochain X G, ¬ α.IsCoboundary := by
  obtain ⟨α, u, v, w, huv, hvw, hwu, hhol⟩ :=
    exists_holonomy_ne_one_of_triangles_nonempty (G := G) htri
  exact ⟨α, Cochain.not_isCoboundary_of_holonomy_ne_one huv hvw hwu hhol⟩

/-- Whenever `X` has at least one filled triangle and `G` is a nontrivial finite group, some
1-cochain on `X` has strictly positive gauge distance. -/
theorem exists_gaugeDist_pos_of_triangles_nonempty {V G : Type*} [Fintype V] [LinearOrder V]
    [Group G] [Finite G] [Nontrivial G] {X : TwoComplex V} (htri : X.triangles.Nonempty)
    (ℓ : GroupNorm G) :
    ∃ α : Cochain X G, 0 < α.gaugeDist ℓ := by
  obtain ⟨α, hα⟩ := exists_not_isCoboundary_of_triangles_nonempty (G := G) htri
  exact ⟨α, (α.gaugeDist_pos_iff_not_isCoboundary ℓ).mpr hα⟩

/-- Whenever `X` has at least one filled triangle, `G` is nontrivial, and `ℓ` is conjugation
invariant, some 1-cochain on `X` has strictly positive gauge distance (without requiring `G` to be
finite). -/
theorem exists_gaugeDist_pos_of_triangles_nonempty_of_isConjInvariant {V G : Type*}
    [Fintype V] [LinearOrder V] [Group G] [Nontrivial G] {X : TwoComplex V}
    (htri : X.triangles.Nonempty) {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    ∃ α : Cochain X G, 0 < α.gaugeDist ℓ := by
  obtain ⟨α, u, v, w, huv, hvw, hwu, hhol⟩ :=
    exists_holonomy_ne_one_of_triangles_nonempty (G := G) htri
  exact ⟨α, Cochain.gaugeDist_pos_of_holonomy_ne_one_of_isConjInvariant hℓ huv hvw hwu hhol⟩

/-- On `complete V` with `3 ≤ Fintype.card V` and nontrivial `G`, there exists a cochain that is
not a coboundary. -/
theorem exists_not_isCoboundary_complete {V G : Type*} [Fintype V] [Group G] [Nontrivial G]
    (hV : 3 ≤ Fintype.card V) :
    ∃ α : Cochain (complete V) G, ¬ α.IsCoboundary := by
  refine exists_not_isCoboundary_of_triangles_nonempty ?_
  rw [← card_pos, card_triangles_complete]
  exact Nat.choose_pos hV

/-- On `complete V` with `3 ≤ Fintype.card V` and a nontrivial finite group `G`, there exists a
cochain at strictly positive gauge distance. -/
theorem exists_gaugeDist_pos_complete {V G : Type*} [Fintype V] [LinearOrder V]
    [Group G] [Finite G] [Nontrivial G] (hV : 3 ≤ Fintype.card V) (ℓ : GroupNorm G) :
    ∃ α : Cochain (complete V) G, 0 < α.gaugeDist ℓ := by
  refine exists_gaugeDist_pos_of_triangles_nonempty ?_ ℓ
  rw [← card_pos, card_triangles_complete]
  exact Nat.choose_pos hV

/-- On `complete V` with `3 ≤ Fintype.card V`, nontrivial `G`, and conjugation-invariant `ℓ`,
there exists a cochain at strictly positive gauge distance (without requiring `G` to be finite). -/
theorem exists_gaugeDist_pos_complete_of_isConjInvariant {V G : Type*} [Fintype V] [LinearOrder V]
    [Group G] [Nontrivial G] (hV : 3 ≤ Fintype.card V) {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    ∃ α : Cochain (complete V) G, 0 < α.gaugeDist ℓ := by
  refine exists_gaugeDist_pos_of_triangles_nonempty_of_isConjInvariant ?_ hℓ
  rw [← card_pos, card_triangles_complete]
  exact Nat.choose_pos hV

end Existence

end TauCeti

end
