/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Basic
import TauCeti.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Edge cochains and simply connected regions of the triangular lattice

An edge cochain is a function `c : TriEdge → ℤ`, read as the increment of a function on `ℤ²` from
`v` to `v + e_k` along the edge `(v, k)`. It is closed on a region `R` when it sums to zero around
every face of `R`, that is `c(f, e₁) + c(f, e₂) = c(f, e₃)` for the edges `f.edge k` of every face
`f ∈ R`; it is exact on `R` when it is the coboundary `g(v + e_k) − g(v)` of some `g : ℤ² → ℤ` on
every edge of `R`. A region is simply connected when it is nonempty, connected, and every cochain
closed on it is exact on it. This is the combinatorial form of the simple connectivity of the union
of the faces of `R`, which makes the local height rules of a tiling consistent.

## Main definitions

* `TauCeti.IsClosedCochainOn R c`: the cochain `c` is closed on the region `R`.
* `TauCeti.IsExactCochainOn R c`: the cochain `c` is exact on the region `R`.
* `TauCeti.IsSimplyConnectedRegion R`: `R` is nonempty and connected, and every cochain closed on
  `R` is exact on `R`.
* `TauCeti.neutralIncrement`: the neutral increment `c₀`, `0` along `e₁` and `e₂` and `1` along
  `e₃`.
* `TauCeti.faceSum c f`: the sum `c(f, e₁) + c(f, e₂) − c(f, e₃)` of a cochain round a face, so
  that `c` is closed on `R` when it vanishes on every face of `R`.
* `TauCeti.faceSign f`: `1` on white faces and `−1` on black ones, the orientation making
  `faceSign f * faceSum c f` the counterclockwise circulation of `c` round `f`.

## Main statements

* `TauCeti.IsExactCochainOn.isClosedCochainOn`: exact cochains are closed.
* `TauCeti.IsConnectedRegion.sub_eq_sub_of_isCochainPrimitiveOn`: on a connected region a
  primitive is unique up to an additive constant.
* `TauCeti.isSimplyConnectedRegion_vadd_iff` and `TauCeti.isSimplyConnectedRegion_rot_iff`:
  simple connectivity is invariant under translations and the rotation `ρ`.
* `TauCeti.IsCochainPrimitiveOn.insert_of_isClosedCochainOn`: if `g` is a primitive on `R` of a
  cochain `c` closed on the face `f`, and `g` is correct on two edges of `f`, then `g` is a
  primitive of `c` on `insert f R`.
* `TauCeti.isSimplyConnectedRegion_singleton`: a single face is simply connected.
* `TauCeti.IsSimplyConnectedRegion.insert_of_notMem_regionVertices` and
  `TauCeti.IsSimplyConnectedRegion.insert_of_two_edges` (shelling): adding a face that meets the
  region in one edge, whose opposite vertex is new, or in two edges, keeps it simply connected.
* `TauCeti.IsClosedCochainOn.isExactCochainOn_univ` and `TauCeti.isSimplyConnectedRegion_univ`:
  the plane is simply connected.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
-/

public section

open Pointwise

namespace TauCeti

/-- A cochain `c : TriEdge → ℤ` is closed on a region `R` when it sums to zero around every face
of `R`: `c(v,1) + c(v+e₁,2) = c(v,3)` for `W(v)` and `c(v,2) + c(v+e₂,1) = c(v,3)` for `B(v)`,
uniformly `c (f.edge 0) + c (f.edge 1) = c (f.edge 2)`. -/
def IsClosedCochainOn (R : Set TriFace) (c : TriEdge → ℤ) : Prop :=
  ∀ f ∈ R, c (f.edge 0) + c (f.edge 1) = c (f.edge 2)

/-- A function `g : ℤ × ℤ → ℤ` is a primitive of the cochain `c` on the region `R` when
`c(u, k) = g(u + e_k) − g(u)` for every edge `(u, k)` of `R`. -/
def IsCochainPrimitiveOn (R : Set TriFace) (c : TriEdge → ℤ) (g : ℤ × ℤ → ℤ) : Prop :=
  ∀ e ∈ regionEdges R, c e = g e.target - g e.v

/-- A cochain is exact on a region `R` when it has a primitive on `R`; only the values of the
primitive on the vertices of `R` matter. -/
def IsExactCochainOn (R : Set TriFace) (c : TriEdge → ℤ) : Prop :=
  ∃ g : ℤ × ℤ → ℤ, IsCochainPrimitiveOn R c g

/-- A region is simply connected when it is nonempty, connected through its edges, and every
cochain closed on it is exact on it. -/
structure IsSimplyConnectedRegion (R : Set TriFace) : Prop where
  /-- A simply connected region is nonempty. -/
  nonempty : R.Nonempty
  /-- A simply connected region is connected. -/
  isConnectedRegion : IsConnectedRegion R
  /-- Every cochain closed on a simply connected region is exact on it. -/
  isExactCochainOn_of_isClosedCochainOn : ∀ c, IsClosedCochainOn R c → IsExactCochainOn R c

/-- The neutral increment `c₀`: `0` along `e₁` and `e₂`, `1` along `e₃`. -/
def neutralIncrement (e : TriEdge) : ℤ :=
  if e.k = 2 then 1 else 0

variable {R S : Set TriFace} {c d : TriEdge → ℤ} {g g' : ℤ × ℤ → ℤ}

theorem isClosedCochainOn_def :
    IsClosedCochainOn R c ↔ ∀ f ∈ R, c (f.edge 0) + c (f.edge 1) = c (f.edge 2) := Iff.rfl

/-- The sum `c(f, e₁) + c(f, e₂) − c(f, e₃)` of a cochain round a face `f`. A cochain is closed on
a region when this vanishes on every face of the region. -/
def faceSum (c : TriEdge → ℤ) (f : TriFace) : ℤ :=
  c (f.edge 0) + c (f.edge 1) - c (f.edge 2)

/-- The orientation sign of a face: `1` for white faces and `−1` for black ones. Round a white face
`faceSum` runs counterclockwise and round a black face clockwise. -/
def faceSign (f : TriFace) : ℤ :=
  if f.isWhite then 1 else -1

theorem faceSum_def (c : TriEdge → ℤ) (f : TriFace) :
    faceSum c f = c (f.edge 0) + c (f.edge 1) - c (f.edge 2) := (rfl)

theorem faceSign_def (f : TriFace) : faceSign f = if f.isWhite then 1 else -1 := (rfl)

@[simp] theorem faceSign_mk_true (v : ℤ × ℤ) : faceSign ⟨v, true⟩ = 1 := (rfl)

@[simp] theorem faceSign_mk_false (v : ℤ × ℤ) : faceSign ⟨v, false⟩ = -1 := (rfl)

/-- The two faces of an edge have opposite orientation signs. -/
@[simp] theorem faceSign_across (f : TriFace) (k : Fin 3) :
    faceSign (f.across k) = -faceSign f := by
  simp only [faceSign_def, TriFace.isWhite_across]
  cases f.isWhite <;> simp

@[simp] theorem faceSum_zero (f : TriFace) : faceSum 0 f = 0 := by
  simp [faceSum_def]

@[simp] theorem faceSum_add (c c' : TriEdge → ℤ) (f : TriFace) :
    faceSum (c + c') f = faceSum c f + faceSum c' f := by
  simp only [faceSum_def, Pi.add_apply]
  ring

@[simp] theorem faceSum_neg (c : TriEdge → ℤ) (f : TriFace) : faceSum (-c) f = -faceSum c f := by
  simp only [faceSum_def, Pi.neg_apply]
  ring

@[simp] theorem faceSum_sub (c c' : TriEdge → ℤ) (f : TriFace) :
    faceSum (c - c') f = faceSum c f - faceSum c' f := by
  simp only [faceSum_def, Pi.sub_apply]
  ring

theorem isClosedCochainOn_iff_faceSum : IsClosedCochainOn R c ↔ ∀ f ∈ R, faceSum c f = 0 := by
  simp only [isClosedCochainOn_def, faceSum_def, sub_eq_zero]

theorem isCochainPrimitiveOn_def :
    IsCochainPrimitiveOn R c g ↔ ∀ e ∈ regionEdges R, c e = g e.target - g e.v := Iff.rfl

theorem isExactCochainOn_def :
    IsExactCochainOn R c ↔ ∃ g : ℤ × ℤ → ℤ, IsCochainPrimitiveOn R c g := Iff.rfl

theorem neutralIncrement_def (e : TriEdge) :
    neutralIncrement e = if e.k = 2 then 1 else 0 := (rfl)

@[simp] theorem neutralIncrement_mk_zero (v : ℤ × ℤ) : neutralIncrement ⟨v, 0⟩ = 0 := (rfl)

@[simp] theorem neutralIncrement_mk_one (v : ℤ × ℤ) : neutralIncrement ⟨v, 1⟩ = 0 := (rfl)

@[simp] theorem neutralIncrement_mk_two (v : ℤ × ℤ) : neutralIncrement ⟨v, 2⟩ = 1 := (rfl)

/-- The edge of direction `k` of a face has neutral increment `1` if `k = 2` and `0` otherwise. -/
theorem TriFace.neutralIncrement_edge (f : TriFace) (k : Fin 3) :
    neutralIncrement (f.edge k) = if k = 2 then 1 else 0 := by
  rw [neutralIncrement_def, TriFace.edge_k]

theorem neutralIncrement_eq_zero_or_eq_one (e : TriEdge) :
    neutralIncrement e = 0 ∨ neutralIncrement e = 1 := by
  rw [neutralIncrement_def]
  split_ifs <;> simp

/-- An increment in `{0, 1}` differs from `1 - neutralIncrement e` exactly when it is the neutral
increment. -/
theorem ne_one_sub_neutralIncrement_iff {d : ℤ} {e : TriEdge} (hd : d = 0 ∨ d = 1) :
    d ≠ 1 - neutralIncrement e ↔ d = neutralIncrement e := by
  rcases neutralIncrement_eq_zero_or_eq_one e with h | h <;> rw [h] <;> omega

theorem IsClosedCochainOn.mono (h : IsClosedCochainOn S c) (hRS : R ⊆ S) :
    IsClosedCochainOn R c :=
  fun f hf => h f (hRS hf)

theorem IsCochainPrimitiveOn.mono (h : IsCochainPrimitiveOn S c g) (hRS : R ⊆ S) :
    IsCochainPrimitiveOn R c g :=
  fun e he => h e (regionEdges_mono hRS he)

theorem IsExactCochainOn.mono (h : IsExactCochainOn S c) (hRS : R ⊆ S) : IsExactCochainOn R c :=
  h.imp fun _ hg => hg.mono hRS

@[simp] theorem isClosedCochainOn_empty (c : TriEdge → ℤ) : IsClosedCochainOn ∅ c :=
  fun _ hf => (Set.notMem_empty _ hf).elim

@[simp] theorem isClosedCochainOn_insert {f : TriFace} :
    IsClosedCochainOn (insert f R) c ↔
      c (f.edge 0) + c (f.edge 1) = c (f.edge 2) ∧ IsClosedCochainOn R c :=
  Set.forall_mem_insert

@[simp] theorem isClosedCochainOn_singleton {f : TriFace} :
    IsClosedCochainOn {f} c ↔ c (f.edge 0) + c (f.edge 1) = c (f.edge 2) :=
  Set.forall_mem_singleton

@[simp] theorem isClosedCochainOn_union :
    IsClosedCochainOn (R ∪ S) c ↔ IsClosedCochainOn R c ∧ IsClosedCochainOn S c :=
  Set.forall_mem_union

@[simp] theorem isClosedCochainOn_zero (R : Set TriFace) : IsClosedCochainOn R 0 :=
  fun _ _ => by simp

theorem IsClosedCochainOn.add (hc : IsClosedCochainOn R c) (hd : IsClosedCochainOn R d) :
    IsClosedCochainOn R (c + d) :=
  fun f hf => by simp only [Pi.add_apply]; linarith [hc f hf, hd f hf]

theorem IsClosedCochainOn.neg (hc : IsClosedCochainOn R c) : IsClosedCochainOn R (-c) :=
  fun f hf => by simp only [Pi.neg_apply]; linarith [hc f hf]

theorem IsClosedCochainOn.sub (hc : IsClosedCochainOn R c) (hd : IsClosedCochainOn R d) :
    IsClosedCochainOn R (c - d) :=
  fun f hf => by simp only [Pi.sub_apply]; linarith [hc f hf, hd f hf]

@[simp] theorem isCochainPrimitiveOn_empty (c : TriEdge → ℤ) (g : ℤ × ℤ → ℤ) :
    IsCochainPrimitiveOn ∅ c g := by
  simp [isCochainPrimitiveOn_def]

@[simp] theorem isCochainPrimitiveOn_insert {f : TriFace} :
    IsCochainPrimitiveOn (insert f R) c g ↔
      (∀ e ∈ f.edges, c e = g e.target - g e.v) ∧ IsCochainPrimitiveOn R c g := by
  simp only [isCochainPrimitiveOn_def, regionEdges_insert, Set.forall_mem_union, Finset.mem_coe]

@[simp] theorem isCochainPrimitiveOn_singleton {f : TriFace} :
    IsCochainPrimitiveOn {f} c g ↔ ∀ e ∈ f.edges, c e = g e.target - g e.v := by
  simp only [isCochainPrimitiveOn_def, regionEdges_singleton, Finset.mem_coe]

@[simp] theorem isCochainPrimitiveOn_union :
    IsCochainPrimitiveOn (R ∪ S) c g ↔ IsCochainPrimitiveOn R c g ∧ IsCochainPrimitiveOn S c g := by
  simp only [isCochainPrimitiveOn_def, regionEdges_union, Set.forall_mem_union]

/-- The zero cochain has every constant function as a primitive. -/
theorem isCochainPrimitiveOn_zero_const (R : Set TriFace) (a : ℤ) :
    IsCochainPrimitiveOn R 0 fun _ => a :=
  fun _ _ => by simp

theorem IsCochainPrimitiveOn.add (hg : IsCochainPrimitiveOn R c g)
    (hg' : IsCochainPrimitiveOn R d g') :
    IsCochainPrimitiveOn R (c + d) (g + g') :=
  fun e he => by simp only [Pi.add_apply, hg e he, hg' e he]; ring

theorem IsCochainPrimitiveOn.neg (hg : IsCochainPrimitiveOn R c g) :
    IsCochainPrimitiveOn R (-c) (-g) :=
  fun e he => by simp only [Pi.neg_apply, hg e he]; ring

theorem IsCochainPrimitiveOn.sub (hg : IsCochainPrimitiveOn R c g)
    (hg' : IsCochainPrimitiveOn R d g') :
    IsCochainPrimitiveOn R (c - d) (g - g') :=
  fun e he => by simp only [Pi.sub_apply, hg e he, hg' e he]; ring

/-- Shifting a primitive by a constant gives a primitive of the same cochain. -/
theorem IsCochainPrimitiveOn.add_const (hg : IsCochainPrimitiveOn R c g) (a : ℤ) :
    IsCochainPrimitiveOn R c fun u => g u + a :=
  fun e he => by rw [hg e he]; ring

@[simp] theorem isExactCochainOn_empty (c : TriEdge → ℤ) : IsExactCochainOn ∅ c :=
  ⟨0, isCochainPrimitiveOn_empty c 0⟩

@[simp] theorem isExactCochainOn_zero (R : Set TriFace) : IsExactCochainOn R 0 :=
  ⟨_, isCochainPrimitiveOn_zero_const R 0⟩

theorem IsExactCochainOn.add (hc : IsExactCochainOn R c) (hd : IsExactCochainOn R d) :
    IsExactCochainOn R (c + d) :=
  let ⟨_, hg⟩ := hc; let ⟨_, hg'⟩ := hd; ⟨_, hg.add hg'⟩

theorem IsExactCochainOn.neg (hc : IsExactCochainOn R c) : IsExactCochainOn R (-c) :=
  let ⟨_, hg⟩ := hc; ⟨_, hg.neg⟩

theorem IsExactCochainOn.sub (hc : IsExactCochainOn R c) (hd : IsExactCochainOn R d) :
    IsExactCochainOn R (c - d) :=
  let ⟨_, hg⟩ := hc; let ⟨_, hg'⟩ := hd; ⟨_, hg.sub hg'⟩

/-- The coboundary `g(u + e_k) − g(u)` of any `g : ℤ × ℤ → ℤ` is closed on every region. -/
theorem isClosedCochainOn_coboundary (R : Set TriFace) (g : ℤ × ℤ → ℤ) :
    IsClosedCochainOn R fun e => g e.target - g e.v := by
  rintro ⟨v, _ | _⟩ -
  · simp only [TriFace.edge_mk_false, TriEdge.target_mk, latticeDir_zero, latticeDir_one,
      latticeDir_two, Fin.reduceEq, ↓reduceIte, add_latticeDir_one_add_latticeDir_zero]
    ring
  · simp only [TriFace.edge_mk_true, TriEdge.target_mk, latticeDir_zero, latticeDir_one,
      latticeDir_two, Fin.reduceEq, ↓reduceIte, add_latticeDir_zero_add_latticeDir_one]
    ring

/-- The coboundary of a function sums to zero round every face. -/
theorem faceSum_coboundary (g : ℤ × ℤ → ℤ) (f : TriFace) :
    faceSum (fun e => g e.target - g e.v) f = 0 :=
  isClosedCochainOn_iff_faceSum.1 (isClosedCochainOn_coboundary Set.univ g) f (Set.mem_univ f)

/-- Every `g : ℤ × ℤ → ℤ` is a primitive of its coboundary `g(u + e_k) − g(u)` on every
region. -/
theorem isCochainPrimitiveOn_coboundary (R : Set TriFace) (g : ℤ × ℤ → ℤ) :
    IsCochainPrimitiveOn R (fun e => g e.target - g e.v) g :=
  fun _ _ => rfl

/-- The coboundary `g(u + e_k) − g(u)` of any `g : ℤ × ℤ → ℤ` is exact on every region. -/
theorem isExactCochainOn_coboundary (R : Set TriFace) (g : ℤ × ℤ → ℤ) :
    IsExactCochainOn R fun e => g e.target - g e.v :=
  ⟨g, isCochainPrimitiveOn_coboundary R g⟩

/-- **Exact cochains are closed.** -/
theorem IsExactCochainOn.isClosedCochainOn (h : IsExactCochainOn R c) :
    IsClosedCochainOn R c := by
  obtain ⟨g, hg⟩ := h
  intro f hf
  have := isClosedCochainOn_coboundary R g f hf
  rw [hg _ (edges_subset_regionEdges hf (f.edge_mem_edges 0)),
    hg _ (edges_subset_regionEdges hf (f.edge_mem_edges 1)),
    hg _ (edges_subset_regionEdges hf (f.edge_mem_edges 2))]
  exact this

/-- **Primitives are unique up to a constant on a connected region.** Two primitives `g`, `g'` of
the same cochain on a connected region differ by the same constant at every vertex of the
region. -/
theorem IsConnectedRegion.sub_eq_sub_of_isCochainPrimitiveOn (hR : IsConnectedRegion R)
    (hg : IsCochainPrimitiveOn R c g) (hg' : IsCochainPrimitiveOn R c g') {u u' : ℤ × ℤ}
    (hu : u ∈ regionVertices R) (hu' : u' ∈ regionVertices R) :
    g u - g' u = g u' - g' u' := by
  obtain ⟨p⟩ := isConnectedRegion_def.1 hR u hu u' hu'
  induction p with
  | nil => rfl
  | @cons a b _ hab _ ih =>
    obtain ⟨e, he, hee⟩ := regionGraph_adj.1 hab
    refine Eq.trans ?_ (ih ?_ hu')
    · have h1 := hg e he
      have h2 := hg' e he
      rw [TriEdge.endpoints_def, Sym2.eq_iff] at hee
      rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
    · rw [regionVertices_eq]
      exact ⟨e, he, hee ▸ Sym2.mem_mk_right a b⟩

/-! ### Translations -/

section Translation

variable (w : ℤ × ℤ)

@[simp] theorem neutralIncrement_vadd (e : TriEdge) :
    neutralIncrement (w +ᵥ e) = neutralIncrement e := by
  simp [neutralIncrement_def]

@[simp] theorem isClosedCochainOn_vadd_iff :
    IsClosedCochainOn (w +ᵥ R) c ↔ IsClosedCochainOn R fun e => c (w +ᵥ e) := by
  refine ⟨fun h f hf => ?_, fun h f hf => ?_⟩
  · simpa using h (w +ᵥ f) (Set.vadd_mem_vadd_set hf)
  · obtain ⟨f, hf, rfl⟩ := hf
    simpa using h f hf

@[simp] theorem isCochainPrimitiveOn_vadd_iff :
    IsCochainPrimitiveOn (w +ᵥ R) c g ↔
      IsCochainPrimitiveOn R (fun e => c (w +ᵥ e)) fun u => g (w + u) := by
  refine ⟨fun h e he => ?_, fun h e he => ?_⟩
  · simpa using h (w +ᵥ e) (by rw [regionEdges_vadd]; exact Set.vadd_mem_vadd_set he)
  · rw [regionEdges_vadd] at he
    obtain ⟨e, he, rfl⟩ := he
    simpa using h e he

@[simp] theorem isExactCochainOn_vadd_iff :
    IsExactCochainOn (w +ᵥ R) c ↔ IsExactCochainOn R fun e => c (w +ᵥ e) := by
  refine ⟨fun ⟨g, hg⟩ => ⟨_, (isCochainPrimitiveOn_vadd_iff w).1 hg⟩, fun ⟨g, hg⟩ =>
    ⟨fun u => g (-w + u), (isCochainPrimitiveOn_vadd_iff w).2 ?_⟩⟩
  simpa only [neg_add_cancel_left] using hg

/-- **Simple connectivity is invariant under translations.** -/
@[simp] theorem isSimplyConnectedRegion_vadd_iff :
    IsSimplyConnectedRegion (w +ᵥ R) ↔ IsSimplyConnectedRegion R := by
  have key : ∀ (w : ℤ × ℤ) (R : Set TriFace), IsSimplyConnectedRegion R →
      IsSimplyConnectedRegion (w +ᵥ R) := fun w R h =>
    ⟨h.nonempty.vadd_set, (isConnectedRegion_vadd_iff w R).2 h.isConnectedRegion, fun c hc =>
      (isExactCochainOn_vadd_iff w).2
        (h.isExactCochainOn_of_isClosedCochainOn _ ((isClosedCochainOn_vadd_iff w).1 hc))⟩
  exact ⟨fun h => by simpa using key (-w) _ h, key w R⟩

end Translation

/-! ### The rotation -/

section Rotation

/-- The neutral increment of `ρ e` is that of `e` for `e` of direction `e₁`, and its complement
`1 − c₀(e)` for the other two directions. -/
theorem neutralIncrement_rot (e : TriEdge) :
    neutralIncrement (TriEdge.rot e) =
      if e.k = 0 then neutralIncrement e else 1 - neutralIncrement e := by
  obtain ⟨v, k⟩ := e
  fin_cases k <;> simp [neutralIncrement_def]

/-- **Closedness under the rotation.** `ρ` preserves the orientation of the edges of direction
`1` and reverses those of directions `2` and `3` (`ρ e₂ = -e₃` and `ρ e₃ = -e₁`), so a cochain `c`
is closed on `ρ R` exactly when its signed pullback, `c ∘ ρ` along `e₁` and `-c ∘ ρ` along `e₂`
and `e₃`, is closed on `R`. -/
@[simp] theorem isClosedCochainOn_rot_iff :
    IsClosedCochainOn (TriFace.rot '' R) c ↔
      IsClosedCochainOn R fun e => if e.k = 0 then c (TriEdge.rot e) else -c (TriEdge.rot e) := by
  simp only [isClosedCochainOn_def, Set.forall_mem_image, TriFace.edge_rot, TriFace.edge_k]
  refine forall₂_congr fun f _ => ?_
  simp only [Fin.reduceSub, Fin.reduceEq, ↓reduceIte]
  constructor <;> intro h <;> linarith

/-- A function `g` is a primitive of `c` on `ρ R` exactly when `g ∘ ρ` is a primitive on `R` of
the signed pullback of `c` (see `isClosedCochainOn_rot_iff`). -/
@[simp] theorem isCochainPrimitiveOn_rot_iff :
    IsCochainPrimitiveOn (TriFace.rot '' R) c g ↔
      IsCochainPrimitiveOn R (fun e => if e.k = 0 then c (TriEdge.rot e) else -c (TriEdge.rot e))
        fun u => g (latticeRot u) := by
  simp only [isCochainPrimitiveOn_def, regionEdges_rot, Set.forall_mem_image, TriEdge.rot_v,
    TriEdge.target_rot]
  refine forall₂_congr fun e _ => ?_
  split_ifs <;> constructor <;> intro h <;> linarith

@[simp] theorem isExactCochainOn_rot_iff :
    IsExactCochainOn (TriFace.rot '' R) c ↔
      IsExactCochainOn R fun e => if e.k = 0 then c (TriEdge.rot e) else -c (TriEdge.rot e) := by
  refine ⟨fun ⟨g, hg⟩ => ⟨_, isCochainPrimitiveOn_rot_iff.1 hg⟩, fun ⟨g, hg⟩ =>
    ⟨fun u => g (latticeRot.symm u), isCochainPrimitiveOn_rot_iff.2 ?_⟩⟩
  simpa only [AddEquiv.symm_apply_apply] using hg

/-- **Simple connectivity is invariant under the rotation `ρ`.** -/
@[simp] theorem isSimplyConnectedRegion_rot_iff (R : Set TriFace) :
    IsSimplyConnectedRegion (TriFace.rot '' R) ↔ IsSimplyConnectedRegion R := by
  have key : ∀ R : Set TriFace, IsSimplyConnectedRegion R →
      IsSimplyConnectedRegion (TriFace.rot '' R) := fun R h =>
    ⟨h.nonempty.image _, (isConnectedRegion_rot_iff R).2 h.isConnectedRegion, fun c hc =>
      isExactCochainOn_rot_iff.2
        (h.isExactCochainOn_of_isClosedCochainOn _ (isClosedCochainOn_rot_iff.1 hc))⟩
  refine ⟨fun h => ?_, key R⟩
  have h3 : TriFace.rot '' (TriFace.rot '' (TriFace.rot '' R)) = R := by
    have h : ∀ f, TriFace.rot (TriFace.rot (TriFace.rot f)) = f := fun f => by
      simpa [pow_succ] using DFunLike.congr_fun TriFace.rot_pow_three f
    simp only [Set.image_image, h, Set.image_id']
  simpa only [h3] using key _ (key _ h)

end Rotation

/-! ### Faces and shelling -/

/-- If a cochain vanishes on two distinct edges of a face and is closed on that face, it vanishes
on the third. -/
private theorem edge_eq_zero_of_closed {f : TriFace}
    (hd : d (f.edge 0) + d (f.edge 1) = d (f.edge 2)) {i j : Fin 3} (hij : i ≠ j)
    (hi : d (f.edge i) = 0) (hj : d (f.edge j) = 0) (k : Fin 3) : d (f.edge k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- **Extending a primitive across a face.** If `g` is a primitive on `R` of a cochain `c` closed
on the face `f`, and `g` is also a primitive of `c` along two distinct edges of `f`, then `g` is a
primitive of `c` on `insert f R`. -/
theorem IsCochainPrimitiveOn.insert_of_isClosedCochainOn {f : TriFace}
    (hg : IsCochainPrimitiveOn R c g) (hc : IsClosedCochainOn {f} c) {i j : Fin 3}
    (hij : i ≠ j)
    (hi : c (f.edge i) = g (f.edge i).target - g (f.edge i).v)
    (hj : c (f.edge j) = g (f.edge j).target - g (f.edge j).v) :
    IsCochainPrimitiveOn (insert f R) c g := by
  intro e he
  obtain ⟨f', hf', hef'⟩ := mem_regionEdges.1 he
  rcases hf' with rfl | hf'
  · have hd := (hc.sub (isClosedCochainOn_coboundary _ g)) f' rfl
    simp only [Pi.sub_apply] at hd
    have := edge_eq_zero_of_closed (d := fun e => c e - (g e.target - g e.v)) hd hij
      (sub_eq_zero.2 hi) (sub_eq_zero.2 hj) e.k
    rw [TriFace.mem_edges_iff_edge_eq.1 hef'] at this
    exact sub_eq_zero.1 this
  · exact hg e (mem_regionEdges.2 ⟨f', hf', hef'⟩)

/-- **A single face is simply connected.** -/
theorem isSimplyConnectedRegion_singleton (f : TriFace) : IsSimplyConnectedRegion {f} := by
  refine ⟨Set.singleton_nonempty f, isConnectedRegion_singleton f, fun c hc => ?_⟩
  -- The primitive vanishes at `f.v`, takes `c (f.edge 2)` at the top vertex `f.v + e₃`, and is
  -- fixed by `c` on the first edge of `f` at the remaining vertex.
  obtain ⟨v, col⟩ := f
  let i : Fin 3 := if col then 0 else 1
  let m : ℤ × ℤ := if col then v + (1, 0) else v + (0, 1)
  let g : ℤ × ℤ → ℤ := fun u => if u = v + (1, 1) then c (TriFace.edge ⟨v, col⟩ 2)
    else if u = m then c (TriFace.edge ⟨v, col⟩ i) else 0
  refine ⟨g, isCochainPrimitiveOn_singleton.2 ?_⟩
  cases col <;> simp [g, i, m, Prod.ext_iff] at hc ⊢ <;> omega

/-- **Shelling across one edge.** If `R` is simply connected and a face `f` meets the edges of
`R` in an edge `f.edge i` whose opposite vertex `p` is not a vertex of `R`, then `R ∪ {f}` is
simply connected. -/
theorem IsSimplyConnectedRegion.insert_of_notMem_regionVertices (hR : IsSimplyConnectedRegion R)
    {f : TriFace} {i : Fin 3} (hi : f.edge i ∈ regionEdges R) {p : ℤ × ℤ}
    (hp : p ∈ f.vertices) (hpR : p ∉ regionVertices R) :
    IsSimplyConnectedRegion (insert f R) := by
  have hpi : p ∉ (f.edge i).endpoints := fun h => hpR (mem_regionVertices_of_mem_endpoints hi h)
  have hj : i + 1 ≠ i := by fin_cases i <;> decide
  set e₁ := f.edge (i + 1) with he₁
  have hpe₁ : p ∈ e₁.endpoints := TriFace.mem_endpoints_of_notMem hj.symm hp hpi
  refine ⟨hR.nonempty.mono (Set.subset_insert _ _),
    hR.isConnectedRegion.insert_of_mem_regionVertices
      (TriFace.v_mem_vertices_of_mem_edges (f.edge_mem_edges i))
      (mem_regionVertices_of_mem_endpoints hi (TriEdge.mem_endpoints.2 (Or.inl rfl))),
    fun c hc => ?_⟩
  obtain ⟨g, hg⟩ := hR.isExactCochainOn_of_isClosedCochainOn c (hc.mono (Set.subset_insert _ _))
  -- adjust `g` at the new vertex `p` so that it is a primitive along `e₁`
  let t : ℤ := if p = e₁.target then g e₁.v + c e₁ else g e₁.target - c e₁
  have hgR : IsCochainPrimitiveOn R c (Function.update g p t) := by
    intro e he
    have h1 : e.target ≠ p := fun h => hpR (mem_regionVertices_of_mem_endpoints he
      (TriEdge.mem_endpoints.2 (Or.inr h.symm)))
    have h2 : e.v ≠ p := fun h => hpR (mem_regionVertices_of_mem_endpoints he
      (TriEdge.mem_endpoints.2 (Or.inl h.symm)))
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    exact hg e he
  refine ⟨_, hgR.insert_of_isClosedCochainOn
    (hc.mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))) hj.symm (hgR _ hi) ?_⟩
  rw [← he₁]
  rcases TriEdge.mem_endpoints.1 hpe₁ with h | h
  · have hne : e₁.target ≠ p := h ▸ e₁.v_ne_target.symm
    rw [Function.update_of_ne hne, h, Function.update_self]
    simp only [t, hne.symm, ↓reduceIte]
    ring
  · have hne : e₁.v ≠ p := h ▸ e₁.v_ne_target
    rw [Function.update_of_ne hne, h, Function.update_self]
    simp only [t, h, ↓reduceIte]
    ring

/-- **Shelling across two edges.** If `R` is simply connected and two distinct edges of a face
`f` are edges of `R`, then `R ∪ {f}` is simply connected. -/
theorem IsSimplyConnectedRegion.insert_of_two_edges (hR : IsSimplyConnectedRegion R)
    {f : TriFace} {i j : Fin 3} (hij : i ≠ j) (hi : f.edge i ∈ regionEdges R)
    (hj : f.edge j ∈ regionEdges R) : IsSimplyConnectedRegion (insert f R) := by
  refine ⟨hR.nonempty.mono (Set.subset_insert _ _),
    hR.isConnectedRegion.insert_of_mem_regionVertices
      (TriFace.v_mem_vertices_of_mem_edges (f.edge_mem_edges i))
      (mem_regionVertices_of_mem_endpoints hi (TriEdge.mem_endpoints.2 (Or.inl rfl))),
    fun c hc => ?_⟩
  obtain ⟨g, hg⟩ := hR.isExactCochainOn_of_isClosedCochainOn c (hc.mono (Set.subset_insert _ _))
  exact ⟨g, hg.insert_of_isClosedCochainOn
    (hc.mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))) hij (hg _ hi) (hg _ hj)⟩

/-! ### The plane -/

/-- **The plane is simply connected, the exactness part.** A cochain closed on every face of the
plane is exact on the plane. -/
theorem IsClosedCochainOn.isExactCochainOn_univ (hc : IsClosedCochainOn Set.univ c) :
    IsExactCochainOn Set.univ c := by
  -- The primitive vanishing at `0` sums `c` along `e₁` on the axis `y = 0` and then along `e₂`.
  -- the square relation `c(v,1) + c(v+e₁,2) = c(v,2) + c(v+e₂,1)` from the two faces at `v`
  have hsq : ∀ v : ℤ × ℤ, c ⟨v, 0⟩ + c ⟨v + (1, 0), 1⟩ = c ⟨v, 1⟩ + c ⟨v + (0, 1), 0⟩ := by
    intro v
    have hw := hc ⟨v, true⟩ (Set.mem_univ _)
    have hb := hc ⟨v, false⟩ (Set.mem_univ _)
    simp only [TriFace.edge_mk_true, TriFace.edge_mk_false, Fin.reduceEq, ↓reduceIte] at hw hb
    linarith
  -- the discrete primitive of a sequence `a : ℤ → ℤ` vanishing at `0`
  let P : (ℤ → ℤ) → ℤ → ℤ := fun a i => ∑ j ∈ Finset.Ico 0 i, a j - ∑ j ∈ Finset.Ico i 0, a j
  have hP : ∀ a i, P a (i + 1) = P a i + a i :=
    Finset.sum_Ico_zero_add_one_sub_sum_Ico_add_one_zero
  let B : ℤ → ℤ → ℤ := fun x => P fun y => c ⟨(x, y), 1⟩
  let A : ℤ → ℤ := P fun x => c ⟨(x, 0), 0⟩
  let g : ℤ × ℤ → ℤ := fun v => A v.1 + B v.1 v.2
  have hB : ∀ x y, B x (y + 1) = B x y + c ⟨(x, y), 1⟩ := fun x y => hP _ y
  -- moving along `e₁` changes `B` by the difference of the `e₁`-increments
  have hD : ∀ x y, B (x + 1) y - B x y = c ⟨(x, y), 0⟩ - c ⟨(x, 0), 0⟩ := by
    intro x y
    induction y using Int.induction_on with
    | zero => simp [B, P]
    | succ y ih =>
      have := hsq (x, y)
      simp only [Prod.mk_add_mk, add_zero] at this
      rw [hB, hB]
      linarith
    | pred y ih =>
      have := hsq (x, -(y : ℤ) - 1)
      have h1 := hB (x + 1) (-(y : ℤ) - 1)
      have h2 := hB x (-(y : ℤ) - 1)
      simp only [Prod.mk_add_mk, add_zero, sub_add_cancel] at this h1 h2
      linarith
  have he₁ : ∀ v : ℤ × ℤ, g (v + (1, 0)) - g v = c ⟨v, 0⟩ := by
    rintro ⟨x, y⟩
    simp only [g, A, Prod.mk_add_mk, add_zero, hP]
    linarith [hD x y]
  have he₂ : ∀ v : ℤ × ℤ, g (v + (0, 1)) - g v = c ⟨v, 1⟩ := by
    rintro ⟨x, y⟩
    simp only [g, Prod.mk_add_mk, hB]
    ring_nf
  refine ⟨g, fun ⟨v, k⟩ _ => ?_⟩
  fin_cases k
  · simpa using (he₁ v).symm
  · simpa using (he₂ v).symm
  · have hw := hc ⟨v, true⟩ (Set.mem_univ _)
    simp only [TriFace.edge_mk_true, Fin.reduceEq, ↓reduceIte] at hw
    have h1 := he₁ v
    have h2 := he₂ (v + (1, 0))
    rw [add_latticeDir_zero_add_latticeDir_one] at h2
    simp only [Fin.reduceFinMk, Fin.isValue, TriEdge.target_mk, latticeDir_two]
    linarith

/-- **The plane is simply connected.** -/
theorem isSimplyConnectedRegion_univ : IsSimplyConnectedRegion Set.univ :=
  ⟨⟨⟨0, true⟩, Set.mem_univ _⟩, isConnectedRegion_univ, fun _ hc => hc.isExactCochainOn_univ⟩

/-- A primitive on the plane is a function whose increment along every edge is the cochain. -/
theorem isCochainPrimitiveOn_univ_iff :
    IsCochainPrimitiveOn Set.univ c g ↔ ∀ e : TriEdge, c e = g e.target - g e.v := by
  rw [isCochainPrimitiveOn_def]
  exact ⟨fun h e => h e (mem_regionEdges_iff.2 (Or.inl (Set.mem_univ _))), fun h e _ => h e⟩

/-- Two primitives on the plane of the same cochain that agree at `0` are equal. -/
theorem eq_of_isCochainPrimitiveOn_univ (hg : IsCochainPrimitiveOn Set.univ c g)
    (hg' : IsCochainPrimitiveOn Set.univ c g') (h0 : g 0 = g' 0) : g = g' := by
  funext u
  have := isConnectedRegion_univ.sub_eq_sub_of_isCochainPrimitiveOn hg hg'
    (mem_regionVertices_univ u) (mem_regionVertices_univ 0)
  omega

end TauCeti
