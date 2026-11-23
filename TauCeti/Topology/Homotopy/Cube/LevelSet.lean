/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic

/-!
# Zero level sets of monotone families on a cube deform onto their diagonal roots

Let `X` be a topological space and `G : X → (ι → [0, 1]) → ℝ` a jointly continuous family of
functions on the cube `[0, 1]^ι`, each strictly increasing for the coordinatewise order (any strict
increase of some coordinates strictly increases `G x`), with `G x 0 ≤ 0 ≤ G x 1`. This file shows
that the zero level set

`Z = {(x, u) | G x u = 0} ⊆ X × [0, 1]^ι` (`TauCeti.cubeLevelSet G`)

deforms onto the graph of its *diagonal root*, fibrewise over `X`.

* For each `x` there is exactly one point `t(x) · 1` of the diagonal of the cube with
  `G x (t(x) · 1) = 0` (`TauCeti.cubeDiagonalRoot G x`, with `t(x)` being
  `TauCeti.cubeDiagonalRootParam G x`), and it depends continuously on `x`
  (`TauCeti.continuous_cubeDiagonalRoot`, `TauCeti.continuous_cubeDiagonalRootParam`). When
  `G x 0 < 0 < G x 1`, it lies in the open cube (`TauCeti.cubeDiagonalRootParam_mem_Ioo`).
* For every point `a` of the cube, the shifts `clamp(a + τ · 1)` of `a` along the diagonal,
  clamped back into the cube (`TauCeti.clampShift a τ`), increase with `τ`, so `G x` vanishes on
  exactly one of them (`TauCeti.cubeLevelPoint G x a`). Although `τ` may be non-unique, at a plateau
  where all coordinates are clamped, the vector is unique: two different such vectors are
  comparable and `G x` would separate them. This *level point* depends continuously on `(x, a)`
  (`TauCeti.continuous_cubeLevelPoint`), by the closed graph theorem for maps into the compact cube:
  `τ` ranges over the compact interval `[-1, 1]`.
* Moving `u` along the segment from `u` to `t(x) · 1` and taking level points gives a homotopy
  `(x, u) ↦ (x, cubeLevelPoint G x ((1 - s) u + s t(x) · 1))` in `Z` from the identity to the map
  `(x, u) ↦ (x, t(x) · 1)` (`TauCeti.cubeLevelSetHomotopy`). It preserves the first coordinate
  and fixes the graph of the diagonal root, so it is a strong deformation retraction of `Z`
  onto that graph. Hence the projection `Z → X` and the section `x ↦ (x, t(x) · 1)` form a fibre
  homotopy equivalence over `X` (`TauCeti.cubeLevelSetFiberHomotopyEquiv`), and in particular
  the section is a homotopy equivalence `X ≃ₕ Z` (`TauCeti.cubeLevelSetHomotopyEquiv`).
* Since the equivalence is fibrewise, for any `A ⊆ X` the projection is also a homotopy
  equivalence of pairs `(Z, Z ∩ (A × [0, 1]^ι)) → (X, A)`, so it induces isomorphisms on relative
  singular homology (`TauCeti.FiberHomotopyEquiv.isIso_singularHomologyMap_preimagePairMap`
  applied to `TauCeti.cubeLevelSetFiberHomotopyEquiv`).

This is meant for the pair deformation in the isolating-block proof of the Poincaré–Birkhoff
theorem by generating functions. There `x` collects the base point on the circle and the negative
incoming momenta `v ∈ [0, 1]^K`, `u ∈ [0, 1]^K` are the positive incoming momenta, and `G` is the
closing defect of the broken orbit. Once that defect is shown to be strictly increasing in `u`
with the endpoint signs above, and the block and its exit set are identified with `Z` and with
the points of `Z` whose `v` lies on the boundary of the cube, taking `A` to be those points
yields the homotopy equivalence of the block with its exit set to `S¹ × ([0, 1]^K, ∂[0, 1]^K)`.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public noncomputable section

open Set Function unitInterval
open scoped ContinuousMap

namespace TauCeti

section Cube

variable {ι : Type*}

/-! ### Clamped diagonal shifts -/

/-- The shift of a point `a` of the cube `[0, 1]^ι` by `τ` along the diagonal, clamped back into
the cube: its coordinates are `clamp(a i + τ)`. -/
def clampShift (a : ι → I) (τ : ℝ) : ι → I :=
  fun i ↦ projIcc 0 1 zero_le_one (a i + τ)

lemma clampShift_apply (a : ι → I) (τ : ℝ) (i : ι) :
    clampShift a τ i = projIcc 0 1 zero_le_one (a i + τ) := (rfl)

@[simp]
lemma clampShift_zero (a : ι → I) : clampShift a 0 = a := by
  ext i
  simp [clampShift_apply]

lemma clampShift_of_le_neg_one (a : ι → I) {τ : ℝ} (hτ : τ ≤ -1) : clampShift a τ = 0 := by
  ext i
  simp [clampShift_apply, projIcc_of_le_left _ (by linarith [(a i).property.2] : a i + τ ≤ 0)]

lemma clampShift_of_one_le (a : ι → I) {τ : ℝ} (hτ : 1 ≤ τ) : clampShift a τ = 1 := by
  ext i
  simp [clampShift_apply, projIcc_of_right_le _ (by linarith [(a i).property.1] : 1 ≤ a i + τ)]

/-- The clamped shifts of the corner `0` are the points of the diagonal. -/
lemma clampShift_zero_left (τ : ℝ) :
    clampShift (0 : ι → I) τ = fun _ ↦ projIcc 0 1 zero_le_one τ := by
  ext i
  simp [clampShift_apply]

lemma monotone_clampShift (a : ι → I) : Monotone (clampShift a) :=
  fun _ _ h i ↦ monotone_projIcc _ (by linarith)

@[fun_prop]
lemma continuous_clampShift : Continuous fun p : (ι → I) × ℝ ↦ clampShift p.1 p.2 :=
  continuous_pi fun _ ↦ continuous_projIcc.comp (by fun_prop)

/-- Every clamped shift of `a` is a shift by some `τ ∈ [-1, 1]`. -/
lemma exists_mem_Icc_clampShift_eq (a : ι → I) (τ : ℝ) :
    ∃ τ' ∈ Icc (-1 : ℝ) 1, clampShift a τ' = clampShift a τ := by
  rcases le_or_gt τ (-1) with h | h
  · exact ⟨-1, ⟨le_rfl, by norm_num⟩, by
      rw [clampShift_of_le_neg_one a le_rfl, clampShift_of_le_neg_one a h]⟩
  rcases le_or_gt 1 τ with h' | h'
  · exact ⟨1, ⟨by norm_num, le_rfl⟩, by
      rw [clampShift_of_one_le a le_rfl, clampShift_of_one_le a h']⟩
  exact ⟨τ, ⟨h.le, h'.le⟩, rfl⟩

/-! ### Level points -/

variable {X : Type*} {G : X → (ι → I) → ℝ} {x : X} {a : ι → I}

/-- The *level point* of `a` for `G x`: the clamped diagonal shift `clampShift a τ` of `a`, with
`τ ∈ [-1, 1]`, at which `G x` vanishes, or `a` itself if there is none. When each `G x` is
continuous and strictly increasing with `G x 0 ≤ 0 ≤ G x 1`, this point exists
(`TauCeti.apply_cubeLevelPoint_eq_zero`) and is unique
(`TauCeti.cubeLevelPoint_eq_of_apply_clampShift_eq_zero`),
and it depends continuously on `(x, a)` (`TauCeti.continuous_cubeLevelPoint`). -/
def cubeLevelPoint (G : X → (ι → I) → ℝ) (x : X) (a : ι → I) : ι → I :=
  open scoped Classical in
  if h : ∃ τ ∈ Icc (-1 : ℝ) 1, G x (clampShift a τ) = 0 then clampShift a h.choose else a

/-- If some clamped shift `clampShift a τ` with `τ ∈ [-1, 1]` is a zero of `G x`, the level point
of `a` is the chosen such shift. -/
lemma cubeLevelPoint_of_exists (h : ∃ τ ∈ Icc (-1 : ℝ) 1, G x (clampShift a τ) = 0) :
    cubeLevelPoint G x a = clampShift a h.choose := by
  rw [cubeLevelPoint, dite_eq_left h]

/-- If no clamped shift `clampShift a τ` with `τ ∈ [-1, 1]` is a zero of `G x`, the level point
of `a` is `a` itself. -/
lemma cubeLevelPoint_of_not_exists (h : ¬∃ τ ∈ Icc (-1 : ℝ) 1, G x (clampShift a τ) = 0) :
    cubeLevelPoint G x a = a := by
  rw [cubeLevelPoint, dite_eq_right h]

lemma exists_cubeLevelPoint_eq_clampShift (G : X → (ι → I) → ℝ) (x : X) (a : ι → I) :
    ∃ τ ∈ Icc (-1 : ℝ) 1, cubeLevelPoint G x a = clampShift a τ := by
  by_cases h : ∃ τ ∈ Icc (-1 : ℝ) 1, G x (clampShift a τ) = 0
  · exact ⟨h.choose, h.choose_spec.1, cubeLevelPoint_of_exists h⟩
  · exact ⟨0, ⟨by norm_num, by norm_num⟩, by rw [cubeLevelPoint_of_not_exists h, clampShift_zero]⟩

/-- A strictly increasing function on the cube vanishes on at most one clamped diagonal shift
of `a`. -/
lemma clampShift_eq_of_apply_eq_zero (hmono : StrictMono (G x)) {τ τ' : ℝ}
    (h : G x (clampShift a τ) = 0) (h' : G x (clampShift a τ') = 0) :
    clampShift a τ = clampShift a τ' := by
  by_contra hne
  rcases le_total τ τ' with hle | hle
  · exact (hmono ((monotone_clampShift a hle).lt_of_ne hne)).ne (h.trans h'.symm)
  · exact (hmono ((monotone_clampShift a hle).lt_of_ne (Ne.symm hne))).ne (h'.trans h.symm)

/-- **Uniqueness of the level point.** A clamped diagonal shift of `a` on which the strictly
increasing function `G x` vanishes is the level point of `a`. -/
theorem cubeLevelPoint_eq_of_apply_clampShift_eq_zero (hmono : StrictMono (G x)) {τ : ℝ}
    (h : G x (clampShift a τ) = 0) : cubeLevelPoint G x a = clampShift a τ := by
  obtain ⟨τ', hτ', hτ'eq⟩ := exists_mem_Icc_clampShift_eq a τ
  have hex : ∃ τ ∈ Icc (-1 : ℝ) 1, G x (clampShift a τ) = 0 := ⟨τ', hτ', hτ'eq ▸ h⟩
  rw [cubeLevelPoint_of_exists hex]
  exact clampShift_eq_of_apply_eq_zero hmono hex.choose_spec.2 h

/-- A point of the zero level set of a strictly increasing `G x` is its own level point. -/
theorem cubeLevelPoint_eq_self (hmono : StrictMono (G x)) (h : G x a = 0) :
    cubeLevelPoint G x a = a := by
  simpa using cubeLevelPoint_eq_of_apply_clampShift_eq_zero (τ := 0) hmono (by simpa using h)

/-- **Existence of the level point.** If `G x` is continuous with `G x 0 ≤ 0 ≤ G x 1`, it vanishes
at the level point of every point `a` of the cube. -/
theorem apply_cubeLevelPoint_eq_zero (hG : Continuous (G x)) (h₀ : G x 0 ≤ 0) (h₁ : 0 ≤ G x 1)
    (a : ι → I) : G x (cubeLevelPoint G x a) = 0 := by
  have hc : ContinuousOn (fun τ ↦ G x (clampShift a τ)) (Icc (-1) 1) :=
    (hG.comp (continuous_clampShift.comp (continuous_const.prodMk continuous_id))).continuousOn
  obtain ⟨τ, hτ, h⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hc
    ⟨by simpa [clampShift_of_le_neg_one a le_rfl] using h₀,
      by simpa [clampShift_of_one_le a le_rfl] using h₁⟩
  have hex : ∃ τ ∈ Icc (-1 : ℝ) 1, G x (clampShift a τ) = 0 := ⟨τ, hτ, h⟩
  rw [cubeLevelPoint_of_exists hex]
  exact hex.choose_spec.2

/-- The level point of `a` is the unique clamped diagonal shift of `a` on which `G x` vanishes. -/
theorem cubeLevelPoint_eq_clampShift_iff (hG : Continuous (G x)) (hmono : StrictMono (G x))
    (h₀ : G x 0 ≤ 0) (h₁ : 0 ≤ G x 1) {τ : ℝ} :
    cubeLevelPoint G x a = clampShift a τ ↔ G x (clampShift a τ) = 0 :=
  ⟨fun h ↦ h ▸ apply_cubeLevelPoint_eq_zero hG h₀ h₁ a,
    cubeLevelPoint_eq_of_apply_clampShift_eq_zero hmono⟩

/-- **Continuity of the level point**, jointly in the parameter and the point of the cube, for a
jointly continuous family of strictly increasing functions with `G x 0 ≤ 0 ≤ G x 1`. -/
theorem continuous_cubeLevelPoint [TopologicalSpace X] (hG : Continuous (uncurry G))
    (hmono : ∀ x, StrictMono (G x)) (h₀ : ∀ x, G x 0 ≤ 0) (h₁ : ∀ x, 0 ≤ G x 1) :
    Continuous fun p : X × (ι → I) ↦ cubeLevelPoint G p.1 p.2 := by
  -- The graph is the set of `((x, a), w)` with `G x w = 0` and `w = clampShift a τ` for some
  -- `τ ∈ [-1, 1]`; it is closed because `[-1, 1]` is compact, and the cube is compact.
  apply continuous_of_isClosed_graph
  let S : Set (((X × (ι → I)) × (ι → I)) × Icc (-1 : ℝ) 1) :=
    {r | r.1.2 = clampShift r.1.1.2 r.2}
  have hS : IsClosed S :=
    isClosed_eq (by fun_prop) (continuous_clampShift.comp
      (by fun_prop : Continuous fun r : ((X × (ι → I)) × (ι → I)) × Icc (-1 : ℝ) 1 ↦
        (r.1.1.2, (r.2 : ℝ))))
  have hgraph : (graph fun p : X × (ι → I) ↦ cubeLevelPoint G p.1 p.2) =
      {q : (X × (ι → I)) × (ι → I) | G q.1.1 q.2 = 0} ∩ Prod.fst '' S := by
    ext ⟨⟨x, a⟩, w⟩
    simp only [mem_graph, mem_inter_iff, mem_ofPred_eq, mem_image, Prod.exists, Subtype.exists,
      S]
    constructor
    · rintro rfl
      obtain ⟨τ, hτ, h⟩ := exists_cubeLevelPoint_eq_clampShift G x a
      exact ⟨apply_cubeLevelPoint_eq_zero (hG.uncurry_left x) (h₀ x) (h₁ x) a, x, a,
        cubeLevelPoint G x a, τ, hτ, h, rfl⟩
    · rintro ⟨hw, x', a', w', τ, -, hw', heq⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      rw [hw'] at hw ⊢
      exact cubeLevelPoint_eq_of_apply_clampShift_eq_zero (hmono x') hw
  rw [hgraph]
  exact (isClosed_eq (hG.comp (by fun_prop : Continuous fun q : (X × (ι → I)) × (ι → I) ↦
    (q.1.1, q.2))) continuous_const).inter
    (isClosedMap_fst_of_compactSpace _ hS)

/-! ### The diagonal root -/

/-- The *diagonal root* of `G x`: the level point of the corner `0`. It is a point
`t · 1` of the diagonal of the cube (`TauCeti.cubeDiagonalRoot_eq_const`, with
`t = TauCeti.cubeDiagonalRootParam G x`). When `G x` is continuous with `G x 0 ≤ 0 ≤ G x 1`,
`G x` vanishes there (`TauCeti.apply_cubeDiagonalRoot_eq_zero`), and when `G x` is moreover
strictly increasing it is the only point of the diagonal on which `G x` vanishes
(`TauCeti.cubeDiagonalRoot_eq_of_apply_eq_zero`). -/
def cubeDiagonalRoot (G : X → (ι → I) → ℝ) (x : X) : ι → I :=
  cubeLevelPoint G x 0

lemma cubeDiagonalRoot_def (G : X → (ι → I) → ℝ) (x : X) :
    cubeDiagonalRoot G x = cubeLevelPoint G x 0 :=
  (rfl)

/-- The *diagonal root parameter* `t(x)` of `G x`: the common value of the coordinates of the
diagonal root `t(x) · 1` (`TauCeti.cubeDiagonalRoot_eq_const`). -/
def cubeDiagonalRootParam (G : X → (ι → I) → ℝ) (x : X) : I :=
  projIcc 0 1 zero_le_one (exists_cubeLevelPoint_eq_clampShift G x 0).choose

/-- The diagonal root lies on the diagonal of the cube. -/
theorem cubeDiagonalRoot_eq_const (G : X → (ι → I) → ℝ) (x : X) :
    cubeDiagonalRoot G x = fun _ ↦ cubeDiagonalRootParam G x := by
  rw [cubeDiagonalRoot_def, (exists_cubeLevelPoint_eq_clampShift G x 0).choose_spec.2,
    clampShift_zero_left, cubeDiagonalRootParam]

@[simp]
lemma cubeDiagonalRoot_apply (G : X → (ι → I) → ℝ) (x : X) (i : ι) :
    cubeDiagonalRoot G x i = cubeDiagonalRootParam G x := by
  rw [cubeDiagonalRoot_eq_const]

/-- If `G x` is continuous with `G x 0 ≤ 0 ≤ G x 1`, it vanishes at its diagonal root. -/
theorem apply_cubeDiagonalRoot_eq_zero (hG : Continuous (G x)) (h₀ : G x 0 ≤ 0)
    (h₁ : 0 ≤ G x 1) : G x (cubeDiagonalRoot G x) = 0 :=
  apply_cubeLevelPoint_eq_zero hG h₀ h₁ 0

/-- The diagonal root of a continuous, strictly increasing `G x` is its own level point. -/
theorem cubeLevelPoint_cubeDiagonalRoot (hG : Continuous (G x)) (hmono : StrictMono (G x))
    (h₀ : G x 0 ≤ 0) (h₁ : 0 ≤ G x 1) :
    cubeLevelPoint G x (cubeDiagonalRoot G x) = cubeDiagonalRoot G x :=
  cubeLevelPoint_eq_self hmono (apply_cubeDiagonalRoot_eq_zero hG h₀ h₁)

/-- **Uniqueness of the diagonal root.** A point of the diagonal on which the strictly increasing
function `G x` vanishes is the diagonal root. -/
theorem cubeDiagonalRoot_eq_of_apply_eq_zero (hmono : StrictMono (G x)) {t : I}
    (h : G x (fun _ ↦ t) = 0) : cubeDiagonalRoot G x = fun _ ↦ t := by
  have ht : clampShift (0 : ι → I) t = fun _ ↦ t := by
    rw [clampShift_zero_left, projIcc_val]
  rw [cubeDiagonalRoot_def, cubeLevelPoint_eq_of_apply_clampShift_eq_zero hmono (ht ▸ h), ht]

/-- **Uniqueness of the diagonal root parameter.** If the cube is nonempty, a constant vector
`t · 1` on which the strictly increasing function `G x` vanishes has `t` the diagonal root
parameter. -/
theorem cubeDiagonalRootParam_eq_of_apply_eq_zero [Nonempty ι] (hmono : StrictMono (G x)) {t : I}
    (h : G x (fun _ ↦ t) = 0) : cubeDiagonalRootParam G x = t := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [← cubeDiagonalRoot_apply G x i, cubeDiagonalRoot_eq_of_apply_eq_zero hmono h]

/-- When `G x 0 < 0 < G x 1`, the diagonal root parameter lies in the open interval `(0, 1)`. -/
theorem cubeDiagonalRootParam_mem_Ioo (hG : Continuous (G x)) (h₀ : G x 0 < 0) (h₁ : 0 < G x 1) :
    (cubeDiagonalRootParam G x : ℝ) ∈ Ioo 0 1 := by
  have hroot := apply_cubeDiagonalRoot_eq_zero hG h₀.le h₁.le
  rw [cubeDiagonalRoot_eq_const] at hroot
  set t := cubeDiagonalRootParam G x
  refine ⟨lt_of_le_of_ne t.property.1 fun h ↦ h₀.ne ?_,
    lt_of_le_of_ne t.property.2 fun h ↦ h₁.ne' ?_⟩
  · have : (fun _ ↦ t : ι → I) = 0 := funext fun _ ↦ Subtype.ext h.symm
    rwa [this] at hroot
  · have : (fun _ ↦ t : ι → I) = 1 := funext fun _ ↦ Subtype.ext h
    rwa [this] at hroot

/-- The diagonal root depends continuously on the parameter. -/
theorem continuous_cubeDiagonalRoot [TopologicalSpace X] (hG : Continuous (uncurry G))
    (hmono : ∀ x, StrictMono (G x)) (h₀ : ∀ x, G x 0 ≤ 0) (h₁ : ∀ x, 0 ≤ G x 1) :
    Continuous (cubeDiagonalRoot G) :=
  (continuous_cubeLevelPoint hG hmono h₀ h₁).comp (continuous_id.prodMk continuous_const)

/-- If the cube is nonempty, the diagonal root parameter depends continuously on the
parameter. -/
theorem continuous_cubeDiagonalRootParam [TopologicalSpace X] [Nonempty ι]
    (hG : Continuous (uncurry G)) (hmono : ∀ x, StrictMono (G x)) (h₀ : ∀ x, G x 0 ≤ 0)
    (h₁ : ∀ x, 0 ≤ G x 1) : Continuous (cubeDiagonalRootParam G) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ((continuous_apply i).comp (continuous_cubeDiagonalRoot hG hmono h₀ h₁)).congr
    fun x ↦ cubeDiagonalRoot_apply G x i

/-! ### The deformation of the zero level set -/

/-- The zero level set `{(x, u) | G x u = 0}` of a family of functions on the cube `[0, 1]^ι`. -/
def cubeLevelSet (G : X → (ι → I) → ℝ) : Set (X × (ι → I)) :=
  {p | G p.1 p.2 = 0}

@[simp]
lemma mem_cubeLevelSet {p : X × (ι → I)} : p ∈ cubeLevelSet G ↔ G p.1 p.2 = 0 :=
  Iff.rfl

variable [TopologicalSpace X]

/-- The projection `(x, u) ↦ x` of the zero level set to the parameter space. -/
def cubeLevelSetProj (G : X → (ι → I) → ℝ) : C(cubeLevelSet G, X) :=
  ⟨fun p ↦ p.val.1, by fun_prop⟩

@[simp]
lemma cubeLevelSetProj_apply (p : cubeLevelSet G) : cubeLevelSetProj G p = p.val.1 :=
  (rfl)

variable (hG : Continuous (uncurry G)) (hmono : ∀ x, StrictMono (G x)) (h₀ : ∀ x, G x 0 ≤ 0)
  (h₁ : ∀ x, 0 ≤ G x 1)

/-- The section `x ↦ (x, t(x) · 1)` of the zero level set through the diagonal roots. -/
def cubeLevelSetSection : C(X, cubeLevelSet G) where
  toFun x := ⟨(x, cubeDiagonalRoot G x),
    apply_cubeDiagonalRoot_eq_zero (hG.uncurry_left x) (h₀ x) (h₁ x)⟩
  continuous_toFun :=
    (continuous_id.prodMk (continuous_cubeDiagonalRoot hG hmono h₀ h₁)).subtype_mk _

@[simp]
lemma coe_cubeLevelSetSection_apply (x : X) :
    (cubeLevelSetSection hG hmono h₀ h₁ x : X × (ι → I)) = (x, cubeDiagonalRoot G x) :=
  (rfl)

/-- The point `(1 - s) u + s t(x) · 1` of the segment from `u` to the diagonal root. -/
private def segmentToRoot (G : X → (ι → I) → ℝ) (s : I) (p : X × (ι → I)) : ι → I :=
  fun i ↦ Icc.convexComb (p.2 i) (cubeDiagonalRoot G p.1 i) s

omit [TopologicalSpace X] in
@[simp]
private lemma segmentToRoot_zero (p : X × (ι → I)) : segmentToRoot G 0 p = p.2 := by
  ext i
  simp [segmentToRoot]

omit [TopologicalSpace X] in
@[simp]
private lemma segmentToRoot_one (p : X × (ι → I)) :
    segmentToRoot G 1 p = cubeDiagonalRoot G p.1 := by
  ext i
  simp [segmentToRoot]

omit [TopologicalSpace X] in
/-- The segment from a diagonal root to itself is constant. -/
@[simp]
private lemma segmentToRoot_cubeDiagonalRoot (s : I) (x : X) :
    segmentToRoot G s (x, cubeDiagonalRoot G x) = cubeDiagonalRoot G x := by
  ext i
  simp [segmentToRoot, Icc.convexComb_eq]

private lemma continuous_segmentToRoot (hd : Continuous (cubeDiagonalRoot G)) :
    Continuous fun q : I × (X × (ι → I)) ↦ segmentToRoot G q.1 q.2 := by
  refine continuous_pi fun i ↦ continuous_induced_rng.2 ?_
  simp only [comp_def, segmentToRoot, Icc.coe_convexComb]
  fun_prop

/-- **The deformation of the zero level set onto the diagonal roots.** At time `s` it sends
`(x, u)` to `(x, cubeLevelPoint G x ((1 - s) u + s t(x) · 1))`. It starts at the identity, ends at
`(x, u) ↦ (x, t(x) · 1)`, preserves `x` (`TauCeti.cubeLevelSetHomotopy_apply_fst`) and fixes the
graph of the diagonal root at all times. Its second coordinate is
`TauCeti.cubeLevelSetHomotopy_apply_snd`. -/
def cubeLevelSetHomotopy :
    ContinuousMap.HomotopyRel (ContinuousMap.id (cubeLevelSet G))
      ((cubeLevelSetSection hG hmono h₀ h₁).comp (cubeLevelSetProj G))
      (range (cubeLevelSetSection hG hmono h₀ h₁)) where
  toFun q := ⟨(q.2.val.1, cubeLevelPoint G q.2.val.1 (segmentToRoot G q.1 q.2.val)),
    apply_cubeLevelPoint_eq_zero (hG.uncurry_left _) (h₀ _) (h₁ _) _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _
    exact (continuous_cubeLevelPoint hG hmono h₀ h₁).comp
      ((by fun_prop : Continuous fun q : I × cubeLevelSet G ↦ q.2.val.1).prodMk
        ((continuous_segmentToRoot (continuous_cubeDiagonalRoot hG hmono h₀ h₁)).comp
          (by fun_prop : Continuous fun q : I × cubeLevelSet G ↦ (q.1, (q.2 : X × (ι → I))))))
  map_zero_left p := by
    refine Subtype.ext (Prod.ext rfl ?_)
    simpa using cubeLevelPoint_eq_self (hmono _) p.property
  map_one_left p := by
    refine Subtype.ext (Prod.ext rfl ?_)
    simpa using cubeLevelPoint_cubeDiagonalRoot (hG.uncurry_left _) (hmono _) (h₀ _) (h₁ _)
  prop' s := by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext (Prod.ext rfl ?_)
    simpa using cubeLevelPoint_cubeDiagonalRoot (hG.uncurry_left _) (hmono _) (h₀ _) (h₁ _)

/-- The deformation of the zero level set preserves the parameter `x`. -/
@[simp]
theorem cubeLevelSetHomotopy_apply_fst (s : I) (p : cubeLevelSet G) :
    (cubeLevelSetHomotopy hG hmono h₀ h₁ (s, p) : X × (ι → I)).1 = p.val.1 :=
  (rfl)

/-- The deformation of the zero level set at time `s` sends `(x, u)` to the level point of the
point `(1 - s) u + s t(x) · 1` of the segment from `u` to the diagonal root. -/
@[simp]
theorem cubeLevelSetHomotopy_apply_snd (s : I) (p : cubeLevelSet G) :
    (cubeLevelSetHomotopy hG hmono h₀ h₁ (s, p) : X × (ι → I)).2 =
      cubeLevelPoint G p.val.1 fun i ↦
        Icc.convexComb (p.val.2 i) (cubeDiagonalRoot G p.val.1 i) s :=
  (rfl)

/-- **The zero level set is fibre homotopy equivalent to the parameter space** over `X`: the
projection `(x, u) ↦ x` and the section through the diagonal roots are inverse fibre homotopy
equivalences, by the fibrewise deformation onto the diagonal roots
(`TauCeti.cubeLevelSetHomotopy`). -/
def cubeLevelSetFiberHomotopyEquiv :
    FiberHomotopyEquiv (cubeLevelSetProj G) (ContinuousMap.id X) where
  toFun := cubeLevelSetProj G
  invFun := cubeLevelSetSection hG hmono h₀ h₁
  comp_toFun := rfl
  comp_invFun := rfl
  left_inv := ⟨{ (cubeLevelSetHomotopy hG hmono h₀ h₁).toHomotopy.symm with
    prop' t := ContinuousMap.ext fun p ↦ by
      -- `prop'` states the time-`t` map as an anonymous `ContinuousMap`; rewrite it to the
      -- reversed homotopy at time `σ t` and apply `cubeLevelSetHomotopy_apply_fst`.
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
        ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.symm_apply,
        ContinuousMap.HomotopyWith.coe_toHomotopy, cubeLevelSetProj_apply,
        cubeLevelSetHomotopy_apply_fst] }⟩
  right_inv := .refl _ rfl

@[simp]
lemma cubeLevelSetFiberHomotopyEquiv_toFun :
    (cubeLevelSetFiberHomotopyEquiv hG hmono h₀ h₁).toFun = cubeLevelSetProj G :=
  (rfl)

@[simp]
lemma cubeLevelSetFiberHomotopyEquiv_invFun :
    (cubeLevelSetFiberHomotopyEquiv hG hmono h₀ h₁).invFun = cubeLevelSetSection hG hmono h₀ h₁ :=
  (rfl)

/-- **The zero level set is homotopy equivalent to the parameter space**: the section through
the diagonal roots is a homotopy equivalence `X ≃ₕ cubeLevelSet G`, with homotopy inverse the
projection. -/
def cubeLevelSetHomotopyEquiv : X ≃ₕ cubeLevelSet G :=
  (cubeLevelSetFiberHomotopyEquiv hG hmono h₀ h₁).symm.toHomotopyEquiv

@[simp]
lemma cubeLevelSetHomotopyEquiv_toFun :
    (cubeLevelSetHomotopyEquiv hG hmono h₀ h₁).toFun = cubeLevelSetSection hG hmono h₀ h₁ :=
  ContinuousMap.ext fun x ↦
    ((cubeLevelSetFiberHomotopyEquiv hG hmono h₀ h₁).symm.toHomotopyEquiv_apply x).trans <| by
      rw [FiberHomotopyEquiv.symm_toFun, cubeLevelSetFiberHomotopyEquiv_invFun]

@[simp]
lemma cubeLevelSetHomotopyEquiv_invFun :
    (cubeLevelSetHomotopyEquiv hG hmono h₀ h₁).invFun = cubeLevelSetProj G :=
  ContinuousMap.ext fun p ↦
    ((cubeLevelSetFiberHomotopyEquiv hG hmono h₀ h₁).symm.toHomotopyEquiv_symm_apply p).trans <| by
      rw [FiberHomotopyEquiv.symm_invFun, cubeLevelSetFiberHomotopyEquiv_toFun]

end Cube

end TauCeti
