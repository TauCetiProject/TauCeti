/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
public import TauCeti.Combinatorics.Hive.Octahedron.Lattice
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Abel

/-!
# Associator hive-face embeddings and section gluing

The four boundary faces of the associator region `Aₙ` in `Lₙ` carry two glued input hives on the
lower section `S` and two glued output hives on the upper section `S'`. This file defines the four
explicit coordinate embeddings from `Vertex n` into `SpaceTimePoint n`, proves their shared-edge
matching identities, constructs the section gluing maps `glueInput` and `glueOutput` together with
the normalized output face projections `readOutputLeft` (subtracting `|λ| = F(n, 0)`) and
`readOutputRight`, and proves that wall agreement between `S` and `S'` preserves all four exterior
boundaries.

## Main definitions

* `TauCeti.Hive.Octahedron.embedInputLeft`, `TauCeti.Hive.Octahedron.embedInputRight`,
  `TauCeti.Hive.Octahedron.embedOutputLeft`, `TauCeti.Hive.Octahedron.embedOutputRight`:
  the four hive-face embeddings `Vertex n → SpaceTimePoint n`.
* `TauCeti.Hive.Octahedron.glueInput`, `TauCeti.Hive.Octahedron.inputHivePairEquiv`:
  gluing two functions or matching hives onto `S` with no extra cross-diagonal rhombus constraints.
* `TauCeti.Hive.Octahedron.readOutputLeft`, `TauCeti.Hive.Octahedron.readOutputRight`,
  `TauCeti.Hive.Octahedron.glueOutput`, `TauCeti.Hive.Octahedron.outputHivePairEquiv`:
  reading normalized output faces from `S'` and inverse gluing adding `|λ|` back to the first
  output face.

## Main results

* `TauCeti.Hive.Octahedron.shared_input_edge_eq`, `TauCeti.Hive.Octahedron.shared_output_edge_eq`:
  hives with matching shared boundaries agree along the diagonal `x = y` of `S` and (up to the
  `A`-corner shift `|λ|`) along the anti-diagonal `x + y = n` of `S'`.
* `TauCeti.Hive.Octahedron.inputHivePairEquiv`, `TauCeti.Hive.Octahedron.outputHivePairEquiv`:
  equivalences between pairs of normalized hives with matching shared boundary and functions on
  `S` / `S'` vanishing at `(0, 0)` whose two face pullbacks are rhombus-concave.
* `TauCeti.Hive.Octahedron.boundary_readOutput_of_eq_on_wall`: wall agreement transfers input
  exterior boundaries `(λ, μ, ν, π*)` to the two output faces `(μ, ν, τ*)` and `(λ, τ, π*)`.

## References

* A. Henriques and J. Kamnitzer, *The octahedron recurrence and $\mathfrak{gl}_n$ crystals*,
  Adv. Math. **206** (2006), 211–249, §3.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive.Octahedron

/-! ### Four associator hive-face embeddings -/

section FaceEmbeddings

variable {n : ℕ}

/-- Embed the first input hive face `(λ, μ, σ*)` onto `{y ≤ x} ⊆ S` by `(x, y, z) ↦ (n - x, z, y)`.
-/
def embedInputLeft (p : Vertex n) : SpaceTimePoint n where
  x := ⟨n - p.x, by omega⟩
  y := ⟨p.z, by have := p.sum_eq; omega⟩
  t := p.y
  even_sum := ⟨p.y + p.z, by dsimp only; have := p.sum_eq; omega⟩

/-- Embed the second input hive face `(σ, ν, π*)` onto `{x ≤ y} ⊆ S` by `(x, y, z) ↦ (y, n - x, z)`.
-/
def embedInputRight (p : Vertex n) : SpaceTimePoint n where
  x := ⟨p.y, by have := p.sum_eq; omega⟩
  y := ⟨n - p.x, by omega⟩
  t := p.z
  even_sum := ⟨p.y + p.z, by dsimp only; have := p.sum_eq; omega⟩

/-- Embed the first output hive face `(μ, ν, τ*)` onto `{n ≤ x + y} ⊆ S'` by
`(x, y, z) ↦ (n - z, n - x, n - y)`. -/
def embedOutputLeft (p : Vertex n) : SpaceTimePoint n where
  x := ⟨n - p.z, by omega⟩
  y := ⟨n - p.x, by omega⟩
  t := (n : ℤ) - p.y
  even_sum := ⟨n, by dsimp only; have := p.sum_eq; omega⟩

/-- Embed the second output hive face `(λ, τ, π*)` onto `{x + y ≤ n} ⊆ S'` by
`(x, y, z) ↦ (y, z, n - x)`. -/
def embedOutputRight (p : Vertex n) : SpaceTimePoint n where
  x := ⟨p.y, by have := p.sum_eq; omega⟩
  y := ⟨p.z, by have := p.sum_eq; omega⟩
  t := (n : ℤ) - p.x
  even_sum := ⟨p.y + p.z, by dsimp only; have := p.sum_eq; omega⟩

@[simp] theorem embedInputLeft_x_val (p : Vertex n) : (embedInputLeft p).x.val = n - p.x := by
  unfold embedInputLeft; rfl
@[simp] theorem embedInputLeft_y_val (p : Vertex n) : (embedInputLeft p).y.val = p.z := by
  unfold embedInputLeft; rfl
@[simp] theorem embedInputLeft_t (p : Vertex n) : (embedInputLeft p).t = p.y := by
  unfold embedInputLeft; rfl

@[simp] theorem embedInputRight_x_val (p : Vertex n) : (embedInputRight p).x.val = p.y := by
  unfold embedInputRight; rfl
@[simp] theorem embedInputRight_y_val (p : Vertex n) : (embedInputRight p).y.val = n - p.x := by
  unfold embedInputRight; rfl
@[simp] theorem embedInputRight_t (p : Vertex n) : (embedInputRight p).t = p.z := by
  unfold embedInputRight; rfl

@[simp] theorem embedOutputLeft_x_val (p : Vertex n) : (embedOutputLeft p).x.val = n - p.z := by
  unfold embedOutputLeft; rfl
@[simp] theorem embedOutputLeft_y_val (p : Vertex n) : (embedOutputLeft p).y.val = n - p.x := by
  unfold embedOutputLeft; rfl
@[simp] theorem embedOutputLeft_t (p : Vertex n) : (embedOutputLeft p).t = (n : ℤ) - p.y := by
  unfold embedOutputLeft; rfl

@[simp] theorem embedOutputRight_x_val (p : Vertex n) : (embedOutputRight p).x.val = p.y := by
  unfold embedOutputRight; rfl
@[simp] theorem embedOutputRight_y_val (p : Vertex n) : (embedOutputRight p).y.val = p.z := by
  unfold embedOutputRight; rfl
@[simp] theorem embedOutputRight_t (p : Vertex n) : (embedOutputRight p).t = (n : ℤ) - p.x := by
  unfold embedOutputRight; rfl

theorem embedInputLeft_on_lowerSection (p : Vertex n) :
    lowerSection n (embedInputLeft p).x (embedInputLeft p).y = (embedInputLeft p).t := by
  have := p.sum_eq
  simp only [lowerSection_apply, embedInputLeft_x_val, embedInputLeft_y_val, embedInputLeft_t,
    Int.abs_eq_natAbs]; omega

theorem embedInputRight_on_lowerSection (p : Vertex n) :
    lowerSection n (embedInputRight p).x (embedInputRight p).y = (embedInputRight p).t := by
  have := p.sum_eq
  simp only [lowerSection_apply, embedInputRight_x_val, embedInputRight_y_val, embedInputRight_t,
    Int.abs_eq_natAbs]; omega

theorem embedOutputLeft_on_upperSection (p : Vertex n) :
    upperSection n (embedOutputLeft p).x (embedOutputLeft p).y = (embedOutputLeft p).t := by
  have := p.sum_eq
  simp only [upperSection_apply, embedOutputLeft_x_val, embedOutputLeft_y_val, embedOutputLeft_t,
    Int.abs_eq_natAbs]; omega

theorem embedOutputRight_on_upperSection (p : Vertex n) :
    upperSection n (embedOutputRight p).x (embedOutputRight p).y = (embedOutputRight p).t := by
  have := p.sum_eq
  simp only [upperSection_apply, embedOutputRight_x_val, embedOutputRight_y_val, embedOutputRight_t,
    Int.abs_eq_natAbs]; omega

theorem embedInputLeft_isAssociator (p : Vertex n) : (embedInputLeft p).IsAssociator := by
  rw [isAssociator_iff_between]
  exact ⟨(embedInputLeft_on_lowerSection p).le,
    (embedInputLeft_on_lowerSection p).symm.le.trans (lowerSection_le_upperSection n _ _)⟩

theorem embedInputRight_isAssociator (p : Vertex n) : (embedInputRight p).IsAssociator := by
  rw [isAssociator_iff_between]
  exact ⟨(embedInputRight_on_lowerSection p).le,
    (embedInputRight_on_lowerSection p).symm.le.trans (lowerSection_le_upperSection n _ _)⟩

theorem embedOutputLeft_isAssociator (p : Vertex n) : (embedOutputLeft p).IsAssociator := by
  rw [isAssociator_iff_between]
  exact ⟨(lowerSection_le_upperSection n _ _).trans (embedOutputLeft_on_upperSection p).le,
    (embedOutputLeft_on_upperSection p).symm.le⟩

theorem embedOutputRight_isAssociator (p : Vertex n) : (embedOutputRight p).IsAssociator := by
  rw [isAssociator_iff_between]
  exact ⟨(lowerSection_le_upperSection n _ _).trans (embedOutputRight_on_upperSection p).le,
    (embedOutputRight_on_upperSection p).symm.le⟩

theorem embedInputLeft_injective : Function.Injective (embedInputLeft (n := n)) := fun p q h => by
  have hx := congrArg (fun r => r.x.val) h
  have hy := congrArg (fun r => r.y.val) h
  have ht := congrArg SpaceTimePoint.t h
  have := p.sum_eq; have := q.sum_eq
  simp at hx hy ht; ext <;> omega

theorem embedInputRight_injective : Function.Injective (embedInputRight (n := n)) := fun p q h => by
  have hx := congrArg (fun r => r.x.val) h
  have hy := congrArg (fun r => r.y.val) h
  have ht := congrArg SpaceTimePoint.t h
  have := p.sum_eq; have := q.sum_eq
  simp at hx hy ht; ext <;> omega

theorem embedOutputLeft_injective : Function.Injective (embedOutputLeft (n := n)) := fun p q h => by
  have hx := congrArg (fun r => r.x.val) h
  have hy := congrArg (fun r => r.y.val) h
  have ht := congrArg SpaceTimePoint.t h
  have := p.sum_eq; have := q.sum_eq
  simp at hx hy ht; ext <;> omega

theorem embedOutputRight_injective : Function.Injective (embedOutputRight (n := n)) :=
  fun p q h => by
    have hx := congrArg (fun r => r.x.val) h
    have hy := congrArg (fun r => r.y.val) h
    have ht := congrArg SpaceTimePoint.t h
    have := p.sum_eq; have := q.sum_eq
    simp at hx hy ht; ext <;> omega

/-- Along the shared diagonal `x = y` (`t = 0`), the `C → A` edge of the first input face reversed
matches the `A → B` edge of the second input face (`A` matched with `A` and `C` matched with `B`).
-/
theorem embedInputLeft_edgePoint_two_rev (k : Fin (n + 1)) :
    embedInputLeft (Vertex.edgePoint n 2 k.rev) = (lowerSection n).point k k := by
  have := k.isLt
  ext
  · simp [Fin.val_rev]; omega
  · simp [Fin.val_rev]; omega
  · simp

theorem embedInputRight_edgePoint_zero (k : Fin (n + 1)) :
    embedInputRight (Vertex.edgePoint n 0 k) = (lowerSection n).point k k := by
  have := k.isLt
  ext
  · simp
  · simp; omega
  · simp

/-- Along the shared anti-diagonal `x + y = n` (`t = n`), the `C → A` edge of the first output face
reversed matches the `B → C` edge of the second output face. -/
theorem embedOutputLeft_edgePoint_two_rev (k : Fin (n + 1)) :
    embedOutputLeft (Vertex.edgePoint n 2 k.rev) = (upperSection n).point k.rev k := by
  have := k.isLt
  ext
  · simp [Fin.val_rev]; omega
  · simp [Fin.val_rev]; omega
  · simp only [Fin.isValue, embedOutputLeft_t, Vertex.edgePoint_two_y, CharP.cast_eq_zero,
      sub_zero, Section.point_t, upperSection_apply, Fin.val_rev, Nat.reduceSubDiff,
      Int.abs_eq_natAbs]
    omega

theorem embedOutputRight_edgePoint_one (k : Fin (n + 1)) :
    embedOutputRight (Vertex.edgePoint n 1 k) = (upperSection n).point k.rev k := by
  have := k.isLt
  ext
  · simp [Fin.val_rev]
  · simp
  · simp only [Fin.isValue, embedOutputRight_t, Vertex.edgePoint_one_x, CharP.cast_eq_zero,
      sub_zero, Section.point_t, upperSection_apply, Fin.val_rev, Nat.reduceSubDiff,
      Int.abs_eq_natAbs]
    omega

@[simp] theorem embedInputLeft_cornerA_x : (embedInputLeft (Vertex.cornerA n)).x = 0 := by
  ext; simp
@[simp] theorem embedInputLeft_cornerA_y : (embedInputLeft (Vertex.cornerA n)).y = 0 := by
  ext; simp
@[simp] theorem embedInputRight_cornerA_x : (embedInputRight (Vertex.cornerA n)).x = 0 := by
  ext; simp
@[simp] theorem embedInputRight_cornerA_y : (embedInputRight (Vertex.cornerA n)).y = 0 := by
  ext; simp

end FaceEmbeddings

/-! ### Section gluing and normalized face extraction -/

section GluingBasic

variable {n : ℕ} {R : Type*}

/-- Glue two functions on `Δₙ` onto the lower section `S` along the diagonal `x = y`. -/
def glueInput (f₁ f₂ : Vertex n → R) (x y : Fin (n + 1)) : R :=
  if h : y.val ≤ x.val then f₁ ⟨n - x.val, x.val - y.val, y.val, by have := x.isLt; omega⟩
  else f₂ ⟨n - y.val, x.val, y.val - x.val, by have := y.isLt; omega⟩

theorem glueInput_of_le (f₁ f₂ : Vertex n → R) {x y : Fin (n + 1)} (h : y.val ≤ x.val) :
    glueInput f₁ f₂ x y = f₁ ⟨n - x.val, x.val - y.val, y.val, by have := x.isLt; omega⟩ := by
  unfold glueInput; exact dite_eq_left_of_eq_true (eq_true h)

theorem glueInput_of_gt (f₁ f₂ : Vertex n → R) {x y : Fin (n + 1)} (h : ¬ y.val ≤ x.val) :
    glueInput f₁ f₂ x y = f₂ ⟨n - y.val, x.val, y.val - x.val, by have := y.isLt; omega⟩ := by
  unfold glueInput; exact dite_eq_right_of_eq_false (eq_false h)

@[simp] theorem glueInput_embedInputLeft (f₁ f₂ : Vertex n → R) (p : Vertex n) :
    glueInput f₁ f₂ (embedInputLeft p).x (embedInputLeft p).y = f₁ p := by
  have hp := p.sum_eq
  rw [glueInput_of_le f₁ f₂ (by simp; omega)]
  congr 1; ext
  · simp; omega
  · simp; omega
  · simp

theorem glueInput_embedInputRight {f₁ f₂ : Vertex n → R}
    (hmatch : ∀ k : Fin (n + 1), f₁ (Vertex.edgePoint n 2 k.rev) = f₂ (Vertex.edgePoint n 0 k))
    (p : Vertex n) :
    glueInput f₁ f₂ (embedInputRight p).x (embedInputRight p).y = f₂ p := by
  have hp := p.sum_eq
  by_cases hle : (embedInputRight p).y.val ≤ (embedInputRight p).x.val
  · rw [glueInput_of_le f₁ f₂ hle]
    have hz : p.z = 0 := by simp at hle; omega
    have hxy : p.x = n - p.y := by omega
    convert hmatch ⟨p.y, by omega⟩ using 1
    · congr 1; ext
      · simp [Fin.val_rev]
      · simp; omega
      · simp; omega
    · congr 1; ext <;> simp [hz, hxy]
  · rw [glueInput_of_gt f₁ f₂ hle]
    congr 1; ext
    · simp; omega
    · simp
    · simp; omega

@[simp] theorem glueInput_zero_zero (f₁ f₂ : Vertex n → R) :
    glueInput f₁ f₂ 0 0 = f₁ (Vertex.cornerA n) := by
  simpa using glueInput_embedInputLeft f₁ f₂ (Vertex.cornerA n)

@[simp] theorem glueInput_last_zero (f₁ f₂ : Vertex n → R) :
    glueInput f₁ f₂ (Fin.last n) 0 = f₁ (Vertex.edgePoint n 0 (Fin.last n)) := by
  have hx : (embedInputLeft (Vertex.edgePoint n 0 (Fin.last n))).x = Fin.last n := by ext; simp
  have hy : (embedInputLeft (Vertex.edgePoint n 0 (Fin.last n))).y = 0 := by ext; simp
  simpa [hx, hy] using glueInput_embedInputLeft f₁ f₂ (Vertex.edgePoint n 0 (Fin.last n))

/-- Read the second output face `(λ, τ, π*)` from a function on `S'` without a constant shift. -/
def readOutputRight (F : Fin (n + 1) → Fin (n + 1) → R) (p : Vertex n) : R :=
  F (embedOutputRight p).x (embedOutputRight p).y

theorem readOutputRight_apply (F : Fin (n + 1) → Fin (n + 1) → R) (p : Vertex n) :
    readOutputRight F p = F (embedOutputRight p).x (embedOutputRight p).y := by
  unfold readOutputRight; rfl

@[simp] theorem readOutputRight_cornerA (F : Fin (n + 1) → Fin (n + 1) → R) :
    readOutputRight F (Vertex.cornerA n) = F 0 0 := by
  have hx : (embedOutputRight (Vertex.cornerA n)).x = 0 := by ext; simp
  have hy : (embedOutputRight (Vertex.cornerA n)).y = 0 := by ext; simp
  rw [readOutputRight_apply, hx, hy]

end GluingBasic

section GluingGroup

variable {n : ℕ} {R : Type*} [AddCommGroup R]

/-- Two hives whose shared boundary satisfies `h₁.boundary 2 i = -h₂.boundary 0 i.rev` agree
identically along the matched edge (`A, C` of `h₁` matched with `A, B` of `h₂`, both vanishing at
`A`). -/
theorem shared_input_edge_eq [PartialOrder R] {h₁ h₂ : Hive n R}
    (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev) (k : Fin (n + 1)) :
    h₁ (Vertex.edgePoint n 2 k.rev) = h₂ (Vertex.edgePoint n 0 k) := by
  rw [h₁.apply_edgePoint_two, h₂.apply_edgePoint_zero]
  have hrev : (∑ i : Fin n with k.rev.val ≤ i.val, h₁.boundary 2 i) =
      -∑ j : Fin n with j.val < k.val, h₂.boundary 0 j := by
    simp only [hb, Finset.sum_neg_distrib, neg_inj, Finset.sum_filter]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans
      (Equiv.sum_comp Fin.revPerm fun j : Fin n => if j.val < k.val then h₂.boundary 0 j else 0)
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have := i.isLt; have := k.isLt
    by_cases hi : n - k.val ≤ i.val
    · have hi' : n - (i.val + 1) < k.val := by omega
      simp [hi, hi']
    · have hi' : ¬ n - (i.val + 1) < k.val := by omega
      simp [hi, hi']
  rw [hrev, neg_neg]

theorem shared_input_edge_eq_of_productBoundary {lam μ σ ν π : DominantWeight n}
    {h₁ h₂ : IntegerHive n} (hb₁ : h₁.boundary = productBoundary lam μ σ)
    (hb₂ : h₂.boundary = productBoundary σ ν π) (k : Fin (n + 1)) :
    h₁ (Vertex.edgePoint n 2 k.rev) = h₂ (Vertex.edgePoint n 0 k) :=
  shared_input_edge_eq (fun i => by simp [hb₁, hb₂]) k

/-- Equivalence between pairs of normalized hives with matching shared boundary and functions on the
lower section `S` vanishing at `(0, 0)` whose two face pullbacks are rhombus-concave; no extra
rhombus inequality is imposed across the shared diagonal. -/
def inputHivePairEquiv [PartialOrder R] :
    {h : Hive n R × Hive n R // ∀ i : Fin n, h.1.boundary 2 i = -h.2.boundary 0 i.rev} ≃
      {F : Fin (n + 1) → Fin (n + 1) → R // F 0 0 = 0 ∧
        IsRhombusConcave (fun p => F (embedInputLeft p).x (embedInputLeft p).y) ∧
        IsRhombusConcave (fun p => F (embedInputRight p).x (embedInputRight p).y)} where
  toFun h := ⟨glueInput h.1.1 h.1.2, by simp,
    by simpa [glueInput_embedInputLeft] using h.1.1.isRhombusConcave,
    by
      have hm := shared_input_edge_eq h.2
      simpa [glueInput_embedInputRight hm] using h.1.2.isRhombusConcave⟩
  invFun F :=
    let h₁ : Hive n R := ⟨fun p => F.1 (embedInputLeft p).x (embedInputLeft p).y,
      by simp [F.2.1], fun hr => (Hive.isRhombusConcave_def _).mp F.2.2.1 hr⟩
    let h₂ : Hive n R := ⟨fun p => F.1 (embedInputRight p).x (embedInputRight p).y,
      by simp [F.2.1], fun hr => (Hive.isRhombusConcave_def _).mp F.2.2.2 hr⟩
    ⟨(h₁, h₂), fun i => by
      simp only [Hive.boundary_apply, Hive.mk_apply, h₁, h₂]
      have h13 := (embedInputLeft_edgePoint_two_rev (n := n) i.rev.castSucc).trans
        (embedInputRight_edgePoint_zero (n := n) i.rev.castSucc).symm
      have h24 := (embedInputLeft_edgePoint_two_rev (n := n) i.rev.succ).trans
        (embedInputRight_edgePoint_zero (n := n) i.rev.succ).symm
      rw [Fin.rev_castSucc, Fin.rev_rev] at h13
      rw [Fin.rev_succ, Fin.rev_rev] at h24
      rw [congrArg SpaceTimePoint.x h13, congrArg SpaceTimePoint.y h13,
        congrArg SpaceTimePoint.x h24, congrArg SpaceTimePoint.y h24]
      abel⟩
  left_inv h := by
    apply Subtype.ext; apply Prod.ext
    · ext p; exact glueInput_embedInputLeft _ _ p
    · ext p; exact glueInput_embedInputRight (shared_input_edge_eq h.2) p
  right_inv F := by
    apply Subtype.ext; funext x y; dsimp only
    by_cases hle : y.val ≤ x.val
    · rw [glueInput_of_le _ _ hle, Hive.mk_apply]
      set p : Vertex n := ⟨n - x.val, x.val - y.val, y.val, by have := x.isLt; omega⟩
      have hx : (embedInputLeft p).x = x := by ext; simp [p]; have := x.isLt; omega
      have hy : (embedInputLeft p).y = y := by ext; simp [p]
      rw [hx, hy]
    · rw [glueInput_of_gt _ _ hle, Hive.mk_apply]
      set p : Vertex n := ⟨n - y.val, x.val, y.val - x.val, by have := y.isLt; omega⟩
      have hx : (embedInputRight p).x = x := by ext; simp [p]
      have hy : (embedInputRight p).y = y := by ext; simp [p]; have := y.isLt; omega
      rw [hx, hy]

/-- Read the first output face `(μ, ν, τ*)` from a function on `S'`, subtracting `F(n, 0)` (which
equals `|λ|`) to normalize its `A`-corner `(n, 0, 0) ↦ (n, 0, n)`. -/
def readOutputLeft (F : Fin (n + 1) → Fin (n + 1) → R) (p : Vertex n) : R :=
  F (embedOutputLeft p).x (embedOutputLeft p).y - F (Fin.last n) 0

theorem readOutputLeft_apply (F : Fin (n + 1) → Fin (n + 1) → R) (p : Vertex n) :
    readOutputLeft F p = F (embedOutputLeft p).x (embedOutputLeft p).y - F (Fin.last n) 0 := by
  unfold readOutputLeft; rfl

@[simp] theorem readOutputLeft_cornerA (F : Fin (n + 1) → Fin (n + 1) → R) :
    readOutputLeft F (Vertex.cornerA n) = 0 := by
  have hx : (embedOutputLeft (Vertex.cornerA n)).x = Fin.last n := by ext; simp
  have hy : (embedOutputLeft (Vertex.cornerA n)).y = 0 := by ext; simp
  rw [readOutputLeft_apply, hx, hy, sub_self]

/-- Inverse gluing onto the upper section `S'`: add `|λ| = g₂(B)` back to the first output face
before gluing with `g₂` along `x + y = n`. -/
def glueOutput (g₁ g₂ : Vertex n → R) (x y : Fin (n + 1)) : R :=
  if h : x.val + y.val ≤ n then g₂ ⟨n - x.val - y.val, x.val, y.val, by omega⟩
  else g₂ (Vertex.edgePoint n 0 (Fin.last n)) +
    g₁ ⟨n - y.val, x.val + y.val - n, n - x.val, by have := x.isLt; have := y.isLt; omega⟩

theorem glueOutput_of_le (g₁ g₂ : Vertex n → R) {x y : Fin (n + 1)} (h : x.val + y.val ≤ n) :
    glueOutput g₁ g₂ x y = g₂ ⟨n - x.val - y.val, x.val, y.val, by omega⟩ := by
  unfold glueOutput; exact dite_eq_left_of_eq_true (eq_true h)

theorem glueOutput_of_gt (g₁ g₂ : Vertex n → R) {x y : Fin (n + 1)} (h : ¬ x.val + y.val ≤ n) :
    glueOutput g₁ g₂ x y = g₂ (Vertex.edgePoint n 0 (Fin.last n)) +
      g₁ ⟨n - y.val, x.val + y.val - n, n - x.val, by have := x.isLt; have := y.isLt; omega⟩ := by
  unfold glueOutput; exact dite_eq_right_of_eq_false (eq_false h)

@[simp] theorem readOutputRight_glueOutput (g₁ g₂ : Vertex n → R) (p : Vertex n) :
    readOutputRight (glueOutput g₁ g₂) p = g₂ p := by
  have hp := p.sum_eq
  rw [readOutputRight_apply, glueOutput_of_le g₁ g₂ (by simp; omega)]
  congr 1; ext
  · simp; omega
  · simp
  · simp

theorem readOutputLeft_glueOutput {g₁ g₂ : Vertex n → R}
    (hmatch : ∀ k : Fin (n + 1),
      g₂ (Vertex.edgePoint n 0 (Fin.last n)) + g₁ (Vertex.edgePoint n 2 k.rev) =
        g₂ (Vertex.edgePoint n 1 k))
    (p : Vertex n) :
    readOutputLeft (glueOutput g₁ g₂) p = g₁ p := by
  have hp := p.sum_eq
  have hlast : glueOutput g₁ g₂ (Fin.last n) 0 = g₂ (Vertex.edgePoint n 0 (Fin.last n)) := by
    rw [glueOutput_of_le g₁ g₂ (by simp)]
    congr 1; ext <;> simp
  rw [readOutputLeft_apply, hlast]
  by_cases hle : (embedOutputLeft p).x.val + (embedOutputLeft p).y.val ≤ n
  · rw [glueOutput_of_le g₁ g₂ hle]
    have hy : p.y = 0 := by simp at hle; omega
    have hxz : p.x = n - p.z := by omega
    have hm := hmatch ⟨p.z, by omega⟩
    have hp1 : (⟨n - (embedOutputLeft p).x.val - (embedOutputLeft p).y.val,
        (embedOutputLeft p).x.val, (embedOutputLeft p).y.val, by omega⟩ : Vertex n) =
        Vertex.edgePoint n 1 ⟨p.z, by omega⟩ := by
      ext
      · simp; omega
      · simp
      · simp; omega
    have hp2 : Vertex.edgePoint n 2 (⟨p.z, by omega⟩ : Fin (n + 1)).rev = p := by
      ext
      · simp [Fin.val_rev, hxz]
      · simp [hy]
      · simp [Fin.val_rev]; omega
    rw [hp1, ← hm, hp2]; abel
  · rw [glueOutput_of_gt g₁ g₂ hle]
    have hq : (⟨n - (embedOutputLeft p).y.val,
        (embedOutputLeft p).x.val + (embedOutputLeft p).y.val - n,
        n - (embedOutputLeft p).x.val, by
          have := (embedOutputLeft p).x.isLt; have := (embedOutputLeft p).y.isLt; omega⟩ :
        Vertex n) = p := by
      ext
      · simp; omega
      · simp; omega
      · simp; omega
    rw [hq]; abel

theorem glueOutput_readOutput (F : Fin (n + 1) → Fin (n + 1) → R) :
    glueOutput (readOutputLeft F) (readOutputRight F) = F := by
  funext x y
  have hB : readOutputRight F (Vertex.edgePoint n 0 (Fin.last n)) = F (Fin.last n) 0 := by
    have hx : (embedOutputRight (Vertex.edgePoint n 0 (Fin.last n))).x = Fin.last n := by ext; simp
    have hy : (embedOutputRight (Vertex.edgePoint n 0 (Fin.last n))).y = 0 := by ext; simp
    rw [readOutputRight_apply, hx, hy]
  by_cases hle : x.val + y.val ≤ n
  · rw [glueOutput_of_le _ _ hle]
    set p : Vertex n := ⟨n - x.val - y.val, x.val, y.val, by omega⟩
    have hx : (embedOutputRight p).x = x := by ext; simp [p]
    have hy : (embedOutputRight p).y = y := by ext; simp [p]
    rw [readOutputRight_apply, hx, hy]
  · rw [glueOutput_of_gt _ _ hle, hB, readOutputLeft_apply]
    set p : Vertex n := ⟨n - y.val, x.val + y.val - n, n - x.val,
      by have := x.isLt; have := y.isLt; omega⟩
    have hx : (embedOutputLeft p).x = x := by ext; simp [p]; have := x.isLt; omega
    have hy : (embedOutputLeft p).y = y := by ext; simp [p]; have := y.isLt; omega
    rw [hx, hy]; abel

/-- Shared-edge relation between `readOutputLeft F` and `readOutputRight F` for every function `F`
on `S'`: side `2` of `readOutputLeft F` is the dual of side `1` of `readOutputRight F`. -/
theorem boundaryLinear_readOutput_shared (F : Fin (n + 1) → Fin (n + 1) → R) (i : Fin n) :
    Hive.boundaryLinear ℤ n R (readOutputLeft F) 2 i =
      -Hive.boundaryLinear ℤ n R (readOutputRight F) 1 i.rev := by
  simp only [Hive.boundaryLinear_apply, readOutputLeft_apply, readOutputRight_apply]
  have h13 := (embedOutputLeft_edgePoint_two_rev (n := n) i.rev.castSucc).trans
    (embedOutputRight_edgePoint_one (n := n) i.rev.castSucc).symm
  have h24 := (embedOutputLeft_edgePoint_two_rev (n := n) i.rev.succ).trans
    (embedOutputRight_edgePoint_one (n := n) i.rev.succ).symm
  rw [Fin.rev_castSucc, Fin.rev_rev] at h13
  rw [Fin.rev_succ, Fin.rev_rev] at h24
  rw [congrArg SpaceTimePoint.x h13, congrArg SpaceTimePoint.y h13,
    congrArg SpaceTimePoint.x h24, congrArg SpaceTimePoint.y h24]
  abel

/-- Two output hives whose shared boundary satisfies `g₁.boundary 2 i = -g₂.boundary 1 i.rev`
satisfy `g₂(B) + g₁(edgePoint 2 k.rev) = g₂(edgePoint 1 k)` along the anti-diagonal `x + y = n`. -/
theorem shared_output_edge_eq [PartialOrder R] {g₁ g₂ : Hive n R}
    (hb : ∀ i : Fin n, g₁.boundary 2 i = -g₂.boundary 1 i.rev) (k : Fin (n + 1)) :
    g₂ (Vertex.edgePoint n 0 (Fin.last n)) + g₁ (Vertex.edgePoint n 2 k.rev) =
      g₂ (Vertex.edgePoint n 1 k) := by
  rw [g₂.apply_edgePoint_zero, g₁.apply_edgePoint_two, g₂.apply_edgePoint_one]
  have hlast : (∑ i : Fin n with i.val < (Fin.last n).val, g₂.boundary 0 i) =
      ∑ i : Fin n, g₂.boundary 0 i := Finset.sum_congr (by ext i; simp) fun _ _ => rfl
  have hrev : (∑ i : Fin n with k.rev.val ≤ i.val, g₁.boundary 2 i) =
      -∑ j : Fin n with j.val < k.val, g₂.boundary 1 j := by
    simp only [hb, Finset.sum_neg_distrib, neg_inj, Finset.sum_filter]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans
      (Equiv.sum_comp Fin.revPerm fun j : Fin n => if j.val < k.val then g₂.boundary 1 j else 0)
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have := i.isLt; have := k.isLt
    by_cases hi : n - k.val ≤ i.val
    · have hi' : n - (i.val + 1) < k.val := by omega
      simp [hi, hi']
    · have hi' : ¬ n - (i.val + 1) < k.val := by omega
      simp [hi, hi']
  rw [hlast, hrev]; abel

/-- Equivalence between pairs of normalized output hives matching along side `2` of `g₁` and side
`1` of `g₂` and functions on `S'` vanishing at `(0, 0)` whose normalized face pullbacks
`readOutputLeft` and `readOutputRight` are rhombus-concave. -/
def outputHivePairEquiv [PartialOrder R] :
    {g : Hive n R × Hive n R // ∀ i : Fin n, g.1.boundary 2 i = -g.2.boundary 1 i.rev} ≃
      {F : Fin (n + 1) → Fin (n + 1) → R // F 0 0 = 0 ∧
        IsRhombusConcave (readOutputLeft F) ∧
        IsRhombusConcave (readOutputRight F)} where
  toFun g :=
    have hm := shared_output_edge_eq g.2
    ⟨glueOutput g.1.1 g.1.2,
      by
        have h0 : glueOutput g.1.1 g.1.2 0 0 = g.1.2 (Vertex.cornerA n) := by
          rw [glueOutput_of_le _ _ (by simp)]; congr 1; ext <;> simp
        rw [h0, g.1.2.apply_cornerA],
      by
        have heq : readOutputLeft (glueOutput (⇑g.1.1) (⇑g.1.2)) = ⇑g.1.1 :=
          funext (readOutputLeft_glueOutput hm)
        rw [heq]; exact g.1.1.isRhombusConcave,
      by
        have heq : readOutputRight (glueOutput (⇑g.1.1) (⇑g.1.2)) = ⇑g.1.2 :=
          funext (readOutputRight_glueOutput _ _)
        rw [heq]; exact g.1.2.isRhombusConcave⟩
  invFun F :=
    let g₁ : Hive n R := ⟨readOutputLeft F.1, readOutputLeft_cornerA F.1,
      fun hr => (Hive.isRhombusConcave_def _).mp F.2.2.1 hr⟩
    let g₂ : Hive n R := ⟨readOutputRight F.1, (readOutputRight_cornerA F.1).trans F.2.1,
      fun hr => (Hive.isRhombusConcave_def _).mp F.2.2.2 hr⟩
    ⟨(g₁, g₂), fun i => by
      simpa only [g₁, g₂, Hive.boundary_apply, Hive.mk_apply, Hive.boundaryLinear_apply] using
        boundaryLinear_readOutput_shared F.1 i⟩
  left_inv g := by
    apply Subtype.ext; apply Prod.ext
    · ext p; exact readOutputLeft_glueOutput (shared_output_edge_eq g.2) p
    · ext p; exact readOutputRight_glueOutput _ _ p
  right_inv F := Subtype.ext (glueOutput_readOutput F.1)

/-- Whenever `F` on `S'` agrees on the four exterior walls with `glueInput h₁ h₂` (for hives
`h₁, h₂` matching along their shared edge), the four exterior boundaries of `readOutputLeft F` and
`readOutputRight F` equal `(μ, ν)` and `(λ, π*)`, and the shift `F(n, 0)` equals `|λ|`. -/
theorem boundary_readOutput_of_eq_on_wall [PartialOrder R] {h₁ h₂ : Hive n R}
    (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev)
    {F : Fin (n + 1) → Fin (n + 1) → R}
    (hwall : ∀ x y : Fin (n + 1), IsWall x y → F x y = glueInput h₁ h₂ x y) :
    F 0 0 = 0 ∧
      F (Fin.last n) 0 = (∑ i : Fin n, h₁.boundary 0 i) ∧
      Hive.boundaryLinear ℤ n R (readOutputLeft F) 0 = h₁.boundary 1 ∧
      Hive.boundaryLinear ℤ n R (readOutputLeft F) 1 = h₂.boundary 1 ∧
      Hive.boundaryLinear ℤ n R (readOutputRight F) 0 = h₁.boundary 0 ∧
      Hive.boundaryLinear ℤ n R (readOutputRight F) 2 = h₂.boundary 2 := by
  have hm := shared_input_edge_eq hb
  have hF00 : F 0 0 = 0 := by
    rw [hwall 0 0 ((isWall_def _ _).mpr (Or.inl rfl)), glueInput_zero_zero, h₁.apply_cornerA]
  have hFn0 : F (Fin.last n) 0 = ∑ i : Fin n, h₁.boundary 0 i := by
    rw [hwall (Fin.last n) 0 ((isWall_def _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))),
      glueInput_last_zero, h₁.apply_edgePoint_zero]
    exact Finset.sum_congr (by ext i; simp) fun _ _ => rfl
  refine ⟨hF00, hFn0, ?_, ?_, ?_, ?_⟩
  · ext i
    have hpt (k : Fin (n + 1)) :
        F (embedOutputLeft (Vertex.edgePoint n 0 k)).x
          (embedOutputLeft (Vertex.edgePoint n 0 k)).y =
          h₁ (Vertex.edgePoint n 1 k) := by
      rw [hwall _ _ ((isWall_def _ _).mpr (Or.inr (Or.inl (by simp))))]
      have hx : (embedOutputLeft (Vertex.edgePoint n 0 k)).x =
          (embedInputLeft (Vertex.edgePoint n 1 k)).x := by ext; simp
      have hy : (embedOutputLeft (Vertex.edgePoint n 0 k)).y =
          (embedInputLeft (Vertex.edgePoint n 1 k)).y := by
        have := k.isLt; ext; simp; omega
      rw [hx, hy, glueInput_embedInputLeft]
    simp only [Hive.boundaryLinear_apply, readOutputLeft_apply, hpt, Hive.boundary_apply]; abel
  · ext i
    have hpt (k : Fin (n + 1)) :
        F (embedOutputLeft (Vertex.edgePoint n 1 k)).x
          (embedOutputLeft (Vertex.edgePoint n 1 k)).y =
          h₂ (Vertex.edgePoint n 1 k) := by
      rw [hwall _ _ ((isWall_def _ _).mpr (Or.inr (Or.inr (Or.inr (by simp)))))]
      have hx : (embedOutputLeft (Vertex.edgePoint n 1 k)).x =
          (embedInputRight (Vertex.edgePoint n 1 k)).x := by ext; simp
      have hy : (embedOutputLeft (Vertex.edgePoint n 1 k)).y =
          (embedInputRight (Vertex.edgePoint n 1 k)).y := by ext; simp
      rw [hx, hy, glueInput_embedInputRight hm]
    simp only [Hive.boundaryLinear_apply, readOutputLeft_apply, hpt, Hive.boundary_apply]; abel
  · ext i
    have hpt (k : Fin (n + 1)) :
        F (embedOutputRight (Vertex.edgePoint n 0 k)).x
          (embedOutputRight (Vertex.edgePoint n 0 k)).y =
          h₁ (Vertex.edgePoint n 0 k) := by
      rw [hwall _ _ ((isWall_def _ _).mpr (Or.inr (Or.inr (Or.inl (by simp)))))]
      have hx : (embedOutputRight (Vertex.edgePoint n 0 k)).x =
          (embedInputLeft (Vertex.edgePoint n 0 k)).x := by
        have := k.isLt; ext; simp; omega
      have hy : (embedOutputRight (Vertex.edgePoint n 0 k)).y =
          (embedInputLeft (Vertex.edgePoint n 0 k)).y := by ext; simp
      rw [hx, hy, glueInput_embedInputLeft]
    simp only [Hive.boundaryLinear_apply, readOutputRight_apply, hpt, Hive.boundary_apply]
  · ext i
    have hpt (k : Fin (n + 1)) :
        F (embedOutputRight (Vertex.edgePoint n 2 k)).x
          (embedOutputRight (Vertex.edgePoint n 2 k)).y =
          h₂ (Vertex.edgePoint n 2 k) := by
      rw [hwall _ _ ((isWall_def _ _).mpr (Or.inl (by simp)))]
      have hx : (embedOutputRight (Vertex.edgePoint n 2 k)).x =
          (embedInputRight (Vertex.edgePoint n 2 k)).x := by ext; simp
      have hy : (embedOutputRight (Vertex.edgePoint n 2 k)).y =
          (embedInputRight (Vertex.edgePoint n 2 k)).y := by ext; simp
      rw [hx, hy, glueInput_embedInputRight hm]
    simp only [Hive.boundaryLinear_apply, readOutputRight_apply, hpt, Hive.boundary_apply]

end GluingGroup

end TauCeti.Hive.Octahedron
