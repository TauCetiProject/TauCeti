/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.ForkCorner
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
import TauCeti.RepresentationTheory.Quiver.Representation.AsModule

/-!
# Independence of the type-`D` fork words

For the signless preprojective algebra `Π` of the Bourbaki-labelled `Dₙ` diagram, `n ≥ 3`, let
`c = n - 3` be the fork vertex and let `x, y` be its two leaf backtracks. The reduced fork words
`TauCeti.signlessPreprojectiveDForkWords` span the fork corner `e_c Π e_c`. They are the unit,
the words `x (x + y)^(t - 1)` and `y (x + y)^(t - 1)` for `1 ≤ t ≤ c`, and `x (x + y)^c`. This file
proves that they are linearly independent over every field, characteristic two included. Hence
they form a basis of the fork corner, and `dim e_c Π e_c = 2 n - 4`. These are the fork-corner
coordinates for the Frobenius pairing of the type-`D` preprojective algebra.

Independence is detected by an explicit representation of `Π`. Every vertex carries the ambient
coordinate space `(Bool × ℕ) →₀ k`. For `t > 0`, the coordinate `(true, t)` stands for the
alternating word of `t` leaf backtracks whose leftmost factor is `x`, and `(false, t)` for the one
whose leftmost factor is `y`. The coordinate `(true, 0)` is the empty word. At the arm vertex
`j ≤ c`, the fork-corner words of `D_{j+3}` are encoded in the finite subspace spanned by
`(true, t)` for `t ≤ j + 1` and `(false, t)` for `1 ≤ t ≤ j`. The maps are defined on the whole
ambient space, and the relations are checked there; only these finite subspaces carry the word
interpretation. The longest `y`-word, of length `j + 1`, is minus the longest `x`-word in
`D_{j+3}`, so it gets no coordinate of its own: the maps (through `bWord`) encode it as the vector
`-(true, j + 1)`. This is a choice of encoding, not a relation in the ambient space, where
`(false, j + 1)` and `(true, j + 1)` stay independent coordinates.

The arrow from the fork to a leaf multiplies on the left by `x` or by `y`. The arrow back
projects onto the words with that leftmost factor. Along the arm, the arrow towards the fork
multiplies by `x + y`, and the arrow away from it truncates, with alternating signs. With these
maps the signless relations hold. The fork words send the empty word at the fork to distinct
basis vectors. Multiplication uses later-factor-first order. The construction parallels the grid
representation of
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basis`.

## Main results

* `TauCeti.linearIndependent_signlessPreprojectiveDForkWords`: the reduced fork words are
  linearly independent over every field.
* `TauCeti.signlessPreprojectiveDForkBasis`: the basis of the fork corner by these words.
* `TauCeti.finrank_cornerSubmodule_signlessPreprojective_D_fork`: the fork corner has dimension
  `2 n - 4`.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the local relations.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin Frobenius
  property.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver CategoryTheory

variable (k : Type*) [Field k] {n : ℕ}

attribute [local instance] forkNeighborSetFintype

/-! ### The word operators -/

/-- The ambient coordinate space of the detecting representation. Its basis vectors index
words in the two leaf backtracks; at each arm vertex the fork-corner words are encoded in the
finite subspace described in the module docstring. -/
private abbrev ForkCoord (k : Type*) [Field k] := (Bool × ℕ) →₀ k

/-- The word of length `t` with leftmost factor `y`, at the arm vertex `j`. The longest word
`t = j + 1` is rewritten as minus the word with leftmost factor `x`. -/
private noncomputable def bWord (j t : ℕ) : ForkCoord k :=
  if t ≤ j then Finsupp.single (false, t) 1 else -Finsupp.single (true, t) 1

/-- Left multiplication by `x` on the fork-corner words of length at most `j + 1`. -/
private noncomputable def xStep (j : ℕ) : Module.End k (ForkCoord k) :=
  Finsupp.linearCombination k fun w : Bool × ℕ =>
    if w.2 ≤ j ∧ (w.1 = true ↔ w.2 = 0) then Finsupp.single (true, w.2 + 1) 1 else 0

/-- Left multiplication by `y` on the fork-corner words of length at most `j + 1`. -/
private noncomputable def yStep (j : ℕ) : Module.End k (ForkCoord k) :=
  Finsupp.linearCombination k fun w : Bool × ℕ =>
    if w.1 = true ∧ w.2 ≤ j then bWord k j (w.2 + 1) else 0

/-- Left multiplication by `x + y` on the fork-corner words of length at most `j + 1`. -/
private noncomputable def sStep (j : ℕ) : Module.End k (ForkCoord k) := xStep k j + yStep k j

/-- The projection onto the words with leftmost factor `x`, of length at most `j + 1`. -/
private noncomputable def xProj (j : ℕ) : Module.End k (ForkCoord k) :=
  Finsupp.linearCombination k fun w : Bool × ℕ =>
    if w.1 = true ∧ 1 ≤ w.2 ∧ w.2 ≤ j + 1 then Finsupp.single w 1 else 0

/-- The projection onto the words with leftmost factor `y`, of length at most `j + 1`. -/
private noncomputable def yProj (j : ℕ) : Module.End k (ForkCoord k) :=
  Finsupp.linearCombination k fun w : Bool × ℕ =>
    if w.1 = false ∧ 1 ≤ w.2 ∧ w.2 ≤ j ∨ w = (true, j + 1) then Finsupp.single w 1 else 0

/-- The truncation from the words at the arm vertex `j + 1` to those at the vertex `j`. -/
private noncomputable def truncStep (j : ℕ) : Module.End k (ForkCoord k) :=
  Finsupp.linearCombination k fun w : Bool × ℕ =>
    if w.1 = true ∧ w.2 ≤ j + 1 then Finsupp.single w 1
    else if 1 ≤ w.2 ∧ w.2 ≤ j + 1 then bWord k j w.2 else 0

private theorem forkCoord_ext {f g : Module.End k (ForkCoord k)}
    (h : ∀ l t, f (Finsupp.single (l, t) 1) = g (Finsupp.single (l, t) 1)) : f = g :=
  Finsupp.lhom_ext' fun w => LinearMap.ext_ring (h w.1 w.2)

private theorem sStep_apply (j : ℕ) (x : ForkCoord k) :
    sStep k j x = xStep k j x + yStep k j x := (rfl)

private theorem xStep_single (j : ℕ) (l : Bool) (t : ℕ) :
    xStep k j (Finsupp.single (l, t) 1) =
      if t ≤ j ∧ (l = true ↔ t = 0) then Finsupp.single (true, t + 1) 1 else 0 := by
  simp [xStep]

private theorem yStep_single (j : ℕ) (l : Bool) (t : ℕ) :
    yStep k j (Finsupp.single (l, t) 1) = if l = true ∧ t ≤ j then bWord k j (t + 1) else 0 := by
  simp [yStep]

private theorem xProj_single (j : ℕ) (l : Bool) (t : ℕ) :
    xProj k j (Finsupp.single (l, t) 1) =
      if l = true ∧ 1 ≤ t ∧ t ≤ j + 1 then Finsupp.single (l, t) 1 else 0 := by
  simp [xProj]

private theorem yProj_single (j : ℕ) (l : Bool) (t : ℕ) :
    yProj k j (Finsupp.single (l, t) 1) =
      if l = false ∧ 1 ≤ t ∧ t ≤ j ∨ (l, t) = (true, j + 1) then Finsupp.single (l, t) 1
      else 0 := by
  simp [yProj]

private theorem truncStep_single (j : ℕ) (l : Bool) (t : ℕ) :
    truncStep k j (Finsupp.single (l, t) 1) =
      if l = true ∧ t ≤ j + 1 then Finsupp.single (l, t) 1
      else if 1 ≤ t ∧ t ≤ j + 1 then bWord k j t else 0 := by
  simp [truncStep]

private theorem xProj_comp_xStep (j : ℕ) : xProj k j ∘ₗ xStep k j = xStep k j :=
  forkCoord_ext k fun l t => by
    rw [LinearMap.comp_apply, xStep_single]
    split_ifs with h
    · simp [xProj_single, h.1]
    · rw [map_zero]

private theorem yProj_comp_yStep (j : ℕ) : yProj k j ∘ₗ yStep k j = yStep k j :=
  forkCoord_ext k fun l t => by
    rw [LinearMap.comp_apply, yStep_single]
    split_ifs with h
    · rw [bWord]
      split_ifs with h'
      · simp [yProj_single, h']
      · simp [yProj_single, show t = j by omega]
    · rw [map_zero]

private theorem xStep_comp_xProj (j : ℕ) : xStep k j ∘ₗ xProj k j = 0 :=
  forkCoord_ext k fun l t => by
    rw [LinearMap.comp_apply, xProj_single, LinearMap.zero_apply]
    split_ifs with h
    · simp [xStep_single]; grind
    · rw [map_zero]

private theorem yStep_comp_yProj (j : ℕ) : yStep k j ∘ₗ yProj k j = 0 :=
  forkCoord_ext k fun l t => by
    rw [LinearMap.comp_apply, yProj_single, LinearMap.zero_apply]
    split_ifs with h
    · simp [yStep_single]; grind
    · rw [map_zero]

private theorem sStep_zero : sStep k 0 = 0 :=
  forkCoord_ext k fun l t => by
    rw [sStep, LinearMap.add_apply, xStep_single, yStep_single, LinearMap.zero_apply]
    cases l <;> rcases t with _ | t <;> simp [bWord]

/-- Multiplying by `x + y` after truncating to the vertex `j` is multiplying by `x + y`: the
words killed by the truncation are killed by `x + y`. -/
private theorem sStep_comp_truncStep (j : ℕ) : sStep k (j + 1) ∘ₗ truncStep k j = sStep k (j + 1) :=
  forkCoord_ext k fun l t => by
    rw [LinearMap.comp_apply]
    obtain rfl | ⟨h1, h2⟩ | rfl | h : t = 0 ∨ (1 ≤ t ∧ t ≤ j) ∨ t = j + 1 ∨ j + 2 ≤ t := by omega
    · cases l <;> simp [truncStep_single, sStep, xStep_single, yStep_single, bWord]
    · have h3 : t ≤ j + 1 := by omega
      have h4 : t ≠ 0 := by omega
      cases l
      · simp [truncStep_single, sStep, xStep_single, yStep_single, bWord, h1, h2, h3, h4]
      · simp [truncStep_single, sStep, xStep_single, yStep_single, bWord, h3, h4,
          show t + 1 ≤ j + 1 by omega]
    · cases l <;> simp [truncStep_single, sStep, xStep_single, yStep_single, bWord]
    · cases l <;> simp [truncStep_single, sStep, xStep_single, yStep_single,
        show ¬t ≤ j + 1 by omega]

/-- Truncating after multiplying by `x + y` at the vertex `j + 1` is multiplying by `x + y` at
the vertex `j`. -/
private theorem truncStep_comp_sStep (j : ℕ) : truncStep k j ∘ₗ sStep k (j + 1) = sStep k j :=
  forkCoord_ext k fun l t => by
    rw [LinearMap.comp_apply]
    obtain rfl | ⟨h1, h2⟩ | rfl | h : t = 0 ∨ (1 ≤ t ∧ t ≤ j) ∨ t = j + 1 ∨ j + 2 ≤ t := by omega
    · cases l <;> simp [truncStep_single, sStep, xStep_single, yStep_single, bWord]
    · have h3 : t ≤ j + 1 := by omega
      have h4 : t ≠ 0 := by omega
      have h5 : t + 1 ≤ j + 1 := by omega
      cases l
      · simp [truncStep_single, sStep, xStep_single, yStep_single, h2, h3, h4, h5]
      · simp [truncStep_single, sStep, xStep_single, yStep_single, bWord, h2, h3, h4, h5]
    · cases l <;> simp [truncStep_single, sStep, xStep_single, yStep_single, bWord]
    · cases l <;> simp [sStep, xStep_single, yStep_single, show ¬t ≤ j + 1 by omega,
        show ¬t ≤ j by omega]

/-! ### The detecting representation -/

/-- The adjacency pattern of `Dₙ` with `c = n - 3`, on natural-number labels. -/
private def DAdj (c i j : ℕ) : Prop :=
  i = c ∧ j = c + 1 ∨ i = c + 1 ∧ j = c ∨ i = c ∧ j = c + 2 ∨ i = c + 2 ∧ j = c ∨
    i = j + 1 ∧ i ≤ c ∨ j = i + 1 ∧ j ≤ c

/-- The action of the arrow `i → j` of the doubled `Dₙ` diagram, for `c = n - 3`. -/
private noncomputable def dStep (c i j : ℕ) : Module.End k (ForkCoord k) :=
  if i = c ∧ j = c + 1 then xStep k c
  else if i = c + 1 ∧ j = c then xProj k c
  else if i = c ∧ j = c + 2 then yStep k c
  else if i = c + 2 ∧ j = c then yProj k c
  else if i = j + 1 ∧ i ≤ c then (-1 : k) ^ (c - j) • truncStep k j
  else if j = i + 1 ∧ j ≤ c then sStep k j
  else 0

private theorem dStep_eq_zero {c i j : ℕ} (h : ¬DAdj c i j) : dStep k c i j = 0 := by
  simp only [DAdj, not_or] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  simp only [dStep, h₁, h₂, h₃, h₄, h₅, h₆, ite_false]

private theorem dStep_fork_left (c : ℕ) : dStep k c c (c + 1) = xStep k c := by
  unfold dStep; split_ifs <;> first | rfl | omega

private theorem dStep_left_fork (c : ℕ) : dStep k c (c + 1) c = xProj k c := by
  unfold dStep; split_ifs <;> first | rfl | omega

private theorem dStep_fork_right (c : ℕ) : dStep k c c (c + 2) = yStep k c := by
  unfold dStep; split_ifs <;> first | rfl | omega

private theorem dStep_right_fork (c : ℕ) : dStep k c (c + 2) c = yProj k c := by
  unfold dStep; split_ifs <;> first | rfl | omega

private theorem dStep_down {c j : ℕ} (h : j + 1 ≤ c) :
    dStep k c (j + 1) j = (-1 : k) ^ (c - j) • truncStep k j := by
  unfold dStep; split_ifs <;> first | rfl | omega

private theorem dStep_up {c j : ℕ} (h : j + 1 ≤ c) : dStep k c j (j + 1) = sStep k (j + 1) := by
  unfold dStep; split_ifs <;> first | rfl | omega

/-- The two leaf backtracks at the fork add up to multiplication by `x + y`. -/
private theorem xProj_comp_xStep_add_yProj_comp_yStep (j : ℕ) :
    xProj k j ∘ₗ xStep k j + yProj k j ∘ₗ yStep k j = sStep k j := by
  rw [xProj_comp_xStep, yProj_comp_yStep, sStep]

/-- The backtrack from the arm vertex `j + 1` towards the fork and back. -/
private theorem dStep_up_comp_down {c j : ℕ} (h : j + 1 ≤ c) :
    dStep k c j (j + 1) ∘ₗ dStep k c (j + 1) j = (-1 : k) ^ (c - j) • sStep k (j + 1) := by
  rw [dStep_down k h, dStep_up k h, LinearMap.comp_smul, sStep_comp_truncStep]

/-- The backtrack from the arm vertex `j` away from the fork and back. -/
private theorem dStep_down_comp_up {c j : ℕ} (h : j + 1 ≤ c) :
    dStep k c (j + 1) j ∘ₗ dStep k c j (j + 1) = (-1 : k) ^ (c - j) • sStep k j := by
  rw [dStep_down k h, dStep_up k h, LinearMap.smul_comp, truncStep_comp_sStep]

private theorem sum_range_dStep_eq_sum (c i : ℕ) (S : Finset ℕ) (hS : ∀ j ∈ S, j < c + 3)
    (hout : ∀ j < c + 3, DAdj c i j → j ∈ S) :
    ∑ j ∈ Finset.range (c + 3), dStep k c j i ∘ₗ dStep k c i j =
      ∑ j ∈ S, dStep k c j i ∘ₗ dStep k c i j := by
  refine (Finset.sum_subset (fun j hj => Finset.mem_range.2 (hS j hj)) fun j hj hjS => ?_).symm
  rw [dStep_eq_zero k fun h => hjS (hout j (Finset.mem_range.1 hj) h), LinearMap.comp_zero]

/-- The relation of the signless preprojective algebra holds at every vertex of `Dₙ`. -/
private theorem sum_range_dStep_comp (c i : ℕ) (hi : i < c + 3) :
    ∑ j ∈ Finset.range (c + 3), dStep k c j i ∘ₗ dStep k c i j = 0 := by
  obtain hleaf | hc | hlt : c < i ∨ c = i ∨ i < c := by omega
  · -- At a leaf, only the arrow to the fork contributes.
    rw [sum_range_dStep_eq_sum k c i {c} (by simp) (by
      intro j _ h; unfold DAdj at h; simp only [Finset.mem_singleton]; omega),
      Finset.sum_singleton]
    obtain rfl | rfl : i = c + 1 ∨ i = c + 2 := by omega
    · rw [dStep_fork_left, dStep_left_fork, xStep_comp_xProj]
    · rw [dStep_fork_right, dStep_right_fork, yStep_comp_yProj]
  · -- At the fork, the two leaf backtracks add up to `sStep`, cancelled by the long arm.
    subst hc
    cases c with
    | zero =>
      rw [sum_range_dStep_eq_sum k 0 0 {1, 2} (by simp) (by
        intro j _ h; unfold DAdj at h; simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.sum_pair (by omega), dStep_fork_left, dStep_left_fork, dStep_fork_right,
        dStep_right_fork, xProj_comp_xStep_add_yProj_comp_yStep, sStep_zero]
    | succ m =>
      rw [sum_range_dStep_eq_sum k (m + 1) (m + 1) {m, m + 2, m + 3} (by simp; omega) (by
        intro j _ h; unfold DAdj at h; simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.sum_insert (by simp), Finset.sum_pair (by omega), dStep_up_comp_down k le_rfl,
        dStep_fork_left, dStep_left_fork, dStep_fork_right, dStep_right_fork,
        xProj_comp_xStep_add_yProj_comp_yStep, Nat.add_sub_cancel_left, pow_one]
      exact forkCoord_ext k fun l t => by simp
  · -- On the long arm, consecutive backtracks carry opposite signs.
    obtain rfl | ⟨m, rfl⟩ : i = 0 ∨ ∃ m, i = m + 1 := by rcases i with _ | m <;> simp
    · rw [sum_range_dStep_eq_sum k c 0 {1} (by simp) (by
        intro j _ h; unfold DAdj at h; simp only [Finset.mem_singleton]; omega),
        Finset.sum_singleton, dStep_down_comp_up k (by omega), sStep_zero, smul_zero]
    · rw [sum_range_dStep_eq_sum k c (m + 1) {m, m + 2} (by simp; omega) (by
        intro j _ h; unfold DAdj at h; simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.sum_pair (by omega), dStep_up_comp_down k (by omega),
        dStep_down_comp_up k (j := m + 1) (by omega), ← add_smul]
      obtain ⟨e, he⟩ : ∃ e, c - m = e + 1 := ⟨c - m - 1, by omega⟩
      rw [he, show c - (m + 1) = e by omega, pow_succ, mul_neg_one, neg_add_cancel, zero_smul]

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Q" => DoubledQuiver DG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "π" => signlessPreprojectiveMk k Q
local notation "e" => fun a : Fin (DynkinType.D n).rank => π (vertexIdempotent k (vertex DG a))

private noncomputable local instance : DecidableEq Q := Classical.decEq _

/-- The representation of the doubled `Dₙ` quiver detecting the fork words. -/
private noncomputable def forkRep (n : ℕ) : QuiverRep k Q :=
  Paths.lift {
    obj := fun _ => ModuleCat.of k (ForkCoord k)
    map := fun {i j} _ => ModuleCat.ofHom (dStep k (n - 3)
      ((vertexEquiv DG).symm i).val ((vertexEquiv DG).symm j).val) }

/-- `Paths.lift` assigns `ModuleCat.of k (ForkCoord k)` to every vertex. Thus its underlying
`QuiverRep.vertexSpace` reduces to `ForkCoord k`; this equivalence records that identification. -/
private noncomputable def forkVertexEquiv (i : Q) :
    ForkCoord k ≃ₗ[k] QuiverRep.vertexSpace k Q (forkRep k n) i :=
  LinearEquiv.refl k _

private theorem forkRep_map_arrow {i j : Q} (f : i ⟶ j) :
    (forkRep k n).map f.toPath = ModuleCat.ofHom (dStep k (n - 3)
      ((vertexEquiv DG).symm i).val ((vertexEquiv DG).symm j).val) :=
  Paths.lift_toPath _ _

private theorem forkRep_arrow {i j : Q} (f : i ⟶ j) (x : ForkCoord k) :
    QuiverRep.mapₗ k Q (forkRep k n) f.toPath (forkVertexEquiv k i x) =
      forkVertexEquiv k j
        (dStep k (n - 3) ((vertexEquiv DG).symm i).val ((vertexEquiv DG).symm j).val x) := by
  rw [QuiverRep.mapₗ_apply, forkRep_map_arrow]
  -- `forkVertexEquiv` is the underlying identity of each constant `ModuleCat.of` object.
  rfl

private theorem sum_neighborSet_dStep (hn : 3 ≤ n) (i : Fin (DynkinType.D n).rank) :
    ∑ w : (DG).neighborSet i, dStep k (n - 3) w.val.val i.val ∘ₗ dStep k (n - 3) i.val w.val.val =
      0 := by
  classical
  have hzero (j : Fin (DynkinType.D n).rank) (hj : ¬(DG).Adj i j) :
      dStep k (n - 3) j.val i.val ∘ₗ dStep k (n - 3) i.val j.val = 0 := by
    rw [dStep_eq_zero k (j := j.val) fun h => hj ((diagramGraph_D_adj hn i j).2 (by
      unfold DAdj at h; omega)), LinearMap.comp_zero]
  rw [← Finset.sum_subtype (Finset.univ.filter ((DG).Adj i))
      (fun j => by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborSet])
      (fun j => dStep k (n - 3) j.val i.val ∘ₗ dStep k (n - 3) i.val j.val),
    Finset.sum_filter_of_ne fun j _ h => by_contra fun hj => h (hzero j hj),
    Fin.sum_univ_eq_sum_range (fun j => dStep k (n - 3) j i.val ∘ₗ dStep k (n - 3) i.val j)]
  have hn' : n - 3 + 3 = (DynkinType.D n).rank := by rw [DynkinType.rank_D]; omega
  have h := sum_range_dStep_comp k (n - 3) i.val (by rw [hn']; exact i.isLt)
  rwa [hn'] at h

private theorem forkRep_relator (hn : 3 ≤ n) (v : Q) :
    QuiverRep.toEnd k Q (forkRep k n) (signlessPreprojectiveRelator k v) = 0 := by
  classical
  obtain ⟨i, rfl⟩ := exists_eq_vertex DG v
  rw [signlessPreprojectiveRelator_congr k (vertex DG i) _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum]
  simp only [backtrackElem_eq_ofPath, QuiverRep.toEnd_ofPath]
  have hzero : (∑ w : (DG).neighborSet i,
      QuiverRep.mapₗ k Q (forkRep k n)
        (backtrackPath DG (((DG).mem_neighborSet i w).1 w.2))) = 0 := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := (forkVertexEquiv k (vertex DG i)).surjective z
    simp only [LinearMap.sum_apply, backtrackPath_eq_comp, arrowPath_eq_toPath,
      QuiverRep.mapₗ_comp, LinearMap.comp_apply, forkRep_arrow, vertexEquiv_symm_vertex]
    rw [← map_sum, LinearMap.zero_apply, ← map_zero (forkVertexEquiv k (vertex DG i))]
    congr 1
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun (sum_neighborSet_dStep k hn i) x
  apply LinearMap.ext
  intro z
  simp only [LinearMap.sum_apply, QuiverRep.pathEnd_apply]
  rw [← map_sum (DirectSum.lof k Q (QuiverRep.vertexSpace k Q (forkRep k n)) (vertex DG i))]
  have hz := LinearMap.congr_fun hzero
    (DirectSum.component k Q (QuiverRep.vertexSpace k Q (forkRep k n)) (vertex DG i) z)
  simpa only [LinearMap.sum_apply, LinearMap.zero_apply, map_zero] using
    congrArg (DirectSum.lof k Q (QuiverRep.vertexSpace k Q (forkRep k n)) (vertex DG i)) hz

private noncomputable def forkAction (hn : 3 ≤ n) :=
  signlessPreprojectiveLift (QuiverRep.toEnd k Q (forkRep k n)) (forkRep_relator k hn)

private noncomputable def forkVector (a : Fin (DynkinType.D n).rank) :
    ForkCoord k →ₗ[k] DirectSum Q (QuiverRep.vertexSpace k Q (forkRep k n)) :=
  DirectSum.lof k Q (QuiverRep.vertexSpace k Q (forkRep k n)) (vertex DG a) ∘ₗ
    (forkVertexEquiv k (vertex DG a)).toLinearMap

private theorem forkAction_vertex (hn : 3 ≤ n) (a : Fin (DynkinType.D n).rank) (x : ForkCoord k) :
    forkAction k hn (e a) (forkVector k a x) = forkVector k a x := by
  rw [forkAction, signlessPreprojectiveLift_signlessPreprojectiveMk,
    QuiverRep.toEnd_vertexIdempotent, QuiverRep.pathEnd_apply, QuiverRep.mapₗ_nil]
  simp only [forkVector, LinearMap.comp_apply, DirectSum.component.lof_self, LinearMap.id_apply]

private theorem forkAction_arrow (hn : 3 ≤ n) (a b : Fin (DynkinType.D n).rank) (x : ForkCoord k)
    (h : (DG).Adj a b) :
    forkAction k hn (signlessArrow k DG a b) (forkVector k a x) =
      forkVector k b (dStep k (n - 3) a b x) := by
  rw [signlessArrow_of_adj k h, forkAction,
    signlessPreprojectiveLift_signlessPreprojectiveMk, ofArrow_eq_ofPath,
    QuiverRep.toEnd_ofPath, QuiverRep.pathEnd_apply]
  simp only [forkVector, LinearMap.comp_apply, DirectSum.component.lof_self, forkRep_arrow,
    vertexEquiv_symm_vertex, LinearEquiv.coe_coe]

/-! ### The fork words act on the empty word -/

private theorem xStep_yStep_sStep_pow (j t : ℕ) (ht : t ≤ j) :
    xStep k j ((sStep k j ^ t) (Finsupp.single (true, 0) 1)) = Finsupp.single (true, t + 1) 1 ∧
      yStep k j ((sStep k j ^ t) (Finsupp.single (true, 0) 1)) = bWord k j (t + 1) := by
  induction t with
  | zero => simp [xStep_single, yStep_single]
  | succ t ih =>
    obtain ⟨hx, hy⟩ := ih (by omega)
    rw [pow_succ', Module.End.mul_apply, sStep_apply, hx, hy]
    simp [bWord, xStep_single, yStep_single, show t + 1 ≤ j by omega]

private theorem forkAction_turn_aux (hn : 3 ≤ n) (a : Fin (DynkinType.D n).rank)
    (ha : n - 3 < a.val) (x : ForkCoord k) :
    forkAction k hn (signlessArrow k DG a (n - 3) * signlessArrow k DG (n - 3) a)
        (forkVector k (preprojectiveDForkVertex n hn) x) =
      forkVector k (preprojectiveDForkVertex n hn)
        (dStep k (n - 3) a (n - 3) (dStep k (n - 3) (n - 3) a x)) := by
  have hoa : (DG).Adj (preprojectiveDForkVertex n hn) a :=
    (diagramGraph_D_adj hn _ a).2 (.inr (.inr (.inl ⟨preprojectiveDForkVertex_val hn, ha⟩)))
  have h₁ := forkAction_arrow k hn _ a x hoa
  have h₂ := forkAction_arrow k hn a _ (dStep k (n - 3) (n - 3) a x) hoa.symm
  simp only [preprojectiveDForkVertex_val] at h₁ h₂
  rw [map_mul, Module.End.mul_apply, h₁, h₂]

private theorem forkAction_turn_left (hn : 3 ≤ n) (x : ForkCoord k) :
    forkAction k hn
        (signlessArrow k DG (n - 3 + 1) (n - 3) * signlessArrow k DG (n - 3) (n - 3 + 1))
        (forkVector k (preprojectiveDForkVertex n hn) x) =
      forkVector k (preprojectiveDForkVertex n hn) (xStep k (n - 3) x) := by
  have h := forkAction_turn_aux k hn ⟨n - 3 + 1, by rw [DynkinType.rank_D]; omega⟩
    (by dsimp only; omega) x
  rwa [dStep_fork_left, dStep_left_fork, show xProj k (n - 3) (xStep k (n - 3) x) =
    xStep k (n - 3) x from LinearMap.congr_fun (xProj_comp_xStep k _) x] at h

private theorem forkAction_turn_right (hn : 3 ≤ n) (x : ForkCoord k) :
    forkAction k hn
        (signlessArrow k DG (n - 3 + 2) (n - 3) * signlessArrow k DG (n - 3) (n - 3 + 2))
        (forkVector k (preprojectiveDForkVertex n hn) x) =
      forkVector k (preprojectiveDForkVertex n hn) (yStep k (n - 3) x) := by
  have h := forkAction_turn_aux k hn ⟨n - 3 + 2, by rw [DynkinType.rank_D]; omega⟩
    (by dsimp only; omega) x
  rwa [dStep_fork_right, dStep_right_fork, show yProj k (n - 3) (yStep k (n - 3) x) =
    yStep k (n - 3) x from LinearMap.congr_fun (yProj_comp_yStep k _) x] at h

/-- The sum of the two leaf backtracks at the fork acts as `x + y`. -/
private theorem forkAction_turn_add (hn : 3 ≤ n) (x : ForkCoord k) :
    forkAction k hn
        (signlessArrow k DG (n - 3 + 1) (n - 3) * signlessArrow k DG (n - 3) (n - 3 + 1) +
          signlessArrow k DG (n - 3 + 2) (n - 3) * signlessArrow k DG (n - 3) (n - 3 + 2))
        (forkVector k (preprojectiveDForkVertex n hn) x) =
      forkVector k (preprojectiveDForkVertex n hn) (sStep k (n - 3) x) := by
  rw [map_add, LinearMap.add_apply, forkAction_turn_left, forkAction_turn_right, ← map_add,
    sStep_apply]

private theorem forkAction_turn_add_pow (hn : 3 ≤ n) (t : ℕ) (x : ForkCoord k) :
    forkAction k hn
        ((signlessArrow k DG (n - 3 + 1) (n - 3) * signlessArrow k DG (n - 3) (n - 3 + 1) +
          signlessArrow k DG (n - 3 + 2) (n - 3) * signlessArrow k DG (n - 3) (n - 3 + 2)) ^ t)
        (forkVector k (preprojectiveDForkVertex n hn) x) =
      forkVector k (preprojectiveDForkVertex n hn) ((sStep k (n - 3) ^ t) x) := by
  induction t generalizing x with
  | zero => simp only [pow_zero, map_one, Module.End.one_apply]
  | succ t ih => simp only [pow_succ, map_mul, Module.End.mul_apply, forkAction_turn_add, ih]

private theorem forkAction_branchWord (hn : 3 ≤ n) (l : Bool) (t : ℕ) (x : ForkCoord k) :
    forkAction k hn (signlessPreprojectiveDBranchWord k (preprojectiveDForkVertex n hn)
        (preprojectiveDForkVertex n hn) l (t + 1))
        (forkVector k (preprojectiveDForkVertex n hn) x) =
      forkVector k (preprojectiveDForkVertex n hn)
        ((if l then xStep k (n - 3) else yStep k (n - 3)) ((sStep k (n - 3) ^ t) x)) := by
  rw [signlessPreprojectiveDBranchWord_def]
  simp only [preprojectiveDForkVertex_val, le_refl, ite_true, Nat.sub_self, ladderValley_zero_zero,
    mul_one, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, map_mul, Module.End.mul_apply,
    forkAction_vertex, forkAction_turn_add_pow]
  cases l <;> simp only [Bool.false_eq_true, ite_true, ite_false, forkAction_turn_left,
    forkAction_turn_right, forkAction_vertex]

/-- Reading off the fork component of the action on the empty word. -/
private noncomputable def forkDetect (hn : 3 ≤ n) : Π →ₗ[k] ForkCoord k where
  toFun z := (forkVertexEquiv k (vertex DG (preprojectiveDForkVertex n hn))).symm
    (DirectSum.component k Q (QuiverRep.vertexSpace k Q (forkRep k n))
      (vertex DG (preprojectiveDForkVertex n hn))
      (forkAction k hn z (forkVector k (preprojectiveDForkVertex n hn)
        (Finsupp.single (true, 0) 1))))
  map_add' z w := by simp only [map_add, LinearMap.add_apply]
  map_smul' a z := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

private theorem forkDetect_of_eq (hn : 3 ≤ n) {z : Π} {x : ForkCoord k}
    (h : forkAction k hn z (forkVector k (preprojectiveDForkVertex n hn)
      (Finsupp.single (true, 0) 1)) = forkVector k (preprojectiveDForkVertex n hn) x) :
    forkDetect k hn z = x := by
  simp only [forkDetect, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h]
  simp only [forkVector, LinearMap.comp_apply, DirectSum.component.lof_self, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- The coordinate detecting each reduced fork word. -/
private def forkWordIndex (n : ℕ) : Option (Bool × Fin (n - 3)) ⊕ Unit → Bool × ℕ
  | .inl none => (true, 0)
  | .inl (some (l, t)) => (l, t.val + 1)
  | .inr _ => (true, n - 3 + 1)

private theorem forkWordIndex_injective (n : ℕ) : Function.Injective (forkWordIndex n) := by
  rintro ((_ | ⟨l, t⟩) | u) ((_ | ⟨l', t'⟩) | u') h <;>
    simp only [forkWordIndex, Prod.mk.injEq] at h
  · rfl
  · omega
  · omega
  · omega
  · simp only [Sum.inl.injEq, Option.some.injEq, Prod.mk.injEq]
    exact ⟨h.1, Fin.ext (by simpa using h.2)⟩
  · have := t.isLt; omega
  · omega
  · have := t'.isLt; omega
  · rfl

private theorem forkDetect_forkWords (hn : 3 ≤ n) (i : Option (Bool × Fin (n - 3)) ⊕ Unit) :
    forkDetect k hn (signlessPreprojectiveDForkWords k hn i) =
      Finsupp.single (forkWordIndex n i) 1 := by
  apply forkDetect_of_eq
  rcases i with (_ | ⟨l, t⟩) | u
  · rw [signlessPreprojectiveDForkWords_inl_none]
    exact forkAction_vertex k hn _ _
  · rw [signlessPreprojectiveDForkWords_inl_some, forkAction_branchWord]
    obtain ⟨hx, hy⟩ := xStep_yStep_sStep_pow k (n - 3) t.val (by omega)
    cases l
    · simp only [Bool.false_eq_true, ite_false, hy, bWord, show t.val + 1 ≤ n - 3 by omega,
        ite_true, forkWordIndex]
    · simp only [ite_true, hx, forkWordIndex]
  · rw [signlessPreprojectiveDForkWords_inr, forkAction_branchWord]
    simp only [↓reduceIte, (xStep_yStep_sStep_pow k (n - 3) (n - 3) le_rfl).1, forkWordIndex]

/-- The reduced fork words are linearly independent over every field. Here `x` and `y` are
the backtracks from the fork into the two leaves. The words are the unit, the alternating
words `x (x + y)^(t - 1)` and `y (x + y)^(t - 1)` for `t = 1, …, n - 3`, and the single word
`x (x + y)^(n - 3)` of the longest length. -/
theorem linearIndependent_signlessPreprojectiveDForkWords (hn : 3 ≤ n) :
    LinearIndependent k (signlessPreprojectiveDForkWords k hn) := by
  apply LinearIndependent.of_comp (forkDetect k hn)
  simpa only [Function.comp_def, forkDetect_forkWords] using
    (Finsupp.linearIndependent_single_one k (Bool × ℕ)).comp _ (forkWordIndex_injective n)

/-- The basis of the fork corner `e_c Π e_c` of the signless preprojective algebra of `Dₙ`,
where `c = n - 3` is the fork vertex, consisting of the reduced fork words. -/
noncomputable def signlessPreprojectiveDForkBasis (hn : 3 ≤ n) :
    Module.Basis (Option (Bool × Fin (n - 3)) ⊕ Unit) k
      (cornerSubmodule k (e (preprojectiveDForkVertex n hn)) (e (preprojectiveDForkVertex n hn))) :=
  (Module.Basis.span (linearIndependent_signlessPreprojectiveDForkWords k hn)).map
    (LinearEquiv.ofEq _ _ (cornerSubmodule_signlessPreprojective_D_fork_eq_span k hn).symm)

/-- The fork-corner basis vector is the indicated reduced fork word. -/
@[simp]
theorem coe_signlessPreprojectiveDForkBasis_apply (hn : 3 ≤ n)
    (i : Option (Bool × Fin (n - 3)) ⊕ Unit) :
    (signlessPreprojectiveDForkBasis k hn i : Π) = signlessPreprojectiveDForkWords k hn i := by
  rw [signlessPreprojectiveDForkBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

/-- The fork corner of the signless preprojective algebra of `Dₙ` has dimension `2 n - 4`. -/
@[simp]
theorem finrank_cornerSubmodule_signlessPreprojective_D_fork (hn : 3 ≤ n) :
    Module.finrank k
      (cornerSubmodule k (e (preprojectiveDForkVertex n hn)) (e (preprojectiveDForkVertex n hn))) =
        2 * n - 4 := by
  rw [Module.finrank_eq_card_basis (signlessPreprojectiveDForkBasis k hn)]
  simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_unit]
  omega

end TauCeti
