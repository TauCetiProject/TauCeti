/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import Mathlib.Tactic

/-!
# Positive combinations of two roots in G₂

For independent roots α and β in G₂, a root mα + nβ with m,n positive can only have
coefficients (1,1), (2,1), (1,2), (3,1), (1,3), (3,2), or (2,3). Its existence also
forces α + β to be a root. These restrictions specify the possible factors in the
Chevalley commutator formula; they do not assert that every listed factor occurs.

The proof uses Mathlib's `RootPairing.EmbeddedG2.allCoeffs` and its enumeration theorem,
so no second choice of roots or normalization is introduced. In the coefficient table,
it suffices to check one short and one long root: the two simple reflections transport
the calculation to all other roots.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §5.2, Theorem 5.2.2.
-/

public section

namespace RootPairing

open Function Set

private def g2CombinationsAt (a : Fin 2 → ℤ) : Prop :=
  ∀ (b : Fin 2 → ℤ), b ∈ EmbeddedG2.allCoeffs → a ≠ b → a ≠ -b →
    ∀ (m n : ℕ), 0 < m → 0 < n → m • a + n • b ∈ EmbeddedG2.allCoeffs →
      (m, n) ∈ ({(1, 1), (2, 1), (1, 2), (3, 1), (1, 3), (3, 2), (2, 3)} :
        Finset (ℕ × ℕ)) ∧ a + b ∈ EmbeddedG2.allCoeffs

private theorem g2CombinationsAt_long : g2CombinationsAt ![0, 1] := by
  intro b hb hne hneg m n hm hn hc
  simp only [EmbeddedG2.allCoeffs, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [funext_iff, Fin.forall_fin_two] at hne <;>
    simp [funext_iff, Fin.forall_fin_two] at hneg <;>
    simp [EmbeddedG2.allCoeffs, funext_iff, Fin.forall_fin_two] at hc ⊢ <;> omega

private theorem g2CombinationsAt_short : g2CombinationsAt ![1, 0] := by
  intro b hb hne hneg m n hm hn hc
  simp only [EmbeddedG2.allCoeffs, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [funext_iff, Fin.forall_fin_two] at hne <;>
    simp [funext_iff, Fin.forall_fin_two] at hneg <;>
    simp [EmbeddedG2.allCoeffs, funext_iff, Fin.forall_fin_two] at hc ⊢ <;> omega

-- The simple reflections in the coordinates of Mathlib's allCoeffs table.
private def g2ShortReflection : Module.End ℤ (Fin 2 → ℤ) where
  toFun a := ![3 * a 1 - a 0, a 1]
  map_add' a b := by
    ext i
    fin_cases i
    · dsimp; ring
    · rfl
  map_smul' s a := by
    ext i
    fin_cases i
    · dsimp; ring
    · rfl

private def g2LongReflection : Module.End ℤ (Fin 2 → ℤ) where
  toFun a := ![a 0, a 0 - a 1]
  map_add' a b := by
    ext i
    fin_cases i
    · rfl
    · dsimp; ring
  map_smul' s a := by
    ext i
    fin_cases i
    · rfl
    · dsimp; ring

private theorem g2ShortReflection_involutive : Involutive g2ShortReflection := by
  intro a
  ext i
  fin_cases i <;> simp [g2ShortReflection]

private theorem g2LongReflection_involutive : Involutive g2LongReflection := by
  intro a
  ext i
  fin_cases i <;> simp [g2LongReflection]

private theorem g2ShortReflection_mem {a : Fin 2 → ℤ} (ha : a ∈ EmbeddedG2.allCoeffs) :
    g2ShortReflection a ∈ EmbeddedG2.allCoeffs := by
  simp only [EmbeddedG2.allCoeffs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [g2ShortReflection, EmbeddedG2.allCoeffs, funext_iff, Fin.forall_fin_two]

private theorem g2LongReflection_mem {a : Fin 2 → ℤ} (ha : a ∈ EmbeddedG2.allCoeffs) :
    g2LongReflection a ∈ EmbeddedG2.allCoeffs := by
  simp only [EmbeddedG2.allCoeffs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [g2LongReflection, EmbeddedG2.allCoeffs, funext_iff, Fin.forall_fin_two]

private theorem g2CombinationsAt_map (f : Module.End ℤ (Fin 2 → ℤ))
    (hf : Involutive f) (hmem : ∀ a ∈ EmbeddedG2.allCoeffs, f a ∈ EmbeddedG2.allCoeffs)
    {a : Fin 2 → ℤ} (ha : g2CombinationsAt a) : g2CombinationsAt (f a) := by
  intro b hb hne hneg m n hm hn hc
  have hab : a ≠ f b := fun h => hne (by rw [h, hf])
  have hab' : a ≠ -(f b) := fun h => hneg (by rw [h, map_neg, hf])
  have hc' := hmem _ hc
  rw [map_add, map_nsmul, map_nsmul, hf] at hc'
  obtain ⟨hpairs, hsum⟩ := ha (f b) (hmem b hb) hab hab' m n hm hn hc'
  exact ⟨hpairs, by simpa only [map_add, hf b] using hmem _ hsum⟩

private theorem g2_neg_mem_allCoeffs {a : Fin 2 → ℤ} (ha : a ∈ EmbeddedG2.allCoeffs) :
    -a ∈ EmbeddedG2.allCoeffs := by
  simp only [EmbeddedG2.allCoeffs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [EmbeddedG2.allCoeffs, funext_iff, Fin.forall_fin_two]

private theorem g2CombinationsAt_neg {a : Fin 2 → ℤ} (ha : g2CombinationsAt a) :
    g2CombinationsAt (-a) :=
  g2CombinationsAt_map (-LinearMap.id) (by intro a; simp) (fun _ => g2_neg_mem_allCoeffs) ha

private theorem g2CombinationsAt_of_mem {a : Fin 2 → ℤ} (ha : a ∈ EmbeddedG2.allCoeffs) :
    g2CombinationsAt a := by
  have hs {a} (h : g2CombinationsAt a) :=
    g2CombinationsAt_map g2ShortReflection g2ShortReflection_involutive
      (fun _ => g2ShortReflection_mem) h
  have hl {a} (h : g2CombinationsAt a) :=
    g2CombinationsAt_map g2LongReflection g2LongReflection_involutive
      (fun _ => g2LongReflection_mem) h
  have h11 : g2CombinationsAt ![1, 1] := by
    simpa [g2LongReflection] using hl g2CombinationsAt_short
  have h21 : g2CombinationsAt ![2, 1] := by
    simpa [g2ShortReflection] using hs h11
  have h31 : g2CombinationsAt ![3, 1] := by
    simpa [g2ShortReflection] using hs g2CombinationsAt_long
  have h32 : g2CombinationsAt ![3, 2] := by
    simpa [g2LongReflection] using hl h31
  simp only [EmbeddedG2.allCoeffs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact g2CombinationsAt_long
  · simpa only [Matrix.neg_cons, Matrix.neg_empty, neg_zero] using
      g2CombinationsAt_neg g2CombinationsAt_long
  · exact g2CombinationsAt_short
  · simpa only [Matrix.neg_cons, Matrix.neg_empty, neg_zero] using
      g2CombinationsAt_neg g2CombinationsAt_short
  · exact h11
  · simpa only [Matrix.neg_cons, Matrix.neg_empty] using g2CombinationsAt_neg h11
  · exact h21
  · simpa only [Matrix.neg_cons, Matrix.neg_empty] using g2CombinationsAt_neg h21
  · exact h31
  · simpa only [Matrix.neg_cons, Matrix.neg_empty] using g2CombinationsAt_neg h31
  · exact h32
  · simpa only [Matrix.neg_cons, Matrix.neg_empty] using g2CombinationsAt_neg h32

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsG2]

/-- A strictly positive combination of independent G₂ roots which is a root has one of
seven possible coefficient pairs, and the sum of the two roots is a root. -/
theorem coefficients_and_add_mem_range_root_of_isG2 {i j : ι}
    (hij : LinearIndependent R ![P.root i, P.root j]) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (h : m • P.root i + n • P.root j ∈ range P.root) :
    (m, n) ∈ ({(1, 1), (2, 1), (1, 2), (3, 1), (1, 3), (3, 2), (2, 3)} :
      Finset (ℕ × ℕ)) ∧ P.root i + P.root j ∈ range P.root := by
  classical
  let _ := IsG2.toEmbeddedG2 P
  let f := Fintype.linearCombination ℤ ![EmbeddedG2.shortRoot P, EmbeddedG2.longRoot P]
  have hf : Injective f :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp
      ((EmbeddedG2.linearIndependent_short_long P).restrict_scalars' ℤ)
  have coords (k : ι) : ∃ a ∈ EmbeddedG2.allCoeffs, f a = P.root k := by
    have hk := EmbeddedG2.mem_allRoots P k
    rw [EmbeddedG2.allRoots_eq_map_allCoeffs] at hk
    exact List.mem_map.mp hk
  obtain ⟨a, ha, hai⟩ := coords i
  obtain ⟨b, hb, hbj⟩ := coords j
  obtain ⟨k, hk⟩ := h
  obtain ⟨c, hc, hck⟩ := coords k
  have heq : m • a + n • b = c := hf (by rw [map_add, map_nsmul, map_nsmul, hai, hbj, hck, hk])
  obtain ⟨hne, hneg⟩ := (IsReduced.linearIndependent_iff P).mp hij
  have hab : a ≠ b := fun h => hne (P.root.injective (by rw [← hai, h, hbj]))
  have hab' : a ≠ -b := fun h => hneg (by rw [← hai, h, map_neg, hbj])
  obtain ⟨hpairs, hsum⟩ := g2CombinationsAt_of_mem ha b hb hab hab' m n hm hn (heq ▸ hc)
  refine ⟨hpairs, ?_⟩
  have hsum' : f (a + b) ∈ EmbeddedG2.allRoots P := by
    rw [EmbeddedG2.allRoots_eq_map_allCoeffs]
    exact List.mem_map.mpr ⟨a + b, hsum, rfl⟩
  have := EmbeddedG2.allRoots_subset_range_root P (List.mem_toFinset.mpr hsum')
  simpa only [map_add, hai, hbj] using this

/-- Exact positive-root support for an independent pair in G₂. Each possible coefficient
pair retains its own root-membership condition; not all seven need occur. -/
theorem pos_nsmul_add_pos_nsmul_mem_range_root_iff_of_isG2 {i j : ι}
    (hij : LinearIndependent R ![P.root i, P.root j]) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    m • P.root i + n • P.root j ∈ range P.root ↔
      (m = 1 ∧ n = 1 ∧ P.root i + P.root j ∈ range P.root) ∨
      (m = 2 ∧ n = 1 ∧ 2 • P.root i + P.root j ∈ range P.root) ∨
      (m = 1 ∧ n = 2 ∧ P.root i + 2 • P.root j ∈ range P.root) ∨
      (m = 3 ∧ n = 1 ∧ 3 • P.root i + P.root j ∈ range P.root) ∨
      (m = 1 ∧ n = 3 ∧ P.root i + 3 • P.root j ∈ range P.root) ∨
      (m = 3 ∧ n = 2 ∧ 3 • P.root i + 2 • P.root j ∈ range P.root) ∨
      (m = 2 ∧ n = 3 ∧ 2 • P.root i + 3 • P.root j ∈ range P.root) := by
  constructor
  · intro h
    have hpairs := (P.coefficients_and_add_mem_range_root_of_isG2 hij hm hn h).1
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpairs
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  · rintro (⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
      ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩) <;> simpa using h

end RootPairing
