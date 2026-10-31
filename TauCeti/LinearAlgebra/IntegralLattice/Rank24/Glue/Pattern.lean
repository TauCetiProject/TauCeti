/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.Perm.SumCongr
import TauCeti.Data.List.Rotate

/-!
# Conway--Sloane glue-generator patterns

The compact notation for glue generators uses literal words, rotations of one marked block,
and even permutations of positions. `GluePattern` records those three operations as data;
`GluePattern.expand` produces the finite set of digit words they denote. Only the marked
block rotates, so a prefix or suffix stays fixed. Even permutations act on positions, including
when digits repeat. Expansion removes duplicate words, not generators from their additive span.

Every expanded word has the declared length. Rotating the marked seed or evenly permuting an
even-permutation seed leaves the expanded set unchanged. These equalities let a subsequent
checked decoder and additive closure use any such seed without changing the glue subgroup.
Digits remain natural numbers here: their admissibility depends on the ordered component
alphabets and must be checked when decoding, rather than assumed by pattern expansion.

Each pattern also records its seed `GluePattern.seed` as a function of the positions, and the
subgroup `GluePattern.symmetries` of coordinate permutations it indicates: the identity for a
literal word, the rotations of the marked block (fixing the prefix and suffix) for a cyclic
pattern, and the alternating group for an even-permutation pattern. The expansion is exactly the
orbit of the seed under these permutations (`GluePattern.mem_expand_iff_exists_mem_symmetries`),
so it is invariant under them (`GluePattern.ofFn_comp_mem_expand_iff`).

The examples include the three rotations of the `D₈³` seed, the fixed-prefix `E₆⁴` pattern,
and all twelve even permutations of the `D₆⁴` seed.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*,
  3rd edition, Chapter 4 §3 and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

/-- A literal glue word, a word with one cyclically expanded block, or a word expanded by
all even permutations of its positions. The prefix and suffix of a cyclic block stay fixed. -/
inductive GluePattern where
  /-- A single digit word. -/
  | literal (word : List ℕ)
  /-- Rotate `block` while keeping `pre` and `post` fixed. -/
  | cyclic (pre block post : List ℕ)
  /-- Apply every even permutation of the positions of `word`. -/
  | evenPermutations {n : ℕ} (word : Fin n → ℕ)

namespace GluePattern

/-- The number of component labels in every word of a pattern. -/
@[expose] def length : GluePattern → ℕ
  | literal word => word.length
  | cyclic pre block post => pre.length + block.length + post.length
  | @evenPermutations n _ => n

/-- A literal pattern has the length of its supplied word. -/
@[simp]
theorem length_literal (word : List ℕ) : (literal word).length = word.length :=
  (rfl)

/-- A cyclic pattern has the total length of its three blocks. -/
@[simp]
theorem length_cyclic (pre block post : List ℕ) :
    (cyclic pre block post).length = pre.length + block.length + post.length :=
  (rfl)

/-- Even-permutation expansion preserves the number of positions. -/
@[simp]
theorem length_evenPermutations {n : ℕ} (word : Fin n → ℕ) :
    (evenPermutations word).length = n :=
  (rfl)

/-- Expand a pattern into its finite set of digit words. An empty cyclic block has one
expansion, namely the concatenation of its fixed prefix and suffix. -/
def expand : GluePattern → Finset (List ℕ)
  | literal word => {word}
  | cyclic pre block post =>
    block.cyclicPermutations.toFinset.image (fun w ↦ pre ++ w ++ post)
  | @evenPermutations n word =>
    Finset.univ.image (fun σ : alternatingGroup (Fin n) ↦ List.ofFn (word ∘ σ.val))

/-- Literal expansion produces precisely the supplied word. -/
@[simp]
theorem expand_literal (word : List ℕ) : (literal word).expand = {word} :=
  (rfl)

/-- Cyclic expansion changes only the marked block. -/
theorem expand_cyclic (pre block post : List ℕ) :
    (cyclic pre block post).expand =
      block.cyclicPermutations.toFinset.image (fun w ↦ pre ++ w ++ post) :=
  (rfl)

/-- Even-permutation expansion enumerates the actual alternating group on positions. -/
theorem expand_evenPermutations {n : ℕ} (word : Fin n → ℕ) :
    (evenPermutations word).expand =
      Finset.univ.image (fun σ : alternatingGroup (Fin n) ↦ List.ofFn (word ∘ σ.val)) :=
  (rfl)

/-- Membership in a cyclic expansion means rotating exactly the marked block. -/
@[simp]
theorem mem_expand_cyclic_iff (pre block post word : List ℕ) :
    word ∈ (cyclic pre block post).expand ↔
      ∃ b, b ∈ block.cyclicPermutations ∧ pre ++ b ++ post = word := by
  simp [expand_cyclic]

/-- Membership in an even-permutation expansion gives an even permutation of positions. -/
@[simp]
theorem mem_expand_evenPermutations_iff {n : ℕ} (seed : Fin n → ℕ) (word : List ℕ) :
    word ∈ (evenPermutations seed).expand ↔
      ∃ σ : alternatingGroup (Fin n), List.ofFn (seed ∘ σ.val) = word := by
  simp [expand_evenPermutations]

/-- Every expanded word has the pattern's specified length. -/
theorem length_of_mem_expand (p : GluePattern) {word : List ℕ} (h : word ∈ p.expand) :
    word.length = p.length := by
  cases p with
  | literal seed =>
    have hw : word = seed := by simpa using h
    simp [hw, length]
  | cyclic pre block post =>
    obtain ⟨b, hb, rfl⟩ := (mem_expand_cyclic_iff _ _ _ _).mp h
    simp [length, List.length_mem_cyclicPermutations block hb, Nat.add_assoc]
  | evenPermutations seed =>
    obtain ⟨σ, rfl⟩ := (mem_expand_evenPermutations_iff _ _).mp h
    simp [length]

/-- The unrotated cyclic seed is always among its expansions. -/
theorem seed_mem_expand_cyclic (pre block post : List ℕ) :
    pre ++ block ++ post ∈ (cyclic pre block post).expand :=
  (mem_expand_cyclic_iff _ _ _ _).mpr ⟨block, List.mem_cyclicPermutations_self block, rfl⟩

/-- The identity permutation puts the seed in its even-permutation expansion. -/
theorem seed_mem_expand_evenPermutations {n : ℕ} (word : Fin n → ℕ) :
    List.ofFn word ∈ (evenPermutations word).expand := by
  exact (mem_expand_evenPermutations_iff _ _).mpr ⟨1, by simp⟩

/-- No pattern has an empty expansion, even in length zero. -/
theorem expand_nonempty (p : GluePattern) : p.expand.Nonempty := by
  cases p with
  | literal word => simp
  | cyclic pre block post => exact ⟨_, seed_mem_expand_cyclic _ _ _⟩
  | evenPermutations word => exact ⟨_, seed_mem_expand_evenPermutations _⟩

/-- Rotating the marked seed leaves the expanded set unchanged. In particular, decoding and
taking the additive span after expansion are independent of the starting point in the block. -/
@[simp]
theorem expand_cyclic_rotate (pre block post : List ℕ) (k : ℕ) :
    (cyclic pre (block.rotate k) post).expand = (cyclic pre block post).expand := by
  simp only [expand_cyclic, List.cyclicPermutations_rotate]
  congr 1
  ext word
  simp

/-- Evenly permuting a seed leaves its entire even-permutation expansion unchanged. -/
@[simp]
theorem expand_evenPermutations_comp {n : ℕ} (word : Fin n → ℕ)
    (τ : alternatingGroup (Fin n)) :
    (evenPermutations (word ∘ τ.val)).expand = (evenPermutations word).expand := by
  ext w
  simp only [mem_expand_evenPermutations_iff]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨τ * σ, rfl⟩
  · rintro ⟨σ, rfl⟩
    refine ⟨τ⁻¹ * σ, ?_⟩
    congr 1
    funext i
    simp

/-- An expanded cyclic word has exactly the same multiset of digits as its seed. -/
theorem perm_of_mem_expand_cyclic {pre block post word : List ℕ}
    (h : word ∈ (cyclic pre block post).expand) :
    word.Perm (pre ++ block ++ post) := by
  obtain ⟨b, hb, rfl⟩ := (mem_expand_cyclic_iff _ _ _ _).mp h
  exact ((List.mem_cyclicPermutations_iff.mp hb).perm.append_left pre).append_right post

/-- An expanded even-permutation word has exactly the same multiset of digits as its seed. -/
theorem perm_of_mem_expand_evenPermutations {n : ℕ} {seed : Fin n → ℕ} {word : List ℕ}
    (h : word ∈ (evenPermutations seed).expand) : word.Perm (List.ofFn seed) := by
  obtain ⟨σ, rfl⟩ := (mem_expand_evenPermutations_iff _ _).mp h
  exact Equiv.Perm.ofFn_comp_perm σ.val seed

/-- The `D₈³` pattern rotates the entire block `(122)`. -/
theorem expand_d8_cubed :
    (cyclic [] [1, 2, 2] []).expand = {[1, 2, 2], [2, 2, 1], [2, 1, 2]} := by
  decide

/-- The `E₆⁴` pattern keeps its leading `1` fixed while rotating `(012)`. -/
theorem expand_e6_fourth :
    (cyclic [1] [0, 1, 2] []).expand = {[1, 0, 1, 2], [1, 1, 2, 0], [1, 2, 0, 1]} := by
  decide

/-- The even-permutation pattern `(0123)` for `D₆⁴` gives twelve distinct words. -/
theorem card_expand_d6_fourth :
    (evenPermutations (fun i : Fin 4 ↦ i.val)).expand.card = 12 := by
  rw [expand_evenPermutations, Finset.card_image_of_injective]
  · rw [Finset.card_univ]
    exact (card_alternatingGroup (α := Fin 4)).trans (by decide)
  · intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.ext (congrFun (List.ofFn_injective h) i)

/-! ### Seeds and indicated coordinate permutations -/

/-- The seed of a pattern as a function of its positions: the literal word, the unrotated cyclic
word, or the word whose positions are evenly permuted. -/
def seed : (p : GluePattern) → Fin p.length → ℕ
  | literal word => word.get
  | cyclic pre block post => Fin.append (Fin.append pre.get block.get) post.get
  | evenPermutations word => word

/-- The coordinate permutations indicated by a pattern: only the identity for a literal word,
the rotations of the marked block (fixing the prefix and suffix) for a cyclic pattern, and the
even permutations of all positions for an even-permutation pattern. -/
def symmetries : (p : GluePattern) → Subgroup (Equiv.Perm (Fin p.length))
  | literal _ => ⊥
  | cyclic _ block _ =>
    Subgroup.zpowers (Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate block.length)) 1)
  | evenPermutations _ => alternatingGroup _

/-- The seed of a literal pattern lists its word. -/
@[simp]
theorem seed_literal (word : List ℕ) : (literal word).seed = word.get :=
  (rfl)

/-- The seed of a cyclic pattern is its unrotated word. -/
@[simp]
theorem seed_cyclic (pre block post : List ℕ) :
    (cyclic pre block post).seed = Fin.append (Fin.append pre.get block.get) post.get :=
  (rfl)

/-- The seed of an even-permutation pattern is its word. -/
@[simp]
theorem seed_evenPermutations {n : ℕ} (word : Fin n → ℕ) :
    (evenPermutations word).seed = word :=
  (rfl)

/-- A literal pattern indicates no coordinate permutation other than the identity. -/
@[simp]
theorem symmetries_literal (word : List ℕ) : (literal word).symmetries = ⊥ :=
  (rfl)

/-- A cyclic pattern indicates the rotations of its marked block. -/
@[simp]
theorem symmetries_cyclic (pre block post : List ℕ) :
    (cyclic pre block post).symmetries =
      Subgroup.zpowers
        (Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate block.length)) 1) :=
  (rfl)

/-- An even-permutation pattern indicates the even permutations of its positions. -/
@[simp]
theorem symmetries_evenPermutations {n : ℕ} (word : Fin n → ℕ) :
    (evenPermutations word).symmetries = alternatingGroup (Fin n) :=
  (rfl)

/-- Rotating the marked block of a cyclic seed `k` times rotates the block of the listed word. -/
theorem ofFn_seed_cyclic_comp_pow (pre block post : List ℕ) (k : ℕ) :
    List.ofFn ((cyclic pre block post).seed ∘
        ⇑(Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate block.length)) 1 ^ k)) =
      pre ++ block.rotate k ++ post := by
  -- The positions of the seed are indexed by `(cyclic pre block post).length`, which is only
  -- definitionally the sum of the three block lengths; state the computation on the sum.
  have h : List.ofFn (Fin.append (Fin.append pre.get block.get) post.get ∘
      ⇑(Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate block.length)) 1 ^ k)) =
        pre ++ block.rotate k ++ post := by
    simp only [Equiv.Perm.finSumPerm_pow, one_pow, Fin.append_comp_finSumPerm,
      Equiv.Perm.coe_one, Function.comp_id, List.ofFn_fin_append, List.ofFn_get,
      List.ofFn_comp_finRotate_pow]
  exact h

/-- **A pattern expands to the orbit of its seed** under its indicated coordinate
permutations. -/
theorem mem_expand_iff_exists_mem_symmetries (p : GluePattern) (word : List ℕ) :
    word ∈ p.expand ↔ ∃ g ∈ p.symmetries, List.ofFn (p.seed ∘ g) = word := by
  cases p with
  | literal w =>
    simp only [expand_literal, Finset.mem_singleton, symmetries_literal, Subgroup.mem_bot,
      exists_eq_left, Equiv.Perm.coe_one, Function.comp_id, eq_comm]
    exact iff_of_eq (congrArg (word = ·) (List.ofFn_get w).symm)
  | cyclic pre block post =>
    rw [mem_expand_cyclic_iff, symmetries_cyclic]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨k, rfl⟩ := (List.mem_cyclicPermutations_iff.mp hb).symm
      exact ⟨_, Subgroup.npow_mem_zpowers _ k, ofFn_seed_cyclic_comp_pow pre block post k⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg)
      exact ⟨_, List.mem_cyclicPermutations_iff.mpr (List.IsRotated.forall block k),
        (ofFn_seed_cyclic_comp_pow pre block post k).symm⟩
  | evenPermutations w =>
    rw [mem_expand_evenPermutations_iff, symmetries_evenPermutations]
    exact ⟨fun ⟨σ, h⟩ ↦ ⟨σ.val, σ.2, h⟩, fun ⟨g, hg, h⟩ ↦ ⟨⟨g, hg⟩, h⟩⟩

/-- **The expansion of a pattern is invariant under its indicated coordinate permutations**:
permuting the positions of a word by a symmetry of the pattern does not change whether the word
is an expansion. -/
theorem ofFn_comp_mem_expand_iff (p : GluePattern) (f : Fin p.length → ℕ)
    {g : Equiv.Perm (Fin p.length)} (hg : g ∈ p.symmetries) :
    List.ofFn (f ∘ g) ∈ p.expand ↔ List.ofFn f ∈ p.expand := by
  simp only [mem_expand_iff_exists_mem_symmetries, List.ofFn_inj]
  constructor
  · rintro ⟨h, hh, hfg⟩
    refine ⟨h * g⁻¹, mul_mem hh (inv_mem hg), ?_⟩
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hfg, Function.comp_assoc,
      Equiv.Perm.coe_inv, Equiv.self_comp_symm, Function.comp_id]
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, mul_mem hh hg, rfl⟩

end GluePattern

end TauCeti
