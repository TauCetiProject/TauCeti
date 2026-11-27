/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.AElementary
public import TauCeti.ModelTheory.ModelExistence.Types

/-!
# Types and truth assignments relative to a fragment

The fragment type of a tuple consists of the formulas in a fragment's arity slice that hold of
that tuple. Equivalently, the tuple determines a truth assignment on the slice, and varying the
tuple gives the realized fragment `n`-types `A.realizedTypes M n` of a structure `M`. These two
views carry the same information, including for fragments that are not closed under negation.

Restriction to a smaller fragment intersects the type with its slice, or precomposes the truth
assignment with the slice inclusion and surjects the realized fragment types onto those of the
smaller fragment. Fragment-elementary embeddings preserve both descriptions; conversely,
preservation of the fragment types characterizes fragment elementarity. In particular, isomorphisms
preserve fragment types, truth assignments, and realized fragment types, and along an expansion by
a language homomorphism `g`, fragment types pull back along `Fragment.comap g` and push forward
along `Fragment.map g`. No countability, formation closure, injectivity of `g`, or nonemptiness
assumption is needed.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1
  (fragments and elementarity relative to a fragment).
-/

public section

universe u v u' v' w w'

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
  {A B : Fragment L} {n : ℕ}

/-- The type of a tuple relative to a fragment: the members of its arity slice true of the tuple.
It need not decide formulas outside the fragment, or contain their negations. -/
def fragmentType (A : Fragment L) (M : Type w) [L.Structure M] {n : ℕ} (a : Fin n → M) :
    Set (L.BoundedFormulaω Empty n) :=
  A.slice n ∩ infinitaryType M a

/-- A formula belongs to the fragment type exactly when it belongs to the fragment and is true
of the tuple. -/
@[simp]
theorem mem_fragmentType {a : Fin n → M} {φ : L.BoundedFormulaω Empty n} :
    φ ∈ fragmentType A M a ↔ (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧
      φ.Realize Empty.elim a := by
  simp only [fragmentType, Set.mem_inter_iff, Fragment.mem_slice, mem_infinitaryType]

/-- A fragment type is the restriction of the complete infinitary type to the arity slice. -/
theorem fragmentType_eq_inter (A : Fragment L) (a : Fin n → M) :
    fragmentType A M a = A.slice n ∩ infinitaryType M a := (rfl)

/-- The type of a tuple relative to the top fragment is its complete infinitary type. -/
@[simp]
theorem fragmentType_top (a : Fin n → M) :
    fragmentType (⊤ : Fragment L) M a = infinitaryType M a := by
  rw [fragmentType_eq_inter, Fragment.slice_top, Set.univ_inter]

/-- The type of a tuple relative to the bottom fragment is empty. -/
@[simp]
theorem fragmentType_bot (a : Fin n → M) : fragmentType (⊥ : Fragment L) M a = ∅ := by
  rw [fragmentType_eq_inter, Fragment.slice_bot, Set.empty_inter]

/-- Restricting a fragment restricts the fragment type by intersection with its arity slice. -/
theorem fragmentType_eq_inter_of_le (hAB : A ≤ B) (a : Fin n → M) :
    fragmentType A M a = A.slice n ∩ fragmentType B M a := by
  simpa only [fragmentType_eq_inter, Set.inter_def] using
    (Set.sep_eq_inter_sep (p := fun φ => φ ∈ infinitaryType M a) (Fragment.slice_mono hAB n))

/-- Fragment types are monotone in the fragment. -/
theorem fragmentType_mono (hAB : A ≤ B) (a : Fin n → M) :
    fragmentType A M a ⊆ fragmentType B M a :=
  Set.inter_subset_inter_left _ (Fragment.slice_mono hAB n)

/-- Equality of fragment types means agreement on realization of every formula in the slice. -/
theorem fragmentType_eq_iff {a : Fin n → M} {b : Fin n → N} :
    fragmentType A M a = fragmentType A N b ↔
      ∀ φ ∈ A.slice n, φ.Realize Empty.elim a ↔ φ.Realize Empty.elim b := by
  simpa only [fragmentType, Set.inter_def, mem_infinitaryType] using
    (Set.sep_ext_iff (s := A.slice n) (p := fun φ => φ ∈ infinitaryType M a)
      (q := fun φ => φ ∈ infinitaryType N b))

/-- An `A`-elementary embedding preserves the type of every tuple relative to `A`. -/
@[simp]
theorem AElementary.fragmentType_comp {f : N ↪[L] M} (hf : AElementary A f)
    (a : Fin n → N) : fragmentType A M (f ∘ a) = fragmentType A N a :=
  fragmentType_eq_iff.2 fun _ hφ => hf.realize_iff (Fragment.mem_slice.1 hφ) a

/-- An embedding is fragment-elementary exactly when it preserves every fragment type. -/
theorem aElementary_iff_fragmentType_comp {f : N ↪[L] M} :
    AElementary A f ↔ ∀ (n : ℕ) (a : Fin n → N),
      fragmentType A M (f ∘ a) = fragmentType A N a := by
  refine ⟨fun h _ a => h.fragmentType_comp a, fun h => aElementary_iff.2 ?_⟩
  intro n φ hφ a
  exact fragmentType_eq_iff.1 (h n a) φ (Fragment.mem_slice.2 hφ)

namespace Fragment

/-- The realized truth assignment of a tuple on the arity slice of a fragment. -/
def truthAssignment (A : Fragment L) (M : Type w) [L.Structure M] {n : ℕ} (a : Fin n → M) :
    A.slice n → Prop :=
  fun φ => φ.val.Realize Empty.elim a

/-- Evaluation of a realized truth assignment is realization of the formula. -/
@[simp]
theorem truthAssignment_apply (A : Fragment L) (a : Fin n → M) (φ : A.slice n) :
    A.truthAssignment M a φ ↔ φ.val.Realize Empty.elim a :=
  Iff.rfl

/-- On the slice, the truth assignment records membership in the fragment type. -/
theorem truthAssignment_iff_mem_fragmentType (A : Fragment L) (a : Fin n → M) (φ : A.slice n) :
    A.truthAssignment M a φ ↔ φ.val ∈ fragmentType A M a := by
  simp only [truthAssignment_apply, mem_fragmentType, mem_slice.1 φ.property, true_and]

/-- The truth assignment restricts along fragment inclusion by precomposition with the slice map.
The slice map is Mathlib's `Set.inclusion`, so its identity and composition laws apply directly. -/
theorem truthAssignment_restrict (hAB : A ≤ B) (a : Fin n → M) :
    A.truthAssignment M a = B.truthAssignment M a ∘ Set.inclusion (slice_mono hAB n) := (rfl)

/-- Equality of realized truth assignments is equivalent to equality of fragment types. -/
theorem truthAssignment_eq_iff {a : Fin n → M} {b : Fin n → N} :
    A.truthAssignment M a = A.truthAssignment N b ↔ fragmentType A M a = fragmentType A N b := by
  rw [fragmentType_eq_iff, funext_iff]
  simp only [truthAssignment_apply, Subtype.forall, propext_iff]

/-- The fragment `n`-types realized in `M`: the truth assignments on `A.slice n` of the `n`-tuples
of `M`. -/
def realizedTypes (A : Fragment L) (M : Type w) [L.Structure M] (n : ℕ) :
    Set (A.slice n → Prop) :=
  Set.range (A.truthAssignment M (n := n))

/-- `A.realizedTypes M n` is the range of `A.truthAssignment M` at arity `n`. -/
theorem realizedTypes_def (A : Fragment L) (M : Type w) [L.Structure M] (n : ℕ) :
    A.realizedTypes M n = Set.range (A.truthAssignment M (n := n)) :=
  (rfl)

/-- A truth assignment on `A.slice n` is realized in `M` exactly when it is the truth assignment of
some `n`-tuple of `M`. -/
@[simp]
theorem mem_realizedTypes {p : A.slice n → Prop} :
    p ∈ A.realizedTypes M n ↔ ∃ a : Fin n → M, A.truthAssignment M a = p :=
  Iff.rfl

/-- The truth assignment of any `n`-tuple of `M` belongs to `A.realizedTypes M n`. -/
theorem truthAssignment_mem_realizedTypes (A : Fragment L) (a : Fin n → M) :
    A.truthAssignment M a ∈ A.realizedTypes M n :=
  ⟨a, rfl⟩

/-- At arity `0`, the only realized fragment type is the truth assignment of the empty tuple. -/
theorem realizedTypes_zero (A : Fragment L) (M : Type w) [L.Structure M] :
    A.realizedTypes M 0 = {A.truthAssignment M Fin.elim0} := by
  rw [realizedTypes_def, Set.range_unique, Subsingleton.elim default Fin.elim0]

/-- On a countable carrier `M`, a structure realizes only countably many fragment `n`-types. -/
theorem countable_realizedTypes (A : Fragment L) (M : Type w) [L.Structure M] [Countable M]
    (n : ℕ) :
    (A.realizedTypes M n).Countable :=
  Set.countable_range _

/-- Restricting along a fragment inclusion `A ≤ B` surjects `B.realizedTypes M n` onto
`A.realizedTypes M n`. -/
theorem image_restrict_realizedTypes (hAB : A ≤ B) (M : Type w) [L.Structure M] (n : ℕ) :
    (· ∘ Set.inclusion (slice_mono hAB n)) '' B.realizedTypes M n = A.realizedTypes M n := by
  rw [realizedTypes_def, realizedTypes_def, ← Set.range_comp]
  exact congrArg Set.range (funext fun a => (truthAssignment_restrict hAB a).symm)

end Fragment

/-- An `A`-elementary embedding preserves the realized truth assignment on every arity slice. -/
@[simp]
theorem AElementary.truthAssignment_comp {f : N ↪[L] M} (hf : AElementary A f)
    (a : Fin n → N) : A.truthAssignment M (f ∘ a) = A.truthAssignment N a :=
  Fragment.truthAssignment_eq_iff.2 (hf.fragmentType_comp a)

/-- An isomorphism preserves every fragment type. -/
@[simp]
theorem Equiv.fragmentType_comp (e : N ≃[L] M) (A : Fragment L) (a : Fin n → N) :
    fragmentType A M (e ∘ a) = fragmentType A N a :=
  (e.aElementary A).fragmentType_comp a

/-- An isomorphism preserves every realized truth assignment. -/
@[simp]
theorem Equiv.truthAssignment_comp (e : N ≃[L] M) (A : Fragment L) (a : Fin n → N) :
    A.truthAssignment M (e ∘ a) = A.truthAssignment N a :=
  (e.aElementary A).truthAssignment_comp a

/-- Isomorphic structures realize the same fragment `n`-types. -/
theorem Equiv.realizedTypes_eq (e : M ≃[L] N) (A : Fragment L) (n : ℕ) :
    A.realizedTypes M n = A.realizedTypes N n := by
  ext p
  simp only [Fragment.mem_realizedTypes]
  refine ⟨fun ⟨a, ha⟩ => ⟨e ∘ a, by rw [e.truthAssignment_comp, ha]⟩,
    fun ⟨b, hb⟩ => ⟨e.symm ∘ b, by rw [e.symm.truthAssignment_comp, hb]⟩⟩

/-! ### Transport along language maps -/

section LanguageMap

variable {L' : Language.{u', v'}}

/-- Along an expansion, the fragment type relative to `B.comap g` is the preimage under `g` of the
fragment type relative to `B`. -/
@[simp]
theorem LHom.fragmentType_comap (g : L →ᴸ L') (B : Fragment L')
    [L'.Structure M] [g.IsExpansionOn M] (a : Fin n → M) :
    fragmentType (B.comap g) M a = g.onBoundedFormulaInf ⁻¹' fragmentType B M a := by
  rw [fragmentType_eq_inter, fragmentType_eq_inter, Set.preimage_inter, Fragment.slice_comap,
    g.preimage_onBoundedFormulaInf_infinitaryType]

/-- Along an expansion, the fragment type relative to `A.map g` is the image under `g` of the
fragment type relative to `A`. No injectivity of `g` is needed. -/
@[simp]
theorem LHom.fragmentType_map (g : L →ᴸ L') (A : Fragment L)
    [L'.Structure M] [g.IsExpansionOn M] (a : Fin n → M) :
    fragmentType (A.map g) M a = g.onBoundedFormulaInf '' fragmentType A M a := by
  rw [fragmentType_eq_inter, Fragment.slice_map, ← Set.image_inter_preimage,
    g.preimage_onBoundedFormulaInf_infinitaryType, ← fragmentType_eq_inter]

/-- Along an expansion, the truth assignment on `(B.comap g).slice n` factors through
`g.onBoundedFormulaInf` into the truth assignment on `B.slice n`. -/
theorem Fragment.truthAssignment_comap (g : L →ᴸ L') (B : Fragment L')
    [L'.Structure M] [g.IsExpansionOn M] (a : Fin n → M) :
    (B.comap g).truthAssignment M a =
      B.truthAssignment M a ∘ fun φ => ⟨g.onBoundedFormulaInf φ.val,
          by simpa using φ.property⟩ := by
  ext φ
  simp [LHom.realize_onBoundedFormulaInf]

/-- Along a language equivalence, reinterpreting `M` along the inverse map transports fragment
types by `e.onBoundedFormulaInf`. -/
theorem LEquiv.fragmentType_reduct (e : L ≃ᴸ L') (A : Fragment L) (a : Fin n → M) :
    letI := e.invLHom.reduct M
    fragmentType (A.map e.toLHom) M a = e.onBoundedFormulaInf '' fragmentType A M a := by
  let := e.invLHom.reduct M
  rw [← e.comap_invLHom_eq_map_toLHom, e.invLHom.fragmentType_comap, Equiv.image_eq_preimage_symm]
  ext ψ
  simp

end LanguageMap

end FirstOrder.Language
