/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import TauCeti.CategoryTheory.AlmostSplit.Basic
import TauCeti.CategoryTheory.IrreducibleMorphism
import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Finiteness from left almost split maps and vanishing chains

Let `T` be a class of objects of a preadditive category with finite biproducts, with local
endomorphism rings, such that every object of `T` has a left almost split map into a finite
biproduct of objects of `T`. A nonzero morphism `W ⟶ Y` between objects of `T` that is not an
isomorphism factors through this map, so a component of the map, followed by some morphism to `Y`,
is again nonzero after `W`. Iterating produces a chain of non-isomorphisms out of `W` along which
the composite stays nonzero, with objects taken from a finite collection at each step.

If every composite of `N` non-isomorphisms between objects of `T` vanishes, the process has to stop
within `N` steps, and it stops only when the morphism to `Y` is an isomorphism. Hence only finitely
many objects of `T`, up to isomorphism, receive a nonzero morphism from a given finite collection
(`TauCeti.exists_finite_forall_iso_of_hom_ne_zero`). This is the argument behind the first
Brauer–Thrall conjecture, where `T` is the class of indecomposable modules of bounded length, the
vanishing of chains is the Harada–Sai lemma, and the finite collection consists of the
indecomposable summands of the ring.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section VI.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Let `i` be a left almost split map into a finite biproduct, and `c ≫ g ≠ 0` with `g` not a split
monomorphism. Then `g` can be replaced by a component of `i` followed by a morphism out of that
summand, keeping the composite with `c` nonzero. Such a component of `i` is never a split
monomorphism, by `TauCeti.isSplitMono_of_isSplitMono_comp`. -/
theorem IsLeftAlmostSplit.exists_comp_π_comp_ne_zero {J : Type*} [Finite J] {X Y W : C} {F : J → C}
    [HasBiproduct F] {i : X ⟶ ⨁ F} (hi : IsLeftAlmostSplit i) {c : W ⟶ X} {g : X ⟶ Y}
    (hg : ¬ IsSplitMono g) (hc : c ≫ g ≠ 0) :
    ∃ (j : J) (h : F j ⟶ Y), c ≫ (i ≫ biproduct.π F j) ≫ h ≠ 0 := by
  cases nonempty_fintype J
  obtain ⟨t, rfl⟩ := hi.factors Y g hg
  by_contra! hzero
  refine hc ?_
  have ht : t = ∑ j, biproduct.π F j ≫ biproduct.ι F j ≫ t := by
    simp only [← Category.assoc, ← Preadditive.sum_comp, biproduct.total, Category.id_comp]
  rw [ht]
  simp only [Preadditive.comp_sum]
  exact Finset.sum_eq_zero fun j _ ↦ by simpa using hzero j (biproduct.ι F j ≫ t)

section Chain

/-- The objects reached from `S₀` in `m` steps along the relation `succ`. -/
private def chainLevel (succ : C → Set C) (S₀ : Set C) : ℕ → Set C
  | 0 => S₀
  | m + 1 => ⋃ X ∈ chainLevel succ S₀ m, succ X

/-- The state of the chain construction in `TauCeti.exists_mem_chainLevel_iso`: an object of `T`
with a morphism from `W` and a morphism to `Y`. -/
private structure ChainState (T : ObjectProperty C) (W Y : C) where
  /-- The current object. -/
  obj : C
  /-- The current object lies in `T`. -/
  prop : T obj
  /-- The composite of the chain built so far. -/
  fromBase : W ⟶ obj
  /-- The morphism to the target that is still to be factored. -/
  toTarget : obj ⟶ Y

variable (T : ObjectProperty C)

/-- Starting from a nonzero morphism `f : W ⟶ Y`, keep replacing the morphism to `Y` through the
steps provided by `hsucc`, as long as it is not an isomorphism. By the vanishing of composites of
`N` non-isomorphisms, it becomes an isomorphism within `N` steps. -/
private theorem exists_mem_chainLevel_iso (hlocal : ∀ X, T X → IsLocalRing (End X))
    {W Y : C} (succ : C → Set C)
    (hsucc : ∀ X, T X → ∀ (c : W ⟶ X) (g : X ⟶ Y), ¬ IsIso g → c ≫ g ≠ 0 →
      ∃ E ∈ succ X, T E ∧ ∃ (ι : X ⟶ E) (t : E ⟶ Y), ¬ IsIso ι ∧ c ≫ ι ≫ t ≠ 0)
    (N : ℕ) (hN : ∀ (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)), (∀ n, T (X n)) →
      (∀ n, ¬ IsIso (f n)) → (Functor.ofSequence f).map (homOfLE (Nat.zero_le N)) = 0)
    {S₀ : Set C} (hW : W ∈ S₀) (hTW : T W) {f : W ⟶ Y} (hf : f ≠ 0) :
    ∃ m ≤ N, ∃ Q ∈ chainLevel succ S₀ m, Nonempty (Y ≅ Q) := by
  by_contra! hiso
  -- One step of the chain. Once the construction is stuck it continues by zero morphisms, so that
  -- it gives a sequence of non-isomorphisms indexed by all of `ℕ`.
  have hstep (s : ChainState T W Y) : ∃ (s' : ChainState T W Y) (ι : s.obj ⟶ s'.obj),
      ¬ IsIso ι ∧ s'.fromBase = s.fromBase ≫ ι ∧
      (s.fromBase ≫ s.toTarget ≠ 0 → ¬ IsIso s.toTarget →
        s'.obj ∈ succ s.obj ∧ s'.fromBase ≫ s'.toTarget ≠ 0) := by
    by_cases h : s.fromBase ≫ s.toTarget ≠ 0 ∧ ¬ IsIso s.toTarget
    · obtain ⟨E, hE, hTE, ι, t, hι, ht⟩ := hsucc s.obj s.prop s.fromBase s.toTarget h.2 h.1
      exact ⟨⟨E, hTE, s.fromBase ≫ ι, t⟩, ι, hι, rfl, fun _ _ ↦ ⟨hE, by simpa using ht⟩⟩
    · have := hlocal _ s.prop
      refine ⟨⟨s.obj, s.prop, 0, 0⟩, 0, fun h₀ ↦ ?_, by simp, fun h₁ h₂ ↦ (h ⟨h₁, h₂⟩).elim⟩
      exact one_ne_zero (α := End s.obj) (End.ext (isIsoZeroSelfEquiv s.obj h₀))
  choose next ι hι hbase hnext using hstep
  -- The sequence of states, starting from `f`.
  let s : ℕ → ChainState T W Y := fun m ↦ Nat.rec ⟨W, hTW, 𝟙 W, f⟩ (fun _ x ↦ next x) m
  let link : ∀ m, (s m).obj ⟶ (s (m + 1)).obj := fun m ↦ ι (s m)
  -- The composite stays nonzero and the objects stay in the levels, up to step `N`.
  have hinv (m : ℕ) (hm : m ≤ N) :
      (s m).obj ∈ chainLevel succ S₀ m ∧ (s m).fromBase ≫ (s m).toTarget ≠ 0 := by
    induction m with
    | zero => exact ⟨hW, by simpa [s] using hf⟩
    | succ m ih =>
      obtain ⟨h₁, h₂⟩ := ih (by omega)
      have hniso : ¬ IsIso (s m).toTarget := fun _ ↦
        (hiso m (by omega) _ h₁).false (asIso (s m).toTarget).symm
      obtain ⟨h₃, h₄⟩ := hnext (s m) h₂ hniso
      exact ⟨Set.mem_iUnion₂.mpr ⟨_, h₁, h₃⟩, h₄⟩
  -- The morphisms `fromBase` form a cone over the sequence, so the last one factors through the
  -- composite of the links, which vanishes.
  have hmap := (NatTrans.ofSequence (F := (Functor.const ℕ).obj W)
    (G := Functor.ofSequence (X := fun m ↦ (s m).obj) link) (fun m ↦ (s m).fromBase)
    (fun m ↦ (Category.id_comp _).trans ((hbase (s m)).trans
      (congrArg _ (Functor.ofSequence_map_homOfLE_succ link m).symm)))).naturality
    (homOfLE (Nat.zero_le N))
  have hvanish := hN (fun m ↦ (s m).obj) link (fun m ↦ (s m).prop) (fun m ↦ hι (s m))
  have hc : (s N).fromBase = 0 :=
    (Category.id_comp _).symm.trans
      (hmap.trans ((congrArg ((s 0).fromBase ≫ ·) hvanish).trans comp_zero))
  exact (hinv N le_rfl).2 (by rw [hc, zero_comp])

variable [HasFiniteBiproducts C]

/-- **Finitely many objects are reached by nonzero morphisms.** Let `T` be a class of objects with
local endomorphism rings, each having a left almost split map into a finite biproduct of objects of
`T`, and suppose that the composite of the first `N` links of any sequence of non-isomorphisms
between objects of `T` vanishes. Then the objects of `T` receiving a nonzero morphism from a finite
collection of objects of `T` lie, up to isomorphism, in a finite collection of objects of `T`. -/
theorem exists_finite_forall_iso_of_hom_ne_zero (hlocal : ∀ X, T X → IsLocalRing (End X))
    (hsrc : ∀ X, T X → ∃ (n : ℕ) (F : Fin n → C) (i : X ⟶ ⨁ F),
      (∀ j, T (F j)) ∧ IsLeftAlmostSplit i)
    (N : ℕ) (hN : ∀ (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)), (∀ n, T (X n)) →
      (∀ n, ¬ IsIso (f n)) → (Functor.ofSequence f).map (homOfLE (Nat.zero_le N)) = 0)
    {S₀ : Set C} (hS₀ : S₀.Finite) (hT₀ : ∀ X ∈ S₀, T X) :
    ∃ S : Set C, S.Finite ∧ (∀ Q ∈ S, T Q) ∧
      ∀ Y, T Y → ∀ W ∈ S₀, ∀ f : W ⟶ Y, f ≠ 0 → ∃ Q ∈ S, Nonempty (Y ≅ Q) := by
  choose n F i hF hi using hsrc
  -- The summands of the targets of the left almost split maps.
  let succ : C → Set C := fun X ↦ ⋃ h : T X, Set.range (F X h)
  have hsuccT {X Q : C} (hQ : Q ∈ succ X) : T Q := by
    obtain ⟨h, j, rfl⟩ := Set.mem_iUnion.mp hQ
    exact hF X h j
  have hLT (m : ℕ) : ∀ Q ∈ chainLevel succ S₀ m, T Q := by
    induction m with
    | zero => exact hT₀
    | succ m _ =>
      intro Q hQ
      obtain ⟨_, _, hQ⟩ := Set.mem_iUnion₂.mp hQ
      exact hsuccT hQ
  have hLF (m : ℕ) : (chainLevel succ S₀ m).Finite := by
    induction m with
    | zero => exact hS₀
    | succ m ih => exact ih.biUnion fun X _ ↦ Set.finite_iUnion fun _ ↦ Set.finite_range _
  refine ⟨⋃ m ∈ Set.Iic N, chainLevel succ S₀ m, (Set.finite_Iic N).biUnion fun m _ ↦ hLF m,
    fun Q hQ ↦ ?_, fun Y hY W hW f hf ↦ ?_⟩
  · obtain ⟨m, _, hQ⟩ := Set.mem_iUnion₂.mp hQ
    exact hLT m Q hQ
  have hstep (X : C) (hX : T X) (c : W ⟶ X) (g : X ⟶ Y) (hg : ¬ IsIso g) (hc : c ≫ g ≠ 0) :
      ∃ E ∈ succ X, T E ∧ ∃ (ι : X ⟶ E) (t : E ⟶ Y), ¬ IsIso ι ∧ c ≫ ι ≫ t ≠ 0 := by
    have := hlocal X hX
    have := hlocal Y hY
    obtain ⟨j, t, ht⟩ := (hi X hX).exists_comp_π_comp_ne_zero
      (mem_jacobsonRadical_iff_not_isSplitMono.mp (mem_jacobsonRadical_iff_not_isIso.mpr hg)) hc
    refine ⟨F X hX j, Set.mem_iUnion.mpr ⟨hX, j, rfl⟩, hF X hX j, i X hX ≫ biproduct.π _ j, t,
      fun _ ↦ ?_, ht⟩
    have : IsSplitMono (i X hX) := isSplitMono_of_isSplitMono_comp _ (biproduct.π _ j)
    exact (hi X hX).not_isSplitMono this
  obtain ⟨m, hm, Q, hQ, he⟩ := exists_mem_chainLevel_iso T hlocal succ hstep N hN hW (hT₀ W hW) hf
  exact ⟨Q, Set.mem_iUnion₂.mpr ⟨m, hm, hQ⟩, he⟩

end Chain

end TauCeti
