/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Embedding.Set
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Logic.Equiv.Fin.Basic
-- Non-public: `Finset.countable`, the index of the covering used for countability of `finitary`.
import Mathlib.Logic.Equiv.List

/-!
# Finitely supported permutations

This file records small bridges for Mathlib's finite-support predicate for permutations,
`(MulAction.fixedBy ι π)ᶜ.Finite`, and packages the permutations satisfying it as the **finitary
symmetric group** `Equiv.Perm.finitary ι`, a subgroup of `Equiv.Perm ι`.

The finitary symmetric group on a countable index type is itself countable; countability is what
lets an action of it be handled one group element at a time under a filter closed under countable
intersections (Mathlib's `CountableInterFilter`), such as the a.e. filter of a measure.

The file also supplies `Equiv.Perm.exists_prodCongrRight_mem_finitary_apply_eq_on_finset`:
finitely many values of an arbitrary family of permutations can be matched by a family whose
induced permutation of the product moves only finitely many indexed points altogether; the
type synonym `FinitaryPerm` of the finitary symmetric group of `ℕ`, carrying the domain actions on
path and array spaces that are installed beside those spaces; and the
**block swap** `Nat.blockSwap N`, the finitely supported permutation of `ℕ` exchanging `[0, N)` with
`[N, 2N)`, which carries any finite index set inside `[0, N)` onto a disjoint copy.
-/

public section

namespace TauCeti

/-- Constructor for Mathlib's finite-support predicate from an eventual fixedness bound. -/
theorem finite_compl_fixedBy_of_eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : ∃ N, ∀ n, N ≤ n → π n = n) : (MulAction.fixedBy ℕ π)ᶜ.Finite := by
  rcases hπ with ⟨N, hN⟩
  exact (Set.finite_Iio N).subset fun n hn => by
    by_contra hnN
    have hfixed : n ∈ MulAction.fixedBy ℕ π := by
      simpa [MulAction.mem_fixedBy, Equiv.Perm.smul_def] using hN n (not_lt.mp hnN)
    exact hn hfixed

/-- A permutation of `ℕ` with finite Mathlib support fixes every sufficiently large index. -/
theorem finite_compl_fixedBy_eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) : ∃ N, ∀ n, N ≤ n → π n = n := by
  rcases hπ.bddAbove with ⟨N, hN⟩
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra hne
  have hn_support : n ∈ (MulAction.fixedBy ℕ π)ᶜ := by
    simpa [MulAction.mem_fixedBy, Equiv.Perm.smul_def] using hne
  exact (not_lt_of_ge hn) (Nat.lt_succ_of_le (hN hn_support))

/-- A permutation of `ℕ` is finitely supported iff it fixes all sufficiently large indices. -/
theorem finite_compl_fixedBy_iff_eventually_eq_self {π : Equiv.Perm ℕ} :
    (MulAction.fixedBy ℕ π)ᶜ.Finite ↔ ∃ N, ∀ n, N ≤ n → π n = n :=
  ⟨finite_compl_fixedBy_eventually_eq_self, finite_compl_fixedBy_of_eventually_eq_self⟩

/-- Conjugating a group element preserves Mathlib's finite-support predicate
`(MulAction.fixedBy α ·)ᶜ.Finite`; in particular this applies to conjugation of permutations. -/
theorem finite_compl_fixedBy_conj {G α : Type*} [Group G] [MulAction G α] {g h : G}
    (hh : (MulAction.fixedBy α h)ᶜ.Finite) : (MulAction.fixedBy α (g⁻¹ * h * g))ᶜ.Finite := by
  simpa [Set.smul_set_compl, MulAction.smul_fixedBy] using hh.smul_set (a := g⁻¹)

/-! ## The block swap -/

/-- The finitely supported permutation of `ℕ` that swaps the block `[0, N)` with `[N, 2N)`
pointwise and fixes everything from `2 * N` on: Mathlib's half-swap `finAddFlip` on `Fin (N + N)`,
transported to `ℕ` along the value embedding. -/
def _root_.Nat.blockSwap (N : ℕ) : Equiv.Perm ℕ :=
  Equiv.Perm.viaFintypeEmbedding (finAddFlip (m := N) (n := N)) ⟨Fin.val, Fin.val_injective⟩

/-- On `[0, N)`, `N.blockSwap` shifts by `N`. -/
@[simp]
theorem _root_.Nat.blockSwap_apply_of_lt {N i : ℕ} (hi : i < N) : N.blockSwap i = N + i := by
  have h : (⟨Fin.val, Fin.val_injective⟩ : Fin (N + N) ↪ ℕ)
      (Fin.castAdd N ⟨i, hi⟩) = i := rfl
  rw [Nat.blockSwap, ← h, Equiv.Perm.viaFintypeEmbedding_apply_image, finAddFlip_apply_castAdd]
  rfl

/-- On `[N, 2N)`, `N.blockSwap` shifts back by `N`. -/
@[simp]
theorem _root_.Nat.blockSwap_apply_add_of_lt {N i : ℕ} (hi : i < N) : N.blockSwap (N + i) = i := by
  have h : (⟨Fin.val, Fin.val_injective⟩ : Fin (N + N) ↪ ℕ)
      (Fin.natAdd N ⟨i, hi⟩) = N + i := rfl
  rw [Nat.blockSwap, ← h, Equiv.Perm.viaFintypeEmbedding_apply_image, finAddFlip_apply_natAdd]
  rfl

/-- From `2 * N` on, `N.blockSwap` is the identity. -/
@[simp]
theorem _root_.Nat.blockSwap_apply_of_le {N n : ℕ} (hn : N + N ≤ n) : N.blockSwap n = n := by
  refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ ?_
  rintro ⟨j, rfl⟩
  exact absurd j.isLt (not_lt.mpr hn)

/-- `N.blockSwap` carries any index set inside `[0, N)` off itself: the moved copy lands in
`[N, 2N)`. -/
theorem _root_.Nat.disjoint_map_blockSwap {N : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.range N) :
    Disjoint F (F.map (Equiv.toEmbedding (N.blockSwap))) := by
  rw [Finset.disjoint_left]
  intro a haF hamem
  obtain ⟨b, hbF, hb⟩ := Finset.mem_map.mp hamem
  have hbN : b < N := Finset.mem_range.mp (hF hbF)
  have haN : a < N := Finset.mem_range.mp (hF haF)
  rw [Equiv.coe_toEmbedding, Nat.blockSwap_apply_of_lt hbN] at hb
  omega

/-- `N.blockSwap` is finitely supported. -/
theorem _root_.Nat.finite_compl_fixedBy_blockSwap (N : ℕ) :
    (MulAction.fixedBy ℕ (N.blockSwap))ᶜ.Finite :=
  finite_compl_fixedBy_of_eventually_eq_self ⟨N + N, fun _ hn => Nat.blockSwap_apply_of_le hn⟩

/-- `blockSwap N` is an involution: two swaps restore every index. -/
@[simp]
theorem _root_.Nat.blockSwap_blockSwap (N i : ℕ) : N.blockSwap (N.blockSwap i) = i := by
  rcases lt_or_ge i N with hi | hi
  · rw [Nat.blockSwap_apply_of_lt hi, Nat.blockSwap_apply_add_of_lt hi]
  rcases lt_or_ge i (N + N) with hi2 | hi2
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < N ∧ i = N + j := ⟨i - N, by omega, by omega⟩
    rw [Nat.blockSwap_apply_add_of_lt hj, Nat.blockSwap_apply_of_lt hj]
  · rw [Nat.blockSwap_apply_of_le hi2, Nat.blockSwap_apply_of_le hi2]

/-- `blockSwap N` is its own inverse. -/
@[simp]
theorem _root_.Nat.blockSwap_symm (N : ℕ) : N.blockSwap.symm = N.blockSwap :=
  Equiv.ext fun i => by
    rw [Equiv.symm_apply_eq]
    exact (Nat.blockSwap_blockSwap N i).symm


/-- The self-maps of a countable type that move only finitely many points form a countable set:
such a map is determined by the finite set it moves together with its values there. -/
theorem countable_setOf_finite_ne_id {ι : Type*} [Countable ι] :
    {f : ι → ι | {x | f x ≠ x}.Finite}.Countable := by
  classical
  have hpiece : ∀ s : Finset ι, (Set.range fun g : {x // x ∈ s} → ι => fun x =>
      if hx : x ∈ s then g ⟨x, hx⟩ else x).Countable := fun s => Set.countable_range _
  refine Set.Countable.mono ?_ (Set.countable_iUnion hpiece)
  intro f hf
  refine Set.mem_iUnion.2 ⟨hf.toFinset, ⟨fun x => f x, ?_⟩⟩
  funext x
  by_cases hx : x ∈ hf.toFinset
  · simp [hx]
  · have hfx : f x = x := by simpa using hx
    simp [hx, hfx]

end TauCeti

namespace Equiv.Perm

/-- The **finitary symmetric group** on `ι`: the subgroup of `Equiv.Perm ι` consisting of the
permutations that move only finitely many points, i.e. those satisfying Mathlib's finite-support
predicate `(MulAction.fixedBy ι π)ᶜ.Finite`.

For finite `ι` this is all of `Equiv.Perm ι`; the definition is interesting for infinite index
types, where it is the group generated by the transpositions.

Membership is `mem_finitary`; the structure body is not exposed, so that is the only interface. -/
def finitary (ι : Type*) : Subgroup (Equiv.Perm ι) where
  carrier := {π | (MulAction.fixedBy ι π)ᶜ.Finite}
  one_mem' := by simp
  mul_mem' {π σ} hπ hσ := by
    refine (hπ.union hσ).subset ?_
    simpa only [← Set.compl_inter, Set.compl_subset_compl] using MulAction.fixedBy_mul ι π σ
  inv_mem' {π} hπ := by
    simpa only [Set.mem_ofPred_eq, MulAction.fixedBy_inv ι π] using hπ

@[simp]
theorem mem_finitary {ι : Type*} {π : Equiv.Perm ι} :
    π ∈ finitary ι ↔ (MulAction.fixedBy ι π)ᶜ.Finite :=
  Iff.rfl

/-- The finitary symmetric group on a countable index type is countable: a finitely supported
permutation moves only finitely many points, hence is determined by a finite amount of data. -/
instance {ι : Type*} [Countable ι] : Countable (finitary ι) := by
  have hcountable : Countable {f : ι → ι // {x | f x ≠ x}.Finite} :=
    (TauCeti.countable_setOf_finite_ne_id (ι := ι)).to_subtype
  have hinj : Function.Injective fun π : finitary ι =>
      (⟨⇑(π : Equiv.Perm ι), by
          simpa [MulAction.fixedBy, Equiv.Perm.smul_def, Set.compl_ofPred] using
            mem_finitary.mp π.2⟩ :
        {f : ι → ι // {x | f x ≠ x}.Finite}) := by
    intro π σ hπσ
    exact Subtype.ext (Equiv.coe_fn_injective (congrArg Subtype.val hπσ))
  exact hinj.countable

/-- **A pair of embeddings from a finite type is realised by a permutation supported on their
ranges.** For `f g : ι ↪ β` with `ι` finite there is a permutation of `β` carrying each `f i` to
`g i` and fixing every point outside `Set.range f ∪ Set.range g`.

That union is finite, so `Set.Finite.subset` turns the containment into finite support in the sense
of `(MulAction.fixedBy β σ)ᶜ.Finite`. -/
theorem exists_compl_fixedBy_subset_apply_eq {ι β : Type*} [Finite ι] (f g : ι ↪ β) :
    ∃ σ : Equiv.Perm β,
      (MulAction.fixedBy β σ)ᶜ ⊆ Set.range f ∪ Set.range g ∧ ∀ i, σ (f i) = g i := by
  classical
  set T : Set β := Set.range f ∪ Set.range g
  have : Fintype ↥T := ((Set.finite_range f).union (Set.finite_range g)).fintype
  have hfT : ∀ i, f i ∈ T := fun i => Or.inl ⟨i, rfl⟩
  have hgT : ∀ i, g i ∈ T := fun i => Or.inr ⟨i, rfl⟩
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (f.codRestrict T hfT) (g.codRestrict T hgT)
    (f.codRestrict T hfT).injective (g.codRestrict T hgT).injective
  refine ⟨Equiv.Perm.viaFintypeEmbedding σ (Function.Embedding.subtype _), fun b hb => ?_,
    fun i => ?_⟩
  · by_contra hbT
    refine hb ?_
    simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
    refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range σ _ ?_
    rintro ⟨x, rfl⟩
    exact hbT x.2
  · calc (Equiv.Perm.viaFintypeEmbedding σ (Function.Embedding.subtype _)) (f i)
        = ((σ (f.codRestrict T hfT i) : ↥T) : β) :=
          Equiv.Perm.viaFintypeEmbedding_apply_image σ _ (f.codRestrict T hfT i)
      _ = g i := congrArg Subtype.val (hσ i)

/-- Finite-support form of `Equiv.Perm.exists_compl_fixedBy_subset_apply_eq`: for `f g : ι ↪ β`
with `ι` finite there is a permutation of `β` carrying each `f i` to `g i` whose support is finite.

This is the shape consumers of finitely supported reindexing want, `(MulAction.fixedBy β σ)ᶜ.Finite`
being Mathlib's finite-support predicate. -/
theorem exists_finite_compl_fixedBy_apply_eq {ι β : Type*} [Finite ι] (f g : ι ↪ β) :
    ∃ σ : Equiv.Perm β, (MulAction.fixedBy β σ)ᶜ.Finite ∧ ∀ i, σ (f i) = g i := by
  obtain ⟨σ, hsub, hval⟩ := exists_compl_fixedBy_subset_apply_eq f g
  exact ⟨σ, ((Set.finite_range f).union (Set.finite_range g)).subset hsub, hval⟩

/-- A permutation can be matched on a finite set by a finitely supported permutation. -/
theorem exists_finite_compl_fixedBy_apply_eq_on_finset {β : Type*} (π : Equiv.Perm β)
    (s : Finset β) :
    ∃ σ : Equiv.Perm β, (MulAction.fixedBy β σ)ᶜ.Finite ∧ ∀ b ∈ s, σ b = π b := by
  let f : ↥s ↪ β := Function.Embedding.subtype _
  let g : ↥s ↪ β := f.trans π.toEmbedding
  obtain ⟨σ, hσ, hval⟩ := exists_finite_compl_fixedBy_apply_eq f g
  exact ⟨σ, hσ, fun b hb => by simpa [f, g] using hval ⟨b, hb⟩⟩

/-- The support of a row-wise family, read on the product, is the set of cells that the family
moves in their own row. -/
@[simp]
theorem compl_fixedBy_prodCongrRight {ι β : Type*} {τ : ι → Equiv.Perm β} :
    (MulAction.fixedBy (ι × β) (Equiv.prodCongrRight τ))ᶜ = {p : ι × β | τ p.1 p.2 ≠ p.2} := by
  ext ⟨a, b⟩
  simp [MulAction.mem_fixedBy, Equiv.Perm.smul_def]

/-- **A row-wise family is finitely supported on the product exactly when it is finitely supported
row by row.** The permutation of `ι × β` induced by `τ : ι → Equiv.Perm β` moves only finitely many
cells iff only finitely many rows of `τ` are nontrivial and every row moves only finitely many
points. -/
@[grind =]
theorem mem_finitary_prodCongrRight_iff {ι β : Type*} {τ : ι → Equiv.Perm β} :
    Equiv.prodCongrRight τ ∈ finitary (ι × β) ↔
      {a | τ a ≠ 1}.Finite ∧ ∀ a, τ a ∈ finitary β := by
  classical
  rw [mem_finitary, compl_fixedBy_prodCongrRight]
  constructor
  · intro hτ
    refine ⟨(hτ.image Prod.fst).subset fun a ha => ?_, fun a => ?_⟩
    · by_contra hnot
      apply ha
      ext b
      by_contra hb
      exact hnot ⟨(a, b), hb, rfl⟩
    · have hrow : Prod.mk a ⁻¹' {p : ι × β | τ p.1 p.2 ≠ p.2} = (MulAction.fixedBy β (τ a))ᶜ := by
        ext b
        simp [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
      exact mem_finitary.mpr (hrow ▸ hτ.preimage (Prod.mk_right_injective a).injOn)
  · rintro ⟨hrows, hsupp⟩
    have hS : (⋃ a ∈ {a | τ a ≠ 1}, Prod.mk a '' (MulAction.fixedBy β (τ a))ᶜ).Finite :=
      hrows.biUnion fun a _ => (mem_finitary.mp (hsupp a)).image (Prod.mk a)
    refine hS.subset fun p hp => ?_
    have hrow : τ p.1 ≠ 1 := by
      intro hτ
      simp [hτ] at hp
    refine Set.mem_iUnion.2 ⟨p.1, Set.mem_iUnion.2 ⟨hrow, p.2, ?_, rfl⟩⟩
    simpa [MulAction.mem_fixedBy, Equiv.Perm.smul_def] using hp

/-- **A family of permutations can be matched on finitely many indexed points by a family with
finite total support.** Given `π : ι → Equiv.Perm β` and finitely many pairs `(i, b)`, there is a
family `τ` agreeing with `π` at every listed pair and moving only finitely many pairs altogether. -/
theorem exists_prodCongrRight_mem_finitary_apply_eq_on_finset {ι β : Type*}
    (π : ι → Equiv.Perm β) (F : Finset (ι × β)) :
    ∃ τ : ι → Equiv.Perm β,
      Equiv.prodCongrRight τ ∈ finitary (ι × β) ∧
      ∀ p ∈ F, τ p.1 p.2 = π p.1 p.2 := by
  classical
  let rows : Finset ι := F.image Prod.fst
  have hexists : ∀ a : ι, ∃ σ : Equiv.Perm β,
      (MulAction.fixedBy β σ)ᶜ.Finite ∧
        ∀ b ∈ (F.filter fun q => q.1 = a).image Prod.snd, σ b = π a b := by
    intro a
    exact exists_finite_compl_fixedBy_apply_eq_on_finset (π a) _
  choose σ hσ using hexists
  let τ : ι → Equiv.Perm β := fun a => if a ∈ rows then σ a else 1
  refine ⟨τ, mem_finitary_prodCongrRight_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · refine rows.finite_toSet.subset fun a ha => ?_
    by_contra hnot
    have hnot' : a ∉ rows := by simpa using hnot
    have hτ : τ a = 1 := by simp only [τ, hnot', ↓reduceIte]
    exact ha hτ
  · intro a
    rw [mem_finitary]
    by_cases ha : a ∈ rows
    · simpa [τ, ha] using (hσ a).1
    · simp [τ, ha]
  · intro p hp
    have hrow : p.1 ∈ rows := Finset.mem_image.2 ⟨p, hp, rfl⟩
    have hpfilter : p ∈ F.filter fun q => q.1 = p.1 := Finset.mem_filter.2 ⟨hp, rfl⟩
    have hmem : p.2 ∈ (F.filter fun q => q.1 = p.1).image Prod.snd :=
      Finset.mem_image.2 ⟨p, hpfilter, rfl⟩
    simpa [τ, hrow] using (hσ p.1).2 p.2 hmem

end Equiv.Perm

namespace TauCeti

/-! ## The finitary symmetric group as a type synonym -/

/-- The **finitary symmetric group of `ℕ`**, the group of finitely supported permutations of `ℕ`,
as a type synonym for `↥(Equiv.Perm.finitary ℕ)` carrying the domain actions on path and array
spaces: finitary reindexing of the time index of a path `x : ℕ → α`, and diagonal relabelling of
both coordinates of an array `x : ℕ × ℕ → α`. Each action is installed beside the space it acts
on. The synonym is deliberate: these are actions on the *domain* of a function, whereas
`Pi.instSMul` would make a subgroup of `Equiv.Perm ℕ` act on the *values* whenever the state space
`α` carries an action of it — which it does for `α = ℕ`. Wrapping the group keeps the domain
actions from competing with that one.

The interface is `equivFinitary`, `toPerm`, `ofPerm` and `FinitaryPerm.ext`; no proof outside this
section unfolds the synonym. -/
-- The group structure, and with it `toPerm_one`, `toPerm_mul` and `toPerm_inv`, is transported
-- along the synonym, so those lemmas hold definitionally and by nothing else; the module system
-- therefore requires this definition and `equivFinitary`, `toPerm`, `ofPerm` below to be
-- `@[expose]`d.
@[expose]
def FinitaryPerm : Type := Equiv.Perm.finitary ℕ

namespace FinitaryPerm

instance instGroup : Group FinitaryPerm := inferInstanceAs (Group (Equiv.Perm.finitary ℕ))

instance instCountable : Countable FinitaryPerm :=
  inferInstanceAs (Countable (Equiv.Perm.finitary ℕ))

/-- The identification of `FinitaryPerm` with the finitary symmetric group `Equiv.Perm.finitary ℕ`
that it abbreviates. -/
@[expose]
def equivFinitary : FinitaryPerm ≃ Equiv.Perm.finitary ℕ := Equiv.refl _

/-- The finitely supported permutation of `ℕ` underlying an element of `FinitaryPerm`. -/
@[expose]
def toPerm (g : FinitaryPerm) : Equiv.Perm ℕ := (equivFinitary g).val

/-- The permutation underlying an element of `FinitaryPerm` is finitely supported. -/
theorem finite_compl_fixedBy_toPerm (g : FinitaryPerm) :
    (MulAction.fixedBy ℕ (toPerm g))ᶜ.Finite :=
  Equiv.Perm.mem_finitary.mp (equivFinitary g).2

/-- An element of `FinitaryPerm` is determined by the permutation underlying it. -/
theorem toPerm_injective : Function.Injective toPerm := fun _ _ h =>
  equivFinitary.injective (Subtype.ext h)

@[ext]
theorem ext {g h : FinitaryPerm} (hgh : toPerm g = toPerm h) : g = h := toPerm_injective hgh

/-- Package a finitely supported permutation of `ℕ` as an element of `FinitaryPerm`. -/
@[expose]
def ofPerm (π : Equiv.Perm ℕ) (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) : FinitaryPerm :=
  equivFinitary.symm ⟨π, Equiv.Perm.mem_finitary.mpr hπ⟩

@[simp]
theorem toPerm_ofPerm (π : Equiv.Perm ℕ) (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) :
    toPerm (ofPerm π hπ) = π :=
  rfl

@[simp]
theorem toPerm_one : toPerm 1 = 1 := rfl

@[simp]
theorem toPerm_mul (g h : FinitaryPerm) : toPerm (g * h) = toPerm g * toPerm h := rfl

@[simp]
theorem toPerm_inv (g : FinitaryPerm) : toPerm g⁻¹ = (toPerm g)⁻¹ := rfl

end FinitaryPerm

end TauCeti
