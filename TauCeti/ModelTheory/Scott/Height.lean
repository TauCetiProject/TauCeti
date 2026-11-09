/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.Scott.Rank
public import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# External stabilization and the Scott height

A structure `M` **stabilizes completely** at `α` when, for every countable structure `N` in
`Type`, finite or empty ones included, and for tuples of every length, back-and-forth equivalence
at `α` between a tuple of `M` and a tuple of `N` upgrades to equivalence at `α + 1`. Unlike
the internal stabilization `SelfStabilizesCompletely`, the partner tuple lies in another
structure. The **Scott height** `scottHeight M` is the least such level, an ordinal in the universe
of `M`.

The height is what makes back-and-forth equivalence of countable structures decide
isomorphism at a single level: for countable `M` and `N`, `M ≅ N` exactly when their empty
tuples are equivalent at `scottHeight M`. It is an isomorphism invariant, and it is countable
for countable `M`, because it lies within `ω` of the internal stabilization level: if `M`
stabilizes internally at `α`, it stabilizes externally at every limit level above `α`, in
particular at `α + ω`. Hence `scottHeight M ≤ internalScottRank M + ω`.

The comparison partners range over countable structures in `Type` only. Every countable
structure in any universe is isomorphic to one of these, so the isomorphism criterion holds for
countable partners in every universe.

## Main definitions

* `TauCeti.StabilizesCompletely M α`: external one-step stabilization of `M` at `α`.
* `TauCeti.scottHeight M`: the least externally stabilizing level.

## Main results

* `TauCeti.StabilizesCompletely.bfEquiv_of_le`: external stabilization propagates to all later
  levels.
* `TauCeti.SelfStabilizesCompletely.stabilizesCompletely_of_isSuccLimit`: internal stabilization
  at `α` gives external stabilization at every limit above `α`.
* `TauCeti.scottHeight_le_internalScottRank_add_omega0` and `TauCeti.scottHeight_lt_omega_one`.
* `FirstOrder.Language.Equiv.scottHeight_eq`: the Scott height is an isomorphism invariant.
* `TauCeti.nonempty_equiv_of_bfEquiv_of_scottHeight_le` and
  `TauCeti.nonempty_equiv_iff_bfEquiv_scottHeight`: for countable structures, equivalence at the
  Scott height decides isomorphism.

## References

* Dana Scott, Logic with denumerably long formulas and finite strings of quantifiers, 1965.
* Cameron Freer's `cameronfreer/infinitary-logic`, checkpoint
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Scott/Height/Defs.lean` and
  `InfinitaryLogic/Scott/InternalRankBounds.lean`, defines a Scott height by external
  stabilization against countable partners in the universe of the structure and proves
  `lift_scottHeight_le_internalScottRank_add_omega0`. Here the partners live in `Type`, the
  height lives in the universe of the structure, and the bound by the internal rank plus `ω`
  comes from a direct back-and-forth argument.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder Fin
open scoped Ordinal

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]

variable (M) in
/-- `M` stabilizes completely at `α`: for every countable structure `N` in `Type` and tuples of
every length, back-and-forth equivalence at `α` between a tuple of `M` and a tuple of `N`
implies equivalence at `α + 1`. -/
def StabilizesCompletely (α : Ordinal.{o}) : Prop :=
  ∀ (N : Type) [L.Structure N] [Countable N] (n : ℕ) (a : Fin n → M) (b : Fin n → N),
    BFEquiv (L := L) α n a b → BFEquiv (L := L) (α + 1) n a b

variable (M) in
/-- External stabilization is one-step stabilization against every countable structure in
`Type`, at every tuple length. -/
theorem stabilizesCompletely_def (α : Ordinal.{o}) :
    StabilizesCompletely (L := L) M α ↔
      ∀ (N : Type) [L.Structure N] [Countable N] (n : ℕ) (a : Fin n → M) (b : Fin n → N),
        BFEquiv (L := L) α n a b → BFEquiv (L := L) (α + 1) n a b := Iff.rfl

namespace StabilizesCompletely

/-- External stabilization at `α` makes equivalence at `α` with a countable structure in `Type`
persist at every later level. -/
theorem bfEquiv_of_le {α β : Ordinal.{o}} (h : StabilizesCompletely (L := L) M α) (hαβ : α ≤ β)
    {N : Type} [L.Structure N] [Countable N] {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hab : BFEquiv (L := L) α n a b) : BFEquiv (L := L) β n a b :=
  bfEquiv_of_le_of_forall_add_one (h N) hαβ hab

/-- Every level above an externally stabilizing level is itself externally stabilizing. -/
theorem mono {α β : Ordinal.{o}} (h : StabilizesCompletely (L := L) M α) (hαβ : α ≤ β) :
    StabilizesCompletely (L := L) M β :=
  fun _ _ _ _ _ _ hab => h.bfEquiv_of_le (hαβ.trans le_self_add) (hab.mono hαβ)

end StabilizesCompletely

namespace SelfStabilizesCompletely

variable {α : Ordinal.{o}}

/-- Internal stabilization at `α` gives external stabilization at every limit above `α`. -/
theorem stabilizesCompletely_of_isSuccLimit (h : SelfStabilizesCompletely (L := L) M α)
    {β : Ordinal.{o}} (hβ : Order.IsSuccLimit β) (hαβ : α < β) :
    StabilizesCompletely (L := L) M β :=
  fun _ _ _ _ _ _ hab => h.bfEquiv_add_one_of_isSuccLimit hβ hαβ hab

/-- Internal stabilization at `α` gives external stabilization at `α + ω`. -/
theorem stabilizesCompletely_add_omega0 (h : SelfStabilizesCompletely (L := L) M α) :
    StabilizesCompletely (L := L) M (α + ω) :=
  h.stabilizesCompletely_of_isSuccLimit (Ordinal.isSuccLimit_add α Ordinal.isSuccLimit_omega0)
    (lt_add_of_pos_right α Ordinal.omega0_pos)

end SelfStabilizesCompletely

variable (M)

/-- Every structure stabilizes externally at some ordinal in its own universe. -/
theorem exists_stabilizesCompletely : ∃ α : Ordinal.{w}, StabilizesCompletely (L := L) M α :=
  ⟨_,
    (selfStabilizesCompletely_selfStabilizationOrdinal (L := L) M).stabilizesCompletely_add_omega0⟩

/-- The **Scott height** of `M`: the least ordinal, in the universe of `M`, at which `M`
stabilizes externally against every countable structure in `Type`. -/
noncomputable def scottHeight : Ordinal.{w} :=
  sInf {α | StabilizesCompletely (L := L) M α}

/-- The Scott height is the infimum of the externally stabilizing levels. -/
theorem scottHeight_def :
    scottHeight (L := L) M = sInf {α | StabilizesCompletely (L := L) M α} :=
  (rfl)

/-- The infimum defining the Scott height is attained. -/
@[simp]
theorem stabilizesCompletely_scottHeight :
    StabilizesCompletely (L := L) M (scottHeight (L := L) M) :=
  csInf_mem (s := {α : Ordinal.{w} | StabilizesCompletely (L := L) M α})
    (exists_stabilizesCompletely (L := L) M)

variable {M}

/-- The Scott height is no larger than any externally stabilizing level. -/
theorem scottHeight_le {α : Ordinal.{w}} (h : StabilizesCompletely (L := L) M α) :
    scottHeight (L := L) M ≤ α :=
  csInf_le' h

variable (M)

/-- A level stabilizes externally exactly when it is at least the Scott height. -/
theorem scottHeight_le_iff {α : Ordinal.{w}} :
    scottHeight (L := L) M ≤ α ↔ StabilizesCompletely (L := L) M α :=
  ⟨(stabilizesCompletely_scottHeight (L := L) M).mono, scottHeight_le⟩

/-- The Scott height is within `ω` of the least internal stabilization level. -/
theorem scottHeight_le_selfStabilizationOrdinal_add_omega0 :
    scottHeight (L := L) M ≤ selfStabilizationOrdinal (L := L) M + ω :=
  scottHeight_le
    (selfStabilizesCompletely_selfStabilizationOrdinal (L := L) M).stabilizesCompletely_add_omega0

/-- The Scott height is within `ω` of the internal Scott rank. -/
theorem scottHeight_le_internalScottRank_add_omega0 :
    scottHeight (L := L) M ≤ internalScottRank (L := L) M + ω :=
  (scottHeight_le_selfStabilizationOrdinal_add_omega0 M).trans
    (add_le_add_left (selfStabilizationOrdinal_le_internalScottRank (L := L)) ω)

/-- The Scott height of a countable structure is a countable ordinal. The relational language
need not be countable. -/
theorem scottHeight_lt_omega_one [Countable M] : scottHeight (L := L) M < ω₁ :=
  (scottHeight_le_selfStabilizationOrdinal_add_omega0 M).trans_lt
    (Ordinal.isPrincipal_add_omega 1 (selfStabilizationOrdinal_lt_omega_one (L := L) M)
      Ordinal.omega0_lt_omega_one)

variable {M}

/-- **Equivalence at the Scott height decides isomorphism.** If `M` and `N` are countable, in
any universes, and their empty tuples are back-and-forth equivalent at a level at least the
Scott height of `M`, then `M` and `N` are isomorphic. -/
theorem nonempty_equiv_of_bfEquiv_of_scottHeight_le [Countable M] {N : Type w'}
    [L.Structure N] [Countable N] {β : Ordinal.{w}} (hβ : scottHeight (L := L) M ≤ β)
    (h : BFEquiv (L := L) β 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  -- Transport `N` to a countable copy in `Type`, against which `M` stabilizes at `β`.
  let e : N ≃ Shrink.{0} N := equivShrink.{0, w'} N
  let _ : L.Structure (Shrink.{0} N) := e.inducedStructure
  have : Countable (Shrink.{0} N) := Countable.of_equiv N e
  let f : N ≃[L] Shrink.{0} N := e.inducedStructureEquiv
  have h' : BFEquiv (L := L) β 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → Shrink.{0} N) := by
    simpa only [Subsingleton.elim (f ∘ Fin.elim0) Fin.elim0] using h.trans (f.bfEquiv β _)
  have hall : ∀ γ : Ordinal.{w},
      BFEquiv (L := L) γ 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → Shrink.{0} N) := by
    intro γ
    rcases le_total β γ with hγ | hγ
    · exact ((scottHeight_le_iff M).mp hβ).bfEquiv_of_le hγ h'
    · exact h'.mono hγ
  obtain ⟨g⟩ := countable_potentialIso_iff_iso.mp (potentialIso_iff_bfEquiv_all.mpr hall)
  exact ⟨f.symm.comp g⟩

/-- **Isomorphism is equivalence at the Scott height.** Two countable structures, in any
universes, are isomorphic exactly when their empty tuples are back-and-forth equivalent at the
Scott height of the first. -/
theorem nonempty_equiv_iff_bfEquiv_scottHeight [Countable M] {N : Type w'} [L.Structure N]
    [Countable N] :
    Nonempty (M ≃[L] N) ↔
      BFEquiv (L := L) (scottHeight (L := L) M) 0 (Fin.elim0 : Fin 0 → M)
        (Fin.elim0 : Fin 0 → N) := by
  refine ⟨fun ⟨e⟩ => ?_, nonempty_equiv_of_bfEquiv_of_scottHeight_le le_rfl⟩
  simpa only [Subsingleton.elim (e ∘ Fin.elim0) Fin.elim0] using e.bfEquiv _ Fin.elim0

end TauCeti

namespace FirstOrder.Language.Equiv

open TauCeti

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- External stabilization transfers along an isomorphism. -/
private theorem stabilizesCompletely_of_equiv {α : Ordinal.{o}}
    (h : StabilizesCompletely (L := L) M α) (e : M ≃[L] N) : StabilizesCompletely (L := L) N α := by
  -- Pull the tuple back along `e`, stabilize in `M`, and push the result forward.
  intro P _ _ n a b hab
  have ha : BFEquiv (L := L) α n a (e.symm ∘ a) := e.symm.bfEquiv α a
  have ha' : BFEquiv (L := L) (α + 1) n a (e.symm ∘ a) := e.symm.bfEquiv (α + 1) a
  exact ha'.trans (h P n _ b (ha.symm.trans hab))

/-- External stabilization at a level is invariant under isomorphism. -/
theorem stabilizesCompletely_iff (e : M ≃[L] N) {α : Ordinal.{o}} :
    StabilizesCompletely (L := L) M α ↔ StabilizesCompletely (L := L) N α :=
  ⟨fun h => stabilizesCompletely_of_equiv h e, fun h => stabilizesCompletely_of_equiv h e.symm⟩

/-- The Scott height is an isomorphism invariant. -/
theorem scottHeight_eq {N : Type w} [L.Structure N] (e : M ≃[L] N) :
    scottHeight (L := L) M = scottHeight (L := L) N := by
  simp only [scottHeight_def, e.stabilizesCompletely_iff]

end FirstOrder.Language.Equiv
