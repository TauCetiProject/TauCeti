/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.BackAndForth
public import TauCeti.ModelTheory.Counting.Stratification
import TauCeti.ModelTheory.BackAndForth.PureSet
import TauCeti.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# A countable structure of internal Scott rank `ω` whose `ω`-class has continuum-many models

This file constructs the prefix row assembly `PrefixModel` over `ℕ` with pure-set fibers
(`Lc = Language.empty`) and its Cantor-indexed family of non-isomorphic companions
`CompanionModel z` (`z : ℕ → Bool`), proving:

* `internalScottRank_prefixModel`: `internalScottRank PrefixModel = ω` (and
  `selfStabilizationOrdinal PrefixModel = ω`);
* `bfEquiv_omega0_companionModel_prefixModel`: every `CompanionModel z` is back-and-forth
  equivalent to `PrefixModel` at ordinal level `ω`;
* `isEmpty_equiv_companionModel_prefixModel` and `isEmpty_equiv_companionModel_of_ne`: none of the
  `CompanionModel z` is isomorphic to `PrefixModel`, and distinct binary sequences yield
  non-isomorphic companions;
* `omega0_lt_scottHeight_prefixModel` and `scottHeight_prefixModel_le`:
  `ω < scottHeight PrefixModel ≤ ω + ω`;
* `exists_internalScottRank_omega_with_large_bfClass`: existential witness form;
* `not_isIsolatingRank_internalScottRank`: the internal Scott rank on configurations on `ℕ` is not
  an isolating rank (although it is isomorphism-invariant and countable, it fails one-sided
  isolation at `prefixModelCode`);
* `IsIsolatingRank.omega0_lt_prefixModelCode` and
  `mk_quotient_comap_isoSetoid_bfClass_prefixModelCode`: every isolating rank strictly exceeds `ω`
  at `prefixModelCode`, whose `ω`-level back-and-forth class splits into `𝔠` isomorphism classes.

## Construction

An admissible row (`Row`) is a nondecreasing word `p : List ℕ` satisfying `p[i] ≤ i` at every
index `i < p.length`. In `PrefixModel = Carrier Row BaseFiber`, the fiber at `(p, τ)` is the
finite pure set `Fin (last τ + 1)` when `τ.1` is a prefix of `p.1`, and the infinite pure set `ℕ`
otherwise. Because `last τ ≤ τ.length - 1`, any row `p` of length `L` is pinned among rows of
`PrefixModel` at back-and-forth depth `L + 2`, bounding every finite tuple's orbit rank below `ω`;
conversely, extending `List.range (k + 1)` by `[k]` shows no finite level stabilizes all rows.

Each `z : ℕ → Bool` defines a nondecreasing path `pathOf z` (`pathOf z (2 * n) = n`,
`pathOf z (2 * n + 1) = n + (z n).toNat`) and adds one infinite-path row `none : Option Row` whose
finite fibers sit along the prefixes of `pathOf z`. At any finite depth `m`, a Hilbert-hotel
bijection absorbing `none` into `pathPrefix z (2 * m)` matches every fiber up to depth `m` because
diverging fibers have `last τ ≥ pathOf z (2 * m) = m`.

## References

* Adapted from `InfinitaryLogic/Examples/ScottRankOmega.lean` and
  `InfinitaryLogic/ModelTheory/PrefixAssembly.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0); see also David Marker, *Lectures on Infinitary Model Theory*, Cambridge University
  Press, 2016, and Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*,
  Cambridge University Press, 2021, for structures of limit Scott rank `ω` with non-isomorphic
  `≡_ω`-companions (the high-Scott-rank / non-isolated phenomenon at limit ordinals).
-/

public section

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language Fin Cardinal Ordinal

/-! ### Pure-set fibers controlled by a Boolean flag -/

/-- Pure-set fiber attached to label `τ : Label ℕ` according to a Boolean flag `b`: when `b = true`
it is the finite set `Fin (τ.1.getLast τ.2 + 1)`, and when `b = false` it is `ℕ`. -/
def FiberType : Bool → Label ℕ → Type
  | true, τ => Fin (τ.1.getLast τ.2 + 1)
  | false, _ => ℕ

instance instStructureFiberType (b : Bool) (τ : Label ℕ) :
    Language.empty.Structure (FiberType b τ) :=
  Language.emptyStructure

instance instCountableFiberType (b : Bool) (τ : Label ℕ) : Countable (FiberType b τ) := by
  cases b <;> dsimp [FiberType] <;> infer_instance

private theorem bfEquiv_fiberType_of_le (b₁ b₂ : Bool) (τ : Label ℕ) {k : ℕ}
    (hk : k ≤ τ.1.getLast τ.2 + 1) :
    BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType b₁ τ) (Fin.elim0 : Fin 0 → FiberType b₂ τ) := by
  have hft : BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType false τ) (Fin.elim0 : Fin 0 → FiberType true τ) := by
    have : Infinite (FiberType false τ) := inferInstanceAs (Infinite ℕ)
    rw [bfEquiv_empty_elim0_natCast_iff_le_card]
    simp only [FiberType, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    exact_mod_cast hk
  cases b₁ <;> cases b₂
  · exact BFEquiv.refl _ _
  · exact hft
  · exact hft.symm
  · exact BFEquiv.refl _ _

private theorem not_bfEquiv_fiberType_of_lt {b₁ b₂ : Bool} (hb : b₁ ≠ b₂) (τ : Label ℕ) {k : ℕ}
    (hk : τ.1.getLast τ.2 + 1 < k) :
    ¬ BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType b₁ τ) (Fin.elim0 : Fin 0 → FiberType b₂ τ) := by
  have hft : ¬ BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType false τ) (Fin.elim0 : Fin 0 → FiberType true τ) := by
    have : Infinite (FiberType false τ) := inferInstanceAs (Infinite ℕ)
    rw [bfEquiv_empty_elim0_natCast_iff_le_card, not_le]
    simp only [FiberType, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    exact_mod_cast hk
  cases b₁ <;> cases b₂
  · exact absurd rfl hb
  · exact hft
  · exact fun h => hft h.symm
  · exact absurd rfl hb

private theorem eq_of_fiberType_equiv {b₁ b₂ : Bool} {τ : Label ℕ}
    (e : FiberType b₁ τ ≃ FiberType b₂ τ) : b₁ = b₂ := by
  have : Infinite (FiberType false τ) := inferInstanceAs (Infinite ℕ)
  cases b₁ <;> cases b₂
  · rfl
  · exact False.elim ((not_infinite_iff_finite.mpr
      (inferInstanceAs (Finite (Fin (τ.1.getLast τ.2 + 1)))))
      (Infinite.of_injective e e.injective))
  · exact False.elim ((not_infinite_iff_finite.mpr
      (inferInstanceAs (Finite (Fin (τ.1.getLast τ.2 + 1)))))
      (Infinite.of_injective e.symm e.symm.injective))
  · rfl

/-! ### Admissible rows and the prefix row assembly `PrefixModel` -/

/-- A word `l : List ℕ` is admissible when it is nondecreasing and satisfies `l[i] ≤ i` at every
position `i < l.length`. -/
def IsAdmissible (l : List ℕ) : Prop :=
  (∀ ⦃i j : ℕ⦄ (hi : i < l.length) (hj : j < l.length), i ≤ j → l[i] ≤ l[j]) ∧
    ∀ ⦃i : ℕ⦄ (hi : i < l.length), l[i] ≤ i

/-- Admissible finite words over `ℕ`, indexing the rows of `PrefixModel`. -/
abbrev Row : Type := {l : List ℕ // IsAdmissible l}

private theorem isAdmissible_take {l : List ℕ} (hl : IsAdmissible l) (k : ℕ) :
    IsAdmissible (l.take k) := by
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · simp only [List.getElem_take]
    exact hl.1 (by simp only [List.length_take] at hi; omega)
      (by simp only [List.length_take] at hj; omega) hij
  · simp only [List.getElem_take]
    exact hl.2 (by simp only [List.length_take] at hi; omega)

private theorem getLast_le_pred_length {l : List ℕ} (hl : IsAdmissible l) (hne : l ≠ []) :
    l.getLast hne ≤ l.length - 1 := by
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  rw [List.getLast_eq_getElem]
  exact hl.2 (by omega)

private theorem isAdmissible_range (m : ℕ) : IsAdmissible (List.range m) :=
  ⟨fun _ _ _ _ hij => by simpa using hij, fun _ _ => by simp⟩

instance instInfiniteRow : Infinite Row :=
  Infinite.of_injective (fun m : ℕ => (⟨List.range m, isAdmissible_range m⟩ : Row)) fun a b h => by
    simpa using congrArg (fun r : Row => r.1.length) h

/-- Component pure-set fibers of `PrefixModel`: finite of size `last τ + 1` when `τ.1 <+: p.1`,
and `ℕ` otherwise. -/
abbrev BaseFiber (p : Row) (τ : Label ℕ) : Type :=
  FiberType (decide (τ.1 <+: p.1)) τ

/-- The prefix row assembly over `ℕ` with pure-set fibers, having internal Scott rank `ω`. -/
abbrev PrefixModel : Type := Carrier Row BaseFiber

/-! ### Row pinning and internal Scott rank `ω` of `PrefixModel` -/

/-- Any row `p₁` of `PrefixModel` is uniquely determined among rows of `PrefixModel` by
back-and-forth equivalence at finite depth `p₁.1.length + 2`. -/
private theorem row_eq_of_bfEquiv {N : ℕ} {a b : Fin N → PrefixModel} {i₀ : Fin N}
    {p₁ p₂ : Row} (ha₀ : a i₀ = .row p₁) (hb₀ : b i₀ = .row p₂)
    (h : BFEquiv (L := lang ℕ Language.empty) ((p₁.1.length + 2 : ℕ) : Ordinal.{0}) N a b) :
    p₁ = p₂ := by
  have hpref : p₁.1 <+: p₂.1 := by
    by_contra hnp
    have hne : p₁.1 ≠ [] := fun he => hnp (he ▸ List.nil_prefix)
    let τ : Label ℕ := ⟨p₁.1, hne⟩
    have hf := bfEquiv_fiber_elim0_of_row_eq h ha₀ hb₀ τ
    have hlast : τ.1.getLast τ.2 + 1 < p₁.1.length + 2 := by
      have hle := getLast_le_pred_length p₁.2 hne
      have hpos : 0 < p₁.1.length := List.length_pos_iff.mpr hne
      dsimp only [τ]
      omega
    exact not_bfEquiv_fiberType_of_lt (by simp [τ, hnp]) τ hlast hf
  have hlen : p₂.1.length ≤ p₁.1.length := by
    by_contra hlt
    have hlt' : p₁.1.length < p₂.1.length := Nat.lt_of_not_ge hlt
    let l := p₂.1.take (p₁.1.length + 1)
    have hllen : l.length = p₁.1.length + 1 := by simp [l]; omega
    have hne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
    let τ : Label ℕ := ⟨l, hne⟩
    have hf := bfEquiv_fiber_elim0_of_row_eq h ha₀ hb₀ τ
    have hnp₁ : ¬ (l <+: p₁.1) := fun hp => by
      have := hp.length_le
      omega
    have hp₂ : l <+: p₂.1 := List.take_prefix _ _
    have hlast : τ.1.getLast τ.2 + 1 < p₁.1.length + 2 := by
      have hle : τ.1.getLast τ.2 ≤ l.length - 1 :=
        getLast_le_pred_length (isAdmissible_take p₂.2 (p₁.1.length + 1)) hne
      omega
    exact not_bfEquiv_fiberType_of_lt (by simp [τ, hnp₁, hp₂]) τ hlast hf
  obtain ⟨t, ht⟩ := hpref
  have htl : t = [] := List.eq_nil_of_length_eq_zero (by
    have := congrArg List.length ht
    simp only [List.length_append] at this
    omega)
  rw [htl, List.append_nil] at ht
  exact Subtype.ext ht

/-- Given tuples `a` and `b` in `PrefixModel` with matching owner rows, matching optional labels,
and the same atomic type, an automorphism of `PrefixModel` fixing every row carries `a` to `b`. -/
private theorem exists_aut_comp_eq_of_ownerRow_eq {n : ℕ} {a b : Fin n → PrefixModel}
    (hsat : SameAtomicType (L := lang ℕ Language.empty) a b)
    (hrow : ∀ i, (b i).ownerRow = (a i).ownerRow) :
    ∃ g : PrefixModel ≃[lang ℕ Language.empty] PrefixModel, g ∘ a = b := by
  classical
  have hlab : ∀ i, (b i).label? = (a i).label? := fun i => (label?_eq_of_sameAtomicType hsat i).symm
  have hfib : ∀ (p : Row) (τ : Label ℕ),
      ∃ f : BaseFiber p τ ≃[Language.empty] BaseFiber p τ,
        ∀ (i : Fin n) (x y : BaseFiber p τ),
          a i = .pt p τ x → b i = .pt p τ y → f x = y := by
    intro p τ
    let P : Fin n → Prop := fun i => (a i).ownerRow = p ∧ (a i).label? = some τ
    let e₀ : Fin (Fintype.card {i : Fin n // P i}) ≃ {i : Fin n // P i} :=
      (Fintype.equivFin {i : Fin n // P i}).symm
    choose xs hxs using fun q => Carrier.ownerRow_eq_and_label?_eq_some_iff.mp (e₀ q).2
    choose ys hys using fun q => Carrier.ownerRow_eq_and_label?_eq_some_iff.mp
      ⟨(hrow (e₀ q).1).trans (e₀ q).2.1, (hlab (e₀ q).1).trans (e₀ q).2.2⟩
    have heq_iff : ∀ q₁ q₂, xs q₁ = xs q₂ ↔ ys q₁ = ys q₂ := fun q₁ q₂ => by
      rw [← (Carrier.pt_injective p τ).eq_iff, ← hxs q₁, ← hxs q₂,
        hsat.eq_iff (e₀ q₁).1 (e₀ q₂).1, hys q₁, hys q₂, (Carrier.pt_injective p τ).eq_iff]
    obtain ⟨π, -, hπ⟩ := exists_perm_apply_eq_of_eq_iff (fun _ : BaseFiber p τ => ()) heq_iff
      fun _ => rfl
    refine ⟨{ toEquiv := π }, fun i x y hai hbi => ?_⟩
    let q := e₀.symm ⟨i, by simp [P, hai]⟩
    have hqi : (e₀ q).1 = i := congrArg Subtype.val (e₀.apply_symm_apply _)
    have hx : xs q = x := Carrier.pt_injective p τ ((hqi ▸ hxs q).symm.trans hai)
    have hy : ys q = y := Carrier.pt_injective p τ ((hqi ▸ hys q).symm.trans hbi)
    exact hx ▸ hy ▸ hπ q
  choose f hf using hfib
  refine ⟨equivOfFibers (Equiv.refl Row) f, funext fun i => ?_⟩
  cases hai : a i with
  | row p =>
    have hb := Carrier.label?_eq_none_iff.mp (by rw [hlab i, hai, Carrier.label?_row])
    rw [hrow i, hai, Carrier.ownerRow_row] at hb
    rw [Function.comp_apply, hai, hb]
    exact equivOfFibers_row (Equiv.refl Row) f p
  | pt p τ x =>
    obtain ⟨y, hbi⟩ := Carrier.ownerRow_eq_and_label?_eq_some_iff.mp
      ⟨by rw [hrow i, hai, Carrier.ownerRow_pt], by rw [hlab i, hai, Carrier.label?_pt]⟩
    rw [Function.comp_apply, hai, hbi]
    exact (equivOfFibers_pt (Equiv.refl Row) f p τ x).trans
      (congrArg (Carrier.pt p τ) (hf p τ i x y hai hbi))

private theorem internalScottRank_prefixModel_le :
    internalScottRank (L := lang ℕ Language.empty) PrefixModel ≤ Ordinal.omega0 := by
  rw [internalScottRank_le_iff]
  intro n a
  let r : ℕ := Finset.sup Finset.univ fun i : Fin n => (a i).ownerRow.1.length
  let K : ℕ := (r + 2) + n
  refine (orbitRank_le a ?_).trans_lt (Ordinal.natCast_lt_omega0 K)
  rw [mem_orbitStable_iff]
  intro b hab β
  have hab' : BFEquiv (L := lang ℕ Language.empty)
      (((r + 2 : ℕ) : Ordinal.{0}) + n) n a b := by
    simpa [K, Nat.cast_add] using hab
  have happ := bfEquiv_append_ownerRow hab'
  have hrow : ∀ i : Fin n, (b i).ownerRow = (a i).ownerRow := fun i => by
    have hle : (a i).ownerRow.1.length + 2 ≤ r + 2 :=
      Nat.add_le_add_right (Finset.le_sup (f := fun j : Fin n => (j |> a).ownerRow.1.length)
        (Finset.mem_univ i)) 2
    exact (row_eq_of_bfEquiv (i₀ := natAdd n i) (by simp only [append_right])
      (by simp only [append_right]) (happ.mono (Nat.cast_le.mpr hle))).symm
  obtain ⟨g, rfl⟩ := exists_aut_comp_eq_of_ownerRow_eq hab.sameAtomicType hrow
  exact g.bfEquiv β a

private theorem isAdmissible_range_snoc (k : ℕ) :
    IsAdmissible (List.range (k + 1) ++ [k]) := by
  have hget : ∀ i (hi : i < (List.range (k + 1) ++ [k]).length),
      (List.range (k + 1) ++ [k])[i] = if i < k + 1 then i else k := fun i hi => by
    have hi' : i < k + 2 := by simp at hi; omega
    rw [List.getElem_append]
    simp only [List.length_range]
    split_ifs with hlt
    · simp
    · obtain rfl : i = k + 1 := by omega
      simp
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · rw [hget i hi, hget j hj]
    split_ifs <;> omega
  · rw [hget i hi]
    split_ifs <;> omega

private theorem omega0_le_selfStabilizationOrdinal_prefixModel :
    Ordinal.omega0 ≤ selfStabilizationOrdinal (L := lang ℕ Language.empty) PrefixModel := by
  refine Ordinal.omega0_le.mpr fun k => ?_
  let p₁ : Row := ⟨List.range (k + 1), isAdmissible_range (k + 1)⟩
  let p₂ : Row := ⟨List.range (k + 1) ++ [k], isAdmissible_range_snoc k⟩
  have hpne : p₁ ≠ p₂ := fun h => by
    have := congrArg (fun r : Row => r.1.length) h
    simp [p₁, p₂] at this
  let σ : Row ≃ Row := Equiv.swap p₁ p₂
  have hfib : ∀ (r : Row) (τ : Label ℕ), BFEquiv (L := Language.empty) ((k + 1 : ℕ) : Ordinal.{0})
      0 (Fin.elim0 : Fin 0 → BaseFiber r τ) (Fin.elim0 : Fin 0 → BaseFiber (σ r) τ) := by
    intro r τ
    by_cases hτ : τ.1 = p₂.1
    · have hlast : τ.1.getLast τ.2 = k := by simp [hτ, p₂]
      exact bfEquiv_fiberType_of_le _ _ τ (by omega)
    · have hd : decide (τ.1 <+: p₁.1) = decide (τ.1 <+: p₂.1) := by
        simp [p₁, p₂, List.prefix_concat_iff, hτ]
      by_cases hr₁ : r = p₁
      · subst hr₁
        rw [Equiv.swap_apply_left]
        dsimp only [BaseFiber]
        rw [hd]
      · by_cases hr₂ : r = p₂
        · subst hr₂
          rw [Equiv.swap_apply_right]
          dsimp only [BaseFiber]
          rw [← hd]
        · rw [Equiv.swap_apply_of_ne_of_ne hr₁ hr₂]
  let a : Fin 1 → PrefixModel := fun _ => .row p₁
  let b : Fin 1 → PrefixModel := fun _ => .row p₂
  have hab : BFEquiv (L := lang ℕ Language.empty) ((k + 1 : ℕ) : Ordinal.{0}) 1 a b := by
    simpa [a, b, σ, Equiv.swap_apply_left] using
      bfEquiv_row_of_rowEquiv σ ((k + 1 : ℕ) : Ordinal.{0}) (fun _ : Fin 1 => p₁) hfib
  have hnot : ((k + 1 : ℕ) : Ordinal.{0}) ∉ orbitStable (L := lang ℕ Language.empty) a := by
    rw [mem_orbitStable_iff]
    intro hst
    exact hpne (row_eq_of_bfEquiv (i₀ := 0) rfl rfl
      (hst b hab ((p₁.1.length + 2 : ℕ) : Ordinal.{0})))
  have hlt : ((k + 1 : ℕ) : Ordinal.{0}) < orbitRank (L := lang ℕ Language.empty) a := by
    rwa [← not_le, orbitRank_le_iff]
  exact ((Nat.cast_le.mpr (Nat.le_succ k)).trans hlt.le).trans
    (orbitRank_le_selfStabilizationOrdinal a)

/-- The simultaneous internal stabilization ordinal of `PrefixModel` is `ω`. -/
theorem selfStabilizationOrdinal_prefixModel :
    selfStabilizationOrdinal (L := lang ℕ Language.empty) PrefixModel = Ordinal.omega0 :=
  le_antisymm
    (selfStabilizationOrdinal_le_internalScottRank.trans internalScottRank_prefixModel_le)
    omega0_le_selfStabilizationOrdinal_prefixModel

/-- `PrefixModel` has internal Scott rank `ω`. -/
theorem internalScottRank_prefixModel :
    internalScottRank (L := lang ℕ Language.empty) PrefixModel = Ordinal.omega0 :=
  le_antisymm internalScottRank_prefixModel_le
    (omega0_le_selfStabilizationOrdinal_prefixModel.trans
      selfStabilizationOrdinal_le_internalScottRank)

/-! ### Binary-sequence paths and the companion assemblies `CompanionModel z` -/

/-- Nondecreasing path encoded by `z : ℕ → Bool`: `pathOf z (2 * n) = n` and
`pathOf z (2 * n + 1) = n + (z n).toNat`. -/
def pathOf (z : ℕ → Bool) (k : ℕ) : ℕ :=
  k / 2 + if k % 2 = 1 then (z (k / 2)).toNat else 0

private theorem pathOf_two_mul (z : ℕ → Bool) (n : ℕ) : pathOf z (2 * n) = n := by
  simp [pathOf]

private theorem pathOf_two_mul_add_one (z : ℕ → Bool) (n : ℕ) :
    pathOf z (2 * n + 1) = n + (z n).toNat := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp [pathOf, hdiv, hmod]

private theorem pathOf_mono (z : ℕ → Bool) : Monotone (pathOf z) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [pathOf_two_mul, pathOf_two_mul_add_one]
    omega
  · have hnext : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
    rw [pathOf_two_mul_add_one, hnext, pathOf_two_mul]
    cases z n <;> simp

private theorem pathOf_le (z : ℕ → Bool) (k : ℕ) : pathOf z k ≤ k := by
  dsimp only [pathOf]
  split_ifs with h
  · have hb : (z (k / 2)).toNat ≤ 1 := Bool.toNat_le (z (k / 2))
    omega
  · omega

/-- The length-`m` admissible prefix of `pathOf z`. -/
def pathPrefix (z : ℕ → Bool) (m : ℕ) : Row :=
  ⟨(List.range m).map (pathOf z),
    ⟨fun _ _ _ _ hij => by simpa using pathOf_mono z hij,
      fun i _ => by simpa using pathOf_le z i⟩⟩

@[simp]
private theorem length_pathPrefix (z : ℕ → Bool) (m : ℕ) :
    (pathPrefix z m).1.length = m := by
  simp [pathPrefix]

private theorem prefix_pathPrefix_iff (z : ℕ → Bool) (l : List ℕ) (k : ℕ) :
    l <+: (pathPrefix z k).1 ↔ l.length ≤ k ∧ l = (pathPrefix z l.length).1 := by
  refine ⟨fun h => ⟨by simpa using h.length_le, ?_⟩, fun ⟨hlen, hl⟩ => ?_⟩
  · simpa [pathPrefix, ← List.map_take, min_eq_left (by simpa using h.length_le : l.length ≤ k)]
      using List.prefix_iff_eq_take.mp h
  · rw [List.prefix_iff_eq_take]
    simpa [pathPrefix, ← List.map_take, min_eq_left hlen] using hl

/-- Component pure-set fibers of `CompanionModel z`: `BaseFiber p` on `some p`, and finite along
the prefixes of `pathOf z` on the extra path row `none`. -/
abbrev CompanionFiber (z : ℕ → Bool) : Option Row → Label ℕ → Type
  | some p, τ => BaseFiber p τ
  | none, τ => FiberType (decide (τ.1 = (pathPrefix z τ.1.length).1)) τ

instance instStructureCompanionFiber (z : ℕ → Bool) (r : Option Row) (τ : Label ℕ) :
    Language.empty.Structure (CompanionFiber z r τ) := by
  cases r <;> infer_instance

instance instCountableCompanionFiber (z : ℕ → Bool) (r : Option Row) (τ : Label ℕ) :
    Countable (CompanionFiber z r τ) := by
  cases r <;> infer_instance

/-- The companion row assembly attached to `z : ℕ → Bool`. -/
abbrev CompanionModel (z : ℕ → Bool) : Type := Carrier (Option Row) (CompanionFiber z)

/-! ### Level-`ω` equivalence via Hilbert-hotel row bijections -/

private def hilbertRowFun (z : ℕ → Bool) (m : ℕ) : Option Row → Row
  | none => pathPrefix z (2 * m)
  | some p =>
    if 2 * m ≤ p.1.length ∧ p = pathPrefix z p.1.length then
      pathPrefix z (p.1.length + 1)
    else p

private def hilbertRowInv (z : ℕ → Bool) (m : ℕ) (q : Row) : Option Row :=
  if q = pathPrefix z (2 * m) then none
  else if 2 * m + 1 ≤ q.1.length ∧ q = pathPrefix z q.1.length then
    some (pathPrefix z (q.1.length - 1))
  else some q

private theorem leftInverse_hilbertRowInv (z : ℕ → Bool) (m : ℕ) :
    Function.LeftInverse (hilbertRowInv z m) (hilbertRowFun z m)
  | none => by simp [hilbertRowFun, hilbertRowInv]
  | some p => by
    dsimp only [hilbertRowFun, hilbertRowInv]
    by_cases h₁ : 2 * m ≤ p.1.length ∧ p = pathPrefix z p.1.length
    · rw [ite_eq_left h₁]
      have hne : pathPrefix z (p.1.length + 1) ≠ pathPrefix z (2 * m) := fun he => by
        have := congrArg (fun r : Row => r.1.length) he
        simp at this
        omega
      have h₂ : 2 * m + 1 ≤ (pathPrefix z (p.1.length + 1)).1.length ∧
          pathPrefix z (p.1.length + 1) =
            pathPrefix z (pathPrefix z (p.1.length + 1)).1.length :=
        ⟨by simp; omega, by simp⟩
      rw [ite_eq_right hne, ite_eq_left h₂]
      simpa using h₁.2.symm
    · rw [ite_eq_right h₁]
      have hne : p ≠ pathPrefix z (2 * m) := fun he =>
        h₁ ⟨by rw [he]; simp, by rw [he]; simp⟩
      have h₂ : ¬ (2 * m + 1 ≤ p.1.length ∧ p = pathPrefix z p.1.length) := fun h =>
        h₁ ⟨by omega, h.2⟩
      rw [ite_eq_right hne, ite_eq_right h₂]

private theorem rightInverse_hilbertRowInv (z : ℕ → Bool) (m : ℕ) :
    Function.RightInverse (hilbertRowInv z m) (hilbertRowFun z m) := fun q => by
  dsimp only [hilbertRowFun, hilbertRowInv]
  by_cases h₁ : q = pathPrefix z (2 * m)
  · rw [ite_eq_left h₁]
    exact h₁.symm
  · rw [ite_eq_right h₁]
    by_cases h₂ : 2 * m + 1 ≤ q.1.length ∧ q = pathPrefix z q.1.length
    · rw [ite_eq_left h₂]
      dsimp only
      have h₃ : 2 * m ≤ (pathPrefix z (q.1.length - 1)).1.length ∧
          pathPrefix z (q.1.length - 1) =
            pathPrefix z (pathPrefix z (q.1.length - 1)).1.length :=
        ⟨by simp; omega, by simp⟩
      rw [ite_eq_left h₃]
      have hk : (pathPrefix z (q.1.length - 1)).1.length + 1 = q.1.length := by simp; omega
      rw [hk]
      exact h₂.2.symm
    · rw [ite_eq_right h₂]
      dsimp only
      have h₃ : ¬ (2 * m ≤ q.1.length ∧ q = pathPrefix z q.1.length) := fun h => by
        rcases eq_or_lt_of_le h.1 with heq | hlt
        · exact h₁ (h.2.trans (by rw [heq]))
        · exact h₂ ⟨by omega, h.2⟩
      rw [ite_eq_right h₃]

private def hilbertRow (z : ℕ → Bool) (m : ℕ) : Option Row ≃ Row where
  toFun := hilbertRowFun z m
  invFun := hilbertRowInv z m
  left_inv := leftInverse_hilbertRowInv z m
  right_inv := rightInverse_hilbertRowInv z m

private theorem le_getLast_of_eq_pathPrefix (z : ℕ → Bool) {m : ℕ} (τ : Label ℕ)
    (hlen : 2 * m < τ.1.length) (hτ : τ.1 = (pathPrefix z τ.1.length).1) :
    m ≤ τ.1.getLast τ.2 + 1 := by
  have hlast : τ.1.getLast τ.2 = pathOf z (τ.1.length - 1) := by
    rw [List.getLast_eq_getElem]
    have hget := congrArg (fun l : List ℕ => l[τ.1.length - 1]?) hτ
    have hi : τ.1.length - 1 < τ.1.length := by omega
    have hi' : τ.1.length - 1 < (pathPrefix z τ.1.length).1.length := by simpa using hi
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at hget
    simpa [pathPrefix] using Option.some.inj hget
  have hm : m ≤ pathOf z (τ.1.length - 1) := by
    rw [← pathOf_two_mul z m]
    exact pathOf_mono z (by omega)
  omega

/-- Helper matching two `FiberType` flags at depth `m` whenever either `b₁ = b₂` or
`m ≤ τ.1.getLast τ.2 + 1`. -/
private theorem bfEquiv_fiberType_of_eq_or_le {b₁ b₂ : Bool} (τ : Label ℕ) {m : ℕ}
    (h : b₁ = b₂ ∨ m ≤ τ.1.getLast τ.2 + 1) :
    BFEquiv (L := Language.empty) (m : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType b₁ τ) (Fin.elim0 : Fin 0 → FiberType b₂ τ) := by
  rcases h with rfl | hle
  · exact BFEquiv.refl _ _
  · exact bfEquiv_fiberType_of_le b₁ b₂ τ hle

/-- Every companion `CompanionModel z` is back-and-forth equivalent to `PrefixModel` at level
`ω`. -/
theorem bfEquiv_omega0_companionModel_prefixModel (z : ℕ → Bool) :
    BFEquiv (L := lang ℕ Language.empty) Ordinal.omega0.{0} 0
      (Fin.elim0 : Fin 0 → CompanionModel z) (Fin.elim0 : Fin 0 → PrefixModel) := by
  rw [BFEquiv.limit Ordinal.isSuccLimit_omega0]
  intro β hβ
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hβ
  refine bfEquiv_elim0_of_rowEquiv (hilbertRow z m) (m : Ordinal.{0}) fun r τ => ?_
  cases r with
  | none =>
    apply bfEquiv_fiberType_of_eq_or_le τ
    by_cases hτ : τ.1 = (pathPrefix z τ.1.length).1
    · by_cases hlen : τ.1.length ≤ 2 * m
      · left
        have hp : τ.1 <+: (pathPrefix z (2 * m)).1 :=
          (prefix_pathPrefix_iff z τ.1 (2 * m)).mpr ⟨hlen, hτ⟩
        rw [decide_eq_true hτ]
        simp [hilbertRow, hilbertRowFun, hp]
      · exact Or.inr (le_getLast_of_eq_pathPrefix z τ (Nat.lt_of_not_ge hlen) hτ)
    · left
      have hnp : ¬ (τ.1 <+: (pathPrefix z (2 * m)).1) := fun hp =>
        hτ ((prefix_pathPrefix_iff z τ.1 (2 * m)).mp hp).2
      rw [decide_eq_false hτ]
      simp [hilbertRow, hilbertRowFun, hnp]
  | some p =>
    by_cases hp : 2 * m ≤ p.1.length ∧ p = pathPrefix z p.1.length
    · have hhr : hilbertRow z m (some p) = pathPrefix z (p.1.length + 1) := ite_eq_left hp
      rw [hhr]
      apply bfEquiv_fiberType_of_eq_or_le τ
      by_cases hτ : τ.1 = (pathPrefix z τ.1.length).1
      · by_cases hlen : τ.1.length ≤ p.1.length
        · left
          have hp₁ : τ.1 <+: p.1 := hp.2.symm ▸
            (prefix_pathPrefix_iff z τ.1 p.1.length).mpr ⟨hlen, hτ⟩
          have hp₂ : τ.1 <+: (pathPrefix z (p.1.length + 1)).1 :=
            (prefix_pathPrefix_iff z τ.1 (p.1.length + 1)).mpr ⟨by omega, hτ⟩
          simp [hp₁, hp₂]
        · exact Or.inr (le_getLast_of_eq_pathPrefix z τ (by omega) hτ)
      · left
        have hnp₁ : ¬ (τ.1 <+: p.1) := fun h₁ =>
          hτ ((prefix_pathPrefix_iff z τ.1 p.1.length).mp (hp.2 ▸ h₁)).2
        have hnp₂ : ¬ (τ.1 <+: (pathPrefix z (p.1.length + 1)).1) := fun h₂ =>
          hτ ((prefix_pathPrefix_iff z τ.1 (p.1.length + 1)).mp h₂).2
        simp [hnp₁, hnp₂]
    · have hhr : hilbertRow z m (some p) = p := ite_eq_right hp
      rw [hhr]
      exact BFEquiv.refl _ _

/-! ### Non-isomorphism and Scott-height consequences -/

/-- The infinite-path row `none` in `CompanionModel z` cannot match any finite-word row `p` on all
fibers simultaneously, because `pathPrefix z (p.1.length + 1)` has a finite fiber over `none` and an
infinite fiber over `p`. -/
private theorem false_of_fiberBij_none (z : ℕ → Bool) (p : Row)
    (f : ∀ τ, CompanionFiber z none τ ≃ BaseFiber p τ) : False := by
  let τ : Label ℕ := ⟨(pathPrefix z (p.1.length + 1)).1, List.ne_nil_of_length_pos (by simp)⟩
  have heq : decide (τ.1 = (pathPrefix z τ.1.length).1) = decide (τ.1 <+: p.1) :=
    eq_of_fiberType_equiv (f τ)
  simp only [τ, length_pathPrefix, decide_true, true_eq_decide_iff] at heq
  have hlen := heq.length_le
  simp at hlen

/-- No companion `CompanionModel z` is isomorphic to `PrefixModel`. -/
theorem isEmpty_equiv_companionModel_prefixModel (z : ℕ → Bool) :
    IsEmpty (CompanionModel z ≃[lang ℕ Language.empty] PrefixModel) :=
  ⟨fun e => false_of_fiberBij_none z (rowEquiv e none) (fiberBij e none)⟩

/-- Distinct binary sequences yield non-isomorphic companions. -/
theorem isEmpty_equiv_companionModel_of_ne {z z' : ℕ → Bool} (h : z ≠ z') :
    IsEmpty (CompanionModel z ≃[lang ℕ Language.empty] CompanionModel z') := by
  refine ⟨fun e => ?_⟩
  have hnone : rowEquiv e none = none := by
    cases hr : rowEquiv e none with
    | none => rfl
    | some p =>
      exact False.elim (false_of_fiberBij_none z p fun τ => by
        have hf := fiberBij e none τ
        rw [hr] at hf
        exact hf)
  obtain ⟨n, hn⟩ := Function.ne_iff.mp h
  let τ : Label ℕ := ⟨(pathPrefix z (2 * n + 2)).1, List.ne_nil_of_length_pos (by simp)⟩
  have heq : decide (τ.1 = (pathPrefix z τ.1.length).1) =
      decide (τ.1 = (pathPrefix z' τ.1.length).1) := by
    have hf := fiberBij e none τ
    rw [hnone] at hf
    exact eq_of_fiberType_equiv hf
  simp only [τ, length_pathPrefix, decide_true, true_eq_decide_iff] at heq
  have hget := congrArg (fun l : List ℕ => l[2 * n + 1]?) heq
  have hi : 2 * n + 1 < 2 * n + 2 := by omega
  simp only [pathPrefix, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq, pathOf_two_mul_add_one] at hget
  have : (z n).toNat = (z' n).toNat := by omega
  exact hn (by cases h1 : z n <;> cases h2 : z' n <;> simp_all)

/-- The Scott height of `PrefixModel` strictly exceeds `ω`. -/
theorem omega0_lt_scottHeight_prefixModel :
    Ordinal.omega0 < scottHeight (L := lang ℕ Language.empty) PrefixModel := by
  by_contra! hle
  obtain ⟨e⟩ := nonempty_equiv_of_bfEquiv_of_scottHeight_le hle
    (bfEquiv_omega0_companionModel_prefixModel (fun _ => false)).symm
  exact (isEmpty_equiv_companionModel_prefixModel (fun _ => false)).false e.symm

/-- The Scott height of `PrefixModel` is at most `ω + ω`. -/
theorem scottHeight_prefixModel_le :
    scottHeight (L := lang ℕ Language.empty) PrefixModel ≤ Ordinal.omega0 + Ordinal.omega0 := by
  simpa [internalScottRank_prefixModel] using
    scottHeight_le_internalScottRank_add_omega0 (L := lang ℕ Language.empty) PrefixModel

/-- There is a countable `(lang ℕ Language.empty)`-structure of internal Scott rank `ω` (with
Scott height strictly above `ω`) together with a Cantor-indexed family of pairwise non-isomorphic
countable companions, none isomorphic to it, all back-and-forth equivalent to it at level `ω`. -/
theorem exists_internalScottRank_omega_with_large_bfClass :
    ∃ (M : Type) (_ : (lang ℕ Language.empty).Structure M) (_ : Countable M)
      (N : (ℕ → Bool) → Type) (_ : ∀ z, (lang ℕ Language.empty).Structure (N z))
      (_ : ∀ z, Countable (N z)),
      internalScottRank (L := lang ℕ Language.empty) M = Ordinal.omega0 ∧
      Ordinal.omega0 < scottHeight (L := lang ℕ Language.empty) M ∧
      (∀ z, BFEquiv (L := lang ℕ Language.empty) Ordinal.omega0.{0} 0
        (Fin.elim0 : Fin 0 → N z) (Fin.elim0 : Fin 0 → M)) ∧
      (∀ z, IsEmpty (N z ≃[lang ℕ Language.empty] M)) ∧
      (∀ z z', z ≠ z' → IsEmpty (N z ≃[lang ℕ Language.empty] N z')) :=
  ⟨PrefixModel, inferInstance, inferInstance, CompanionModel, fun _ => inferInstance,
    fun _ => inferInstance, internalScottRank_prefixModel, omega0_lt_scottHeight_prefixModel,
    bfEquiv_omega0_companionModel_prefixModel, isEmpty_equiv_companionModel_prefixModel,
    fun _ _ h => isEmpty_equiv_companionModel_of_ne h⟩

/-! ### Consequences for configurations on `ℕ` and isolating ranks -/

/-- Encoding of `PrefixModel` as a relational configuration on `ℕ`. -/
noncomputable def prefixModelCode :
    RelationalConfiguration (lang ℕ Language.empty) ℕ :=
  (nonempty_equiv_of_countable.some : PrefixModel ≃ ℕ).encodeVia

/-- Encoding of `CompanionModel z` as a relational configuration on `ℕ`. -/
noncomputable def companionModelCode (z : ℕ → Bool) :
    RelationalConfiguration (lang ℕ Language.empty) ℕ :=
  (nonempty_equiv_of_countable.some : CompanionModel z ≃ ℕ).encodeVia

/-- The decoded structure of `prefixModelCode` has internal Scott rank `ω`. -/
theorem internalScottRank_prefixModelCode :
    (letI := prefixModelCode.toStructure;
      internalScottRank (L := lang ℕ Language.empty) ℕ) = Ordinal.omega0 := by
  let e : PrefixModel ≃ ℕ := nonempty_equiv_of_countable.some
  have hts : prefixModelCode.toStructure = e.inducedStructure :=
    e.toStructure_encodeVia
  let _ : (lang ℕ Language.empty).Structure ℕ := e.inducedStructure
  have heq : (letI := prefixModelCode.toStructure;
      internalScottRank (L := lang ℕ Language.empty) ℕ) =
      internalScottRank (L := lang ℕ Language.empty) ℕ := by
    congr!
  rw [heq, ← e.inducedStructureEquiv.internalScottRank_eq]
  exact internalScottRank_prefixModel

/-- Every `companionModelCode z` lies in the `ω`-level back-and-forth class of
`prefixModelCode`. -/
theorem bfEquivSetoid_prefixModelCode_companionModelCode (z : ℕ → Bool) :
    RelationalConfiguration.bfEquivSetoid (lang ℕ Language.empty) ℕ Ordinal.omega0.{0}
      prefixModelCode (companionModelCode z) := by
  rw [RelationalConfiguration.bfEquivSetoid_apply]
  let e₁ : PrefixModel ≃ ℕ := nonempty_equiv_of_countable.some
  let e₂ : CompanionModel z ≃ ℕ := nonempty_equiv_of_countable.some
  obtain ⟨E₁⟩ := e₁.nonempty_equiv_encodeVia (L := lang ℕ Language.empty)
  obtain ⟨E₂⟩ := e₂.nonempty_equiv_encodeVia (L := lang ℕ Language.empty)
  let E₁s := @Language.Equiv.symm (lang ℕ Language.empty) PrefixModel ℕ
    _ prefixModelCode.toStructure E₁
  have h₁ : @BFEquiv (lang ℕ Language.empty) _ ℕ PrefixModel
      prefixModelCode.toStructure _ Ordinal.omega0.{0} 0 Fin.elim0 Fin.elim0 := by
    convert @Language.Equiv.bfEquiv (lang ℕ Language.empty) _ ℕ PrefixModel
      prefixModelCode.toStructure _ E₁s Ordinal.omega0.{0} 0 Fin.elim0 using 1
  have h₂ : @BFEquiv (lang ℕ Language.empty) _ (CompanionModel z) ℕ
      _ (companionModelCode z).toStructure Ordinal.omega0.{0} 0 Fin.elim0 Fin.elim0 := by
    convert @Language.Equiv.bfEquiv (lang ℕ Language.empty) _ (CompanionModel z) ℕ
      _ (companionModelCode z).toStructure E₂ Ordinal.omega0.{0} 0 Fin.elim0 using 1
  have h₁' := @BFEquiv.trans (lang ℕ Language.empty) _ ℕ PrefixModel (CompanionModel z)
    prefixModelCode.toStructure _ _ 0 Fin.elim0 Fin.elim0 Fin.elim0 Ordinal.omega0.{0}
    h₁ (bfEquiv_omega0_companionModel_prefixModel z).symm
  exact @BFEquiv.trans (lang ℕ Language.empty) _ ℕ (CompanionModel z) ℕ
    prefixModelCode.toStructure _ (companionModelCode z).toStructure 0
    Fin.elim0 Fin.elim0 Fin.elim0 Ordinal.omega0.{0} h₁' h₂

/-- No `companionModelCode z` is isomorphic as a configuration on `ℕ` to `prefixModelCode`. -/
theorem not_isoSetoid_prefixModelCode_companionModelCode (z : ℕ → Bool) :
    ¬ RelationalConfiguration.isoSetoid (lang ℕ Language.empty) ℕ
      prefixModelCode (companionModelCode z) := by
  intro h
  obtain ⟨e⟩ := (Equiv.isoSetoid_encodeVia_iff _ _).mp h
  exact (isEmpty_equiv_companionModel_prefixModel z).false e.symm

/-- Distinct binary sequences yield non-isomorphic configurations `companionModelCode z` on `ℕ`. -/
theorem not_isoSetoid_companionModelCode_of_ne {z z' : ℕ → Bool} (h : z ≠ z') :
    ¬ RelationalConfiguration.isoSetoid (lang ℕ Language.empty) ℕ
      (companionModelCode z) (companionModelCode z') := by
  intro hiso
  obtain ⟨e⟩ := (Equiv.isoSetoid_encodeVia_iff _ _).mp hiso
  exact (isEmpty_equiv_companionModel_of_ne h).false e

/-- Every isolating rank on `RelationalConfiguration (lang ℕ Language.empty) ℕ` assigns to
`prefixModelCode` a value strictly greater than `ω`. -/
theorem _root_.TauCeti.IsIsolatingRank.omega0_lt_prefixModelCode
    {ρ : RelationalConfiguration (lang ℕ Language.empty) ℕ → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) :
    Ordinal.omega0 < ρ prefixModelCode := by
  by_contra! hle
  exact not_isoSetoid_prefixModelCode_companionModelCode (fun _ => false)
    (hρ.isolates_of_le hle (bfEquivSetoid_prefixModelCode_companionModelCode (fun _ => false)))

/-- The internal Scott rank, read on decoded relational configurations on `ℕ`, is not an isolating
rank: although isomorphism-invariant and bounded below `ω₁`, it equals `ω` at `prefixModelCode`
while `prefixModelCode` is `ω`-equivalent to non-isomorphic configurations. -/
theorem not_isIsolatingRank_internalScottRank :
    ¬ IsIsolatingRank (L := lang ℕ Language.empty)
        (fun c => letI := c.toStructure; internalScottRank (L := lang ℕ Language.empty) ℕ) := by
  intro h
  exact (h.omega0_lt_prefixModelCode.trans_eq internalScottRank_prefixModelCode).false

/-- The single `ω`-level back-and-forth equivalence class of `prefixModelCode` splits into
continuum-many isomorphism classes on `ℕ`. -/
theorem mk_quotient_comap_isoSetoid_bfClass_prefixModelCode :
    Cardinal.mk (Quotient
      ((RelationalConfiguration.isoSetoid (lang ℕ Language.empty) ℕ).comap
        (Subtype.val : {d | RelationalConfiguration.bfEquivSetoid
          (lang ℕ Language.empty) ℕ Ordinal.omega0.{0} prefixModelCode d} → _))) =
      Cardinal.continuum := by
  let K : Set (RelationalConfiguration (lang ℕ Language.empty) ℕ) :=
    {d | RelationalConfiguration.bfEquivSetoid
      (lang ℕ Language.empty) ℕ Ordinal.omega0.{0} prefixModelCode d}
  apply le_antisymm
  · exact Cardinal.mk_quotient_le.trans
      ((Cardinal.mk_subtype_le _).trans
        (RelationalConfiguration.mk_le_continuum (lang ℕ Language.empty) ℕ))
  · let emb : (ℕ → Bool) →
        Quotient ((RelationalConfiguration.isoSetoid (lang ℕ Language.empty) ℕ).comap
          (Subtype.val : K → _)) :=
      fun z => Quotient.mk _ ⟨companionModelCode z,
        bfEquivSetoid_prefixModelCode_companionModelCode z⟩
    have hinj : Function.Injective emb := fun z z' heq => by
      by_contra hne
      exact not_isoSetoid_companionModelCode_of_ne hne
        (Quotient.exact (s := (RelationalConfiguration.isoSetoid (lang ℕ Language.empty) ℕ).comap
          (Subtype.val : K → _)) heq)
    calc Cardinal.continuum = Cardinal.mk (ℕ → Bool) := by simp
      _ ≤ _ := Cardinal.mk_le_of_injective hinj

end TauCeti.RowAssembly
