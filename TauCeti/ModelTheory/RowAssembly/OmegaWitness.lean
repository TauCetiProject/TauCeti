/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.BackAndForth
public import TauCeti.ModelTheory.Counting.Stratification
import TauCeti.ModelTheory.BackAndForth.PureSet
import TauCeti.ModelTheory.Scott.PureSet
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
* `nonempty_equiv_prefixModelCode` and `nonempty_equiv_companionModelCode`: isomorphism bridges
  between `PrefixModel` / `CompanionModel z` and their configurations `prefixModelCode` /
  `companionModelCode z` on `ℕ`;
* `not_isIsolatingRank_internalScottRank`: the internal Scott rank on configurations on `ℕ` is not
  an isolating rank (although it is isomorphism-invariant and countable, it fails one-sided
  isolation at `prefixModelCode`);
* `IsIsolatingRank.omega0_lt_prefixModelCode` and
  `mk_quotient_comap_isoSetoid_bfClass_prefixModelCode`: every isolating rank strictly exceeds `ω`
  at `prefixModelCode`, whose `ω`-level back-and-forth class splits into `𝔠` isomorphism classes.

## Construction

An admissible row is a nondecreasing word `p : List ℕ` satisfying `p[i] ≤ i` at every index
`i < p.length`. In `PrefixModel`, built as a row assembly over admissible rows with pure-set
fibers, the fiber at `(p, τ)` is the finite pure set `Fin (last τ + 1)` when `τ.1` is a prefix of
`p.1`, and the infinite pure set `ℕ` otherwise. Because `last τ ≤ τ.length - 1`, any row `p` of
length `L` is pinned among rows of `PrefixModel` at back-and-forth depth `L + 2`, bounding every
finite tuple's orbit rank below `ω`; conversely, extending `List.range (k + 1)` by `[k]` shows no
finite level stabilizes all rows.

Each `z : ℕ → Bool` defines a nondecreasing path `π_z` (`π_z (2 * n) = n`,
`π_z (2 * n + 1) = n + (z n).toNat`) and adds one infinite-path row whose finite fibers sit along
the prefixes of `π_z`. At any finite depth `m`, a Hilbert-hotel bijection absorbing the extra row
into the length-`2 * m` prefix of `π_z` matches every fiber up to depth `m` because diverging
fibers have `last τ ≥ π_z (2 * m) = m`.

## References

* Adapted from `InfinitaryLogic/ModelTheory/FiberPrefixDetection.lean`, `FiberProfileBound.lean`,
  `FiberProfilePerm.lean`, `FiberIsoCarrying.lean`, `FiberOrbitBound.lean`, `FiberTwoRow.lean`,
  `FiberExactRank.lean`, `FiberExactOmega.lean`, `FiberCompanion.lean`, `FiberCompanionShift.lean`,
  `FiberCompanionEquiv.lean`, `FiberCompanionIso.lean`, and `FiberCantorFamily.lean` in Cameron
  Freer's `cameronfreer/infinitary-logic` (checkpoint
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, Apache-2.0); see also David Marker, *Lectures on
  Infinitary Model Theory*, Cambridge University Press, 2016, and Antonio Montalbán, *Computable
  Structure Theory: Beyond the Arithmetic*, Part 2, for structures of limit Scott rank `ω` with
  non-isomorphic `≡_ω`-companions (the high-Scott-rank / non-isolated phenomenon at limit
  ordinals).
-/

public section

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language Fin Cardinal Ordinal

/-! ### Pure-set fibers controlled by a Boolean flag -/

/-- Pure-set fiber attached to label `τ : Label ℕ` according to a Boolean flag `b`: when `b = true`
it is the finite set `Fin (τ.1.getLast τ.2 + 1)`, and when `b = false` it is `ℕ`. -/
private def FiberType : Bool → Label ℕ → Type
  | true, τ => Fin (τ.1.getLast τ.2 + 1)
  | false, _ => ℕ

private instance instStructureFiberType (b : Bool) (τ : Label ℕ) :
    Language.empty.Structure (FiberType b τ) :=
  Language.emptyStructure

private instance instCountableFiberType (b : Bool) (τ : Label ℕ) : Countable (FiberType b τ) := by
  cases b <;> dsimp [FiberType] <;> infer_instance

private instance instInfiniteFiberTypeFalse (τ : Label ℕ) : Infinite (FiberType false τ) :=
  inferInstanceAs (Infinite ℕ)

private instance instFintypeFiberTypeTrue (τ : Label ℕ) : Fintype (FiberType true τ) :=
  inferInstanceAs (Fintype (Fin (τ.1.getLast τ.2 + 1)))

private theorem card_fiberType_true (τ : Label ℕ) :
    Fintype.card (FiberType true τ) = τ.1.getLast τ.2 + 1 :=
  Fintype.card_fin _

private theorem bfEquiv_fiberType_iff (b₁ b₂ : Bool) (τ : Label ℕ) (k : ℕ) :
    BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType b₁ τ) (Fin.elim0 : Fin 0 → FiberType b₂ τ) ↔
      b₁ = b₂ ∨ k ≤ τ.1.getLast τ.2 + 1 := by
  have hft : BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType false τ) (Fin.elim0 : Fin 0 → FiberType true τ) ↔
      k ≤ τ.1.getLast τ.2 + 1 := by
    rw [bfEquiv_empty_elim0_natCast_iff_le_card, ENat.card_eq_coe_fintype_card, card_fiberType_true]
    exact_mod_cast Iff.rfl
  cases b₁ <;> cases b₂
  · simp [BFEquiv.refl]
  · simpa using hft
  · rw [BFEquiv.symm_iff]
    simpa using hft
  · simp [BFEquiv.refl]

private theorem eq_of_fiberType_equiv {b₁ b₂ : Bool} {τ : Label ℕ}
    (e : FiberType b₁ τ ≃ FiberType b₂ τ) : b₁ = b₂ := by
  cases b₁ <;> cases b₂
  · rfl
  · have := Finite.of_equiv _ e.symm
    exact (not_finite (FiberType false τ)).elim
  · have := Finite.of_equiv _ e
    exact (not_finite (FiberType false τ)).elim
  · rfl

/-! ### Admissible rows and the prefix row assembly `PrefixModel` -/

/-- A word `l : List ℕ` is admissible when it is nondecreasing and satisfies `l[i] ≤ i` at every
position `i < l.length`. -/
private def IsAdmissible (l : List ℕ) : Prop :=
  (∀ ⦃i j : ℕ⦄ (hi : i < l.length) (hj : j < l.length), i ≤ j → l[i] ≤ l[j]) ∧
    ∀ ⦃i : ℕ⦄ (hi : i < l.length), l[i] ≤ i

/-- Admissible finite words over `ℕ`, indexing the rows of `PrefixModel`. -/
private abbrev Row : Type := {l : List ℕ // IsAdmissible l}

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

private instance instInfiniteRow : Infinite Row :=
  Infinite.of_injective (fun m : ℕ => (⟨List.range m, isAdmissible_range m⟩ : Row)) fun a b h => by
    simpa using congrArg (fun r : Row => r.1.length) h

/-- Component pure-set fibers of `PrefixModel`: finite of size `last τ + 1` when `τ.1 <+: p.1`,
and `ℕ` otherwise. -/
private abbrev BaseFiber (p : Row) (τ : Label ℕ) : Type :=
  FiberType (decide (τ.1 <+: p.1)) τ

/-- The prefix row assembly over `ℕ` with pure-set fibers, having internal Scott rank `ω`. -/
def PrefixModel : Type := Carrier Row BaseFiber

@[no_expose] noncomputable instance instStructurePrefixModel :
    (lang ℕ Language.empty).Structure PrefixModel :=
  inferInstanceAs ((lang ℕ Language.empty).Structure (Carrier Row BaseFiber))

instance instCountablePrefixModel : Countable PrefixModel :=
  inferInstanceAs (Countable (Carrier Row BaseFiber))

instance instInfinitePrefixModel : Infinite PrefixModel :=
  inferInstanceAs (Infinite (Carrier Row BaseFiber))

/-! ### Row pinning and internal Scott rank `ω` of `PrefixModel` -/

/-- Any row `p₁` of `PrefixModel` is uniquely determined among rows of `PrefixModel` by
back-and-forth equivalence at finite depth `p₁.1.length + 2`. -/
private theorem row_eq_of_bfEquiv {N : ℕ} {a b : Fin N → Carrier Row BaseFiber} {i₀ : Fin N}
    {p₁ p₂ : Row} (ha₀ : a i₀ = .row p₁) (hb₀ : b i₀ = .row p₂)
    (h : BFEquiv (L := lang ℕ Language.empty) ((p₁.1.length + 2 : ℕ) : Ordinal.{0}) N a b) :
    p₁ = p₂ := by
  have hpref : p₁.1 <+: p₂.1 := by
    by_contra hnp
    have hne : p₁.1 ≠ [] := fun he => hnp (he ▸ List.nil_prefix)
    let τ : Label ℕ := ⟨p₁.1, hne⟩
    have hf := (bfEquiv_fiberType_iff _ _ τ (p₁.1.length + 2)).mp
      (bfEquiv_fiber_elim0_of_row_eq h ha₀ hb₀ τ)
    have hle := getLast_le_pred_length p₁.2 hne
    have hpos : 0 < p₁.1.length := List.length_pos_iff.mpr hne
    rcases hf with hdec | hge
    · simp [τ, hnp] at hdec
    · dsimp only [τ] at hge
      omega
  have hlen : p₂.1.length ≤ p₁.1.length := by
    by_contra hlt
    have hlt' : p₁.1.length < p₂.1.length := Nat.lt_of_not_ge hlt
    let l := p₂.1.take (p₁.1.length + 1)
    have hllen : l.length = p₁.1.length + 1 := by simp [l]; omega
    have hne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
    let τ : Label ℕ := ⟨l, hne⟩
    have hf := (bfEquiv_fiberType_iff _ _ τ (p₁.1.length + 2)).mp
      (bfEquiv_fiber_elim0_of_row_eq h ha₀ hb₀ τ)
    have hnp₁ : ¬ (l <+: p₁.1) := fun hp => by
      have := hp.length_le
      omega
    have hp₂ : l <+: p₂.1 := List.take_prefix _ _
    have hle : τ.1.getLast τ.2 ≤ l.length - 1 :=
      getLast_le_pred_length (isAdmissible_take p₂.2 (p₁.1.length + 1)) hne
    rcases hf with hdec | hge
    · simp [τ, hnp₁, hp₂] at hdec
    · omega
  exact Subtype.ext (hpref.eq_of_length_le hlen)

private theorem internalScottRank_prefixModel_le :
    internalScottRank (L := lang ℕ Language.empty) (Carrier Row BaseFiber) ≤ Ordinal.omega0 := by
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
  have hsat := hab.sameAtomicType
  refine (MatchedBF.mk (σ := Equiv.refl Row) hrow
    (fun i => (label?_eq_of_sameAtomicType hsat i).symm) ?_).bfEquiv
  intro p τ m idx xs ys hxs hys
  refine (selfStabilizesCompletely_empty (BaseFiber p τ)).bfEquiv_of_bfEquiv
    (BFEquiv.zero.mpr ((sameAtomicType_empty_iff xs ys).mpr fun j k => ?_))
  rw [← (Carrier.pt_injective p τ).eq_iff, ← hxs j, ← hxs k,
    hsat.eq_iff (idx j) (idx k), hys j, hys k, (Carrier.pt_injective _ τ).eq_iff]

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
    Ordinal.omega0 ≤ selfStabilizationOrdinal (L := lang ℕ Language.empty)
      (Carrier Row BaseFiber) := by
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
      exact (bfEquiv_fiberType_iff _ _ τ (k + 1)).mpr (Or.inr (by omega))
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
  let a : Fin 1 → Carrier Row BaseFiber := fun _ => .row p₁
  let b : Fin 1 → Carrier Row BaseFiber := fun _ => .row p₂
  have hab : BFEquiv (L := lang ℕ Language.empty) ((k + 1 : ℕ) : Ordinal.{0}) 1 a b := by
    simpa [a, b, σ, Equiv.swap_apply_left] using
      bfEquiv_row_of_bfEquiv_elim0 σ ((k + 1 : ℕ) : Ordinal.{0}) (fun _ : Fin 1 => p₁) hfib
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
@[simp]
theorem selfStabilizationOrdinal_prefixModel :
    selfStabilizationOrdinal (L := lang ℕ Language.empty) PrefixModel = Ordinal.omega0 := by
  change selfStabilizationOrdinal (L := lang ℕ Language.empty) (Carrier Row BaseFiber) = _
  exact le_antisymm
    (selfStabilizationOrdinal_le_internalScottRank.trans internalScottRank_prefixModel_le)
    omega0_le_selfStabilizationOrdinal_prefixModel

/-- `PrefixModel` has internal Scott rank `ω`. -/
@[simp]
theorem internalScottRank_prefixModel :
    internalScottRank (L := lang ℕ Language.empty) PrefixModel = Ordinal.omega0 := by
  change internalScottRank (L := lang ℕ Language.empty) (Carrier Row BaseFiber) = _
  exact le_antisymm internalScottRank_prefixModel_le
    (omega0_le_selfStabilizationOrdinal_prefixModel.trans
      selfStabilizationOrdinal_le_internalScottRank)

/-! ### Binary-sequence paths and the companion assemblies `CompanionModel z` -/

/-- Nondecreasing path encoded by `z : ℕ → Bool`: `pathOf z (2 * n) = n` and
`pathOf z (2 * n + 1) = n + (z n).toNat`. -/
private def pathOf (z : ℕ → Bool) (k : ℕ) : ℕ :=
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
private def pathPrefix (z : ℕ → Bool) (m : ℕ) : Row :=
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
private abbrev CompanionFiber (z : ℕ → Bool) : Option Row → Label ℕ → Type
  | some p, τ => BaseFiber p τ
  | none, τ => FiberType (decide (τ.1 = (pathPrefix z τ.1.length).1)) τ

private instance instStructureCompanionFiber (z : ℕ → Bool) (r : Option Row) (τ : Label ℕ) :
    Language.empty.Structure (CompanionFiber z r τ) := by
  cases r <;> infer_instance

private instance instCountableCompanionFiber (z : ℕ → Bool) (r : Option Row) (τ : Label ℕ) :
    Countable (CompanionFiber z r τ) := by
  cases r <;> infer_instance

/-- The companion row assembly attached to `z : ℕ → Bool`. -/
def CompanionModel (z : ℕ → Bool) : Type := Carrier (Option Row) (CompanionFiber z)

@[no_expose] noncomputable instance instStructureCompanionModel (z : ℕ → Bool) :
    (lang ℕ Language.empty).Structure (CompanionModel z) :=
  inferInstanceAs ((lang ℕ Language.empty).Structure (Carrier (Option Row) (CompanionFiber z)))

instance instCountableCompanionModel (z : ℕ → Bool) : Countable (CompanionModel z) :=
  inferInstanceAs (Countable (Carrier (Option Row) (CompanionFiber z)))

instance instInfiniteCompanionModel (z : ℕ → Bool) : Infinite (CompanionModel z) :=
  inferInstanceAs (Infinite (Carrier (Option Row) (CompanionFiber z)))

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

@[simp]
private theorem hilbertRow_none (z : ℕ → Bool) (m : ℕ) :
    hilbertRow z m none = pathPrefix z (2 * m) := (rfl)

@[simp]
private theorem hilbertRow_some (z : ℕ → Bool) (m : ℕ) (p : Row) :
    hilbertRow z m (some p) =
      if 2 * m ≤ p.1.length ∧ p = pathPrefix z p.1.length then
        pathPrefix z (p.1.length + 1)
      else p := (rfl)

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

/-- Every companion `CompanionModel z` is back-and-forth equivalent to `PrefixModel` at level
`ω`. -/
theorem bfEquiv_omega0_companionModel_prefixModel (z : ℕ → Bool) :
    BFEquiv (L := lang ℕ Language.empty) Ordinal.omega0.{0} 0
      (Fin.elim0 : Fin 0 → CompanionModel z) (Fin.elim0 : Fin 0 → PrefixModel) := by
  change BFEquiv (L := lang ℕ Language.empty) Ordinal.omega0.{0} 0
    (Fin.elim0 : Fin 0 → Carrier (Option Row) (CompanionFiber z))
    (Fin.elim0 : Fin 0 → Carrier Row BaseFiber)
  rw [BFEquiv.limit Ordinal.isSuccLimit_omega0]
  intro β hβ
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hβ
  refine bfEquiv_elim0_of_bfEquiv_elim0 (hilbertRow z m) (m : Ordinal.{0}) fun r τ => ?_
  cases r with
  | none =>
    rw [hilbertRow_none]
    apply (bfEquiv_fiberType_iff _ _ τ m).mpr
    by_cases hτ : τ.1 = (pathPrefix z τ.1.length).1
    · by_cases hlen : τ.1.length ≤ 2 * m
      · left
        have hp : τ.1 <+: (pathPrefix z (2 * m)).1 :=
          (prefix_pathPrefix_iff z τ.1 (2 * m)).mpr ⟨hlen, hτ⟩
        rw [decide_eq_true hτ, decide_eq_true hp]
      · exact Or.inr (le_getLast_of_eq_pathPrefix z τ (Nat.lt_of_not_ge hlen) hτ)
    · left
      have hnp : ¬ (τ.1 <+: (pathPrefix z (2 * m)).1) := fun hp =>
        hτ ((prefix_pathPrefix_iff z τ.1 (2 * m)).mp hp).2
      rw [decide_eq_false hτ, decide_eq_false hnp]
  | some p =>
    by_cases hp : 2 * m ≤ p.1.length ∧ p = pathPrefix z p.1.length
    · rw [hilbertRow_some, ite_eq_left hp]
      apply (bfEquiv_fiberType_iff _ _ τ m).mpr
      by_cases hτ : τ.1 = (pathPrefix z τ.1.length).1
      · by_cases hlen : τ.1.length ≤ p.1.length
        · left
          have hp₁ : τ.1 <+: p.1 := hp.2.symm ▸
            (prefix_pathPrefix_iff z τ.1 p.1.length).mpr ⟨hlen, hτ⟩
          have hp₂ : τ.1 <+: (pathPrefix z (p.1.length + 1)).1 :=
            (prefix_pathPrefix_iff z τ.1 (p.1.length + 1)).mpr ⟨by omega, hτ⟩
          rw [decide_eq_true hp₁, decide_eq_true hp₂]
        · exact Or.inr (le_getLast_of_eq_pathPrefix z τ (by omega) hτ)
      · left
        have hnp₁ : ¬ (τ.1 <+: p.1) := fun h₁ =>
          hτ ((prefix_pathPrefix_iff z τ.1 p.1.length).mp (hp.2 ▸ h₁)).2
        have hnp₂ : ¬ (τ.1 <+: (pathPrefix z (p.1.length + 1)).1) := fun h₂ =>
          hτ ((prefix_pathPrefix_iff z τ.1 (p.1.length + 1)).mp h₂).2
        rw [decide_eq_false hnp₁, decide_eq_false hnp₂]
    · rw [hilbertRow_some, ite_eq_right hp]
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
    IsEmpty (CompanionModel z ≃[lang ℕ Language.empty] PrefixModel) := by
  change IsEmpty (Carrier (Option Row) (CompanionFiber z) ≃[lang ℕ Language.empty]
    Carrier Row BaseFiber)
  exact ⟨fun e => false_of_fiberBij_none z (e.rowEquiv none) (e.fiberBij none)⟩

/-- Distinct binary sequences yield non-isomorphic companions. -/
theorem isEmpty_equiv_companionModel_of_ne {z z' : ℕ → Bool} (h : z ≠ z') :
    IsEmpty (CompanionModel z ≃[lang ℕ Language.empty] CompanionModel z') := by
  change IsEmpty (Carrier (Option Row) (CompanionFiber z) ≃[lang ℕ Language.empty]
    Carrier (Option Row) (CompanionFiber z'))
  refine ⟨fun e => ?_⟩
  have hnone : e.rowEquiv none = none := by
    cases hr : e.rowEquiv none with
    | none => rfl
    | some p =>
      exact False.elim (false_of_fiberBij_none z p fun τ => by
        have hf := e.fiberBij none τ
        rw [hr] at hf
        exact hf)
  obtain ⟨n, hn⟩ := Function.ne_iff.mp h
  let τ : Label ℕ := ⟨(pathPrefix z (2 * n + 2)).1, List.ne_nil_of_length_pos (by simp)⟩
  have heq : decide (τ.1 = (pathPrefix z τ.1.length).1) =
      decide (τ.1 = (pathPrefix z' τ.1.length).1) := by
    have hf := e.fiberBij none τ
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
  simpa using scottHeight_le_internalScottRank_add_omega0 (L := lang ℕ Language.empty) PrefixModel

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

/-- `prefixModelCode` decodes to a structure on `ℕ` isomorphic to `PrefixModel`. -/
theorem nonempty_equiv_prefixModelCode :
    Nonempty (@Language.Equiv (lang ℕ Language.empty) PrefixModel ℕ _
      prefixModelCode.toStructure) := by
  unfold prefixModelCode
  exact Equiv.nonempty_equiv_encodeVia _

/-- `companionModelCode z` decodes to a structure on `ℕ` isomorphic to `CompanionModel z`. -/
theorem nonempty_equiv_companionModelCode (z : ℕ → Bool) :
    Nonempty (@Language.Equiv (lang ℕ Language.empty) (CompanionModel z) ℕ _
      (companionModelCode z).toStructure) := by
  unfold companionModelCode
  exact Equiv.nonempty_equiv_encodeVia _

/-- The decoded structure of `prefixModelCode` has internal Scott rank `ω`. -/
theorem internalScottRank_prefixModelCode :
    (letI := prefixModelCode.toStructure;
      internalScottRank (L := lang ℕ Language.empty) ℕ) = Ordinal.omega0 := by
  let := prefixModelCode.toStructure
  obtain ⟨E⟩ := nonempty_equiv_prefixModelCode
  exact E.symm.internalScottRank_eq.trans internalScottRank_prefixModel

/-- Every `companionModelCode z` lies in the `ω`-level back-and-forth class of
`prefixModelCode`. -/
theorem bfEquivSetoid_prefixModelCode_companionModelCode (z : ℕ → Bool) :
    RelationalConfiguration.bfEquivSetoid (lang ℕ Language.empty) ℕ Ordinal.omega0.{0}
      prefixModelCode (companionModelCode z) := by
  rw [prefixModelCode, companionModelCode, Equiv.bfEquivSetoid_encodeVia_iff]
  exact (bfEquiv_omega0_companionModel_prefixModel z).symm

/-- No `companionModelCode z` is isomorphic as a configuration on `ℕ` to `prefixModelCode`. -/
@[simp]
theorem not_isoSetoid_prefixModelCode_companionModelCode (z : ℕ → Bool) :
    ¬ RelationalConfiguration.isoSetoid (lang ℕ Language.empty) ℕ
      prefixModelCode (companionModelCode z) := by
  rw [prefixModelCode, companionModelCode, Equiv.isoSetoid_encodeVia_iff]
  rintro ⟨e⟩
  exact (isEmpty_equiv_companionModel_prefixModel z).false e.symm

/-- Two companion configurations on `ℕ` are isomorphic if and only if they come from the same
binary sequence. -/
@[simp]
theorem isoSetoid_companionModelCode_iff (z z' : ℕ → Bool) :
    RelationalConfiguration.isoSetoid (lang ℕ Language.empty) ℕ
      (companionModelCode z) (companionModelCode z') ↔ z = z' := by
  refine ⟨fun hiso => ?_, fun h => h ▸ (RelationalConfiguration.isoSetoid _ _).refl _⟩
  by_contra hne
  rw [companionModelCode, companionModelCode, Equiv.isoSetoid_encodeVia_iff] at hiso
  exact hiso.elim (isEmpty_equiv_companionModel_of_ne hne).false

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
    have hinj : Function.Injective emb := fun z z' heq =>
      (isoSetoid_companionModelCode_iff z z').mp
        (Quotient.exact (s := (RelationalConfiguration.isoSetoid (lang ℕ Language.empty) ℕ).comap
          (Subtype.val : K → _)) heq)
    calc Cardinal.continuum = Cardinal.mk (ℕ → Bool) := by simp
      _ ≤ _ := Cardinal.mk_le_of_injective hinj

end TauCeti.RowAssembly
