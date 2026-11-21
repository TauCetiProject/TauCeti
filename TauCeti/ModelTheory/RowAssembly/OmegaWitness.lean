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

This file constructs the prefix row assembly `PrefixModel` in `lang (List ℕ) Language.empty` with
pure-set fibers (`Lc = Language.empty`) and its Cantor-indexed family of non-isomorphic companions
`CompanionModel z` (`z : ℕ → Bool`), proving:

* `selfStabilizationOrdinal_prefixModel` and `internalScottRank_prefixModel`:
  `selfStabilizationOrdinal PrefixModel = ω` and `internalScottRank PrefixModel = ω`;
* `bfEquiv_omega0_companionModel_prefixModel`: every `CompanionModel z` is back-and-forth
  equivalent to `PrefixModel` at ordinal level `ω`;
* `isEmpty_equiv_companionModel_prefixModel` and `isEmpty_equiv_companionModel_of_ne`: none of the
  `CompanionModel z` is isomorphic to `PrefixModel`, and distinct binary sequences yield
  non-isomorphic companions;
* `omega0_lt_scottHeight_prefixModel` and `scottHeight_prefixModel_le_omega0_add_omega0`:
  `ω < scottHeight PrefixModel ≤ ω + ω`;
* `exists_internalScottRank_omega_with_large_bfClass`: existential witness form;
* `nonempty_equiv_prefixModelCode` and `nonempty_equiv_companionModelCode`: isomorphism bridges
  between `PrefixModel` / `CompanionModel z` and their configurations `prefixModelCode` /
  `companionModelCode z` on `ℕ`;
* `not_isIsolatingRank_internalScottRank`: the internal Scott rank on
  `RelationalConfiguration (lang (List ℕ) Language.empty) ℕ` is not an isolating rank;
* `IsIsolatingRank.omega0_lt_prefixModelCode`,
  `bfEquivSetoid_omega0_prefixModelCode_companionModelCode`, and
  `mk_quotient_comap_isoSetoid_bfClass_omega0_prefixModelCode`: every isolating rank strictly
  exceeds `ω` at `prefixModelCode`, whose `ω`-level back-and-forth class splits into `𝔠`
  isomorphism classes.

## Construction

An admissible row is a nondecreasing word `p : List ℕ` satisfying `p[i] ≤ i` at every index
`i < p.length`. In `PrefixModel`, built as a row assembly with fiber label type `List ℕ` over
admissible rows with pure-set fibers, the fiber at `(p, τ)` (`τ : List ℕ`) is the finite pure set
`Fin (τ.getLastD 0 + 1)` when `τ` is a prefix of `p` (in particular, `Fin 1` uniformly at
`τ = []`), and the infinite pure set `ℕ` otherwise. Because every admissible word `l : List ℕ`
satisfies `l.getLastD 0 ≤ l.length - 1`, any row `p` of length `L` is pinned among rows of
`PrefixModel` at back-and-forth depth `L + 2`, bounding every finite tuple's orbit rank below `ω`;
conversely, extending `List.range (k + 1)` by `[k]` shows no finite level stabilizes all rows.

Each `z : ℕ → Bool` defines a nondecreasing path `π_z` (`π_z (2 * n) = n`,
`π_z (2 * n + 1) = n + (z n).toNat`) and adds one infinite-path row whose finite fibers sit along
the prefixes of `π_z`. At any finite depth `m`, a Hilbert-hotel bijection absorbing the extra row
into the length-`2 * m` prefix of `π_z` matches every fiber up to depth `m` because diverging
fibers have `τ.getLastD 0 ≥ π_z (2 * m) = m`.

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

/-- Pure-set fiber attached to label `τ : List ℕ` according to a Boolean flag `b`: when `b = true`
it is the finite set `Fin (τ.getLastD 0 + 1)`, and when `b = false` it is `ℕ`. -/
private def FiberType : Bool → List ℕ → Type
  | true, τ => Fin (τ.getLastD 0 + 1)
  | false, _ => ℕ

private instance instStructureFiberType (b : Bool) (τ : List ℕ) :
    Language.empty.Structure (FiberType b τ) :=
  Language.emptyStructure

private instance instCountableFiberType (b : Bool) (τ : List ℕ) : Countable (FiberType b τ) := by
  cases b <;> dsimp [FiberType] <;> infer_instance

private instance instInfiniteFiberTypeFalse (τ : List ℕ) : Infinite (FiberType false τ) :=
  inferInstanceAs (Infinite ℕ)

private instance instFintypeFiberTypeTrue (τ : List ℕ) : Fintype (FiberType true τ) :=
  inferInstanceAs (Fintype (Fin (τ.getLastD 0 + 1)))

private theorem card_fiberType_true (τ : List ℕ) :
    Fintype.card (FiberType true τ) = τ.getLastD 0 + 1 :=
  Fintype.card_fin _

private theorem bfEquiv_fiberType_iff (b₁ b₂ : Bool) (τ : List ℕ) (k : ℕ) :
    BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType b₁ τ) (Fin.elim0 : Fin 0 → FiberType b₂ τ) ↔
      b₁ = b₂ ∨ k ≤ τ.getLastD 0 + 1 := by
  have hft : BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → FiberType false τ) (Fin.elim0 : Fin 0 → FiberType true τ) ↔
      k ≤ τ.getLastD 0 + 1 := by
    rw [bfEquiv_empty_elim0_natCast_iff_le_card, ENat.card_eq_coe_fintype_card, card_fiberType_true]
    exact_mod_cast Iff.rfl
  cases b₁ <;> cases b₂
  · simp [BFEquiv.refl]
  · simpa using hft
  · rw [BFEquiv.symm_iff]
    simpa using hft
  · simp [BFEquiv.refl]

private theorem eq_of_fiberType_equiv {b₁ b₂ : Bool} {τ : List ℕ}
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

private theorem getLastD_le_pred_length {l : List ℕ} (hl : IsAdmissible l) :
    l.getLastD 0 ≤ l.length - 1 := by
  by_cases hne : l = []
  · subst hne
    simp
  · have hpos : 0 < l.length := List.length_pos_iff.mpr hne
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some,
      List.getLast_eq_getElem]
    exact hl.2 (by omega)

private theorem isAdmissible_range (m : ℕ) : IsAdmissible (List.range m) :=
  ⟨fun _ _ _ _ hij => by simpa using hij, fun _ _ => by simp⟩

private instance instInfiniteRow : Infinite Row :=
  Infinite.of_injective (fun m : ℕ => (⟨List.range m, isAdmissible_range m⟩ : Row)) fun a b h => by
    simpa using congrArg (fun r : Row => r.val.length) h

/-- Component pure-set fibers of `PrefixModel`: finite of size `τ.getLastD 0 + 1` when
`τ <+: p.1`, and `ℕ` otherwise. -/
private abbrev BaseFiber (p : Row) (τ : List ℕ) : Type :=
  FiberType (decide (τ <+: p.val)) τ

/-- The prefix row assembly with label type `List ℕ` and pure-set fibers, having internal Scott
rank `ω`. -/
def PrefixModel : Type := Carrier Row BaseFiber

@[no_expose] noncomputable instance instStructurePrefixModel :
    (lang (List ℕ) Language.empty).Structure PrefixModel :=
  inferInstanceAs ((lang (List ℕ) Language.empty).Structure (Carrier Row BaseFiber))

instance instCountablePrefixModel : Countable PrefixModel :=
  inferInstanceAs (Countable (Carrier Row BaseFiber))

instance instInfinitePrefixModel : Infinite PrefixModel :=
  inferInstanceAs (Infinite (Carrier Row BaseFiber))

private noncomputable def prefixModelEquivCarrier :
    PrefixModel ≃[lang (List ℕ) Language.empty] Carrier Row BaseFiber where
  toEquiv := Equiv.refl _
  map_fun' := isEmptyElim
  map_rel' _ _ := Iff.rfl

/-! ### Row pinning and internal Scott rank `ω` of `PrefixModel` -/

/-- Any row `p₁` of `PrefixModel` is uniquely determined among rows of `PrefixModel` by
back-and-forth equivalence at finite depth `p₁.1.length + 2`. -/
private theorem row_eq_of_bfEquiv {N : ℕ} {a b : Fin N → Carrier Row BaseFiber} {i₀ : Fin N}
    {p₁ p₂ : Row} (ha₀ : a i₀ = .row p₁) (hb₀ : b i₀ = .row p₂)
    (h : BFEquiv (L := lang (List ℕ) Language.empty) ((p₁.val.length + 2 : ℕ) : Ordinal.{0}) N a b)
        :
    p₁ = p₂ := by
  have hpref : p₁.val <+: p₂.val := by
    by_contra hnp
    have hne : p₁.val ≠ [] := fun he => hnp (he ▸ List.nil_prefix)
    have hf := (bfEquiv_fiberType_iff _ _ p₁.val (p₁.val.length + 2)).mp
      (bfEquiv_fiber_elim0_of_eq_row h ha₀ hb₀ p₁.val)
    have hle := getLastD_le_pred_length p₁.property
    have hpos : 0 < p₁.val.length := List.length_pos_iff.mpr hne
    rcases hf with hdec | hge
    · simp [hnp] at hdec
    · omega
  have hlen : p₂.val.length ≤ p₁.val.length := by
    by_contra hlt
    have hlt' : p₁.val.length < p₂.val.length := Nat.lt_of_not_ge hlt
    let l := p₂.val.take (p₁.val.length + 1)
    have hllen : l.length = p₁.val.length + 1 := by simp [l]; omega
    have hf := (bfEquiv_fiberType_iff _ _ l (p₁.val.length + 2)).mp
      (bfEquiv_fiber_elim0_of_eq_row h ha₀ hb₀ l)
    have hnp₁ : ¬ (l <+: p₁.val) := fun hp => by
      have := hp.length_le
      omega
    have hp₂ : l <+: p₂.val := List.take_prefix _ _
    have hle : l.getLastD 0 ≤ l.length - 1 :=
      getLastD_le_pred_length (isAdmissible_take p₂.property (p₁.val.length + 1))
    rcases hf with hdec | hge
    · simp [hnp₁, hp₂] at hdec
    · omega
  exact Subtype.ext (hpref.eq_of_length_le hlen)

private theorem internalScottRank_prefixModel_le :
    internalScottRank (L := lang (List ℕ) Language.empty) (Carrier Row BaseFiber) ≤
      Ordinal.omega0 := by
  rw [internalScottRank_le_iff]
  intro n a
  let r : ℕ := Finset.sup Finset.univ fun i : Fin n => (a i).ownerRow.val.length
  let K : ℕ := (r + 2) + n
  refine (orbitRank_le a ?_).trans_lt (Ordinal.natCast_lt_omega0 K)
  rw [mem_orbitStable_iff]
  intro b hab β
  have hab' : BFEquiv (L := lang (List ℕ) Language.empty)
      (((r + 2 : ℕ) : Ordinal.{0}) + n) n a b := by
    simpa [K, Nat.cast_add] using hab
  have happ := bfEquiv_append_ownerRow hab'
  have hrow : ∀ i : Fin n, (b i).ownerRow = (a i).ownerRow := fun i => by
    have hle : (a i).ownerRow.val.length + 2 ≤ r + 2 :=
      Nat.add_le_add_right (Finset.le_sup (f := fun j : Fin n => (a j).ownerRow.val.length)
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
    Ordinal.omega0 ≤ selfStabilizationOrdinal (L := lang (List ℕ) Language.empty)
      (Carrier Row BaseFiber) := by
  refine Ordinal.omega0_le.mpr fun k => ?_
  let p₁ : Row := ⟨List.range (k + 1), isAdmissible_range (k + 1)⟩
  let p₂ : Row := ⟨List.range (k + 1) ++ [k], isAdmissible_range_snoc k⟩
  have hpne : p₁ ≠ p₂ := fun h => by
    have := congrArg (fun r : Row => r.val.length) h
    simp [p₁, p₂] at this
  let σ : Row ≃ Row := Equiv.swap p₁ p₂
  have hfib : ∀ (r : Row) (τ : List ℕ), BFEquiv (L := Language.empty) ((k + 1 : ℕ) : Ordinal.{0})
      0 (Fin.elim0 : Fin 0 → BaseFiber r τ) (Fin.elim0 : Fin 0 → BaseFiber (σ r) τ) := by
    intro r τ
    by_cases hτ : τ = p₂.val
    · have hlast : τ.getLastD 0 = k := by simp [hτ, p₂]
      exact (bfEquiv_fiberType_iff _ _ τ (k + 1)).mpr (Or.inr (by omega))
    · have hd : decide (τ <+: p₁.val) = decide (τ <+: p₂.val) := by
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
  have hab : BFEquiv (L := lang (List ℕ) Language.empty) ((k + 1 : ℕ) : Ordinal.{0}) 1 a b := by
    simpa [a, b, σ, Equiv.swap_apply_left] using
      bfEquiv_row_of_bfEquiv_elim0 σ ((k + 1 : ℕ) : Ordinal.{0}) (fun _ : Fin 1 => p₁) hfib
  have hnot : ((k + 1 : ℕ) : Ordinal.{0}) ∉ orbitStable (L := lang (List ℕ) Language.empty) a := by
    rw [mem_orbitStable_iff]
    intro hst
    exact hpne (row_eq_of_bfEquiv (i₀ := 0) rfl rfl
      (hst b hab ((p₁.val.length + 2 : ℕ) : Ordinal.{0})))
  have hlt : ((k + 1 : ℕ) : Ordinal.{0}) < orbitRank (L := lang (List ℕ) Language.empty) a := by
    rwa [← not_le, orbitRank_le_iff]
  exact ((Nat.cast_le.mpr (Nat.le_succ k)).trans hlt.le).trans
    (orbitRank_le_selfStabilizationOrdinal a)

/-- The simultaneous internal stabilization ordinal of `PrefixModel` is `ω`. -/
@[simp]
theorem selfStabilizationOrdinal_prefixModel :
    selfStabilizationOrdinal (L := lang (List ℕ) Language.empty) PrefixModel = Ordinal.omega0 :=
  prefixModelEquivCarrier.selfStabilizationOrdinal_eq.trans <|
    le_antisymm
      (selfStabilizationOrdinal_le_internalScottRank.trans internalScottRank_prefixModel_le)
      omega0_le_selfStabilizationOrdinal_prefixModel

/-- `PrefixModel` has internal Scott rank `ω`. -/
@[simp]
theorem internalScottRank_prefixModel :
    internalScottRank (L := lang (List ℕ) Language.empty) PrefixModel = Ordinal.omega0 :=
  prefixModelEquivCarrier.internalScottRank_eq.trans <|
    le_antisymm internalScottRank_prefixModel_le
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
    (pathPrefix z m).val.length = m := by
  simp [pathPrefix]

private theorem prefix_pathPrefix_iff (z : ℕ → Bool) (l : List ℕ) (k : ℕ) :
    l <+: (pathPrefix z k).val ↔ l.length ≤ k ∧ l = (pathPrefix z l.length).val := by
  refine ⟨fun h => ⟨by simpa using h.length_le, ?_⟩, fun ⟨hlen, hl⟩ => ?_⟩
  · simpa [pathPrefix, ← List.map_take, min_eq_left (by simpa using h.length_le : l.length ≤ k)]
      using List.prefix_iff_eq_take.mp h
  · rw [List.prefix_iff_eq_take]
    simpa [pathPrefix, ← List.map_take, min_eq_left hlen] using hl

/-- Component pure-set fibers of `CompanionModel z`: `BaseFiber p` on `some p`, and finite along
the prefixes of `pathOf z` on the extra path row `none`. -/
private abbrev CompanionFiber (z : ℕ → Bool) : Option Row → List ℕ → Type
  | some p, τ => BaseFiber p τ
  | none, τ => FiberType (decide (τ = (pathPrefix z τ.length).val)) τ

private instance instStructureCompanionFiber (z : ℕ → Bool) (r : Option Row) (τ : List ℕ) :
    Language.empty.Structure (CompanionFiber z r τ) := by
  cases r <;> infer_instance

private instance instCountableCompanionFiber (z : ℕ → Bool) (r : Option Row) (τ : List ℕ) :
    Countable (CompanionFiber z r τ) := by
  cases r <;> infer_instance

/-- The companion row assembly attached to `z : ℕ → Bool`. -/
def CompanionModel (z : ℕ → Bool) : Type := Carrier (Option Row) (CompanionFiber z)

@[no_expose] noncomputable instance instStructureCompanionModel (z : ℕ → Bool) :
    (lang (List ℕ) Language.empty).Structure (CompanionModel z) :=
  inferInstanceAs
    ((lang (List ℕ) Language.empty).Structure (Carrier (Option Row) (CompanionFiber z)))

instance instCountableCompanionModel (z : ℕ → Bool) : Countable (CompanionModel z) :=
  inferInstanceAs (Countable (Carrier (Option Row) (CompanionFiber z)))

instance instInfiniteCompanionModel (z : ℕ → Bool) : Infinite (CompanionModel z) :=
  inferInstanceAs (Infinite (Carrier (Option Row) (CompanionFiber z)))

private noncomputable def companionModelEquivCarrier (z : ℕ → Bool) :
    CompanionModel z ≃[lang (List ℕ) Language.empty] Carrier (Option Row) (CompanionFiber z) where
  toEquiv := Equiv.refl _
  map_fun' := isEmptyElim
  map_rel' _ _ := Iff.rfl

/-! ### Level-`ω` equivalence via Hilbert-hotel row bijections -/

section HilbertRow

private def hilbertSeq (z : ℕ → Bool) (m k : ℕ) : Row :=
  pathPrefix z (2 * m + k)

private theorem injective_hilbertSeq (z : ℕ → Bool) (m : ℕ) :
    Function.Injective (hilbertSeq z m) := fun a b h => by
  have hlen := congrArg (fun r : Row => r.val.length) h
  simp only [hilbertSeq, length_pathPrefix] at hlen
  omega

open Classical in
private noncomputable def hilbertSplit (z : ℕ → Bool) (m : ℕ) :
    Row ≃ ↥(Set.range (hilbertSeq z m))ᶜ ⊕ ℕ :=
  (Equiv.Set.sumCompl (Set.range (hilbertSeq z m))).symm.trans
    ((Equiv.sumComm _ _).trans
      (Equiv.sumCongr (.refl _)
        (Equiv.ofInjective (hilbertSeq z m) (injective_hilbertSeq z m)).symm))

private theorem hilbertSplit_symm_inr (z : ℕ → Bool) (m k : ℕ) :
    (hilbertSplit z m).symm (Sum.inr k) = hilbertSeq z m k := by
  simp [hilbertSplit]

private theorem hilbertSplit_symm_inl (z : ℕ → Bool) (m : ℕ)
    (x : ↥(Set.range (hilbertSeq z m))ᶜ) :
    (hilbertSplit z m).symm (Sum.inl x) = x.val := by
  simp [hilbertSplit]

private theorem hilbertSplit_apply_hilbertSeq (z : ℕ → Bool) (m k : ℕ) :
    hilbertSplit z m (hilbertSeq z m k) = Sum.inr k := by
  rw [← hilbertSplit_symm_inr, Equiv.apply_symm_apply]

private theorem hilbertSplit_apply_of_notMem (z : ℕ → Bool) (m : ℕ) {p : Row}
    (hp : p ∉ Set.range (hilbertSeq z m)) :
    hilbertSplit z m p = Sum.inl ⟨p, hp⟩ := by
  rw [← Equiv.eq_symm_apply, hilbertSplit_symm_inl]

private noncomputable def hilbertRow (z : ℕ → Bool) (m : ℕ) : Option Row ≃ Row :=
  (Equiv.optionEquivSumPUnit.{0} Row).trans
    (((hilbertSplit z m).sumCongr (.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (.refl _) Equiv.natEquivNatSumPUnit.symm).trans
          (hilbertSplit z m).symm)))

private theorem hilbertRow_none (z : ℕ → Bool) (m : ℕ) :
    hilbertRow z m none = pathPrefix z (2 * m) := by
  simp [hilbertRow, hilbertSplit_symm_inr, hilbertSeq,
    Equiv.natEquivNatSumPUnit]

private theorem hilbertRow_some_hilbertSeq (z : ℕ → Bool) (m k : ℕ) :
    hilbertRow z m (some (hilbertSeq z m k)) = hilbertSeq z m (k + 1) := by
  simp [hilbertRow, hilbertSplit_apply_hilbertSeq, hilbertSplit_symm_inr,
    Equiv.natEquivNatSumPUnit]

private theorem hilbertRow_some_of_notMem (z : ℕ → Bool) (m : ℕ) {p : Row}
    (hp : p ∉ Set.range (hilbertSeq z m)) :
    hilbertRow z m (some p) = p := by
  simp [hilbertRow, hilbertSplit_apply_of_notMem z m hp, hilbertSplit_symm_inl]

end HilbertRow

private theorem le_getLastD_of_eq_pathPrefix (z : ℕ → Bool) {m : ℕ} (τ : List ℕ)
    (hlen : 2 * m < τ.length) (hτ : τ = (pathPrefix z τ.length).val) :
    m ≤ τ.getLastD 0 + 1 := by
  have hne : τ ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlast : τ.getLastD 0 = pathOf z (τ.length - 1) := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some,
      List.getLast_eq_getElem]
    have hget := congrArg (fun l : List ℕ => l[τ.length - 1]?) hτ
    have hi : τ.length - 1 < τ.length := by omega
    have hi' : τ.length - 1 < (pathPrefix z τ.length).val.length := by simpa using hi
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at hget
    simpa [pathPrefix] using Option.some.inj hget
  have hm : m ≤ pathOf z (τ.length - 1) := by
    rw [← pathOf_two_mul z m]
    exact pathOf_mono z (by omega)
  omega

private theorem bfEquiv_companionFiber_none_pathPrefix (z : ℕ → Bool) {m k : ℕ}
    (hk : 2 * m ≤ k) (τ : List ℕ) :
    BFEquiv (L := Language.empty) (m : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → CompanionFiber z none τ)
      (Fin.elim0 : Fin 0 → BaseFiber (pathPrefix z k) τ) := by
  apply (bfEquiv_fiberType_iff _ _ τ m).mpr
  by_cases hτ : τ = (pathPrefix z τ.length).val
  · by_cases hlen : τ.length ≤ k
    · left
      have hp : τ <+: (pathPrefix z k).val := (prefix_pathPrefix_iff z τ k).mpr ⟨hlen, hτ⟩
      rw [decide_eq_true hτ, decide_eq_true hp]
    · exact Or.inr (le_getLastD_of_eq_pathPrefix z τ (by omega) hτ)
  · left
    have hnp : ¬ (τ <+: (pathPrefix z k).val) := fun hp =>
      hτ ((prefix_pathPrefix_iff z τ k).mp hp).2
    rw [decide_eq_false hτ, decide_eq_false hnp]

/-- Every companion `CompanionModel z` is back-and-forth equivalent to `PrefixModel` at level
`ω`. -/
theorem bfEquiv_omega0_companionModel_prefixModel (z : ℕ → Bool) :
    BFEquiv (L := lang (List ℕ) Language.empty) Ordinal.omega0.{0} 0
      (Fin.elim0 : Fin 0 → CompanionModel z) (Fin.elim0 : Fin 0 → PrefixModel) := by
  have hcar : BFEquiv (L := lang (List ℕ) Language.empty) Ordinal.omega0.{0} 0
      (Fin.elim0 : Fin 0 → Carrier (Option Row) (CompanionFiber z))
      (Fin.elim0 : Fin 0 → Carrier Row BaseFiber) := by
    rw [BFEquiv.limit Ordinal.isSuccLimit_omega0]
    intro β hβ
    obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hβ
    refine bfEquiv_elim0_of_bfEquiv_elim0 (hilbertRow z m) (m : Ordinal.{0}) fun r τ => ?_
    cases r with
    | none =>
      rw [hilbertRow_none]
      exact bfEquiv_companionFiber_none_pathPrefix z le_rfl τ
    | some p =>
      by_cases hp : p ∈ Set.range (hilbertSeq z m)
      · rcases hp with ⟨k, rfl⟩
        rw [hilbertRow_some_hilbertSeq]
        exact (bfEquiv_companionFiber_none_pathPrefix z (by omega : 2 * m ≤ 2 * m + k) τ).symm.trans
          (bfEquiv_companionFiber_none_pathPrefix z (by omega : 2 * m ≤ 2 * m + (k + 1)) τ)
      · rw [hilbertRow_some_of_notMem z m hp]
        exact BFEquiv.refl _ _
  have h₁ : BFEquiv (L := lang (List ℕ) Language.empty) Ordinal.omega0.{0} 0
      (Fin.elim0 : Fin 0 → CompanionModel z)
      (Fin.elim0 : Fin 0 → Carrier (Option Row) (CompanionFiber z)) := by
    have h := (companionModelEquivCarrier z).bfEquiv Ordinal.omega0.{0}
      (Fin.elim0 : Fin 0 → CompanionModel z)
    rwa [Subsingleton.elim ((companionModelEquivCarrier z) ∘ Fin.elim0) Fin.elim0] at h
  have h₂ : BFEquiv (L := lang (List ℕ) Language.empty) Ordinal.omega0.{0} 0
      (Fin.elim0 : Fin 0 → Carrier Row BaseFiber)
      (Fin.elim0 : Fin 0 → PrefixModel) := by
    have h := prefixModelEquivCarrier.symm.bfEquiv Ordinal.omega0.{0}
      (Fin.elim0 : Fin 0 → Carrier Row BaseFiber)
    rwa [Subsingleton.elim (prefixModelEquivCarrier.symm ∘ Fin.elim0) Fin.elim0] at h
  exact (h₁.trans hcar).trans h₂

/-! ### Non-isomorphism and Scott-height consequences -/

/-- The infinite-path row `none` in `CompanionModel z` cannot match any finite-word row `p` on all
fibers simultaneously, because `pathPrefix z (p.1.length + 1)` has a finite fiber over `none` and an
infinite fiber over `p`. -/
private theorem false_of_fiberToEquiv_none (z : ℕ → Bool) (p : Row)
    (f : ∀ τ, CompanionFiber z none τ ≃ BaseFiber p τ) : False := by
  let τ : List ℕ := (pathPrefix z (p.val.length + 1)).val
  have heq : decide (τ = (pathPrefix z τ.length).val) = decide (τ <+: p.val) :=
    eq_of_fiberType_equiv (f τ)
  simp only [τ, length_pathPrefix, decide_true, true_eq_decide_iff] at heq
  have hlen := heq.length_le
  simp at hlen

/-- No companion `CompanionModel z` is isomorphic to `PrefixModel`. -/
theorem isEmpty_equiv_companionModel_prefixModel (z : ℕ → Bool) :
    IsEmpty (CompanionModel z ≃[lang (List ℕ) Language.empty] PrefixModel) :=
  ⟨fun e =>
    let e' := prefixModelEquivCarrier.comp (e.comp (companionModelEquivCarrier z).symm)
    false_of_fiberToEquiv_none z (e'.rowEquiv none) (e'.fiberToEquiv none)⟩

/-- Distinct binary sequences yield non-isomorphic companions. -/
theorem isEmpty_equiv_companionModel_of_ne {z z' : ℕ → Bool} (h : z ≠ z') :
    IsEmpty (CompanionModel z ≃[lang (List ℕ) Language.empty] CompanionModel z') := by
  refine ⟨fun e => ?_⟩
  let e' := (companionModelEquivCarrier z').comp (e.comp (companionModelEquivCarrier z).symm)
  have hnone : e'.rowEquiv none = none := by
    cases hr : e'.rowEquiv none with
    | none => rfl
    | some p =>
      exact False.elim (false_of_fiberToEquiv_none z p fun τ => by
        have hf := e'.fiberToEquiv none τ
        rw [hr] at hf
        exact hf)
  obtain ⟨n, hn⟩ := Function.ne_iff.mp h
  let τ : List ℕ := (pathPrefix z (2 * n + 2)).val
  have heq : decide (τ = (pathPrefix z τ.length).val) =
      decide (τ = (pathPrefix z' τ.length).val) := by
    have hf := e'.fiberToEquiv none τ
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
    Ordinal.omega0 < scottHeight (L := lang (List ℕ) Language.empty) PrefixModel := by
  by_contra! hle
  obtain ⟨e⟩ := nonempty_equiv_of_bfEquiv_of_scottHeight_le hle
    (bfEquiv_omega0_companionModel_prefixModel (fun _ => false)).symm
  exact (isEmpty_equiv_companionModel_prefixModel (fun _ => false)).false e.symm

/-- The Scott height of `PrefixModel` is at most `ω + ω`. -/
theorem scottHeight_prefixModel_le_omega0_add_omega0 :
    scottHeight (L := lang (List ℕ) Language.empty) PrefixModel ≤
      Ordinal.omega0 + Ordinal.omega0 := by
  simpa using scottHeight_le_internalScottRank_add_omega0
    (L := lang (List ℕ) Language.empty) PrefixModel

/-- There is a countable `(lang (List ℕ) Language.empty)`-structure of internal Scott rank `ω`
(with Scott height strictly above `ω`) together with a Cantor-indexed family of pairwise
non-isomorphic countable companions, none isomorphic to it, all back-and-forth equivalent to it at
level `ω`. -/
theorem exists_internalScottRank_omega_with_large_bfClass :
    ∃ (M : Type) (_ : (lang (List ℕ) Language.empty).Structure M) (_ : Countable M)
      (N : (ℕ → Bool) → Type) (_ : ∀ z, (lang (List ℕ) Language.empty).Structure (N z))
      (_ : ∀ z, Countable (N z)),
      internalScottRank (L := lang (List ℕ) Language.empty) M = Ordinal.omega0 ∧
      Ordinal.omega0 < scottHeight (L := lang (List ℕ) Language.empty) M ∧
      (∀ z, BFEquiv (L := lang (List ℕ) Language.empty) Ordinal.omega0.{0} 0
        (Fin.elim0 : Fin 0 → N z) (Fin.elim0 : Fin 0 → M)) ∧
      (∀ z, IsEmpty (N z ≃[lang (List ℕ) Language.empty] M)) ∧
      (∀ z z', z ≠ z' → IsEmpty (N z ≃[lang (List ℕ) Language.empty] N z')) :=
  ⟨PrefixModel, inferInstance, inferInstance, CompanionModel, fun _ => inferInstance,
    fun _ => inferInstance, internalScottRank_prefixModel, omega0_lt_scottHeight_prefixModel,
    bfEquiv_omega0_companionModel_prefixModel, isEmpty_equiv_companionModel_prefixModel,
    fun _ _ h => isEmpty_equiv_companionModel_of_ne h⟩

/-! ### Consequences for configurations on `ℕ` and isolating ranks -/

/-- Encoding of `PrefixModel` as a relational configuration on `ℕ`. -/
noncomputable def prefixModelCode :
    RelationalConfiguration (lang (List ℕ) Language.empty) ℕ :=
  (nonempty_equiv_of_countable.some : PrefixModel ≃ ℕ).encodeVia

/-- Encoding of `CompanionModel z` as a relational configuration on `ℕ`. -/
noncomputable def companionModelCode (z : ℕ → Bool) :
    RelationalConfiguration (lang (List ℕ) Language.empty) ℕ :=
  (nonempty_equiv_of_countable.some : CompanionModel z ≃ ℕ).encodeVia

/-- `prefixModelCode` decodes to a structure on `ℕ` isomorphic to `PrefixModel`. -/
theorem nonempty_equiv_prefixModelCode :
    Nonempty (@Language.Equiv (lang (List ℕ) Language.empty) PrefixModel ℕ _
      prefixModelCode.toStructure) := by
  unfold prefixModelCode
  exact Equiv.nonempty_equiv_encodeVia _

/-- `companionModelCode z` decodes to a structure on `ℕ` isomorphic to `CompanionModel z`. -/
theorem nonempty_equiv_companionModelCode (z : ℕ → Bool) :
    Nonempty (@Language.Equiv (lang (List ℕ) Language.empty) (CompanionModel z) ℕ _
      (companionModelCode z).toStructure) := by
  unfold companionModelCode
  exact Equiv.nonempty_equiv_encodeVia _

/-- The decoded structure of `prefixModelCode` has internal Scott rank `ω`. -/
theorem internalScottRank_prefixModelCode :
    (letI := prefixModelCode.toStructure;
      internalScottRank (L := lang (List ℕ) Language.empty) ℕ) = Ordinal.omega0 := by
  let := prefixModelCode.toStructure
  obtain ⟨E⟩ := nonempty_equiv_prefixModelCode
  exact E.symm.internalScottRank_eq.trans internalScottRank_prefixModel

/-- Every `companionModelCode z` lies in the `ω`-level back-and-forth class of
`prefixModelCode`. -/
theorem bfEquivSetoid_omega0_prefixModelCode_companionModelCode (z : ℕ → Bool) :
    RelationalConfiguration.bfEquivSetoid (lang (List ℕ) Language.empty) ℕ Ordinal.omega0.{0}
      prefixModelCode (companionModelCode z) := by
  rw [prefixModelCode, companionModelCode, Equiv.bfEquivSetoid_encodeVia_iff]
  exact (bfEquiv_omega0_companionModel_prefixModel z).symm

/-- No `companionModelCode z` is isomorphic as a configuration on `ℕ` to `prefixModelCode`. -/
@[simp]
theorem not_isoSetoid_prefixModelCode_companionModelCode (z : ℕ → Bool) :
    ¬ RelationalConfiguration.isoSetoid (lang (List ℕ) Language.empty) ℕ
      prefixModelCode (companionModelCode z) := by
  rw [prefixModelCode, companionModelCode, Equiv.isoSetoid_encodeVia_iff]
  rintro ⟨e⟩
  exact (isEmpty_equiv_companionModel_prefixModel z).false e.symm

/-- Two companion configurations on `ℕ` are isomorphic if and only if they come from the same
binary sequence. -/
@[simp]
theorem isoSetoid_companionModelCode_iff (z z' : ℕ → Bool) :
    RelationalConfiguration.isoSetoid (lang (List ℕ) Language.empty) ℕ
      (companionModelCode z) (companionModelCode z') ↔ z = z' := by
  refine ⟨fun hiso => ?_, fun h => h ▸ (RelationalConfiguration.isoSetoid _ _).refl _⟩
  by_contra hne
  rw [companionModelCode, companionModelCode, Equiv.isoSetoid_encodeVia_iff] at hiso
  exact hiso.elim (isEmpty_equiv_companionModel_of_ne hne).false

/-- Every isolating rank on `RelationalConfiguration (lang (List ℕ) Language.empty) ℕ` assigns to
`prefixModelCode` a value strictly greater than `ω`. -/
theorem _root_.TauCeti.IsIsolatingRank.omega0_lt_prefixModelCode
    {ρ : RelationalConfiguration (lang (List ℕ) Language.empty) ℕ → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) :
    Ordinal.omega0 < ρ prefixModelCode := by
  by_contra! hle
  exact not_isoSetoid_prefixModelCode_companionModelCode (fun _ => false)
    (hρ.isolates_of_le hle
      (bfEquivSetoid_omega0_prefixModelCode_companionModelCode (fun _ => false)))

/-- The internal Scott rank on `RelationalConfiguration (lang (List ℕ) Language.empty) ℕ` is not
an isolating rank. -/
theorem not_isIsolatingRank_internalScottRank :
    ¬ IsIsolatingRank (L := lang (List ℕ) Language.empty)
        (fun c => letI := c.toStructure;
          internalScottRank (L := lang (List ℕ) Language.empty) ℕ) := by
  intro h
  exact (h.omega0_lt_prefixModelCode.trans_eq internalScottRank_prefixModelCode).false

/-- The single `ω`-level back-and-forth equivalence class of `prefixModelCode` splits into
continuum-many isomorphism classes on `ℕ`. -/
theorem mk_quotient_comap_isoSetoid_bfClass_omega0_prefixModelCode :
    Cardinal.mk (Quotient
      ((RelationalConfiguration.isoSetoid (lang (List ℕ) Language.empty) ℕ).comap
        (Subtype.val : {d | RelationalConfiguration.bfEquivSetoid
          (lang (List ℕ) Language.empty) ℕ Ordinal.omega0.{0} prefixModelCode d} → _))) =
      Cardinal.continuum := by
  let K : Set (RelationalConfiguration (lang (List ℕ) Language.empty) ℕ) :=
    {d | RelationalConfiguration.bfEquivSetoid
      (lang (List ℕ) Language.empty) ℕ Ordinal.omega0.{0} prefixModelCode d}
  apply le_antisymm
  · exact Cardinal.mk_quotient_le.trans
      ((Cardinal.mk_subtype_le _).trans
        (RelationalConfiguration.mk_le_continuum (lang (List ℕ) Language.empty) ℕ))
  · let emb : (ℕ → Bool) →
        Quotient ((RelationalConfiguration.isoSetoid (lang (List ℕ) Language.empty) ℕ).comap
          (Subtype.val : K → _)) :=
      fun z => Quotient.mk _ ⟨companionModelCode z,
        bfEquivSetoid_omega0_prefixModelCode_companionModelCode z⟩
    have hinj : Function.Injective emb := fun z z' heq =>
      (isoSetoid_companionModelCode_iff z z').mp
        (Quotient.exact (s := (RelationalConfiguration.isoSetoid
          (lang (List ℕ) Language.empty) ℕ).comap (Subtype.val : K → _)) heq)
    calc Cardinal.continuum = Cardinal.mk (ℕ → Bool) := by simp
      _ ≤ _ := Cardinal.mk_le_of_injective hinj

end TauCeti.RowAssembly
