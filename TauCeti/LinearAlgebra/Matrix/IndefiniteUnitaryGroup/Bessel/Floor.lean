/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SubringCongruence
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel.Basic

/-!
# Floor groups, Weyl elements and the Bessel subgroup of the split unitary group

Let `R` be a commutative ring with involution and `G_T` the unitary group of the split form
`TauCeti.splitGram ϱ T` on the basis `e₀, …, e_{ϱ-1}, x_i (i ∈ κ), z, e*₀, …, e*_{ϱ-1}`, whose
vectors carry a level and a floor (`TauCeti.splitLevel`, `TauCeti.besselFloor`). This file
defines the subgroups of `G_T` along which the hyperbolic pairs are removed one floor at a time,
and proves the first properties of these groups that a Bruhat decomposition of `G_T` relative to
the unipotent Bessel group `U = TauCeti.besselU ϱ T` rests on:

* the tower of floor groups: the fixers `H_l` of the floors below `l` decrease, the groups
  `𝒩_{<l}` (`TauCeti.unipotentBelow`) increase to `U`, and the groups `Q_l`
  (`TauCeti.partialUnitriangularSubgroup`) decrease to `U` and contain `U` and `H_l`;
* the leading principal minors `δ_j` of the frame Gram matrix (`Matrix.frameMinor`) are invariant
  under `γ ↦ s⁻¹ γ s'` for `s, s' ∈ Q_l` and `j ≤ l`, hence constant on the double cosets `U γ U`;
* the Weyl elements `w_p` (`TauCeti.splitWeylElement`), which exchange `e_a` and `e*_a` up to
  units for `a < l`, have `δ_j(w_p) = p₀ ⋯ p_{j-1}` for `j ≤ l ≤ ϱ` and commute with `H_l`;
* the Bessel subgroup `S = Q_{ϱ+1}` (`TauCeti.besselS`) normalises `U`;
* the sum `σ` of the entries just above the diagonal of the frame block
  (`TauCeti.besselSimpleRootSum`) is additive on `S` and vanishes on `H = H_{ϱ+1}`
  (`TauCeti.besselH`);
* for a subring `𝒪` and a unit `g`, the `h ∈ H` with `h y ∈ U K_𝒪(g)` lie in a single right coset
  of `H ∩ K_𝒪(g)`, where `K_𝒪(g)` (`TauCeti.besselCongruenceSubgroup`) is the principal congruence
  subgroup of `G_T` of level `g` over `𝒪`.

## Main definitions

* `TauCeti.unipotentBelow ϱ T l`: the group `𝒩_{<l}` of isometries that are block unitriangular
  when the basis vectors of floor below `l` keep their level and the others get level `ϱ`.
* `TauCeti.floorUnipotent ϱ T l`: the group `𝒩_l = H_l ∩ 𝒩_{<l+1}`.
* `TauCeti.partialUnitriangularSubgroup ϱ T l`: the group `Q_l`; for `l ≤ ϱ + 1` it consists of the
  isometries `g` with `g f_b - f_b ∈ ⟨e_c : c < b⟩` for the frame vectors `f_b`, `b < l`
  (`TauCeti.mem_partialUnitriangularSubgroup_iff_frame`), and for `l ≥ ϱ + 2` it is `U`.
* `TauCeti.besselS ϱ T`, `TauCeti.besselH ϱ T`: the Bessel subgroup `S = Q_{ϱ+1}` and the group
  `H = H_{ϱ+1}` of isometries fixing every `e_a`, `e*_a` and `z`.
* `TauCeti.splitWeylElement l p T`: the Weyl element `w_p` with `e_a ↦ p_a e*_a` and
  `e*_a ↦ (star p_a)⁻¹ e_a` for `a < l`, fixing the other basis vectors.
* `TauCeti.besselSimpleRootSum γ`: the sum `σ(γ)` of the entries `γ_{f_a, f_{a+1}}`.
* `Matrix.frameMinor T γ j`: the leading principal minor `δ_j(γ)` of the frame Gram matrix.
* `TauCeti.besselCongruenceSubgroup ϱ T 𝒪 g`: the subgroup `K_𝒪(g)` of `G_T`.

## Main results

* `TauCeti.floorFixingSubgroup_antitone`, `TauCeti.unipotentBelow_monotone`,
  `TauCeti.partialUnitriangularSubgroup_antitone` and the extreme cases
  `TauCeti.floorFixingSubgroup_zero`, `TauCeti.floorFixingSubgroup_eq_bot`,
  `TauCeti.unipotentBelow_eq_besselU`, `TauCeti.partialUnitriangularSubgroup_eq_besselU`.
* `TauCeti.besselU_le_partialUnitriangularSubgroup`,
  `TauCeti.floorFixingSubgroup_le_partialUnitriangularSubgroup`: `U ⊆ Q_l` and `H_l ⊆ Q_l`.
* `TauCeti.frameMinor_inv_mul_mul`: `δ_j(s⁻¹ γ s') = δ_j(γ)` for `s, s' ∈ Q_l` and `j ≤ l`;
  `TauCeti.frameMinor_inv_mul_mul_of_mem_besselU` is the case of `U`.
* `TauCeti.frameMinor_splitWeylElement`, `TauCeti.commute_splitWeylElement`: the leading minors
  of `w_p`, and `w_p` commutes with `H_l`; `TauCeti.splitWeylElement_inv`: `w_p⁻¹ = w_{star p}`.
* `TauCeti.besselS_le_normalizer_besselU`: `S` normalises `U`.
* `TauCeti.besselSimpleRootSum_mul`, `TauCeti.besselSimpleRootSum_inv`,
  `TauCeti.besselSimpleRootSum_eq_zero_of_mem_besselH`: `σ` is additive on `S` and vanishes on `H`.
* `TauCeti.mul_inv_mem_besselCongruenceSubgroup`: if `u h y` and `u' h' y` lie in `K_𝒪(g)` with
  `u, u' ∈ U` and `h, h' ∈ H`, then `h' h⁻¹ ∈ K_𝒪(g)`.

## References

The definitions of `𝒩_{<l}`, `𝒩_l`, `Q_l`, the Weyl elements and `σ`, and the plan of the proofs,
follow the Lean project grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), file `src/Lib/DiscreteSeries/Bruhat/FloorGroups.lean` (declarations
`New.Shape.Form.unipotentBelow`, `New.Floors.FloorGroups.floorUnipotent`,
`New.Shape.Form.partialUnitriangularGroup`, `New.Floors.FloorGroups.weylElem`,
`New.simpleRootSum`, `New.besselS_le_normalizer_besselU`,
`New.div_mem_unitaryLevel_of_besselU_mul`).
For the Bruhat decomposition and the Bessel data of a pair of unitary groups compare
* V. Platonov and A. Rapinchuk, *Algebraic groups and number theory* (1994), §7.1;
* W. T. Gan, B. H. Gross and D. Prasad, *Symplectic local root numbers, central critical
  L-values, and restriction problems in the representation theory of classical groups*,
  Astérisque 346 (2012).
-/

public section

open Matrix

namespace TauCeti

/-! ### The floor groups -/

section Subgroups

variable {R : Type*} [CommRing R] [StarRing R] (ϱ : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]
  (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R)

/-- The group `𝒩_{<l}`: the isometries that are block upper unitriangular when the basis vectors
of floor below `l` keep their level and all other basis vectors get the middle level `ϱ`. -/
def unipotentBelow (l : ℕ) : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (unitriangularSubgroup (fun i : BesselIndex ϱ κ ↦ if besselFloor i < l then splitLevel i else ϱ)
    R).subgroupOf _

/-- The group `𝒩_l = H_l ∩ 𝒩_{<l+1}`. -/
def floorUnipotent (l : ℕ) : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  floorFixingSubgroup ϱ T l ⊓ unipotentBelow ϱ T (l + 1)

/-- The group `Q_l`: the isometries that agree with the identity matrix at every entry `(i, j)`
with `level j ≤ level i` whose column `j` has floor and level below `l`, and, when `ϱ + 1 < l`, at
every entry with `level j ≤ level i`. For `l ≤ ϱ + 1` these are the isometries `g` with
`g f_b - f_b ∈ ⟨e_c : c < b⟩` for every frame vector `f_b` with `b < l`
(`TauCeti.mem_partialUnitriangularSubgroup_iff_frame`), and for `l ≥ ϱ + 2` this is `U`
(`TauCeti.partialUnitriangularSubgroup_eq_besselU`). -/
def partialUnitriangularSubgroup (l : ℕ) : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (agreeWithOneOn (fun i j : BesselIndex ϱ κ ↦ splitLevel j ≤ splitLevel i ∧
      (besselFloor j < l ∧ splitLevel j < l ∨ ϱ + 1 < l)) R <| by
    -- If `level j ≤ level k`, the entry `(k, j)` is prescribed; otherwise the entry `(i, k)` is,
    -- since the floor of `k` is at most `level k + 1 ≤ level j`.
    intro i k j ⟨hji, hj⟩
    rcases le_or_gt (splitLevel j) (splitLevel k) with hjk | hkj
    · exact .inr ⟨hjk, hj⟩
    · have := besselFloor_le_splitLevel_add_one k
      exact .inl ⟨hkj.le.trans hji, by omega⟩).subgroupOf _

/-- The **Bessel subgroup** `S = Q_{ϱ+1}`: the isometries `s` with `s f_b - f_b` in the span of
the earlier frame vectors, for every vector `f_b` of the frame `(e₀, …, e_{ϱ-1}, z)`. -/
abbrev besselS : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  partialUnitriangularSubgroup ϱ T (ϱ + 1)

/-- The group `H = H_{ϱ+1}` of the isometries that fix every `e_a`, every `e*_a` and `z`. -/
abbrev besselH : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  floorFixingSubgroup ϱ T (ϱ + 1)

variable {ϱ T}

/-- Membership in `𝒩_{<l}`, entry by entry. -/
@[simp]
theorem mem_unipotentBelow {l : ℕ} {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ unipotentBelow ϱ T l ↔ ∀ i j : BesselIndex ϱ κ,
      (if besselFloor j < l then splitLevel j else ϱ) ≤
          (if besselFloor i < l then splitLevel i else ϱ) →
        ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j =
          (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j := by
  rw [unipotentBelow, Subgroup.mem_subgroupOf, mem_unitriangularSubgroup,
    blockUnitriangular_iff_forall_le]

/-- Membership in `𝒩_l`: an element of `H_l` that lies in `𝒩_{<l+1}`. -/
@[simp]
theorem mem_floorUnipotent {l : ℕ} {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ floorUnipotent ϱ T l ↔ g ∈ floorFixingSubgroup ϱ T l ∧ g ∈ unipotentBelow ϱ T (l + 1) :=
  Iff.rfl

/-- Membership in `Q_l`, entry by entry. -/
@[simp]
theorem mem_partialUnitriangularSubgroup {l : ℕ} {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ partialUnitriangularSubgroup ϱ T l ↔ ∀ i j : BesselIndex ϱ κ,
      splitLevel j ≤ splitLevel i → besselFloor j < l ∧ splitLevel j < l ∨ ϱ + 1 < l →
        ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j =
          (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j := by
  rw [partialUnitriangularSubgroup, Subgroup.mem_subgroupOf, mem_agreeWithOneOn]
  exact forall₂_congr fun _ _ ↦ and_imp

/-- For `l ≤ ϱ + 1`, an isometry `g` lies in `Q_l` exactly when, for every frame vector `f_b` with
`b < l`, the vector `g f_b - f_b` lies in the span of the `e_c` with `c < b`. -/
theorem mem_partialUnitriangularSubgroup_iff_frame {l : ℕ} (hl : l ≤ ϱ + 1)
    {g : unitaryGroupOf (splitGram ϱ T)} :
    g ∈ partialUnitriangularSubgroup ϱ T l ↔ ∀ b : Fin (ϱ + 1), (b : ℕ) < l →
      ∀ i : BesselIndex ϱ κ, (∀ c : Fin ϱ, i = .inl c → (b : ℕ) ≤ c) →
        ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i
            (besselFrame b) =
          (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i (besselFrame b) := by
  rw [mem_partialUnitriangularSubgroup]
  refine ⟨fun h b hb i hi ↦ h i _ ?_ (.inl ⟨by simpa using hb, by simpa using hb⟩),
    fun h i j hji hj ↦ ?_⟩
  · -- Only the `e_c` with `c < b` have level below `b`.
    rw [splitLevel_besselFrame]
    by_contra! hlt
    obtain ⟨c, rfl⟩ := exists_eq_inl_of_splitLevel_lt hlt (by omega)
    have := hi c rfl
    simp only [splitLevel_inl] at hlt
    omega
  · obtain ⟨hjf, hjl⟩ := hj.resolve_right (by omega)
    obtain ⟨b, hb, rfl⟩ := exists_besselFrame_eq_of_besselFloor_lt hjf hjl hl
    refine h b hb i fun c hc ↦ ?_
    simpa [hc] using hji

/-! ### The tower of floor groups -/

/-- The fixers `H_l` of the floors below `l` decrease with `l`. -/
theorem floorFixingSubgroup_antitone : Antitone (floorFixingSubgroup ϱ T) :=
  fun _ _ hll' _ hg ↦ (mem_floorFixingSubgroup ϱ T).2 fun i j hj ↦
    (mem_floorFixingSubgroup ϱ T).1 hg i j (hj.trans_le hll')

@[simp]
theorem floorFixingSubgroup_zero : floorFixingSubgroup ϱ T 0 = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ (mem_floorFixingSubgroup ϱ T).2 fun _ _ h ↦ absurd h (Nat.not_lt_zero _)

/-- The fixer `H_l` is trivial for `l ≥ ϱ + 2`, as every floor is at most `ϱ + 1`. -/
theorem floorFixingSubgroup_eq_bot {l : ℕ} (hl : ϱ + 2 ≤ l) : floorFixingSubgroup ϱ T l = ⊥ :=
  eq_bot_iff.2 fun g hg ↦ Subgroup.mem_bot.2 <| Subtype.ext <| Units.ext <| Matrix.ext fun i j ↦
    (mem_floorFixingSubgroup ϱ T).1 hg i j (by have := besselFloor_le j; omega)

/-- The groups `𝒩_{<l}` increase with `l`. -/
theorem unipotentBelow_monotone : Monotone (unipotentBelow ϱ T) := by
  refine monotone_nat_of_le_succ fun l g hg ↦ mem_unipotentBelow.2 fun i j hij ↦
    mem_unipotentBelow.1 hg i j ?_
  -- Only the levels of the two vectors of floor `l` change, from `ϱ` to their true level.
  rcases i with a | (i | u) | a <;> rcases j with b | (j | v) | b <;>
    simp only [besselFloor_inl, besselFloor_x, besselFloor_z, besselFloor_eStar, splitLevel_inl,
      splitLevel_middle, splitLevel_eStar] at hij ⊢ <;>
    split_ifs at hij ⊢ <;> omega

/-- For `l ≥ ϱ` the group `𝒩_{<l}` is the unipotent Bessel group `U`. -/
theorem unipotentBelow_eq_besselU {l : ℕ} (hl : ϱ ≤ l) : unipotentBelow ϱ T l = besselU ϱ T := by
  -- The basis vectors of floor at least `l ≥ ϱ` lie in the middle block, of level `ϱ`.
  have h (i : BesselIndex ϱ κ) :
      (if besselFloor i < l then splitLevel i else ϱ) = splitLevel i := by
    split_ifs with hi
    · rfl
    · rcases i with a | (i | u) | a
      · simp only [besselFloor_inl] at hi; omega
      · exact (splitLevel_middle _).symm
      · exact (splitLevel_middle _).symm
      · simp only [besselFloor_eStar] at hi; omega
  ext g
  simp only [mem_unipotentBelow, mem_besselU_iff_forall_le, h]

/-- The groups `Q_l` decrease with `l`. -/
theorem partialUnitriangularSubgroup_antitone : Antitone (partialUnitriangularSubgroup ϱ T) :=
  fun _ _ hll' _ hg ↦ mem_partialUnitriangularSubgroup.2 fun i j hji hj ↦
    mem_partialUnitriangularSubgroup.1 hg i j hji (by omega)

/-- For `l ≥ ϱ + 2` the group `Q_l` is the unipotent Bessel group `U`. -/
theorem partialUnitriangularSubgroup_eq_besselU {l : ℕ} (hl : ϱ + 2 ≤ l) :
    partialUnitriangularSubgroup ϱ T l = besselU ϱ T := by
  ext g
  rw [mem_partialUnitriangularSubgroup, mem_besselU_iff_forall_le]
  exact forall₂_congr fun i j ↦ ⟨fun h hji ↦ h hji (.inr (by omega)), fun h hji _ ↦ h hji⟩

/-- The unipotent Bessel group `U` lies in every `Q_l`. -/
theorem besselU_le_partialUnitriangularSubgroup (l : ℕ) :
    besselU ϱ T ≤ partialUnitriangularSubgroup ϱ T l :=
  fun _ hg ↦ mem_partialUnitriangularSubgroup.2 fun i j hji _ ↦
    (mem_besselU_iff_forall_le ϱ T).1 hg i j hji

/-- The fixer `H_l` of the floors below `l` lies in `Q_l`. -/
theorem floorFixingSubgroup_le_partialUnitriangularSubgroup (l : ℕ) :
    floorFixingSubgroup ϱ T l ≤ partialUnitriangularSubgroup ϱ T l :=
  fun _ hg ↦ mem_partialUnitriangularSubgroup.2 fun i j _ hj ↦
    (mem_floorFixingSubgroup ϱ T).1 hg i j (by have := besselFloor_le j; omega)

/-- The group `H` lies in the Bessel subgroup `S`. -/
theorem besselH_le_besselS : besselH ϱ T ≤ besselS ϱ T :=
  floorFixingSubgroup_le_partialUnitriangularSubgroup _

/-! ### Rows of isometries -/

/-- The row `e*_a` of an element of `H_l` is that of `1` for `a < l`. -/
theorem floorFixingSubgroup_apply_eStar {l : ℕ} {s : unitaryGroupOf (splitGram ϱ T)}
    (hs : s ∈ floorFixingSubgroup ϱ T l) {a : Fin ϱ} (ha : (a : ℕ) < l) (k : BesselIndex ϱ κ) :
    ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
        (.inr (.inr a)) k =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inr (.inr a)) k :=
  ((splitGram_mul_apply_inl T _ a k).symm.trans
    (mul_val_apply_eq_apply_of_mem_unitaryGroupOf s.property
      (fun m ↦ (mem_floorFixingSubgroup ϱ T).1 hs m _ (by simpa using ha)) k)).trans
    (splitGram_apply_inl T a k)

/-- The row `e_a` of an element of `H_l` is that of `1` for `a < l`. -/
theorem floorFixingSubgroup_apply_inl {l : ℕ} {s : unitaryGroupOf (splitGram ϱ T)}
    (hs : s ∈ floorFixingSubgroup ϱ T l) {a : Fin ϱ} (ha : (a : ℕ) < l) (k : BesselIndex ϱ κ) :
    ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inl a) k =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inl a) k :=
  ((splitGram_mul_apply_eStar T _ a k).symm.trans
    (mul_val_apply_eq_apply_of_mem_unitaryGroupOf s.property
      (fun m ↦ (mem_floorFixingSubgroup ϱ T).1 hs m _ (by simpa using ha)) k)).trans
    (splitGram_apply_eStar T a k)

end Subgroups

end TauCeti

/-! ### Leading minors of the frame Gram matrix -/

namespace Matrix

open TauCeti

section FrameMinor

variable {R : Type*} [CommRing R] {ϱ : ℕ} {κ : Type*} [Fintype κ]
  (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R) (γ : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)

/-- The leading principal minor `δ_j(γ)` of order `j ≤ ϱ + 1` of the frame Gram matrix
`(h(f_a, γ f_b))_{a, b}` of `γ`, for the split form of `T`; `δ_0(γ) = 1`. -/
def frameMinor (j : Fin (ϱ + 2)) : R :=
  ((frameGram T γ).submatrix (Fin.castLE j.is_le) (Fin.castLE j.is_le)).det

theorem frameMinor_def (j : Fin (ϱ + 2)) :
    frameMinor T γ j = ((frameGram T γ).submatrix (Fin.castLE j.is_le) (Fin.castLE j.is_le)).det :=
  (rfl)

/-- `δ_j(γ)` is the minor of `J γ` on the first `j` frame vectors. -/
theorem frameMinor_eq_det_submatrix (j : Fin (ϱ + 2)) :
    frameMinor T γ j = ((splitGram ϱ T * γ).submatrix (besselFrame ∘ Fin.castLE j.is_le)
      (besselFrame ∘ Fin.castLE j.is_le)).det := by
  rw [frameMinor_def]
  congr 1
  ext a b
  simp

@[simp]
theorem frameMinor_zero : frameMinor T γ 0 = 1 := by
  rw [frameMinor_def]
  have : IsEmpty (Fin ((0 : Fin (ϱ + 2)) : ℕ)) := by simp only [Fin.val_zero]; infer_instance
  exact det_isEmpty

end FrameMinor

end Matrix

namespace TauCeti

open Matrix

section FrameMinor

variable {R : Type*} [CommRing R] [StarRing R] {ϱ : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
  {T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R}

/-- An element `s` of `Q_l` changes each frame vector `f_b` with `b < l` by earlier frame vectors,
so a right factor `s` keeps the minors of order `j ≤ l` of a matrix on the frame. -/
theorem det_submatrix_besselFrame_mul {l : ℕ} {s : unitaryGroupOf (splitGram ϱ T)}
    (hs : s ∈ partialUnitriangularSubgroup ϱ T l) (X : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
    (j : Fin (ϱ + 2)) (hj : (j : ℕ) ≤ l) :
    ((X * ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)).submatrix
        (besselFrame ∘ Fin.castLE j.is_le) (besselFrame ∘ Fin.castLE j.is_le)).det =
      (X.submatrix (besselFrame ∘ Fin.castLE j.is_le) (besselFrame ∘ Fin.castLE j.is_le)).det := by
  have := j.is_le
  refine det_submatrix_mul_of_apply_eq_one_apply X _
    (besselFrame_injective.comp (Fin.castLE_injective _)) fun k b hk ↦ ?_
  have hb := b.isLt
  refine mem_partialUnitriangularSubgroup.1 hs k _ ?_
    (.inl ⟨by simp only [Function.comp_apply, besselFloor_besselFrame, Fin.val_castLE]; omega,
      by simp only [Function.comp_apply, splitLevel_besselFrame, Fin.val_castLE]; omega⟩)
  -- A row of level below `b` is some `e_c` with `c < b`, an earlier frame vector.
  simp only [Function.comp_apply, splitLevel_besselFrame, Fin.val_castLE]
  by_contra! hlt
  obtain ⟨c, rfl⟩ := exists_eq_inl_of_splitLevel_lt hlt (by omega)
  simp only [splitLevel_inl] at hlt
  have := hk ⟨c, by omega⟩ ((besselFrame_eq_inl (b := Fin.castLE j.is_le ⟨c, by omega⟩)
    (by simp)).trans (congrArg Sum.inl (Fin.ext (by simp))))
  simp only [Fin.le_iff_val_le_val] at this
  omega

/-- **The leading minors of the frame Gram matrix are invariant under `Q_l`.** For `s, s' ∈ Q_l`
and `j ≤ l`, `δ_j(s⁻¹ γ s') = δ_j(γ)`. -/
theorem frameMinor_inv_mul_mul {l : ℕ} {s s' : unitaryGroupOf (splitGram ϱ T)}
    (hs : s ∈ partialUnitriangularSubgroup ϱ T l) (hs' : s' ∈ partialUnitriangularSubgroup ϱ T l)
    (γ : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (j : Fin (ϱ + 2)) (hj : (j : ℕ) ≤ l) :
    frameMinor T ((((s⁻¹ : unitaryGroupOf (splitGram ϱ T)) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) * γ *
        ((s' : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)) j =
      frameMinor T γ j := by
  set S : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R :=
    ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
  set f : Fin j → BesselIndex ϱ κ := besselFrame ∘ Fin.castLE j.is_le
  -- `J s⁻¹ = sᴴ J`, so `J s⁻¹ γ s' = ((J γ)ᴴ s)ᴴ s'`, and the conjugate transpose turns the left
  -- factor into a right one.
  have h_inv : splitGram ϱ T *
      (((s⁻¹ : unitaryGroupOf (splitGram ϱ T)) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) = Sᴴ * splitGram ϱ T := by
    rw [Subgroup.coe_inv, mul_val_inv_eq_star_mul_of_mem_unitaryGroupOf s.property,
      star_eq_conjTranspose]
  have h_form : splitGram ϱ T * (((s⁻¹ : unitaryGroupOf (splitGram ϱ T)) :
      GL (BesselIndex ϱ κ) R) * γ *
        ((s' : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)) =
      ((splitGram ϱ T * γ)ᴴ * S)ᴴ *
        ((s' : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      h_inv, Matrix.mul_assoc Sᴴ]
  have h_conj (M : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) :
      (Mᴴ.submatrix f f).det = star (M.submatrix f f).det := by
    rw [← conjTranspose_submatrix, det_conjTranspose]
  rw [frameMinor_eq_det_submatrix, frameMinor_eq_det_submatrix, h_form,
    det_submatrix_besselFrame_mul hs' _ j hj, h_conj, det_submatrix_besselFrame_mul hs _ j hj,
    h_conj, star_star]

/-- The leading minors of the frame Gram matrix are constant on the double cosets `U γ U`. -/
theorem frameMinor_inv_mul_mul_of_mem_besselU {u u' : unitaryGroupOf (splitGram ϱ T)}
    (hu : u ∈ besselU ϱ T) (hu' : u' ∈ besselU ϱ T)
    (γ : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (j : Fin (ϱ + 2)) :
    frameMinor T ((((u⁻¹ : unitaryGroupOf (splitGram ϱ T)) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) * γ *
        ((u' : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)) j =
      frameMinor T γ j :=
  frameMinor_inv_mul_mul (besselU_le_partialUnitriangularSubgroup (ϱ + 2) hu)
    (besselU_le_partialUnitriangularSubgroup (ϱ + 2) hu') γ j (by have := j.is_le; omega)

end FrameMinor

/-! ### Weyl elements -/

section Weyl

variable {R : Type*} [CommRing R] [StarRing R] (ϱ : ℕ) {μ : Type*} [DecidableEq μ]

/-- The matrix of the Weyl element of the first `l` hyperbolic pairs with parameters `p`: it sends
`e_a ↦ p_a e*_a` and `e*_a ↦ (star p_a)⁻¹ e_a` for `a < l`, and fixes the other basis vectors. -/
def splitWeylMatrix (l : ℕ) (p : Fin ϱ → Rˣ) : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R :=
  fromBlocks (diagonal fun a ↦ if (a : ℕ) < l then 0 else 1)
    (fromCols 0 (diagonal fun a ↦ if (a : ℕ) < l then (((star (p a))⁻¹ : Rˣ) : R) else 0))
    (fromRows 0 (diagonal fun a ↦ if (a : ℕ) < l then (p a : R) else 0))
    (fromBlocks 1 0 0 (diagonal fun a ↦ if (a : ℕ) < l then 0 else 1))

variable {ϱ} (l : ℕ) (p : Fin ϱ → Rˣ)

@[simp] lemma splitWeylMatrix_inl_inl (a b : Fin ϱ) :
    splitWeylMatrix (μ := μ) ϱ l p (.inl a) (.inl b) =
      diagonal (fun a : Fin ϱ ↦ if (a : ℕ) < l then (0 : R) else 1) a b := (rfl)
@[simp] lemma splitWeylMatrix_inl_middle (a : Fin ϱ) (j : μ) :
    splitWeylMatrix ϱ l p (.inl a) (.inr (.inl j)) = 0 := (rfl)
@[simp] lemma splitWeylMatrix_inl_eStar (a b : Fin ϱ) :
    splitWeylMatrix (μ := μ) ϱ l p (.inl a) (.inr (.inr b)) =
      diagonal (fun a : Fin ϱ ↦ if (a : ℕ) < l then (((star (p a))⁻¹ : Rˣ) : R) else 0) a b :=
  (rfl)
@[simp] lemma splitWeylMatrix_middle_inl (i : μ) (b : Fin ϱ) :
    splitWeylMatrix ϱ l p (.inr (.inl i)) (.inl b) = 0 := (rfl)
@[simp] lemma splitWeylMatrix_middle_middle (i j : μ) :
    splitWeylMatrix ϱ l p (.inr (.inl i)) (.inr (.inl j)) = (1 : Matrix μ μ R) i j := (rfl)
@[simp] lemma splitWeylMatrix_middle_eStar (i : μ) (b : Fin ϱ) :
    splitWeylMatrix ϱ l p (.inr (.inl i)) (.inr (.inr b)) = 0 := (rfl)
@[simp] lemma splitWeylMatrix_eStar_inl (a b : Fin ϱ) :
    splitWeylMatrix (μ := μ) ϱ l p (.inr (.inr a)) (.inl b) =
      diagonal (fun a : Fin ϱ ↦ if (a : ℕ) < l then (p a : R) else 0) a b := (rfl)
@[simp] lemma splitWeylMatrix_eStar_middle (a : Fin ϱ) (j : μ) :
    splitWeylMatrix ϱ l p (.inr (.inr a)) (.inr (.inl j)) = 0 := (rfl)
@[simp] lemma splitWeylMatrix_eStar_eStar (a b : Fin ϱ) :
    splitWeylMatrix (μ := μ) ϱ l p (.inr (.inr a)) (.inr (.inr b)) =
      diagonal (fun a : Fin ϱ ↦ if (a : ℕ) < l then (0 : R) else 1) a b := (rfl)

variable [Fintype μ]

/-- Left multiplication by the Weyl matrix, in the row `e_a`. -/
theorem splitWeylMatrix_mul_apply_inl (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (a : Fin ϱ)
    (k : SplitIndex ϱ μ) :
    (splitWeylMatrix (μ := μ) ϱ l p * M) (.inl a) k =
      if (a : ℕ) < l then (((star (p a))⁻¹ : Rˣ) : R) * M (.inr (.inr a)) k
      else M (.inl a) k := by
  by_cases ha : (a : ℕ) < l <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply, ha]

/-- Left multiplication by the Weyl matrix, in a row of the middle block. -/
theorem splitWeylMatrix_mul_apply_middle (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (i : μ)
    (k : SplitIndex ϱ μ) :
    (splitWeylMatrix (μ := μ) ϱ l p * M) (.inr (.inl i)) k = M (.inr (.inl i)) k := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- Left multiplication by the Weyl matrix, in the row `e*_a`. -/
theorem splitWeylMatrix_mul_apply_eStar (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (a : Fin ϱ)
    (k : SplitIndex ϱ μ) :
    (splitWeylMatrix (μ := μ) ϱ l p * M) (.inr (.inr a)) k =
      if (a : ℕ) < l then (p a : R) * M (.inl a) k else M (.inr (.inr a)) k := by
  by_cases ha : (a : ℕ) < l <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply, ha]

/-- Left multiplication by the conjugate transpose of the Weyl matrix, in the row `e_a`. -/
theorem star_splitWeylMatrix_mul_apply_inl (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R)
    (a : Fin ϱ) (k : SplitIndex ϱ μ) :
    (star (splitWeylMatrix (μ := μ) ϱ l p) * M) (.inl a) k =
      if (a : ℕ) < l then star (p a : R) * M (.inr (.inr a)) k else M (.inl a) k := by
  by_cases ha : (a : ℕ) < l <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply, Matrix.star_apply, ha,
      apply_ite star, ite_mul, Finset.sum_ite_eq']

/-- Left multiplication by the conjugate transpose of the Weyl matrix, in a row of the middle
block. -/
theorem star_splitWeylMatrix_mul_apply_middle (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R)
    (i : μ) (k : SplitIndex ϱ μ) :
    (star (splitWeylMatrix (μ := μ) ϱ l p) * M) (.inr (.inl i)) k = M (.inr (.inl i)) k := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.star_apply, apply_ite star]

/-- Left multiplication by the conjugate transpose of the Weyl matrix, in the row `e*_a`. -/
theorem star_splitWeylMatrix_mul_apply_eStar (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R)
    (a : Fin ϱ) (k : SplitIndex ϱ μ) :
    (star (splitWeylMatrix (μ := μ) ϱ l p) * M) (.inr (.inr a)) k =
      if (a : ℕ) < l then star (((star (p a))⁻¹ : Rˣ) : R) * M (.inl a) k
      else M (.inr (.inr a)) k := by
  by_cases ha : (a : ℕ) < l <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply, Matrix.star_apply, ha,
      apply_ite star, ite_mul, Finset.sum_ite_eq']

/-- Right multiplication by the Weyl matrix, in the column `e_b`. -/
theorem mul_splitWeylMatrix_apply_inl (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R)
    (i : SplitIndex ϱ μ) (b : Fin ϱ) :
    (M * splitWeylMatrix (μ := μ) ϱ l p) i (.inl b) =
      if (b : ℕ) < l then M i (.inr (.inr b)) * (p b : R) else M i (.inl b) := by
  by_cases hb : (b : ℕ) < l <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply, hb]

/-- Right multiplication by the Weyl matrix, in a column of the middle block. -/
theorem mul_splitWeylMatrix_apply_middle (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R)
    (i : SplitIndex ϱ μ) (j : μ) :
    (M * splitWeylMatrix (μ := μ) ϱ l p) i (.inr (.inl j)) = M i (.inr (.inl j)) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- Right multiplication by the Weyl matrix, in the column `e*_b`. -/
theorem mul_splitWeylMatrix_apply_eStar (M : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R)
    (i : SplitIndex ϱ μ) (b : Fin ϱ) :
    (M * splitWeylMatrix (μ := μ) ϱ l p) i (.inr (.inr b)) =
      if (b : ℕ) < l then M i (.inl b) * (((star (p b))⁻¹ : Rˣ) : R)
      else M i (.inr (.inr b)) := by
  by_cases hb : (b : ℕ) < l <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply, hb]

/-- The Weyl matrix with the conjugate parameters is the inverse of the Weyl matrix. -/
theorem splitWeylMatrix_mul_splitWeylMatrix_star :
    splitWeylMatrix (μ := μ) ϱ l p * splitWeylMatrix ϱ l (star p) = 1 := by
  have key (a : Fin ϱ) : star (((p a)⁻¹ : Rˣ) : R) * star (p a : R) = 1 := by
    simpa using Units.inv_mul (star (p a))
  ext (a | i | a) k
  · rw [splitWeylMatrix_mul_apply_inl]
    by_cases ha : (a : ℕ) < l <;> rcases k with b | j | b <;>
      simp [ha, diagonal_apply, Matrix.one_apply, key]
  · rw [splitWeylMatrix_mul_apply_middle]
    rcases k with b | j | b <;> simp [Matrix.one_apply]
  · rw [splitWeylMatrix_mul_apply_eStar]
    by_cases ha : (a : ℕ) < l <;> rcases k with b | j | b <;>
      simp [ha, diagonal_apply, Matrix.one_apply]

/-- The Weyl matrix is an isometry of the split form, for every middle block `T`. -/
theorem star_splitWeylMatrix_mul_splitGram_mul_splitWeylMatrix (T : Matrix μ μ R) :
    star (splitWeylMatrix ϱ l p) * splitGram ϱ T * splitWeylMatrix ϱ l p = splitGram ϱ T := by
  have key (a : Fin ϱ) : star (p a : R) * star (((p a)⁻¹ : Rˣ) : R) = 1 := by
    simpa using Units.mul_inv (star (p a))
  ext (a | i | a) k
  · rw [Matrix.mul_assoc, star_splitWeylMatrix_mul_apply_inl, splitGram_mul_apply_eStar,
      splitGram_mul_apply_inl]
    by_cases ha : (a : ℕ) < l <;> rcases k with b | j | b <;>
      simp [ha, diagonal_apply, Matrix.one_apply, key]
  · rw [Matrix.mul_assoc, star_splitWeylMatrix_mul_apply_middle, splitGram_mul_apply_middle]
    rcases k with b | j | b <;> simp [Matrix.one_apply]
  · rw [Matrix.mul_assoc, star_splitWeylMatrix_mul_apply_eStar, splitGram_mul_apply_inl,
      splitGram_mul_apply_eStar]
    by_cases ha : (a : ℕ) < l <;> rcases k with b | j | b <;>
      simp [ha, diagonal_apply, Matrix.one_apply]

variable (T : Matrix μ μ R)

/-- The **Weyl element** `w_p` of the first `l` hyperbolic pairs: the isometry with
`e_a ↦ p_a e*_a` and `e*_a ↦ (star p_a)⁻¹ e_a` for `a < l`, fixing the other basis vectors. -/
def splitWeylElement : unitaryGroupOf (splitGram ϱ T) :=
  ⟨⟨splitWeylMatrix ϱ l p, splitWeylMatrix ϱ l (star p),
      splitWeylMatrix_mul_splitWeylMatrix_star l p, by
      simpa using splitWeylMatrix_mul_splitWeylMatrix_star l (star p)⟩,
    mem_unitaryGroupOf_iff.2 (star_splitWeylMatrix_mul_splitGram_mul_splitWeylMatrix l p T)⟩

@[simp]
theorem coe_splitWeylElement :
    ((splitWeylElement l p T : GL (SplitIndex ϱ μ) R) :
        Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) =
      splitWeylMatrix ϱ l p :=
  (rfl)

/-- The inverse of the Weyl element `w_p` is the Weyl element `w_{star p}`. -/
@[simp]
theorem splitWeylElement_inv : (splitWeylElement l p T)⁻¹ = splitWeylElement l (star p) T :=
  inv_eq_of_mul_eq_one_right <| Subtype.ext <| Units.ext <| by
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_splitWeylElement, Subgroup.coe_one,
      Units.val_one] using splitWeylMatrix_mul_splitWeylMatrix_star l p

end Weyl

section WeylFloor

variable {R : Type*} [CommRing R] [StarRing R] {ϱ : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
  {T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R}

/-- **The leading minors of a Weyl element.** For `l ≤ ϱ` and `j ≤ l`, the leading minor of order
`j` of the frame Gram matrix of the Weyl element `w_p` of the first `l` pairs is `p₀ ⋯ p_{j-1}`. -/
theorem frameMinor_splitWeylElement {l : ℕ} (hl : l ≤ ϱ) (p : Fin ϱ → Rˣ) (j : Fin (ϱ + 2))
    (hj : (j : ℕ) ≤ l) :
    frameMinor T ((splitWeylElement l p T : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) j =
      ∏ a : Fin j, (p (Fin.castLE (hj.trans hl) a) : R) := by
  -- The first `j` frame vectors are `e_a`, which `w_p` sends to `p_a e*_a`: the block is diagonal.
  have h_block : (frameGram T ((splitWeylElement l p T : GL (BesselIndex ϱ κ) R) :
      Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)).submatrix (Fin.castLE j.is_le)
        (Fin.castLE j.is_le) = diagonal fun a : Fin j ↦ (p (Fin.castLE (hj.trans hl) a) : R) := by
    ext a b
    have ha := a.isLt
    have hb := b.isLt
    rw [submatrix_apply, frameGram_apply, coe_splitWeylElement,
      besselFrame_eq_inl (b := Fin.castLE j.is_le a) (by simp; omega),
      besselFrame_eq_inl (b := Fin.castLE j.is_le b) (by simp; omega), splitGram_mul_apply_inl,
      splitWeylMatrix_eStar_inl, diagonal_apply, diagonal_apply]
    simp only [Fin.val_castLE, Fin.mk.injEq, Fin.val_inj, show (a : ℕ) < l by omega, ↓reduceIte]
    exact if_congr Iff.rfl
      (congrArg (fun c ↦ ((p c : Rˣ) : R)) (Fin.ext (Fin.val_castLE _ a).symm)) rfl
  rw [frameMinor_def, h_block, det_diagonal]

/-- **A Weyl element commutes with the fixer of its floors.** The Weyl element of the first `l`
hyperbolic pairs commutes with every element of `H_l`. -/
theorem commute_splitWeylElement {l : ℕ} (p : Fin ϱ → Rˣ) {s : unitaryGroupOf (splitGram ϱ T)}
    (hs : s ∈ floorFixingSubgroup ϱ T l) : Commute (splitWeylElement l p T) s := by
  -- The rows and the columns of `s` on the pairs `a < l` are those of `1`.
  have hrow₁ (a : Fin ϱ) (ha : (a : ℕ) < l) (k : BesselIndex ϱ κ) :
      ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inl a) k =
        (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inl a) k :=
    floorFixingSubgroup_apply_inl hs ha k
  have hrow₂ (a : Fin ϱ) (ha : (a : ℕ) < l) (k : BesselIndex ϱ κ) :
      ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
          (.inr (.inr a)) k =
        (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inr (.inr a)) k :=
    floorFixingSubgroup_apply_eStar hs ha k
  have hcol₁ (m : BesselIndex ϱ κ) (b : Fin ϱ) (hb : (b : ℕ) < l) :
      ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) m (.inl b) =
        (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) m (.inl b) :=
    (mem_floorFixingSubgroup ϱ T).1 hs m _ (by simpa using hb)
  have hcol₂ (m : BesselIndex ϱ κ) (b : Fin ϱ) (hb : (b : ℕ) < l) :
      ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) m
          (.inr (.inr b)) =
        (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) m (.inr (.inr b)) :=
    (mem_floorFixingSubgroup ϱ T).1 hs m _ (by simpa using hb)
  refine Subtype.ext <| Units.ext ?_
  simp only [Subgroup.coe_mul, Units.val_mul, coe_splitWeylElement]
  ext (a | i | a) (b | j | b) <;>
    simp only [splitWeylMatrix_mul_apply_inl, splitWeylMatrix_mul_apply_middle,
      splitWeylMatrix_mul_apply_eStar, mul_splitWeylMatrix_apply_inl,
      mul_splitWeylMatrix_apply_middle, mul_splitWeylMatrix_apply_eStar]
  -- In each block, split on whether the pairs involved are exchanged.
  · by_cases ha : (a : ℕ) < l <;> by_cases hb : (b : ℕ) < l <;>
      rcases eq_or_ne a b with rfl | hab <;> simp [*]
  · by_cases ha : (a : ℕ) < l <;> simp [*]
  · by_cases ha : (a : ℕ) < l <;> by_cases hb : (b : ℕ) < l <;>
      rcases eq_or_ne a b with rfl | hab <;> simp [*]
  · by_cases hb : (b : ℕ) < l <;> simp [*]
  · by_cases hb : (b : ℕ) < l <;> simp [*]
  · by_cases ha : (a : ℕ) < l <;> by_cases hb : (b : ℕ) < l <;>
      rcases eq_or_ne a b with rfl | hab <;> simp [*]
  · by_cases ha : (a : ℕ) < l <;> simp [*]
  · by_cases ha : (a : ℕ) < l <;> by_cases hb : (b : ℕ) < l <;>
      rcases eq_or_ne a b with rfl | hab <;> simp [*]

end WeylFloor

/-! ### The Bessel subgroup normalises `U` -/

section Normalizer

variable {R : Type*} [CommRing R] [StarRing R] {ϱ : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
  {T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R}

/-- For `s ∈ Q_l` and `a < l`, the row `e*_a` of `s` is that of `1` outside the columns `e*_b` with
`b < a`. -/
theorem partialUnitriangularSubgroup_apply_eStar {l : ℕ} {s : unitaryGroupOf (splitGram ϱ T)}
    (hs : s ∈ partialUnitriangularSubgroup ϱ T l) {a : Fin ϱ} (ha : (a : ℕ) < l)
    {k : BesselIndex ϱ κ} (hk : ∀ b : Fin ϱ, (b : ℕ) < a → k ≠ .inr (.inr b)) :
    ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
        (.inr (.inr a)) k =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inr (.inr a)) k := by
  set S : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R :=
    ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
  set S' : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R :=
    (((s⁻¹ : unitaryGroupOf (splitGram ϱ T)) : GL (BesselIndex ϱ κ) R) :
      Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
  -- The row `e_a` of `J s = (s⁻¹)ᴴ J` is the row `e*_a` of `s`, and the column `e_a` of
  -- `s⁻¹ ∈ Q_l` is that of `1` at the levels at least `a`.
  have h_form : splitGram ϱ T * S = star S' * splitGram ϱ T := by
    simpa [S, S'] using mul_val_inv_eq_star_mul_of_mem_unitaryGroupOf (s⁻¹).property
  have h_col (x : BesselIndex ϱ κ) (hx : (a : ℕ) ≤ splitLevel x) :
      S' x (.inl a) = (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) x (.inl a) :=
    mem_partialUnitriangularSubgroup.1 (inv_mem hs) x (.inl a) (by simpa using hx)
      (.inl ⟨by simpa using ha, by simpa using ha⟩)
  calc S (.inr (.inr a)) k = (splitGram ϱ T * S) (.inl a) k :=
        (splitGram_mul_apply_inl T S a k).symm
    _ = (star S' * splitGram ϱ T) (.inl a) k := by rw [h_form]
    _ = (star (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) * splitGram ϱ T) (.inl a) k := by
        simp only [Matrix.mul_apply, Matrix.star_apply]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        by_cases hx : (a : ℕ) ≤ splitLevel x
        · rw [h_col x hx]
        · -- Otherwise `x` is some `e_c` with `c < a`, and the row `e_c` of `J` vanishes at `k`.
          obtain ⟨c, rfl⟩ := exists_eq_inl_of_splitLevel_lt (not_le.1 hx) (by omega)
          simp only [splitLevel_inl, not_le] at hx
          rw [splitGram_apply_inl, Matrix.one_apply_ne (hk c hx).symm, mul_zero, mul_zero]
    _ = (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inr (.inr a)) k := by
        rw [star_one, Matrix.one_mul, splitGram_apply_inl]

/-- The elements of the Bessel subgroup `S` are block upper triangular for the levels. -/
theorem blockTriangular_of_mem_besselS {s : unitaryGroupOf (splitGram ϱ T)}
    (hs : s ∈ besselS ϱ T) :
    ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R).BlockTriangular
      splitLevel := by
  intro i j hij
  rw [← Matrix.one_apply_ne (fun h : i = j ↦ hij.ne (h ▸ rfl))]
  by_cases hj : besselFloor j < ϱ + 1 ∧ splitLevel j < ϱ + 1
  · exact mem_partialUnitriangularSubgroup.1 hs i j hij.le (.inl hj)
  · -- Otherwise `j` has level at least `ϱ`, so `i`, of larger level, is some `e*_a`.
    have hjl : ϱ ≤ splitLevel j := by
      rcases j with b | (j | u) | b
      · simp only [besselFloor_inl, splitLevel_inl] at hj; omega
      · exact (splitLevel_middle _).ge
      · exact (splitLevel_middle _).ge
      · simp only [splitLevel_eStar]; omega
    obtain ⟨a, rfl⟩ := exists_eq_eStar_of_lt_splitLevel (hjl.trans_lt hij)
    refine partialUnitriangularSubgroup_apply_eStar hs (by omega) fun b hb h ↦ ?_
    subst h
    simp only [splitLevel_eStar] at hij
    omega

/-- **The Bessel subgroup normalises the unipotent Bessel group.** -/
theorem besselS_le_normalizer_besselU :
    besselS ϱ T ≤ Subgroup.normalizer (besselU ϱ T : Set (unitaryGroupOf (splitGram ϱ T))) := by
  intro s hs
  have hd : (s : GL (BesselIndex ϱ κ) R) ∈ blockTriangularGroup R splitLevel :=
    mem_blockTriangularGroup_iff.2 (blockTriangular_of_mem_besselS hs)
  refine Subgroup.mem_normalizer_iff.2 fun u ↦ ?_
  simp only [mem_besselU, ← mem_unitriangularSubgroup, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨fun hu ↦ ?_, fun hu ↦ ?_⟩
  · simpa using conj_mem_unitriangularSubgroup ((blockTriangularGroup R splitLevel).inv_mem hd) hu
  · simpa [mul_assoc] using conj_mem_unitriangularSubgroup hd hu

end Normalizer

/-! ### The sum of the entries just above the diagonal of the frame block -/

section SimpleRootSum

variable {R : Type*} [CommRing R] [StarRing R] {ϱ : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
  {T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R}

/-- The sum `σ(γ) = Σ_{a < ϱ} γ_{f_a, f_{a+1}}` of the entries just above the diagonal of the block
of `γ` on the frame `(e₀, …, e_{ϱ-1}, z)`. -/
def besselSimpleRootSum (γ : unitaryGroupOf (splitGram ϱ T)) : R :=
  ∑ a : Fin ϱ, ((γ : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
    (besselFrame a.castSucc) (besselFrame a.succ)

theorem besselSimpleRootSum_def (γ : unitaryGroupOf (splitGram ϱ T)) :
    besselSimpleRootSum γ =
      ∑ a : Fin ϱ, ((γ : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
        (besselFrame a.castSucc) (besselFrame a.succ) :=
  (rfl)

/-- The entries of an element of `S` vanish below the frame vector `f_b` in its column, except on
the diagonal, where they are `1`. -/
private theorem besselS_apply_besselFrame {s : unitaryGroupOf (splitGram ϱ T)}
    (hs : s ∈ besselS ϱ T) (b : Fin (ϱ + 1)) (k : BesselIndex ϱ κ) (hk : (b : ℕ) ≤ splitLevel k) :
    ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) k
        (besselFrame b) = (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) k (besselFrame b) :=
  mem_partialUnitriangularSubgroup.1 hs k _ (by simpa using hk)
    (.inl ⟨by simpa using b.isLt, by simpa using b.isLt⟩)

@[simp]
theorem besselSimpleRootSum_one : besselSimpleRootSum (1 : unitaryGroupOf (splitGram ϱ T)) = 0 :=
  Finset.sum_eq_zero fun a _ ↦ Matrix.one_apply_ne
    (besselFrame_injective.ne (Fin.castSucc_lt_succ (i := a)).ne)

/-- **`σ` is additive on the Bessel subgroup.** -/
theorem besselSimpleRootSum_mul {s u : unitaryGroupOf (splitGram ϱ T)} (hs : s ∈ besselS ϱ T)
    (hu : u ∈ besselS ϱ T) :
    besselSimpleRootSum (s * u) = besselSimpleRootSum s + besselSimpleRootSum u := by
  simp only [besselSimpleRootSum_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  set x : BesselIndex ϱ κ := besselFrame a.castSucc
  set y : BesselIndex ϱ κ := besselFrame a.succ
  have hxy : y ≠ x := besselFrame_injective.ne (Fin.castSucc_lt_succ (i := a)).ne'
  -- In the entry `(x, y)` of `s u` only the summation indices `y` and `x` contribute: the column
  -- `y` of `u` vanishes at the other indices of level at least `a + 1`, and the row `x` of `s` at
  -- the indices of level below `a`, which are earlier frame vectors.
  have h_entry : ((s * u : unitaryGroupOf (splitGram ϱ T)) : GL (BesselIndex ϱ κ) R) x y =
      ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) x y *
          ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) y y +
        ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) x x *
          ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) x y := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine Fintype.sum_eq_add y x hxy fun k ⟨hky, hkx⟩ ↦ ?_
    by_cases hk : (a : ℕ) + 1 ≤ splitLevel k
    · rw [besselS_apply_besselFrame hu a.succ k (by simpa using hk), Matrix.one_apply_ne hky,
        mul_zero]
    · -- Here `k` is some `e_c` with `c ≤ a`, and `c ≠ a` as `k ≠ x`.
      obtain ⟨c, rfl⟩ := exists_eq_inl_of_splitLevel_lt (not_le.1 hk) (by omega)
      simp only [splitLevel_inl, not_le] at hk
      have hxa : x = .inl a := besselFrame_castSucc a
      have hc : (c : ℕ) < a := by
        rcases Nat.lt_or_ge (c : ℕ) a with h | h
        · exact h
        · exact absurd (by rw [hxa]; exact congrArg Sum.inl (Fin.ext (by omega))) hkx
      rw [show (Sum.inl c : BesselIndex ϱ κ) = besselFrame c.castSucc from
          (besselFrame_castSucc c).symm,
        besselS_apply_besselFrame hs c.castSucc x (by simpa [x] using hc.le),
        Matrix.one_apply_ne (besselFrame_injective.ne (by simpa [Fin.ext_iff] using hc.ne')),
        zero_mul]
  have hxx : ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) x x =
      1 := (besselS_apply_besselFrame hs a.castSucc x (by simp [x])).trans (Matrix.one_apply_eq x)
  have hyy : ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) y y =
      1 := (besselS_apply_besselFrame hu a.succ y (by simp [y])).trans (Matrix.one_apply_eq y)
  rw [h_entry, hxx, hyy, mul_one, one_mul]

/-- `σ(s⁻¹) = -σ(s)` on the Bessel subgroup. -/
theorem besselSimpleRootSum_inv {s : unitaryGroupOf (splitGram ϱ T)} (hs : s ∈ besselS ϱ T) :
    besselSimpleRootSum s⁻¹ = -besselSimpleRootSum s := by
  have h := besselSimpleRootSum_mul hs (inv_mem hs)
  rw [mul_inv_cancel, besselSimpleRootSum_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- `σ` vanishes on `H`, whose columns at the frame vectors are those of `1`. -/
theorem besselSimpleRootSum_eq_zero_of_mem_besselH {h : unitaryGroupOf (splitGram ϱ T)}
    (hh : h ∈ besselH ϱ T) : besselSimpleRootSum h = 0 :=
  Finset.sum_eq_zero fun a _ ↦ ((mem_floorFixingSubgroup ϱ T).1 hh _ _ (by simp)).trans
    (Matrix.one_apply_ne (besselFrame_injective.ne (Fin.castSucc_lt_succ (i := a)).ne))

end SimpleRootSum

/-! ### Principal congruence subgroups and the group `H` -/

section Congruence

variable {R : Type*} [CommRing R] [StarRing R] (ϱ : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]
  (T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R)

/-- The **principal congruence subgroup** `K_𝒪(g)` of `G_T` of level `g` over a subring `𝒪`: the
isometries `γ` with entries in `𝒪`, whose inverse has entries in `𝒪`, and with `g⁻¹ (γ - 1)`
integral over `𝒪`. -/
def besselCongruenceSubgroup (𝒪 : Subring R) (g : Rˣ) : Subgroup (unitaryGroupOf (splitGram ϱ T)) :=
  (subringCongruenceSubgroup (BesselIndex ϱ κ) 𝒪 g).subgroupOf _

variable {ϱ T}

/-- Membership in `K_𝒪(g)`: as an element of `GL`, the isometry lies in the congruence subgroup of
level `g` over `𝒪`. -/
@[simp]
theorem mem_besselCongruenceSubgroup {𝒪 : Subring R} {g : Rˣ}
    {γ : unitaryGroupOf (splitGram ϱ T)} :
    γ ∈ besselCongruenceSubgroup ϱ T 𝒪 g ↔
      (γ : GL (BesselIndex ϱ κ) R) ∈ subringCongruenceSubgroup (BesselIndex ϱ κ) 𝒪 g :=
  Subgroup.mem_subgroupOf

/-- For `u ∈ U` and `h ∈ H`, every entry of `h` is the entry at the same place of `u h` or of
`1`. -/
theorem besselH_apply_eq_or {u h : unitaryGroupOf (splitGram ϱ T)} (hu : u ∈ besselU ϱ T)
    (hh : h ∈ besselH ϱ T) (i j : BesselIndex ϱ κ) :
    ((h : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j =
        ((u * h : unitaryGroupOf (splitGram ϱ T)) : GL (BesselIndex ϱ κ) R) i j ∨
      ((h : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j =
        (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i j := by
  by_cases hj : besselFloor j < ϱ + 1
  · exact .inr ((mem_floorFixingSubgroup ϱ T).1 hh i j hj)
  rcases i with a | i | a
  · exact .inr (floorFixingSubgroup_apply_inl hh (by omega) j)
  · -- In a middle row, `u` agrees with `1` up to the columns `e*_b`, where `h` vanishes.
    refine .inl ?_
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    conv_lhs => rw [← Matrix.one_mul (((h : GL (BesselIndex ϱ κ) R) :
      Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)), Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : splitLevel k ≤ ϱ
    · rw [(mem_besselU_iff_forall_le ϱ T).1 hu _ k (by simpa using hk)]
    · obtain ⟨b, rfl⟩ := exists_eq_eStar_of_lt_splitLevel (not_le.1 hk)
      have hbj : (.inr (.inr b) : BesselIndex ϱ κ) ≠ j := fun h' ↦
        hj (by rw [← h', besselFloor_eStar]; omega)
      rw [floorFixingSubgroup_apply_eStar hh (by omega), Matrix.one_apply_ne hbj, mul_zero,
        mul_zero]
  · exact .inr (floorFixingSubgroup_apply_eStar hh (by omega) j)

/-- If `u h ∈ K_𝒪(g)` with `u ∈ U` and `h ∈ H`, then `h ∈ K_𝒪(g)`. -/
theorem mem_besselCongruenceSubgroup_of_besselU_mul {𝒪 : Subring R} {g : Rˣ}
    {u h : unitaryGroupOf (splitGram ϱ T)} (hu : u ∈ besselU ϱ T) (hh : h ∈ besselH ϱ T)
    (huh : u * h ∈ besselCongruenceSubgroup ϱ T 𝒪 g) : h ∈ besselCongruenceSubgroup ϱ T 𝒪 g := by
  -- `(u h)⁻¹ = (h⁻¹ u⁻¹ h) h⁻¹` has the same shape, since `H` normalises `U`; so every entry of
  -- `h` and of `h⁻¹` is an entry of `u h`, of `(u h)⁻¹` or of `1`.
  have hconj : h⁻¹ * u⁻¹ * h ∈ besselU ϱ T := by
    simpa using (Subgroup.mem_normalizer_iff''.1
      (besselS_le_normalizer_besselU (besselH_le_besselS hh)) u⁻¹).1 (inv_mem hu)
  have hinv : h⁻¹ * u⁻¹ * h * h⁻¹ = (u * h)⁻¹ := by group
  obtain ⟨h₁, h₂, h₃⟩ := mem_subringCongruenceSubgroup.1 (mem_besselCongruenceSubgroup.1 huh)
  refine mem_besselCongruenceSubgroup.2 (mem_subringCongruenceSubgroup.2
    ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩)
  · rcases besselH_apply_eq_or hu hh i j with e | e <;> rw [e]
    exacts [h₁ i j, 𝒪.matrix.one_mem i j]
  · have e := besselH_apply_eq_or hconj (inv_mem hh) i j
    rw [hinv] at e
    rw [← Subgroup.coe_inv]
    rcases e with e | e <;> rw [e]
    · simpa using h₂ i j
    · exact 𝒪.matrix.one_mem i j
  · rw [Matrix.smul_apply, Matrix.sub_apply]
    rcases besselH_apply_eq_or hu hh i j with e | e <;> rw [e]
    · simpa [Matrix.sub_apply] using h₃ i j
    · simp

/-- **The `H`-part of an element of `U K_𝒪(g)` is determined up to `H ∩ K_𝒪(g)`.** If `h, h' ∈ H`,
`u, u' ∈ U` and `y ∈ G_T` satisfy `u h y ∈ K_𝒪(g)` and `u' h' y ∈ K_𝒪(g)`, then
`h' h⁻¹ ∈ K_𝒪(g)`. So the `h ∈ H` with `h y ∈ U K_𝒪(g)` lie in a single right coset of
`H ∩ K_𝒪(g)`. -/
theorem mul_inv_mem_besselCongruenceSubgroup {𝒪 : Subring R} {g : Rˣ}
    {h h' u u' y : unitaryGroupOf (splitGram ϱ T)} (hh : h ∈ besselH ϱ T)
    (hh' : h' ∈ besselH ϱ T) (hu : u ∈ besselU ϱ T) (hu' : u' ∈ besselU ϱ T)
    (hy : u * h * y ∈ besselCongruenceSubgroup ϱ T 𝒪 g)
    (hy' : u' * h' * y ∈ besselCongruenceSubgroup ϱ T 𝒪 g) :
    h' * h⁻¹ ∈ besselCongruenceSubgroup ϱ T 𝒪 g := by
  have hd : h' * h⁻¹ ∈ besselH ϱ T := mul_mem hh' (inv_mem hh)
  -- `(u' h' y) (u h y)⁻¹ = v (h' h⁻¹)` with `v = u' (h' h⁻¹) u⁻¹ (h' h⁻¹)⁻¹ ∈ U`.
  have hconj : h' * h⁻¹ * u⁻¹ * (h' * h⁻¹)⁻¹ ∈ besselU ϱ T := by
    simpa using (Subgroup.mem_normalizer_iff.1
      (besselS_le_normalizer_besselU (besselH_le_besselS hd)) u⁻¹).1 (inv_mem hu)
  have h_eq : u' * (h' * h⁻¹ * u⁻¹ * (h' * h⁻¹)⁻¹) * (h' * h⁻¹) = u' * h' * y * (u * h * y)⁻¹ := by
    group
  exact mem_besselCongruenceSubgroup_of_besselU_mul (mul_mem hu' hconj) hd
    (h_eq ▸ mul_mem hy' (inv_mem hy))

end Congruence

end TauCeti
