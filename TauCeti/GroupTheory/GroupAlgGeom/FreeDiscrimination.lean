/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BigPowers
public import TauCeti.GroupTheory.FreeGroup.BigPowers
public import TauCeti.GroupTheory.FreeGroup.CSA
public import TauCeti.GroupTheory.GroupAlgGeom.Basic
import Mathlib.GroupTheory.CoprodI

/-!
# Free `G`-groups are discriminated by `G`

Let `G` be a nonabelian CSA group with the big powers property, for instance a nonabelian free
group or, more generally, a nonabelian fully residually free group. Then the free `G`-group
`G[X] = G ∗ F(X)` is discriminated by `G` over `G`: any finitely many nonidentity elements of
`G[X]` survive under one homomorphism `G[X] →* G` fixing `G`. This complements the
discrimination of extensions of centralizers of `G` by their retractions onto `G`.

The discriminating homomorphisms send each variable `x` to a conjugate `c x * u ^ k * (c x)⁻¹`
of a large power of one fixed element `u ≠ 1`. For nonempty `X` the group `G` must be
nonabelian: a homomorphism to the trivial group kills the variables, and a homomorphism to a
nontrivial commutative group kills the commutator of a variable with a nontrivial coefficient,
which is nontrivial in `G[X]`. (For empty `X`, `G[X] ≅ G` is discriminated by any `G`.) More
generally, the coefficient group may embed into a
nonabelian CSA BP target `H`, and the same construction discriminates `G[X]` by `H` over that
embedding.

## Main results

* `TauCeti.GroupAlgGeom.GX.isDiscriminatedBy_of_injective`: `G[X]` is discriminated over `G` by
  any nonabelian CSA BP target receiving an injective coefficient map from `G`.
* `TauCeti.GroupAlgGeom.GX.isDiscriminatedBy`: for a nonabelian CSA group `G` with the big
  powers property, `G[X]` is discriminated by `G` over `G`.
* `TauCeti.GroupAlgGeom.GX.isDiscriminatedBy_of_isFreeGroup`: for a nonabelian free group `F`,
  `F[X]` is discriminated by `F` over `F`.

## Implementation notes

An element of `G[X]` is the product of a reduced word in the free product of `G` with one
infinite cyclic factor for each variable (Mathlib's `Monoid.CoprodI.Word`). Under
`x ↦ c x * u ^ k * (c x)⁻¹` the word becomes an alternating product
`g * u ^ (k * e₁) * s₁ * ⋯ * u ^ (k * eₙ) * sₙ` whose separators are
`sᵢ = (c xᵢ)⁻¹ * hᵢ * c xᵢ₊₁` for `i < n`, with final separator
`sₙ = (c xₙ)⁻¹ * hₙ`. For `i < n`, `hᵢ` is the coefficient letter between the `i`-th and the
`(i + 1)`-th variable letters, or `1` if they are adjacent; `hₙ` is the trailing coefficient or `1`.
The conjugators `c x` are chosen among the powers of an element `v` outside the centralizer
`C_G(u)` so that no separator except possibly the last lies in `C_G(u)`. This is possible because
each condition excludes at most one left coset of `C_G(u)`, while distinct powers of `v` lie in
distinct cosets. The big powers property for alternating products
(`Group.IsBP.exists_forall_mul_prod_ne_one`) then keeps the product nontrivial for all large `k`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.
-/

public section

open Group Subgroup Monoid

namespace TauCeti.GroupAlgGeom

namespace GX

universe u v t

variable {G : Type u} {X : Type v} [Group G]

/-! ### `G[X]` as a free product of `G` and one infinite cyclic group per variable -/

/-- The factors of `G[X]` as an indexed free product: `G` at `none`, and an infinite cyclic group
at `some x` for each variable `x`. -/
private abbrev Factor (G : Type u) (X : Type v) : Option X → Type u
  | none => G
  | some _ => ULift.{u} (Multiplicative ℤ)

private instance instGroupFactor : ∀ o, Group (Factor G X o)
  | none => inferInstanceAs (Group G)
  | some _ => inferInstanceAs (Group (ULift (Multiplicative ℤ)))

/-- A letter of a reduced word in the free product of the factors. -/
private abbrev Letter (G : Type u) (X : Type v) : Type (max u v) := Σ o, Factor G X o

/-- The homomorphism from the indexed free product onto `G[X]`. -/
private def ofCoprodI : CoprodI (Factor G X) →* GX G X :=
  CoprodI.lift fun
    | none => Coprod.inl
    | some x => Coprod.inr.comp
        ((zpowersHom (FreeGroup X) (FreeGroup.of x)).comp MulEquiv.ulift.toMonoidHom)

/-- The inverse of `ofCoprodI`. -/
private def toCoprodI : GX G X →* CoprodI (Factor G X) :=
  Coprod.lift (CoprodI.of (M := Factor G X) (i := none) : G →* CoprodI (Factor G X))
    (FreeGroup.lift fun x => CoprodI.of (i := some x) (ULift.up (Multiplicative.ofAdd 1)))

private theorem ofCoprodI_of_none (g : Factor G X none) :
    ofCoprodI (CoprodI.of g) = Coprod.inl (g : G) :=
  CoprodI.lift_of _ _

private theorem ofCoprodI_of_some (x : X) (m : ULift.{u} (Multiplicative ℤ)) :
    ofCoprodI (CoprodI.of (M := Factor G X) (i := some x) m) =
      Coprod.inr (FreeGroup.of x ^ m.down.toAdd) := by
  rw [ofCoprodI, CoprodI.lift_of, MonoidHom.comp_apply, MonoidHom.comp_apply]
  -- `MulEquiv.ulift` sends the cyclic factor to its underlying element.
  change Coprod.inr (zpowersHom (FreeGroup X) (FreeGroup.of x) m.down) = _
  rw [zpowersHom_apply]

private theorem ofCoprodI_toCoprodI (w : GX G X) : ofCoprodI (toCoprodI w) = w := by
  have : (ofCoprodI (G := G) (X := X)).comp toCoprodI = .id _ := by
    ext x
    · exact ofCoprodI_of_none x
    · simpa [toCoprodI] using ofCoprodI_of_some (G := G) x (.up (.ofAdd 1))
  exact DFunLike.congr_fun this w

/-- The product of the letters of a list. -/
private def wordProd (L : List (Letter G X)) : CoprodI (Factor G X) :=
  (L.map fun l => CoprodI.of l.2).prod

/-! ### Evaluating a word at conjugates of powers of `u` -/

/-- The product of the coefficient letters at the start of a list, up to its first variable
letter. -/
private def lead : List (Letter G X) → G
  | [] => 1
  | ⟨none, g⟩ :: L => g * lead L
  | ⟨some _, _⟩ :: _ => 1

variable {H : Type t} [Group H] (c : X → H)

/-- The conjugator `c x` of the first variable letter `x` of a list, or `1` if there is none. -/
private def nextConj : List (Letter G X) → H
  | [] => 1
  | ⟨none, _⟩ :: L => nextConj L
  | ⟨some x, _⟩ :: _ => c x

/-- The exponents of the variable letters of a list, paired with the separators that follow
after evaluation at `x ↦ c x * u ^ k * (c x)⁻¹`: `(c x)⁻¹ * ι h * c x'` between variable
letters, and `(c x)⁻¹ * ι h` after the last variable letter. -/
private def pairs (ι : G →* H) : List (Letter G X) → List (ℤ × H)
  | [] => []
  | ⟨none, _⟩ :: L => pairs ι L
  | ⟨some x, m⟩ :: L => ((ULift.down m).toAdd, (c x)⁻¹ * ι (lead L) * nextConj c L) :: pairs ι L

variable (ι : G →* H) (u : H)

/-- Evaluation of a word at the conjugates `c x * u ^ k * (c x)⁻¹` is an alternating product of
powers of `u ^ k` and separators. -/
private theorem eval_ofCoprodI_wordProd (k : ℕ) (L : List (Letter G X)) :
    eval ι (fun x => c x * u ^ k * (c x)⁻¹) (ofCoprodI (wordProd L)) =
      ι (lead L) * nextConj c L *
        ((pairs c ι L).map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod := by
  induction L with
  | nil => simp [wordProd, lead, nextConj, pairs]
  | cons l L ih =>
    obtain ⟨_ | x, m⟩ := l
    · simp only [wordProd, List.map_cons, List.prod_cons, map_mul] at ih ⊢
      rw [ih, ofCoprodI_of_none, eval_inl]
      simp [lead, nextConj, pairs, mul_assoc]
    · simp only [wordProd, List.map_cons, List.prod_cons, map_mul] at ih ⊢
      rw [ih, ofCoprodI_of_some, eval_inr, map_zpow, FreeGroup.lift_apply_of, conj_zpow]
      simp only [lead, nextConj, pairs, List.map_cons, List.prod_cons, map_one,
        ← zpow_natCast, ← zpow_mul]
      group

/-- A list without variable letters evaluates to its coefficient product. -/
private theorem ofCoprodI_wordProd_of_pairs_eq_nil {L : List (Letter G X)}
    (hL : pairs c ι L = []) : ofCoprodI (wordProd L) = Coprod.inl (lead L) := by
  induction L with
  | nil => simp [wordProd, lead]
  | cons l L ih =>
    obtain ⟨_ | x, m⟩ := l
    · simp only [wordProd, List.map_cons, List.prod_cons, map_mul] at ih ⊢
      rw [ofCoprodI_of_none, ih hL]
      simp [lead]
    · simp [pairs] at hL

private theorem exists_of_mem_pairs {L : List (Letter G X)} {p : ℤ × H} (hp : p ∈ pairs c ι L) :
    ∃ x m, (⟨some x, m⟩ : Letter G X) ∈ L ∧ p.1 = (ULift.down m).toAdd := by
  induction L with
  | nil => simp [pairs] at hp
  | cons l L ih =>
    obtain ⟨_ | x, m⟩ := l
    · obtain ⟨x, m, hm, h⟩ := ih hp
      exact ⟨x, m, List.mem_cons_of_mem _ hm, h⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨x, m, List.mem_cons_self, rfl⟩
      · obtain ⟨x, m, hm, h⟩ := ih hp
        exact ⟨x, m, List.mem_cons_of_mem _ hm, h⟩

/-- In a reduced word whose conjugators separate distinct variable letters and conjugate the
coefficient letters out of `C_H(u)`, no separator except possibly the last lies in `C_H(u)`. -/
private theorem isChain_pairs {L : List (Letter G X)} (hL : L.IsChain fun l l' => l.1 ≠ l'.1)
    (hc : ∀ (x x' : X) (m : Factor G X (some x)) (m' : Factor G X (some x')) (h : G),
      (⟨some x, m⟩ : Letter G X) ∈ L → (⟨some x', m'⟩ : Letter G X) ∈ L →
        (h = 1 ∧ x ≠ x' ∨ (⟨none, h⟩ : Letter G X) ∈ L) →
          (c x)⁻¹ * ι h * c x' ∉ centralizer {u}) :
    (pairs c ι L).IsChain fun p _ => p.2 ∉ centralizer {u} := by
  induction L with
  | nil => exact .nil
  | cons l L ih =>
    have ih' := ih hL.tail fun x x' m m' h hm hm' hh => hc x x' m m' h (List.mem_cons_of_mem _ hm)
        (List.mem_cons_of_mem _ hm') (hh.imp_right (List.mem_cons_of_mem _))
    obtain ⟨_ | x, m⟩ := l
    · exact ih'
    refine List.isChain_cons.2 ⟨fun q hq => ?_, ih'⟩
    -- The next variable letter follows either directly or after one coefficient letter.
    obtain _ | ⟨⟨_ | x', m'⟩, L'⟩ := L
    · simp [pairs] at hq
    · obtain _ | ⟨⟨_ | x'', m''⟩, L''⟩ := L'
      · simp [pairs] at hq
      · exact absurd rfl (List.isChain_cons_cons.1 hL.tail).1
      · simpa [lead, nextConj] using hc x x'' m m'' m' List.mem_cons_self
          (by simp) (Or.inr (by simp))
    · simpa [lead, nextConj] using hc x x' m m' 1 List.mem_cons_self (by simp)
        (Or.inl ⟨rfl, fun h => (List.isChain_cons_cons.1 hL).1 (by rw [h])⟩)

/-! ### Discrimination -/

open scoped Classical in
/-- The reduced word of an element of `G[X]` in the free product of the factors. -/
private noncomputable def word (w : GX G X) : CoprodI.Word (Factor G X) :=
  CoprodI.Word.equiv (toCoprodI w)

private theorem ofCoprodI_wordProd_word (w : GX G X) :
    ofCoprodI (wordProd (word w).toList) = w := by
  classical
  -- `wordProd` of the letters of a reduced word is `Word.prod`, the inverse of `Word.equiv`.
  have : wordProd (word w).toList = CoprodI.Word.equiv.symm (word w) := rfl
  rw [this, word, Equiv.symm_apply_apply, ofCoprodI_toCoprodI]

/-- A nonidentity element of `G[X]` survives under `x ↦ c x * u ^ k * (c x)⁻¹` for all large `k`,
provided the conjugators satisfy the separation conditions on the letters of its reduced word. -/
private theorem exists_forall_eval_ne_one (hι : Function.Injective ι) (hBP : IsBP H)
    (hH : IsCSA H) (hu : u ≠ 1)
    {w : GX G X} (hw : w ≠ 1)
    (hc : ∀ (x x' : X) (m : Factor G X (some x)) (m' : Factor G X (some x')) (h : G),
      (⟨some x, m⟩ : Letter G X) ∈ (word w).toList →
        (⟨some x', m'⟩ : Letter G X) ∈ (word w).toList →
          (h = 1 ∧ x ≠ x' ∨ (⟨none, h⟩ : Letter G X) ∈ (word w).toList) →
            (c x)⁻¹ * ι h * c x' ∉ centralizer {u}) :
    ∃ N : ℕ, ∀ k, N ≤ k → eval ι (fun x => c x * u ^ k * (c x)⁻¹) w ≠ 1 := by
  have hW := ofCoprodI_wordProd_word w
  by_cases hl : pairs c ι (word w).toList = []
  · -- Without variable letters, `w` is a nonidentity coefficient.
    obtain ⟨g, rfl⟩ : ∃ g, w = Coprod.inl g :=
      ⟨_, hW.symm.trans (ofCoprodI_wordProd_of_pairs_eq_nil c ι hl)⟩
    refine ⟨0, fun k _ => ?_⟩
    rw [eval_inl]
    exact fun h => hw (by rw [(map_eq_one_iff ι hι).1 h, map_one])
  · obtain ⟨N, hN⟩ := Group.IsBP.exists_forall_mul_prod_ne_one hBP hH hu
      (ι (lead (word w).toList) * nextConj c (word w).toList) hl
      (fun p hp h0 => by
        obtain ⟨x, m, hm, hp⟩ := exists_of_mem_pairs c ι hp
        refine (word w).ne_one _ hm (ULift.ext ?_)
        rw [ULift.one_down, ← toAdd_eq_zero, ← hp, h0])
      ((isChain_pairs c ι u (word w).chain_ne hc).imp fun p _ hp h => absurd h hp)
    exact ⟨N, fun k hk => by rw [← hW, eval_ofCoprodI_wordProd]; exact hN k hk⟩

/-- If the coefficient group embeds into a nonabelian CSA group `H` with the big powers
property, the free `G`-group `G[X]` is discriminated by `H` over that coefficient embedding. -/
theorem isDiscriminatedBy_of_injective (hι : Function.Injective ι)
    (hBP : IsBP H) (hH : IsCSA H) (hab : ¬IsMulCommutative H) :
    IsDiscriminatedBy (Coprod.inl : G →* GX G X) ι := by
  classical
  have := hBP.isMulTorsionFree
  obtain ⟨u, v, huv⟩ : ∃ u v : H, ¬Commute u v := by
    simpa [isMulCommutative_iff, commute_iff_eq] using hab
  have hu : u ≠ 1 := by rintro rfl; exact huv (Commute.one_left v)
  have hv : v ∉ centralizer {u} := fun h => huv (mem_centralizer_singleton_iff.1 h).symm
  refine (isDiscriminatedBy_def _ _).2 fun S hS => ?_
  -- Choose conjugators for the variables and coefficient letters of the reduced words of `S`.
  obtain ⟨n, hn⟩ := hH.exists_inv_pow_mul_mul_pow_notMem_centralizer hv
    (S.biUnion fun w => ((word w).toList.filterMap Sigma.fst).toFinset)
    (ι '' (⋃ w ∈ (S : Set (GX G X)), {g | (⟨none, g⟩ : Letter G X) ∈ (word w).toList}))
    ((S.finite_toSet.biUnion fun w _ => (word w).toList.finite_toSet.preimage
      (sigma_mk_injective (i := none)).injOn).image ι)
  let c : X → H := fun x => v ^ n x
  choose! N hN using fun w (hw : w ∈ S) => exists_forall_eval_ne_one c ι u hι hBP hH hu (hS w hw)
    fun x x' m m' h hm hm' hh => hn x
      (Finset.mem_biUnion.2 ⟨w, hw, List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hm, rfl⟩)⟩) x'
      (Finset.mem_biUnion.2 ⟨w, hw, List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hm', rfl⟩)⟩) (ι h)
      (hh.imp (fun hh => ⟨by rw [hh.1, map_one], hh.2⟩) fun hh =>
        ⟨Set.mem_image_of_mem ι (Set.mem_biUnion hw hh),
        fun heq => (word w).ne_one _ hh ((map_eq_one_iff ι hι).1 heq)⟩)
  exact ⟨evalGHom ι fun x => c x * u ^ (S.sup N) * (c x)⁻¹,
    fun w hw => by rw [coe_evalGHom]; exact hN w hw _ (Finset.le_sup hw)⟩

/-- **Free `G`-groups are discriminated by `G`.** Let `G` be a nonabelian CSA group with the big
powers property. Then `G[X]` is discriminated by `G` over `G`: any finitely many nonidentity
elements of `G[X]` survive under one homomorphism `G[X] →* G` fixing `G`. -/
theorem isDiscriminatedBy (hBP : IsBP G) (hG : IsCSA G) (hab : ¬IsMulCommutative G) :
    IsDiscriminatedBy (Coprod.inl : G →* GX G X) (.id G) :=
  isDiscriminatedBy_of_injective (.id G) Function.injective_id hBP hG hab

/-- **Free `F`-groups over a nonabelian free group are discriminated by it.** For a nonabelian
free group `F`, the free `F`-group `F[X]` is discriminated by `F` over `F`. -/
theorem isDiscriminatedBy_of_isFreeGroup {F : Type u} [Group F] [IsFreeGroup F]
    (hF : ¬IsMulCommutative F) :
    IsDiscriminatedBy (Coprod.inl : F →* GX F X) (.id F) :=
  isDiscriminatedBy IsFreeGroup.isBP IsFreeGroup.isCSA hF

end GX

end TauCeti.GroupAlgGeom
