/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Data.List.Chain

/-!
# Free independence of subalgebras

Let `A` be a unital algebra over a commutative ring `R` and let `φ : A →ₗ[R] R` be a linear
functional. A family of unital subalgebras `B i` of `A` is *freely independent* with respect to
`φ` if `φ (a₁ * ⋯ * aₙ) = 0` whenever `n ≥ 1`, each `aⱼ` lies in some `B iⱼ` and is centred,
`φ aⱼ = 0`, and consecutive labels differ, `iⱼ ≠ iⱼ₊₁`. Labels that are not adjacent may
coincide. In free probability `R = ℂ` and `φ` is normalised, `φ 1 = 1`; here normalisation is a
separate hypothesis of the results that use it, and no positivity or traciality is assumed.

A word `a₁ ⋯ aₙ` is encoded as a list `[(i₁, a₁), …, (iₙ, aₙ)]` of label–element pairs, whose
value is the ordered product of the list of elements.

The main result is that freeness determines a normalised functional on the subalgebra generated
by the family from its restrictions to the individual members: every word reduces, by merging
adjacent letters with equal labels and by centring letters one at a time, to centred alternating
words, on which free functionals vanish, and to shorter words.

## Main definitions

* `TauCeti.IsFreelyIndependent φ B` — the subalgebras `B i` are freely independent with respect
  to `φ`, unfolded by `TauCeti.isFreelyIndependent_iff`.

## Main results

* `TauCeti.IsFreelyIndependent.mono`, `TauCeti.IsFreelyIndependent.comp` and
  `TauCeti.IsFreelyIndependent.map` — freeness passes to smaller subalgebras, to subfamilies
  along injective reindexings, and to images under algebra homomorphisms intertwining the
  functionals.
* `TauCeti.isFreelyIndependent_of_subsingleton` — a family with at most one member, in particular
  the empty family, is free.
* `TauCeti.isFreelyIndependent_domRestrict_iff` — for a normalised functional, members equal to the
  scalars may be added to or removed from a free family.
* `TauCeti.IsFreelyIndependent.apply_mul_of_ne` — the first mixed moment factorises,
  `φ (a * b) = φ a * φ b`.
* `TauCeti.IsFreelyIndependent.eqOn_iSup` — two normalised functionals for which the family is
  free and which agree on each member agree on the subalgebra the family generates, with
  `TauCeti.IsFreelyIndependent.eq_of_iSup_eq_top` the case of a generating family.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 5.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {R A A' ι κ : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring A'] [Algebra R A']

/-- Subalgebras `B i` of `A` are *freely independent* with respect to a linear functional `φ` if
`φ (a₁ * ⋯ * aₙ) = 0` for every nonempty word `[(i₁, a₁), …, (iₙ, aₙ)]` whose consecutive labels
are distinct and whose letters satisfy `aⱼ ∈ B iⱼ` and `φ aⱼ = 0`. Labels that are not adjacent
may coincide. -/
def IsFreelyIndependent (φ : A →ₗ[R] R) (B : ι → Subalgebra R A) : Prop :=
  ∀ w : List (ι × A), w ≠ [] → (w.map Prod.fst).IsChain (· ≠ ·) → (∀ x ∈ w, x.2 ∈ B x.1) →
    (∀ x ∈ w, φ x.2 = 0) → φ (w.map Prod.snd).prod = 0

theorem isFreelyIndependent_iff {φ : A →ₗ[R] R} {B : ι → Subalgebra R A} :
    IsFreelyIndependent φ B ↔
      ∀ w : List (ι × A), w ≠ [] → (w.map Prod.fst).IsChain (· ≠ ·) →
        (∀ x ∈ w, x.2 ∈ B x.1) → (∀ x ∈ w, φ x.2 = 0) → φ (w.map Prod.snd).prod = 0 :=
  Iff.rfl

/-- A family with at most one member is free: an alternating word then has a single letter. -/
theorem isFreelyIndependent_of_subsingleton [Subsingleton ι] (φ : A →ₗ[R] R)
    (B : ι → Subalgebra R A) : IsFreelyIndependent φ B := by
  rintro (_ | ⟨x, _ | ⟨y, w⟩⟩) hne halt - hc
  · exact (hne rfl).elim
  · simpa using hc x (by simp)
  · simp only [List.map_cons, List.isChain_cons_cons] at halt
    exact (halt.1 (Subsingleton.elim _ _)).elim

namespace IsFreelyIndependent

variable {φ ψ : A →ₗ[R] R} {B C : ι → Subalgebra R A}

/-- Freeness passes to smaller subalgebras. -/
theorem mono (h : IsFreelyIndependent φ B) (hCB : ∀ i, C i ≤ B i) : IsFreelyIndependent φ C :=
  fun w hne halt hw hc => h w hne halt (fun x hx => hCB _ (hw x hx)) hc

/-- Freeness passes to subfamilies along an injective reindexing. -/
theorem comp (h : IsFreelyIndependent φ B) {e : κ → ι} (he : Function.Injective e) :
    IsFreelyIndependent φ (B ∘ e) := by
  intro w hne halt hw hc
  simpa [List.map_map, Prod.map_snd'] using h (w.map (Prod.map e id)) (by simpa using hne)
    (by simpa [List.map_map, List.isChain_map, he.ne_iff] using halt)
    (fun _ hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hw y hy)
    (fun _ hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hc y hy)

/-- Freeness is transported along an algebra homomorphism `f` intertwining the functionals:
the images of a free family are free. -/
theorem map (h : IsFreelyIndependent φ B) (f : A →ₐ[R] A') {φ' : A' →ₗ[R] R}
    (hf : φ'.comp f.toLinearMap = φ) : IsFreelyIndependent φ' fun i => (B i).map f := by
  intro w hne halt hw hc
  choose g hgB hgf using fun x (hx : x ∈ w) => Subalgebra.mem_map.1 (hw x hx)
  have hφ (a : A) : φ' (f a) = φ a := by simpa using LinearMap.congr_fun hf a
  let w' : List (ι × A) := w.pmap (fun x hx => (x.1, g x hx)) fun _ hx => hx
  have hsnd : (w'.map Prod.snd).map f = w.map Prod.snd := by simp [w', List.map_pmap, hgf]
  have hfst : w'.map Prod.fst = w.map Prod.fst := by simp [w', List.map_pmap]
  rw [← hsnd, ← map_list_prod, hφ]
  refine h w' (by simpa [w'] using hne) (hfst ▸ halt) (fun y hy => ?_) fun y hy => ?_
  · obtain ⟨x, hx, rfl⟩ := List.mem_pmap.1 hy
    exact hgB x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_pmap.1 hy
    rw [← hφ, hgf]
    exact hc x hx

/-- The first mixed moment of a free family factorises: for a normalised functional and letters
from members with distinct labels, `φ (a * b) = φ a * φ b`. -/
theorem apply_mul_of_ne (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    {a b : A} (ha : a ∈ B i) (hb : b ∈ B j) : φ (a * b) = φ a * φ b := by
  have := h [(i, a - algebraMap R A (φ a)), (j, b - algebraMap R A (φ b))] (by simp)
    (by simpa using hij)
    (by simp [sub_mem, ha, hb])
    (by simp [Algebra.algebraMap_eq_smul_one, hφ])
  simpa [Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub, hφ, sub_eq_zero] using this

/-- Centring the letter `x` of the word `v ++ x :: u` at `c` splits the value of the word into the
value of the centred word and `c` times the value of the word with `x` deleted. -/
private theorem prod_append_cons (v u : List (ι × A)) (x : ι × A) (c : R) :
    ((v ++ x :: u).map Prod.snd).prod =
      ((v ++ (x.1, x.2 - algebraMap R A c) :: u).map Prod.snd).prod +
        c • ((v ++ u).map Prod.snd).prod := by
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, sub_mul, mul_sub,
    Algebra.smul_def, Algebra.left_comm _ c]
  abel

/-- The centring step: if two normalised functionals for which `B` is free agree on each `B i`
and on all words of length less than `n`, then they agree on every alternating word `v ++ u` of
length `n ≠ 0` whose prefix `v` is centred. The letters of `u` are centred one at a time, each
step producing a word with a longer centred prefix and a shorter word. -/
private theorem apply_prod_append_eq_of_isChain (hφ : φ 1 = 1) (hfφ : IsFreelyIndependent φ B)
    (hfψ : IsFreelyIndependent ψ B) (h : ∀ i, Set.EqOn φ ψ (B i)) {n : ℕ} (hn0 : n ≠ 0)
    (ih : ∀ w : List (ι × A), w.length < n → (∀ x ∈ w, x.2 ∈ B x.1) →
      φ (w.map Prod.snd).prod = ψ (w.map Prod.snd).prod) :
    ∀ u v : List (ι × A), (v ++ u).length = n → (∀ x ∈ v ++ u, x.2 ∈ B x.1) →
      ((v ++ u).map Prod.fst).IsChain (· ≠ ·) → (∀ x ∈ v, φ x.2 = 0) →
      φ ((v ++ u).map Prod.snd).prod = ψ ((v ++ u).map Prod.snd).prod := by
  intro u
  induction u with
  | nil =>
    intro v hlen hw halt hc
    simp only [List.append_nil] at hlen hw halt ⊢
    have hne : v ≠ [] := by rintro rfl; exact hn0 hlen.symm
    rw [hfφ v hne halt hw hc,
      hfψ v hne halt hw fun x hx => (h x.1 (hw x hx)).symm.trans (hc x hx)]
  | cons x u ihu =>
    intro v hlen hw halt hc
    have hx : x.2 ∈ B x.1 := hw x (by simp)
    rw [prod_append_cons v u x (φ x.2), map_add, map_add, map_smul, map_smul]
    congr 1
    · have := ihu (v ++ [(x.1, x.2 - algebraMap R A (φ x.2))]) (by simpa using hlen) ?_ ?_ ?_
      · simpa using this
      · simp only [List.append_assoc, List.singleton_append, List.mem_append, List.mem_cons]
          at hw ⊢
        rintro y (hy | rfl | hy)
        · exact hw y (.inl hy)
        · exact sub_mem hx (Subalgebra.algebraMap_mem _ _)
        · exact hw y (.inr (.inr hy))
      · simpa using halt
      · simp only [List.mem_append, List.mem_singleton]
        rintro y (hy | rfl)
        · exact hc y hy
        · simp [Algebra.algebraMap_eq_smul_one, hφ]
    · congr 1
      refine ih (v ++ u) ?_ ?_
      · simp only [List.length_append, List.length_cons] at hlen ⊢
        omega
      · simp only [List.mem_append, List.mem_cons] at hw ⊢
        rintro y (hy | hy)
        · exact hw y (.inl hy)
        · exact hw y (.inr (.inr hy))

/-- The merging step: a word with two adjacent letters of equal labels has the same value as a
shorter word, obtained by multiplying those two letters together. -/
private theorem exists_shorter_of_not_isChain {w : List (ι × A)} (hw : ∀ x ∈ w, x.2 ∈ B x.1)
    (halt : ¬(w.map Prod.fst).IsChain (· ≠ ·)) :
    ∃ w' : List (ι × A), w'.length < w.length ∧ (∀ x ∈ w', x.2 ∈ B x.1) ∧
      (w'.map Prod.snd).prod = (w.map Prod.snd).prod := by
  obtain ⟨k, hk, hne⟩ := List.exists_not_getElem_of_not_isChain halt
  simp only [List.length_map] at hk
  simp only [List.getElem_map, ne_eq, not_not] at hne
  have hsplit : w = w.take k ++ w[k] :: w[k + 1] :: w.drop (k + 1 + 1) := by
    rw [← List.drop_eq_getElem_cons hk, ← List.drop_eq_getElem_cons, List.take_append_drop]
  obtain ⟨u, x, y, v, rfl, hxy⟩ : ∃ u x y v, w = u ++ x :: y :: v ∧ x.1 = y.1 :=
    ⟨_, _, _, _, hsplit, hne⟩
  refine ⟨u ++ (x.1, x.2 * y.2) :: v, by simp, ?_, by simp [mul_assoc]⟩
  simp only [List.mem_append, List.mem_cons] at hw ⊢
  rintro z (hz | rfl | hz)
  · exact hw z (.inl hz)
  · exact mul_mem (hw x (.inr (.inl rfl))) (hxy ▸ hw y (.inr (.inr (.inl rfl))))
  · exact hw z (.inr (.inr (.inr hz)))

/-- Two normalised functionals for which `B` is free and which agree on each `B i` agree on the
value of every word with letters from the `B i`. -/
private theorem apply_prod_eq (hφ : φ 1 = 1) (hψ : ψ 1 = 1) (hfφ : IsFreelyIndependent φ B)
    (hfψ : IsFreelyIndependent ψ B) (h : ∀ i, Set.EqOn φ ψ (B i)) (w : List (ι × A))
    (hw : ∀ x ∈ w, x.2 ∈ B x.1) : φ (w.map Prod.snd).prod = ψ (w.map Prod.snd).prod := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  have ih' (w' : List (ι × A)) (hlen : w'.length < n) (hw' : ∀ x ∈ w', x.2 ∈ B x.1) :
      φ (w'.map Prod.snd).prod = ψ (w'.map Prod.snd).prod :=
    ih _ hlen w' hw' rfl
  by_cases halt : (w.map Prod.fst).IsChain (· ≠ ·)
  · rcases eq_or_ne w [] with rfl | hne
    · simp [hφ, hψ]
    have hn0 : n ≠ 0 := by rw [← hn]; exact (List.length_pos_iff.2 hne).ne'
    exact apply_prod_append_eq_of_isChain hφ hfφ hfψ h hn0 ih' w [] hn hw halt (by simp)
  · obtain ⟨w', hlen, hw', hprod⟩ := exists_shorter_of_not_isChain hw halt
    rw [← hprod]
    exact ih' w' (hn ▸ hlen) hw'

/-- Freeness determines the joint distribution from the individual ones: two normalised
functionals for which `B` is free and which agree on each `B i` agree on the subalgebra
generated by the `B i`. -/
theorem eqOn_iSup (hφ : φ 1 = 1) (hψ : ψ 1 = 1) (hfφ : IsFreelyIndependent φ B)
    (hfψ : IsFreelyIndependent ψ B) (h : ∀ i, Set.EqOn φ ψ (B i)) :
    Set.EqOn φ ψ (⨆ i, B i : Subalgebra R A) := by
  let S : Set A := {p | ∃ w : List (ι × A), (∀ x ∈ w, x.2 ∈ B x.1) ∧ (w.map Prod.snd).prod = p}
  have hS : S * S ⊆ S := by
    rintro _ ⟨_, ⟨w₁, hw₁, rfl⟩, _, ⟨w₂, hw₂, rfl⟩, rfl⟩
    refine ⟨w₁ ++ w₂, ?_, by simp⟩
    simp only [List.mem_append]
    rintro x (hx | hx)
    exacts [hw₁ x hx, hw₂ x hx]
  intro x hx'
  have hx : x ∈ Submodule.span R S := by
    refine Algebra.iSup_induction B (motive := (· ∈ Submodule.span R S)) hx'
      (fun i a ha => ?_) (fun a b ha hb => add_mem ha hb) (fun a b ha hb => ?_) fun r => ?_
    · exact Submodule.subset_span ⟨[(i, a)], by simpa using ha, by simp⟩
    · exact Submodule.span_mono hS (Submodule.span_mul_span R S S ▸ Submodule.mul_mem_mul ha hb)
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], by simp, by simp⟩)
  clear hx'
  induction hx using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w, hw, rfl⟩ := hp
    exact apply_prod_eq hφ hψ hfφ hfψ h w hw
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

/-- Two normalised functionals for which a generating family `B` is free and which agree on
each `B i` are equal. -/
theorem eq_of_iSup_eq_top (hφ : φ 1 = 1) (hψ : ψ 1 = 1) (hfφ : IsFreelyIndependent φ B)
    (hfψ : IsFreelyIndependent ψ B) (h : ∀ i, Set.EqOn φ ψ (B i)) (htop : ⨆ i, B i = ⊤) :
    φ = ψ :=
  LinearMap.ext fun x => eqOn_iSup hφ hψ hfφ hfψ h (by rw [htop]; exact Algebra.mem_top)

end IsFreelyIndependent

/-- For a normalised functional, members of a family equal to the scalars do not affect freeness:
if `B i = ⊥` for every label outside `s`, then `B` is free exactly when its restriction to `s`
is free. -/
theorem isFreelyIndependent_domRestrict_iff {φ : A →ₗ[R] R} (hφ : φ 1 = 1)
    {B : ι → Subalgebra R A} {s : Set ι} (hs : ∀ i ∉ s, B i = ⊥) :
    IsFreelyIndependent φ (s.domRestrict B) ↔ IsFreelyIndependent φ B := by
  refine ⟨fun h => ?_, fun h => h.comp Subtype.val_injective⟩
  intro w hne halt hw hc
  by_cases hsw : ∀ x ∈ w, x.1 ∈ s
  · -- All labels lie in `s`: lift the word to a word labelled by `s`.
    let w' : List (s × A) := w.pmap (fun x hx => (⟨x.1, hx⟩, x.2)) hsw
    have hsnd : w'.map Prod.snd = w.map Prod.snd := by simp [w', List.map_pmap]
    have hfst : (w'.map Prod.fst).map Subtype.val = w.map Prod.fst := by
      simp [w', List.map_pmap]
    rw [← hfst, List.isChain_map] at halt
    rw [← hsnd]
    refine h w' (by simpa [w'] using hne) (halt.imp fun _ _ hab h => hab (congrArg _ h))
      (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨x, hx, rfl⟩ := List.mem_pmap.1 hy
      exact hw x hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_pmap.1 hy
      exact hc x hx
  · -- Some letter is a centred scalar, hence zero.
    push Not at hsw
    obtain ⟨x, hx, hxs⟩ := hsw
    obtain ⟨c, hcx⟩ := Algebra.mem_bot.1 (hs x.1 hxs ▸ hw x hx)
    have hx0 : x.2 = 0 := by
      have := hc x hx
      rw [← hcx, Algebra.algebraMap_eq_smul_one, map_smul, hφ, smul_eq_mul, mul_one] at this
      rw [← hcx, this, map_zero]
    rw [List.prod_eq_zero (List.mem_map.2 ⟨x, hx, hx0⟩), map_zero]

end TauCeti
