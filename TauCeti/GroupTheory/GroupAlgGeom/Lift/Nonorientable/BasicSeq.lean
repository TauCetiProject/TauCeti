/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Nonorientable.BasicAut
public import TauCeti.GroupTheory.GroupAlgGeom.Lift.BasicSeq
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.MixedForm
import TauCeti.Data.List.ProdOfFn

/-!
# The basic sequence of automorphisms of a non-orientable quadratic equation

For pairwise distinct variables `xᵢ`, `yᵢ` (`i = 1, …, n`), `zⱼ` (`j = 1, …, m`), `uₖ`
(`k = 1, …, r`) and coefficients `cⱼ`, the basic sequence of the word
`S₁ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ] ∏ₖ uₖ²` (`basicMixedWordSeq`) is the orientable basic sequence of
`S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]` (`TauCeti.GroupAlgGeom.Lift.basicWordSeq`), followed, if there
is a square and `S₀` has an atom, by the automorphism linking the last atom of `S₀` with the first
square (`basicCommSq` if there is a commutator, `basicLinkSq` if there is none), and, if there are
at least two squares, by the two automorphisms `basicSqMul` and `basicSqConj` of the first two
squares. For two squares this is the basic sequence `Γ = (γ₁, …, γ_K)` of [IFT], §7.5, with
`K = m + 2` when `n = 0` and `K = m + 4n + 2` when `n ≥ 1`. [IFT] considers only two squares; for
one square the sequence has `K = m + 4n` terms: it ends with the linking automorphism when `S₀`
has an atom, and it is empty for `S₁ = u₁²`.

For a non-orientable standard quadratic equation `S = 1`, `mixedBasicSeq S` is the basic sequence
of its mixed form (`TauCeti.GroupAlgGeom.Quadratic.Standard.mixedWord`). Its automorphisms fix the
coefficients and the left side of the mixed form, so the products `φ_{j,p}` of their powers
(`TauCeti.GroupAlgGeom.Lift.phi`) do too.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.basicMixedWordSeq`: the basic sequence of the word `S₁`.
* `TauCeti.GroupAlgGeom.Lift.mixedBasicSeq`: the basic sequence of the mixed form of a
  non-orientable standard quadratic equation.

## Main results

* `TauCeti.GroupAlgGeom.Lift.mem_basicMixedWordSeq_iff`: the members of the basic sequence.
* `TauCeti.GroupAlgGeom.Lift.length_basicMixedWordSeq`: the length of the basic sequence.
* `TauCeti.GroupAlgGeom.Lift.apply_basicMixedWord_of_mem_basicMixedWordSeq`: its automorphisms
  fix `S₁`.
* `TauCeti.GroupAlgGeom.Lift.apply_mixedWord_of_mem_mixedBasicSeq`,
  `TauCeti.GroupAlgGeom.Lift.phi_mixedBasicSeq_mixedWord`: the basic sequence of a non-orientable
  equation and the products `φ_{j,p}` fix the left side of its mixed form.
* `TauCeti.GroupAlgGeom.Lift.length_mixedBasicSeq`: `K = m + 2N - 2` for genus `N`, that is
  `m + 4n + 2` for `2n + 2` squares
  (`TauCeti.GroupAlgGeom.Lift.length_mixedBasicSeq_nonorientableCoeff_two_mul_add_two`) and `m + 4n`
  for `2n + 1` squares.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1, Notation 42, and §7.5.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.Lift

variable {G X : Type*} [Group G] {n m r : ℕ}

/-! ### The basic sequence of the word `S₁` -/

section Seq

variable {x y : Fin n → X} {z : Fin m → X} {u : Fin r → X}
  (inj : (Sum.elim (Sum.elim (Sum.elim x y) z) u).Injective) (c : Fin m → G)

/-- The basic sequence of automorphisms of `G[X]` fixing `S₁ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ] ∏ₖ uₖ²`
([IFT], §7.5): the orientable basic sequence of `S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]`; then, if there
is a square and `S₀` has an atom, the automorphism of the first square and the last commutator
(or, if there is no commutator, the last coefficient atom); then, if there are at least two
squares, the two automorphisms of the first two squares. The mixed form of a standard equation
has one or two squares; for three or more squares only the first two get automorphisms of their
own. -/
noncomputable def basicMixedWordSeq : List (MulAut (GX G X)) :=
  basicWordSeq (Sum.elim_injective.1 inj).1 c ++
    (if h : 0 < n ∧ 0 < r then [basicCommSq inj ⟨n - 1, by lia⟩ ⟨0, h.2⟩]
      else if h : 0 < m ∧ 0 < r then [basicLinkSq inj c ⟨m - 1, by lia⟩ ⟨0, h.2⟩] else []) ++
    (if h : 1 < r then [basicSqMul inj ⟨0, by lia⟩ ⟨1, h⟩, basicSqConj inj ⟨0, by lia⟩ ⟨1, h⟩]
      else [])

theorem basicMixedWordSeq_def :
    basicMixedWordSeq inj c =
      basicWordSeq (Sum.elim_injective.1 inj).1 c ++
        (if h : 0 < n ∧ 0 < r then [basicCommSq inj ⟨n - 1, by lia⟩ ⟨0, h.2⟩]
          else if h : 0 < m ∧ 0 < r then [basicLinkSq inj c ⟨m - 1, by lia⟩ ⟨0, h.2⟩]
          else []) ++
        (if h : 1 < r then
          [basicSqMul inj ⟨0, by lia⟩ ⟨1, h⟩, basicSqConj inj ⟨0, by lia⟩ ⟨1, h⟩] else []) :=
  (rfl)

/-- The length of the basic sequence of `S₁`: the length `K(m, n)` of the orientable basic sequence
of `S₀`, plus one linking automorphism when there is a square and `S₀` has an atom, plus two when
there are at least two squares. With two squares and an atom in `S₀` this is `K(m, n) + 3`. -/
@[simp]
theorem length_basicMixedWordSeq :
    (basicMixedWordSeq inj c).length =
      (m - 1) + (if 0 < m ∧ 0 < n then 1 else 0) + (4 * n - 1) +
        (if 0 < r ∧ (0 < n ∨ 0 < m) then 1 else 0) + (if 1 < r then 2 else 0) := by
  simp only [basicMixedWordSeq_def, List.length_append, length_basicWordSeq]
  split_ifs <;> simp <;> lia

/-- The members of the basic sequence of `S₁`: the members of the orientable basic sequence of
`S₀`; the automorphism of the last commutator and the first square, if there are a commutator and
a square; the automorphism of the last coefficient atom and the first square, if there is no
commutator but a coefficient atom and a square; and the two automorphisms of the first two
squares, if there are at least two squares. -/
theorem mem_basicMixedWordSeq_iff {γ : MulAut (GX G X)} :
    γ ∈ basicMixedWordSeq inj c ↔
      γ ∈ basicWordSeq (Sum.elim_injective.1 inj).1 c ∨
        (∃ (i : Fin n) (k : Fin r), (i : ℕ) + 1 = n ∧ (k : ℕ) = 0 ∧ γ = basicCommSq inj i k) ∨
        (∃ (j : Fin m) (k : Fin r), n = 0 ∧ (j : ℕ) + 1 = m ∧ (k : ℕ) = 0 ∧
          γ = basicLinkSq inj c j k) ∨
        (∃ k k' : Fin r, (k : ℕ) = 0 ∧ (k' : ℕ) = 1 ∧ γ = basicSqMul inj k k') ∨
        ∃ k k' : Fin r, (k : ℕ) = 0 ∧ (k' : ℕ) = 1 ∧ γ = basicSqConj inj k k' := by
  simp only [basicMixedWordSeq_def, List.mem_append]
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ ?_⟩
  · obtain (hγ | hγ) | hγ := hγ
    · exact .inl hγ
    · split_ifs at hγ with hn hm
      · exact .inr (.inl ⟨_, _, by simp; lia, rfl, List.mem_singleton.1 hγ⟩)
      · exact .inr (.inr (.inl ⟨_, _, by lia, by simp; lia, rfl, List.mem_singleton.1 hγ⟩))
      · simp at hγ
    · split_ifs at hγ
      · obtain rfl | rfl := List.mem_pair.1 hγ
        · exact .inr (.inr (.inr (.inl ⟨_, _, rfl, rfl, rfl⟩)))
        · exact .inr (.inr (.inr (.inr ⟨_, _, rfl, rfl, rfl⟩)))
      · simp at hγ
  · obtain hγ | ⟨i, k, hi, hk, rfl⟩ | ⟨j, k, hn, hj, hk, rfl⟩ | ⟨k, k', hk, hk', rfl⟩ |
        ⟨k, k', hk, hk', rfl⟩ := hγ
    · exact .inl (.inl hγ)
    · rw [dite_eq_left ⟨by lia, k.pos⟩, List.mem_singleton]
      exact .inl (.inr (congrArg₂ (basicCommSq inj) (Fin.ext (by simp; lia)) (Fin.ext hk)))
    · rw [dite_eq_right (by lia), dite_eq_left ⟨by lia, k.pos⟩, List.mem_singleton]
      exact .inl (.inr (congrArg₂ (basicLinkSq inj c) (Fin.ext (by simp; lia)) (Fin.ext hk)))
    · rw [dite_eq_left (hk' ▸ k'.isLt : 1 < r)]
      exact .inr (List.mem_cons.2 (.inl (congrArg₂ (basicSqMul inj) (Fin.ext hk) (Fin.ext hk'))))
    · rw [dite_eq_left (hk' ▸ k'.isLt : 1 < r)]
      exact .inr (List.mem_pair.2 (.inr (congrArg₂ (basicSqConj inj) (Fin.ext hk) (Fin.ext hk'))))

variable {inj c} {γ : MulAut (GX G X)}

/-- The automorphisms of the orientable basic sequence of `S₀` fix `S₁` when the square variables
are distinct from the variables of `S₀`: they fix `S₀` and the square variables. -/
theorem apply_basicMixedWord_of_mem_basicWordSeq {inj : (Sum.elim (Sum.elim x y) z).Injective}
    (hγ : γ ∈ basicWordSeq inj c) (hu : ∀ a k, Sum.elim (Sum.elim x y) z a ≠ u k) :
    γ (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  have hsq (k : Fin r) : γ (sqAtom u k) = sqAtom u k := by
    rw [sqAtom_def, map_pow, apply_inr_of_of_mem_basicWordSeq _ c hγ fun a ↦ hu a k]
  rw [basicMixedWord_def, map_mul, apply_basicWord_of_mem_basicWordSeq _ c hγ,
    List.map_prod_ofFn_of_forall _ _ hsq]

/-- Every automorphism of the basic sequence of `S₁` fixes `S₁`. -/
theorem apply_basicMixedWord_of_mem_basicMixedWordSeq (hγ : γ ∈ basicMixedWordSeq inj c) :
    γ (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  obtain hγ | ⟨i, k, hi, hk, rfl⟩ | ⟨j, k, hn, hj, hk, rfl⟩ | ⟨k, k', hk, hk', rfl⟩ |
      ⟨k, k', hk, hk', rfl⟩ := (mem_basicMixedWordSeq_iff inj c).1 hγ
  · exact apply_basicMixedWord_of_mem_basicWordSeq hγ (Sum.elim_injective.1 inj).2.2
  · exact basicCommSq_basicMixedWord inj c i k hi hk
  · exact basicLinkSq_basicMixedWord inj c j k hn hj hk
  · exact basicSqMul_basicMixedWord inj c k k' (by lia)
  · exact basicSqConj_basicMixedWord inj c k k' (by lia)

/-- Every automorphism of the basic sequence of `S₁` fixes the coefficients. -/
theorem apply_inl_of_mem_basicMixedWordSeq (hγ : γ ∈ basicMixedWordSeq inj c) (g : G) :
    γ (inl g) = inl g := by
  obtain hγ | ⟨i, k, -, -, rfl⟩ | ⟨j, k, -, -, -, rfl⟩ | ⟨k, k', -, -, rfl⟩ |
      ⟨k, k', -, -, rfl⟩ := (mem_basicMixedWordSeq_iff inj c).1 hγ
  · exact apply_inl_of_mem_basicWordSeq _ c hγ g
  · exact basicCommSq_inl inj i k g
  · exact basicLinkSq_inl inj c j k g
  · exact basicSqMul_inl inj k k' g
  · exact basicSqConj_inl inj k k' g

end Seq

/-! ### Non-orientable standard quadratic equations -/

section Standard

open Quadratic Quadratic.Standard

/-- The basic sequence of automorphisms of `G[X]` of a non-orientable standard quadratic equation
`S = 1`: the basic sequence of the word `S₁` of its mixed form ([IFT], §7.5, (113), (114)). -/
noncomputable def mixedBasicSeq : (S : Standard G X) → ¬S.IsOrientable → List (MulAut (GX G X))
  | .orientable _ hn _ _ inj, h => (h (isOrientable_orientable hn inj)).elim
  | .orientableCoeff _ _ hnm _ _ _ inj _ hc _ hd, h =>
    (h (isOrientable_orientableCoeff hnm inj hc hd)).elim
  | .nonorientable _ _ _ inj, _ =>
    basicMixedWordSeq (injective_sumElim_mixed (inj.sumElim_of_isEmpty Fin.elim0)) Fin.elim0
  | .nonorientableCoeff _ _ _ _ _ inj c _ _ _, _ =>
    basicMixedWordSeq (injective_sumElim_mixed inj) c

variable {N : ℕ} {x : Fin N → X} {z : Fin m → X} {c : Fin m → G} {d : G}

theorem mixedBasicSeq_nonorientable (hN : 0 < N) (inj : x.Injective) :
    mixedBasicSeq (nonorientable (G := G) N hN x inj) (not_isOrientable_nonorientable hN inj) =
      basicMixedWordSeq (injective_sumElim_mixed (inj.sumElim_of_isEmpty Fin.elim0))
        Fin.elim0 := (rfl)

theorem mixedBasicSeq_nonorientableCoeff (hN : 0 < N) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    mixedBasicSeq (nonorientableCoeff N m hN x z inj c hc d hd)
        (not_isOrientable_nonorientableCoeff hN inj hc hd) =
      basicMixedWordSeq (injective_sumElim_mixed inj) c := (rfl)

/-- The product of the mixed atoms of `x₀² ⋯ x²_{N-1} = 1` is the word `S₁` of its mixed
variables. -/
theorem basicMixedWord_eq_prod_mixedAtoms_nonorientable (hN : 0 < N) (inj : x.Injective) :
    basicMixedWord (mixedFst x) (mixedSnd x) Fin.elim0 (mixedSq x) (Fin.elim0 : Fin 0 → G) =
      ((nonorientable N hN x inj).mixedAtoms (not_isOrientable_nonorientable hN inj)).prod := by
  simp [basicMixedWord_def, basicWord_def, funext (commAtom_def (G := G) (mixedFst x) (mixedSnd x)),
    funext (sqAtom_def (G := G) (mixedSq x))]

/-- The product of the mixed atoms of `x₀² ⋯ x²_{N-1} ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` is the word `S₁` of its
mixed variables and coefficients. -/
theorem basicMixedWord_eq_prod_mixedAtoms_nonorientableCoeff (hN : 0 < N)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    basicMixedWord (mixedFst x) (mixedSnd x) z (mixedSq x) c =
      ((nonorientableCoeff N m hN x z inj c hc d hd).mixedAtoms
        (not_isOrientable_nonorientableCoeff hN inj hc hd)).prod := by
  simp [basicMixedWord_def, basicWord_def, funext (coeffAtom_def z c),
    funext (commAtom_def (G := G) (mixedFst x) (mixedSnd x)),
    funext (sqAtom_def (G := G) (mixedSq x)), mul_assoc]

variable {S : Standard G X} (ho : ¬S.IsOrientable) {γ : MulAut (GX G X)}

/-- Every automorphism of the basic sequence of a non-orientable standard quadratic equation fixes
the coefficients. -/
theorem apply_inl_of_mem_mixedBasicSeq (hγ : γ ∈ mixedBasicSeq S ho) (g : G) :
    γ (inl g) = inl g := by
  cases S with
  | orientable n hn x y inj => exact absurd (isOrientable_orientable hn inj) ho
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    exact absurd (isOrientable_orientableCoeff hnm inj hc hd) ho
  | nonorientable N hN x inj =>
    rw [mixedBasicSeq_nonorientable hN inj] at hγ
    exact apply_inl_of_mem_basicMixedWordSeq hγ g
  | nonorientableCoeff N m hN x z inj c hc d hd =>
    rw [mixedBasicSeq_nonorientableCoeff hN inj hc hd] at hγ
    exact apply_inl_of_mem_basicMixedWordSeq hγ g

/-- Every automorphism of the basic sequence of a non-orientable standard quadratic equation fixes
the left side of its mixed form. -/
theorem apply_mixedWord_of_mem_mixedBasicSeq (hγ : γ ∈ mixedBasicSeq S ho) :
    γ (S.mixedWord ho) = S.mixedWord ho := by
  rw [mixedWord_def, map_mul, apply_inl_of_mem_mixedBasicSeq ho hγ]
  congr 1
  cases S with
  | orientable n hn x y inj => exact absurd (isOrientable_orientable hn inj) ho
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    exact absurd (isOrientable_orientableCoeff hnm inj hc hd) ho
  | nonorientable N hN x inj =>
    rw [mixedBasicSeq_nonorientable hN inj] at hγ
    rw [← basicMixedWord_eq_prod_mixedAtoms_nonorientable hN inj]
    exact apply_basicMixedWord_of_mem_basicMixedWordSeq hγ
  | nonorientableCoeff N m hN x z inj c hc d hd =>
    rw [mixedBasicSeq_nonorientableCoeff hN inj hc hd] at hγ
    rw [← basicMixedWord_eq_prod_mixedAtoms_nonorientableCoeff hN inj hc hd]
    exact apply_basicMixedWord_of_mem_basicMixedWordSeq hγ

/-- The automorphisms `φ_{j,p}` of a non-orientable standard quadratic equation fix the left side
of its mixed form. -/
@[simp]
theorem phi_mixedBasicSeq_mixedWord (p : List ℕ) :
    phi (mixedBasicSeq S ho) p (S.mixedWord ho) = S.mixedWord ho :=
  phi_apply_of_forall_mem (fun _ hγ ↦ apply_mixedWord_of_mem_mixedBasicSeq ho hγ) p

/-- The automorphisms `φ_{j,p}` of a non-orientable standard quadratic equation fix the
coefficients. -/
@[simp]
theorem phi_mixedBasicSeq_inl (p : List ℕ) (g : G) :
    phi (mixedBasicSeq S ho) p (inl g) = inl g :=
  phi_apply_of_forall_mem (fun _ hγ ↦ apply_inl_of_mem_mixedBasicSeq ho hγ g) p

/-- **The length of the basic sequence.** The basic sequence of a non-orientable standard quadratic
equation of genus `N` with `m` conjugated coefficients has `m + 2N - 2` terms: `m + 4n + 2` for
`N = 2n + 2` (two squares) and `m + 4n` for `N = 2n + 1` (one square). -/
@[simp]
theorem length_mixedBasicSeq : (mixedBasicSeq S ho).length = S.atomicRank + S.genus - 2 := by
  cases S with
  | orientable n hn x y inj => exact absurd (isOrientable_orientable hn inj) ho
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    exact absurd (isOrientable_orientableCoeff hnm inj hc hd) ho
  | nonorientable N hN x inj =>
    simp only [mixedBasicSeq_nonorientable hN inj, length_basicMixedWordSeq,
      atomicRank_nonorientable, genus_nonorientable]
    split_ifs <;> lia
  | nonorientableCoeff N m hN x z inj c hc d hd =>
    simp only [mixedBasicSeq_nonorientableCoeff hN inj hc hd, length_basicMixedWordSeq,
      atomicRank_nonorientableCoeff, genus_nonorientableCoeff]
    split_ifs <;> lia

/-- **The length of the basic sequence, two squares** ([IFT], §7.5, where `K(m, 0) = m + 2` and
`K(m, n) = m + 4n + 2` for `n ≥ 1`). For `x₀² ⋯ x²_{2n+1} ∏ⱼ₌₁ᵐ zⱼ⁻¹ cⱼ zⱼ d = 1`, whose mixed
form has `n` commutators and two squares, the basic sequence has `m + 4n + 2` terms. -/
theorem length_mixedBasicSeq_nonorientableCoeff_two_mul_add_two {x : Fin (2 * n + 2) → X}
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (mixedBasicSeq (nonorientableCoeff (2 * n + 2) m (by lia) x z inj c hc d hd)
      (not_isOrientable_nonorientableCoeff _ inj hc hd)).length = m + 4 * n + 2 := by
  simp [atomicRank_nonorientableCoeff]
  lia

end Standard

end TauCeti.GroupAlgGeom.Lift
