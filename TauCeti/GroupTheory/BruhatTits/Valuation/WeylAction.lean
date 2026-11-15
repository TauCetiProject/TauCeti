/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BruhatTits.Valuation.Basic
public import TauCeti.GroupTheory.BruhatTits.WeylGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.RootSystem.CoweightLattice

/-!
# Discrete valuations and the action of the Weyl normalizer on valuations

Let `D` be a root datum of type `Φ` in a group `G` and `φ` a valuation of `D` in the sense of
Bruhat–Tits (`TauCeti.BruhatTits.Valuation`). This file defines closed-discrete valuations and, when
`Φ` is finite and crystallographic, constructs the left action of `D.weylNormalizer` on
`Valuation D`, proves the Bruhat–Tits reflection formula, and shows that every element of
`D.weylNormalizer` acts on `φ` by a unique shift in the real coroot span `P.corootSpan ℝ`
(so Weyl-conjugate valuations are equipollent).

## Main definitions

* `TauCeti.BruhatTits.Valuation.IsDiscrete`: finiteness of `Γ a ∩ [r, s]` for every root `a` and
  closed interval `[r, s] ⊆ ℝ` (Bruhat–Tits I, Définition 6.2.21, closed-discrete form).
* `SMul D.weylNormalizer (Valuation D)` and `MulAction D.weylNormalizer (Valuation D)`: the action
  `(n • φ) a (u) = φ (w⁻¹ a) (n⁻¹ u n)`, where `w = D.weylGroupHom n` (Bruhat–Tits I, 6.2.5).

## Main results

* `TauCeti.BruhatTits.Valuation.isDiscrete_of_isEmpty`,
  `TauCeti.BruhatTits.Valuation.isDiscrete_shift_iff`,
  `TauCeti.BruhatTits.Valuation.Equipollent.isDiscrete_iff`, and
  `TauCeti.BruhatTits.Valuation.isDiscrete_smul_iff`: discreteness holds for empty root data and is
  invariant under shifts, equipollence, and the action of `D.weylNormalizer`.
* `TauCeti.BruhatTits.Valuation.smul_apply` and
  `TauCeti.BruhatTits.Valuation.smul_apply_weylGroupEquiv`: pointwise formulas for `n • φ` in terms
  of `D.weylGroupHom` and `D.weylGroupEquiv`.
* `TauCeti.BruhatTits.Valuation.filtration_smul`, `TauCeti.BruhatTits.Valuation.conj_filtration`,
  and `TauCeti.BruhatTits.Valuation.valueSet_smul`: interaction of `n • φ` with filtration subgroups
  and value sets (Bruhat–Tits I, 6.2.10 (iii)).
* `TauCeti.BruhatTits.Valuation.shift_eq_shift_iff_of_mem_corootSpan`: shifts from
  `P.corootSpan ℝ` act faithfully on valuations.
* `TauCeti.BruhatTits.Valuation.isCompatible_iff_smul`: compatibility with `ν : D.T → N` is
  equivalent to every `z ∈ D.T` acting on `φ` by `φ.shift (ν z)`.
* `TauCeti.BruhatTits.Valuation.smul_shift`: equivariance `n • φ.shift v = (n • φ).shift (w v)`.
* `TauCeti.BruhatTits.Valuation.smul_reflection` and
  `TauCeti.BruhatTits.Valuation.smul_reflection_apply_self`: if `m = u' u u'' ∈ M a` with
  `φ a u = k`, then `m • φ = φ.shift (-(k • P.coroot i))` (Bruhat–Tits I, Proposition 6.2.7).
* `TauCeti.BruhatTits.Valuation.existsUnique_mem_corootSpan_smul_eq_shift` and
  `TauCeti.BruhatTits.Valuation.equipollent_smul`: every `n ∈ D.weylNormalizer` shifts `φ` by a
  unique vector in `P.corootSpan ℝ`, preserving equipollence classes (Bruhat–Tits I, 6.2.5).

## References

* [F. Bruhat and J. Tits, *Groupes réductifs sur un corps local : I. Données radicielles
  valuées*][BruhatTits1972], §§6.2.5, 6.2.7, 6.2.10, 6.2.21.
-/

public section

open scoped Pointwise commutatorElement

namespace TauCeti.BruhatTits

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {G : Type*} [Group G]

/-! ### Discrete valuations -/

section Discrete

variable {R : Type*} [Field R] [LinearOrder R] [Module R M] [Module R N]
  {P : RootPairing ι R M N} {D : RootDatum P G}

namespace Valuation

/-- A valuation is *discrete* (in the closed-discrete sense) if each value set `Γ a` meets every
closed bounded interval `[r, s] ⊆ ℝ` in a finite set (cf. Bruhat–Tits I, Définition 6.2.21,
p. 127; for the cosets of discrete subgroups arising from reductive groups this agrees with
discreteness in `ℝ`). -/
def IsDiscrete (φ : Valuation D) : Prop :=
  ∀ (i : ι) (r s : ℝ), (φ.valueSet i ∩ Set.Icc r s).Finite

theorem isDiscrete_iff (φ : Valuation D) :
    φ.IsDiscrete ↔ ∀ (i : ι) (r s : ℝ), (φ.valueSet i ∩ Set.Icc r s).Finite :=
  Iff.rfl

theorem IsDiscrete.finite_inter_Icc {φ : Valuation D} (h : φ.IsDiscrete) (i : ι) (r s : ℝ) :
    (φ.valueSet i ∩ Set.Icc r s).Finite :=
  h i r s

/-- Every valuation of a root datum with no roots is discrete. -/
@[simp]
theorem isDiscrete_of_isEmpty [IsEmpty ι] (φ : Valuation D) : φ.IsDiscrete :=
  isEmptyElim

end Valuation

end Discrete

/-! ### Action of the Weyl normalizer on valuations -/

section WeylNormalizer

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Module R M] [Module R N] {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

namespace RootDatum

variable (D : RootDatum P G)

/-- Conjugating `D.U i` on the right by `n ∈ D.weylNormalizer` lands in
`D.U (w⁻¹ i)`, where `w = D.weylGroupHom n`. -/
theorem inv_mul_mul_mem_U_weylNormalizer (n : D.weylNormalizer) {i : ι} {u : G} (hu : u ∈ D.U i) :
    (n : G)⁻¹ * u * n ∈ D.U (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) := by
  rw [← Subgroup.mem_conjAct_smul_iff, D.weylGroupHom_conj, ← Equiv.Perm.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  exact hu

/-- Conjugating `D.reflectionCoset i` on the right by `n ∈ D.weylNormalizer` lands in
`D.reflectionCoset (w⁻¹ i)`, where `w = D.weylGroupHom n`. -/
theorem inv_mul_mul_mem_reflectionCoset_weylNormalizer (n : D.weylNormalizer) {i : ι} {m : G}
    (hm : m ∈ D.reflectionCoset i) :
    (n : G)⁻¹ * m * n ∈ D.reflectionCoset (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) := by
  set j := P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i
  obtain ⟨m', hm'⟩ := D.reflectionCoset_nonempty j
  let nm : D.weylNormalizer := ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩
  let nm' : D.weylNormalizer := ⟨m', D.reflectionCoset_subset_weylNormalizer j hm'⟩
  have hker : n⁻¹ * nm * n * nm'⁻¹ ∈ D.weylGroupHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      D.weylGroupHom_reflection hm, D.weylGroupHom_reflection hm']
    have hconj := RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj P (D.weylGroupHom n)⁻¹ i
    rw [inv_inv] at hconj
    rw [← hconj, mul_inv_cancel]
  rw [D.ker_weylGroupHom, Subgroup.mem_subgroupOf] at hker
  exact (D.mem_reflectionCoset_iff_mul_inv_mem_T hm').mpr hker

end RootDatum

namespace Valuation

variable {D : RootDatum P G}

/-- Two valuations of a finite crystallographic root datum agree as soon as they agree on every
indivisible root, by (V4). -/
theorem ext_of_isIndivisible {φ ψ : Valuation D}
    (h : ∀ i : ι, P.IsIndivisible i → ∀ u : D.U i, φ i u = ψ i u) : φ = ψ := by
  ext j u
  rcases P.isIndivisible_or_exists_root_eq_two_smul j with hj | ⟨i, hi, hij⟩
  · exact h j hj u
  · rw [φ.apply_eq_two_smul i j hij u, ψ.apply_eq_two_smul i j hij u, h i hi]

omit [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
private theorem apply_congr (φ : Valuation D) {i j : ι} (hij : i = j) {u : D.U i} {v : D.U j}
    (huv : (u : G) = v) : φ i u = φ j v := by
  subst hij
  exact congrArg (φ i) (Subtype.ext huv)

private theorem weylGroupToPerm_inv_inv_apply (n : D.weylNormalizer) (i : ι) :
    P.weylGroupToPerm (D.weylGroupHom n⁻¹)⁻¹ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) = i := by
  rw [D.weylGroupHom.map_inv n, inv_inv, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Equiv.Perm.one_apply]

private theorem smul_three_le_encard_range (n : D.weylNormalizer) (φ : Valuation D) (i : ι) :
    3 ≤ (Set.range fun u : D.U i ↦ φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i)
      ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩).encard := by
  set j := P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i
  have hrange : (Set.range fun u : D.U i ↦ φ j
      ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩) = Set.range (φ j) := by
    refine Set.Subset.antisymm (Set.range_comp_subset_range _ (φ j)) ?_
    rintro _ ⟨v, rfl⟩
    have hu : (n : G) * v * (n : G)⁻¹ ∈ D.U i := by
      have hmem := weylGroupToPerm_inv_inv_apply n i ▸ D.inv_mul_mul_mem_U_weylNormalizer n⁻¹ v.2
      simpa only [Subgroup.coe_inv, inv_inv] using hmem
    exact ⟨⟨(n : G) * v * (n : G)⁻¹, hu⟩, φ.apply_congr rfl (by dsimp only; group)⟩
  rw [hrange]
  exact φ.three_le_encard_range j

private theorem smul_exists_apply_eq_apply_conj_add (n : D.weylNormalizer) (φ : Valuation D)
    (i : ι) (m : G) (hm : m ∈ D.reflectionCoset i) :
    ∃ c : ℝ, ∀ u : D.U (P.reflectionPerm i i), u ≠ 1 →
      φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ (P.reflectionPerm i i))
          ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩ =
        φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i)
          ⟨(n : G)⁻¹ * (m * u * m⁻¹) * n,
            D.inv_mul_mul_mem_U_weylNormalizer n
              (D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm u.2)⟩ + c := by
  set w := (D.weylGroupHom n)⁻¹
  set j := P.weylGroupToPerm w i
  have hneg : P.weylGroupToPerm w (P.reflectionPerm i i) = P.reflectionPerm j j :=
    P.weylGroupToPerm_neg w i
  have hm' : (n : G)⁻¹ * m * n ∈ D.reflectionCoset j :=
    D.inv_mul_mul_mem_reflectionCoset_weylNormalizer n hm
  obtain ⟨c, hc⟩ := φ.exists_apply_eq_apply_conj_add j ((n : G)⁻¹ * m * n) hm'
  refine ⟨c, fun u hu ↦ ?_⟩
  have hu_mem : (n : G)⁻¹ * u * n ∈ D.U (P.reflectionPerm j j) :=
    hneg ▸ D.inv_mul_mul_mem_U_weylNormalizer n u.2
  have hu' : (⟨(n : G)⁻¹ * u * n, hu_mem⟩ : D.U (P.reflectionPerm j j)) ≠ 1 := fun h ↦ hu <|
    Subtype.ext <| by
      have h0 : (n : G)⁻¹ * u * n = 1 := congrArg Subtype.val h
      calc (u : G) = n * ((n : G)⁻¹ * u * n) * (n : G)⁻¹ := by group
        _ = 1 := by rw [h0]; group
  rw [φ.apply_congr hneg (v := ⟨(n : G)⁻¹ * u * n, hu_mem⟩) rfl, hc _ hu']
  exact congrArg (· + (c : WithTop ℝ)) (φ.apply_congr rfl (by dsimp only; group))

private theorem conj_mem_closure_smul (n : D.weylNormalizer) (φ : Valuation D) (i j : ι)
    (k l : ℝ) {y : G}
    (hy : y ∈ Subgroup.closure {g | ∃ (m' : ι) (p q : ℕ), 0 < p ∧ 0 < q ∧
      P.root m' = p • P.root (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) +
        q • P.root (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ j) ∧
      ∃ hy : g ∈ D.U m', ((p * k + q * l : ℝ) : WithTop ℝ) ≤ φ m' ⟨g, hy⟩}) :
    (n : G) * y * (n : G)⁻¹ ∈ Subgroup.closure {g | ∃ (m : ι) (p q : ℕ), 0 < p ∧ 0 < q ∧
      P.root m = p • P.root i + q • P.root j ∧
      ∃ hg : g ∈ D.U m, ((p * k + q * l : ℝ) : WithTop ℝ) ≤
        φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ m)
          ⟨(n : G)⁻¹ * g * n, D.inv_mul_mul_mem_U_weylNormalizer n hg⟩} := by
  set w := (D.weylGroupHom n)⁻¹
  have hr : ∀ b : ι, (D.weylGroupHom n : P.Aut).weightEquiv (P.root (P.weylGroupToPerm w b)) =
      P.root b := fun b ↦ by
    change (D.weylGroupHom n) • P.root (P.weylGroupToPerm w b) = P.root b
    rw [P.weylGroup_apply_root, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Equiv.Perm.one_apply]
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨m', p, q, hp, hq, hm', hyU, hval⟩ := hy
    set m := P.weylGroupToPerm (D.weylGroupHom n) m'
    have hwm : P.weylGroupToPerm w m = m' := by
      simp only [w, m, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Equiv.Perm.one_apply]
    have hrm : P.root m = p • P.root i + q • P.root j := by
      have h1 := congrArg (D.weylGroupHom n : P.Aut).weightEquiv hm'
      rw [map_add, map_nsmul, map_nsmul, hr i, hr j] at h1
      exact (P.weylGroup_apply_root (D.weylGroupHom n) m').symm.trans h1
    have hgU : (n : G) * y * (n : G)⁻¹ ∈ D.U m := by
      rw [← D.weylGroupHom_conj n m', ← ConjAct.toConjAct_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hyU
    refine Subgroup.subset_closure ⟨m, p, q, hp, hq, hrm, hgU, ?_⟩
    exact hval.trans_eq (φ.apply_congr hwm.symm (by dsimp only; group))
  | one => simp
  | mul x y _ _ ihx ihy =>
    have heq : (n : G) * (x * y) * (n : G)⁻¹ =
        ((n : G) * x * (n : G)⁻¹) * ((n : G) * y * (n : G)⁻¹) := by group
    exact heq ▸ mul_mem ihx ihy
  | inv x _ ih =>
    have heq : (n : G) * x⁻¹ * (n : G)⁻¹ = ((n : G) * x * (n : G)⁻¹)⁻¹ := by group
    exact heq ▸ inv_mem ih

private theorem smul_commutator_mem (n : D.weylNormalizer) (φ : Valuation D) (i j : ι)
    (hij : ∀ c : R, 0 < c → P.root j ≠ -(c • P.root i)) (k l : ℝ) (u : D.U i) (v : D.U j)
    (hu : (k : WithTop ℝ) ≤ φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i)
      ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩)
    (hv : (l : WithTop ℝ) ≤ φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ j)
      ⟨(n : G)⁻¹ * v * n, D.inv_mul_mul_mem_U_weylNormalizer n v.2⟩) :
    ⁅(u : G), (v : G)⁆ ∈ Subgroup.closure {g | ∃ (m : ι) (p q : ℕ), 0 < p ∧ 0 < q ∧
      P.root m = p • P.root i + q • P.root j ∧
      ∃ hg : g ∈ D.U m, ((p * k + q * l : ℝ) : WithTop ℝ) ≤
        φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ m)
          ⟨(n : G)⁻¹ * g * n, D.inv_mul_mul_mem_U_weylNormalizer n hg⟩} := by
  set w := (D.weylGroupHom n)⁻¹
  have hr : ∀ b : ι, (D.weylGroupHom n : P.Aut).weightEquiv (P.root (P.weylGroupToPerm w b)) =
      P.root b := fun b ↦ by
    change (D.weylGroupHom n) • P.root (P.weylGroupToPerm w b) = P.root b
    rw [P.weylGroup_apply_root, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Equiv.Perm.one_apply]
  have hij' : ∀ c : R, 0 < c →
      P.root (P.weylGroupToPerm w j) ≠ -(c • P.root (P.weylGroupToPerm w i)) := by
    intro c hc h0
    refine hij c hc ?_
    have h1 := congrArg (D.weylGroupHom n : P.Aut).weightEquiv h0
    rw [map_neg, map_smul, hr i, hr j] at h1
    exact h1
  have hcm := φ.commutator_mem _ _ hij' k l
    ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩
    ⟨(n : G)⁻¹ * v * n, D.inv_mul_mul_mem_U_weylNormalizer n v.2⟩ hu hv
  have hcomm_eq : ⁅((n : G)⁻¹ * u * n), ((n : G)⁻¹ * v * n)⁆ =
      (n : G)⁻¹ * ⁅(u : G), (v : G)⁆ * n := by
    simp only [commutatorElement_def]
    group
  rw [hcomm_eq] at hcm
  have hres := conj_mem_closure_smul n φ i j k l hcm
  have heq : (n : G) * ((n : G)⁻¹ * ⁅(u : G), (v : G)⁆ * n) * (n : G)⁻¹ = ⁅(u : G), (v : G)⁆ := by
    group
  rwa [heq] at hres

private theorem smul_apply_reflectionPerm_left (n : D.weylNormalizer) (φ : Valuation D) (i : ι)
    (u : D.U i) (u' u'' : D.U (P.reflectionPerm i i))
    (h : (u' : G) * u * u'' ∈ D.reflectionCoset i) :
    φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ (P.reflectionPerm i i))
        ⟨(n : G)⁻¹ * u' * n, D.inv_mul_mul_mem_U_weylNormalizer n u'.2⟩ =
      -φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i)
        ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩ := by
  set w := (D.weylGroupHom n)⁻¹
  set j := P.weylGroupToPerm w i
  have hneg : P.weylGroupToPerm w (P.reflectionPerm i i) = P.reflectionPerm j j :=
    P.weylGroupToPerm_neg w i
  have hu' : (n : G)⁻¹ * u' * n ∈ D.U (P.reflectionPerm j j) :=
    hneg ▸ D.inv_mul_mul_mem_U_weylNormalizer n u'.2
  have hu'' : (n : G)⁻¹ * u'' * n ∈ D.U (P.reflectionPerm j j) :=
    hneg ▸ D.inv_mul_mul_mem_U_weylNormalizer n u''.2
  have hm' : ((n : G)⁻¹ * u' * n) * ((n : G)⁻¹ * u * n) * ((n : G)⁻¹ * u'' * n) ∈
      D.reflectionCoset j := by
    have heq : ((n : G)⁻¹ * u' * n) * ((n : G)⁻¹ * u * n) * ((n : G)⁻¹ * u'' * n) =
        (n : G)⁻¹ * ((u' : G) * u * u'') * n := by group
    rw [heq]
    exact D.inv_mul_mul_mem_reflectionCoset_weylNormalizer n h
  rw [φ.apply_congr hneg (v := ⟨(n : G)⁻¹ * u' * n, hu'⟩) rfl]
  exact φ.apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset j
    ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩
    ⟨(n : G)⁻¹ * u' * n, hu'⟩ ⟨(n : G)⁻¹ * u'' * n, hu''⟩ hm'

/-- The Weyl normalizer `D.weylNormalizer` acts on `Valuation D` by
`(n • φ) a (u) = φ (w⁻¹ a) (n⁻¹ u n)`, where `w = D.weylGroupHom n` (Bruhat–Tits I, 6.2.5). -/
noncomputable instance : SMul D.weylNormalizer (Valuation D) where
  smul n φ :=
    { toFun i u := φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i)
        ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩
      three_le_encard_range i := by exact smul_three_le_encard_range n φ i
      min_le_apply_mul i u v := by
        refine (φ.min_le_apply_mul _ _ _).trans_eq (φ.apply_congr rfl ?_)
        simp only [Subgroup.coe_mul]
        group
      apply_le_apply_inv i u := by
        refine (φ.apply_le_apply_inv _ _).trans_eq (φ.apply_congr rfl ?_)
        simp only [Subgroup.coe_inv]
        group
      apply_eq_top_iff i u := by
        rw [φ.apply_eq_top_iff, ← Subtype.coe_inj, ← Subtype.coe_inj]
        dsimp only [OneMemClass.coe_one]
        exact ⟨fun h ↦ by
          calc (u : G) = n * ((n : G)⁻¹ * u * n) * (n : G)⁻¹ := by group
            _ = 1 := by rw [h]; group,
          fun h ↦ by rw [h]; group⟩
      exists_apply_eq_apply_conj_add i m hm := by
        exact smul_exists_apply_eq_apply_conj_add n φ i m hm
      commutator_mem i j hij k l u v hu hv := by
        exact smul_commutator_mem n φ i j hij k l u v hu hv
      apply_eq_two_smul i j h u := by
        set w := (D.weylGroupHom n)⁻¹
        have h' : P.root (P.weylGroupToPerm w j) = (2 : R) • P.root (P.weylGroupToPerm w i) := by
          rw [← P.weylGroup_apply_root, ← P.weylGroup_apply_root, h]
          exact LinearEquiv.map_smul (w : P.Aut).weightEquiv (2 : R) (P.root i)
        exact φ.apply_eq_two_smul _ _ h'
          ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩
      apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset i u u' u'' h := by
        exact smul_apply_reflectionPerm_left n φ i u u' u'' h }

@[simp]
theorem smul_apply (n : D.weylNormalizer) (φ : Valuation D) (i : ι) (u : D.U i) :
    (n • φ) i u = φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i)
      ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩ :=
  (rfl)

/-- Pointwise formula for `n • φ` in terms of `D.weylGroupEquiv : N / T ≃* W(Φ)`. -/
theorem smul_apply_weylGroupEquiv (n : D.weylNormalizer) (φ : Valuation D) (i : ι) (u : D.U i) :
    (n • φ) i u = φ (P.weylGroupToPerm (D.weylGroupEquiv (QuotientGroup.mk n))⁻¹ i)
      ⟨(n : G)⁻¹ * u * n,
        D.weylGroupEquiv_mk n ▸ D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩ := by
  rw [smul_apply]
  exact φ.apply_congr (by rw [D.weylGroupEquiv_mk]) rfl

noncomputable instance : MulAction D.weylNormalizer (Valuation D) where
  one_smul φ := by
    ext i u
    rw [smul_apply]
    exact φ.apply_congr (by simp) (by simp)
  mul_smul n₁ n₂ φ := by
    ext i u
    rw [smul_apply, smul_apply, smul_apply]
    have hidx : P.weylGroupToPerm (D.weylGroupHom (n₁ * n₂))⁻¹ i =
        P.weylGroupToPerm (D.weylGroupHom n₂)⁻¹ (P.weylGroupToPerm (D.weylGroupHom n₁)⁻¹ i) := by
      rw [map_mul, mul_inv_rev, map_mul, Equiv.Perm.mul_apply]
    exact φ.apply_congr hidx (by simp only [Subgroup.coe_mul]; group)

/-- The filtration of `n • φ` at `i` is the `n`-conjugate of the filtration of `φ` at `w⁻¹ i`. -/
@[simp]
theorem filtration_smul (n : D.weylNormalizer) (φ : Valuation D) (i : ι) (k : ℝ) :
    (n • φ).filtration i k =
      ConjAct.toConjAct (n : G) • φ.filtration (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) k := by
  ext g
  rw [Subgroup.mem_conjAct_smul_iff, mem_filtration_iff, mem_filtration_iff]
  constructor
  · rintro ⟨hg, hk⟩
    exact ⟨D.inv_mul_mul_mem_U_weylNormalizer n hg, by rwa [smul_apply] at hk⟩
  · rintro ⟨hg', hk⟩
    have hg : g ∈ D.U i := by
      have hmem := weylGroupToPerm_inv_inv_apply n i ▸ D.inv_mul_mul_mem_U_weylNormalizer n⁻¹ hg'
      have heq : ((n⁻¹ : D.weylNormalizer) : G)⁻¹ * ((n : G)⁻¹ * g * n) *
          ((n⁻¹ : D.weylNormalizer) : G) = g := by
        simp only [Subgroup.coe_inv]
        group
      rwa [heq] at hmem
    exact ⟨hg, by rwa [smul_apply]⟩

/-- Conjugating a filtration subgroup by `n ∈ D.weylNormalizer` transports both the root index and
the valuation (Bruhat–Tits I, 6.2.10 (iii)). -/
theorem conj_filtration (n : D.weylNormalizer) (φ : Valuation D) (i : ι) (k : ℝ) :
    ConjAct.toConjAct (n : G) • φ.filtration i k =
      (n • φ).filtration (P.weylGroupToPerm (D.weylGroupHom n) i) k := by
  rw [filtration_smul, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Equiv.Perm.one_apply]

/-- Acting by `n ∈ D.weylNormalizer` permutes the value sets along `w⁻¹`. -/
@[simp]
theorem valueSet_smul (n : D.weylNormalizer) (φ : Valuation D) (i : ι) :
    (n • φ).valueSet i = φ.valueSet (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) := by
  ext k
  simp only [mem_valueSet_iff, smul_apply]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩, hu⟩
  · rintro ⟨v, hv⟩
    have hu : (n : G) * v * (n : G)⁻¹ ∈ D.U i := by
      have hmem := weylGroupToPerm_inv_inv_apply n i ▸ D.inv_mul_mul_mem_U_weylNormalizer n⁻¹ v.2
      simpa only [Subgroup.coe_inv, inv_inv] using hmem
    exact ⟨⟨(n : G) * v * (n : G)⁻¹, hu⟩,
      (φ.apply_congr rfl (by dsimp only; group)).trans hv⟩

/-- Discreteness is invariant under the action of `D.weylNormalizer`. -/
@[simp]
theorem isDiscrete_smul_iff (n : D.weylNormalizer) (φ : Valuation D) :
    (n • φ).IsDiscrete ↔ φ.IsDiscrete := by
  refine ⟨fun h i r s ↦ ?_, fun h i r s ↦ ?_⟩
  · have h' := h (P.weylGroupToPerm (D.weylGroupHom n) i) r s
    rwa [valueSet_smul, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Equiv.Perm.one_apply] at h'
  · rw [valueSet_smul]
    exact h _ r s

end Valuation

end WeylNormalizer

/-! ### Shifts, compatibility, reflection formula, and equipollence of Weyl conjugates -/

namespace Valuation

variable [Module ℝ M] [Module ℝ N] {P : RootPairing ι ℝ M N} {D : RootDatum P G}
  (φ : Valuation D)

/-- Shifting a valuation preserves discreteness. -/
@[simp]
theorem isDiscrete_shift_iff (v : N) : (φ.shift v).IsDiscrete ↔ φ.IsDiscrete := by
  refine ⟨fun h i r s ↦ ?_, fun h i r s ↦ ?_⟩
  · refine ((h i (r + P.root' i v) (s + P.root' i v)).image (· - P.root' i v)).subset ?_
    rintro x ⟨hx, hrx, hxs⟩
    refine ⟨x + P.root' i v, ⟨?_, by linarith, by linarith⟩, by ring⟩
    rw [valueSet_shift]
    exact ⟨x, hx, rfl⟩
  · refine ((h i (r - P.root' i v) (s - P.root' i v)).image (· + P.root' i v)).subset ?_
    rintro x ⟨hx, hrx, hxs⟩
    rw [valueSet_shift] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨hy, by linarith, by linarith⟩, rfl⟩

variable {φ} in
/-- Discreteness is invariant under equipollence. -/
theorem Equipollent.isDiscrete_iff {ψ : Valuation D} (h : φ.Equipollent ψ) :
    φ.IsDiscrete ↔ ψ.IsDiscrete := by
  obtain ⟨v, hv⟩ := φ.equipollent_iff.mp h
  have hψ : ψ = φ.shift v := by ext i u; simp [hv i u]
  rw [hψ]
  exact (φ.isDiscrete_shift_iff v).symm

/-- On the real coroot span, shifts act faithfully on valuations. -/
theorem shift_eq_shift_iff_of_mem_corootSpan [Finite ι] {v w : N}
    (hv : v ∈ P.corootSpan ℝ) (hw : w ∈ P.corootSpan ℝ) :
    φ.shift v = φ.shift w ↔ v = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have := Fintype.ofFinite ι
  have hker : v - w ∈ LinearMap.ker P.toDualRootSpan := by
    rw [LinearMap.mem_ker]
    ext ⟨x, hx⟩
    rw [RootPairing.toDualRootSpan_apply, LinearMap.zero_apply]
    have hroot : ∀ i : ι, P.toLinearMap (P.root i) (v - w) = 0 := fun i ↦ by
      obtain ⟨k, hk⟩ := (φ.valueSet_nontrivial i).nonempty
      obtain ⟨u, hu⟩ := φ.mem_valueSet_iff.mp hk
      have heq : (φ.shift v) i u = (φ.shift w) i u := congr($h i u)
      rw [shift_apply, shift_apply, hu] at heq
      norm_cast at heq
      have hsub : P.root' i v - P.root' i w = 0 := by linarith
      simpa [RootPairing.root', map_sub] using hsub
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hroot i
    | zero => simp
    | add y₁ y₂ _ _ ih₁ ih₂ => simp [ih₁, ih₂]
    | smul c y _ ih => simp [ih]
  exact sub_eq_zero.mp
    (Submodule.disjoint_def.mp P.disjoint_corootSpan_ker_toDualRootSpan _ (sub_mem hv hw) hker)

/-- For a finite crystallographic root pairing, `φ` is compatible with `ν : D.T → N` if and only
if every `z ∈ D.T` acts on `φ` by the shift `ν z`. -/
theorem isCompatible_iff_smul [Finite ι] [P.IsCrystallographic] {ν : D.T → N} :
    φ.IsCompatible ν ↔
      ∀ z : D.T, (⟨z, D.T_le_weylNormalizer z.2⟩ : D.weylNormalizer) • φ = φ.shift (ν z) := by
  constructor
  · intro h z
    let nz : D.weylNormalizer := ⟨z, D.T_le_weylNormalizer z.2⟩
    have hidx : ∀ i : ι, P.weylGroupToPerm (D.weylGroupHom nz)⁻¹ i = i := fun i ↦ by
      rw [D.weylGroupHom_torus z.2]; simp
    ext i u
    rw [smul_apply, shift_apply]
    refine (φ.apply_congr (hidx i)
      (v := ⟨(z : G)⁻¹ * u * z, D.inv_mul_mul_mem_U z.2 u.2⟩) rfl).trans ?_
    have hc := h.apply_conj z ⟨(z : G)⁻¹ * u * z, D.inv_mul_mul_mem_U z.2 u.2⟩
    have hu_eq : (⟨z * ((z : G)⁻¹ * u * z) * (z : G)⁻¹,
        D.mul_mul_inv_mem_U z.2 (D.inv_mul_mul_mem_U z.2 u.2)⟩ : D.U i) = u :=
      Subtype.ext (by dsimp only; group)
    rw [hu_eq] at hc
    rw [hc]
    generalize φ i ⟨(z : G)⁻¹ * u * z, D.inv_mul_mul_mem_U z.2 u.2⟩ = val
    cases val with
    | top => simp
    | coe r => norm_cast; ring
  · refine fun h ↦ φ.isCompatible_iff.mpr fun i z u ↦ ?_
    let nz : D.weylNormalizer := ⟨z, D.T_le_weylNormalizer z.2⟩
    have hidx : P.weylGroupToPerm (D.weylGroupHom nz)⁻¹ i = i := by
      rw [D.weylGroupHom_torus z.2]; simp
    let w : D.U i := ⟨z * u * (z : G)⁻¹, D.mul_mul_inv_mem_U z.2 u.2⟩
    have hz : (nz • φ) i w = (φ.shift (ν z)) i w := congr($(h z) i w)
    rw [smul_apply, shift_apply] at hz
    have hcongr : φ (P.weylGroupToPerm (D.weylGroupHom nz)⁻¹ i)
        ⟨(nz : G)⁻¹ * w * nz, D.inv_mul_mul_mem_U_weylNormalizer nz w.2⟩ = φ i u :=
      φ.apply_congr hidx (by dsimp [nz, w]; group)
    rw [hcongr] at hz
    rw [hz]
    generalize φ i w = val
    cases val with
    | top => simp
    | coe r => norm_cast; ring

section RealWeylAction

variable [Finite ι] [P.IsCrystallographic]

/-- Equivariance of valuation shifts under `D.weylNormalizer`: `n • (φ + v) = n • φ + w(v)`. -/
theorem smul_shift (n : D.weylNormalizer) (v : N) :
    n • φ.shift v = (n • φ).shift ((D.weylGroupHom n : P.Aut).coweightEquiv.symm v) := by
  ext i u
  rw [smul_apply, shift_apply, shift_apply, smul_apply]
  congr 1
  have h := (D.weylGroupHom n : P.Aut).root'_coweightEquiv
    ((D.weylGroupHom n : P.Aut).indexEquiv.symm i) v
  rw [Equiv.apply_symm_apply] at h
  exact congrArg WithTop.some h.symm

omit [P.IsCrystallographic] in
private theorem bijective_toDualRootSpan_corootSpan (P : RootPairing ι ℝ M N) :
    Function.Bijective (P.toDualRootSpan ∘ₗ (P.corootSpan ℝ).subtype) := by
  have := Fintype.ofFinite ι
  have hinj : Function.Injective (P.toDualRootSpan ∘ₗ (P.corootSpan ℝ).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, ← Submodule.disjoint_iff_comap_eq_bot]
    exact P.disjoint_corootSpan_ker_toDualRootSpan
  have : FiniteDimensional ℝ (P.rootSpan ℝ) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range P.root)
  have : FiniteDimensional ℝ (P.corootSpan ℝ) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range P.coroot)
  have hdim : Module.finrank ℝ (P.corootSpan ℝ) =
      Module.finrank ℝ (Module.Dual ℝ (P.rootSpan ℝ)) := by
    rw [P.finrank_corootSpan_eq', Subspace.dual_finrank_eq]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

omit [Finite ι] [P.IsCrystallographic] in
private theorem exists_root'_eq_zero_and_eq_one {i j : ι}
    (hli : LinearIndependent ℝ ![P.root i, P.root j]) :
    ∃ y : N, P.root' i y = 0 ∧ P.root' j y = 1 := by
  have hnotMem : P.root j ∉ Submodule.span ℝ {P.root i} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 := LinearIndependent.pair_iff.mp hli c (-1) (by simp [hc])
    linarith [h0.2]
  obtain ⟨g, hgi, hgj⟩ :=
    LinearMap.exists_extend_of_notMem (0 : Submodule.span ℝ {P.root i} →ₗ[ℝ] ℝ) hnotMem (1 : ℝ)
  refine ⟨P.flip.toPerfPair.symm g, ?_, ?_⟩
  · have h0 := congr($hgi ⟨P.root i, Submodule.mem_span_singleton_self _⟩)
    simpa [RootPairing.root'] using h0
  · simpa [RootPairing.root'] using hgj

omit [P.IsCrystallographic] in
private theorem exists_regular_preserve_pos (D : RootDatum P G) (y₀ : N) :
    ∃ z₀ : N, (∀ b : ι, P.root' b z₀ ≠ 0) ∧ ∀ b : ι, 0 < P.root' b y₀ → 0 < P.root' b z₀ := by
  have := Fintype.ofFinite ι
  let C : ℝ := (∑ b : ι, |P.root' b D.positiveVector| / |P.root' b y₀|) + 1
  have hlt : ∀ b : ι, |P.root' b D.positiveVector| / |P.root' b y₀| < C := fun b ↦ by
    have hle : |P.root' b D.positiveVector| / |P.root' b y₀| ≤
        ∑ c : ι, |P.root' c D.positiveVector| / |P.root' c y₀| :=
      Finset.single_le_sum (f := fun c : ι ↦ |P.root' c D.positiveVector| / |P.root' c y₀|)
        (fun _ _ ↦ div_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ b)
    linarith
  let z₀ : N := C • y₀ + D.positiveVector
  have hpos : ∀ b : ι, 0 < P.root' b y₀ → 0 < P.root' b z₀ := fun b hb ↦ by
    have h1 : |P.root' b D.positiveVector| / P.root' b y₀ < C := by
      simpa [abs_of_pos hb] using hlt b
    have h2 := (div_lt_iff₀ hb).mp h1
    have h3 : P.root' b z₀ = C * P.root' b y₀ + P.root' b D.positiveVector := by simp [z₀]
    linarith [neg_abs_le (P.root' b D.positiveVector)]
  refine ⟨z₀, fun b ↦ ?_, hpos⟩
  rcases lt_trichotomy (P.root' b y₀) 0 with hneg | hzero | hgt
  · have hpos' : 0 < -P.root' b y₀ := neg_pos.mpr hneg
    have h1 : |P.root' b D.positiveVector| / (-P.root' b y₀) < C := by
      simpa [abs_of_neg hneg] using hlt b
    have h2 := (div_lt_iff₀ hpos').mp h1
    have h3 : P.root' b z₀ = C * P.root' b y₀ + P.root' b D.positiveVector := by simp [z₀]
    have hlt0 : P.root' b z₀ < 0 := by linarith [le_abs_self (P.root' b D.positiveVector)]
    exact hlt0.ne
  · simp [z₀, hzero, D.positiveVector_regular b]
  · exact (hpos b hgt).ne'

omit [Module ℝ M] [Module ℝ N] [Finite ι] [P.IsCrystallographic] in
private theorem le_normalizer_iSup_of_commutator_le {K : Subgroup G} {ι' : Type*}
    {L : ι' → Subgroup G} (h : ∀ b, ⁅K, L b⁆ ≤ ⨆ c, L c) :
    K ≤ Subgroup.normalizer ((⨆ c, L c : Subgroup G) : Set G) := by
  have hconj : ∀ {k : G}, k ∈ K → ∀ {g : G}, g ∈ ⨆ c, L c → k * g * k⁻¹ ∈ ⨆ c, L c := by
    intro k hk g hg
    refine Subgroup.iSup_induction L (C := fun g ↦ k * g * k⁻¹ ∈ ⨆ c, L c) hg
      (fun b x hx ↦ ?_) ?_ fun x y ihx ihy ↦ ?_
    · have hc : ⁅k, x⁆ ∈ ⨆ c, L c := h b (Subgroup.commutator_mem_commutator hk hx)
      have heq : k * x * k⁻¹ = ⁅k, x⁆ * x := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact mul_mem hc (Subgroup.mem_iSup_of_mem b hx)
    · have heq : k * 1 * k⁻¹ = 1 := by group
      rw [heq]
      exact one_mem _
    · have heq : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      rw [heq]
      exact mul_mem ihx ihy
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  refine fun g ↦ ⟨hconj hk, fun hg ↦ ?_⟩
  have h1 := hconj (inv_mem hk) hg
  have heq : k⁻¹ * (k * g * k⁻¹) * (k⁻¹)⁻¹ = g := by group
  rwa [heq] at h1

omit [Finite ι] [P.IsCrystallographic] in
private theorem ne_one_right_of_mul_mul_mem_reflectionCoset {i : ι} {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)}
    (h : (u' : G) * u * u'' ∈ D.reflectionCoset i) : u'' ≠ 1 := by
  rintro rfl
  have hm : (u' : G) * u ∈ D.reflectionCoset i := by simpa using h
  have h1 := D.reflection_conjugates i ((u' : G) * u) hm i
  rw [ConjAct.toConjAct_mul, mul_smul,
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer u.2)] at h1
  have h2 : D.U i = D.U (P.reflectionPerm i i) := by
    rw [← inv_smul_eq_iff.mpr h1.symm, ← ConjAct.toConjAct_inv,
      Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer (inv_mem u'.2))]
  exact D.U_ne_of_root_eq_neg (by simp) h2.symm

omit [Finite ι] [P.IsCrystallographic] in
private theorem inv_mul_mul_mem_U_reflectionCoset {i j : ι} {m : G}
    (hm : m ∈ D.reflectionCoset i) {x : G} (hx : x ∈ D.U j) :
    m⁻¹ * x * m ∈ D.U (P.reflectionPerm i j) := by
  rw [← Subgroup.mem_conjAct_smul_iff, D.reflection_conjugates i m hm, P.reflectionPerm_self]
  exact hx

private theorem smul_reflection_apply_raw {i : ι} {m : G} (hm : m ∈ D.reflectionCoset i)
    (j : ι) (x : D.U j) :
    ((⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ) j x =
      φ (P.reflectionPerm i j)
        ⟨m⁻¹ * x * m, inv_mul_mul_mem_U_reflectionCoset hm x.2⟩ := by
  rw [smul_apply]
  have hidx : P.weylGroupToPerm
      (D.weylGroupHom ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩)⁻¹ j =
      P.reflectionPerm i j := by
    rw [D.weylGroupHom_reflection hm, RootPairing.weylGroup.ofIdx_inv_eq,
      P.weylGroupToPerm_ofIdx_apply]
  exact φ.apply_congr hidx rfl

private theorem smul_reflection_apply_self_aux {i : ι} {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)} {m : G} (hm : m ∈ D.reflectionCoset i)
    (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) (x : D.U i) :
    ((⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ) i x =
      φ i x + ((-(2 * k) : ℝ) : WithTop ℝ) := by
  by_cases hx : x = 1
  · simp [hx]
  have hni_i : P.reflectionPerm (P.reflectionPerm i i) (P.reflectionPerm i i) = i :=
    P.reflectionPerm_reflectionPerm_self i
  have hm_prod : (u' : G) * u * u'' ∈ D.reflectionCoset i := by rwa [hm_eq]
  have hu''_ne : u'' ≠ 1 := ne_one_right_of_mul_mul_mem_reflectionCoset hm_prod
  have hφ_u' : φ (P.reflectionPerm i i) u' = -(k : WithTop ℝ) := by
    rw [φ.apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset i u u' u'' hm_prod, hφ]
  have hφ_u'' : φ (P.reflectionPerm i i) u'' = -(k : WithTop ℝ) := by
    rw [φ.apply_reflectionPerm_right_eq_neg_of_mul_mul_mem_reflectionCoset u u' u'' hm_prod, hφ]
  have hw_mem : m * (u'' : G) * m⁻¹ ∈
      D.U (P.reflectionPerm (P.reflectionPerm i i) (P.reflectionPerm i i)) :=
    hni_i.symm ▸ D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm u''.2
  have hu_ni : (u : G) ∈ D.U (P.reflectionPerm (P.reflectionPerm i i) (P.reflectionPerm i i)) :=
    hni_i.symm ▸ u.2
  have hw_prod : (m * (u'' : G) * m⁻¹) * (u' : G) * (u : G) ∈
      D.reflectionCoset (P.reflectionPerm i i) := by
    have heq : (m * (u'' : G) * m⁻¹) * (u' : G) * (u : G) = m := by
      rw [← hm_eq]
      group
    rw [heq, D.reflectionCoset_reflectionPerm_self]
    exact hm
  have hφ_conj : φ i ⟨m * u'' * m⁻¹, D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm u''.2⟩ =
      (k : WithTop ℝ) := by
    rw [← φ.apply_congr hni_i (u := ⟨m * u'' * m⁻¹, hw_mem⟩) rfl,
      φ.apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset (P.reflectionPerm i i) u'
        ⟨_, hw_mem⟩ ⟨u, hu_ni⟩ hw_prod, hφ_u', neg_neg]
  obtain ⟨c, hc⟩ := φ.exists_apply_eq_apply_conj_add i m hm
  have hc_eq : c = -(2 * k) := by
    have h1 := hc u'' hu''_ne
    rw [hφ_u'', hφ_conj] at h1
    norm_cast at h1
    linarith
  let y : D.U (P.reflectionPerm i i) := ⟨m⁻¹ * x * m, inv_mul_mul_mem_U_reflectionCoset hm x.2⟩
  have hy_ne : y ≠ 1 := fun h ↦ hx <| Subtype.ext <| by
    have h0 : m⁻¹ * (x : G) * m = 1 := congrArg Subtype.val h
    calc (x : G) = m * (m⁻¹ * x * m) * m⁻¹ := by group
      _ = 1 := by rw [h0]; group
  rw [φ.smul_reflection_apply_raw hm i x, hc y hy_ne, hc_eq]
  exact congrArg (· + ((-(2 * k) : ℝ) : WithTop ℝ)) (φ.apply_congr rfl (by dsimp only [y]; group))

private theorem smul_reflection_apply_neg_aux {i : ι} {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)} {m : G} (hm : m ∈ D.reflectionCoset i)
    (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) (x : D.U (P.reflectionPerm i i)) :
    ((⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ)
        (P.reflectionPerm i i) x = φ (P.reflectionPerm i i) x + ((2 * k : ℝ) : WithTop ℝ) := by
  have hm_inv : m⁻¹ ∈ D.reflectionCoset i := D.inv_mem_reflectionCoset hm
  have hm_inv_eq : ((u''⁻¹ : D.U _) : G) * (u⁻¹ : D.U i) * (u'⁻¹ : D.U _) = m⁻¹ := by
    simp only [Subgroup.coe_inv]
    rw [← hm_eq]
    group
  have hφ_inv : φ i u⁻¹ = k := (φ.apply_inv u).trans hφ
  let y : D.U i := ⟨m⁻¹ * x * m, by
    have h := inv_mul_mul_mem_U_reflectionCoset hm x.2
    rwa [P.reflectionPerm_self] at h⟩
  have hself := φ.smul_reflection_apply_self_aux hm_inv hm_inv_eq hφ_inv y
  rw [φ.smul_reflection_apply_raw hm_inv i y,
    φ.apply_congr rfl (v := x) (by dsimp only [y]; group)] at hself
  rw [φ.smul_reflection_apply_raw hm (P.reflectionPerm i i) x,
    φ.apply_congr (P.reflectionPerm_self i i) (v := y) rfl, hself]
  generalize φ i y = val
  cases val with
  | top => simp
  | coe r => norm_cast; ring

omit [Finite ι] [P.IsCrystallographic] in
private def reflCone (P : RootPairing ι ℝ M N) (i j : ι) (y₀ y₁ : N) (b : ι) : Prop :=
  0 < P.root' b y₀ ∧ P.root b = P.root' b y₀ • P.root j + P.root' b y₁ • P.root i

omit [Finite ι] [P.IsCrystallographic] in
private noncomputable def reflConeSubgroup (φ : Valuation D) (i j : ι) (y₀ y₁ : N) (k l : ℝ)
    (b : ι) : Subgroup G :=
  open Classical in
  if reflCone P i j y₀ y₁ b then φ.filtration b (P.root' b y₀ * l + P.root' b y₁ * k) else ⊥

omit [Finite ι] [P.IsCrystallographic] in
private theorem reflConeSubgroup_pos {i j : ι} {y₀ y₁ : N} {k l : ℝ} {b : ι}
    (hb : reflCone P i j y₀ y₁ b) :
    φ.reflConeSubgroup i j y₀ y₁ k l b = φ.filtration b (P.root' b y₀ * l + P.root' b y₁ * k) := by
  simp [reflConeSubgroup, hb]

omit [Finite ι] [P.IsCrystallographic] in
private theorem reflConeSubgroup_neg {i j : ι} {y₀ y₁ : N} {k l : ℝ} {b : ι}
    (hb : ¬reflCone P i j y₀ y₁ b) :
    φ.reflConeSubgroup i j y₀ y₁ k l b = ⊥ := by
  simp [reflConeSubgroup, hb]

omit [Finite ι] [P.IsCrystallographic] in
private theorem reflCone_of_root_eq {i j : ι} {y₀ y₁ : N}
    (hy₀i : P.root' i y₀ = 0) (hy₀j : P.root' j y₀ = 1)
    (hy₁j : P.root' j y₁ = 0) (hy₁i : P.root' i y₁ = 1)
    {b : ι} {c d : ℝ} (hc : 0 < c) (hb : P.root b = c • P.root j + d • P.root i) :
    P.root' b y₀ = c ∧ P.root' b y₁ = d ∧ reflCone P i j y₀ y₁ b := by
  have hc_eq : P.root' b y₀ = c := by simp [RootPairing.root', hb, hy₀i, hy₀j]
  have hd_eq : P.root' b y₁ = d := by simp [RootPairing.root', hb, hy₁i, hy₁j]
  exact ⟨hc_eq, hd_eq, hc_eq ▸ hc, by rwa [hc_eq, hd_eq]⟩

omit [Finite ι] [P.IsCrystallographic] in
private theorem reflConeSubgroup_le_of_two_smul (i j : ι) (y₀ y₁ : N) (k l : ℝ) {b₁ b₂ : ι}
    (h2 : P.root b₂ = (2 : ℝ) • P.root b₁) :
    φ.reflConeSubgroup i j y₀ y₁ k l b₂ ≤ φ.reflConeSubgroup i j y₀ y₁ k l b₁ := by
  classical
  dsimp only [reflConeSubgroup]
  split_ifs with hb₂ hb₁
  · intro g hg_mem
    rw [φ.mem_filtration_iff] at hg_mem ⊢
    obtain ⟨hg, hval⟩ := hg_mem
    have hg₁ : g ∈ D.U b₁ := D.le_of_root_eq_two_smul b₁ b₂ h2 hg
    refine ⟨hg₁, ?_⟩
    have h0 : P.root' b₂ y₀ = 2 * P.root' b₁ y₀ := by simp [RootPairing.root', h2]
    have h1 : P.root' b₂ y₁ = 2 * P.root' b₁ y₁ := by simp [RootPairing.root', h2]
    rw [φ.apply_eq_two_smul b₁ b₂ h2 ⟨g, hg⟩, h0, h1] at hval
    generalize φ b₁ ⟨g, hg₁⟩ = val at hval ⊢
    cases val with
    | top => exact le_top
    | coe r =>
      rw [two_nsmul, ← WithTop.coe_add] at hval
      norm_cast at hval ⊢
      linarith
  · exfalso
    apply hb₁
    have h0 : P.root' b₂ y₀ = 2 * P.root' b₁ y₀ := by simp [RootPairing.root', h2]
    have h1 : P.root' b₂ y₁ = 2 * P.root' b₁ y₁ := by simp [RootPairing.root', h2]
    have hb₁_eq : P.root b₁ = P.root' b₁ y₀ • P.root j + P.root' b₁ y₁ • P.root i := by
      have hsm := congrArg ((2⁻¹ : ℝ) • ·) hb₂.2
      rw [h2, h0, h1] at hsm
      simpa [smul_add, smul_smul] using hsm
    exact ⟨by linarith [hb₂.1], hb₁_eq⟩
  · exact bot_le
  · exact bot_le

omit [Finite ι] [P.IsCrystallographic] in
private theorem commutator_reflConeSubgroup_le {i j : ι} {y₀ y₁ z₀ : N}
    (hy₀i : P.root' i y₀ = 0) (hy₀j : P.root' j y₀ = 1)
    (hy₁j : P.root' j y₁ = 0) (hy₁i : P.root' i y₁ = 1) (k l : ℝ) {b₁ b₂ : ι}
    (hb₁z : 0 < P.root' b₁ z₀) (hb₂z : 0 < P.root' b₂ z₀) :
    ⁅φ.reflConeSubgroup i j y₀ y₁ k l b₁, φ.reflConeSubgroup i j y₀ y₁ k l b₂⁆ ≤
      ⨆ (n) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root n = p • P.root b₁ + q • P.root b₂),
        φ.reflConeSubgroup i j y₀ y₁ k l n := by
  by_cases hb₁ : reflCone P i j y₀ y₁ b₁
  · by_cases hb₂ : reflCone P i j y₀ y₁ b₂
    · have hnot_neg : ∀ c : ℝ, 0 < c → P.root b₂ ≠ -(c • P.root b₁) := fun c hc hneg ↦ by
        have : P.root' b₂ z₀ = -c * P.root' b₁ z₀ := by simp [RootPairing.root', hneg]
        nlinarith
      rw [φ.reflConeSubgroup_pos hb₁, φ.reflConeSubgroup_pos hb₂]
      refine (φ.commutator_filtration_le hnot_neg _ _).trans
        (iSup_le fun n ↦ iSup_le fun p ↦ iSup_le fun q ↦ iSup_le fun ⟨hp, hq, hn_eq⟩ ↦ ?_)
      have hn_lin : P.root n =
          ((p : ℝ) * P.root' b₁ y₀ + (q : ℝ) * P.root' b₂ y₀) • P.root j +
            ((p : ℝ) * P.root' b₁ y₁ + (q : ℝ) * P.root' b₂ y₁) • P.root i := by
        rw [hn_eq, hb₁.2, hb₂.2, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
        module
      have hc_pos : 0 < (p : ℝ) * P.root' b₁ y₀ + (q : ℝ) * P.root' b₂ y₀ := by
        have := hb₁.1
        have := hb₂.1
        positivity
      obtain ⟨hn₀, hn₁, hnc⟩ := reflCone_of_root_eq hy₀i hy₀j hy₁j hy₁i hc_pos hn_lin
      have hLn : φ.reflConeSubgroup i j y₀ y₁ k l n = φ.filtration n
          (p * (P.root' b₁ y₀ * l + P.root' b₁ y₁ * k) +
            q * (P.root' b₂ y₀ * l + P.root' b₂ y₁ * k)) := by
        rw [φ.reflConeSubgroup_pos hnc, hn₀, hn₁]
        congr 1
        ring
      exact hLn ▸ le_iSup₂ (f := fun (n : ι) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
        P.root n = p • P.root b₁ + q • P.root b₂) ↦ φ.reflConeSubgroup i j y₀ y₁ k l n)
        n ⟨p, q, hp, hq, hn_eq⟩
    · simp [φ.reflConeSubgroup_neg hb₂]
  · simp [φ.reflConeSubgroup_neg hb₁]

omit [Finite ι] [P.IsCrystallographic] in
private theorem filtration_le_normalizer_iSup_reflConeSubgroup {i j : ι} {y₀ y₁ : N}
    (hy₀i : P.root' i y₀ = 0) (hy₀j : P.root' j y₀ = 1)
    (hy₁j : P.root' j y₁ = 0) (hy₁i : P.root' i y₁ = 1) (k l : ℝ) {s : ι}
    (hs₀ : P.root' s y₀ = 0) (hs_eq : P.root s = P.root' s y₁ • P.root i) :
    φ.filtration s (P.root' s y₁ * k) ≤
      Subgroup.normalizer ((⨆ c, φ.reflConeSubgroup i j y₀ y₁ k l c : Subgroup G) : Set G) := by
  refine le_normalizer_iSup_of_commutator_le fun b ↦ ?_
  by_cases hb : reflCone P i j y₀ y₁ b
  · have hnot_neg : ∀ c : ℝ, 0 < c → P.root b ≠ -(c • P.root s) := fun c _ hneg ↦ by
      have : P.root' b y₀ = -c * P.root' s y₀ := by simp [RootPairing.root', hneg]
      rw [hs₀, mul_zero] at this
      linarith [hb.1]
    rw [φ.reflConeSubgroup_pos hb]
    refine (φ.commutator_filtration_le hnot_neg _ _).trans
      (iSup_le fun n ↦ iSup_le fun p ↦ iSup_le fun q ↦ iSup_le fun ⟨_hp, hq, hn_eq⟩ ↦ ?_)
    have hn_lin : P.root n = ((q : ℝ) * P.root' b y₀) • P.root j +
        ((p : ℝ) * P.root' s y₁ + (q : ℝ) * P.root' b y₁) • P.root i := by
      rw [hn_eq, hs_eq, hb.2, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
      module
    have hc_pos : 0 < (q : ℝ) * P.root' b y₀ := mul_pos (Nat.cast_pos.mpr hq) hb.1
    obtain ⟨hn₀, hn₁, hnc⟩ := reflCone_of_root_eq hy₀i hy₀j hy₁j hy₁i hc_pos hn_lin
    have hLn : φ.reflConeSubgroup i j y₀ y₁ k l n = φ.filtration n
        (p * (P.root' s y₁ * k) + q * (P.root' b y₀ * l + P.root' b y₁ * k)) := by
      rw [φ.reflConeSubgroup_pos hnc, hn₀, hn₁]
      congr 1
      ring
    exact hLn ▸ le_iSup (φ.reflConeSubgroup i j y₀ y₁ k l) n
  · simp [φ.reflConeSubgroup_neg hb]

omit [Finite ι] [P.IsCrystallographic] in
private theorem inv_mem_normalizer_iSup_reflConeSubgroup {i j : ι} {y₀ y₁ : N}
    (hy₀i : P.root' i y₀ = 0) (hy₀j : P.root' j y₀ = 1)
    (hy₁j : P.root' j y₁ = 0) (hy₁i : P.root' i y₁ = 1)
    {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)} {m : G}
    (hm : m ∈ D.reflectionCoset i) (hm_eq : (u' : G) * u * u'' = m) {k : ℝ}
    (hφu : φ i u = k) (l : ℝ) :
    m⁻¹ ∈ Subgroup.normalizer
      ((⨆ c, φ.reflConeSubgroup i j y₀ y₁ k l c : Subgroup G) : Set G) := by
  let L := φ.reflConeSubgroup i j y₀ y₁ k l
  have hm_prod : (u' : G) * u * u'' ∈ D.reflectionCoset i := by rwa [hm_eq]
  have hu_norm : ((u⁻¹ : D.U i) : G) ∈ Subgroup.normalizer ((⨆ c, L c : Subgroup G) : Set G) :=
    φ.filtration_le_normalizer_iSup_reflConeSubgroup hy₀i hy₀j hy₁j hy₁i k l hy₀i (by simp [hy₁i])
      (by rw [φ.coe_mem_filtration_iff u⁻¹, φ.apply_inv, hy₁i, one_mul, hφu])
  let ni := P.reflectionPerm i i
  have hni₀ : P.root' ni y₀ = 0 := by simp [ni, hy₀i]
  have hni₁ : P.root' ni y₁ = -1 := by simp [ni, hy₁i]
  have hni_root : P.root ni = P.root' ni y₁ • P.root i := by rw [hni₁, neg_one_smul]; simp [ni]
  have hu'_norm : ((u'⁻¹ : D.U ni) : G) ∈ Subgroup.normalizer ((⨆ c, L c : Subgroup G) : Set G) :=
    φ.filtration_le_normalizer_iSup_reflConeSubgroup hy₀i hy₀j hy₁j hy₁i k l hni₀ hni_root
      (by rw [φ.coe_mem_filtration_iff, φ.apply_inv,
        φ.apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset i u u' u'' hm_prod,
        hφu, hni₁, neg_one_mul, WithTop.LinearOrderedAddCommGroup.coe_neg])
  have hu''_norm : ((u''⁻¹ : D.U ni) : G) ∈ Subgroup.normalizer ((⨆ c, L c : Subgroup G) : Set G) :=
    φ.filtration_le_normalizer_iSup_reflConeSubgroup hy₀i hy₀j hy₁j hy₁i k l hni₀ hni_root
      (by rw [φ.coe_mem_filtration_iff, φ.apply_inv,
        φ.apply_reflectionPerm_right_eq_neg_of_mul_mul_mem_reflectionCoset u u' u'' hm_prod,
        hφu, hni₁, neg_one_mul, WithTop.LinearOrderedAddCommGroup.coe_neg])
  have heq : m⁻¹ = ((u''⁻¹ : D.U ni) : G) * ((u⁻¹ : D.U i) : G) * ((u'⁻¹ : D.U ni) : G) := by
    simp only [Subgroup.coe_inv]; rw [← hm_eq]; group
  exact heq ▸ mul_mem (mul_mem hu''_norm hu_norm) hu'_norm

private theorem le_smul_reflection_of_linearIndependent {i j : ι}
    (hj : P.IsIndivisible j) (hli : LinearIndependent ℝ ![P.root i, P.root j])
    {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)} {m : G}
    (hm : m ∈ D.reflectionCoset i) (hm_eq : (u' : G) * u * u'' = m) {k l : ℝ}
    (hφu : φ i u = k) {x : D.U j} (hφx : (l : WithTop ℝ) ≤ φ j x) :
    ((l - P.pairing j i * k : ℝ) : WithTop ℝ) ≤
      ((⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ) j x := by
  have hli_swap : LinearIndependent ℝ ![P.root j, P.root i] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    exact fun c d hcd ↦ (hli d c (by rw [add_comm]; exact hcd)).symm
  obtain ⟨y₀, hy₀i, hy₀j⟩ := exists_root'_eq_zero_and_eq_one hli
  obtain ⟨y₁, hy₁j, hy₁i⟩ := exists_root'_eq_zero_and_eq_one hli_swap
  obtain ⟨z₀, hz₀, hz₀_pos⟩ := exists_regular_preserve_pos D y₀
  let L := φ.reflConeSubgroup i j y₀ y₁ k l
  have hLU : ∀ b, 0 < P.root' b z₀ → L b ≤ D.U b := fun b _ ↦ by
    by_cases hb : reflCone P i j y₀ y₁ b
    · rw [show L b = _ from φ.reflConeSubgroup_pos hb]; exact φ.filtration_le_U b _
    · simp [L, φ.reflConeSubgroup_neg hb]
  have hiSup_eq : (⨆ (b) (_ : 0 < P.root' b z₀), L b) = ⨆ b, L b :=
    le_antisymm (iSup₂_le fun b _ ↦ le_iSup L b) <| iSup_le fun b ↦ by
      by_cases hb : reflCone P i j y₀ y₁ b
      · exact le_iSup₂_of_le b (hz₀_pos b hb.1) le_rfl
      · simp [L, φ.reflConeSubgroup_neg hb]
  have hminv_norm := φ.inv_mem_normalizer_iSup_reflConeSubgroup
    hy₀i hy₀j hy₁j hy₁i hm hm_eq hφu l
  obtain ⟨hj₀, hj₁, hjc⟩ := reflCone_of_root_eq hy₀i hy₀j hy₁j hy₁i (b := j) (c := 1) (d := 0)
    one_pos (by simp)
  have hx_mem : (x : G) ∈ ⨆ c, L c := Subgroup.mem_iSup_of_mem j <| by
    rw [show L j = _ from φ.reflConeSubgroup_pos hjc, hj₀, hj₁, one_mul, zero_mul, add_zero]
    exact (φ.coe_mem_filtration_iff x).mpr hφx
  set j' := P.reflectionPerm i j
  have hj'_lin : P.root j' = (1 : ℝ) • P.root j + (-P.pairing j i) • P.root i := by
    rw [P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing, one_smul, neg_smul,
      sub_eq_add_neg]
  obtain ⟨hj'₀, hj'₁, hj'c⟩ := reflCone_of_root_eq hy₀i hy₀j hy₁j hy₁i one_pos hj'_lin
  have hconj_mem : m⁻¹ * (x : G) * m ∈ (⨆ (b) (_ : 0 < P.root' b z₀), L b) ⊓ D.U j' := by
    rw [hiSup_eq]
    exact ⟨by simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hminv_norm x).mp hx_mem,
      inv_mul_mul_mem_U_reflectionCoset hm x.2⟩
  rw [D.iSup_inf_U_eq_of_commutator_le hz₀ L hLU
    (fun b₁ b₂ _ h2 ↦ φ.reflConeSubgroup_le_of_two_smul i j y₀ y₁ k l h2)
    (fun b₁ b₂ ↦ φ.commutator_reflConeSubgroup_le hy₀i hy₀j hy₁j hy₁i k l)
    (hj.reflectionPerm i) (hz₀_pos j' hj'c.1),
    show L j' = _ from φ.reflConeSubgroup_pos hj'c, hj'₀, hj'₁, one_mul, neg_mul,
    ← sub_eq_add_neg] at hconj_mem
  rw [φ.smul_reflection_apply_raw hm j x]
  exact (φ.coe_mem_filtration_iff ⟨m⁻¹ * x * m, _⟩).mp hconj_mem

omit [Finite ι] [P.IsCrystallographic] in
private theorem linearIndependent_reflectionPerm_of_linearIndependent {i j : ι}
    (hli : LinearIndependent ℝ ![P.root i, P.root j]) :
    LinearIndependent ℝ ![P.root i, P.root (P.reflectionPerm i j)] := by
  rw [LinearIndependent.pair_iff] at hli ⊢
  intro c d hcd
  have h1 : (c - d * P.pairing j i) • P.root i + d • P.root j = 0 := by
    have hr : P.root (P.reflectionPerm i j) = P.root j - P.pairing j i • P.root i := by
      rw [P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing]
    rw [hr] at hcd
    calc (c - d * P.pairing j i) • P.root i + d • P.root j
        = c • P.root i + d • (P.root j - P.pairing j i • P.root i) := by module
      _ = 0 := hcd
  obtain ⟨h2, hd0⟩ := hli _ _ h1
  exact ⟨by linarith [hd0 ▸ h2], hd0⟩

private theorem smul_reflection_of_not_linearIndependent {i j : ι}
    (hi : P.IsIndivisible i) (hj : P.IsIndivisible j)
    (hli : ¬LinearIndependent ℝ ![P.root i, P.root j])
    {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)} {m : G} (hm : m ∈ D.reflectionCoset i)
    (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) (x : D.U j) :
    ((⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ) j x =
      (φ.shift (-(k • P.coroot i))) j x := by
  rcases P.not_linearIndependent_root_iff.mp hli with rfl | hneg | h2 | h2 | hneg2 | hneg2
  · rw [φ.smul_reflection_apply_self_aux hm hm_eq hφ x, shift_apply]
    have hp : P.root' i (-(k • P.coroot i)) = -(2 * k) := by simp [mul_comm]
    rw [hp]
  · have hj_eq : j = P.reflectionPerm i i := P.root.injective <| by
      rw [P.root_reflectionPerm, P.reflection_apply_self, ← neg_eq_iff_eq_neg.mpr hneg]
    subst hj_eq
    rw [φ.smul_reflection_apply_neg_aux hm hm_eq hφ x, shift_apply]
    have hp : P.root' (P.reflectionPerm i i) (-(k • P.coroot i)) = 2 * k := by simp [mul_comm]
    rw [hp]
  · exact absurd h2 (P.isIndivisible_iff.mp hj i)
  · exact absurd h2 (P.isIndivisible_iff.mp hi j)
  · refine absurd (show P.root j = (2 : ℝ) • P.root (P.reflectionPerm i i) by
      simpa [neg_smul] using hneg2) (P.isIndivisible_iff.mp hj _)
  · refine absurd (show P.root i = (2 : ℝ) • P.root (P.reflectionPerm j j) by
      simpa [neg_smul] using hneg2) (P.isIndivisible_iff.mp hi _)

private theorem smul_reflection_of_isIndivisible {i : ι} (hi : P.IsIndivisible i) {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)} {m : G} (hm : m ∈ D.reflectionCoset i)
    (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) :
    (⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ =
      φ.shift (-(k • P.coroot i)) := by
  refine ext_of_isIndivisible fun j hj x ↦ ?_
  by_cases hli : LinearIndependent ℝ ![P.root i, P.root j]
  · by_cases hx : x = 1
    · simp [hx]
    obtain ⟨l, hl⟩ := φ.exists_apply_eq_coe hx
    have hle₁ := φ.le_smul_reflection_of_linearIndependent hj hli hm hm_eq hφ hl.ge
    set j' := P.reflectionPerm i j
    let x' : D.U j' := ⟨m⁻¹ * x * m, inv_mul_mul_mem_U_reflectionCoset hm x.2⟩
    have hx'_ne : x' ≠ 1 := fun h ↦ hx <| Subtype.ext <| by
      have h0 : m⁻¹ * (x : G) * m = 1 := congrArg Subtype.val h
      calc (x : G) = m * (m⁻¹ * x * m) * m⁻¹ := by group
        _ = 1 := by rw [h0]; group
    obtain ⟨l', hl'⟩ := φ.exists_apply_eq_coe hx'_ne
    have hsmul_eq : ((⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ) j
        x = (l' : WithTop ℝ) := (φ.smul_reflection_apply_raw hm j x).trans hl'
    have hm_inv : m⁻¹ ∈ D.reflectionCoset i := D.inv_mem_reflectionCoset hm
    have hm_inv_eq : ((u''⁻¹ : D.U _) : G) * (u⁻¹ : D.U i) * (u'⁻¹ : D.U _) = m⁻¹ := by
      simp only [Subgroup.coe_inv]
      rw [← hm_eq]
      group
    have hle₂ := φ.le_smul_reflection_of_linearIndependent (hj.reflectionPerm i)
      (linearIndependent_reflectionPerm_of_linearIndependent hli)
      hm_inv hm_inv_eq ((φ.apply_inv u).trans hφ) hl'.ge
    rw [φ.smul_reflection_apply_raw hm_inv j' x',
      φ.apply_congr (P.reflectionPerm_self i j) (v := x) (by dsimp only [x']; group), hl] at hle₂
    have hpair_j' : P.pairing j' i = -P.pairing j i := by
      rw [← P.root_coroot'_eq_pairing, P.root_reflectionPerm, P.coroot'_reflection_self,
        P.root_coroot'_eq_pairing]
    rw [hpair_j'] at hle₂
    rw [hsmul_eq] at hle₁ ⊢
    rw [shift_apply, hl, show P.root' j (-(k • P.coroot i)) = -(P.pairing j i * k) by
      simp [mul_comm]]
    norm_cast at hle₁ hle₂ ⊢
    linarith
  · exact φ.smul_reflection_of_not_linearIndependent hi hj hli hm hm_eq hφ x

/-- **Bruhat–Tits reflection formula** (Bruhat–Tits I, Proposition 6.2.7, p. 121): if
`m = u' u u'' ∈ M a` with `u ∈ U a`, `u', u'' ∈ U (-a)` and `φ a u = k`, then
`m • φ = φ.shift (-(k • P.coroot i))`. -/
theorem smul_reflection {i : ι} {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)} {m : G}
    (hm : m ∈ D.reflectionCoset i) (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) :
    (⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ =
      φ.shift (-(k • P.coroot i)) := by
  rcases P.isIndivisible_or_exists_root_eq_two_smul i with hi | ⟨i₀, hi₀, hi_eq⟩
  · exact φ.smul_reflection_of_isIndivisible hi hm hm_eq hφ
  · have hm₀ : m ∈ D.reflectionCoset i₀ :=
      D.reflectionCoset_eq_of_root_eq_two_smul hi_eq ▸ hm
    have hneg_eq : P.root (P.reflectionPerm i i) =
        (2 : ℝ) • P.root (P.reflectionPerm i₀ i₀) := by
      rw [P.root_reflectionPerm, P.reflection_apply_self, P.root_reflectionPerm,
        P.reflection_apply_self, hi_eq, smul_neg]
    let u₀ : D.U i₀ := ⟨u, D.le_of_root_eq_two_smul i₀ i hi_eq u.2⟩
    let u₀' : D.U (P.reflectionPerm i₀ i₀) :=
      ⟨u', D.le_of_root_eq_two_smul _ _ hneg_eq u'.2⟩
    let u₀'' : D.U (P.reflectionPerm i₀ i₀) :=
      ⟨u'', D.le_of_root_eq_two_smul _ _ hneg_eq u''.2⟩
    have hφ₀ : φ i₀ u₀ = ((k / 2 : ℝ) : WithTop ℝ) := by
      have h2 := φ.apply_eq_two_smul i₀ i hi_eq u
      rw [hφ] at h2
      generalize φ i₀ u₀ = val at h2 ⊢
      cases val with
      | top =>
        rw [two_nsmul, WithTop.top_add] at h2
        exact absurd h2 WithTop.coe_ne_top
      | coe r =>
        rw [two_nsmul, ← WithTop.coe_add] at h2
        norm_cast at h2 ⊢
        linarith
    have hres := φ.smul_reflection_of_isIndivisible hi₀ (u := u₀) (u' := u₀') (u'' := u₀'')
      hm₀ hm_eq hφ₀
    have hcor : (k / 2 : ℝ) • P.coroot i₀ = k • P.coroot i := by
      have : HasUniqueDiv M := .of_isTorsionFree ℝ M
      have : HasUniqueDiv N := .of_isTorsionFree ℝ N
      rw [P.coroot_eq_smul_coroot_iff.mpr hi_eq, smul_smul]
      ring_nf
    rwa [hcor] at hres

/-- On `D.U i` itself, `m = u' u u'' ∈ M a` with `φ a u = k` lowers every value by `2 k`. -/
theorem smul_reflection_apply_self {i : ι} {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)}
    {m : G} (hm : m ∈ D.reflectionCoset i) (hm_eq : (u' : G) * u * u'' = m) {k : ℝ}
    (hφ : φ i u = k) (x : D.U i) :
    ((⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ) i x =
      φ i x - ((2 * k : ℝ) : WithTop ℝ) := by
  rw [φ.smul_reflection hm hm_eq hφ, shift_apply]
  have hp : P.root' i (-(k • P.coroot i)) = -(2 * k) := by simp [mul_comm]
  rw [hp, WithTop.LinearOrderedAddCommGroup.coe_neg, sub_eq_add_neg]

omit [Finite ι] [P.IsCrystallographic] in
private theorem coweightEquiv_symm_mem_corootSpan (e : P.Aut) {v : N}
    (hv : v ∈ P.corootSpan ℝ) : e.coweightEquiv.symm v ∈ P.corootSpan ℝ := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have hcor : e.coweightEquiv.symm (P.coroot j) = P.coroot (e.indexEquiv j) :=
      (LinearEquiv.symm_apply_eq e.coweightEquiv).mpr
        (by simp [RootPairing.Hom.coroot_coweightMap_apply])
    rw [hcor]
    exact (P.corootSpanMem ℝ _).2
  | zero => simp
  | add x y _ _ ihx ihy => exact map_add e.coweightEquiv.symm x y ▸ add_mem ihx ihy
  | smul c x _ ih => exact map_smul e.coweightEquiv.symm c x ▸ Submodule.smul_mem _ c ih

omit [Finite ι] [P.IsCrystallographic] in
private theorem exists_mul_mul_mem_reflectionCoset_and_apply_eq (i : ι) :
    ∃ (k : ℝ) (u : D.U i) (u' u'' : D.U (P.reflectionPerm i i)) (m : G),
      m ∈ D.reflectionCoset i ∧ (u' : G) * u * u'' = m ∧ φ i u = k := by
  obtain ⟨k, hk⟩ := (φ.valueSet_nontrivial i).nonempty
  obtain ⟨u, hu⟩ := φ.mem_valueSet_iff.mp hk
  have hu1 : (u : G) ≠ 1 := fun h ↦ by
    have hu' : u = 1 := Subtype.ext h
    simp [hu'] at hu
  set ni := P.reflectionPerm i i
  have hmem : (u : G) ∈ (D.U (P.reflectionPerm ni ni) : Set G) \ {1} :=
    ⟨by rw [P.reflectionPerm_reflectionPerm_self]; exact u.2, hu1⟩
  obtain ⟨_, ⟨x, hx, m, hm, rfl⟩, y, hy, hxy⟩ := D.bruhat ni hmem
  dsimp only at hxy
  rw [D.reflectionCoset_reflectionPerm_self] at hm
  refine ⟨k, u, ⟨x, hx⟩⁻¹, ⟨y, hy⟩⁻¹, m, hm, ?_, hu⟩
  simp only [Subgroup.coe_inv]
  rw [← hxy]
  group

private theorem exists_torus_smul_add_const {t : G} (ht : t ∈ D.T) :
    ∃ d : ι → ℝ, ∀ (i : ι) (x : D.U i),
      ((⟨t, D.T_le_weylNormalizer ht⟩ : D.weylNormalizer) • φ) i x =
        φ i x + (d i : WithTop ℝ) := by
  let nt : D.weylNormalizer := ⟨t, D.T_le_weylNormalizer ht⟩
  have hconst : ∀ i : ι, ∃ c : ℝ, ∀ x : D.U i, (nt • φ) i x = φ i x + (c : WithTop ℝ) := by
    intro i
    set ni := P.reflectionPerm i i
    have hni_i : P.reflectionPerm ni ni = i := P.reflectionPerm_reflectionPerm_self i
    obtain ⟨m, hm⟩ := D.reflectionCoset_nonempty ni
    have hmt : m * t ∈ D.reflectionCoset ni := by
      have heq : m * t = (m * t * m⁻¹) * m := by group
      exact heq ▸ D.mul_mem_reflectionCoset (D.mul_mul_inv_mem_T hm ht) hm
    obtain ⟨c₁, hc₁⟩ := φ.exists_apply_eq_apply_conj_add ni m hm
    obtain ⟨c₂, hc₂⟩ := φ.exists_apply_eq_apply_conj_add ni (m * t) hmt
    refine ⟨c₂ - c₁, fun x ↦ ?_⟩
    by_cases hx : x = 1
    · simp [hx]
    have hnt_apply : (nt • φ) i x = φ i ⟨t⁻¹ * x * t, D.inv_mul_mul_mem_U ht x.2⟩ := by
      rw [smul_apply]
      exact φ.apply_congr (by rw [D.weylGroupHom_torus ht]; simp) rfl
    let x₀ : D.U (P.reflectionPerm ni ni) := ⟨x, hni_i.symm ▸ x.2⟩
    let x₁ : D.U (P.reflectionPerm ni ni) :=
      ⟨t⁻¹ * x * t, hni_i.symm ▸ D.inv_mul_mul_mem_U ht x.2⟩
    have hx₀ : x₀ ≠ 1 := fun h ↦ hx (Subtype.ext (congrArg Subtype.val h : (x : G) = 1))
    have hx₁ : x₁ ≠ 1 := fun h ↦ hx <| Subtype.ext <| by
      have h0 : t⁻¹ * (x : G) * t = 1 := congrArg Subtype.val h
      calc (x : G) = t * (t⁻¹ * x * t) * t⁻¹ := by group
        _ = 1 := by rw [h0]; group
    have h1 := (φ.apply_congr hni_i (u := x₀) (v := x) rfl).symm.trans (hc₁ x₀ hx₀)
    have h2 := (φ.apply_congr hni_i (u := x₁)
      (v := ⟨t⁻¹ * x * t, D.inv_mul_mul_mem_U ht x.2⟩) rfl).symm.trans (hc₂ x₁ hx₁)
    rw [φ.apply_congr rfl
      (v := ⟨m * x₀ * m⁻¹, D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm x₀.2⟩)
      (by dsimp only [x₀, x₁]; group)] at h2
    rw [hnt_apply, h1, h2]
    generalize φ ni ⟨m * x₀ * m⁻¹, _⟩ = val
    cases val with
    | top => simp
    | coe r => norm_cast; ring
  exact ⟨fun i ↦ (hconst i).choose, fun i ↦ (hconst i).choose_spec⟩

private theorem torus_add_const_reflectionPerm {t : G} (ht : t ∈ D.T) {d : ι → ℝ}
    (hd : ∀ (i : ι) (x : D.U i),
      ((⟨t, D.T_le_weylNormalizer ht⟩ : D.weylNormalizer) • φ) i x = φ i x + (d i : WithTop ℝ))
    (i j : ι) : d (P.reflectionPerm i j) = d j - P.pairing j i * d i := by
  let nt : D.weylNormalizer := ⟨t, D.T_le_weylNormalizer ht⟩
  have hnt_idx : ∀ b : ι, P.weylGroupToPerm (D.weylGroupHom nt)⁻¹ b = b := fun b ↦ by
    rw [D.weylGroupHom_torus ht]; simp
  obtain ⟨k, u, u', u'', m, hm, hm_eq, hu⟩ := φ.exists_mul_mul_mem_reflectionCoset_and_apply_eq i
  let nm : D.weylNormalizer := ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩
  have hm' : t⁻¹ * m * t ∈ D.reflectionCoset i := by
    have heq : t⁻¹ * m * t = (t⁻¹ * (m * t * m⁻¹)) * m := by group
    exact heq ▸ D.mul_mem_reflectionCoset (mul_mem (inv_mem ht) (D.mul_mul_inv_mem_T hm ht)) hm
  let v_u : D.U i := ⟨t⁻¹ * u * t, D.inv_mul_mul_mem_U ht u.2⟩
  let v' : D.U (P.reflectionPerm i i) := ⟨t⁻¹ * u' * t, D.inv_mul_mul_mem_U ht u'.2⟩
  let v'' : D.U (P.reflectionPerm i i) := ⟨t⁻¹ * u'' * t, D.inv_mul_mul_mem_U ht u''.2⟩
  have hm'_eq : (v' : G) * v_u * v'' = t⁻¹ * m * t := by
    dsimp only [v_u, v', v'']; rw [← hm_eq]; group
  have hφ_vu : φ i v_u = ((k + d i : ℝ) : WithTop ℝ) := by
    have hnt_u := hd i u
    rw [smul_apply, φ.apply_congr (hnt_idx i) (v := v_u) rfl, hu] at hnt_u
    exact_mod_cast hnt_u
  let nm' : D.weylNormalizer := ⟨t⁻¹ * m * t, D.reflectionCoset_subset_weylNormalizer i hm'⟩
  have hcomm_n : nm * nt = nt * nm' :=
    Subtype.ext (by simp only [Subgroup.coe_mul, nm, nt, nm']; group)
  obtain ⟨l, hl⟩ := (φ.valueSet_nontrivial j).nonempty
  obtain ⟨z, hz⟩ := φ.mem_valueSet_iff.mp hl
  have heval : ((nm * nt) • φ) j z = ((nt * nm') • φ) j z := by rw [hcomm_n]
  rw [mul_smul, mul_smul] at heval
  have hlhs : (nm • nt • φ) j z =
      ((l - P.pairing j i * k + d (P.reflectionPerm i j) : ℝ) : WithTop ℝ) := by
    rw [(nt • φ).smul_reflection_apply_raw hm j z, hd, ← φ.smul_reflection_apply_raw hm j z,
      φ.smul_reflection hm hm_eq hu, shift_apply, hz,
      show P.root' j (-(k • P.coroot i)) = -(P.pairing j i * k) by simp [mul_comm]]
    norm_cast
  have hrhs : (nt • nm' • φ) j z =
      ((l + d j - P.pairing j i * (k + d i) : ℝ) : WithTop ℝ) := by
    have hnt_z : φ j ⟨t⁻¹ * z * t, D.inv_mul_mul_mem_U ht z.2⟩ = ((l + d j : ℝ) : WithTop ℝ) := by
      have h1 := hd j z
      rw [smul_apply, φ.apply_congr (hnt_idx j)
        (v := ⟨t⁻¹ * z * t, D.inv_mul_mul_mem_U ht z.2⟩) rfl, hz] at h1
      exact_mod_cast h1
    rw [smul_apply, (nm' • φ).apply_congr (hnt_idx j)
      (v := ⟨t⁻¹ * z * t, D.inv_mul_mul_mem_U ht z.2⟩) rfl,
      φ.smul_reflection hm' hm'_eq hφ_vu, shift_apply, hnt_z,
      show P.root' j (-((k + d i) • P.coroot i)) = -(P.pairing j i * (k + d i)) by
        simp [mul_comm]]
    norm_cast
  rw [hlhs, hrhs] at heval
  norm_cast at heval
  linarith

private theorem exists_mem_corootSpan_of_forall_reflectionPerm (D : RootDatum P G) {d : ι → ℝ}
    (hrefl_d : ∀ i j : ι, d (P.reflectionPerm i j) = d j - P.pairing j i * d i) :
    ∃ v ∈ P.corootSpan ℝ, ∀ i : ι, P.IsIndivisible i → P.root' i v = d i := by
  let b₀ := P.indivisibleBaseOf D.positiveVector D.positiveVector_regular
  have hr_coe : (P.indivisiblePairing.root : _ → M) = fun a ↦ P.root a.1 :=
    funext P.indivisiblePairing_root
  have hli_supp : LinearIndependent ℝ (fun a : b₀.support ↦ P.root a.1.1) := by
    simpa [LinearIndepOn, hr_coe] using b₀.linearIndepOn_root
  let B := Module.Basis.span hli_supp
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.constr ℝ (fun a : b₀.support ↦ d a.1.1))
  obtain ⟨⟨v, hv⟩, hv_eq⟩ :=
    (bijective_toDualRootSpan_corootSpan P).2 (g ∘ₗ (P.rootSpan ℝ).subtype)
  have hv_supp : ∀ a : b₀.support, P.root' a.1.1 v = d a.1.1 := fun a ↦ by
    have h1 : P.toDualRootSpan v ⟨P.root a.1.1, (P.rootSpanMem ℝ a.1.1).2⟩ = g (P.root a.1.1) :=
      congr($hv_eq ⟨P.root a.1.1, (P.rootSpanMem ℝ a.1.1).2⟩)
    have h2 : g (P.root a.1.1) = d a.1.1 := by
      have hB : (B a : M) = P.root a.1.1 :=
        congrArg Subtype.val (Module.Basis.span_apply hli_supp a)
      simpa [hB, B.constr_basis] using congr($hg (B a))
    simpa [RootPairing.root'] using h1.trans h2
  refine ⟨v, hv, fun i hi ↦ b₀.induction_reflect ⟨i, hi⟩ (p := fun c ↦ P.root' c.1 v = d c.1)
    ?_ (fun a ha ↦ hv_supp ⟨a, ha⟩) ?_⟩
  · intro a ih
    have hd_neg : d (P.reflectionPerm a.1 a.1) = -d a.1 := by
      have h := hrefl_d a.1 a.1
      rw [P.pairing_same] at h
      linarith
    rw [P.coe_indivisiblePairing_reflectionPerm a a, P.root'_reflectionPerm_self,
      LinearMap.neg_apply, ih, hd_neg]
  · intro a s ih hs
    have hr : P.root' (P.reflectionPerm s.1 a.1) v =
        P.root' a.1 v - P.pairing a.1 s.1 * P.root' s.1 v := by
      change P.toLinearMap (P.root (P.reflectionPerm s.1 a.1)) v = _
      rw [P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing, map_sub, map_smul]
      rfl
    rw [P.coe_indivisiblePairing_reflectionPerm s a, hr, ih, hv_supp ⟨s, hs⟩, hrefl_d s.1 a.1]

private theorem exists_mem_corootSpan_torus_smul_eq_shift {t : G} (ht : t ∈ D.T) :
    ∃ v ∈ P.corootSpan ℝ,
      (⟨t, D.T_le_weylNormalizer ht⟩ : D.weylNormalizer) • φ = φ.shift v := by
  obtain ⟨d, hd⟩ := φ.exists_torus_smul_add_const ht
  obtain ⟨v, hv, hv_ind⟩ :=
    exists_mem_corootSpan_of_forall_reflectionPerm D (φ.torus_add_const_reflectionPerm ht hd)
  refine ⟨v, hv, ext_of_isIndivisible fun i hi x ↦ ?_⟩
  rw [hd i x, shift_apply, hv_ind i hi]

/-- **Every element of `D.weylNormalizer` acts on `φ` by a unique shift in the real coroot span**
(Bruhat–Tits I, 6.2.5, p. 120). -/
theorem existsUnique_mem_corootSpan_smul_eq_shift (n : D.weylNormalizer) :
    ∃! v : N, v ∈ P.corootSpan ℝ ∧ n • φ = φ.shift v := by
  suffices hex : ∃ v : N, v ∈ P.corootSpan ℝ ∧ n • φ = φ.shift v by
    obtain ⟨v, hv, hφv⟩ := hex
    exact ⟨v, ⟨hv, hφv⟩, fun w ⟨hw, hφw⟩ ↦
      (φ.shift_eq_shift_iff_of_mem_corootSpan hw hv).mp (hφw.symm.trans hφv)⟩
  have hmul : ∀ {n₁ n₂ : D.weylNormalizer},
      (∃ v₁ ∈ P.corootSpan ℝ, n₁ • φ = φ.shift v₁) →
      (∃ v₂ ∈ P.corootSpan ℝ, n₂ • φ = φ.shift v₂) →
      ∃ v ∈ P.corootSpan ℝ, (n₁ * n₂) • φ = φ.shift v := by
    rintro n₁ n₂ ⟨v₁, hv₁, h₁⟩ ⟨v₂, hv₂, h₂⟩
    refine ⟨v₁ + (D.weylGroupHom n₁ : P.Aut).coweightEquiv.symm v₂,
      add_mem hv₁ (coweightEquiv_symm_mem_corootSpan _ hv₂), ?_⟩
    rw [mul_smul, h₂, φ.smul_shift, h₁, shift_shift]
  induction n using D.weylNormalizer_induction with
  | torus t ht => exact φ.exists_mem_corootSpan_torus_smul_eq_shift ht
  | reflection i m hm =>
    obtain ⟨k, u₀, u', u'', m₀, hm₀, hm₀_eq, hu₀⟩ :=
      φ.exists_mul_mul_mem_reflectionCoset_and_apply_eq i
    let nm₀ : D.weylNormalizer := ⟨m₀, D.reflectionCoset_subset_weylNormalizer i hm₀⟩
    have ht : m * m₀⁻¹ ∈ D.T := D.mul_inv_mem_T hm₀ hm
    let nt : D.weylNormalizer := ⟨m * m₀⁻¹, D.T_le_weylNormalizer ht⟩
    have hnm_eq : (⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) =
        nt * nm₀ := Subtype.ext (by simp only [Subgroup.coe_mul, nt, nm₀]; group)
    rw [hnm_eq]
    exact hmul (φ.exists_mem_corootSpan_torus_smul_eq_shift ht)
      ⟨-(k • P.coroot i), neg_mem (Submodule.smul_mem _ k (P.corootSpanMem ℝ i).2),
        φ.smul_reflection hm₀ hm₀_eq hu₀⟩
  | one => exact ⟨0, zero_mem _, by rw [one_smul, shift_zero]⟩
  | mul n₁ n₂ ih₁ ih₂ => exact hmul ih₁ ih₂
  | inv n₁ ih =>
    obtain ⟨v, hv, h₁⟩ := ih
    let w_act := (D.weylGroupHom n₁⁻¹ : P.Aut).coweightEquiv.symm v
    refine ⟨-w_act, neg_mem (coweightEquiv_symm_mem_corootSpan _ hv), ?_⟩
    have h2 : φ = (n₁⁻¹ • φ).shift w_act := by
      calc φ = n₁⁻¹ • (n₁ • φ) := (inv_smul_smul n₁ φ).symm
        _ = n₁⁻¹ • φ.shift v := by rw [h₁]
        _ = (n₁⁻¹ • φ).shift w_act := φ.smul_shift n₁⁻¹ v
    calc n₁⁻¹ • φ = ((n₁⁻¹ • φ).shift w_act).shift (-w_act) := by simp
      _ = φ.shift (-w_act) := by rw [← h2]

/-- Every element of `D.weylNormalizer` preserves equipollence classes of valuations
(Bruhat–Tits I, 6.2.5, p. 120). -/
theorem equipollent_smul (n : D.weylNormalizer) : φ.Equipollent (n • φ) := by
  obtain ⟨v, ⟨_, hv⟩, _⟩ := φ.existsUnique_mem_corootSpan_smul_eq_shift n
  exact hv ▸ φ.equipollent_shift v

end RealWeylAction

end Valuation

end TauCeti.BruhatTits
