/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Ordered.Basic
public import TauCeti.Data.Fin.Tuple.Sort
public import TauCeti.Data.Finset.Inversions
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The ordered Čech complex is homotopy equivalent to the Čech complex

Let `C` be a thin category with finite products, for instance the open subsets of a topological
space, let `U : ι → C` be a family of objects indexed by a linearly ordered type, and let
`P : Cᵒᵖ ⥤ A` be a presheaf with values in a preadditive category with products. Restricting a
cochain of Mathlib's Čech complex `Č(U, P)` (all tuples of indices, repeated ones included) to the
strictly increasing tuples gives the map `toStrictMonoCechComplex` onto the ordered Čech complex
`Čₒ(U, P)`. This file shows that it is a homotopy equivalence
(`strictMonoCechComplexHomotopyEquiv`), so both complexes have the same cohomology. The homotopy
inverse is the alternating extension `fromStrictMonoCechComplex`: its factor at a tuple with a
repeated entry is zero, and its factor at an injective tuple `b` is the factor of the increasing
rearrangement `b ∘ Tuple.sort b`, times the inversion sign `(-1) ^ #(univ.inversions b)`. No
covering condition or finiteness is assumed, the family may be empty, and no division occurs, so
the comparison holds over any coefficients, `𝔽₂` included.

Thinness is needed for the alternating cochains to form a subcomplex: in a thin category the
product `U (b 0) × ⋯ × U (b n)` and the restrictions between such products only depend on the set
of entries of `b`. Without it the statement fails. For a single member `X` admitting a map from the
terminal object `T`, the augmented Čech complex is exact
(`TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_hom`), so `Č(U, P)` has cohomology `P(T)` in
degree `0`, whereas `Čₒ(U, P)` is `P(X)` in degree `0`.

## The construction

All maps are dual to universal maps of integral chains on tuples. Let `Kₙ` be the free abelian
group on the tuples `Fin (n + 1) → ι`, with the alternating boundary `∂`. The alternation `alt`
sends an injective tuple to the signed increasing rearrangement and a tuple with a repeated entry
to `0`; it commutes with `∂`, since for a tuple with `b p = b q` the only faces which can survive
alternation remove `p` or `q`, and they cancel. A chain homotopy `H` between the identity and
`alt` is constructed degree by degree with the cone on the first entry,
`H b = b 0 * (b - alt b - H (∂ b))`, using `∂ (v * x) = x - v * ∂ x`. Every chain occurring here is
a combination of tuples whose entries are entries of `b`. A linear map with this property induces a
map of Čech cochains, whose factor at `b` combines the factors at these tuples restricted along
the unique maps of a thin category; this is compatible with composition and sends `∂` to the Čech
differential, `alt` to the composite of restriction and alternating extension, and `H` to the
homotopy.

## Main definitions

* `TauCeti.CategoryTheory.fromStrictMonoCechComplex U`: the alternating extension
  `Čₒ(U, P) ⟶ Č(U, P)`, natural in `P`.
* `TauCeti.CategoryTheory.strictMonoCechComplexHomotopyEquiv U P`: the homotopy equivalence
  `Č(U, P) ≃ Čₒ(U, P)` whose forward map is `toStrictMonoCechComplex`.

## Main results

* `TauCeti.CategoryTheory.fromStrictMonoCechComplex_app_f_π` and
  `TauCeti.CategoryTheory.fromStrictMonoCechComplex_app_f_π_of_not_injective`: the factors of the
  alternating extension.
* `TauCeti.CategoryTheory.fromStrictMonoCechComplex_comp_toStrictMonoCechComplex`: the alternating
  extension is a right inverse of the restriction.
* Instances: restriction and alternating extension are quasi-isomorphisms.

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.23 (alternating and ordered Čech
  complexes, tags 01FH–01FM), for the statement; the homotopy here is constructed directly.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Finset

universe w v v' u u'

namespace TauCeti.CategoryTheory

namespace OrderedCechHomotopy

variable {ι : Type w} {n : ℕ}

/-- Integral chains on tuples of length `n + 1`. -/
private abbrev Chain (ι : Type w) (n : ℕ) := (Fin (n + 1) → ι) →₀ ℤ

/-- The boundary of chains on tuples. -/
private def bdry (n : ℕ) : Chain ι (n + 1) →ₗ[ℤ] Chain ι n :=
  Finsupp.linearCombination ℤ fun b ↦
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (b ∘ j.succAbove) 1

private lemma bdry_single (n : ℕ) (b : Fin (n + 2) → ι) :
    bdry n (Finsupp.single b 1) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (b ∘ j.succAbove) 1 := by
  simp [bdry]

/-- The first simplicial identity `SimplexCategory.δ_comp_δ''` for the coface maps
`Fin.succAbove`. -/
private lemma succAbove_comp_succAbove {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 3)}
    (h : (j : ℕ) ≤ i) :
    j.succAbove ∘ i.succAbove = i.succ.succAbove ∘ (j.castLT (by omega)).succAbove :=
  (congrArg (fun f ↦ ⇑(SimplexCategory.Hom.toOrderHom f))
    (SimplexCategory.δ_comp_δ'' (i := j) (j := i) (Fin.le_def.2 h))).symm

/-- The boundary of chains on tuples squares to zero on a tuple. The terms of the double sum are
paired by `(j, i) ↦ (i + 1, j)` for `j ≤ i`, as in
`AlgebraicTopology.AlternatingFaceMapComplex.d_squared`. -/
private lemma bdry_bdry_single (n : ℕ) (b : Fin (n + 3) → ι) :
    bdry n (bdry (n + 1) (Finsupp.single b 1)) = 0 := by
  simp only [bdry_single, map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← Finset.sum_product']
  let S : Finset (Fin (n + 3) × Fin (n + 2)) := {ji | (ji.1 : ℕ) ≤ ji.2}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, add_eq_zero_iff_eq_neg,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_bij' (fun ji h ↦ (ji.2.succ, ji.1.castLT (by
      have : (ji.1 : ℕ) ≤ ji.2 := (Finset.mem_filter.1 h).2
      omega)))
    (fun ji h ↦ (ji.2.castSucc, ji.1.pred fun h0 ↦ by simp [S, h0] at h)) ?_ ?_ ?_ ?_ ?_
  · intro ji h
    simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ,
      Fin.val_castLT, not_le] at h ⊢
    omega
  · intro ji h
    simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_castSucc, Fin.val_pred, not_le] at h ⊢
    omega
  · intro ji h
    simp
  · intro ji h
    simp
  · rintro ⟨j, i⟩ h
    have h' : (j : ℕ) ≤ i := (Finset.mem_filter.1 h).2
    rw [Function.comp_assoc, succAbove_comp_succAbove h', ← Function.comp_assoc, ← neg_smul,
      Fin.val_succ, Fin.val_castLT, pow_succ]
    congr 1
    ring

/-- The boundary of chains on tuples squares to zero. -/
private lemma bdry_bdry (n : ℕ) (x : Chain ι (n + 2)) : bdry n (bdry (n + 1) x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single b k =>
    rw [← mul_one k, ← smul_eq_mul, ← Finsupp.smul_single, map_zsmul, map_zsmul,
      bdry_bdry_single, smul_zero]

section LinearOrder

variable [LinearOrder ι]

/-! ### Alternation -/

/-- The alternation of chains on tuples: an injective tuple goes to its increasing rearrangement
times the sign of the rearrangement, and a tuple with a repeated entry goes to zero. -/
private def alt (n : ℕ) : Chain ι n →ₗ[ℤ] Chain ι n :=
  Finsupp.linearCombination ℤ fun b ↦
    if Function.Injective b then
      (-1 : ℤ) ^ #(univ.inversions b) • Finsupp.single (b ∘ Tuple.sort b) 1
    else 0

private lemma alt_single_of_injective {b : Fin (n + 1) → ι} (hb : Function.Injective b) :
    alt n (Finsupp.single b 1) =
      (-1 : ℤ) ^ #(univ.inversions b) • Finsupp.single (b ∘ Tuple.sort b) 1 := by
  simp [alt, hb]

private lemma alt_single_of_not_injective {b : Fin (n + 1) → ι} (hb : ¬Function.Injective b) :
    alt n (Finsupp.single b 1) = 0 := by
  simp [alt, hb]

/-- Alternation fixes a strictly increasing tuple. -/
private lemma alt_single_of_strictMono {b : Fin (n + 1) → ι} (hb : StrictMono b) :
    alt n (Finsupp.single b 1) = Finsupp.single b 1 := by
  simp [alt_single_of_injective hb.injective, Tuple.sort_eq_refl_iff_monotone.2 hb.monotone,
    inversions_eq_empty_of_monotone hb.monotone]

/-- The terms of the boundary of an injective tuple, after alternation, are the terms of the
boundary of its increasing rearrangement. -/
private lemma alt_bdry_single_of_injective {b : Fin (n + 2) → ι} (hb : Function.Injective b) :
    alt n (bdry n (Finsupp.single b 1)) = bdry n (alt (n + 1) (Finsupp.single b 1)) := by
  rw [alt_single_of_injective hb, map_zsmul, bdry_single, bdry_single, map_sum, Finset.smul_sum]
  refine Fintype.sum_bijective (Tuple.sort b).symm (Tuple.sort b).symm.bijective _ _ fun k ↦ ?_
  have hb' : Function.Injective (b ∘ k.succAbove) := hb.comp Fin.succAbove_right_injective
  have hE : #{i | i < k ∧ b i = b k} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    exact fun i _ ⟨hi, h⟩ ↦ hi.ne (hb h)
  have h := neg_one_pow_card_univ_inversions_comp_succAbove (R := ℤ) b k
  rw [hE, pow_zero, mul_one, pow_add] at h
  rw [map_zsmul, alt_single_of_injective hb', Tuple.comp_succAbove_comp_sort hb k, smul_smul,
    smul_smul]
  congr 1
  have hL : ((-1 : ℤ) ^ #{i | b i < b k}) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [Tuple.val_sort_symm_apply hb]
  linear_combination (-(-1 : ℤ) ^ #{i | b i < b k}) * h -
    ((-1) ^ (k : ℕ) * (-1) ^ #(univ.inversions (b ∘ k.succAbove))) * hL

/-- The coefficients of the two surviving terms of the boundary of a tuple with exactly one
repeated pair of entries `b p = b q`, `p < q`, cancel. -/
private lemma neg_one_pow_mul_neg_one_pow_card_inversions_add {b : Fin (n + 1) → ι}
    {p q : Fin (n + 1)}
    (hlt : p < q) (h : b p = b q) (hq : Function.Injective (b ∘ q.succAbove)) :
    (-1 : ℤ) ^ (p : ℕ) * (-1) ^ #(univ.inversions (b ∘ p.succAbove)) +
      (-1) ^ (q : ℕ) * (-1) ^ #(univ.inversions (b ∘ q.succAbove)) = 0 := by
  have hEp : #{i | i < p ∧ b i = b p} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    exact fun i _ ⟨hi, hbi⟩ ↦
      hi.ne (Fin.eq_of_injective_comp_succAbove hq (hi.trans hlt).ne hlt.ne hbi)
  have hEq : #{i | i < q ∧ b i = b q} = 1 := by
    refine card_eq_one.2 ⟨p, ext fun i ↦ ?_⟩
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun ⟨hi, hbi⟩ ↦ Fin.eq_of_injective_comp_succAbove hq hi.ne hlt.ne (hbi.trans h.symm),
      by rintro rfl; exact ⟨hlt, h⟩⟩
  have hp' := neg_one_pow_card_univ_inversions_comp_succAbove (R := ℤ) b p
  have hq' := neg_one_pow_card_univ_inversions_comp_succAbove (R := ℤ) b q
  rw [hEp, pow_zero, mul_one, pow_add] at hp'
  rw [hEq, pow_one, ← h, pow_add] at hq'
  have ha : ((-1 : ℤ) ^ #{i | b i < b p}) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-(-1 : ℤ) ^ #{i | b i < b p}) * hp' + (-(-1 : ℤ) ^ #{i | b i < b p}) * hq' -
    ((-1 : ℤ) ^ (p : ℕ) * (-1) ^ #(univ.inversions (b ∘ p.succAbove)) +
      (-1) ^ (q : ℕ) * (-1) ^ #(univ.inversions (b ∘ q.succAbove))) * ha

/-- For a tuple with a repeated entry `b p = b q`, the alternation of its boundary vanishes: only
the terms removing `p` or `q` can survive, and they cancel. -/
private lemma alt_bdry_single_of_not_injective {b : Fin (n + 2) → ι}
    (hb : ¬Function.Injective b) : alt n (bdry n (Finsupp.single b 1)) = 0 := by
  obtain ⟨p, q, h, hpq⟩ := Function.not_injective_iff.1 hb
  wlog hlt : p < q generalizing p q
  · exact this q p h.symm hpq.symm ((Ne.lt_or_gt hpq).resolve_left hlt)
  rw [bdry_single, map_sum, Fintype.sum_eq_add p q hpq fun k hk ↦ ?_]
  · simp only [map_zsmul]
    by_cases hp : Function.Injective (b ∘ p.succAbove)
    · have hq := Fin.injective_comp_succAbove_of_eq hpq h hp
      rw [alt_single_of_injective hp, alt_single_of_injective hq,
        Tuple.comp_sort_eq_comp_sort_of_range_eq hq hp
          ((Fin.range_comp_succAbove_of_eq hpq.symm h.symm).trans
            (Fin.range_comp_succAbove_of_eq hpq h).symm), smul_smul, smul_smul, ← add_smul,
        neg_one_pow_mul_neg_one_pow_card_inversions_add hlt h hq, zero_smul]
    · have hq : ¬Function.Injective (b ∘ q.succAbove) := fun hq ↦
        hp (Fin.injective_comp_succAbove_of_eq hpq.symm h.symm hq)
      rw [alt_single_of_not_injective hp, alt_single_of_not_injective hq, smul_zero, smul_zero,
        add_zero]
  · rw [map_zsmul, alt_single_of_not_injective, smul_zero]
    intro hk'
    obtain ⟨p', hp'⟩ := Fin.exists_succAbove_eq hk.1.symm
    obtain ⟨q', hq'⟩ := Fin.exists_succAbove_eq hk.2.symm
    have hb' : (b ∘ k.succAbove) p' = (b ∘ k.succAbove) q' := by simp [hp', hq', h]
    exact hpq (hp' ▸ hq' ▸ congrArg _ (hk' hb'))

/-- Alternation commutes with the boundary. -/
private lemma alt_bdry (x : Chain ι (n + 1)) : alt n (bdry n x) = bdry n (alt (n + 1) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single b k =>
    rw [← mul_one k, ← smul_eq_mul, ← Finsupp.smul_single, map_zsmul, map_zsmul, map_zsmul,
      map_zsmul]
    by_cases hb : Function.Injective b
    · rw [alt_bdry_single_of_injective hb]
    · rw [alt_bdry_single_of_not_injective hb, alt_single_of_not_injective hb, map_zero]

/-- On tuples of length one, alternation is the identity. -/
private lemma alt_zero (x : Chain ι 0) : alt 0 x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | single b k =>
    have hb : StrictMono b := fun i j h ↦ absurd (Fin.ext (by omega)) h.ne
    rw [← mul_one k, ← smul_eq_mul, ← Finsupp.smul_single, map_zsmul, alt_single_of_strictMono hb]

/-! ### The cone and the homotopy -/

/-- The cone on a vertex `v`: prepend `v` to every tuple. -/
private def cone (v : ι) (n : ℕ) : Chain ι n →ₗ[ℤ] Chain ι (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ fun a ↦ (Fin.cons v a : Fin (n + 2) → ι)

omit [LinearOrder ι] in
private lemma cone_single (v : ι) (a : Fin (n + 1) → ι) (k : ℤ) :
    cone v n (Finsupp.single a k) = Finsupp.single (Fin.cons v a) k := by
  simp [cone]

omit [LinearOrder ι] in
/-- The cone is a contracting homotopy in positive degrees. -/
private lemma bdry_cone (v : ι) (x : Chain ι (n + 1)) :
    bdry (n + 1) (cone v (n + 1) x) = x - cone v n (bdry n x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]; abel
  | single a k =>
    rw [← mul_one k, ← smul_eq_mul, ← Finsupp.smul_single, map_zsmul, map_zsmul, map_zsmul,
      map_zsmul, ← smul_sub]
    congr 1
    have h₀ : (Fin.cons v a : Fin (n + 3) → ι) ∘ (0 : Fin (n + 3)).succAbove = a := by
      ext x
      simp
    rw [cone_single, bdry_single, Fin.sum_univ_succ, h₀, bdry_single, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
      Finset.sum_neg_distrib, map_zsmul, cone_single, Fin.cons_comp_succ_succAbove, sub_eq_add_neg]
    -- `Fin.removeNth j a` is `a ∘ j.succAbove` by definition
    rfl

/-- The homotopy between the identity and alternation: a tuple `b` of length `n + 2` goes to the
cone with vertex `b 0` on `b - alt b - homotopy (bdry b)`. -/
private def homotopy : (n : ℕ) → Chain ι n →ₗ[ℤ] Chain ι (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℤ fun b ↦ cone (b 0) (n + 1)
      (Finsupp.single b 1 - alt (n + 1) (Finsupp.single b 1) -
        homotopy n (bdry n (Finsupp.single b 1)))

private lemma homotopy_succ_single (b : Fin (n + 2) → ι) :
    homotopy (n + 1) (Finsupp.single b 1) = cone (b 0) (n + 1)
      (Finsupp.single b 1 - alt (n + 1) (Finsupp.single b 1) -
        homotopy n (bdry n (Finsupp.single b 1))) := by
  simp [homotopy]

/-- The homotopy identity in degree `n + 1`, assuming its consequence on boundaries in degree
`n`. -/
private lemma bdry_homotopy_add (hn : ∀ y : Chain ι (n + 1),
      bdry n (homotopy n (bdry n y)) = bdry n y - alt n (bdry n y))
    (z : Chain ι (n + 1)) :
    bdry (n + 1) (homotopy (n + 1) z) + homotopy n (bdry n z) = z - alt (n + 1) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, map_add, add_add_add_comm, hx, hy]
    abel
  | single b k =>
    rw [← mul_one k, ← smul_eq_mul, ← Finsupp.smul_single]
    simp only [map_zsmul, ← smul_add, ← smul_sub]
    congr 1
    have h : bdry n (Finsupp.single b 1 - alt (n + 1) (Finsupp.single b 1) -
        homotopy n (bdry n (Finsupp.single b 1))) = 0 := by
      rw [map_sub, map_sub, hn, alt_bdry]
      abel
    rw [homotopy_succ_single, bdry_cone, h, map_zero, sub_zero]
    abel

/-- The homotopy identity applied to boundaries. -/
private lemma bdry_homotopy_bdry (n : ℕ) (y : Chain ι (n + 1)) :
    bdry n (homotopy n (bdry n y)) = bdry n y - alt n (bdry n y) := by
  induction n with
  | zero => simp [homotopy, alt_zero]
  | succ n ih =>
    have := bdry_homotopy_add ih (bdry (n + 1) y)
    rwa [bdry_bdry, map_zero, add_zero] at this

/-- The homotopy identity in degree `0`. -/
private lemma bdry_homotopy_zero :
    (bdry 0).comp (homotopy (ι := ι) 0) = LinearMap.id - alt 0 :=
  LinearMap.ext fun x ↦ by simp [homotopy, alt_zero]

/-- The homotopy identity in degree `n + 1`. -/
private lemma bdry_homotopy_succ (n : ℕ) :
    (bdry (n + 1)).comp (homotopy (ι := ι) (n + 1)) + (homotopy n).comp (bdry n) =
      LinearMap.id - alt (n + 1) :=
  LinearMap.ext (bdry_homotopy_add (bdry_homotopy_bdry n))

/-! ### Entries of tuples -/

/-- A linear map of chains which sends every tuple `b` to a chain on tuples whose entries are
entries of `b`. -/
private def RangeRespecting {m k : ℕ} (L : Chain ι m →ₗ[ℤ] Chain ι k) : Prop :=
  ∀ b : Fin (m + 1) → ι,
    L (Finsupp.single b 1) ∈ Finsupp.supported ℤ ℤ {a | Set.range a ⊆ Set.range b}

omit [LinearOrder ι] in
private lemma RangeRespecting.map_mem {m k : ℕ} {L : Chain ι m →ₗ[ℤ] Chain ι k}
    (hL : RangeRespecting L) {s : Set ι} {x : Chain ι m}
    (hx : x ∈ Finsupp.supported ℤ ℤ {a | Set.range a ⊆ s}) :
    L x ∈ Finsupp.supported ℤ ℤ {a | Set.range a ⊆ s} :=
  (Submodule.span_le (p := (Finsupp.supported ℤ ℤ {a | Set.range a ⊆ s}).comap L)).2
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact Finsupp.supported_mono (fun _ hc ↦ Set.Subset.trans hc ha) (hL a))
    (Finsupp.supported_eq_span_single ℤ _ ▸ hx)

omit [LinearOrder ι] in
private lemma rangeRespecting_bdry (n : ℕ) : RangeRespecting (bdry (ι := ι) n) := fun b ↦ by
  rw [bdry_single]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
    (Finsupp.single_mem_supported ℤ 1 (Set.range_comp_subset_range _ _))

private lemma rangeRespecting_alt (n : ℕ) : RangeRespecting (alt (ι := ι) n) := fun b ↦ by
  by_cases hb : Function.Injective b
  · rw [alt_single_of_injective hb]
    exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℤ 1 (Tuple.range_comp_sort b).le)
  · rw [alt_single_of_not_injective hb]
    exact zero_mem _

omit [LinearOrder ι] in
private lemma cone_mem_supported {v : ι} {s : Set ι} (hv : v ∈ s) {x : Chain ι n}
    (hx : x ∈ Finsupp.supported ℤ ℤ {a | Set.range a ⊆ s}) :
    cone v n x ∈ Finsupp.supported ℤ ℤ {a | Set.range a ⊆ s} :=
  Finsupp.supported_comap_lmapDomain ℤ ℤ _ _ <| Finsupp.supported_mono (fun a ha ↦ by
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, Fin.range_cons] using Set.insert_subset hv ha)
    hx

private lemma rangeRespecting_homotopy : ∀ n, RangeRespecting (homotopy (ι := ι) n)
  | 0 => fun _ ↦ by simp [homotopy]
  | n + 1 => fun b ↦ by
    rw [homotopy_succ_single]
    exact cone_mem_supported (Set.mem_range_self 0) (sub_mem (sub_mem
      (Finsupp.single_mem_supported ℤ 1 (Set.Subset.refl _)) (rangeRespecting_alt _ b))
      ((rangeRespecting_homotopy n).map_mem (rangeRespecting_bdry n b)))

end LinearOrder

/-! ### Chains on tuples acting on Čech cochains -/

section Dual

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [Quiver.IsThin C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A] (U : ι → C)
  (P : Cᵒᵖ ⥤ A)

/-- The projection `U (b 0) × ⋯ × U (b (m - 1)) ⟶ U (a 0) × ⋯ × U (a (k - 1))` when every entry
of `a` is an entry of `b`. In a thin category it is the only morphism between these products. -/
private def tupleRestrict {m k : ℕ} {b : Fin m → ι} {a : Fin k → ι}
    (h : Set.range a ⊆ Set.range b) : (∏ᶜ fun j ↦ U (b j)) ⟶ ∏ᶜ fun j ↦ U (a j) :=
  Pi.lift fun j ↦ Pi.π _ (h ⟨j, rfl⟩).choose ≫ eqToHom (congrArg U (h ⟨j, rfl⟩).choose_spec)

/-- The degree `m` term of the Čech complex, as the product which defines it. -/
private abbrev cechX (m : ℕ) : A :=
  ∏ᶜ fun a : Fin (m + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))

/-- The differential of the Čech complex, with source and target the products which define its
terms. -/
private abbrev cechD (n : ℕ) : cechX U P n ⟶ cechX U P (n + 1) :=
  ((cechComplexFunctor U).obj P).d n (n + 1)

open scoped Classical in
/-- The factor at a tuple `b` of the Čech cochain dual to a chain `y`: a tuple `a` in `y` whose
entries are entries of `b` contributes the factor of `a`, restricted to the product indexed by
`b`. -/
private def evalChain {n : ℕ} (b : Fin (n + 1) → ι) (m : ℕ) :
    Chain ι m →+ (cechX U P m ⟶ P.obj (op (∏ᶜ fun j ↦ U (b j)))) :=
  Finsupp.liftAddHom fun a ↦ zmultiplesHom _ (if h : Set.range a ⊆ Set.range b then
    Pi.π (fun a : Fin (m + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a ≫
      P.map (tupleRestrict U h).op else 0)

omit [Quiver.IsThin C] in
private lemma evalChain_single {n m : ℕ} {b : Fin (n + 1) → ι} {a : Fin (m + 1) → ι}
    (h : Set.range a ⊆ Set.range b) (k : ℤ) :
    evalChain U P b m (Finsupp.single a k) =
      k • (Pi.π (fun a : Fin (m + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a ≫
        P.map (tupleRestrict U h).op) := by
  simp [evalChain, h]

/-- Restriction of the factor of `b` to a tuple `c` whose entries are entries of `b`. -/
private lemma evalChain_eq_comp {n n' m : ℕ} {b : Fin (n + 1) → ι} {c : Fin (n' + 1) → ι}
    (hcb : Set.range c ⊆ Set.range b) {y : Chain ι m}
    (hy : y ∈ Finsupp.supported ℤ ℤ {a | Set.range a ⊆ Set.range c}) :
    evalChain U P b m y = evalChain U P c m y ≫ P.map (tupleRestrict U hcb).op := by
  rw [Finsupp.supported_eq_span_single] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    rw [evalChain_single U P (Set.Subset.trans ha hcb), evalChain_single U P ha, one_smul,
      one_smul, Category.assoc, ← P.map_comp, ← op_comp,
      Subsingleton.elim (tupleRestrict U hcb ≫ tupleRestrict U ha)]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, Preadditive.add_comp]
  | smul k x _ hx => rw [map_zsmul, map_zsmul, hx, Preadditive.zsmul_comp]

/-- The map of Čech cochains dual to a linear map of chains on tuples. -/
private def dualMap {m k : ℕ} (L : Chain ι m →ₗ[ℤ] Chain ι k) :
    cechX U P k ⟶ cechX U P m :=
  Pi.lift fun b ↦ evalChain U P b k (L (Finsupp.single b 1))

omit [Quiver.IsThin C] in
@[reassoc]
private lemma dualMap_π {m k : ℕ} (L : Chain ι m →ₗ[ℤ] Chain ι k) (b : Fin (m + 1) → ι) :
    dualMap U P L ≫ Pi.π _ b = evalChain U P b k (L (Finsupp.single b 1)) :=
  Pi.lift_comp_π _ _

private lemma dualMap_comp_evalChain {m k n : ℕ} {L : Chain ι m →ₗ[ℤ] Chain ι k}
    (hL : RangeRespecting L) {b : Fin (n + 1) → ι} {y : Chain ι m}
    (hy : y ∈ Finsupp.supported ℤ ℤ {a | Set.range a ⊆ Set.range b}) :
    dualMap U P L ≫ evalChain U P b m y = evalChain U P b k (L y) := by
  rw [Finsupp.supported_eq_span_single] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    rw [evalChain_single U P hc, one_smul, dualMap_π_assoc, ← evalChain_eq_comp U P hc (hL c)]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, Preadditive.comp_add, hx, hy]
  | smul k x _ hx => rw [map_zsmul, map_zsmul, map_zsmul, Preadditive.comp_zsmul, hx]

private lemma dualMap_comp {m k n : ℕ} {L : Chain ι k →ₗ[ℤ] Chain ι n}
    {M : Chain ι m →ₗ[ℤ] Chain ι k} (hL : RangeRespecting L) (hM : RangeRespecting M) :
    dualMap U P (L.comp M) = dualMap U P L ≫ dualMap U P M :=
  Pi.hom_ext _ _ fun b ↦ by
    rw [Category.assoc, dualMap_π, dualMap_π, dualMap_comp_evalChain U P hL (hM b),
      LinearMap.comp_apply]

omit [Quiver.IsThin C] in
private lemma dualMap_add {m k : ℕ} (L M : Chain ι m →ₗ[ℤ] Chain ι k) :
    dualMap U P (L + M) = dualMap U P L + dualMap U P M :=
  Pi.hom_ext _ _ fun b ↦ by
    rw [Preadditive.add_comp, dualMap_π, dualMap_π, dualMap_π, LinearMap.add_apply, map_add]

omit [Quiver.IsThin C] in
private lemma dualMap_sub {m k : ℕ} (L M : Chain ι m →ₗ[ℤ] Chain ι k) :
    dualMap U P (L - M) = dualMap U P L - dualMap U P M :=
  Pi.hom_ext _ _ fun b ↦ by
    rw [Preadditive.sub_comp, dualMap_π, dualMap_π, dualMap_π, LinearMap.sub_apply, map_sub]

private lemma dualMap_id (m : ℕ) : dualMap U P (LinearMap.id : Chain ι m →ₗ[ℤ] Chain ι m) = 𝟙 _ :=
  Pi.hom_ext _ _ fun b ↦ by
    rw [dualMap_π, Category.id_comp, LinearMap.id_apply, evalChain_single U P subset_rfl,
      one_smul, Subsingleton.elim (tupleRestrict U _) (𝟙 _), op_id, P.map_id, Category.comp_id]

/-- The boundary of chains on tuples is dual to the Čech differential. -/
private lemma dualMap_bdry (n : ℕ) : dualMap U P (bdry n) = cechD U P n :=
  Pi.hom_ext _ _ fun k ↦ (dualMap_π U P _ k).trans <|
    Eq.trans (by
      rw [bdry_single, map_sum]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [map_zsmul, evalChain_single U P (Set.range_comp_subset_range _ _), one_smul,
        Subsingleton.elim (tupleRestrict U _)
          (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x))]
      -- the factor of `k ∘ m.succAbove` is written once through `cechX` and once through the
      -- Čech nerve; these are the same product
      rfl) (cechComplexFunctor_obj_d_comp_π U P n k).symm

end Dual

end OrderedCechHomotopy

open OrderedCechHomotopy

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] {ι : Type w} [LinearOrder ι] (U : ι → C)

/-! ### The alternating extension of ordered cochains -/

/-- The degree `n` component of `fromStrictMonoCechComplex`. -/
private def fromStrictMonoCechX (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((strictMonoCechComplexFunctor U).obj P).X n ⟶ cechX U P n :=
  Pi.lift fun b ↦ if hb : Function.Injective b then
    (-1 : ℤ) ^ #(univ.inversions b) •
      (strictMonoCechComplexπ U P ⟨b ∘ Tuple.sort b, Tuple.strictMono_comp_sort hb⟩ ≫
        P.map (Pi.lift fun j ↦ Pi.π (fun j ↦ U (b j)) (Tuple.sort b j)).op) else 0

@[reassoc]
private lemma fromStrictMonoCechX_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (b : Fin (n + 1) → ι) :
    fromStrictMonoCechX U P n ≫ Pi.π (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) b =
      if hb : Function.Injective b then
        (-1 : ℤ) ^ #(univ.inversions b) •
          (strictMonoCechComplexπ U P ⟨b ∘ Tuple.sort b, Tuple.strictMono_comp_sort hb⟩ ≫
            P.map (Pi.lift fun j ↦ Pi.π (fun j ↦ U (b j)) (Tuple.sort b j)).op)
      else 0 :=
  Pi.lift_comp_π _ _

/-- The restriction of Čech cochains to the strictly increasing tuples, with source the product
which defines the Čech complex. -/
private abbrev toStrictMonoCechX (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechX U P n ⟶ ((strictMonoCechComplexFunctor U).obj P).X n :=
  ((toStrictMonoCechComplex U).app P).f n

variable [Quiver.IsThin C]

/-- Restricting a Čech cochain to the strictly increasing tuples and extending it alternatingly is
the dual of alternation. -/
private lemma toStrictMonoCechX_comp_fromStrictMonoCechX (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    toStrictMonoCechX U P n ≫ fromStrictMonoCechX U P n = dualMap U P (alt n) :=
  Pi.hom_ext _ _ fun b ↦ by
    rw [Category.assoc, fromStrictMonoCechX_π, dualMap_π]
    by_cases hb : Function.Injective b
    · simp only [hb, ↓reduceDIte]
      rw [alt_single_of_injective hb, map_zsmul,
        evalChain_single U P (Tuple.range_comp_sort b).le, one_smul, Preadditive.comp_zsmul,
        -- the goal writes the restriction as `toStrictMonoCechX` and its projection through
        -- `cechX`, local abbreviations which `rw` does not unfold to match the projection lemma;
        -- the `show` restates `toStrictMonoCechComplex_app_f_π_assoc` in these terms
        show toStrictMonoCechX U P n ≫ _ ≫ _ =
          Pi.π (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) _ ≫ _ from
          toStrictMonoCechComplex_app_f_π_assoc U P n _ _,
        Subsingleton.elim (tupleRestrict U _)]
    · simp only [hb, ↓reduceDIte, comp_zero, alt_single_of_not_injective hb, map_zero]

private lemma fromStrictMonoCechX_comm (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    fromStrictMonoCechX U P n ≫ cechD U P n =
      ((strictMonoCechComplexFunctor U).obj P).d n (n + 1) ≫ fromStrictMonoCechX U P (n + 1) := by
  have hcomm : toStrictMonoCechX U P n ≫ ((strictMonoCechComplexFunctor U).obj P).d n (n + 1) =
      cechD U P n ≫ toStrictMonoCechX U P (n + 1) := ((toStrictMonoCechComplex U).app P).comm n _
  have : Epi (toStrictMonoCechX U P n) :=
    inferInstanceAs (Epi (((toStrictMonoCechComplex U).app P).f n))
  rw [← cancel_epi (toStrictMonoCechX U P n), ← Category.assoc,
    toStrictMonoCechX_comp_fromStrictMonoCechX, reassoc_of% hcomm,
    toStrictMonoCechX_comp_fromStrictMonoCechX, ← dualMap_bdry,
    ← dualMap_comp U P (rangeRespecting_alt n) (rangeRespecting_bdry n),
    ← dualMap_comp U P (rangeRespecting_bdry n) (rangeRespecting_alt (n + 1))]
  exact congrArg _ (LinearMap.ext alt_bdry)

/-- The action of a morphism of presheaves on the Čech complexes, between the products which
define their terms. -/
private abbrev cechMapX {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) : cechX U P n ⟶ cechX U Q n :=
  ((cechComplexFunctor U).map α).f n

omit [Quiver.IsThin C] in
private lemma fromStrictMonoCechX_naturality {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    ((strictMonoCechComplexFunctor U).map α).f n ≫ fromStrictMonoCechX U Q n =
      fromStrictMonoCechX U P n ≫ cechMapX U α n :=
  Pi.hom_ext _ _ fun b ↦ by
    rw [Category.assoc, Category.assoc, fromStrictMonoCechX_π,
      -- the goal writes the map as `cechMapX` and its projections through `cechX`, local
      -- abbreviations which `rw` does not unfold to match the projection lemma; the `show`
      -- restates `cechComplexFunctor_map_f_π` in these terms
      show cechMapX U α n ≫ Pi.π (fun a : Fin (n + 1) → ι ↦ Q.obj (op (∏ᶜ fun j ↦ U (a j)))) b =
        Pi.π (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) b ≫ _ from
        cechComplexFunctor_map_f_π U P α n b,
      fromStrictMonoCechX_π_assoc]
    by_cases hb : Function.Injective b
    · simp [hb]
    · simp [hb]

private lemma fromStrictMonoCechX_comp_toStrictMonoCechX (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    fromStrictMonoCechX U P n ≫ toStrictMonoCechX U P n = 𝟙 _ := by
  have : Epi (toStrictMonoCechX U P n) :=
    inferInstanceAs (Epi (((toStrictMonoCechComplex U).app P).f n))
  rw [← cancel_epi (toStrictMonoCechX U P n), ← Category.assoc,
    toStrictMonoCechX_comp_fromStrictMonoCechX, Category.comp_id]
  ext a
  -- as in `toStrictMonoCechX_comp_fromStrictMonoCechX`, the `show` restates
  -- `toStrictMonoCechComplex_app_f_π` through the local abbreviations `toStrictMonoCechX` and
  -- `cechX` of the goal, which `rw` does not unfold
  rw [Category.assoc, show toStrictMonoCechX U P n ≫ _ =
      Pi.π (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a.1 from
      toStrictMonoCechComplex_app_f_π U P n a,
    dualMap_π, alt_single_of_strictMono a.2, evalChain_single U P subset_rfl, one_smul,
    Subsingleton.elim (tupleRestrict U _) (𝟙 _), op_id, P.map_id, Category.comp_id]

/-- The alternating extension `Čₒ(U, P) ⟶ Č(U, P)` of ordered Čech cochains, natural in the
presheaf `P`, for a family of objects of a thin category indexed by a linearly ordered type. Its
factor at a tuple `b` is zero when `b` has a repeated entry
(`fromStrictMonoCechComplex_app_f_π_of_not_injective`); when `b` is injective it is the factor of
the increasing rearrangement `b ∘ Tuple.sort b` of `b`, times the sign `(-1) ^ #(univ.inversions b)`
of the rearrangement (`fromStrictMonoCechComplex_app_f_π`). It is a right inverse of
`toStrictMonoCechComplex` (`fromStrictMonoCechComplex_comp_toStrictMonoCechComplex`), and in fact
a homotopy inverse (`strictMonoCechComplexHomotopyEquiv`).

Thinness makes the alternating cochains a subcomplex: in a thin category the products
`U (b 0) × ⋯ × U (b n)` and their restriction maps only depend on the set of entries of `b`. -/
def fromStrictMonoCechComplex :
    strictMonoCechComplexFunctor (A := A) U ⟶ cechComplexFunctor U where
  app P :=
    { f := fromStrictMonoCechX U P
      comm' := by
        rintro i _ rfl
        exact fromStrictMonoCechX_comm U P i }
  naturality _ _ α := HomologicalComplex.hom_ext _ _ (fromStrictMonoCechX_naturality U α)

/-- The factor of the alternating extension at an injective tuple `b` is the factor of its
increasing rearrangement `b ∘ Tuple.sort b`, restricted along the reindexing
`U (b 0) × ⋯ × U (b n) ⟶ U (b (σ 0)) × ⋯ × U (b (σ n))` for `σ = Tuple.sort b`, times the sign
`(-1) ^ #(univ.inversions b)` of the rearrangement. -/
@[reassoc]
theorem fromStrictMonoCechComplex_app_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ) {b : Fin (n + 1) → ι}
    (hb : Function.Injective b) :
    ((fromStrictMonoCechComplex U).app P).f n ≫ Pi.π _ b =
      (-1 : ℤ) ^ #(univ.inversions b) •
        (strictMonoCechComplexπ U P ⟨b ∘ Tuple.sort b, Tuple.strictMono_comp_sort hb⟩ ≫
          P.map (Pi.lift fun j ↦ Pi.π (fun j ↦ U (b j)) (Tuple.sort b j)).op) :=
  (fromStrictMonoCechX_π U P n b).trans (by simp only [hb, ↓reduceDIte])

/-- The factor of the alternating extension at a tuple with a repeated entry vanishes. -/
@[simp, reassoc]
theorem fromStrictMonoCechComplex_app_f_π_of_not_injective (P : Cᵒᵖ ⥤ A) (n : ℕ)
    {b : Fin (n + 1) → ι} (hb : ¬Function.Injective b) :
    ((fromStrictMonoCechComplex U).app P).f n ≫
      Pi.π (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) b = 0 :=
  (fromStrictMonoCechX_π U P n b).trans <| by simp only [hb, ↓reduceDIte]

/-- The alternating extension is a right inverse of the restriction to strictly increasing
tuples. -/
@[reassoc (attr := simp)]
theorem fromStrictMonoCechComplex_comp_toStrictMonoCechComplex :
    fromStrictMonoCechComplex U ≫ toStrictMonoCechComplex (A := A) U = 𝟙 _ := by
  ext P n : 3
  exact fromStrictMonoCechX_comp_toStrictMonoCechX U P n

/-! ### The homotopy equivalence -/

/-- The homotopy identity on Čech cochains in degree `0`. -/
private lemma one_sub_toStrictMonoCechX_comp_zero (P : Cᵒᵖ ⥤ A) :
    𝟙 _ - toStrictMonoCechX U P 0 ≫ fromStrictMonoCechX U P 0 =
      cechD U P 0 ≫ dualMap U P (homotopy 0) := by
  rw [toStrictMonoCechX_comp_fromStrictMonoCechX, ← dualMap_bdry,
    ← dualMap_comp U P (rangeRespecting_bdry 0) (rangeRespecting_homotopy 0), bdry_homotopy_zero,
    dualMap_sub, dualMap_id]

/-- The homotopy identity on Čech cochains in degree `n + 1`. -/
private lemma one_sub_toStrictMonoCechX_comp_succ (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    𝟙 _ - toStrictMonoCechX U P (n + 1) ≫ fromStrictMonoCechX U P (n + 1) =
      cechD U P (n + 1) ≫ dualMap U P (homotopy (n + 1)) +
        dualMap U P (homotopy n) ≫ cechD U P n := by
  rw [toStrictMonoCechX_comp_fromStrictMonoCechX, ← dualMap_bdry, ← dualMap_bdry,
    ← dualMap_comp U P (rangeRespecting_bdry _) (rangeRespecting_homotopy _),
    ← dualMap_comp U P (rangeRespecting_homotopy _) (rangeRespecting_bdry _), ← dualMap_add,
    bdry_homotopy_succ, dualMap_sub, dualMap_id]

/-- The component `Č^{j + 1}(U, P) ⟶ Čʲ(U, P)` of the homotopy between the identity of the Čech
complex and its retraction onto the alternating cochains. -/
private abbrev homotopyX (P : Cᵒᵖ ⥤ A) (j : ℕ) :
    ((cechComplexFunctor U).obj P).X (j + 1) ⟶ ((cechComplexFunctor U).obj P).X j :=
  dualMap U P (homotopy j)

/-- The homotopy between the identity of `Č(U, P)` and the composite of the restriction to the
strictly increasing tuples with the alternating extension. In degree `n + 1` it is dual to the
chain homotopy which sends a tuple `b` to the cone with vertex `b 0` on
`b - alt b - homotopy (∂ b)`. -/
private def homotopyIdCompFromStrictMono (P : Cᵒᵖ ⥤ A) :
    Homotopy (𝟙 ((cechComplexFunctor U).obj P))
      ((toStrictMonoCechComplex U).app P ≫ (fromStrictMonoCechComplex U).app P) :=
  Homotopy.equivSubZero.symm <| (Homotopy.ofEq <| by
    ext n : 1
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f]
    cases n with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (rfl : (ComplexShape.up ℕ).Rel 0 1)
        fun l hl ↦ Nat.succ_ne_zero l hl, eqToHom_refl, Category.id_comp]
      exact one_sub_toStrictMonoCechX_comp_zero U P
    | succ n =>
      rw [Homotopy.nullHomotopicMap'_f (c := ComplexShape.up ℕ) (k₂ := n) (k₁ := n + 1)
        (k₀ := n + 2) rfl rfl,
        eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]
      exact one_sub_toStrictMonoCechX_comp_succ U P n).trans
    (Homotopy.nullHomotopy' fun i j (h : (ComplexShape.up ℕ).Rel j i) ↦
      eqToHom (by rw [← (h : j + 1 = i)]) ≫ homotopyX U P j)

/-- **The ordered Čech complex is homotopy equivalent to the Čech complex.** For a family of
objects of a thin category (for instance open subsets of a topological space) indexed by a
linearly ordered type, restricting Čech cochains to the strictly increasing tuples
(`toStrictMonoCechComplex`) is a homotopy equivalence `Č(U, P) ≃ Čₒ(U, P)`, with homotopy inverse
the alternating extension (`fromStrictMonoCechComplex`). No covering condition, finiteness or
coefficient hypothesis beyond preadditivity is needed, and no division by factorials occurs.

Thinness cannot be dropped: in a category with products, the Čech complex of the family with
the single member `X` has the terms `P(X × ⋯ × X)`, whereas its ordered Čech complex is `P(X)`
in degree `0`. -/
def strictMonoCechComplexHomotopyEquiv (P : Cᵒᵖ ⥤ A) :
    HomotopyEquiv ((cechComplexFunctor U).obj P) ((strictMonoCechComplexFunctor U).obj P) where
  hom := (toStrictMonoCechComplex U).app P
  inv := (fromStrictMonoCechComplex U).app P
  homotopyHomInvId := (homotopyIdCompFromStrictMono U P).symm
  homotopyInvHomId := Homotopy.ofEq <| by
    rw [← NatTrans.comp_app, fromStrictMonoCechComplex_comp_toStrictMonoCechComplex,
      NatTrans.id_app]

@[simp]
theorem strictMonoCechComplexHomotopyEquiv_hom (P : Cᵒᵖ ⥤ A) :
    (strictMonoCechComplexHomotopyEquiv U P).hom = (toStrictMonoCechComplex U).app P :=
  (rfl)

@[simp]
theorem strictMonoCechComplexHomotopyEquiv_inv (P : Cᵒᵖ ⥤ A) :
    (strictMonoCechComplexHomotopyEquiv U P).inv = (fromStrictMonoCechComplex U).app P :=
  (rfl)

/-- Restriction to the strictly increasing tuples is a quasi-isomorphism: the ordered Čech complex
has the same cohomology as the Čech complex. -/
instance [CategoryWithHomology A] (P : Cᵒᵖ ⥤ A) :
    QuasiIso ((toStrictMonoCechComplex U).app P) :=
  (strictMonoCechComplexHomotopyEquiv U P).quasiIso_hom

/-- The alternating extension is a quasi-isomorphism. -/
instance [CategoryWithHomology A] (P : Cᵒᵖ ⥤ A) :
    QuasiIso ((fromStrictMonoCechComplex U).app P) :=
  (strictMonoCechComplexHomotopyEquiv U P).quasiIso_inv

end TauCeti.CategoryTheory
