/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Basic

/-!
# The parity grading of the parity-presented signed symmetric algebra

For an internal `ZMod 2`-grading `G` of an `R`-module `V`, the parity-presented signed symmetric
algebra `TauCeti.ParitySignedSym G` is internally `ZMod 2`-graded by total generator parity.
Its piece `TauCeti.paritySignedSymPiece G i` (`i : ZMod 2`) is spanned by products of homogeneous
generators whose parities sum to `i`.

When `V` carries an integer grading `H : InternalGrading R V ℤ`, the algebra equivalence
`TauCeti.SignedSym.parityEquiv H : SignedSym H ≃ₐ[R] ParitySignedSym H.parity` identifies the
coarsened parity grading `TauCeti.parityGrading (signedSymPiece H)` with
`TauCeti.paritySignedSymPiece H.parity`, sending elements of integer input degree `p` into parity
`p` modulo two. No integer lift of `G` is required to use the parity grading on
`TauCeti.ParitySignedSym G`.

The API parallels `TauCeti.signedSymPiece` in
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Grading`.

## Main definitions

* `TauCeti.paritySignedSymPiece`: the parity-`i` submodule of `TauCeti.ParitySignedSym G`.
* `TauCeti.ParitySignedSym.gradedLift` and `TauCeti.ParitySignedSym.gradedMap`: the graded
  universal property and functoriality of the parity presentation.
* `TauCeti.SignedSym.gradedToParity` and `TauCeti.SignedSym.gradedOfParity`: the mutually inverse
  graded algebra maps between `parityGrading (signedSymPiece H)` and
  `paritySignedSymPiece H.parity`.

## Main results

* `TauCeti.ParitySignedSym.homogeneous_induction`: induction on parity-homogeneous elements.
* `TauCeti.isInternal_paritySignedSymPiece` and the `GradedAlgebra (paritySignedSymPiece G)`
  instance.
* `TauCeti.SignedSym.parityEquiv_mem_paritySignedSymPiece` and
  `TauCeti.SignedSym.map_parityEquiv_parityGrading`: `SignedSym.parityEquiv` sends degree `p`
  into parity `p` modulo two and identifies the parity pieces.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
* Y. Eliashberg, A. Givental, and H. Hofer, *Introduction to symplectic field theory*, Section 1.9.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

/-- The parity-`i` piece of `ParitySignedSym G`: the `R`-submodule spanned by products of
homogeneous generators whose parities sum to `i`. The empty product has parity `0`. -/
def paritySignedSymPiece (G : InternalGrading R V (ZMod 2)) (i : ZMod 2) :
    Submodule R (ParitySignedSym G) :=
  Submodule.span R {a | ∃ (n : ℕ) (d : Fin n → ZMod 2) (x : Fin n → V),
    (∀ k, x k ∈ G.piece (d k)) ∧ ∑ k, d k = i ∧
      a = (List.ofFn fun k => ParitySignedSym.generator G (x k)).prod}

section Pieces

variable (G : InternalGrading R V (ZMod 2))

/-- The parity-`i` piece is the span of words in homogeneous generators of total parity `i`. -/
theorem paritySignedSymPiece_def (i : ZMod 2) :
    paritySignedSymPiece G i =
      Submodule.span R {a | ∃ (n : ℕ) (d : Fin n → ZMod 2) (x : Fin n → V),
        (∀ k, x k ∈ G.piece (d k)) ∧ ∑ k, d k = i ∧
          a = (List.ofFn fun k => ParitySignedSym.generator G (x k)).prod} := (rfl)

variable {G} in
/-- A submodule containing every word of homogeneous generators of total parity `i` contains
`paritySignedSymPiece G i`. -/
theorem paritySignedSymPiece_le {i : ZMod 2} {C : Submodule R (ParitySignedSym G)}
    (h : ∀ (n : ℕ) (d : Fin n → ZMod 2) (x : Fin n → V),
      (∀ k, x k ∈ G.piece (d k)) → ∑ k, d k = i →
        (List.ofFn fun k => ParitySignedSym.generator G (x k)).prod ∈ C) :
    paritySignedSymPiece G i ≤ C := by
  rw [paritySignedSymPiece_def, Submodule.span_le]
  rintro _ ⟨n, d, x, hx, hd, rfl⟩
  exact h n d x hx hd

/-- A product of homogeneous generators lies in the piece of the sum of their parities. -/
theorem list_prod_generator_mem_paritySignedSymPiece {n : ℕ} (d : Fin n → ZMod 2)
    (x : Fin n → V) (hx : ∀ k, x k ∈ G.piece (d k)) :
    (List.ofFn fun k => ParitySignedSym.generator G (x k)).prod ∈
      paritySignedSymPiece G (∑ k, d k) :=
  Submodule.subset_span ⟨n, d, x, hx, rfl, rfl⟩

/-- The quotient class of a pure tensor word of homogeneous letters lies in the piece of the sum
of their parities. -/
theorem quotient_tprod_mem_paritySignedSymPiece {n : ℕ} (d : Fin n → ZMod 2)
    (x : Fin n → V) (hx : ∀ k, x k ∈ G.piece (d k)) :
    ParitySignedSym.quotient G (TensorAlgebra.tprod R V n x) ∈
      paritySignedSymPiece G (∑ k, d k) := by
  rw [ParitySignedSym.quotient_tprod]
  exact list_prod_generator_mem_paritySignedSymPiece G d x hx

/-- A homogeneous generator retains its parity in `ParitySignedSym G`. -/
theorem generator_mem_paritySignedSymPiece {i : ZMod 2} {x : V} (hx : x ∈ G.piece i) :
    ParitySignedSym.generator G x ∈ paritySignedSymPiece G i := by
  simpa only [Fin.sum_univ_one, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one] using
    list_prod_generator_mem_paritySignedSymPiece G (fun _ : Fin 1 => i)
      (fun _ : Fin 1 => x) fun _ => hx

namespace ParitySignedSym

/-- Induction on parity-homogeneous expressions in `ParitySignedSym G`, tracking total parity. -/
@[elab_as_elim]
theorem homogeneous_induction {P : ZMod 2 → ParitySignedSym G → Prop}
    (one : P 0 1)
    (generator : ∀ (i : ZMod 2) (x : V), x ∈ G.piece i → P i (ParitySignedSym.generator G x))
    (mul : ∀ (i j : ZMod 2) (a b : ParitySignedSym G), P i a → P j b → P (i + j) (a * b))
    (zero : ∀ i, P i 0)
    (add : ∀ (i : ZMod 2) (a b : ParitySignedSym G), P i a → P i b → P i (a + b))
    (smul : ∀ (i : ZMod 2) (r : R) (a : ParitySignedSym G), P i a → P i (r • a))
    {i : ZMod 2} {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G i) : P i a := by
  rw [paritySignedSymPiece_def] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, d, x, hx, rfl, rfl⟩ := ha
    induction n with
    | zero => simpa using one
    | succ n ih =>
      simpa only [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons] using
        mul (d 0) (∑ k : Fin n, d k.succ) _ _ (generator _ _ (hx 0))
          (ih (fun k => d k.succ) (fun k => x k.succ) fun k => hx k.succ)
  | zero => exact zero i
  | add a b _ _ ha hb => exact add i a b ha hb
  | smul r a _ ha => exact smul i r a ha

end ParitySignedSym

private theorem generator_mul_mem_paritySignedSymPiece {i j : ZMod 2} {x : V}
    {b : ParitySignedSym G} (hx : x ∈ G.piece i) (hb : b ∈ paritySignedSymPiece G j) :
    ParitySignedSym.generator G x * b ∈ paritySignedSymPiece G (i + j) := by
  refine paritySignedSymPiece_le
    (C := (paritySignedSymPiece G (i + j)).comap
      (LinearMap.mulLeft R (ParitySignedSym.generator G x)))
    (fun n d y hy hd => ?_) hb
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply, ← hd]
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, List.prod_cons]
    using list_prod_generator_mem_paritySignedSymPiece G (Fin.cons i d) (Fin.cons x y)
      (Fin.cases hx hy)

/-- Multiplication in `ParitySignedSym G` adds parities. -/
instance : SetLike.GradedMonoid (paritySignedSymPiece G) where
  one_mem := by
    simpa using list_prod_generator_mem_paritySignedSymPiece G Fin.elim0 Fin.elim0
      fun k => k.elim0
  mul_mem i j a b ha hb := by
    refine ParitySignedSym.homogeneous_induction G
      (P := fun i a => ∀ {j : ZMod 2} {b : ParitySignedSym G},
        b ∈ paritySignedSymPiece G j → a * b ∈ paritySignedSymPiece G (i + j))
      (fun hb => by simpa using hb)
      (fun i x hx _ _ hb => generator_mul_mem_paritySignedSymPiece G hx hb)
      (fun i k a c ha hc _ _ hb => by rw [mul_assoc, add_assoc]; exact ha (hc hb))
      (fun _ _ _ _ => by simp)
      (fun _ _ _ ha hc _ _ hb => by rw [add_mul]; exact add_mem (ha hb) (hc hb))
      (fun _ r _ ha _ _ hb => by rw [smul_mul_assoc]; exact Submodule.smul_mem _ r (ha hb))
      ha hb

end Pieces

namespace SignedSym

variable (G : InternalGrading R V ℤ)

/-- `SignedSym.parityEquiv` sends elements of integer input degree `p` into the piece of parity
`p` modulo two. -/
theorem parityEquiv_mem_paritySignedSymPiece {p : ℤ} {a : SignedSym G}
    (ha : a ∈ signedSymPiece G p) :
    parityEquiv G a ∈ paritySignedSymPiece G.parity p := by
  refine homogeneous_induction G
    (P := fun p a => parityEquiv G a ∈ paritySignedSymPiece G.parity p)
    (by simpa using SetLike.GradedOne.one_mem (A := paritySignedSymPiece G.parity))
    (fun p x hx => by
      rw [parityEquiv_generator]
      exact generator_mem_paritySignedSymPiece G.parity
        (by simpa only [InternalGrading.parity_piece] using mem_parityGrading_of_mem hx))
    (fun p q a b ha hb => by
      rw [map_mul, Int.cast_add]
      exact SetLike.mul_mem_graded ha hb)
    (fun p => by simp)
    (fun p a b ha hb => by rw [map_add]; exact add_mem ha hb)
    (fun p r a ha => by rw [map_smul]; exact Submodule.smul_mem _ r ha)
    ha

/-- The image of the integer degree-`p` piece under `SignedSym.parityEquiv` lies in the piece of
parity `p` modulo two. -/
theorem map_parityEquiv_signedSymPiece_le (p : ℤ) :
    (signedSymPiece G p).map (parityEquiv G).toLinearMap ≤ paritySignedSymPiece G.parity p := by
  rintro _ ⟨a, ha, rfl⟩
  exact parityEquiv_mem_paritySignedSymPiece G ha

private theorem parityEquiv_mem_of_mem_parityGrading {i : ZMod 2} {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) i) :
    parityEquiv G a ∈ paritySignedSymPiece G.parity i := by
  refine coarsenGrading_induction
    (motive := fun a => parityEquiv G a ∈ paritySignedSymPiece G.parity i)
    ha (fun p hp y hy => ?_) (by simp) fun x y hx hy => by rw [map_add]; exact add_mem hx hy
  rw [← hp]
  exact parityEquiv_mem_paritySignedSymPiece G hy

private theorem parityEquiv_symm_mem_parityGrading {i : ZMod 2}
    {b : ParitySignedSym G.parity} (hb : b ∈ paritySignedSymPiece G.parity i) :
    (parityEquiv G).symm b ∈ parityGrading (signedSymPiece G) i := by
  have hgen := (isHomogeneous_signedSymGenerator G).coarsenGrading (Int.castAddHom (ZMod 2))
  refine ParitySignedSym.homogeneous_induction G.parity
    (P := fun i b => (parityEquiv G).symm b ∈ parityGrading (signedSymPiece G) i)
    (by simpa using SetLike.GradedOne.one_mem (A := parityGrading (signedSymPiece G)))
    (fun i x hx => by
      rw [parityEquiv_symm_generator]
      rw [InternalGrading.parity_piece] at hx
      simpa only [map_zero, add_zero] using hgen.map_mem hx)
    (fun i j a c ha hc => by rw [map_mul]; exact SetLike.mul_mem_graded ha hc)
    (fun _ => by simp)
    (fun _ a c ha hc => by rw [map_add]; exact add_mem ha hc)
    (fun _ r a ha => by rw [map_smul]; exact Submodule.smul_mem _ r ha)
    hb

/-- `SignedSym.parityEquiv` identifies the coarsened parity pieces of `SignedSym G` with the
parity pieces of `ParitySignedSym G.parity`. -/
@[simp]
theorem map_parityEquiv_parityGrading (i : ZMod 2) :
    (parityGrading (signedSymPiece G) i).map (parityEquiv G).toLinearMap =
      paritySignedSymPiece G.parity i := by
  refine le_antisymm ?_ fun b hb =>
    ⟨(parityEquiv G).symm b, parityEquiv_symm_mem_parityGrading G hb,
      (parityEquiv G).apply_symm_apply b⟩
  rintro _ ⟨a, ha, rfl⟩
  exact parityEquiv_mem_of_mem_parityGrading G ha

/-- The inverse of `SignedSym.parityEquiv` maps each parity piece of `ParitySignedSym G.parity`
onto the coarsened parity piece of `SignedSym G`. -/
@[simp]
theorem map_parityEquiv_symm_paritySignedSymPiece (i : ZMod 2) :
    (paritySignedSymPiece G.parity i).map (parityEquiv G).symm.toLinearMap =
      parityGrading (signedSymPiece G) i := by
  refine le_antisymm ?_ fun a ha =>
    ⟨parityEquiv G a, parityEquiv_mem_of_mem_parityGrading G ha,
      (parityEquiv G).symm_apply_apply a⟩
  rintro _ ⟨b, hb, rfl⟩
  exact parityEquiv_symm_mem_parityGrading G hb

/-- `SignedSym.parityEquiv` reflects and preserves membership in the parity pieces. -/
@[simp]
theorem mem_paritySignedSymPiece_parityEquiv_iff {i : ZMod 2} {a : SignedSym G} :
    parityEquiv G a ∈ paritySignedSymPiece G.parity i ↔
      a ∈ parityGrading (signedSymPiece G) i :=
  ⟨fun h => by
    simpa only [AlgEquiv.symm_apply_apply] using parityEquiv_symm_mem_parityGrading G h,
    parityEquiv_mem_of_mem_parityGrading G⟩

/-- The inverse of `SignedSym.parityEquiv` reflects and preserves membership in the parity
pieces. -/
@[simp]
theorem mem_parityGrading_parityEquiv_symm_iff {i : ZMod 2} {b : ParitySignedSym G.parity} :
    (parityEquiv G).symm b ∈ parityGrading (signedSymPiece G) i ↔
      b ∈ paritySignedSymPiece G.parity i :=
  ⟨fun h => by
    simpa only [AlgEquiv.apply_symm_apply] using parityEquiv_mem_of_mem_parityGrading G h,
    parityEquiv_symm_mem_parityGrading G⟩

end SignedSym

section Internality

private def intLiftPiece (G : InternalGrading R V (ZMod 2)) (p : ℤ) : Submodule R V :=
  if p = 0 then G.piece 0 else if p = 1 then G.piece 1 else ⊥

private theorem intLiftPiece_eq_zero_of_sum_eq_zero (G : InternalGrading R V (ZMod 2))
    {s : Finset ℤ} {x : ℤ → V}
    (hsum : ∑ p ∈ s, x p = 0) {q q' : ℤ} {i i' : ZMod 2} (hq : q ∈ s)
    (hqi : x q ∈ G.piece i) (hqq' : ∀ p ∈ s, p ≠ q → p ≠ q' → x p = 0)
    (hq'i' : q' ∈ s → x q' ∈ G.piece i') (hii' : i' ≠ i) : x q = 0 := by
  let π : V →ₗ[R] V :=
    (G.piece i).subtype ∘ₗ DirectSum.component R (ZMod 2) (fun j => G.piece j) i ∘ₗ
      (DirectSum.decomposeLinearEquiv G.piece).toLinearMap
  have hπ (v : V) : π v = (DirectSum.decompose G.piece v i : V) := rfl
  have h := congrArg π hsum
  rw [map_sum, map_zero, Finset.sum_eq_single q] at h
  · rwa [hπ, DirectSum.decompose_of_mem_same _ hqi] at h
  · intro p hp hpq
    by_cases hpq' : p = q'
    · subst hpq'
      rw [hπ]
      exact DirectSum.decompose_of_mem_ne _ (hq'i' hp) hii'
    · simp [hqq' p hp hpq hpq']
  · exact fun hnot => (hnot hq).elim

private theorem isInternal_intLiftPiece (G : InternalGrading R V (ZMod 2)) :
    DirectSum.IsInternal (intLiftPiece G) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s x hx hsum q hq
    have hbot : ∀ p ∈ s, p ≠ 0 → p ≠ 1 → x p = 0 := fun p hp h0 h1 => by
      simpa [intLiftPiece, h0, h1] using hx p hp
    by_cases hq0 : q = 0
    · subst hq0
      exact intLiftPiece_eq_zero_of_sum_eq_zero G hsum hq
        (by simpa [intLiftPiece] using hx 0 hq) hbot
        (fun hp => by simpa [intLiftPiece] using hx 1 hp) (by decide : (1 : ZMod 2) ≠ 0)
    · by_cases hq1 : q = 1
      · subst hq1
        exact intLiftPiece_eq_zero_of_sum_eq_zero G hsum hq
          (by simpa [intLiftPiece] using hx 1 hq)
          (fun p hp hp1 hp0 => hbot p hp hp0 hp1)
          (fun hp => by simpa [intLiftPiece] using hx 0 hp) (by decide : (0 : ZMod 2) ≠ 1)
      · exact hbot q hq hq0 hq1
  · refine top_unique ?_
    rw [← G.isInternal.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    match i with
    | 0 => exact le_iSup_of_le (0 : ℤ) (by simp [intLiftPiece])
    | 1 => exact le_iSup_of_le (1 : ℤ) (by simp [intLiftPiece])

private noncomputable def intLift (G : InternalGrading R V (ZMod 2)) : InternalGrading R V ℤ where
  piece := intLiftPiece G
  isInternal := isInternal_intLiftPiece G

private theorem intLift_parity (G : InternalGrading R V (ZMod 2)) : (intLift G).parity = G := by
  ext i x
  rw [InternalGrading.parity_piece]
  match i with
  | 0 =>
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · refine parityGrading_le_iff.2 (fun n hn => ?_) hx
      have hn1 : n ≠ 1 := by rintro rfl; exact (by decide : ((1 : ℤ) : ZMod 2) ≠ 0) hn
      by_cases hn0 : n = 0
      · subst hn0; simp [intLift, intLiftPiece]
      · simp [intLift, intLiftPiece, hn0, hn1]
    · have hx0 : x ∈ (intLift G).piece 0 := by simpa [intLift, intLiftPiece] using hx
      exact mem_parityGrading_of_mem hx0
  | 1 =>
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · refine parityGrading_le_iff.2 (fun n hn => ?_) hx
      have hn0 : n ≠ 0 := by rintro rfl; exact (by decide : ((0 : ℤ) : ZMod 2) ≠ 1) hn
      by_cases hn1 : n = 1
      · subst hn1; simp [intLift, intLiftPiece]
      · simp [intLift, intLiftPiece, hn0, hn1]
    · have hx1 : x ∈ (intLift G).piece 1 := by simpa [intLift, intLiftPiece] using hx
      exact mem_parityGrading_of_mem hx1

private theorem map_congr_refl_paritySignedSymPiece {G H : InternalGrading R V (ZMod 2)}
    (hGH : G = H) (i : ZMod 2) :
    (paritySignedSymPiece G i).map
      (ParitySignedSym.congr G H (LinearEquiv.refl R V)
        (hGH ▸ LinearMap.isHomogeneous_id G.piece)).toLinearMap =
      paritySignedSymPiece H i := by
  subst hGH
  ext a
  simp

/-- The parity pieces of `ParitySignedSym G` form an internal direct sum. -/
theorem isInternal_paritySignedSymPiece (G : InternalGrading R V (ZMod 2)) :
    DirectSum.IsInternal (paritySignedSymPiece G) := by
  let H := intLift G
  let c : ParitySignedSym H.parity ≃ₐ[R] ParitySignedSym G :=
    ParitySignedSym.congr H.parity G (LinearEquiv.refl R V)
      (intLift_parity G ▸ LinearMap.isHomogeneous_id H.parity.piece)
  let e : SignedSym H ≃ₐ[R] ParitySignedSym G := (SignedSym.parityEquiv H).trans c
  have hpiece :
      ((InternalGrading.ofDecomposition (parityGrading (signedSymPiece H))).map
        e.toLinearEquiv).piece = paritySignedSymPiece G := by
    funext i
    rw [InternalGrading.map_piece, InternalGrading.ofDecomposition_piece]
    have he : e.toLinearEquiv.toLinearMap =
        c.toLinearMap ∘ₗ (SignedSym.parityEquiv H).toLinearMap := rfl
    rw [he, Submodule.map_comp, SignedSym.map_parityEquiv_parityGrading H i]
    exact map_congr_refl_paritySignedSymPiece (intLift_parity G) i
  rw [← hpiece]
  exact ((InternalGrading.ofDecomposition (parityGrading (signedSymPiece H))).map
    e.toLinearEquiv).isInternal

/-- `ParitySignedSym G` is internally `ZMod 2`-graded by total generator parity. -/
noncomputable instance (G : InternalGrading R V (ZMod 2)) :
    GradedAlgebra (paritySignedSymPiece G) :=
  (isInternal_paritySignedSymPiece G).gradedAlgebra

end Internality

section Generator

variable (G : InternalGrading R V (ZMod 2))

/-- The canonical generator map has parity degree `0`. -/
theorem isHomogeneous_paritySignedSymGenerator :
    LinearMap.IsHomogeneous (ParitySignedSym.generator G) G.piece (paritySignedSymPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx => by
    simpa only [add_zero] using generator_mem_paritySignedSymPiece G hx

/-- The parity-`i` component of a generator is the generator of its parity-`i` component. -/
@[simp]
theorem decompose_paritySignedSymGenerator (x : V) (i : ZMod 2) :
    (DirectSum.decompose (paritySignedSymPiece G) (ParitySignedSym.generator G x) i :
      ParitySignedSym G) =
      ParitySignedSym.generator G (DirectSum.decompose G.piece x i : V) := by
  have h := (isHomogeneous_paritySignedSymGenerator G).map_decompose i x
  rw [add_zero] at h
  exact h.symm

end Generator

namespace ParitySignedSym

section GradedHomExt

variable {G : InternalGrading R V (ZMod 2)}
variable {A : Type w} [Semiring A] [Algebra R A] {𝒜 : ZMod 2 → Submodule R A} [GradedAlgebra 𝒜]

/-- Graded algebra maps out of `ParitySignedSym G` are determined by their values on generators. -/
@[ext]
theorem gradedHom_ext {φ ψ : paritySignedSymPiece G →ₐᵍ[R] 𝒜}
    (h : ∀ x, φ (generator G x) = ψ (generator G x)) : φ = ψ := by
  have hφψ : φ.toAlgHom = ψ.toAlgHom := hom_ext G h
  exact GradedAlgHom.ext fun a => DFunLike.congr_fun hφψ a

end GradedHomExt

section GradedLift

variable (G : InternalGrading R V (ZMod 2))
variable {A : Type w} [Ring A] [Algebra R A] (𝒜 : ZMod 2 → Submodule R A)

/-- `ParitySignedSym.lift` preserves parity when its generator assignment does. -/
theorem isHomogeneous_lift [SetLike.GradedMonoid 𝒜] (f : V →ₗ[R] A)
    (hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      f x * f y = ((-1 : ℤˣ) ^ (i * j)) • (f y * f x))
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) :
    LinearMap.IsHomogeneous (lift G f hr).toLinearMap (paritySignedSymPiece G) 𝒜 0 := by
  refine LinearMap.isHomogeneous_def.2 fun i a ha => ?_
  rw [add_zero]
  refine homogeneous_induction G (P := fun i a => lift G f hr a ∈ 𝒜 i)
    (by simpa only [map_one] using SetLike.GradedOne.one_mem (A := 𝒜))
    (fun j x hx => by simpa only [lift_generator, add_zero] using hf.map_mem hx)
    (fun j k b c hb hc => by rw [map_mul]; exact SetLike.mul_mem_graded hb hc)
    (fun _ => by simp)
    (fun _ b c hb hc => by rw [map_add]; exact add_mem hb hc)
    (fun _ r b hb => by rw [map_smul]; exact Submodule.smul_mem _ r hb)
    ha

variable [GradedAlgebra 𝒜]

/-- The graded universal extension of a parity-preserving generator assignment satisfying the
parity sign rule. Its underlying algebra map is `ParitySignedSym.lift`. -/
noncomputable def gradedLift (f : V →ₗ[R] A)
    (hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      f x * f y = ((-1 : ℤˣ) ^ (i * j)) • (f y * f x))
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) : paritySignedSymPiece G →ₐᵍ[R] 𝒜 where
  toAlgHom := lift G f hr
  map_mem hx := by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using (isHomogeneous_lift G 𝒜 f hr hf).map_mem hx

@[simp]
theorem gradedLift_toAlgHom (f : V →ₗ[R] A) (hr hf) :
    (gradedLift G 𝒜 f hr hf).toAlgHom = lift G f hr := (rfl)

/-- The graded lift extends the given assignment on every generator. -/
@[simp]
theorem gradedLift_generator (f : V →ₗ[R] A) (hr hf) (x : V) :
    gradedLift G 𝒜 f hr hf (generator G x) = f x :=
  lift_generator G f hr x

/-- The parity-preserving extension is unique among graded algebra maps. -/
theorem gradedLift_unique (f : V →ₗ[R] A) (hr hf) (φ : paritySignedSymPiece G →ₐᵍ[R] 𝒜)
    (hφ : ∀ x, φ (generator G x) = f x) : φ = gradedLift G 𝒜 f hr hf := by
  apply gradedHom_ext
  simpa only [gradedLift_generator] using hφ

end GradedLift

section GradedMap

variable (G : InternalGrading R V (ZMod 2))
variable {W : Type*} [AddCommGroup W] [Module R W] (H : InternalGrading R W (ZMod 2))

/-- Functorial maps induced by parity-preserving linear maps preserve the parity grading. -/
theorem isHomogeneous_map (f : V →ₗ[R] W) (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    LinearMap.IsHomogeneous (map G H f hf).toLinearMap
      (paritySignedSymPiece G) (paritySignedSymPiece H) 0 := by
  have hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      (generator H).comp f x * (generator H).comp f y =
        ((-1 : ℤˣ) ^ (i * j)) • ((generator H).comp f y * (generator H).comp f x) := by
    intro i j x y hx hy
    exact generator_mul_generator H
      (by simpa only [add_zero] using hf.map_mem hx)
      (by simpa only [add_zero] using hf.map_mem hy)
  rw [lift_unique G ((generator H).comp f) hr (map G H f hf) (map_generator G H f hf)]
  apply isHomogeneous_lift
  simpa only [add_zero] using (isHomogeneous_paritySignedSymGenerator H).comp hf

/-- A parity-preserving linear map induces a graded algebra map of parity presentations.
Its underlying algebra map is `ParitySignedSym.map`. -/
noncomputable def gradedMap (f : V →ₗ[R] W) (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    paritySignedSymPiece G →ₐᵍ[R] paritySignedSymPiece H where
  toAlgHom := map G H f hf
  map_mem hx := by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using (isHomogeneous_map G H f hf).map_mem hx

@[simp]
theorem gradedMap_toAlgHom (f : V →ₗ[R] W) (hf) :
    (gradedMap G H f hf).toAlgHom = map G H f hf := (rfl)

@[simp]
theorem gradedMap_apply (f : V →ₗ[R] W) (hf) (a : ParitySignedSym G) :
    gradedMap G H f hf a = map G H f hf a := (rfl)

/-- The graded algebra map induced by the identity is the identity. -/
@[simp]
theorem gradedMap_id :
    gradedMap G G LinearMap.id (LinearMap.isHomogeneous_id G.piece) =
      GradedAlgHom.id R (paritySignedSymPiece G) := by
  ext x
  simp

variable {U : Type*} [AddCommGroup U] [Module R U]

/-- Graded algebra maps of parity presentations respect composition. -/
theorem gradedMap_comp (K : InternalGrading R U (ZMod 2)) (f : V →ₗ[R] W) (g : W →ₗ[R] U)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0)
    (hg : LinearMap.IsHomogeneous g H.piece K.piece 0) :
    gradedMap G K (g.comp f) (by simpa using hg.comp hf) =
      (gradedMap H K g hg).comp (gradedMap G H f hf) := by
  ext x
  simp

end GradedMap

end ParitySignedSym

namespace SignedSym

variable (G : InternalGrading R V ℤ)

/-- `SignedSym.parityEquiv` is parity-homogeneous of degree `0`. -/
theorem isHomogeneous_parityEquiv :
    LinearMap.IsHomogeneous (parityEquiv G).toLinearMap
      (parityGrading (signedSymPiece G)) (paritySignedSymPiece G.parity) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha => by
    simpa only [add_zero, AlgEquiv.toLinearMap_apply, mem_paritySignedSymPiece_parityEquiv_iff]
      using ha

/-- The inverse of `SignedSym.parityEquiv` is parity-homogeneous of degree `0`. -/
theorem isHomogeneous_parityEquiv_symm :
    LinearMap.IsHomogeneous (parityEquiv G).symm.toLinearMap
      (paritySignedSymPiece G.parity) (parityGrading (signedSymPiece G)) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hb => by
    simpa only [add_zero, AlgEquiv.toLinearMap_apply, mem_parityGrading_parityEquiv_symm_iff]
      using hb

/-- `SignedSym.parityEquiv` commutes with parity decomposition. -/
@[simp]
theorem decompose_parityEquiv (a : SignedSym G) (i : ZMod 2) :
    (DirectSum.decompose (paritySignedSymPiece G.parity) (parityEquiv G a) i :
      ParitySignedSym G.parity) =
      parityEquiv G (DirectSum.decompose (parityGrading (signedSymPiece G)) a i : SignedSym G) := by
  have h := (isHomogeneous_parityEquiv G).map_decompose i a
  rw [add_zero] at h
  exact h.symm

/-- The inverse of `SignedSym.parityEquiv` commutes with parity decomposition. -/
@[simp]
theorem decompose_parityEquiv_symm (b : ParitySignedSym G.parity) (i : ZMod 2) :
    (DirectSum.decompose (parityGrading (signedSymPiece G)) ((parityEquiv G).symm b) i :
      SignedSym G) =
      (parityEquiv G).symm
        (DirectSum.decompose (paritySignedSymPiece G.parity) b i : ParitySignedSym G.parity) := by
  have h := (isHomogeneous_parityEquiv_symm G).map_decompose i b
  rw [add_zero] at h
  exact h.symm

/-- `SignedSym.parityEquiv` bundled as a graded algebra map from the coarsened parity grading of
`SignedSym G` to `paritySignedSymPiece G.parity`. -/
noncomputable def gradedToParity :
    parityGrading (signedSymPiece G) →ₐᵍ[R] paritySignedSymPiece G.parity where
  toAlgHom := (parityEquiv G).toAlgHom
  map_mem ha := (mem_paritySignedSymPiece_parityEquiv_iff G).2 ha

@[simp]
theorem gradedToParity_toAlgHom :
    (gradedToParity G).toAlgHom = (parityEquiv G).toAlgHom := (rfl)

@[simp]
theorem gradedToParity_apply (a : SignedSym G) :
    gradedToParity G a = parityEquiv G a := (rfl)

/-- The inverse of `SignedSym.parityEquiv` bundled as a graded algebra map. -/
noncomputable def gradedOfParity :
    paritySignedSymPiece G.parity →ₐᵍ[R] parityGrading (signedSymPiece G) where
  toAlgHom := (parityEquiv G).symm.toAlgHom
  map_mem hb := (mem_parityGrading_parityEquiv_symm_iff G).2 hb

@[simp]
theorem gradedOfParity_toAlgHom :
    (gradedOfParity G).toAlgHom = (parityEquiv G).symm.toAlgHom := (rfl)

@[simp]
theorem gradedOfParity_apply (b : ParitySignedSym G.parity) :
    gradedOfParity G b = (parityEquiv G).symm b := (rfl)

@[simp]
theorem gradedToParity_comp_gradedOfParity :
    (gradedToParity G).comp (gradedOfParity G) =
      GradedAlgHom.id R (paritySignedSymPiece G.parity) := by
  ext x
  simp

@[simp]
theorem gradedOfParity_comp_gradedToParity :
    (gradedOfParity G).comp (gradedToParity G) =
      GradedAlgHom.id R (parityGrading (signedSymPiece G)) := by
  ext a
  exact (parityEquiv G).symm_apply_apply a

end SignedSym

end TauCeti
