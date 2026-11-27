/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.ParityFold
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Alternating.Basic
import TauCeti.LinearAlgebra.Pi

/-!
# The torsion of the parity fold of a bounded complex

Let `C` be a `ℤ`-graded chain complex of vector spaces, vanishing outside a finite set `S` of
degrees, and let `ChainComplex.parityFold C S` be its parity fold, the two-periodic complex whose
term of parity `r` is the product `∏ C.X j` over the degrees `j ∈ S` of parity `r`
(`TauCeti.Algebra.Homology.Periodic.ParityFold`). This is how the finite parity complex of a
Floer–Novikov theory whose relative grading is an integer grading relates to that integer complex.

Over a field, give each `C.X j` a basis `c j`, and the term of parity `r` of the fold the basis made
of the bases `c j` of the degrees of parity `r`, in an order `e r` (`ChainComplex.parityFoldBasis`).
Then the torsion `HomologicalComplex.parityTorsion` of the based two-periodic complex is, up to
sign, the Reidemeister torsion `HomologicalComplex.reidemeisterTorsion` of `C`
(`ChainComplex.homologicalComplex_parityTorsion_parityFold_eq_reidemeisterTorsion_or_eq_neg`).
Both torsions are made of the same brackets: the torsion of `C` is the alternating product
`∏ⱼ [bⱼ sⱼ₋₁ / cⱼ] ^ ((-1) ^ (j + 1))`, the brackets of odd degrees in the numerator, and the
torsion of the fold is the bracket of its odd term over the bracket of its even term. Taking the
bases of the boundaries and the lifts of the fold to be those of `C`, each concentrated in its
degree, the vectors whose determinant is the bracket of the fold in parity `r` are those of the
brackets of `C` in the degrees of parity `r`, each concentrated in its degree, in another order. The
determinant of such a block family in the product basis is the product of the determinants of the
blocks (`Module.Basis.det_pi_single`), and the reordering contributes a sign. The sign depends on
the orders `e` and on the dimensions of the boundaries, and torsions of parity complexes are in any
case only defined up to sign when their bases come from unordered generators; reordering the bases
changes the torsion of the fold by the signs of the permutations
(`HomologicalComplex.parityTorsion_reindex`).

## Main definitions

* `ChainComplex.parityFoldBasis S c e`: the bases of the parity fold made of the bases `c j` of the
  terms of `C`.

## Main results

* `ChainComplex.homologicalComplex_parityTorsion_parityFold_eq_reidemeisterTorsion_or_eq_neg`:
  the torsion of the based parity fold is, up to sign, the Reidemeister torsion of `C`.

## References

* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), §2.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic
  tori, I*, J. Symplectic Geom. 3 (2005), §2.
* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
-/

public section

noncomputable section

open CategoryTheory Limits Module

namespace ChainComplex

section BoundaryBasis

open HomologicalComplex (chosenBoundaryBasis chosenBoundaryLift chosenBoundaryLift_spec)

variable {F : Type*} [Field F] {C : ChainComplex (ModuleCat F) ℤ} {S : Finset ℤ}
  {n : ℤ → ℕ}
  (c : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The boundaries of `C` vanish in a degree outside `S`. -/
private theorem finrank_range_d_eq_zero_of_notMem (hS : ∀ j ∉ S, IsZero (C.X j)) {i k : ℤ}
    (hk : k ∉ S) : finrank F (LinearMap.range (C.d i k).hom) = 0 := by
  have := ModuleCat.subsingleton_of_isZero (hS k hk)
  exact Module.finrank_zero_of_subsingleton

/-- The boundaries of `C` vanish out of a degree outside `S`. -/
private theorem finrank_range_d_eq_zero_of_notMem_left (hS : ∀ j ∉ S, IsZero (C.X j))
    {i k : ℤ} (hi : i ∉ S) : finrank F (LinearMap.range (C.d i k).hom) = 0 := by
  have := ModuleCat.subsingleton_of_isZero (hS i hi)
  rw [LinearMap.range_eq_bot.2 (Subsingleton.elim _ _), finrank_bot]

variable (S) in
/-- The chosen lifts of the boundaries of `C` out of the degrees of parity `r`, as vectors of the
parity fold concentrated in one degree. -/
private def foldLift (r : ZMod 2)
    (t : Σ i : parityFoldDegrees S r, Fin (finrank F (LinearMap.range (C.d i (i - 1)).hom))) :
    ∀ j : parityFoldDegrees S r, C.X j :=
  Pi.single t.fst (chosenBoundaryLift C c t.fst (t.fst - 1) t.snd)

variable (S) in
/-- The images in the parity fold of the chosen lifts `foldLift`: the chosen bases of the
boundaries of `C` into the degrees of parity `s`, as vectors concentrated in one degree. -/
private def foldBoundary (r s : ZMod 2)
    (t : Σ i : parityFoldDegrees S r, Fin (finrank F (LinearMap.range (C.d i (i - 1)).hom))) :
    ∀ j : parityFoldDegrees S s, C.X j :=
  ((C.parityFold S).d r s).hom (foldLift S c r t)

/-- The components of the vectors `foldBoundary`. -/
private theorem foldBoundary_apply {r s : ZMod 2} (i : parityFoldDegrees S r)
    (l : Fin (finrank F (LinearMap.range (C.d i (i - 1)).hom))) (k : parityFoldDegrees S s) :
    foldBoundary S c r s ⟨i, l⟩ k = (C.d i k).hom (chosenBoundaryLift C c i (i - 1) l) :=
  parityFold_d_single_apply C S i _ k

/-- The image of a chosen lift is the chosen boundary basis vector, concentrated in the degree
below. -/
private theorem foldBoundary_eq {r s : ZMod 2} (i : parityFoldDegrees S r)
    (k : parityFoldDegrees S s) (hik : (i : ℤ) = k + 1)
    (l : Fin (finrank F (LinearMap.range (C.d i (i - 1)).hom))) :
    foldBoundary S c r s ⟨i, l⟩ =
      Pi.single k ((C.d i k).hom (chosenBoundaryLift C c i (i - 1) l)) :=
  parityFold_d_single C S i k hik _

/-- If `C` vanishes outside `S`, the vectors `foldBoundary` are linearly independent. -/
private theorem linearIndependent_foldBoundary (hS : ∀ j ∉ S, IsZero (C.X j)) {r s : ZMod 2}
    (hrs : r + 1 = s) : LinearIndependent F (foldBoundary S c r s) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro g hg ⟨i, l⟩
  by_cases hi : (i : ℤ) - 1 ∈ S
  swap
  · have h₀ := finrank_range_d_eq_zero_of_notMem hS (i := i) hi
    exact (Nat.not_lt_zero _ (lt_of_lt_of_eq l.isLt h₀)).elim
  -- Read off the component in degree `i - 1`, where only the vectors coming from degree `i` live.
  let k : parityFoldDegrees S s :=
    ⟨i - 1, by rw [← hrs]; exact mem_parityFoldDegrees_sub_one i.property hi⟩
  have hk := congrFun hg k
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Fintype.sum_sigma] at hk
  rw [Finset.sum_eq_single i (fun i' _ hi' ↦ Finset.sum_eq_zero fun l' _ ↦ by
    rw [foldBoundary, foldLift, parityFold_d_single_apply_of_ne C S i' _ k fun h ↦
      hi' (Subtype.ext (by dsimp only [k] at h; omega)), smul_zero]) (by simp)] at hk
  simp only [foldBoundary_apply, k, chosenBoundaryLift_spec] at hk
  exact Fintype.linearIndependent_iff.1
    ((chosenBoundaryBasis C c i (i - 1)).linearIndependent.map' _ (Submodule.ker_subtype _))
    (fun l ↦ g ⟨i, l⟩) hk l

/-- The vectors `foldBoundary` span the boundaries of the parity fold. -/
private theorem span_foldBoundary {r s : ZMod 2} :
    Submodule.span F (Set.range (foldBoundary S c r s)) =
      LinearMap.range ((C.parityFold S).d r s).hom := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  rintro _ ⟨x, rfl⟩
  rw [← Finset.univ_sum_single x, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  -- Write the boundary of the component `x i` in the chosen basis, and lift it.
  let b := chosenBoundaryBasis C c i (i - 1)
  let y : LinearMap.range (C.d i (i - 1)).hom := ⟨_, x i, rfl⟩
  let u := ∑ l, b.repr y l • chosenBoundaryLift C c i (i - 1) l
  have hu : (C.d i (i - 1)).hom (x i - u) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul, chosenBoundaryLift_spec]
    rw [sub_eq_zero]
    have h := congrArg Subtype.val (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hsplit : (Pi.single i (x i) : ∀ j : parityFoldDegrees S r, C.X j) =
      Pi.single i (x i - u) + ∑ l, b.repr y l •
        (Pi.single i (chosenBoundaryLift C c i (i - 1) l) :
          ∀ j : parityFoldDegrees S r, C.X j) := by
    have hlin := map_sum (LinearMap.single F (fun j : parityFoldDegrees S r ↦ C.X j) i)
      (fun l ↦ b.repr y l • chosenBoundaryLift C c i (i - 1) l) Finset.univ
    simp only [map_smul, LinearMap.coe_single] at hlin
    rw [← hlin, ← Pi.single_add, sub_add_cancel]
  rw [hsplit, map_add, parityFold_d_single_eq_zero C S i _ hu, zero_add, map_sum]
  exact Submodule.sum_mem _ fun l _ ↦ by
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, l⟩, rfl⟩)

/-- The basis of the boundaries of the parity fold made of the vectors `foldBoundary`. -/
private def foldBoundaryBasis (hS : ∀ j ∉ S, IsZero (C.X j)) {r s : ZMod 2} (hrs : r + 1 = s) :
    Basis (Fin (Fintype.card (Σ i : parityFoldDegrees S r,
      Fin (finrank F (LinearMap.range (C.d i (i - 1)).hom))))) F
      (LinearMap.range ((C.parityFold S).d r s).hom) :=
  ((Basis.span (linearIndependent_foldBoundary c hS hrs)).map
    (LinearEquiv.ofEq _ _ (span_foldBoundary c))).reindex (Fintype.equivFin _)

private theorem coe_foldBoundaryBasis (hS : ∀ j ∉ S, IsZero (C.X j)) {r s : ZMod 2}
    (hrs : r + 1 = s) (t) :
    (foldBoundaryBasis c hS hrs t : (C.parityFold S).X s) =
      foldBoundary S c r s ((Fintype.equivFin _).symm t) := by
  simp only [foldBoundaryBasis, Basis.reindex_apply, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.span_apply]

/-- The lifts `foldLift` are lifts of the basis `foldBoundaryBasis`. -/
private theorem foldLift_spec (hS : ∀ j ∉ S, IsZero (C.X j)) {r s : ZMod 2} (hrs : r + 1 = s)
    (t) : ((C.parityFold S).d r s).hom ((foldLift S c r ∘ (Fintype.equivFin _).symm) t) =
      foldBoundaryBasis c hS hrs t :=
  (coe_foldBoundaryBasis c hS hrs t).symm

end BoundaryBasis

section Torsion

open HomologicalComplex (chosenBoundaryBasis chosenBoundaryLift chosenBoundaryLift_spec
  torsionBracket)

variable {F : Type*} [Field F] {C : ChainComplex (ModuleCat F) ℤ} {S : Finset ℤ}
  {n : ℤ → ℕ}
  (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {m : ZMod 2 → ℕ}
  (e : ∀ r, (Σ j : parityFoldDegrees S r, Fin (n j)) ≃ Fin (m r))

variable (S) in
/-- The basis of the term of parity `r` of the parity fold made of the bases `c j` of the terms of
`C` of parity `r`, ordered by `e r`. -/
def parityFoldBasis (r : ZMod 2) : Basis (Fin (m r)) F ((C.parityFold S).X r) :=
  (Pi.basis fun j : parityFoldDegrees S r ↦ c j).reindex (e r)

/-- The basis vectors of `parityFoldBasis` are the basis vectors of the terms of `C`, each
concentrated in its degree. -/
@[simp]
theorem parityFoldBasis_apply (r : ZMod 2) (t : Fin (m r)) :
    parityFoldBasis S c e r t = Pi.single ((e r).symm t).fst (c _ ((e r).symm t).snd) := by
  rw [parityFoldBasis, Basis.reindex_apply, Pi.basis_apply]

/-- The coordinates of a vector in `parityFoldBasis` are the coordinates of its components in the
bases of the terms of `C`. -/
@[simp]
theorem parityFoldBasis_repr (r : ZMod 2) (x : (C.parityFold S).X r) (t : Fin (m r)) :
    (parityFoldBasis S c e r).repr x t = (c _).repr (x ((e r).symm t).fst) ((e r).symm t).snd := by
  rw [parityFoldBasis, Basis.repr_reindex_apply, Pi.basis_repr]

/-- The bracket of an acyclic complex `C` in degree `j`, for the chosen bases of the boundaries
and the chosen lifts. -/
private def chosenBracket (hC : C.Acyclic) (j : ℤ) : F :=
  torsionBracket c (ChainComplex.prev ℤ j) (ChainComplex.next ℤ j) (hC j)
    (chosenBoundaryBasis C c (j + 1) j) (chosenBoundaryBasis C c j (j - 1))
    (chosenBoundaryLift C c j (j - 1)) (chosenBoundaryLift_spec C c j (j - 1))

/-- The family of vectors of `C.X j` whose determinant is the bracket `chosenBracket`: the chosen
basis of the boundaries followed by the chosen lifts. -/
private def chosenBracketFamily (hC : C.Acyclic) (j : ℤ) : Fin (n j) → C.X j :=
  Fin.append (fun l ↦ (chosenBoundaryBasis C c (j + 1) j l : C.X j))
      (chosenBoundaryLift C c j (j - 1)) ∘
    Fin.cast (HomologicalComplex.eq_add_of_exactAt c (ChainComplex.prev ℤ j)
      (ChainComplex.next ℤ j) (hC j) (chosenBoundaryBasis C c (j + 1) j)
      (chosenBoundaryBasis C c j (j - 1)))

private theorem chosenBracket_eq_det (hC : C.Acyclic) (j : ℤ) :
    chosenBracket c hC j = (c j).det (chosenBracketFamily c hC j) :=
  HomologicalComplex.torsionBracket_eq_det_append c _ _ _ _ _ _ _ _

private theorem linearIndependent_chosenBracketFamily (hC : C.Acyclic) (j : ℤ) :
    LinearIndependent F (chosenBracketFamily c hC j) :=
  ((c j).is_basis_iff_det.2 (isUnit_iff_ne_zero.2 (by
    rw [← chosenBracket_eq_det]
    exact HomologicalComplex.torsionBracket_ne_zero c _ _ _ _ _ _ _))).1

/-- The vectors of the brackets of `C` in the degrees of parity `r`, each concentrated in its
degree, are distinct. -/
private theorem injective_single_chosenBracketFamily (hC : C.Acyclic) (r : ZMod 2) :
    Function.Injective fun x : Σ j : parityFoldDegrees S r, Fin (n j) ↦
      (Pi.single x.fst (chosenBracketFamily c hC x.fst x.snd) :
        ∀ j : parityFoldDegrees S r, C.X j) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  by_cases hj : j = j'
  · subst hj
    exact congrArg (Sigma.mk j)
      ((linearIndependent_chosenBracketFamily c hC j).injective (Pi.single_injective j h))
  · have := congrFun h j
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hj] at this
    exact ((linearIndependent_chosenBracketFamily c hC j).ne_zero a this).elim

/-- In `ZMod 2`, the parity following the parity `s` following `r` is `r` again. -/
private theorem add_one_eq_of_add_one_eq {r s : ZMod 2} (h : r + 1 = s) : s + 1 = r := by
  rw [← h, CharTwo.add_cancel_right]

/-- Every vector of a bracket of `C` in a degree `j` of parity `r`, concentrated in degree `j`, is a
vector of the family of the bracket of the parity fold in parity `r`: a basis vector of the
boundaries of `C.X j` is the image of a chosen lift out of degree `j + 1`, and a lift out of
degree `j` is a chosen lift. -/
private theorem exists_foldBracket_eq (hS : ∀ j ∉ S, IsZero (C.X j)) (hC : C.Acyclic)
    {r s : ZMod 2} (hrs : r + 1 = s) (j : parityFoldDegrees S r) (a : Fin (n j)) :
    ∃ u, Fin.append (fun l ↦
        (foldBoundaryBasis c hS (add_one_eq_of_add_one_eq hrs) l : (C.parityFold S).X r))
        (foldLift S c r ∘ (Fintype.equivFin _).symm) u =
      Pi.single j (chosenBracketFamily c hC j a) := by
  have hnj := HomologicalComplex.eq_add_of_exactAt c (ChainComplex.prev ℤ j)
    (ChainComplex.next ℤ j) (hC j) (chosenBoundaryBasis C c (j + 1) j)
    (chosenBoundaryBasis C c j (j - 1))
  obtain ⟨a', rfl⟩ : ∃ a', a = Fin.cast hnj.symm a' := ⟨Fin.cast hnj a, by simp⟩
  simp only [chosenBracketFamily, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  induction a' using Fin.addCases with
  | left l =>
    by_cases hj1 : (j : ℤ) + 1 ∈ S
    swap
    · have h₀ := finrank_range_d_eq_zero_of_notMem_left hS (k := j) hj1
      exact (Nat.not_lt_zero _ (lt_of_lt_of_eq l.isLt h₀)).elim
    let i : parityFoldDegrees S s :=
      ⟨j + 1, by rw [← hrs]; exact mem_parityFoldDegrees_add_one j.property hj1⟩
    have key : ∀ a : ℤ, a = j →
        ∃ l' : Fin (finrank F (LinearMap.range (C.d (j + 1) a).hom)),
          (C.d (j + 1) j).hom (chosenBoundaryLift C c (j + 1) a l') =
            chosenBoundaryBasis C c (j + 1) j l := by
      rintro a rfl
      exact ⟨l, chosenBoundaryLift_spec C c _ _ l⟩
    obtain ⟨l', hl'⟩ := key ((j : ℤ) + 1 - 1) (add_sub_cancel_right _ _)
    refine ⟨Fin.castAdd _ (Fintype.equivFin _ ⟨i, l'⟩), ?_⟩
    rw [Fin.append_left, coe_foldBoundaryBasis, Equiv.symm_apply_apply,
      foldBoundary_eq c i j rfl, Fin.append_left]
    exact congrArg _ hl'
  | right l =>
    refine ⟨Fin.natAdd _ (Fintype.equivFin _ ⟨j, l⟩), ?_⟩
    rw [Fin.append_right, Function.comp_apply, Equiv.symm_apply_apply, Fin.append_right,
      foldLift]

/-- **The brackets of the parity fold.** In parity `r`, with the boundary bases `foldBoundaryBasis`
and the lifts `foldLift`, the bracket of the parity fold is, up to sign, the product of the
brackets of `C` in the degrees of `S` of parity `r`: the vectors whose determinant it is are those
of the brackets of `C`, each concentrated in its degree, in another order. -/
private theorem torsionBracket_parityFoldBasis (hS : ∀ j ∉ S, IsZero (C.X j)) (hC : C.Acyclic)
    {r s : ZMod 2} (hrs : r + 1 = s) (hP : (C.parityFold S).ExactAt r) :
    ∃ ε : ℤˣ, torsionBracket (parityFoldBasis S c e)
      ((ComplexShape.up _).prev_eq' (add_one_eq_of_add_one_eq hrs))
      ((ComplexShape.up _).next_eq' hrs) hP (foldBoundaryBasis c hS (add_one_eq_of_add_one_eq hrs))
      (foldBoundaryBasis c hS hrs) (foldLift S c r ∘ (Fintype.equivFin _).symm)
      (foldLift_spec c hS hrs) = ε • ∏ j : parityFoldDegrees S r, chosenBracket c hC j := by
  classical
  have hsr := add_one_eq_of_add_one_eq hrs
  have hi : (ComplexShape.up (ZMod 2)).prev r = s := (ComplexShape.up _).prev_eq' hsr
  have hk : (ComplexShape.up (ZMod 2)).next r = s := (ComplexShape.up _).next_eq' hrs
  have hn := HomologicalComplex.eq_add_of_exactAt (parityFoldBasis S c e) hi hk hP
    (foldBoundaryBasis c hS hsr) (foldBoundaryBasis c hS hrs)
  rw [HomologicalComplex.torsionBracket_eq_det_append _ hi hk hP _ _ _ _ hn, parityFoldBasis,
    Basis.det_reindex]
  have hdet : (Pi.basis fun j : parityFoldDegrees S r ↦ c j).det
      (fun x : Σ j : parityFoldDegrees S r, Fin (n j) ↦
        Pi.single x.fst (chosenBracketFamily c hC x.fst x.snd)) =
      ∏ j : parityFoldDegrees S r, chosenBracket c hC j := by
    exact (Module.Basis.det_pi_single _ fun j : parityFoldDegrees S r ↦
      chosenBracketFamily c hC j).trans
        (Finset.prod_congr rfl fun j _ ↦ (chosenBracket_eq_det c hC j).symm)
  rw [← hdet]
  refine (Pi.basis fun j : parityFoldDegrees S r ↦ c j).det.exists_map_eq_units_smul
    (injective_single_chosenBracketFamily c hC r) fun x ↦ ?_
  obtain ⟨u, hu⟩ := exists_foldBracket_eq c hS hC hrs x.fst x.snd
  exact ⟨(e r).symm (Fin.cast hn.symm u), by simp [hu]⟩

/-- The bracket of `C` in degree `j` does not depend on how the degree `j - 1` is written. -/
private theorem torsionBracket_chosen_congr (hC : C.Acyclic) {j k k' : ℤ}
    (hk : (ComplexShape.down ℤ).next j = k) (hk' : (ComplexShape.down ℤ).next j = k') :
    torsionBracket c (ChainComplex.prev ℤ j) hk (hC j) (chosenBoundaryBasis C c (j + 1) j)
        (chosenBoundaryBasis C c j k) (chosenBoundaryLift C c j k)
        (chosenBoundaryLift_spec C c j k) =
      torsionBracket c (ChainComplex.prev ℤ j) hk' (hC j) (chosenBoundaryBasis C c (j + 1) j)
        (chosenBoundaryBasis C c j k') (chosenBoundaryLift C c j k')
        (chosenBoundaryLift_spec C c j k') := by
  obtain rfl : k = k' := hk.symm.trans hk'
  rfl

/-- The Reidemeister torsion of an acyclic complex vanishing outside `S` is the product of its
brackets in the odd degrees of `S` over the product of its brackets in the even degrees. -/
private theorem reidemeisterTorsion_eq_prod_mul_inv_prod (hS : ∀ j ∉ S, n j = 0)
    (hC : C.Acyclic) :
    C.reidemeisterTorsion c = (∏ j : parityFoldDegrees S 1, chosenBracket c hC j) *
      (∏ j : parityFoldDegrees S 0, chosenBracket c hC j)⁻¹ := by
  classical
  have hfin : {i | n i ≠ 0}.Finite :=
    S.finite_toSet.subset fun i hi ↦ by_contra fun h ↦ hi (hS i h)
  rw [HomologicalComplex.reidemeisterTorsion_eq_finprod hfin hC
    (fun j ↦ chosenBoundaryBasis C c (j + 1) j) (fun j ↦ chosenBoundaryLift C c (j + 1) j)
    (fun j ↦ chosenBoundaryLift_spec C c (j + 1) j)]
  -- Reindex by the degree `i = j + 1` of the bracket, and restrict to `S`.
  let f (i : ℤ) : F := chosenBracket c hC i ^ ((i - 1).negOnePow : ℤ)
  have hshift : ∏ᶠ j : ℤ, torsionBracket c (by simp) (by simp) (hC (j + 1))
      (chosenBoundaryBasis C c (j + 1 + 1) (j + 1)) (chosenBoundaryBasis C c (j + 1) j)
      (chosenBoundaryLift C c (j + 1) j) (chosenBoundaryLift_spec C c (j + 1) j) ^
        (j.negOnePow : ℤ) = ∏ᶠ j : ℤ, f (Equiv.addRight 1 j) :=
    finprod_congr fun j ↦ by
      simp only [f, Equiv.coe_addRight, add_sub_cancel_right, chosenBracket]
      rw [torsionBracket_chosen_congr c hC]
  rw [hshift, finprod_comp_equiv (Equiv.addRight 1) (f := f),
    finprod_eq_prod_of_mulSupport_subset f (s := S) fun i hi ↦ by_contra fun h ↦ hi (by
      simp only [f, chosenBracket]
      rw [HomologicalComplex.torsionBracket_eq_one c _ _ _ _ _ _ _ (hS i h), one_zpow]),
    ← Finset.prod_filter_mul_prod_filter_not S fun i : ℤ ↦ (i : ZMod 2) = 1]
  -- The brackets of odd degree enter with exponent `1`, those of even degree with exponent `-1`.
  have hodd : ∀ i ∈ parityFoldDegrees S 1, f i = chosenBracket c hC i := fun i hi ↦ by
    have : Even (i - 1) :=
      (ZMod.intCast_eq_one_iff_odd.1 (Finset.mem_filter.1 hi).2).sub_odd odd_one
    simp [f, Int.negOnePow_even _ this]
  have h0 : S.filter (fun i : ℤ ↦ ¬(i : ZMod 2) = 1) = parityFoldDegrees S 0 :=
    Finset.filter_congr fun i _ ↦ by
      generalize (i : ZMod 2) = t
      revert t
      decide
  have heven : ∀ i ∈ parityFoldDegrees S 0, f i = (chosenBracket c hC i)⁻¹ := fun i hi ↦ by
    have : Odd (i - 1) :=
      (ZMod.intCast_eq_zero_iff_even.1 (Finset.mem_filter.1 hi).2).sub_odd odd_one
    simp [f, Int.negOnePow_odd _ this]
  rw [h0, Finset.prod_congr rfl hodd, Finset.prod_congr rfl heven, Finset.prod_inv_distrib,
    ← Finset.prod_coe_sort (parityFoldDegrees S 1),
    ← Finset.prod_coe_sort (parityFoldDegrees S 0)]

/-- **The torsion of the parity fold.** Let `C` be a chain complex of vector spaces over a field,
based by `c` and vanishing outside the finite set of degrees `S`, and give each term of its parity
fold the basis made of the bases of the terms of `C` of that parity, in any order `e`. Then the
torsion of the parity fold is, up to sign, the Reidemeister torsion of `C`. Both vanish when `C` is
not acyclic. -/
theorem homologicalComplex_parityTorsion_parityFold_eq_reidemeisterTorsion_or_eq_neg
    (hS : ∀ j ∉ S, n j = 0) :
    (C.parityFold S).parityTorsion (parityFoldBasis S c e) = C.reidemeisterTorsion c ∨
      (C.parityFold S).parityTorsion (parityFoldBasis S c e) = -C.reidemeisterTorsion c := by
  have hS' : ∀ j ∉ S, IsZero (C.X j) := fun j hj ↦ by
    have : IsEmpty (Fin (n j)) := by rw [hS j hj]; infer_instance
    have := (c j).repr.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  by_cases hC : C.Acyclic
  swap
  · left
    rw [HomologicalComplex.parityTorsion_of_not_acyclic _ _
      (mt (parityFold_acyclic_iff hS').1 hC),
      HomologicalComplex.reidemeisterTorsion_of_not_acyclic _ _ hC]
  have hP := (parityFold_acyclic_iff hS').2 hC
  have h10 : (1 : ZMod 2) + 1 = 0 := by decide
  obtain ⟨ε₁, h₁⟩ := torsionBracket_parityFoldBasis c e hS' hC h10 (hP 1)
  obtain ⟨ε₀, h₀⟩ := torsionBracket_parityFoldBasis c e hS' hC (zero_add 1) (hP 0)
  rw [HomologicalComplex.parityTorsion_eq hP (foldBoundaryBasis c hS' h10)
    (foldBoundaryBasis c hS' (zero_add 1)) _ (foldLift_spec c hS' (zero_add 1)) _
    (foldLift_spec c hS' h10), h₁, h₀, reidemeisterTorsion_eq_prod_mul_inv_prod c hS hC]
  rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
    rcases Int.units_eq_one_or ε₀ with rfl | rfl <;> simp [neg_mul, mul_neg, inv_neg]

end Torsion

end ChainComplex
