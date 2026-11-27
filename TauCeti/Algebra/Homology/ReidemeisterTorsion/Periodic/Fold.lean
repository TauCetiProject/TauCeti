/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Alternating.Basic
import TauCeti.LinearAlgebra.Pi

/-!
# Folding a bounded complex into a two-periodic complex

Let `C` be a `ℤ`-graded chain complex of modules, vanishing outside a finite set `S` of degrees.
Reading its degrees modulo two folds it into a two-periodic complex, the **parity fold**
`ChainComplex.parityFold C S`: its term of parity `r` is the product `∏ C.X j` over the degrees
`j ∈ S` of parity `r` (`ChainComplex.parityFoldDegrees S r`), and its differentials are those of
`C`. This is how the finite parity complex of a Floer–Novikov theory whose relative grading is an
integer grading relates to that integer complex.

The parity fold is exact in parity `r` exactly when `C` is exact in every degree of parity `r`
(`ChainComplex.parityFold_exactAt_iff`), so it is acyclic exactly when `C` is
(`ChainComplex.parityFold_acyclic_iff`).

Over a field, give each `C.X j` a basis `c j`, and the term of parity `r` of the fold the basis made
of the bases `c j` of the degrees of parity `r`, in an order `e r` (`ChainComplex.parityFoldBasis`).
Then the torsion `HomologicalComplex.parityTorsion` of the based two-periodic complex is, up to
sign, the Reidemeister torsion `HomologicalComplex.reidemeisterTorsion` of `C`
(`ChainComplex.parityTorsion_parityFold`). Both torsions are made of the same brackets: the torsion
of `C` is the alternating product `∏ⱼ [bⱼ sⱼ₋₁ / cⱼ] ^ ((-1) ^ (j + 1))`, the brackets of odd
degrees in the numerator, and the torsion of the fold is the bracket of its odd term over the
bracket of its even term. Taking the bases of the boundaries and the lifts of the fold to be those
of `C`, each concentrated in its degree, the vectors whose determinant is the bracket of the fold in
parity `r` are those of the brackets of `C` in the degrees of parity `r`, each concentrated in its
degree, in another order. The determinant of such a block family in the product basis is the product
of the determinants of the blocks (`Module.Basis.det_pi_single`), and the reordering contributes a
sign. The sign depends on the orders `e` and on the dimensions of the boundaries, and torsions of
parity complexes are in any case only defined up to sign when their bases come from unordered
generators; reordering the bases changes the torsion of the fold by the signs of the permutations
(`HomologicalComplex.parityTorsion_reindex`).

The compression of cochain complexes `TauCeti.PeriodicComplex.compression` folds an
integer-indexed complex in any category through coproducts. The parity fold is the concrete form
of this construction for chain complexes of modules vanishing outside `S`, a finite product with
explicit bases, which the torsion needs.

## Main definitions

* `ChainComplex.parityFold C S`: the two-periodic complex obtained by reading the degrees of `C`
  in `S` modulo two.
* `ChainComplex.parityFoldBasis S c e`: its bases made of the bases `c j` of the terms of `C`.

## Main results

* `ChainComplex.parityFold_acyclic_iff`: the parity fold is acyclic exactly when `C` is.
* `ChainComplex.parityTorsion_parityFold`: the torsion of the based parity fold is, up to sign,
  the Reidemeister torsion of `C`.

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

variable {R : Type*} [Ring R] (C : ChainComplex (ModuleCat R) ℤ) (S : Finset ℤ)

/-- The degrees in `S` of parity `r`. -/
abbrev parityFoldDegrees (r : ZMod 2) : Finset ℤ :=
  S.filter fun j ↦ (j : ZMod 2) = r

variable {S} in
/-- A differential of `C` between degrees whose parities are not consecutive vanishes. -/
private theorem d_eq_zero_of_parity {r s : ZMod 2} (hrs : r + 1 ≠ s) (i : parityFoldDegrees S r)
    (j : parityFoldDegrees S s) : C.d i j = 0 :=
  C.shape _ _ fun hij ↦ hrs <| by
    have hi := (Finset.mem_filter.1 i.property).2
    have hj := (Finset.mem_filter.1 j.property).2
    rw [ComplexShape.down_Rel] at hij
    have h : (((j : ℤ) + 1 : ℤ) : ZMod 2) = ((i : ℤ) : ZMod 2) := by
      rw [hij]
    push_cast at h
    rw [hi, hj] at h
    rw [← h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The **parity fold** of a chain complex `C` along a finite set `S` of degrees: the two-periodic
complex whose term of parity `r` is the product of the terms `C.X j` for the degrees `j ∈ S` of
parity `r`, with the differentials of `C` between them. When `C` vanishes outside `S`, this is the
sum over each parity class of the terms of `C`. -/
-- Implicitly reducible so that its terms unfold to the products `∀ j, C.X j` when vectors of
-- these products are fed to its differentials.
@[expose, implicit_reducible]
def parityFold : HomologicalComplex (ModuleCat R) (ComplexShape.up (ZMod 2)) where
  X r := ModuleCat.of R (∀ j : parityFoldDegrees S r, C.X j)
  d r s := ModuleCat.ofHom (LinearMap.pi fun j ↦ ∑ i : parityFoldDegrees S r,
      (C.d i j).hom ∘ₗ
        (LinearMap.proj i : (∀ j : parityFoldDegrees S r, C.X j) →ₗ[R] C.X i))
  shape r s hrs := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun j ↦ ?_)
    simp only [ModuleCat.hom_ofHom, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [d_eq_zero_of_parity C hrs i j, ModuleCat.hom_zero, LinearMap.zero_apply]
  d_comp_d' r s t _ _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun k ↦ ?_)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.pi_apply,
      LinearMap.sum_apply, LinearMap.proj_apply, map_sum, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦
      HomologicalComplex.d_comp_d_apply C _ _ _ _

/-- The component in degree `j` of the differential of the parity fold. -/
@[simp]
theorem parityFold_d_apply (r s : ZMod 2) (x : (C.parityFold S).X r) (j : parityFoldDegrees S s) :
    ((C.parityFold S).d r s).hom x j = ∑ i : parityFoldDegrees S r, (C.d i j).hom (x i) := by
  simp only [parityFold, ModuleCat.hom_ofHom]
  exact LinearMap.sum_apply _ _ x

/-- The differential of the parity fold on a vector concentrated in one degree `i`. -/
theorem parityFold_d_single {r s : ZMod 2} (i : parityFoldDegrees S r) (z : C.X i)
    (j : parityFoldDegrees S s) :
    ((C.parityFold S).d r s).hom (Pi.single i z) j = (C.d i j).hom z := by
  refine (parityFold_d_apply C S r s _ j).trans ?_
  rw [Finset.sum_eq_single i (fun i' _ hi' ↦ by
    rw [Pi.single_eq_of_ne hi', map_zero]) (by simp), Pi.single_eq_same]

/-- The differential of the parity fold carries a vector concentrated in degree `k + 1` to the
vector concentrated in degree `k` given by the differential of `C`. -/
theorem parityFold_d_single_eq {r s : ZMod 2} (i : parityFoldDegrees S r)
    (k : parityFoldDegrees S s) (hik : (i : ℤ) = k + 1) (z : C.X i) :
    ((C.parityFold S).d r s).hom (Pi.single i z) = Pi.single k ((C.d i k).hom z) := by
  funext j
  rw [parityFold_d_single]
  by_cases hj : j = k
  · subst hj
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, C.shape _ _ fun h ↦ hj (Subtype.ext (by
      rw [ComplexShape.down_Rel] at h
      omega)), ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The differential of the parity fold kills a vector concentrated in degree `i` whose component
is a cycle of `C`. -/
theorem parityFold_d_single_eq_zero {r s : ZMod 2} (i : parityFoldDegrees S r)
    (z : C.X i) (hz : (C.d i (i - 1)).hom z = 0) :
    ((C.parityFold S).d r s).hom (Pi.single i z) = 0 := by
  funext k
  rw [parityFold_d_single]
  obtain ⟨k, hk⟩ := k
  by_cases hki : k = i - 1
  · subst hki
    exact hz
  · rw [C.shape (i : ℤ) k fun h ↦ hki (by rw [ComplexShape.down_Rel] at h; omega),
      ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]

section Acyclic

variable {C S}

/-- A degree of parity `r` shifted by one has parity `r + 1`. -/
private theorem mem_parityFoldDegrees_add_one {r : ZMod 2} {j : ℤ}
    (hj : j ∈ parityFoldDegrees S r) (h : j + 1 ∈ S) : j + 1 ∈ parityFoldDegrees S (r + 1) :=
  Finset.mem_filter.2 ⟨h, by push_cast; rw [(Finset.mem_filter.1 hj).2]⟩

/-- A degree of parity `r` shifted by minus one has parity `r + 1`. -/
private theorem mem_parityFoldDegrees_sub_one {r : ZMod 2} {j : ℤ}
    (hj : j ∈ parityFoldDegrees S r) (h : j - 1 ∈ S) : j - 1 ∈ parityFoldDegrees S (r + 1) :=
  Finset.mem_filter.2 ⟨h, by push_cast; rw [(Finset.mem_filter.1 hj).2, CharTwo.sub_eq_add]⟩

variable (S) in
/-- The vector of the parity fold concentrated in degree `j + 1` with component `z`, or `0` when
`j + 1 ∉ S`. -/
private def foldSingleSucc {r : ZMod 2} (j : parityFoldDegrees S r) (z : C.X (j + 1)) :
    (C.parityFold S).X (r + 1) :=
  if h : (j : ℤ) + 1 ∈ S then Pi.single ⟨j + 1, mem_parityFoldDegrees_add_one j.property h⟩ z
  else 0

/-- If `C` vanishes outside `S`, the differential of the parity fold carries
`foldSingleSucc S j z` to the vector concentrated in degree `j` given by the differential of `C`. -/
private theorem parityFold_d_foldSingleSucc (hS : ∀ j ∉ S, IsZero (C.X j)) {r : ZMod 2}
    (j : parityFoldDegrees S r) (z : C.X (j + 1)) :
    ((C.parityFold S).d (r + 1) r).hom (foldSingleSucc S j z) =
      Pi.single j ((C.d (j + 1) j).hom z) := by
  by_cases h : (j : ℤ) + 1 ∈ S
  · have : foldSingleSucc S j z = Pi.single ⟨j + 1, mem_parityFoldDegrees_add_one j.property h⟩ z :=
      dite_eq_left h
    rw [this]
    exact parityFold_d_single_eq C S ⟨j + 1, mem_parityFoldDegrees_add_one j.property h⟩ j rfl z
  · have : foldSingleSucc S j z = 0 := dite_eq_right h
    rw [this, map_zero, (ModuleCat.subsingleton_of_isZero (hS _ h)).elim z 0, map_zero,
      Pi.single_zero]

/-- Exactness of the parity fold in parity `r`, on elements. -/
private theorem parityFold_exactAt_iff_forall (r : ZMod 2) :
    (C.parityFold S).ExactAt r ↔ ∀ x, ((C.parityFold S).d r (r + 1)).hom x = 0 →
      ∃ y, ((C.parityFold S).d (r + 1) r).hom y = x := by
  have hprev : (ComplexShape.up (ZMod 2)).prev r = r + 1 := by
    rw [CochainComplex.prev, CharTwo.sub_eq_add]
  rw [HomologicalComplex.exactAt_iff' _ (r + 1) r (r + 1) hprev (CochainComplex.next _ r),
    ShortComplex.moduleCat_exact_iff]
  -- The maps of the short complex are the differentials, and `ConcreteCategory.hom` is
  -- `ModuleCat.Hom.hom` for morphisms of modules.
  rfl

/-- If the parity fold is exact in parity `r`, then `C` is exact in every degree of `S` of
parity `r`. -/
private theorem exactAt_of_parityFold_exactAt {r : ZMod 2} (hP : (C.parityFold S).ExactAt r)
    {j : ℤ} (hj : j ∈ parityFoldDegrees S r) : C.ExactAt j := by
  rw [HomologicalComplex.exactAt_iff' _ (j + 1) j (j - 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  -- The vector concentrated in degree `j` with component `z` is a cycle of the fold, hence a
  -- boundary, and `z` is the component in degree `j` of that boundary.
  obtain ⟨y, hy⟩ := (parityFold_exactAt_iff_forall r).1 hP (Pi.single ⟨j, hj⟩ z)
    (parityFold_d_single_eq_zero C S ⟨j, hj⟩ z hz)
  have hz' := congrFun hy ⟨j, hj⟩
  rw [Pi.single_eq_same, parityFold_d_apply] at hz'
  rw [← LinearMap.mem_range]
  rw [← hz']
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have key : ∀ (a : ℤ), a = j + 1 → ∀ u : C.X a,
      (C.d a j).hom u ∈ LinearMap.range (C.d (j + 1) j).hom := by
    rintro a rfl u
    exact ⟨u, rfl⟩
  by_cases hi : (i : ℤ) = j + 1
  · exact key _ hi _
  · rw [C.shape (i : ℤ) j fun h ↦ hi (by rw [ComplexShape.down_Rel] at h; omega)]
    exact Submodule.zero_mem _

/-- If `C` vanishes outside `S` and is exact in every degree of `S` of parity `r`, then the parity
fold is exact in parity `r`. -/
private theorem parityFold_exactAt_of_exactAt (hS : ∀ j ∉ S, IsZero (C.X j)) {r : ZMod 2}
    (hC : ∀ j ∈ parityFoldDegrees S r, C.ExactAt j) : (C.parityFold S).ExactAt r := by
  rw [parityFold_exactAt_iff_forall]
  intro x hx
  -- Every component of `x` is a cycle of `C`.
  have hcyc (j : parityFoldDegrees S r) : (C.d j (j - 1)).hom (x j) = 0 := by
    by_cases hj : (j : ℤ) - 1 ∈ S
    · have := congrFun hx ⟨j - 1, mem_parityFoldDegrees_sub_one j.property hj⟩
      rwa [parityFold_d_apply, Finset.sum_eq_single j (fun i _ hij ↦ by
        rw [C.shape (i : ℤ) ((j : ℤ) - 1) fun h ↦ hij (Subtype.ext (by
          rw [ComplexShape.down_Rel] at h
          omega)), ModuleCat.hom_zero, LinearMap.zero_apply]) (by simp)] at this
    · exact (ModuleCat.subsingleton_of_isZero (hS _ hj)).elim _ _
  -- Hence a boundary of `C`, and `x` is the boundary of the sum of the vectors it comes from.
  have hlift (j : parityFoldDegrees S r) : ∃ w : C.X (j + 1), (C.d (j + 1) j).hom w = x j := by
    have hj := hC j j.property
    rw [HomologicalComplex.exactAt_iff' _ ((j : ℤ) + 1) j ((j : ℤ) - 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at hj
    exact hj _ (hcyc j)
  choose w hw using hlift
  refine ⟨∑ j : parityFoldDegrees S r, foldSingleSucc S j (w j), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← Finset.univ_sum_single x]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [parityFold_d_foldSingleSucc hS, hw]

/-- The parity fold is exact in parity `r` exactly when `C` is exact in every degree of `S` of
parity `r`, provided `C` vanishes outside `S`. -/
theorem parityFold_exactAt_iff (hS : ∀ j ∉ S, IsZero (C.X j)) (r : ZMod 2) :
    (C.parityFold S).ExactAt r ↔ ∀ j ∈ parityFoldDegrees S r, C.ExactAt j :=
  ⟨fun hP _ hj ↦ exactAt_of_parityFold_exactAt hP hj, parityFold_exactAt_of_exactAt hS⟩

/-- The parity fold of a complex vanishing outside `S` is acyclic exactly when the complex is. -/
theorem parityFold_acyclic_iff (hS : ∀ j ∉ S, IsZero (C.X j)) :
    (C.parityFold S).Acyclic ↔ C.Acyclic := by
  refine ⟨fun h j ↦ ?_, fun h r ↦ (parityFold_exactAt_iff hS r).2 fun j _ ↦ h j⟩
  by_cases hj : j ∈ S
  · exact (parityFold_exactAt_iff hS (j : ZMod 2)).1 (h _) j (Finset.mem_filter.2 ⟨hj, rfl⟩)
  · exact .of_isZero (hS j hj)

end Acyclic

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
  parityFold_d_single C S i _ k

/-- The image of a chosen lift is the chosen boundary basis vector, concentrated in the degree
below. -/
private theorem foldBoundary_eq {r s : ZMod 2} (i : parityFoldDegrees S r)
    (k : parityFoldDegrees S s) (hik : (i : ℤ) = k + 1)
    (l : Fin (finrank F (LinearMap.range (C.d i (i - 1)).hom))) :
    foldBoundary S c r s ⟨i, l⟩ =
      Pi.single k ((C.d i k).hom (chosenBoundaryLift C c i (i - 1) l)) :=
  parityFold_d_single_eq C S i k hik _

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
    rw [foldBoundary_apply, C.shape (i' : ℤ) ((i : ℤ) - 1) fun h ↦ hi' (Subtype.ext (by
      rw [ComplexShape.down_Rel] at h
      omega)), ModuleCat.hom_zero, LinearMap.zero_apply, smul_zero]) (by simp)] at hk
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

/-- Every vector of a bracket of `C` in a degree `j` of parity `r`, concentrated in degree `j`, is a
vector of the family of the bracket of the parity fold in parity `r`: a basis vector of the
boundaries of `C.X j` is the image of a chosen lift out of degree `j + 1`, and a lift out of
degree `j` is a chosen lift. -/
private theorem exists_foldBracket_eq (hS : ∀ j ∉ S, IsZero (C.X j)) (hC : C.Acyclic)
    {r s : ZMod 2} (hrs : r + 1 = s) (hsr : s + 1 = r) (j : parityFoldDegrees S r)
    (a : Fin (n j)) :
    ∃ u, Fin.append (fun l ↦ (foldBoundaryBasis c hS hsr l : (C.parityFold S).X r))
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
    {r s : ZMod 2} (hrs : r + 1 = s) (hsr : s + 1 = r)
    (hi : (ComplexShape.up (ZMod 2)).prev r = s) (hk : (ComplexShape.up (ZMod 2)).next r = s)
    (hP : (C.parityFold S).ExactAt r) :
    ∃ ε : ℤˣ, torsionBracket (parityFoldBasis S c e) hi hk hP (foldBoundaryBasis c hS hsr)
      (foldBoundaryBasis c hS hrs) (foldLift S c r ∘ (Fintype.equivFin _).symm)
      (foldLift_spec c hS hrs) = ε • ∏ j : parityFoldDegrees S r, chosenBracket c hC j := by
  classical
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
  obtain ⟨u, hu⟩ := exists_foldBracket_eq c hS hC hrs hsr x.fst x.snd
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
theorem parityTorsion_parityFold (hS : ∀ j ∉ S, n j = 0) :
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
  obtain ⟨ε₁, h₁⟩ := torsionBracket_parityFoldBasis c e hS' hC h10 (zero_add 1)
    CochainComplex.prev_zmod_two_one CochainComplex.next_zmod_two_one (hP 1)
  obtain ⟨ε₀, h₀⟩ := torsionBracket_parityFoldBasis c e hS' hC (zero_add 1) h10
    CochainComplex.prev_zmod_two_zero CochainComplex.next_zmod_two_zero (hP 0)
  rw [HomologicalComplex.parityTorsion_eq hP (foldBoundaryBasis c hS' h10)
    (foldBoundaryBasis c hS' (zero_add 1)) _ (foldLift_spec c hS' (zero_add 1)) _
    (foldLift_spec c hS' h10), h₁, h₀, reidemeisterTorsion_eq_prod_mul_inv_prod c hS hC]
  rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
    rcases Int.units_eq_one_or ε₀ with rfl | rfl <;> simp [neg_mul, mul_neg, inv_neg]

end Torsion

end ChainComplex
