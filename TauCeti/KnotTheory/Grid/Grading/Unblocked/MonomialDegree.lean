/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# Gradings of `GC⁻` by the degrees of its monomials

The unblocked grid chain module `GC⁻` is free over the coefficient ring `R` on the monomial
generators `V^e · x`, one for each grid state `x` and exponent vector `e`. So any function
`deg : GridState n → (Fin n →₀ ℕ) → ι` assigning a degree to each monomial generator grades `GC⁻`
over `R`: the piece of degree `a` consists of the chains all of whose monomials have degree `a`.
The bigrading `OddComponentGridDiagram.bigradedChainMinusGrading`, the Alexander grading
`OddComponentGridDiagram.alexanderChainMinusGrading` and the Alexander multigrading
`GridDiagram.componentAlexanderChainMinusGrading` are all of this form.

This file proves once, for an arbitrary degree function, that these pieces make `GC⁻` an internal
direct sum, and gives the two closure criteria every such grading uses: the unblocked differential
and multiplication by a monomial send homogeneous chains to homogeneous chains as soon as they move
the degree of every monomial generator by the same map of degrees.

## Main definitions

* `TauCeti.GridChainMinus.monomialDegreePiece`: the chains of `GC⁻` all of whose monomials have a
  prescribed degree.
* `TauCeti.GridChainMinus.monomialDegreeGrading`: the internal grading of `GC⁻` formed by these
  pieces.

## Main results

* `TauCeti.GridChainMinus.iSup_monomialDegreePiece_eq_top`,
  `TauCeti.GridChainMinus.iSupIndep_monomialDegreePiece`: the pieces span `GC⁻` and are
  independent.
* `TauCeti.GridChainMinus.monomial_smul_mem_monomialDegreePiece`: multiplication by a monomial
  moves the degree of homogeneous chains as it moves the degree of each monomial generator.
* `TauCeti.GridDiagram.unblockedDifferential_mem_monomialDegreePiece`: the unblocked differential
  moves the degree of homogeneous chains as the rectangles it counts move the degree of each
  monomial generator.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridChainMinus

section Semiring

variable {n : ℕ} (R : Type*) [CommSemiring R] {ι : Type*}

/-- The chains of `GC⁻` all of whose monomials `V^e · x` have degree `deg x e` in the set `S`.
Only singletons and complements of singletons are used: the first are the homogeneous pieces, and
comparing against the second makes the pieces independent. -/
private noncomputable def monomialDegreeSupported (deg : GridState n → (Fin n →₀ ℕ) → ι)
    (S : Set ι) : Submodule R (GridChainMinus R n) :=
  ⨅ x, (restrictSupport R {e | deg x e ∈ S}).comap (Finsupp.lapply x)

variable {R} {deg : GridState n → (Fin n →₀ ℕ) → ι}

/-- A chain is supported in a set of degrees exactly when every monomial occurring in it has
degree in that set. -/
private theorem mem_monomialDegreeSupported {S : Set ι} {c : GridChainMinus R n} :
    c ∈ monomialDegreeSupported R deg S ↔ ∀ x : GridState n, ∀ e ∈ (c x).support, deg x e ∈ S := by
  simp only [monomialDegreeSupported, Submodule.mem_iInf, Submodule.mem_comap,
    Finsupp.lapply_apply, mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe,
    Set.mem_ofPred_eq]

/-- Enlarging the set of degrees enlarges the supported submodule. -/
private theorem monomialDegreeSupported_mono {S T : Set ι} (h : S ⊆ T) :
    monomialDegreeSupported R deg S ≤ monomialDegreeSupported R deg T :=
  iInf_mono fun _ => Submodule.comap_mono (restrictSupport_mono R fun _ he => h he)

variable (R deg) in
/-- The chains of `GC⁻` homogeneous of degree `a`: those all of whose monomials `V^e · x` have
degree `deg x e = a`.

The variables move the degree, so this is a submodule over the coefficient ring `R` only, not over
`R[V₀, …, V_{n-1}]`. -/
noncomputable def monomialDegreePiece (a : ι) : Submodule R (GridChainMinus R n) :=
  monomialDegreeSupported R deg {a}

/-- A chain is homogeneous of degree `a` exactly when every monomial occurring in it has degree
`a`. -/
theorem mem_monomialDegreePiece {a : ι} {c : GridChainMinus R n} :
    c ∈ monomialDegreePiece R deg a ↔ ∀ x : GridState n, ∀ e ∈ (c x).support, deg x e = a := by
  simp only [monomialDegreePiece, mem_monomialDegreeSupported, Set.mem_singleton_iff]

variable (R deg) in
/-- A single monomial generator `V^e · x`, with any coefficient, is homogeneous of its own
degree. -/
theorem single_monomial_mem_monomialDegreePiece (x : GridState n) (e : Fin n →₀ ℕ) (b : R) :
    (Finsupp.single x (monomial e b) : GridChainMinus R n) ∈
      monomialDegreePiece R deg (deg x e) := by
  rw [mem_monomialDegreePiece]
  intro z f hf
  rcases eq_or_ne z x with rfl | hzx
  · rw [Finsupp.single_eq_same] at hf
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hf)]
  · rw [Finsupp.single_eq_of_ne hzx] at hf
    simp at hf

/-- Multiplying by the monomial `V^d` sends chains homogeneous of degree `a` to chains homogeneous
of degree `φ a` when it moves the degree of every monomial generator by `φ`. -/
theorem monomial_smul_mem_monomialDegreePiece (d : Fin n →₀ ℕ) (b : R) {φ : ι → ι}
    (hφ : ∀ x e, deg x (d + e) = φ (deg x e)) {a : ι} {c : GridChainMinus R n}
    (hc : c ∈ monomialDegreePiece R deg a) :
    (monomial d b : MvPolynomial (Fin n) R) • c ∈ monomialDegreePiece R deg (φ a) := by
  classical
  rw [mem_monomialDegreePiece] at hc ⊢
  intro z f hf
  rw [Finsupp.smul_apply, smul_eq_mul] at hf
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hf)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb), hφ, hc z e he]

/-! ### `GC⁻` is the direct sum of the pieces -/

variable (R deg)

/-- The pieces of `GC⁻` span it: every chain is a finite sum of monomial multiples of grid-state
generators. -/
theorem iSup_monomialDegreePiece_eq_top : ⨆ a, monomialDegreePiece R deg a = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro c -
  induction c using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add x p c _ _ ih =>
    refine Submodule.add_mem _ ?_ ih
    have hp : (Finsupp.single x p : GridChainMinus R n) =
        ∑ e ∈ p.support, Finsupp.single x (monomial e (p.coeff e)) := by
      conv_lhs => rw [MvPolynomial.as_sum p]
      exact map_sum (Finsupp.singleAddHom x) _ _
    rw [hp]
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.mem_iSup_of_mem (deg x e) (single_monomial_mem_monomialDegreePiece R deg x e _)

/-- The pieces of `GC⁻` are independent: every monomial of a chain has exactly one degree. -/
theorem iSupIndep_monomialDegreePiece : iSupIndep (monomialDegreePiece R deg) := by
  intro a
  rw [Submodule.disjoint_def]
  intro c hc hc'
  rw [mem_monomialDegreePiece] at hc
  have hcompl : c ∈ monomialDegreeSupported R deg {a}ᶜ :=
    iSup₂_le (fun _ hb => monomialDegreeSupported_mono (Set.singleton_subset_iff.mpr hb)) hc'
  refine Finsupp.ext fun z => ?_
  rw [Finsupp.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact fun e he =>
    Set.mem_compl_singleton_iff.mp (mem_monomialDegreeSupported.mp hcompl z e he) (hc z e he)

end Semiring

section Ring

variable {n : ℕ} (R : Type*) [CommRing R] {ι : Type*} [DecidableEq ι]
  (deg : GridState n → (Fin n →₀ ℕ) → ι)

/-- `GC⁻` is the internal direct sum of its pieces of each degree.

The coefficient ring is a `CommRing` here because independence plus spanning gives an internal
direct sum only over a ring (`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`). -/
theorem isInternal_monomialDegreePiece : DirectSum.IsInternal (monomialDegreePiece R deg) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_monomialDegreePiece R deg) (iSup_monomialDegreePiece_eq_top R deg)

/-- The internal grading of `GC⁻` over the coefficient ring `R` by the degrees `deg x e` of its
monomial generators `V^e · x`. -/
noncomputable def monomialDegreeGrading : InternalGrading R (GridChainMinus R n) ι :=
  ⟨monomialDegreePiece R deg, isInternal_monomialDegreePiece R deg⟩

/-- The pieces of the grading by monomial degrees are the homogeneous pieces. -/
@[simp]
theorem monomialDegreeGrading_piece (a : ι) :
    (monomialDegreeGrading R deg).piece a = monomialDegreePiece R deg a :=
  (rfl)

end Ring

end GridChainMinus

namespace GridDiagram

open GridChainMinus

variable {n : ℕ} (G : GridDiagram n) {R : Type*} [CommSemiring R] {ι : Type*}
  {deg : GridState n → (Fin n →₀ ℕ) → ι}

/-- The unblocked grid differential sends chains homogeneous of degree `a` to chains homogeneous of
degree `φ a` when every rectangle it counts, together with multiplication by its weight `V^{O(r)}`,
moves the degree of every monomial generator by `φ`. -/
theorem unblockedDifferential_mem_monomialDegreePiece {φ : ι → ι}
    (hφ : ∀ x y : GridState n, ∀ r ∈ G.unblockedRectangles x y, ∀ e,
      deg y (e + ∑ c ∈ G.OColumns r.toGridRectangle, Finsupp.single c 1) = φ (deg x e))
    {a : ι} {c : GridChainMinus R n} (hc : c ∈ monomialDegreePiece R deg a) :
    G.unblockedDifferential R c ∈ monomialDegreePiece R deg (φ a) := by
  classical
  rw [mem_monomialDegreePiece] at hc ⊢
  intro z f hf
  rw [unblockedDifferential_apply_apply, Finsupp.sum] at hf
  obtain ⟨w, -, hfw⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hf)
  obtain ⟨e, he, d, hd, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hfw)
  obtain ⟨r, hr, rfl⟩ := G.exists_mem_unblockedRectangles_of_mem_support_unblockedCoefficient R hd
  rw [hφ w z r hr e, hc w e he]

end GridDiagram

end TauCeti
