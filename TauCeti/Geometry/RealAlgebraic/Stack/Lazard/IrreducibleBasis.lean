/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
public import TauCeti.RingTheory.MvPolynomial.IrreducibleBasis.Lazard
public import TauCeti.RingTheory.MvPolynomial.SquarefreeBasis.Lazard

/-!
# Lazard delineations of a family from its irreducible basis

Let `F` be a finite family of polynomials in a distinguished variable over `ℝ[X₀, …, Xₙ₋₁]`, and
let `B` be an irreducible basis of `F` (`Finset.IsIrreducibleBasis`): every member of `F` is its
content times a unit times a product of powers of members of `B`. Read each such polynomial as a
real polynomial in `n + 1` variables whose last variable is the distinguished one, as in
`TauCeti.LazardDelineation`.

A Lazard delineation of the basis over `S ⊆ ℝⁿ` induces a Lazard delineation of the family with
exactly the same root functions, provided the content of every member of `F` has constant Lazard
valuation on `S`. For each nonzero member of `F`, Lazard evaluation is multiplicative, so its
Lazard evaluation is a nonzero constant times a product of powers of the Lazard evaluations of
the basis members.
Hence its roots are basis roots, its root multiplicities are fixed weighted sums of the basis
multiplicities, and its removed base exponents are the content exponents plus a fixed weighted
sum of the basis exponents. Zero members are allowed; the root-coverage condition for a Lazard
delineation applies only to nonzero members. Every section of the basis stack is a root of some
nonzero member of `F`, since each basis member divides one.

No connectedness, analyticity or preservation of ordinary fibre degrees is needed. Nonzero
members of `F` may be nullified at points of `S`, and their contents may vanish.
This is the passage from the basis to the original family in Lazard's lifting: once the basis
has a Lazard delineation over a cell on which the Lazard projection is valuation-invariant, every
original input is valuation-invariant, hence sign-invariant, on each section and sector above it
(`TauCeti.LazardDelineation.lazardValuation_snoc_eq_of_mem_sectionSet`,
`TauCeti.LazardDelineation.signInvariant_sectionSet` and their sector versions).

## Main definitions and results

* `TauCeti.LazardDelineation.ofIrreducibleBasis`: the Lazard delineation of a family induced by a
  Lazard delineation of its irreducible basis.
* `TauCeti.LazardDelineation.ofIrreducibleBasis_count`,
  `TauCeti.LazardDelineation.ofIrreducibleBasis_root`: it has the same ordered root functions.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Sections 2 and 5.
-/

public section

open MvPolynomial

namespace TauCeti.LazardDelineation

variable {n : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))} {S : Set (Fin n → ℝ)}

/-- **Lazard delineation of a family from its irreducible basis.** A Lazard delineation of an
irreducible basis `B` of `F` over `S` induces a Lazard delineation of `F` with the same ordered
root functions, provided the content of every member of `F` has constant Lazard valuation on `S`.
Members of `F` may be nullified at points of `S`; no connectedness of `S` is needed. -/
noncomputable def ofIrreducibleBasis
    (D : LazardDelineation
      (fun b : B ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm b.1)) S)
    (hB : F.IsIrreducibleBasis B)
    (hc : ∀ f ∈ F, ∀ x ∈ S, ∀ y ∈ S,
      f.content.lazardValuation x = f.content.lazardValuation y) :
    LazardDelineation
      (fun f : F ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm f.1)) S :=
  let e := (optionEquivLeft ℝ (Fin n)).symm.trans (optionEquivRight ℝ (Fin n))
  let x₀ : S := ⟨D.nonempty.some, D.nonempty.some_mem⟩
  -- Putting the distinguished variable last and moving it back into the coefficients is the
  -- coefficient swap `e` of the irreducible-basis reconstruction of Lazard evaluations.
  have hswap (f : Polynomial (MvPolynomial (Fin n) ℝ)) :
      optionEquivRight ℝ (Fin n) (rename finSuccEquivLast
        (rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm f))) = e f := by
    rw [rename_rename, Equiv.self_comp_symm, rename_id_apply, AlgEquiv.trans_apply]
  -- The basis data of `D`, restated through `e`.
  have hexp (b : Polynomial (MvPolynomial (Fin n) ℝ)) (hb : b ∈ B) (x : S) :
      (e b).lazardExponent (Polynomial.C ∘ x.1) = D.exponent ⟨b, hb⟩ := by
    rw [← D.lazardExponent_eq ⟨b, hb⟩ x, hswap]
  have hmul (b : Polynomial (MvPolynomial (Fin n) ℝ)) (hb : b ∈ B) (i : Fin D.count) (x : S) :
      ((e b).lazardEval (Polynomial.C ∘ x.1)).rootMultiplicity (D.root i x) =
        D.multiplicity ⟨b, hb⟩ i := by
    rw [← D.rootMultiplicity_root ⟨b, hb⟩ i x, hswap]
  { nonempty := D.nonempty
    count := D.count
    root := D.root
    continuous_root := D.continuous_root
    strictMono_root := D.strictMono_root
    exponent f := (e f.1).lazardExponent (Polynomial.C ∘ x₀.1)
    lazardExponent_eq f x := by
      rw [hswap]
      refine hB.isSquarefreeBasis.lazardExponent_eq f.2 ?_
        fun b hb ↦ (hexp b hb x).trans (hexp b hb x₀).symm
      -- Constant content valuation gives constant content exponents, including content `0`.
      obtain h0 | h0 := eq_or_ne f.1.content 0
      · simp [h0]
      · have h := hc f.1 f.2 x x.2 x₀ x₀.2
        rw [lazardValuation_eq_lazardExponent h0, lazardValuation_eq_lazardExponent h0] at h
        exact toLex.injective (WithTop.coe_injective h)
    multiplicity f i := ((e f.1).lazardEval (Polynomial.C ∘ x₀.1)).rootMultiplicity (D.root i x₀)
    rootMultiplicity_root f i x := by
      rw [hswap]
      exact hB.rootMultiplicity_lazardEval_eq f.2 fun b hb ↦
        (hmul b hb i x).trans (hmul b hb i x₀).symm
    exists_root_eq f x hf t ht := by
      rw [hswap] at ht
      have hf0 : f.1 ≠ 0 := by
        rintro h
        exact hf (by simp only [h, map_zero])
      -- A root of a nonzero input is a root of a basis member, hence a section value.
      obtain ⟨b, hb, hbt⟩ := (hB.exists_isRoot_lazardEval_iff x.1 t).1 ⟨f.1, f.2, hf0, ht⟩
      refine D.exists_root_eq ⟨b, hb⟩ x ?_ t (by rwa [hswap])
      exact (map_ne_zero_iff _ (rename_injective _ finSuccEquivLast.symm.injective)).2
        (EmbeddingLike.map_ne_zero_iff.2 (hB.irreducible b hb).ne_zero)
    exists_multiplicity_pos i := by
      -- Each section is a root of a basis member, which divides a nonzero input.
      obtain ⟨⟨b, hb⟩, hpos⟩ := D.exists_multiplicity_pos i
      rw [← hmul b hb i x₀] at hpos
      obtain ⟨f, hf, hf0, hft⟩ := (hB.exists_isRoot_lazardEval_iff x₀.1 (D.root i x₀)).2
        ⟨b, hb, (Polynomial.rootMultiplicity_pos'.1 hpos).2⟩
      exact ⟨⟨f, hf⟩, (Polynomial.rootMultiplicity_pos
        (lazardEval_ne_zero (EmbeddingLike.map_ne_zero_iff.2 hf0) _)).2 hft⟩ }

variable (D : LazardDelineation
    (fun b : B ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm b.1)) S)
  (hB : F.IsIrreducibleBasis B)
  (hc : ∀ f ∈ F, ∀ x ∈ S, ∀ y ∈ S, f.content.lazardValuation x = f.content.lazardValuation y)

/-- Passing from a basis to its family preserves the number of sections. -/
@[simp]
theorem ofIrreducibleBasis_count : (D.ofIrreducibleBasis hB hc).count = D.count :=
  (rfl)

/-- Passing from a basis to its family preserves the ordered root functions. -/
@[simp]
theorem ofIrreducibleBasis_root (i : Fin (D.ofIrreducibleBasis hB hc).count) (x : S) :
    (D.ofIrreducibleBasis hB hc).root i x =
      D.root (Fin.cast (D.ofIrreducibleBasis_count hB hc) i) x :=
  (rfl)

end TauCeti.LazardDelineation
