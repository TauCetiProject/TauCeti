/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.Basis
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Dimension
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift

/-!
# The dual Weyl lattice of a dominant weight

For a dominant weight `λ = (λ_0 ≥ ⋯ ≥ λ_{N-1})` of `GL_N` and a commutative ring `R`, the dual Weyl
lattice `∇_R(λ)` (`TauCeti.dualWeylLattice R λ`) is the dual Weyl module of the `N × N` matrix of
variables whose column degrees are the entries `λ_s - λ_{N-1}` of the normalised weight `λ⁰`, the
row lengths of the Young diagram `TauCeti.DominantWeight.detShiftShape λ`. `GL_N` acts on the rows,
twisted by `det ^ λ_{N-1}`.

## Main definitions

* `TauCeti.dualWeylLattice R λ`: the dual Weyl lattice `∇_R(λ)`.
* `TauCeti.dualWeylLattice.standardBasis R λ`: its basis of the bideterminants of the
  semistandard tableaux of shape `λ⁰` with entries smaller than `N`.

## Main results

* `TauCeti.mem_dualWeylLattice`: membership unfolded, homogeneity of degree `λ_s - λ_{N-1}` in the
  column `s` and invariance under the column operations.
* `TauCeti.dualWeylLattice.finrank_eq_weylDimension`: over a nontrivial commutative ring (that is,
  one with the strong rank condition) the rank of `∇_R(λ)` is the Weyl dimension of `λ`.

## References

* C. De Concini, D. Eisenbud, C. Procesi, *Young diagrams and determinantal varieties*,
  Invent. Math. **56** (1980), 129-165.
* K. Akin, D. A. Buchsbaum, J. Weyman, *Schur functors and Schur complexes*, Adv. Math. **44**
  (1982), 207-278.
* J. C. Jantzen, *Representations of algebraic groups*, 2nd ed., Math. Surveys Monogr. **107**,
  Amer. Math. Soc. (2003), II.2 (the induced modules `H⁰(λ) = ∇(λ)`).
-/

public section

namespace TauCeti

open MvPolynomial DualWeylModule

variable (R : Type*) [CommRing R] {N : ℕ}

/-- The **dual Weyl lattice** `∇_R(λ)` of a dominant weight `λ` of `GL_N`: the polynomials over
`R` in the `N × N` matrix of variables that are homogeneous of degree `λ_s - λ_{N-1}` in the column
`s` and invariant under every column operation `x ↦ x·(1 + T·e_{st})`, `s < t`. -/
noncomputable def dualWeylLattice (l : DominantWeight N) :
    Submodule R (MvPolynomial (Fin N × Fin N) R) :=
  dualWeylModule R N fun s : Fin N => l.detShiftShape.rowLen s

theorem dualWeylLattice_def (l : DominantWeight N) :
    dualWeylLattice R l = dualWeylModule R N fun s : Fin N => l.detShiftShape.rowLen s :=
  (rfl)

variable {R}

/-- Membership in the dual Weyl lattice of a dominant weight `λ` of `GL_{N+1}`: every monomial
has degree `λ_s - λ_N` in the column `s`, and every column operation `x ↦ x·(1 + T·e_{st})` with
`s < t` fixes the polynomial. -/
theorem mem_dualWeylLattice {l : DominantWeight (N + 1)}
    {f : MvPolynomial (Fin (N + 1) × Fin (N + 1)) R} :
    f ∈ dualWeylLattice R l ↔
      (∀ m ∈ f.support, ∀ s, ∑ a, m (a, s) = (l.val s - l.val (Fin.last N)).toNat) ∧
        ∀ s t : Fin (N + 1), s < t → columnOperation R s t f = Polynomial.C f := by
  simp [dualWeylLattice_def, mem_dualWeylModule]

namespace dualWeylLattice

variable (R) (l : DominantWeight N)

/-- The **standard bideterminant basis** of the dual Weyl lattice `∇_R(λ)` over a commutative
ring `R`, indexed by the semistandard tableaux of shape `λ⁰` with entries smaller than `N`. -/
noncomputable def standardBasis :
    Module.Basis (BoundedSSYT N l.detShiftShape) R (dualWeylLattice R l) :=
  DualWeylModule.standardBasis R N (DominantWeight.colLen_zero_detShiftShape_le l)

@[simp]
theorem coe_standardBasis (T : BoundedSSYT N l.detShiftShape) :
    (standardBasis R l T : MvPolynomial (Fin N × Fin N) R) =
      bideterminant R _ (DominantWeight.colLen_zero_detShiftShape_le l) (ssytFilling T) :=
  DualWeylModule.coe_standardBasis R N _ T

/-- **The rank of the dual Weyl lattice is the Weyl dimension**: the number of semistandard
tableaux of shape `λ⁰` with entries smaller than `N`, which is `dim V_λ`. -/
theorem finrank_eq_weylDimension [StrongRankCondition R] :
    Module.finrank R (dualWeylLattice R l) = weylDimension l := by
  rw [Module.finrank_eq_card_basis (standardBasis R l), ← Nat.card_eq_fintype_card,
    ← GTPattern.card_topWeight_eq_card_boundedSSYT_detShiftShape,
    GTPattern.card_topWeight_eq_weylDimension]

end dualWeylLattice

end TauCeti
