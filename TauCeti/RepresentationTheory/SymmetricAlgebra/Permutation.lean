/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous

/-!
# Invariants of a permutation representation

Let a group `G` act on a finite set `σ`, and so linearly on the permutation module `K[σ]` with
basis the points of `σ` (`Representation.ofMulAction`). The polynomial functions on `K[σ]` form
`Sym(K[σ]*)`, the symmetric algebra on the dual, with the contragredient action. The coordinate
functions `xᵢ`, the basis dual to the points, identify `Sym(K[σ]*)` with the polynomial ring
`K[xᵢ | i ∈ σ]` (`SymmetricAlgebra.equivMvPolynomial`), and under this identification `g` acts by
renaming each variable `xᵢ` to `x_(g • i)`. So the invariant polynomials of `G` are the
polynomials fixed by these renamings.

For the full symmetric group `S_σ`, the invariants are the symmetric polynomials. By the
fundamental theorem of symmetric polynomials (`MvPolynomial.esymmAlgEquiv`), if `σ` has `n`
elements then the invariant algebra `Sym(K[σ]*)^(S_σ)` is a polynomial algebra on the `n`
elementary symmetric invariants `e₁, …, eₙ`, where `eₖ` is homogeneous of degree `k`. Thus the
degrees of the basic invariants of the full permutation representation are `1, 2, …, n`. The
degree-one invariant `e₁ = ∑ᵢ xᵢ` is a genuine invariant linear form, not an artifact of
conventions: it spans the invariant linear forms on `K[σ]`. When `n` is invertible in `K`, `K[σ]`
is the direct sum of the fixed line spanned by `∑ᵢ i` and the trace-zero hyperplane `e₁ = 0`, on
which `S_σ` acts by its reflection representation. That representation omits the trivial summand
and its basic invariants have degrees `2, …, n` instead; it is not treated here.

No hypothesis on `K` beyond commutativity is needed: the fundamental theorem holds over every
commutative ring, including in characteristic dividing `n!`, where the group order is not
invertible. The cases `n = 0` and `n = 1` are included: the invariant algebra is then `K` or
`K[x]`.

## Main results

* `Representation.ofMulAction_dual_dualBasis`: the contragredient action permutes the coordinate
  functions.
* `Representation.equivMvPolynomial_symmetricAlgebra_ofMulAction_dual`: on polynomials in the
  coordinates, `g` acts by renaming the variables along `g • ·`.
* `Representation.mem_symmetricAlgebraInvariants_ofMulAction_dual_iff`: a polynomial function is
  invariant exactly when its coordinate polynomial is fixed by these renamings.
* `Representation.map_symmetricAlgebraInvariants_ofMulAction_perm_dual`: for the symmetric group
  the invariants are the symmetric polynomials.
* `Representation.symmetricAlgebraInvariantsPermEquiv`: the invariant algebra of the symmetric
  group is isomorphic to `MvPolynomial.symmetricSubalgebra`.
* `Representation.esymmSymmetricAlgebraInvariantsEquiv`: **the invariant algebra of the full
  permutation representation of `S_σ` is a polynomial algebra** on the elementary symmetric
  invariants, with `coe_esymmSymmetricAlgebraInvariantsEquiv_X` computing the generators and
  `esymmSymmetricAlgebraInvariantsEquiv_X_mem_homogeneousSubmodule` giving their degrees
  `1, …, n`.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  Chapter 3.
-/

public section

open MvPolynomial MonoidAlgebra TauCeti.SymmetricAlgebra

namespace Representation

variable (K : Type*) [CommRing K]

section MulAction

variable {G σ : Type*} [Group G] [MulAction G σ] [Finite σ] [DecidableEq σ]

/-- The contragredient of a permutation representation permutes the coordinate functions: `g`
sends the coordinate `xᵢ` to `x_(g • i)`. -/
theorem ofMulAction_dual_dualBasis (g : G) (i : σ) :
    (ofMulAction K G σ).dual g ((MonoidAlgebra.basis σ K).dualBasis i) =
      (MonoidAlgebra.basis σ K).dualBasis (g • i) := by
  refine (MonoidAlgebra.basis σ K).ext fun j ↦ ?_
  rw [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, basis_apply,
    ofMulAction_single]
  simp only [← basis_apply, Module.Basis.dualBasis_apply_self, inv_smul_eq_iff]

/-- In the coordinates of a permutation representation, `g` acts on polynomial functions by
renaming each variable `xᵢ` to `x_(g • i)`. -/
theorem equivMvPolynomial_symmetricAlgebra_ofMulAction_dual (g : G)
    (p : SymmetricAlgebra K (Module.Dual K K[σ])) :
    SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis
        ((ofMulAction K G σ).dual.symmetricAlgebra g p) =
      rename (g • ·)
        (SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis p) := by
  rw [symmetricAlgebra_apply]
  exact SymmetricAlgebra.equivMvPolynomial_map _ _ _ _ (ofMulAction_dual_dualBasis K g) p

/-- A polynomial function on a permutation representation is invariant exactly when its
polynomial in the coordinates is fixed by the renamings `xᵢ ↦ x_(g • i)`. -/
theorem mem_symmetricAlgebraInvariants_ofMulAction_dual_iff
    (p : SymmetricAlgebra K (Module.Dual K K[σ])) :
    p ∈ (ofMulAction K G σ).dual.symmetricAlgebraInvariants ↔
      ∀ g : G, rename (g • ·)
          (SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis p) =
        SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis p := by
  simp only [mem_symmetricAlgebraInvariants,
    ← equivMvPolynomial_symmetricAlgebra_ofMulAction_dual, EmbeddingLike.apply_eq_iff_eq]

end MulAction

section Perm

variable (σ : Type*) [DecidableEq σ]

section Finite

variable [Finite σ]

/-- A polynomial function on the full permutation representation of `S_σ` is invariant exactly
when its polynomial in the coordinates is symmetric. -/
theorem mem_symmetricAlgebraInvariants_ofMulAction_perm_dual_iff
    (p : SymmetricAlgebra K (Module.Dual K K[σ])) :
    p ∈ (ofMulAction K (Equiv.Perm σ) σ).dual.symmetricAlgebraInvariants ↔
      (SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis p).IsSymmetric := by
  rw [mem_symmetricAlgebraInvariants_ofMulAction_dual_iff]
  exact forall_congr' fun g ↦ by rw [show (g • · : σ → σ) = g from funext g.smul_def]

/-- **The invariants of the full permutation representation are the symmetric polynomials**: the
coordinates of `K[σ]` carry the invariant algebra of `S_σ` onto
`MvPolynomial.symmetricSubalgebra`. -/
theorem map_symmetricAlgebraInvariants_ofMulAction_perm_dual :
    (ofMulAction K (Equiv.Perm σ) σ).dual.symmetricAlgebraInvariants.map
        (SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis :
          SymmetricAlgebra K (Module.Dual K K[σ]) →ₐ[K] MvPolynomial σ K) =
      symmetricSubalgebra σ K := by
  have : (ofMulAction K (Equiv.Perm σ) σ).dual.symmetricAlgebraInvariants =
      (symmetricSubalgebra σ K).comap
        (SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis :
          SymmetricAlgebra K (Module.Dual K K[σ]) →ₐ[K] MvPolynomial σ K) :=
    Subalgebra.ext (mem_symmetricAlgebraInvariants_ofMulAction_perm_dual_iff K σ)
  rw [this]
  exact Subalgebra.map_comap_eq_self_of_surjective (AlgEquiv.surjective _) _

/-- The invariant algebra of the full permutation representation of `S_σ` is isomorphic to the
algebra of symmetric polynomials in the coordinates. -/
noncomputable def symmetricAlgebraInvariantsPermEquiv :
    (ofMulAction K (Equiv.Perm σ) σ).dual.symmetricAlgebraInvariants ≃ₐ[K]
      symmetricSubalgebra σ K :=
  ((SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis).subalgebraMap _).trans
    (Subalgebra.equivOfEq _ _ (map_symmetricAlgebraInvariants_ofMulAction_perm_dual K σ))

/-- The isomorphism with the symmetric polynomials takes an invariant to its polynomial in the
coordinates. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsPermEquiv_apply
    (p : (ofMulAction K (Equiv.Perm σ) σ).dual.symmetricAlgebraInvariants) :
    (symmetricAlgebraInvariantsPermEquiv K σ p : MvPolynomial σ K) =
      SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis p :=
  (rfl)

/-- The inverse isomorphism reads a symmetric polynomial in the coordinates as a polynomial
function. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsPermEquiv_symm_apply (q : symmetricSubalgebra σ K) :
    ((symmetricAlgebraInvariantsPermEquiv K σ).symm q : SymmetricAlgebra K (Module.Dual K K[σ])) =
      (SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis).symm q := by
  rw [AlgEquiv.eq_symm_apply, ← coe_symmetricAlgebraInvariantsPermEquiv_apply,
    AlgEquiv.apply_symm_apply]

end Finite

variable [Fintype σ] {n : ℕ}

/-- **The invariants of the full permutation representation of `S_σ` form a polynomial algebra
on the elementary symmetric invariants.** If `σ` has `n` elements, the variable `Xᵢ` is sent to
the elementary symmetric invariant `e_(i + 1)` in the coordinates, which is homogeneous of degree
`i + 1` (`esymmSymmetricAlgebraInvariantsEquiv_X_mem_homogeneousSubmodule`). So the basic
invariants have degrees `1, …, n`. -/
noncomputable def esymmSymmetricAlgebraInvariantsEquiv (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) K ≃ₐ[K]
      (ofMulAction K (Equiv.Perm σ) σ).dual.symmetricAlgebraInvariants :=
  (esymmAlgEquiv σ K hn).trans (symmetricAlgebraInvariantsPermEquiv K σ).symm

/-- The generator `Xᵢ` is sent to the elementary symmetric polynomial of degree `i + 1` in the
coordinates. -/
theorem coe_esymmSymmetricAlgebraInvariantsEquiv_X (hn : Fintype.card σ = n) (i : Fin n) :
    (esymmSymmetricAlgebraInvariantsEquiv K σ hn (X i) :
        SymmetricAlgebra K (Module.Dual K K[σ])) =
      (SymmetricAlgebra.equivMvPolynomial (MonoidAlgebra.basis σ K).dualBasis).symm
        (esymm σ K (i + 1)) := by
  simp [esymmSymmetricAlgebraInvariantsEquiv, esymmAlgHom]

/-- The generator `Xᵢ` is sent to `∑ ∏_(j ∈ t) xⱼ`, the sum over the subsets `t` of `σ` with
`i + 1` elements of the products of their coordinates. -/
@[simp]
theorem coe_esymmSymmetricAlgebraInvariantsEquiv_X_eq_sum (hn : Fintype.card σ = n)
    (i : Fin n) :
    (esymmSymmetricAlgebraInvariantsEquiv K σ hn (X i) :
        SymmetricAlgebra K (Module.Dual K K[σ])) =
      ∑ t ∈ Finset.univ.powersetCard (i + 1), ∏ j ∈ t,
        SymmetricAlgebra.ι K _ ((MonoidAlgebra.basis σ K).dualBasis j) := by
  simp [coe_esymmSymmetricAlgebraInvariantsEquiv_X, esymm]

/-- **The basic invariants of the full permutation representation have degrees `1, …, n`**: the
generator `Xᵢ` is sent to a homogeneous invariant of degree `i + 1`. -/
theorem esymmSymmetricAlgebraInvariantsEquiv_X_mem_homogeneousSubmodule
    (hn : Fintype.card σ = n) (i : Fin n) :
    (esymmSymmetricAlgebraInvariantsEquiv K σ hn (X i) :
        SymmetricAlgebra K (Module.Dual K K[σ])) ∈
      homogeneousSubmodule K (Module.Dual K K[σ]) (i + 1) := by
  rw [coe_esymmSymmetricAlgebraInvariantsEquiv_X,
    ← SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff
      (b := (MonoidAlgebra.basis σ K).dualBasis),
    AlgEquiv.apply_symm_apply]
  exact isHomogeneous_esymm _

end Perm

end Representation
