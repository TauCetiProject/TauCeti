/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Branching

/-!
# Stability of the symmetric polynomials of a fixed degree

Setting the last of `d + 1` variables to zero sends the Schur polynomial of a partition in
`d + 1` variables to its Schur polynomial in `d` variables (`TauCeti.aeval_snoc_zero_schurPoly`,
the partition-indexed form of `TauCeti.aeval_snoc_zero_diagramSchurPoly`). Since the Schur
polynomials of the partitions of `n` are a basis of the symmetric polynomials of degree `n` in at
least `n` variables, this specialization is injective on the symmetric polynomials of degree `n`
as long as `n ≤ d` (`TauCeti.injOn_aeval_snoc_zero_symmetricHomogeneousSubmodule`).

## Main results

* `TauCeti.aeval_snoc_zero_schurPoly`: the Schur polynomials are stable under setting the last
  variable to zero.
* `TauCeti.injOn_aeval_snoc_zero_symmetricHomogeneousSubmodule`: for `n ≤ d`, setting the last of
  `d + 1` variables to zero is injective on the symmetric polynomials of degree `n`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Sections 2 and 3: the restriction `Λⁿ_{d+1} → Λⁿ_d` is an isomorphism for `d ≥ n`.
-/

public section

namespace TauCeti

open MvPolynomial

variable {R : Type*} {n : ℕ}

/-- The Schur polynomial of a partition in `d + 1` variables becomes the Schur polynomial in `d`
variables once the last variable is set to zero.

Not a `simp` lemma: `simp` rewrites `aeval` to `bind₁` by `MvPolynomial.aeval_eq_bind₁`, so this
left-hand side is not in `simp`-normal form. -/
theorem aeval_snoc_zero_schurPoly [CommSemiring R] (d : ℕ) (μ : n.Partition) :
    aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) R) 0) (schurPoly (Fin (d + 1)) R μ) =
      schurPoly (Fin d) R μ := by
  rw [schurPoly_eq_rename, schurPoly_eq_rename, rename_diagramSchurPoly, rename_diagramSchurPoly,
    aeval_snoc_zero_diagramSchurPoly]

/-- **Stability in degree `n`**: as long as `n ≤ d`, setting the last of `d + 1` variables to zero
loses no information about a symmetric polynomial of degree `n`. The Schur polynomials of the
partitions of `n` are a basis on both sides, and setting a variable to zero matches them up.
For `d < n` this fails: `s_((1,1))` vanishes in one variable. -/
theorem injOn_aeval_snoc_zero_symmetricHomogeneousSubmodule [CommRing R] {d : ℕ} (hn : n ≤ d) :
    Set.InjOn (aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) R) 0))
      (symmetricHomogeneousSubmodule (Fin (d + 1)) R n : Set (MvPolynomial (Fin (d + 1)) R)) := by
  let φ : symmetricHomogeneousSubmodule (Fin (d + 1)) R n →ₗ[R] MvPolynomial (Fin d) R :=
    (aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) R) 0)).toLinearMap.comp
      (symmetricHomogeneousSubmodule (Fin (d + 1)) R n).subtype
  let b := (schurPolyBasis (Fin (d + 1)) R n).reindex
    (partitionEquivSchurIndex (Fin (d + 1)) n (by simpa using hn.trans d.le_succ)).symm
  have hφ : Function.Injective φ := LinearMap.injective_of_linearIndependent b.span_eq <| by
    convert linearIndependent_schurPoly (σ := Fin d) (R := R) (by simpa using hn) using 1
    funext μ
    simp [φ, b, aeval_snoc_zero_schurPoly]
  exact fun p hp q hq hpq => congrArg Subtype.val (@hφ ⟨p, hp⟩ ⟨q, hq⟩ hpq)

end TauCeti
