/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.BasisToDual
public import TauCeti.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.HallInner
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Algebra

/-!
# The Hall inner product on the symmetric functions

The **Hall inner product** on the ring `Λ_R` of symmetric functions over a commutative ring is the
symmetric bilinear form for which the Schur functions `s_μ`, over all partitions `μ` of all
degrees, are orthonormal. Symmetric functions of different degrees are orthogonal.

In degree `n` the form is `TauCeti.stableHallInner R n`, the dot product of coordinates in the
Schur basis `TauCeti.stableSchurBasis R n`. It is the Hall inner product of symmetric polynomials
`TauCeti.hallInner` read through the projection to any alphabet `Fin d` with `n ≤ d`
(`TauCeti.hallInner_stableSymmetricProj`), so it does not depend on the alphabet. Below degree the
projection forgets the Schur functions of the partitions with more than `d` parts (they vanish in
`d` variables, `TauCeti.schurPoly_eq_zero_of_card_lt`), so it does not preserve the form: `s_(1,1)`
has norm `1`, while its image in one variable is `0`.

Through this comparison the orthogonality of the power sums in finitely many variables passes to
the symmetric functions: `⟨p_μ, p_ν⟩ = z_μ δ_(μν)` for the power-sum products `p_μ`. That needs the
character table of the symmetric group, and is proved in
`TauCeti/RepresentationTheory/Symmetric/StableHallInner.lean`.

On all of `Λ_R` the Hall inner product `TauCeti.SymmetricFunction.hallInner R` is defined by the
Schur basis `TauCeti.SymmetricFunction.schurBasis R`, indexed by `Σ n, n.Partition`, which collects
the Schur bases of all degrees. It restricts to `TauCeti.stableHallInner R n` in degree `n`
(`TauCeti.SymmetricFunction.hallInner_of_of`) and pairs different degrees to zero
(`TauCeti.SymmetricFunction.hallInner_of_of_of_ne`), so it is the sum over all degrees of the Hall
inner products of the homogeneous components (`TauCeti.SymmetricFunction.hallInner_apply`).

## Main definitions

* `TauCeti.stableHallInner R n`: the Hall inner product on the symmetric functions of degree `n`.
* `TauCeti.SymmetricFunction.schurBasis R`: the basis of `Λ_R` consisting of the Schur functions.
* `TauCeti.SymmetricFunction.hallInner R`: the Hall inner product on `Λ_R`.

## Main results

* `TauCeti.stableHallInner_stableSchur`: the Schur functions of degree `n` are orthonormal.
* `TauCeti.hallInner_stableSymmetricProj`: in an alphabet of at least `n` letters, projection is
  an isometry from `TauCeti.stableHallInner R n` to the Hall inner product of symmetric
  polynomials.
* `TauCeti.SymmetricFunction.hallInner_schurBasis`: the Schur functions of all degrees are
  orthonormal.
* `TauCeti.SymmetricFunction.hallInner_apply`: the Hall inner product on `Λ_R` is the sum of the
  Hall inner products of the homogeneous components.
* `TauCeti.SymmetricFunction.isSymm_hallInner`, `TauCeti.SymmetricFunction.nondegenerate_hallInner`:
  the Hall inner product on `Λ_R` is symmetric and nondegenerate.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 4, (4.5)–(4.8): the scalar product on `Λ` and the orthonormality of the Schur functions.
-/

public section

namespace TauCeti

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ### The Hall inner product in a fixed degree -/

variable (R n) in
/-- **The Hall inner product on the symmetric functions of degree `n`**: the bilinear form in which
the Schur functions `s_μ` of the partitions `μ` of `n` are orthonormal
(`TauCeti.stableHallInner_stableSchur`). It is the dot product of the coordinates in the Schur
basis (`TauCeti.stableHallInner_apply`), and agrees with the Hall inner product of symmetric
polynomials in any alphabet of at least `n` letters (`TauCeti.hallInner_stableSymmetricProj`). -/
noncomputable def stableHallInner : LinearMap.BilinForm R (stableSymmetricSubmodule R n) :=
  (stableSchurBasis R n).toDual

/-- **Pairing with a Schur function on the right reads off the Schur coordinate.** -/
@[simp]
theorem stableHallInner_stableSchur_right (f : stableSymmetricSubmodule R n) (μ : n.Partition) :
    stableHallInner R n f (stableSchur R μ) = (stableSchurBasis R n).repr f μ := by
  rw [← stableSchurBasis_apply]
  exact Module.Basis.toDual_apply_left _ f μ

/-- **Pairing with a Schur function on the left reads off the Schur coordinate.** -/
@[simp]
theorem stableHallInner_stableSchur_left (μ : n.Partition) (f : stableSymmetricSubmodule R n) :
    stableHallInner R n (stableSchur R μ) f = (stableSchurBasis R n).repr f μ := by
  rw [← stableSchurBasis_apply]
  exact Module.Basis.toDual_apply_right _ μ f

/-- **The Schur functions are orthonormal for the Hall inner product**: `⟨s_μ, s_ν⟩ = δ_(μν)`. It
is not a `simp` lemma: `TauCeti.stableHallInner_stableSchur_right` and
`TauCeti.stableSchurBasis_repr_stableSchur` already prove it. -/
theorem stableHallInner_stableSchur (μ ν : n.Partition) :
    stableHallInner R n (stableSchur R μ) (stableSchur R ν) = if μ = ν then 1 else 0 := by
  simp [Finsupp.single_apply]

/-- **The Hall inner product is the dot product of Schur coordinates.** -/
theorem stableHallInner_apply (f g : stableSymmetricSubmodule R n) :
    stableHallInner R n f g =
      ∑ μ, (stableSchurBasis R n).repr f μ * (stableSchurBasis R n).repr g μ :=
  Module.Basis.toDual_apply_eq_sum _ f g

/-- **The Hall inner product is symmetric.** -/
theorem stableHallInner_comm (f g : stableSymmetricSubmodule R n) :
    stableHallInner R n f g = stableHallInner R n g f :=
  Module.Basis.toDual_comm _ f g

/-- **The Hall inner product is a symmetric bilinear form.** -/
theorem isSymm_stableHallInner : (stableHallInner R n).IsSymm :=
  Module.Basis.isSymm_toDual _

/-- **The Hall inner product is nondegenerate**: a symmetric function orthogonal to every Schur
function has all its Schur coordinates `0`. -/
theorem nondegenerate_stableHallInner : (stableHallInner R n).Nondegenerate :=
  Module.Basis.nondegenerate_toDual _

/-- **The Hall inner product of symmetric functions is the Hall inner product of their projections
to any alphabet of at least `n` letters.** In particular it does not depend on the alphabet. With
fewer letters this fails: `s_(1,1)` has norm `1` but projects to `0` in one variable. -/
theorem hallInner_stableSymmetricProj {d : ℕ} (hn : n ≤ d) (f g : stableSymmetricSubmodule R n) :
    hallInner (Fin d) R n (stableSymmetricProj R n d f) (stableSymmetricProj R n d g) =
      stableHallInner R n f g := by
  rw [hallInner_apply, stableHallInner_apply]
  exact (Fintype.sum_equiv (partitionEquivSchurIndex (Fin d) n (by simpa using hn)) _ _
    fun μ => by rw [stableSchurBasis_repr_apply hn f, stableSchurBasis_repr_apply hn g]).symm

/-! ### The Hall inner product on the ring of symmetric functions -/

namespace SymmetricFunction

open DirectSum

variable (R) in
/-- **The Schur basis of the ring of symmetric functions**: the Schur functions `s_μ`, over all
partitions `μ` of all degrees `n`, indexed by `Σ n, n.Partition`. It collects the Schur bases
`TauCeti.stableSchurBasis R n` of the homogeneous components; its vectors are read off by
`TauCeti.SymmetricFunction.schurBasis_apply`. -/
noncomputable def schurBasis : Module.Basis (Σ n : ℕ, n.Partition) R (SymmetricFunction R) :=
  DFinsupp.basis fun n => stableSchurBasis R n

/-- **The vectors of the Schur basis of `Λ_R` are the Schur functions.** -/
@[simp]
theorem schurBasis_apply (μ : Σ n : ℕ, n.Partition) :
    schurBasis R μ = of _ μ.1 (stableSchur R μ.2) := by
  rw [schurBasis, DFinsupp.basis_apply, stableSchurBasis_apply]
  -- `DirectSum.of` is `DFinsupp.single`, bundled as an additive monoid homomorphism.
  rfl

/-- **The Schur coordinates of a symmetric function are the Schur coordinates of its homogeneous
components.** -/
@[simp]
theorem schurBasis_repr_apply (x : SymmetricFunction R) (μ : Σ n : ℕ, n.Partition) :
    (schurBasis R).repr x μ = (stableSchurBasis R μ.1).repr (x μ.1) μ.2 :=
  DFinsupp.basis_repr _ x μ

variable (R) in
/-- **The Hall inner product on the ring of symmetric functions**: the bilinear form in which the
Schur functions of all degrees are orthonormal (`TauCeti.SymmetricFunction.hallInner_schurBasis`).
In each degree `n` it is `TauCeti.stableHallInner R n`
(`TauCeti.SymmetricFunction.hallInner_of_of`), and symmetric functions of different degrees are
orthogonal (`TauCeti.SymmetricFunction.hallInner_of_of_of_ne`). -/
noncomputable def hallInner : LinearMap.BilinForm R (SymmetricFunction R) :=
  (schurBasis R).toDual

/-- **The Schur functions of all degrees are orthonormal for the Hall inner product.** It is not a
`simp` lemma, since `TauCeti.SymmetricFunction.schurBasis_apply` rewrites its left side. -/
theorem hallInner_schurBasis (μ ν : Σ n : ℕ, n.Partition) :
    hallInner R (schurBasis R μ) (schurBasis R ν) = if μ = ν then 1 else 0 :=
  Module.Basis.toDual_apply _ μ ν

/-- **Pairing with a Schur function of degree `n` on the right reads off a Schur coordinate of the
homogeneous component of degree `n`.** -/
@[simp]
theorem hallInner_of_stableSchur_right (x : SymmetricFunction R) (μ : n.Partition) :
    hallInner R x (of _ n (stableSchur R μ)) = (stableSchurBasis R n).repr (x n) μ := by
  have h := Module.Basis.toDual_apply_left (schurBasis R) x ⟨n, μ⟩
  rw [schurBasis_apply, schurBasis_repr_apply] at h
  exact h

/-- **Pairing with a Schur function of degree `n` on the left reads off a Schur coordinate of the
homogeneous component of degree `n`.** -/
@[simp]
theorem hallInner_of_stableSchur_left (μ : n.Partition) (x : SymmetricFunction R) :
    hallInner R (of _ n (stableSchur R μ)) x = (stableSchurBasis R n).repr (x n) μ := by
  have h := Module.Basis.toDual_apply_right (schurBasis R) ⟨n, μ⟩ x
  rw [schurBasis_apply, schurBasis_repr_apply] at h
  exact h

/-- **In degree `n` the Hall inner product of `Λ_R` is the Hall inner product of the symmetric
functions of degree `n`.** -/
@[simp]
theorem hallInner_of_of (f g : stableSymmetricSubmodule R n) :
    hallInner R (of _ n f) (of _ n g) = stableHallInner R n f g := by
  have : hallInner R (of _ n f) ∘ₗ lof R ℕ _ n = stableHallInner R n f :=
    (stableSchurBasis R n).ext fun μ => by simp [lof_eq_of]
  exact LinearMap.congr_fun this g

/-- **Symmetric functions of different degrees are orthogonal for the Hall inner product.** -/
@[simp]
theorem hallInner_of_of_of_ne {m : ℕ} (h : n ≠ m) (f : stableSymmetricSubmodule R n)
    (g : stableSymmetricSubmodule R m) : hallInner R (of _ n f) (of _ m g) = 0 := by
  have : hallInner R (of _ n f) ∘ₗ lof R ℕ _ m = 0 :=
    (stableSchurBasis R m).ext fun μ => by simp [lof_eq_of, of_eq_of_ne _ _ _ h.symm]
  exact LinearMap.congr_fun this g

/-- **Pairing with a symmetric function of degree `n` on the left pairs it with the homogeneous
component of degree `n`.** -/
theorem hallInner_of_left (f : stableSymmetricSubmodule R n) (y : SymmetricFunction R) :
    hallInner R (of _ n f) y = stableHallInner R n f (y n) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of m g =>
    by_cases h : n = m
    · subst h
      rw [hallInner_of_of, of_eq_same]
    · rw [hallInner_of_of_of_ne h, of_eq_of_ne _ _ _ h, map_zero]
  | add y z hy hz => rw [map_add, hy, hz, DirectSum.add_apply, map_add]

/-- **The Hall inner product on `Λ_R` is the sum over all degrees of the Hall inner products of the
homogeneous components.** -/
theorem hallInner_apply [∀ (i : ℕ) (f : stableSymmetricSubmodule R i), Decidable (f ≠ 0)]
    (x y : SymmetricFunction R) :
    hallInner R x y = ∑ n ∈ x.support, stableHallInner R n (x n) (y n) := by
  conv_lhs => rw [← sum_support_of x]
  simp only [map_sum, LinearMap.sum_apply, hallInner_of_left]

/-- **The Hall inner product on `Λ_R` is symmetric.** -/
theorem hallInner_comm (x y : SymmetricFunction R) : hallInner R x y = hallInner R y x :=
  Module.Basis.toDual_comm _ x y

/-- **The Hall inner product on `Λ_R` is a symmetric bilinear form.** -/
theorem isSymm_hallInner : (hallInner R).IsSymm :=
  Module.Basis.isSymm_toDual _

/-- **The Hall inner product on `Λ_R` is nondegenerate.** -/
theorem nondegenerate_hallInner : (hallInner R).Nondegenerate :=
  Module.Basis.nondegenerate_toDual _

end SymmetricFunction

end TauCeti
