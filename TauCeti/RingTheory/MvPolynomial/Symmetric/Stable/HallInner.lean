/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.RepresentationTheory.Symmetric.FrobeniusCharacteristic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Generators

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
the symmetric functions: `⟨p_μ, p_ν⟩ = z_μ δ_(μν)` for the power-sum products `p_μ`
(`TauCeti.stableHallInner_stablePsumPart`), where `z_μ` is the order of the centralizer of a
permutation of cycle type `μ` (`TauCeti.zPart`).

On all of `Λ_R` the Hall inner product `TauCeti.SymmetricFunction.hallInner R` is defined by the
Schur basis `TauCeti.SymmetricFunction.schurBasis R`, indexed by `Σ n, n.Partition`, which collects
the Schur bases of all degrees. It restricts to `TauCeti.stableHallInner R n` in degree `n`
(`TauCeti.SymmetricFunction.hallInner_of_of`) and pairs different degrees to zero
(`TauCeti.SymmetricFunction.hallInner_of_of_of_ne`).

## Main definitions

* `TauCeti.stableHallInner R n`: the Hall inner product on the symmetric functions of degree `n`.
* `TauCeti.SymmetricFunction.schurBasis R`: the basis of `Λ_R` consisting of the Schur functions.
* `TauCeti.SymmetricFunction.hallInner R`: the Hall inner product on `Λ_R`.

## Main results

* `TauCeti.stableHallInner_stableSchur`: the Schur functions of degree `n` are orthonormal.
* `TauCeti.hallInner_stableSymmetricProj`: in an alphabet of at least `n` letters, projection is
  an isometry from `TauCeti.stableHallInner R n` to the Hall inner product of symmetric
  polynomials.
* `TauCeti.stableHallInner_stablePsumPart`: **the power sums are orthogonal**,
  `⟨p_μ, p_ν⟩ = z_μ δ_(μν)`.
* `TauCeti.SymmetricFunction.hallInner_schurBasis`: the Schur functions of all degrees are
  orthonormal.
* `TauCeti.SymmetricFunction.isSymm_hallInner`, `TauCeti.SymmetricFunction.nondegenerate_hallInner`:
  the Hall inner product on `Λ_R` is symmetric and nondegenerate.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 4, (4.5)–(4.8): the scalar product on `Λ`, the orthonormality of the Schur functions
  and the orthogonality of the power sums.
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
      ∑ μ, (stableSchurBasis R n).repr f μ * (stableSchurBasis R n).repr g μ := by
  conv_lhs => rw [← (stableSchurBasis R n).sum_repr g]
  simp only [map_sum, map_smul, stableSchurBasis_apply, stableHallInner_stableSchur_right,
    smul_eq_mul, mul_comm]

/-- **The Hall inner product is symmetric.** -/
theorem stableHallInner_comm (f g : stableSymmetricSubmodule R n) :
    stableHallInner R n f g = stableHallInner R n g f := by
  simp only [stableHallInner_apply, mul_comm]

/-- **The Hall inner product is a symmetric bilinear form.** -/
theorem isSymm_stableHallInner : (stableHallInner R n).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr stableHallInner_comm

/-- **The Hall inner product is nondegenerate**: a symmetric function orthogonal to every Schur
function has all its Schur coordinates `0`. -/
theorem nondegenerate_stableHallInner : (stableHallInner R n).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (stableHallInner R n) := fun f hf =>
    (stableSchurBasis R n).ext_elem fun μ => by
      rw [← stableHallInner_stableSchur_right, hf, map_zero, Finsupp.zero_apply]
  exact ⟨hl, fun g hg => hl g fun f => by rw [stableHallInner_comm]; exact hg f⟩

/-- **The Hall inner product of symmetric functions is the Hall inner product of their projections
to any alphabet of at least `n` letters.** In particular it does not depend on the alphabet. With
fewer letters this fails: `s_(1,1)` has norm `1` but projects to `0` in one variable. -/
theorem hallInner_stableSymmetricProj {d : ℕ} (hn : n ≤ d) (f g : stableSymmetricSubmodule R n) :
    hallInner (Fin d) R n (stableSymmetricProj R n d f) (stableSymmetricProj R n d g) =
      stableHallInner R n f g := by
  rw [hallInner_apply, stableHallInner_apply]
  exact (Fintype.sum_equiv (partitionEquivSchurIndex (Fin d) n (by simpa using hn)) _ _
    fun μ => by rw [stableSchurBasis_repr_apply hn f, stableSchurBasis_repr_apply hn g]).symm

/-- **The power sums are orthogonal for the Hall inner product**: `⟨p_μ, p_ν⟩ = z_μ δ_(μν)` for
the power-sum products of partitions of `n`, where `z_μ = ∏ᵢ i^(mᵢ) mᵢ!` is the order of the
centralizer of a permutation of cycle type `μ` (`TauCeti.zPart`). This holds over every commutative
ring. -/
@[simp]
theorem stableHallInner_stablePsumPart (μ ν : n.Partition) :
    stableHallInner R n (stablePsumPart R μ) (stablePsumPart R ν) =
      if μ = ν then (zPart μ : R) else 0 := by
  have h (ρ : n.Partition) : stableSymmetricProj R n n (stablePsumPart R ρ) =
      ⟨psumPart (Fin n) R ρ, psumPart_mem_symmetricHomogeneousSubmodule R ρ⟩ :=
    Subtype.ext (coe_stableSymmetricProj_stablePsumPart R ρ n)
  rw [← hallInner_stableSymmetricProj le_rfl, h, h, hallInner_psumPart (by simp)]

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
  classical
  have h : schurBasis R μ = DFinsupp.single μ.1 (stableSchur R μ.2) := by
    simp [schurBasis, DFinsupp.basis, Module.Basis.coe_ofRepr,
      DFinsupp.mapRange.linearEquiv_apply]
  -- `DirectSum.of` is `DFinsupp.single`, bundled as an additive monoid homomorphism.
  exact h

/-- **The Schur coordinates of a symmetric function are the Schur coordinates of its homogeneous
components.** -/
@[simp]
theorem schurBasis_repr_apply (x : SymmetricFunction R) (μ : Σ n : ℕ, n.Partition) :
    (schurBasis R).repr x μ = (stableSchurBasis R μ.1).repr (x μ.1) μ.2 := by
  -- `DFinsupp.basis` reads off coordinates componentwise through `sigmaFinsuppEquivDFinsupp`, whose
  -- inverse evaluates `f ⟨n, μ⟩` as `f n μ` by definition (`sigmaFinsuppEquivDFinsupp_symm_apply`).
  rfl

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

/-- **The Hall inner product on `Λ_R` is symmetric.** -/
theorem hallInner_comm (x y : SymmetricFunction R) : hallInner R x y = hallInner R y x := by
  have : (hallInner R).flip = hallInner R :=
    LinearMap.BilinForm.ext_basis (schurBasis R) fun μ ν =>
      (hallInner_schurBasis ν μ).trans ((if_congr eq_comm rfl rfl).trans
        (hallInner_schurBasis μ ν).symm)
  exact LinearMap.congr_fun₂ this y x

/-- **The Hall inner product on `Λ_R` is a symmetric bilinear form.** -/
theorem isSymm_hallInner : (hallInner R).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr hallInner_comm

/-- **The Hall inner product on `Λ_R` is nondegenerate.** -/
theorem nondegenerate_hallInner : (hallInner R).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (hallInner R) := fun x hx =>
    (schurBasis R).toDual_inj x (LinearMap.ext hx)
  exact ⟨hl, fun y hy => hl y fun x => by rw [hallInner_comm]; exact hy x⟩

end SymmetricFunction

end TauCeti
