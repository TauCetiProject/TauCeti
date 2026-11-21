/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Diagonalizable
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.TwoWeylCocharacter

/-!
# Dynamic subgroups of the cocharacter `2ρ^∨`

Let `P` be a root datum with character lattice `M` and a base `b`, and let
`π : H →ₐc[R] R[Multiplicative M]` present a homomorphism `T → G = Spec H` from the split torus
`T = D(M)` with character lattice `M`, for instance a chosen split maximal torus. Through `π`, the
sum of the positive coroots `RootPairing.twoWeylCocharacter P b` becomes the cocharacter
`λ = 2ρ^∨` of `G`.

Its adjoint weights are read off from the `T`-weights, `⟨α, 2ρ^∨⟩ = 2 ht(α)` on the roots: the
root space `𝔤_α` has weight `2 ht(α)` for `2ρ^∨`, so `Ad(2ρ^∨(u))` multiplies a root vector of `α`
by `u ^ (2 ht(α))`. In particular the root space of every positive root lies in the Lie algebra of
the dynamic unipotent subgroup `U_G(λ)`, with no further hypothesis. If moreover every nontrivial
`T`-weight of the adjoint representation is a root of `P`, as for the diagonal torus of `GL_n` with
its diagonal root datum, then `2ρ^∨` grades the Lie algebra by twice the height, and the three
dynamic Lie algebras are determined by the base:

```text
Lie U_G(2ρ^∨) = ⊕_{α > 0} 𝔤_α,   Lie Z_G(2ρ^∨) = 𝔤_0,   Lie P_G(2ρ^∨) = 𝔤_0 ⊕ ⊕_{α > 0} 𝔤_α.
```

Here `𝔤_0` is the trivial weight space, the weight space `Derivation.adjointWeightSpace π 1` of the
trivial character. These are statements about Lie algebras only: no comparison of `P_G(2ρ^∨)` with a
Borel subgroup is made here. None of them needs a field, smoothness or reductivity.

## Main declarations

* `BialgHom.adjointWeightSpace_root_le_adjointWeightSpace_cocharacter_twoWeylCocharacter`: the root
  space `𝔤_α` has weight `2 ht(α)` for `2ρ^∨`.
* `BialgHom.adjointWeightSpace_cocharacter_twoWeylCocharacter`: the weight spaces of `2ρ^∨` are
  sums of root spaces of a fixed height.
* `BialgHom.map_adjointWeightSpace_root_le_lieSubalgebra_unipotent_twoWeylCocharacter`: a
  positive root space lies in `Lie U_G(2ρ^∨)`.
* `BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_twoWeylCocharacter_toSubmodule`:
  `Lie U_G(2ρ^∨)` is the sum of the positive root spaces.
* `BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter_twoWeylCocharacter_toSubmodule`:
  `Lie P_G(2ρ^∨)` is the trivial weight space plus the positive root spaces.
* `BialgHom.lieSubalgebra_leviDefiningHopfIdeal_cocharacter_twoWeylCocharacter_toSubmodule`:
  `Lie Z_G(2ρ^∨)` is the trivial weight space.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 21.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

open RootPairing TauCeti

namespace BialgHom

universe u v w x

section Tangent

variable {R : Type u} {H : Type u} {ι : Type v} {M : Type w} {N : Type x} [CommRing R]
  [CommRing H] [HopfAlgebra R H] [AddCommGroup M] [AddCommGroup N]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  (π : H →ₐc[R] MonoidAlgebra R (Multiplicative M))
  [Finite ι] {P : RootDatum ι M N} [P.IsReduced] (b : P.Base)

/-- **The cocharacter `2ρ^∨` acts on a root space with weight twice the height of the root.** The
root space `𝔤_α` lies in the weight space of `2ρ^∨` of weight `2 ht(α)`; on points, `Ad(2ρ^∨(u))`
multiplies a root vector of `α` by `u ^ (2 ht(α))`. -/
theorem adjointWeightSpace_root_le_adjointWeightSpace_cocharacter_twoWeylCocharacter (i : ι) :
    Derivation.adjointWeightSpace π (Multiplicative.ofAdd (P.root i)) ≤
      Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp
          (π.cocharacter (P.twoWeylCocharacter b)))
        (Multiplicative.ofAdd (2 * b.height i)) := by
  rw [adjointWeightSpace_cocharacter]
  exact le_iSup₂_of_le
    (f := fun χ (_ : DiagonalizableGroup.pairing χ (P.twoWeylCocharacter b) =
      2 * b.height i) ↦ Derivation.adjointWeightSpace π χ) _
    (P.pairing_ofAdd_root_twoWeylCocharacter b i) le_rfl

/-- **A positive root space lies in the Lie algebra of the dynamic unipotent subgroup of
`2ρ^∨`.** The root `α` pairs to `2 ht(α) > 0` with `2ρ^∨`. -/
theorem map_adjointWeightSpace_root_le_lieSubalgebra_unipotent_twoWeylCocharacter {i : ι}
    (hi : i ∈ posRoots P b) :
    (Derivation.adjointWeightSpace π (Multiplicative.ofAdd (P.root i))).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap ≤
      ((π.cocharacter (P.twoWeylCocharacter b)).unipotentDefiningHopfIdeal.lieSubalgebra
        (B := R)).toSubmodule := by
  rw [lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_toSubmodule]
  exact Submodule.map_mono (le_iSup₂_of_le
    (f := fun χ (_ : 0 < DiagonalizableGroup.pairing χ (P.twoWeylCocharacter b)) ↦
      Derivation.adjointWeightSpace π χ) _
    (P.pairing_ofAdd_root_twoWeylCocharacter_pos b hi) le_rfl)

variable {π}
variable (hroots : Derivation.nontrivialAdjointWeights π ⊆
  Set.range fun i ↦ Multiplicative.ofAdd (P.root i))
include hroots

/-- **The cocharacter `2ρ^∨` grades the Lie algebra by twice the height**, when every nontrivial
adjoint weight is a root: its weight space of weight `n` is the sum of the root spaces of the roots
`i` with `2 * b.height i = n`, together with the trivial weight space when `n = 0`. In particular
it vanishes for odd `n`. -/
theorem adjointWeightSpace_cocharacter_twoWeylCocharacter (n : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp
          (π.cocharacter (P.twoWeylCocharacter b)))
        (Multiplicative.ofAdd n) =
      (⨆ _ : n = 0, Derivation.adjointWeightSpace π 1) ⊔
        ⨆ (i) (_ : 2 * b.height i = n),
          Derivation.adjointWeightSpace π (Multiplicative.ofAdd (P.root i)) := by
  rw [adjointWeightSpace_cocharacter, Derivation.iSup_adjointWeightSpace_eq_sup_iSup π hroots,
    DiagonalizableGroup.pairing_one_left]
  simp_rw [P.pairing_ofAdd_root_twoWeylCocharacter b, eq_comm (a := (0 : ℤ))]

/-- **The Lie algebra of the dynamic unipotent subgroup of `2ρ^∨` is the sum of the positive root
spaces**, when every nontrivial adjoint weight is a root. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_twoWeylCocharacter_toSubmodule :
    ((π.cocharacter (P.twoWeylCocharacter b)).unipotentDefiningHopfIdeal.lieSubalgebra
        (B := R)).toSubmodule =
      (⨆ i ∈ posRoots P b, Derivation.adjointWeightSpace π (Multiplicative.ofAdd (P.root i))).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  rw [lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_toSubmodule,
    Derivation.iSup_adjointWeightSpace_eq_sup_iSup π hroots, DiagonalizableGroup.pairing_one_left]
  simp_rw [P.pairing_ofAdd_root_twoWeylCocharacter_pos_iff b, lt_irrefl, iSup_false,
    bot_sup_eq]

/-- **The Lie algebra of the dynamic parabolic subgroup of `2ρ^∨` is the trivial weight space plus
the positive root spaces**, when every nontrivial adjoint weight is a root. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter_twoWeylCocharacter_toSubmodule :
    ((Cocharacter.parabolicDefiningHopfIdeal
        (π.cocharacter (P.twoWeylCocharacter b))).lieSubalgebra (B := R)).toSubmodule =
      (Derivation.adjointWeightSpace π 1 ⊔
        ⨆ i ∈ posRoots P b, Derivation.adjointWeightSpace π (Multiplicative.ofAdd (P.root i))).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  rw [lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter_toSubmodule,
    Derivation.iSup_adjointWeightSpace_eq_sup_iSup π hroots, DiagonalizableGroup.pairing_one_left]
  simp_rw [P.pairing_ofAdd_root_twoWeylCocharacter_nonneg_iff b, le_refl, iSup_true]

end Tangent

section LeviTangent

variable {R H M : Type u} {ι : Type v} {N : Type x} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommGroup M] [AddCommGroup N] [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  {π : H →ₐc[R] MonoidAlgebra R (Multiplicative M)}
  [Finite ι] {P : RootDatum ι M N} [P.IsReduced] (b : P.Base)

/-- **The Lie algebra of the dynamic Levi subgroup of `2ρ^∨` is the trivial weight space**, when
every nontrivial adjoint weight is a root: no root pairs to `0` with `2ρ^∨`. -/
theorem lieSubalgebra_leviDefiningHopfIdeal_cocharacter_twoWeylCocharacter_toSubmodule
    (hroots : Derivation.nontrivialAdjointWeights π ⊆
      Set.range fun i ↦ Multiplicative.ofAdd (P.root i)) :
    ((Cocharacter.leviDefiningHopfIdeal
        (π.cocharacter (P.twoWeylCocharacter b))).lieSubalgebra (B := R)).toSubmodule =
      (Derivation.adjointWeightSpace π 1).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  rw [lieSubalgebra_leviDefiningHopfIdeal_cocharacter_toSubmodule,
    Derivation.iSup_adjointWeightSpace_eq_sup_iSup π hroots, DiagonalizableGroup.pairing_one_left]
  simp only [P.pairing_ofAdd_root_twoWeylCocharacter_ne_zero b, iSup_true, iSup_false,
    iSup_bot, sup_bot_eq]

end LeviTangent

end BialgHom
