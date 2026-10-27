/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Diagonalizable
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.KernelCentralizer
import TauCeti.Order.CompactlyGenerated
import TauCeti.Order.CompleteLattice.Basic

/-!
# Contracted subgroups of the centralizer of a character kernel

Let `T = D(X)` be a chosen split maximal torus of an affine group `G = Spec H` over a commutative
ring `R`, with character lattice `X = ℤ^r` written additively. For a character `α ∈ X` and a
cocharacter `ψ` of `T`, with image `λ` in `G`, this file defines the closed subgroup

`U_G(λ) ∩ Z_G(ker α)`

of points of the centralizer of `ker α` which are contracted to the identity by conjugation with
`λ(t)` as `t → 0`. Classically, since `Z_G(ker α)` is closed and contains `λ`, these are the points
of the dynamic unipotent subgroup `U_{Z_G(ker α)}(λ)` of the centralizer itself; when `G` is
connected reductive over a field, `α` is a root and `⟨α, ψ⟩ > 0`, this is the root group `U_α`,
and replacing `ψ` by `ψ⁻¹` gives `U_{-α}`. These identifications are not proved here.

Its Lie algebra is computed from the weight decomposition `𝔤 = ⨁ χ, 𝔤_χ` of `Lie G` under `T`.
The Lie algebra of `Z_G(ker α)` is `⨆ n : ℤ, 𝔤_{nα}` and that of `U_G(λ)` is the sum of the
`𝔤_χ` with `⟨χ, ψ⟩ > 0`. Since the weight spaces are independent, the two meet in

`Lie (U_G(λ) ∩ Z_G(ker α)) = ⨆ (n : ℤ) (_ : 0 < n * ⟨α, ψ⟩), 𝔤_{nα}`.

In particular this is `⨆ n > 0, 𝔤_{nα}` whenever `⟨α, ψ⟩ > 0`, independently of `ψ`, and it is
zero when `⟨α, ψ⟩ = 0`. For `⟨α, ψ⟩ ≠ 0` the weights `nα` split by the sign of `n * ⟨α, ψ⟩`, so
the Lie algebras of `U_G(λ) ∩ Z_G(ker α)`, of `Z_G(T)` and of `U_G(λ⁻¹) ∩ Z_G(ker α)` span the Lie
algebra of `Z_G(ker α)`: this is the tangent form of the open cell `U_{-α} × Z_G(T) × U_α` in the
rank-one centralizer. Nothing here assumes a field, smoothness, reductivity, or that `α` is a
root; the Lie-algebra statements assume only that the augmentation cotangent module of `H` is
finite projective.

## Main declarations

* `TauCeti.SplitMaximalTorus.unipotentCentralizerKerHopfIdeal`: the closed subgroup
  `U_G(λ) ∩ Z_G(ker α)`.
* `TauCeti.SplitMaximalTorus.centralizerKerHopfIdeal_le_unipotentCentralizerKerHopfIdeal` and
  `TauCeti.SplitMaximalTorus.unipotentDefiningHopfIdeal_le_unipotentCentralizerKerHopfIdeal`: it
  lies in `Z_G(ker α)` and in `U_G(λ)`.
* `TauCeti.SplitMaximalTorus.lieSubalgebra_unipotentCentralizerKerHopfIdeal_toSubmodule`: its Lie
  algebra is `⨆ (n : ℤ) (_ : 0 < n * ⟨α, ψ⟩), 𝔤_{nα}`.
* `SplitMaximalTorus.lieSubalgebra_unipotentCentralizerKerHopfIdeal_toSubmodule_of_pairing_pos`:
  for `⟨α, ψ⟩ > 0` its Lie algebra is `⨆ n > 0, 𝔤_{nα}`.
* `SplitMaximalTorus.lieSubalgebra_unipotentCentralizerKerHopfIdeal_eq_bot_of_pairing_eq_zero`:
  for `⟨α, ψ⟩ = 0` its Lie algebra is zero.
* `TauCeti.SplitMaximalTorus.lieSubalgebra_centralizerKerHopfIdeal_toSubmodule_eq_sup`: for
  `⟨α, ψ⟩ ≠ 0` the Lie algebras of `U_G(λ) ∩ Z_G(ker α)`, `Z_G(T)` and `U_G(λ⁻¹) ∩ Z_G(ker α)`
  span that of `Z_G(ker α)`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), §§7.1 and 8.1.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §13.18.
-/

public section

namespace TauCeti.SplitMaximalTorus

universe u

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R} [Algebra.FiniteType R H] {r : ℕ}

/-- **The subgroup `U_G(λ) ∩ Z_G(ker α)`** of points of the centralizer of the kernel of the
character `α` contracted to the identity by the cocharacter `λ` of `G` given by the cocharacter
`ψ` of the split maximal torus. -/
noncomputable def unipotentCentralizerKerHopfIdeal (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) : HopfIdeal R H :=
  T.centralizerKerHopfIdeal α ⊔ (T.coordinateMap.hom.cocharacter ψ).unipotentDefiningHopfIdeal

/-- `U_G(λ) ∩ Z_G(ker α)` is cut out by the equations of both subgroups. -/
theorem unipotentCentralizerKerHopfIdeal_def (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    T.unipotentCentralizerKerHopfIdeal α ψ =
      T.centralizerKerHopfIdeal α ⊔
        (T.coordinateMap.hom.cocharacter ψ).unipotentDefiningHopfIdeal :=
  (rfl)

/-- **`U_G(λ) ∩ Z_G(ker α) ⊆ Z_G(ker α)`**. -/
theorem centralizerKerHopfIdeal_le_unipotentCentralizerKerHopfIdeal
    (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    T.centralizerKerHopfIdeal α ≤ T.unipotentCentralizerKerHopfIdeal α ψ :=
  le_sup_left

/-- **`U_G(λ) ∩ Z_G(ker α) ⊆ U_G(λ)`**. -/
theorem unipotentDefiningHopfIdeal_le_unipotentCentralizerKerHopfIdeal
    (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    (T.coordinateMap.hom.cocharacter ψ).unipotentDefiningHopfIdeal ≤
      T.unipotentCentralizerKerHopfIdeal α ψ :=
  le_sup_right

/-- The kernel of `-α` is the kernel of `α`, so the subgroup only depends on `α` up to sign; the
opposite subgroup is obtained by inverting the cocharacter instead. -/
@[simp]
theorem unipotentCentralizerKerHopfIdeal_neg (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    T.unipotentCentralizerKerHopfIdeal (-α) ψ = T.unipotentCentralizerKerHopfIdeal α ψ := by
  rw [unipotentCentralizerKerHopfIdeal_def, unipotentCentralizerKerHopfIdeal_def,
    centralizerKerHopfIdeal_neg]

/-! ### Lie algebras -/

section Lie

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- A tangent vector lies in the Lie algebra of `U_G(λ) ∩ Z_G(ker α)` exactly when it is a sum of
weight vectors of `T` whose weights are the multiples `n • α` with `0 < n * ⟨α, ψ⟩`. -/
theorem cotangentLinearEquiv_mem_lieSubalgebra_unipotentCentralizerKerHopfIdeal_iff
    (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Derivation.cotangentLinearEquiv (B := R) x ∈
        (T.unipotentCentralizerKerHopfIdeal α ψ).lieSubalgebra (B := R) ↔
      x ∈ ⨆ (n : ℤ) (_ : 0 < n * DiagonalizableGroup.pairing (Multiplicative.ofAdd α) ψ),
        Derivation.adjointWeightSpace T.coordinateMap.hom (Multiplicative.ofAdd (n • α)) := by
  let 𝔤 := Derivation.adjointWeightSpace (R := R) T.coordinateMap.hom
  -- `isInternal_adjointWeightSpace` is stated with classical decidable equality of characters.
  let : DecidableEq (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) := Classical.decEq _
  have hind := (Derivation.isInternal_adjointWeightSpace T.coordinateMap.hom).submodule_iSupIndep
  -- The Lie algebra of `U_G(λ)`, read in the cotangent dual.
  have hU : Derivation.cotangentLinearEquiv (B := R) x ∈
        (T.coordinateMap.hom.cocharacter ψ).unipotentDefiningHopfIdeal.lieSubalgebra (B := R) ↔
      x ∈ ⨆ (χ) (_ : 0 < DiagonalizableGroup.pairing χ ψ), 𝔤 χ := by
    rw [← LieSubalgebra.mem_toSubmodule,
      BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_toSubmodule,
      Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  -- The multiples of `α`, as a predicate on characters.
  have hZ : (⨆ n : ℤ, 𝔤 (Multiplicative.ofAdd (n • α))) =
      ⨆ (χ) (_ : ∃ n : ℤ, χ = Multiplicative.ofAdd (n • α)), 𝔤 χ := by
    simp only [iSup_exists]
    rw [iSup_comm]
    simp only [iSup_iSup_eq_left]
    -- The sides differ only in the carrier `SplitTorus.characterGroup`, which unfolds to
    -- `Multiplicative (ULift (Fin r) →₀ ℤ)` by definition.
    rfl
  rw [unipotentCentralizerKerHopfIdeal_def, HopfIdeal.mem_lieSubalgebra_sup_iff,
    cotangentLinearEquiv_mem_lieSubalgebra_centralizerKerHopfIdeal_iff, hU, ← Submodule.mem_inf,
    hZ, hind.iSup₂_inf_iSup₂_eq_iSup₂_and]
  -- Reindex the characters `χ = n • α` by the integers `n`.
  simp only [iSup_and, iSup_exists]
  rw [iSup_comm]
  simp only [iSup_iSup_eq_left, ofAdd_zsmul, DiagonalizableGroup.pairing_zpow_left]
  -- The sides differ only in the carrier `SplitTorus.characterGroup`, which unfolds to
  -- `Multiplicative (ULift (Fin r) →₀ ℤ)` by definition.
  rfl

/-- **The Lie algebra of `U_G(λ) ∩ Z_G(ker α)` is `⨆ (n : ℤ) (_ : 0 < n * ⟨α, ψ⟩), 𝔤_{nα}`**,
transported along cotangent duality. -/
theorem lieSubalgebra_unipotentCentralizerKerHopfIdeal_toSubmodule
    (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ) :
    ((T.unipotentCentralizerKerHopfIdeal α ψ).lieSubalgebra (B := R)).toSubmodule =
      (⨆ (n : ℤ) (_ : 0 < n * DiagonalizableGroup.pairing (Multiplicative.ofAdd α) ψ),
          Derivation.adjointWeightSpace T.coordinateMap.hom (Multiplicative.ofAdd (n • α))).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R) :
          Module.Dual R (Bialgebra.CotangentSpace R H) →ₗ[R]
            Derivation R H (Bialgebra.CounitAlgebra R H R)) := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, Submodule.mem_map_equiv,
    ← cotangentLinearEquiv_mem_lieSubalgebra_unipotentCentralizerKerHopfIdeal_iff,
    LinearEquiv.apply_symm_apply]

/-- **For `⟨α, ψ⟩ > 0` the Lie algebra of `U_G(λ) ∩ Z_G(ker α)` is `⨆ n > 0, 𝔤_{nα}`**, the sum
of the weight spaces of `T` on the positive multiples of `α`; in particular it does not depend on
the choice of such a `ψ`. -/
theorem lieSubalgebra_unipotentCentralizerKerHopfIdeal_toSubmodule_of_pairing_pos
    (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ)
    (hψ : 0 < DiagonalizableGroup.pairing (Multiplicative.ofAdd α) ψ) :
    ((T.unipotentCentralizerKerHopfIdeal α ψ).lieSubalgebra (B := R)).toSubmodule =
      (⨆ (n : ℤ) (_ : 0 < n),
          Derivation.adjointWeightSpace T.coordinateMap.hom (Multiplicative.ofAdd (n • α))).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R) :
          Module.Dual R (Bialgebra.CotangentSpace R H) →ₗ[R]
            Derivation R H (Bialgebra.CounitAlgebra R H R)) := by
  rw [lieSubalgebra_unipotentCentralizerKerHopfIdeal_toSubmodule]
  simp only [mul_pos_iff_of_pos_right hψ]

/-- **For `⟨α, ψ⟩ = 0` the Lie algebra of `U_G(λ) ∩ Z_G(ker α)` is zero.** -/
@[simp]
theorem lieSubalgebra_unipotentCentralizerKerHopfIdeal_eq_bot_of_pairing_eq_zero
    (T : SplitMaximalTorus R H r) (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ)
    (hψ : DiagonalizableGroup.pairing (Multiplicative.ofAdd α) ψ = 0) :
    (T.unipotentCentralizerKerHopfIdeal α ψ).lieSubalgebra (B := R) = ⊥ := by
  rw [← LieSubalgebra.toSubmodule_eq_bot,
    lieSubalgebra_unipotentCentralizerKerHopfIdeal_toSubmodule]
  simp [hψ]

/-- **The Lie algebra of `Z_G(ker α)` is spanned by those of `U_G(λ) ∩ Z_G(ker α)`, `Z_G(T)` and
`U_G(λ⁻¹) ∩ Z_G(ker α)`** whenever `⟨α, ψ⟩ ≠ 0`: the weight spaces `𝔤_{nα}` split into those with
`n * ⟨α, ψ⟩` positive, zero and negative. This is the tangent form of the open cell
`U_{-α} × Z_G(T) × U_α` of the rank-one centralizer. -/
theorem lieSubalgebra_centralizerKerHopfIdeal_toSubmodule_eq_sup (T : SplitMaximalTorus R H r)
    (α : ULift.{u} (Fin r) →₀ ℤ)
    (ψ : Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ)
    (hψ : DiagonalizableGroup.pairing (Multiplicative.ofAdd α) ψ ≠ 0) :
    ((T.centralizerKerHopfIdeal α).lieSubalgebra (B := R)).toSubmodule =
      ((T.unipotentCentralizerKerHopfIdeal α ψ).lieSubalgebra (B := R)).toSubmodule ⊔
        ((BialgHom.centralizerHopfIdeal T.coordinateMap.hom).lieSubalgebra (B := R)).toSubmodule ⊔
        ((T.unipotentCentralizerKerHopfIdeal α ψ⁻¹).lieSubalgebra (B := R)).toSubmodule := by
  rw [← centralizerKerHopfIdeal_zero, lieSubalgebra_centralizerKerHopfIdeal_toSubmodule,
    lieSubalgebra_centralizerKerHopfIdeal_toSubmodule,
    lieSubalgebra_unipotentCentralizerKerHopfIdeal_toSubmodule,
    lieSubalgebra_unipotentCentralizerKerHopfIdeal_toSubmodule,
    DiagonalizableGroup.pairing_inv_right, ← Submodule.map_sup,
    ← Submodule.map_sup]
  congr 1
  have h := iSup_int_eq_sup_pos_mul_sup_zero_sup_neg_mul
    (fun n ↦ Derivation.adjointWeightSpace T.coordinateMap.hom (Multiplicative.ofAdd (n • α))) hψ
  simp only [smul_zero, zero_smul, iSup_const] at h ⊢
  exact h

end Lie

end TauCeti.SplitMaximalTorus
