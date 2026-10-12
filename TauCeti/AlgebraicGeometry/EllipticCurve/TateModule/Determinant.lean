/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.WeilPairing
public import Mathlib.LinearAlgebra.Determinant
import TauCeti.LinearAlgebra.Determinant
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The determinant of the elliptic Tate-module representation

For an elliptic curve over a field `F`, a separably closed extension `K`, and a prime `ℓ`
invertible in `K`, the determinant of the action of `Gal(K/F)` on `T_ℓ E` is the `ℓ`-adic
cyclotomic character. The statement uses `LinearMap.det` and is independent of a basis of the
Tate module or a generator of `ℤ_ℓ(1)`.

The alternating Weil pairing identifies the determinant action with the action on the Tate
twist. This uses the rank-two determinant transformation law
`LinearMap.det_eq_of_compl₁₂_self_eq_smul` from `TauCeti.LinearAlgebra.Determinant`, together
with nondegeneracy of `WeierstrassCurve.tateModuleWeilPairing`. Cancellation is justified by
the rank-one freeness of the Tate twist, so it does not require a perfect-pairing theorem.

## Main result

* `TauCeti.det_tateModuleGaloisRepresentation`: the determinant is the cyclotomic character.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7–8.
-/

public section

noncomputable section

open scoped WeierstrassCurve

namespace TauCeti

variable {F K : Type*} [Field F] [Field K] [IsSepClosed K] [Algebra F K]
  {W : WeierstrassCurve F} [W.IsElliptic] {ℓ : ℕ} [Fact ℓ.Prime]

open scoped Classical in
/-- **The determinant of the elliptic `ℓ`-adic Galois representation is the cyclotomic
character.** The extension is allowed to be any separably closed extension of the ground
field, and the equality is independent of all choices of bases. -/
@[simp]
theorem det_tateModuleGaloisRepresentation (hℓ : (ℓ : K) ≠ 0) (σ : K ≃ₐ[F] K) :
    LinearMap.det (W.tateModuleGaloisRepresentation ℓ σ) =
      ((cyclotomicCharacter K ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
  let : NeZero (ℓ : K) := ⟨hℓ⟩
  let e := ((W⁄K).nonempty_linearEquiv_tateModule hℓ).some
  let b := (Pi.basisFun ℤ_[ℓ] (Fin 2)).map e.symm
  have hω : (W⁄K).tateModuleWeilPairing hℓ ≠ 0 := by
    intro h
    apply b.ne_zero 0
    apply (W⁄K).tateModuleWeilPairing_nondegenerate hℓ
    intro y
    simp [h]
  apply LinearMap.det_eq_of_compl₁₂_self_eq_smul b
    ((W⁄K).tateModuleWeilPairing_self hℓ) hω
  apply LinearMap.ext₂
  intro x y
  simpa only [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using
    (WeierstrassCurve.tateModuleWeilPairing_galoisRepresentation hℓ W σ x y).trans
      (PadicTateTwist.galoisRepresentation_apply_eq_smul σ _)

end TauCeti

end
