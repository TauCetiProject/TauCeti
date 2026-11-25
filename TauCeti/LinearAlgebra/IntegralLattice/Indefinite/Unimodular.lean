/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.SignedUnitLattice
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Isotropic
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction

/-!
# Signature `(1, 0, 1)` unimodular classification and the even-to-odd neighbor reduction

Every unimodular integral lattice of signature `(1, 0, 1)` has Gram determinant `-1`, which yields
an explicit nonzero isotropic lattice vector without invoking the Hasse–Minkowski theorem.
Combining this unconditional isotropy with the isotropic splitting theorems of
`TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Isotropic` classifies unimodular lattices of
signature `(1, 0, 1)`: each is isometric to `hyperbolicPlane` (when even) or
`signedUnitLattice 1 1` (when odd).

For a general even unimodular lattice `L` whose rational form is isotropic, splitting off a copy of
`hyperbolicPlane` and applying `exists_isNeighbor_orthogonalSum_signedUnitLattice_one_one` exhibits
`L` up to isometry as an even Kneser two-neighbor of `(L.restrict S) ⊕ signedUnitLattice 1 1`, an
odd unimodular lattice of the same signature.

## Main results

* `TauCeti.IntegralLattice.not_anisotropic_norm_of_isUnimodular_of_signature_one_one`: every
  unimodular lattice of signature `(1, 0, 1)` has isotropic rational norm form.
* `TauCeti.IntegralLattice.nonempty_isometry_hyperbolicPlane_of_isUnimodular_of_signature_one_one`:
  every even unimodular lattice of signature `(1, 0, 1)` is isometric to `hyperbolicPlane`.
* `IntegralLattice.nonempty_isometry_signedUnitLattice_one_one_of_isUnimodular_of_signature_one_one`
  — every odd unimodular lattice of signature `(1, 0, 1)` is isometric to `signedUnitLattice 1 1`.
* `TauCeti.IntegralLattice.exists_odd_isUnimodular_isNeighbor`: every rationally isotropic even
  unimodular lattice is isometric to an even Kneser two-neighbor of an odd unimodular lattice of
  the same signature.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, §§2–5.
-/

public section

open Module TensorProduct

namespace TauCeti.IntegralLattice

universe u
variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- **Every unimodular lattice of signature `(1, 0, 1)` is rationally isotropic.** -/
theorem not_anisotropic_norm_of_isUnimodular_of_signature_one_one {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hsig : L.signature = (1, 0, 1)) : ¬ L.norm.Anisotropic := by
  have hsp : L.sigPos = 1 ∧ L.sigNull = 0 ∧ L.sigNeg = 1 := by simpa [signature] using hsig
  have hrank : Module.finrank ℤ L = 2 := by
    rw [L.finrank_carrier, ← L.signature_sum_eq_finrank, hsp.1, hsp.2.1, hsp.2.2]
  let b : Basis (Fin 2) ℤ L := Module.finBasisOfFinrankEq ℤ L hrank
  let G := L.gramMatrix b
  have hGsymm : G 1 0 = G 0 1 := (L.isSymm_gramMatrix b).apply 0 1
  have hGdet : G 0 0 * G 1 1 - G 0 1 * G 0 1 = -1 := by
    have hdet : G.det = -1 := by
      rw [← L.gramDet_def b, ← L.determinant_eq_gramDet b,
        L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hsp.2.2,
        L.isUnimodular_iff_discriminant_eq_one.mp hLu]
      norm_num
    rwa [Matrix.det_fin_two, hGsymm] at hdet
  rw [QuadraticMap.not_anisotropic_iff_exists]
  by_cases h00 : G 0 0 = 0
  · refine ⟨b 0, fun h ↦ b.ne_zero 0 (Subtype.ext h), ?_⟩
    rw [← L.integralNorm_cast, L.integralNorm_apply, ← L.gramMatrix_apply b 0 0]
    exact Int.cast_eq_zero.mpr h00
  · let w : L := (-G 0 1 + 1) • b 0 + G 0 0 • b 1
    have hw_ne : w ≠ 0 := fun hw ↦ by simpa [w, h00] using congrArg (fun x ↦ b.repr x 1) hw
    have hw_norm : L.integralNorm w = 0 := by
      rw [L.integralNorm_apply]
      simp only [w, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        ← L.gramMatrix_apply b, smul_eq_mul]
      linear_combination G 0 0 * hGdet + ((-G 0 1 + 1) * G 0 0) * hGsymm
    exact ⟨w, fun h ↦ hw_ne (Subtype.ext h), by rw [← L.integralNorm_cast, hw_norm, Int.cast_zero]⟩

/-- **Classification of even unimodular lattices of signature `(1, 0, 1)`.** -/
theorem nonempty_isometry_hyperbolicPlane_of_isUnimodular_of_signature_one_one
    {L : IntegralLattice V} (hLu : L.IsUnimodular) (hLe : L.IsEven)
    (hsig : L.signature = (1, 0, 1)) : Nonempty (Isometry hyperbolicPlane L) := by
  obtain ⟨S, _, _, ⟨e⟩⟩ := hLu.exists_isometry_hyperbolicPlane_orthogonalSum hLe
    (not_anisotropic_norm_of_isUnimodular_of_signature_one_one hLu hsig)
  rw [← L.restrict_eq_ofIntegralForm S] at e
  set Y := L.restrict S
  have hYrank : Module.finrank ℚ (ℚ ⊗[ℤ] S) = 0 := by
    have hsum := e.signature_eq
    have hU := hyperbolicPlane_signature
    rw [hsig, signature_orthogonalSum] at hsum
    simp only [signature, Prod.mk.injEq] at hU hsum
    have := Y.signature_sum_eq_finrank
    omega
  have : FiniteDimensional ℚ (ℚ ⊗[ℤ] S) := Y.finiteDimensional
  have : Subsingleton (ℚ ⊗[ℤ] S) := Module.finrank_zero_iff.mp hYrank
  exact ⟨(Isometry.orthogonalSumSubsingletonRight hyperbolicPlane Y).trans e⟩

/-- **Classification of odd unimodular lattices of signature `(1, 0, 1)`.** -/
theorem nonempty_isometry_signedUnitLattice_one_one_of_isUnimodular_of_signature_one_one
    {L : IntegralLattice V} (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven)
    (hsig : L.signature = (1, 0, 1)) : Nonempty (Isometry (signedUnitLattice 1 1) L) := by
  obtain ⟨S, hYu, _, ⟨e⟩⟩ := hLu.exists_isometry_rankOne_orthogonalSum hLo
    (not_anisotropic_norm_of_isUnimodular_of_signature_one_one hLu hsig) isUnit_one
  rw [← L.restrict_eq_ofIntegralForm S] at hYu e
  set Y := L.restrict S
  have hsp : Y.sigPos = 0 ∧ Y.sigNull = 0 ∧ Y.sigNeg = 1 := by
    have hsum := e.signature_eq
    have hr1 := rankOne_signature_of_pos (a := 1) zero_lt_one
    rw [hsig, signature_orthogonalSum] at hsum
    simp only [signature, Prod.mk.injEq] at hr1 hsum
    omega
  have hYrank : Module.finrank ℤ Y = 1 := by
    rw [Y.finrank_carrier, ← Y.signature_sum_eq_finrank, hsp.1, hsp.2.1, hsp.2.2]
  let b : Basis (Fin 1) ℤ Y := Module.finBasisOfFinrankEq ℤ Y hYrank
  have hb0 : Y.integralForm (b 0) (b 0) = -1 := by
    have hYdet : Y.determinant = -1 := by
      rw [Y.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hsp.2.2,
        Y.isUnimodular_iff_discriminant_eq_one.mp hYu]
      norm_num
    rwa [Y.determinant_eq_gramDet b, gramDet_def, Matrix.det_unique, gramMatrix_apply] at hYdet
  let G1 : Matrix (Fin 1) (Fin 1) ℤ := Matrix.of fun _ _ ↦ -1
  have hG1 : G1.IsSymm := by ext; rfl
  let eY : Isometry (rankOne (-1)) Y :=
    (Isometry.ofEq (ofGramMatrix_singleton_eq_rankOne (-1) rfl hG1).symm).trans
      (Isometry.ofGramMatrixEq (ofGramMatrix.basis (Basis.singleton (Fin 1) ℚ) G1 hG1) b (by
        rw [gramMatrix_ofGramMatrix]
        ext i j; fin_cases i; fin_cases j
        simpa [G1, gramMatrix_apply] using hb0.symm))
  exact ⟨rankOneOrthogonalSumIsometrySignedUnitLattice.symm.trans
    (((Isometry.refl (rankOne 1)).orthogonalSum eY).trans e)⟩

/-- **Even-to-odd reduction for rationally isotropic even unimodular lattices.** -/
theorem exists_odd_isUnimodular_isNeighbor {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLe : L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ (S : Submodule ℤ L) (K : IntegralLattice ((ℚ ⊗[ℤ] S) × (Fin 1 ⊕ Fin 1 → ℚ))),
      ((L.restrict S).orthogonalSum (signedUnitLattice 1 1)).IsUnimodular ∧
        ¬ ((L.restrict S).orthogonalSum (signedUnitLattice 1 1)).IsEven ∧
        ((L.restrict S).orthogonalSum (signedUnitLattice 1 1)).signature = L.signature ∧
        ((L.restrict S).orthogonalSum (signedUnitLattice 1 1)).IsNeighbor K 2 ∧
        K.IsEven ∧ Nonempty (Isometry K L) := by
  obtain ⟨S, hYe, hYu, ⟨e_split⟩⟩ := hLu.exists_isometry_hyperbolicPlane_orthogonalSum hLe hiso
  rw [← L.restrict_eq_ofIntegralForm S] at hYe hYu e_split
  set Y := L.restrict S
  let eL := (Isometry.orthogonalSumComm Y hyperbolicPlane).trans e_split
  let N := Y.orthogonalSum (signedUnitLattice 1 1)
  have hNsig : N.signature = L.signature := by
    have hL' := eL.signature_eq
    have hU := hyperbolicPlane_signature
    have hI := signedUnitLattice_signature 1 1
    rw [signature_orthogonalSum] at hL'
    simp only [N, signature_orthogonalSum, signature, Prod.mk.injEq] at hU hI hL' ⊢
    omega
  obtain ⟨K, hNK, hKe, ⟨eK⟩⟩ := exists_isNeighbor_orthogonalSum_signedUnitLattice_one_one hYe
  exact ⟨S, K, (isUnimodular_orthogonalSum_iff _ _).mpr ⟨hYu, isUnimodular_signedUnitLattice 1 1⟩,
    fun h ↦ not_isEven_signedUnitLattice_of_pos (by decide : 0 < 1 + 1)
      ((isEven_orthogonalSum_iff _ _).mp h).2,
    hNsig, hNK, hKe, ⟨eK.symm.trans eL⟩⟩

end TauCeti.IntegralLattice
