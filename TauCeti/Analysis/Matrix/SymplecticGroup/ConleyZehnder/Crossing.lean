/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Normalization
import Mathlib.Topology.Subpath
import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Homotopy
import TauCeti.LinearAlgebra.Eigenspace.Matrix
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The crossing form formula for the Conley–Zehnder index

Let `Ψ : [0, 1] → Sp(2n, ℝ)` be a path of symplectic matrices. Its *crossings* are the parameters
`t` at which `Ψ t` has the eigenvalue `1`, that is, at which the graph of `Ψ t` meets the diagonal.
At a crossing `t` where `Ψ` has derivative `Ψ' t`, the *crossing form* of Robbin and Salamon is the
quadratic form

`Γ(Ψ, t) (v) = -v ⬝ᵥ J Ψ'(t) v`, `v ∈ ker (Ψ t - 1)`,

that is, `Matrix.crossingForm (Ψ t - 1) (-(J * Ψ' t))`. Writing `Ψ' = J S Ψ` with `S` symmetric,
as for the linearized flow of a Hamiltonian, this is the form `v ↦ v ⬝ᵥ S v` of `S` on the fixed
vectors of `Ψ t` (`Matrix.crossingForm_sub_one_neg_J_mul_J_mul_mul`). A crossing is *regular*
when its crossing form is nondegenerate.

This file proves the crossing form formula for the Conley–Zehnder index
`TauCeti.GLSymplectic.conleyZehnderIndex` of a path whose crossings are regular
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_crossingForm_add_finsum`):

`CZ(Ψ) = -((sign Γ(Ψ, 0) + sign Γ(Ψ, 1)) / 2 + ∑ᶠ t ∈ (0, 1), sign Γ(Ψ, t))`.

The crossings at the endpoints count one half, parameters that are not crossings contribute zero,
and the sign is the convention `CZ = -μ_RS` of `TauCeti.GLSymplectic.conleyZehnderIndex`. The path
may have the eigenvalue `-1` anywhere, including at its crossings. For the path `t ↦ exp (t J S)`
with `S` small, symmetric and nondegenerate, the only crossing is `t = 0`, where the crossing form
is the form of `S` on the whole space, and the formula returns the normalization
`-signature(S) / 2` of `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_div_two`.

**Paths avoiding `-1`.** For a path avoiding the eigenvalue `-1`, the index is half the drop of the
signature of the symmetric matrices `K t = (Ψ t)ᵀ J - J Ψ t`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one`), and the change
of the signature of a path of symmetric matrices with regular crossings is given by the signatures
of its crossing forms (`Matrix.signature_sub_signature_eq_crossingForm_add_two_mul_finsum`). The
crossings of `K` are those of `Ψ`: a symplectic `Ψ` satisfies `Ψᵀ J - J Ψ = (Ψ + 1)ᵀ (-J (Ψ - 1))`,
so `K t` and `Ψ t - 1` have the same kernel when `Ψ t + 1` is invertible. On every vector `v`,
`v ⬝ᵥ (Bᵀ J - J B) v = 2 (-v ⬝ᵥ J B v)`, so the crossing form of `K` is twice the crossing form
`Γ(Ψ, t)`, with the same signature.

**Other complements.** In terms of graphs, `Ψ + 1` is invertible when the graph of `Ψ` is
transverse to the graph of `-1`, a complement of the diagonal. At a crossing where `Ψ` also has the
eigenvalue `-1` that complement is not transverse, and another one is used. For a scalar `c`,
`K_c = Ψᵀ J - J Ψ + c (Ψ - 1)ᵀ (Ψ - 1)` factors as `(Ψ + 1 - c J (Ψ - 1))ᵀ (-J (Ψ - 1))`
(`Matrix.transpose_mul_J_sub_J_mul_add_smul_eq_transpose_mul_neg_J_mul`), so its kernel is still
the space of fixed vectors of `Ψ` where `Ψ + 1 - c J (Ψ - 1)` is invertible, and on that space the
correction `c (Ψ'ᵀ (Ψ - 1) + (Ψ - 1)ᵀ Ψ')` of its derivative vanishes: its crossing form is again
twice `Γ(Ψ, t)`. Every symplectic `Ψ` admits such a `c` in any interval `(-ε, ε)`: the determinant
of `Ψ + 1 - c J (Ψ - 1)` is a polynomial in `c`, which at `c = i` is, up to a factor, the
determinant of the straightened graph frame of `Ψ`, and so does not vanish identically
(`TauCeti.exists_mem_Ioo_isUnit_det_add_one_sub_smul`).

To compute the index from `K_c`, the path is sheared. With `N = 1 - (c / 2) J (Ψ - 1)`, the
shear `Φ = 1 + (Ψ - 1) N⁻¹` (`Matrix.symplecticShear`) is symplectic, its fixed vectors are the
images under `N` of those of `Ψ`, `(Φ + 1) N = Ψ + 1 - c J (Ψ - 1)`, and `Nᵀ (Φᵀ J - J Φ) N = K_c`.
For `|c|` small, the shears by `s c / 2`, `s ∈ [0, 1]`, are a homotopy from `Ψ` to `Φ` along which
the eigenvalue `1` keeps its multiplicity at the endpoints, so `Ψ` and `Φ` have the same index
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopy_of_finrank_eigenspace_eq`). The path `Φ`
avoids `-1`, and by Sylvester's law of inertia its index is half the drop of the signature of
`K_c`.

The formula is local. The open sets of parameters at which `Ψ + 1 - c J (Ψ - 1)` is invertible,
for `|c|` below a bound making all the shears defined, cover `[0, 1]`, and the Lebesgue number
lemma subdivides `[0, 1]` into intervals each contained in one of them. On each interval the index
is the crossing sum, the crossings being the singular parameters of `K_c`, which are isolated
because they are regular; so the crossings are finitely many. The index is additive under
catenation, and so is the crossing sum, an interior subdivision point counting one half on each
side.

## Main results

* `Matrix.crossingForm_sub_one_neg_J_mul_J_mul_mul`: for `Ψ' = J S Ψ`, the crossing form is the
  form of `S` on the fixed vectors of `Ψ`.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_crossingForm_add_finsum`:
  the crossing form formula for the Conley–Zehnder index of a path with regular crossings.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index of a path of symplectic matrices, its crossing form
  `Γ(Ψ, t) = ω₀(v, Ψ'(t) v)` on `ker (Ψ(t) - 1)` and the formula for paths with regular
  crossings).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the crossing form of a path `Ψ' = J S Ψ` as the form of
  `S` on the fixed vectors).
-/

public section

open Set
open scoped unitInterval Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **The crossing form of a Hamiltonian path.** If `Ψ' = J S Ψ`, the crossing form of `Ψ` with
derivative `Ψ'` is the quadratic form of `S` on the fixed vectors of `Ψ`. -/
theorem crossingForm_sub_one_neg_J_mul_J_mul_mul (Ψ S : Matrix (n ⊕ n) (n ⊕ n) R) :
    crossingForm (Ψ - 1) (-(J n R * (J n R * S * Ψ))) = crossingForm (Ψ - 1) S := by
  ext x
  have hfix : Ψ *ᵥ (x : n ⊕ n → R) = x := by
    simpa [sub_mulVec, sub_eq_zero] using LinearMap.mem_ker.1 x.property
  simp [crossingForm_apply, ← Matrix.mul_assoc, J_squared, ← mulVec_mulVec, hfix]

/-- The symmetric matrix `Ψᵀ J - J Ψ + c • ((Ψ - 1)ᵀ (Ψ - 1))`, whose kernel is the space of fixed
vectors of `Ψ` where `Ψ + 1 - c • (J (Ψ - 1))` is invertible
(`Matrix.ker_mulVecLin_transpose_mul_J_sub_J_mul_add_smul`). -/
private noncomputable def crossingMatrix (c : R) (Ψ : Matrix (n ⊕ n) (n ⊕ n) R) :
    Matrix (n ⊕ n) (n ⊕ n) R :=
  Ψᵀ * J n R - J n R * Ψ + c • ((Ψ - 1)ᵀ * (Ψ - 1))

/-- The derivative of `crossingMatrix c` at `Ψ` in the direction `Ψ'`. -/
private noncomputable def crossingMatrixDeriv (c : R) (Ψ Ψ' : Matrix (n ⊕ n) (n ⊕ n) R) :
    Matrix (n ⊕ n) (n ⊕ n) R :=
  Ψ'ᵀ * J n R - J n R * Ψ' + c • (Ψ'ᵀ * (Ψ - 1) + (Ψ - 1)ᵀ * Ψ')

/-- Where `Ψ + 1 - c • (J * (Ψ - 1))` is invertible, the kernel of `crossingMatrix c Ψ` is the
space of fixed vectors of `Ψ`. -/
private theorem ker_mulVecLin_crossingMatrix {Ψ : Matrix (n ⊕ n) (n ⊕ n) R}
    (hΨ : Ψ ∈ symplecticGroup n R) {c : R} (h : IsUnit (Ψ + 1 - c • (J n R * (Ψ - 1))).det) :
    LinearMap.ker (crossingMatrix c Ψ).mulVecLin = LinearMap.ker (Ψ - 1).mulVecLin := by
  rw [crossingMatrix, ker_mulVecLin_transpose_mul_J_sub_J_mul_add_smul hΨ h]

/-- Where `Ψ + 1 - c • (J * (Ψ - 1))` is invertible, the crossing form of `crossingMatrix c` at `Ψ`
with derivative `crossingMatrixDeriv c Ψ Ψ'` is isometric to twice the crossing form of `Ψ` with
derivative `Ψ'`: the two forms live on the same space of fixed vectors of `Ψ`, and there the
correction `c • (Ψ'ᵀ (Ψ - 1) + (Ψ - 1)ᵀ Ψ')` vanishes. -/
private noncomputable def crossingFormIsometryEquivSymplectic {Ψ : Matrix (n ⊕ n) (n ⊕ n) R}
    (hΨ : Ψ ∈ symplecticGroup n R) {c : R} (h : IsUnit (Ψ + 1 - c • (J n R * (Ψ - 1))).det)
    (Ψ' : Matrix (n ⊕ n) (n ⊕ n) R) :
    (crossingForm (crossingMatrix c Ψ) (crossingMatrixDeriv c Ψ Ψ')).IsometryEquiv
      ((2 : R) • crossingForm (Ψ - 1) (-(J n R * Ψ'))) :=
  ⟨LinearEquiv.ofEq _ _ (ker_mulVecLin_crossingMatrix hΨ h), fun v ↦ by
    have hv : (Ψ - 1) *ᵥ (v : n ⊕ n → R) = 0 :=
      LinearMap.mem_ker.1 ((ker_mulVecLin_crossingMatrix hΨ h).le v.property)
    have hextra : (v : n ⊕ n → R) ⬝ᵥ (Ψ'ᵀ * (Ψ - 1) + (Ψ - 1)ᵀ * Ψ') *ᵥ v = 0 := by
      simp only [add_mulVec, ← mulVec_mulVec, hv, mulVec_zero, zero_add,
        dotProduct_mulVec, vecMul_transpose, zero_vecMul, zero_dotProduct]
    rw [crossingMatrixDeriv, crossingForm_apply, add_mulVec, dotProduct_add, smul_mulVec,
      dotProduct_smul, hextra, smul_zero, add_zero, dotProduct_transpose_mul_J_sub_J_mul_mulVec]
    simp only [smul_apply, crossingForm_apply, LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
      LinearEquiv.coe_ofEq_apply, smul_eq_mul]⟩

end Matrix

open Matrix Filter Topology

namespace TauCeti

namespace GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Shearing a path.** If the shears `symplecticShear (s b) (Ψ t)`, `s ∈ [0, 1]`, of the
matrices `Ψ t` of a path `γ` are all defined, then the path `t ↦ symplecticShear b (Ψ t)` has the
same Conley–Zehnder index as `γ`: the shears form a homotopy along which the eigenvalue `1` of the
endpoints keeps its multiplicity. -/
private theorem exists_path_shear_and_conleyZehnderIndex_eq {A B : GLSymplectic n ℝ}
    (γ : Path A B) {b : ℝ}
    (hN : ∀ s t : I, IsUnit (1 - ((s : ℝ) * b) • (J n ℝ *
      (((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) - 1))).det) :
    ∃ (C D : GLSymplectic n ℝ) (δ : Path C D), (∀ t, ((δ t : GL (n ⊕ n) ℝ) :
      Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        symplecticShear b ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) ∧
        conleyZehnderIndex γ = conleyZehnderIndex δ := by
  set m : I → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t ↦ ((γ t : GL (n ⊕ n) ℝ) : Matrix _ _ ℝ)
  have hm : Continuous m := Units.continuous_val.comp (continuous_subtypeVal.comp γ.continuous)
  have hNc : Continuous fun p : I × I ↦ 1 - ((p.1 : ℝ) * b) • (J n ℝ * (m p.2 - 1)) :=
    continuous_const.sub (((continuous_subtypeVal.comp continuous_fst).mul continuous_const).smul
      (continuous_const.matrix_mul ((hm.comp continuous_snd).sub continuous_const)))
  have hinv : Continuous fun p : I × I ↦ (1 - ((p.1 : ℝ) * b) • (J n ℝ * (m p.2 - 1)))⁻¹ :=
    continuous_iff_continuousAt.2 fun p ↦ (continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (hN p.1 p.2).ne_zero)).comp hNc.continuousAt
  let G : I × I → symplecticGroup n ℝ := fun p ↦ ⟨symplecticShear ((p.1 : ℝ) * b) (m p.2),
    symplecticShear_mem (mem_iff_mem_symplecticGroup.1 (γ p.2).property) (hN p.1 p.2)⟩
  have hS : Continuous fun p : I × I ↦ symplecticShear ((p.1 : ℝ) * b) (m p.2) := by
    simp only [symplecticShear]
    exact continuous_const.add (((hm.comp continuous_snd).sub continuous_const).matrix_mul hinv)
  have hG : Continuous G := hS.subtype_mk _
  let F : C(I × I, GLSymplectic n ℝ) :=
    ⟨fun p ↦ symplecticGroupContinuousMulEquiv n ℝ (G p),
      (symplecticGroupContinuousMulEquiv n ℝ).continuous.comp hG⟩
  have hF (p : I × I) : ((F p : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      symplecticShear ((p.1 : ℝ) * b) (m p.2) := by
    simp [F, G]
  refine ⟨F (1, 0), F (1, 1),
    ⟨⟨fun t ↦ F (1, t), F.continuous.comp (continuous_const.prodMk continuous_id)⟩, rfl, rfl⟩,
    fun t ↦ by simp [hF, m], ?_⟩
  exact conleyZehnderIndex_eq_of_homotopy_of_finrank_eigenspace_eq γ _ F
    (fun t ↦ Subtype.ext (Units.ext (by
      rw [hF, Set.Icc.coe_zero, zero_mul, symplecticShear_zero])))
    (fun t ↦ rfl) (fun s ↦ by rw [hF, finrank_eigenspace_symplecticShear (hN s 0)])
    fun s ↦ by rw [hF, finrank_eigenspace_symplecticShear (hN s 1)]

/-- **The Conley–Zehnder index through a complement `c`.** Let `γ` be a path of symplectic
matrices `Ψ t` such that `Ψ t + 1 - c • (J (Ψ t - 1))` is invertible for every `t`, and such that
the shears `symplecticShear (s c / 2) (Ψ t)`, `s ∈ [0, 1]`, are defined. Then the Conley–Zehnder
index of `γ` is half the drop of the signature of `crossingMatrix c` from `Ψ 0` to `Ψ 1`. For
`c = 0` this is `TauCeti.GLSymplectic.conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one`,
to which the general case reduces by shearing: the path `t ↦ symplecticShear (c / 2) (Ψ t)` has the
same index and avoids the eigenvalue `-1`, and its matrices `Ψᵀ J - J Ψ` are congruent to
`crossingMatrix c (Ψ t)`. -/
private theorem conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one_sub_smul
    {A B : GLSymplectic n ℝ} (γ : Path A B) {c : ℝ}
    (hN : ∀ s t : I, IsUnit (1 - ((s : ℝ) * (c / 2)) • (J n ℝ *
      (((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) - 1))).det)
    (h : ∀ t : I, IsUnit (((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) + 1 -
      c • (J n ℝ * (((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) - 1))).det) :
    conleyZehnderIndex γ =
      (signature (crossingMatrix c ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) -
        signature (crossingMatrix c ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) : ℝ) / 2 := by
  set m : I → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t ↦ ((γ t : GL (n ⊕ n) ℝ) : Matrix _ _ ℝ)
  obtain ⟨C, D, δ, hδ, hCZ⟩ := exists_path_shear_and_conleyZehnderIndex_eq γ hN
  have hc : (2 : ℝ) * (c / 2) = c := by ring
  have hN1 (t : I) : IsUnit (1 - (c / 2) • (J n ℝ * (m t - 1))).det := by
    simpa using hN 1 t
  -- The sheared path avoids `-1`, and its matrices `Ψᵀ J - J Ψ` are congruent to the given ones.
  have hunit (t : I) : IsUnit ((((δ t : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) :
      Matrix (n ⊕ n) (n ⊕ n) ℝ) + 1).det := by
    have hd : IsUnit ((symplecticShear (c / 2) (m t) + 1) *
        (1 - (c / 2) • (J n ℝ * (m t - 1)))).det := by
      rw [symplecticShear_add_one_mul (hN1 t), hc]
      exact h t
    rw [det_mul] at hd
    rw [hδ]
    exact isUnit_of_mul_isUnit_left hd
  have hsig (t : I) : signature ((symplecticShear (c / 2) (m t))ᵀ * J n ℝ -
      J n ℝ * symplecticShear (c / 2) (m t)) = signature (crossingMatrix c (m t)) := by
    have := signature_congr (P := (1 - (c / 2) • (J n ℝ * (m t - 1)))ᵀ)
      (by rw [det_transpose]; exact hN1 t)
      ((symplecticShear (c / 2) (m t))ᵀ * J n ℝ - J n ℝ * symplecticShear (c / 2) (m t))
    rw [crossingMatrix]
    rwa [transpose_transpose, transpose_mul_transpose_mul_J_sub_J_mul_symplecticShear_mul (hN1 t),
      hc, eq_comm] at this
  have hC : ((C : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = symplecticShear (c / 2) (m 0) := by
    rw [← δ.source, hδ]
  have hD : ((D : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = symplecticShear (c / 2) (m 1) := by
    rw [← δ.target, hδ]
  rw [hCZ, conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one δ hunit, hC, hD, hsig, hsig]
  simp only [m, γ.source, γ.target]

/-! ### Crossings -/

/-- The signature of the crossing form of `Ψ` at `t`, for the derivative `Ψ' t`. -/
private noncomputable def crossingSig (Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ) (t : ℝ) : ℤ :=
  (sigPos (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))) : ℤ) -
    sigNeg (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t)))

/-- Where `Ψ t` does not have the eigenvalue `1` the crossing form lives on the zero space, so its
signature vanishes. -/
private theorem crossingSig_eq_zero {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} {t : ℝ}
    (h : (Ψ t - 1).det ≠ 0) : crossingSig Ψ Ψ' t = 0 := by
  have hfin : Module.finrank ℝ (LinearMap.ker (Ψ t - 1).mulVecLin) = 0 :=
    Submodule.finrank_eq_zero.2 (LinearMap.ker_eq_bot.2 (mulVec_injective_of_det_ne_zero h))
  simp [crossingSig, QuadraticForm.sigPos_eq_zero_of_finrank_eq_zero _ hfin,
    QuadraticForm.sigNeg_eq_zero_of_finrank_eq_zero _ hfin]

/-- The entries of `Ψᵀ J - J Ψ` have the derivatives of the entries of `Ψ'ᵀ J - J Ψ'`. -/
private theorem hasDerivWithinAt_transpose_mul_J_sub_J_mul
    {Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} {Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ} {s : Set ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' i j) s t) (i j : n ⊕ n) :
    HasDerivWithinAt (fun r ↦ ((Ψ r)ᵀ * J n ℝ - J n ℝ * Ψ r) i j)
      ((Ψ'ᵀ * J n ℝ - J n ℝ * Ψ') i j) s t := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact (HasDerivWithinAt.fun_sum fun k _ ↦ (h k i).mul_const _).sub
    (HasDerivWithinAt.fun_sum fun k _ ↦ (h k j).const_mul _)

/-- The entries of `crossingMatrix c (Ψ r)` have the derivatives of the entries of
`crossingMatrixDeriv c (Ψ t) Ψ'`. -/
private theorem hasDerivWithinAt_crossingMatrix
    {Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} {Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ} {s : Set ℝ} {t : ℝ}
    (c : ℝ) (h : ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' i j) s t) (i j : n ⊕ n) :
    HasDerivWithinAt (fun r ↦ crossingMatrix c (Ψ r) i j)
      (crossingMatrixDeriv c (Ψ t) Ψ' i j) s t := by
  have hD (k l : n ⊕ n) : HasDerivWithinAt (fun r ↦ (Ψ r - 1) k l) (Ψ' k l) s t := by
    simpa only [Matrix.sub_apply] using (h k l).sub_const ((1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) k l)
  have hsum : HasDerivWithinAt (fun r ↦ ((Ψ r - 1)ᵀ * (Ψ r - 1) : Matrix (n ⊕ n) (n ⊕ n) ℝ) i j)
      ((Ψ'ᵀ * (Ψ t - 1) + (Ψ t - 1)ᵀ * Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ) i j) s t := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      ← Finset.sum_add_distrib]
    exact HasDerivWithinAt.fun_sum fun k _ ↦ (hD k i).mul (hD k j)
  simpa only [crossingMatrix, crossingMatrixDeriv, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul] using (hasDerivWithinAt_transpose_mul_J_sub_J_mul h i j).fun_add (hsum.const_mul c)

/-- The signature of the crossing form of `crossingMatrix c` is that of the crossing form of `Ψ`. -/
private theorem sigPos_sub_sigNeg_crossingForm_crossingMatrix
    {Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨ : Ψ ∈ symplecticGroup n ℝ) {c : ℝ}
    (h : IsUnit (Ψ + 1 - c • (J n ℝ * (Ψ - 1))).det) (Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (sigPos (crossingForm (crossingMatrix c Ψ) (crossingMatrixDeriv c Ψ Ψ')) : ℤ) -
        sigNeg (crossingForm (crossingMatrix c Ψ) (crossingMatrixDeriv c Ψ Ψ')) =
      (sigPos (crossingForm (Ψ - 1) (-(J n ℝ * Ψ'))) : ℤ) -
        sigNeg (crossingForm (Ψ - 1) (-(J n ℝ * Ψ'))) := by
  have e : QuadraticMap.Equivalent _ _ := ⟨crossingFormIsometryEquivSymplectic hΨ h Ψ'⟩
  rw [e.sigPos_eq, e.sigNeg_eq, QuadraticForm.sigPos_smul_of_pos _ two_pos,
    QuadraticForm.sigNeg_smul_of_pos _ two_pos]

/-- Where `Ψ + 1 - c • (J (Ψ - 1))` is invertible, a regular crossing of `Ψ` is a regular crossing
of `crossingMatrix c`. -/
private theorem nondegenerate_crossingForm_crossingMatrix
    {Ψ Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨ : Ψ ∈ symplecticGroup n ℝ) {c : ℝ}
    (h : IsUnit (Ψ + 1 - c • (J n ℝ * (Ψ - 1))).det)
    (hreg : (crossingForm (Ψ - 1) (-(J n ℝ * Ψ'))).Nondegenerate) :
    (crossingForm (crossingMatrix c Ψ) (crossingMatrixDeriv c Ψ Ψ')).Nondegenerate :=
  (crossingFormIsometryEquivSymplectic hΨ h Ψ').nondegenerate_iff.2
    ((QuadraticMap.nondegenerate_smul_iff (isUnit_iff_ne_zero.2 two_ne_zero) _).2 hreg)

/-- The matrix `crossingMatrix c (Ψ t)` is continuous where `Ψ` is. -/
private theorem continuousOn_crossingMatrix {Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} {s : Set ℝ}
    (hΨc : ContinuousOn Ψ s) (c : ℝ) : ContinuousOn (fun t ↦ crossingMatrix c (Ψ t)) s :=
  ((((continuous_id.matrix_transpose.matrix_mul continuous_const).sub
    (continuous_const.matrix_mul continuous_id)).add
      (((continuous_id.sub continuous_const).matrix_transpose.matrix_mul
        (continuous_id.sub continuous_const)).const_smul c)).comp_continuousOn hΨc)

/-- The determinant of `M + 1 - c • (J (M - 1))` is continuous in the matrix `M`. -/
private theorem continuous_det_add_one_sub_smul (c : ℝ) :
    Continuous fun M : Matrix (n ⊕ n) (n ⊕ n) ℝ ↦ (M + 1 - c • (J n ℝ * (M - 1))).det :=
  ((continuous_id.add continuous_const).sub ((continuous_const.matrix_mul
    (continuous_id.sub continuous_const)).const_smul c)).matrix_det

/-- Along a path `Ψ` of symplectic matrices on `[a, b]` such that `Ψ + 1 - c • (J (Ψ - 1))` stays
invertible, with regular crossings, the signature of `crossingMatrix c Ψ` changes by the signatures
of the crossing forms of `Ψ`, counted twice at the interior crossings and once at the endpoints. -/
private theorem signature_crossingMatrix_sub_signature {a b : ℝ} (hab : a < b)
    {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨc : ContinuousOn Ψ (Icc a b))
    (hmem : ∀ t ∈ Icc a b, Ψ t ∈ symplecticGroup n ℝ) {c : ℝ}
    (h₁ : ∀ t ∈ Icc a b, IsUnit (Ψ t + 1 - c • (J n ℝ * (Ψ t - 1))).det)
    (hd : ∀ t ∈ Icc a b, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc a b) t)
    (hreg : ∀ t ∈ Icc a b, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    signature (crossingMatrix c (Ψ b)) - signature (crossingMatrix c (Ψ a)) =
      crossingSig Ψ Ψ' a + 2 * ∑ᶠ t ∈ Ioo a b, crossingSig Ψ Ψ' t + crossingSig Ψ Ψ' b := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ, ∀ t, K t = crossingMatrix c (Ψ t) :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ,
      ∀ t, K' t = crossingMatrixDeriv c (Ψ t) (Ψ' t) :=
    ⟨_, fun _ ↦ rfl⟩
  have hKc : ContinuousOn K (Icc a b) := (continuousOn_crossingMatrix hΨc c).congr fun t _ ↦ hK t
  have hKsymm (t : ℝ) (_ : t ∈ Icc a b) : (K t).IsSymm := by
    rw [hK]
    exact transpose_transpose_mul_J_sub_J_mul_add_smul (Ψ t) c
  -- The crossings of `K` are those of `Ψ`.
  have hdet (t : ℝ) (ht : t ∈ Icc a b) (hKt : (K t).det = 0) : (Ψ t - 1).det = 0 := by
    rwa [hK, crossingMatrix, det_transpose_mul_J_sub_J_mul_add_smul_eq_zero_iff (hmem t ht)
      (h₁ t ht)] at hKt
  have hKd (t : ℝ) (ht : t ∈ Icc a b) (hKt : (K t).det = 0) (i j : n ⊕ n) :
      HasDerivWithinAt (fun r ↦ K r i j) (K' t i j) (Icc a b) t := by
    simpa only [hK, hK'] using hasDerivWithinAt_crossingMatrix c (hd t ht (hdet t ht hKt)) i j
  -- The crossing forms of `K` are twice those of `Ψ`.
  have hcross (t : ℝ) (ht : t ∈ Icc a b) :
      (sigPos (crossingForm (K t) (K' t)) : ℤ) - sigNeg (crossingForm (K t) (K' t)) =
        crossingSig Ψ Ψ' t := by
    rw [hK, hK']
    exact sigPos_sub_sigNeg_crossingForm_crossingMatrix (hmem t ht) (h₁ t ht) (Ψ' t)
  have hKreg (t : ℝ) (ht : t ∈ Icc a b) (hKt : (K t).det = 0) :
      (crossingForm (K t) (K' t)).Nondegenerate := by
    rw [hK, hK']
    exact nondegenerate_crossingForm_crossingMatrix (hmem t ht) (h₁ t ht)
      (hreg t ht (hdet t ht hKt))
  rw [← hK, ← hK, signature_sub_signature_eq_crossingForm_add_two_mul_finsum hab hKc
    hKsymm hKd hKreg, hcross a (left_mem_Icc.2 hab.le), hcross b (right_mem_Icc.2 hab.le),
    finsum_mem_congr rfl fun t ht ↦ hcross t (Ioo_subset_Icc_self ht)]

/-- **Regular crossings are isolated.** At a regular crossing `t ∈ [0, 1]`, choose `c` with
`Ψ t + 1 - c • (J (Ψ t - 1))` invertible. Then `Ψ s` does not have the eigenvalue `1` at the
parameters `s ≠ t` of `[0, 1]` close to `t`: near `t` the crossings of `Ψ` are those of the
symmetric matrices `crossingMatrix c Ψ`, and regular crossings of a path of symmetric matrices are
isolated. -/
private theorem eventually_nhdsWithin_Icc_diff_det_sub_one_ne_zero
    {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨc : ContinuousOn Ψ (Icc 0 1))
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {c : ℝ} (hunit : IsUnit (Ψ t + 1 - c • (J n ℝ * (Ψ t - 1))).det)
    (hd : ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    ∀ᶠ s in 𝓝[Icc 0 1 \ {t}] t, (Ψ s - 1).det ≠ 0 := by
  -- The crossings of the path of symmetric matrices `crossingMatrix c Ψ` are isolated.
  obtain ⟨V, hV⟩ : ∃ V : ℝ → (n ⊕ n → ℝ) →L[ℝ] (n ⊕ n → ℝ) →L[ℝ] ℝ,
      V = fun s ↦ (crossingMatrix c (Ψ s)).toContinuousLinearMap₂' :=
    ⟨_, rfl⟩
  have hsymm (s : ℝ) : (V s).toBilinForm.IsSymm := by
    rw [hV]
    exact isSymm_toBilinForm_toContinuousLinearMap₂'
      (transpose_transpose_mul_J_sub_J_mul_add_smul (Ψ s) c)
  have hVd : HasDerivWithinAt V (crossingMatrixDeriv c (Ψ t) (Ψ' t)).toContinuousLinearMap₂'
      (Icc 0 1) t := by
    rw [hV]
    exact hasDerivWithinAt_toContinuousLinearMap₂' (hasDerivWithinAt_crossingMatrix c hd)
  have hΓ : (ContinuousLinearMap.crossingForm (V t)
      (crossingMatrixDeriv c (Ψ t) (Ψ' t)).toContinuousLinearMap₂').Nondegenerate := by
    rw [hV]
    exact (crossingFormIsometryEquiv (transpose_transpose_mul_J_sub_J_mul_add_smul (Ψ t) c)
      _).nondegenerate_iff.2 (nondegenerate_crossingForm_crossingMatrix (hmem t ht) hunit hreg)
  have hK :=
    ContinuousLinearMap.eventually_nhdsWithin_Icc_diff_nondegenerate_of_crossingForm_nondegenerate
      ht (fun s _ ↦ hsymm s) hVd hΓ
  -- Near `t` in `[0, 1]` the matrix `Ψ + 1 - c • (J (Ψ - 1))` stays invertible, so those are the
  -- crossings of `Ψ`.
  have hnear : ∀ᶠ s in 𝓝[Icc 0 1 \ {t}] t, (Ψ s + 1 - c • (J n ℝ * (Ψ s - 1))).det ≠ 0 :=
    nhdsWithin_mono _ Set.sdiff_subset
      (((continuous_det_add_one_sub_smul c).comp_continuousOn hΨc t ht).eventually
        (isOpen_ne.mem_nhds hunit.ne_zero))
  filter_upwards [hK, hnear, self_mem_nhdsWithin] with s hs hs' hsI
  rw [hV, nondegenerate_toBilinForm_toContinuousLinearMap₂'_iff_det_ne_zero] at hs
  exact fun h ↦ hs ((det_transpose_mul_J_sub_J_mul_add_smul_eq_zero_iff (hmem s hsI.1)
    (isUnit_iff_ne_zero.2 hs')).2 h)

/-- **Regular crossings are finite in number.** If every crossing `t ∈ [0, 1]` is regular, there
are finitely many crossings: they form a closed subset of `[0, 1]` whose points are isolated. -/
private theorem finite_setOf_det_sub_one_eq_zero {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hΨc : ContinuousOn Ψ (Icc 0 1)) (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite := by
  have hclosed : IsClosed {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0} :=
    ContinuousOn.preimage_isClosed_of_isClosed
      (continuous_id.matrix_det.comp_continuousOn (hΨc.sub continuousOn_const)) isClosed_Icc
      isClosed_singleton
  refine (isCompact_Icc.of_isClosed_subset hclosed fun t ht ↦ ht.1).finite
    (isDiscrete_iff_nhdsNE.2 fun t ht ↦ ?_)
  rw [inf_principal_eq_bot]
  obtain ⟨c, -, hc⟩ := exists_mem_Ioo_isUnit_det_add_one_sub_smul (hmem t ht.1) one_pos
  have h := eventually_nhdsWithin_iff.1 (eventually_nhdsWithin_Icc_diff_det_sub_one_ne_zero hΨc
    hmem ht.1 hc (hd t ht.1 ht.2) (hreg t ht.1 ht.2))
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with s hs hne hsC
  exact hs ⟨hsC.1, hne⟩ hsC.2

/-- The crossing sum of `Ψ` over `[a, b]`: minus the sum of the signatures of the crossing forms
at the parameters of `[a, b]`, those at `a` and `b` counting one half. It is written through
`[a, b)`, so that it is additive in the interval and vanishes for `a = b`. -/
private noncomputable def crossingSum (Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ) (a b : ℝ) : ℝ :=
  -(((∑ᶠ t ∈ Ico a b, crossingSig Ψ Ψ' t : ℤ) : ℝ) - (crossingSig Ψ Ψ' a : ℝ) / 2 +
    (crossingSig Ψ Ψ' b : ℝ) / 2)

section CrossingSum

variable {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}

/-- With finitely many crossings in `[0, 1]`, a subset of `[0, 1]` contains finitely many
parameters at which the crossing form has nonzero signature. -/
private theorem finite_inter_support_crossingSig
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite) {s : Set ℝ} (hs : s ⊆ Icc 0 1) :
    (s ∩ Function.support (crossingSig Ψ Ψ')).Finite :=
  hfin.subset fun _ ht ↦ ⟨hs ht.1, not_not.1 fun h ↦ ht.2 (crossingSig_eq_zero h)⟩

/-- The crossing sum is additive over adjacent intervals of `[0, 1]`. -/
private theorem crossingSum_add_crossingSum
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite) {a b c : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    crossingSum Ψ Ψ' a b + crossingSum Ψ Ψ' b c = crossingSum Ψ Ψ' a c := by
  have h := finsum_mem_union' (f := crossingSig Ψ Ψ') Ico_disjoint_Ico_same
    (finite_inter_support_crossingSig hfin
      (Ico_subset_Icc_self.trans (Icc_subset_Icc ha (hbc.trans hc))))
    (finite_inter_support_crossingSig hfin
      (Ico_subset_Icc_self.trans (Icc_subset_Icc (ha.trans hab) hc)))
  rw [Ico_union_Ico_eq_Ico hab hbc] at h
  simp only [crossingSum, h]
  push_cast
  ring

/-- On a nondegenerate interval of `[0, 1]` the crossing sum is minus the sum of the signatures
of the crossing forms in the open interval and half those at the endpoints. -/
private theorem crossingSum_eq
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    crossingSum Ψ Ψ' a b = -(((crossingSig Ψ Ψ' a + crossingSig Ψ Ψ' b : ℤ) : ℝ) / 2 +
      ((∑ᶠ t ∈ Ioo a b, crossingSig Ψ Ψ' t : ℤ) : ℝ)) := by
  rw [crossingSum, ← insert_left_Ioo hab, finsum_mem_insert' _
    (fun h : a ∈ Ioo a b ↦ lt_irrefl a h.1)
    (finite_inter_support_crossingSig hfin (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha hb)))]
  push_cast
  ring

end CrossingSum

/-- **Uniformly invertible shears.** For a continuous path `Ψ` on `[0, 1]` there is `ε > 0` such
that `1 - β • (J (Ψ t - 1))` is invertible for all `|β| < ε` and all `t`: it is the identity at
`β = 0`, and `[0, 1]` is compact. -/
private theorem exists_pos_forall_isUnit_det_one_sub_smul {Ψ : I → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hΨ : Continuous Ψ) :
    ∃ ε > (0 : ℝ), ∀ β ∈ Ioo (-ε) ε, ∀ t, IsUnit (1 - β • (J n ℝ * (Ψ t - 1))).det := by
  have hf : Continuous fun p : ℝ × I ↦ (1 - p.1 • (J n ℝ * (Ψ p.2 - 1))).det :=
    (continuous_const.sub (continuous_fst.smul (continuous_const.matrix_mul
      ((hΨ.comp continuous_snd).sub continuous_const)))).matrix_det
  have h := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun β t ↦ (1 - β • (J n ℝ * (Ψ t - 1))).det ≠ 0) fun t _ ↦
      hf.continuousAt.eventually_ne (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 h
  refine ⟨ε, hε, fun β hβ t ↦ isUnit_iff_ne_zero.2 (hball β ?_ t (mem_univ t))⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  exact hβ

/-- `[0, 1]` subdivides into intervals on each of which `Ψ + 1 - c • (J (Ψ - 1))` is invertible
for some `c ∈ (-ε, ε)`: by `TauCeti.exists_mem_Ioo_isUnit_det_add_one_sub_smul`, the open sets of
parameters, one for each `c`, cover `[0, 1]`. -/
private theorem exists_monotone_isUnit_det_add_one_sub_smul
    {Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨI : Continuous fun t : I ↦ Ψ t)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ m ≥ N, t m = 1) ∧ ∀ m, ∃ c ∈ Ioo (-ε) ε,
      ∀ r ∈ Icc (t m : ℝ) (t (m + 1)), IsUnit (Ψ r + 1 - c • (J n ℝ * (Ψ r - 1))).det := by
  obtain ⟨t, ht0, htm, hN, htc⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (c := fun c : Ioo (-ε) ε ↦ {t : I | (Ψ t + 1 - (c : ℝ) • (J n ℝ * (Ψ t - 1))).det ≠ 0})
    (fun c ↦ isOpen_ne_fun ((continuous_det_add_one_sub_smul (c : ℝ)).comp hΨI) continuous_const)
    fun t _ ↦ mem_iUnion.2 <| by
      obtain ⟨c, hc, hu⟩ := exists_mem_Ioo_isUnit_det_add_one_sub_smul (hmem t t.property) hε
      exact ⟨⟨c, hc⟩, hu.ne_zero⟩
  refine ⟨t, ht0, htm, hN, fun m ↦ ?_⟩
  obtain ⟨c, hc⟩ := htc m
  refine ⟨c, c.property, fun r hr ↦ isUnit_iff_ne_zero.2 ?_⟩
  simpa using hc (a := ⟨r, Icc_subset_Icc (unitInterval.nonneg _) (unitInterval.le_one _) hr⟩)
    ⟨Subtype.coe_le_coe.1 hr.1, Subtype.coe_le_coe.1 hr.2⟩

section Subpath

variable {A B : GLSymplectic n ℝ} (γ : Path A B) {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}

/-- The matrices along the subpath of `γ` from `a` to `b ≥ a` are the matrices `Ψ t`,
`t ∈ [a, b]`. -/
private theorem exists_mem_Icc_coe_subpath_eq
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t) {a b : I}
    (hab : a ≤ b) (s : I) :
    ∃ t ∈ Icc (a : ℝ) b, ((γ.subpath a b s : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t := by
  obtain ⟨t, ht, hts⟩ := (γ.range_subpath_of_le a b hab).le (mem_range_self s)
  exact ⟨t, ⟨Subtype.coe_le_coe.2 ht.1, Subtype.coe_le_coe.2 ht.2⟩, by rw [← hts, hγ]⟩

/-- On an interval `[a, b]` of `[0, 1]` on which `Ψ + 1 - c • (J (Ψ - 1))` is invertible and the
shears `symplecticShear (s c / 2) Ψ` are defined, the Conley–Zehnder index of the subpath of `γ`
is the crossing sum. -/
private theorem conleyZehnderIndex_subpath_eq_crossingSum
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t)
    (hΨc : ContinuousOn Ψ (Icc 0 1)) (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ)
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate)
    {a b : I} (hab : a ≤ b) {c : ℝ}
    (hN : ∀ s : I, ∀ t ∈ Icc (a : ℝ) b, IsUnit (1 - ((s : ℝ) * (c / 2)) • (J n ℝ * (Ψ t - 1))).det)
    (h₁ : ∀ t ∈ Icc (a : ℝ) b, IsUnit (Ψ t + 1 - c • (J n ℝ * (Ψ t - 1))).det) :
    conleyZehnderIndex (γ.subpath a b) = crossingSum Ψ Ψ' a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · rw [Path.subpath_self, conleyZehnderIndex_refl]
    simp [crossingSum]
  have hab' : (a : ℝ) < b := hlt
  have hIcc : Icc (a : ℝ) b ⊆ Icc 0 1 :=
    Icc_subset_Icc (unitInterval.nonneg a) (unitInterval.le_one b)
  have hsig := congrArg (Int.cast : ℤ → ℝ)
    (signature_crossingMatrix_sub_signature hab' (hΨc.mono hIcc)
      (fun t ht ↦ hmem t (hIcc ht)) h₁ (fun t ht h i j ↦ (hd t (hIcc ht) h i j).mono hIcc)
      fun t ht ↦ hreg t (hIcc ht))
  have hCZ := conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one_sub_smul (γ.subpath a b)
    (c := c) (fun s u ↦ by
      obtain ⟨t, ht, hts⟩ := exists_mem_Icc_coe_subpath_eq γ hγ hlt.le u
      rw [hts]
      exact hN s t ht) fun u ↦ by
      obtain ⟨t, ht, hts⟩ := exists_mem_Icc_coe_subpath_eq γ hγ hlt.le u
      rw [hts]
      exact h₁ t ht
  rw [hCZ, hγ, hγ, crossingSum_eq hfin (unitInterval.nonneg a) hab' (unitInterval.le_one b)]
  push_cast at hsig ⊢
  linarith

/-- If on each interval `[t m, t (m + 1)]` of a subdivision of `[0, 1]` the Conley–Zehnder index
of the subpath of `γ` is the crossing sum, then so it is on each interval `[0, t m]`. -/
private theorem conleyZehnderIndex_subpath_zero_eq_crossingSum
    (hfin : {t ∈ Icc (0 : ℝ) 1 | (Ψ t - 1).det = 0}.Finite) {t : ℕ → I} (ht0 : t 0 = 0)
    (htm : Monotone t)
    (hpiece : ∀ m, conleyZehnderIndex (γ.subpath (t m) (t (m + 1))) =
      crossingSum Ψ Ψ' (t m) (t (m + 1))) (m : ℕ) :
    conleyZehnderIndex (γ.subpath 0 (t m)) = crossingSum Ψ Ψ' 0 (t m) := by
  induction m with
  | zero =>
    rw [ht0, Path.subpath_self, conleyZehnderIndex_refl]
    simp [crossingSum]
  | succ m ih =>
    rw [← conleyZehnderIndex_eq_of_homotopic (Path.Homotopic.subpath_trans_subpath γ 0 (t m)
      (t (m + 1))), conleyZehnderIndex_trans, ih, hpiece m]
    exact crossingSum_add_crossingSum hfin le_rfl (unitInterval.nonneg _) (htm m.le_succ)
      (unitInterval.le_one _)

end Subpath

/-- **The crossing form formula for the Conley–Zehnder index.** Let `γ` be a path of symplectic
matrices, read on `[0, 1]` as a matrix-valued function `Ψ`. Suppose that at every crossing
`t ∈ [0, 1]`, where `Ψ t` has the eigenvalue `1`, `Ψ` has entrywise derivative `Ψ' t` within
`[0, 1]`, and the crossing form `Matrix.crossingForm (Ψ t - 1) (-(J * Ψ' t))`, the form
`v ↦ -v ⬝ᵥ J Ψ' t v` on the fixed vectors of `Ψ t`, is nondegenerate. Then the Conley–Zehnder
index of `γ` is minus the sum of the signatures of the crossing forms, the crossings at the
endpoints counting one half. Parameters that are not crossings contribute zero, and `Ψ` may have
the eigenvalue `-1` anywhere, including at its crossings. -/
theorem conleyZehnderIndex_eq_neg_crossingForm_add_finsum
    {A B : GLSymplectic n ℝ} (γ : Path A B)
    {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    conleyZehnderIndex γ =
      -((((sigPos (crossingForm (Ψ 0 - 1) (-(J n ℝ * Ψ' 0))) : ℤ) -
            sigNeg (crossingForm (Ψ 0 - 1) (-(J n ℝ * Ψ' 0))) +
          ((sigPos (crossingForm (Ψ 1 - 1) (-(J n ℝ * Ψ' 1))) : ℤ) -
            sigNeg (crossingForm (Ψ 1 - 1) (-(J n ℝ * Ψ' 1)))) : ℤ) : ℝ) / 2 +
        ((∑ᶠ t ∈ Ioo (0 : ℝ) 1,
          ((sigPos (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))) : ℤ) -
            sigNeg (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t)))) : ℤ) : ℝ)) := by
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Ψ t ∈ symplecticGroup n ℝ := by
    simpa [← hγ ⟨t, ht⟩] using mem_iff_mem_symplecticGroup.1 (γ ⟨t, ht⟩).property
  have hΨI : Continuous fun t : I ↦ Ψ t :=
    (Units.continuous_val.comp (continuous_subtypeVal.comp γ.continuous)).congr hγ
  have hΨc : ContinuousOn Ψ (Icc 0 1) := by
    refine (Units.continuous_val.comp (continuous_subtypeVal.comp
      γ.continuous_extend)).continuousOn.congr fun t ht ↦ ?_
    simp [← hγ ⟨t, ht⟩, Path.extend_extends' γ ⟨t, ht⟩]
  have hfin := finite_setOf_det_sub_one_eq_zero hΨc hmem hd hreg
  -- Subdivide `[0, 1]` into intervals each carrying a complement `c` small enough for the shears.
  obtain ⟨ε, hε, hshear⟩ := exists_pos_forall_isUnit_det_one_sub_smul hΨI
  obtain ⟨t, ht0, htm, ⟨N, hN⟩, htc⟩ := exists_monotone_isUnit_det_add_one_sub_smul hΨI hmem hε
  have h := conleyZehnderIndex_subpath_zero_eq_crossingSum γ hfin ht0 htm (fun m ↦ by
    obtain ⟨c, hc, hc'⟩ := htc m
    refine conleyZehnderIndex_subpath_eq_crossingSum γ hγ hΨc hmem hfin hd hreg (htm m.le_succ)
      (fun s r hr ↦ ?_) hc'
    have hr' : r ∈ Icc (0 : ℝ) 1 :=
      Icc_subset_Icc (unitInterval.nonneg _) (unitInterval.le_one _) hr
    refine hshear _ ⟨?_, ?_⟩ ⟨r, hr'⟩ <;>
      nlinarith [unitInterval.nonneg s, unitInterval.le_one s, hc.1, hc.2]) N
  rw [hN N le_rfl, conleyZehnderIndex_congr _ γ fun s ↦ by simp [Path.subpath_zero_one],
    Set.Icc.coe_one, crossingSum_eq hfin le_rfl zero_lt_one le_rfl] at h
  simpa only [crossingSig] using h

end GLSymplectic

end TauCeti
