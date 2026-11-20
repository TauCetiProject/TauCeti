/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Omega
import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.DualJacobiTrudi

/-!
# The Jacobi--Trudi identities in the symmetric functions and `ω(s_λ) = s_(λᵗ)`

Over a commutative ring `R`, the Schur function of a partition `μ` in the ring `Λ_R` of symmetric
functions is given by the two Jacobi--Trudi determinants

`s_μ = det (h_(μᵢ - i + j))_(0 ≤ i, j < r)` and `s_μ = det (e_(μᵗᵢ - i + j))_(0 ≤ i, j < r')`,

for every `r` at least the number of parts (rows) of `μ` and every `r'` at least its largest part
(number of columns of `μ`, i.e. parts of the conjugate partition `μᵗ`). The indices are integers,
and `h_m = e_m = 0` for `m < 0`; these are `TauCeti.SymmetricFunction.hsymmInt` and
`TauCeti.SymmetricFunction.esymmInt`. Both identities follow from their versions in finitely many
variables (`TauCeti.schurPoly_eq_det_hsymmInt` and `Nat.Partition.schurPoly_eq_det_esymmInt`),
since a symmetric function is determined by its specializations to the alphabets `Fin d`.

The algebra involution `ω` (`TauCeti.SymmetricFunction.omega`) exchanges `h_m` and `e_m` in every
integer degree, so it carries the dual Jacobi--Trudi determinant of `μ` into the Jacobi--Trudi
determinant of `μᵗ`, giving `ω(s_μ) = s_(μᵗ)` (`TauCeti.SymmetricFunction.omega_of_stableSchur`).
Because the Schur functions of degree `n` form an `R`-basis of the degree-`n` symmetric functions
(`TauCeti.stableSchurBasis`), `ω` preserves the grading: its restriction to degree `n` is the
linear involution `TauCeti.stableOmega R n` permuting the Schur basis by partition conjugation.

## Main definitions

* `TauCeti.SymmetricFunction.hsymmInt R m`: the complete homogeneous symmetric function `h_m` for
  `m ≥ 0`, and `0` for `m < 0`.
* `TauCeti.SymmetricFunction.esymmInt R m`: the elementary symmetric function `e_m` for `m ≥ 0`,
  and `0` for `m < 0`.
* `TauCeti.stableOmega R n`: the degree-`n` linear involution induced by `ω`, sending `s_μ` to
  `s_(μᵗ)`.

## Main results

* `TauCeti.SymmetricFunction.of_stableSchur_eq_det_hsymmInt`,
  `TauCeti.SymmetricFunction.of_stableSchur_shapePartition_eq_det_hsymmInt`: **the Jacobi--Trudi
  identity** `s_μ = det (h_(μᵢ - i + j))` in `Λ_R`.
* `TauCeti.SymmetricFunction.of_stableSchur_eq_det_esymmInt`,
  `TauCeti.SymmetricFunction.of_stableSchur_eq_det_esymmInt_conjugate`,
  `TauCeti.SymmetricFunction.of_stableSchur_shapePartition_eq_det_esymmInt`: **the dual
  Jacobi--Trudi identity** `s_μ = det (e_(μᵗᵢ - i + j))` in `Λ_R`.
* `TauCeti.SymmetricFunction.omega_hsymmInt`, `TauCeti.SymmetricFunction.omega_esymmInt`:
  `ω(h_m) = e_m` and `ω(e_m) = h_m` in every integer degree.
* `TauCeti.SymmetricFunction.omega_of_stableSchur`: **`ω(s_μ) = s_(μᵗ)`**.
* `TauCeti.SymmetricFunction.of_stableSchur_singletonSecondRow_eq_hsymm`,
  `TauCeti.SymmetricFunction.of_stableSchur_conjugate_singletonSecondRow_eq_esymm`:
  `s_{(n + 1, 1)} = h_{n + 1} h₁ - h_{n + 2}` and `s_{(2, 1ⁿ)} = e_{n + 1} e₁ - e_{n + 2}`.
* `TauCeti.SymmetricFunction.omega_of`, `TauCeti.SymmetricFunction.omega_apply`,
  `TauCeti.SymmetricFunction.lmap_stableOmega`: `ω` acts degree by degree as `TauCeti.stableOmega`.
* `TauCeti.stableOmega_stableSchur`, `TauCeti.stableOmega_stableEsymm`,
  `TauCeti.stableOmega_stableHsymm`, `TauCeti.stableOmega_stablePsum`,
  `TauCeti.stableOmega_stableSymmetricMul`, `TauCeti.stableSymmetricMap_stableOmega`: the action of
  `TauCeti.stableOmega` on the standard families, on homogeneous products, and under change of
  coefficients.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, (3.4), (3.5), and (3.8).
-/

public section

namespace TauCeti

open MvPolynomial DirectSum

namespace SymmetricFunction

/-! ### Integer-indexed complete and elementary symmetric functions -/

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The **complete homogeneous symmetric function of integer degree** `m`: `h_m` for `m ≥ 0` and
`0` for `m < 0`. This is the indexing of the Jacobi--Trudi determinant
`TauCeti.SymmetricFunction.of_stableSchur_eq_det_hsymmInt`. -/
noncomputable def hsymmInt (m : ℤ) : SymmetricFunction R :=
  if 0 ≤ m then DirectSum.of _ m.toNat (stableHsymm R m.toNat) else 0

/-- The **elementary symmetric function of integer degree** `m`: `e_m` for `m ≥ 0` and `0` for
`m < 0`. This is the indexing of the dual Jacobi--Trudi determinant
`TauCeti.SymmetricFunction.of_stableSchur_eq_det_esymmInt`. -/
noncomputable def esymmInt (m : ℤ) : SymmetricFunction R :=
  if 0 ≤ m then DirectSum.of _ m.toNat (stableEsymm R m.toNat) else 0

variable {R}

/-- In a nonnegative degree, `TauCeti.SymmetricFunction.hsymmInt` is `h_m`. -/
@[simp]
theorem hsymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    hsymmInt R m = DirectSum.of _ m.toNat (stableHsymm R m.toNat) := by
  simp [hsymmInt, hm]

/-- In a natural-number degree, `TauCeti.SymmetricFunction.hsymmInt` is `h_n`. -/
theorem hsymmInt_natCast (n : ℕ) :
    hsymmInt R n = DirectSum.of _ n (stableHsymm R n) := by
  simp

/-- In a negative degree, `TauCeti.SymmetricFunction.hsymmInt` vanishes. -/
@[simp]
theorem hsymmInt_of_neg {m : ℤ} (hm : m < 0) : hsymmInt R m = 0 := by
  simp [hsymmInt, not_le.mpr hm]

/-- `h_0 = 1`. -/
theorem hsymmInt_zero : hsymmInt R 0 = 1 := by
  simp

/-- In a nonnegative degree, `TauCeti.SymmetricFunction.esymmInt` is `e_m`. -/
@[simp]
theorem esymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    esymmInt R m = DirectSum.of _ m.toNat (stableEsymm R m.toNat) := by
  simp [esymmInt, hm]

/-- In a natural-number degree, `TauCeti.SymmetricFunction.esymmInt` is `e_n`. -/
theorem esymmInt_natCast (n : ℕ) :
    esymmInt R n = DirectSum.of _ n (stableEsymm R n) := by
  simp

/-- In a negative degree, `TauCeti.SymmetricFunction.esymmInt` vanishes. -/
@[simp]
theorem esymmInt_of_neg {m : ℤ} (hm : m < 0) : esymmInt R m = 0 := by
  simp [esymmInt, not_le.mpr hm]

/-- `e_0 = 1`. -/
theorem esymmInt_zero : esymmInt R 0 = 1 := by
  simp

/-- In `d` variables, `TauCeti.SymmetricFunction.hsymmInt` specializes to `TauCeti.hsymmInt`. -/
@[simp]
theorem specialization_hsymmInt (d : ℕ) (m : ℤ) :
    specialization R d (hsymmInt R m) = TauCeti.hsymmInt (Fin d) R m := by
  rcases le_or_gt 0 m with hm | hm
  · simp [hsymmInt, hm]
  · simp [hm]

/-- In `d` variables, `TauCeti.SymmetricFunction.esymmInt` specializes to `TauCeti.esymmInt`. -/
@[simp]
theorem specialization_esymmInt (d : ℕ) (m : ℤ) :
    specialization R d (esymmInt R m) = TauCeti.esymmInt (Fin d) R m := by
  rcases le_or_gt 0 m with hm | hm
  · simp [esymmInt, hm]
  · simp [hm]

/-- Changing coefficients fixes `TauCeti.SymmetricFunction.hsymmInt`. -/
@[simp]
theorem map_hsymmInt {S : Type*} [CommSemiring S] (f : R →+* S) (m : ℤ) :
    map f (hsymmInt R m) = hsymmInt S m := by
  unfold hsymmInt
  split_ifs <;> simp

/-- Changing coefficients fixes `TauCeti.SymmetricFunction.esymmInt`. -/
@[simp]
theorem map_esymmInt {S : Type*} [CommSemiring S] (f : R →+* S) (m : ℤ) :
    map f (esymmInt R m) = esymmInt S m := by
  unfold esymmInt
  split_ifs <;> simp

end CommSemiring

/-! ### The Jacobi--Trudi identities and `ω(s_μ) = s_(μᵗ)` -/

section CommRing

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **`ω(h_m) = e_m`** in every integer degree. -/
@[simp]
theorem omega_hsymmInt (m : ℤ) : omega R (hsymmInt R m) = esymmInt R m := by
  unfold hsymmInt esymmInt
  split_ifs <;> simp

/-- **`ω(e_m) = h_m`** in every integer degree. -/
@[simp]
theorem omega_esymmInt (m : ℤ) : omega R (esymmInt R m) = hsymmInt R m := by
  rw [← omega_hsymmInt, omega_omega]

/-- **The Jacobi--Trudi identity** in the symmetric functions: the Schur function of a partition
`μ` is `det (h_(μᵢ - i + j))_(0 ≤ i, j < r)` for every `r` at least the number of parts of `μ`,
where `μᵢ` is the `i`-th largest part (`0` past the last part) and `h_m = 0` for `m < 0`. -/
theorem of_stableSchur_eq_det_hsymmInt (μ : n.Partition) {r : ℕ} (hr : μ.parts.card ≤ r) :
    DirectSum.of _ n (stableSchur R μ) =
      (Matrix.of fun i j : Fin r =>
        hsymmInt R (((YoungDiagram.ofPartition μ).rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det :=
  ext_specialization fun d => by
    rw [specialization_of, coe_stableSymmetricProj_stableSchur, schurPoly_eq_det_hsymmInt μ hr,
      AlgHom.map_det]
    congr 1
    ext i j : 1
    simp

/-- **The Jacobi--Trudi identity in `Λ_R`**, for a Young diagram `μ`: the Schur function of `μ` is
`det (h_(μᵢ - i + j))_(0 ≤ i, j < r)` for every `r` at least the number of rows of `μ`. -/
theorem of_stableSchur_shapePartition_eq_det_hsymmInt (μ : YoungDiagram) {r : ℕ}
    (hr : μ.colLen 0 ≤ r) :
    DirectSum.of _ μ.card (stableSchur R (shapePartition μ)) =
      (Matrix.of fun i j : Fin r =>
        hsymmInt R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  have hr' : (shapePartition μ).parts.card ≤ r := by
    rwa [← YoungDiagram.colLen_zero_ofPartition, ofPartition_shapePartition]
  simpa using of_stableSchur_eq_det_hsymmInt (R := R) (shapePartition μ) hr'

/-- **The dual Jacobi--Trudi identity** in the symmetric functions: the Schur function of a
partition `μ` is `det (e_(μᵗᵢ - i + j))_(0 ≤ i, j < r)` for every `r` at least the largest part of
`μ`, where `μᵗᵢ` is the length of the `i`-th column of the Young diagram of `μ` and `e_m = 0` for
`m < 0`. -/
theorem of_stableSchur_eq_det_esymmInt (μ : n.Partition) {r : ℕ}
    (hr : (YoungDiagram.ofPartition μ).rowLen 0 ≤ r) :
    DirectSum.of _ n (stableSchur R μ) =
      (Matrix.of fun i j : Fin r =>
        esymmInt R (((YoungDiagram.ofPartition μ).colLen i : ℤ) - (i : ℕ) + (j : ℕ))).det :=
  ext_specialization fun d => by
    rw [specialization_of, coe_stableSymmetricProj_stableSchur,
      Nat.Partition.schurPoly_eq_det_esymmInt μ hr, AlgHom.map_det]
    congr 1
    ext i j : 1
    simp

/-- **The dual Jacobi--Trudi identity in `Λ_R`**, for a Young diagram `μ`: the Schur function of `μ`
is `det (e_(μᵗᵢ - i + j))_(0 ≤ i, j < r)`, where `μᵗᵢ` is the length of column `i`, for every `r`
at least the number of columns of `μ`. -/
theorem of_stableSchur_shapePartition_eq_det_esymmInt (μ : YoungDiagram) {r : ℕ}
    (hr : μ.rowLen 0 ≤ r) :
    DirectSum.of _ μ.card (stableSchur R (shapePartition μ)) =
      (Matrix.of fun i j : Fin r =>
        esymmInt R ((μ.colLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  have hr' : (YoungDiagram.ofPartition (shapePartition μ)).rowLen 0 ≤ r := by
    rwa [ofPartition_shapePartition]
  simpa using of_stableSchur_eq_det_esymmInt (R := R) (shapePartition μ) hr'

/-- **The dual Jacobi--Trudi identity in `Λ_R`, indexed by the parts of the conjugate partition**:
for a partition `μ` of `n` and every `r` at least the number of parts of `μᵗ`,
`s_μ = det (e_(μᵗᵢ - i + j))_(0 ≤ i, j < r)`. -/
theorem of_stableSchur_eq_det_esymmInt_conjugate (μ : n.Partition) {r : ℕ}
    (hr : μ.conjugate.parts.card ≤ r) :
    DirectSum.of _ n (stableSchur R μ) =
      (Matrix.of fun i j : Fin r =>
        esymmInt R
          (((YoungDiagram.ofPartition μ.conjugate).rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  have hr' : (YoungDiagram.ofPartition μ).rowLen 0 ≤ r := by
    rwa [← YoungDiagram.colLen_transpose, ← YoungDiagram.ofPartition_conjugate,
      YoungDiagram.colLen_zero_ofPartition]
  rw [of_stableSchur_eq_det_esymmInt μ hr']
  congr 1
  ext i j : 1
  simp

/-- **`ω(s_μ) = s_(μᵗ)`**: the involution `ω` sends the Schur function of a partition to the Schur
function of the conjugate partition. -/
@[simp]
theorem omega_of_stableSchur (μ : n.Partition) :
    omega R (DirectSum.of _ n (stableSchur R μ)) =
      DirectSum.of _ n (stableSchur R μ.conjugate) := by
  rw [of_stableSchur_eq_det_esymmInt_conjugate μ le_rfl,
    of_stableSchur_eq_det_hsymmInt μ.conjugate le_rfl,
    ← AlgEquiv.coe_toAlgHom, AlgHom.map_det]
  congr 1
  ext i j : 1
  simp

variable (R) in
/-- **The Jacobi--Trudi expansion of `s_{(n + 1, 1)}`**: for every `n`,
`s_{(n + 1, 1)} = h_{n + 1} h₁ - h_{n + 2}` in `Λ_R`. -/
theorem of_stableSchur_singletonSecondRow_eq_hsymm (n : ℕ) :
    DirectSum.of _ (n + 2) (stableSchur R (Nat.Partition.singletonSecondRow n)) =
      (DirectSum.of _ (n + 1) (stableHsymm R (n + 1)) : SymmetricFunction R) *
          DirectSum.of _ 1 (stableHsymm R 1) -
        DirectSum.of _ (n + 2) (stableHsymm R (n + 2)) := by
  have hr : (Nat.Partition.singletonSecondRow n).parts.card ≤ 2 := by
    simp [Nat.Partition.singletonSecondRow_parts]
  have hsort : (((n + 1) ::ₘ {1} : Multiset ℕ).sort (· ≥ ·)) = [n + 1, 1] := by
    simpa only [Nat.Partition.singletonSecondRow_parts, Multiset.insert_eq_cons] using
      Nat.Partition.sort_parts_singletonSecondRow n
  rw [of_stableSchur_eq_det_hsymmInt _ hr, Matrix.det_fin_two,
    ← hsymmInt_natCast (R := R) (n + 1), ← hsymmInt_natCast (R := R) (n + 2)]
  simp [hsort, add_assoc]

variable (R) in
/-- **The dual Jacobi--Trudi expansion of `s_{(2, 1ⁿ)}`** (the Schur function of
`(Nat.Partition.singletonSecondRow n).conjugate`): for every `n`,
`s_{(2, 1ⁿ)} = e_{n + 1} e₁ - e_{n + 2}` in `Λ_R`. -/
theorem of_stableSchur_conjugate_singletonSecondRow_eq_esymm (n : ℕ) :
    DirectSum.of _ (n + 2) (stableSchur R (Nat.Partition.singletonSecondRow n).conjugate) =
      (DirectSum.of _ (n + 1) (stableEsymm R (n + 1)) : SymmetricFunction R) *
          DirectSum.of _ 1 (stableEsymm R 1) -
        DirectSum.of _ (n + 2) (stableEsymm R (n + 2)) := by
  simpa using congrArg (omega R) (of_stableSchur_singletonSecondRow_eq_hsymm R n)

end CommRing

end SymmetricFunction

/-! ### The degreewise involution `stableOmega` -/

section StableOmega

variable (R : Type*) [CommRing R]

/-- **The involution `ω` in degree `n`**: the `R`-linear equivalence on the symmetric functions of
degree `n` sending each Schur function `s_μ` to `s_(μᵗ)` (`TauCeti.stableOmega_stableSchur`). This
is the degree-`n` restriction of `TauCeti.SymmetricFunction.omega`
(`TauCeti.SymmetricFunction.omega_of`, `TauCeti.SymmetricFunction.omega_apply`). -/
noncomputable def stableOmega (n : ℕ) :
    stableSymmetricSubmodule R n ≃ₗ[R] stableSymmetricSubmodule R n :=
  (stableSchurBasis R n).equiv (stableSchurBasis R n)
    (Function.Involutive.toPerm _root_.Nat.Partition.conjugate
      _root_.Nat.Partition.conjugate_conjugate)

/-- **`stableOmega` sends `s_μ` to `s_(μᵗ)`.** -/
@[simp]
theorem stableOmega_stableSchur {n : ℕ} (μ : n.Partition) :
    stableOmega R n (stableSchur R μ) = stableSchur R μ.conjugate := by
  rw [← stableSchurBasis_apply, stableOmega, Module.Basis.equiv_apply, stableSchurBasis_apply]
  rfl

/-- `stableOmega ∘ stableOmega = id`, as linear equivalences. -/
@[simp]
theorem stableOmega_trans_stableOmega (n : ℕ) :
    (stableOmega R n).trans (stableOmega R n) = LinearEquiv.refl R (stableSymmetricSubmodule R n) :=
  LinearEquiv.toLinearMap_injective <| (stableSchurBasis R n).ext fun μ => by simp

/-- **`stableOmega` is an involution.** -/
@[simp]
theorem stableOmega_stableOmega (n : ℕ) (f : stableSymmetricSubmodule R n) :
    stableOmega R n (stableOmega R n f) = f :=
  DFunLike.congr_fun (stableOmega_trans_stableOmega R n) f

/-- `stableOmega` is its own inverse. -/
@[simp]
theorem stableOmega_symm (n : ℕ) : (stableOmega R n).symm = stableOmega R n :=
  LinearEquiv.ext fun f => (LinearEquiv.symm_apply_eq _).mpr (stableOmega_stableOmega R n f).symm

/-- **The Schur coordinates of `stableOmega R n f` are those of `f` at the conjugate partition.** -/
@[simp]
theorem stableSchurBasis_repr_stableOmega {n : ℕ} (f : stableSymmetricSubmodule R n)
    (μ : n.Partition) :
    (stableSchurBasis R n).repr (stableOmega R n f) μ =
      (stableSchurBasis R n).repr f μ.conjugate :=
  calc
    (stableSchurBasis R n).repr (stableOmega R n f) μ
      = ((stableSchurBasis R n).map (stableOmega R n)).repr f μ := by simp
    _ = ((stableSchurBasis R n).repr f)
          ((Function.Involutive.toPerm _root_.Nat.Partition.conjugate
            _root_.Nat.Partition.conjugate_conjugate) μ) := by simp [stableOmega]
    _ = (stableSchurBasis R n).repr f μ.conjugate :=
      congrArg _ (congrFun (Function.Involutive.coe_toPerm _) μ)

namespace SymmetricFunction

/-- **`ω` preserves the grading**: on a symmetric function `f` of degree `n`, `ω` acts in degree
`n` by `TauCeti.stableOmega R n`.

Not a `simp` lemma: `TauCeti.SymmetricFunction.omega_of_stableEsymm`,
`TauCeti.SymmetricFunction.omega_of_stableHsymm`, `TauCeti.SymmetricFunction.omega_of_stablePsum`,
and `TauCeti.SymmetricFunction.omega_of_stableSchur` rewrite `omega` directly on the standard
families without passing through `TauCeti.stableOmega`. -/
theorem omega_of {n : ℕ} (f : stableSymmetricSubmodule R n) :
    omega R (DirectSum.of _ n f) = DirectSum.of _ n (stableOmega R n f) := by
  have h : (omega R).toLinearMap.comp (DirectSum.lof R ℕ _ n) =
      (DirectSum.lof R ℕ _ n).comp (stableOmega R n).toLinearMap :=
    (stableSchurBasis R n).ext fun μ => by simp [DirectSum.lof_eq_of]
  exact DFunLike.congr_fun h f

/-- **As a linear map on `Λ_R`, `ω` is the direct sum of the degreewise maps
`TauCeti.stableOmega R n`.** -/
theorem lmap_stableOmega :
    DirectSum.lmap (fun n => (stableOmega R n).toLinearMap) = (omega R).toLinearMap :=
  DirectSum.linearMap_ext R fun _ => LinearMap.ext fun f => by
    simp [DirectSum.lof_eq_of, omega_of]

/-- **The homogeneous component of degree `n` of `ω(x)` is `stableOmega R n (x n)`.** -/
@[simp]
theorem omega_apply (x : SymmetricFunction R) (n : ℕ) :
    omega R x n = stableOmega R n (x n) := by
  have h := DFunLike.congr_fun (lmap_stableOmega R) x
  simpa using congrArg (fun y : SymmetricFunction R => y n) h.symm

end SymmetricFunction

/-- `stableOmega` fixes the unit in degree zero. -/
@[simp]
theorem stableOmega_stableSymmetricOne :
    stableOmega R 0 (stableSymmetricOne R) = stableSymmetricOne R := by
  refine DirectSum.of_injective (β := fun k => stableSymmetricSubmodule R k) 0 ?_
  rw [← SymmetricFunction.omega_of, SymmetricFunction.of_stableSymmetricOne, map_one]

/-- **`stableOmega` sends `e_n` to `h_n`.** -/
@[simp]
theorem stableOmega_stableEsymm (n : ℕ) :
    stableOmega R n (stableEsymm R n) = stableHsymm R n := by
  refine DirectSum.of_injective (β := fun k => stableSymmetricSubmodule R k) n ?_
  rw [← SymmetricFunction.omega_of, SymmetricFunction.omega_of_stableEsymm]

/-- **`stableOmega` sends `h_n` to `e_n`.** -/
@[simp]
theorem stableOmega_stableHsymm (n : ℕ) :
    stableOmega R n (stableHsymm R n) = stableEsymm R n := by
  refine DirectSum.of_injective (β := fun k => stableSymmetricSubmodule R k) n ?_
  rw [← SymmetricFunction.omega_of, SymmetricFunction.omega_of_stableHsymm]

/-- **`stableOmega` sends `p_n` to `(-1)^(n + 1) • p_n`** for `n ≠ 0`. -/
@[simp]
theorem stableOmega_stablePsum {n : ℕ} (hn : n ≠ 0) :
    stableOmega R n (stablePsum R hn) = (-1 : R) ^ (n + 1) • stablePsum R hn := by
  refine DirectSum.of_injective (β := fun k => stableSymmetricSubmodule R k) n ?_
  rw [← SymmetricFunction.omega_of, SymmetricFunction.omega_of_stablePsum R hn]
  simp [← DirectSum.lof_eq_of R, Algebra.smul_def]

/-- **`stableOmega` is multiplicative across degrees**: on a product of homogeneous symmetric
functions of degrees `n` and `m`, `stableOmega R (n + m)` multiplies their images under
`stableOmega R n` and `stableOmega R m`. -/
@[simp]
theorem stableOmega_stableSymmetricMul {n m : ℕ} (f : stableSymmetricSubmodule R n)
    (g : stableSymmetricSubmodule R m) :
    stableOmega R (n + m) (stableSymmetricMul R n m f g) =
      stableSymmetricMul R n m (stableOmega R n f) (stableOmega R m g) := by
  refine DirectSum.of_injective (β := fun k => stableSymmetricSubmodule R k) (n + m) ?_
  rw [← SymmetricFunction.omega_of, ← gMul_mul_stableSymmetricSubmodule, ← DirectSum.of_mul_of,
    map_mul, SymmetricFunction.omega_of, SymmetricFunction.omega_of, DirectSum.of_mul_of,
    gMul_mul_stableSymmetricSubmodule]

/-- **Changing coefficients commutes with `stableOmega`.** -/
@[simp]
theorem stableSymmetricMap_stableOmega {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {n : ℕ} (g : stableSymmetricSubmodule R n) :
    stableSymmetricMap f n (stableOmega R n g) =
      stableOmega S n (stableSymmetricMap f n g) := by
  have h := congrArg (fun y : SymmetricFunction S => y n)
    (SymmetricFunction.map_omega f (DirectSum.of _ n g))
  simpa [SymmetricFunction.omega_of] using h

end StableOmega

end TauCeti
