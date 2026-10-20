/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.PrimeDecomposition
public import TauCeti.NumberTheory.HeckeRing.Multiplication
import TauCeti.NumberTheory.HeckeRing.Multiplicity.Support
import TauCeti.LinearAlgebra.Matrix.ChainConjugate

/-!
# The leading coefficient of a product of diagonal double cosets

For positive divisibility chains `a` and `b`, the double coset `T(a b)` occurs in the product
`T(a) · T(b)` of the integral Hecke ring of `(SL_n(ℤ), Δ)` with coefficient exactly one. For
`p`-power diagonals with monotone exponent vectors `e` and `f` this is the coefficient of the
leading term `T(p ^ (e + f))` of `T(p ^ e) · T(p ^ f)`; the companion statement that every other
coset of the product lies strictly below it in the dominance order is
`HeckeRing.GLn.exists_primePowDiag_of_diagElem_mul_apply_ne_zero`. Together they form the
triangular expansion on which Shimura's presentation of the `p`-local Hecke ring as a polynomial
ring rests (Theorem 3.20).

The coefficient is Shimura's multiplicity: the number of left cosets `σ diag(a) SL_n(ℤ)` in the
double coset `T(a)` for which `σ diag(a) τ diag(b)` lies in `diag(a b) SL_n(ℤ)` for some `τ`.
The coset of `σ = 1` is one of them, and it is the only one by
`Matrix.dvd_apply_mul_of_dvd_mul_diagonal_mul_diagonal_apply`: an equation
`σ diag(a) τ diag(b) = diag(a) diag(b) γ` with `σ`, `τ`, `γ` in `SL_n(ℤ)` forces
`diag(a)⁻¹ σ diag(a)` to be integral.

## Main results

* `HeckeRing.GLn.diagElem_mul_apply_diagCoset_mul`: the coefficient of `T(a b)` in
  `T(a) · T(b)` is `1`.
* `HeckeRing.GLn.diagElem_primePowDiag_mul_apply_diagCoset_add`: the coefficient of
  `T(p ^ (e + f))` in `T(p ^ e) · T(p ^ f)` is `1`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, the proof of Theorem 3.20.
-/

public section

open Matrix HeckeRing DoubleCoset Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable {n : ℕ}

/-- If `a i ∣ σ i j * a j` for all `i` and `j`, then conjugating `σ ∈ SL_n(ℤ)` by `diag(a)`
stays in `SL_n(ℤ)`. -/
private lemma natDiagGL_inv_mul_mul_mem_SLnZ {a : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (σ : SpecialLinearGroup (Fin n) ℤ) (h : ∀ i j, (a i : ℤ) ∣ σ i j * a j) :
    (natDiagGL n a)⁻¹ * mapGL ℚ σ * natDiagGL n a ∈ SLnZ n := by
  choose Y hY using h
  have hYmul : diagonal (fun i ↦ (a i : ℤ)) * Matrix.of Y =
      (σ : Matrix (Fin n) (Fin n) ℤ) * diagonal (fun i ↦ (a i : ℤ)) := by
    ext i j
    simp [hY]
  have hdet : (Matrix.of Y).det = 1 := by
    have h := congrArg det hYmul
    rw [det_mul, det_mul, σ.prop, one_mul] at h
    have hne : (diagonal (fun i ↦ (a i : ℤ))).det ≠ 0 := by
      rw [det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun i _ ↦ by exact_mod_cast (ha i).ne'
    exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
  let Y' : SpecialLinearGroup (Fin n) ℤ := ⟨Matrix.of Y, hdet⟩
  have hY' : (Y' : Matrix (Fin n) (Fin n) ℤ) = Matrix.of Y := (rfl)
  refine (mem_SLnZ_iff n).2 ⟨Y', ?_⟩
  rw [mul_assoc, eq_inv_mul_iff_mul_eq]
  ext i j
  have hij := congrFun (congrFun hYmul i) j
  simp only [diagonal_mul, mul_diagonal, of_apply] at hij
  simp only [Units.val_mul, natDiagGL_coe n a ha, diagonal_mul, mul_diagonal]
  simp only [mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
    Int.coe_castRingHom, map_apply, hY', of_apply]
  exact_mod_cast hij

/-- **A product landing in `diag(a b) SL_n(ℤ)` has a trivial first factor.** If
`σ diag(a) τ diag(b) = diag(a b) γ` in `GL_n(ℚ)` with `σ`, `τ`, `γ` in `SL_n(ℤ)`, then
`diag(a)⁻¹ σ diag(a)` lies in `SL_n(ℤ)`. -/
private lemma natDiagGL_inv_mul_mul_mem_SLnZ_of_eq {a b : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (ha' : IsDvdChain a) (hb : ∀ i, 0 < b i) (hb' : IsDvdChain b) {σ τ γ : GL (Fin n) ℚ}
    (hσ : σ ∈ SLnZ n) (hτ : τ ∈ SLnZ n) (hγ : γ ∈ SLnZ n)
    (h : σ * natDiagGL n a * τ * natDiagGL n b = natDiagGL n (a * b) * γ) :
    (natDiagGL n a)⁻¹ * σ * natDiagGL n a ∈ SLnZ n := by
  obtain ⟨σ', rfl⟩ := (mem_SLnZ_iff n).1 hσ
  obtain ⟨τ', rfl⟩ := (mem_SLnZ_iff n).1 hτ
  obtain ⟨γ', rfl⟩ := (mem_SLnZ_iff n).1 hγ
  refine natDiagGL_inv_mul_mul_mem_SLnZ ha σ' fun i j ↦ ?_
  -- read the identity in `GL_n(ℚ)` as one between integral matrices
  have hint : (σ' : Matrix (Fin n) (Fin n) ℤ) * diagonal (fun i ↦ (a i : ℤ)) *
      (τ' : Matrix (Fin n) (Fin n) ℤ) * diagonal (fun i ↦ (b i : ℤ)) =
      diagonal (fun i ↦ ((a * b) i : ℤ)) * (γ' : Matrix (Fin n) (Fin n) ℤ) := by
    refine Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective ?_
    have hcast : ∀ X : Matrix (Fin n) (Fin n) ℤ,
        X.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix X := fun _ ↦ (rfl)
    have hmat := congrArg (fun g : GL (Fin n) ℚ ↦ (g : Matrix (Fin n) (Fin n) ℚ)) h
    simp only [Units.val_mul, natDiagGL_coe_eq_map_intCast n _ ha,
      natDiagGL_coe_eq_map_intCast n _ hb,
      natDiagGL_coe_eq_map_intCast n (a * b) fun i ↦ Nat.mul_pos (ha i) (hb i), mapGL_coe_matrix,
      map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom] at hmat
    simp only [hcast, map_mul] at hmat ⊢
    exact hmat
  refine Matrix.dvd_apply_mul_of_dvd_mul_diagonal_mul_diagonal_apply
    (fun i j hij ↦ Int.natCast_dvd_natCast.2 (isDvdChain_iff.1 ha' hij))
    (fun i j hij ↦ Int.natCast_dvd_natCast.2 (isDvdChain_iff.1 hb' hij))
    (fun i ↦ by exact_mod_cast (ha i).ne') (fun i ↦ by exact_mod_cast (hb i).ne')
    (by rw [σ'.prop]; exact isUnit_one) (by rw [τ'.prop]; exact isUnit_one)
    (fun i j ↦ ?_) i j
  rw [hint, diagonal_mul, Pi.mul_apply]
  exact ⟨γ' i j, by push_cast; ring⟩

-- The multiplicities below are those of the Hecke ring, whose finiteness instances need the
-- arithmetic Hecke triple, which carries `NeZero n`.
variable [NeZero n]

/-- `T(a b)` occurs in `T(a) · T(b)` at most once. -/
private lemma multiplicity_diagCoset_mul_le_one {a b : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (ha' : IsDvdChain a) (hb : ∀ i, 0 < b i) (hb' : IsDvdChain b) :
    multiplicity (SLnZ n) (SLnZ n) (SLnZ n) ((diagCoset a).rep : GL (Fin n) ℚ)
      ((diagCoset b).rep : GL (Fin n) ℚ) ((diagCoset (a * b)).rep : GL (Fin n) ℚ) ≤ 1 := by
  classical
  rw [multiplicity_def, Nat.card_eq_fintype_card]
  refine Fintype.card_le_one_iff_subsingleton.mpr ⟨?_⟩
  obtain ⟨h₁, hh₁, h₂, hh₂, hδa⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul a
  obtain ⟨h₃, hh₃, h₄, hh₄, hδb⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul b
  obtain ⟨g₁, hg₁, g₂, hg₂, hδc⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul (a * b)
  set δa := ((diagCoset a).rep : GL (Fin n) ℚ)
  set δb := ((diagCoset b).rep : GL (Fin n) ℚ)
  set δc := ((diagCoset (a * b)).rep : GL (Fin n) ℚ)
  -- every pair in the fibre has first component conjugated into `SL_n(ℤ)` by `diag(a)`
  have key (i : DecompQuotient (SLnZ n) (SLnZ n) δa) (j : DecompQuotient (SLnZ n) (SLnZ n) δb)
      (hp : ((i.out : GL (Fin n) ℚ) * δa * ((j.out : GL (Fin n) ℚ) * δb) :
        GL (Fin n) ℚ ⧸ SLnZ n) = (δc : GL (Fin n) ℚ ⧸ SLnZ n)) :
      (natDiagGL n a)⁻¹ * (g₁⁻¹ * i.out * h₁) * natDiagGL n a ∈ SLnZ n := by
    rw [QuotientGroup.eq] at hp
    -- forget the coset representatives, on whose types `δa` and `δb` enter
    have hu : (i.out : GL (Fin n) ℚ) ∈ SLnZ n := i.out.2
    have hv : (j.out : GL (Fin n) ℚ) ∈ SLnZ n := j.out.2
    generalize (i.out : GL (Fin n) ℚ) = u at hp hu ⊢
    generalize (j.out : GL (Fin n) ℚ) = v at hp hv
    set κ := (u * δa * (v * δb))⁻¹ * δc
    refine natDiagGL_inv_mul_mul_mem_SLnZ_of_eq ha ha' hb hb'
      ((SLnZ n).mul_mem ((SLnZ n).mul_mem ((SLnZ n).inv_mem hg₁) hu) hh₁)
      ((SLnZ n).mul_mem ((SLnZ n).mul_mem hh₂ hv) hh₃)
      (γ := g₂ * κ⁻¹ * h₄⁻¹)
      ((SLnZ n).mul_mem ((SLnZ n).mul_mem hg₂ ((SLnZ n).inv_mem hp)) ((SLnZ n).inv_mem hh₄)) ?_
    have hκ : u * δa * (v * δb) = δc * κ⁻¹ := by simp [κ]
    rw [hδa, hδb, hδc] at hκ
    calc g₁⁻¹ * u * h₁ * natDiagGL n a * (h₂ * v * h₃) * natDiagGL n b
        = g₁⁻¹ * (u * (h₁ * natDiagGL n a * h₂) * (v * (h₃ * natDiagGL n b * h₄))) * h₄⁻¹ := by
          group
      _ = natDiagGL n (a * b) * (g₂ * κ⁻¹ * h₄⁻¹) := by rw [hκ]; group
  rintro ⟨⟨i₁, j₁⟩, hp₁⟩ ⟨⟨i₂, j₂⟩, hp₂⟩
  simp only [Set.mem_ofPred_eq] at hp₁ hp₂
  obtain rfl : i₁ = i₂ := by
    refine mk_out_mul_injective (SLnZ n) (SLnZ n) δa ?_
    rw [QuotientGroup.eq]
    have hmem := (SLnZ n).mul_mem ((SLnZ n).inv_mem hh₂)
      ((SLnZ n).mul_mem ((SLnZ n).mul_mem ((SLnZ n).inv_mem (key i₁ j₁ hp₁)) (key i₂ j₂ hp₂))
        hh₂)
    generalize (i₁.out : GL (Fin n) ℚ) = u₁ at hmem ⊢
    generalize (i₂.out : GL (Fin n) ℚ) = u₂ at hmem ⊢
    convert hmem using 1
    rw [hδa]
    group
  obtain rfl : j₁ = j₂ := snd_eq_of_fst_eq hp₁ hp₂
  rfl

/-- `T(a b)` occurs in `T(a) · T(b)`. -/
private lemma multiplicity_diagCoset_mul_ne_zero {a b : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) :
    multiplicity (SLnZ n) (SLnZ n) (SLnZ n) ((diagCoset a).rep : GL (Fin n) ℚ)
      ((diagCoset b).rep : GL (Fin n) ℚ) ((diagCoset (a * b)).rep : GL (Fin n) ℚ) ≠ 0 := by
  obtain ⟨h₁, hh₁, h₂, hh₂, hδa⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul a
  obtain ⟨h₃, hh₃, h₄, hh₄, hδb⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul b
  obtain ⟨g₁, hg₁, g₂, hg₂, hδc⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul (a * b)
  rw [multiplicity_ne_zero_iff, mem_doubleCoset]
  refine ⟨g₁ * h₁⁻¹ * (diagCoset a).rep * (h₂⁻¹ * h₃⁻¹), mem_doubleCoset.2
    ⟨g₁ * h₁⁻¹, (SLnZ n).mul_mem hg₁ ((SLnZ n).inv_mem hh₁), h₂⁻¹ * h₃⁻¹,
      (SLnZ n).mul_mem ((SLnZ n).inv_mem hh₂) ((SLnZ n).inv_mem hh₃), rfl⟩,
    h₄⁻¹ * g₂, (SLnZ n).mul_mem ((SLnZ n).inv_mem hh₄) hg₂, ?_⟩
  rw [hδc, hδa, hδb, ← natDiagGL_mul n a b ha hb]
  group

/-- **The leading coefficient of a product of diagonal double cosets.** For positive divisibility
chains `a` and `b`, the double coset `T(a b)` occurs in `T(a) · T(b)` with coefficient `1`. -/
theorem diagElem_mul_apply_diagCoset_mul {a b : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (ha' : IsDvdChain a) (hb : ∀ i, 0 < b i) (hb' : IsDvdChain b) :
    (diagElem a * diagElem b) (diagCoset (a * b)) = 1 := by
  rw [diagElem_def, diagElem_def, HeckeCosetModule.single_mul_single,
    HeckeCosetModule.smul_apply, HeckeCosetModule.smul_apply, one_mul, one_mul,
    HeckeCosetModule.structureConstants_apply, Nat.cast_eq_one]
  exact le_antisymm (multiplicity_diagCoset_mul_le_one ha ha' hb hb')
    (Nat.one_le_iff_ne_zero.2 (multiplicity_diagCoset_mul_ne_zero ha hb))

/-- **The leading term of a product of `p`-power diagonal cosets has coefficient one.** For
`0 < p` and monotone exponent vectors `e` and `f`, the coset `T(p ^ (e + f))` occurs in
`T(p ^ e) · T(p ^ f)` with coefficient `1`. -/
theorem diagElem_primePowDiag_mul_apply_diagCoset_add {p : ℕ} (hp : 0 < p) {e f : Fin n → ℕ}
    (he : Monotone e) (hf : Monotone f) :
    (diagElem (primePowDiag n p e) * diagElem (primePowDiag n p f))
      (diagCoset (primePowDiag n p (e + f))) = 1 := by
  rw [primePowDiag_add]
  exact diagElem_mul_apply_diagCoset_mul (primePowDiag_pos n p hp e)
    (isDvdChain_primePowDiag n p e he) (primePowDiag_pos n p hp f)
    (isDvdChain_primePowDiag n p f hf)

end HeckeRing.GLn
