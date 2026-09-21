/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperTriFactorization
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperUnit
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeCosets

-- Only a proof needs the field structure on `ZMod p` (to read `p ∤ a` as invertibility).
import Mathlib.Algebra.Field.ZMod

/-!
# The double coset `Γ₀(N) · diag(1, p) · Γ₀(N)` at a prime

The right-coset decomposition of the `Γ₀(N)` double coset of `diag(1, p)`, the `Γ₀(N)`
counterpart of `Gamma1/CoprimeCosets.lean` and `Gamma1/UpperTriCosets.lean`. At `p ∤ N` the
representatives are the same `p + 1` matrices as over `Γ₁(N)` — `!![1, j; 0, p]` for `j < p` and
the twisted diagonal `σ · diag(p, 1)`, `primeRep σ p` — and at `p ∣ N` the `p` upper-triangular
ones. Injectivity of the representatives and the membership of the twisted one come from the
`Γ₁(N)` files, since `Γ₁(N) ≤ Γ₀(N)`; what is new is the covering step over `Γ₀(N)`, whose
elements need not have `a ≡ 1 (mod N)`.

## The covering step

For `γ = [a, b; c, d] ∈ Γ₀(N)`: if `p ∤ a`, the upper-triangular factorisation
`exists_mem_Gamma0_upperTriRep_mul_of_isUnit` at offset `0` writes `diag(1, p) · γ` as an element
of `Γ₀(N)` times `!![1, j; 0, p]`; if `p ∣ a`, then
`diag(1, p) · γ = [a / p, b; c, p d] · diag(p, 1)` with the first factor in `Γ₀(N)`, which is the
coset of `σ · diag(p, 1)` because `σ ∈ Γ₀(N)`.

## Main results

* `HeckeRing.GL2.doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_prime`: at a prime
  `p ∤ N`, the union of the `p + 1` right cosets named by `primeRep σ p`.
* `HeckeRing.GL2.doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_dvd`: at a prime
  `p ∣ N`, the union of the `p` upper-triangular right cosets. Read at the chosen representative
  of `diagCosetGamma0 N ![1, p]` through `HeckeCoset.toSet_eq_doubleCoset_rep` and
  `diagCosetGamma0_toSet`, these are the shapes the twisted slash-sum machinery of
  `HeckeSlash/Nebentypus/Independence.lean` consumes.
* `HeckeRing.GL2.Delta0UpperUnit_upperTriRep`, `HeckeRing.GL2.Delta0UpperUnit_mapGL_mul_scaleRep`:
  the upper-left unit of either kind of representative is `1`, so the twisting character of
  `HeckeSlash/Nebentypus/*` is trivial on both.

## Provenance

The coset bookkeeping behind `heckeRingHomCharSpace_D_p_eq_scalar_charRestrict` of the AINTLIB
`LeanModularForms` project (`LeanModularForms/HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean`,
Chris Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), reorganised around
this repository's `primeRep` and `doubleCoset_eq_iUnion_rightCosets_of_forall_exists`.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable {N p : ℕ} {σ : SL(2, ℤ)}

/-- When `p` divides the upper-left entry of `γ ∈ Γ₀(N)`, `diag(1, p) · γ` factors through the
scaling representative: `diag(1, p) · !![a, b; c, d] = !![a / p, b; c, p d] · diag(p, 1)`, and the
first factor lies in `Γ₀(N)`. -/
lemma exists_mem_Gamma0_natDiagGL_mul_eq_mul_scaleRep_of_dvd (hp : 0 < p) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) (hpa : (p : ℤ) ∣ γ 0 0) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ natDiagGL 2 ![1, p] * mapGL ℚ γ = mapGL ℚ δ * scaleRep p := by
  obtain ⟨a', ha'⟩ := hpa
  have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  let δ : SL(2, ℤ) := ⟨!![a', γ 0 1; γ 1 0, (p : ℤ) * γ 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet - γ 1 1 * ha'⟩
  have h00 : (δ 0 0 : ℤ) = a' := rfl
  have h01 : (δ 0 1 : ℤ) = γ 0 1 := rfl
  have h10 : (δ 1 0 : ℤ) = γ 1 0 := rfl
  have h11 : (δ 1 1 : ℤ) = (p : ℤ) * γ 1 1 := rfl
  refine ⟨δ, Gamma0_mem.mpr (by rw [h10]; exact Gamma0_mem.mp hγ), ?_⟩
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_natDiagGL_one hp, coe_mapGL_int_rat_fin_two γ,
    coe_mapGL_int_rat_fin_two δ, coe_scaleRep p hp, h00, h01, h10, h11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha', mul_comm]

/-- **Every `diag(1, p) · γ` with `γ ∈ Γ₀(N)` lies in a right coset named by `primeRep σ p`**: at
`p ∤ a` the upper-triangular factorisation `exists_mem_Gamma0_upperTriRep_mul_of_isUnit` at offset
`0` lands on `!![1, j; 0, p]`; at `p ∣ a` the scaling factorisation lands on `σ · diag(p, 1)`
after absorbing `σ⁻¹ ∈ Γ₀(N)`. -/
lemma exists_mem_Gamma0_natDiagGL_mul_primeRep (hp : p.Prime) (hσ10 : σ 1 0 = (N : ℤ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ (i : Option (Fin p)) (δ : SL(2, ℤ)), δ ∈ Gamma0 N ∧
      natDiagGL 2 ![1, p] * mapGL ℚ γ = mapGL ℚ δ * primeRep σ p i := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpa : (p : ℤ) ∣ γ 0 0
  · obtain ⟨δ, hδ, heq⟩ := exists_mem_Gamma0_natDiagGL_mul_eq_mul_scaleRep_of_dvd hp.pos hγ hpa
    have hσ : σ ∈ Gamma0 N := Gamma0_mem.mpr (by rw [hσ10]; exact_mod_cast ZMod.natCast_self N)
    refine ⟨none, δ * σ⁻¹, Subgroup.mul_mem _ hδ (Subgroup.inv_mem _ hσ), ?_⟩
    rw [primeRep_none, heq, map_mul, map_inv, mul_assoc, ← mul_assoc (mapGL ℚ σ)⁻¹,
      inv_mul_cancel, one_mul]
  · have hA : IsUnit (((γ 0 0 + ((⟨0, hp.pos⟩ : Fin p) : ℕ) * γ 1 0 : ℤ) : ZMod p)) := by
      have h0 : ((γ 0 0 + ((⟨0, hp.pos⟩ : Fin p) : ℕ) * γ 1 0 : ℤ) : ZMod p)
          = ((γ 0 0 : ℤ) : ZMod p) := by
        push_cast
        simp
      rw [h0]
      refine (isUnit_iff_ne_zero (G₀ := ZMod p)).mpr ?_
      intro h
      exact hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    have hpc : (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0 := by
      push_cast
      rw [Gamma0_mem.mp hγ, mul_zero]
    obtain ⟨δ, hδ, -, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit hA hpc
    refine ⟨some (upperTriShift p γ ⟨0, hp.pos⟩), δ, hδ, ?_⟩
    rw [primeRep_some, ← hmul, ← natDiagGL_mul_mapGL_T_zpow hp.pos ⟨0, hp.pos⟩]
    simp

/-- **The `Γ₀(N)` double coset of `diag(1, p)` at a prime `p ∤ N` is the union of `p + 1` right
cosets**, named by the same representatives `primeRep σ p` as over `Γ₁(N)`: `p ∤ N` is carried by
the twist `σ` with bottom row `(N, p)`. -/
theorem doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_prime (hp : p.Prime)
    (hσ10 : σ 1 0 = (N : ℤ)) (hσ11 : σ 1 1 = (p : ℤ)) :
    doubleCoset (natDiagGL 2 ![1, p]) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) =
      ⋃ i : Option (Fin p), MulOpposite.op (primeRep σ p i) •
        ((Gamma0 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  apply doubleCoset_eq_iUnion_rightCosets_of_forall_exists
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      (natDiagGL 2 ![1, p]) (primeRep σ p)
  · intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨i, δ, hδ, heq⟩ := exists_mem_Gamma0_natDiagGL_mul_primeRep hp hσ10 hγ
    exact ⟨i, mapGL ℚ δ, Subgroup.mem_map_of_mem _ hδ, heq⟩
  · intro i
    cases i with
    | none =>
      obtain ⟨γ, hγ, heq⟩ := exists_mem_Gamma1_natDiagGL_mul_eq_primeRep_none hp.pos hσ10 hσ11
      exact ⟨mapGL ℚ γ, Subgroup.mem_map_of_mem _ (Gamma1_in_Gamma0 N hγ), heq⟩
    | some b =>
      exact ⟨mapGL ℚ (ModularGroup.T ^ (b : ℤ)),
        Subgroup.mem_map_of_mem _ (Gamma1_in_Gamma0 N (T_zpow_mem_Gamma1 N _)), by
        rw [primeRep_some, natDiagGL_mul_mapGL_T_zpow hp.pos b]⟩

/-- **At a prime dividing the level, the `Γ₀(N)` double coset of `diag(1, p)` is the union of the
`p` upper-triangular right cosets**: the factorisation
`exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0` never leaves the family. -/
theorem doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_dvd (hp : p.Prime) (hpN : p ∣ N) :
    doubleCoset (natDiagGL 2 ![1, p]) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) =
      ⋃ j : Fin p, MulOpposite.op (upperTriRep p j) •
        ((Gamma0 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  apply doubleCoset_eq_iUnion_rightCosets_of_forall_exists
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      (natDiagGL 2 ![1, p]) (upperTriRep p)
  · intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨δ, hδ, -, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0 hpN hγ ⟨0, hp.pos⟩
    refine ⟨upperTriShift p γ ⟨0, hp.pos⟩, mapGL ℚ δ, Subgroup.mem_map_of_mem _ hδ, ?_⟩
    rw [← hmul, ← natDiagGL_mul_mapGL_T_zpow hp.pos ⟨0, hp.pos⟩]
    simp
  · intro j
    exact ⟨mapGL ℚ (ModularGroup.T ^ (j : ℤ)),
      Subgroup.mem_map_of_mem _ (Gamma1_in_Gamma0 N (T_zpow_mem_Gamma1 N _)),
      natDiagGL_mul_mapGL_T_zpow hp.pos j⟩

/-! ### The upper-left units of the representatives -/

/-- **The upper-left unit of an upper-triangular representative is `1`.** -/
@[simp] theorem Delta0UpperUnit_upperTriRep (j : Fin p)
    (hmem : upperTriRep p j ∈ Delta0 N) : Delta0UpperUnit N ⟨upperTriRep p j, hmem⟩ = 1 := by
  have h : (Delta0UpperUnit N ⟨upperTriRep p j, hmem⟩ : ZMod N)
      = ((!![1, (j : ℕ); 0, (p : ℕ)] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) := by
    refine Delta0UpperUnit_apply_val N ?_
    -- The witness equation is stated for the `GL₂(ℚ)` matrix underlying the `Δ₀(N)` element;
    -- that element is the subtype `⟨upperTriRep p j, hmem⟩`, whose coercion to `GL₂(ℚ)` is
    -- `upperTriRep p j` by definition, which is what `change` exposes.
    change ((upperTriRep p j : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
    rw [coe_upperTriRep]
    ext i l
    fin_cases i <;> fin_cases l <;> simp
  exact Units.ext (by simpa using h)

/-- **The upper-left unit of the twisted representative `σ · diag(p, 1)` is `1`**: its upper-left
entry is `σ₀₀ p ≡ 1 (mod N)`, by the determinant of `σ`. -/
@[simp] theorem Delta0UpperUnit_mapGL_mul_scaleRep (hp : 0 < p) (hσ10 : σ 1 0 = (N : ℤ))
    (hσ11 : σ 1 1 = (p : ℤ)) (hmem : mapGL ℚ σ * scaleRep p ∈ Delta0 N) :
    Delta0UpperUnit N ⟨mapGL ℚ σ * scaleRep p, hmem⟩ = 1 := by
  have h : (Delta0UpperUnit N ⟨mapGL ℚ σ * scaleRep p, hmem⟩ : ZMod N)
      = ((!![σ 0 0 * (p : ℤ), σ 0 1; σ 1 0 * (p : ℤ), σ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0
          : ZMod N) := by
    refine Delta0UpperUnit_apply_val N ?_
    -- As above: the `Δ₀(N)` element is the subtype `⟨mapGL ℚ σ * scaleRep p, hmem⟩`, and its
    -- underlying `GL₂(ℚ)` matrix is the product, which `change` exposes.
    change ((mapGL ℚ σ * scaleRep p : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
    rw [Units.val_mul, coe_mapGL_int_rat_fin_two, coe_scaleRep p hp]
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : ((σ 0 0 * (p : ℤ) : ℤ) : ZMod N) = 1 := by
    have : σ 0 0 * (p : ℤ) = 1 + σ 0 1 * (N : ℤ) := by
      linear_combination mul_sub_mul_eq_one_of_lowerRow hσ10 hσ11
    rw [this]
    push_cast
    simp
  exact Units.ext (by simpa [h1] using h)

end HeckeRing.GL2
