/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Commutativity
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Coset
import TauCeti.Data.ZMod.Units

/-!
# Anti-involutions of Hecke pairs over `Δ₀(N)`

Shimura's commutativity criterion (Proposition 3.8) asks an anti-involution of a Hecke pair to
fix every double coset. For a pair `(Δ₀(N), H)`, with `H` any subgroup of `GL₂(ℚ)`, this file
reduces that to the elements of `Δ₀(N)` with a primitive integral witness, one no prime divides
entrywise, provided the anti-involution fixes the scalars `diag(d, d)`.

Dividing an integral witness by the gcd `d` of its four entries leaves a primitive one, and `d`
is positive and coprime to the level, so `diag(d, d)` lies in `Δ₀(N)`. That scalar is central,
and a central element fixed by the anti-involution splits off a double coset
(`HeckeAntiInvolution.bar_mem_doubleCoset_self_mul_of_mem_centralizer`). The subgroup `H` plays
no part, so the reduction serves the Atkin-Lehner anti-involutions at the levels `Γ₀(N)` and
`Γ₁(N)` alike.

## Main results

* `HeckeRing.GL2.bar_mem_doubleCoset_of_forall_primitive`: an anti-involution of a Hecke pair
  `(Δ₀(N), H)` fixing the scalars fixes every double coset once it fixes those of primitive
  witnesses.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.
* The reduction generalises the scalar step of the AINTLIB `LeanModularForms` project
  (Chris Birkbeck),
  [`HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`](https://github.com/CBirkbeck/AINTLIB),
  declarations `Gamma0_AL_in_DC_of_smul` and `Gamma0_AL_in_doubleCoset`, Apache-2.0 at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, from the level `Γ₀(N)` to an arbitrary subgroup.
-/

public section

open Matrix HeckeRing.GLn

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **The primitive case suffices.** An anti-involution `ι` of a Hecke pair `(Δ₀(N), H)` that
fixes the scalars `diag(d, d)` fixes the `H`-double coset of every `x ∈ Δ₀(N)`, as soon as it
fixes those of the elements of `Δ₀(N)` with an integral witness no prime divides entrywise.

Dividing an integral witness of `x` by the gcd `d` of its four entries leaves a primitive one
(`exists_primitive_content_quotient`), and `d` is positive and coprime to the level. The scalar
`diag(d, d)` is central, so it splits off by
`HeckeAntiInvolution.bar_mem_doubleCoset_self_mul_of_mem_centralizer`. Nothing is asked of
`H`, so the same reduction serves the levels `Γ₀(N)` and `Γ₁(N)`. -/
theorem bar_mem_doubleCoset_of_forall_primitive {H : Subgroup (GL (Fin 2) ℚ)}
    (ι : HeckeAntiInvolution (Delta0 N) H)
    (hscalar : ∀ d : ℕ, 0 < d → ∀ hs : natDiagGL 2 (fun _ ↦ d) ∈ Delta0 N,
      ι.bar _ hs = natDiagGL 2 (fun _ ↦ d))
    (hprim : ∀ (x₀ : GL (Fin 2) ℚ) (hx₀ : x₀ ∈ Delta0 N) (A : Matrix (Fin 2) (Fin 2) ℤ),
      (x₀ : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
      (∀ p : ℕ, p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧ (p : ℤ) ∣ A 1 0 ∧
        (p : ℤ) ∣ A 1 1)) →
      ι.bar x₀ hx₀ ∈ DoubleCoset.doubleCoset x₀ H H)
    (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) :
    ι.bar x hx ∈ DoubleCoset.doubleCoset x H H := by
  obtain ⟨A, hA, hxdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hx
  have hAco : Int.gcd (A 0 0) N = 1 := Int.isUnit_intCast_iff_gcd_eq_one.mp hAunit
  have hA_det_pos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]
    exact hxdet
  -- divide the witness by the gcd `d` of its four entries
  set d : ℕ := Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
    (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) with hd_def
  obtain ⟨A₀, hA₀_eq, hA₀_det_pos, hA₀N, hA₀co, hA₀_prim⟩ :=
    exists_primitive_content_quotient N A hA_det_pos hAN hAco d hd_def
  have hd : 0 < d := Nat.pos_of_ne_zero fun h ↦ by
    have hA0 : A = 0 := Matrix.ext fun i j ↦ by simpa [h] using hA₀_eq i j
    simp [hA0] at hA_det_pos
  have hdN : Nat.Coprime d N :=
    Nat.Coprime.coprime_dvd_left ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)) hAco
  have hA₀_det_ne : (A₀.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hA₀_det_pos.ne'
  set x₀ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA₀_det_ne
  have hx₀_val : (x₀ : Matrix (Fin 2) (Fin 2) ℚ) = A₀.map (Int.cast : ℤ → ℚ) := by simp [x₀]
  have hx₀ : x₀ ∈ Delta0 N := (mem_Delta0_iff N).mpr ⟨A₀, hx₀_val,
    by rw [hx₀_val, ← Int.cast_det]; exact_mod_cast hA₀_det_pos, hA₀N,
    Int.isUnit_intCast_iff_gcd_eq_one.mpr hA₀co⟩
  -- the scalar `d` lies in `Δ₀(N)` and is central
  let s : GL (Fin 2) ℚ := natDiagGL 2 (fun _ ↦ d)
  have hs : s ∈ Delta0 N := natDiagGL_mem_Delta0_of_coprime N _ fun _ ↦ hdN
  have hs_wit : (s : Matrix (Fin 2) (Fin 2) ℚ) =
      (Matrix.diagonal (fun _ ↦ (d : ℤ))).map (Int.cast : ℤ → ℚ) :=
    natDiagGL_coe_eq_map_intCast 2 _ fun _ ↦ hd
  have hs_central : s ∈ Subgroup.center (GL (Fin 2) ℚ) :=
    Subgroup.mem_center_iff.mpr fun g ↦ (natDiagGL_const_comm 2 d g).symm
  have hxeq : x = s * x₀ := by
    apply Units.ext
    rw [Units.val_mul, hA, hs_wit, hx₀_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal, hA₀_eq]
  subst hxeq
  exact ι.bar_mem_doubleCoset_self_mul_of_mem_centralizer hs hx₀
    (Subgroup.center_le_centralizer _ hs_central) (hscalar d hd hs)
    (hprim x₀ hx₀ A₀ hx₀_val hA₀_prim)

end HeckeRing.GL2
