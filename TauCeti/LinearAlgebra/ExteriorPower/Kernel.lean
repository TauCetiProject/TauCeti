/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The kernel of the exterior-square action

An automorphism of a finite free module of rank at least three acts trivially on its exterior
square exactly when it is scalar multiplication by a scalar whose square is one. This holds
over any commutative ring, including in characteristic two. Over a domain the scalars are `±1`.
The rank restriction is essential: in rank two the exterior square detects only the determinant.

This criterion identifies the kernel of the exterior-square realization of the six-dimensional
orthogonal representation of the four-dimensional special linear group.
-/

public section

open exteriorPower

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- In rank at least three, an automorphism acts trivially on the exterior square exactly when
it is scalar multiplication by a scalar whose square is one. -/
theorem Module.Basis.exteriorPower_map_eq_id_iff [Fintype ι] (b : Module.Basis ι R M)
    (hι : 3 ≤ Fintype.card ι) (f : M ≃ₗ[R] M) :
    exteriorPower.map 2 f.toLinearMap = LinearMap.id ↔
      ∃ c : R, c ^ 2 = 1 ∧ f.toLinearMap = c • LinearMap.id := by
  classical
  have hthird (i j : ι) : ∃ k : ι, k ≠ i ∧ k ≠ j := by
    have hcard : ({i, j} : Finset ι).card < (Finset.univ : Finset ι).card := by
      have := Finset.card_insert_le i ({j} : Finset ι)
      simp only [Finset.card_singleton, Finset.card_univ] at *
      omega
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨k, by simpa using hk⟩
  constructor
  · intro hf
    -- Move one factor through the inverse. Pairing with two coordinate functionals then
    -- recovers individual matrix entries, rather than quadratic minors of the matrix.
    have hwed (x y : M) :
        ιMulti R 2 ![f x, y] = ιMulti R 2 ![x, f.symm y] := by
      have h := LinearMap.congr_fun hf (ιMulti R 2 ![x, f.symm y])
      have hv : f ∘ ![x, f.symm y] = ![f x, y] := by
        ext i
        fin_cases i <;> simp
      simpa only [map_apply_ιMulti, LinearEquiv.coe_coe, hv, LinearMap.id_apply] using h
    have hcoeff (i j k l : ι) :
        b.coord k (f (b i)) * b.coord l (b j) -
            b.coord l (f (b i)) * b.coord k (b j) =
          b.coord k (b i) * b.coord l (f.symm (b j)) -
            b.coord l (b i) * b.coord k (f.symm (b j)) := by
      have h := congrArg (pairingDual R M 2 (ιMulti R 2 ![b.coord k, b.coord l]))
        (hwed (b i) (b j))
      simpa [pairingDual_ιMulti_ιMulti, Matrix.det_fin_two] using h
    have hoff (i k : ι) (hik : i ≠ k) : b.coord k (f (b i)) = 0 := by
      obtain ⟨j, hji, hjk⟩ := hthird i k
      simpa [Module.Basis.coord_apply, hik, hik.symm, hji, hji.symm, hjk, hjk.symm]
        using hcoeff i j k j
    have hdiag (i j : ι) (hij : i ≠ j) :
        b.coord i (f (b i)) = b.coord j (f.symm (b j)) := by
      simpa [Module.Basis.coord_apply, hij, hij.symm] using hcoeff i j i j
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    let c := b.coord i₀ (f (b i₀))
    have hsame (i : ι) : b.coord i (f (b i)) = c := by
      obtain ⟨j, hji, hji₀⟩ := hthird i i₀
      exact (hdiag i j hji.symm).trans (hdiag i₀ j hji₀.symm).symm
    have hscalar : f.toLinearMap = c • LinearMap.id := by
      apply b.ext
      intro i
      apply b.repr.injective
      ext k
      by_cases hik : i = k
      · subst k
        simpa [Module.Basis.coord_apply] using hsame i
      · simp [← Module.Basis.coord_apply, hoff i k hik, Ne.symm hik]
    have hsq : c ^ 2 = 1 := by
      obtain ⟨j, hji, -⟩ := hthird i₀ i₀
      have h := LinearMap.congr_fun hf (ιMulti R 2 ![b i₀, b j])
      rw [hscalar] at h
      have hp := congrArg
        (pairingDual R M 2 (ιMulti R 2 ![b.coord i₀, b.coord j])) h
      simpa [map_apply_ιMulti, pairingDual_ιMulti_ιMulti, Matrix.det_fin_two,
        Function.comp_def, Module.Basis.coord_apply, hji, hji.symm, pow_two] using hp
    exact ⟨c, hsq, hscalar⟩
  · rintro ⟨c, hc, hf⟩
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, map_apply_ιMulti, hf,
      LinearMap.smul_apply, LinearMap.id_apply, Function.comp_def]
    rw [(ιMulti R 2).map_smul_univ (fun _ ↦ c) v]
    simp [hc]

/-- Over a domain, the kernel of the exterior-square action in rank at least three consists of
the two scalar automorphisms `±1`. In characteristic two these coincide. -/
theorem Module.Basis.exteriorPower_map_eq_id_iff_eq_or_eq_neg_id [Fintype ι]
    [IsDomain R] (b : Module.Basis ι R M) (hι : 3 ≤ Fintype.card ι) (f : M ≃ₗ[R] M) :
    exteriorPower.map 2 f.toLinearMap = LinearMap.id ↔
      f.toLinearMap = LinearMap.id ∨ f.toLinearMap = -LinearMap.id := by
  rw [b.exteriorPower_map_eq_id_iff hι f]
  constructor
  · rintro ⟨c, hc, hf⟩
    rcases sq_eq_one_iff.mp hc with rfl | rfl <;> simp_all
  · rintro (hf | hf)
    · exact ⟨1, by simp, by simpa using hf⟩
    · exact ⟨-1, by simp, by simpa using hf⟩
