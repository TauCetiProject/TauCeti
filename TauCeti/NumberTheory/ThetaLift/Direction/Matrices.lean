/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.Direction.Congruences

/-!
# Simultaneous changes of theta directions

`TauCeti.exists_direction_matrices_of_frobenius_pairings` imposes all the paired congruences
on one family of changes of directions. It intersects the coefficient submodules from
`TauCeti.exists_colengthDvd_frobenius_pairing` before extracting matrices and expressing their
determinant bound as divisibility. The theta-jet substitution uses the same matrices for
every prescribed exponent. Its valuation loss is controlled by the determinant product, which
has one factor per column of the corresponding height.

The construction follows `New.exists_newDirection_dvd` in
`grh/src/New/Derivatives/Divisibility/NullFrames.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC)
at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset Matrix

namespace TauCeti

/-- For finitely many Frobenius exponents and a partner rule on finitely many places, one
matrix per place and height suffices to make all nonexempt pairings divisible by `π`.
Here `none` indexes height one and `a` gives column multiplicities. A pairing is exempt if
its source block is `none` and either its source is marked or its partner block is `none`
at a marked place. The modulus `π` divides `p`, each `d i` is a `p ^ e i`-th root of `π`,
and each coordinate of the partner's distinguished direction `Y (partner i t) none 1`
admits a `p ^ e i`-th root. The weighted product of matrix determinants divides the product
of the local congruence costs expressed in the modulus roots. -/
theorem exists_direction_matrices_of_frobenius_pairings
    {R ι n τ I : Type*} [CommRing R] [PreValuationRing R]
    [Fintype ι] [Fintype n] [Fintype τ] [Fintype I] {height : ι → ℕ}
    {p : ℕ} (hp : p.Prime) {π : R} (hπ : π ∣ (p : R))
    (e : I → ℕ) (partner : I → τ → τ) (mark : τ → Bool)
    (a : τ → Option ι → ℕ)
    (Y : ∀ (_ : τ) (h : Option ι), (Fin (h.elim 1 height) → R) →ₗ[R] (n → R))
    (d : I → R) (hd : ∀ i, d i ^ (p ^ e i) = π)
    (hroot : ∀ i t j, ∃ x : R, x ^ (p ^ e i) = Y (partner i t) none 1 j) :
    ∃ g : ∀ (_ : τ) (h : Option ι), Matrix (Fin (h.elim 1 height)) (Fin (h.elim 1 height)) R,
      (∀ i t h j, ¬(h = none ∧ (mark t = true ∨ j = none ∧ mark (partner i t) = true)) →
        ∀ k k', π ∣ (fun u ↦ (Y t h (g t h k) u) ^ (p ^ e i)) ⬝ᵥ
          Y (partner i t) j (g (partner i t) j k')) ∧
      (∏ t, ∏ h, (g t h).det ^ a t h) ∣
        ∏ i, ∏ t, d i ^
          (min (if mark t then 0 else a t none)
            (p ^ e i * ((∑ h, a (partner i t) (some h)) +
              if mark (partner i t) then 0 else a (partner i t) none)) +
            (∑ h, a t (some h)) +
            min (∑ h, a t (some h) * height h)
              (p ^ e i * (∑ h, a (partner i t) (some h) * height h))) := by
  classical
  choose root hroot using hroot
  have hlocal (i : I) (t : τ) := exists_colengthDvd_frobenius_pairing (e := e i) (d := d i) hp
    ((hd i).symm ▸ hπ) (Y t) (Y (partner i t)) (root i t)
    (hroot i t) (a t) (a (partner i t)) (mark t) (mark (partner i t))
  choose L M l r hL hM hcost hpair using hlocal
  let A (t : τ) (h : Option ι) (i : I) (u : τ) : Submodule R (Fin (h.elim 1 height) → R) :=
    (if t = u then L i u h else ⊤) ⊓ (if t = partner i u then M i u h else ⊤)
  let B (t : τ) (h : Option ι) (i : I) (u : τ) : R :=
    (if t = u then d i ^ l i u h else 1) *
      (if t = partner i u then (d i ^ (p ^ e i)) ^ r i u h else 1)
  have hA (t h i u) : (⊤ : Submodule R _).ColengthDvd (A t h i u) (B t h i u) := by
    dsimp only [A, B]
    apply Submodule.ColengthDvd.inf
    · split_ifs <;> first | exact hL i u h | exact Submodule.colengthDvd_self _ _
    · split_ifs <;> first | exact hM i u h | exact Submodule.colengthDvd_self _ _
  have hmatrix (t h) := (Submodule.ColengthDvd.iInf fun i ↦
    Submodule.ColengthDvd.iInf (hA t h i)).exists_matrix_row_mem
  choose g hg hrow using hmatrix
  refine ⟨g, ?_, ?_⟩
  · intro i t h j hj k k'
    have hmem (v) (b) (k) : g v b k ∈ A v b i t :=
      (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp (hrow v b k) i) t
    rw [← hd i]
    refine hpair i t h j hj _ ?_ _ ?_
    · simpa only [A, ite_true] using (Submodule.mem_inf.mp (hmem t h k)).1
    · simpa only [A, ite_true] using (Submodule.mem_inf.mp (hmem (partner i t) j k')).2
  refine (Finset.prod_dvd_prod_of_dvd _ _ fun t _ ↦ Finset.prod_dvd_prod_of_dvd _ _
    fun h _ ↦ pow_dvd_pow_of_dvd (hg t h) _).trans ?_
  suffices heq : (∏ t, ∏ h, (∏ i, ∏ u, B t h i u) ^ a t h) = _ by rw [heq]
  simp_rw [← Finset.prod_pow]
  calc
    _ = ∏ i, ∏ u, ∏ t, ∏ h, B t h i u ^ a t h := by
      simpa only [← Finset.univ_product_univ, Finset.prod_product] using
        (Finset.prod_comm (s := (Finset.univ : Finset (τ × Option ι)))
          (t := (Finset.univ : Finset (I × τ)))
          (f := fun th iu ↦ B th.1 th.2 iu.1 iu.2 ^ a th.1 th.2))
    _ = _ := by
      refine Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl fun u _ ↦ ?_
      rw [← hcost i u]
      rw [Finset.prod_comm]
      -- Separate the factors at the source and the partner, including for a self-pairing.
      simp_rw [B, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow, Fintype.prod_ite_eq']
      simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum, ← pow_add]
      congr 1
      rw [Finset.mul_sum]
      grind

end TauCeti
