/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.Algebra.Group.Primary.Generators
import TauCeti.Algebra.Module.SpanRank
import TauCeti.Data.Fintype.Fiber
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Generators
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Padic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.Basic

/-!
# Odd-prime classification of integral localizations by the discriminant form

Let `L` and `M` be nondegenerate integral lattices and let `p` be an odd prime. Over `ℤ_p`, the
localization `L_p = ℤ_p ⊗[ℤ] L` has a diagonal Jordan form `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` with `uᵢ ∈ ℤ_pˣ`
(`TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow`), and its
`p`-primary discriminant bilinear module `(A_L)_p` is isometric to the orthogonal sum of Nikulin's
odd cyclic generators `q_{θᵢ}^{(p)}(pᵏⁱ)` for integer lifts `θᵢ ≡ uᵢ (mod p^{max(kᵢ, 1)})`
(`TauCeti.IntegralLattice.nonempty_isometry_pi_oddCyclic_primaryComponent`).

For every positive scale `m ≥ 1`, the isometry class of `(A_L)_p` determines both the rank
`#{i | kᵢ = m}` and the Legendre symbol product `∏_{kᵢ = m} (θᵢ / p)` of the `p^m`-modular Jordan
constituent (`TauCeti.FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff`), hence the unit
square class `∏_{kᵢ = m} uᵢ` over `ℤ_p`. Only the unimodular constituent `m = 0` is invisible to
`(A_L)_p`: its rank is recovered from `rank L` by subtracting the positive-scale counts, and its
unit determinant square class is recovered from the `p`-adic square class of `det L` once the
positive-scale contributions are divided out. Applying the Henselian unit-diagonal classification on
each scale fiber constructs an integral `ℤ_p`-isometry `L_p ≃ M_p`.

Two consequences follow directly from the same diagonal analysis:

* The least number of generators of `(A_L)_p` equals `#{i | kᵢ ≠ 0}`: each nontrivial cyclic
  summand `ℤ/pᵏⁱ` contributes one generator modulo `p`, while `kᵢ = 0` contributes none.
* When `rank L` and `rank M` attain this lower bound `ℓ((A_L)_p)` and `ℓ((A_M)_p)`, neither
  localization has a unimodular constituent `kᵢ = 0`, so an isometry `(A_L)_p ≅ (A_M)_p` determines
  `L_p ≃ M_p` without any determinant or rank hypothesis. This is the uniqueness clause of
  Nikulin's Theorem 1.9.1 at odd primes.

At odd order, a bilinear isometry between finite quadratic modules automatically preserves the
quadratic refinement
(`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`), so the odd-prime
classification takes the same form for arbitrary nondegenerate lattices via `b_L` and for even
nondegenerate lattices via `q_L`.

## Main results

* `TauCeti.IntegralLattice.spanFinrank_primaryComponent_discriminantGroup_le_finrank`: for any
  prime `p`, `ℓ((A_L)_p) ≤ rank L`.
* `TauCeti.IntegralLattice.spanFinrank_primaryComponent_discriminantGroup_eq_card_filter`: at an
  odd prime `p`, `ℓ((A_L)_p) = #{i | kᵢ ≠ 0}` in any diagonal Jordan form `B(bᵢ, bᵢ) = uᵢ pᵏⁱ`.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_discriminantBilinear` and
  `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_exists_unit_sq_and_discriminantBilinear`
  classify `L_p ≃ M_p` at an odd prime `p` by `rank L = rank M`, `det L · det M` being a square in
  `ℤ_p` (equivalently `det L = u² det M` for `u ∈ ℤ_pˣ`), and `(A_L)_p ≅ (A_M)_p`.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_discriminantQuadratic`: the even-lattice
  counterpart in terms of the `p`-primary discriminant quadratic modules.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_of_finrank_eq_spanFinrank` and
  `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_of_isEven_of_finrank_eq_spanFinrank`:
  minimal-rank `p`-adic localizations (`rank L = ℓ((A_L)_p)`) are isometric if and only if their
  `p`-primary discriminant forms are isometric.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Theorem 1.9.1
  and Corollaries 1.9.4 and 1.16.3.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C and 92:1--92:2.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module Finset AddCommGroup

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ### Generator count of a `p`-primary discriminant component -/

/-- For every prime `p`, the `p`-primary component of the discriminant group of a nondegenerate
integral lattice needs at most `rank L` generators. -/
theorem spanFinrank_primaryComponent_discriminantGroup_le_finrank
    (L : IntegralLattice V) [L.IsNondegenerate] (p : ℕ) [Fact p.Prime] :
    (⊤ : Submodule ℤ (primaryComponent L.DiscriminantGroup p)).spanFinrank ≤ finrank ℤ L := by
  classical
  have hp : p.Prime := Fact.out
  by_cases hmem : p ∈ (Nat.card L.DiscriminantGroup).primeFactors
  · refine (Finset.le_sup (f := fun q : (Nat.card L.DiscriminantGroup).primeFactors ↦
      (⊤ : Submodule ℤ (primaryComponent L.DiscriminantGroup q.1)).spanFinrank)
      (Finset.mem_univ (⟨p, hmem⟩ : (Nat.card L.DiscriminantGroup).primeFactors))).trans ?_
    rw [← TauCeti.AddCommGroup.spanFinrank_eq_sup_primaryComponents]
    exact L.spanFinrank_discriminantGroup_le_finrank
  · have hfact : (Nat.card L.DiscriminantGroup).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hdvd ↦
        hmem (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
    have hcard : Nat.card (primaryComponent L.DiscriminantGroup p) = 1 := by
      rw [TauCeti.AddCommGroup.natCard_primaryComponent _ hp, hfact, pow_zero]
    have : Subsingleton (primaryComponent L.DiscriminantGroup p) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    rw [Subsingleton.elim (⊤ : Submodule ℤ (primaryComponent L.DiscriminantGroup p)) ⊥,
      Submodule.spanFinrank_bot]
    exact Nat.zero_le _

/-- The generator number of a finite product `∏ᵢ ℤ/pᵏⁱ` over `ℤ` is the number of nonzero
exponents `kᵢ ≠ 0`. -/
private theorem spanFinrank_pi_zmod_pow {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (k : ι → ℕ) :
    (⊤ : Submodule ℤ (∀ i, ZMod (p ^ k i))).spanFinrank = #{i | k i ≠ 0} := by
  classical
  have hp : p.Prime := Fact.out
  have : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ hp.ne_zero⟩
  apply le_antisymm
  · -- Single-coordinate generators on `{i // k i ≠ 0}` span the product, as `ZMod 1` is trivial.
    let g : {i // k i ≠ 0} → ∀ i, ZMod (p ^ k i) := fun j ↦ Pi.single j.1 1
    have hspan : Submodule.span ℤ (Set.range g) = ⊤ := by
      refine top_unique fun x _ ↦ ?_
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      by_cases hi : k i = 0
      · have : Subsingleton (ZMod (p ^ k i)) := by rw [hi, pow_zero]; infer_instance
        rw [Subsingleton.elim (x i) 0, Pi.single_zero]
        exact Submodule.zero_mem _
      · have hx : Pi.single i (x i) = ((x i).val : ℤ) • g ⟨i, hi⟩ := by
          ext j
          by_cases hji : j = i
          · subst hji
            simp [g]
          · simp [g, hji]
        rw [hx]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    rw [← hspan]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range g)).trans ?_
    calc (Set.range g).ncard ≤ Fintype.card {i // k i ≠ 0} := by
          simpa [Nat.card_eq_fintype_card] using Set.ncard_image_le (f := g) (s := Set.univ)
      _ = #{i | k i ≠ 0} := Fintype.card_subtype _
  · -- Reducing the nontrivial coordinates modulo `p` maps onto the `𝔽_p`-vector space `𝔽_p^S`.
    let π : (∀ i, ZMod (p ^ k i)) →ₗ[ℤ] ({i // k i ≠ 0} → ZMod p) :=
      LinearMap.pi fun j ↦
        ((ZMod.castHom (dvd_pow_self p j.2) (ZMod p)).toAddMonoidHom.toIntLinearMap).comp
          (LinearMap.proj j.1)
    have hsurj : Function.Surjective π := fun y ↦ by
      refine ⟨fun i ↦ if hi : k i ≠ 0 then ((y ⟨i, hi⟩).val : ZMod (p ^ k i)) else 0, ?_⟩
      ext ⟨i, hi⟩
      simp [π, hi]
    have hle := Submodule.spanFinrank_map_le_of_fg π (Module.Finite.fg_top (R := ℤ))
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at hle
    calc #{i | k i ≠ 0} = Fintype.card {i // k i ≠ 0} := (Fintype.card_subtype _).symm
      _ = finrank (ZMod p) ({i // k i ≠ 0} → ZMod p) := (Module.finrank_pi (ZMod p)).symm
      _ = (⊤ : Submodule (ZMod p) ({i // k i ≠ 0} → ZMod p)).spanFinrank :=
          Module.finrank_eq_spanFinrank_of_free
      _ = (⊤ : Submodule ℤ ({i // k i ≠ 0} → ZMod p)).spanFinrank :=
          (Submodule.spanFinrank_restrictScalars_eq
            (ZMod.ringHom_surjective (algebraMap ℤ (ZMod p))) ⊤).symm
      _ ≤ (⊤ : Submodule ℤ (∀ i, ZMod (p ^ k i))).spanFinrank := hle

/-- **Generator count of `(A_L)_p` from a diagonal Jordan form.** At an odd prime `p`, if `b` is an
orthogonal basis of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), then the least number of
generators of the `p`-primary discriminant group `(A_L)_p` is `#{i | kᵢ ≠ 0}`. -/
theorem spanFinrank_primaryComponent_discriminantGroup_eq_card_filter
    {L : IntegralLattice V} [L.IsNondegenerate] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {ι : Type*} [Fintype ι] {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {u : ι → ℤ_[p]ˣ} {k : ι → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    (⊤ : Submodule ℤ (primaryComponent L.DiscriminantGroup p)).spanFinrank = #{i | k i ≠ 0} := by
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hθ : ∀ i, (p : ℤ_[p]) ^ k i ∣ (u i : ℤ_[p]) - ((u i : ℤ_[p]).appr (k i) : ℤ) :=
    fun i ↦ Ideal.mem_span_singleton.mp (PadicInt.appr_spec (k i) (u i : ℤ_[p]))
  obtain ⟨f⟩ := L.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu hθ
  let e : (∀ i, ZMod (p ^ k i)) ≃ₗ[ℤ] primaryComponent L.DiscriminantGroup p :=
    f.toAddEquiv.toIntLinearEquiv
  have he := Submodule.spanFinrank_map_eq_of_injective e.toLinearMap e.injective (p := ⊤)
  rw [Submodule.map_top, LinearEquiv.range] at he
  exact he.trans (spanFinrank_pi_zmod_pow k)

/-! ### `p`-adic unit squares and integer approximations -/

/-- Canonical integer lift `θ ≡ u (mod p^{max(k, 1)})` of a `p`-adic unit `u`. -/
private noncomputable def approxInt {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) (k : ℕ) : ℤ :=
  (u : ℤ_[p]).appr (max k 1)

private theorem pow_dvd_sub_approxInt {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) (k : ℕ) :
    (p : ℤ_[p]) ^ k ∣ (u : ℤ_[p]) - approxInt u k :=
  (pow_dvd_pow (p : ℤ_[p]) (le_max_left k 1)).trans
    (Ideal.mem_span_singleton.mp (PadicInt.appr_spec (max k 1) (u : ℤ_[p])))

private theorem dvd_sub_approxInt {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) (k : ℕ) :
    (p : ℤ_[p]) ∣ (u : ℤ_[p]) - approxInt u k :=
  (pow_one (p : ℤ_[p]) ▸ pow_dvd_pow (p : ℤ_[p]) (le_max_right k 1)).trans
    (Ideal.mem_span_singleton.mp (PadicInt.appr_spec (max k 1) (u : ℤ_[p])))

private theorem not_dvd_approxInt {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) (k : ℕ) :
    ¬(p : ℤ) ∣ approxInt u k := by
  rw [← PadicInt.isUnit_intCast_iff]
  by_contra hnu
  have hdvd : (p : ℤ_[p]) ∣ approxInt u k := PadicInt.not_isUnit_iff_dvd.mp hnu
  have hu : (p : ℤ_[p]) ∣ (u : ℤ_[p]) := by
    simpa using (dvd_sub_approxInt u k).add hdvd
  exact (PadicInt.not_isUnit_iff_dvd.mpr hu) u.isUnit

private theorem isCoprime_approxInt {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) (k : ℕ) :
    IsCoprime (p : ℤ) (approxInt u k) :=
  (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Fact.out)).mpr (not_dvd_approxInt u k)

/-- At an odd prime `p`, the product of `u ∈ ℤ_pˣ` and its integer lift `approxInt u k` is a unit
square in `ℤ_p`, because their residues modulo `p` coincide. -/
private theorem isSquare_mul_approxInt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (u : ℤ_[p]ˣ) (k : ℕ) :
    IsSquare ((u : ℤ_[p]) * approxInt u k) := by
  have hθu : IsUnit (approxInt u k : ℤ_[p]) :=
    PadicInt.isUnit_intCast_iff.mpr (not_dvd_approxInt u k)
  have hmem : (u : ℤ_[p]) - approxInt u k ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact dvd_sub_approxInt u k
  have hres_eq : IsLocalRing.residue ℤ_[p] (u : ℤ_[p]) =
      IsLocalRing.residue ℤ_[p] (approxInt u k : ℤ_[p]) :=
    sub_eq_zero.mp <| by
      rw [← map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  have hres : IsLocalRing.residue ℤ_[p] (approxInt u k : ℤ_[p]) ^ 2 =
      IsLocalRing.residue ℤ_[p] ((u : ℤ_[p]) * approxInt u k) := by
    rw [map_mul, hres_eq, sq]
  obtain ⟨x, hx, -⟩ := TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq (n := 2)
    (by exact_mod_cast PadicInt.isUnit_two hp) hθu hres
  exact ⟨x, by rw [← hx, sq]⟩

/-- An integer prime to an odd prime `p` with Legendre symbol `1` is a square in `ℤ_p`. -/
private theorem isSquare_padicInt_of_legendreSym_eq_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {m : ℤ} (hm : ¬(p : ℤ) ∣ m) (hleg : legendreSym p m = 1) :
    IsSquare (m : ℤ_[p]) := by
  obtain ⟨r, hr⟩ := (TauCeti.Padic.isSquare_intCast_iff_legendreSym_eq_one hp hm).mpr hleg
  have hr_le : ‖r‖ ≤ 1 := by
    have hnorm : ‖r‖ * ‖r‖ ≤ 1 := by
      rw [← norm_mul, ← hr]
      exact PadicInt.norm_le_one (m : ℤ_[p])
    nlinarith [norm_nonneg r]
  exact ⟨r.lift hr_le, PadicInt.ext hr⟩

/-- In `ℤ_p`, cancelling a nonzero square factor from `a * b ^ 2` preserves squareness of a unit
`a`. -/
private theorem isSquare_of_isSquare_mul_sq {p : ℕ} [Fact p.Prime] {a b : ℤ_[p]}
    (ha : IsUnit a) (hb : b ≠ 0) (hsq : IsSquare (a * b ^ 2)) :
    IsSquare a := by
  obtain ⟨r, hr⟩ := hsq
  have hnorm : ‖r‖ ≤ ‖b‖ := by
    have h1 : ‖r‖ * ‖r‖ = ‖b‖ * ‖b‖ := by
      rw [← norm_mul, ← hr, norm_mul, PadicInt.isUnit_iff.mp ha, one_mul, sq, norm_mul]
    nlinarith [norm_nonneg r, norm_nonneg b]
  obtain ⟨s, rfl⟩ := PadicInt.dvd_of_norm_le hnorm
  refine ⟨s, mul_right_cancel₀ (pow_ne_zero 2 hb) ?_⟩
  linear_combination hr

/-- Positive-level Legendre-symbol agreement between integer lifts translates to `p`-adic squareness
of the corresponding unit products. -/
private theorem isSquare_prod_filter_of_legendreSym_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {n : ℕ} (k : Fin n → ℕ) (u v : Fin n → ℤ_[p]ˣ) (k' : Fin n → ℕ) {m : ℕ}
    (hleg : ∏ i with k i = m, legendreSym p (approxInt (u i) (k i)) =
      ∏ i with k i = m, legendreSym p (approxInt (v i) (k' i))) :
    IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v i) := by
  rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod]
  set S := ({i : Fin n | k i = m} : Finset (Fin n))
  have hcop_v (i : Fin n) : IsCoprime (p : ℤ) (approxInt (v i) (k' i)) := isCoprime_approxInt _ _
  have hleg_prod : ∀ (T : Finset (Fin n)) (g : Fin n → ℤ),
      legendreSym p (∏ i ∈ T, g i) = ∏ i ∈ T, legendreSym p (g i) := by
    intro T g
    induction T using Finset.cons_induction with
    | empty => simp
    | cons a T ha ih => rw [Finset.prod_cons, Finset.prod_cons, legendreSym.mul, ih]
  have hsq_leg : legendreSym p (∏ i ∈ S, approxInt (u i) (k i) * approxInt (v i) (k' i)) = 1 := by
    rw [hleg_prod, Finset.prod_congr rfl fun i _ ↦ legendreSym.mul p _ _,
      Finset.prod_mul_distrib, hleg, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    simpa [sq] using legendreSym.sq_one p
      ((ZMod.isUnit_intCast_iff_isCoprime _ p).mpr (hcop_v i)).ne_zero
  have hndvd : ¬(p : ℤ) ∣ ∏ i ∈ S, approxInt (u i) (k i) * approxInt (v i) (k' i) := by
    rw [← PadicInt.isUnit_intCast_iff, Int.cast_prod]
    exact IsUnit.prod_iff.mpr fun i _ ↦ by
      rw [Int.cast_mul]
      exact (PadicInt.isUnit_intCast_iff.mpr (not_dvd_approxInt _ _)).mul
        (PadicInt.isUnit_intCast_iff.mpr (not_dvd_approxInt _ _))
  have hZ := isSquare_padicInt_of_legendreSym_eq_one hp hndvd hsq_leg
  rw [Int.cast_prod] at hZ
  have hu_sq : IsSquare (∏ i ∈ S, (u i : ℤ_[p]) * approxInt (u i) (k i)) :=
    Finset.prod_induction _ IsSquare (fun _ _ ha hb ↦ ha.mul hb) IsSquare.one
      fun i _ ↦ isSquare_mul_approxInt hp (u i) (k i)
  have hv_sq : IsSquare (∏ i ∈ S, (v i : ℤ_[p]) * approxInt (v i) (k' i)) :=
    Finset.prod_induction _ IsSquare (fun _ _ ha hb ↦ ha.mul hb) IsSquare.one
      fun i _ ↦ isSquare_mul_approxInt hp (v i) (k' i)
  have hcomb : IsSquare (((∏ i ∈ S, (u i : ℤ_[p])) * ∏ i ∈ S, (v i : ℤ_[p])) *
      (∏ i ∈ S, (approxInt (u i) (k i) : ℤ_[p]) * approxInt (v i) (k' i)) ^ 2) := by
    convert (hu_sq.mul hv_sq).mul hZ using 1
    simp only [Int.cast_mul, Finset.prod_mul_distrib, sq]
    ring
  have hunit_uv : IsUnit ((∏ i ∈ S, (u i : ℤ_[p])) * ∏ i ∈ S, (v i : ℤ_[p])) :=
    (IsUnit.prod_iff.mpr fun i _ ↦ (u i).isUnit).mul
      (IsUnit.prod_iff.mpr fun i _ ↦ (v i).isUnit)
  have hne : (∏ i ∈ S, (approxInt (u i) (k i) : ℤ_[p]) * approxInt (v i) (k' i)) ≠ 0 := by
    have hu_int := PadicInt.isUnit_intCast_iff.mpr hndvd
    rw [Int.cast_prod] at hu_int
    simpa [Int.cast_mul] using hu_int.ne_zero
  exact isSquare_of_isSquare_mul_sq hunit_uv hne hcomb

/-! ### Assembling an integral `ℤ_p`-isometry from fiberwise unit-diagonal equivalences -/

/-- If two diagonal `ℤ_p`-quadratic forms with matching scale exponents `k` have unit products in
the same square class on every scale fiber `{i | k i = m}`, then they are integrally equivalent
over `ℤ_p`. -/
private theorem equivalent_weightedSumSquares_mul_pow_of_forall_fiber
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (k : Fin n → ℕ) (u v : Fin n → ℤ_[p]ˣ)
    (hfiber : ∀ m : ℕ, IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v i)) :
    (QuadraticMap.weightedSumSquares ℤ_[p]
        fun i ↦ (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i).Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p]
        fun i ↦ (v i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
  classical
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two hp
  let S : Finset ℕ := Finset.univ.image k
  let κ : Fin n → S := fun i ↦ ⟨k i, Finset.mem_image_of_mem k (Finset.mem_univ i)⟩
  let σ : (Σ m : S, {i : Fin n // κ i = m}) ≃ Fin n := Equiv.sigmaFiberEquiv κ
  -- On each scale fiber `m ∈ S`, Henselian unit-diagonal classification supplies a linear isometry.
  have hstep (m : S) : ∃ e : ({i : Fin n // κ i = m} → ℤ_[p]) ≃ₗ[ℤ_[p]]
      ({i : Fin n // κ i = m} → ℤ_[p]), ∀ z,
      ∑ i : {i : Fin n // κ i = m}, (v i.1 : ℤ_[p]) * (e z i * e z i) =
        ∑ i : {i : Fin n // κ i = m}, (u i.1 : ℤ_[p]) * (z i * z i) := by
    let α := Fintype.equivFin {i : Fin n // κ i = m}
    have hsq : IsSquare ((∏ j, u (α.symm j).1) * ∏ j, v (α.symm j).1) := by
      have hsub : ∀ w : Fin n → ℤ_[p]ˣ,
          ∏ j, w (α.symm j).1 = ∏ i with k i = m.1, w i := fun w ↦ by
        rw [Equiv.prod_comp α.symm (fun i : {i : Fin n // κ i = m} ↦ w i.1),
          ← Finset.prod_subtype ({i : Fin n | k i = m.1})
            (fun i ↦ by simp [κ, Subtype.ext_iff]) (fun i ↦ w i)]
      rw [hsub u, hsub v]
      exact hfiber m.1
    obtain ⟨f⟩ := (TauCeti.equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
      h2 (fun j ↦ u (α.symm j).1) (fun j ↦ v (α.symm j).1)).mpr hsq
    let c := LinearEquiv.funCongrLeft ℤ_[p] ℤ_[p] α.symm
    refine ⟨c.trans (f.toLinearEquiv.trans c.symm), fun z ↦ ?_⟩
    have hf := f.map_app (c z)
    simp only [QuadraticMap.weightedSumSquares_units, QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul] at hf
    calc ∑ i : {i : Fin n // κ i = m}, (v i.1 : ℤ_[p]) *
            (c.symm (f (c z)) i * c.symm (f (c z)) i)
        = ∑ j, (v (α.symm j).1 : ℤ_[p]) * (f (c z) j * f (c z) j) :=
          (Equiv.sum_comp α.symm fun i ↦ (v i.1 : ℤ_[p]) *
            (c.symm (f (c z)) i * c.symm (f (c z)) i)).symm.trans <|
            Finset.sum_congr rfl fun j _ ↦ by simp [c]
      _ = ∑ j, (u (α.symm j).1 : ℤ_[p]) * (c z j * c z j) := hf
      _ = ∑ i : {i : Fin n // κ i = m}, (u i.1 : ℤ_[p]) * (z i * z i) :=
          (Finset.sum_congr rfl fun j _ ↦ by simp [c]).trans <|
            Equiv.sum_comp α.symm fun i ↦ (u i.1 : ℤ_[p]) * (z i * z i)
  choose e he using hstep
  -- Reassemble the fiberwise linear equivalences along `σ : (Σ m, fiber m) ≃ Fin n`.
  let curryEquiv : ((Σ m : S, {i : Fin n // κ i = m}) → ℤ_[p]) ≃ₗ[ℤ_[p]]
      (∀ m : S, {i : Fin n // κ i = m} → ℤ_[p]) :=
    { toFun := fun f m i ↦ f ⟨m, i⟩
      invFun := fun g p ↦ g p.1 p.2
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let σEquiv : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] ((Σ m : S, {i : Fin n // κ i = m}) → ℤ_[p]) :=
    LinearEquiv.funCongrLeft ℤ_[p] ℤ_[p] σ
  let E : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]) :=
    σEquiv.trans (curryEquiv.trans ((LinearEquiv.piCongrRight e).trans
      (curryEquiv.symm.trans σEquiv.symm)))
  refine ⟨{ toLinearEquiv := E, map_app' := fun x ↦ ?_ }⟩
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  rw [← Equiv.sum_comp σ, ← Equiv.sum_comp σ, Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  have hk_eq (i : {i : Fin n // κ i = m}) : k (σ ⟨m, i⟩) = m.1 :=
    congrArg Subtype.val i.2
  have hE_eq (i : {i : Fin n // κ i = m}) :
      E x (σ ⟨m, i⟩) = e m (fun j ↦ x (σ ⟨m, j⟩)) i := by
    dsimp [E, σEquiv, curryEquiv]
    rw [σ.symm_apply_apply]
  calc ∑ i : {i : Fin n // κ i = m},
          ((v (σ ⟨m, i⟩) : ℤ_[p]) * (p : ℤ_[p]) ^ k (σ ⟨m, i⟩)) *
            (E x (σ ⟨m, i⟩) * E x (σ ⟨m, i⟩))
      = (p : ℤ_[p]) ^ m.1 * ∑ i : {i : Fin n // κ i = m},
          (v i.1 : ℤ_[p]) * (e m (fun j ↦ x (σ ⟨m, j⟩)) i * e m (fun j ↦ x (σ ⟨m, j⟩)) i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hk_eq i, hE_eq i]
        simp only [σ, Equiv.sigmaFiberEquiv_apply]
        ring
    _ = (p : ℤ_[p]) ^ m.1 * ∑ i : {i : Fin n // κ i = m},
          (u i.1 : ℤ_[p]) * (x (σ ⟨m, i⟩) * x (σ ⟨m, i⟩)) := by
        rw [he m]
    _ = ∑ i : {i : Fin n // κ i = m},
          ((u (σ ⟨m, i⟩) : ℤ_[p]) * (p : ℤ_[p]) ^ k (σ ⟨m, i⟩)) *
            (x (σ ⟨m, i⟩) * x (σ ⟨m, i⟩)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hk_eq i]
        simp only [σ, Equiv.sigmaFiberEquiv_apply]
        ring

/-- Reindexing an orthogonal basis preserves orthogonality. -/
private theorem iIsOrtho_reindex {R M ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {B : LinearMap.BilinForm R M} {b : Basis ι R M} (hb : B.iIsOrtho b) (e : ι ≃ κ) :
    B.iIsOrtho (b.reindex e) :=
  LinearMap.BilinForm.iIsOrtho_def.mpr fun i j hij ↦ by
    simpa [Basis.reindex_apply] using
      LinearMap.BilinForm.iIsOrtho_def.mp hb (e.symm i) (e.symm j) (e.symm.injective.ne hij)

/-- Diagonal Jordan form of `L_p` indexed by `Fin n` when `rank L = n`. -/
private theorem exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow
    (L : IntegralLattice V) [L.IsNondegenerate] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ}
    (hn : finrank ℤ L = n) :
    ∃ (b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)) (u : Fin n → ℤ_[p]ˣ) (k : Fin n → ℕ),
      (L.localIntegralForm p).iIsOrtho b ∧
        ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i := by
  have hnL : finrank ℤ_[p] (L.LocalCarrier p) = n := by
    rw [Module.finrank_eq_card_basis ((Module.finBasis ℤ L).baseChange ℤ_[p]), Fintype.card_fin, hn]
  obtain ⟨b', u', k', hb', hbu'⟩ :=
    L.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
  refine ⟨b'.reindex (finCongr hnL), fun i ↦ u' ((finCongr hnL).symm i),
    fun i ↦ k' ((finCongr hnL).symm i), iIsOrtho_reindex hb' (finCongr hnL), fun i ↦ ?_⟩
  simpa [Basis.reindex_apply] using hbu' ((finCongr hnL).symm i)

/-- Given two diagonal Jordan forms of the same rank at an odd prime `p` whose `p`-primary
discriminant bilinear modules are isometric, `k` and `l` agree up to a permutation `σ` and every
positive-scale fiber has square unit product. -/
private theorem exists_perm_and_isSquare_pos_of_isometry_primaryComponent
    {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ}
    {b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)} {c : Basis (Fin n) ℤ_[p] (M.LocalCarrier p)}
    {u v : Fin n → ℤ_[p]ˣ} {k l : Fin n → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b) (hc : (M.localIntegralForm p).iIsOrtho c)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hcv : ∀ i, M.localIntegralForm p (c i) (c i) = v i * (p : ℤ_[p]) ^ l i)
    (hdisc : Nonempty (FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict (primaryComponent M.discriminantBilinearModule p)))) :
    ∃ σ : Equiv.Perm (Fin n), (∀ i, l (σ i) = k i) ∧
      ∀ m, 0 < m → IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v (σ i)) := by
  classical
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨fL⟩ := L.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu
    (fun i ↦ pow_dvd_sub_approxInt (u i) (k i))
  obtain ⟨fM⟩ := M.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hc hcv
    (fun i ↦ pow_dvd_sub_approxInt (v i) (l i))
  obtain ⟨fLM⟩ := hdisc
  have hodd_card : Odd (Nat.card (FiniteQuadraticModule.pi fun i ↦
      FiniteQuadraticModule.oddCyclic (p ^ k i) hp_odd.pow (approxInt (u i) (k i)))) := by
    -- Unfold the carrier of `FiniteQuadraticModule.pi` to `∀ i, ZMod (p ^ k i)`.
    change Odd (Nat.card (∀ i, ZMod (p ^ k i)))
    rw [Nat.card_pi]
    exact Finset.prod_induction _ Odd (fun _ _ ha hb ↦ ha.mul hb) odd_one fun i _ ↦ by
      rw [Nat.card_zmod]
      exact hp_odd.pow
  have hquad : Nonempty (FiniteQuadraticModule.Isometry
      (FiniteQuadraticModule.pi fun i ↦
        FiniteQuadraticModule.oddCyclic (p ^ k i) hp_odd.pow (approxInt (u i) (k i)))
      (FiniteQuadraticModule.pi fun i ↦
        FiniteQuadraticModule.oddCyclic (p ^ l i) hp_odd.pow (approxInt (v i) (l i)))) :=
    (FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_card).mpr
      ⟨fL.trans (fLM.trans fM.symm)⟩
  have hclass := (FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff hp_odd k l
    (fun i ↦ isCoprime_approxInt (u i) (k i))
    (fun i ↦ isCoprime_approxInt (v i) (l i))).mp hquad
  -- Positive-scale occurrence counts agree; subtracting from `n` matches `m = 0` as well.
  have hocc : ∀ m, Function.occCount k m = Function.occCount l m := by
    have hpos : ∀ m, 0 < m → Function.occCount k m = Function.occCount l m := fun m hm ↦ by
      rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
      exact (hclass m hm).1
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · let T : Finset ℕ := insert 0 (Finset.univ.image k ∪ Finset.univ.image l)
      have hkT : ∑ a ∈ T, Function.occCount k a = Nat.card (Fin n) :=
        Function.sum_occCount_eq_card k fun i ↦ Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_image_of_mem k (Finset.mem_univ i)))
      have hlT : ∑ a ∈ T, Function.occCount l a = Nat.card (Fin n) :=
        Function.sum_occCount_eq_card l fun i ↦ Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_image_of_mem l (Finset.mem_univ i)))
      rw [← Finset.add_sum_erase T _ (Finset.mem_insert_self 0 _)] at hkT hlT
      have herase : ∑ a ∈ T.erase 0, Function.occCount k a =
          ∑ a ∈ T.erase 0, Function.occCount l a :=
        Finset.sum_congr rfl fun a ha ↦ hpos a (Nat.pos_of_ne_zero (Finset.ne_of_mem_erase ha))
      omega
    · exact hpos m hm
  obtain ⟨σ, hσ⟩ := Function.exists_perm_of_occCount_eq hocc
  have hσi : ∀ i, l (σ i) = k i := congrFun hσ
  refine ⟨σ, hσi, fun m hm ↦ ?_⟩
  have hleg_σ : ∏ i with k i = m, legendreSym p (approxInt (u i) (k i)) =
      ∏ i with k i = m, legendreSym p (approxInt (v (σ i)) (l (σ i))) := by
    rw [(hclass m hm).2, Finset.prod_filter, Finset.prod_filter]
    exact (Equiv.prod_comp (σ : Fin n ≃ Fin n) fun j ↦
      if l j = m then legendreSym p (approxInt (v j) (l j)) else 1).symm.trans
      (Finset.prod_congr rfl fun i _ ↦ by simp [hσi i])
  exact isSquare_prod_filter_of_legendreSym_eq hp k u (fun i ↦ v (σ i)) (fun i ↦ l (σ i)) hleg_σ

/-- Once two diagonal Jordan forms match up to `σ` and agree in square class on every fiber `m`,
the localized integral forms are isometric over `ℤ_p`. -/
private theorem localIntegralForm_equivalent_of_forall_fiber
    {L : IntegralLattice V} {M : IntegralLattice W} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ}
    {b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)} {c : Basis (Fin n) ℤ_[p] (M.LocalCarrier p)}
    {u v : Fin n → ℤ_[p]ˣ} {k l : Fin n → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b) (hc : (M.localIntegralForm p).iIsOrtho c)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hcv : ∀ i, M.localIntegralForm p (c i) (c i) = v i * (p : ℤ_[p]) ^ l i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, l (σ i) = k i)
    (hfiber : ∀ m : ℕ, IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v (σ i))) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) := by
  let := (PadicInt.isUnit_two hp).invertible
  have hdiag := equivalent_weightedSumSquares_mul_pow_of_forall_fiber hp k u (fun i ↦ v (σ i))
    hfiber
  have hL_quad : (L.localIntegralForm p).toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p] fun i ↦ (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
    simpa only [hbu] using hb.equivalent_weightedSumSquares
  have hM_quad : (M.localIntegralForm p).toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p] fun i ↦ (v (σ i) : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
    have hcσ : (M.localIntegralForm p).iIsOrtho (c.reindex σ.symm) := iIsOrtho_reindex hc σ.symm
    simpa only [Basis.reindex_apply, Equiv.symm_symm, hcv, hσ] using
      hcσ.equivalent_weightedSumSquares
  exact ((L.isSymm_localIntegralForm p).equivalent_iff_toQuadraticMap_equivalent
    (M.isSymm_localIntegralForm p)).mpr (hL_quad.trans (hdiag.trans hM_quad.symm))

/-- The local determinant of `L` in `ℤ_p` differs by a unit square from `(∏ᵢ uᵢ) p^{∑ᵢ kᵢ}` in any
orthogonal diagonal Jordan basis `b` of `L_p`. -/
private theorem exists_unit_sq_mul_det_eq {L : IntegralLattice V} {p : ℕ} [Fact p.Prime] {n : ℕ}
    (hn : finrank ℤ L = n) {b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)}
    {u : Fin n → ℤ_[p]ˣ} {k : Fin n → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    ∃ d : ℤ_[p]ˣ, (d : ℤ_[p]) ^ 2 * (L.determinant : ℤ_[p]) =
      (∏ i, (u i : ℤ_[p])) * (p : ℤ_[p]) ^ (∑ i, k i) := by
  let b₀ := ((Module.finBasis ℤ L).reindex (finCongr hn)).baseChange ℤ_[p]
  have hdet₀ : ((L.localIntegralForm p).toMatrix b₀).det = (L.determinant : ℤ_[p]) :=
    L.det_toMatrix_localIntegralForm p _
  have hdet_b : ((L.localIntegralForm p).toMatrix b).det =
      (∏ i, (u i : ℤ_[p])) * (p : ℤ_[p]) ^ (∑ i, k i) := by
    rw [hb.toMatrix_eq_diagonal, Matrix.det_diagonal]
    simp_rw [hbu, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hchg := LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det b₀ b (L.localIntegralForm p)
  have hu_chg : IsUnit (b₀.toMatrix b).det := b₀.isUnit_det b
  refine ⟨hu_chg.unit, ?_⟩
  rw [IsUnit.unit_spec, ← hdet₀, ← hchg, hdet_b]

/-! ### Odd-prime classification theorems -/

/-- **Odd-prime local classification by the discriminant bilinear form.** Let `p` be an odd prime
and let `L` and `M` be nondegenerate integral lattices. Their localized integral forms over `ℤ_p`
are isometric if and only if `L` and `M` have the same rank, the product of their signed
determinants is a square in `ℤ_p`, and the `p`-primary components of their discriminant bilinear
modules are isometric. -/
theorem localIntegralForm_equivalent_iff_discriminantBilinear
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteBilinearModule.Isometry
          (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
          (M.discriminantBilinearModule.restrict
            (primaryComponent M.discriminantBilinearModule p))) := by
  classical
  constructor
  · intro h
    obtain ⟨hrank, hsq⟩ := L.localIntegralForm_equivalent_imp M p h
    exact ⟨hrank, hsq, h.map primaryDiscriminantBilinearIsometry⟩
  · rintro ⟨hrank, hsq, hdisc⟩
    obtain ⟨b, u, k, hb, hbu⟩ :=
      L.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp (rfl : finrank ℤ L = _)
    obtain ⟨c, v, l, hc, hcv⟩ :=
      M.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp hrank.symm
    obtain ⟨σ, hσ, hpos⟩ :=
      exists_perm_and_isSquare_pos_of_isometry_primaryComponent hp hb hc hbu hcv hdisc
    -- Compare the full unit products via the determinant square class.
    obtain ⟨dL, hdL⟩ := exists_unit_sq_mul_det_eq rfl hb hbu
    obtain ⟨dM, hdM⟩ := exists_unit_sq_mul_det_eq hrank.symm hc hcv
    have hsum_eq : ∑ j, l j = ∑ i, k i :=
      (Equiv.sum_comp (σ : Fin _ ≃ Fin _) l).symm.trans (Finset.sum_congr rfl fun i _ ↦ hσ i)
    have hprod_v : ∏ j, (v j : ℤ_[p]) = ∏ i, (v (σ i) : ℤ_[p]) :=
      (Equiv.prod_comp (σ : Fin _ ≃ Fin _) fun j ↦ (v j : ℤ_[p])).symm
    have hfull : IsSquare ((∏ i, u i) * ∏ i, v (σ i)) := by
      rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod]
      have hsq_pow : IsSquare (((∏ i, (u i : ℤ_[p])) * ∏ i, (v (σ i) : ℤ_[p])) *
          ((p : ℤ_[p]) ^ ∑ i, k i) ^ 2) := by
        obtain ⟨z, hz⟩ := hsq
        refine ⟨z * dL * dM, ?_⟩
        have hmul := congrArg₂ (· * ·) hdL hdM
        rw [hsum_eq, hprod_v] at hmul
        rw [sq]
        linear_combination -hmul + (dL : ℤ_[p]) ^ 2 * (dM : ℤ_[p]) ^ 2 * hz
      exact isSquare_of_isSquare_mul_sq
        ((IsUnit.prod_iff.mpr fun i _ ↦ (u i).isUnit).mul
          (IsUnit.prod_iff.mpr fun i _ ↦ (v (σ i)).isUnit))
        (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) hsq_pow
    -- Subtract the positive-scale fibers in `ℤ_pˣ` to obtain squareness on the `m = 0` fiber.
    have hzero : IsSquare ((∏ i with k i = 0, u i) * ∏ i with k i = 0, v (σ i)) := by
      let P : Finset ℕ := (Finset.univ.image k).erase 0
      have hsplit (w : Fin (finrank ℤ L) → ℤ_[p]ˣ) :
          ∏ i, w i = (∏ i with k i = 0, w i) * ∏ m ∈ P, ∏ i with k i = m, w i := by
        have hpart := (Finset.prod_fiberwise_of_maps_to
          (s := Finset.univ) (g := k) (t := insert 0 P)
          (fun i _ ↦ by
            by_cases hk0 : k i = 0
            · simp [hk0]
            · exact Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨hk0, Finset.mem_image_of_mem k (Finset.mem_univ i)⟩))
          w).symm
        rw [hpart, Finset.prod_insert (Finset.notMem_erase 0 _)]
      have hP_sq : IsSquare (∏ m ∈ P, ((∏ i with k i = m, u i) * ∏ i with k i = m, v (σ i))) :=
        Finset.prod_induction _ IsSquare (fun _ _ ha hb ↦ ha.mul hb) IsSquare.one
          fun m hm ↦ hpos m (Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hm))
      rw [hsplit u, hsplit (fun i ↦ v (σ i))] at hfull
      have hrearr : ((∏ i with k i = 0, u i) * ∏ m ∈ P, ∏ i with k i = m, u i) *
          ((∏ i with k i = 0, v (σ i)) * ∏ m ∈ P, ∏ i with k i = m, v (σ i)) =
          ((∏ i with k i = 0, u i) * ∏ i with k i = 0, v (σ i)) *
            ∏ m ∈ P, ((∏ i with k i = m, u i) * ∏ i with k i = m, v (σ i)) := by
        rw [Finset.prod_mul_distrib]
        ac_rfl
      rw [hrearr] at hfull
      simpa [mul_inv_cancel_right] using hfull.mul hP_sq.inv
    exact localIntegralForm_equivalent_of_forall_fiber hp hb hc hbu hcv σ hσ fun m ↦ by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact hzero
      · exact hpos m hm

/-- Unit-square determinant formulation of
`localIntegralForm_equivalent_iff_discriminantBilinear`. -/
theorem localIntegralForm_equivalent_iff_exists_unit_sq_and_discriminantBilinear
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        (∃ u : ℤ_[p]ˣ, (L.determinant : ℤ_[p]) = (u : ℤ_[p]) ^ 2 * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteBilinearModule.Isometry
          (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
          (M.discriminantBilinearModule.restrict
            (primaryComponent M.discriminantBilinearModule p))) := by
  constructor
  · intro h
    exact ⟨(L.localIntegralForm_equivalent_imp M p h).1,
      L.exists_determinant_eq_unit_sq_mul_of_localIntegralForm_equivalent M p h,
      h.map primaryDiscriminantBilinearIsometry⟩
  · rintro ⟨hrank, ⟨u, hu⟩, hdisc⟩
    refine (L.localIntegralForm_equivalent_iff_discriminantBilinear M hp).mpr ⟨hrank, ?_, hdisc⟩
    refine ⟨(u : ℤ_[p]) * (M.determinant : ℤ_[p]), ?_⟩
    rw [hu]
    ring

/-- **Odd-prime local classification for even lattices.** For even nondegenerate lattices `L` and
`M` and an odd prime `p`, `L_p ≃ M_p` if and only if `rank L = rank M`, `det L · det M` is a square
in `ℤ_p`, and the `p`-primary components of their discriminant quadratic modules are isometric. -/
theorem localIntegralForm_equivalent_iff_discriminantQuadratic
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteQuadraticModule.Isometry
          ((L.discriminantQuadraticModule hL).restrict
            (primaryComponent (L.discriminantQuadraticModule hL) p))
          ((M.discriminantQuadraticModule hM).restrict
            (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  have hp_prime : p.Prime := Fact.out
  have hp_odd : Odd p := hp_prime.odd_of_ne_two hp
  have hodd_L : Odd (Nat.card ((L.discriminantQuadraticModule hL).restrict
      (primaryComponent (L.discriminantQuadraticModule hL) p))) := by
    -- The carrier of the restricted discriminant quadratic module is `primaryComponent _ p`.
    change Odd (Nat.card (primaryComponent L.DiscriminantGroup p))
    rw [TauCeti.AddCommGroup.natCard_primaryComponent _ hp_prime]
    exact hp_odd.pow
  rw [L.localIntegralForm_equivalent_iff_discriminantBilinear M hp,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_L]
  rfl

/-! ### Minimal-rank uniqueness at odd primes (Nikulin Theorem 1.9.1) -/

/-- **Uniqueness of minimal-rank `p`-adic localizations at odd primes (Nikulin, Theorem 1.9.1).**
If `p` is an odd prime and both `L` and `M` achieve the minimal rank `rank L = ℓ((A_L)_p)` and
`rank M = ℓ((A_M)_p)`, then `L_p` and `M_p` are isometric if and only if the `p`-primary
components of their discriminant bilinear modules are isometric; neither equal rank nor a
determinant hypothesis needs to be supplied separately. -/
theorem localIntegralForm_equivalent_iff_of_finrank_eq_spanFinrank
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hLrank : finrank ℤ L = (⊤ : Submodule ℤ (primaryComponent L.DiscriminantGroup p)).spanFinrank)
    (hMrank : finrank ℤ M =
      (⊤ : Submodule ℤ (primaryComponent M.DiscriminantGroup p)).spanFinrank) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      Nonempty (FiniteBilinearModule.Isometry
        (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
        (M.discriminantBilinearModule.restrict
          (primaryComponent M.discriminantBilinearModule p))) := by
  classical
  refine ⟨fun h ↦ h.map primaryDiscriminantBilinearIsometry, fun hdisc ↦ ?_⟩
  obtain ⟨fLM⟩ := hdisc
  have hspan_eq :
      (⊤ : Submodule ℤ (primaryComponent L.DiscriminantGroup p)).spanFinrank =
        (⊤ : Submodule ℤ (primaryComponent M.DiscriminantGroup p)).spanFinrank := by
    let e : primaryComponent L.DiscriminantGroup p ≃ₗ[ℤ] primaryComponent M.DiscriminantGroup p :=
      fLM.toAddEquiv.toIntLinearEquiv
    have he := Submodule.spanFinrank_map_eq_of_injective e.toLinearMap e.injective (p := ⊤)
    rw [Submodule.map_top, LinearEquiv.range] at he
    exact he.symm
  have hrank : finrank ℤ L = finrank ℤ M := hLrank.trans (hspan_eq.trans hMrank.symm)
  obtain ⟨b, u, k, hb, hbu⟩ :=
    L.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp (rfl : finrank ℤ L = _)
  obtain ⟨c, v, l, hc, hcv⟩ :=
    M.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp hrank.symm
  obtain ⟨σ, hσ, hpos⟩ :=
    exists_perm_and_isSquare_pos_of_isometry_primaryComponent hp hb hc hbu hcv ⟨fLM⟩
  -- Minimal rank forces every exponent `k i` to be nonzero, so the `m = 0` fiber is empty.
  have hk_card : #{i : Fin (finrank ℤ L) | k i ≠ 0} = finrank ℤ L := by
    rw [← spanFinrank_primaryComponent_discriminantGroup_eq_card_filter hp hb hbu, ← hLrank]
  have hk_all : ({i : Fin (finrank ℤ L) | k i ≠ 0} : Finset (Fin (finrank ℤ L))) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hk_card])
  have hk_ne_zero (i : Fin (finrank ℤ L)) : k i ≠ 0 := by
    have hi : i ∈ ({i : Fin (finrank ℤ L) | k i ≠ 0} : Finset (Fin (finrank ℤ L))) :=
      hk_all.symm ▸ Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  have hzero_empty : ({i : Fin (finrank ℤ L) | k i = 0} : Finset (Fin (finrank ℤ L))) = ∅ := by
    ext i
    simp [hk_ne_zero i]
  exact localIntegralForm_equivalent_of_forall_fiber hp hb hc hbu hcv σ hσ fun m ↦ by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hzero_empty]
    · exact hpos m hm

/-- Even-lattice counterpart of
`localIntegralForm_equivalent_iff_of_finrank_eq_spanFinrank`. -/
theorem localIntegralForm_equivalent_iff_of_isEven_of_finrank_eq_spanFinrank
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hLrank : finrank ℤ L = (⊤ : Submodule ℤ (primaryComponent L.DiscriminantGroup p)).spanFinrank)
    (hMrank : finrank ℤ M =
      (⊤ : Submodule ℤ (primaryComponent M.DiscriminantGroup p)).spanFinrank) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      Nonempty (FiniteQuadraticModule.Isometry
        ((L.discriminantQuadraticModule hL).restrict
          (primaryComponent (L.discriminantQuadraticModule hL) p))
        ((M.discriminantQuadraticModule hM).restrict
          (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  have hp_prime : p.Prime := Fact.out
  have hp_odd : Odd p := hp_prime.odd_of_ne_two hp
  have hodd_L : Odd (Nat.card ((L.discriminantQuadraticModule hL).restrict
      (primaryComponent (L.discriminantQuadraticModule hL) p))) := by
    -- The carrier of the restricted discriminant quadratic module is `primaryComponent _ p`.
    change Odd (Nat.card (primaryComponent L.DiscriminantGroup p))
    rw [TauCeti.AddCommGroup.natCard_primaryComponent _ hp_prime]
    exact hp_odd.pow
  rw [L.localIntegralForm_equivalent_iff_of_finrank_eq_spanFinrank M hp hLrank hMrank,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_L]
  rfl

end TauCeti.IntegralLattice
