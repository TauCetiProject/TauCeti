/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Rank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.Algebra.Module.SpanRank
import TauCeti.Data.Fintype.Fiber
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
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
each scale fiber (`TauCeti.equivalent_weightedSumSquares_mul_of_forall_fiber`) constructs an
integral `ℤ_p`-isometry `L_p ≃ M_p`.

When `rank L` and `rank M` attain the minimal generator count `AddGroup.rank (A_L)_p` and
`AddGroup.rank (A_M)_p`
(`TauCeti.IntegralLattice.rank_primaryComponent_discriminantGroup_eq_card_filter`), neither
localization has a unimodular constituent `kᵢ = 0`, so an isometry `(A_L)_p ≅ (A_M)_p` determines
`L_p ≃ M_p` without any determinant or rank hypothesis. This is the uniqueness clause of Nikulin's
Theorem 1.9.1 at odd primes.

At odd order, a bilinear isometry between finite quadratic modules automatically preserves the
quadratic refinement
(`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`), so the odd-prime
classification takes the same form for arbitrary nondegenerate lattices via `b_L` and for even
nondegenerate lattices via `q_L`.

## Main results

* `IntegralLattice.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule` and
  `IntegralLattice.localIntegralForm_equivalent_iff_exists_unit_sq_and_discriminantBilinearModule`
  classify `L_p ≃ M_p` at an odd prime `p` by `rank L = rank M`, `det L · det M` being a square in
  `ℤ_p` (equivalently `det L = u² det M` for `u ∈ ℤ_pˣ`), and `(A_L)_p ≅ (A_M)_p`.
* `IntegralLattice.localIntegralForm_equivalent_iff_isSquare_and_discriminantQuadraticModule`:
  the even-lattice counterpart in terms of the `p`-primary discriminant quadratic modules.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_of_finrank_eq_rank` and
  `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_of_isEven_of_finrank_eq_rank`:
  minimal-rank `p`-adic localizations (`rank L = AddGroup.rank (A_L)_p`) are isometric if and only
  if their `p`-primary discriminant forms are isometric.

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

/-! ### `p`-adic unit squares and integer approximations -/

/-- Canonical integer lift `θ ≡ u (mod p^{max(k, 1)})` of a `p`-adic unit `u`. -/
private noncomputable def approxInt {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) (k : ℕ) : ℤ :=
  (u : ℤ_[p]).appr (max k 1)

private theorem pow_dvd_sub_approxInt {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) (k : ℕ) :
    (p : ℤ_[p]) ^ k ∣ (u : ℤ_[p]) - approxInt u k :=
  (pow_dvd_pow (p : ℤ_[p]) (le_max_left k 1)).trans
    (PadicInt.dvd_sub_appr (u : ℤ_[p]) (max k 1))

private theorem dvd_sub_approxInt {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) (k : ℕ) :
    (p : ℤ_[p]) ∣ (u : ℤ_[p]) - approxInt u k :=
  (pow_one (p : ℤ_[p]) ▸ pow_dvd_pow (p : ℤ_[p]) (le_max_right k 1)).trans
    (PadicInt.dvd_sub_appr (u : ℤ_[p]) (max k 1))

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

/-- Positive-level Legendre-symbol agreement between integer lifts translates to `p`-adic squareness
of the corresponding unit products. -/
private theorem isSquare_prod_filter_of_legendreSym_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {n : ℕ} (k : Fin n → ℕ) (u v : Fin n → ℤ_[p]ˣ) (k' : Fin n → ℕ) {m : ℕ}
    (hleg : ∏ i with k i = m, legendreSym p (approxInt (u i) (k i)) =
      ∏ i with k i = m, legendreSym p (approxInt (v i) (k' i))) :
    IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v i) := by
  rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod]
  set S := ({i : Fin n | k i = m} : Finset (Fin n))
  have hsq_leg : legendreSym p (∏ i ∈ S, approxInt (u i) (k i) * approxInt (v i) (k' i)) = 1 := by
    rw [← legendreSym.hom_apply, map_prod]
    simp only [legendreSym.hom_apply, legendreSym.mul]
    rw [Finset.prod_mul_distrib, hleg, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    simpa [sq] using legendreSym.sq_one p
      ((ZMod.isUnit_intCast_iff_isCoprime _ p).mpr (isCoprime_approxInt (v i) (k' i))).ne_zero
  have hndvd : ¬(p : ℤ) ∣ ∏ i ∈ S, approxInt (u i) (k i) * approxInt (v i) (k' i) := by
    rw [← PadicInt.isUnit_intCast_iff, Int.cast_prod]
    exact IsUnit.prod_iff.mpr fun i _ ↦ by
      rw [Int.cast_mul]
      exact (PadicInt.isUnit_intCast_iff.mpr (not_dvd_approxInt _ _)).mul
        (PadicInt.isUnit_intCast_iff.mpr (not_dvd_approxInt _ _))
  have hZ := (PadicInt.isSquare_intCast_iff_legendreSym_eq_one hp hndvd).mpr hsq_leg
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
  have hne : (∏ i ∈ S, (approxInt (u i) (k i) : ℤ_[p]) * approxInt (v i) (k' i)) ≠ 0 := by
    have hu_int := PadicInt.isUnit_intCast_iff.mpr hndvd
    rw [Int.cast_prod] at hu_int
    simpa [Int.cast_mul] using hu_int.ne_zero
  exact (PadicInt.isSquare_mul_sq_iff hne).mp hcomb

/-! ### Assembling an integral `ℤ_p`-isometry from fiberwise unit-diagonal equivalences -/

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
    fun i ↦ k' ((finCongr hnL).symm i), hb'.reindex (finCongr hnL), fun i ↦ ?_⟩
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
    rw [Nat.card_pi]
    exact Finset.prod_induction _ Odd (fun _ _ ha hb ↦ ha.mul hb) odd_one fun i _ ↦ by
      rw [FiniteQuadraticModule.natCard_oddCyclic]
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
  obtain ⟨σ, hσ⟩ :=
    Function.exists_perm_of_occCount_eq_of_ne (u := k) (v := l) (z := 0) fun m hm ↦ by
      rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
      exact (hclass m (Nat.pos_of_ne_zero hm)).1
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
  have hdiag := TauCeti.equivalent_weightedSumSquares_mul_of_forall_fiber
    (PadicInt.isUnit_two hp) k (fun m ↦ (p : ℤ_[p]) ^ m) u (fun i ↦ v (σ i)) hfiber
  have hL_quad : (L.localIntegralForm p).toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p] fun i ↦ (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
    simpa only [hbu] using hb.equivalent_weightedSumSquares
  have hM_quad : (M.localIntegralForm p).toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p] fun i ↦ (v (σ i) : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
    simpa only [Basis.reindex_apply, Equiv.symm_symm, hcv, hσ] using
      (hc.reindex σ.symm).equivalent_weightedSumSquares
  exact ((L.isSymm_localIntegralForm p).equivalent_iff_toQuadraticMap_equivalent
    (M.isSymm_localIntegralForm p)).mpr (hL_quad.trans (hdiag.trans hM_quad.symm))

/-- In any commutative group, if `∏ i, u i * ∏ i, v i` is a square and every positive-level fiber
`{i | k i = m}` (`m > 0`) has square product, then the `k i = 0` fiber also has square product. -/
private theorem isSquare_prod_filter_eq_zero_of_isSquare_prod {G ι : Type*} [CommGroup G]
    [Fintype ι] (k : ι → ℕ) (u v : ι → G)
    (hfull : IsSquare ((∏ i, u i) * ∏ i, v i))
    (hpos : ∀ m, 0 < m → IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v i)) :
    IsSquare ((∏ i with k i = 0, u i) * ∏ i with k i = 0, v i) := by
  let P : Finset ℕ := (Finset.univ.image k).erase 0
  have hsplit (w : ι → G) :
      ∏ i, w i = (∏ i with k i = 0, w i) * ∏ m ∈ P, ∏ i with k i = m, w i := by
    have hpart := (Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (g := k) (t := insert 0 P)
      (fun i _ ↦ by
        by_cases hk0 : k i = 0
        · simp [hk0]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hk0, Finset.mem_image_of_mem k (Finset.mem_univ i)⟩))
      w).symm
    rw [hpart, Finset.prod_insert (Finset.notMem_erase 0 _)]
  have hP_sq : IsSquare (∏ m ∈ P, ((∏ i with k i = m, u i) * ∏ i with k i = m, v i)) :=
    Finset.prod_induction _ IsSquare (fun _ _ ha hb ↦ ha.mul hb) IsSquare.one
      fun m hm ↦ hpos m (Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hm))
  rw [hsplit u, hsplit v] at hfull
  have hrearr : ((∏ i with k i = 0, u i) * ∏ m ∈ P, ∏ i with k i = m, u i) *
      ((∏ i with k i = 0, v i) * ∏ m ∈ P, ∏ i with k i = m, v i) =
      ((∏ i with k i = 0, u i) * ∏ i with k i = 0, v i) *
        ∏ m ∈ P, ((∏ i with k i = m, u i) * ∏ i with k i = m, v i) := by
    rw [Finset.prod_mul_distrib]
    ac_rfl
  rw [hrearr] at hfull
  simpa [mul_inv_cancel_right] using hfull.mul hP_sq.inv

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

/-- **Odd-prime local classification by the discriminant bilinear module.** Let `p` be an odd prime
and let `L` and `M` be nondegenerate integral lattices. Their localized integral forms over `ℤ_p`
are isometric if and only if `L` and `M` have the same rank, the product of their signed
determinants is a square in `ℤ_p`, and the `p`-primary components of their discriminant bilinear
modules are isometric. -/
theorem localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule
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
    obtain ⟨dL, hdL⟩ := exists_unit_sq_mul_det_eq rfl hb hbu
    obtain ⟨dM, hdM⟩ := exists_unit_sq_mul_det_eq hrank.symm hc hcv
    have hsum_eq : ∑ j, l j = ∑ i, k i :=
      (Equiv.sum_comp (σ : Fin _ ≃ Fin _) l).symm.trans (Finset.sum_congr rfl fun i _ ↦ hσ i)
    have hprod_v : ∏ j, (v j : ℤ_[p]) = ∏ i, (v (σ i) : ℤ_[p]) :=
      (Equiv.prod_comp (σ : Fin _ ≃ Fin _) fun j ↦ (v j : ℤ_[p])).symm
    have hfull : IsSquare ((∏ i, u i) * ∏ i, v (σ i)) := by
      rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod,
        ← PadicInt.isSquare_mul_sq_iff
          (pow_ne_zero (∑ i, k i) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))]
      obtain ⟨z, hz⟩ := hsq
      refine ⟨z * dL * dM, ?_⟩
      have hmul := congrArg₂ (· * ·) hdL hdM
      rw [hsum_eq, hprod_v] at hmul
      rw [sq]
      linear_combination -hmul + (dL : ℤ_[p]) ^ 2 * (dM : ℤ_[p]) ^ 2 * hz
    have hzero := isSquare_prod_filter_eq_zero_of_isSquare_prod k u (fun i ↦ v (σ i)) hfull hpos
    exact localIntegralForm_equivalent_of_forall_fiber hp hb hc hbu hcv σ hσ fun m ↦ by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact hzero
      · exact hpos m hm

/-- Unit-square determinant formulation of
`localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule`. -/
theorem localIntegralForm_equivalent_iff_exists_unit_sq_and_discriminantBilinearModule
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
    refine (L.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule M hp).mpr
      ⟨hrank, ?_, hdisc⟩
    refine ⟨(u : ℤ_[p]) * (M.determinant : ℤ_[p]), ?_⟩
    rw [hu]
    ring

/-- **Odd-prime local classification for even lattices.** For even nondegenerate lattices `L` and
`M` and an odd prime `p`, `L_p ≃ M_p` if and only if `rank L = rank M`, `det L · det M` is a square
in `ℤ_p`, and the `p`-primary components of their discriminant quadratic modules are isometric. -/
theorem localIntegralForm_equivalent_iff_isSquare_and_discriminantQuadraticModule
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
  have hodd_L :=
    (L.discriminantQuadraticModule hL).odd_natCard_restrict_primaryComponent Fact.out hp
  rw [L.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule M hp,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_L,
    FiniteQuadraticModule.restrict_toFiniteBilinearModule,
    FiniteQuadraticModule.restrict_toFiniteBilinearModule,
    L.discriminantQuadraticModule_toFiniteBilinearModule hL,
    M.discriminantQuadraticModule_toFiniteBilinearModule hM]

/-! ### Minimal-rank uniqueness at odd primes (Nikulin Theorem 1.9.1) -/

/-- **Uniqueness of minimal-rank `p`-adic localizations at odd primes (Nikulin, Theorem 1.9.1).**
If `p` is an odd prime and both `L` and `M` achieve the minimal rank
`finrank ℤ L = AddGroup.rank (A_L)_p` and `finrank ℤ M = AddGroup.rank (A_M)_p`, then `L_p` and
`M_p` are isometric if and only if the `p`-primary components of their discriminant bilinear
modules are isometric; neither equal rank nor a determinant hypothesis needs to be supplied
separately. -/
theorem localIntegralForm_equivalent_iff_of_finrank_eq_rank
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hLrank : finrank ℤ L = AddGroup.rank (primaryComponent L.DiscriminantGroup p))
    (hMrank : finrank ℤ M = AddGroup.rank (primaryComponent M.DiscriminantGroup p)) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      Nonempty (FiniteBilinearModule.Isometry
        (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
        (M.discriminantBilinearModule.restrict
          (primaryComponent M.discriminantBilinearModule p))) := by
  classical
  refine ⟨fun h ↦ h.map primaryDiscriminantBilinearIsometry, fun hdisc ↦ ?_⟩
  obtain ⟨fLM⟩ := hdisc
  have hrank_eq : AddGroup.rank (primaryComponent L.DiscriminantGroup p) =
      AddGroup.rank (primaryComponent M.DiscriminantGroup p) := by
    rw [AddGroup.rank_eq_spanFinrank_top, AddGroup.rank_eq_spanFinrank_top]
    exact Submodule.spanFinrank_eq_of_equiv fLM.toAddEquiv.toIntLinearEquiv
  have hrank : finrank ℤ L = finrank ℤ M := hLrank.trans (hrank_eq.trans hMrank.symm)
  obtain ⟨b, u, k, hb, hbu⟩ :=
    L.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp (rfl : finrank ℤ L = _)
  obtain ⟨c, v, l, hc, hcv⟩ :=
    M.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp hrank.symm
  obtain ⟨σ, hσ, hpos⟩ :=
    exists_perm_and_isSquare_pos_of_isometry_primaryComponent hp hb hc hbu hcv ⟨fLM⟩
  -- Minimal rank forces every exponent `k i` to be nonzero, so the `m = 0` fiber is empty.
  have hk_card : #{i : Fin (finrank ℤ L) | k i ≠ 0} = finrank ℤ L := by
    rw [← L.rank_primaryComponent_discriminantGroup_eq_card_filter hb hbu, ← hLrank]
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

/-- Even-lattice counterpart of `localIntegralForm_equivalent_iff_of_finrank_eq_rank`. -/
theorem localIntegralForm_equivalent_iff_of_isEven_of_finrank_eq_rank
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hLrank : finrank ℤ L = AddGroup.rank (primaryComponent L.DiscriminantGroup p))
    (hMrank : finrank ℤ M = AddGroup.rank (primaryComponent M.DiscriminantGroup p)) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      Nonempty (FiniteQuadraticModule.Isometry
        ((L.discriminantQuadraticModule hL).restrict
          (primaryComponent (L.discriminantQuadraticModule hL) p))
        ((M.discriminantQuadraticModule hM).restrict
          (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  have hodd_L :=
    (L.discriminantQuadraticModule hL).odd_natCard_restrict_primaryComponent Fact.out hp
  rw [L.localIntegralForm_equivalent_iff_of_finrank_eq_rank M hp hLrank hMrank,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_L,
    FiniteQuadraticModule.restrict_toFiniteBilinearModule,
    FiniteQuadraticModule.restrict_toFiniteBilinearModule,
    L.discriminantQuadraticModule_toFiniteBilinearModule hL,
    M.discriminantQuadraticModule_toFiniteBilinearModule hM]

end TauCeti.IntegralLattice
