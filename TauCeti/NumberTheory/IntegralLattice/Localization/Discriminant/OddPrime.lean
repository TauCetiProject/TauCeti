/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Rank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.Algebra.Group.Even
import TauCeti.Data.Fintype.Fiber
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Refinement
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal.Basic
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SquareClasses
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

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
square class `∏_{kᵢ = m} uᵢ` over `ℤ_p`. When neither diagonal Jordan form has a unimodular
summand `kᵢ = 0`, an isometry of the associated orthogonal sums of odd cyclic generators already
forces the two `ℤ_p`-bilinear forms to be equivalent
(`LinearMap.BilinForm.equivalent_of_iIsOrtho_of_isometry_pi_oddCyclic`). Otherwise, the unimodular
constituent `m = 0` is invisible to `(A_L)_p`: its rank is recovered from `rank L` by subtracting
the positive-scale counts, and its unit determinant square class is recovered from the `p`-adic
square class of `det L` once the positive-scale contributions are divided out.

At odd order, a bilinear isometry between finite quadratic modules automatically preserves the
quadratic refinement
(`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`), so the odd-prime
classification takes the same form for arbitrary nondegenerate lattices via `b_L` and for even
nondegenerate lattices via `q_L`.

## Main results

* `LinearMap.BilinForm.equivalent_of_iIsOrtho_of_forall_fiber` and
  `LinearMap.BilinForm.equivalent_of_iIsOrtho_of_isometry_pi_oddCyclic`: standalone odd-prime
  uniqueness over `ℤ_p` for finite free diagonal Jordan forms, without reference to a global
  lattice.
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

/-! ### Standalone odd-prime uniqueness over `ℤ_p` -/

section LocalForms

private theorem isCoprime_of_dvd_unit_sub {p : ℕ} [Fact p.Prime] {u : ℤ_[p]ˣ} {a : ℤ}
    (ha : (p : ℤ_[p]) ∣ (u : ℤ_[p]) - a) : IsCoprime (p : ℤ) a := by
  have hmod : PadicInt.toZMod (u : ℤ_[p]) = (a : ZMod p) := by
    simpa only [map_intCast] using (PadicInt.toZMod_eq_iff_dvd_sub (u : ℤ_[p]) a).mpr ha
  have hne : (a : ZMod p) ≠ 0 :=
    hmod ▸ (PadicInt.isUnit_iff_toZMod_ne_zero (u : ℤ_[p])).mp u.isUnit
  have hndvd : ¬ (p : ℤ) ∣ a := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd.mpr hndvd

private theorem forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic
    {p : ℕ} [Fact p.Prime] {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hp_odd : Odd p) {θ : ι → ℤ} {η : κ → ℤ}
    (hθ : ∀ i, (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i)
    (hη : ∀ j, (p : ℤ_[p]) ∣ (v j : ℤ_[p]) - η j)
    (hdisc : Nonempty (TauCeti.FiniteBilinearModule.Isometry
      (TauCeti.FiniteQuadraticModule.pi fun i ↦
        TauCeti.FiniteQuadraticModule.oddCyclic (p ^ k i) hp_odd.pow (θ i)).toFiniteBilinearModule
      (TauCeti.FiniteQuadraticModule.pi fun j ↦
        TauCeti.FiniteQuadraticModule.oddCyclic (p ^ l j) hp_odd.pow
          (η j)).toFiniteBilinearModule)) :
    ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m} ∧
      IsSquare ((∏ i with k i = m, u i) * ∏ j with l j = m, v j) := by
  classical
  have hp : p ≠ 2 := by
    rintro rfl
    exact absurd hp_odd (by decide)
  have hodd_card : Odd (Nat.card (TauCeti.FiniteQuadraticModule.pi fun i ↦
      TauCeti.FiniteQuadraticModule.oddCyclic (p ^ k i) hp_odd.pow (θ i))) := by
    rw [Nat.card_pi]
    exact Finset.prod_induction _ Odd (fun _ _ ha hb ↦ ha.mul hb) odd_one fun i _ ↦ by
      rw [TauCeti.FiniteQuadraticModule.natCard_oddCyclic]
      exact hp_odd.pow
  have hquad : Nonempty (TauCeti.FiniteQuadraticModule.Isometry
      (TauCeti.FiniteQuadraticModule.pi fun i ↦
        TauCeti.FiniteQuadraticModule.oddCyclic (p ^ k i) hp_odd.pow (θ i))
      (TauCeti.FiniteQuadraticModule.pi fun j ↦
        TauCeti.FiniteQuadraticModule.oddCyclic (p ^ l j) hp_odd.pow (η j))) :=
    (TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd_card).mpr
      hdisc
  have hclass := (TauCeti.FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff hp_odd k l
    (fun i ↦ isCoprime_of_dvd_unit_sub (hθ i))
    (fun j ↦ isCoprime_of_dvd_unit_sub (hη j))).mp hquad
  intro m hm
  refine ⟨(hclass m hm).1, ?_⟩
  rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod]
  exact (TauCeti.PadicInt.isSquare_prod_mul_prod_iff_legendreSym_eq hp
    {i : ι | k i = m} {j : κ | l j = m}
    (fun i ↦ (u i : ℤ_[p])) (fun j ↦ (v j : ℤ_[p])) θ η
    (fun i _ ↦ (u i).isUnit) (fun j _ ↦ (v j).isUnit)
    (fun i _ ↦ hθ i) (fun j _ ↦ hη j)).mpr (hclass m hm).2

end LocalForms

namespace LinearMap.BilinForm

/-- **Fiberwise equivalence of odd-prime `ℤ_p`-bilinear forms.** Once two diagonal Jordan forms
over `ℤ_p` (`p ≠ 2`) match along `σ : ι ≃ κ` and agree in square class on every scale fiber `m`,
the bilinear forms are equivalent over `ℤ_p`. -/
theorem equivalent_of_iIsOrtho_of_forall_fiber {p : ℕ} [Fact p.Prime]
    {P₁ P₂ ι κ : Type*} [AddCommGroup P₁] [Module ℤ_[p] P₁]
    [AddCommGroup P₂] [Module ℤ_[p] P₂] [Fintype ι]
    (B₁ : LinearMap.BilinForm ℤ_[p] P₁) (B₂ : LinearMap.BilinForm ℤ_[p] P₂) (hp : p ≠ 2)
    {b : Basis ι ℤ_[p] P₁} {c : Basis κ ℤ_[p] P₂}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : B₁.iIsOrtho b) (hc : B₂.iIsOrtho c)
    (hbu : ∀ i, B₁ (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hcv : ∀ j, B₂ (c j) (c j) = v j * (p : ℤ_[p]) ^ l j)
    (σ : ι ≃ κ) (hσ : ∀ i, l (σ i) = k i)
    (hfiber : ∀ m : ℕ, IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v (σ i))) :
    B₁.Equivalent B₂ := by
  classical
  let := (PadicInt.isUnit_two hp).invertible
  have hdiag := TauCeti.equivalent_weightedSumSquares_mul_of_forall_fiber_of_isUnit_two
    (PadicInt.isUnit_two hp) k (fun m ↦ (p : ℤ_[p]) ^ m) u (fun i ↦ v (σ i)) hfiber
  have h1_quad : B₁.toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p] fun i ↦ (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
    simpa only [hbu] using hb.equivalent_weightedSumSquares
  have h2_quad : B₂.toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℤ_[p] fun i ↦ (v (σ i) : ℤ_[p]) * (p : ℤ_[p]) ^ k i) := by
    simpa only [Basis.reindex_apply, Equiv.symm_symm, hcv, hσ] using
      (hc.reindex σ.symm).equivalent_weightedSumSquares
  exact (hb.isSymm.equivalent_iff_toQuadraticMap_equivalent
    hc.isSymm (PadicInt.isUnit_two hp).mem_nonZeroDivisors).mpr
    (h1_quad.trans (hdiag.trans h2_quad.symm))

/-- **Minimal-rank uniqueness over `ℤ_p` at an odd prime.** Let `p` be an odd prime and let
`B₁` and `B₂` be `ℤ_p`-bilinear forms presented in diagonal Jordan bases `b` and `c` with
`B₁ (b i) (b i) = uᵢ p^{kᵢ}` (`kᵢ ≠ 0`) and `B₂ (c j) (c j) = vⱼ p^{lⱼ}` (`lⱼ ≠ 0`). If the
corresponding orthogonal sums of odd cyclic generators for integer lifts `θᵢ ≡ uᵢ (mod p)` and
`ηⱼ ≡ vⱼ (mod p)` are bilinearly isometric, then `B₁` and `B₂` are equivalent over `ℤ_p`. -/
theorem equivalent_of_iIsOrtho_of_isometry_pi_oddCyclic {p : ℕ} [Fact p.Prime]
    {P₁ P₂ ι κ : Type*} [AddCommGroup P₁] [Module ℤ_[p] P₁]
    [AddCommGroup P₂] [Module ℤ_[p] P₂] [Fintype ι] [Fintype κ]
    (B₁ : LinearMap.BilinForm ℤ_[p] P₁) (B₂ : LinearMap.BilinForm ℤ_[p] P₂)
    {b : Basis ι ℤ_[p] P₁} {c : Basis κ ℤ_[p] P₂}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : B₁.iIsOrtho b) (hc : B₂.iIsOrtho c)
    (hbu : ∀ i, B₁ (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hcv : ∀ j, B₂ (c j) (c j) = v j * (p : ℤ_[p]) ^ l j)
    (hk : ∀ i, k i ≠ 0) (hl : ∀ j, l j ≠ 0)
    (hp_odd : Odd p) {θ : ι → ℤ} {η : κ → ℤ}
    (hθ : ∀ i, (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i)
    (hη : ∀ j, (p : ℤ_[p]) ∣ (v j : ℤ_[p]) - η j)
    (hdisc : Nonempty (TauCeti.FiniteBilinearModule.Isometry
      (TauCeti.FiniteQuadraticModule.pi fun i ↦
        TauCeti.FiniteQuadraticModule.oddCyclic (p ^ k i) hp_odd.pow (θ i)).toFiniteBilinearModule
      (TauCeti.FiniteQuadraticModule.pi fun j ↦
        TauCeti.FiniteQuadraticModule.oddCyclic (p ^ l j) hp_odd.pow
          (η j)).toFiniteBilinearModule)) :
    B₁.Equivalent B₂ := by
  classical
  have hp : p ≠ 2 := by
    rintro rfl
    exact absurd hp_odd (by decide)
  have hpos := forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic hp_odd hθ hη hdisc
  obtain ⟨σ, hσ⟩ := Function.exists_equiv_of_occCount_eq (u := k) (v := l) fun m ↦ by
    obtain rfl | hm := eq_or_ne m 0
    · rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
      simp [hk, hl]
    · rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
      exact (hpos m (Nat.pos_of_ne_zero hm)).1
  have hσi : ∀ i, l (σ i) = k i := congrFun hσ
  refine B₁.equivalent_of_iIsOrtho_of_forall_fiber B₂ hp hb hc hbu hcv σ hσi fun m ↦ ?_
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · simp [hk]
  · have hprod_v : ∏ i with k i = m, v (σ i) = ∏ j with l j = m, v j := by
      rw [Finset.prod_filter, Finset.prod_filter]
      exact (Finset.prod_congr rfl fun i _ ↦ by simp [hσi i]).trans
        (Equiv.prod_comp σ fun j ↦ if l j = m then v j else 1)
    rw [hprod_v]
    exact (hpos m hm).2

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ### Assembling an integral `ℤ_p`-isometry from fiberwise unit-diagonal equivalences -/

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
  choose θL _ hθL_dvd using fun i ↦
    _root_.PadicInt.exists_int_isCoprime_and_pow_dvd_sub (u i).isUnit (k i)
  choose θM _ hθM_dvd using fun j ↦
    _root_.PadicInt.exists_int_isCoprime_and_pow_dvd_sub (v j).isUnit (l j)
  obtain ⟨fL⟩ := L.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu fun i ↦
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (k i) 1)).trans (hθL_dvd i)
  obtain ⟨fM⟩ := M.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hc hcv fun j ↦
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (l j) 1)).trans (hθM_dvd j)
  obtain ⟨fLM⟩ := hdisc
  have hpos := forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic
    (u := u) (v := v) (k := k) (l := l) (hp_odd := hp_odd)
    (fun i ↦ by simpa only [pow_one] using
      (pow_dvd_pow (p : ℤ_[p]) (le_max_right (k i) 1)).trans (hθL_dvd i))
    (fun j ↦ by simpa only [pow_one] using
      (pow_dvd_pow (p : ℤ_[p]) (le_max_right (l j) 1)).trans (hθM_dvd j))
    ⟨fL.trans (fLM.trans fM.symm)⟩
  obtain ⟨σ, hσ⟩ :=
    Function.exists_perm_of_occCount_eq_of_ne (u := k) (v := l) (z := 0) fun m hm ↦ by
      rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
      exact (hpos m (Nat.pos_of_ne_zero hm)).1
  have hσi : ∀ i, l (σ i) = k i := congrFun hσ
  refine ⟨σ, hσi, fun m hm ↦ ?_⟩
  have hprod_v : ∏ i with k i = m, v (σ i) = ∏ j with l j = m, v j := by
    rw [Finset.prod_filter, Finset.prod_filter]
    exact (Finset.prod_congr rfl fun i _ ↦ by simp [hσi i]).trans
      (Equiv.prod_comp (σ : Fin n ≃ Fin n) fun j ↦ if l j = m then v j else 1)
  rw [hprod_v]
  exact (hpos m hm).2

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
      L.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
        (rfl : finrank ℤ L = _)
    obtain ⟨c, v, l, hc, hcv⟩ :=
      M.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp M.form_nondegenerate
        hrank.symm
    obtain ⟨σ, hσ, hpos⟩ :=
      exists_perm_and_isSquare_pos_of_isometry_primaryComponent hp hb hc hbu hcv hdisc
    obtain ⟨dL, hdL⟩ := L.exists_unit_sq_mul_determinant_eq_prod_mul_pow hb hbu
    obtain ⟨dM, hdM⟩ := M.exists_unit_sq_mul_determinant_eq_prod_mul_pow hc hcv
    have hsum_eq : ∑ j, l j = ∑ i, k i :=
      (Equiv.sum_comp (σ : Fin _ ≃ Fin _) l).symm.trans (Finset.sum_congr rfl fun i _ ↦ hσ i)
    have hprod_v : ∏ j, (v j : ℤ_[p]) = ∏ i, (v (σ i) : ℤ_[p]) :=
      (Equiv.prod_comp (σ : Fin _ ≃ Fin _) fun j ↦ (v j : ℤ_[p])).symm
    have hfull : IsSquare ((∏ i, u i) * ∏ i, v (σ i)) := by
      rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod,
        ← TauCeti.IsIntegrallyClosed.isSquare_mul_sq_iff
          (pow_ne_zero (∑ i, k i) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))]
      obtain ⟨z, hz⟩ := hsq
      refine ⟨z * dL * dM, ?_⟩
      have hmul := congrArg₂ (· * ·) hdL hdM
      rw [hsum_eq, hprod_v] at hmul
      rw [sq]
      linear_combination -hmul + (dL : ℤ_[p]) ^ 2 * (dM : ℤ_[p]) ^ 2 * hz
    have hzero : IsSquare ((∏ i with k i = 0, u i) * ∏ i with k i = 0, v (σ i)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.univ.isSquare_prod_filter_of_isSquare_prod k (fun i ↦ u i * v (σ i)) 0
        (by rwa [Finset.prod_mul_distrib]) fun m hm ↦ ?_
      rw [Finset.prod_mul_distrib]
      exact hpos m (Nat.pos_of_ne_zero hm)
    exact (L.localIntegralForm p).equivalent_of_iIsOrtho_of_forall_fiber
      (M.localIntegralForm p) hp hb hc hbu hcv σ hσ fun m ↦ by
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
  rw [L.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule M hp,
    L.nonempty_isometry_restrict_discriminantQuadraticModule_primaryComponent_iff M hL hM
      ((Fact.out : p.Prime).odd_of_ne_two hp)]

/-! ### Minimal-rank uniqueness at odd primes (Nikulin Theorem 1.9.1) -/

private theorem ne_zero_of_finrank_eq_rank
    (L : IntegralLattice V) [L.IsNondegenerate] {p : ℕ} [Fact p.Prime]
    {b : Basis (Fin (finrank ℤ L)) ℤ_[p] (L.LocalCarrier p)} {u : Fin (finrank ℤ L) → ℤ_[p]ˣ}
    {k : Fin (finrank ℤ L) → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hLrank : finrank ℤ L = AddGroup.rank (primaryComponent L.DiscriminantGroup p))
    (i : Fin (finrank ℤ L)) : k i ≠ 0 := by
  classical
  have hk_card : #{j : Fin (finrank ℤ L) | k j ≠ 0} = finrank ℤ L := by
    rw [← L.rank_primaryComponent_discriminantGroup_eq_card_filter hb hbu, ← hLrank]
  have hk_all : ({j : Fin (finrank ℤ L) | k j ≠ 0} : Finset (Fin (finrank ℤ L))) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hk_card])
  have hi : i ∈ ({j : Fin (finrank ℤ L) | k j ≠ 0} : Finset (Fin (finrank ℤ L))) :=
    hk_all.symm ▸ Finset.mem_univ i
  exact (Finset.mem_filter.mp hi).2

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
  refine ⟨fun h ↦ h.map primaryDiscriminantBilinearIsometry, fun ⟨fLM⟩ ↦ ?_⟩
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨b, u, k, hb, hbu⟩ :=
    L.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
      (rfl : finrank ℤ L = _)
  obtain ⟨c, v, l, hc, hcv⟩ :=
    M.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp M.form_nondegenerate
      (rfl : finrank ℤ M = _)
  choose θL _ hθL_dvd using fun i ↦
    _root_.PadicInt.exists_int_isCoprime_and_pow_dvd_sub (u i).isUnit (k i)
  choose θM _ hθM_dvd using fun j ↦
    _root_.PadicInt.exists_int_isCoprime_and_pow_dvd_sub (v j).isUnit (l j)
  obtain ⟨fL⟩ := L.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu fun i ↦
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (k i) 1)).trans (hθL_dvd i)
  obtain ⟨fM⟩ := M.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hc hcv fun j ↦
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (l j) 1)).trans (hθM_dvd j)
  exact (L.localIntegralForm p).equivalent_of_iIsOrtho_of_isometry_pi_oddCyclic
    (M.localIntegralForm p) hb hc hbu hcv
    (ne_zero_of_finrank_eq_rank L hb hbu hLrank)
    (ne_zero_of_finrank_eq_rank M hc hcv hMrank)
    (hp_odd := hp_odd) (θ := θL) (η := θM)
    (fun i ↦ by simpa only [pow_one] using
      (pow_dvd_pow (p : ℤ_[p]) (le_max_right (k i) 1)).trans (hθL_dvd i))
    (fun j ↦ by simpa only [pow_one] using
      (pow_dvd_pow (p : ℤ_[p]) (le_max_right (l j) 1)).trans (hθM_dvd j))
    ⟨fL.trans (fLM.trans fM.symm)⟩

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
  rw [L.localIntegralForm_equivalent_iff_of_finrank_eq_rank M hp hLrank hMrank,
    L.nonempty_isometry_restrict_discriminantQuadraticModule_primaryComponent_iff M hL hM
      ((Fact.out : p.Prime).odd_of_ne_two hp)]

end TauCeti.IntegralLattice
