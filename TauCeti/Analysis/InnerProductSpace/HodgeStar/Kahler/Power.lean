/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.DegreeTwo
import TauCeti.Algebra.BigOperators.Ring.SquareZero
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex
import TauCeti.Data.Fin.StrictMono
import TauCeti.Geometry.Symplectic.Finrank

/-!
# Normalized exterior powers of the Kähler form

For a finite-dimensional real inner product space `V` with an almost complex structure `J`, the
normalized `r`-th Kähler power (power index `r`, form degree `2 * r`) is defined via
`TauCeti.alternatingFormEquiv` and `exteriorPower.pow` as
`J.kahlerPowerForm r := (r!)⁻¹ • alternatingFormEquiv V (2 * r) (exteriorPower.pow J.kahlerForm r)`.

Specializing `J` to multiplication by `i` (`AlmostComplexStructure.ofComplexModule E`) defines
`TauCeti.kahlerPowerForm E r` on any finite-dimensional Hermitian vector space `E`.

This file establishes the evaluation, wedge recurrence, dimension vanishing, naturality under
complex linear isometries, adapted-frame evaluation (`= 1`), and Hilbert norm `√(n choose r)` for
normalized Kähler powers in every power index `r`.

## Main definitions

* `TauCeti.AlmostComplexStructure.kahlerPowerForm`: the normalized `r`-th Kähler power `ωʳ / r!`
  (form degree `2 * r`) of an almost complex structure `J`.
* `TauCeti.kahlerPowerForm`: the normalized `r`-th Kähler power `ωʳ / r!` (form degree `2 * r`) on
  a finite-dimensional Hermitian vector space.

## Main results

* `TauCeti.AlmostComplexStructure.kahlerPowerForm_apply`, `kahlerPowerForm_def`,
  `alternatingFormEquiv_symm_kahlerPowerForm`, `kahlerPowerForm_zero`, `kahlerPowerForm_one`,
  `kahlerPowerForm_succ`, `kahlerPowerForm_eq_zero_of_finrank_lt`,
  `kahlerPowerForm_comp_linearIsometry`, `kahlerPowerForm_apply_of_adapted`, and
  `sqrt_alternatingFormInner_kahlerPowerForm`.
* `TauCeti.kahlerPowerForm_apply`, `kahlerPowerForm_def`,
  `alternatingFormEquiv_symm_kahlerPowerForm`, `kahlerPowerForm_zero`, `kahlerPowerForm_one`,
  `kahlerPowerForm_succ`, `kahlerPowerForm_eq_zero_of_finrank_lt`,
  `kahlerPowerForm_comp_linearIsometry`, `kahlerPowerForm_complexToRealFamily`, and
  `sqrt_alternatingFormInner_kahlerPowerForm`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), §II.6.
* H. Federer, *Geometric Measure Theory*, Springer (1969), §1.8.2.
-/

public section

noncomputable section

open Module exteriorPower
open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti

namespace AlmostComplexStructure

section KahlerPower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The normalized `r`-th Kähler power `ωʳ / r!` (power index `r`, form degree `2 * r`) of an
almost complex structure `J` on a finite-dimensional real inner product space, as a continuous
alternating `2r`-form. -/
def kahlerPowerForm (J : AlmostComplexStructure V) (r : ℕ) : V [⋀^Fin (2 * r)]→L[ℝ] ℝ :=
  (r.factorial : ℝ)⁻¹ • alternatingFormEquiv V (2 * r) (exteriorPower.pow J.kahlerForm r)

/-- Unfolding lemma for `kahlerPowerForm` in terms of `exteriorPower.pow`. -/
theorem kahlerPowerForm_def (J : AlmostComplexStructure V) (r : ℕ) :
    J.kahlerPowerForm r =
      (r.factorial : ℝ)⁻¹ • alternatingFormEquiv V (2 * r) (exteriorPower.pow J.kahlerForm r) := by
  rw [kahlerPowerForm]

/-- Evaluation formula for `AlmostComplexStructure.kahlerPowerForm` on an arbitrary `2r`-frame. -/
theorem kahlerPowerForm_apply (J : AlmostComplexStructure V) (r : ℕ) (v : Fin (2 * r) → V) :
    J.kahlerPowerForm r v =
      ⟪(r.factorial : ℝ)⁻¹ • exteriorPower.pow J.kahlerForm r, ιMulti ℝ (2 * r) v⟫ := by
  rw [kahlerPowerForm, ContinuousAlternatingMap.smul_apply, alternatingFormEquiv_apply,
    real_inner_smul_left, smul_eq_mul]

/-- Under the Riesz identification `alternatingFormEquiv`, the normalized Kähler power
`J.kahlerPowerForm r` corresponds to `(r!)⁻¹ • exteriorPower.pow J.kahlerForm r`. -/
@[simp]
theorem alternatingFormEquiv_symm_kahlerPowerForm (J : AlmostComplexStructure V) (r : ℕ) :
    (alternatingFormEquiv V (2 * r)).symm (J.kahlerPowerForm r) =
      (r.factorial : ℝ)⁻¹ • exteriorPower.pow J.kahlerForm r := by
  rw [kahlerPowerForm, map_smul, LinearEquiv.symm_apply_apply]

/-- For power index `r = 0` (form degree `0`), `ω⁰ / 0!` is the constant form `1`. -/
@[simp]
theorem kahlerPowerForm_zero (J : AlmostComplexStructure V) :
    J.kahlerPowerForm 0 = ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) 1 := by
  rw [kahlerPowerForm, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  exact alternatingFormEquiv_pow_zero J.kahlerForm

/-- For power index `r = 1` (form degree `2`), `ω¹ / 1!` is the alternating two-form of
`J.kahlerForm`. -/
@[simp]
theorem kahlerPowerForm_one (J : AlmostComplexStructure V) :
    J.kahlerPowerForm 1 = alternatingFormEquiv V 2 J.kahlerForm := by
  rw [kahlerPowerForm, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  congr 1
  exact Subtype.ext (by simp)

/-- Wedge recurrence for normalized Kähler powers:
`ω^(r+1) / (r+1)! = (r + 1)⁻¹ • (ωʳ / r!) ∧ ω`. -/
theorem kahlerPowerForm_succ (J : AlmostComplexStructure V) (r : ℕ) :
    J.kahlerPowerForm (r + 1) =
      ((r + 1 : ℕ) : ℝ)⁻¹ •
        (J.kahlerPowerForm r).wedge (alternatingFormEquiv V 2 J.kahlerForm) := by
  rw [kahlerPowerForm, alternatingFormEquiv_pow_succ, kahlerPowerForm,
    ContinuousAlternatingMap.wedge_smul_left, smul_smul, Nat.factorial_succ, Nat.cast_mul,
    mul_inv]

/-- Normalized Kähler powers vanish whenever the form degree exceeds the real dimension
(`2 * r > finrank ℝ V`). -/
theorem kahlerPowerForm_eq_zero_of_finrank_lt (J : AlmostComplexStructure V) {r : ℕ}
    (hr : finrank ℝ V < 2 * r) : J.kahlerPowerForm r = 0 := by
  rw [kahlerPowerForm,
    exteriorPower.eq_zero_of_finrank_lt (2 * r) hr (exteriorPower.pow J.kahlerForm r),
    map_zero, smul_zero]

/-- Pullback of `J.kahlerPowerForm r` along a continuous linear map `L : W →L[ℝ] V` when the
degree-two form pulls back to `alternatingFormEquiv W 2 B`. -/
theorem kahlerPowerForm_compContinuousLinearMap {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (J : AlmostComplexStructure V)
    (L : W →L[ℝ] V) (B : ⋀[ℝ]^2 W)
    (h2 : (alternatingFormEquiv V 2 J.kahlerForm).compContinuousLinearMap L =
      alternatingFormEquiv W 2 B) (r : ℕ) :
    (J.kahlerPowerForm r).compContinuousLinearMap L =
      (r.factorial : ℝ)⁻¹ • alternatingFormEquiv W (2 * r) (exteriorPower.pow B r) := by
  rw [kahlerPowerForm, ← ContinuousAlternatingMap.compContinuousLinearMapₗ_apply, map_smul,
    ContinuousAlternatingMap.compContinuousLinearMapₗ_apply,
    alternatingFormEquiv_pow_compContinuousLinearMap L B J.kahlerForm h2 r]

/-- Naturality of `kahlerPowerForm` under complex-linear isometric embeddings between
finite-dimensional real inner product spaces with almost complex structures. -/
theorem kahlerPowerForm_comp_linearIsometry {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    (f : V →ₗᵢ[ℝ] W) (hf : ∀ v, f (J v) = J' (f v)) (r : ℕ) :
    (J'.kahlerPowerForm r).compContinuousLinearMap f.toContinuousLinearMap =
      J.kahlerPowerForm r := by
  have h2 : (alternatingFormEquiv W 2 J'.kahlerForm).compContinuousLinearMap
      f.toContinuousLinearMap = alternatingFormEquiv V 2 J.kahlerForm := by
    ext v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    have hfv : (f.toContinuousLinearMap ∘ v) = ![f (v 0), f (v 1)] := by
      ext i; fin_cases i <;> rfl
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hfv, alternatingFormEquiv_apply,
      inner_kahlerForm_ιMulti_eq_inv_two_mul_sub, ← hf, ← hf, f.inner_map_map, f.inner_map_map,
      ← inner_kahlerForm_ιMulti_eq_inv_two_mul_sub, ← alternatingFormEquiv_apply, ← hv]
  exact kahlerPowerForm_compContinuousLinearMap J' f.toContinuousLinearMap J.kahlerForm h2 r

/-- The normalized Kähler power `ωʳ / r!` evaluates to `1` on every `J`-adapted orthonormal
`2r`-frame `(w₀, J w₀, …, w_{2r-2}, J w_{2r-2})`, without requiring `J` to be orthogonal outside
the span of `w`. -/
theorem kahlerPowerForm_apply_of_adapted {J : AlmostComplexStructure V}
    {r : ℕ} {w : Fin (2 * r) → V} (hw : Orthonormal ℝ w)
    (hadapt : ∀ j : Fin r, w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩)) :
    J.kahlerPowerForm r w = 1 := by
  let P : Submodule ℝ V := Submodule.span ℝ (Set.range w)
  let bP : OrthonormalBasis (Fin (2 * r)) ℝ P :=
    (Basis.span hw.linearIndependent).toOrthonormalBasis (by
      convert orthonormal_span hw
      simp [Basis.span_apply])
  have hbP_coe (i : Fin (2 * r)) : (bP i : V) = w i := by simp [bP, Basis.span_apply]
  have hJP : ∀ x ∈ P, J x ∈ P := fun x hx ↦ by
    have hx_repr : (∑ i, ⟪bP i, ⟨x, hx⟩⟫ • bP i : P).val = x :=
      congrArg Subtype.val (bP.sum_repr' ⟨x, hx⟩)
    rw [← hx_repr, Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨⟨j, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
    rw [Submodule.coe_smul, map_smul, hbP_coe]
    refine Submodule.smul_mem _ _ ?_
    rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1) with rfl | rfl
    · rw [complexRealIndexEquiv_zero, ← hadapt j]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [complexRealIndexEquiv_one, hadapt j, J.apply_apply]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨_, rfl⟩)
  let JP : AlmostComplexStructure P :=
    { toLinearMap := J.toLinearMap.restrict hJP
      square_neg := by ext x; exact J.apply_apply x.val }
  have hJP_adapt (j : Fin r) :
      bP ⟨2 * (j : ℕ) + 1, by omega⟩ = JP (bP ⟨2 * (j : ℕ), by omega⟩) :=
    Subtype.ext (by simpa [JP, hbP_coe] using hadapt j)
  have hJP_orth := inner_apply_apply_of_adapted (J := JP) bP hJP_adapt
  let FP : ⋀[ℝ]^2 P := (alternatingFormEquiv P 2).symm
    ((alternatingFormEquiv V 2 J.kahlerForm).compContinuousLinearMap P.subtypeL)
  have hFP_eq : FP = JP.kahlerForm := by
    refine exteriorPower.ext_inner_ιMulti_two fun x y ↦ ?_
    rw [← inner_twoVectorContraction_apply, inner_kahlerForm_ιMulti hJP_orth]
    have hcontr : ⟪twoVectorContraction FP x, y⟫ =
        ⟪twoVectorContraction J.kahlerForm x.val, y.val⟫ := by
      rw [twoVectorContraction_alternatingFormEquiv_symm_compContinuousLinearMap]
      simp
    rw [hcontr, inner_twoVectorContraction_apply, inner_kahlerForm_ιMulti_eq_inv_two_mul_sub]
    have hskew : ⟪J y.val, x.val⟫ = -⟪J x.val, y.val⟫ := by
      have := inner_apply_left hJP_orth y x
      simpa [JP, real_inner_comm] using this
    rw [hskew, Submodule.coe_inner]
    simp only [JP, LinearMap.restrict_apply]
    ring
  have hpow : (r.factorial : ℝ)⁻¹ • exteriorPower.pow FP r = ιMulti ℝ (2 * r) bP := by
    simpa only [one_smul, Finset.prod_const_one,
        ← hFP_eq.trans (kahlerForm_eq_sum_of_adapted bP hJP_adapt)] using
      exteriorPower.inv_factorial_smul_pow_sum_smul_ιMulti_two (fun _ : Fin r ↦ (1 : ℝ)) bP
  have hcomp : P.subtypeL ∘ bP = w := funext hbP_coe
  have heval := DFunLike.congr_fun
    (kahlerPowerForm_compContinuousLinearMap J P.subtypeL FP (LinearEquiv.apply_symm_apply _ _).symm
      r) (bP : Fin (2 * r) → P)
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hcomp,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, alternatingFormEquiv_apply,
    ← real_inner_smul_left, hpow, real_inner_self_eq_norm_sq, bP.orthonormal.norm_ιMulti,
    one_pow] at heval
  exact heval

private theorem noncommProd_adapted_eq_exteriorPowerBasis {n r : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ V) (s : Set.powersetCard (Fin n) r)
    (hcs : (s.val : Set (Fin n)).Pairwise (Function.onFun Commute fun k : Fin n ↦
      _root_.ExteriorAlgebra.ιMulti ℝ 2
        ![b ⟨2 * (k : ℕ), by omega⟩, b ⟨2 * (k : ℕ) + 1, by omega⟩])) :
    s.val.noncommProd (fun k : Fin n ↦
      _root_.ExteriorAlgebra.ιMulti ℝ 2
        ![b ⟨2 * (k : ℕ), by omega⟩, b ⟨2 * (k : ℕ) + 1, by omega⟩]) hcs =
      (b.exteriorPower (2 * r)
        (Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm s))) :
        _root_.ExteriorAlgebra ℝ V) := by
  let e : Fin r ↪o Fin n := Set.powersetCard.ofFinEmbEquiv.symm s
  have hB_coe : (b.exteriorPower (2 * r) (Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb e)) :
      _root_.ExteriorAlgebra ℝ V) =
      _root_.ExteriorAlgebra.ιMulti ℝ (2 * r) (b ∘ doubleOrderEmb e) := by
    have hBs : b.exteriorPower (2 * r) (Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb e)) =
        ιMulti ℝ (2 * r) (b ∘ Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb e))) := by
      rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.toBasis_exteriorPower, basis_apply,
        ιMulti_family, OrthonormalBasis.coe_toBasis]
    rw [hBs, ιMulti_apply_coe, Equiv.symm_apply_apply]
  have hs_eq : s.val = ((List.finRange r).map e).toFinset := by
    apply Finset.coe_injective
    rw [List.toFinset_map, List.toFinset_finRange, Fintype.coe_image_univ]
    dsimp only [e]
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.range_orderEmbOfFin s.val (Set.powersetCard.card_eq s)).symm
  have hnodup : ((List.finRange r).map e).Nodup := (List.nodup_finRange r).map e.injective
  have hprod := (Finset.noncommProd_congr hs_eq (fun _ _ ↦ rfl) hcs).trans
    (Finset.noncommProd_toFinset _ _ _ hnodup)
  rw [hprod, List.map_map, hB_coe]
  simpa only [Function.comp_def, doubleOrderEmb_even, doubleOrderEmb_odd, one_smul,
    Finset.prod_const_one] using
    TauCeti.ExteriorAlgebra.prod_map_finRange_smul_ιMulti_two
      (fun _ : Fin r ↦ (1 : ℝ)) (b ∘ doubleOrderEmb e)

private theorem kahlerPowerForm_symm_eq_sum_adapted {J : AlmostComplexStructure V} {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ V)
    (hb : ∀ j : Fin n, b ⟨2 * (j : ℕ) + 1, by omega⟩ = J (b ⟨2 * (j : ℕ), by omega⟩)) (r : ℕ) :
    (alternatingFormEquiv V (2 * r)).symm (J.kahlerPowerForm r) =
      ∑ s : Set.powersetCard (Fin n) r, b.exteriorPower (2 * r)
        (Set.powersetCard.ofFinEmbEquiv
          (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm s))) := by
  let x : Fin n → _root_.ExteriorAlgebra ℝ V := fun k ↦
    _root_.ExteriorAlgebra.ιMulti ℝ 2 ![b ⟨2 * (k : ℕ), by omega⟩, b ⟨2 * (k : ℕ) + 1, by omega⟩]
  have hcoe : (J.kahlerForm : _root_.ExteriorAlgebra ℝ V) = ∑ k : Fin n, x k := by
    rw [kahlerForm_eq_sum_of_adapted b hb]; simp [x]
  have hcomm : Pairwise (Function.onFun Commute x) := fun _ _ _ ↦ by
    simpa [x] using TauCeti.ExteriorAlgebra.commute_smul_ιMulti_two (1 : ℝ) 1
      (b ⟨2 * _, _⟩) (b ⟨2 * _ + 1, _⟩) (b ⟨2 * _, _⟩) (b ⟨2 * _ + 1, _⟩)
  have hsq : ∀ k ∈ (Finset.univ : Finset (Fin n)), x k * x k = 0 := fun k _ ↦ by
    simpa [x] using TauCeti.ExteriorAlgebra.smul_ιMulti_two_mul_self (1 : ℝ)
      (b ⟨2 * (k : ℕ), by omega⟩) (b ⟨2 * (k : ℕ) + 1, by omega⟩)
  rw [alternatingFormEquiv_symm_kahlerPowerForm]
  apply Subtype.ext
  rw [SetLike.val_smul, Submodule.coe_sum, exteriorPower.coe_pow]
  rw [hcoe, Finset.sum_pow_of_pairwise_commute_of_mul_self_eq_zero Finset.univ x hcomm hsq r,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero (R := ℝ).mpr (Nat.factorial_ne_zero r)), one_smul,
    ← Finset.sum_coe_sort ((Finset.univ : Finset (Fin n)).powersetCard r)]
  refine Finset.sum_bij
    (fun (s : ((Finset.univ : Finset (Fin n)).powersetCard r)) _ ↦
      Set.powersetCard.ofCard (Finset.mem_powersetCard.mp s.property).2)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun s₁ _ s₂ _ h ↦ Subtype.ext (by
      simpa [Set.powersetCard.ofCard] using congrArg Subtype.val h))
    (fun s _ ↦
      ⟨⟨s.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Set.powersetCard.card_eq s⟩⟩,
        Finset.mem_univ _, rfl⟩)
    (fun s _ ↦ noncommProd_adapted_eq_exteriorPowerBasis b
      (Set.powersetCard.ofCard (Finset.mem_powersetCard.mp s.property).2) _)

/-- **Hilbert norm of the normalized Kähler power**: for an orthogonal almost complex structure `J`
on a `2n`-dimensional real inner product space, the Hilbert norm `√⟨ωʳ / r!, ωʳ / r!⟩` equals
`√(n choose r)`. -/
theorem sqrt_alternatingFormInner_kahlerPowerForm {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) (r : ℕ) :
    √(alternatingFormInner V (2 * r) (J.kahlerPowerForm r) (J.kahlerPowerForm r)) =
      √((finrank ℝ V / 2).choose r) := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  have hdim : finrank ℝ V = 2 * n := by omega
  have hn_eq : finrank ℝ V / 2 = n := by omega
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) n hdim
  have hB_ite := orthonormal_iff_ite.mp (b.exteriorPower (2 * r)).orthonormal
  have hinj (s t : Set.powersetCard (Fin n) r) :
      Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm s)) =
        Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm t)) ↔
        s = t := by
    simp [doubleOrderEmb_injective.eq_iff]
  rw [ContinuousAlternatingMap.sqrt_alternatingFormInner_self,
    kahlerPowerForm_symm_eq_sum_adapted b hb r, hn_eq, norm_eq_sqrt_real_inner]
  congr 1
  rw [sum_inner]
  simp_rw [inner_sum, hB_ite, hinj]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end KahlerPower

end AlmostComplexStructure

section HermitianPower

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [InnerProductSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]

variable (E) in
/-- The normalized `r`-th Kähler power `ωʳ / r!` (power index `r`, form degree `2 * r`) on a
finite-dimensional Hermitian vector space `E`, as a real continuous alternating `2r`-form. -/
@[expose] def kahlerPowerForm (r : ℕ) : E [⋀^Fin (2 * r)]→L[ℝ] ℝ :=
  (AlmostComplexStructure.ofComplexModule E).kahlerPowerForm r

/-- Unfolding lemma for `TauCeti.kahlerPowerForm`. -/
theorem kahlerPowerForm_def (r : ℕ) :
    kahlerPowerForm E r = (r.factorial : ℝ)⁻¹ •
      alternatingFormEquiv E (2 * r)
        (exteriorPower.pow (AlmostComplexStructure.ofComplexModule E).kahlerForm r) :=
  AlmostComplexStructure.kahlerPowerForm_def _ r

/-- Evaluation formula for `TauCeti.kahlerPowerForm` on an arbitrary `2r`-frame. -/
theorem kahlerPowerForm_apply (r : ℕ) (v : Fin (2 * r) → E) :
    kahlerPowerForm E r v =
      ⟪(r.factorial : ℝ)⁻¹ •
          exteriorPower.pow (AlmostComplexStructure.ofComplexModule E).kahlerForm r,
        ιMulti ℝ (2 * r) v⟫ :=
  AlmostComplexStructure.kahlerPowerForm_apply _ r v

/-- Under the Riesz identification `alternatingFormEquiv`, `TauCeti.kahlerPowerForm E r`
corresponds to `(r!)⁻¹ • exteriorPower.pow (AlmostComplexStructure.ofComplexModule E).kahlerForm r`.
-/
@[simp]
theorem alternatingFormEquiv_symm_kahlerPowerForm (r : ℕ) :
    (alternatingFormEquiv E (2 * r)).symm (kahlerPowerForm E r) =
      (r.factorial : ℝ)⁻¹ •
        exteriorPower.pow (AlmostComplexStructure.ofComplexModule E).kahlerForm r :=
  AlmostComplexStructure.alternatingFormEquiv_symm_kahlerPowerForm _ r

/-- For power index `r = 0` (form degree `0`), `ω⁰ / 0!` is the constant form `1`. -/
@[simp]
theorem kahlerPowerForm_zero :
    kahlerPowerForm E 0 = ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1 :=
  AlmostComplexStructure.kahlerPowerForm_zero _

/-- For power index `r = 1` (form degree `2`), `ω¹ / 1!` is `TauCeti.kahlerTwoForm E`. -/
@[simp]
theorem kahlerPowerForm_one : kahlerPowerForm E 1 = kahlerTwoForm E := by
  rw [kahlerPowerForm, AlmostComplexStructure.kahlerPowerForm_one,
    alternatingFormEquiv_ofComplexModule_kahlerForm]

/-- Wedge recurrence for normalized Kähler powers on a Hermitian vector space:
`ω^(r+1) / (r+1)! = (r + 1)⁻¹ • (ωʳ / r!) ∧ ω`. -/
theorem kahlerPowerForm_succ (r : ℕ) :
    kahlerPowerForm E (r + 1) =
      ((r + 1 : ℕ) : ℝ)⁻¹ • (kahlerPowerForm E r).wedge (kahlerTwoForm E) := by
  rw [kahlerPowerForm, AlmostComplexStructure.kahlerPowerForm_succ,
    alternatingFormEquiv_ofComplexModule_kahlerForm, kahlerPowerForm]

/-- Normalized Kähler powers vanish whenever the power index exceeds the complex dimension
(`r > finrank ℂ E`, equivalently form degree `2 * r > finrank ℝ E`). -/
theorem kahlerPowerForm_eq_zero_of_finrank_lt {r : ℕ} (hr : finrank ℂ E < r) :
    kahlerPowerForm E r = 0 := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  refine AlmostComplexStructure.kahlerPowerForm_eq_zero_of_finrank_lt _ ?_
  rw [finrank_real_eq_two_mul_finrank_complex]
  omega

/-- Naturality of `TauCeti.kahlerPowerForm` under every complex linear isometry `f : E →ₗᵢ[ℂ] F`
(in particular, unitary invariance when `f : E ≃ₗᵢ[ℂ] E`). -/
theorem kahlerPowerForm_comp_linearIsometry (f : E →ₗᵢ[ℂ] F) (r : ℕ) :
    (kahlerPowerForm F r).compContinuousLinearMap (f.toContinuousLinearMap.restrictScalars ℝ) =
      kahlerPowerForm E r := by
  let fR : E →ₗᵢ[ℝ] F :=
    { toLinearMap := f.toLinearMap.restrictScalars ℝ
      norm_map' := f.norm_map }
  exact AlmostComplexStructure.kahlerPowerForm_comp_linearIsometry fR
    (fun v ↦ by
      rw [AlmostComplexStructure.ofComplexModule_apply,
        AlmostComplexStructure.ofComplexModule_apply]
      exact f.map_smul Complex.I v) r

/-- The normalized Kähler power `ωʳ / r!` evaluates to `1` on the real frame
`TauCeti.complexToRealFamily u` of every complex-orthonormal family `u : Fin r → E`. -/
theorem kahlerPowerForm_complexToRealFamily {r : ℕ} {u : Fin r → E} (hu : Orthonormal ℂ u) :
    kahlerPowerForm E r (complexToRealFamily u) = 1 :=
  AlmostComplexStructure.kahlerPowerForm_apply_of_adapted
    (orthonormal_complexToRealFamily hu) (complexToRealFamily_odd_eq_ofComplexModule u)

/-- **Hilbert norm of the normalized Kähler power**:
`√⟨ωʳ / r!, ωʳ / r!⟩ = √((finrank ℂ E).choose r)`. -/
theorem sqrt_alternatingFormInner_kahlerPowerForm (r : ℕ) :
    √(alternatingFormInner E (2 * r) (kahlerPowerForm E r) (kahlerPowerForm E r)) =
      √((finrank ℂ E).choose r) := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  rw [kahlerPowerForm, AlmostComplexStructure.sqrt_alternatingFormInner_kahlerPowerForm
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule r,
    finrank_real_eq_two_mul_finrank_complex, Nat.mul_div_right _ (by decide : 0 < 2)]

end HermitianPower

end TauCeti
