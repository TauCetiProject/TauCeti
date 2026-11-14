/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Rank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Bilinear
public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.Algebra.Group.Primary.Generators
import TauCeti.Algebra.Module.SpanRank
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RatCast

/-!
# The `p`-primary discriminant form from a diagonal Jordan form

Let `L` be a nondegenerate integral lattice and `p` a prime. Whenever the localization
`L_p = ℤ_p ⊗[ℤ] L` has an orthogonal basis `b` with self-pairings `B(bᵢ, bᵢ) = uᵢ pᵏⁱ`, `uᵢ` a unit
of `ℤ_p`, the dual classes of `p^{-kᵢ} bᵢ` give an additive isomorphism
`∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p` (`TauCeti.IntegralLattice.piZModPowEquivPrimaryComponent`), so the generator
count of `(A_L)_p` is `#{i | kᵢ ≠ 0}` for every prime `p`.

At an odd prime `p`, every nondegenerate `L_p` admits such an orthogonal basis
(`TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow`). For integers
`θᵢ ≡ uᵢ (mod pᵏⁱ)`, this file identifies the `p`-primary component of the discriminant bilinear
form `b_L` with the orthogonal sum of Nikulin's odd cyclic generators:

```text
(A_L)_p ≅ ⊕ᵢ q_{θᵢ}^{(p)}(pᵏⁱ),
```

where `q_θ^{(p)}(pᵏ)` is the group `ℤ/pᵏ` with pairing `b(x, y) = θxy / pᵏ`. Summands with `kᵢ = 0`
are trivial, so only the non-unimodular Jordan constituents of `L_p` contribute. Orthogonal sums of
odd cyclic generators are classified by their exponents and the Legendre symbols of their
coefficients (`TauCeti.FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff`), which feeds the
classification of `L_p` at odd primes by its discriminant form (Nikulin, Corollaries 1.9.4 and
1.16.3).

## Main results

* `TauCeti.IntegralLattice.piZModPowEquivPrimaryComponent`: for any prime `p` and any orthogonal
  basis `b` of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ`, an additive equivalence
  `(∀ i, ZMod (p ^ k i)) ≃+ primaryComponent L.DiscriminantGroup p`.
* `TauCeti.IntegralLattice.spanFinrank_primaryComponent_discriminantGroup_eq_card_filter` and
  `TauCeti.IntegralLattice.rank_primaryComponent_discriminantGroup_eq_card_filter`: in such a
  diagonal basis, the generator count of `(A_L)_p` equals `#{i | kᵢ ≠ 0}`.
* `TauCeti.IntegralLattice.nonempty_isometry_pi_oddCyclic_primaryComponent`: at an odd prime, the
  `p`-primary component of the discriminant bilinear module of `L` is isometric to the orthogonal
  sum of the odd cyclic generators `q_{θᵢ}^{(p)}(pᵏⁱ)` read off a diagonal Jordan form of `L_p`.

## Implementation notes

The `p`-primary component of `A_L` is the discriminant group `(ℤ_p ⊗[ℤ] Lᵛ) / L_p` of the
localization (`TauCeti.IntegralLattice.primaryComponentEquivLocalDiscriminantGroup`). The dual of
`L_p` has the basis `p^{-kᵢ} bᵢ`, so the classes of these vectors generate that group, the class of
`p^{-kᵢ} bᵢ` is killed by `pᵏⁱ`, and `B(p^{-kᵢ} bᵢ, p^{-kⱼ} bⱼ) = δᵢⱼ uᵢ p^{-kᵢ}`. Representatives
in `Lᵛ` of these classes pair by rational numbers that differ from these values by `p`-adic
integers, and a rational number with `p`-power denominator that is a `p`-adic integer is an
integer (`Padic.addCircle_coe_eq_coe_of_eq_add_algebraMap`), so the classes pair to
`δᵢⱼ θᵢ / pᵏⁱ` in `ℚ/ℤ`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8 and
  Corollaries 1.9.4 and 1.16.3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module TensorProduct AddCommGroup Finset

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V} [L.IsNondegenerate]
  {p : ℕ} [Fact p.Prime] {ι : Type*} {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {u : ι → ℤ_[p]ˣ}
  {k : ι → ℕ}

/-! ### The dual basis vectors `p^{-kᵢ} bᵢ` -/

/-- For a diagonal Jordan form `B(bᵢ, bᵢ) = uᵢ pᵏⁱ`, the vector `p^{-kᵢ} bᵢ` of the completed
rational space lies in the localized dual. -/
private theorem exists_localizationDualToCompletion_eq
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) (i : ι) :
    ∃ y : L.LocalDualCarrier p, L.localizationDualToCompletion p y =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [← LinearMap.mem_range, range_localizationDualToCompletion,
    LinearMap.BilinForm.mem_dualSubmodule]
  rintro _ ⟨x, rfl⟩
  refine Submodule.mem_one.mpr ⟨b.repr x i * u i, ?_⟩
  rw [LinearMap.BilinForm.smul_left, completedRationalForm_localizationToCompletion,
    hb.apply_basis_left, hbu]
  simp only [map_mul, map_pow, map_natCast]
  field_simp

variable {y : ι → L.LocalDualCarrier p}

/-- The dual vector `p^{-kᵢ} bᵢ` pairs with `bⱼ` to `δᵢⱼ uᵢ`. -/
private theorem localDualPairingEquiv_basis [DecidableEq ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (i j : ι) :
    L.localDualPairingEquiv p (y i) (b j) = if i = j then (u i : ℤ_[p]) else 0 := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]
  rw [← completedRationalForm_localizationDualToCompletion, hy, LinearMap.BilinForm.smul_left,
    completedRationalForm_localizationToCompletion]
  split_ifs with hij
  · subst hij
    rw [hbu]
    simp only [map_mul, map_pow, map_natCast]
    field_simp
  · simp [LinearMap.BilinForm.iIsOrtho_def.mp hb i j hij]

private theorem localDualPairingEquiv_localCarrierToDual (x z : L.LocalCarrier p) :
    L.localDualPairingEquiv p (L.localCarrierToDual p x) z = L.localIntegralForm p x z := by
  apply FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]
  rw [← completedRationalForm_localizationDualToCompletion,
    localizationDualToCompletion_localCarrierToDual, completedRationalForm_localizationToCompletion]

omit [L.IsNondegenerate] in
/-- `pᵏⁱ` times the dual vector `p^{-kᵢ} bᵢ` is `bᵢ`. -/
private theorem pow_nsmul_eq_localCarrierToDual
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (i : ι) :
    p ^ k i • y i = L.localCarrierToDual p (b i) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply L.localizationDualToCompletion_injective p
  rw [map_nsmul, localizationDualToCompletion_localCarrierToDual, hy,
    ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ hp),
    one_smul]

/-- The classes of the dual vectors `p^{-kᵢ} bᵢ` generate the discriminant group of `L_p`. -/
private theorem exists_mk_eq_sum_nsmul [Fintype ι] (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (z : L.LocalDualCarrier p) :
    ∃ n : ι → ℕ, (Submodule.Quotient.mk z : L.LocalDiscriminantGroup p) =
      ∑ i, n i • Submodule.Quotient.mk (y i) := by
  classical
  -- The coordinates of `z` in the basis `p^{-kᵢ} bᵢ` are `B(z, bᵢ) uᵢ⁻¹`.
  set c : ι → ℤ_[p] := fun i ↦ L.localDualPairingEquiv p z (b i) * ↑(u i)⁻¹
  have hz : z = ∑ i, c i • y i := by
    apply (L.localDualPairingEquiv p).injective
    refine b.ext fun j ↦ ?_
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      localDualPairingEquiv_basis hb hbu hy, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, c]
    rw [mul_assoc, Units.inv_mul, mul_one]
  -- Reduce each coordinate modulo `pᵏⁱ`; the remainders contribute vectors of `L_p`.
  choose t ht using fun i ↦ Ideal.mem_span_singleton'.mp (PadicInt.appr_spec (k i) (c i))
  refine ⟨fun i ↦ (c i).appr (k i), ?_⟩
  have hc i : c i = ((c i).appr (k i) : ℤ_[p]) + t i * (p : ℤ_[p]) ^ k i := by
    rw [ht i, add_sub_cancel]
  rw [hz, ← Submodule.mkQ_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h0 : (Submodule.Quotient.mk ((p : ℤ_[p]) ^ k i • y i) : L.LocalDiscriminantGroup p) = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, pow_nsmul_eq_localCarrierToDual hy]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b i, rfl⟩
  rw [Submodule.mkQ_apply, hc i, add_smul, mul_smul, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul _ (t i), h0, smul_zero, add_zero, Nat.cast_smul_eq_nsmul,
    Submodule.Quotient.mk_smul]

/-- The completed pairing of the dual vectors `p^{-kᵢ} bᵢ` and `p^{-kⱼ} bⱼ` is `δᵢⱼ θᵢ / pᵏⁱ` up to
a `p`-adic integer, for `θᵢ ≡ uᵢ (mod pᵏⁱ)`. -/
private theorem exists_completedRationalForm_eq_add_algebraMap [DecidableEq ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i))
    {θ : ι → ℤ} (hθ : ∀ i, (p : ℤ_[p]) ^ k i ∣ u i - θ i) (i j : ι) :
    ∃ w : ℤ_[p], L.completedRationalForm p (L.localizationDualToCompletion p (y i))
        (L.localizationDualToCompletion p (y j)) =
      ((if i = j then θ i / p ^ k i else 0 : ℚ) : ℚ_[p]) + algebraMap ℤ_[p] ℚ_[p] w := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [hy j, map_smul, completedRationalForm_localizationDualToCompletion,
    localDualPairingEquiv_basis hb hbu hy, smul_eq_mul]
  split_ifs with hij
  · subst hij
    obtain ⟨t, ht⟩ := hθ i
    refine ⟨t, ?_⟩
    rw [sub_eq_iff_eq_add.mp ht]
    simp only [map_add, map_mul, map_pow, map_natCast, map_intCast]
    push_cast
    field_simp
    ring
  · exact ⟨0, by simp⟩

/-! ### The classes of the dual basis vectors in `A_L` -/

/-- The `p`-primary class of the dual vector `p^{-kᵢ} bᵢ` is killed by `pᵏⁱ`. -/
private theorem pow_nsmul_symm_mk_eq_zero
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (i : ι) :
    p ^ k i • (L.primaryComponentEquivLocalDiscriminantGroup p).symm
      (Submodule.Quotient.mk (y i)) = 0 := by
  rw [← map_nsmul, ← Submodule.Quotient.mk_smul, pow_nsmul_eq_localCarrierToDual hy,
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ (b i)), map_zero]

/-- The additive homomorphism `(cᵢ) ↦ ∑ᵢ cᵢ [p^{-kᵢ} bᵢ]` from `∏ᵢ ℤ/pᵏⁱ` to `(A_L)_p`. -/
private noncomputable def piZModPowHom [Fintype ι]
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) :
    (∀ i, ZMod (p ^ k i)) →+ primaryComponent L.DiscriminantGroup p :=
  haveI : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ∑ i, (ZMod.lift (p ^ k i) ⟨zmultiplesHom _
      ((L.primaryComponentEquivLocalDiscriminantGroup p).symm (Submodule.Quotient.mk (y i))), by
    rw [zmultiplesHom_apply, natCast_zsmul]
    exact pow_nsmul_symm_mk_eq_zero hy i⟩).comp
    (Pi.evalAddMonoidHom (fun i ↦ ZMod (p ^ k i)) i)

private theorem piZModPowHom_intCast [Fintype ι]
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (n : ι → ℤ) :
    piZModPowHom hy (fun i ↦ (n i : ZMod (p ^ k i))) =
      ∑ i, n i • (L.primaryComponentEquivLocalDiscriminantGroup p).symm
        (Submodule.Quotient.mk (y i)) := by
  have : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  simp [piZModPowHom, ZMod.lift_coe]

private theorem bijective_piZModPowHom [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) :
    Function.Bijective (piZModPowHom hy) := by
  classical
  have : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_, fun c ↦ ?_⟩
  · have hc_val : c = fun i ↦ (((c i).val : ℤ) : ZMod (p ^ k i)) :=
      funext fun i ↦ by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hc_val, piZModPowHom_intCast] at hc
    have hmk : (Submodule.Quotient.mk (∑ i, (c i).val • y i) : L.LocalDiscriminantGroup p) = 0 := by
      have hmap := congrArg (L.primaryComponentEquivLocalDiscriminantGroup p) hc
      rw [map_zero, map_sum] at hmap
      rw [← Submodule.mkQ_apply, map_sum]
      refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hmap
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, ← natCast_zsmul, map_zsmul,
        (L.primaryComponentEquivLocalDiscriminantGroup p).apply_symm_apply, natCast_zsmul]
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hmk
    ext j
    have hpair := congrArg (fun w ↦ L.localDualPairingEquiv p w (b j)) hx
    simp only [localDualPairingEquiv_localCarrierToDual, (L.isSymm_localIntegralForm p).eq x (b j),
      hb.apply_basis_left j x, hbu, map_sum, map_nsmul, LinearMap.sum_apply, LinearMap.smul_apply,
      localDualPairingEquiv_basis hb hbu hy, nsmul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hpair
    have hdvd : (p : ℤ_[p]) ^ k j ∣ ((c j).val : ℤ_[p]) := by
      refine ⟨b.repr x j, (u j).isUnit.mul_right_cancel ?_⟩
      linear_combination -hpair
    exact (ZMod.natCast_zmod_val (c j)) ▸
      (ZMod.natCast_eq_zero_iff (c j).val (p ^ k j)).mpr
        ((PadicInt.pow_p_dvd_natCast_iff _ _).mp hdvd)
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
      (L.primaryComponentEquivLocalDiscriminantGroup p c)
    obtain ⟨n, hn⟩ := exists_mk_eq_sum_nsmul hb hbu hy z
    refine ⟨fun i ↦ ((n i : ℤ) : ZMod (p ^ k i)),
      (L.primaryComponentEquivLocalDiscriminantGroup p).injective ?_⟩
    rw [piZModPowHom_intCast, map_sum, ← hz, hn]
    simp

/-- **Additive structure of `(A_L)_p` from a diagonal Jordan form.** For any prime `p` (including
`p = 2`) and any orthogonal basis `b` of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), the dual
classes of `p^{-kᵢ} bᵢ` give an additive isomorphism `∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p`. -/
noncomputable def piZModPowEquivPrimaryComponent [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    (∀ i, ZMod (p ^ k i)) ≃+ primaryComponent L.DiscriminantGroup p :=
  AddEquiv.ofBijective
    (piZModPowHom (fun i ↦ Classical.choose_spec (exists_localizationDualToCompletion_eq hb hbu i)))
    (bijective_piZModPowHom hb hbu
      (fun i ↦ Classical.choose_spec (exists_localizationDualToCompletion_eq hb hbu i)))

/-- **Generator count (`spanFinrank`) of `(A_L)_p` from a diagonal Jordan form.** For any prime `p`
and any orthogonal basis `b` of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), the least number of
generators of `(A_L)_p` over `ℤ` equals `#{i | kᵢ ≠ 0}`. -/
theorem spanFinrank_primaryComponent_discriminantGroup_eq_card_filter [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    (⊤ : Submodule ℤ (primaryComponent L.DiscriminantGroup p)).spanFinrank = #{i | k i ≠ 0} :=
  (Submodule.spanFinrank_eq_of_equiv
    (L.piZModPowEquivPrimaryComponent hb hbu).toIntLinearEquiv.symm).trans
    (AddCommGroup.spanFinrank_pi_zmod_pow k)

/-- **Generator count (`AddGroup.rank`) of `(A_L)_p` from a diagonal Jordan form.** For any prime
`p` and any orthogonal basis `b` of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), the rank of
`(A_L)_p` equals `#{i | kᵢ ≠ 0}`. -/
theorem rank_primaryComponent_discriminantGroup_eq_card_filter [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    AddGroup.rank (primaryComponent L.DiscriminantGroup p) = #{i | k i ≠ 0} := by
  rw [AddGroup.rank_eq_spanFinrank_top]
  exact L.spanFinrank_primaryComponent_discriminantGroup_eq_card_filter hb hbu

/-- The `p`-primary classes of the dual vectors `p^{-kᵢ} bᵢ` pair to `δᵢⱼ θᵢ / pᵏⁱ` in `ℚ/ℤ`. -/
private theorem discriminantPairing_symm_mk [DecidableEq ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i))
    {θ : ι → ℤ} (hθ : ∀ i, (p : ℤ_[p]) ^ k i ∣ u i - θ i) (i j : ι) :
    L.discriminantPairing
        ((L.primaryComponentEquivLocalDiscriminantGroup p).symm (Submodule.Quotient.mk (y i)) :
          L.DiscriminantGroup)
        ((L.primaryComponentEquivLocalDiscriminantGroup p).symm (Submodule.Quotient.mk (y j))) =
      ((if i = j then θ i / p ^ k i else 0 : ℚ) : AddCircle (1 : ℚ)) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _
    ((L.primaryComponentEquivLocalDiscriminantGroup p).symm (Submodule.Quotient.mk (y i)) :
      L.DiscriminantGroup)
  obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _
    ((L.primaryComponentEquivLocalDiscriminantGroup p).symm (Submodule.Quotient.mk (y j)) :
      L.DiscriminantGroup)
  obtain ⟨m, hm⟩ := exists_one_tmul_eq_add_localCarrierToDual hx
  obtain ⟨m', hm'⟩ := exists_one_tmul_eq_add_localCarrierToDual hx'
  obtain ⟨w, hw⟩ := exists_form_eq_completedRationalForm_add_algebraMap hm hm'
  obtain ⟨w', hw'⟩ := exists_completedRationalForm_eq_add_algebraMap hb hbu hy hθ i j
  -- `pᵏʲ` kills the class of `x'`, so `pᵏʲ B(x, x')` is an integer.
  have h0 : L.discriminantPairing (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk (p ^ k j • x')) = 0 := by
    rw [Submodule.Quotient.mk_smul, hx', ← AddSubgroup.coe_nsmul,
      pow_nsmul_symm_mk_eq_zero hy, AddSubgroup.coe_zero, map_zero]
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp ((L.discriminantPairing_mk_eq_zero_iff _ _).mp h0)
  rw [← hx, ← hx', discriminantPairing_mk]
  refine Padic.addCircle_coe_eq_coe_of_eq_add_algebraMap (k := k j)
    (n := n - if i = j then θ i else 0) ?_ (z := w + w') (by rw [hw, hw', map_add]; ring)
  rw [eq_intCast] at hn
  simp only [Submodule.coe_smul_of_tower, map_nsmul, nsmul_eq_mul, Nat.cast_pow] at hn
  split_ifs with hij
  · subst hij
    push_cast
    field_simp
    linear_combination -hn
  · push_cast
    linear_combination -hn

/-- Integer combinations of the classes of the dual vectors `p^{-kᵢ} bᵢ` pair like vectors of the
orthogonal sum of the cyclic forms `θᵢ xy / pᵏⁱ`. -/
private theorem discriminantPairing_sum_zsmul [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i))
    {θ : ι → ℤ} (hθ : ∀ i, (p : ℤ_[p]) ^ k i ∣ u i - θ i) (n n' : ι → ℤ) :
    L.discriminantPairing
        (∑ i, n i • (L.primaryComponentEquivLocalDiscriminantGroup p).symm
          (Submodule.Quotient.mk (y i)) : primaryComponent L.DiscriminantGroup p)
        (∑ i, n' i • (L.primaryComponentEquivLocalDiscriminantGroup p).symm
          (Submodule.Quotient.mk (y i)) : primaryComponent L.DiscriminantGroup p) =
      ∑ i, ((θ i * n i * n' i / p ^ k i : ℚ) : AddCircle (1 : ℚ)) := by
  classical
  simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul, map_sum, map_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply, discriminantPairing_symm_mk hb hbu hy hθ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp only [↓reduceIte, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  congr 1
  ring

/-! ### The `p`-primary discriminant form -/

/-- **The `p`-primary discriminant form from a diagonal Jordan form.** Let `p` be an odd prime and
let `b` be an orthogonal basis of the localization `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ`, `uᵢ` a unit
of `ℤ_p`. For integers `θᵢ ≡ uᵢ (mod pᵏⁱ)`, the `p`-primary component of the discriminant
bilinear module of `L` is isometric to the orthogonal sum of Nikulin's odd cyclic generators
`q_{θᵢ}^{(p)}(pᵏⁱ)`. -/
theorem nonempty_isometry_pi_oddCyclic_primaryComponent [Fintype ι] (hp : Odd p)
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    {θ : ι → ℤ} (hθ : ∀ i, (p : ℤ_[p]) ^ k i ∣ u i - θ i) :
    Nonempty (FiniteBilinearModule.Isometry
      (FiniteQuadraticModule.pi fun i ↦
        FiniteQuadraticModule.oddCyclic (p ^ k i) hp.pow (θ i)).toFiniteBilinearModule
      (L.discriminantBilinearModule.restrict
        (primaryComponent L.discriminantBilinearModule p))) := by
  let hy := fun i ↦ Classical.choose_spec (exists_localizationDualToCompletion_eq hb hbu i)
  have hcast (c : ∀ i, ZMod (p ^ k i)) : ∃ n : ι → ℤ, (fun i ↦ (n i : ZMod (p ^ k i))) = c :=
    ⟨fun i ↦ (c i).cast, funext fun i ↦ ZMod.intCast_zmod_cast _⟩
  refine ⟨{ toAddEquiv := L.piZModPowEquivPrimaryComponent hb hbu, map_pairing' := fun c c' ↦ ?_ }⟩
  obtain ⟨n, rfl⟩ := hcast c
  obtain ⟨n', rfl⟩ := hcast c'
  refine ((L.discriminantBilinearModule.restrict_pairing _ _ _).trans ?_).trans
    (FiniteQuadraticModule.pi_pairing _ _ _).symm
  refine (L.discriminantBilinearModule_pairing _ _).trans ?_
  have hL := discriminantPairing_sum_zsmul hb hbu hy hθ n n'
  rw [← piZModPowHom_intCast hy n, ← piZModPowHom_intCast hy n'] at hL
  refine hL.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [FiniteQuadraticModule.oddCyclic_pairing_intCast, Nat.cast_pow]

end TauCeti.IntegralLattice
