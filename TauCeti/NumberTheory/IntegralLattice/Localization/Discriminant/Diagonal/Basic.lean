/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Bilinear
public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal.Group
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.Padics.RatCast

/-!
# The `p`-primary discriminant form from a diagonal Jordan form

Let `L` be a nondegenerate integral lattice and `p` an odd prime. Whenever the localization
`L_p = ℤ_p ⊗[ℤ] L` has an orthogonal basis `b` with self-pairings `B(bᵢ, bᵢ) = uᵢ pᵏⁱ`, `uᵢ` a unit
of `ℤ_p`, for integers `θᵢ ≡ uᵢ (mod pᵏⁱ)`, this file identifies the `p`-primary component of the
discriminant bilinear form `b_L` with the orthogonal sum of Nikulin's odd cyclic generators:

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

* `TauCeti.IntegralLattice.nonempty_isometry_pi_oddCyclic_primaryComponent`: at an odd prime, the
  `p`-primary component of the discriminant bilinear module of `L` is isometric to the orthogonal
  sum of the odd cyclic generators `q_{θᵢ}^{(p)}(pᵏⁱ)` read off a diagonal Jordan form of `L_p`.

## Implementation notes

The additive isomorphism `∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p` is proved in
`TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal.Group` via the dual
representatives `diagonalDualVec` of `p^{-kᵢ} bᵢ`. Representatives in `Lᵛ` of these classes pair by
rational numbers that differ from `δᵢⱼ uᵢ p^{-kᵢ}` by `p`-adic integers, and a rational number
with `p`-power denominator that is a `p`-adic integer is an integer
(`Padic.addCircle_coe_eq_coe_of_eq_add_algebraMap`), so the classes pair to `δᵢⱼ θᵢ / pᵏⁱ` in
`ℚ/ℤ`.

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
  {k : ι → ℕ} {y : ι → L.LocalDualCarrier p}

/-! ### Discriminant pairing of the dual basis vectors `p^{-kᵢ} bᵢ` -/

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
  have hcast (c : ∀ i, ZMod (p ^ k i)) : ∃ n : ι → ℤ, (fun i ↦ (n i : ZMod (p ^ k i))) = c :=
    ⟨fun i ↦ (c i).cast, funext fun i ↦ ZMod.intCast_zmod_cast _⟩
  refine ⟨{ toAddEquiv := L.piZModPowEquivPrimaryComponent hb hbu, map_pairing' := fun c c' ↦ ?_ }⟩
  obtain ⟨n, rfl⟩ := hcast c
  obtain ⟨n', rfl⟩ := hcast c'
  refine ((L.discriminantBilinearModule.restrict_pairing _ _ _).trans ?_).trans
    (FiniteQuadraticModule.pi_pairing _ _ _).symm
  refine (L.discriminantBilinearModule_pairing _ _).trans ?_
  have hL :
      L.discriminantPairing
          (L.piZModPowEquivPrimaryComponent hb hbu (fun i ↦ (n i : ZMod (p ^ k i))))
          (L.piZModPowEquivPrimaryComponent hb hbu (fun i ↦ (n' i : ZMod (p ^ k i)))) =
        ∑ i, ((θ i * n i * n' i / p ^ k i : ℚ) : AddCircle (1 : ℚ)) := by
    rw [piZModPowEquivPrimaryComponent_intCast, piZModPowEquivPrimaryComponent_intCast]
    exact discriminantPairing_sum_zsmul hb hbu
      (localizationDualToCompletion_diagonalDualVec hb hbu) hθ n n'
  refine hL.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [FiniteQuadraticModule.oddCyclic_pairing_intCast, Nat.cast_pow]

end TauCeti.IntegralLattice
