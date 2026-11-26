/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Basis
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.RingTheory.Dagger.Omega.DeRham.Derivative

/-!
# Coordinate formulas for the overconvergent exterior derivative

Over an arbitrary complete ultrametric normed field `K` (of any characteristic), computes the
coordinates of `Omega.extDerivPow` on the Monsky–Washnitzer algebra `W = K⟨X_σ⟩†` in the
exterior-power basis `((washnitzerBasis σ K).exteriorPower _)`:
`washnitzerBasis_exteriorPower_ne_zero` records non-vanishing of basis wedges,
`washnitzerBasis_exteriorPower_repr_extDerivPow` expands `dω` in terms of partial
derivatives `pderiv σ K` and shuffle signs `basisEraseSign`, and
`extDerivPow_one_eq_zero_iff_washnitzer` characterizes closed `1`-forms by the curl-free
condition `∂ᵢ fⱼ = ∂ⱼ fᵢ`.
-/

public section

namespace TauCeti.Dagger.Omega

open TauCeti.Dagger.washnitzerAlgebra TauCeti.ExteriorAlgebra

section CoordinateFormula

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Over a complete ultrametric normed field `K`, every exterior-power basis wedge
`dX_{i₀} ∧ ⋯ ∧ dX_{i_{r-1}}` on `washnitzerAlgebra σ K` is nonzero. -/
theorem washnitzerBasis_exteriorPower_ne_zero [Finite σ] [LinearOrder σ] (r : ℕ)
    (t : Set.powersetCard σ r) :
    (washnitzerBasis σ K).exteriorPower r t ≠ 0 :=
  have : Nontrivial (washnitzerAlgebra σ K) :=
    (FaithfulSMul.algebraMap_injective K (washnitzerAlgebra σ K)).nontrivial
  ((washnitzerBasis σ K).exteriorPower r).ne_zero t

/-- Over a complete ultrametric normed field `K`, basis monomials `dX_{i₀} ∧ ⋯ ∧ dX_{i_{r-1}}`
are killed by `extDerivPow` in any characteristic. -/
theorem extDerivPow_washnitzerBasis_exteriorPower [Finite σ] [LinearOrder σ] (r : ℕ)
    (t : Set.powersetCard σ r) :
    extDerivPow K (washnitzerAlgebra σ K) r
        ((washnitzerBasis σ K).exteriorPower r t) = 0 := by
  have hcomp : (washnitzerBasis σ K) ∘ (Set.powersetCard.ofFinEmbEquiv.symm t) =
      (d K (washnitzerAlgebra σ K)) ∘ (X σ K ∘ Set.powersetCard.ofFinEmbEquiv.symm t) :=
    funext fun _ ↦ washnitzerBasis_apply ..
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, hcomp]
  exact extDerivPow_ιMulti_comp_d _

private theorem washnitzerBasis_exteriorPower_repr_extDerivPow_smul
    [Fintype σ] [LinearOrder σ] (r : ℕ) (t : Set.powersetCard σ r)
    (c : washnitzerAlgebra σ K) (u : Set.powersetCard σ (r + 1)) :
    ((washnitzerBasis σ K).exteriorPower (r + 1)).repr
        (extDerivPow K (washnitzerAlgebra σ K) r
          (c • (washnitzerBasis σ K).exteriorPower r t)) u =
      ∑ k : σ, if k ∉ t.val ∧ insert k t.val = u.val then
        basisEraseSign k u.val • pderiv σ K k c else 0 := by
  rw [← (washnitzerBasis σ K).exteriorAlgebra_repr_coe_eq, ← Module.Basis.coord_apply,
    extDerivPow_smul, extDerivPow_washnitzerBasis_exteriorPower, smul_zero, add_zero,
    coe_wedgeLeft_apply, ← ExteriorAlgebra.basis_eq_coe_basis]
  conv_lhs => rw [← (washnitzerBasis σ K).sum_repr (d K (washnitzerAlgebra σ K) c)]
  rw [map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [washnitzerBasis_repr_d, LinearMap.map_smul, smul_mul_assoc, LinearMap.map_smul, ι_mul_basis]
  by_cases hkt : k ∈ t.val
  · simp [hkt]
  · rw [ite_eq_right hkt, Units.smul_def, ← Int.cast_smul_eq_zsmul (washnitzerAlgebra σ K),
      LinearMap.map_smul, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases hins : insert k t.val = u.val
    · rw [ite_eq_left ⟨hkt, hins⟩, hins, Units.smul_def,
        ← Int.cast_smul_eq_zsmul (washnitzerAlgebra σ K), Finsupp.single_eq_same]; simp [mul_comm]
    · rw [ite_eq_right fun h ↦ hins h.2, Finsupp.single_eq_of_ne' hins]; simp

/-- **Coordinate formula for the overconvergent exterior derivative** over a complete ultrametric
normed field `K` in any characteristic. -/
theorem washnitzerBasis_exteriorPower_repr_extDerivPow [Finite σ] [LinearOrder σ]
    (r : ℕ) (ω : ⋀[washnitzerAlgebra σ K]^r (Omega K (washnitzerAlgebra σ K)))
    (u : Set.powersetCard σ (r + 1)) :
    ((washnitzerBasis σ K).exteriorPower (r + 1)).repr
        (extDerivPow K (washnitzerAlgebra σ K) r ω) u =
      ∑ k ∈ u.val.attach, basisEraseSign k.val u.val •
        pderiv σ K k.val (((washnitzerBasis σ K).exteriorPower r).repr ω
          (Set.powersetCard.ofCard (s := u.val.erase k.val)
            (by rw [Finset.card_erase_of_mem k.property, Set.powersetCard.card_eq u]; rfl))) := by
  let : Fintype σ := Fintype.ofFinite σ; let : Fintype (Set.powersetCard σ r) := Fintype.ofFinite _
  rw [← Module.Basis.coord_apply]
  conv_lhs => rw [← ((washnitzerBasis σ K).exteriorPower r).sum_repr ω]
  rw [map_sum, map_sum, Finset.sum_congr rfl fun t _ ↦ by
      rw [Module.Basis.coord_apply, washnitzerBasis_exteriorPower_repr_extDerivPow_smul],
    Finset.sum_comm, ← Finset.sum_subset (Finset.subset_univ u.val)]
  · rw [← Finset.sum_attach u.val]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    let tk : Set.powersetCard σ r := Set.powersetCard.ofCard (s := u.val.erase k.val)
      (by rw [Finset.card_erase_of_mem k.property, Set.powersetCard.card_eq u]; rfl)
    rw [Finset.sum_eq_single tk
      (fun t _ hne ↦ ite_eq_right fun ⟨hkt, hins⟩ ↦ hne <| Subtype.ext <|
        (Finset.erase_insert hkt).symm.trans (congrArg (·.erase k.val) hins))
      (fun h ↦ absurd (Finset.mem_univ tk) h),
      ite_eq_left ⟨Finset.notMem_erase k.val u.val, Finset.insert_erase k.property⟩]
  · exact fun k _ hku ↦ Finset.sum_eq_zero fun t _ ↦ by
      rw [ite_eq_right]; rintro ⟨_, hins⟩; exact hku (hins ▸ Finset.mem_insert_self k t.val)

/-- For `i < j`, the `{i, j}`-coordinate of `dω` for a `1`-form `ω` is `∂ᵢ ωⱼ - ∂ⱼ ωᵢ`. -/
private theorem washnitzerBasis_exteriorPower_two_repr_extDerivPow_one [Finite σ]
    [LinearOrder σ] (ω : Omega K (washnitzerAlgebra σ K)) {i j : σ} (hij : i < j) :
    ((washnitzerBasis σ K).exteriorPower 2).repr
        (extDerivPow K (washnitzerAlgebra σ K) 1
          ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω))
        (Set.powersetCard.ofCard (Finset.card_pair hij.ne)) =
      pderiv σ K i ((washnitzerBasis σ K).repr ω j) -
        pderiv σ K j ((washnitzerBasis σ K).repr ω i) := by
  set u := Set.powersetCard.ofCard (Finset.card_pair hij.ne)
  rw [washnitzerBasis_exteriorPower_repr_extDerivPow]
  have hatt : u.val.attach = {⟨i, by simp [u]⟩, ⟨j, by simp [u]⟩} := by
    ext ⟨x, hx⟩; simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton,
      Subtype.ext_iff, true_iff]; simpa [u, Set.powersetCard.ofCard] using hx
  rw [hatt, Finset.sum_pair (fun h ↦ hij.ne (congrArg Subtype.val h))]
  have hei (hc : (u.val.erase i).card = 1) :
      Set.powersetCard.ofCard hc = Set.powersetCard.ofCard (Finset.card_singleton j) :=
    Subtype.ext (by simp [u, Set.powersetCard.ofCard, hij.ne])
  have hej (hc : (u.val.erase j).card = 1) :
      Set.powersetCard.ofCard hc = Set.powersetCard.ofCard (Finset.card_singleton i) :=
    Subtype.ext (by simp only [u, Set.powersetCard.ofCard]; rw [Finset.pair_comm]; simp [hij.ne'])
  -- Since `i < j`, `i` has sign `+1` (`{x ∈ u | x < i} = ∅`) and `j` has sign `-1` (`{i}`).
  have hfi : u.val.filter (· < i) = ∅ := by
    simp [u, Set.powersetCard.val_ofCard, Finset.filter_insert, hij.le]
  have hfj : u.val.filter (· < j) = {i} := by
    simp [u, Set.powersetCard.val_ofCard, Finset.filter_insert, Finset.filter_singleton, hij]
  rw [hei, hej, (washnitzerBasis σ K).exteriorPower_one_repr_oneEquiv_symm,
    (washnitzerBasis σ K).exteriorPower_one_repr_oneEquiv_symm,
    basisEraseSign_eq_neg_one_pow_card_filter_lt, basisEraseSign_eq_neg_one_pow_card_filter_lt,
    hfi, hfj]; simp [sub_eq_add_neg]

/-- **Curl-free characterization of closed `1`-forms** on `W = K⟨X_σ⟩†` over a complete
ultrametric normed field `K` (any characteristic): `d(∑ᵢ fᵢ dXᵢ) = 0` iff `∂ᵢ fⱼ = ∂ⱼ fᵢ` for all
`i, j : σ`. -/
theorem extDerivPow_one_eq_zero_iff_washnitzer [Finite σ]
    (ω : Omega K (washnitzerAlgebra σ K)) :
    extDerivPow K (washnitzerAlgebra σ K) 1
        ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0 ↔
      ∀ i j, pderiv σ K i ((washnitzerBasis σ K).repr ω j) =
        pderiv σ K j ((washnitzerBasis σ K).repr ω i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let : LinearOrder σ := LinearOrder.lift' e e.injective
  rw [← ((washnitzerBasis σ K).exteriorPower 2).repr.map_eq_zero_iff, Finsupp.ext_iff]
  refine ⟨fun h i j ↦ ?_, fun h u ↦ ?_⟩
  · have hlt {a b : σ} (hab : a < b) : pderiv σ K a ((washnitzerBasis σ K).repr ω b) =
        pderiv σ K b ((washnitzerBasis σ K).repr ω a) := sub_eq_zero.mp <| by
      simpa [washnitzerBasis_exteriorPower_two_repr_extDerivPow_one ω hab] using
        h (Set.powersetCard.ofCard (Finset.card_pair hab.ne))
    rcases lt_trichotomy i j with hij | rfl | hji; exacts [hlt hij, rfl, (hlt hji).symm]
  · obtain ⟨i, j, hij, hu⟩ := Finset.card_eq_two.mp (Set.powersetCard.card_eq u)
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm (hu.trans (Finset.pair_comm i j))
        (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
    have hu' : u = Set.powersetCard.ofCard (Finset.card_pair hlt.ne) := Subtype.ext hu
    rw [hu', washnitzerBasis_exteriorPower_two_repr_extDerivPow_one ω hlt, h i j, sub_self,
      Finsupp.coe_zero, Pi.zero_apply]

end CoordinateFormula

end TauCeti.Dagger.Omega
