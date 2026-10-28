/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic

/-!
# The cusp forms have codimension at most the number of cusps

Let `H` be a finite-index subgroup of `SL(2, ℤ)`, acting through its image in `GL(2, ℝ)`. The
constant term of a modular form on `H` at the cusp represented by `γ ∈ SL(2, ℤ)` depends on `γ`
only through the cusp orbit of `γ • ∞`, up to a sign: if `γ • ∞` and `γ' • ∞` are
`H`-equivalent, then `γ' = h γ (±Tʲ)` with `h ∈ H`, so the two constant-term functionals differ
by the factor `(±1)ᵏ`, the same for every form.

Consequently the constant terms at one representative of each cusp orbit already have the cusp
forms as their common kernel, and a subspace of `M_k(H)` meeting the cusp forms trivially
embeds into the functions on the cusp orbits. Its dimension is therefore at most the number
`ε∞` of cusps of `H`. This is the upper bound in Diamond–Shurman's computation of the dimension
of the Eisenstein space: comparing it with the number of linearly independent Eisenstein series
shows that those series span a complement of the cusp forms.

## Main results

* `TauCeti.ModularForm.exists_constantTermAt_eq_zpow_smul_of_cuspOrbitOfSL2Z_eq`: the constant
  terms at two representatives of the same cusp orbit agree up to a factor `(±1)ᵏ`.
* `TauCeti.ModularForm.constantTermAt_eq_of_cuspOrbitOfSL2Z_eq`: at even weight, the constant
  terms at equivalent cusp representatives agree.
* `TauCeti.ModularForm.finrank_le_finrank_range_constantTerms_of_disjoint`: a subspace
  disjoint from cusp forms has dimension at most the image of representative constant terms.
* `TauCeti.ModularForm.finrank_le_card_cuspOrbit_of_disjoint`: a subspace of `M_k(H)` with zero
  intersection with the cusp forms has dimension at most the number of cusps of `H`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§3.1, 4.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup ModularForm
open scoped MatrixGroups

namespace TauCeti.ModularForm

variable {H : Subgroup SL(2, ℤ)} [H.FiniteIndex] {k : ℤ}

/-- **Constant terms at equivalent cusps agree up to sign.** If `γ • ∞` and `γ' • ∞` lie in the
same cusp orbit of `H`, the constant-term functionals at `γ` and `γ'` on `M_k(H)` differ by the
factor `uᵏ` for a sign `u = ±1`. -/
theorem exists_constantTermAt_eq_zpow_smul_of_cuspOrbitOfSL2Z_eq {γ γ' : SL(2, ℤ)}
    (h : H.cuspOrbitOfSL2Z γ = H.cuspOrbitOfSL2Z γ') :
    ∃ u : ℤˣ, constantTermAt (Γ := H.map (mapGL ℝ)) (k := k) γ' =
      ((u : ℤ) : ℂ) ^ k • constantTermAt γ := by
  obtain ⟨g, hg, hc⟩ := (H.cuspOrbitOfSL2Z_eq_iff γ γ').mp h
  set m := γ⁻¹ * g * γ'
  have had : m 0 0 * m 1 1 = 1 := by
    simpa only [det_fin_two, hc, mul_zero, sub_zero] using m.det_coe
  refine ⟨⟨m 0 0, m 1 1, had, by rw [mul_comm, had]⟩, LinearMap.ext fun f ↦ ?_⟩
  rw [LinearMap.smul_apply, smul_eq_mul, Units.val_mk, ← constantTermAt_mul_of_c_eq_zero γ hc,
    ← constantTermAt_mul_left (Subgroup.mem_map_of_mem _ hg) γ']
  simp only [m, mul_assoc, mul_inv_cancel_left]

/-- At even weight, constant terms at representatives of the same cusp orbit agree, without
requiring that `-I ∈ H`. -/
theorem constantTermAt_eq_of_cuspOrbitOfSL2Z_eq (hk : Even k) {γ γ' : SL(2, ℤ)}
    (h : H.cuspOrbitOfSL2Z γ = H.cuspOrbitOfSL2Z γ') :
    constantTermAt (Γ := H.map (mapGL ℝ)) (k := k) γ' = constantTermAt γ := by
  obtain ⟨u, hu⟩ := exists_constantTermAt_eq_zpow_smul_of_cuspOrbitOfSL2Z_eq (k := k) h
  rcases Int.units_eq_one_or u with rfl | rfl <;> simpa [hk.neg_one_zpow] using hu

variable (H k) in
/-- Reading constant terms at any choice of cusp representatives bounds the dimension of a
subspace disjoint from cusp forms by the dimension of the resulting constant-term image. -/
theorem finrank_le_finrank_range_constantTerms_of_disjoint
    (r : (H.map sl2zToPSL2R).CuspOrbit → SL(2, ℤ))
    (hr : Function.RightInverse r H.cuspOrbitOfSL2Z)
    {V : Submodule ℂ (ModularForm (H.map (mapGL ℝ)) k)}
    (hV : Disjoint V (cuspFormSubmodule (H.map (mapGL ℝ)) k)) :
    Module.finrank ℂ V ≤ Module.finrank ℂ
      (LinearMap.range ((LinearMap.funLeft ℂ ℂ r).comp
        (constantTerms (Γ := H.map (mapGL ℝ)) (k := k)))) := by
  let L := (LinearMap.funLeft ℂ ℂ r).comp (constantTerms (Γ := H.map (mapGL ℝ)) (k := k))
  have hker (f : ModularForm (H.map (mapGL ℝ)) k) (hf : L f = 0) :
      f ∈ cuspFormSubmodule (H.map (mapGL ℝ)) k := by
    rw [mem_cuspFormSubmodule_iff_constantTermAt_eq_zero]
    intro γ
    obtain ⟨u, hu⟩ := exists_constantTermAt_eq_zpow_smul_of_cuspOrbitOfSL2Z_eq (k := k)
      (hr (H.cuspOrbitOfSL2Z γ))
    have h0 := congrFun hf (H.cuspOrbitOfSL2Z γ)
    rw [LinearMap.comp_apply, LinearMap.funLeft_apply, constantTerms_apply,
      Pi.zero_apply] at h0
    rw [hu, LinearMap.smul_apply, h0, smul_zero]
  have hinj : Function.Injective (L.comp V.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    exact Subtype.ext <| (Submodule.disjoint_def.mp hV) _ f.2 (hker _ hf)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (L.comp V.subtype).codRestrict (LinearMap.range L)
      fun f ↦ ⟨f, rfl⟩) (fun _ _ h ↦ hinj (congrArg Subtype.val h))

variable (H k) in
/-- **The cusp forms have codimension at most the number of cusps.** A subspace of `M_k(H)`
whose intersection with the cusp forms is zero, such as a complement of the cusp forms, has
dimension at most the number of cusps of `H`. -/
theorem finrank_le_card_cuspOrbit_of_disjoint {V : Submodule ℂ (ModularForm (H.map (mapGL ℝ)) k)}
    (hV : Disjoint V (cuspFormSubmodule (H.map (mapGL ℝ)) k)) :
    Module.finrank ℂ V ≤ Nat.card (H.map sl2zToPSL2R).CuspOrbit := by
  let r := Function.surjInv H.cuspOrbitOfSL2Z_surjective
  have hle := finrank_le_finrank_range_constantTerms_of_disjoint H k r
    (Function.surjInv_eq H.cuspOrbitOfSL2Z_surjective) hV
  have := Fintype.ofFinite (H.map sl2zToPSL2R).CuspOrbit
  exact hle.trans <| by
    simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
      Submodule.finrank_le (LinearMap.range ((LinearMap.funLeft ℂ ℂ r).comp
        (constantTerms (Γ := H.map (mapGL ℝ)) (k := k))))

end TauCeti.ModularForm
