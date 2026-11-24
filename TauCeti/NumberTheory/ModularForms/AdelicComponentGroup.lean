/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology

/-!
# The congruence groups of the `GL₂` components

For a compact subgroup `U` of `GL₂(𝔸_f)` and `g ∈ GL₂(𝔸_f)`, the group of the component of the
adelic quotient `GL₂(ℚ)\GL₂(𝔸)/K_∞U` through `g` is
`Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹`, with `GL₂(ℚ)` embedded diagonally in `GL₂(𝔸_f)`
(`TauCeti.AdelicExamples.GL2.componentGroup`). This file proves that every element of `Γ_{g,U}`
has determinant `1`, so that `Γ_{g,U} = SL₂(ℚ) ∩ gUg⁻¹`.

The argument is a direct computation with determinants. The determinants of the compact group
`gUg⁻¹` form a compact subgroup of `𝔸_f^×`, and every compact subgroup of the finite ideles lies
in the everywhere-integral units `Ô^×` (`TauCeti.map_det_le_integralUnits_of_isCompact`, for any
Dedekind domain). A positive rational number whose principal finite idele lies in `Ô^×` is a unit
of `ℤ`, hence equal to `1` (`IsDedekindDomain.FiniteAdeleRing.eq_one_of_pos_of_mem_integralUnits`).

## Main definitions

* `TauCeti.AdelicExamples.GL2.componentGroup U g`: the group `Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹`.

## Main results

* `TauCeti.AdelicExamples.GL2.det_eq_one_of_mem_componentGroup`: for compact `U`, every element
  of `Γ_{g,U}` has determinant `1`.
* `TauCeti.AdelicExamples.GL2.componentGroup_eq_ker_det_inf`: for compact `U`,
  `Γ_{g,U} = SL₂(ℚ) ∩ gUg⁻¹`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, §4 (definition
  of congruence subgroups, p. 42) and Lemma 5.13 with the remarks after it, pp. 57-58.
-/

public noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix

namespace TauCeti

namespace AdelicExamples.GL2

/-- The group `Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹` of the component through `g` of the adelic quotient
`GL₂(ℚ)\GL₂(𝔸)/K_∞U`: the rational matrices of positive determinant whose diagonal image in
`GL₂(𝔸_f)` lies in the conjugate `gUg⁻¹`. -/
def componentGroup (U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) : Subgroup (GL (Fin 2) ℚ) :=
  GLPos (Fin 2) ℚ ⊓
    (U.map (MulAut.conj g).toMonoidHom).comap
      (GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)))

/-- Membership in `Γ_{g,U}`: positive determinant, and diagonal image in `gUg⁻¹`. -/
@[simp]
theorem mem_componentGroup_iff {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} {γ : GL (Fin 2) ℚ} :
    γ ∈ componentGroup U g ↔
      0 < (GeneralLinearGroup.det γ : ℚ) ∧
        g⁻¹ * GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) γ * g ∈ U := by
  rw [componentGroup, Subgroup.mem_inf, mem_glpos, Subgroup.mem_comap, Subgroup.mem_map_equiv,
    MulAut.conj_symm_apply]

/-- **For compact `U`, every element of `Γ_{g,U}` has determinant `1`.** -/
theorem det_eq_one_of_mem_componentGroup {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} {γ : GL (Fin 2) ℚ} (hγ : γ ∈ componentGroup U g) :
    GeneralLinearGroup.det γ = 1 := by
  rw [mem_componentGroup_iff] at hγ
  refine eq_one_of_pos_of_mem_integralUnits hγ.1 ?_
  have hmem := map_det_le_integralUnits_of_isCompact hU
    (Subgroup.mem_map_of_mem GeneralLinearGroup.det hγ.2)
  have hdet : GeneralLinearGroup.det
      (g⁻¹ * GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) γ * g) =
        unitEmbedding ℤ ℚ (GeneralLinearGroup.det γ) := by
    ext
    simp [unitEmbedding_apply, GeneralLinearGroup.val_det_apply, RingHom.map_det, mul_comm]
  rwa [hdet] at hmem

/-- **`Γ_{g,U} = SL₂(ℚ) ∩ gUg⁻¹`** for compact `U`: the positivity condition on the determinant
can be replaced by the condition that it is `1`. -/
theorem componentGroup_eq_ker_det_inf {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    componentGroup U g =
      GeneralLinearGroup.det.ker ⊓
        (U.map (MulAut.conj g).toMonoidHom).comap
          (GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))) := by
  ext γ
  refine ⟨fun h ↦ Subgroup.mem_inf.mpr
    ⟨det_eq_one_of_mem_componentGroup hU h, (Subgroup.mem_inf.mp h).2⟩, fun h ↦ ?_⟩
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp h
  refine Subgroup.mem_inf.mpr ⟨?_, h2⟩
  rw [mem_glpos, MonoidHom.mem_ker.mp h1]
  exact zero_lt_one

end AdelicExamples.GL2

end TauCeti
