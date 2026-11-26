/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# The congruence groups of the `GL₂` components

For a compact subgroup `U` of `GL₂(𝔸_f)` and `g ∈ GL₂(𝔸_f)`, the group of the component of the
adelic quotient `GL₂(ℚ)\GL₂(𝔸)/K_∞U` through `g` is
`Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹`, with `GL₂(ℚ)` embedded diagonally in `GL₂(𝔸_f)`
(`TauCeti.AdelicExamples.GL2.componentGroup`). This file proves that every element of `Γ_{g,U}`
has determinant `1`, so that `Γ_{g,U} = SL₂(ℚ) ∩ gUg⁻¹`. It also proves the elementary
functoriality of `Γ_{g,U}`: it is monotone in `U`, and for `q ∈ GL₂(ℚ)` and `u ∈ U` it
satisfies `Γ_{qgu,U} = qΓ_{g,U}q⁻¹`. Finally, if the principal level `K(M)` (the kernel of
reduction modulo `M` on the integral points of `GL₂(𝔸_f)`) lies in `gUg⁻¹`, then the principal
congruence subgroup `Γ(M)` of `SL₂(ℤ)` lies in `Γ_{g,U}`, so for `M ≠ 0` the integral matrices
of `Γ_{g,U}` form a congruence subgroup, in particular of finite index, of `SL₂(ℤ)`.

That every element of `Γ_{g,U}` has determinant `1` is a direct computation with determinants.
The determinants of the compact group `gUg⁻¹` form a compact subgroup of `𝔸_f^×`, and every
compact subgroup of the finite ideles lies in the everywhere-integral units `Ô^×`
(`TauCeti.map_det_le_integralUnits_of_isCompact`, for any Dedekind domain). A positive rational
number whose principal finite idele lies in `Ô^×` is a unit of `ℤ`, hence equal to `1`
(`IsDedekindDomain.FiniteAdeleRing.eq_one_of_pos_of_mem_integralUnits`).

## Main definitions

* `TauCeti.AdelicExamples.GL2.componentGroup U g`: the group `Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹`.

## Main results

* `TauCeti.AdelicExamples.GL2.det_eq_one_of_mem_componentGroup`: for compact `U`, every element
  of `Γ_{g,U}` has determinant `1`.
* `TauCeti.AdelicExamples.GL2.componentGroup_eq_ker_det_inf`: for compact `U`,
  `Γ_{g,U} = SL₂(ℚ) ∩ gUg⁻¹`.
* `TauCeti.AdelicExamples.GL2.componentGroup_mono`: `U' ≤ U` gives `Γ_{g,U'} ≤ Γ_{g,U}`.
* `TauCeti.AdelicExamples.GL2.relIndex_componentGroup_ne_zero`: for `U'` open and `U` compact,
  `Γ_{g,U'}` has finite index in `Γ_{g,U}`.
* `TauCeti.AdelicExamples.GL2.componentGroup_mul_mul`: `Γ_{qgu,U} = qΓ_{g,U}q⁻¹`.
* `TauCeti.AdelicExamples.GL2.mapGL_mem_componentGroup_iff`: an element of `SL₂(ℤ)` lies in
  `Γ_{g,U}` exactly when its diagonal image lies in `gUg⁻¹`.
* `TauCeti.AdelicExamples.GL2.map_Gamma_le_componentGroup`: `Γ(M) ⊆ Γ_{g,U}` when
  `K(M) ⊆ gUg⁻¹`.
* `TauCeti.AdelicExamples.GL2.isCongruenceSubgroup_comap_mapGL_componentGroup`: then, for
  `M ≠ 0`, `Γ_{g,U} ∩ SL₂(ℤ)` is a congruence subgroup of `SL₂(ℤ)`, hence of finite index.
* `TauCeti.AdelicExamples.GL2.mapGL_mem_componentGroup_principalLevel_one_iff`: at principal
  level `N ≠ 0`, the integral matrices of `Γ_{1,K(N)}` form `Γ(N)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, §4 (definition
  of congruence subgroups, p. 42) and Lemma 5.13 with the remarks after it, pp. 57-58.
-/

public noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix
open scoped MatrixGroups

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

/-- `Γ_{g,U}` is monotone in `U`. -/
theorem componentGroup_mono {U U' : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} (h : U' ≤ U)
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) : componentGroup U' g ≤ componentGroup U g := by
  intro γ hγ
  rw [mem_componentGroup_iff] at hγ ⊢
  exact ⟨hγ.1, h hγ.2⟩

/-- **`Γ_{qgu,U} = qΓ_{g,U}q⁻¹`** for `q ∈ GL₂(ℚ)` and `u ∈ U`. Conjugation does not change
determinants, so no sign condition on `det q` is needed. -/
theorem componentGroup_mul_mul {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (q : GL (Fin 2) ℚ)
    {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) :
    componentGroup U (GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) q * g * u) =
      (componentGroup U g).map (MulAut.conj q).toMonoidHom := by
  ext γ
  rw [Subgroup.mem_map_equiv, mem_componentGroup_iff, mem_componentGroup_iff,
    MulAut.conj_symm_apply]
  have hdet : (GeneralLinearGroup.det (q⁻¹ * γ * q) : ℚ) = GeneralLinearGroup.det γ := by
    simp [mul_comm]
  have hconj : (GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) q * g * u)⁻¹ *
      GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) γ *
        (GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) q * g * u) =
      u⁻¹ * (g⁻¹ * GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (q⁻¹ * γ * q) *
        g) * u := by
    simp only [map_mul, map_inv, _root_.mul_inv_rev]
    group
  rw [hdet, hconj, Subgroup.mul_mem_cancel_right U hu, Subgroup.mul_mem_cancel_left U (inv_mem hu)]

/-- An element of `SL₂(ℤ)` lies in `Γ_{g,U}` exactly when its diagonal image in `GL₂(𝔸_f)` lies
in `gUg⁻¹`: its determinant `1` is automatically positive. -/
theorem mapGL_mem_componentGroup_iff {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} {γ : SL(2, ℤ)} :
    SpecialLinearGroup.mapGL ℚ γ ∈ componentGroup U g ↔
      GeneralLinearGroup.map (algebraMap ℤ (FiniteAdeleRing ℤ ℚ)) γ.toGL ∈
        U.map (MulAut.conj g).toMonoidHom := by
  have himage : GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
      (SpecialLinearGroup.mapGL ℚ γ) =
        GeneralLinearGroup.map (algebraMap ℤ (FiniteAdeleRing ℤ ℚ)) γ.toGL := by
    ext i j
    simp [SpecialLinearGroup.mapGL_coe_matrix]
  rw [componentGroup, Subgroup.mem_inf, mem_glpos, SpecialLinearGroup.det_mapGL, Units.val_one,
    Subgroup.mem_comap, himage]
  exact and_iff_right zero_lt_one

/-- **`Γ(M) ⊆ Γ_{g,U}`.** If the principal level `K(M)` of `GL₂(𝔸_f)` lies in `gUg⁻¹`, then the
image in `GL₂(ℚ)` of the principal congruence subgroup `Γ(M)` of `SL₂(ℤ)` lies in `Γ_{g,U}`. -/
theorem map_Gamma_le_componentGroup {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} {M : ℕ}
    (h : principalLevel ℚ (Ideal.span {(M : ℤ)}) ≤ U.map (MulAut.conj g).toMonoidHom) :
    (CongruenceSubgroup.Gamma M).map (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ) ≤
      componentGroup U g := by
  rintro _ ⟨γ, hγ, rfl⟩
  have hmem : ∀ i j, (γ.toGL : Matrix (Fin 2) (Fin 2) ℤ) i j -
      (1 : Matrix (Fin 2) (Fin 2) ℤ) i j ∈ Ideal.span {(M : ℤ)} := by
    obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.mem_Gamma_iff_dvd.mp hγ
    simp [Fin.forall_fin_two, Ideal.mem_span_singleton, h00, h01, h10, h11]
  exact mapGL_mem_componentGroup_iff.mpr (h (map_algebraMap_mem_principalLevel hmem))

/-- **At principal level `N ≠ 0`, the elements of `SL₂(ℤ)` in `Γ_{1,K(N)}` are those of
`Γ(N)`**: an element of `SL₂(ℤ)` lies in `Γ_{1,K(N)}` exactly when it lies in the principal
congruence subgroup `Γ(N)`. -/
theorem mapGL_mem_componentGroup_principalLevel_one_iff {N : ℕ} [NeZero N] {γ : SL(2, ℤ)} :
    SpecialLinearGroup.mapGL ℚ γ ∈ componentGroup (principalLevel ℚ (Ideal.span {(N : ℤ)})) 1 ↔
      γ ∈ CongruenceSubgroup.Gamma N := by
  refine ⟨fun h ↦ ?_, fun h ↦ map_Gamma_le_componentGroup (fun x hx ↦ ⟨x, hx, by simp⟩)
    ⟨γ, h, rfl⟩⟩
  replace h : GeneralLinearGroup.map (algebraMap ℤ (FiniteAdeleRing ℤ ℚ)) γ.toGL ∈
      principalLevel ℚ (Ideal.span {(N : ℤ)}) := by
    simpa using mapGL_mem_componentGroup_iff.mp h
  obtain ⟨hg, -, h⟩ := mem_principalLevel_iff.mp h
  have hN : Ideal.span {(N : ℤ)} ≠ ⊥ := by simp [NeZero.ne N]
  have hentry (i j : Fin 2) : (N : ℤ) ∣ γ i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [← Ideal.mem_span_singleton, ← algebraMap_mem_completedIdeal_iff (K := ℚ) hN]
    convert h i j using 1
    refine Subtype.ext ?_
    fin_cases i <;> fin_cases j <;> simp
  simpa using CongruenceSubgroup.mem_Gamma_iff_dvd.mpr
    ⟨hentry 0 0, by simpa using hentry 0 1, by simpa using hentry 1 0, hentry 1 1⟩

/-- **`Γ_{g,U} ∩ SL₂(ℤ)` is a congruence subgroup of `SL₂(ℤ)`** when the principal level
`K(M)`, `M ≠ 0`, lies in `gUg⁻¹`: it contains `Γ(M)`. In particular it has finite index in
`SL₂(ℤ)` (`CongruenceSubgroup.IsCongruenceSubgroup.finiteIndex`). -/
theorem isCongruenceSubgroup_comap_mapGL_componentGroup
    {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)}
    {M : ℕ} [NeZero M]
    (h : principalLevel ℚ (Ideal.span {(M : ℤ)}) ≤ U.map (MulAut.conj g).toMonoidHom) :
    CongruenceSubgroup.IsCongruenceSubgroup
      ((componentGroup U g).comap (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ)) :=
  ⟨M, NeZero.ne M, Subgroup.map_le_iff_le_comap.mp (map_Gamma_le_componentGroup h)⟩

/-- **`Γ_{g,U'}` has finite index in `Γ_{g,U}`** whenever `U'` is an open and `U` a compact
subgroup of `GL₂(𝔸_f)`; no containment `U' ≤ U` is assumed. -/
theorem relIndex_componentGroup_ne_zero {U U' : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    (componentGroup U' g).relIndex (componentGroup U g) ≠ 0 := by
  -- The index is at most that of `gU'g⁻¹` in `gUg⁻¹`, which is that of `U'` in `U`.
  set φ := GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
  set c := (MulAut.conj g).toMonoidHom
  have hc : (U'.map c).relIndex (U.map c) ≠ 0 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact Subgroup.relIndex_ne_zero_of_isOpen_of_isCompact hU' hU
  -- `Γ_{g,U'} = φ⁻¹(gU'g⁻¹) ⊓ GL₂(ℚ)^+` and likewise for `U`
  rw [componentGroup, componentGroup, inf_comm (GLPos _ _), inf_comm (GLPos _ _)]
  exact Subgroup.relIndex_inter_ne_zero (Subgroup.relIndex_comap_ne_zero φ hc) _

end AdelicExamples.GL2

end TauCeti
