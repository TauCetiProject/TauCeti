/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Sugawara.Vacuum.Basic
public import TauCeti.Algebra.Lie.Killing.SymmetricAlgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Homogeneous
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear

import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Injective

/-!
# PBW symbol and nonscalarity of the quadratic Segal--Sugawara state

Under the PBW isomorphism `U(t⁻¹ L[t⁻¹]) ≃ V` (`TauCeti.CurrentAlgebra.vacuumPBWEquiv`), the
quadratic Segal--Sugawara state `S₋₂ |0⟩` (`TauCeti.CurrentAlgebra.sugawaraVacuum`) corresponds to
`∑ᵢ ι(t⁻¹ ⊗ bᵢ) ι(t⁻¹ ⊗ b'ᵢ)` in PBW filtration degree `2`, whose class in `gr₂ U(t⁻¹ L[t⁻¹])` is
the image of the quadratic symmetric Casimir `TauCeti.symmetricCasimir K L` along the mode-`(-1)`
embedding
(`pbwGradedPieceMk_vacuumPBWEquiv_symm_sugawaraVacuum_eq_pbwHomogeneousComponentMap`).
When `2 ≠ 0` in `K` and `L` is nontrivial, injectivity of the PBW map and of `SymmetricAlgebra.map`
shows that this PBW preimage does not lie in filtration degree `1`
(`TauCeti.CurrentAlgebra.vacuumPBWEquiv_symm_sugawaraVacuum_notMem_pbwFiltration_one`). Therefore
`S₋₂ |0⟩` does not lie in the `K`-span of `|0⟩` at any level, including the critical level and
`a = 0` (`TauCeti.CurrentAlgebra.sugawaraVacuum_notMem_span_vacuum`). In particular, when `2 ≠ 0` in
`K` and `L` is nontrivial, `S₋₂` is never a scalar in `Û` at any level or central value
(`TauCeti.CurrentAlgebra.sugawaraMode_neg_two_notMem_bot`), so at the critical level the completed
center `Z(Û)` is strictly larger than the scalars
(`TauCeti.CurrentAlgebra.center_completedEnveloping_ne_bot`).

## Main results

* `pbwGradedPieceMk_vacuumPBWEquiv_symm_sugawaraVacuum_eq_pbwHomogeneousComponentMap`:
  the degree-two PBW symbol of `S₋₂ |0⟩` is the mode-`(-1)` image of `symmetricCasimir K L`.
* `TauCeti.CurrentAlgebra.sugawaraVacuum_notMem_span_vacuum`: `S₋₂ |0⟩` is nonscalar in `V` at
  every level when `2 ≠ 0` and `L` is nontrivial.
* `TauCeti.CurrentAlgebra.center_completedEnveloping_ne_bot`: at the critical level
  `2 a Φ = κ_L`, `Z(Û) ≠ ⊥` when `2 ≠ 0` and `L` is nontrivial.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.2, §3.1, and §3.2.2.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4 and §2.5.10.
* V. G. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.7 and §5.7.
-/

public section

noncomputable section

open LieAlgebra TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.CurrentAlgebra

/-! ### PBW preimage, quadratic Casimir symbol, and nonscalarity -/

section SugawaraVacuumPBW

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {Φ : LinearMap.BilinForm K L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : K}

local notation "Û" => CompletedEnveloping Φ hΦ hΦs a
local notation "hV" => smoothModules_natCast_vacuumModule Φ hΦ hΦs a
local notation "Nneg" => negativeLieSubalgebra Φ hΦ hΦs
local notation "Uneg" => _root_.UniversalEnvelopingAlgebra K Nneg

/-- **The PBW preimage of `S₋₂ |0⟩` in `U(t⁻¹ L[t⁻¹])`** is `∑ᵢ ι(t⁻¹ ⊗ bᵢ) ι(t⁻¹ ⊗ b'ᵢ)` in every
basis `b` of `L` with Killing-dual basis `b'`. -/
theorem vacuumPBWEquiv_symm_sugawaraVacuum {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) :
    (vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a) =
      ∑ i, _root_.UniversalEnvelopingAlgebra.ι K (negativeSingle Φ hΦ hΦs neg_one_lt_zero (b i)) *
        _root_.UniversalEnvelopingAlgebra.ι K
          (negativeSingle Φ hΦ hΦs neg_one_lt_zero (killingDualBasis b i)) := by
  rw [sugawaraVacuum_eq_sum b, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← negativeEnvelopingHom_ι_negativeSingle neg_one_lt_zero,
    ← negativeEnvelopingHom_ι_negativeSingle neg_one_lt_zero, ← map_mul,
    vacuumPBWEquiv_symm_smul_vacuum]

/-- **The PBW preimage of `S₋₂ |0⟩` lies in PBW filtration degree `2`.** -/
theorem vacuumPBWEquiv_symm_sugawaraVacuum_mem_pbwFiltration_two :
    (vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a) ∈ pbwFiltration K Nneg 2 := by
  rw [vacuumPBWEquiv_symm_sugawaraVacuum (Module.finBasis K L)]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  exact mul_mem_pbwFiltration K Nneg (ι_mem_pbwFiltration_one K Nneg _)
    (ι_mem_pbwFiltration_one K Nneg _)

/-- **The degree-two PBW graded class of `S₋₂ |0⟩` is the PBW image of the mode-`(-1)` quadratic
symmetric Casimir `SymmetricAlgebra.map K (negativeSingle ...) (symmetricCasimir K L)`.** -/
theorem pbwGradedPieceMk_vacuumPBWEquiv_symm_sugawaraVacuum_eq_pbwHomogeneousComponentMap :
    pbwGradedPieceMk K Nneg 2
        ⟨(vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a),
          vacuumPBWEquiv_symm_sugawaraVacuum_mem_pbwFiltration_two⟩ =
      pbwHomogeneousComponentMap K Nneg 2
        ⟨SymmetricAlgebra.map K (negativeSingle Φ hΦ hΦs neg_one_lt_zero) (symmetricCasimir K L),
          TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule _
            (symmetricCasimir_mem_homogeneousSubmodule K L)⟩ := by
  -- Expand both sides in `b = Module.finBasis K L`, apply `pbwHomogeneousComponentMap_ι_mul_ι`
  -- termwise, and sum to recover the PBW preimage of `S₋₂ |0⟩`.
  set b := Module.finBasis K L
  set e := negativeSingle Φ hΦ hΦs (neg_one_lt_zero : (-1 : ℤ) < 0)
  have hp :
      (⟨SymmetricAlgebra.map K e (symmetricCasimir K L),
          TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule _
            (symmetricCasimir_mem_homogeneousSubmodule K L)⟩ :
          TauCeti.SymmetricAlgebra.homogeneousSubmodule K Nneg 2) =
        ∑ i, ⟨SymmetricAlgebra.ι K Nneg (e (b i)) *
            SymmetricAlgebra.ι K Nneg (e (killingDualBasis b i)),
          SetLike.mul_mem_graded
            (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule K Nneg _)
            (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule K Nneg _)⟩ :=
    Subtype.ext (by simp [symmetricCasimir_eq_sum b])
  rw [hp, map_sum]
  simp_rw [pbwHomogeneousComponentMap_ι_mul_ι]
  rw [← map_sum (pbwGradedPieceMk K Nneg 2)]
  exact congrArg (pbwGradedPieceMk K Nneg 2) (Subtype.ext (by
    simp only [Submodule.coe_sum, e, vacuumPBWEquiv_symm_sugawaraVacuum b]))

/-- **Away from characteristic two, the PBW preimage of `S₋₂ |0⟩` for a nontrivial Lie algebra does
not lie in PBW filtration degree `1`** (it has exact PBW degree `2`). -/
theorem vacuumPBWEquiv_symm_sugawaraVacuum_notMem_pbwFiltration_one
    [NeZero (2 : K)] [Nontrivial L] :
    (vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a) ∉ pbwFiltration K Nneg 1 := by
  intro hmem
  have hprev : (vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a) ∈
      pbwFiltrationPrevious K Nneg 2 := by
    rwa [pbwFiltrationPrevious_succ]
  have hmk :=
    (pbwGradedPieceMk_vacuumPBWEquiv_symm_sugawaraVacuum_eq_pbwHomogeneousComponentMap
      (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a)).symm.trans
      ((pbwGradedPieceMk_eq_zero_iff K Nneg _).2 hprev)
  have hsym := pbwHomogeneousComponentMap_injective K Nneg 2
    (hmk.trans (map_zero (pbwHomogeneousComponentMap K Nneg 2)).symm)
  have hmap : SymmetricAlgebra.map K (negativeSingle Φ hΦ hΦs neg_one_lt_zero)
      (symmetricCasimir K L) = 0 := congrArg Subtype.val hsym
  have hcas := SymmetricAlgebra.map_injective (negativeSingle Φ hΦ hΦs neg_one_lt_zero)
    (negativeSingle_injective neg_one_lt_zero) (hmap.trans (map_zero _).symm)
  exact symmetricCasimir_ne_zero K L hcas

/-- **Away from characteristic two, `S₋₂ |0⟩` is not a scalar multiple of the vacuum vector `|0⟩`**
when `L` is nontrivial, at every level `Φ` and central value `a` (including the critical level and
`a = 0`). -/
theorem sugawaraVacuum_notMem_span_vacuum [NeZero (2 : K)] [Nontrivial L] :
    sugawaraVacuum Φ hΦ hΦs a ∉ Submodule.span K {vacuum Φ hΦ hΦs a} := by
  intro hspan
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hspan
  apply vacuumPBWEquiv_symm_sugawaraVacuum_notMem_pbwFiltration_one
    (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a)
  rw [← hr, map_smul, ← vacuumPBWEquiv_one (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a),
    LinearEquiv.symm_apply_apply, Algebra.smul_def, mul_one]
  exact algebraMap_mem_pbwFiltration K Nneg r 1

/-- **Away from characteristic two, `S₋₂ |0⟩ ≠ 0` when `L` is nontrivial**, at every level `Φ` and
central value `a`. -/
theorem sugawaraVacuum_ne_zero [NeZero (2 : K)] [Nontrivial L] :
    sugawaraVacuum Φ hΦ hΦs a ≠ 0 :=
  fun h0 ↦ sugawaraVacuum_notMem_span_vacuum (h0 ▸ Submodule.zero_mem _)

/-- **Away from characteristic two and when `1 - 2 a c ≠ 0`, the normalised quadratic state
`L₋₂ |0⟩` (which serves as the candidate Virasoro conformal vector when `Φ = c • κ_L`) is not a
scalar multiple of `|0⟩`** when `L` is nontrivial. -/
theorem limSmul_sugawaraVirasoro_neg_two_vacuum_notMem_span_vacuum
    [NeZero (2 : K)] [Nontrivial L] {c : K} (hc : 1 - 2 * a * c ≠ 0) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c (-2)) (vacuum Φ hΦ hΦs a) ∉
      Submodule.span K {vacuum Φ hΦ hΦs a} := by
  rw [limSmul_sugawaraVirasoro_neg_two_vacuum]
  intro hspan
  apply sugawaraVacuum_notMem_span_vacuum (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a)
  have h2 := Submodule.smul_mem _ (1 - 2 * a * c) hspan
  rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at h2

/-- **Away from characteristic two, `S₋₂` is not a scalar in the completed enveloping algebra `Û`**
when `L` is nontrivial, at every level `Φ` and central value `a`. -/
theorem sugawaraMode_neg_two_notMem_bot [NeZero (2 : K)] [Nontrivial L] :
    sugawaraMode Φ hΦ hΦs a (-2) ∉ (⊥ : Subalgebra K Û) := by
  intro hbot
  obtain ⟨r, hr⟩ := Algebra.mem_bot.1 hbot
  apply sugawaraVacuum_notMem_span_vacuum (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a)
  rw [sugawaraVacuum_def, ← hr, ← (toCompletedEnveloping Φ hΦ hΦs a).commutes,
    limSmul_toCompletedEnveloping, algebraMap_smul]
  exact Submodule.mem_span_singleton.2 ⟨r, rfl⟩

/-- **Away from characteristic two, `S₋₂ ≠ 0` in `Û` when `L` is nontrivial**, at every level `Φ`
and central value `a`. -/
theorem sugawaraMode_neg_two_ne_zero [NeZero (2 : K)] [Nontrivial L] :
    sugawaraMode Φ hΦ hΦs a (-2) ≠ 0 :=
  fun h0 ↦ sugawaraMode_neg_two_notMem_bot (h0 ▸ Subalgebra.zero_mem ⊥)

/-- **At the critical level `2 a Φ = κ_L`, the completed center `Z(Û)` is strictly larger than the
scalars `K`** whenever `2 ≠ 0` in `K` and `L` is nontrivial, witnessed by `S₋₂ ∈ Z(Û) \ K`. -/
theorem center_completedEnveloping_ne_bot [NeZero (2 : K)] [Nontrivial L]
    (h : (2 * a) • Φ = killingForm K L) :
    Subalgebra.center K Û ≠ ⊥ := by
  intro hbot
  exact sugawaraMode_neg_two_notMem_bot (hbot ▸ sugawaraMode_mem_center h (-2))

end SugawaraVacuumPBW

end TauCeti.CurrentAlgebra
