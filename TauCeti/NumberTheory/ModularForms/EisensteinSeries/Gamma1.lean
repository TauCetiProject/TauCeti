/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Primitive
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# The cusp--Eisenstein decomposition for `Gamma1`

In weight at least three, the Eisenstein subspace for `Gamma1 N` is the space of forms whose
restriction to the principal congruence subgroup belongs to the span of the primitive
residue-class Eisenstein series. This file proves that it is complementary to the cusp forms.

The spanning argument descends the corresponding decomposition for `Gamma N` by the trace from
`Gamma N` to `Gamma1 N`. The trace preserves the primitive Eisenstein span: on every coset, the
slash transformation formula sends the series with residue `a` to the series whose residue is the
right translate of `a`. Tracing a cusp form remains cuspidal, while tracing a restricted
`Gamma1 N` form multiplies it by the finite relative index.

## Main results

* `TauCeti.EisensteinSeries.gamma1EisensteinSubspace`: the Eisenstein subspace of
  `M_k(Gamma1 N)` detected after restriction to `Gamma N`.
* `TauCeti.EisensteinSeries.isCompl_gamma1EisensteinSubspace_cuspFormSubmodule`: the
  cusp--Eisenstein decomposition of `M_k(Gamma1 N)` in weight at least three.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Section 4.2.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open UpperHalfPlane
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ} {k : ℤ} [NeZero N]

private abbrev gammaMap (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (Gamma N).map (mapGL ℝ)

private abbrev gamma1Map (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (Gamma1 N).map (mapGL ℝ)

omit [NeZero N] in
private theorem gammaMap_le_gamma1Map : gammaMap N ≤ gamma1Map N :=
  Subgroup.map_mono (Gamma_le_Gamma1 N)

private instance gammaMap_isFiniteRelIndex_gamma1Map :
    (gammaMap N).IsFiniteRelIndex (gamma1Map N) := by
  have hle : gamma1Map N ≤ 𝒮ℒ := by
    intro g hg
    obtain ⟨γ, -, rfl⟩ := hg
    exact ⟨γ, rfl⟩
  exact Subgroup.isFiniteRelIndex_of_le_right (gammaMap N) hle

private lemma quotientFunc_eisensteinSeriesMF (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
    (q : gamma1Map N ⧸ (gammaMap N).subgroupOf (gamma1Map N)) :
    ∃ b : Fin 2 → ZMod N,
      SlashInvariantForm.quotientFunc (eisensteinSeriesMF hk a) q =
        eisensteinSeries b k := by
  induction q using QuotientGroup.induction_on' with
  | H h =>
      obtain ⟨γ, hγ, hmap⟩ := h.property
      refine ⟨a ᵥ* (SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ⁻¹), ?_⟩
      rw [SlashInvariantForm.quotientFunc_mk]
      change eisensteinSeries a k ∣[k] h.val⁻¹ =
        eisensteinSeries (a ᵥ* (SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ⁻¹)) k
      rw [← hmap, ← map_inv]
      have hslash : eisensteinSeries a k ∣[k] mapGL ℝ γ⁻¹ =
          eisensteinSeries a k ∣[k] γ⁻¹ :=
        (ModularForm.SL_slash (eisensteinSeries a k) γ⁻¹).symm
      rw [hslash, eisensteinSeries_slash_apply]

private noncomputable def traceGamma1 :
    ModularForm (gammaMap N) k →ₗ[ℂ] ModularForm (gamma1Map N) k where
  toFun f := ModularForm.trace (gamma1Map N) f
  map_add' f g := by
    apply DFunLike.coe_injective
    simp only [FunLike.coe_add]
    rw [ModularForm.coe_trace, ModularForm.coe_trace, ModularForm.coe_trace]
    let _ := Fintype.ofFinite
      (gamma1Map N ⧸ (gammaMap N).subgroupOf (gamma1Map N))
    ext z
    simp only [Finset.sum_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    induction q using QuotientGroup.induction_on' with
    | H h =>
        simp only [SlashInvariantForm.quotientFunc_mk, FunLike.coe_add]
        exact congrFun (SlashAction.add_slash k h.val⁻¹ ⇑f ⇑g) z
  map_smul' c f := by
    apply DFunLike.coe_injective
    simp only [FunLike.coe_smul, RingHom.id_apply]
    rw [ModularForm.coe_trace, ModularForm.coe_trace]
    let _ := Fintype.ofFinite
      (gamma1Map N ⧸ (gammaMap N).subgroupOf (gamma1Map N))
    ext z
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    induction q using QuotientGroup.induction_on' with
    | H h =>
        obtain ⟨γ, hγ, hmap⟩ := h.property
        simp only [SlashInvariantForm.quotientFunc_mk, FunLike.coe_smul]
        rw [← hmap, ← map_inv]
        exact congrFun (ModularForm.smul_slash_of_det_pos k
          (det_pos_of_mem_slGL ⟨γ⁻¹, rfl⟩) (⇑f) c) z

private theorem traceGamma1_apply (f : ModularForm (gammaMap N) k) :
    traceGamma1 f = ModularForm.trace (gamma1Map N) f :=
  rfl

private lemma traceGamma1_eisensteinSeriesMF_mem (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) :
    ModularForm.ofLe gammaMap_le_gamma1Map (traceGamma1 (eisensteinSeriesMF hk a)) ∈
      primitiveEisensteinSubspace N hk := by
  classical
  let _ := Fintype.ofFinite
    (gamma1Map N ⧸ (gammaMap N).subgroupOf (gamma1Map N))
  choose b hb using fun q ↦ quotientFunc_eisensteinSeriesMF hk a q
  have htrace :
      ModularForm.ofLe gammaMap_le_gamma1Map (traceGamma1 (eisensteinSeriesMF hk a)) =
        ∑ q, eisensteinSeriesMF hk (b q) := by
    apply DFunLike.coe_injective
    rw [ModularForm.coe_ofLe, traceGamma1_apply, ModularForm.coe_trace,
      FunLike.coe_sum]
    funext z
    rw [Finset.sum_apply]
    simp_rw [hb]
    simp only [coe_eisensteinSeriesMF]
    exact (Finset.sum_apply z Finset.univ
      (fun q ↦ eisensteinSeries (b q) k)).symm
  rw [htrace]
  exact Submodule.sum_mem _ fun q _ ↦ mem_primitiveEisensteinSubspace hk (b q)

private lemma traceGamma1_mem_primitiveEisensteinSubspace (hk : 3 ≤ k)
    {f : ModularForm (gammaMap N) k} (hf : f ∈ primitiveEisensteinSubspace N hk) :
    ModularForm.ofLe gammaMap_le_gamma1Map (traceGamma1 f) ∈
      primitiveEisensteinSubspace N hk := by
  have hle : primitiveEisensteinSubspace N hk ≤
      (primitiveEisensteinSubspace N hk).comap
        ((ModularForm.ofLeₗ gammaMap_le_gamma1Map).comp traceGamma1) := by
    apply primitiveEisensteinSubspace_le hk
    intro a
    change ((ModularForm.ofLeₗ gammaMap_le_gamma1Map).comp traceGamma1)
        (eisensteinSeriesMF hk a) ∈ primitiveEisensteinSubspace N hk
    simpa only [LinearMap.comp_apply, ModularForm.ofLeₗ_apply] using
      traceGamma1_eisensteinSeriesMF_mem hk a
  have hmem := hle hf
  simpa only [Submodule.mem_comap, LinearMap.comp_apply, ModularForm.ofLeₗ_apply] using hmem

private lemma traceGamma1_mem_cuspFormSubmodule
    {f : ModularForm (gammaMap N) k} (hf : f ∈ cuspFormSubmodule (gammaMap N) k) :
    traceGamma1 f ∈ cuspFormSubmodule (gamma1Map N) k := by
  obtain ⟨g, rfl⟩ := hf
  refine ⟨CuspForm.trace (gamma1Map N) g, ?_⟩
  ext z
  rfl

private lemma traceGamma1_ofLe (f : ModularForm (gamma1Map N) k) :
    traceGamma1 (ModularForm.ofLe gammaMap_le_gamma1Map f) =
      ((gammaMap N).relIndex (gamma1Map N) : ℂ) • f := by
  rw [traceGamma1_apply]
  have hres : ModularForm.ofLe gammaMap_le_gamma1Map f =
      ModularForm.restrict gammaMap_le_gamma1Map f := by
    apply DFunLike.coe_injective
    rw [ModularForm.coe_ofLe, ModularForm.coe_restrict]
  rw [hres]
  simpa only [Nat.cast_smul_eq_nsmul] using
    trace_restrict f gammaMap_le_gamma1Map

/-- The Eisenstein subspace of `M_k(Gamma1 N)` in weight at least three: a form belongs to it
exactly when its restriction to `Gamma N` belongs to the primitive residue-class Eisenstein
span. -/
def gamma1EisensteinSubspace (N : ℕ) [NeZero N] (hk : 3 ≤ k) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  (primitiveEisensteinSubspace N hk).comap
    (ModularForm.ofLeₗ (Subgroup.map_mono (Gamma_le_Gamma1 N)))

/-- Membership in the `Gamma1 N` Eisenstein subspace is detected after restriction to the
principal congruence subgroup. -/
theorem mem_gamma1EisensteinSubspace_iff (hk : 3 ≤ k)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ gamma1EisensteinSubspace N hk ↔
      ModularForm.ofLe (Subgroup.map_mono (Gamma_le_Gamma1 N)) f ∈
        primitiveEisensteinSubspace N hk :=
  by
    simp only [gamma1EisensteinSubspace, Submodule.mem_comap,
      ModularForm.ofLeₗ_apply]

omit [NeZero N] in
private lemma ofLe_mem_cuspFormSubmodule
    {f : ModularForm (gamma1Map N) k} (hf : f ∈ cuspFormSubmodule (gamma1Map N) k) :
    ModularForm.ofLe gammaMap_le_gamma1Map f ∈ cuspFormSubmodule (gammaMap N) k := by
  obtain ⟨g, hg⟩ := hf
  refine ⟨CuspForm.ofLe gammaMap_le_gamma1Map g, ?_⟩
  ext z
  change (CuspForm.ofLe gammaMap_le_gamma1Map g) z =
    (ModularForm.ofLe gammaMap_le_gamma1Map f) z
  rw [CuspForm.coe_ofLe, ModularForm.coe_ofLe]
  exact DFunLike.congr_fun hg z

/-- The `Gamma1 N` Eisenstein subspace and the cusp-form submodule have zero intersection in
weight at least three. -/
theorem disjoint_gamma1EisensteinSubspace_cuspFormSubmodule (hk : 3 ≤ k) :
    Disjoint (gamma1EisensteinSubspace N hk)
      (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k) := by
  rw [Submodule.disjoint_def]
  intro f hfE hfS
  apply ModularForm.ofLe_injective gammaMap_le_gamma1Map
  have hzero := (Submodule.disjoint_def.mp
    (disjoint_primitiveEisensteinSubspace_cuspFormSubmodule hk)) _
      ((mem_gamma1EisensteinSubspace_iff hk f).mp hfE)
      (ofLe_mem_cuspFormSubmodule hfS)
  simpa only [← ModularForm.ofLeₗ_apply, map_zero] using hzero

/-- In weight at least three, the `Gamma1 N` Eisenstein subspace and the cusp forms together
span all modular forms on `Gamma1 N`. -/
theorem sup_gamma1EisensteinSubspace_cuspFormSubmodule_eq_top (hk : 3 ≤ k) :
    gamma1EisensteinSubspace N hk ⊔
      cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k = ⊤ := by
  apply eq_top_iff.mpr
  intro f _
  have hf : ModularForm.ofLe gammaMap_le_gamma1Map f ∈
      primitiveEisensteinSubspace N hk ⊔ cuspFormSubmodule (gammaMap N) k := by
    rw [sup_primitiveEisensteinSubspace_cuspFormSubmodule_eq_top hk]
    exact Submodule.mem_top
  obtain ⟨e, he, s, hs, hes⟩ := Submodule.mem_sup.mp hf
  have htrace := congrArg traceGamma1 hes
  rw [map_add, traceGamma1_ofLe] at htrace
  have he' : traceGamma1 e ∈ gamma1EisensteinSubspace N hk :=
    (mem_gamma1EisensteinSubspace_iff hk _).mpr
      (traceGamma1_mem_primitiveEisensteinSubspace hk he)
  have hs' : traceGamma1 s ∈ cuspFormSubmodule (gamma1Map N) k :=
    traceGamma1_mem_cuspFormSubmodule hs
  have hindex : ((gammaMap N).relIndex (gamma1Map N) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.relIndex_ne_zero
  have hmem : ((gammaMap N).relIndex (gamma1Map N) : ℂ) • f ∈
      gamma1EisensteinSubspace N hk ⊔ cuspFormSubmodule (gamma1Map N) k := by
    rw [← htrace]
    exact Submodule.add_mem_sup he' hs'
  have hinv := Submodule.smul_mem
    (gamma1EisensteinSubspace N hk ⊔ cuspFormSubmodule (gamma1Map N) k)
    ((gammaMap N).relIndex (gamma1Map N) : ℂ)⁻¹ hmem
  simpa only [inv_smul_smul₀ hindex] using hinv

/-- The cusp--Eisenstein decomposition on `Gamma1 N` in weight at least three. -/
theorem isCompl_gamma1EisensteinSubspace_cuspFormSubmodule (hk : 3 ≤ k) :
    IsCompl (gamma1EisensteinSubspace N hk)
      (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⟨disjoint_gamma1EisensteinSubspace_cuspFormSubmodule hk,
    codisjoint_iff.mpr (sup_gamma1EisensteinSubspace_cuspFormSubmodule_eq_top hk)⟩

end TauCeti.EisensteinSeries
