/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Primitive
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import TauCeti.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# The cusp--Eisenstein decomposition for congruence subgroups

Let `Γ` be a subgroup of `SL(2, ℤ)` containing the principal congruence subgroup `Γ(N)`, such as
`Γ₁(N)` (via `CongruenceSubgroup.Gamma_le_Gamma1`) or `Γ₀(N)`. In weight at least three, the
Eisenstein subspace for `Γ` is the space of forms whose restriction to `Γ(N)` belongs to the span
of the primitive residue-class Eisenstein series. This file proves that it is complementary to
the cusp forms.

The spanning argument descends the corresponding decomposition for `Γ(N)` by the trace
`ModularForm.traceₗ` from `Γ(N)` to `Γ`. The trace preserves the primitive Eisenstein span: on
every coset, the slash transformation formula sends the series with residue `a` to the series
whose residue is the right translate of `a`. Tracing a cusp form remains cuspidal
(`ModularForm.traceₗ_mem_cuspFormSubmodule`), while tracing a restricted `Γ`-form multiplies it
by the finite relative index (`ModularForm.traceₗ_ofLe`).

## Main results

* `TauCeti.EisensteinSeries.congruenceEisensteinSubspace`: the Eisenstein subspace of `M_k(Γ)`
  detected after restriction to `Γ(N)`.
* `TauCeti.EisensteinSeries.isCompl_congruenceEisensteinSubspace_cuspFormSubmodule`: the
  cusp--Eisenstein decomposition of `M_k(Γ)` in weight at least three.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Section 4.2.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open UpperHalfPlane
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ} {k : ℤ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}

private abbrev gammaMap (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (Gamma N).map (mapGL ℝ)

private lemma quotientFunc_eisensteinSeriesMF (Γ : Subgroup SL(2, ℤ)) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N)
    (q : Γ.map (mapGL ℝ) ⧸ (gammaMap N).subgroupOf (Γ.map (mapGL ℝ))) :
    ∃ b : Fin 2 → ZMod N,
      SlashInvariantForm.quotientFunc (eisensteinSeriesMF hk a) q =
        eisensteinSeries b k := by
  induction q using QuotientGroup.induction_on' with
  | H h =>
      obtain ⟨γ, -, hmap⟩ := h.property
      refine ⟨a ᵥ* (SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ⁻¹), ?_⟩
      rw [SlashInvariantForm.quotientFunc_mk, coe_eisensteinSeriesMF, ← hmap, ← map_inv]
      have hslash : eisensteinSeries a k ∣[k] mapGL ℝ γ⁻¹ =
          eisensteinSeries a k ∣[k] γ⁻¹ :=
        (ModularForm.SL_slash (eisensteinSeries a k) γ⁻¹).symm
      rw [hslash, eisensteinSeries_slash_apply]

private lemma traceₗ_eisensteinSeriesMF_mem (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) :
    ModularForm.ofLe (Subgroup.map_mono hΓ)
        (traceₗ (Γ.map (mapGL ℝ)) (eisensteinSeriesMF hk a)) ∈
      primitiveEisensteinSubspace N hk := by
  classical
  let _ := Fintype.ofFinite
    (Γ.map (mapGL ℝ) ⧸ (gammaMap N).subgroupOf (Γ.map (mapGL ℝ)))
  choose b hb using fun q ↦ quotientFunc_eisensteinSeriesMF Γ hk a q
  have htrace : ModularForm.ofLe (Subgroup.map_mono hΓ)
      (traceₗ (Γ.map (mapGL ℝ)) (eisensteinSeriesMF hk a)) =
        ∑ q, eisensteinSeriesMF hk (b q) := by
    apply DFunLike.coe_injective
    rw [ModularForm.coe_ofLe, traceₗ_apply, ModularForm.coe_trace, FunLike.coe_sum]
    funext z
    rw [Finset.sum_apply]
    simp_rw [hb]
    simp only [coe_eisensteinSeriesMF]
    exact (Finset.sum_apply z Finset.univ
      (fun q ↦ eisensteinSeries (b q) k)).symm
  rw [htrace]
  exact Submodule.sum_mem _ fun q _ ↦ mem_primitiveEisensteinSubspace hk (b q)

private lemma traceₗ_mem_primitiveEisensteinSubspace (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    {f : ModularForm (gammaMap N) k} (hf : f ∈ primitiveEisensteinSubspace N hk) :
    ModularForm.ofLe (Subgroup.map_mono hΓ) (traceₗ (Γ.map (mapGL ℝ)) f) ∈
      primitiveEisensteinSubspace N hk := by
  have hle : primitiveEisensteinSubspace N hk ≤
      (primitiveEisensteinSubspace N hk).comap
        ((ModularForm.ofLeₗ (Subgroup.map_mono hΓ)).comp (traceₗ (Γ.map (mapGL ℝ)))) := by
    apply primitiveEisensteinSubspace_le hk
    intro a
    rw [Submodule.mem_comap, LinearMap.comp_apply, ModularForm.ofLeₗ_apply]
    exact traceₗ_eisensteinSeriesMF_mem hΓ hk a
  have hmem := hle hf
  simpa only [Submodule.mem_comap, LinearMap.comp_apply, ModularForm.ofLeₗ_apply] using hmem

/-- The Eisenstein subspace of `M_k(Γ)`, for a subgroup `Γ` of `SL(2, ℤ)` containing `Γ(N)`, in
weight at least three: a form belongs to it exactly when its restriction to `Γ(N)` belongs to the
primitive residue-class Eisenstein span. -/
def congruenceEisensteinSubspace (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    Submodule ℂ (ModularForm (Γ.map (mapGL ℝ)) k) :=
  (primitiveEisensteinSubspace N hk).comap (ModularForm.ofLeₗ (Subgroup.map_mono hΓ))

/-- The defining pullback of the primitive Eisenstein span along restriction to `Γ(N)`. -/
theorem congruenceEisensteinSubspace_def (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    congruenceEisensteinSubspace hΓ hk =
      (primitiveEisensteinSubspace N hk).comap (ModularForm.ofLeₗ (Subgroup.map_mono hΓ)) :=
  (rfl)

/-- Membership in the Eisenstein subspace of `M_k(Γ)` is detected after restriction to the
principal congruence subgroup. -/
theorem mem_congruenceEisensteinSubspace_iff (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    (f : ModularForm (Γ.map (mapGL ℝ)) k) :
    f ∈ congruenceEisensteinSubspace hΓ hk ↔
      ModularForm.ofLe (Subgroup.map_mono hΓ) f ∈ primitiveEisensteinSubspace N hk := by
  rw [congruenceEisensteinSubspace_def, Submodule.mem_comap, ModularForm.ofLeₗ_apply]

/-- The Eisenstein subspace of `M_k(Γ)` and the cusp-form submodule have zero intersection in
weight at least three. -/
theorem disjoint_congruenceEisensteinSubspace_cuspFormSubmodule (hΓ : Gamma N ≤ Γ)
    (hk : 3 ≤ k) :
    Disjoint (congruenceEisensteinSubspace hΓ hk)
      (cuspFormSubmodule (Γ.map (mapGL ℝ)) k) := by
  rw [Submodule.disjoint_def]
  intro f hfE hfS
  apply ModularForm.ofLe_injective (Subgroup.map_mono hΓ)
  have hzero := (Submodule.disjoint_def.mp
    (disjoint_primitiveEisensteinSubspace_cuspFormSubmodule hk)) _
      ((mem_congruenceEisensteinSubspace_iff hΓ hk f).mp hfE)
      (ModularForm.ofLe_mem_cuspFormSubmodule _ hfS)
  simpa only [← ModularForm.ofLeₗ_apply, map_zero] using hzero

/-- In weight at least three, the Eisenstein subspace of `M_k(Γ)` and the cusp forms together
span all modular forms on `Γ`. -/
theorem sup_congruenceEisensteinSubspace_cuspFormSubmodule_eq_top (hΓ : Gamma N ≤ Γ)
    (hk : 3 ≤ k) :
    congruenceEisensteinSubspace hΓ hk ⊔ cuspFormSubmodule (Γ.map (mapGL ℝ)) k = ⊤ := by
  apply eq_top_iff.mpr
  intro f _
  have hf : ModularForm.ofLe (Subgroup.map_mono hΓ) f ∈
      primitiveEisensteinSubspace N hk ⊔ cuspFormSubmodule (gammaMap N) k := by
    rw [sup_primitiveEisensteinSubspace_cuspFormSubmodule_eq_top hk]
    exact Submodule.mem_top
  obtain ⟨e, he, s, hs, hes⟩ := Submodule.mem_sup.mp hf
  have htrace := congrArg (traceₗ (Γ.map (mapGL ℝ))) hes
  rw [map_add, traceₗ_ofLe] at htrace
  have he' : traceₗ (Γ.map (mapGL ℝ)) e ∈ congruenceEisensteinSubspace hΓ hk :=
    (mem_congruenceEisensteinSubspace_iff hΓ hk _).mpr
      (traceₗ_mem_primitiveEisensteinSubspace hΓ hk he)
  have hs' : traceₗ (Γ.map (mapGL ℝ)) s ∈ cuspFormSubmodule (Γ.map (mapGL ℝ)) k :=
    ModularForm.traceₗ_mem_cuspFormSubmodule hs
  have hindex : ((gammaMap N).relIndex (Γ.map (mapGL ℝ)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.relIndex_ne_zero
  have hmem : ((gammaMap N).relIndex (Γ.map (mapGL ℝ)) : ℂ) • f ∈
      congruenceEisensteinSubspace hΓ hk ⊔ cuspFormSubmodule (Γ.map (mapGL ℝ)) k := by
    rw [← htrace]
    exact Submodule.add_mem_sup he' hs'
  have hinv := Submodule.smul_mem
    (congruenceEisensteinSubspace hΓ hk ⊔ cuspFormSubmodule (Γ.map (mapGL ℝ)) k)
    ((gammaMap N).relIndex (Γ.map (mapGL ℝ)) : ℂ)⁻¹ hmem
  simpa only [inv_smul_smul₀ hindex] using hinv

/-- The cusp--Eisenstein decomposition on a subgroup `Γ` of `SL(2, ℤ)` containing `Γ(N)`, in
weight at least three. For `Γ₁(N)`, take `hΓ := CongruenceSubgroup.Gamma_le_Gamma1 N`. -/
theorem isCompl_congruenceEisensteinSubspace_cuspFormSubmodule (hΓ : Gamma N ≤ Γ)
    (hk : 3 ≤ k) :
    IsCompl (congruenceEisensteinSubspace hΓ hk) (cuspFormSubmodule (Γ.map (mapGL ℝ)) k) :=
  ⟨disjoint_congruenceEisensteinSubspace_cuspFormSubmodule hΓ hk,
    codisjoint_iff.mpr (sup_congruenceEisensteinSubspace_cuspFormSubmodule_eq_top hΓ hk)⟩

end TauCeti.EisensteinSeries
