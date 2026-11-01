/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Germ
public import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Pullback of meromorphic germs

An analytic map which sends punctured neighbourhoods to punctured neighbourhoods induces a
field homomorphism on meromorphic germs. The punctured-neighbourhood condition is essential:
composition with a locally constant map would depend on the value of a representative at
its centre, which a meromorphic germ does not record.

Pullback depends only on the germ of the map and is contravariantly functorial. A local
homeomorphism analytic in both directions induces an equivalence of the meromorphic germ
fields. Its inverse is pullback by the inverse local homeomorphism.

The construction follows the analytic-germ pullback `TauCeti.analyticGerms.pullback`, using
Mathlib's `Filter.Germ.compTendsto` on punctured rather than ordinary neighbourhoods.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §1.
-/

public noncomputable section

open Filter Topology Function

namespace TauCeti.meromorphicGerms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {a b c : 𝕜}

/-- Pullback of meromorphic germs by an analytic map preserving punctured neighbourhoods. -/
def pullback (g : 𝕜 → 𝕜) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] b)) :
    meromorphicGerms 𝕜 b →+* meromorphicGerms 𝕜 a where
  toFun φ := ⟨(φ : Germ (𝓝[≠] b) 𝕜).compTendsto g ht, by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    rw [← hφ, Germ.coe_compTendsto, coe_mem_meromorphicGerms]
    rw [← hga] at hf
    exact hf.comp_analyticAt hg⟩
  map_zero' := Subtype.ext <| Germ.const_compTendsto 0 ht
  map_one' := Subtype.ext <| Germ.const_compTendsto 1 ht
  map_add' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    obtain ⟨h, hh, hψ⟩ := mem_meromorphicGerms_iff.mp ψ.2
    apply Subtype.ext
    simp only [Subring.coe_add, ← hφ, ← hψ, ← Germ.coe_add, Germ.coe_compTendsto]
    rfl
  map_mul' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    obtain ⟨h, hh, hψ⟩ := mem_meromorphicGerms_iff.mp ψ.2
    apply Subtype.ext
    simp only [Subring.coe_mul, ← hφ, ← hψ, ← Germ.coe_mul, Germ.coe_compTendsto]
    rfl

/-- Pullback is composition of the underlying punctured germs. -/
@[simp]
theorem coe_pullback (g : 𝕜 → 𝕜) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] b)) (φ : meromorphicGerms 𝕜 b) :
    ((pullback g hg hga ht φ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (φ : Germ (𝓝[≠] b) 𝕜).compTendsto g ht := (rfl)

/-- Pullback along the identity fixes every meromorphic germ. -/
@[simp]
theorem pullback_id (φ : meromorphicGerms 𝕜 a) :
    pullback (b := a) id analyticAt_id rfl tendsto_id φ = φ := by
  obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
  apply Subtype.ext
  rw [coe_pullback, ← hφ, Germ.coe_compTendsto]
  rfl

/-- Pullback depends only on the punctured germ of the analytic map. -/
theorem pullback_congr {g g' : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g a)
    (hg' : AnalyticAt 𝕜 g' a) (hga : g a = b) (hg'a : g' a = b)
    (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] b)) (ht' : Tendsto g' (𝓝[≠] a) (𝓝[≠] b))
    (h : g =ᶠ[𝓝[≠] a] g') : pullback g hg hga ht = pullback g' hg' hg'a ht' := by
  apply RingHom.ext
  intro φ
  obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
  apply Subtype.ext
  simp only [coe_pullback, ← hφ, Germ.coe_compTendsto]
  exact Germ.coe_eq.mpr (h.fun_comp f)

/-- Pullbacks compose in the opposite order to analytic maps. -/
@[simp]
theorem pullback_pullback (g : 𝕜 → 𝕜) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] b)) (h : 𝕜 → 𝕜) (hh : AnalyticAt 𝕜 h b)
    (hhb : h b = c) (hu : Tendsto h (𝓝[≠] b) (𝓝[≠] c)) (φ : meromorphicGerms 𝕜 c) :
    pullback g hg hga ht (pullback h hh hhb hu φ) =
      pullback (h ∘ g) (hh.comp_of_eq hg hga) (by simp [hga, hhb]) (hu.comp ht) φ := by
  obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
  apply Subtype.ext
  simp only [coe_pullback, ← hφ, Germ.coe_compTendsto]
  rfl

end TauCeti.meromorphicGerms

namespace OpenPartialHomeomorph

open TauCeti TauCeti.meromorphicGerms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {a : 𝕜}

/-- A local homeomorphism analytic in both directions identifies the meromorphic germ fields
at corresponding points. The equivalence is contravariant. -/
def meromorphicGermsEquiv (e : OpenPartialHomeomorph 𝕜 𝕜) (ha : a ∈ e.source)
    (he : AnalyticAt 𝕜 e a) (he' : AnalyticAt 𝕜 e.symm (e a)) :
    meromorphicGerms 𝕜 (e a) ≃+* meromorphicGerms 𝕜 a where
  toFun := fun φ ↦ pullback e he rfl (e.tendsto_nhdsNE ha) φ
  map_mul' := map_mul (pullback e he rfl (e.tendsto_nhdsNE ha))
  map_add' := map_add (pullback e he rfl (e.tendsto_nhdsNE ha))
  invFun := pullback e.symm he' (e.left_inv ha)
    (by simpa only [e.left_inv ha] using e.symm.tendsto_nhdsNE (e.map_source ha))
  left_inv φ := by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    apply Subtype.ext
    simp only [coe_pullback, ← hφ, Germ.coe_compTendsto]
    apply Germ.coe_eq.mpr
    filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds (e.map_source ha))] with z hz
    exact congrArg f (e.right_inv hz)
  right_inv φ := by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    apply Subtype.ext
    simp only [coe_pullback, ← hφ, Germ.coe_compTendsto]
    apply Germ.coe_eq.mpr
    filter_upwards [nhdsWithin_le_nhds (e.open_source.mem_nhds ha)] with z hz
    exact congrArg f (e.left_inv hz)

/-- The local equivalence acts by the pullback homomorphism. -/
@[simp]
theorem meromorphicGermsEquiv_apply (e : OpenPartialHomeomorph 𝕜 𝕜) (ha : a ∈ e.source)
    (he : AnalyticAt 𝕜 e a) (he' : AnalyticAt 𝕜 e.symm (e a))
    (φ : meromorphicGerms 𝕜 (e a)) :
    e.meromorphicGermsEquiv ha he he' φ = pullback e he rfl (e.tendsto_nhdsNE ha) φ := (rfl)

/-- The inverse local equivalence is pullback by the inverse map. -/
@[simp]
theorem meromorphicGermsEquiv_symm_apply (e : OpenPartialHomeomorph 𝕜 𝕜) (ha : a ∈ e.source)
    (he : AnalyticAt 𝕜 e a) (he' : AnalyticAt 𝕜 e.symm (e a))
    (φ : meromorphicGerms 𝕜 a) :
    (e.meromorphicGermsEquiv ha he he').symm φ = pullback e.symm he' (e.left_inv ha)
      (by simpa only [e.left_inv ha] using e.symm.tendsto_nhdsNE (e.map_source ha)) φ := (rfl)

end OpenPartialHomeomorph
