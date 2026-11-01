/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Pullback
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Differentiation of meromorphic germs

Differentiation makes the field of meromorphic germs at a point a differential algebra over
the scalar field, acting by constant functions. The derivative uses only values on a punctured
neighbourhood, never the value assigned to a representative at its centre. It is constructed using
`Filter.Germ.map'` and Mathlib's `Filter.EventuallyEq.nhdsNE_deriv` and `MeromorphicAt.deriv`.

The bundled `TauCeti.meromorphicGerms.derivation` supplies linearity, the Leibniz rule, and
Mathlib's inverse, quotient and integer-power rules for derivations. Its representative
formula identifies this algebraic derivative with the usual analytic derivative, and
`TauCeti.meromorphicGerms.derivation_pullback` gives the chain rule for analytic changes of
coordinate preserving punctured neighbourhoods.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §1.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.meromorphicGerms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {a b : 𝕜}

/-- Differentiation of meromorphic germs, as a derivation over the constant field. -/
def derivation : Derivation 𝕜 (meromorphicGerms 𝕜 a) (meromorphicGerms 𝕜 a) where
  toFun φ := ⟨Germ.map' deriv (fun {_ _} h ↦ h.nhdsNE_deriv) φ.val, by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    rw [← hφ]
    exact coe_mem_meromorphicGerms.mpr hf.deriv⟩
  map_add' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    obtain ⟨g, hg, hψ⟩ := mem_meromorphicGerms_iff.mp ψ.2
    apply Subtype.ext
    simp only [Subring.coe_add, ← hφ, ← hψ, ← Germ.coe_add]
    apply Germ.coe_eq.mpr
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
    exact deriv_add hfz.differentiableAt hgz.differentiableAt
  map_smul' c φ := by
    obtain ⟨f, _, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    apply Subtype.ext
    simp only [coe_smul, ← hφ, ← Germ.coe_smul]
    apply Germ.coe_eq.mpr
    exact .of_forall fun z ↦ deriv_const_smul_field c f
  map_one_eq_zero' := by
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero, ← Germ.coe_zero]
    exact Germ.coe_eq.mpr (.of_forall fun z ↦ deriv_const z (1 : 𝕜))
  leibniz' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    obtain ⟨g, hg, hψ⟩ := mem_meromorphicGerms_iff.mp ψ.2
    apply Subtype.ext
    simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, Subring.coe_add,
      Subring.coe_mul, ← hφ, ← hψ, ← Germ.coe_mul]
    apply Germ.coe_eq.mpr
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
    simpa only [Pi.mul_apply, Pi.add_apply, mul_comm, add_comm] using
      deriv_mul hfz.differentiableAt hgz.differentiableAt

/-- The underlying punctured germ of the derivative is obtained by differentiating any
representative. No value at the centre is used. -/
theorem coe_derivation {φ : meromorphicGerms 𝕜 a} {f : 𝕜 → 𝕜}
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = f) :
    ((derivation φ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (deriv f : Germ (𝓝[≠] a) 𝕜) :=
  (congrArg (Germ.map' deriv (fun {_ _} h ↦ h.nhdsNE_deriv)) hφ).trans
    (Germ.map'_coe deriv (fun {_ _} h ↦ h.nhdsNE_deriv) f)

/-- Differentiation on the germ field agrees with differentiation of meromorphic functions. -/
@[simp]
theorem derivation_mk {f : 𝕜 → 𝕜} (hf : MeromorphicAt f a) :
    derivation (⟨(f : Germ (𝓝[≠] a) 𝕜), coe_mem_meromorphicGerms.mpr hf⟩ :
      meromorphicGerms 𝕜 a) =
      ⟨(deriv f : Germ (𝓝[≠] a) 𝕜), coe_mem_meromorphicGerms.mpr hf.deriv⟩ :=
  Subtype.ext (coe_derivation rfl)

/-- The coordinate germ has derivative one. In particular differentiation on the germ field
is nonzero. -/
@[simp]
theorem derivation_coordinate :
    derivation (⟨((fun z ↦ z - a) : Germ (𝓝[≠] a) 𝕜),
      coe_mem_meromorphicGerms.mpr ((MeromorphicAt.id a).sub (.const a a))⟩ :
      meromorphicGerms 𝕜 a) = 1 := by
  apply Subtype.ext
  rw [coe_derivation rfl, Subring.coe_one, ← Germ.coe_one]
  exact Germ.coe_eq.mpr (.of_forall fun z ↦ by simp)

/-- The chain rule on meromorphic germ fields. Pullback by an analytic coordinate map
intertwines differentiation up to multiplication by its derivative germ. -/
theorem derivation_pullback (g : 𝕜 → 𝕜) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] b)) (φ : meromorphicGerms 𝕜 b) :
    derivation (pullback g hg hga ht φ) =
      pullback g hg hga ht (derivation φ) *
        ⟨(deriv g : Germ (𝓝[≠] a) 𝕜), coe_mem_meromorphicGerms.mpr hg.meromorphicAt.deriv⟩ := by
  obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
  apply Subtype.ext
  rw [coe_derivation (by rw [coe_pullback, ← hφ, Germ.coe_compTendsto]),
    Subring.coe_mul, coe_pullback, coe_derivation hφ.symm, Germ.coe_compTendsto,
    ← Germ.coe_mul]
  apply Germ.coe_eq.mpr
  filter_upwards [ht.eventually hf.eventually_analyticAt,
    nhdsWithin_le_nhds hg.eventually_analyticAt] with z hfz hgz
  exact deriv_comp z hfz.differentiableAt hgz.differentiableAt

end TauCeti.meromorphicGerms
