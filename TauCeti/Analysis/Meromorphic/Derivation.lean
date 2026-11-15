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

private def differentiate (φ : meromorphicGerms 𝕜 a) : meromorphicGerms 𝕜 a :=
  ⟨Germ.map' deriv (fun {_ _} h ↦ h.nhdsNE_deriv) φ.val, by
    obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
    rw [← hφ]
    exact (Germ.map'_coe deriv (fun {_ _} h ↦ h.nhdsNE_deriv) f).symm ▸
      coe_mem_meromorphicGerms.mpr hf.deriv⟩

private theorem coe_differentiate {φ : meromorphicGerms 𝕜 a} {f : 𝕜 → 𝕜}
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = f) :
    ((differentiate φ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (deriv f : Germ (𝓝[≠] a) 𝕜) :=
  (congrArg (Germ.map' deriv (fun {_ _} h ↦ h.nhdsNE_deriv)) hφ).trans
    (Germ.map'_coe deriv (fun {_ _} h ↦ h.nhdsNE_deriv) f)

private theorem differentiate_mk {f : 𝕜 → 𝕜} (hf : MeromorphicAt f a) :
    differentiate (mk f hf) = mk (deriv f) hf.deriv :=
  Subtype.ext ((coe_differentiate (coe_mk f hf)).trans (coe_mk (deriv f) hf.deriv).symm)

/-- Differentiation of meromorphic germs, as a `𝕜`-derivation, where scalars act by
constant functions. -/
def derivation : Derivation 𝕜 (meromorphicGerms 𝕜 a) (meromorphicGerms 𝕜 a) where
  toFun := differentiate
  map_add' φ ψ := by
    obtain ⟨f, hf, rfl⟩ := exists_mk φ
    obtain ⟨g, hg, rfl⟩ := exists_mk ψ
    simp only [← mk_add, differentiate_mk, mk_eq_mk_iff]
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
    exact deriv_add hfz.differentiableAt hgz.differentiableAt
  map_smul' c φ := by
    obtain ⟨f, hf, rfl⟩ := exists_mk φ
    simp only [← mk_smul, differentiate_mk, mk_eq_mk_iff]
    exact .of_forall fun z ↦ deriv_const_smul_field c f
  map_one_eq_zero' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ← mk_one, differentiate_mk, ← mk_zero,
      mk_eq_mk_iff]
    exact .of_forall fun z ↦ deriv_const z (1 : 𝕜)
  leibniz' φ ψ := by
    obtain ⟨f, hf, rfl⟩ := exists_mk φ
    obtain ⟨g, hg, rfl⟩ := exists_mk ψ
    simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, ← mk_mul, ← mk_add,
      differentiate_mk, mk_eq_mk_iff]
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
    rw [deriv_mul hfz.differentiableAt hgz.differentiableAt]
    simp only [Pi.mul_apply, Pi.add_apply]
    ring

/-- The underlying punctured germ of the derivative is obtained by differentiating any
representative. No value at the centre is used. -/
theorem coe_derivation {φ : meromorphicGerms 𝕜 a} {f : 𝕜 → 𝕜}
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = f) :
    ((derivation φ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (deriv f : Germ (𝓝[≠] a) 𝕜) :=
  coe_differentiate hφ

/-- Differentiation on the germ field agrees with differentiation of meromorphic functions. -/
@[simp]
theorem derivation_mk {f : 𝕜 → 𝕜} (hf : MeromorphicAt f a) :
    derivation (mk f hf) = mk (deriv f) hf.deriv :=
  differentiate_mk hf

/-- The coordinate germ has derivative one. In particular differentiation on the germ field
is nonzero. -/
@[simp]
theorem derivation_coordinate :
    derivation (coordinate a) = 1 := by
  have hcoord : coordinate a = mk (fun z ↦ z - a) ((MeromorphicAt.id a).sub (.const a a)) :=
    Subtype.ext (coe_coordinate.trans (coe_mk _ _).symm)
  rw [hcoord, derivation_mk, ← mk_one, mk_eq_mk_iff]
  exact .of_forall fun z ↦ by simp

/-- The chain rule on meromorphic germ fields. Pullback by an analytic coordinate map
intertwines differentiation up to multiplication by its derivative germ. -/
theorem derivation_pullback (g : 𝕜 → 𝕜) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] b)) (φ : meromorphicGerms 𝕜 b) :
    derivation (pullback g hg hga ht φ) =
      pullback g hg hga ht (derivation φ) * mk (deriv g) hg.meromorphicAt.deriv := by
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  simp only [pullback_mk, derivation_mk, ← mk_mul, mk_eq_mk_iff]
  filter_upwards [ht.eventually hf.eventually_analyticAt,
    nhdsWithin_le_nhds hg.eventually_analyticAt] with z hfz hgz
  exact deriv_comp z hfz.differentiableAt hgz.differentiableAt

end TauCeti.meromorphicGerms
