/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Canonical evaluation into the strong bidual

For a topological vector space `E` over a normed field `𝕜` with continuous scalar multiplication,
every singleton `{x}` is von Neumann bounded, so evaluation at `x` is a continuous linear
functional on the strong dual `StrongDual 𝕜 E` (`E →L[𝕜] 𝕜` with the topology of uniform
convergence on von Neumann bounded sets). Varying `x` defines the canonical linear evaluation map
`StrongDual.eval 𝕜 E : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`, `x ↦ (f ↦ f x)`, obtained by
specializing `ContinuousLinearMap.applyₗ` to the scalar codomain `𝕜`. Unlike on normed spaces
(`NormedSpace.inclusionInDoubleDual`), this map need not be continuous unless `E` is
infrabarrelled.

It is injective if and only if continuous linear functionals separate the points of `E`
(`StrongDual.eval_injective_iff`), and it intertwines every continuous linear map `S : E →L[𝕜] F`
with its double strong transpose `ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 S)`
(`StrongDual.precomp_precomp_eval_apply`, `StrongDual.precomp_precomp_comp_eval`).

When `E` and `F` carry continuous linear equivalences `eE` and `eF` with their strong biduals
whose underlying maps agree with `StrongDual.eval`, the same pairing identity upgrades naturality
to continuous linear maps (`StrongDual.precomp_precomp_comp_eq_of_coe_eq_eval`) and recovers `S`
from its double strong transpose (`StrongDual.symm_comp_precomp_precomp_comp_eq_of_coe_eq_eval`).
Moreover, if `e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` agrees with `StrongDual.eval 𝕜 E`, then
the inverse of its strong transpose,
`ContinuousLinearEquiv.arrowCongr e (ContinuousLinearEquiv.refl 𝕜 𝕜)`, is a topological linear
isomorphism from `StrongDual 𝕜 E` onto its own strong bidual acting by canonical evaluation
`Ξ ↦ Ξ φ` (`StrongDual.arrowCongr_refl_apply_of_coe_eq_eval`): the strong dual of a strongly
reflexive space is strongly reflexive, with canonical evaluation inverse to the strong transpose of
evaluation on `E`. Likewise, any dual pair of equivalences `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F` compatible with evaluation induces strong-bidual evaluation
equivalences on both `E` and `F` (`StrongDual.bidualEquivOfDualEquiv`,
`StrongDual.dualBidualEquivOfDualEquiv`).

## Main declarations

* `StrongDual.eval`: canonical linear evaluation `E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`.
* `StrongDual.eval_injective_iff`: `StrongDual.eval 𝕜 E` is injective iff `SeparatingDual 𝕜 E`.
* `StrongDual.precomp_precomp_eval_apply`: naturality of `StrongDual.eval` under double strong
  transposition.
* `StrongDual.precomp_precomp_comp_eq_of_coe_eq_eval`: naturality of strong-bidual continuous
  linear equivalences agreeing with `StrongDual.eval`.
* `StrongDual.bidualEquivOfDualEquiv`, `StrongDual.dualBidualEquivOfDualEquiv`: strong-bidual
  evaluation equivalences constructed from compatible dual identifications.
* `StrongDual.arrowCongr_refl_apply_of_coe_eq_eval`: for an evaluation isomorphism
  `e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`,
  `ContinuousLinearEquiv.arrowCongr e (.refl 𝕜 𝕜)` acts by canonical evaluation on
  `StrongDual 𝕜 E`, inverse to the strong transpose `precomp 𝕜 e`.

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapter IV, §3, no. 3.
* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan 19 (1967), 366–383.
-/

public section

open ContinuousLinearMap

namespace StrongDual

variable (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousSMul 𝕜 E]

/-- Canonical linear evaluation `x ↦ (f ↦ f x)` from a topological vector space `E` into its
strong bidual `StrongDual 𝕜 (StrongDual 𝕜 E)`, specializing `ContinuousLinearMap.applyₗ` to the
scalar codomain `𝕜`. -/
def eval : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  ContinuousLinearMap.applyₗ (E := E) 𝕜 (RingHom.id 𝕜)

variable {𝕜 E}

@[simp]
theorem eval_apply (x : E) (f : StrongDual 𝕜 E) : eval 𝕜 E x f = f x :=
  (rfl)

/-- Canonical evaluation into the strong bidual is injective if and only if continuous linear
functionals separate points of `E`. -/
theorem eval_injective_iff : Function.Injective (eval 𝕜 E) ↔ SeparatingDual 𝕜 E := by
  refine ⟨fun hinj ↦ ⟨fun x hx ↦ ?_⟩, fun _ x y h ↦ ?_⟩
  · contrapose! hx
    exact hinj (ContinuousLinearMap.ext fun f ↦ by simp [hx f])
  · exact (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun f ↦ congr($h f)

/-- When continuous linear functionals separate points of `E`, canonical evaluation into the strong
bidual is injective. -/
theorem eval_injective [SeparatingDual 𝕜 E] : Function.Injective (eval 𝕜 E) :=
  eval_injective_iff.2 inferInstance

section Naturality

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousSMul 𝕜 F]

/-- Pointwise naturality of canonical evaluation into the strong bidual under the double strong
transpose of a continuous linear map. -/
theorem precomp_precomp_eval_apply (S : E →L[𝕜] F) (x : E) :
    precomp 𝕜 (precomp 𝕜 S : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) (eval 𝕜 E x) =
      eval 𝕜 F (S x) := by
  ext f
  rfl

/-- Operator naturality of canonical evaluation into the strong bidual under the double strong
transpose of a continuous linear map. -/
theorem precomp_precomp_comp_eval (S : E →L[𝕜] F) :
    (precomp 𝕜 (precomp 𝕜 S : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)).toLinearMap.comp (eval 𝕜 E) =
      (eval 𝕜 F).comp S.toLinearMap := by
  ext x f
  rfl

/-- If `eE` and `eF` are strong-bidual continuous linear equivalences whose underlying maps are
canonical evaluation, every continuous linear map `S : E →L[𝕜] F` intertwines them with its double
strong transpose `S′′`. -/
theorem precomp_precomp_comp_eq_of_coe_eq_eval
    (eE : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) (heE : ⇑eE = eval 𝕜 E)
    (eF : F ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) (heF : ⇑eF = eval 𝕜 F) (S : E →L[𝕜] F) :
    (precomp 𝕜 (precomp 𝕜 S : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)).comp
        eE.toContinuousLinearMap =
      eF.toContinuousLinearMap.comp S := by
  ext x f
  have hx := DFunLike.congr_fun (congr_fun heE x) (f.comp S)
  have hSx := DFunLike.congr_fun (congr_fun heF (S x)) f
  simpa [comp_apply, precomp_apply] using hx.trans hSx.symm

/-- Under strong-bidual evaluation equivalences `eE` and `eF`, a continuous linear map `S` is
recovered from its double strong transpose `S′′` as `eF⁻¹ ∘ S′′ ∘ eE`. -/
theorem symm_comp_precomp_precomp_comp_eq_of_coe_eq_eval
    (eE : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) (heE : ⇑eE = eval 𝕜 E)
    (eF : F ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) (heF : ⇑eF = eval 𝕜 F) (S : E →L[𝕜] F) :
    eF.symm.toContinuousLinearMap.comp
        ((precomp 𝕜 (precomp 𝕜 S : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)).comp
          eE.toContinuousLinearMap) =
      S := by
  rw [precomp_precomp_comp_eq_of_coe_eq_eval eE heE eF heF S, ← comp_assoc]
  ext x
  simp

end Naturality

section DualReflexivity

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

omit [ContinuousSMul 𝕜 E] in
/-- Given topological linear isomorphisms `a : StrongDual 𝕜 E ≃L[𝕜] F` and
`b : E ≃L[𝕜] StrongDual 𝕜 F` compatible with evaluation (`b x (a ℓ) = ℓ x`), composing `b` with
`a.symm.arrowCongr (.refl 𝕜 𝕜)` gives a topological linear isomorphism
`E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` whose underlying map is canonical evaluation. -/
def bidualEquivOfDualEquiv (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F) :
    E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  b.trans (a.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))

omit [ContinuousSMul 𝕜 E] in
theorem bidualEquivOfDualEquiv_apply (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) (x : E) (ℓ : StrongDual 𝕜 E) :
    bidualEquivOfDualEquiv a b x ℓ = ℓ x :=
  h x ℓ

theorem coe_bidualEquivOfDualEquiv (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    ⇑(bidualEquivOfDualEquiv a b) = eval 𝕜 E := by
  ext x ℓ
  exact h x ℓ

omit [ContinuousSMul 𝕜 E] in
/-- Given compatible `a : StrongDual 𝕜 E ≃L[𝕜] F` and `b : E ≃L[𝕜] StrongDual 𝕜 F`, the dual
partner `F` also carries a strong-bidual topological linear isomorphism agreeing with canonical
evaluation `eval 𝕜 F`. -/
def dualBidualEquivOfDualEquiv (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F) :
    F ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F) :=
  a.symm.trans (b.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))

omit [ContinuousSMul 𝕜 E] in
theorem dualBidualEquivOfDualEquiv_apply (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) (f : F) (φ : StrongDual 𝕜 F) :
    dualBidualEquivOfDualEquiv a b f φ = φ f := by
  calc dualBidualEquivOfDualEquiv a b f φ
      = (a.symm f) (b.symm φ) := rfl
    _ = b (b.symm φ) (a (a.symm f)) := (h (b.symm φ) (a.symm f)).symm
    _ = φ f := by rw [b.apply_symm_apply, a.apply_symm_apply]

omit [ContinuousSMul 𝕜 E] in
theorem coe_dualBidualEquivOfDualEquiv [ContinuousSMul 𝕜 F]
    (a : StrongDual 𝕜 E ≃L[𝕜] F) (b : E ≃L[𝕜] StrongDual 𝕜 F)
    (h : ∀ (x : E) (ℓ : StrongDual 𝕜 E), b x (a ℓ) = ℓ x) :
    ⇑(dualBidualEquivOfDualEquiv a b) = eval 𝕜 F := by
  ext f φ
  exact dualBidualEquivOfDualEquiv_apply a b h f φ

/-- If `e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` agrees with canonical evaluation `eval 𝕜 E`,
then `ContinuousLinearEquiv.arrowCongr e (.refl 𝕜 𝕜)` is a topological linear isomorphism from
`StrongDual 𝕜 E` onto its strong bidual, inverse to the strong transpose `precomp 𝕜 e`, and it acts
by canonical evaluation `Ξ ↦ Ξ φ`. -/
theorem arrowCongr_refl_apply_of_coe_eq_eval
    (e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) (he : ⇑e = eval 𝕜 E)
    (φ : StrongDual 𝕜 E) (Ξ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    ContinuousLinearEquiv.arrowCongr e (ContinuousLinearEquiv.refl 𝕜 𝕜) φ Ξ = Ξ φ := by
  calc ContinuousLinearEquiv.arrowCongr e (ContinuousLinearEquiv.refl 𝕜 𝕜) φ Ξ
      = φ (e.symm Ξ) := rfl
    _ = e (e.symm Ξ) φ := (DFunLike.congr_fun (congr_fun he (e.symm Ξ)) φ).symm
    _ = Ξ φ := by rw [e.apply_symm_apply]

omit [ContinuousSMul 𝕜 E] in
/-- The inverse of `ContinuousLinearEquiv.arrowCongr e (.refl 𝕜 𝕜)` is the strong transpose
`precomp 𝕜 e` of `e`. -/
theorem arrowCongr_refl_symm_toContinuousLinearMap (e : E ≃L[𝕜] F) :
    (ContinuousLinearEquiv.arrowCongr e (ContinuousLinearEquiv.refl 𝕜 𝕜)).symm.toContinuousLinearMap
      = precomp 𝕜 e.toContinuousLinearMap :=
  (rfl)

end DualReflexivity

end StrongDual
