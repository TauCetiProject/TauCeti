/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Product.Basic
public import TauCeti.Topology.Maps.Proper.Basic

/-!
# Properness of products of analytic toric maps

Under the canonical product comparisons `TauCeti.Toric.Fan.analyticProdHomeomorph` of the source
and target realizations, the analytic map of a componentwise product `f.prodMap g` of fan
morphisms is the product of the analytic maps of `f` and `g`
(`TauCeti.Toric.Fan.analyticProdHomeomorph_naturality`). Since homeomorphisms are proper, the
analytic map of `f.prodMap g` is proper exactly when that product map is. Hence a product of
proper toric maps is proper, and, when both source fans are nonempty, a product of toric maps is
proper exactly when both factors are.

The nonemptiness hypotheses cannot be dropped: if the second source fan has no cones, the source
realization of `f.prodMap g` is empty, so its analytic map is proper whatever `f` is.

## Main declarations

* `TauCeti.Toric.FanHom.isProperMap_analyticMap_prodMap`: the analytic map of a product of fan
  morphisms with proper analytic maps is proper.
* `TauCeti.Toric.FanHom.isProperMap_analyticMap_prodMap_iff`: for nonempty source fans, the
  analytic map of `f.prodMap g` is proper exactly when those of `f` and `g` are.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open Topology

namespace TauCeti.Toric.FanHom

universe u

variable {N₁ N₂ N₁' N₂' V₁ V₂ V₁' V₂' : Type u} [AddCommGroup N₁] [AddCommGroup N₂]
  [AddCommGroup N₁'] [AddCommGroup N₂'] [AddCommGroup V₁] [AddCommGroup V₂]
  [AddCommGroup V₁'] [AddCommGroup V₂'] [Module ℝ V₁] [Module ℝ V₂] [Module ℝ V₁']
  [Module ℝ V₂'] {i₁ : N₁ →+ V₁} {i₂ : N₂ →+ V₂} {i₁' : N₁' →+ V₁'} {i₂' : N₂' →+ V₂'}
  {Φ₁ : Fan i₁} {Φ₂ : Fan i₂} {Ψ₁ : Fan i₁'} {Ψ₂ : Fan i₂'}
  (f : FanHom Φ₁ Ψ₁) (g : FanHom Φ₂ Ψ₂) (hΦ₁ : Φ₁.IsRegular) (hΦ₂ : Φ₂.IsRegular)
  (hΨ₁ : Ψ₁.IsRegular) (hΨ₂ : Ψ₂.IsRegular)

/-- The analytic map of a product of fan morphisms is proper exactly when the product of the
analytic maps of the factors is proper: the two maps are conjugate under the product
comparisons of the source and target realizations. -/
private theorem isProperMap_analyticMap_prodMap_iff_isProperMap_prodMap :
    IsProperMap ((f.prodMap g).analyticMap (Fan.IsRegular.prod Φ₁ Φ₂ hΦ₁ hΦ₂)
        (Fan.IsRegular.prod Ψ₁ Ψ₂ hΨ₁ hΨ₂)) ↔
      IsProperMap (Prod.map (f.analyticMap hΦ₁ hΨ₁) (g.analyticMap hΦ₂ hΨ₂)) := by
  rw [← (Ψ₁.analyticProdHomeomorph Ψ₂ hΨ₁ hΨ₂).comp_isProperMap_iff,
    ← (Φ₁.analyticProdHomeomorph Φ₂ hΦ₁ hΦ₂).comp_isProperMap_iff' (f := Prod.map _ _)]
  exact iff_of_eq (congrArg IsProperMap
    (funext (Fan.analyticProdHomeomorph_naturality Φ₁ Φ₂ hΦ₁ hΦ₂ f g hΨ₁ hΨ₂)))

/-- The analytic map of a componentwise product of fan morphisms whose analytic maps are proper
is proper. No nonemptiness hypothesis is needed. -/
theorem isProperMap_analyticMap_prodMap (hf : IsProperMap (f.analyticMap hΦ₁ hΨ₁))
    (hg : IsProperMap (g.analyticMap hΦ₂ hΨ₂)) :
    IsProperMap ((f.prodMap g).analyticMap (Fan.IsRegular.prod Φ₁ Φ₂ hΦ₁ hΦ₂)
      (Fan.IsRegular.prod Ψ₁ Ψ₂ hΨ₁ hΨ₂)) :=
  (isProperMap_analyticMap_prodMap_iff_isProperMap_prodMap f g hΦ₁ hΦ₂ hΨ₁ hΨ₂).2
    (hf.prodMap hg)

/-- For nonempty source fans, the analytic map of a componentwise product of fan morphisms is
proper exactly when the analytic maps of both factors are proper. The nonemptiness hypotheses
are necessary: if one source fan has no cones, the source realization of the product is empty,
so its analytic map is proper whatever the other factor is. -/
theorem isProperMap_analyticMap_prodMap_iff (hΦ₁0 : Nonempty Φ₁.cones)
    (hΦ₂0 : Nonempty Φ₂.cones) :
    IsProperMap ((f.prodMap g).analyticMap (Fan.IsRegular.prod Φ₁ Φ₂ hΦ₁ hΦ₂)
        (Fan.IsRegular.prod Ψ₁ Ψ₂ hΨ₁ hΨ₂)) ↔
      IsProperMap (f.analyticMap hΦ₁ hΨ₁) ∧ IsProperMap (g.analyticMap hΦ₂ hΨ₂) := by
  have : Nonempty (Φ₁.analyticRealization hΦ₁) :=
    ⟨Φ₁.analyticDistinguishedPoint hΦ₁ hΦ₁0.some⟩
  have : Nonempty (Φ₂.analyticRealization hΦ₂) :=
    ⟨Φ₂.analyticDistinguishedPoint hΦ₂ hΦ₂0.some⟩
  rw [isProperMap_analyticMap_prodMap_iff_isProperMap_prodMap, isProperMap_prodMap_iff]

end TauCeti.Toric.FanHom
