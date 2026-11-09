/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Radical
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rechart

/-!
# Reduced holomorphic node equations

Weierstrass division identifies a distinguished polynomial quotient with its holomorphic
germ quotient. Radicality can therefore be checked over the fraction field of the base
germ ring. The theorem `isRadical_span_nodeEquation` proves that `xy - s(b)` generates a
radical ideal for every holomorphic base germ `s`, even if `s` is zero or has a multiple zero.
The invertible change `x = u + v`, `y = u - v` gives the
quadratic normal form `u² - v² - s(b)`. The nonzero coefficient `v² + s(b)`, not the
derivative of `s`, ensures reducedness. This is a statement about the actual holomorphic
germ quotient; no analytic-space category or global-sections exactness is assumed.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II,
  for Weierstrass division and analytic hypersurface local rings.
-/

public noncomputable section

open Polynomial Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The quadratic normal form of `xy = s(b)` has a radical defining ideal, including when
`s` is zero or has arbitrarily high vanishing order. Here `v` is the extra base coordinate
and `u` is the final vertical coordinate. -/
private theorem isRadical_span_nodeNormalForm [FiniteDimensional ℂ E] (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (Ideal.span {(evalVertical (b, (0 : ℂ)) 0
      (X ^ 2 - C (evalVertical b 0 (X ^ 2 + C s))))}).IsRadical := by
  apply isRadical_span_evalVertical_X_pow_sub_C
  · apply (map_ne_zero_iff _ (evalVertical_injective b 0)).mpr
    exact (monic_X_pow_add_C s (by decide : 2 ≠ 0)).ne_zero
  · decide

/-- The holomorphic germ of `xy - s(b)` at a point of the ambient base times two lines.
The parameter is an arbitrary holomorphic base germ, not a globally defined function. -/
def nodeEquation (b : E) (x y : ℂ)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk ((b, x), y) :=
  germOfContMDiff (fun z : (E × ℂ) × ℂ ↦ z.1.2 * z.2)
      (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, x), y) -
    stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) (fun z ↦ z.1.1)
      (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, x), y) s

/-- In any representative of the base germ, the node equation is `xy - s(b)`. -/
theorem toFilterGerm_nodeEquation (b : E) (x y : ℂ)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b)
    {f : E → ℂ} (hf : toFilterGerm 𝓘(ℂ, E) E b (𝓝 b) le_rfl s = f) :
    toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, x), y) (𝓝 ((b, x), y)) le_rfl
      (nodeEquation b x y s) = (fun z : (E × ℂ) × ℂ ↦ z.1.2 * z.2 - f z.1.1) := by
  rw [nodeEquation, map_sub, toFilterGerm_germOfContMDiff, toFilterGerm_stalkPrecomp,
    hf, Germ.coe_compTendsto, ← Germ.coe_sub]
  rfl

/-- Evaluation of the defining equation at its ambient base point. -/
@[simp]
theorem eval_nodeEquation (b : E) (x y : ℂ)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    eval 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, x), y) (nodeEquation b x y s) =
      x * y - eval 𝓘(ℂ, E) E b s := by
  simp [nodeEquation, eval_stalkPrecomp]

-- Reducibility keeps the preserved base coordinate visible in dependent stalk types.
private abbrev nodeCoordinateChange :
    ((E × ℂ) × ℂ) ≃ₘ^ω⟮𝓘(ℂ, (E × ℂ) × ℂ), 𝓘(ℂ, (E × ℂ) × ℂ)⟯ ((E × ℂ) × ℂ) where
  toFun p := ((p.1.1, p.2 + p.1.2), p.2 - p.1.2)
  invFun p := ((p.1.1, (p.1.2 - p.2) / 2), (p.1.2 + p.2) / 2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  contMDiff_toFun := contMDiff_iff_contDiff.mpr (by dsimp; fun_prop)
  contMDiff_invFun := contMDiff_iff_contDiff.mpr (by dsimp; fun_prop)

private theorem nodeCoordinateChange_apply (p : (E × ℂ) × ℂ) :
    nodeCoordinateChange p = ((p.1.1, p.2 + p.1.2), p.2 - p.1.2) := (rfl)

private theorem nodeCoordinateChange_equation (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)
        nodeCoordinateChange nodeCoordinateChange.contMDiff ((b, (0 : ℂ)), 0)
        (nodeEquation b (0 + 0) (0 - 0) s) =
      evalVertical (b, (0 : ℂ)) 0 (X ^ 2 - C (evalVertical b 0 (X ^ 2 + C s))) := by
  obtain ⟨f, _, hfs⟩ := exists_toFilterGerm_eq b s
  apply toFilterGerm_nhds_injective ((b, (0 : ℂ)), 0)
  rw [toFilterGerm_stalkPrecomp]
  -- The pullback's source stalk is indexed by the computed image of the origin.
  erw [toFilterGerm_nodeEquation b (0 + 0) (0 - 0) s (hfs _ le_rfl)]
  simp only [map_sub, map_pow, map_add, evalVertical_X, evalVertical_C,
    toFilterGerm_germOfContMDiff, toFilterGerm_stalkPrecomp, hfs _ le_rfl,
    Germ.coe_compTendsto, ← Germ.coe_add, ← Germ.coe_pow, ← Germ.coe_sub]
  congr 1
  funext p
  simp only [Function.comp_apply, nodeCoordinateChange_apply, sub_zero,
    Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
  ring

/-- **All holomorphic node equations are reduced.** The ideal `(xy - s(b))` at `(b, 0, 0)`
is radical for every holomorphic base germ, including permanent nodes and singular total
spaces such as `xy = b²`. If `s(b) ≠ 0`, the equation is a unit and its ideal is the whole ring. -/
theorem isRadical_span_nodeEquation [FiniteDimensional ℂ E] (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (Ideal.span {nodeEquation b 0 0 s}).IsRadical := by
  let e := nodeCoordinateChange (E := E)
  let p := ((b, (0 : ℂ)), (0 : ℂ))
  let F := stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) e e.contMDiff p
  have hrad : (Ideal.span {F (nodeEquation b (0 + 0) (0 - 0) s)}).IsRadical := by
    rw [nodeCoordinateChange_equation]
    exact isRadical_span_nodeNormalForm b s
  have hmap : (Ideal.span {nodeEquation b (0 + 0) (0 - 0) s}).map F =
      Ideal.span {F (nodeEquation b (0 + 0) (0 - 0) s)} := by
    simp only [Ideal.map_span, Set.image_singleton]
  rw [← hmap] at hrad
  have h := hrad.comap (f := F)
  rw [Ideal.comap_map_of_bijective F (e.stalkPrecomp_bijective p)] at h
  -- Eliminate the coordinate equalities dependently, including the stalk ring instances.
  have transport (x y : ℂ) (hx : x = 0) (hy : y = 0) :
      (Ideal.span {nodeEquation b x y s}).IsRadical →
        (Ideal.span {nodeEquation b 0 0 s}).IsRadical := by
    subst x y
    exact id
  exact transport _ _ (add_zero _) (sub_zero _) h

end TauCeti.holomorphicStructureSheaf
