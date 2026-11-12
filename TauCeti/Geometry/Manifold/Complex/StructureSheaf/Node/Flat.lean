/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Node.NormalForm
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.OffNodeChart
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Flat
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback

/-!
# Flatness of the smoothing family `xy = s(b)` over its base

The local model for smoothing a node over a base `E` is the hypersurface
`N_s = {(b, x, y) | xy = s(b)}`, for a holomorphic base germ `s`. This file proves that `N_s` is
flat over the base at every point, for every `s`: pulling base germs back along `(b, x, y) ↦ b`
makes the local ring of `N_s` a flat algebra over the holomorphic stalk of the base
(`TauCeti.holomorphicStructureSheaf.flat_quotientMk_comp_stalkPrecomp_smoothingEquation`). No
condition is imposed on `s`: it may vanish identically (a permanent node). When `s` and its
differential both vanish at `b`, as for `xy = b²`, the total space is singular at the node.

At the node the local ring is flat over the germs `𝒪_{E × ℂ, (b, 0)}` in the transverse
coordinates `(b, v)` (`nodeTransverseHom_flat`), and these are flat over `𝒪_{E, b}`
(`flat_stalkPrecomp_fst`); the composite is the pullback from the base
(`nodeTransverseHom_comp_stalkPrecomp_fst`). This gives
`TauCeti.holomorphicStructureSheaf.flat_quotientMk_comp_stalkPrecomp_nodeEquation` in the
coordinates `((b, x), y)` of `Node.NormalForm`. Away from the node a product chart
(`offNodeChartFstEquiv`, `offNodeChartSndEquiv`) identifies the local ring of `N_s` with the
germs on `E × ℂ`, which are again flat over the base. Off `N_s` the local ring is zero.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the local models `xy = a` of nodal families.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II,
  for Weierstrass division and analytic hypersurface local rings.
-/

public section

open Filter
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The associator `((b, x), y) ↦ (b, x, y)` carries the local equation of `N_s` in the
coordinates of `OffNodeChart` to the node equation in the coordinates of `Node.NormalForm`. -/
private theorem stalkPrecomp_assoc_smoothingEquation (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) (fun z ↦ (z.1.1, z.1.2, z.2))
        (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0)
        (smoothingEquation (b, 0, 0) s) = nodeEquation b 0 0 s := by
  obtain ⟨S, -, hS⟩ := exists_toFilterGerm_eq b s
  apply toFilterGerm_nhds_injective ((b, (0 : ℂ)), (0 : ℂ))
  rw [toFilterGerm_stalkPrecomp, toFilterGerm_smoothingEquation (S := S) (hS _ le_rfl),
    toFilterGerm_nodeEquation b 0 0 s (hS _ le_rfl), Germ.coe_compTendsto]
  -- Both sides are the germ of `((b, x), y) ↦ x * y - S b`.
  rfl

variable [FiniteDimensional ℂ E]

/-- **The node is flat over the base.** For every holomorphic base germ `s`, pulling base germs
back along `((b, x), y) ↦ b` makes the local ring `𝒪 ⧸ (xy - s(b))` at the node `((b, 0), 0)` a
flat algebra over `𝒪_{E, b}`. -/
theorem flat_quotientMk_comp_stalkPrecomp_nodeEquation (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    ((Ideal.Quotient.mk (Ideal.span {nodeEquation b 0 0 s})).comp
      (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) (fun z ↦ z.1.1)
        (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0))).Flat := by
  rw [← nodeTransverseHom_comp_stalkPrecomp_fst]
  exact (flat_stalkPrecomp_fst b 0).comp (nodeTransverseHom_flat b s)

/-- At the node `(b, 0, 0)`, the flatness of `flat_quotientMk_comp_stalkPrecomp_nodeEquation`
transported along the associator `((b, x), y) ↦ (b, x, y)`. -/
private theorem flat_quotientMk_comp_stalkPrecomp_smoothingEquation_node (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    ((Ideal.Quotient.mk (Ideal.span {smoothingEquation (b, 0, 0) s})).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) Prod.fst
        (contMDiff_iff_contDiff.mpr contDiff_fst) (b, 0, 0))).Flat := by
  have hP : Function.Bijective (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)
      (fun z ↦ (z.1.1, z.1.2, z.2)) (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0)) := by
    rw [← stalkPullback_eq_stalkPrecomp]
    exact stalkPullback_bijective _ (g := fun q : E × ℂ × ℂ ↦ ((q.1, q.2.1), q.2.2))
      (.of_forall fun _ ↦ (contMDiff_iff_contDiff.mpr (by fun_prop)).contMDiffAt)
      (.of_forall fun _ ↦ rfl) (.of_forall fun _ ↦ rfl)
  let Q := Ideal.quotientEquiv (Ideal.span {smoothingEquation (b, 0, 0) s})
    (Ideal.span {nodeEquation b 0 0 s}) (RingEquiv.ofBijective _ hP) (by
      rw [Ideal.map_span, Set.image_singleton]
      exact congrArg (Ideal.span {·}) (stalkPrecomp_assoc_smoothingEquation b s).symm)
  have key : Q.toRingHom.comp ((Ideal.Quotient.mk _).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) Prod.fst
        (contMDiff_iff_contDiff.mpr contDiff_fst) (b, 0, 0))) =
      (Ideal.Quotient.mk _).comp (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) (fun z ↦ z.1.1)
        (contMDiff_iff_contDiff.mpr (by fun_prop)) ((b, 0), 0)) := by
    ext t
    rw [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingHom.comp_apply, Ideal.quotientEquiv_mk,
      RingEquiv.ofBijective_apply, ← stalkPrecomp_comp]
    -- `Prod.fst ∘ (fun z ↦ (z.1.1, z.1.2, z.2))` is literally `fun z ↦ z.1.1`.
    rfl
  rw [← RingHom.Flat.comp_iff_of_bijective_left (g := Q.toRingHom) Q.bijective, key]
  exact flat_quotientMk_comp_stalkPrecomp_nodeEquation b s

/-- **`N_s` is flat over the base.** At every point `p = (b, x, y)` of `E × ℂ × ℂ` and for every
holomorphic germ `s` at `b`, pulling base germs back along `(b, x, y) ↦ b` makes the local ring
`𝒪_p ⧸ (xy - s(b))` of `N_s` a flat algebra over `𝒪_{E, b}`. -/
theorem flat_quotientMk_comp_stalkPrecomp_smoothingEquation (p : E × ℂ × ℂ)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk p.1) :
    ((Ideal.Quotient.mk (Ideal.span {smoothingEquation p s})).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) Prod.fst
        (contMDiff_iff_contDiff.mpr contDiff_fst) p)).Flat := by
  by_cases hs : eval 𝓘(ℂ, E) E p.1 s = p.2.1 * p.2.2
  · by_cases hx : p.2.1 = 0
    · by_cases hy : p.2.2 = 0
      · obtain ⟨b, x, y⟩ := p
        dsimp only at hx hy s ⊢
        subst hx hy
        exact flat_quotientMk_comp_stalkPrecomp_smoothingEquation_node b s
      · -- Where `y ≠ 0`, `N_s` is the graph `x = s(b) / y` over `E × ℂ`.
        have key : (offNodeChartSnd p s).comp (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst
            contDiff_fst.contMDiff (p.1, p.2.2)) = (Ideal.Quotient.mk _).comp
            (stalkPrecomp 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) Prod.fst
              (contMDiff_iff_contDiff.mpr contDiff_fst) p) := by
          ext t
          rw [RingHom.comp_apply, offNodeChartSnd_apply, ← stalkPrecomp_comp]
          -- `Prod.fst ∘ (fun q ↦ (q.1, q.2.2))` is literally `Prod.fst`.
          rfl
        rw [← key]
        exact (flat_stalkPrecomp_fst p.1 p.2.2).comp
          (.of_bijective (offNodeChartSnd_bijective hy hs))
    · -- Where `x ≠ 0`, `N_s` is the graph `y = s(b) / x` over `E × ℂ`.
      have key : (offNodeChartFst p s).comp (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst
          contDiff_fst.contMDiff (p.1, p.2.1)) = (Ideal.Quotient.mk _).comp
          (stalkPrecomp 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) Prod.fst
            (contMDiff_iff_contDiff.mpr contDiff_fst) p) := by
        ext t
        rw [RingHom.comp_apply, offNodeChartFst_apply, ← stalkPrecomp_comp]
        -- `Prod.fst ∘ (fun q ↦ (q.1, q.2.1))` is literally `Prod.fst`.
        rfl
      rw [← key]
      exact (flat_stalkPrecomp_fst p.1 p.2.1).comp
        (.of_bijective (offNodeChartFst_bijective hx hs))
  · -- Off `N_s` the local equation is a unit, so the local ring is zero.
    have hu : IsUnit (smoothingEquation p s) := by
      rw [isUnit_stalk_iff, eval_smoothingEquation, sub_ne_zero]
      exact Ne.symm hs
    have : Subsingleton (_ ⧸ Ideal.span {smoothingEquation p s}) :=
      Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
    algebraize [(Ideal.Quotient.mk (Ideal.span {smoothingEquation p s})).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ × ℂ) (E × ℂ × ℂ) Prod.fst
        (contMDiff_iff_contDiff.mpr contDiff_fst) p)]
    exact inferInstanceAs (Module.Flat _ _)

end TauCeti.holomorphicStructureSheaf
