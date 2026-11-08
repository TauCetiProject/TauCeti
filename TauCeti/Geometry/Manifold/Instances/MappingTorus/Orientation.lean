/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.Orientation.Quotient

/-!
# The orientation of a mapping torus

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M` preserving an
orientation `o` of `M` at every point, and let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its
smooth mapping torus. The integer translations `(t, x) ↦ (t + k, φ ^ (-k) x)` generating the
quotient preserve the product orientation of `ℝ × M`, in which the time direction `∂_t` comes first
and is followed by `o`. So this orientation descends to `Y_φ`
(`TauCeti.SmoothMappingTorus.orientation φ o hφ`); it is the orientation `dt` followed by the fibre
orientation `o`. It is characterised by the quotient map `(t, x) ↦ [t, x]` preserving orientation
at every point (`TauCeti.SmoothMappingTorus.eq_orientation_iff`).

## Main definitions

* `TauCeti.SmoothMappingTorus.orientation φ o hφ`: the orientation of `Y_φ` descended from the
  product orientation of `ℝ × M`.

## Main results

* `TauCeti.SmoothMappingTorus.isOrientationPreservingAt_uncurry_mk`: the quotient map
  `ℝ × M → Y_φ` preserves orientation from the product orientation.
* `TauCeti.SmoothMappingTorus.eq_orientation_iff`: the orientation of `Y_φ` is the only one from
  which the quotient map preserves orientation everywhere.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15 (product orientations) and Chapter 21 (quotients by
  discrete group actions).
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2 (mapping
  tori).
-/

public section

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

open Cover Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M) {m : ℕ} (o : Manifold.Orientation I M (Fin m))

/-- The product orientation of `ℝ × M`, read on the cover of the mapping torus. -/
private def coverOrientation : Manifold.Orientation (𝓘(ℝ).prod I) (Cover φ) (Fin (1 + m)) :=
  (Manifold.Orientation.real.prod o).pullback (contMDiff_ofProd_symm φ 1)
    ((isLocalDiffeomorph_ofProd_symm φ 1).isInvertible_mfderiv one_ne_zero)
    (by rw [Fintype.card_fin, finrank_prod, finrank_self, ← o.card_eq, Fintype.card_fin])

omit [T2Space M] [LocallyCompactSpace M] in
private theorem isOrientationPreservingAt_ofProd_symm (z : Cover φ) :
    IsOrientationPreservingAt (coverOrientation φ o) (Manifold.Orientation.real.prod o)
      (ofProd φ).symm z :=
  isOrientationPreservingAt_pullback _ _ _ _ z

omit [T2Space M] [LocallyCompactSpace M] in
private theorem isOrientationPreservingAt_ofProd (p : ℝ × M) :
    IsOrientationPreservingAt (Manifold.Orientation.real.prod o) (coverOrientation φ o)
      (ofProd φ) p := by
  have h : IsOrientationPreservingAt (coverOrientation φ o) (Manifold.Orientation.real.prod o)
      (ofProdDiffeomorph φ 1).symm (ofProdDiffeomorph φ 1 p) := by
    rw [coe_ofProdDiffeomorph_symm]
    exact isOrientationPreservingAt_ofProd_symm φ o _
  rw [← coe_ofProdDiffeomorph φ 1]
  exact h.diffeomorph_symm (e := (ofProdDiffeomorph φ 1).symm) one_ne_zero

variable {φ o} (hφ : ∀ x, IsOrientationPreservingAt o o φ x)
include hφ

omit [T2Space M] [LocallyCompactSpace M] in
/-- The integer translations `(t, x) ↦ (t + k, φ ^ (-k) x)` preserve the product orientation. -/
private theorem isOrientationPreservingAt_smul (k : Multiplicative ℤ) (z : Cover φ) :
    IsOrientationPreservingAt (coverOrientation φ o) (coverOrientation φ o) (k • ·) z := by
  have h : (k • · : Cover φ → Cover φ) =
      ofProd φ ∘ Prod.map (· + (k.toAdd : ℝ)) ⇑(φ ^ (-k.toAdd)) ∘ (ofProd φ).symm :=
    funext (smul_def φ k)
  rw [h]
  exact (isOrientationPreservingAt_ofProd φ o _).comp
    (((isOrientationPreservingAt_add_const _ _).prodMap
      (isOrientationPreservingAt_zpow hφ (by simp) _ _)).comp
      (isOrientationPreservingAt_ofProd_symm φ o z))

variable (φ o)

/-- The **orientation of the mapping torus** `Y_φ` of a diffeomorphism `φ` preserving an orientation
`o` of `M`: the orientation descended from the product orientation of `ℝ × M`, in which the time
direction `∂_t` comes first and is followed by `o`. -/
def orientation : Manifold.Orientation (𝓘(ℝ).prod I) (SmoothMappingTorus φ) (Fin (1 + m)) :=
  (coverOrientation φ o).quotient (isOrientationPreservingAt_smul hφ)

/-- The quotient map `(t, x) ↦ [t, x]` preserves orientation from the product orientation of
`ℝ × M` to the orientation of the mapping torus. -/
@[simp]
theorem isOrientationPreservingAt_uncurry_mk (p : ℝ × M) :
    IsOrientationPreservingAt (Manifold.Orientation.real.prod o) (orientation φ o hφ)
      (uncurry (mk φ)) p := by
  -- By definition, `(t, x) ↦ [t, x]` is the orbit projection after the identification `ofProd φ`.
  have h : uncurry (mk φ) = Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (Cover φ)) ∘
      ofProd φ := funext fun p ↦ mk_def φ p.1 p.2
  rw [h]
  exact (isOrientationPreservingAt_quotientMk _ _ _).comp (isOrientationPreservingAt_ofProd φ o p)

/-- The orientation of the mapping torus is the only orientation from which the quotient map
`(t, x) ↦ [t, x]` preserves orientation at every point. -/
theorem eq_orientation_iff {o' : Manifold.Orientation (𝓘(ℝ).prod I) (SmoothMappingTorus φ)
    (Fin (1 + m))} :
    o' = orientation φ o hφ ↔
      ∀ p, IsOrientationPreservingAt (Manifold.Orientation.real.prod o) o' (uncurry (mk φ)) p := by
  refine ⟨fun h ↦ h ▸ isOrientationPreservingAt_uncurry_mk φ o hφ, fun h ↦ ext fun y ↦ ?_⟩
  obtain ⟨p, rfl⟩ := uncurry_mk_surjective φ y
  exact (h p).orientationAt_eq (isOrientationPreservingAt_uncurry_mk φ o hφ p)

end SmoothMappingTorus

end TauCeti
