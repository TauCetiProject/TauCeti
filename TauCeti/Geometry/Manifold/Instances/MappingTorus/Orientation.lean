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

Conversely, when `M` is preconnected, `Y_φ` is orientable only if `φ` preserves `o` at every point
(`TauCeti.SmoothMappingTorus.orientable_iff_forall_isOrientationPreservingAt`). An orientation of
`Y_φ` pulls back to the product orientation of the preconnected manifold `ℝ × M` or to its
opposite, so the quotient map preserves orientation from the product orientation to a suitable
orientation of `Y_φ`. The quotient map identifies the time-one translation `(t, x) ↦ (t + 1, x)`,
which preserves the product orientation, with `(t, x) ↦ (t, φ x)`, so `id × φ` and hence `φ`
preserve orientation. In particular, the mapping torus of an orientation-reversing diffeomorphism,
such as the open Möbius band, is not orientable
(`TauCeti.SmoothMappingTorus.not_orientable_of_isOrientationReversingAt`).

## Main definitions

* `TauCeti.SmoothMappingTorus.orientation φ o hφ`: the orientation of `Y_φ` descended from the
  product orientation of `ℝ × M`.

## Main results

* `TauCeti.SmoothMappingTorus.isOrientationPreservingAt_uncurry_mk`: the quotient map
  `ℝ × M → Y_φ` preserves orientation from the product orientation.
* `TauCeti.SmoothMappingTorus.eq_orientation_iff`: the orientation of `Y_φ` is the only one from
  which the quotient map preserves orientation everywhere.
* `TauCeti.SmoothMappingTorus.orientable_iff_forall_isOrientationPreservingAt`: for preconnected
  `M`, `Y_φ` is orientable exactly when `φ` preserves `o` at every point.
* `TauCeti.SmoothMappingTorus.not_orientable_of_isOrientationReversingAt`: for preconnected `M`,
  `Y_φ` is not orientable when `φ` reverses `o` at some point.

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

omit hφ

/-! ### Orientability -/

section Orientable

variable [PreconnectedSpace M]

omit [T2Space M] [LocallyCompactSpace M] [IsManifold I ∞ M] [PreconnectedSpace M] in
include o in
private theorem finrank_prod_eq : finrank ℝ (ℝ × E) = 1 + m := by
  rw [finrank_prod, finrank_self, ← o.card_eq, Fintype.card_fin]

/-- If the mapping torus of `φ` carries some orientation, the quotient map `(t, x) ↦ [t, x]`
preserves orientation everywhere from the product orientation of `ℝ × M` to some orientation of
the mapping torus. Pulled back to the preconnected manifold `ℝ × M`, the given orientation is the
product orientation or its opposite; in the second case, use the opposite orientation. -/
private theorem exists_forall_isOrientationPreservingAt_uncurry_mk
    (O : Manifold.Orientation (𝓘(ℝ).prod I) (SmoothMappingTorus φ) (Fin (1 + m))) :
    ∃ O' : Manifold.Orientation (𝓘(ℝ).prod I) (SmoothMappingTorus φ) (Fin (1 + m)),
      ∀ p, IsOrientationPreservingAt (Manifold.Orientation.real.prod o) O' (uncurry (mk φ)) p := by
  have hq := isLocalDiffeomorph_uncurry_mk (n := ∞) φ
  have hι : Fintype.card (Fin (1 + m)) = finrank ℝ (ℝ × E) := by
    rw [Fintype.card_fin, finrank_prod_eq o]
  have hdf (p : ℝ × M) := hq.isInvertible_mfderiv (x := p) (by simp)
  rcases eq_or_eq_neg (Manifold.Orientation.real.prod o)
      (O.pullback (hq.contMDiff.of_le (by simp)) hdf hι) with h | h
  · exact ⟨O, (eq_pullback_iff _ _ _ _).mp h⟩
  · exact ⟨-O, fun p ↦ (isOrientationPreservingAt_neg_right _ _ _ _).mpr
      ((eq_neg_pullback_iff _ _ _ _).mp h p)⟩

/-- If the mapping torus of a diffeomorphism `φ` of a preconnected manifold carries an orientation,
then `φ` preserves every orientation `o` of `M` at every point. The time-one translation of
`ℝ × M` preserves its product orientation and agrees with `id × φ` after the quotient map, which
preserves orientation from the product orientation for a suitable orientation of the torus. -/
private theorem isOrientationPreservingAt_of_orientation
    (O : Manifold.Orientation (𝓘(ℝ).prod I) (SmoothMappingTorus φ) (Fin (1 + m))) (x : M) :
    IsOrientationPreservingAt o o φ x := by
  let R := Manifold.Orientation.real.prod o
  obtain ⟨O', hO'⟩ := exists_forall_isOrientationPreservingAt_uncurry_mk φ o O
  have hT : IsOrientationPreservingAt R R (Prod.map (· + 1) id) ((0 : ℝ), x) :=
    (isOrientationPreservingAt_add_const 1 0).prodMap (isOrientationPreservingAt_id o x)
  have hTF : uncurry (mk φ) ∘ Prod.map (· + 1) id = uncurry (mk φ) ∘ Prod.map id φ :=
    funext fun p ↦ mk_add_one φ p.1 p.2
  have hF : IsOrientationPreservingAt R R (Prod.map id φ) ((0 : ℝ), x) :=
    (hO' _).of_comp (hTF ▸ (hO' _).comp hT)
      (mdifferentiableAt_id.prodMap (φ.mdifferentiable (by simp) x))
  refine ((φ.isLocalDiffeomorph x).isOrientationPreservingAt_or_isOrientationReversingAt
    (by simp) o o).resolve_right fun h ↦ ?_
  have hneg : IsOrientationPreservingAt R (-R) (Prod.map id φ) ((0 : ℝ), x) := by
    rw [← prod_neg_right]
    exact (isOrientationPreservingAt_id _ _).prodMap
      ((isOrientationPreservingAt_neg_right o o φ x).mpr h)
  exact not_isOrientationPreservingAt_and_isOrientationReversingAt R R _ _
    ⟨hF, (isOrientationPreservingAt_neg_right _ _ _ _).mp hneg⟩

/-- **Orientability of a mapping torus.** For a diffeomorphism `φ` of a preconnected manifold
with an orientation `o`, the mapping torus of `φ` is orientable exactly when `φ` preserves `o` at
every point. -/
theorem orientable_iff_forall_isOrientationPreservingAt :
    Orientable (𝓘(ℝ).prod I) (SmoothMappingTorus φ) ↔ ∀ x, IsOrientationPreservingAt o o φ x := by
  refine ⟨fun ⟨⟨O⟩⟩ ↦ isOrientationPreservingAt_of_orientation φ o
    (O.reindex (finCongr (finrank_prod_eq o))), fun hφ ↦ ⟨⟨?_⟩⟩⟩
  exact (orientation φ o hφ).reindex (finCongr (finrank_prod_eq o).symm)

/-- The mapping torus of a diffeomorphism of a preconnected oriented manifold which reverses the
orientation at some point is not orientable. -/
theorem not_orientable_of_isOrientationReversingAt {x : M}
    (h : IsOrientationReversingAt o o φ x) :
    ¬ Orientable (𝓘(ℝ).prod I) (SmoothMappingTorus φ) := fun hY ↦
  not_isOrientationPreservingAt_and_isOrientationReversingAt o o φ x
    ⟨(orientable_iff_forall_isOrientationPreservingAt φ o).mp hY x, h⟩

end Orientable

end SmoothMappingTorus

end TauCeti
