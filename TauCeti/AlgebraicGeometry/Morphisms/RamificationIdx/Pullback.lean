/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx.Basic
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.AlgebraicGeometry.RationalPoint.BaseChange
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.ClosedPoint
public import TauCeti.RingTheory.RamificationInertia.BaseChange
import TauCeti.AlgebraicGeometry.AffineScheme.Basic

/-!
# Pointwise ramification indices under base change and closed-fibre comparison

This file studies the behaviour of `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt` under base
change along an arbitrary field extension `L / k`:

* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isSeparable_residueField`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isClosed`: invariance of
  `ramificationIdxAt` under arbitrary field extensions at separable (or closed over perfect `k`)
  points.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_fiberEquivOfIsAlgClosed`:
  `fiberEquivOfIsAlgClosed` preserves `ramificationIdxAt` in arbitrary characteristic.
-/

public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

section FieldPullback

section SinglePullback

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X X' : Scheme.{u}}
  [X.Over (Spec (.of k))] [X'.Over (Spec (.of L))] {gX : X' ⟶ X}
  (HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))))

include HX

/-- **Vertical ramification index one under field extension** whenever `κ(gX x') / k` is
separable (with no finite-type assumption on `X` or `L / k`). -/
theorem ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField {x' : X'}
    (hsep : Algebra.IsSeparable k (X.residueField (gX x'))) : gX.ramificationIdxAt x' = 1 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (gX x')) isOpen_univ
  replace hV : IsAffineOpen V := hV
  let _ : Algebra k Γ(X, V) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ V le_top).hom.toAlgebra
  have hVover : hV.fromSpec ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, V))) := by
    rw [hV.fromSpec_comp_eq_SpecMap, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  have := hV.isOpenImmersion_fromSpec
  obtain ⟨ι, hι, q, p, rfl, -, h₂, hgx, hp⟩ :=
    TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_at_of_isPullback HX
      (iY := 𝟙 (Spec (.of k))) (iY' := 𝟙 (Spec (.of L))) (iX := hV.fromSpec)
      (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hVover])
      ⟨X' ↘ Spec (.of L) <| x', rfl⟩ (hV.range_fromSpec ▸ hxV)
  have := q.isPrime
  have := p.isPrime
  let B := L ⊗[k] Γ(X, V); let _ : Algebra Γ(X, V) B := Algebra.TensorProduct.rightAlgebra
  rw [hgx] at hsep
  have hsepP : Algebra.IsSeparable k p.asIdeal.ResidueField :=
    Algebra.IsSeparable.of_algHom _ _ (hV.fromSpec.residueFieldAlgEquivOfIsOpenImmersion
      (CommRingCat.ofHom (algebraMap k Γ(X, V))) hVover.symm p).symm.toAlgHom
  have hsepI : ∀ (I : Ideal Γ(X, V)) [I.IsPrime], p.asIdeal = I →
      Algebra.IsSeparable k I.ResidueField := by rintro I _ rfl; convert hsepP
  rw [ramificationIdxAt_eq_of_isOpenImmersion_square ι gX _ hV.fromSpec h₂ q,
    ramificationIdxAt_specMap]
  exact Ideal.ramificationIdx_eq_one_of_isPushout_of_isSeparable k L q.asIdeal
    (hsepI (q.asIdeal.under Γ(X, V)) hp)

/-- Over a perfect field `k`, `gX.ramificationIdxAt x' = 1` over any closed point of `X`. -/
theorem ramificationIdxAt_eq_one_of_isPullback_of_isClosed [PerfectField k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] {x' : X'} (hx : IsClosed {gX x'}) :
    gX.ramificationIdxAt x' = 1 :=
  have := Scheme.finite_residueField_of_isClosed (k := k) hx
  ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField HX inferInstance

end SinglePullback

section PullbackSquare

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
  {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
  [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
  (Hf : IsPullback gX f' f gY)
  (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))))

include Hf HY

/-- **Horizontal ramification index invariance under field extension** at any point `x'` where both
`κ(gX x')` and `κ(f (gX x'))` are separable over `k` (no flatness assumption on `f`). -/
theorem ramificationIdxAt_eq_of_isPullback_of_isSeparable_residueField {x' : X'}
    (hsepX : Algebra.IsSeparable k (X.residueField (gX x')))
    (hsepY : Algebra.IsSeparable k (Y.residueField (f (gX x')))) :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') := by
  have HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    simpa only [comp_over] using Hf.paste_vert HY
  have : Flat gX := MorphismProperty.of_isPullback (P := @Flat) HX.flip inferInstance
  have hw : gY (f' x') = f (gX x') := by rw [← Scheme.Hom.comp_apply, ← Hf.w, Scheme.Hom.comp_apply]
  exact ramificationIdxAt_eq_of_commSq_of_eq_one Hf.w x' (Flat.stalkMap gX x')
    (ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField HX hsepX)
    (ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField HY (by rwa [hw]))

/-- Over a perfect field `k`, `f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')` at points
mapping to closed points of `X` and `Y`. -/
theorem ramificationIdxAt_eq_of_isPullback_of_isClosed [PerfectField k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    {x' : X'} (hx : IsClosed {gX x'}) (hy : IsClosed {f (gX x')}) :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') :=
  have := Scheme.finite_residueField_of_isClosed (k := k) hx
  have := Scheme.finite_residueField_of_isClosed (k := k) hy
  ramificationIdxAt_eq_of_isPullback_of_isSeparable_residueField Hf HY inferInstance inferInstance

/-- `fiberEquivOfIsAlgClosed` preserves `ramificationIdxAt` in arbitrary characteristic. -/
theorem ramificationIdxAt_fiberEquivOfIsAlgClosed [IsAlgClosed k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    (y' : Y') (hy : IsClosed {gY y'})
    (hfib : ∀ x : X, f x = gY y' → IsClosed {x}) (x' : {x' : X' // f' x' = y'}) :
    f'.ramificationIdxAt x'.val =
      f.ramificationIdxAt (fiberEquivOfIsAlgClosed Hf HY y' hy hfib x').val :=
  have hfgx : f (gX x'.val) = gY y' := by
    rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, x'.property]
  (fiberEquivOfIsAlgClosed_coe Hf HY y' hy hfib x').symm ▸
    ramificationIdxAt_eq_of_isPullback_of_isClosed Hf HY (hfib (gX x'.val) hfgx) (hfgx ▸ hy)

end PullbackSquare

end FieldPullback

end AlgebraicGeometry.Scheme.Hom
