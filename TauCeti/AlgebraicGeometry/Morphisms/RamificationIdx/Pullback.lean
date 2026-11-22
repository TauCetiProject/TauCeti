/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus.Pullback
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.ClosedPoint
public import TauCeti.RingTheory.RamificationInertia.BaseChange

/-!
# Pointwise ramification indices under base change and closed-fibre comparison

This file relates `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt` to `ramificationLocus` and
studies its behaviour in commutative squares and under base change along an arbitrary field
extension `L / k`:

* `Scheme.Hom.notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_one_of_notMem_ramificationLocus`,
  `AlgebraicGeometry.Scheme.Hom.mem_ramificationLocus_iff_ramificationIdxAt_ne_one`: pointwise
  relation between `ramificationLocus` and `ramificationIdxAt`.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_commSq_of_eq_one`: horizontal comparison
  in a commutative square with flat left stalk map and vertical ramification indices `1`.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isSeparable_residueField`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isClosed`: invariance of
  `ramificationIdxAt` under arbitrary field extensions at separable (or closed over perfect `k`)
  points.
* `AlgebraicGeometry.Scheme.Hom.fiberEquivOfIsAlgClosed`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_fiberEquivOfIsAlgClosed`,
  `AlgebraicGeometry.Scheme.Hom.fiberEquivOfIsAlgClosedOfLocallyQuasiFinite`: closed-fibre
  bijection over an algebraically closed base field preserving `ramificationIdxAt`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

section RamificationLocus

/-- **Pointwise criterion for the ramification locus.** For `f` locally of finite type,
`x ∉ f.ramificationLocus` iff `f.ramificationIdxAt x = 1` and `κ(x) / κ(f x)` is separable. -/
theorem notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    x ∉ f.ramificationLocus ↔
      f.ramificationIdxAt x = 1 ∧
        letI := (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  let R := Y.presheaf.stalk (f x); let S := X.presheaf.stalk x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.EssFiniteType R S :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap f x)
  have hsep : Algebra.IsSeparable (ResidueField R) (ResidueField S) ↔
      letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
    constructor <;> intro h <;>
    · convert! h
      exact Algebra.algebra_ext _ _ fun r ↦
        let ⟨_, hr⟩ := IsLocalRing.residue_surjective r; hr ▸ rfl
  rw [mem_ramificationLocus_iff, not_not, RingHom.FormallyUnramified,
    ← RingHom.algebraMap_toAlgebra (f.stalkMap x).hom,
    Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, hsep, ramificationIdxAt_def,
    ramificationIdx_maximalIdeal_eq_one_iff, Ideal.under, maximalIdeal_comap, and_comm]

/-- Outside `f.ramificationLocus` (for `f` locally of finite type), `f.ramificationIdxAt x = 1`. -/
theorem ramificationIdxAt_eq_one_of_notMem_ramificationLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {x : X} (hx : x ∉ f.ramificationLocus) :
    f.ramificationIdxAt x = 1 :=
  ((notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable f x).mp hx).1

/-- At a quasi-finite point over a perfect residue field `κ(f x)`, `x ∈ f.ramificationLocus` iff
`f.ramificationIdxAt x ≠ 1`. -/
theorem mem_ramificationLocus_iff_ramificationIdxAt_ne_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {x : X} (hqf : f.QuasiFiniteAt x)
    [PerfectField (Y.residueField (f x))] :
    x ∈ f.ramificationLocus ↔ f.ramificationIdxAt x ≠ 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) := hqf.finite_residueField
  have hsep : Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := inferInstance
  rw [← not_iff_not, not_not, notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hsep⟩⟩

end RamificationLocus

section CommSq

/-- **Comparison of `ramificationIdxAt` in a commutative square** with flat left stalk map and
vertical ramification indices `1`. -/
theorem ramificationIdxAt_eq_of_commSq_of_eq_one {X Y X' Y' : Scheme.{u}} {gX : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y} (w : gX ≫ f = f' ≫ gY) (x' : X')
    (hflat : (gX.stalkMap x').hom.Flat) (hgX : gX.ramificationIdxAt x' = 1)
    (hgY : gY.ramificationIdxAt (f' x') = 1) :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') := by
  let R := Y.presheaf.stalk (f (gX x')); let R' := Y.presheaf.stalk (gY (f' x'))
  let S := Y'.presheaf.stalk (f' x'); let A := X.presheaf.stalk (gX x')
  let B := X'.presheaf.stalk x'
  have hw : f (gX x') = gY (f' x') := by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  let eR : R ⟶ R' := (Y.presheaf.stalkCongr (.of_eq hw)).hom
  let : Algebra R R' := eR.hom.toAlgebra; let : Algebra R' S := (gY.stalkMap (f' x')).hom.toAlgebra
  let : Algebra R S := (eR ≫ gY.stalkMap (f' x')).hom.toAlgebra
  let : Algebra R A := (f.stalkMap (gX x')).hom.toAlgebra
  let : Algebra A B := (gX.stalkMap x').hom.toAlgebra
  let : Algebra S B := (f'.stalkMap x').hom.toAlgebra
  let : Algebra R B := (f.stalkMap (gX x') ≫ gX.stalkMap x').hom.toAlgebra
  have hsq : f.stalkMap (gX x') ≫ gX.stalkMap x' =
      (eR ≫ gY.stalkMap (f' x')) ≫ f'.stalkMap x' := by
    rw [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ w x',
      Scheme.Hom.stalkMap_comp, Category.assoc]; rfl
  have : IsScalarTower R R' S := .of_algebraMap_eq' rfl
  have : IsScalarTower R A B := .of_algebraMap_eq' rfl
  have : IsScalarTower R S B := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hsq)
  have : IsLocalHom (algebraMap S B) := inferInstanceAs (IsLocalHom (f'.stalkMap x').hom)
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (gX.stalkMap x').hom)
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  rw [ramificationIdxAt_def] at hgX hgY
  have hRS : (maximalIdeal S).ramificationIdx R = 1 := by
    rw [← Ideal.ramificationIdx_eq_of_surjective (T := S)
      (ConcreteCategory.bijective_of_isIso eR).surjective]
    exact hgY
  rw [ramificationIdxAt_def, ramificationIdxAt_def]
  exact Ideal.ramificationIdx_eq_of_isLocalHom_square (R := R) (S := S) (A := A) (B := B) hgX hRS

end CommSq

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
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (gX x')) isOpen_univ
  let _ : Algebra k Γ(X, V) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ V le_top).hom.toAlgebra
  have hVover : hV.fromSpec ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, V))) := by
    rw [hV.fromSpec_comp_eq_SpecMap, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  have := hV.isOpenImmersion_fromSpec
  obtain ⟨ι, hι, -, h₂, hrange⟩ :=
    TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_of_isPullback HX
      (iY := 𝟙 (Spec (.of k))) (iY' := 𝟙 (Spec (.of L))) (iX := hV.fromSpec)
      (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hVover])
  obtain ⟨q, rfl⟩ : x' ∈ Set.range ι := by
    rw [hrange, hV.range_fromSpec]; exact ⟨⟨X' ↘ Spec (.of L) <| x', rfl⟩, hxV⟩
  have := q.isPrime
  let B := L ⊗[k] Γ(X, V); let _ : Algebra Γ(X, V) B := Algebra.TensorProduct.rightAlgebra
  let φR := CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[k] B).toRingHom
  let p := Spec.map φR q; have := p.isPrime
  have hgx : gX (ι q) = hV.fromSpec p := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : _ ⟶ X ↦ m q) h₂
  have hp : p.asIdeal = q.asIdeal.under Γ(X, V) :=
    (congrArg PrimeSpectrum.asIdeal (Spec.map_apply φR q)).trans (PrimeSpectrum.comap_asIdeal _ q)
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

/-- Over an algebraically closed field `k`, every closed point of a locally-finite-type `k`-scheme
has a unique preimage in the base change along any field extension `L / k`. -/
theorem existsUnique_preimage_of_isPullback_of_isAlgClosed [IsAlgClosed k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] {x : X} (hx : IsClosed {x}) :
    ∃! x' : X', gX x' = x := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let s : Spec (.of k) ⟶ X := pointOfClosedPoint (X ↘ Spec (.of k)) x hx
  have hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 _ := pointOfClosedPoint_comp (X ↘ Spec (.of k)) x hx
  have hw : (b ≫ s) ≫ (X ↘ Spec (.of k)) = 𝟙 _ ≫ b := by simp [hs]
  have hpre := TauCeti.AlgebraicGeometry.preimage_singleton_section_closedPoint_of_isPullback HX
    hs (HX.lift_snd (b ≫ s) (𝟙 _) hw) (HX.lift_fst (b ≫ s) (𝟙 _) hw)
  have hsx : s (closedPoint k) = x := pointOfClosedPoint_apply (X ↘ Spec (.of k)) x hx _
  rw [hsx] at hpre
  exact ⟨HX.lift (b ≫ s) (𝟙 _) hw (closedPoint L),
    Set.mem_preimage.mp (hpre.symm ▸ Set.mem_singleton _),
    fun _ hz ↦ Set.mem_singleton_iff.mp (hpre ▸ Set.mem_preimage.mpr hz)⟩

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

section AlgClosedFiber

variable [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- **Closed-fibre bijection under field extension from an algebraically closed field** along
`gX`, for any `y'` over a closed point `gY y'` whose fibre in `X` consists of closed points. -/
noncomputable def fiberEquivOfIsAlgClosed (y' : Y') (hy : IsClosed {gY y'})
    (hfib : ∀ x : X, f x = gY y' → IsClosed {x}) :
    {x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'} := by
  have HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    simpa only [comp_over] using Hf.paste_vert HY
  refine Equiv.ofBijective (fun x' ↦ ⟨gX x'.val, by
      rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, x'.property]⟩) ⟨?_, ?_⟩
  · rintro ⟨x'₁, hx'₁⟩ ⟨x'₂, hx'₂⟩ h
    have hxcl : IsClosed {gX x'₁} :=
      hfib (gX x'₁) (by rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, hx'₁])
    obtain ⟨_, -, hunique⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HX hxcl
    exact Subtype.ext ((hunique x'₁ rfl).trans (hunique x'₂ (congrArg Subtype.val h).symm).symm)
  · rintro ⟨x, hx⟩
    obtain ⟨x', hx', -⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HX (hfib x hx)
    obtain ⟨_, -, hyunique⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HY hy
    have hgy : gY (f' x') = gY y' := by
      rw [← Scheme.Hom.comp_apply, ← Hf.w, Scheme.Hom.comp_apply, hx', hx]
    exact ⟨⟨x', (hyunique (f' x') hgy).trans (hyunique y' rfl).symm⟩, Subtype.ext hx'⟩

/-- `fiberEquivOfIsAlgClosed` acts on underlying points via the projection `gX`. -/
@[simp]
theorem fiberEquivOfIsAlgClosed_coe (y' : Y') (hy : IsClosed {gY y'})
    (hfib : ∀ x : X, f x = gY y' → IsClosed {x}) (x' : {x' : X' // f' x' = y'}) :
    (fiberEquivOfIsAlgClosed Hf HY y' hy hfib x').val = gX x'.val := by
  unfold fiberEquivOfIsAlgClosed; rfl

/-- `fiberEquivOfIsAlgClosed` preserves `ramificationIdxAt` in arbitrary characteristic. -/
theorem ramificationIdxAt_fiberEquivOfIsAlgClosed (y' : Y') (hy : IsClosed {gY y'})
    (hfib : ∀ x : X, f x = gY y' → IsClosed {x}) (x' : {x' : X' // f' x' = y'}) :
    f'.ramificationIdxAt x'.val =
      f.ramificationIdxAt (fiberEquivOfIsAlgClosed Hf HY y' hy hfib x').val :=
  have hfgx : f (gX x'.val) = gY y' := by
    rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, x'.property]
  ramificationIdxAt_eq_of_isPullback_of_isClosed Hf HY (hfib (gX x'.val) hfgx) (hfgx ▸ hy)

/-- Specialization of `fiberEquivOfIsAlgClosed` to locally quasi-finite morphisms. -/
noncomputable def fiberEquivOfIsAlgClosedOfLocallyQuasiFinite [LocallyQuasiFinite f]
    (y' : Y') (hy : IsClosed {gY y'}) :
    {x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'} :=
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  fiberEquivOfIsAlgClosed Hf HY y' hy fun _ hx ↦
    isClosed_singleton_of_locallyQuasiFinite_of_isClosed f (hx ▸ hy)

end AlgClosedFiber

end PullbackSquare

end FieldPullback

end AlgebraicGeometry.Scheme.Hom
