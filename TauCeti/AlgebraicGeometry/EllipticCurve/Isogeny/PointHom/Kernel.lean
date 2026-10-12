/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Place
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import TauCeti.FieldTheory.FunctionField.Place.Zeros

/-!
# The kernel of a separable isogeny is the kernel of its point map

An isogeny `φ : W₁ → W₂` has two kernels. `Isogeny.ker` is read off the function field: the points
`P` whose translation `τ_P^*` fixes every function pulled back from `W₂`. The class-group point map
`Isogeny.toPointHom` has an ordinary kernel, the points sent to `O₂`. For a separable isogeny over
a separably closed field the two agree (Silverman III.4.10).

One inclusion is formal. If `τ_P^*` fixes the pulled-back field then restricting places along the
pullback cannot distinguish the place of `P` from the place of `O₁`, and by the point--place
dictionary that is `φ(P) = O₂`. The other inclusion is where separability and the closed base
field enter, through the compatibility `τ_P^* ∘ φ^* = φ^* ∘ τ_{φ(P)}^*` of translations with the
pullback. For every point `Q` off the fibres of `O₂` under `Q ↦ φ(Q)` and `Q ↦ φ(Q + P)`, the
functions `τ_P^* φ^* x` and `φ^* τ_{φ(P)}^* x` both take at `Q` the value of `x` at
`φ(Q + P) = φ(Q) + φ(P)`; there are infinitely many such `Q`, and a nonzero function has only
finitely many zeros, so the two agree, likewise for `y`, and hence on the whole function field.
When `φ(P) = O₂` the right-hand side is `φ^*`, so `τ_P^*` fixes the pulled-back field.

Since the point kernel has `deg φ` elements, so does `Isogeny.ker`, and the reduction of the
kernel count to Galois theory in `Isogeny/Kernel.lean` then closes: `F(W₁)` is Galois over the
pulled-back field, whose automorphisms are exactly the translations by kernel points, and which is
the fixed field of those translations.

## Main results

* `TauCeti.Isogeny.translation_fieldPullback`: **`τ_P^* ∘ φ^* = φ^* ∘ τ_{φ(P)}^*`** for a separable
  isogeny over a separably closed field.
* `TauCeti.Isogeny.mem_ker_iff_toPointHom_eq_zero`: a point lies in `Isogeny.ker` exactly when
  the point map sends it to `O₂`.
* `TauCeti.Isogeny.ker_eq_map_ker_toPointHom`: `Isogeny.ker` is the kernel of `toPointHom`.
* `TauCeti.Isogeny.card_ker_eq_degree`: **`#ker φ = deg φ`** for a separable isogeny over a
  separably closed field.
* `TauCeti.Isogeny.isGalois_fieldRange`,
  `TauCeti.Isogeny.exists_mem_ker_translation_eq_of_mem_fixingSubgroup` and
  `TauCeti.Isogeny.translationFixedField_ker`: `F(W₁)` is Galois over `φ^* F(W₂)` with group the
  translations by `ker φ`, and `φ^* F(W₂)` is the fixed field of those translations.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

local instance isIntegrallyClosed_coordinateRing_source : IsIntegrallyClosed W₁.CoordinateRing :=
  W₁.isIntegrallyClosed_coordinateRing
local instance isIntegrallyClosed_coordinateRing_target : IsIntegrallyClosed W₂.CoordinateRing :=
  W₂.isIntegrallyClosed_coordinateRing
local instance isDedekindDomain_coordinateRing_target : IsDedekindDomain W₂.CoordinateRing :=
  W₂.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- Translation commutes with the pullback of a function regular at all affine points of `W₂`:
at a point `Q` with `φ(Q)` and `φ(Q + P)` affine, both `τ_P^* φ^* z` and `φ^* τ_{φ(P)}^* z` take
the value of `z` at `φ(Q + P) = φ(Q) + φ(P)`, so their difference has infinitely many zeros. -/
private theorem translation_fieldPullback_of_forall_exists {P : W₁.Point} {z : W₂.FunctionField}
    (hz : ∀ (x' y' : F) (h' : W₂.Nonsingular x' y'), ∃ c : F,
      (Place.ofPrime F W₂.FunctionField (CoordinateRing.pointPlace h'.1)).valuation
        (z - algebraMap F W₂.FunctionField c) < 1) :
    translation W₁ (Point.equivBaseChangeSelf W₁ P) (φ.fieldPullback z) =
      φ.fieldPullback (translation W₂ (Point.equivBaseChangeSelf W₂ (φ.toPointHom P)) z) := by
  set σ := translation W₁ (Point.equivBaseChangeSelf W₁ P) with hσ
  set ρ := translation W₂ (Point.equivBaseChangeSelf W₂ (φ.toPointHom P)) with hρ
  set g := σ (φ.fieldPullback z) - φ.fieldPullback (ρ z) with hg
  -- `g` vanishes at every point `Q` with `φ(Q)` and `φ(Q + P)` affine
  have hzero : ∀ Q : W₁.Point, φ.toPointHom Q ≠ 0 → φ.toPointHom (Q + P) ≠ 0 →
      (pointEquivDegreeOnePlace W₁ Q).1.valuation g < 1 := by
    intro Q hQ hQP
    obtain ⟨x', y', h', hQP'⟩ : ∃ x' y' h', φ.toPointHom (Q + P) = .some x' y' h' := by
      cases h : φ.toPointHom (Q + P) with
      | zero => exact (hQP h).elim
      | some x' y' h' => exact ⟨x', y', h', rfl⟩
    obtain ⟨x'', y'', h'', hQ'⟩ : ∃ x' y' h', φ.toPointHom Q = .some x' y' h' := by
      cases h : φ.toPointHom Q with
      | zero => exact (hQ h).elim
      | some x' y' h' => exact ⟨x', y', h', rfl⟩
    obtain ⟨c, hc⟩ := hz x' y' h'
    -- `φ^* z` takes the value `c` at `Q + P`, and `τ_P^*` carries the place of `Q + P` to that
    -- of `Q`
    have hσval : (pointEquivDegreeOnePlace W₁ Q).1.valuation
        (σ (φ.fieldPullback z) - algebraMap F W₁.FunctionField c) < 1 := by
      have hsmul : σ • (pointEquivDegreeOnePlace W₁ (Q + P)).1 =
          (pointEquivDegreeOnePlace W₁ Q).1 := by
        rw [hσ, translation_smul_pointEquivDegreeOnePlace, add_sub_cancel_right]
      have hval := φ.valuation_fieldPullback_lt_one_of_toPointHom_eq_some hQP' hc
      rw [map_sub, AlgHom.commutes] at hval
      rw [← σ.commutes c, ← map_sub, ← hsmul, Place.valuation_smul_apply]
      exact hval
    -- `z` takes the value `c` at `φ(Q) + φ(P)`, and `τ_{φ(P)}^*` carries its place to that of
    -- `φ(Q)`
    have hρval : (Place.ofPrime F W₂.FunctionField (CoordinateRing.pointPlace h''.1)).valuation
        (ρ z - algebraMap F W₂.FunctionField c) < 1 := by
      have hsmul : ρ • (pointEquivDegreeOnePlace W₂ (φ.toPointHom (Q + P))).1 =
          (pointEquivDegreeOnePlace W₂ (φ.toPointHom Q)).1 := by
        rw [hρ, translation_smul_pointEquivDegreeOnePlace, map_add, add_sub_cancel_right]
      rw [hQP', hQ', coe_pointEquivDegreeOnePlace_some, coe_pointEquivDegreeOnePlace_some]
        at hsmul
      rw [← ρ.commutes c, ← map_sub, ← hsmul, Place.valuation_smul_apply]
      exact hc
    have hval := φ.valuation_fieldPullback_lt_one_of_toPointHom_eq_some hQ' hρval
    rw [map_sub, AlgHom.commutes] at hval
    rw [hg, ← sub_sub_sub_cancel_right _ _ (algebraMap F W₁.FunctionField c)]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hσval hval)
  -- a nonzero function has finitely many zeros, but only finitely many points are excluded and
  -- there are infinitely many points
  by_contra hne
  have hg0 : g ≠ 0 := sub_ne_zero.mpr hne
  have hfib : {Q : W₁.Point | φ.toPointHom Q = 0 ∨ φ.toPointHom (Q + P) = 0}.Finite :=
    (φ.finite_setOf_toPointHom_eq 0).union
      ((φ.finite_setOf_toPointHom_eq 0).preimage (add_left_injective P).injOn)
  have hf : Function.Injective fun Q : W₁.Point ↦ (pointEquivDegreeOnePlace W₁ Q).1 :=
    Subtype.val_injective.comp (pointEquivDegreeOnePlace W₁).injective
  refine ((Set.infinite_image_iff hf.injOn).mpr hfib.infinite_compl).mono ?_
    (Place.finite_setOf_ord_pos W₁.isFunctionField g)
  rintro _ ⟨Q, hQ, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or] at hQ
  exact (Place.valuation_lt_one_iff_ord_pos _ hg0).mp (hzero Q hQ.1 hQ.2)

/-- **Translation commutes with a separable isogeny**: `τ_P^* ∘ φ^* = φ^* ∘ τ_{φ(P)}^*` on the
function field of `W₂`, over a separably closed field. This is the function-field form of
`φ(Q + P) = φ(Q) + φ(P)`. -/
theorem translation_fieldPullback (P : W₁.Point) (z : W₂.FunctionField) :
    translation W₁ (Point.equivBaseChangeSelf W₁ P) (φ.fieldPullback z) =
      φ.fieldPullback (translation W₂ (Point.equivBaseChangeSelf W₂ (φ.toPointHom P)) z) := by
  set σ := translation W₁ (Point.equivBaseChangeSelf W₁ P)
  set ρ := translation W₂ (Point.equivBaseChangeSelf W₂ (φ.toPointHom P))
  -- both sides are `F`-algebra maps out of `F(W₂)`, agreeing on the coordinate functions
  have hcoord : (σ.toAlgHom.comp φ.fieldPullback).comp
      (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField) =
      (φ.fieldPullback.comp ρ.toAlgHom).comp
        (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField) := by
    refine CoordinateRing.algHom_ext ?_ ?_
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
        ← AdjoinRoot.mk_C, ← genericX_def]
      exact φ.translation_fieldPullback_of_forall_exists fun x' _ h' ↦
        ⟨x', valuation_pointPlace_genericX_sub_lt_one W₂ h'.1⟩
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
        ← AdjoinRoot.mk_X, ← genericY_def]
      exact φ.translation_fieldPullback_of_forall_exists fun _ y' h' ↦
        ⟨y', valuation_pointPlace_genericY_sub_lt_one W₂ h'.1⟩
  have hext := IsFractionRing.ringHom_ext (A := W₂.CoordinateRing) (K := W₂.FunctionField)
    (f1 := (σ.toAlgHom.comp φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField))
    (f2 := (φ.fieldPullback.comp ρ.toAlgHom : W₂.FunctionField →+* W₁.FunctionField))
    fun x ↦ AlgHom.congr_fun hcoord x
  exact RingHom.congr_fun hext z

/-- **A point lies in the kernel of a separable isogeny exactly when its point map kills it**, over
a separably closed field: `τ_P^*` fixes the pulled-back function field if and only if
`φ(P) = O₂` (Silverman III.4.10). -/
theorem mem_ker_iff_toPointHom_eq_zero (P : W₁.Point) :
    Point.equivBaseChangeSelf W₁ P ∈ φ.ker ↔ φ.toPointHom P = 0 := by
  constructor
  · intro hP
    let _ := φ.fieldPullback.toRingHom.toAlgebra
    have := φ.isScalarTower_of_algebraMap_eq_fieldPullback fun _ ↦ rfl
    have := φ.finiteDimensional_functionField fun _ ↦ rfl
    set σ := translation W₁ (Point.equivBaseChangeSelf W₁ P)
    have hfix : ∀ z : W₂.FunctionField,
        σ.symm (algebraMap W₂.FunctionField W₁.FunctionField z) =
          algebraMap W₂.FunctionField W₁.FunctionField z := fun z ↦
      σ.symm_apply_eq.mpr (mem_ker_iff.mp hP _ ⟨z, rfl⟩).symm
    -- `τ_P^*` fixes the pulled-back field, so it does not change the restriction of a place
    have hres : ∀ v : Place F W₁.FunctionField,
        (σ • v).restrict F W₂.FunctionField = v.restrict F W₂.FunctionField := fun v ↦ by
      rw [Place.restrict_eq_iff_isEquiv_comap]
      have : (σ • v).valuation.comap (algebraMap W₂.FunctionField W₁.FunctionField) =
          v.valuation.comap (algebraMap W₂.FunctionField W₁.FunctionField) :=
        Valuation.ext fun z ↦ by
          rw [Valuation.comap_apply, Valuation.comap_apply, Place.valuation_smul, hfix]
      rw [this]
      exact (Place.restrict_eq_iff_isEquiv_comap F W₂.FunctionField v _).mp rfl
    -- the place of `φ(P)` is the restriction of the place of `P`, which `τ_P^*` carries to the
    -- place of `O₁`, whose restriction is the place of `φ(O₁) = O₂`
    have h := φ.coe_pointEquivDegreeOnePlace_toPointHom (fun _ ↦ rfl) P
    rw [← hres (pointEquivDegreeOnePlace W₁ P).1, translation_smul_pointEquivDegreeOnePlace,
      sub_self, ← φ.coe_pointEquivDegreeOnePlace_toPointHom (fun _ ↦ rfl) 0, map_zero] at h
    exact (pointEquivDegreeOnePlace W₂).injective (Subtype.ext h)
  · intro hP
    refine mem_ker_iff.mpr fun _ hz ↦ ?_
    obtain ⟨z, rfl⟩ := AlgHom.mem_fieldRange.mp hz
    rw [translation_fieldPullback, hP, map_zero, translation_zero, AlgEquiv.one_apply]

/-- **The kernel of a separable isogeny is the kernel of its point map**, over a separably closed
field, carried along the identification of the points of `W₁` with those of its trivial base
change. -/
theorem ker_eq_map_ker_toPointHom :
    φ.ker = φ.toPointHom.ker.map (Point.equivBaseChangeSelf W₁).toAddMonoidHom := by
  ext P
  rw [AddSubgroup.mem_map_equiv, AddMonoidHom.mem_ker, ← mem_ker_iff_toPointHom_eq_zero,
    AddEquiv.apply_symm_apply]

/-- **The kernel of a separable isogeny has `deg φ` points** over a separably closed field
(Silverman III.4.10(c)). -/
-- Simplify before `mem_ker_iff` rewrites membership in the kernel subtype.
@[simp↓] theorem card_ker_eq_degree : Nat.card φ.ker = φ.degree := by
  rw [ker_eq_map_ker_toPointHom, ← φ.card_ker_toPointHom_eq_degree]
  exact (Nat.card_congr (φ.toPointHom.ker.equivMapOfInjective _
    (Point.equivBaseChangeSelf W₁).injective).toEquiv).symm

omit [DecidableEq F] in
/-- **The function field of `W₁` is Galois over the field pulled back along a separable isogeny**,
over a separably closed field (Silverman III.4.10(b)). -/
theorem isGalois_fieldRange : IsGalois φ.fieldPullback.fieldRange W₁.FunctionField := by
  -- the kernel count needs decidable equality on `F`, which the conclusion does not mention
  classical
  exact (φ.card_ker_eq_degree_iff_isGalois_and_forall_exists_translation.mp
    φ.card_ker_eq_degree).1

attribute [instance] isGalois_fieldRange

/-- **Every automorphism of `F(W₁)` over the pulled-back field is the translation by a kernel
point**, over a separably closed field (Silverman III.4.10(b)). -/
theorem exists_mem_ker_translation_eq_of_mem_fixingSubgroup
    {σ : W₁.FunctionField ≃ₐ[F] W₁.FunctionField}
    (hσ : σ ∈ φ.fieldPullback.fieldRange.fixingSubgroup) :
    ∃ P ∈ φ.ker, translation W₁ P = σ := by
  obtain ⟨P, rfl⟩ :=
    (φ.card_ker_eq_degree_iff_isGalois_and_forall_exists_translation.mp φ.card_ker_eq_degree).2 σ hσ
  exact ⟨P, mem_ker_iff.mpr fun z hz ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ z hz,
    rfl⟩

/-- **The pulled-back field is the fixed field of the translations by the kernel**, over a
separably closed field (Silverman III.4.10(b)). -/
theorem translationFixedField_ker :
    translationFixedField W₁ φ.ker = φ.fieldPullback.fieldRange :=
  le_antisymm (φ.card_ker_eq_degree_iff.mp φ.card_ker_eq_degree)
    (φ.ker_def ▸ le_translationFixedField_translationFixingSubgroup W₁ _)

end TauCeti.Isogeny

end
