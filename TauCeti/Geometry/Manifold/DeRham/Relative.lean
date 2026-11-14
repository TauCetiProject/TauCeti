/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Relative
public import TauCeti.Geometry.Manifold.DeRham.DegreeZero
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.DeRham.Extend

/-!
# The relative de Rham complex of an open pair

For an open subset `W` of a manifold `M`, restriction of smooth forms is a cochain map from the
de Rham complex of `M` to that of `W`. Extending both complexes by zero to negative degrees along
`ComplexShape.embeddingUpNat`, the relative de Rham complex `TauCeti.relativeDeRhamComplex I M W` is
Mathlib's mapping cocone `CochainComplex.mappingCocone` of the extended restriction, the shifted
mapping cone. Its cohomology is the relative de Rham cohomology of the pair `(M, W)`.

In degree `k + 1` the relative complex is identified with `Ω^(k+1)(M) × Ω^k(W)`
(`TauCeti.relativeDeRhamComplex.XEquiv`), and in degree `0` with `Ω^0(M)`
(`TauCeti.relativeDeRhamComplex.XEquivZero`); it vanishes in negative degrees. These coordinates
are the relative coordinates `CochainComplex.mappingCocone.relativeCoordinates` of the cocone, whose
second component is the negative of the second projection of the shifted cone. In them the
differential is `(α, β) ↦ (dα, α|_W - dβ)`. Hence a relative cocycle is a pair of a closed form `α`
on `M` and a form `β` on `W` with `α|_W = dβ`, and relative coboundaries are the pairs
`(dγ, γ|_W - dη)`. In degree `0` the relative cocycles are the locally constant functions on `M`
vanishing on `W`.

`TauCeti.relativeDeRhamComplex.mk` sends a relative cocycle of positive degree to its relative
de Rham cohomology class. The connecting map `TauCeti.relativeDeRhamComplex.δ` from the de Rham
cohomology of `W` to the relative cohomology of `(M, W)` sends the class of a closed form `b` on `W`
to `-[(0, b)]`; when `b` is the restriction of a form `b'` on `M`, this is the class `[(db', 0)]`.

A smooth map of pairs `f : (M, W) → (M', W')` induces a cochain map of relative complexes,
`TauCeti.relativeDeRhamComplex.map`, which in coordinates is pullback on both components. When `W`
is empty the first projection of the cocone is an isomorphism onto the extended de Rham complex of
`M`, so the relative complex recovers the absolute one.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Chapter I, §6.
-/

public section

noncomputable section

open CategoryTheory Limits
open TopologicalSpace (Opens)
open CochainComplex (mappingCocone mappingCone)
open scoped ContDiff Manifold

namespace TauCeti

universe u v

variable {E : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

namespace relativeDeRhamComplex

/-- Restriction of smooth forms to an open subset `W`, as a cochain map between the de Rham
complexes of `M` and of `W` extended by zero to negative degrees. -/
def restriction (W : Opens M) :
    (deRhamComplex I M).extend ComplexShape.embeddingUpNat ⟶
      (deRhamComplex I W).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap (deRhamComplex.map Subtype.val contMDiff_subtype_val) _

end relativeDeRhamComplex

variable (M) in
/-- The relative de Rham complex of an open pair `(M, W)`: the mapping cocone of the restriction
of forms from `M` to `W`, both de Rham complexes being extended by zero to negative degrees. -/
abbrev relativeDeRhamComplex (W : Opens M) : CochainComplex (ModuleCat ℝ) ℤ :=
  mappingCocone (relativeDeRhamComplex.restriction I W)

namespace relativeDeRhamComplex

variable {I} (W : Opens M)

/-- Under the canonical identifications of the objects with smooth forms, the restriction cochain
map is restriction of forms to `W`. -/
theorem restriction_f_extendXIso_inv (p : ℤ) (k : ℕ) (hk : (k : ℤ) = p)
    (α : SmoothForm I M ℝ k) :
    (restriction I W).f p (((deRhamComplex I M).extendXIso ComplexShape.embeddingUpNat hk).inv
        ((deRhamComplexXIso I k).inv α)) =
      ((deRhamComplex I W).extendXIso ComplexShape.embeddingUpNat hk).inv
        ((deRhamComplexXIso I k).inv
          (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)) := by
  rw [← deRhamComplex.extendXEquiv_symm_apply, ← deRhamComplex.extendXEquiv_symm_apply]
  exact deRhamComplex.extendMap_map_f_extendXEquiv_symm _ _ p k hk α

private lemma restriction_f_extendXEquiv_symm (p : ℤ) (k : ℕ) (hk : (k : ℤ) = p)
    (α : SmoothForm I M ℝ k) :
    (restriction I W).f p ((deRhamComplex.extendXEquiv I M p k hk).symm α) =
      (deRhamComplex.extendXEquiv I W p k hk).symm
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α) := by
  rw [deRhamComplex.extendXEquiv_symm_apply, deRhamComplex.extendXEquiv_symm_apply]
  exact restriction_f_extendXIso_inv W p k hk α

/-- The coordinates of the relative de Rham complex in degree `p = k + 1`: a pair of a
`(k + 1)`-form on `M` and a `k`-form on `W`. The second coordinate is the negative of the second
projection of the shifted mapping cone, so that the differential is `(α, β) ↦ (dα, α|_W - dβ)`. -/
def XEquiv (p : ℤ) (k : ℕ) (hk : ((k + 1 : ℕ) : ℤ) = p) :
    (relativeDeRhamComplex I M W).X p ≃ₗ[ℝ] SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k :=
  (mappingCocone.relativeCoordinates (restriction I W) p k (by omega)).trans
    ((deRhamComplex.extendXEquiv I M p (k + 1) hk).prodCongr
      (deRhamComplex.extendXEquiv I W k k rfl))

/-- The coordinate of the relative de Rham complex in degree `0`: a smooth function on `M`. -/
def XEquivZero : (relativeDeRhamComplex I M W).X 0 ≃ₗ[ℝ] SmoothForm I M ℝ 0 :=
  letI : Unique (((deRhamComplex I W).extend ComplexShape.embeddingUpNat).X (-1)) :=
    @uniqueOfSubsingleton _ (deRhamComplex.subsingleton_extend_X I W (by norm_num)) 0
  (mappingCocone.relativeCoordinates (restriction I W) 0 (-1) rfl).trans
    (((deRhamComplex.extendXEquiv I M 0 0 rfl).prodCongr (LinearEquiv.refl ℝ _)).trans
      (LinearEquiv.prodUnique (R := ℝ)))

/-- The relative de Rham complex vanishes in negative degrees. -/
theorem isZero_X_of_neg {p : ℤ} (hp : p < 0) : IsZero ((relativeDeRhamComplex I M W).X p) := by
  have := deRhamComplex.subsingleton_extend_X I M hp
  have := deRhamComplex.subsingleton_extend_X I W (p := p + -1) (by omega)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (mappingCocone.relativeCoordinates (restriction I W) p (p + -1) rfl).toEquiv.subsingleton

private lemma XEquiv_symm_eq (p : ℤ) (k : ℕ) (hk : ((k + 1 : ℕ) : ℤ) = p)
    (x : SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k) :
    (XEquiv W p k hk).symm x = (mappingCocone.relativeCoordinates (restriction I W) p k
      (by omega)).symm ((deRhamComplex.extendXEquiv I M p (k + 1) hk).symm x.1,
        (deRhamComplex.extendXEquiv I W k k rfl).symm x.2) :=
  rfl

private lemma XEquivZero_symm_eq (α : SmoothForm I M ℝ 0) :
    (XEquivZero W).symm α =
      (mappingCocone.relativeCoordinates (restriction I W) 0 (-1) rfl).symm
        ((deRhamComplex.extendXEquiv I M 0 0 rfl).symm α, 0) := by
  apply (XEquivZero W).injective
  rw [LinearEquiv.apply_symm_apply]
  unfold XEquivZero
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  simp

/-- In coordinates, the differential of the relative de Rham complex in positive degree is
`(α, β) ↦ (dα, α|_W - dβ)`. -/
@[simp]
theorem d_XEquiv_symm (p p' : ℤ) (k : ℕ) (hk : ((k + 1 : ℕ) : ℤ) = p) (hp' : p + 1 = p')
    (α : SmoothForm I M ℝ (k + 1)) (β : SmoothForm I W ℝ k) :
    (relativeDeRhamComplex I M W).d p p' ((XEquiv W p k hk).symm (α, β)) =
      (XEquiv W p' (k + 1) (by push_cast; omega)).symm
        (mextDerivₗ I (k + 1) α,
          SmoothForm.mpullback Subtype.val contMDiff_subtype_val α - mextDerivₗ I k β) := by
  subst hk hp'
  rw [XEquiv_symm_eq, XEquiv_symm_eq]
  refine (mappingCocone.d_relativeCoordinates_symm _ _ k (by omega) _).trans
    (congrArg _ (Prod.ext (deRhamComplex.extend_d_extendXEquiv_symm I M _ _ _ _ _ _) ?_))
  dsimp only
  rw [map_sub, restriction_f_extendXEquiv_symm,
    deRhamComplex.extend_d_extendXEquiv_symm I W k _ k rfl rfl]

/-- In coordinates, the differential of the relative de Rham complex in degree `0` is
`α ↦ (dα, α|_W)`. -/
@[simp]
theorem d_XEquivZero_symm (α : SmoothForm I M ℝ 0) :
    (relativeDeRhamComplex I M W).d 0 1 ((XEquivZero W).symm α) =
      (XEquiv W 1 0 rfl).symm
        (mextDerivₗ I 0 α, SmoothForm.mpullback Subtype.val contMDiff_subtype_val α) := by
  have := deRhamComplex.subsingleton_extend_X I W (p := -1) (by norm_num)
  rw [XEquivZero_symm_eq, XEquiv_symm_eq]
  refine (mappingCocone.d_relativeCoordinates_symm _ 0 (-1) rfl _).trans
    (congrArg _ (Prod.ext (deRhamComplex.extend_d_extendXEquiv_symm I M _ _ _ _ _ _) ?_))
  dsimp only
  rw [map_zero, sub_zero]
  exact restriction_f_extendXEquiv_symm W 0 0 rfl α

/-- In coordinates, the first projection of the relative complex to the extended de Rham complex
of `M` remembers the form on `M`. -/
@[simp]
theorem fst_f_XEquiv_symm (p : ℤ) (k : ℕ) (hk : ((k + 1 : ℕ) : ℤ) = p)
    (α : SmoothForm I M ℝ (k + 1)) (β : SmoothForm I W ℝ k) :
    (mappingCocone.fst (restriction I W)).f p ((XEquiv W p k hk).symm (α, β)) =
      ((deRhamComplex I M).extendXIso ComplexShape.embeddingUpNat hk).inv
        ((deRhamComplexXIso I (k + 1)).inv α) := by
  rw [XEquiv_symm_eq, ← deRhamComplex.extendXEquiv_symm_apply]
  exact (congrArg Prod.fst (mappingCocone.relativeCoordinates_apply _ _ _ _ _)).symm.trans
    (congrArg Prod.fst (LinearEquiv.apply_symm_apply _ _))

/-- In degree `0`, the first projection of the relative complex is the identity in coordinates. -/
@[simp]
theorem fst_f_XEquivZero_symm (α : SmoothForm I M ℝ 0) :
    (mappingCocone.fst (restriction I W)).f 0 ((XEquivZero W).symm α) =
      ((deRhamComplex I M).extendXIso ComplexShape.embeddingUpNat rfl).inv
        ((deRhamComplexXIso I 0).inv α) := by
  rw [XEquivZero_symm_eq]
  exact ((congrArg Prod.fst (mappingCocone.relativeCoordinates_apply _ _ _ _ _)).symm.trans
    (congrArg Prod.fst (LinearEquiv.apply_symm_apply _ _))).trans
    (deRhamComplex.extendXEquiv_symm_apply I M 0 0 rfl α)

/-! ### Relative cocycles and coboundaries -/

/-- A pair `(α, β)` is a relative cocycle exactly when `α` is closed and `α|_W = dβ`. -/
theorem d_XEquiv_symm_eq_zero_iff (p p' : ℤ) (k : ℕ) (hk : ((k + 1 : ℕ) : ℤ) = p)
    (hp' : p + 1 = p') (α : SmoothForm I M ℝ (k + 1)) (β : SmoothForm I W ℝ k) :
    (relativeDeRhamComplex I M W).d p p' ((XEquiv W p k hk).symm (α, β)) = 0 ↔
      mextDerivₗ I (k + 1) α = 0 ∧
        SmoothForm.mpullback Subtype.val contMDiff_subtype_val α = mextDerivₗ I k β := by
  rw [d_XEquiv_symm W p p' k hk hp', LinearEquiv.map_eq_zero_iff, Prod.mk_eq_zero, sub_eq_zero]

/-- A smooth function is a relative cocycle in degree `0` exactly when it is closed and vanishes
on `W`. -/
theorem d_XEquivZero_symm_eq_zero_iff (α : SmoothForm I M ℝ 0) :
    (relativeDeRhamComplex I M W).d 0 1 ((XEquivZero W).symm α) = 0 ↔
      mextDerivₗ I 0 α = 0 ∧
        SmoothForm.mpullback Subtype.val contMDiff_subtype_val α = (0 : SmoothForm I W ℝ 0) := by
  rw [d_XEquivZero_symm, LinearEquiv.map_eq_zero_iff, Prod.mk_eq_zero]

/-- The relative cocycles of degree `0` are the locally constant functions on `M` vanishing
on `W`. -/
theorem d_XEquivZero_symm_eq_zero_iff_isLocallyConstant (α : SmoothForm I M ℝ 0) :
    (relativeDeRhamComplex I M W).d 0 1 ((XEquivZero W).symm α) = 0 ↔
      IsLocallyConstant (fun x ↦ α.1 x 0) ∧ ∀ x ∈ W, α.1 x 0 = 0 := by
  rw [d_XEquivZero_symm_eq_zero_iff, ← mem_closedForms_iff_mextDerivₗ_eq_zero,
    mem_closedForms_zero_iff]
  refine and_congr_right fun _ ↦ ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg (fun φ : SmoothForm I W ℝ 0 ↦ φ.1 ⟨x, hx⟩ 0) h
    rw [SmoothForm.mpullback_apply,
      Subsingleton.elim (fun _ ↦ _) (0 : Fin 0 → TangentSpace I x)] at this
    simpa using this
  · ext x v
    rw [SmoothForm.mpullback_apply, Subsingleton.elim (fun _ ↦ _) (0 : Fin 0 → _)]
    simpa using h x x.2

/-- A pair `(α, β)` in degree `k + 2` is a relative coboundary exactly when it is
`(dγ, γ|_W - dη)` for a form `γ` on `M` and a form `η` on `W`. -/
theorem XEquiv_symm_mem_range_d_iff (q p : ℤ) (k : ℕ) (hq : ((k + 1 : ℕ) : ℤ) = q)
    (hp : ((k + 1 + 1 : ℕ) : ℤ) = p) (α : SmoothForm I M ℝ (k + 1 + 1))
    (β : SmoothForm I W ℝ (k + 1)) :
    (XEquiv W p (k + 1) hp).symm (α, β) ∈
        LinearMap.range ((relativeDeRhamComplex I M W).d q p).hom ↔
      ∃ γ : SmoothForm I M ℝ (k + 1), ∃ η : SmoothForm I W ℝ k,
        mextDerivₗ I (k + 1) γ = α ∧
          SmoothForm.mpullback Subtype.val contMDiff_subtype_val γ - mextDerivₗ I k η = β := by
  have hqp : q + 1 = p := by omega
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨⟨γ, η⟩, rfl⟩ := (XEquiv W q k hq).symm.surjective y
    have h := (d_XEquiv_symm W q p k hq hqp γ η).symm.trans hy
    rw [(XEquiv W p (k + 1) _).symm.injective.eq_iff, Prod.mk.injEq] at h
    exact ⟨γ, η, h⟩
  · rintro ⟨γ, η, hγ, hη⟩
    exact ⟨(XEquiv W q k hq).symm (γ, η),
      (d_XEquiv_symm W q p k hq hqp γ η).trans (by rw [hγ, hη])⟩

/-- A pair `(α, β)` in degree `1` is a relative coboundary exactly when it is `(dγ, γ|_W)` for a
smooth function `γ` on `M`. -/
theorem XEquiv_symm_mem_range_d_zero_iff (α : SmoothForm I M ℝ 1) (β : SmoothForm I W ℝ 0) :
    (XEquiv W 1 0 rfl).symm (α, β) ∈
        LinearMap.range ((relativeDeRhamComplex I M W).d 0 1).hom ↔
      ∃ γ : SmoothForm I M ℝ 0,
        mextDerivₗ I 0 γ = α ∧ SmoothForm.mpullback Subtype.val contMDiff_subtype_val γ = β := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨γ, rfl⟩ := (XEquivZero W).symm.surjective y
    have h := (d_XEquivZero_symm W γ).symm.trans hy
    rw [(XEquiv W 1 0 rfl).symm.injective.eq_iff, Prod.mk.injEq] at h
    exact ⟨γ, h⟩
  · rintro ⟨γ, hγ, hβ⟩
    exact ⟨(XEquivZero W).symm γ, (d_XEquivZero_symm W γ).trans (by rw [hγ, hβ])⟩

/-! ### Relative cohomology classes and the connecting map -/

section Classes

variable (I)

/-- The relative cocycles of degree `k + 1` in coordinates: pairs `(α, β)` of a closed
`(k + 1)`-form `α` on `M` and a `k`-form `β` on `W` with `α|_W = dβ`. -/
def cocycles (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k) :=
  LinearMap.ker (((mextDerivₗ I (k + 1)).comp (LinearMap.fst ℝ _ _)).prod
    ((SmoothForm.mpullback Subtype.val contMDiff_subtype_val).comp (LinearMap.fst ℝ _ _) -
      (mextDerivₗ I k).comp (LinearMap.snd ℝ _ _)))

/-- Membership in the relative cocycles: `α` is closed and `α|_W = dβ`. -/
@[simp]
theorem mem_cocycles {k : ℕ} (x : SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k) :
    x ∈ cocycles I W k ↔ mextDerivₗ I (k + 1) x.1 = 0 ∧
      SmoothForm.mpullback Subtype.val contMDiff_subtype_val x.1 = mextDerivₗ I k x.2 := by
  simp [cocycles, sub_eq_zero]

/-- The relative de Rham cohomology class of a relative cocycle of degree `k + 1`. -/
def mk (k : ℕ) :
    cocycles I W k →ₗ[ℝ] (relativeDeRhamComplex I M W).homology ((k + 1 : ℕ) : ℤ) :=
  (relativeDeRhamComplex I M W).moduleCatHomologyClass (Z := cocycles I W k)
    (CochainComplex.next ℤ _)
    ((XEquiv W _ k rfl).symm.toLinearMap ∘ₗ (cocycles I W k).subtype) fun x ↦ by
      obtain ⟨⟨α, β⟩, hx⟩ := x
      exact (d_XEquiv_symm_eq_zero_iff W _ _ k rfl rfl α β).mpr ((mem_cocycles I W _).mp hx)

/-- Every relative de Rham cohomology class of positive degree is represented by a relative
cocycle. -/
theorem mk_surjective (k : ℕ) : Function.Surjective (mk I W k) := by
  rw [mk]
  refine (relativeDeRhamComplex I M W).moduleCatHomologyClass_surjective _ _ _ fun y hy ↦ ?_
  obtain ⟨⟨α, β⟩, rfl⟩ := (XEquiv W _ k rfl).symm.surjective y
  exact ⟨⟨(α, β), (mem_cocycles I W _).mpr
    ((d_XEquiv_symm_eq_zero_iff W _ _ k rfl rfl α β).mp hy)⟩, rfl⟩

/-- The class of a relative cocycle vanishes exactly when the cocycle is a coboundary. -/
theorem mk_eq_zero_iff (k : ℕ) (x : cocycles I W k) :
    mk I W k x = 0 ↔ ∃ y : (relativeDeRhamComplex I M W).X k,
      (relativeDeRhamComplex I M W).d k ((k + 1 : ℕ) : ℤ) y = (XEquiv W _ k rfl).symm x := by
  rw [mk]
  exact (relativeDeRhamComplex I M W).moduleCatHomologyClass_eq_zero_iff _ _ _ (by simp) x

/-- The pair `(0, b)` for a closed form `b` on `W` as a relative cocycle. -/
private def inrClosed (k : ℕ) : closedForms I W k →ₗ[ℝ] cocycles I W k :=
  ((LinearMap.inr ℝ _ _).comp (closedForms I W k).subtype).codRestrict _ fun b ↦ by
    rw [mem_cocycles]
    exact ⟨map_zero _, by simpa using ((mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp b.2).symm⟩

private lemma mk_inrClosed_eq_zero (k : ℕ) (b : closedForms I W k)
    (hb : b.1 ∈ exactForms I W k) : mk I W k (inrClosed I W k b) = 0 := by
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hb
    rw [show b = 0 from Subtype.ext hb, map_zero, map_zero]
  | succ k =>
    rw [exactForms_succ, LinearMap.mem_range] at hb
    obtain ⟨η, hη⟩ := hb
    rw [mk_eq_zero_iff]
    refine ⟨(XEquiv W _ k rfl).symm (0, -η),
      (d_XEquiv_symm W _ _ k rfl (by omega) _ _).trans ?_⟩
    simp [inrClosed, hη]

/-- The negative of the class of `(0, b)`, for closed forms `b` on `W`. -/
private def δClosed (k : ℕ) :
    closedForms I W k →ₗ[ℝ] (relativeDeRhamComplex I M W).homology ((k + 1 : ℕ) : ℤ) :=
  -(mk I W k ∘ₗ inrClosed I W k)

private lemma ker_le_ker_δClosed (k : ℕ) :
    LinearMap.ker (deRhamCohomology.mk I (M := W) k) ≤ LinearMap.ker (δClosed I W k) := by
  intro b hb
  rw [LinearMap.mem_ker, deRhamCohomology.mk_eq_zero_iff] at hb
  rw [LinearMap.mem_ker, δClosed, LinearMap.neg_apply, LinearMap.comp_apply,
    mk_inrClosed_eq_zero I W k b hb, neg_zero]

/-- The connecting map `H^k_dR(W) → H^(k+1)(M, W)` of the relative de Rham complex, with the sign
convention `δ[b] = -[(0, b)]` for a closed form `b` on `W`
(`TauCeti.relativeDeRhamComplex.δ_mk`). -/
def δ (k : ℕ) :
    deRhamCohomology I W k →ₗ[ℝ] (relativeDeRhamComplex I M W).homology ((k + 1 : ℕ) : ℤ) :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I W k)
    (M₂ := deRhamCohomology I W k)
    (M₃ := (relativeDeRhamComplex I M W).homology ((k + 1 : ℕ) : ℤ))
    (f := deRhamCohomology.mk I k) (deRhamCohomology.mk_surjective I k)
    ⟨δClosed I W k, ker_le_ker_δClosed I W k⟩

/-- The connecting map sends the class of a closed form `b` on `W` to `-[(0, b)]`. -/
theorem δ_mk (k : ℕ) (b : SmoothForm I W ℝ k) (hb : b ∈ closedForms I W k) :
    δ I W k (deRhamCohomology.mk I k ⟨b, hb⟩) =
      -mk I W k ⟨(0, b), (mem_cocycles I W _).mpr
        ⟨map_zero _, by
          simpa using ((mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp hb).symm⟩⟩ := by
  rw [δ, LinearMap.equivOfSurjective_apply]
  rfl

/-- If a closed form `b` on `W` is the restriction of a form `b'` on `M`, the connecting map sends
its class to the class of `(db', 0)`. -/
theorem δ_mk_of_mpullback_eq (k : ℕ) (b : SmoothForm I W ℝ k) (hb : b ∈ closedForms I W k)
    (b' : SmoothForm I M ℝ k)
    (hb' : SmoothForm.mpullback Subtype.val contMDiff_subtype_val b' = b) :
    δ I W k (deRhamCohomology.mk I k ⟨b, hb⟩) =
      mk I W k ⟨(mextDerivₗ I k b', 0), (mem_cocycles I W _).mpr
        ⟨LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) b', by
          rw [map_zero, ← SmoothForm.mextDerivₗ_mpullback, hb',
            (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp hb]⟩⟩ := by
  rw [δ_mk, neg_eq_iff_add_eq_zero, ← map_add, mk_eq_zero_iff]
  cases k with
  | zero => exact ⟨(XEquivZero W).symm b', (d_XEquivZero_symm W b').trans (by simp [hb'])⟩
  | succ k =>
    exact ⟨(XEquiv W _ k rfl).symm (b', 0),
      (d_XEquiv_symm W _ _ k rfl (by omega) b' 0).trans (by simp [hb'])⟩

end Classes

/-! ### Maps of pairs -/

section Map

variable {E' E'' : Type u} {H' H'' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I' : ModelWithCorners ℝ E' H'} {I'' : ModelWithCorners ℝ E'' H''}
  {M' M'' : Type v} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']
  [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' 2 M'']
  {W} {W' : Opens M'} {W'' : Opens M''}

/-- Pullback along a smooth map of pairs commutes with restriction to the open subsets. -/
private lemma restriction_comp_extendMap (f : M → M') (hf : ContMDiff I I' ∞ f)
    (hW : Set.MapsTo f W W') :
    restriction I' W' ≫ HomologicalComplex.extendMap
        (deRhamComplex.map (fun x : W ↦ (⟨f x, hW x.2⟩ : W')) (hf.restrict hW)) _ =
      HomologicalComplex.extendMap (deRhamComplex.map f hf) _ ≫ restriction I W := by
  simp only [restriction, ← HomologicalComplex.extendMap_comp, ← deRhamComplex.map_comp]
  rfl

/-- The cochain map of relative de Rham complexes induced by a smooth map of pairs
`f : (M, W) → (M', W')`, given by pullback of forms on `M'` and on `W'`. -/
def map (f : M → M') (hf : ContMDiff I I' ∞ f) (hW : Set.MapsTo f W W') :
    relativeDeRhamComplex I' M' W' ⟶ relativeDeRhamComplex I M W :=
  (mappingCone.map _ _ _ _ (restriction_comp_extendMap f hf hW))⟦(-1 : ℤ)⟧'

/-- In coordinates, the cochain map induced by a smooth map of pairs is pullback on both
components. -/
@[simp]
theorem map_f_XEquiv_symm (f : M → M') (hf : ContMDiff I I' ∞ f) (hW : Set.MapsTo f W W')
    (p : ℤ) (k : ℕ) (hk : ((k + 1 : ℕ) : ℤ) = p) (α : SmoothForm I' M' ℝ (k + 1))
    (β : SmoothForm I' W' ℝ k) :
    (map f hf hW).f p ((XEquiv W' p k hk).symm (α, β)) =
      (XEquiv W p k hk).symm (SmoothForm.mpullback f hf α,
        SmoothForm.mpullback (fun x : W ↦ (⟨f x, hW x.2⟩ : W')) (hf.restrict hW) β) := by
  apply (mappingCocone.relativeCoordinates (restriction I W) p k (by omega)).injective
  rw [XEquiv_symm_eq, XEquiv_symm_eq, LinearEquiv.apply_symm_apply]
  refine (mappingCocone.relativeCoordinates_map _ _ _ _ _ p k (by omega) _).trans ?_
  rw [LinearEquiv.apply_symm_apply, deRhamComplex.extendMap_map_f_extendXEquiv_symm,
    deRhamComplex.extendMap_map_f_extendXEquiv_symm]

/-- In degree `0`, the cochain map induced by a smooth map of pairs is pullback of functions. -/
@[simp]
theorem map_f_XEquivZero_symm (f : M → M') (hf : ContMDiff I I' ∞ f) (hW : Set.MapsTo f W W')
    (α : SmoothForm I' M' ℝ 0) :
    (map f hf hW).f 0 ((XEquivZero W').symm α) =
      (XEquivZero W).symm (SmoothForm.mpullback f hf α) := by
  apply (mappingCocone.relativeCoordinates (restriction I W) 0 (-1) rfl).injective
  rw [XEquivZero_symm_eq, XEquivZero_symm_eq, LinearEquiv.apply_symm_apply]
  refine (mappingCocone.relativeCoordinates_map _ _ _ _ _ 0 (-1) rfl _).trans ?_
  rw [LinearEquiv.apply_symm_apply, deRhamComplex.extendMap_map_f_extendXEquiv_symm, map_zero]

/-- The identity map of a pair induces the identity of its relative de Rham complex. -/
@[simp]
theorem map_id :
    map (I := I) (I' := I) (W := W) (W' := W) id contMDiff_id (Set.mapsTo_id _) = 𝟙 _ := by
  have h₁ : deRhamComplex.map (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id = 𝟙 _ :=
    deRhamComplex.map_id
  have h₂ : deRhamComplex.map (I := I) (I' := I) (fun x : W ↦ (⟨id x, Set.mapsTo_id _ x.2⟩ : W))
      (contMDiff_id.restrict (Set.mapsTo_id _)) = 𝟙 _ := deRhamComplex.map_id
  simp only [map, h₁, h₂, HomologicalComplex.extendMap_id, mappingCone.map_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The cochain maps induced by smooth maps of pairs reverse composition. -/
theorem map_comp (f : M → M') (g : M' → M'') (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I' I'' ∞ g) (hW : Set.MapsTo f W W') (hW' : Set.MapsTo g W' W'') :
    map (g ∘ f) (hg.comp hf) (hW'.comp hW) = map g hg hW' ≫ map f hf hW := by
  have h₁ := deRhamComplex.map_comp f g hf hg
  have h₂ := deRhamComplex.map_comp (fun x : W ↦ (⟨f x, hW x.2⟩ : W'))
    (fun x : W' ↦ (⟨g x, hW' x.2⟩ : W'')) (hf.restrict hW) (hg.restrict hW')
  refine Eq.trans ?_ ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map_comp _ _)
  rw [← mappingCone.map_comp]
  simp only [← HomologicalComplex.extendMap_comp, ← h₁, ← h₂]
  rfl

end Map

/-! ### The absolute case -/

/-- For an empty open subset `W`, the first projection identifies the relative de Rham complex of
`(M, W)` with the de Rham complex of `M` extended by zero. -/
instance isIso_fst_of_isEmpty [IsEmpty W] : IsIso (mappingCocone.fst (restriction I W)) := by
  have (p : ℤ) : IsIso ((mappingCocone.fst (restriction I W)).f p) := by
    let : Unique (((deRhamComplex I W).extend ComplexShape.embeddingUpNat).X (p + -1)) :=
      @uniqueOfSubsingleton _ (deRhamComplex.subsingleton_extend_X_of_isEmpty I W (p + -1)) 0
    rw [ConcreteCategory.isIso_iff_bijective]
    have h : ⇑((mappingCocone.fst (restriction I W)).f p) =
        Prod.fst ∘ mappingCocone.relativeCoordinates (restriction I W) p (p + -1) rfl :=
      funext fun x ↦ (congrArg Prod.fst (mappingCocone.relativeCoordinates_apply _ _ _ _ x)).symm
    rw [h]
    exact ((Equiv.prodUnique _ _).bijective.comp
      (mappingCocone.relativeCoordinates (restriction I W) p (p + -1) rfl).bijective)
  exact HomologicalComplex.Hom.isIso_of_components _

end relativeDeRhamComplex

end TauCeti
