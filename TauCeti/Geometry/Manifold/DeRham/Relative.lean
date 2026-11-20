/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Relative
public import Mathlib.Algebra.Homology.Embedding.Extend
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The relative de Rham complex of an open pair

Let `W` be an open subset of a manifold `M`. Extend the de Rham complexes of `M` and of `W` by zero
to `ℤ`-indexed complexes along `ComplexShape.embeddingUpNat`. The *relative de Rham complex*
`TauCeti.relativeDeRhamComplex I W` is Mathlib's mapping cocone of the extended restriction map
`TauCeti.deRhamRestriction I W`. Its cohomology is the relative de Rham cohomology `H^q(M, W)`
(`TauCeti.relativeDeRhamCohomology`).

In degree `k + 1` a relative cochain is a pair `(α, β)` of a `(k + 1)`-form `α` on `M` and a
`k`-form `β` on `W` (`TauCeti.relativeDeRhamComplex.coord`). These are the relative coordinates
`CochainComplex.mappingCocone.relativeCoordinates` of the cocone, which negate Mathlib's second
projection, read through the identification of the terms of the extended complexes with forms. In
these coordinates the differential is

`d (α, β) = (dα, α|_W - dβ)`

(`TauCeti.relativeDeRhamComplex.coord_d`). Writing `inl α = (α, 0)` and `inr β = (0, β)`, this
reads `d (inl α) = inl (dα) + inr (α|_W)` and `d (inr β) = -inr (dβ)`
(`TauCeti.relativeDeRhamComplex.d_inl`, `TauCeti.relativeDeRhamComplex.d_inr`). In degree `0` a
relative cochain is a function on `M` (`TauCeti.relativeDeRhamComplex.inl_zero_bijective`). So the
relative cocycles are the pairs with `dα = 0` and `α|_W = dβ`
(`TauCeti.relativeDeRhamComplex.d_coord_symm_eq_zero_iff`), and the relative coboundaries are the
pairs `(dγ, γ|_W - dε)` (`TauCeti.relativeDeRhamComplex.coord_symm_mem_range_d_iff`). A smooth map
of open pairs `(M, W) → (M', W')` acts componentwise by pullback
(`TauCeti.relativeDeRhamComplex.map_inl`, `TauCeti.relativeDeRhamComplex.map_inr`).

The class of a relative cocycle `(α, β)` is `TauCeti.relativeDeRhamCohomology.mk`. The connecting
map `δ : H^k(W) → H^(k+1)(M, W)` is `δ [b] = -[(0, b)]`
(`TauCeti.relativeDeRhamCohomology.δ_mk`). When `b` is the restriction of a `k`-form `b'` on `M`,
it is the class of `(db', 0)` (`TauCeti.relativeDeRhamCohomology.δ_mk_of_mpullback_eq`), since
`d (b', 0) = (db', b)`. This fixes the sign of `δ` for its comparison with the connecting map of
singular cohomology.

Two degenerate pairs recover known groups. In degree `0` the relative cohomology is the space of
functions on `M` with zero differential that vanish on `W`
(`TauCeti.relativeDeRhamCohomology.classZero_bijective`). For empty `W` the first projection of
the cocone is an isomorphism onto the extended de Rham complex of `M`
(`TauCeti.relativeDeRhamComplex.isIso_fst_of_isEmpty`), so it identifies `H^k(M, ∅)` with the de
Rham cohomology of `M`.

The construction needs no finite dimensionality, separation or countability of `M`.

## Main definitions

* `TauCeti.deRhamRestriction I W`: the restriction of forms to `W`, extended to `ℤ`.
* `TauCeti.relativeDeRhamComplex I W`: the relative de Rham complex of the open pair `(M, W)`.
* `TauCeti.relativeDeRhamCohomology I W q`: its cohomology.
* `TauCeti.relativeDeRhamComplex.coord`, `TauCeti.relativeDeRhamComplex.inl`,
  `TauCeti.relativeDeRhamComplex.inr`: coordinates of relative cochains.
* `TauCeti.relativeDeRhamComplex.map`: the cochain map induced by a smooth map of open pairs.
* `TauCeti.relativeDeRhamCohomology.cocycles`, `TauCeti.relativeDeRhamCohomology.mk`: relative
  cocycles of positive degree and their classes.
* `TauCeti.relativeDeRhamCohomology.δ`: the connecting map `H^k(W) → H^(k+1)(M, W)`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, Chapter I, §6 (the relative de Rham complex of a map).
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace
open scoped ContDiff

namespace TauCeti

universe u v

variable {E : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

section Extend

variable (M) in
/-- The degree-`k` term of the de Rham complex extended by zero to `ℤ`, identified with smooth
`k`-forms. -/
def deRhamComplexExtendXEquiv (k : ℕ) (p : ℤ) (hp : (k : ℤ) = p) :
    ((deRhamComplex I M).extend ComplexShape.embeddingUpNat).X p ≃ₗ[ℝ]
      SmoothForm I M ℝ k :=
  ((extendXIso _ ComplexShape.embeddingUpNat hp).trans
    (deRhamComplexXIso I k)).toLinearEquiv

/-- The inverse identification sends a form to its image in the extended complex. -/
theorem deRhamComplexExtendXEquiv_symm_apply (k : ℕ) (p : ℤ) (hp : (k : ℤ) = p)
    (φ : SmoothForm I M ℝ k) :
    (deRhamComplexExtendXEquiv I M k p hp).symm φ =
      (extendXIso (deRhamComplex I M) ComplexShape.embeddingUpNat hp).inv
        ((deRhamComplexXIso I k).inv φ) :=
  (rfl)

/-- The differential of the extended de Rham complex is the exterior derivative. -/
@[simp]
theorem deRhamComplexExtend_d_symm_apply (k : ℕ) (p q : ℤ) (hp : (k : ℤ) = p)
    (hq : ((k + 1 : ℕ) : ℤ) = q) (φ : SmoothForm I M ℝ k) :
    ((deRhamComplex I M).extend ComplexShape.embeddingUpNat).d p q
        ((deRhamComplexExtendXEquiv I M k p hp).symm φ) =
      (deRhamComplexExtendXEquiv I M (k + 1) q hq).symm (mextDerivₗ I (F := ℝ) k φ) := by
  simp only [deRhamComplexExtendXEquiv_symm_apply,
    extend_d_eq _ ComplexShape.embeddingUpNat hp hq, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rw [deRhamComplex_d_apply]
  simp

/-- The extended de Rham complex vanishes in negative degrees. -/
theorem subsingleton_deRhamComplexExtend_X {p : ℤ} (hp : p < 0) :
    Subsingleton (((deRhamComplex I M).extend ComplexShape.embeddingUpNat).X p) :=
  ModuleCat.subsingleton_of_isZero <| isZero_extend_X _ _ _ fun n hn ↦ by
    have : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    simp only [ComplexShape.embeddingUpNat_f] at hn
    lia

/-- The map of extended de Rham complexes induced by a smooth map is pullback of forms. -/
@[simp]
theorem extendMap_deRhamComplexMap_f_symm_apply {E' : Type u} {H' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type v} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' 2 M'] {g : M → M'} (hg : ContMDiff I I' ∞ g) (k : ℕ) (p : ℤ)
    (hp : (k : ℤ) = p) (φ : SmoothForm I' M' ℝ k) :
    (extendMap (deRhamComplex.map g hg) ComplexShape.embeddingUpNat).f p
        ((deRhamComplexExtendXEquiv I' M' k p hp).symm φ) =
      (deRhamComplexExtendXEquiv I M k p hp).symm (SmoothForm.mpullback g hg φ) := by
  simp only [deRhamComplexExtendXEquiv_symm_apply,
    extendMap_f _ ComplexShape.embeddingUpNat hp, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rw [deRhamComplex.map_f_inv_apply]

end Extend

variable (W : Opens M)

/-- The restriction of smooth forms from `M` to the open subset `W`, as a map of de Rham complexes
extended by zero to `ℤ`-indexed complexes. -/
def deRhamRestriction :
    (deRhamComplex I M).extend ComplexShape.embeddingUpNat ⟶
      (deRhamComplex I W).extend ComplexShape.embeddingUpNat :=
  extendMap (deRhamComplex.map (I := I) (I' := I) (Subtype.val : W → M) contMDiff_subtypeVal) _

/-- The restriction map pulls a form back along the inclusion of `W`. -/
@[simp]
theorem deRhamRestriction_f_symm_apply (k : ℕ) (p : ℤ) (hp : (k : ℤ) = p)
    (φ : SmoothForm I M ℝ k) :
    (deRhamRestriction I W).f p ((deRhamComplexExtendXEquiv I M k p hp).symm φ) =
      (deRhamComplexExtendXEquiv I W k p hp).symm
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal φ) :=
  extendMap_deRhamComplexMap_f_symm_apply I _ k p hp φ

/-- The relative de Rham complex of the open pair `(M, W)`: the mapping cocone of the restriction
of forms from `M` to `W`. -/
abbrev relativeDeRhamComplex : CochainComplex (ModuleCat ℝ) ℤ :=
  CochainComplex.mappingCocone (deRhamRestriction I W)

/-- The relative de Rham cohomology `H^q(M, W)` of the open pair `(M, W)`. -/
abbrev relativeDeRhamCohomology (q : ℤ) : Type _ :=
  (relativeDeRhamComplex I W).homology q

namespace relativeDeRhamComplex

open CochainComplex.mappingCocone

/-- The relative cochain `(α, 0)` of degree `k`, for a `k`-form `α` on `M`. -/
def inl (k : ℕ) : SmoothForm I M ℝ k →ₗ[ℝ] (relativeDeRhamComplex I W).X k :=
  ((CochainComplex.mappingCocone.inl (deRhamRestriction I W)).v k k (add_zero _)).hom ∘ₗ
    (deRhamComplexExtendXEquiv I M k k rfl).symm.toLinearMap

/-- The relative cochain `(0, β)` of degree `k + 1`, for a `k`-form `β` on `W`. -/
def inr (k : ℕ) : SmoothForm I W ℝ k →ₗ[ℝ] (relativeDeRhamComplex I W).X (k + 1 : ℕ) :=
  -(((CochainComplex.mappingCocone.inr (deRhamRestriction I W)).val.v k (k + 1 : ℕ)
    (by push_cast; rfl)).hom ∘ₗ (deRhamComplexExtendXEquiv I W k k rfl).symm.toLinearMap)

/-- `CochainComplex.mappingCocone.relativeCoordinates_d` with the target degree written
`((k + 1 : ℕ) : ℤ)`, the form in which the degrees of `inl` and `inr` are stated; it is
definitionally `(k : ℤ) + 1`, since `Int` addition computes on casts of natural numbers. -/
private theorem relativeCoordinates_d_natCast (k : ℕ) (q : ℤ) (hq : (k : ℤ) + -1 = q)
    (x : (relativeDeRhamComplex I W).X k) :
    relativeCoordinates (deRhamRestriction I W) (k + 1 : ℕ) k (by push_cast; lia)
        ((relativeDeRhamComplex I W).d k (k + 1 : ℕ) x) =
      (((deRhamComplex I M).extend ComplexShape.embeddingUpNat).d k (k + 1 : ℕ)
          (relativeCoordinates (deRhamRestriction I W) k q hq x).1,
        (deRhamRestriction I W).f k (relativeCoordinates (deRhamRestriction I W) k q hq x).1 -
          ((deRhamComplex I W).extend ComplexShape.embeddingUpNat).d q k
            (relativeCoordinates (deRhamRestriction I W) k q hq x).2) :=
  relativeCoordinates_d _ k q hq x

/-- The relative coordinates of `inl α` are `(α, 0)`. -/
@[simp]
theorem relativeCoordinates_inl (k : ℕ) (q : ℤ) (hq : (k : ℤ) + -1 = q)
    (α : SmoothForm I M ℝ k) :
    relativeCoordinates (deRhamRestriction I W) k q hq (inl I W k α) =
      ((deRhamComplexExtendXEquiv I M k k rfl).symm α, 0) := by
  rw [relativeCoordinates_apply]
  have h₁ := ConcreteCategory.congr_hom (inl_v_fst_f (deRhamRestriction I W) k)
    ((deRhamComplexExtendXEquiv I M k k rfl).symm α)
  have h₂ := ConcreteCategory.congr_hom (inl_v_snd_v (deRhamRestriction I W) k q hq)
    ((deRhamComplexExtendXEquiv I M k k rfl).symm α)
  simp only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply, ModuleCat.id_apply]
    at h₁ h₂
  simp [inl, h₁, h₂]

/-- The relative coordinates of `inr β` are `(0, β)`. -/
theorem relativeCoordinates_inr (k : ℕ) (hpk : ((k + 1 : ℕ) : ℤ) + -1 = k)
    (β : SmoothForm I W ℝ k) :
    relativeCoordinates (deRhamRestriction I W) (k + 1 : ℕ) k hpk (inr I W k β) =
      (0, (deRhamComplexExtendXEquiv I W k k rfl).symm β) := by
  rw [relativeCoordinates_apply]
  have h₁ := ConcreteCategory.congr_hom
    (inr_v_fst_f (deRhamRestriction I W) k (k + 1 : ℕ) (by push_cast; rfl))
    ((deRhamComplexExtendXEquiv I W k k rfl).symm β)
  have h₂ := ConcreteCategory.congr_hom
    (inr_v_snd_v (deRhamRestriction I W) k (k + 1 : ℕ) (by push_cast; rfl))
    ((deRhamComplexExtendXEquiv I W k k rfl).symm β)
  simp only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply, ModuleCat.id_apply]
    at h₁ h₂
  simp only [inr, LinearMap.neg_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_neg,
    neg_neg]
  refine Prod.ext ?_ h₂
  -- The goal applies `inr` through the `ModuleCat.Hom.hom` abbreviation, while `h₁` uses
  -- `ConcreteCategory.hom`; unfolding the abbreviation lets `h₁` rewrite.
  dsimp only [ModuleCat.Hom.hom]
  rw [h₁, neg_zero]

/-- In degree `k + 1`, a relative cochain is a pair `(α, β)` of a `(k + 1)`-form `α` on `M` and a
`k`-form `β` on `W`. -/
def coord (k : ℕ) :
    (relativeDeRhamComplex I W).X (k + 1 : ℕ) ≃ₗ[ℝ]
      SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k :=
  (relativeCoordinates (deRhamRestriction I W) _ k (by push_cast; lia)).trans
    ((deRhamComplexExtendXEquiv I M (k + 1) _ rfl).prodCongr
      (deRhamComplexExtendXEquiv I W k k rfl))

/-- The coordinates of `inl α` are `(α, 0)`. -/
theorem coord_inl (k : ℕ) (α : SmoothForm I M ℝ (k + 1)) :
    coord I W k (inl I W (k + 1) α) = (α, 0) := by
  simp only [coord, LinearEquiv.trans_apply]
  rw [relativeCoordinates_inl]
  simp

/-- The coordinates of `inr β` are `(0, β)`. -/
theorem coord_inr (k : ℕ) (β : SmoothForm I W ℝ k) :
    coord I W k (inr I W k β) = (0, β) := by
  simp only [coord, LinearEquiv.trans_apply]
  rw [relativeCoordinates_inr]
  simp

/-- Every relative cochain of degree `k + 1` is `inl α + inr β` for its coordinates `(α, β)`. -/
theorem coord_symm_apply (k : ℕ) (α : SmoothForm I M ℝ (k + 1)) (β : SmoothForm I W ℝ k) :
    (coord I W k).symm (α, β) = inl I W (k + 1) α + inr I W k β := by
  apply (coord I W k).injective
  rw [LinearEquiv.apply_symm_apply, map_add, coord_inl, coord_inr]
  simp

/-- In degree `0` a relative cochain is a smooth function on `M`: `inl` is bijective there. -/
theorem inl_zero_bijective : Function.Bijective (inl I W 0) := by
  have := subsingleton_deRhamComplexExtend_X I (M := W) (p := ((0 : ℕ) : ℤ) + -1) (by lia)
  refine ⟨fun α β h ↦ ?_, fun x ↦ ?_⟩
  · have h' := congrArg (relativeCoordinates (deRhamRestriction I W) _ _ rfl) h
    rw [relativeCoordinates_inl, relativeCoordinates_inl] at h'
    exact (deRhamComplexExtendXEquiv I M 0 0 rfl).symm.injective (congrArg Prod.fst h')
  · set e := relativeCoordinates (deRhamRestriction I W) ((0 : ℕ) : ℤ) _ rfl
    refine ⟨deRhamComplexExtendXEquiv I M 0 ((0 : ℕ) : ℤ) rfl (e x).1, e.injective ?_⟩
    rw [relativeCoordinates_inl, LinearEquiv.symm_apply_apply]
    exact Prod.ext rfl (Subsingleton.elim _ _)

/-- The differential of `inl α` is `inl (dα) + inr (α|_W)`. -/
theorem d_inl (k : ℕ) (α : SmoothForm I M ℝ k) :
    (relativeDeRhamComplex I W).d k (k + 1 : ℕ) (inl I W k α) =
      inl I W (k + 1) (mextDerivₗ I (F := ℝ) k α) +
        inr I W k (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal α) := by
  rw [← coord_symm_apply]
  apply (relativeCoordinates (deRhamRestriction I W) (k + 1 : ℕ) k (by push_cast; lia)).injective
  rw [relativeCoordinates_d_natCast _ _ k (k + -1) rfl, relativeCoordinates_inl]
  simp only [coord, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.prodCongr_symm,
    LinearEquiv.prodCongr_apply, LinearEquiv.apply_symm_apply, map_zero, sub_zero]
  rw [deRhamComplexExtend_d_symm_apply I k k _ rfl rfl, deRhamRestriction_f_symm_apply]

/-- The differential of `inr β` is `-inr (dβ)`. -/
theorem d_inr (k : ℕ) (β : SmoothForm I W ℝ k) :
    (relativeDeRhamComplex I W).d (k + 1 : ℕ) (k + 1 + 1 : ℕ) (inr I W k β) =
      -inr I W (k + 1) (mextDerivₗ I (F := ℝ) k β) := by
  apply (relativeCoordinates (deRhamRestriction I W) (k + 1 + 1 : ℕ) (k + 1 : ℕ)
    (by push_cast; lia)).injective
  rw [relativeCoordinates_d_natCast _ _ (k + 1) k (by push_cast; lia), relativeCoordinates_inr,
    map_neg, relativeCoordinates_inr]
  simp only [map_zero, zero_sub, Prod.neg_mk, neg_zero]
  rw [deRhamComplexExtend_d_symm_apply I k k _ rfl rfl]

/-- In coordinates the differential is `d (α, β) = (dα, α|_W - dβ)`. -/
theorem coord_d (k : ℕ) (α : SmoothForm I M ℝ (k + 1)) (β : SmoothForm I W ℝ k) :
    coord I W (k + 1) ((relativeDeRhamComplex I W).d (k + 1 : ℕ) (k + 1 + 1 : ℕ)
        ((coord I W k).symm (α, β))) =
      (mextDerivₗ I (F := ℝ) (k + 1) α,
        SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal α -
          mextDerivₗ I (F := ℝ) k β) := by
  have h : (relativeDeRhamComplex I W).d (k + 1 : ℕ) (k + 1 + 1 : ℕ)
      ((coord I W k).symm (α, β)) =
        (coord I W (k + 1)).symm (mextDerivₗ I (F := ℝ) (k + 1) α,
        SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal α -
          mextDerivₗ I (F := ℝ) k β) := by
    rw [coord_symm_apply, coord_symm_apply, map_add, d_inl, d_inr, map_sub]
    abel
  rw [h, LinearEquiv.apply_symm_apply]

/-- A relative cochain `(α, β)` is a cocycle exactly when `dα = 0` and `α|_W = dβ`. -/
theorem d_coord_symm_eq_zero_iff (k : ℕ)
    (x : SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k) :
    (relativeDeRhamComplex I W).d (k + 1 : ℕ) (k + 1 + 1 : ℕ) ((coord I W k).symm x) = 0 ↔
      mextDerivₗ I (F := ℝ) (k + 1) x.1 = 0 ∧
        SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal x.1 =
          mextDerivₗ I (F := ℝ) k x.2 := by
  obtain ⟨α, β⟩ := x
  rw [← (coord I W (k + 1)).map_eq_zero_iff, coord_d, Prod.mk_eq_zero, sub_eq_zero]

/-- A relative cochain `(α, β)` of degree `k + 2` is a coboundary exactly when it is
`(dγ, γ|_W - dε)` for some pair `(γ, ε)`. -/
theorem coord_symm_mem_range_d_iff (k : ℕ) (α : SmoothForm I M ℝ (k + 1 + 1))
    (β : SmoothForm I W ℝ (k + 1)) :
    (coord I W (k + 1)).symm (α, β) ∈
        LinearMap.range ((relativeDeRhamComplex I W).d (k + 1 : ℕ) (k + 1 + 1 : ℕ)).hom ↔
      ∃ γ : SmoothForm I M ℝ (k + 1), ∃ ε : SmoothForm I W ℝ k,
        mextDerivₗ I (F := ℝ) (k + 1) γ = α ∧
          SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal γ -
            mextDerivₗ I (F := ℝ) k ε = β := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨⟨γ, ε⟩, rfl⟩ := (coord I W k).symm.surjective x
    refine ⟨γ, ε, ?_⟩
    have h := congrArg (coord I W (k + 1)) hx
    rw [coord_d, LinearEquiv.apply_symm_apply] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨γ, ε, rfl, rfl⟩
    exact ⟨(coord I W k).symm (γ, ε), (coord I W (k + 1)).injective (by
      rw [coord_d, LinearEquiv.apply_symm_apply])⟩

section Map

variable {E' : Type u} {H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {M' : Type v} [TopologicalSpace M']
  [ChartedSpace H' M'] [IsManifold I' 2 M'] {W' : Opens M'} {f : M → M'} {g : W → W'}

omit [IsManifold I 2 M] [IsManifold I' 2 M'] in
/-- The restriction `g : W → W'` of a smooth map `f : M → M'` is smooth. -/
private theorem contMDiff_of_val_comp (hf : ContMDiff I I' ∞ f) (hfg : ∀ x, (g x : M') = f x) :
    ContMDiff I I' ∞ g :=
  (ContMDiff.subtypeVal_comp_iff W' g).mp (by
    convert hf.comp contMDiff_subtypeVal using 1
    exact funext hfg)

private theorem deRhamRestriction_comm (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g)
    (hfg : ∀ x, (g x : M') = f x) :
    deRhamRestriction I' W' ≫ extendMap (deRhamComplex.map g hg) _ =
      extendMap (deRhamComplex.map f hf) _ ≫ deRhamRestriction I W := by
  simp only [deRhamRestriction, ← extendMap_comp, ← deRhamComplex.map_comp]
  congr 2
  exact funext hfg

/-- The cochain map of relative de Rham complexes induced by a smooth map of open pairs
`f : (M, W) → (M', W')`, given with its restriction `g : W → W'`; it is pullback on both
components. -/
def map (hf : ContMDiff I I' ∞ f) (hfg : ∀ x, (g x : M') = f x) :
    relativeDeRhamComplex I' W' ⟶ relativeDeRhamComplex I W :=
  (CochainComplex.mappingCone.map _ _ _ _
    (deRhamRestriction_comm I W hf (contMDiff_of_val_comp I W hf hfg) hfg))⟦(-1 : ℤ)⟧'

/-- In relative coordinates the induced map acts by pullback on both components. -/
private theorem relativeCoordinates_map_f (hf : ContMDiff I I' ∞ f)
    (hfg : ∀ x, (g x : M') = f x) (p q : ℤ) (hpq : p + -1 = q)
    (x : (relativeDeRhamComplex I' W').X p) :
    relativeCoordinates (deRhamRestriction I W) p q hpq ((map I W hf hfg).f p x) =
      ((extendMap (deRhamComplex.map f hf) _).f p
          (relativeCoordinates (deRhamRestriction I' W') p q hpq x).1,
        (extendMap (deRhamComplex.map g (contMDiff_of_val_comp I W hf hfg)) _).f q
          (relativeCoordinates (deRhamRestriction I' W') p q hpq x).2) :=
  -- `map` is typed between the mapping cocones, while `relativeCoordinates_map` is stated for the
  -- shifted cone map; the two hom types agree only after unfolding `mappingCocone`.
  relativeCoordinates_map _ _ _ _ _ p q hpq x

/-- The induced map sends `inl α` to `inl (f^* α)`. -/
@[simp]
theorem map_inl (hf : ContMDiff I I' ∞ f) (hfg : ∀ x, (g x : M') = f x) (k : ℕ)
    (α : SmoothForm I' M' ℝ k) :
    (map I W hf hfg).f k (inl I' W' k α) = inl I W k (SmoothForm.mpullback f hf α) := by
  apply (relativeCoordinates (deRhamRestriction I W) k (k + -1) rfl).injective
  rw [relativeCoordinates_map_f, relativeCoordinates_inl, relativeCoordinates_inl]
  rw [extendMap_deRhamComplexMap_f_symm_apply, map_zero]

/-- The induced map sends `inr β` to `inr (g^* β)`. The smoothness `hg` of `g` only serves to
state the pullback `g^* β`. -/
theorem map_inr (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g)
    (hfg : ∀ x, (g x : M') = f x) (k : ℕ) (β : SmoothForm I' W' ℝ k) :
    (map I W hf hfg).f (k + 1 : ℕ) (inr I' W' k β) =
      inr I W k (SmoothForm.mpullback g hg β) := by
  apply (relativeCoordinates (deRhamRestriction I W) (k + 1 : ℕ) k (by push_cast; lia)).injective
  rw [relativeCoordinates_map_f, relativeCoordinates_inr, relativeCoordinates_inr]
  rw [extendMap_deRhamComplexMap_f_symm_apply, map_zero]

end Map

/-- For empty `W`, the first projection of the cocone is an isomorphism onto the extended de Rham
complex of `M`: a relative cochain is a form on `M`. -/
theorem isIso_fst_of_isEmpty [IsEmpty W] : IsIso (fst (deRhamRestriction I W)) := by
  have hsub :
      ∀ q, Subsingleton (((deRhamComplex I W).extend ComplexShape.embeddingUpNat).X q) := by
    intro q
    by_cases hq : ∃ n : ℕ, (n : ℤ) = q
    · obtain ⟨n, hn⟩ := hq
      refine (deRhamComplexExtendXEquiv I W n q hn).toEquiv.subsingleton_congr.mpr
        ⟨fun a b ↦ ?_⟩
      ext x
      exact isEmptyElim x
    · exact ModuleCat.subsingleton_of_isZero <| isZero_extend_X _ _ _ fun n hn ↦ hq ⟨n, hn⟩
  have : ∀ p, IsIso ((fst (deRhamRestriction I W)).f p) := fun p ↦ by
    have := hsub (p + -1)
    rw [ConcreteCategory.isIso_iff_bijective]
    set e := relativeCoordinates (deRhamRestriction I W) p (p + -1) rfl
    have he : ∀ x, (fst (deRhamRestriction I W)).f p x = (e x).1 := fun x ↦ by
      simp [e, relativeCoordinates_apply]
    refine ⟨fun x y h ↦
        e.injective (Prod.ext (by rwa [← he, ← he]) (Subsingleton.elim _ _)),
      fun a ↦ ⟨e.symm (a, 0), by rw [he, LinearEquiv.apply_symm_apply]⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end relativeDeRhamComplex

namespace relativeDeRhamCohomology

open relativeDeRhamComplex

private theorem next_natCast (k : ℕ) :
    (ComplexShape.up ℤ).next (k : ℤ) = ((k + 1 : ℕ) : ℤ) := by
  simp

private theorem prev_natCast (k : ℕ) :
    (ComplexShape.up ℤ).prev ((k + 1 : ℕ) : ℤ) = (k : ℤ) := by
  simp

/-- The relative cocycles of degree `k + 1`: the pairs `(α, β)` of a `(k + 1)`-form on `M` and a
`k`-form on `W` with `dα = 0` and `α|_W = dβ`. -/
def cocycles (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k) :=
  LinearMap.ker (((mextDerivₗ I (F := ℝ) (k + 1)).comp (LinearMap.fst ℝ _ _)).prod
    ((SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal).comp
        (LinearMap.fst ℝ _ _) - (mextDerivₗ I (F := ℝ) k).comp (LinearMap.snd ℝ _ _)))

/-- A pair `(α, β)` is a relative cocycle exactly when `dα = 0` and `α|_W = dβ`. -/
@[simp]
theorem mem_cocycles_iff {k : ℕ} (x : SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k) :
    x ∈ cocycles I W k ↔ mextDerivₗ I (F := ℝ) (k + 1) x.1 = 0 ∧
      SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal x.1 =
        mextDerivₗ I (F := ℝ) k x.2 := by
  simp [cocycles, sub_eq_zero]

/-- The relative cohomology class of a relative cocycle `(α, β)` of degree `k + 1`. -/
def mk (k : ℕ) : cocycles I W k →ₗ[ℝ] relativeDeRhamCohomology I W (k + 1 : ℕ) :=
  (relativeDeRhamComplex I W).moduleCatHomologyClass (Z := cocycles I W k) (next_natCast (k + 1))
    ((coord I W k).symm.toLinearMap ∘ₗ (cocycles I W k).subtype)
    fun z ↦ by
      rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe]
      exact (d_coord_symm_eq_zero_iff I W k z.val).mpr ((mem_cocycles_iff I W z.val).mp z.property)

/-- The class of a relative cocycle `(α, β)` is the homology class of the cochain with
coordinates `(α, β)`. -/
theorem mk_apply (k : ℕ) (z : cocycles I W k) :
    relativeDeRhamCohomology.mk I W k z =
      (relativeDeRhamComplex I W).homologyπ (k + 1 : ℕ)
        ((relativeDeRhamComplex I W).moduleCatCyclesMk ((coord I W k).symm z) (k + 1 + 1 : ℕ)
          (by simp)
          ((d_coord_symm_eq_zero_iff I W k z.val).mpr
            ((mem_cocycles_iff I W z.val).mp z.property))) :=
  moduleCatHomologyClass_apply _ _ _ _ z

/-- The class of a relative cocycle vanishes exactly when its cochain is the differential of a
relative cochain of degree `k`. -/
theorem mk_eq_zero_iff (k : ℕ) (z : cocycles I W k) :
    relativeDeRhamCohomology.mk I W k z = 0 ↔ ∃ y : (relativeDeRhamComplex I W).X k,
      (relativeDeRhamComplex I W).d k (k + 1 : ℕ) y = (coord I W k).symm z :=
  moduleCatHomologyClass_eq_zero_iff _ _ _ _ (prev_natCast k) z

/-- Every relative cohomology class of positive degree is the class of a relative cocycle. -/
theorem mk_surjective (k : ℕ) : Function.Surjective (relativeDeRhamCohomology.mk I W k) :=
  (relativeDeRhamComplex I W).moduleCatHomologyClass_surjective _ _ _ fun x hx ↦ by
    refine ⟨⟨coord I W k x, (mem_cocycles_iff I W _).mpr ?_⟩, ?_⟩
    · rw [← d_coord_symm_eq_zero_iff, LinearEquiv.symm_apply_apply]
      exact hx
    · simp

/-- For a closed form `b` on `W`, the pair `(0, b)` is a relative cocycle. -/
theorem zero_prod_mem_cocycles (k : ℕ) (b : closedForms I W k) :
    ((0 : SmoothForm I M ℝ (k + 1)), (b : SmoothForm I W ℝ k)) ∈ cocycles I W k := by
  rw [mem_cocycles_iff]
  exact ⟨map_zero _, (map_zero _).trans
    ((mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp b.property).symm⟩

/-- The relative cocycle `(0, b)` of a closed form `b` on `W`. -/
private def inrCocycle (k : ℕ) : closedForms I W k →ₗ[ℝ] cocycles I W k where
  toFun b := ⟨(0, b), zero_prod_mem_cocycles I W k b⟩
  map_add' b c := by ext <;> simp
  map_smul' c b := by ext <;> simp

private theorem coe_inrCocycle (k : ℕ) (b : closedForms I W k) :
    (inrCocycle I W k b : SmoothForm I M ℝ (k + 1) × SmoothForm I W ℝ k) =
      (0, (b : SmoothForm I W ℝ k)) :=
  (rfl)

/-- The class map `b ↦ [(0, b)]` from closed forms on `W`. -/
private def classInr (k : ℕ) :
    closedForms I W k →ₗ[ℝ] relativeDeRhamCohomology I W (k + 1 : ℕ) :=
  relativeDeRhamCohomology.mk I W k ∘ₗ inrCocycle I W k

/-- The class `[(0, b)]` vanishes when `b` is exact. -/
private theorem classInr_eq_zero (k : ℕ) (b : closedForms I W k)
    (hb : b.val ∈ exactForms I W k) : classInr I W k b = 0 := by
  rw [classInr, LinearMap.comp_apply, mk_eq_zero_iff, coe_inrCocycle, coord_symm_apply, map_zero,
    zero_add]
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hb
    exact ⟨0, by simp [hb]⟩
  | succ k =>
    rw [exactForms_succ, LinearMap.mem_range] at hb
    obtain ⟨ε, hε⟩ := hb
    refine ⟨-inr I W k ε, ?_⟩
    rw [map_neg, d_inr, neg_neg, hε]

/-- The class map `b ↦ [(0, b)]` kills the kernel of the class map of closed forms on `W`. -/
private theorem ker_mk_le_ker_classInr (k : ℕ) :
    LinearMap.ker (deRhamCohomology.mk I (M := W) k) ≤ LinearMap.ker (classInr I W k) :=
  fun b hb ↦ by
    rw [LinearMap.mem_ker, deRhamCohomology.mk_eq_zero_iff] at hb
    exact LinearMap.mem_ker.mpr (classInr_eq_zero I W k b hb)

/-- The connecting map `δ : H^k(W) → H^(k+1)(M, W)`, `δ [b] = -[(0, b)]`. -/
def δ (k : ℕ) : deRhamCohomology I W k →ₗ[ℝ] relativeDeRhamCohomology I W (k + 1 : ℕ) :=
  -LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I W k)
    (M₂ := deRhamCohomology I W k) (M₃ := relativeDeRhamCohomology I W (k + 1 : ℕ))
    (f := deRhamCohomology.mk I k) (deRhamCohomology.mk_surjective I (M := W) k)
    ⟨classInr I W k, ker_mk_le_ker_classInr I W k⟩

/-- The connecting map sends the class of a closed form `b` on `W` to minus the class of the
relative cocycle `(0, b)`. -/
theorem δ_mk (k : ℕ) (b : closedForms I W k) :
    δ I W k (deRhamCohomology.mk I k b) =
      -relativeDeRhamCohomology.mk I W k ⟨(0, b), zero_prod_mem_cocycles I W k b⟩ := by
  rw [δ, LinearMap.neg_apply, LinearMap.equivOfSurjective_apply, classInr, LinearMap.comp_apply]
  exact congrArg (fun z ↦ -relativeDeRhamCohomology.mk I W k z)
    (Subtype.ext (coe_inrCocycle I W k b))

/-- If the closed form `b` on `W` is the restriction of a form `b'` on `M`, then `(db', 0)` is a
relative cocycle. -/
theorem mextDerivₗ_prod_zero_mem_cocycles (k : ℕ) (b : closedForms I W k)
    (b' : SmoothForm I M ℝ k)
    (hb' : SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal b' = b) :
    (mextDerivₗ I (F := ℝ) k b', (0 : SmoothForm I W ℝ k)) ∈ cocycles I W k := by
  rw [mem_cocycles_iff]
  refine ⟨LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I (M := M) (F := ℝ) k) b', ?_⟩
  dsimp only
  rw [map_zero, ← SmoothForm.mextDerivₗ_mpullback, hb']
  exact (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp b.property

/-- When the closed form `b` on `W` is the restriction of a form `b'` on `M`, the connecting map
sends its class to the class of the relative cocycle `(db', 0)`. -/
theorem δ_mk_of_mpullback_eq (k : ℕ) (b : closedForms I W k) (b' : SmoothForm I M ℝ k)
    (hb' : SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal b' = b) :
    δ I W k (deRhamCohomology.mk I k b) =
      relativeDeRhamCohomology.mk I W k ⟨(mextDerivₗ I (F := ℝ) k b', 0),
        mextDerivₗ_prod_zero_mem_cocycles I W k b b' hb'⟩ := by
  rw [δ_mk, neg_eq_iff_add_eq_zero, ← map_add, mk_eq_zero_iff]
  refine ⟨inl I W k b', ?_⟩
  rw [d_inl, hb']
  apply (coord I W k).injective
  rw [map_add, coord_inl, coord_inr, LinearEquiv.apply_symm_apply]
  simp

/-- The relative cocycles of degree `0`: the smooth functions on `M` with zero differential and
zero restriction to `W`. -/
def cocyclesZero : Submodule ℝ (SmoothForm I M ℝ 0) :=
  closedForms I M 0 ⊓
    LinearMap.ker (SmoothForm.mpullback (k := 0) (F := ℝ) (Subtype.val : W → M)
      contMDiff_subtypeVal)

/-- A smooth function on `M` is a relative cocycle of degree `0` exactly when its differential
vanishes and it vanishes on `W`. -/
@[simp]
theorem mem_cocyclesZero_iff (α : SmoothForm I M ℝ 0) :
    α ∈ cocyclesZero I W ↔ mextDerivₗ I (F := ℝ) 0 α = 0 ∧
      SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal α = 0 := by
  rw [cocyclesZero, Submodule.mem_inf, mem_closedForms_iff_mextDerivₗ_eq_zero, LinearMap.mem_ker]

/-- The cochain `inl α` of a relative cocycle `α` of degree `0` is a cycle. -/
theorem d_inl_eq_zero_of_mem_cocyclesZero {α : SmoothForm I M ℝ 0}
    (hα : α ∈ cocyclesZero I W) :
    (relativeDeRhamComplex I W).d (0 : ℕ) (0 + 1 : ℕ) (inl I W 0 α) = 0 := by
  obtain ⟨h1, h2⟩ := (mem_cocyclesZero_iff I W α).mp hα
  rw [d_inl I W 0, h1, h2, map_zero, map_zero, add_zero]

/-- The class map from the relative cocycles of degree `0` to the relative cohomology. -/
def classZero : cocyclesZero I W →ₗ[ℝ] relativeDeRhamCohomology I W (0 : ℕ) :=
  (relativeDeRhamComplex I W).moduleCatHomologyClass (Z := cocyclesZero I W) (next_natCast 0)
    (inl I W 0 ∘ₗ (cocyclesZero I W).subtype) fun α ↦
      d_inl_eq_zero_of_mem_cocyclesZero I W α.property

/-- The class of a relative cocycle `α` of degree `0` is the homology class of the cochain
`inl α`. -/
theorem classZero_apply (α : cocyclesZero I W) :
    classZero I W α =
      (relativeDeRhamComplex I W).homologyπ (0 : ℕ)
        ((relativeDeRhamComplex I W).moduleCatCyclesMk (inl I W 0 α) (0 + 1 : ℕ) (by simp)
          (d_inl_eq_zero_of_mem_cocyclesZero I W α.property)) :=
  moduleCatHomologyClass_apply _ _ _ _ α

/-- In degree `0` the relative de Rham cohomology is the space of smooth functions on `M` with zero
differential and zero restriction to `W`. -/
theorem classZero_bijective : Function.Bijective (classZero I W) := by
  have : Subsingleton ((relativeDeRhamComplex I W).X (((0 : ℕ) : ℤ) + -1)) := by
    have := subsingleton_deRhamComplexExtend_X I (M := M) (p := ((0 : ℕ) : ℤ) + -1) (by lia)
    have := subsingleton_deRhamComplexExtend_X I (M := W) (p := ((0 : ℕ) : ℤ) + -1 + -1)
      (by lia)
    exact (CochainComplex.mappingCocone.relativeCoordinates (deRhamRestriction I W) _ _
      rfl).toEquiv.subsingleton
  refine ⟨(injective_iff_map_eq_zero _).mpr fun α hα ↦ ?_, fun c ↦ ?_⟩
  · rw [classZero, moduleCatHomologyClass_eq_zero_iff _ _ _ _ (p := ((0 : ℕ) : ℤ) + -1)
      (by simp)] at hα
    obtain ⟨y, hy⟩ := hα
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact Subtype.ext ((inl_zero_bijective I W).injective (hy.symm.trans (map_zero _).symm))
  · refine (relativeDeRhamComplex I W).moduleCatHomologyClass_surjective _ _ _ (fun x hx ↦ ?_) c
    obtain ⟨α, rfl⟩ := (inl_zero_bijective I W).surjective x
    have h := congrArg (coord I W 0) hx
    rw [d_inl I W 0, map_add, coord_inl, coord_inr, map_zero] at h
    simp only [Prod.mk_add_mk, zero_add, add_zero, Prod.mk_eq_zero] at h
    exact ⟨⟨α, (mem_cocyclesZero_iff I W α).mpr h⟩, rfl⟩

end relativeDeRhamCohomology

end TauCeti
