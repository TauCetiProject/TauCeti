/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Relative
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Cohomology

/-!
# The relative Dolbeault complex of an open pair

Let `M` be a complex manifold, `U` an open subset and `p` a holomorphic degree. The relative
Dolbeault complex of the pair `(M, U)` is the mapping cocone `Cone(A^(p,•)(M) ⟶ A^(p,•)(U))[-1]`
of the restriction of smooth forms of type `(p,•)` from `M` to `U`
(`TauCeti.relativeDolbeaultComplex`). The Dolbeault complexes are indexed by `ℕ`; they are
extended by zero in negative degrees along `ComplexShape.embeddingUpNat`, so that Mathlib's
`CochainComplex.mappingCocone` applies. For a closed subset `S` of `M` and `U = M ∖ S` its
cohomology is the relative Dolbeault cohomology of `(M, M ∖ S)`, which by the relative Dolbeault
theorem computes the cohomology `H_S^q(M, Ω^p)` of holomorphic `p`-forms with supports in `S`; that
comparison is not proved here.

The terms are, through the relative coordinates `CochainComplex.mappingCocone.relativeCoordinates`
which negate the second component of Mathlib's shifted cone,

`A^(p,q+1)(M) × A^(p,q)(U)` in degree `q + 1`, and `A^(p,0)(M)` in degree `0`,

and the differential is `(α, β) ↦ (∂bar α, α|_U - ∂bar β)` (`d_XEquiv_symm`, `d_XEquivZero_symm`).
Thus a pair `(α, β)` is a relative cocycle exactly when `∂bar α = 0` and `α|_U = ∂bar β`, and it is
a relative coboundary exactly when `(α, β) = (∂bar γ, γ|_U - ∂bar η)`. In degree zero the relative
cocycles are the `∂bar`-closed, that is holomorphic, `p`-forms on `M` vanishing on `U`.

In positive degree the relative cocycles form the submodule
`TauCeti.relativeDolbeaultComplex.cocycles` of the coordinates, with the class map
`TauCeti.relativeDolbeaultComplex.mk` onto the cohomology of the relative complex. The connecting
map `H^(p,q)(U) → H^(p,q+1)(M, U)` is `δ[b] = -[(0, b)]`; when `b` is the restriction of a form
`b'` on `M`, it is also `[(∂bar b', 0)]`.

A holomorphic map of pairs, a commutative square of holomorphic maps `f : M₁ → M₂` and
`g : U₁ → U₂` over the inclusions, induces a cochain map of relative complexes acting by pullback
on both coordinates (`TauCeti.relativeDolbeaultComplex.map`); it is compatible with identities and
composition. Restricting to an open subset of `M`, and enlarging `U`, are maps of pairs.

## Main declarations

* `TauCeti.relativeDolbeaultComplex.restriction`: the restriction of the extended Dolbeault
  complexes from `M` to `U`.
* `TauCeti.relativeDolbeaultComplex`: the relative Dolbeault complex of `(M, U)`, the mapping
  cocone of the restriction.
* `TauCeti.relativeDolbeaultComplex.XEquiv`, `TauCeti.relativeDolbeaultComplex.XEquivZero`: its
  terms in relative coordinates.
* `TauCeti.relativeDolbeaultComplex.d_XEquiv_symm`,
  `TauCeti.relativeDolbeaultComplex.d_XEquivZero_symm`: the relative differential.
* `TauCeti.relativeDolbeaultComplex.d_XEquiv_symm_eq_zero_iff`,
  `TauCeti.relativeDolbeaultComplex.XEquiv_symm_mem_range_d_iff`: relative cocycles and
  coboundaries.
* `TauCeti.relativeDolbeaultComplex.cocycles`, `TauCeti.relativeDolbeaultComplex.mk`: relative
  cocycles of positive degree and their classes, with `mk_surjective` and `mk_eq_zero_iff`.
* `TauCeti.relativeDolbeaultComplex.δ`: the connecting map, with `δ_mk` and
  `δ_mk_of_restrictType_eq`.
* `TauCeti.relativeDolbeaultComplex.map`: the cochain map induced by a holomorphic map of pairs,
  with `map_f_XEquiv_symm`, `map_id` and `map_comp`.

## References

* N. Honda, T. Izawa and T. Suwa, *Sato hyperfunctions via relative Dolbeault cohomology*,
  J. Math. Soc. Japan 75 (2023).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Chapter I, §6, for the
  analogous relative de Rham complex.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace HomologicalComplex
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure CochainComplex

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace dolbeaultComplex

/-! ### The Dolbeault complex extended by zero to `ℤ` -/

variable (E M F) in
/-- The degree-`n` term of the Dolbeault complex extended by zero, for `n = q`, is the module of
type-`(p,q)` forms. -/
def extendXEquiv (p q : ℕ) (n : ℤ) (hn : (q : ℤ) = n) :
    ((dolbeaultComplex E M F p).extend ComplexShape.embeddingUpNat).X n ≃ₗ[ℂ]
      (ofComplexManifold E M).typeForms (F := F) p q :=
  ((extendXIso _ _ (i := q) (by simp [← hn])) ≪≫ dolbeaultComplexXIso p q).toLinearEquiv

/-- The inverse of `extendXEquiv` is the inverse of the canonical identifications. -/
theorem extendXEquiv_symm_apply (p q : ℕ) (n : ℤ) (hn : (q : ℤ) = n)
    (α : (ofComplexManifold E M).typeForms (F := F) p q) :
    (extendXEquiv E M F p q n hn).symm α =
      (extendXIso (dolbeaultComplex E M F p) ComplexShape.embeddingUpNat (i := q)
        (by simp [← hn])).inv ((dolbeaultComplexXIso p q).inv α) :=
  (rfl)

variable (E M F) in
/-- The Dolbeault complex extended by zero vanishes in negative degrees. -/
theorem isZero_extend_X (p : ℕ) (n : ℤ) (hn : n < 0) :
    Limits.IsZero (((dolbeaultComplex E M F p).extend ComplexShape.embeddingUpNat).X n) :=
  HomologicalComplex.isZero_extend_X _ _ _ fun i ↦ by
    rw [ComplexShape.embeddingUpNat_f]
    omega

/-- In the coordinates `extendXEquiv`, the differential of the extended Dolbeault complex is
`∂bar`. -/
theorem extend_d_extendXEquiv_symm (p q : ℕ) (n m : ℤ) (hn : (q : ℤ) = n) (hm : n + 1 = m)
    (α : (ofComplexManifold E M).typeForms (F := F) p q) :
    ((dolbeaultComplex E M F p).extend ComplexShape.embeddingUpNat).d n m
        ((extendXEquiv E M F p q n hn).symm α) =
      (extendXEquiv E M F p (q + 1) m (by push_cast; omega)).symm
        ((ofComplexManifold E M).delBarType p q α) := by
  subst hn hm
  rw [extend_d_eq _ _ (i := q) (j := q + 1) (by simp) (by simp)]
  simp [extendXEquiv_symm_apply, dolbeaultComplex_d_apply]

/-- In the coordinates `extendXEquiv`, the extension of the cochain map of a holomorphic map is
pullback of type forms. -/
theorem extendMap_map_f_extendXEquiv_symm {E₁ E₂ : Type u} [NormedAddCommGroup E₁]
    [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] {M₁ M₂ : Type v}
    [TopologicalSpace M₁] [ChartedSpace E₁ M₁] [IsManifold 𝓘(ℂ, E₁) ∞ M₁]
    [TopologicalSpace M₂] [ChartedSpace E₂ M₂] [IsManifold 𝓘(ℂ, E₂) ∞ M₂]
    {f : M₁ → M₂} (hf : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f)
    (p q : ℕ) (n : ℤ) (hn : (q : ℤ) = n) (α : (ofComplexManifold E₂ M₂).typeForms (F := F) p q) :
    (extendMap (map (F := F) hf hJ p) ComplexShape.embeddingUpNat).f n
        ((extendXEquiv E₂ M₂ F p q n hn).symm α) =
      (extendXEquiv E₁ M₁ F p q n hn).symm (mpullbackType hf hJ p q α) := by
  subst hn
  rw [extendMap_f _ _ (i := q) (by simp)]
  simp only [extendXEquiv_symm_apply, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rw [map_f_inv_apply]

end dolbeaultComplex

namespace relativeDolbeaultComplex

variable (E M F)

/-- The restriction of forms of type `(p,•)` from `M` to an open subset `U`, as a map of the
Dolbeault complexes extended by zero to `ℤ`. -/
def restriction (U : Opens M) (p : ℕ) :
    (dolbeaultComplex E M F p).extend ComplexShape.embeddingUpNat ⟶
      (dolbeaultComplex E U F p).extend ComplexShape.embeddingUpNat :=
  extendMap (dolbeaultComplex.map contMDiff_subtype_val (isPseudoholomorphic_subtype_val U) p) _

end relativeDolbeaultComplex

variable (E M F) in
/-- The relative Dolbeault complex of an open pair `(M, U)` in holomorphic degree `p`: the
mapping cocone of the restriction of forms of type `(p,•)` from `M` to `U`, both Dolbeault
complexes being extended by zero to negative degrees. -/
abbrev relativeDolbeaultComplex (U : Opens M) (p : ℕ) : CochainComplex (ModuleCat ℂ) ℤ :=
  mappingCocone (relativeDolbeaultComplex.restriction E M F U p)

namespace relativeDolbeaultComplex

variable (U : Opens M) (p : ℕ)

/-- Restriction of forms of type `(p,q)` from `M` to the open subset `U`. -/
abbrev restrictType (q : ℕ) :
    (ofComplexManifold E M).typeForms (F := F) p q →ₗ[ℂ]
      (ofComplexManifold E U).typeForms (F := F) p q :=
  mpullbackType contMDiff_subtype_val (isPseudoholomorphic_subtype_val U) p q

/-- In the coordinates `dolbeaultComplex.extendXEquiv`, the restriction cochain map is restriction
of type forms to `U`. -/
theorem restriction_f_extendXEquiv_symm (q : ℕ) (n : ℤ) (hn : (q : ℤ) = n)
    (α : (ofComplexManifold E M).typeForms (F := F) p q) :
    (restriction E M F U p).f n ((dolbeaultComplex.extendXEquiv E M F p q n hn).symm α) =
      (dolbeaultComplex.extendXEquiv E U F p q n hn).symm (restrictType U p q α) :=
  dolbeaultComplex.extendMap_map_f_extendXEquiv_symm _ _ p q n hn α

/-- The coordinates of the relative Dolbeault complex in degree `n = q + 1`: a pair of a form of
type `(p,q+1)` on `M` and a form of type `(p,q)` on `U`. The second coordinate is the negative of
the second projection of the shifted mapping cone, so that the differential is
`(α, β) ↦ (∂bar α, α|_U - ∂bar β)`. -/
def XEquiv (n : ℤ) (q : ℕ) (hq : ((q + 1 : ℕ) : ℤ) = n) :
    (relativeDolbeaultComplex E M F U p).X n ≃ₗ[ℂ]
      (ofComplexManifold E M).typeForms (F := F) p (q + 1) ×
        (ofComplexManifold E U).typeForms (F := F) p q :=
  (mappingCocone.relativeCoordinates (restriction E M F U p) n q (by omega)).trans
    ((dolbeaultComplex.extendXEquiv E M F p (q + 1) n hq).prodCongr
      (dolbeaultComplex.extendXEquiv E U F p q q rfl))

/-- The coordinate of the relative Dolbeault complex in degree `0`: a form of type `(p,0)` on
`M`. -/
def XEquivZero :
    (relativeDolbeaultComplex E M F U p).X 0 ≃ₗ[ℂ] (ofComplexManifold E M).typeForms (F := F) p 0 :=
  letI : Unique (((dolbeaultComplex E U F p).extend ComplexShape.embeddingUpNat).X (-1)) :=
    @uniqueOfSubsingleton _ (ModuleCat.isZero_iff_subsingleton.mp
      (dolbeaultComplex.isZero_extend_X E U F p (-1) (by norm_num))) 0
  (mappingCocone.relativeCoordinates (restriction E M F U p) 0 (-1) rfl).trans
    (((dolbeaultComplex.extendXEquiv E M F p 0 0 rfl).prodCongr (LinearEquiv.refl ℂ _)).trans
      (LinearEquiv.prodUnique (R := ℂ)))

/-- The relative Dolbeault complex vanishes in negative degrees. -/
theorem isZero_X_of_neg {n : ℤ} (hn : n < 0) :
    Limits.IsZero ((relativeDolbeaultComplex E M F U p).X n) := by
  have := ModuleCat.isZero_iff_subsingleton.mp (dolbeaultComplex.isZero_extend_X E M F p n hn)
  have := ModuleCat.isZero_iff_subsingleton.mp
    (dolbeaultComplex.isZero_extend_X E U F p (n + -1) (by omega))
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (mappingCocone.relativeCoordinates (restriction E M F U p) n (n + -1)
    rfl).toEquiv.subsingleton

private lemma XEquiv_symm_eq (n : ℤ) (q : ℕ) (hq : ((q + 1 : ℕ) : ℤ) = n)
    (x : (ofComplexManifold E M).typeForms (F := F) p (q + 1) ×
      (ofComplexManifold E U).typeForms (F := F) p q) :
    (XEquiv U p n q hq).symm x = (mappingCocone.relativeCoordinates (restriction E M F U p) n q
      (by omega)).symm ((dolbeaultComplex.extendXEquiv E M F p (q + 1) n hq).symm x.1,
        (dolbeaultComplex.extendXEquiv E U F p q q rfl).symm x.2) :=
  rfl

private lemma XEquivZero_symm_eq (α : (ofComplexManifold E M).typeForms (F := F) p 0) :
    (XEquivZero U p).symm α =
      (mappingCocone.relativeCoordinates (restriction E M F U p) 0 (-1) rfl).symm
        ((dolbeaultComplex.extendXEquiv E M F p 0 0 rfl).symm α, 0) := by
  apply (XEquivZero U p).injective
  rw [LinearEquiv.apply_symm_apply]
  unfold XEquivZero
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  simp

/-! ### The relative differential -/

/-- In coordinates, the differential of the relative Dolbeault complex in positive degree is
`(α, β) ↦ (∂bar α, α|_U - ∂bar β)`. -/
@[simp]
theorem d_XEquiv_symm (n n' : ℤ) (q : ℕ) (hq : ((q + 1 : ℕ) : ℤ) = n) (hn' : n + 1 = n')
    (α : (ofComplexManifold E M).typeForms (F := F) p (q + 1))
    (β : (ofComplexManifold E U).typeForms (F := F) p q) :
    (relativeDolbeaultComplex E M F U p).d n n' ((XEquiv U p n q hq).symm (α, β)) =
      (XEquiv U p n' (q + 1) (by push_cast; omega)).symm
        ((ofComplexManifold E M).delBarType p (q + 1) α,
          restrictType U p (q + 1) α - (ofComplexManifold E U).delBarType p q β) := by
  subst hq hn'
  rw [XEquiv_symm_eq, XEquiv_symm_eq]
  refine (mappingCocone.d_relativeCoordinates_symm _ _ q (by omega) _).trans
    (congrArg _ (Prod.ext (dolbeaultComplex.extend_d_extendXEquiv_symm _ _ _ _ _ rfl _) ?_))
  dsimp only
  rw [restriction_f_extendXEquiv_symm,
    dolbeaultComplex.extend_d_extendXEquiv_symm p q q _ rfl (by push_cast; rfl)]
  exact ((dolbeaultComplex.extendXEquiv E U F p (q + 1) _ _).symm.toLinearMap.map_sub _ _).symm

/-- In coordinates, the differential of the relative Dolbeault complex in degree `0` is
`α ↦ (∂bar α, α|_U)`. -/
@[simp]
theorem d_XEquivZero_symm (α : (ofComplexManifold E M).typeForms (F := F) p 0) :
    (relativeDolbeaultComplex E M F U p).d 0 1 ((XEquivZero U p).symm α) =
      (XEquiv U p 1 0 rfl).symm
        ((ofComplexManifold E M).delBarType p 0 α, restrictType U p 0 α) := by
  rw [XEquivZero_symm_eq, XEquiv_symm_eq]
  refine (mappingCocone.d_relativeCoordinates_symm _ 0 (-1) rfl _).trans
    (congrArg _ (Prod.ext (dolbeaultComplex.extend_d_extendXEquiv_symm _ _ _ _ _ rfl _) ?_))
  dsimp only
  rw [map_zero, sub_zero]
  exact restriction_f_extendXEquiv_symm U p 0 0 rfl α

/-! ### Relative cocycles and coboundaries -/

/-- A pair `(α, β)` is a relative cocycle exactly when `∂bar α = 0` and `α|_U = ∂bar β`. -/
theorem d_XEquiv_symm_eq_zero_iff (n n' : ℤ) (q : ℕ) (hq : ((q + 1 : ℕ) : ℤ) = n)
    (hn' : n + 1 = n') (α : (ofComplexManifold E M).typeForms (F := F) p (q + 1))
    (β : (ofComplexManifold E U).typeForms (F := F) p q) :
    (relativeDolbeaultComplex E M F U p).d n n' ((XEquiv U p n q hq).symm (α, β)) = 0 ↔
      (ofComplexManifold E M).delBarType p (q + 1) α = 0 ∧
        restrictType U p (q + 1) α = (ofComplexManifold E U).delBarType p q β := by
  rw [d_XEquiv_symm U p n n' q hq hn', LinearEquiv.map_eq_zero_iff, Prod.mk_eq_zero, sub_eq_zero]

/-- A form of type `(p,0)` is a relative cocycle exactly when it is holomorphic, `∂bar α = 0`,
and vanishes on `U`. -/
theorem d_XEquivZero_symm_eq_zero_iff (α : (ofComplexManifold E M).typeForms (F := F) p 0) :
    (relativeDolbeaultComplex E M F U p).d 0 1 ((XEquivZero U p).symm α) = 0 ↔
      (ofComplexManifold E M).delBarType p 0 α = 0 ∧ restrictType U p 0 α = 0 := by
  rw [d_XEquivZero_symm, LinearEquiv.map_eq_zero_iff, Prod.mk_eq_zero]

/-- A pair `(α, β)` in degree `q + 2` is a relative coboundary exactly when it is
`(∂bar γ, γ|_U - ∂bar η)` for a form `γ` on `M` and a form `η` on `U`. -/
theorem XEquiv_symm_mem_range_d_iff (n' n : ℤ) (q : ℕ) (hn' : ((q + 1 : ℕ) : ℤ) = n')
    (hn : ((q + 1 + 1 : ℕ) : ℤ) = n)
    (α : (ofComplexManifold E M).typeForms (F := F) p (q + 1 + 1))
    (β : (ofComplexManifold E U).typeForms (F := F) p (q + 1)) :
    (XEquiv U p n (q + 1) hn).symm (α, β) ∈
        LinearMap.range ((relativeDolbeaultComplex E M F U p).d n' n).hom ↔
      ∃ γ : (ofComplexManifold E M).typeForms (F := F) p (q + 1),
        ∃ η : (ofComplexManifold E U).typeForms (F := F) p q,
          (ofComplexManifold E M).delBarType p (q + 1) γ = α ∧
            restrictType U p (q + 1) γ - (ofComplexManifold E U).delBarType p q η = β := by
  have hn'n : n' + 1 = n := by omega
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨⟨γ, η⟩, rfl⟩ := (XEquiv U p n' q hn').symm.surjective y
    have h := (d_XEquiv_symm U p n' n q hn' hn'n γ η).symm.trans hy
    rw [(XEquiv U p n (q + 1) _).symm.injective.eq_iff, Prod.mk.injEq] at h
    exact ⟨γ, η, h⟩
  · rintro ⟨γ, η, hγ, hη⟩
    exact ⟨(XEquiv U p n' q hn').symm (γ, η),
      (d_XEquiv_symm U p n' n q hn' hn'n γ η).trans (by rw [hγ, hη])⟩

/-- A pair `(α, β)` in degree `1` is a relative coboundary exactly when it is `(∂bar γ, γ|_U)` for
a form `γ` of type `(p,0)` on `M`. -/
theorem XEquiv_symm_mem_range_d_zero_iff (α : (ofComplexManifold E M).typeForms (F := F) p 1)
    (β : (ofComplexManifold E U).typeForms (F := F) p 0) :
    (XEquiv U p 1 0 rfl).symm (α, β) ∈
        LinearMap.range ((relativeDolbeaultComplex E M F U p).d 0 1).hom ↔
      ∃ γ : (ofComplexManifold E M).typeForms (F := F) p 0,
        (ofComplexManifold E M).delBarType p 0 γ = α ∧ restrictType U p 0 γ = β := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨γ, rfl⟩ := (XEquivZero U p).symm.surjective y
    have h := (d_XEquivZero_symm U p γ).symm.trans hy
    rw [(XEquiv U p 1 0 rfl).symm.injective.eq_iff, Prod.mk.injEq] at h
    exact ⟨γ, h⟩
  · rintro ⟨γ, hγ, hβ⟩
    exact ⟨(XEquivZero U p).symm γ, (d_XEquivZero_symm U p γ).trans (by rw [hγ, hβ])⟩

/-! ### Relative cohomology classes and the connecting map -/

section Classes

/-- The relative cocycles of degree `q + 1` in coordinates: pairs `(α, β)` of a form `α` of type
`(p,q+1)` on `M` and a form `β` of type `(p,q)` on `U` with `∂bar α = 0` and `α|_U = ∂bar β`. -/
def cocycles (q : ℕ) :
    Submodule ℂ ((ofComplexManifold E M).typeForms (F := F) p (q + 1) ×
      (ofComplexManifold E U).typeForms (F := F) p q) :=
  LinearMap.ker ((((ofComplexManifold E M).delBarType p (q + 1)).comp (LinearMap.fst ℂ _ _)).prod
    ((restrictType U p (q + 1)).comp (LinearMap.fst ℂ _ _) -
      ((ofComplexManifold E U).delBarType p q).comp (LinearMap.snd ℂ _ _)))

/-- Membership in the relative cocycles: `∂bar α = 0` and `α|_U = ∂bar β`. -/
@[simp]
theorem mem_cocycles {q : ℕ} (x : (ofComplexManifold E M).typeForms (F := F) p (q + 1) ×
      (ofComplexManifold E U).typeForms (F := F) p q) :
    x ∈ cocycles U p q ↔ (ofComplexManifold E M).delBarType p (q + 1) x.1 = 0 ∧
      restrictType U p (q + 1) x.1 = (ofComplexManifold E U).delBarType p q x.2 := by
  simp [cocycles, sub_eq_zero]

/-- The relative Dolbeault cohomology class of a relative cocycle of degree `q + 1`. -/
def mk (q : ℕ) :
    cocycles (E := E) (F := F) U p q →ₗ[ℂ]
      (relativeDolbeaultComplex E M F U p).homology ((q + 1 : ℕ) : ℤ) :=
  (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass (Z := cocycles U p q)
    (CochainComplex.next ℤ _)
    ((XEquiv U p _ q rfl).symm.toLinearMap ∘ₗ (cocycles U p q).subtype) fun x ↦ by
      obtain ⟨⟨α, β⟩, hx⟩ := x
      exact (d_XEquiv_symm_eq_zero_iff U p _ _ q rfl rfl α β).mpr ((mem_cocycles U p _).mp hx)

/-- The relative class map is the homology class map of the relative cocycles, embedded into the
relative complex through the coordinates `XEquiv`. -/
theorem mk_eq_moduleCatHomologyClass (q : ℕ) :
    relativeDolbeaultComplex.mk (E := E) (F := F) U p q =
      (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass (Z := cocycles U p q)
        (CochainComplex.next ℤ _)
        ((XEquiv U p _ q rfl).symm.toLinearMap ∘ₗ (cocycles U p q).subtype) fun x ↦ by
          obtain ⟨⟨α, β⟩, hx⟩ := x
          exact (d_XEquiv_symm_eq_zero_iff U p _ _ q rfl rfl α β).mpr
            ((mem_cocycles U p _).mp hx) :=
  (rfl)

/-- Every relative Dolbeault cohomology class of positive degree is represented by a relative
cocycle. -/
theorem mk_surjective (q : ℕ) :
    Function.Surjective (relativeDolbeaultComplex.mk (E := E) (F := F) U p q) := by
  rw [relativeDolbeaultComplex.mk]
  refine (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass_surjective _ _ _ fun y hy ↦ ?_
  obtain ⟨⟨α, β⟩, rfl⟩ := (XEquiv U p _ q rfl).symm.surjective y
  exact ⟨⟨(α, β), (mem_cocycles U p _).mpr
    ((d_XEquiv_symm_eq_zero_iff U p _ _ q rfl rfl α β).mp hy)⟩, rfl⟩

/-- The class of a relative cocycle vanishes exactly when the cocycle is a coboundary. -/
theorem mk_eq_zero_iff (q : ℕ) (x : cocycles (E := E) (F := F) U p q) :
    relativeDolbeaultComplex.mk U p q x = 0 ↔ ∃ y : (relativeDolbeaultComplex E M F U p).X q,
      (relativeDolbeaultComplex E M F U p).d q ((q + 1 : ℕ) : ℤ) y =
        (XEquiv U p _ q rfl).symm x := by
  rw [relativeDolbeaultComplex.mk]
  exact (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass_eq_zero_iff _ _ _ (by simp) x

/-- The pair `(0, b)` for a `∂bar`-closed form `b` on `U`, as a relative cocycle. -/
private def inrClosed (q : ℕ) :
    Dolbeault.closedForms E U F p q →ₗ[ℂ] cocycles (E := E) (F := F) U p q :=
  ((LinearMap.inr ℂ ((ofComplexManifold E M).typeForms (F := F) p (q + 1))
    ((ofComplexManifold E U).typeForms (F := F) p q)).comp
      (Dolbeault.closedForms E U F p q).subtype).codRestrict _ fun b ↦ by
    rw [mem_cocycles]
    refine ⟨by simp, ?_⟩
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, Submodule.subtype_apply, map_zero]
    exact ((Dolbeault.mem_closedForms_iff_delBarType_eq_zero p q b.1).mp b.2).symm

private lemma mk_inrClosed_eq_zero (q : ℕ) (b : Dolbeault.closedForms E U F p q)
    (hb : b.1 ∈ Dolbeault.exactForms E U F p q) :
    relativeDolbeaultComplex.mk (E := E) (F := F) (M := M) U p q (inrClosed U p q b) = 0 := by
  cases q with
  | zero =>
    rw [Dolbeault.exactForms_zero, Submodule.mem_bot] at hb
    rw [show b = 0 from Subtype.ext hb, map_zero, map_zero]
  | succ q =>
    obtain ⟨η, hη⟩ := (Dolbeault.mem_exactForms_succ p q b.1).mp hb
    rw [mk_eq_zero_iff]
    refine ⟨(XEquiv U p _ q rfl).symm (0, -η),
      (d_XEquiv_symm U p _ _ q rfl (by omega) _ _).trans ?_⟩
    congr 1
    refine Prod.ext (map_zero _) ?_
    exact Subtype.ext (by simp [inrClosed, hη])

/-- The negative of the class of `(0, b)`, for `∂bar`-closed forms `b` on `U`. -/
private def δClosed (q : ℕ) :
    Dolbeault.closedForms E U F p q →ₗ[ℂ]
      (relativeDolbeaultComplex E M F U p).homology ((q + 1 : ℕ) : ℤ) :=
  -(relativeDolbeaultComplex.mk U p q ∘ₗ inrClosed U p q)

private lemma ker_le_ker_δClosed (q : ℕ) :
    LinearMap.ker (dolbeaultCohomology.mk (E := E) (M := U) (F := F) p q) ≤
      LinearMap.ker (δClosed (M := M) U p q) := by
  intro b hb
  rw [LinearMap.mem_ker, dolbeaultCohomology.mk_eq_zero_iff] at hb
  rw [LinearMap.mem_ker, δClosed, LinearMap.neg_apply, LinearMap.comp_apply,
    mk_inrClosed_eq_zero U p q b hb, neg_zero]

/-- The connecting map `H^(p,q)(U) → H^(p,q+1)(M, U)` of the relative Dolbeault complex, with the
sign convention `δ[b] = -[(0, b)]` for a `∂bar`-closed form `b` on `U`
(`TauCeti.relativeDolbeaultComplex.δ_mk`). -/
def δ (q : ℕ) :
    dolbeaultCohomology E U F p q →ₗ[ℂ]
      (relativeDolbeaultComplex E M F U p).homology ((q + 1 : ℕ) : ℤ) :=
  LinearMap.liftOfSurjective (R := ℂ) (M := Dolbeault.closedForms E U F p q)
    (M₂ := dolbeaultCohomology E U F p q)
    (M₃ := (relativeDolbeaultComplex E M F U p).homology ((q + 1 : ℕ) : ℤ))
    (f := dolbeaultCohomology.mk p q) (dolbeaultCohomology.mk_surjective p q)
    ⟨δClosed U p q, ker_le_ker_δClosed U p q⟩

/-- The connecting map sends the class of a `∂bar`-closed form `b` on `U` to `-[(0, b)]`. -/
theorem δ_mk (q : ℕ) (b : Dolbeault.closedForms E U F p q) :
    δ (M := M) U p q (dolbeaultCohomology.mk p q b) =
      -relativeDolbeaultComplex.mk U p q ⟨(0, b.1), (mem_cocycles U p _).mpr ⟨map_zero _,
        (map_zero _).trans ((Dolbeault.mem_closedForms_iff_delBarType_eq_zero p q b.1).mp
          b.2).symm⟩⟩ := by
  rw [δ, LinearMap.equivOfSurjective_apply]
  rfl

/-- If a `∂bar`-closed form `b` on `U` is the restriction of a form `b'` on `M`, the connecting map
sends its class to the class of `(∂bar b', 0)`. -/
theorem δ_mk_of_restrictType_eq (q : ℕ) (b : Dolbeault.closedForms E U F p q)
    (b' : (ofComplexManifold E M).typeForms (F := F) p q) (hb' : restrictType U p q b' = b.1) :
    δ (M := M) U p q (dolbeaultCohomology.mk p q b) =
      relativeDolbeaultComplex.mk U p q ⟨((ofComplexManifold E M).delBarType p q b', 0),
        (mem_cocycles U p _).mpr
        ⟨Subtype.ext (by
            dsimp only
            rw [coe_delBarType, coe_delBarType, delBar_delBar_ofComplexManifold,
              Submodule.coe_zero]), by
          dsimp only
          rw [map_zero, ← delBarType_mpullbackType, hb',
            (Dolbeault.mem_closedForms_iff_delBarType_eq_zero p q b.1).mp b.2]⟩⟩ := by
  rw [δ_mk, neg_eq_iff_add_eq_zero, ← map_add, mk_eq_zero_iff]
  cases q with
  | zero =>
    refine ⟨(XEquivZero U p).symm b', (d_XEquivZero_symm U p b').trans ?_⟩
    congr 1
    exact Prod.ext (by simp) (by simp [hb'])
  | succ q =>
    refine ⟨(XEquiv U p _ q rfl).symm (b', 0),
      (d_XEquiv_symm U p _ _ q rfl (by omega) b' 0).trans ?_⟩
    congr 1
    exact Prod.ext (by simp) (by simp [hb'])

end Classes

/-! ### Maps of pairs -/

section Map

variable {E₁ E₂ E₃ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
  {M₁ M₂ M₃ : Type v} [TopologicalSpace M₁] [ChartedSpace E₁ M₁] [IsManifold 𝓘(ℂ, E₁) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace E₂ M₂] [IsManifold 𝓘(ℂ, E₂) ∞ M₂]
  [TopologicalSpace M₃] [ChartedSpace E₃ M₃] [IsManifold 𝓘(ℂ, E₃) ∞ M₃]
  {U₁ : Opens M₁} {U₂ : Opens M₂} {U₃ : Opens M₃}
  {f : M₁ → M₂} (hf : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f)
  (hJ : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f)
  {g : U₁ → U₂} (hg : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ g)
  (hJg : IsPseudoholomorphic (ofComplexManifold E₁ U₁) (ofComplexManifold E₂ U₂) g)
  (hfg : ∀ x : U₁, (g x : M₂) = f x)

include hfg in
/-- A holomorphic map of pairs commutes with the restriction cochain maps. -/
theorem restriction_comp_extendMap_map (p : ℕ) :
    restriction E₂ M₂ F U₂ p ≫
        extendMap (dolbeaultComplex.map hg hJg p) ComplexShape.embeddingUpNat =
      extendMap (dolbeaultComplex.map hf hJ p) ComplexShape.embeddingUpNat ≫
        restriction E₁ M₁ F U₁ p := by
  rw [restriction, restriction, ← extendMap_comp, ← extendMap_comp,
    ← dolbeaultComplex.map_comp, ← dolbeaultComplex.map_comp,
    dolbeaultComplex.map_congr (funext hfg)]

/-- The cochain map of relative Dolbeault complexes induced by a holomorphic map of pairs
`(M₁, U₁) ⟶ (M₂, U₂)`: holomorphic maps `f : M₁ → M₂` and `g : U₁ → U₂` with `g x = f x` on
`U₁`. It pulls back both coordinates (`map_f_XEquiv_symm`). -/
def map (p : ℕ) :
    relativeDolbeaultComplex E₂ M₂ F U₂ p ⟶ relativeDolbeaultComplex E₁ M₁ F U₁ p :=
  (mappingCone.map (restriction E₂ M₂ F U₂ p) (restriction E₁ M₁ F U₁ p)
    (extendMap (dolbeaultComplex.map hf hJ p) ComplexShape.embeddingUpNat)
    (extendMap (dolbeaultComplex.map hg hJg p) ComplexShape.embeddingUpNat)
    (restriction_comp_extendMap_map hf hJ hg hJg hfg p))⟦(-1 : ℤ)⟧'

/-- The map induced by a holomorphic map of pairs acts componentwise in relative coordinates. -/
private lemma relativeCoordinates_map_f (p : ℕ) (n k : ℤ) (hnk : n + -1 = k)
    (x : (relativeDolbeaultComplex E₂ M₂ F U₂ p).X n) :
    mappingCocone.relativeCoordinates (restriction E₁ M₁ F U₁ p) n k hnk
        ((map hf hJ hg hJg hfg p).f n x) =
      ((extendMap (dolbeaultComplex.map hf hJ p) ComplexShape.embeddingUpNat).f n
          (mappingCocone.relativeCoordinates (restriction E₂ M₂ F U₂ p) n k hnk x).1,
        (extendMap (dolbeaultComplex.map hg hJg p) ComplexShape.embeddingUpNat).f k
          (mappingCocone.relativeCoordinates (restriction E₂ M₂ F U₂ p) n k hnk x).2) :=
  mappingCocone.relativeCoordinates_map _ _ _ _ _ n k hnk x

/-- In coordinates, the map induced by a holomorphic map of pairs pulls back both forms. -/
@[simp]
theorem map_f_XEquiv_symm (p : ℕ) (n : ℤ) (q : ℕ) (hq : ((q + 1 : ℕ) : ℤ) = n)
    (α : (ofComplexManifold E₂ M₂).typeForms (F := F) p (q + 1))
    (β : (ofComplexManifold E₂ U₂).typeForms (F := F) p q) :
    (map hf hJ hg hJg hfg p).f n ((XEquiv U₂ p n q hq).symm (α, β)) =
      (XEquiv U₁ p n q hq).symm (mpullbackType hf hJ p (q + 1) α, mpullbackType hg hJg p q β) := by
  apply (XEquiv U₁ p n q hq).injective
  rw [LinearEquiv.apply_symm_apply, XEquiv_symm_eq, XEquiv, LinearEquiv.trans_apply,
    relativeCoordinates_map_f, LinearEquiv.apply_symm_apply]
  simp [dolbeaultComplex.extendMap_map_f_extendXEquiv_symm]

/-- In coordinates, the map induced by a holomorphic map of pairs in degree `0` is pullback. -/
@[simp]
theorem map_f_XEquivZero_symm (p : ℕ) (α : (ofComplexManifold E₂ M₂).typeForms (F := F) p 0) :
    (map hf hJ hg hJg hfg p).f 0 ((XEquivZero U₂ p).symm α) =
      (XEquivZero U₁ p).symm (mpullbackType hf hJ p 0 α) := by
  apply (XEquivZero U₁ p).injective
  rw [LinearEquiv.apply_symm_apply, XEquivZero_symm_eq, XEquivZero, LinearEquiv.trans_apply,
    relativeCoordinates_map_f, LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.prodUnique_apply,
    dolbeaultComplex.extendMap_map_f_extendXEquiv_symm, LinearEquiv.apply_symm_apply]

/-- The identity map of pairs induces the identity cochain map. -/
@[simp]
theorem map_id (p : ℕ) :
    map (F := F) (U₁ := U₁) (U₂ := U₁) (f := id) contMDiff_id
      (isPseudoholomorphic_id (ofComplexManifold E₁ M₁)) (g := id) contMDiff_id
      (isPseudoholomorphic_id (ofComplexManifold E₁ U₁)) (fun _ ↦ rfl) p = 𝟙 _ := by
  simp only [map, dolbeaultComplex.map_id, extendMap_id, mappingCone.map_id]
  exact (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat ℂ) ℤ) (-1 : ℤ)).map_id _

/-- The maps induced by holomorphic maps of pairs reverse composition. -/
theorem map_comp {f' : M₂ → M₃} (hf' : ContMDiff 𝓘(ℝ, E₂) 𝓘(ℝ, E₃) ∞ f')
    (hJ' : IsPseudoholomorphic (ofComplexManifold E₂ M₂) (ofComplexManifold E₃ M₃) f')
    {g' : U₂ → U₃} (hg' : ContMDiff 𝓘(ℝ, E₂) 𝓘(ℝ, E₃) ∞ g')
    (hJg' : IsPseudoholomorphic (ofComplexManifold E₂ U₂) (ofComplexManifold E₃ U₃) g')
    (hfg' : ∀ x : U₂, (g' x : M₃) = f' x) (p : ℕ) :
    map (F := F) (hf'.comp hf) (hJ'.comp hJ) (hg'.comp hg) (hJg'.comp hJg)
        (fun x ↦ (hfg' (g x)).trans (congrArg f' (hfg x))) p =
      map hf' hJ' hg' hJg' hfg' p ≫ map hf hJ hg hJg hfg p := by
  have ha := congrArg (extendMap · ComplexShape.embeddingUpNat)
    (dolbeaultComplex.map_comp (F := F) hf hJ hf' hJ' p)
  have hb := congrArg (extendMap · ComplexShape.embeddingUpNat)
    (dolbeaultComplex.map_comp (F := F) hg hJg hg' hJg' p)
  simp only [extendMap_comp] at ha hb
  simp only [map, ha, hb]
  rw [mappingCone.map_comp _ (restriction E₂ M₂ F U₂ p) _ _ _
    (restriction_comp_extendMap_map hf' hJ' hg' hJg' hfg' p) _ _
    (restriction_comp_extendMap_map hf hJ hg hJg hfg p)]
  exact (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat ℂ) ℤ) (-1 : ℤ)).map_comp _ _

end Map

end relativeDolbeaultComplex

end TauCeti
