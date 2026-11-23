/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Relative
public import TauCeti.Algebra.Homology.ModuleCat.Extend
public import TauCeti.Algebra.Homology.ModuleCat.Shift.Sequence
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Cohomology

/-!
# The relative Dolbeault complex of an open pair

Let `M` be a complex manifold, `U` an open subset and `p` a holomorphic degree. The relative
Dolbeault complex of the pair `(M, U)` is the mapping cocone `Cone(A^(p,•)(M) ⟶ A^(p,•)(U))[-1]`
of the restriction of smooth forms of type `(p,•)` from `M` to `U`
(`TauCeti.relativeDolbeaultComplex`). The Dolbeault complexes are indexed by `ℕ`; they are
extended by zero in negative degrees along `ComplexShape.embeddingUpNat`, so that Mathlib's
`CochainComplex.mappingCocone` applies; the relative complex is then strictly concentrated in
nonnegative degrees (`CochainComplex.mappingCocone.isStrictlyGE`).

The construction allows any model space `E` and any complex normed coefficient space `F`. For a
closed subset `S` of `M` and `U = M ∖ S` its cohomology is the relative Dolbeault cohomology of
`(M, M ∖ S)` with coefficients in `F`. In the classical setting of scalar coefficients `F = ℂ` on a
finite-dimensional (paracompact) complex manifold, the relative Dolbeault theorem identifies this
cohomology with the cohomology `H_S^q(M, Ω^p)` of the sheaf of holomorphic `p`-forms with supports
in `S`; that comparison is not proved here.

The terms are, through the relative coordinates `CochainComplex.mappingCocone.relativeCoordinates`
which negate the second component of Mathlib's shifted cone,

`A^(p,q+1)(M) × A^(p,q)(U)` in degree `q + 1`, and `A^(p,0)(M)` in degree `0`,

and the differential is `(α, β) ↦ (∂bar α, α|_U - ∂bar β)` (`d_XEquiv_symm`, `d_XEquivZero_symm`).
Thus a pair `(α, β)` is a relative cocycle exactly when `∂bar α = 0` and `α|_U = ∂bar β`, and it is
a relative coboundary exactly when `(α, β) = (∂bar γ, γ|_U - ∂bar η)`. In degree zero the relative
cocycles are the `∂bar`-closed, that is holomorphic, `p`-forms on `M` vanishing on `U`.

In positive degree the relative cocycles form the submodule
`TauCeti.relativeDolbeaultComplex.cocyclesSucc` of the coordinates, with the class map
`TauCeti.relativeDolbeaultComplex.mkSucc` onto the cohomology of the relative complex. In degree
zero the relative cocycles `TauCeti.relativeDolbeaultComplex.cocyclesZero` are identified with the
cohomology (`TauCeti.relativeDolbeaultComplex.mkZeroEquiv`). The connecting
map `H^(p,q)(U) → H^(p,q+1)(M, U)` is the map induced in cohomology by the connecting morphism of
Mathlib's triangle `CochainComplex.mappingCocone.triangle` of the restriction. On classes it is
`δ[b] = -[(0, b)]`; when `b` is the restriction of a form `b'` on `M`, it is also `[(∂bar b', 0)]`.

A holomorphic map of pairs, a commutative square of holomorphic maps `f : M₁ → M₂` and
`g : U₁ → U₂` over the inclusions, induces a cochain map of relative complexes acting by pullback
on both coordinates (`TauCeti.relativeDolbeaultComplex.map`); it is compatible with identities and
composition, with the class maps and with the connecting map. For open subsets `M'` of `M` and `U'`
of `U`, the inclusions `(M', M' ∩ U) ⟶ (M, U)` and `(M, U') ⟶ (M, U)` are holomorphic maps of
pairs; they induce restriction to `M'` and shrinking of `U` (enlarging the support `M ∖ U`) on the
relative complexes.

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
* `TauCeti.relativeDolbeaultComplex.cocyclesSucc`, `TauCeti.relativeDolbeaultComplex.mkSucc`:
  relative cocycles of positive degree and their classes, with `mkSucc_surjective` and
  `mkSucc_eq_zero_iff`.
* `TauCeti.relativeDolbeaultComplex.cocyclesZero`, `TauCeti.relativeDolbeaultComplex.mkZeroEquiv`:
  relative cocycles of degree `0`, identified with the cohomology in degree `0`.
* `TauCeti.relativeDolbeaultComplex.δ`: the connecting map, induced by the connecting morphism of
  `CochainComplex.mappingCocone.triangle` (`δ_apply`), with `δ_mk` and `δ_mk_of_restrictType_eq`.
* `TauCeti.relativeDolbeaultComplex.map`: the cochain map induced by a holomorphic map of pairs,
  with `map_f_XEquiv_symm`, `map_id`, `map_comp`, the action on classes `homologyMap_map_mkSucc`
  and `homologyMap_map_mkZeroEquiv`, and the naturality `homologyMap_map_δ` of the connecting map.

## References

* N. Honda, T. Izawa and T. Suwa, *Sato hyperfunctions via relative Dolbeault cohomology*,
  J. Math. Soc. Japan 75 (2023).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Chapter I, §6, for the
  analogous relative de Rham complex.
* The index conventions and the shape of the coordinate and class API parallel the relative de Rham
  complex of https://github.com/TauCetiProject/TauCeti/pull/39206.
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

namespace relativeDolbeaultComplex

variable (E M F)

/-- The restriction of forms of type `(p,•)` from `M` to an open subset `U`, as a map of the
Dolbeault complexes extended by zero to `ℤ`. -/
def restriction (U : Opens M) (p : ℕ) :
    (dolbeaultComplex E M F p).extend ComplexShape.embeddingUpNat ⟶
      (dolbeaultComplex E U F p).extend ComplexShape.embeddingUpNat :=
  extendMap (dolbeaultComplex.map contMDiff_subtypeVal
    (isPseudoholomorphic_ofComplexManifold_subtype_val U) p) _

/-- The restriction cochain map is the extension by zero of the cochain map induced by the
inclusion of `U`. -/
theorem restriction_def (U : Opens M) (p : ℕ) :
    restriction E M F U p = extendMap (dolbeaultComplex.map contMDiff_subtypeVal
      (isPseudoholomorphic_ofComplexManifold_subtype_val U) p) _ :=
  (rfl)

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
  mpullbackType contMDiff_subtypeVal (isPseudoholomorphic_ofComplexManifold_subtype_val U) p q

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
      (CochainComplex.isZero_of_isStrictlyGE
        ((dolbeaultComplex E U F p).extend ComplexShape.embeddingUpNat) 0 (-1))) 0
  (mappingCocone.relativeCoordinates (restriction E M F U p) 0 (-1) rfl).trans
    (((dolbeaultComplex.extendXEquiv E M F p 0 0 rfl).prodCongr (LinearEquiv.refl ℂ _)).trans
      (LinearEquiv.prodUnique (R := ℂ)))

/-- `XEquiv` reads the relative coordinates through the identifications `extendXEquiv`. -/
theorem XEquiv_apply (n : ℤ) (q : ℕ) (hq : ((q + 1 : ℕ) : ℤ) = n)
    (x : (relativeDolbeaultComplex E M F U p).X n) :
    XEquiv U p n q hq x =
      (dolbeaultComplex.extendXEquiv E M F p (q + 1) n hq
          (mappingCocone.relativeCoordinates (restriction E M F U p) n q (by omega) x).1,
        dolbeaultComplex.extendXEquiv E U F p q q rfl
          (mappingCocone.relativeCoordinates (restriction E M F U p) n q (by omega) x).2) :=
  (rfl)

/-- The inverse of `XEquiv` is the inverse of the relative coordinates. -/
theorem XEquiv_symm_apply (n : ℤ) (q : ℕ) (hq : ((q + 1 : ℕ) : ℤ) = n)
    (x : (ofComplexManifold E M).typeForms (F := F) p (q + 1) ×
      (ofComplexManifold E U).typeForms (F := F) p q) :
    (XEquiv U p n q hq).symm x = (mappingCocone.relativeCoordinates (restriction E M F U p) n q
      (by omega)).symm ((dolbeaultComplex.extendXEquiv E M F p (q + 1) n hq).symm x.1,
        (dolbeaultComplex.extendXEquiv E U F p q q rfl).symm x.2) :=
  (rfl)

/-- `XEquivZero` reads the first relative coordinate through `extendXEquiv`. -/
theorem XEquivZero_apply (x : (relativeDolbeaultComplex E M F U p).X 0) :
    XEquivZero U p x = dolbeaultComplex.extendXEquiv E M F p 0 0 rfl
      (mappingCocone.relativeCoordinates (restriction E M F U p) 0 (-1) rfl x).1 :=
  (rfl)

/-- The inverse of `XEquivZero` is the inverse of the relative coordinates, with second
coordinate zero. -/
theorem XEquivZero_symm_apply (α : (ofComplexManifold E M).typeForms (F := F) p 0) :
    (XEquivZero U p).symm α =
      (mappingCocone.relativeCoordinates (restriction E M F U p) 0 (-1) rfl).symm
        ((dolbeaultComplex.extendXEquiv E M F p 0 0 rfl).symm α, 0) := by
  apply (XEquivZero U p).injective
  rw [LinearEquiv.apply_symm_apply, XEquivZero_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

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
  rw [XEquiv_symm_apply, XEquiv_symm_apply]
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
  rw [XEquivZero_symm_apply, XEquiv_symm_apply]
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
def cocyclesSucc (q : ℕ) :
    Submodule ℂ ((ofComplexManifold E M).typeForms (F := F) p (q + 1) ×
      (ofComplexManifold E U).typeForms (F := F) p q) :=
  LinearMap.ker ((((ofComplexManifold E M).delBarType p (q + 1)).comp (LinearMap.fst ℂ _ _)).prod
    ((restrictType U p (q + 1)).comp (LinearMap.fst ℂ _ _) -
      ((ofComplexManifold E U).delBarType p q).comp (LinearMap.snd ℂ _ _)))

/-- Membership in the relative cocycles: `∂bar α = 0` and `α|_U = ∂bar β`. -/
@[simp]
theorem mem_cocyclesSucc {q : ℕ} (x : (ofComplexManifold E M).typeForms (F := F) p (q + 1) ×
      (ofComplexManifold E U).typeForms (F := F) p q) :
    x ∈ cocyclesSucc U p q ↔ (ofComplexManifold E M).delBarType p (q + 1) x.1 = 0 ∧
      restrictType U p (q + 1) x.1 = (ofComplexManifold E U).delBarType p q x.2 := by
  simp [cocyclesSucc, sub_eq_zero]

/-- For a `∂bar`-closed form `b` on `U`, the pair `(0, b)` is a relative cocycle. -/
theorem zero_prodMk_mem_cocyclesSucc {q : ℕ} (b : Dolbeault.closedForms E U F p q) :
    ((0 : (ofComplexManifold E M).typeForms (F := F) p (q + 1)), b.val) ∈ cocyclesSucc U p q :=
  (mem_cocyclesSucc U p _).mpr ⟨map_zero _, (map_zero _).trans
    ((Dolbeault.mem_closedForms_iff_delBarType_eq_zero p q b.val).mp b.property).symm⟩

/-- For a form `b'` on `M` whose restriction to `U` is `∂bar`-closed, the pair `(∂bar b', 0)` is a
relative cocycle. -/
theorem delBarType_prodMk_zero_mem_cocyclesSucc {q : ℕ}
    (b' : (ofComplexManifold E M).typeForms (F := F) p q)
    (hb' : restrictType U p q b' ∈ Dolbeault.closedForms E U F p q) :
    ((ofComplexManifold E M).delBarType p q b', 0) ∈ cocyclesSucc U p q :=
  (mem_cocyclesSucc U p _).mpr ⟨delBarType_delBarType_ofComplexManifold p q b', by
    rw [map_zero, ← delBarType_mpullbackType,
      (Dolbeault.mem_closedForms_iff_delBarType_eq_zero p q _).mp hb']⟩

/-- The relative Dolbeault cohomology class of a relative cocycle of degree `q + 1`. -/
def mkSucc (q : ℕ) :
    cocyclesSucc (E := E) (F := F) U p q →ₗ[ℂ]
      (relativeDolbeaultComplex E M F U p).homology ((q + 1 : ℕ) : ℤ) :=
  (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass (Z := cocyclesSucc U p q)
    (CochainComplex.next ℤ _)
    ((XEquiv U p _ q rfl).symm.toLinearMap ∘ₗ (cocyclesSucc U p q).subtype) fun x ↦ by
      obtain ⟨⟨α, β⟩, hx⟩ := x
      exact (d_XEquiv_symm_eq_zero_iff U p _ _ q rfl rfl α β).mpr ((mem_cocyclesSucc U p _).mp hx)

/-- The relative class map is the homology class map of the relative cocycles, embedded into the
relative complex through the coordinates `XEquiv`. -/
theorem mkSucc_eq_moduleCatHomologyClass (q : ℕ) :
    relativeDolbeaultComplex.mkSucc (E := E) (F := F) U p q =
      (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass (Z := cocyclesSucc U p q)
        (CochainComplex.next ℤ _)
        ((XEquiv U p _ q rfl).symm.toLinearMap ∘ₗ (cocyclesSucc U p q).subtype) fun x ↦ by
          obtain ⟨⟨α, β⟩, hx⟩ := x
          exact (d_XEquiv_symm_eq_zero_iff U p _ _ q rfl rfl α β).mpr
            ((mem_cocyclesSucc U p _).mp hx) :=
  (rfl)

/-- Every relative Dolbeault cohomology class of positive degree is represented by a relative
cocycle. -/
theorem mkSucc_surjective (q : ℕ) :
    Function.Surjective (relativeDolbeaultComplex.mkSucc (E := E) (F := F) U p q) := by
  rw [relativeDolbeaultComplex.mkSucc]
  refine (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass_surjective _ _ _ fun y hy ↦ ?_
  obtain ⟨⟨α, β⟩, rfl⟩ := (XEquiv U p _ q rfl).symm.surjective y
  exact ⟨⟨(α, β), (mem_cocyclesSucc U p _).mpr
    ((d_XEquiv_symm_eq_zero_iff U p _ _ q rfl rfl α β).mp hy)⟩, rfl⟩

/-- The class of a relative cocycle vanishes exactly when the cocycle is a coboundary. -/
theorem mkSucc_eq_zero_iff (q : ℕ) (x : cocyclesSucc (E := E) (F := F) U p q) :
    relativeDolbeaultComplex.mkSucc U p q x = 0 ↔
      ∃ y : (relativeDolbeaultComplex E M F U p).X q,
        (relativeDolbeaultComplex E M F U p).d q ((q + 1 : ℕ) : ℤ) y =
          (XEquiv U p _ q rfl).symm x := by
  rw [relativeDolbeaultComplex.mkSucc]
  exact (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass_eq_zero_iff _ _ _ (by simp) x

/-- The relative cocycles of degree `0` in coordinates: the holomorphic forms `α` of type `(p,0)`
on `M`, `∂bar α = 0`, vanishing on `U`. -/
def cocyclesZero : Submodule ℂ ((ofComplexManifold E M).typeForms (F := F) p 0) :=
  LinearMap.ker (((ofComplexManifold E M).delBarType p 0).prod (restrictType U p 0))

/-- Membership in the relative cocycles of degree `0`: `∂bar α = 0` and `α|_U = 0`. -/
@[simp]
theorem mem_cocyclesZero (α : (ofComplexManifold E M).typeForms (F := F) p 0) :
    α ∈ cocyclesZero U p ↔
      (ofComplexManifold E M).delBarType p 0 α = 0 ∧ restrictType U p 0 α = 0 := by
  simp [cocyclesZero]

/-- The relative cohomology in degree `0` is the space of relative cocycles of degree `0`: the
class map is a linear equivalence. -/
def mkZeroEquiv :
    cocyclesZero (E := E) (F := F) U p ≃ₗ[ℂ] (relativeDolbeaultComplex E M F U p).homology 0 :=
  have hd (x : cocyclesZero (E := E) (F := F) U p) :
      (relativeDolbeaultComplex E M F U p).d 0 1 ((XEquivZero U p).symm x.val) = 0 :=
    (d_XEquivZero_symm_eq_zero_iff U p x.val).mpr ((mem_cocyclesZero U p _).mp x.property)
  LinearEquiv.ofBijective
    ((relativeDolbeaultComplex E M F U p).moduleCatHomologyClass (Z := cocyclesZero U p)
      (CochainComplex.next ℤ 0)
      ((XEquivZero U p).symm.toLinearMap ∘ₗ (cocyclesZero U p).subtype) hd)
    ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ by
      obtain ⟨y, hy⟩ := ((relativeDolbeaultComplex E M F U p).moduleCatHomologyClass_eq_zero_iff
        _ _ _ (CochainComplex.prev ℤ 0) x).mp hx
      rw [(ModuleCat.isZero_iff_subsingleton.mp (CochainComplex.isZero_of_isStrictlyGE
        (relativeDolbeaultComplex E M F U p) 0 (0 - 1) (by norm_num))).elim y 0, map_zero] at hy
      exact Subtype.ext ((XEquivZero U p).symm.injective
        (hy.symm.trans (XEquivZero U p).symm.map_zero.symm)),
    (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass_surjective _ _ _ fun y hy ↦ by
      obtain ⟨α, rfl⟩ := (XEquivZero U p).symm.surjective y
      exact ⟨⟨α, (mem_cocyclesZero U p _).mpr ((d_XEquivZero_symm_eq_zero_iff U p α).mp hy)⟩,
        rfl⟩⟩

/-- The identification of the relative cohomology in degree `0` with the relative cocycles is the
homology class map of the cocycles, embedded into the relative complex through `XEquivZero`. -/
theorem mkZeroEquiv_apply (x : cocyclesZero (E := E) (F := F) U p) :
    mkZeroEquiv U p x =
      (relativeDolbeaultComplex E M F U p).moduleCatHomologyClass (Z := cocyclesZero U p)
        (CochainComplex.next ℤ 0)
        ((XEquivZero U p).symm.toLinearMap ∘ₗ (cocyclesZero U p).subtype)
        (fun x ↦ (d_XEquivZero_symm_eq_zero_iff U p x.val).mpr
          ((mem_cocyclesZero U p _).mp x.property))
        x :=
  (rfl)

/-- The connecting map `H^(p,q)(U) → H^(p,q+1)(M, U)` of the relative Dolbeault complex: the map
induced in cohomology by the connecting morphism of the triangle `mappingCocone.triangle` of the
restriction, after identifying the Dolbeault cohomology of `U` with that of the extended complex.
On classes, `δ[b] = -[(0, b)]` for a `∂bar`-closed form `b` on `U`
(`TauCeti.relativeDolbeaultComplex.δ_mk`). -/
def δ (q : ℕ) :
    dolbeaultCohomology E U F p q →ₗ[ℂ]
      (relativeDolbeaultComplex E M F U p).homology ((q + 1 : ℕ) : ℤ) :=
  ((homologyFunctor _ _ 0).shiftMap (mappingCocone.triangle (restriction E M F U p)).mor₃
      (q : ℤ) ((q + 1 : ℕ) : ℤ) (by omega)).hom ∘ₗ
    ((dolbeaultComplex E U F p).extendHomologyIso ComplexShape.embeddingUpNat (j := q)
      (j' := (q : ℤ)) (by simp)).inv.hom

/-- The connecting map is the identification of the cohomology of `U` with that of the extended
complex, followed by the map induced by the connecting morphism of `mappingCocone.triangle`. -/
theorem δ_apply (q : ℕ) (c : dolbeaultCohomology E U F p q) :
    δ (M := M) U p q c = ((homologyFunctor _ _ 0).shiftMap
      (mappingCocone.triangle (restriction E M F U p)).mor₃ (q : ℤ) ((q + 1 : ℕ) : ℤ)
        (by omega)).hom (((dolbeaultComplex E U F p).extendHomologyIso
          ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) (by simp)).inv.hom c) :=
  (rfl)

/-- The connecting map sends the class of a `∂bar`-closed form `b` on `U` to `-[(0, b)]`. -/
theorem δ_mk (q : ℕ) (b : Dolbeault.closedForms E U F p q) :
    δ (M := M) U p q (dolbeaultCohomology.mk p q b) =
      -relativeDolbeaultComplex.mkSucc U p q ⟨(0, b.val), zero_prodMk_mem_cocyclesSucc U p b⟩ := by
  rw [δ_apply, dolbeaultCohomology.mk_eq_moduleCatHomologyClass, moduleCatHomologyClass_apply]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  have hb := (Dolbeault.mem_closedForms_iff_delBarType_eq_zero p q b.val).mp b.property
  have hx := dolbeaultComplex.extend_d_extendXEquiv_symm (M := U) (F := F) p q q (q + 1) rfl rfl
    b.val
  rw [hb, LinearEquiv.map_zero, dolbeaultComplex.extendXEquiv_symm_apply] at hx
  -- The class of `b` in the extended complex.
  have h₁ := extendHomologyIso_inv_homologyπ_moduleCatCyclesMk (dolbeaultComplex E U F p)
    ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) (by simp)
    ((dolbeaultComplexXIso p q).inv b.val) (q + 1) (CochainComplex.next ℕ q) (by
      rw [dolbeaultComplex_d_apply, Iso.inv_hom_id_apply, hb, map_zero]) ((q : ℤ) + 1) (by simp)
    hx
  -- The connecting morphism of the triangle sends `b` to `inr b = -(0, b)`.
  have hy : -(XEquiv U p _ q rfl).symm (0, b.val) =
      ((relativeDolbeaultComplex E M F U p).shiftFunctorObjXIso 1 q ((q + 1 : ℕ) : ℤ)
        (by push_cast; ring)).hom.hom
        (((mappingCocone.triangle (restriction E M F U p)).mor₃.f q).hom
          ((extendXIso (dolbeaultComplex E U F p) ComplexShape.embeddingUpNat (i := q)
            (by simp)).inv ((dolbeaultComplexXIso p q).inv b.val))) := by
    rw [XEquiv_symm_apply, mappingCocone.relativeCoordinates_symm_apply, LinearEquiv.map_zero,
      LinearMap.map_zero, zero_sub, _root_.neg_neg, dolbeaultComplex.extendXEquiv_symm_apply]
    exact (congrArg (fun g ↦ ModuleCat.Hom.hom g
      ((extendXIso (dolbeaultComplex E U F p) ComplexShape.embeddingUpNat (i := q)
        (by simp)).inv ((dolbeaultComplexXIso p q).inv b.val)))
      (mappingCocone.triangle_mor₃_f_shiftFunctorObjXIso_hom (restriction E M F U p) q
        ((q + 1 : ℕ) : ℤ) (by push_cast; rfl))).symm
  have hy' : ((relativeDolbeaultComplex E M F U p).d ((q + 1 : ℕ) : ℤ) ((q + 1 : ℕ) + 1)).hom
      (-(XEquiv U p _ q rfl).symm (0, b.val)) = 0 := by
    rw [LinearMap.map_neg, neg_eq_zero, d_XEquiv_symm_eq_zero_iff U p _ _ q rfl rfl]
    exact (mem_cocyclesSucc U p (0, b.val)).mp (zero_prodMk_mem_cocyclesSucc U p b)
  have h₂ := shiftMap_homologyπ_moduleCatCyclesMk
    (mappingCocone.triangle (restriction E M F U p)).mor₃
    (q : ℤ) ((q + 1 : ℕ) : ℤ) (by omega) _ hx _ hy hy'
  -- The class of `-(0, b)` is `-[(0, b)]`.
  have h₃ : (relativeDolbeaultComplex E M F U p).homologyπ ((q + 1 : ℕ) : ℤ)
      ((relativeDolbeaultComplex E M F U p).moduleCatCyclesMk _ (((q + 1 : ℕ) : ℤ) + 1)
        (by simp) hy') =
      -relativeDolbeaultComplex.mkSucc U p q ⟨(0, b.val), zero_prodMk_mem_cocyclesSucc U p b⟩ := by
    rw [mkSucc_eq_moduleCatHomologyClass, moduleCatHomologyClass_apply]
    refine (congrArg ((relativeDolbeaultComplex E M F U p).homologyπ ((q + 1 : ℕ) : ℤ)).hom
      (moduleCat_iCycles_injective _ _ ?_)).trans (LinearMap.map_neg _ _)
    exact ((iCycles_moduleCatCyclesMk _ _ _ _ _ _).trans
      (congrArg Neg.neg (iCycles_moduleCatCyclesMk _ _ _ _ _ _).symm)).trans
        (LinearMap.map_neg _ _).symm
  exact ((congrArg ((homologyFunctor _ _ 0).shiftMap
    (mappingCocone.triangle (restriction E M F U p)).mor₃ (q : ℤ) ((q + 1 : ℕ) : ℤ)
      (by omega)).hom h₁).trans h₂).trans h₃

/-- If a `∂bar`-closed form `b` on `U` is the restriction of a form `b'` on `M`, the connecting map
sends its class to the class of `(∂bar b', 0)`. -/
theorem δ_mk_of_restrictType_eq (q : ℕ) (b : Dolbeault.closedForms E U F p q)
    (b' : (ofComplexManifold E M).typeForms (F := F) p q) (hb' : restrictType U p q b' = b.val) :
    δ (M := M) U p q (dolbeaultCohomology.mk p q b) =
      relativeDolbeaultComplex.mkSucc U p q ⟨((ofComplexManifold E M).delBarType p q b', 0),
        delBarType_prodMk_zero_mem_cocyclesSucc U p b' (hb' ▸ b.property)⟩ := by
  rw [δ_mk, neg_eq_iff_add_eq_zero, ← map_add, mkSucc_eq_zero_iff]
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

/-- The cochain map induced by a holomorphic map of pairs is the shifted map of mapping cones
induced by the extended cochain maps of `f` and `g`. -/
theorem map_def (p : ℕ) :
    map (F := F) hf hJ hg hJg hfg p =
      (mappingCone.map (restriction E₂ M₂ F U₂ p) (restriction E₁ M₁ F U₁ p)
        (extendMap (dolbeaultComplex.map hf hJ p) ComplexShape.embeddingUpNat)
        (extendMap (dolbeaultComplex.map hg hJg p) ComplexShape.embeddingUpNat)
        (restriction_comp_extendMap_map hf hJ hg hJg hfg p))⟦(-1 : ℤ)⟧' :=
  (rfl)

/-- The cochain map induced by a holomorphic map of pairs depends only on the maps. -/
theorem map_congr {f' : M₁ → M₂} (hff : f = f') (hf' : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f')
    (hJ' : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f')
    {g' : U₁ → U₂} (hgg : g = g') (hg' : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ g')
    (hJg' : IsPseudoholomorphic (ofComplexManifold E₁ U₁) (ofComplexManifold E₂ U₂) g')
    (hfg' : ∀ x : U₁, (g' x : M₂) = f' x) (p : ℕ) :
    map (F := F) hf hJ hg hJg hfg p = map hf' hJ' hg' hJg' hfg' p := by
  subst hff hgg
  rfl

/-- The map induced by a holomorphic map of pairs acts componentwise in relative coordinates. -/
-- `mappingCocone.relativeCoordinates_map` does not rewrite after unfolding `map` directly: the
-- unfolded morphism is typed between the mapping cocones, not between the relative complexes.
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
  rw [LinearEquiv.apply_symm_apply, XEquiv_symm_apply, XEquiv, LinearEquiv.trans_apply,
    relativeCoordinates_map_f, LinearEquiv.apply_symm_apply]
  simp [dolbeaultComplex.extendMap_map_f_extendXEquiv_symm]

/-- In coordinates, the map induced by a holomorphic map of pairs in degree `0` is pullback. -/
@[simp]
theorem map_f_XEquivZero_symm (p : ℕ) (α : (ofComplexManifold E₂ M₂).typeForms (F := F) p 0) :
    (map hf hJ hg hJg hfg p).f 0 ((XEquivZero U₂ p).symm α) =
      (XEquivZero U₁ p).symm (mpullbackType hf hJ p 0 α) := by
  apply (XEquivZero U₁ p).injective
  rw [LinearEquiv.apply_symm_apply, XEquivZero_symm_apply, XEquivZero, LinearEquiv.trans_apply,
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

include hfg in
/-- Pullback along a holomorphic map of pairs commutes with restriction of type forms. -/
theorem restrictType_mpullbackType (p q : ℕ)
    (α : (ofComplexManifold E₂ M₂).typeForms (F := F) p q) :
    restrictType U₁ p q (mpullbackType hf hJ p q α) =
      mpullbackType hg hJg p q (restrictType U₂ p q α) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← mpullbackType_comp, ← mpullbackType_comp]
  exact LinearMap.congr_fun
    (mpullbackType_congr (funext fun x ↦ (hfg x).symm) _ _ _ _ p q) α

/-- Pullback of relative cocycles of degree `q + 1` along a holomorphic map of pairs. -/
def mapCocyclesSucc (p q : ℕ) :
    cocyclesSucc (E := E₂) (F := F) U₂ p q →ₗ[ℂ] cocyclesSucc (E := E₁) (F := F) U₁ p q :=
  ((mpullbackType hf hJ p (q + 1)).prodMap (mpullbackType hg hJg p q)).restrict fun x hx ↦ by
    rw [mem_cocyclesSucc] at hx ⊢
    refine ⟨?_, ?_⟩
    · rw [LinearMap.prodMap_apply, delBarType_mpullbackType, hx.1, map_zero]
    · rw [LinearMap.prodMap_apply, restrictType_mpullbackType hf hJ hg hJg hfg, hx.2,
        delBarType_mpullbackType]

/-- Pullback of relative cocycles of positive degree pulls back both forms. -/
@[simp]
theorem coe_mapCocyclesSucc (p q : ℕ) (x : cocyclesSucc (E := E₂) (F := F) U₂ p q) :
    (mapCocyclesSucc hf hJ hg hJg hfg p q x : _ × _) =
      (mpullbackType hf hJ p (q + 1) x.val.fst, mpullbackType hg hJg p q x.val.snd) :=
  (rfl)

/-- Pullback of relative cocycles of degree `0` along a holomorphic map of pairs. -/
def mapCocyclesZero (p : ℕ) :
    cocyclesZero (E := E₂) (F := F) U₂ p →ₗ[ℂ] cocyclesZero (E := E₁) (F := F) U₁ p :=
  (mpullbackType hf hJ p 0).restrict fun α hα ↦ by
    rw [mem_cocyclesZero] at hα ⊢
    rw [delBarType_mpullbackType, hα.1, map_zero, restrictType_mpullbackType hf hJ hg hJg hfg,
      hα.2, map_zero]
    exact ⟨rfl, rfl⟩

/-- Pullback of relative cocycles of degree `0` is pullback of forms. -/
@[simp]
theorem coe_mapCocyclesZero (p : ℕ) (α : cocyclesZero (E := E₂) (F := F) U₂ p) :
    (mapCocyclesZero hf hJ hg hJg hfg p α : (ofComplexManifold E₁ M₁).typeForms (F := F) p 0) =
      mpullbackType hf hJ p 0 α.val :=
  (rfl)

/-- The map induced on relative cohomology of positive degree by a holomorphic map of pairs sends
the class of a relative cocycle to the class of its pullback. -/
theorem homologyMap_map_mkSucc (p q : ℕ) (x : cocyclesSucc (E := E₂) (F := F) U₂ p q) :
    HomologicalComplex.homologyMap (map (F := F) hf hJ hg hJg hfg p) ((q + 1 : ℕ) : ℤ)
        (mkSucc U₂ p q x) =
      mkSucc U₁ p q (mapCocyclesSucc hf hJ hg hJg hfg p q x) := by
  rw [mkSucc_eq_moduleCatHomologyClass, mkSucc_eq_moduleCatHomologyClass]
  exact HomologicalComplex.homologyMap_moduleCatHomologyClass _ _ _ _ _ _ _ (fun x ↦
    map_f_XEquiv_symm hf hJ hg hJg hfg p _ q rfl x.val.fst x.val.snd) x

/-- The map induced on relative cohomology of degree `0` by a holomorphic map of pairs is pullback
of relative cocycles. -/
theorem homologyMap_map_mkZeroEquiv (p : ℕ) (α : cocyclesZero (E := E₂) (F := F) U₂ p) :
    HomologicalComplex.homologyMap (map (F := F) hf hJ hg hJg hfg p) 0 (mkZeroEquiv U₂ p α) =
      mkZeroEquiv U₁ p (mapCocyclesZero hf hJ hg hJg hfg p α) := by
  rw [mkZeroEquiv_apply, mkZeroEquiv_apply]
  exact HomologicalComplex.homologyMap_moduleCatHomologyClass _ _ _ _ _ _ _ (fun α ↦
    map_f_XEquivZero_symm hf hJ hg hJg hfg p α.val) α

/-- The connecting maps are natural in holomorphic maps of pairs. -/
theorem homologyMap_map_δ (p q : ℕ) (c : dolbeaultCohomology E₂ U₂ F p q) :
    HomologicalComplex.homologyMap (map (F := F) hf hJ hg hJg hfg p) ((q + 1 : ℕ) : ℤ)
        (δ U₂ p q c) =
      δ U₁ p q (dolbeaultCohomology.map hg hJg p q c) := by
  obtain ⟨b, rfl⟩ := dolbeaultCohomology.mk_surjective p q c
  rw [δ_mk, map_neg, homologyMap_map_mkSucc, dolbeaultCohomology.map_mk, δ_mk]
  refine congrArg (fun x ↦ -mkSucc U₁ p q x) (Subtype.ext ?_)
  rw [coe_mapCocyclesSucc]
  exact Prod.ext (map_zero _) (Subtype.ext ((coe_mpullbackType hg hJg p q b.val).trans
    (Dolbeault.closedForms.coe_mpullback hg hJg p q b).symm))

end Map

end relativeDolbeaultComplex

end TauCeti
