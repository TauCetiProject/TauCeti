/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Holomorphic

/-!
# The Dolbeault complex and Dolbeault cohomology

Let `J` be a smooth almost complex structure on a manifold `M` and let `F` be a complex normed
space. The operator `∂bar` restricts to a complex-linear map
`TauCeti.SmoothAlmostComplexStructure.delBarTypeForms` from the complex subspace
`TauCeti.SmoothAlmostComplexStructure.typeForms` of forms of type `(p,q)` to that of forms of type
`(p,q+1)`, with `∂bar`-closed and `∂bar`-exact forms
`TauCeti.SmoothAlmostComplexStructure.delBarClosedForms` and
`TauCeti.SmoothAlmostComplexStructure.delBarExactForms`.

On a complex manifold `M` modelled on `𝓘(ℂ, E)`, with its almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M`, `∂bar` squares to zero
(`TauCeti.SmoothAlmostComplexStructure.delBar_delBar_ofComplexManifold`). For each `p` the forms of
type `(p,q)`, `q ≥ 0`, with the differential `∂bar` thus form a cochain complex of complex vector
spaces, the Dolbeault complex `TauCeti.dolbeaultComplex E M F p`. Its cohomology in degree `q` is
the Dolbeault cohomology `H^(p,q)_∂bar(M; F)`, `TauCeti.dolbeaultCohomology E M F p q`, which is
Mathlib's categorical homology in `ModuleCat ℂ`; in particular it is a complex vector space. The
class map from `∂bar`-closed forms of type `(p,q)` is complex-linear and surjective, and its kernel
consists exactly of the `∂bar`-exact forms.

A holomorphic map of complex manifolds is a smooth map of the underlying real manifolds which is
pseudoholomorphic for their almost complex structures. Pullback along it induces complex-linear
maps on Dolbeault cohomology, contravariantly functorial in the map.

In degree `q = 0` there are no `∂bar`-exact forms, so `H^(p,0)_∂bar(M; F)` is the space of
`∂bar`-closed forms of type `(p,0)`, the holomorphic `p`-forms. For `p = 0` these are the
holomorphic functions `M → F` when the model `E` is finite-dimensional and `F` is complete
(`TauCeti.dolbeaultCohomology.zeroZeroEquiv`).

## Main declarations

* `TauCeti.dolbeaultComplex`: the Dolbeault complex of a complex manifold in `ModuleCat ℂ`.
* `TauCeti.dolbeaultCohomology`: Dolbeault cohomology `H^(p,q)_∂bar(M; F)`.
* `TauCeti.dolbeaultCohomology.mk`: the class of a `∂bar`-closed form, with `mk_surjective`,
  `mk_eq_zero_iff` and `mk_eq_mk_iff`.
* `TauCeti.dolbeaultCohomology.map`: the map induced by a holomorphic map, with `map_mk`, `map_id`
  and `map_comp`.
* `TauCeti.dolbeaultCohomology.mkZeroEquiv`: `H^(p,0)_∂bar(M; F)` is the space of `∂bar`-closed
  forms of type `(p,0)`.
* `TauCeti.dolbeaultCohomology.zeroZeroEquiv`: `H^(0,0)_∂bar(M; F)` is the space of holomorphic
  functions `M → F`.

## Implementation notes

The construction follows the de Rham cohomology modules of Tau Ceti. The complex is built with
`CochainComplex.of` from the identifications of its terms, as `TauCeti.deRhamComplex` in
`TauCeti.Geometry.Manifold.DeRham.Basic` and `TauCeti.complexDeRhamComplex` in
`TauCeti.Geometry.Manifold.DeRham.ComplexCoefficients`. As in the latter, the class map and its
surjectivity and kernel come from `HomologicalComplex.moduleCatCohomologyClassOfIso`. The map
induced by a holomorphic map descends pullback of closed forms along the surjective class map with
`LinearMap.liftOfSurjective`, as `TauCeti.deRhamCohomology.map` in
`TauCeti.Geometry.Manifold.DeRham.Map`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §2.
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

/-! ### The Dolbeault complex of a complex manifold -/

section ComplexManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (E M F) in
/-- The Dolbeault complex of a complex manifold in bidegree `(p,•)`: the nonnegative cochain
complex of complex vector spaces of smooth `F`-valued forms of type `(p,q)`, `q ≥ 0`, with the
differential `∂bar`. -/
def dolbeaultComplex (p : ℕ) : CochainComplex (ModuleCat ℂ) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of ℂ ((ofComplexManifold E M).typeForms F p q))
    (fun q ↦ ModuleCat.ofHom ((ofComplexManifold E M).delBarTypeForms F p q))
    (fun q ↦ ModuleCat.hom_ext (delBarTypeForms_comp_delBarTypeForms_ofComplexManifold p q))

/-- The canonical identification of the degree-`q` object of the Dolbeault complex with the smooth
forms of type `(p,q)`. This isomorphism makes the form carrier available without unfolding the
complex. -/
def dolbeaultComplexXIso (p q : ℕ) :
    (dolbeaultComplex E M F p).X q ≅ ModuleCat.of ℂ ((ofComplexManifold E M).typeForms F p q) :=
  Iso.refl _

/-- Under the canonical identifications of the objects, the differential of the Dolbeault complex
is `∂bar`. -/
@[reassoc]
theorem dolbeaultComplex_d (p q : ℕ) :
    (dolbeaultComplex E M F p).d q (q + 1) ≫ (dolbeaultComplexXIso p (q + 1)).hom =
      (dolbeaultComplexXIso p q).hom ≫
        ModuleCat.ofHom ((ofComplexManifold E M).delBarTypeForms F p q) := by
  dsimp +instances [dolbeaultComplexXIso, dolbeaultComplex]
  simp

/-- The differential of the Dolbeault complex, evaluated on an element. -/
theorem dolbeaultComplex_d_apply (p q : ℕ) (x : (dolbeaultComplex E M F p).X q) :
    (dolbeaultComplex E M F p).d q (q + 1) x =
      (dolbeaultComplexXIso p (q + 1)).inv
        ((ofComplexManifold E M).delBarTypeForms F p q ((dolbeaultComplexXIso p q).hom x)) := by
  rw [(Iso.eq_comp_inv _).mpr (dolbeaultComplex_d p q), ModuleCat.comp_apply,
    ModuleCat.comp_apply, ConcreteCategory.hom_ofHom]

variable (E M F) in
/-- The Dolbeault cohomology `H^(p,q)_∂bar(M; F)` of a complex manifold, the categorical homology
of its Dolbeault complex in degree `q`. It is a complex vector space. -/
abbrev dolbeaultCohomology (p q : ℕ) : Type _ :=
  (dolbeaultComplex E M F p).homology q

variable (E M F) in
/-- The `∂bar`-closed forms of type `(p,q)`, as a subspace of the forms of type `(p,q)`. -/
private def closedTypeForms (p q : ℕ) : Submodule ℂ ((ofComplexManifold E M).typeForms F p q) :=
  ((ofComplexManifold E M).delBarClosedForms F p q).comap
    ((ofComplexManifold E M).typeForms F p q).subtype

variable (E M F) in
/-- The `∂bar`-exact forms of type `(p,q)`, as a subspace of the forms of type `(p,q)`. -/
private def exactTypeForms (p q : ℕ) : Submodule ℂ ((ofComplexManifold E M).typeForms F p q) :=
  ((ofComplexManifold E M).delBarExactForms F p q).comap
    ((ofComplexManifold E M).typeForms F p q).subtype

/-- A form of type `(p,q)` is `∂bar`-closed exactly when the differential of the Dolbeault complex
kills it. -/
private theorem mem_closedTypeForms_iff_d_eq_zero (p q : ℕ)
    (φ : (ofComplexManifold E M).typeForms F p q) :
    φ ∈ closedTypeForms E M F p q ↔
      (dolbeaultComplex E M F p).d q (q + 1) ((dolbeaultComplexXIso p q).inv φ) = 0 := by
  rw [(dolbeaultComplex E M F p).moduleCat_d_inv_eq_zero_iff
    (fun q ↦ (ofComplexManifold E M).delBarTypeForms F p q) (dolbeaultComplex_d p),
    closedTypeForms, Submodule.mem_comap, Submodule.coe_subtype, mem_delBarClosedForms,
    ← Submodule.coe_eq_zero (x := (ofComplexManifold E M).delBarTypeForms F p q φ),
    coe_delBarTypeForms]
  exact and_iff_right (mem_typeForms.1 φ.2)

/-- There are no nonzero `∂bar`-exact forms of type `(p,0)`. -/
private theorem exactTypeForms_zero (p : ℕ) : exactTypeForms E M F p 0 = ⊥ := by
  rw [exactTypeForms, delBarExactForms_zero, Submodule.comap_bot, Submodule.ker_subtype]

/-- The `∂bar`-exact forms of type `(p,q+1)` are the image of `∂bar` on forms of type `(p,q)`. -/
private theorem exactTypeForms_succ (p q : ℕ) :
    exactTypeForms E M F p (q + 1) =
      LinearMap.range ((ofComplexManifold E M).delBarTypeForms F p q) := by
  ext ψ
  rw [exactTypeForms, Submodule.mem_comap, Submodule.coe_subtype, mem_delBarExactForms_succ,
    LinearMap.mem_range]
  constructor
  · rintro ⟨χ, hχ, h⟩
    exact ⟨⟨χ, mem_typeForms.2 hχ⟩, Subtype.ext (by rw [coe_delBarTypeForms, h])⟩
  · rintro ⟨χ, rfl⟩
    exact ⟨χ.1, mem_typeForms.1 χ.2, (coe_delBarTypeForms _ _ _).symm⟩

/-- A form of type `(p,q)` is `∂bar`-exact exactly when it is hit by the incoming differential of
the Dolbeault complex. -/
private theorem mem_exactTypeForms_iff_exists_d_eq (p q : ℕ)
    (φ : (ofComplexManifold E M).typeForms F p q) :
    φ ∈ exactTypeForms E M F p q ↔
      ∃ y : (dolbeaultComplex E M F p).X ((ComplexShape.up ℕ).prev q),
        (dolbeaultComplex E M F p).d ((ComplexShape.up ℕ).prev q) q y =
          (dolbeaultComplexXIso p q).inv φ :=
  (dolbeaultComplex E M F p).moduleCat_mem_iff_exists_d_eq_inv
    (V := fun q ↦ (ofComplexManifold E M).typeForms F p q) (e := dolbeaultComplexXIso p)
    (exactTypeForms E M F p) (fun q ↦ (ofComplexManifold E M).delBarTypeForms F p q)
    (dolbeaultComplex_d p)
    (exactTypeForms_zero p) (exactTypeForms_succ p) q φ

variable (E M F) in
/-- The identification of the `∂bar`-closed forms of type `(p,q)` with the corresponding subspace
of the forms of type `(p,q)`. -/
private def closedTypeFormsEquiv (p q : ℕ) :
    closedTypeForms E M F p q ≃ₗ[ℂ] (ofComplexManifold E M).delBarClosedForms F p q :=
  Submodule.comapSubtypeEquivOfLe ((ofComplexManifold E M).delBarClosedForms_le_typeForms F p q)

namespace dolbeaultCohomology

/-- The Dolbeault cohomology class of a `∂bar`-closed form of type `(p,q)`. -/
def mk (p q : ℕ) :
    (ofComplexManifold E M).delBarClosedForms F p q →ₗ[ℂ] dolbeaultCohomology E M F p q :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso
    (fun q ↦ (ofComplexManifold E M).typeForms F p q) (closedTypeForms E M F p)
    (dolbeaultComplexXIso p) (mem_closedTypeForms_iff_d_eq_zero p) q ∘ₗ
    (closedTypeFormsEquiv E M F p q).symm.toLinearMap

/-- Every Dolbeault cohomology class is represented by a `∂bar`-closed form. -/
theorem mk_surjective (p q : ℕ) : Function.Surjective (mk (E := E) (M := M) (F := F) p q) := by
  rw [mk, LinearMap.coe_comp]
  exact ((dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_surjective
    (fun q ↦ (ofComplexManifold E M).typeForms F p q) (closedTypeForms E M F p)
    (dolbeaultComplexXIso p) (mem_closedTypeForms_iff_d_eq_zero p) q).comp
    (closedTypeFormsEquiv E M F p q).symm.surjective

/-- A `∂bar`-closed form represents zero in Dolbeault cohomology exactly when it is
`∂bar`-exact. -/
@[simp]
theorem mk_eq_zero_iff (p q : ℕ) (φ : (ofComplexManifold E M).delBarClosedForms F p q) :
    mk p q φ = 0 ↔ φ.1 ∈ (ofComplexManifold E M).delBarExactForms F p q :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun q ↦ (ofComplexManifold E M).typeForms F p q) (closedTypeForms E M F p)
    (exactTypeForms E M F p) (dolbeaultComplexXIso p) (mem_closedTypeForms_iff_d_eq_zero p)
    (mem_exactTypeForms_iff_exists_d_eq p) q _

/-- Two `∂bar`-closed forms represent the same Dolbeault cohomology class exactly when their
difference is `∂bar`-exact. -/
theorem mk_eq_mk_iff (p q : ℕ) (φ ψ : (ofComplexManifold E M).delBarClosedForms F p q) :
    mk p q φ = mk p q ψ ↔ φ.1 - ψ.1 ∈ (ofComplexManifold E M).delBarExactForms F p q :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_eq_iff
    (fun q ↦ (ofComplexManifold E M).typeForms F p q) (closedTypeForms E M F p)
    (exactTypeForms E M F p) (dolbeaultComplexXIso p) (mem_closedTypeForms_iff_d_eq_zero p)
    (mem_exactTypeForms_iff_exists_d_eq p) q _ _

/-- The kernel of the class map consists exactly of the `∂bar`-exact forms. -/
theorem ker_mk (p q : ℕ) :
    LinearMap.ker (mk (E := E) (M := M) (F := F) p q) =
      ((ofComplexManifold E M).delBarExactForms F p q).comap
        ((ofComplexManifold E M).delBarClosedForms F p q).subtype := by
  ext φ
  exact mk_eq_zero_iff p q φ

/-! ### Holomorphic `p`-forms -/

/-- **`H^(p,0)` is the space of holomorphic `p`-forms.** The class map identifies the
`∂bar`-closed forms of type `(p,0)` with the Dolbeault cohomology `H^(p,0)_∂bar(M; F)`. -/
def mkZeroEquiv (p : ℕ) :
    (ofComplexManifold E M).delBarClosedForms F p 0 ≃ₗ[ℂ] dolbeaultCohomology E M F p 0 :=
  LinearEquiv.ofBijective (mk p 0)
    ⟨fun φ ψ h ↦ by
      rw [mk_eq_mk_iff, delBarExactForms_zero, Submodule.mem_bot, sub_eq_zero] at h
      exact Subtype.ext h,
      mk_surjective p 0⟩

/-- The identification of `H^(p,0)` with the `∂bar`-closed forms of type `(p,0)` is the class
map. -/
@[simp]
theorem mkZeroEquiv_apply (p : ℕ) (φ : (ofComplexManifold E M).delBarClosedForms F p 0) :
    mkZeroEquiv p φ = mk p 0 φ :=
  (rfl)

variable [FiniteDimensional ℂ E] [CompleteSpace F]

variable (E M F) in
/-- **`H^(0,0)` is the space of holomorphic functions.** On a complex manifold with
finite-dimensional model, the Dolbeault cohomology `H^(0,0)_∂bar(M; F)` is the space of holomorphic
functions `M → F`, the complex `C^∞` maps. -/
def zeroZeroEquiv : dolbeaultCohomology E M F 0 0 ≃ₗ[ℂ] C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ, F), F⟯ :=
  (mkZeroEquiv 0).symm ≪≫ₗ
    LinearEquiv.ofEq _ _ ((ofComplexManifold E M).delBarClosedForms_zero_zero F) ≪≫ₗ
      kerDelBarZeroEquiv E M F

/-- The holomorphic function of the class of a `∂bar`-closed function is the function itself. -/
@[simp]
theorem zeroZeroEquiv_mk (φ : (ofComplexManifold E M).delBarClosedForms F 0 0) (x : M) :
    zeroZeroEquiv E M F (mk 0 0 φ) x = φ.1.1 x 0 := by
  rw [zeroZeroEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← mkZeroEquiv_apply,
    LinearEquiv.symm_apply_apply, kerDelBarZeroEquiv_apply, LinearEquiv.coe_ofEq_apply]

end dolbeaultCohomology

/-! ### Functoriality -/

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E') ∞ M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace E'' M''] [IsManifold 𝓘(ℂ, E'') ∞ M'']

namespace dolbeaultCohomology

/-- Pullback followed by the class map kills the `∂bar`-exact forms. -/
private theorem ker_mk_le_ker_mk_comp_mpullbackDelBarClosedForms {f : M → M'}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ) :
    LinearMap.ker (mk (E := E') (M := M') (F := F) p q) ≤
      LinearMap.ker ((mk p q).comp (mpullbackDelBarClosedForms F hf hJ p q)) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  rw [LinearMap.mem_ker, LinearMap.comp_apply, mk_eq_zero_iff, coe_mpullbackDelBarClosedForms]
  exact mpullback_mem_delBarExactForms hf hJ hφ

/-- The complex-linear map on Dolbeault cohomology induced by a holomorphic map `f`, given as a
smooth map of the underlying real manifolds whose differential is complex-linear: it pulls back
classes along `f`. -/
def map {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ) :
    dolbeaultCohomology E' M' F p q →ₗ[ℂ] dolbeaultCohomology E M F p q :=
  LinearMap.liftOfSurjective (M := (ofComplexManifold E' M').delBarClosedForms F p q)
    (M₂ := dolbeaultCohomology E' M' F p q) (M₃ := dolbeaultCohomology E M F p q) (f := mk p q)
    (mk_surjective p q)
    ⟨(mk p q).comp (mpullbackDelBarClosedForms F hf hJ p q),
      ker_mk_le_ker_mk_comp_mpullbackDelBarClosedForms hf hJ p q⟩

/-- The map induced by a holomorphic map sends the class of a `∂bar`-closed form to the class of
its pullback. -/
@[simp]
theorem map_mk {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ)
    (φ : (ofComplexManifold E' M').delBarClosedForms F p q) :
    map hf hJ p q (mk p q φ) = mk p q (mpullbackDelBarClosedForms F hf hJ p q φ) :=
  LinearMap.equivOfSurjective_apply _ _

/-- The map on Dolbeault cohomology induced by the identity is the identity. -/
@[simp]
theorem map_id (p q : ℕ) :
    map (F := F) (f := id) contMDiff_id (isPseudoholomorphic_id (ofComplexManifold E M)) p q =
      LinearMap.id := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective p q c
  rw [map_mk, mpullbackDelBarClosedForms_id, LinearMap.id_apply, LinearMap.id_apply]

/-- The maps on Dolbeault cohomology induced by holomorphic maps reverse composition. -/
theorem map_comp {f : M → M'} {g : M' → M''} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f)
    (hg : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E'') ∞ g)
    (hJ' : IsPseudoholomorphic (ofComplexManifold E' M') (ofComplexManifold E'' M'') g)
    (p q : ℕ) :
    map (F := F) (hg.comp hf) (hJ'.comp hJ) p q = map hf hJ p q ∘ₗ map hg hJ' p q := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective p q c
  rw [LinearMap.comp_apply, map_mk, map_mk, map_mk, mpullbackDelBarClosedForms_comp hf hJ hg hJ',
    LinearMap.comp_apply]

end dolbeaultCohomology

end Pullback

end ComplexManifold

end TauCeti
