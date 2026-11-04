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
space. The complex-valued smooth `(p+q)`-forms of type `(p,q)` form a complex subspace
`J.typeForms F p q`, the range of the type projection. The operator `∂bar` maps forms of type
`(p,q)` to forms of type `(p,q+1)`, so it restricts to a complex-linear map
`J.delBarTypeForms F p q` between these subspaces. The `∂bar`-closed forms of type `(p,q)`,
`J.delBarClosedForms F p q`, are the forms of type `(p,q)` killed by `∂bar`; the `∂bar`-exact
forms of type `(p,q)`, `J.delBarExactForms F p q`, are the images under `∂bar` of the forms of type
`(p,q-1)`, and zero when `q = 0`. Pullback along a smooth pseudoholomorphic map preserves all three
subspaces.

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

* `TauCeti.SmoothAlmostComplexStructure.typeForms`: the smooth forms of type `(p,q)`.
* `TauCeti.SmoothAlmostComplexStructure.delBarTypeForms`: `∂bar` on forms of type `(p,q)`.
* `TauCeti.SmoothAlmostComplexStructure.delBarClosedForms`,
  `TauCeti.SmoothAlmostComplexStructure.delBarExactForms`: `∂bar`-closed and `∂bar`-exact forms.
* `TauCeti.SmoothAlmostComplexStructure.mpullbackDelBarClosedForms`: pullback of `∂bar`-closed
  forms along a smooth pseudoholomorphic map.
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

/-! ### Forms of type `(p,q)` and `∂bar` on an almost complex manifold -/

namespace SmoothAlmostComplexStructure

section AlmostComplex

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M)
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] {p q : ℕ}

/-- The complex subspace of complex-valued smooth `(p+q)`-forms of type `(p,q)` for `J`. -/
def typeForms (p q : ℕ) : Submodule ℂ (SmoothForm I M F (p + q)) where
  carrier := {φ | φ.IsOfType J p q}
  add_mem' := SmoothForm.IsOfType.add
  zero_mem' := SmoothForm.isOfType_zero_iff.2 rfl
  smul_mem' c _ h := h.smul c

variable {J F}

/-- A smooth form lies in `J.typeForms F p q` exactly when it has type `(p,q)`. -/
@[simp]
theorem mem_typeForms {φ : SmoothForm I M F (p + q)} :
    φ ∈ J.typeForms F p q ↔ φ.IsOfType J p q :=
  Iff.rfl

variable (J F)

/-- The forms of type `(p,q)` are the range of the type projection onto them. -/
theorem range_typeProjection (p q : ℕ) :
    LinearMap.range (J.typeProjection (F := F) (k := p + q) p q) = J.typeForms F p q := by
  ext φ
  refine ⟨?_, fun h ↦ ⟨φ, (mem_typeForms.1 h).typeProjection_self⟩⟩
  rintro ⟨ψ, rfl⟩
  exact J.isOfType_typeProjection rfl ψ

/-- The operator `∂bar` on smooth forms of type `(p,q)`, with values in the forms of type
`(p,q+1)`. -/
def delBarTypeForms (p q : ℕ) : J.typeForms F p q →ₗ[ℂ] J.typeForms F p (q + 1) :=
  (J.delBar.domRestrict (J.typeForms F p q)).codRestrict (J.typeForms F p (q + 1))
    fun φ ↦ (mem_typeForms.1 φ.2).delBar

/-- `∂bar` on forms of type `(p,q)` is `∂bar` of the underlying smooth forms. -/
@[simp]
theorem coe_delBarTypeForms (φ : J.typeForms F p q) :
    (J.delBarTypeForms F p q φ : SmoothForm I M F (p + (q + 1))) = J.delBar φ.1 :=
  (rfl)

/-- The complex subspace of `∂bar`-closed smooth forms of type `(p,q)`. -/
def delBarClosedForms (p q : ℕ) : Submodule ℂ (SmoothForm I M F (p + q)) :=
  J.typeForms F p q ⊓ LinearMap.ker J.delBar

variable {J F}

/-- A smooth form is a `∂bar`-closed form of type `(p,q)` exactly when it has type `(p,q)` and
its `∂bar` vanishes. -/
@[simp]
theorem mem_delBarClosedForms {φ : SmoothForm I M F (p + q)} :
    φ ∈ J.delBarClosedForms F p q ↔ φ.IsOfType J p q ∧ J.delBar φ = 0 :=
  Submodule.mem_inf

variable (J F)

/-- Every `∂bar`-closed form of type `(p,q)` has type `(p,q)`. -/
theorem delBarClosedForms_le_typeForms (p q : ℕ) : J.delBarClosedForms F p q ≤ J.typeForms F p q :=
  inf_le_left

/-- The `∂bar`-exact smooth forms of type `(p,q)`: the images under `∂bar` of the forms of type
`(p,q-1)` when `q` is positive, and zero when `q = 0`. -/
def delBarExactForms (p : ℕ) : (q : ℕ) → Submodule ℂ (SmoothForm I M F (p + q))
  | 0 => ⊥
  | q + 1 => (J.typeForms F p q).map J.delBar

/-- There are no nonzero `∂bar`-exact forms of type `(p,0)`. -/
@[simp]
theorem delBarExactForms_zero (p : ℕ) : J.delBarExactForms F p 0 = ⊥ :=
  (rfl)

/-- The `∂bar`-exact forms of type `(p,q+1)` are the images under `∂bar` of the forms of type
`(p,q)`. -/
theorem delBarExactForms_succ (p q : ℕ) :
    J.delBarExactForms F p (q + 1) = (J.typeForms F p q).map J.delBar :=
  (rfl)

variable {J F}

/-- A smooth form is a `∂bar`-exact form of type `(p,q+1)` exactly when it is `∂bar` of a form of
type `(p,q)`. -/
@[simp]
theorem mem_delBarExactForms_succ {φ : SmoothForm I M F (p + (q + 1))} :
    φ ∈ J.delBarExactForms F p (q + 1) ↔ ∃ ψ : SmoothForm I M F (p + q),
      ψ.IsOfType J p q ∧ J.delBar ψ = φ :=
  Iff.rfl

variable (J F)

/-- Every smooth function is a form of type `(0,0)`. -/
@[simp]
theorem typeForms_zero_zero : J.typeForms F 0 0 = ⊤ :=
  eq_top_iff.2 fun φ _ ↦ SmoothForm.isOfType_zero_zero φ J

/-- The `∂bar`-closed forms of type `(0,0)` are the smooth functions killed by `∂bar`. -/
theorem delBarClosedForms_zero_zero :
    J.delBarClosedForms F 0 0 = LinearMap.ker (J.delBar (F := F) (k := 0)) := by
  rw [delBarClosedForms, typeForms_zero_zero, top_inf_eq]

/-! ### Pullback along pseudoholomorphic maps -/

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {J' : SmoothAlmostComplexStructure I' M'} {u : M → M'}

variable {J F}

/-- Pullback along a smooth pseudoholomorphic map preserves `∂bar`-closed forms of type
`(p,q)`. -/
theorem mpullback_mem_delBarClosedForms (hu : ContMDiff I I' ∞ u)
    (hJ : IsPseudoholomorphic J J' u) {φ : SmoothForm I' M' F (p + q)}
    (hφ : φ ∈ J'.delBarClosedForms F p q) :
    SmoothForm.mpullback u hu φ ∈ J.delBarClosedForms F p q := by
  rw [mem_delBarClosedForms] at hφ ⊢
  exact ⟨hφ.1.mpullback hu hJ, by rw [← mpullback_delBar J hu hJ, hφ.2, map_zero]⟩

/-- Pullback along a smooth pseudoholomorphic map preserves `∂bar`-exact forms of type
`(p,q)`. -/
theorem mpullback_mem_delBarExactForms (hu : ContMDiff I I' ∞ u)
    (hJ : IsPseudoholomorphic J J' u) {φ : SmoothForm I' M' F (p + q)}
    (hφ : φ ∈ J'.delBarExactForms F p q) :
    SmoothForm.mpullback u hu φ ∈ J.delBarExactForms F p q := by
  cases q with
  | zero =>
    rw [delBarExactForms_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ q =>
    obtain ⟨ψ, hψ, rfl⟩ := mem_delBarExactForms_succ.1 hφ
    exact mem_delBarExactForms_succ.2
      ⟨SmoothForm.mpullback u hu ψ, hψ.mpullback hu hJ, (mpullback_delBar J hu hJ ψ).symm⟩

variable (F) in
/-- Pullback of `∂bar`-closed forms of type `(p,q)` along a smooth pseudoholomorphic map, as a
complex-linear map. -/
def mpullbackDelBarClosedForms (hu : ContMDiff I I' ∞ u) (hJ : IsPseudoholomorphic J J' u)
    (p q : ℕ) : J'.delBarClosedForms F p q →ₗ[ℂ] J.delBarClosedForms F p q where
  toFun φ := ⟨SmoothForm.mpullback u hu φ.1, mpullback_mem_delBarClosedForms hu hJ φ.2⟩
  map_add' φ ψ := Subtype.ext (map_add _ φ.1 ψ.1)
  map_smul' c φ := Subtype.ext (SmoothForm.mpullback_smul u hu c φ.1)

/-- The underlying form of the pullback of a `∂bar`-closed form is its pullback. -/
@[simp]
theorem coe_mpullbackDelBarClosedForms (hu : ContMDiff I I' ∞ u)
    (hJ : IsPseudoholomorphic J J' u) (φ : J'.delBarClosedForms F p q) :
    (mpullbackDelBarClosedForms F hu hJ p q φ : SmoothForm I M F (p + q)) =
      SmoothForm.mpullback u hu φ.1 :=
  (rfl)

/-- Pullback of `∂bar`-closed forms along the identity is the identity. -/
@[simp]
theorem mpullbackDelBarClosedForms_id :
    mpullbackDelBarClosedForms F contMDiff_id (isPseudoholomorphic_id J) p q = LinearMap.id :=
  LinearMap.ext fun φ ↦ Subtype.ext <| LinearMap.congr_fun SmoothForm.mpullback_id φ.1

/-- Pullback of `∂bar`-closed forms reverses composition. -/
theorem mpullbackDelBarClosedForms_comp {E'' H'' M'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' ∞ M'']
    {J'' : SmoothAlmostComplexStructure I'' M''} {v : M' → M''} (hu : ContMDiff I I' ∞ u)
    (hJ : IsPseudoholomorphic J J' u) (hv : ContMDiff I' I'' ∞ v)
    (hJ' : IsPseudoholomorphic J' J'' v) :
    mpullbackDelBarClosedForms F (hv.comp hu) (hJ'.comp hJ) p q =
      mpullbackDelBarClosedForms F hu hJ p q ∘ₗ mpullbackDelBarClosedForms F hv hJ' p q :=
  LinearMap.ext fun φ ↦ Subtype.ext <| LinearMap.congr_fun (SmoothForm.mpullback_comp u v hu hv) φ.1

end Pullback

end AlmostComplex

end SmoothAlmostComplexStructure

/-! ### The Dolbeault complex of a complex manifold -/

open SmoothAlmostComplexStructure

section ComplexManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On a complex manifold, `∂bar` on forms of type `(p,q)` and on forms of type `(p,q+1)` compose
to zero. -/
theorem delBarTypeForms_comp_delBarTypeForms_ofComplexManifold (p q : ℕ) :
    (ofComplexManifold E M).delBarTypeForms F p (q + 1) ∘ₗ
      (ofComplexManifold E M).delBarTypeForms F p q = 0 :=
  LinearMap.ext fun φ ↦ Subtype.ext (delBar_delBar_ofComplexManifold φ.1)

/-- On a complex manifold, every `∂bar`-exact form of type `(p,q)` is `∂bar`-closed. -/
theorem delBarExactForms_le_delBarClosedForms_ofComplexManifold (p q : ℕ) :
    (ofComplexManifold E M).delBarExactForms F p q ≤
      (ofComplexManifold E M).delBarClosedForms F p q := by
  intro φ hφ
  cases q with
  | zero =>
    rw [delBarExactForms_zero, Submodule.mem_bot] at hφ
    rw [hφ]
    exact zero_mem _
  | succ q =>
    obtain ⟨ψ, hψ, rfl⟩ := mem_delBarExactForms_succ.1 hφ
    exact mem_delBarClosedForms.2 ⟨hψ.delBar, delBar_delBar_ofComplexManifold ψ⟩

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

/-- Under the canonical identifications of the objects, the differential of the Dolbeault complex
is `∂bar`, in the form used to transport equations out of the complex. -/
private theorem dolbeaultComplexXIso_hom_d_apply (p q : ℕ) (x : (dolbeaultComplex E M F p).X q) :
    (dolbeaultComplexXIso p (q + 1)).hom ((dolbeaultComplex E M F p).d q (q + 1) x) =
      (ofComplexManifold E M).delBarTypeForms F p q ((dolbeaultComplexXIso p q).hom x) := by
  rw [dolbeaultComplex_d_apply, Iso.inv_hom_id_apply]

/-- The canonical identification of a term of the Dolbeault complex is injective. -/
private theorem dolbeaultComplexXIso_hom_injective (p q : ℕ) :
    Function.Injective (dolbeaultComplexXIso (E := E) (M := M) (F := F) p q).hom := fun a b h ↦ by
  simpa using congrArg (dolbeaultComplexXIso (E := E) (M := M) (F := F) p q).inv h

variable (E M F) in
/-- A `∂bar`-closed form of type `(p,q)`, regarded as an element in degree `q` of the Dolbeault
complex. -/
private def closedToComplex (p q : ℕ) :
    (ofComplexManifold E M).delBarClosedForms F p q →ₗ[ℂ] (dolbeaultComplex E M F p).X q :=
  (dolbeaultComplexXIso p q).inv.hom ∘ₗ
    Submodule.inclusion (delBarClosedForms_le_typeForms (ofComplexManifold E M) F p q)

/-- A `∂bar`-closed form, regarded in the Dolbeault complex, is the form itself under the
canonical identification. -/
private theorem dolbeaultComplexXIso_hom_closedToComplex (p q : ℕ)
    (φ : (ofComplexManifold E M).delBarClosedForms F p q) :
    (dolbeaultComplexXIso p q).hom (closedToComplex E M F p q φ) =
      Submodule.inclusion (delBarClosedForms_le_typeForms (ofComplexManifold E M) F p q) φ := by
  rw [closedToComplex, LinearMap.comp_apply]
  exact Iso.inv_hom_id_apply _ _

/-- A `∂bar`-closed form vanishes in the Dolbeault complex exactly when it is zero. -/
private theorem closedToComplex_eq_zero_iff (p q : ℕ)
    (φ : (ofComplexManifold E M).delBarClosedForms F p q) :
    closedToComplex E M F p q φ = 0 ↔ φ.1 = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [(Submodule.coe_eq_zero (x := φ)).1 h, map_zero]⟩
  have h' := congrArg (dolbeaultComplexXIso (E := E) (M := M) (F := F) p q).hom h
  rw [dolbeaultComplexXIso_hom_closedToComplex, map_zero] at h'
  exact congrArg Subtype.val h'

variable (E M F) in
/-- A `∂bar`-closed form of type `(p,q)`, regarded in degree `q` of the Dolbeault complex, is
killed by its differential. -/
private theorem dolbeaultComplex_d_closedToComplex (p q : ℕ)
    (φ : (ofComplexManifold E M).delBarClosedForms F p q) :
    (dolbeaultComplex E M F p).d q (q + 1) (closedToComplex E M F p q φ) = 0 := by
  refine dolbeaultComplexXIso_hom_injective p (q + 1) ?_
  rw [dolbeaultComplexXIso_hom_d_apply, dolbeaultComplexXIso_hom_closedToComplex, map_zero]
  exact Subtype.ext (mem_delBarClosedForms.1 φ.2).2

namespace dolbeaultCohomology

/-- The Dolbeault cohomology class of a `∂bar`-closed form of type `(p,q)`. -/
def mk (p q : ℕ) :
    (ofComplexManifold E M).delBarClosedForms F p q →ₗ[ℂ] dolbeaultCohomology E M F p q :=
  (dolbeaultComplex E M F p).moduleCatHomologyClass (CochainComplex.next ℕ q)
    (Z := (ofComplexManifold E M).delBarClosedForms F p q)
    (closedToComplex E M F p q) (dolbeaultComplex_d_closedToComplex E M F p q)

/-- Every Dolbeault cohomology class is represented by a `∂bar`-closed form. -/
theorem mk_surjective (p q : ℕ) : Function.Surjective (mk (E := E) (M := M) (F := F) p q) := by
  rw [mk]
  refine (dolbeaultComplex E M F p).moduleCatHomologyClass_surjective _
    (Z := (ofComplexManifold E M).delBarClosedForms F p q) (closedToComplex E M F p q)
    (dolbeaultComplex_d_closedToComplex E M F p q) fun x hx ↦ ?_
  set y := (dolbeaultComplexXIso (E := E) (M := M) (F := F) p q).hom x with hy
  have hdy : (ofComplexManifold E M).delBarTypeForms F p q y = 0 := by
    rw [hy, ← dolbeaultComplexXIso_hom_d_apply, hx, map_zero]
  refine ⟨⟨y.1, mem_delBarClosedForms.2 ⟨y.2, by simpa using congrArg Subtype.val hdy⟩⟩,
    dolbeaultComplexXIso_hom_injective p q ?_⟩
  rw [dolbeaultComplexXIso_hom_closedToComplex]
  rfl

/-- A `∂bar`-closed form represents zero in Dolbeault cohomology exactly when it is
`∂bar`-exact. -/
@[simp]
theorem mk_eq_zero_iff (p q : ℕ) (φ : (ofComplexManifold E M).delBarClosedForms F p q) :
    mk p q φ = 0 ↔ φ.1 ∈ (ofComplexManifold E M).delBarExactForms F p q := by
  cases q with
  | zero =>
    rw [mk, (dolbeaultComplex E M F p).moduleCatHomologyClass_eq_zero_iff _
        (Z := (ofComplexManifold E M).delBarClosedForms F p 0) (closedToComplex E M F p 0)
        (dolbeaultComplex_d_closedToComplex E M F p 0) CochainComplex.prev_nat_zero,
      delBarExactForms_zero, Submodule.mem_bot, (dolbeaultComplex E M F p).shape 0 0 (by simp)]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const]
    rw [eq_comm, closedToComplex_eq_zero_iff]
  | succ q =>
    rw [mk, (dolbeaultComplex E M F p).moduleCatHomologyClass_eq_zero_iff _
        (Z := (ofComplexManifold E M).delBarClosedForms F p (q + 1))
        (closedToComplex E M F p (q + 1)) (dolbeaultComplex_d_closedToComplex E M F p (q + 1))
        (CochainComplex.prev_nat_succ q), mem_delBarExactForms_succ]
    constructor
    · rintro ⟨y, hy⟩
      have h := congrArg (dolbeaultComplexXIso (E := E) (M := M) (F := F) p (q + 1)).hom hy
      rw [dolbeaultComplexXIso_hom_d_apply, dolbeaultComplexXIso_hom_closedToComplex] at h
      exact ⟨_, ((dolbeaultComplexXIso p q).hom y).2, by simpa using congrArg Subtype.val h⟩
    · rintro ⟨ψ, hψ, hψφ⟩
      refine ⟨(dolbeaultComplexXIso p q).inv ⟨ψ, hψ⟩,
        dolbeaultComplexXIso_hom_injective p (q + 1) ?_⟩
      rw [dolbeaultComplexXIso_hom_d_apply, dolbeaultComplexXIso_hom_closedToComplex,
        Iso.inv_hom_id_apply]
      exact Subtype.ext hψφ

/-- Two `∂bar`-closed forms represent the same Dolbeault cohomology class exactly when their
difference is `∂bar`-exact. -/
theorem mk_eq_mk_iff (p q : ℕ) (φ ψ : (ofComplexManifold E M).delBarClosedForms F p q) :
    mk p q φ = mk p q ψ ↔ φ.1 - ψ.1 ∈ (ofComplexManifold E M).delBarExactForms F p q := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, Submodule.coe_sub]

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
  (mkZeroEquiv 0).symm ≪≫ₗ LinearEquiv.ofEq _ _ (delBarClosedForms_zero_zero _ F) ≪≫ₗ
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
  rw [LinearMap.mem_ker, LinearMap.comp_apply, mk_eq_zero_iff]
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
