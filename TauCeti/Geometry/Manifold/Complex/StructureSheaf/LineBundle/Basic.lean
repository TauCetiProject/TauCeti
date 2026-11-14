/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# The sheaf of holomorphic sections of a holomorphic vector bundle

Let `V` be a complex vector bundle with model fibre `F` over a complex manifold `X` with model
`I`. Its sheaf of holomorphic sections assigns to an open set `U` the complex vector space of
sections `s : (x : U) → V x` whose bundled map `x ↦ ⟨x, s x⟩` into the total space is complex
analytic. When the coordinate changes of `V` are holomorphic (Mathlib's
`ContMDiffVectorBundle ω F V I`), this is the sheaf of sections of the holomorphic bundle `V`; for
`F = ℂ` it is the sheaf of sections of a holomorphic line bundle `L`, the sheaf `𝒪(L)` of
Forster's *Lectures on Riemann Surfaces*, §29. The construction itself needs only a vector bundle
structure on `V`: sums and scalar multiples of analytic sections are analytic by Mathlib's
`ContMDiffAt.add_section` and `ContMDiffAt.const_smul_section`.

The underlying sheaf of types is Mathlib's `TopCat.subsheafToTypes` for the local predicate
`TauCeti.holomorphicSectionLocalPredicate`. Analyticity of the bundled map is local, by Mathlib's
local predicate for `ContMDiff` maps. The sheaf of complex vector spaces has exactly this
underlying presheaf of types, which gives its sheaf condition, as for
`TauCeti.holomorphicStructureSheafModules`.

## Main definitions

* `TauCeti.holomorphicBundleSections`: the holomorphic sections of `V` over an open set, as a
  complex subspace of all sections.
* `TauCeti.holomorphicSectionSheaf`: the sheaf of holomorphic sections, as a
  `TopCat.Sheaf (ModuleCat ℂ)`.
* `TauCeti.holomorphicSectionSheaf.homOfLinearMap`: the sheaf morphism induced by a fibrewise
  linear map whose total-space map is analytic.
* `TauCeti.holomorphicSectionSheaf.isoOfLinearEquiv`: the sheaf isomorphism induced by an
  isomorphism of holomorphic vector bundles.
* `TauCeti.holomorphicSectionSheaf.trivialIso`: the sheaf of the trivial line bundle is the
  holomorphic structure sheaf `TauCeti.holomorphicStructureSheafModules`.
* `TauCeti.holomorphicSectionSheaf.prodFst`, `prodSnd`, `prodInl`, `prodInr` and
  `TauCeti.holomorphicSectionSheaf.prodBicone`: the projections and inclusions of a direct sum
  `V₁ ×ᵇ V₂` on sheaves of sections.

## Main results

* `TauCeti.holomorphicSectionSheaf.existsUnique_gluing`: holomorphic sections that agree on
  overlaps glue uniquely; restriction is `TauCeti.holomorphicSectionSheaf.map_apply`.
* `TauCeti.holomorphicSectionSheaf.prodBiconeIsBilimit`: the sheaf of sections of a direct sum
  `V₁ ×ᵇ V₂` is the biproduct of the two sheaves of sections.
* `TauCeti.holomorphicSectionSheaf.prodIso`: the resulting isomorphism with `⊞`. Finite direct
  sums are iterated binary ones.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §29.
-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
  (V : X → Type) [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V]

/-- Analyticity of the bundled map `x ↦ ⟨x, s x⟩` into the total space, as a local predicate on
sections of `V` over open sets. -/
def holomorphicSectionLocalPredicate : TopCat.LocalPredicate (fun x : TopCat.of X ↦ V x) where
  pred {U} s := ContMDiff I (I.prod 𝓘(ℂ, F)) ω (fun x : U ↦ TotalSpace.mk' F (x : X) (s x))
  res {_ _} i _ h :=
    ((contDiffWithinAt_localInvariantProp (I := I) (I' := I.prod 𝓘(ℂ, F)) ω).localPredicate
      X (TotalSpace F V)).res i _ h
  locality {_} _ w :=
    ((contDiffWithinAt_localInvariantProp (I := I) (I' := I.prod 𝓘(ℂ, F)) ω).localPredicate
      X (TotalSpace F V)).locality _ w

@[simp]
theorem holomorphicSectionLocalPredicate_pred {U : Opens (TopCat.of X)} (s : (x : U) → V x) :
    (holomorphicSectionLocalPredicate I F V).pred s ↔
      ContMDiff I (I.prod 𝓘(ℂ, F)) ω (fun x : U ↦ TotalSpace.mk' F (x : X) (s x)) :=
  Iff.rfl

variable [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V]

/-- Extension by zero of a section over an open set, used to apply Mathlib's lemmas about
sections defined on all of `X`. -/
private def extendSection {U : Opens X} (s : (x : U) → V x) : (x : X) → V x :=
  open Classical in fun x ↦ if h : x ∈ U then s ⟨x, h⟩ else 0

omit [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] in
private theorem mk_extendSection {U : Opens X} (s : (x : U) → V x) :
    (fun x : U ↦ TotalSpace.mk' F (x : X) (s x)) =
      fun x : U ↦ TotalSpace.mk' F (x : X) (extendSection V s x) := by
  funext x
  simp [extendSection, x.2]

omit [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] in
/-- A section over an open set is analytic exactly when its extension by zero is analytic at
every point of the open set. -/
private theorem contMDiff_mk_iff {U : Opens X} (s : (x : U) → V x) :
    ContMDiff I (I.prod 𝓘(ℂ, F)) ω (fun x : U ↦ TotalSpace.mk' F (x : X) (s x)) ↔
      ∀ x : U, ContMDiffAt I (I.prod 𝓘(ℂ, F)) ω
        (fun y : X ↦ TotalSpace.mk' F y (extendSection V s y)) x := by
  rw [mk_extendSection]
  exact forall_congr' fun x ↦
    contMDiffAt_subtype_iff (f := fun y : X ↦ TotalSpace.mk' F y (extendSection V s y))

/-- The holomorphic sections of `V` over an open set `U`, as a complex subspace of all sections:
those whose bundled map into the total space is complex analytic. -/
def holomorphicBundleSections (U : Opens X) : Submodule ℂ ((x : U) → V x) where
  carrier := {s | ContMDiff I (I.prod 𝓘(ℂ, F)) ω (fun x : U ↦ TotalSpace.mk' F (x : X) (s x))}
  zero_mem' := (contMDiff_zeroSection ℂ V).comp contMDiff_subtype_val
  add_mem' {s t} hs ht := by
    refine (contMDiff_mk_iff I F V _).2 fun x ↦ ?_
    refine (((contMDiff_mk_iff I F V s).1 hs x).add_section
      ((contMDiff_mk_iff I F V t).1 ht x)).congr_of_eventuallyEq ?_
    filter_upwards [U.isOpen.mem_nhds x.2] with y (hy : y ∈ U)
    simp [extendSection, hy]
  smul_mem' c s hs := by
    refine (contMDiff_mk_iff I F V _).2 fun x ↦ ?_
    refine (((contMDiff_mk_iff I F V s).1 hs x).const_smul_section (a := c)).congr_of_eventuallyEq
      ?_
    filter_upwards [U.isOpen.mem_nhds x.2] with y (hy : y ∈ U)
    simp [extendSection, hy]

theorem mem_holomorphicBundleSections_iff {U : Opens X} {s : (x : U) → V x} :
    s ∈ holomorphicBundleSections I F V U ↔
      ContMDiff I (I.prod 𝓘(ℂ, F)) ω (fun x : U ↦ TotalSpace.mk' F (x : X) (s x)) :=
  Iff.rfl

/-- The sheaf of holomorphic sections of a vector bundle `V` over a complex manifold, as a sheaf
of complex vector spaces. Its sections over `U` are the sections of `V` over `U` whose bundled
map into the total space is complex analytic. -/
def holomorphicSectionSheaf : TopCat.Sheaf (ModuleCat ℂ) (TopCat.of X) where
  obj :=
    { obj := fun U ↦ ModuleCat.of ℂ (holomorphicBundleSections I F V (unop U))
      map := fun h ↦ ModuleCat.ofHom
        { toFun := (TopCat.subsheafToTypes (holomorphicSectionLocalPredicate I F V)).obj.map h
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat ℂ))]
    exact (TopCat.subsheafToTypes (holomorphicSectionLocalPredicate I F V)).property

namespace holomorphicSectionSheaf

/-- Sections of the sheaf are the holomorphic sections of `V` over the open set. -/
theorem obj_eq (U : (Opens (TopCat.of X))ᵒᵖ) :
    (holomorphicSectionSheaf I F V).obj.obj U =
      ModuleCat.of ℂ (holomorphicBundleSections I F V (unop U)) := (rfl)

/-- The section of `V` underlying a section of the sheaf. -/
def toFun {U : (Opens (TopCat.of X))ᵒᵖ} (s : (holomorphicSectionSheaf I F V).obj.obj U) :
    (x : ↥(unop U)) → V x :=
  Subtype.val (p := (· ∈ holomorphicBundleSections I F V (unop U))) s

instance (U : (Opens (TopCat.of X))ᵒᵖ) :
    CoeFun ((holomorphicSectionSheaf I F V).obj.obj U) (fun _ ↦ (x : ↥(unop U)) → V x) where
  coe := toFun I F V

variable {I F V}

/-- Sections of the sheaf are equal if they agree at every point. -/
@[ext]
theorem ext {U : (Opens (TopCat.of X))ᵒᵖ} {s t : (holomorphicSectionSheaf I F V).obj.obj U}
    (h : ∀ x, s x = t x) : s = t :=
  Subtype.ext (funext h)

/-- The bundled map of a section of the sheaf into the total space is complex analytic. -/
theorem contMDiff {U : (Opens (TopCat.of X))ᵒᵖ} (s : (holomorphicSectionSheaf I F V).obj.obj U) :
    ContMDiff I (I.prod 𝓘(ℂ, F)) ω (fun x : ↥(unop U) ↦ TotalSpace.mk' F (x : X) (s x)) :=
  s.2

/-- A section of `V` over `U` whose bundled map is complex analytic, as a section of the sheaf. -/
def ofContMDiff {U : Opens X} (s : (x : U) → V x)
    (hs : ContMDiff I (I.prod 𝓘(ℂ, F)) ω (fun x : U ↦ TotalSpace.mk' F (x : X) (s x))) :
    (holomorphicSectionSheaf I F V).obj.obj (op U) :=
  ⟨s, hs⟩

@[simp]
theorem ofContMDiff_apply {U : Opens X} (s : (x : U) → V x)
    (hs : ContMDiff I (I.prod 𝓘(ℂ, F)) ω (fun x : U ↦ TotalSpace.mk' F (x : X) (s x))) (x : U) :
    ofContMDiff s hs x = s x := (rfl)

@[simp]
theorem zero_apply {U : (Opens (TopCat.of X))ᵒᵖ} (x : ↥(unop U)) :
    (0 : (holomorphicSectionSheaf I F V).obj.obj U) x = 0 := (rfl)

@[simp]
theorem add_apply {U : (Opens (TopCat.of X))ᵒᵖ} (s t : (holomorphicSectionSheaf I F V).obj.obj U)
    (x : ↥(unop U)) : (s + t) x = s x + t x := (rfl)

@[simp]
theorem neg_apply {U : (Opens (TopCat.of X))ᵒᵖ} (s : (holomorphicSectionSheaf I F V).obj.obj U)
    (x : ↥(unop U)) : (-s) x = -s x := (rfl)

@[simp]
theorem sub_apply {U : (Opens (TopCat.of X))ᵒᵖ} (s t : (holomorphicSectionSheaf I F V).obj.obj U)
    (x : ↥(unop U)) : (s - t) x = s x - t x := (rfl)

@[simp]
theorem smul_apply {U : (Opens (TopCat.of X))ᵒᵖ} (c : ℂ)
    (s : (holomorphicSectionSheaf I F V).obj.obj U) (x : ↥(unop U)) : (c • s) x = c • s x := (rfl)

/-- Restriction of sections of the sheaf restricts the underlying sections of `V`. -/
@[simp]
theorem map_apply {U W : (Opens (TopCat.of X))ᵒᵖ} (h : U ⟶ W)
    (s : (holomorphicSectionSheaf I F V).obj.obj U) (x : ↥(unop W)) :
    (holomorphicSectionSheaf I F V).obj.map h s x = s (Opens.inclusion (leOfHom h.unop) x) :=
  (rfl)

/-- **Gluing.** Holomorphic sections over the members of a family of open sets that agree on all
overlaps glue to a unique holomorphic section over the union. -/
theorem existsUnique_gluing {ι : Type} (U : ι → Opens X)
    (s : ∀ i, (holomorphicSectionSheaf I F V).obj.obj (op (U i)))
    (h : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), s i ⟨x, hi⟩ = s j ⟨x, hj⟩) :
    ∃! t : (holomorphicSectionSheaf I F V).obj.obj (op (iSup U)),
      ∀ i (x : U i), t ⟨x, le_iSup U i x.2⟩ = s i x := by
  have hc : TopCat.Presheaf.IsCompatible (holomorphicSectionSheaf I F V).obj U s :=
    fun i j ↦ ext fun x ↦ h i j x.1 _ _
  obtain ⟨t, ht, hu⟩ := (holomorphicSectionSheaf I F V).existsUnique_gluing U s hc
  refine ⟨t, fun i x ↦ congrArg (fun r ↦ toFun I F V r x) (ht i), fun t' ht' ↦ hu t' ?_⟩
  exact fun i ↦ ext fun x ↦ ht' i x

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  {V₁ : X → Type} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
  [FiberBundle F₁ V₁] [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℂ (V₁ x)] [VectorBundle ℂ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  {V₂ : X → Type} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
  [FiberBundle F₂ V₂] [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℂ (V₂ x)] [VectorBundle ℂ F₂ V₂]

/-- Two morphisms between sheaves of holomorphic sections are equal if they agree on the values
of all sections. -/
theorem hom_ext {f g : holomorphicSectionSheaf I F₁ V₁ ⟶ holomorphicSectionSheaf I F₂ V₂}
    (h : ∀ (U : (Opens (TopCat.of X))ᵒᵖ) (s : (holomorphicSectionSheaf I F₁ V₁).obj.obj U) (x),
      f.hom.app U s x = g.hom.app U s x) : f = g := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact ext (h U s)

/-- A fibrewise linear map `φ : V₁ x → V₂ x` whose total-space map is complex analytic induces a
morphism of sheaves of holomorphic sections, by `s ↦ (x ↦ φ x (s x))`. -/
def homOfLinearMap (φ : ∀ x, V₁ x →ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2))) :
    holomorphicSectionSheaf I F₁ V₁ ⟶ holomorphicSectionSheaf I F₂ V₂ where
  hom.app _ := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨fun x ↦ φ x (s.1 x), hφ.comp s.2⟩
      map_add' := fun s t ↦ Subtype.ext <| funext fun x ↦ map_add (φ x) (s.1 x) (t.1 x)
      map_smul' := fun c s ↦ Subtype.ext <| funext fun x ↦ map_smul (φ x) c (s.1 x) }
  hom.naturality _ _ _ := rfl

@[simp]
theorem homOfLinearMap_app_apply (φ : ∀ x, V₁ x →ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2)))
    {U : (Opens (TopCat.of X))ᵒᵖ} (s : (holomorphicSectionSheaf I F₁ V₁).obj.obj U)
    (x : ↥(unop U)) :
    (homOfLinearMap φ hφ).hom.app U s x = φ x (s x) := (rfl)

/-- The fibrewise identity induces the identity of the sheaf of holomorphic sections. -/
@[simp]
theorem homOfLinearMap_id
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₁)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₁ v.proj (LinearMap.id (R := ℂ) v.2))) :
    homOfLinearMap (fun _ ↦ LinearMap.id) hφ = 𝟙 (holomorphicSectionSheaf I F₁ V₁) :=
  hom_ext fun _ _ _ ↦ rfl

/-- Fibrewise composition of linear maps induces composition of sheaf morphisms. -/
@[reassoc (attr := simp)]
theorem homOfLinearMap_comp {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]
    {V₃ : X → Type} [TopologicalSpace (TotalSpace F₃ V₃)] [∀ x, TopologicalSpace (V₃ x)]
    [FiberBundle F₃ V₃] [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℂ (V₃ x)] [VectorBundle ℂ F₃ V₃]
    (φ : ∀ x, V₁ x →ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2)))
    (ψ : ∀ x, V₂ x →ₗ[ℂ] V₃ x)
    (hψ : ContMDiff (I.prod 𝓘(ℂ, F₂)) (I.prod 𝓘(ℂ, F₃)) ω
      (fun v : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₃ v.proj (ψ v.proj v.2))) :
    homOfLinearMap φ hφ ≫ homOfLinearMap ψ hψ =
      homOfLinearMap (fun x ↦ ψ x ∘ₗ φ x) (hψ.comp hφ) :=
  hom_ext fun _ _ _ ↦ rfl

/-- An isomorphism of holomorphic vector bundles, given as fibrewise linear isomorphisms whose
total-space maps in both directions are complex analytic, induces an isomorphism of the sheaves
of holomorphic sections. -/
def isoOfLinearEquiv (φ : ∀ x, V₁ x ≃ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2)))
    (hφ' : ContMDiff (I.prod 𝓘(ℂ, F₂)) (I.prod 𝓘(ℂ, F₁)) ω
      (fun v : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₁ v.proj ((φ v.proj).symm v.2))) :
    holomorphicSectionSheaf I F₁ V₁ ≅ holomorphicSectionSheaf I F₂ V₂ where
  hom := homOfLinearMap (fun x ↦ (φ x).toLinearMap) hφ
  inv := homOfLinearMap (fun x ↦ (φ x).symm.toLinearMap) hφ'
  hom_inv_id := hom_ext fun _ _ x ↦ (φ x).symm_apply_apply _
  inv_hom_id := hom_ext fun _ _ x ↦ (φ x).apply_symm_apply _

@[simp]
theorem isoOfLinearEquiv_hom_app_apply (φ : ∀ x, V₁ x ≃ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2)))
    (hφ' : ContMDiff (I.prod 𝓘(ℂ, F₂)) (I.prod 𝓘(ℂ, F₁)) ω
      (fun v : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₁ v.proj ((φ v.proj).symm v.2)))
    {U : (Opens (TopCat.of X))ᵒᵖ} (s : (holomorphicSectionSheaf I F₁ V₁).obj.obj U)
    (x : ↥(unop U)) :
    (isoOfLinearEquiv φ hφ hφ').hom.hom.app U s x = φ x (s x) := (rfl)

@[simp]
theorem isoOfLinearEquiv_inv_app_apply (φ : ∀ x, V₁ x ≃ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2)))
    (hφ' : ContMDiff (I.prod 𝓘(ℂ, F₂)) (I.prod 𝓘(ℂ, F₁)) ω
      (fun v : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₁ v.proj ((φ v.proj).symm v.2)))
    {U : (Opens (TopCat.of X))ᵒᵖ} (s : (holomorphicSectionSheaf I F₂ V₂).obj.obj U)
    (x : ↥(unop U)) :
    (isoOfLinearEquiv φ hφ hφ').inv.hom.app U s x = (φ x).symm (s x) := (rfl)

/-! ### The trivial line bundle -/

section Trivial

/-- The holomorphic sections of the trivial line bundle over `U` are the holomorphic functions on
`U`. -/
private def trivialSectionsEquiv (U : Opens X) :
    (holomorphicSectionSheaf I ℂ (Trivial X ℂ)).obj.obj (op U) ≃ₗ[ℂ]
      (holomorphicStructureSheafModules I X).obj.obj (op U) where
  toFun s := holomorphicStructureSheafModules.ofContMDiff (fun x ↦ s x)
    (Trivial.contMDiff_mk_iff.1 (contMDiff s)).2
  invFun f := ofContMDiff (fun x ↦ f x)
    (Trivial.contMDiff_mk_iff.2
      ⟨contMDiff_subtype_val, holomorphicStructureSheafModules.contMDiff f⟩)
  map_add' _ _ := holomorphicStructureSheafModules.ext fun _ ↦ by simp
  map_smul' _ _ := holomorphicStructureSheafModules.ext fun _ ↦ by simp
  left_inv _ := ext fun _ ↦ by simp
  right_inv _ := holomorphicStructureSheafModules.ext fun _ ↦ by simp

variable (I X) in
/-- The sheaf of holomorphic sections of the trivial line bundle `X × ℂ` is the holomorphic
structure sheaf, as a sheaf of complex vector spaces. -/
def trivialIso :
    holomorphicSectionSheaf I ℂ (Trivial X ℂ) ≅ holomorphicStructureSheafModules I X :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso <| NatIso.ofComponents
    (fun U ↦ (trivialSectionsEquiv U.unop).toModuleIso) fun {U W} h ↦ by
      induction U using Opposite.rec
      induction W using Opposite.rec
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      refine holomorphicStructureSheafModules.ext fun x ↦ ?_
      -- Erase the sheaf-to-presheaf and `ModuleCat` compositions, so that the evaluation lemmas
      -- of both sheaves apply.
      change trivialSectionsEquiv _ ((holomorphicSectionSheaf I ℂ (Trivial X ℂ)).obj.map h s) x =
        (holomorphicStructureSheafModules I X).obj.map h (trivialSectionsEquiv _ s) x
      simp [trivialSectionsEquiv]

-- Through the unexposed coercion of the structure sheaf, simp uses this lemma when it is given
-- its arguments, as in simp only [trivialIso_hom_app_apply s x].
/-- The isomorphism with the structure sheaf does not change the values of sections. -/
@[simp]
theorem trivialIso_hom_app_apply {U : Opens X}
    (s : (holomorphicSectionSheaf I ℂ (Trivial X ℂ)).obj.obj (op U)) (x : U) :
    (no_index (ConcreteCategory.hom ((trivialIso I X).hom.hom.app (op U)) s)) x = s x :=
  holomorphicStructureSheafModules.ofContMDiff_apply _ _ x

-- Index past the unexposed section carriers, so that simp applies the lemma.
/-- The inverse of the isomorphism with the structure sheaf does not change the values of
sections. -/
@[simp]
theorem trivialIso_inv_app_apply {U : Opens X}
    (f : (holomorphicStructureSheafModules I X).obj.obj (op U)) (x : U) :
    (no_index (ConcreteCategory.hom ((trivialIso I X).inv.hom.app (op U)) f)) x = f x := (rfl)

end Trivial

/-! ### Direct sums -/

section Prod

variable (I F₁ V₁ F₂ V₂)

/-- The projection of the sheaf of sections of a direct sum `V₁ ×ᵇ V₂` onto the first sheaf. -/
def prodFst : holomorphicSectionSheaf I (F₁ × F₂) (V₁ ×ᵇ V₂) ⟶ holomorphicSectionSheaf I F₁ V₁ :=
  homOfLinearMap (fun x ↦ LinearMap.fst ℂ (V₁ x) (V₂ x)) Bundle.Prod.contMDiff_fst

/-- The projection of the sheaf of sections of a direct sum `V₁ ×ᵇ V₂` onto the second sheaf. -/
def prodSnd : holomorphicSectionSheaf I (F₁ × F₂) (V₁ ×ᵇ V₂) ⟶ holomorphicSectionSheaf I F₂ V₂ :=
  homOfLinearMap (fun x ↦ LinearMap.snd ℂ (V₁ x) (V₂ x)) Bundle.Prod.contMDiff_snd

/-- The inclusion of the first sheaf into the sheaf of sections of a direct sum `V₁ ×ᵇ V₂`. -/
def prodInl : holomorphicSectionSheaf I F₁ V₁ ⟶ holomorphicSectionSheaf I (F₁ × F₂) (V₁ ×ᵇ V₂) :=
  homOfLinearMap (fun x ↦ LinearMap.inl ℂ (V₁ x) (V₂ x)) Bundle.Prod.contMDiff_inl

/-- The inclusion of the second sheaf into the sheaf of sections of a direct sum `V₁ ×ᵇ V₂`. -/
def prodInr : holomorphicSectionSheaf I F₂ V₂ ⟶ holomorphicSectionSheaf I (F₁ × F₂) (V₁ ×ᵇ V₂) :=
  homOfLinearMap (fun x ↦ LinearMap.inr ℂ (V₁ x) (V₂ x)) Bundle.Prod.contMDiff_inr

variable {I F₁ V₁ F₂ V₂}

@[simp]
theorem prodFst_app_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (s : (holomorphicSectionSheaf I (F₁ × F₂) (V₁ ×ᵇ V₂)).obj.obj U) (x : ↥(unop U)) :
    (prodFst I F₁ V₁ F₂ V₂).hom.app U s x = (s x).1 := (rfl)

@[simp]
theorem prodSnd_app_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (s : (holomorphicSectionSheaf I (F₁ × F₂) (V₁ ×ᵇ V₂)).obj.obj U) (x : ↥(unop U)) :
    (prodSnd I F₁ V₁ F₂ V₂).hom.app U s x = (s x).2 := (rfl)

@[simp]
theorem prodInl_app_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (s : (holomorphicSectionSheaf I F₁ V₁).obj.obj U) (x : ↥(unop U)) :
    (prodInl I F₁ V₁ F₂ V₂).hom.app U s x = (s x, 0) := (rfl)

@[simp]
theorem prodInr_app_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (s : (holomorphicSectionSheaf I F₂ V₂).obj.obj U) (x : ↥(unop U)) :
    (prodInr I F₁ V₁ F₂ V₂).hom.app U s x = (0, s x) := (rfl)

@[reassoc (attr := simp)]
theorem prodInl_prodFst : prodInl I F₁ V₁ F₂ V₂ ≫ prodFst I F₁ V₁ F₂ V₂ = 𝟙 _ :=
  hom_ext fun _ _ _ ↦ rfl

@[reassoc (attr := simp)]
theorem prodInl_prodSnd : prodInl I F₁ V₁ F₂ V₂ ≫ prodSnd I F₁ V₁ F₂ V₂ = 0 :=
  hom_ext fun _ _ _ ↦ rfl

@[reassoc (attr := simp)]
theorem prodInr_prodFst : prodInr I F₁ V₁ F₂ V₂ ≫ prodFst I F₁ V₁ F₂ V₂ = 0 :=
  hom_ext fun _ _ _ ↦ rfl

@[reassoc (attr := simp)]
theorem prodInr_prodSnd : prodInr I F₁ V₁ F₂ V₂ ≫ prodSnd I F₁ V₁ F₂ V₂ = 𝟙 _ :=
  hom_ext fun _ _ _ ↦ rfl

/-- The projections and inclusions of a direct sum add up to the identity of the sheaf of
sections of the direct sum. -/
theorem prodFst_prodInl_add_prodSnd_prodInr :
    prodFst I F₁ V₁ F₂ V₂ ≫ prodInl I F₁ V₁ F₂ V₂ + prodSnd I F₁ V₁ F₂ V₂ ≫ prodInr I F₁ V₁ F₂ V₂ =
      𝟙 _ :=
  hom_ext fun _ _ _ ↦ Prod.ext (add_zero _) (zero_add _)

variable (I F₁ V₁ F₂ V₂) in
/-- The sheaf of holomorphic sections of a direct sum `V₁ ×ᵇ V₂`, with the morphisms induced by
the fibrewise projections and inclusions, as a bicone over the two sheaves of sections. -/
-- Exposed so that the cone point is visibly the sheaf of the direct sum: otherwise the legs
-- cannot be stated as `prodFst`, `prodSnd`, `prodInl` and `prodInr` in the simp lemmas.
@[expose, simps]
def prodBicone :
    BinaryBicone (holomorphicSectionSheaf I F₁ V₁) (holomorphicSectionSheaf I F₂ V₂) where
  pt := holomorphicSectionSheaf I (F₁ × F₂) (V₁ ×ᵇ V₂)
  fst := prodFst I F₁ V₁ F₂ V₂
  snd := prodSnd I F₁ V₁ F₂ V₂
  inl := prodInl I F₁ V₁ F₂ V₂
  inr := prodInr I F₁ V₁ F₂ V₂
  inl_fst := prodInl_prodFst
  inl_snd := prodInl_prodSnd
  inr_fst := prodInr_prodFst
  inr_snd := prodInr_prodSnd

variable (I F₁ V₁ F₂ V₂) in
/-- The sheaf of holomorphic sections of a direct sum `V₁ ×ᵇ V₂` is the biproduct of the two
sheaves of holomorphic sections. -/
def prodBiconeIsBilimit : (prodBicone I F₁ V₁ F₂ V₂).IsBilimit :=
  isBinaryBilimitOfTotal _ prodFst_prodInl_add_prodSnd_prodInr

/-- The two sheaves of holomorphic sections have a biproduct, the sheaf of holomorphic sections
of the direct sum. -/
instance hasBinaryBiproduct :
    HasBinaryBiproduct (holomorphicSectionSheaf I F₁ V₁) (holomorphicSectionSheaf I F₂ V₂) :=
  HasBinaryBiproduct.mk ⟨_, prodBiconeIsBilimit I F₁ V₁ F₂ V₂⟩

variable (I F₁ V₁ F₂ V₂) in
/-- The sheaf of holomorphic sections of a direct sum `V₁ ×ᵇ V₂` is isomorphic to the biproduct
`⊞` of the two sheaves of holomorphic sections. -/
def prodIso :
    holomorphicSectionSheaf I (F₁ × F₂) (V₁ ×ᵇ V₂) ≅
      holomorphicSectionSheaf I F₁ V₁ ⊞ holomorphicSectionSheaf I F₂ V₂ :=
  biprod.uniqueUpToIso _ _ (prodBiconeIsBilimit I F₁ V₁ F₂ V₂)

/-- The isomorphism with the biproduct is given by the two projections. -/
@[simp]
theorem prodIso_hom :
    (prodIso I F₁ V₁ F₂ V₂).hom = biprod.lift (prodFst I F₁ V₁ F₂ V₂) (prodSnd I F₁ V₁ F₂ V₂) :=
  (rfl)

/-- The inverse of the isomorphism with the biproduct is given by the two inclusions. -/
@[simp]
theorem prodIso_inv :
    (prodIso I F₁ V₁ F₂ V₂).inv = biprod.desc (prodInl I F₁ V₁ F₂ V₂) (prodInr I F₁ V₁ F₂ V₂) :=
  (rfl)

end Prod

end holomorphicSectionSheaf

end TauCeti
