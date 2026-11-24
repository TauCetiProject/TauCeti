/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Map
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.PrincipalParts
public import TauCeti.Topology.Sheaves.Cech.Flasque
public import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.SheafOfFunctions

/-!
# The principal-parts sequence of a divisor inclusion

For divisors `D ≤ E` on a Riemann surface, this file constructs the short exact sequence of
sheaves of complex vector spaces

`0 → 𝒪_D → 𝒪_E → 𝒫_{D,E} → 0`,

whose quotient `𝒫_{D,E}` is the sheaf of principal parts relative to `D` with poles bounded by
`E`. Its sections over `U` are the families, indexed by the points `x ∈ U`, of germs of order at
least `-E x` modulo those of order at least `-D x`
(`TauCeti.RiemannSurface.LocalPrincipalPart.boundedBy`). These fibres vanish off the finite
support of `E - D`, so `𝒫_{D,E}` is the finite direct sum of the skyscraper sheaves at the points
of `E - D`; the dependent-function description makes it flasque without a biproduct calculation.
For `E = D + x` it is the point-twist sequence of
`TauCeti/Analysis/Complex/RiemannSurface/Divisor/PointTwist.lean`, with the scalar coefficient
replaced by the class of the coordinate germ. Negative coefficients are allowed, and no
compactness is needed for the sheaf sequence.

On a compact Hausdorff Riemann surface, the Čech long exact sequence and the vanishing of the
first Čech cohomology of the flasque sheaf `𝒫_{D,E}` give the six-term exact sequence

`0 → H⁰(𝒪_D) → H⁰(𝒪_E) → ∏_x 𝒫_{D,E,x} → H¹(𝒪_D) → H¹(𝒪_E) → 0`.

Its connecting map `TauCeti.RiemannSurface.principalPartsConnecting` sends a family of principal
parts bounded by `E` to the obstruction to realizing it by a global section of `𝒪_E`. This is the
finite-level form of the Mittag-Leffler connecting map `PrincipalParts D → H¹(X, 𝒪_D)` of
Forster, Theorem 17.3.

## Main declarations

* `principalPartsSheaf D E` and its flasqueness `isFlasque_principalPartsSheaf`.
* `principalPartsMap D E : 𝒪_E ⟶ principalPartsSheaf D E`, taking principal parts.
* `principalPartsSequence_shortExact`: the short exact sequence of sheaves.
* `exact_globalSections_principalParts`, `exact_principalParts_connecting`,
  `exact_principalPartsConnecting_cohomologyMap`: exactness of the six-term sequence.
* `principalPartsSequenceMap`: the morphism of principal-parts sequences induced by `D ≤ D'` and
  `E ≤ E'`, and the naturality of the connecting maps `principalPartsConnecting_naturality`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§16-17.
-/

public noncomputable section

open CategoryTheory Limits Filter Opposite Set TopologicalSpace Topology
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

section Sheaf

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

open LocalPrincipalPart

variable (D E : WeilDivisor X)

/-- The presheaf of families of principal parts relative to `D` bounded by `E`. -/
private def principalPartsPresheaf : TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj U := ModuleCat.of ℂ (∀ x : U.unop, boundedBy D E x.val)
  map h := ModuleCat.ofHom
    { toFun s x := s ⟨x.val, h.unop.le x.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The **sheaf of principal parts** relative to `D` with poles bounded by `E`. Its sections over
`U` are the families of local principal parts `LocalPrincipalPart.boundedBy D E x` at the points
of `U`, which vanish off the support of `E - D`. -/
def principalPartsSheaf : TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj := principalPartsPresheaf D E
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{u} ℂ))]
    -- The underlying presheaf of sets is the presheaf of all dependent functions.
    exact TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun _ ↦ (Equiv.refl _).toIso)
      fun _ ↦ rfl) (TopCat.Presheaf.toTypes_isSheaf (TopCat.of X) fun x ↦ boundedBy D E x)

/-- Read a section of the principal-parts sheaf over `U` as a family of local principal parts. -/
def principalPartsSheafSectionsEquiv (U : Opens X) :
    (principalPartsSheaf D E).obj.obj (op U) ≃ₗ[ℂ] ∀ x : U, boundedBy D E x.val :=
  LinearEquiv.refl ℂ _

/-- Restriction of sections of the principal-parts sheaf is restriction of families. -/
@[simp]
theorem principalPartsSheafSectionsEquiv_map {U V : Opens X} (h : V ⟶ U)
    (s : (principalPartsSheaf D E).obj.obj (op U)) (x : V) :
    principalPartsSheafSectionsEquiv D E V ((principalPartsSheaf D E).obj.map h.op s) x =
      principalPartsSheafSectionsEquiv D E U s ⟨x.val, h.le x.property⟩ := (rfl)

/-- The principal-parts sheaf is flasque: a family on a smaller open set extends by zero. -/
instance isFlasque_principalPartsSheaf :
    TopCat.Presheaf.IsFlasque (principalPartsSheaf D E).obj where
  epi {U V} i := by
    classical
    rw [ModuleCat.epi_iff_surjective]
    intro s
    refine ⟨fun x ↦ if hx : x.val ∈ V.unop then s ⟨x.val, hx⟩ else 0, ?_⟩
    funext x
    exact dite_eq_left x.property

/-- The principal parts of a section of `𝒪_E` relative to `D`. -/
def divisorSections.principalParts (U : Opens X) :
    divisorSections E U →ₗ[ℂ] ∀ x : U, boundedBy D E x.val :=
  LinearMap.pi fun x ↦ (((meromorphicGerms.orderGE (chartAt ℂ x.val x.val) (-D x.val)).mkQ).comp
    (divisorSections.toChartGerm E U x)).codRestrict _ fun f ↦
      mk_mem_boundedBy (divisorSections.toChartGerm_mem_orderGE f x)

/-- The principal part of a section at `x` is the class of its coordinate germ. -/
@[simp]
theorem divisorSections.coe_principalParts_apply (U : Opens X) (f : divisorSections E U)
    (x : U) :
    (divisorSections.principalParts D E U f x : LocalPrincipalPart D x.val) =
      Submodule.Quotient.mk (divisorSections.toChartGerm E U x f) := (rfl)

/-- The morphism `𝒪_E ⟶ 𝒫_{D,E}` taking principal parts relative to `D`. -/
def principalPartsMap : divisorSheaf E ⟶ principalPartsSheaf D E where
  hom.app U := ModuleCat.ofHom ((divisorSections.principalParts D E U.unop).comp
    (divisorSheafSectionsEquiv E U.unop).toLinearMap)
  hom.naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    have hs : divisorSheafSectionsEquiv E V.unop ((divisorSheaf E).obj.map h f) =
        ⟨(divisorSheafSectionsEquiv E U.unop f).val ∘ Opens.inclusion h.unop.le,
          comp_inclusion_mem_divisorSections h.unop.le (divisorSheafSectionsEquiv E U.unop
              f).property⟩ :=
      Subtype.ext (divisorSheafSectionsEquiv_map E h.unop f)
    funext x
    apply Subtype.ext
    -- Both sides are the class of a coordinate germ, which is unchanged by restriction.
    change (divisorSections.principalParts D E V.unop
        (divisorSheafSectionsEquiv E V.unop ((divisorSheaf E).obj.map h f)) x :
          LocalPrincipalPart D x.val) =
      (divisorSections.principalParts D E U.unop (divisorSheafSectionsEquiv E U.unop f)
        ⟨x.val, h.unop.le x.property⟩ : LocalPrincipalPart D x.val)
    rw [hs, divisorSections.coe_principalParts_apply, divisorSections.coe_principalParts_apply,
      divisorSections.toChartGerm_restrict]

/-- The principal parts of a section of `𝒪_E`, read pointwise. -/
@[simp]
theorem principalPartsMap_app_apply (U : Opens X) (f : (divisorSheaf E).obj.obj (op U)) (x : U) :
    (principalPartsSheafSectionsEquiv D E U ((principalPartsMap D E).hom.app (op U) f) x :
        LocalPrincipalPart D x.val) =
      Submodule.Quotient.mk (divisorSections.toChartGerm E U x
        (divisorSheafSectionsEquiv E U f)) := (rfl)

variable {D E}

/-- The inclusion `𝒪_D ⟶ 𝒪_E` followed by taking principal parts relative to `D` is zero. -/
@[reassoc (attr := simp)]
theorem divisorSheafMapOfLE_comp_principalPartsMap (h : D ≤ E) :
    divisorSheafMapOfLE h ≫ principalPartsMap D E = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext x
  apply Subtype.ext
  -- The principal part of a section of `𝒪_D` is the class of a germ of order at least `-D x`.
  change (Submodule.Quotient.mk (divisorSections.toChartGerm E U.unop x
      (divisorSheafSectionsEquiv E U.unop ((divisorSheafMapOfLE h).hom.app U f))) :
        LocalPrincipalPart D x.val) = 0
  rw [divisorSections.toChartGerm_mapOfLE, Submodule.Quotient.mk_eq_zero]
  exact divisorSections.toChartGerm_mem_orderGE _ x

/-- A section of `𝒪_E` whose principal parts relative to `D` vanish satisfies the order bound of
`𝒪_D` at every point. -/
private theorem neg_le_order_of_principalPartsMap_eq_zero {U : Opens X}
    (f : (divisorSheaf E).obj.obj (op U)) (hf : (principalPartsMap D E).hom.app (op U) f = 0)
    (y : U) :
    ((-D y.val : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (Subtype.val.extend (divisorSheafSectionsEquiv E U f).val 0) y.val := by
  have hy : (Submodule.Quotient.mk (divisorSections.toChartGerm E U y
      (divisorSheafSectionsEquiv E U f)) : LocalPrincipalPart D y.val) = 0 :=
    congrArg (fun s ↦ (principalPartsSheafSectionsEquiv D E U s y : LocalPrincipalPart D y.val)) hf
  rwa [Submodule.Quotient.mk_eq_zero, meromorphicGerms.mem_orderGE,
    divisorSections.order_toChartGerm] at hy

section LocalLifting

variable [IsManifold 𝓘(ℂ) 1 X]

/-- The **principal-parts sequence** `𝒪_D ⟶ 𝒪_E ⟶ 𝒫_{D,E}` of a divisor inclusion `D ≤ E`. -/
@[expose] def principalPartsSequence (h : D ≤ E) :
    ShortComplex (TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)) :=
  ShortComplex.mk (divisorSheafMapOfLE h) (principalPartsMap D E)
    (divisorSheafMapOfLE_comp_principalPartsMap h)

omit [IsManifold 𝓘(ℂ) 1 X] in
@[simp]
theorem principalPartsSequence_f (h : D ≤ E) :
    (principalPartsSequence h).f = divisorSheafMapOfLE h := (rfl)

omit [IsManifold 𝓘(ℂ) 1 X] in
@[simp]
theorem principalPartsSequence_g (h : D ≤ E) :
    (principalPartsSequence h).g = principalPartsMap D E := (rfl)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The first object of the principal-parts sequence is the divisor sheaf of `D`. -/
@[simp]
theorem principalPartsSequence_X₁ (h : D ≤ E) :
    (principalPartsSequence h).X₁ = divisorSheaf D := (rfl)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The middle object of the principal-parts sequence is the divisor sheaf of `E`. -/
@[simp]
theorem principalPartsSequence_X₂ (h : D ≤ E) :
    (principalPartsSequence h).X₂ = divisorSheaf E := (rfl)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The final object of the principal-parts sequence is the principal-parts sheaf. -/
@[simp]
theorem principalPartsSequence_X₃ (h : D ≤ E) :
    (principalPartsSequence h).X₃ = principalPartsSheaf D E := (rfl)

/-- **Exactness in the middle of the principal-parts sequence**: a section of `𝒪_E` with zero
principal parts relative to `D` comes locally from `𝒪_D`. -/
theorem principalPartsSequence_exact (h : D ≤ E) : (principalPartsSequence h).Exact :=
  exact_divisorSheafMapOfLE_of_neg_le_order h _ _ neg_le_order_of_principalPartsMap_eq_zero

/-- Principal parts bounded by `E` are prescribed locally by sections of `𝒪_E`: near a point
`y` a coordinate representative realizes the principal part at `y`, and the other points of the
finite support of `E - D` are removed. -/
theorem principalPartsMap_isLocallySurjective :
    TopCat.Presheaf.IsLocallySurjective (principalPartsMap D E).hom := by
  classical
  have := ChartedSpace.t1Space ℂ X
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t y hyU
  obtain ⟨φ, hφ, hφt⟩ :=
    mem_boundedBy_iff.1 (principalPartsSheafSectionsEquiv D E U t ⟨y, hyU⟩).property
  obtain ⟨U₁, hy₁, f, hf⟩ := exists_section_toChartGerm_eq E y φ hφ
  let S : Set X := (((E - D).support.erase y : Finset X) : Set X)
  let V : Opens X := U ⊓ U₁ ⊓ ⟨Sᶜ, (Finset.finite_toSet _).isClosed.isOpen_compl⟩
  have hVU : V ≤ U := fun z hz ↦ hz.1.1
  have hV₁ : V ≤ U₁ := fun z hz ↦ hz.1.2
  have hyV : y ∈ V := ⟨⟨hyU, hy₁⟩, by simp [S]⟩
  refine ⟨V, hVU, ⟨(divisorSheafSectionsEquiv E V).symm
    ⟨f.val ∘ Opens.inclusion hV₁, comp_inclusion_mem_divisorSections hV₁ f.property⟩, ?_⟩, hyV⟩
  funext z
  apply Subtype.ext
  -- Pointwise, the principal part of the restricted representative is that of `t`.
  change (principalPartsSheafSectionsEquiv D E V ((principalPartsMap D E).hom.app (op V)
      ((divisorSheafSectionsEquiv E V).symm
        ⟨f.val ∘ Opens.inclusion hV₁, comp_inclusion_mem_divisorSections hV₁ f.property⟩)) z :
        LocalPrincipalPart D z.val) =
    (principalPartsSheafSectionsEquiv D E U t ⟨z.val, hVU z.property⟩ : LocalPrincipalPart D z.val)
  rw [principalPartsMap_app_apply, LinearEquiv.apply_symm_apply,
    divisorSections.toChartGerm_restrict hV₁ z.property]
  by_cases hzy : z.val = y
  · have key : ∀ (w : X) (_hw : w = y) (h₁ : w ∈ U₁) (h₂ : w ∈ U),
        (Submodule.Quotient.mk (divisorSections.toChartGerm E U₁ ⟨w, h₁⟩ f) :
          LocalPrincipalPart D w) = principalPartsSheafSectionsEquiv D E U t ⟨w, h₂⟩ := by
      rintro w rfl h₁ h₂
      rw [hf]
      exact hφt
    exact key z.val hzy _ _
  · have hED : E z.val ≤ D z.val := by
      by_contra hlt
      have hmem : z.val ∈ S := by
        simp only [S, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Finsupp.mem_support_iff,
          Finsupp.coe_sub, Pi.sub_apply, Set.mem_singleton_iff]
        exact ⟨sub_ne_zero.2 (ne_of_not_le hlt), hzy⟩
      exact z.property.2 hmem
    have hb := boundedBy_eq_bot (D := D) hED
    have h₁ := mk_mem_boundedBy (D := D) (divisorSections.toChartGerm_mem_orderGE
      (⟨f.val ∘ Opens.inclusion hV₁, comp_inclusion_mem_divisorSections hV₁ f.property⟩ :
        divisorSections E V) z)
    rw [divisorSections.toChartGerm_restrict hV₁ z.property, hb, Submodule.mem_bot] at h₁
    have h₂ : (principalPartsSheafSectionsEquiv D E U t ⟨z.val, hVU z.property⟩ :
        LocalPrincipalPart D z.val) ∈ boundedBy D E z.val :=
      (principalPartsSheafSectionsEquiv D E U t ⟨z.val, hVU z.property⟩).property
    rw [h₁, (Submodule.eq_bot_iff _).1 hb _ h₂]

/-- Taking principal parts is an epimorphism of sheaves. -/
instance principalPartsMap_epi : Epi (principalPartsMap D E) := by
  have : CategoryTheory.Sheaf.IsLocallySurjective (principalPartsMap D E) :=
    principalPartsMap_isLocallySurjective
  infer_instance

/-- **The principal-parts short exact sequence** `0 → 𝒪_D → 𝒪_E → 𝒫_{D,E} → 0` of a divisor
inclusion `D ≤ E` on a Riemann surface. -/
theorem principalPartsSequence_shortExact (h : D ≤ E) :
    (principalPartsSequence h).ShortExact := by
  have : Mono (principalPartsSequence h).f := inferInstanceAs (Mono (divisorSheafMapOfLE h))
  have : Epi (principalPartsSequence h).g := inferInstanceAs (Epi (principalPartsMap D E))
  exact { exact := principalPartsSequence_exact h }

variable (D E) in
/-- Families of principal parts over the whole space, indexed by the open set `⊤` or by the
points of `X`. -/
def principalPartsTopEquiv :
    (∀ x : (⊤ : Opens X), boundedBy D E x.val) ≃ₗ[ℂ] ∀ x : X, boundedBy D E x where
  toFun s x := s ⟨x, trivial⟩
  invFun μ x := μ x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsManifold 𝓘(ℂ) 1 X] in
@[simp]
theorem principalPartsTopEquiv_apply (s : ∀ x : (⊤ : Opens X), boundedBy D E x.val) (x : X) :
    principalPartsTopEquiv D E s x = s ⟨x, trivial⟩ := (rfl)

omit [IsManifold 𝓘(ℂ) 1 X] in
@[simp]
theorem principalPartsTopEquiv_symm_apply (μ : ∀ x : X, boundedBy D E x) (x : (⊤ : Opens X)) :
    (principalPartsTopEquiv D E).symm μ x = μ x.val := (rfl)

variable (D E) in
/-- The principal parts relative to `D` of a global section of `𝒪_E`. -/
def globalPrincipalParts : (divisorSheaf E).obj.obj (op ⊤) →ₗ[ℂ] ∀ x : X, boundedBy D E x :=
  ((principalPartsSheafSectionsEquiv D E ⊤).trans (principalPartsTopEquiv D E)).toLinearMap ∘ₗ
    ((principalPartsMap D E).hom.app (op ⊤)).hom

omit [IsManifold 𝓘(ℂ) 1 X] in
@[simp]
theorem coe_globalPrincipalParts_apply (f : (divisorSheaf E).obj.obj (op ⊤)) (x : X) :
    (globalPrincipalParts D E f x : LocalPrincipalPart D x) =
      Submodule.Quotient.mk (divisorSections.toChartGerm E ⊤ ⟨x, trivial⟩
        (divisorSheafSectionsEquiv E ⊤ f)) := (rfl)

/-- A global section of `𝒪_E` comes from `𝒪_D` exactly when its principal parts relative to
`D` vanish. -/
theorem exact_globalSections_principalParts (h : D ≤ E) :
    Function.Exact ((divisorSheafMapOfLE h).hom.app (op ⊤)) (globalPrincipalParts D E) := by
  have hS := principalPartsSequence_shortExact h
  have := hS.mono_f
  have hx := hS.exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ _ ⋙ (evaluation _ (ModuleCat ℂ)).obj (op ⊤))
    inferInstance inferInstance
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hx
  -- Expose the evaluated short-complex maps.
  change Function.Exact ((divisorSheafMapOfLE h).hom.app (op ⊤)).hom
    ((principalPartsMap D E).hom.app (op ⊤)).hom at he
  exact LinearEquiv.postcomp_exact_iff_exact.mpr he

end LocalLifting

section Functoriality

variable {D' E' : WeilDivisor X}

/-- The map of sections over `U` underlying `principalPartsSheafMap`. -/
private def principalPartsSheafMapApp (hD : D ≤ D') (hE : E ≤ E') (U : Opens X) :
    (principalPartsSheaf D E).obj.obj (op U) →ₗ[ℂ] (principalPartsSheaf D' E').obj.obj (op U) :=
  (principalPartsSheafSectionsEquiv D' E' U).symm.toLinearMap ∘ₗ
    LinearMap.piMap (fun x : U ↦ boundedByMapOfLE hD (hE x.val)) ∘ₗ
      (principalPartsSheafSectionsEquiv D E U).toLinearMap

/-- The morphism of principal-parts sheaves `𝒫_{D,E} ⟶ 𝒫_{D',E'}` for `D ≤ D'` and `E ≤ E'`,
projecting each local principal part from `D` to `D'`. -/
def principalPartsSheafMap (hD : D ≤ D') (hE : E ≤ E') :
    principalPartsSheaf D E ⟶ principalPartsSheaf D' E' where
  hom.app U := ModuleCat.ofHom (principalPartsSheafMapApp hD hE U.unop)
  hom.naturality {U V} h := by
    ext s
    rfl

@[simp]
theorem principalPartsSheafMap_app_apply (hD : D ≤ D') (hE : E ≤ E') (U : Opens X)
    (s : (principalPartsSheaf D E).obj.obj (op U)) (x : U) :
    (principalPartsSheafSectionsEquiv D' E' U ((principalPartsSheafMap hD hE).hom.app (op U) s) x :
        LocalPrincipalPart D' x.val) =
      LocalPrincipalPart.mapOfLE hD x.val (principalPartsSheafSectionsEquiv D E U s x) :=
  coe_boundedByMapOfLE_apply hD (hE x.val) (principalPartsSheafSectionsEquiv D E U s x)

/-- The principal parts of a section of `𝒪_E`, projected to `D'`, are the principal parts of its
image in `𝒪_{E'}`. -/
@[reassoc]
theorem principalPartsMap_comp_principalPartsSheafMap (hD : D ≤ D') (hE : E ≤ E') :
    principalPartsMap D E ≫ principalPartsSheafMap hD hE =
      divisorSheafMapOfLE hE ≫ principalPartsMap D' E' := by
  apply CategoryTheory.Sheaf.hom_ext
  ext ⟨U⟩ f
  apply (principalPartsSheafSectionsEquiv D' E' U).injective
  funext x
  apply Subtype.ext
  exact (principalPartsSheafMap_app_apply hD hE U _ x).trans <| (mapOfLE_mk hD x.val _).trans <|
    congrArg Submodule.Quotient.mk (divisorSections.toChartGerm_mapOfLE hE f x).symm

/-- The **morphism of principal-parts sequences** induced by `D ≤ D'` and `E ≤ E'`: the divisor
inclusions on `𝒪_D` and `𝒪_E`, and the projection of principal parts. -/
def principalPartsSequenceMap (hDE : D ≤ E) (hDE' : D' ≤ E') (hD : D ≤ D') (hE : E ≤ E') :
    principalPartsSequence hDE ⟶ principalPartsSequence hDE' where
  τ₁ := divisorSheafMapOfLE hD
  τ₂ := divisorSheafMapOfLE hE
  τ₃ := principalPartsSheafMap hD hE
  comm₁₂ := (divisorSheafMapOfLE_comp hD hDE').trans (divisorSheafMapOfLE_comp hDE hE).symm
  comm₂₃ := (principalPartsMap_comp_principalPartsSheafMap hD hE).symm

@[simp]
theorem principalPartsSequenceMap_τ₁ (hDE : D ≤ E) (hDE' : D' ≤ E') (hD : D ≤ D') (hE : E ≤ E') :
    (principalPartsSequenceMap hDE hDE' hD hE).τ₁ = divisorSheafMapOfLE hD := (rfl)

@[simp]
theorem principalPartsSequenceMap_τ₂ (hDE : D ≤ E) (hDE' : D' ≤ E') (hD : D ≤ D') (hE : E ≤ E') :
    (principalPartsSequenceMap hDE hDE' hD hE).τ₂ = divisorSheafMapOfLE hE := (rfl)

@[simp]
theorem principalPartsSequenceMap_τ₃ (hDE : D ≤ E) (hDE' : D' ≤ E') (hD : D ≤ D') (hE : E ≤ E') :
    (principalPartsSequenceMap hDE hDE' hD hE).τ₃ = principalPartsSheafMap hD hE := (rfl)

end Functoriality

end Sheaf

section Cohomology

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {D E : WeilDivisor X}

open LocalPrincipalPart

variable (D E) in
/-- Families of principal parts bounded by `E` identify with the degree-zero Čech cohomology of
the principal-parts sheaf. -/
def principalPartsCechIso : ModuleCat.of ℂ (∀ x : X, boundedBy D E x) ≅
    (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj (principalPartsSheaf D E).obj :=
  (principalPartsTopEquiv D E).symm.toModuleIso ≪≫
    cechCohomologyZeroIso (principalPartsSheaf D E)

/-- The identification of families of principal parts with degree-zero cohomology is the
identification of global sections with degree-zero cohomology. -/
theorem principalPartsCechIso_hom_apply (c : ∀ x : X, boundedBy D E x)
    (s : (principalPartsSheaf D E).obj.obj (op ⊤))
    (hs : ∀ x : X, principalPartsSheafSectionsEquiv D E ⊤ s ⟨x, trivial⟩ = c x) :
    (principalPartsCechIso D E).hom.hom c =
      (cechCohomologyZeroIso (principalPartsSheaf D E)).hom.hom s := by
  obtain rfl : c = fun x ↦ principalPartsSheafSectionsEquiv D E ⊤ s ⟨x, trivial⟩ :=
    funext fun x ↦ (hs x).symm
  rfl

variable (D E) in
/-- The identification of families of principal parts with degree-zero cohomology passes through
the global sections of the principal-parts sheaf. -/
theorem principalPartsCechIso_def :
    principalPartsCechIso D E =
      ((principalPartsSheafSectionsEquiv D E ⊤).trans
          (principalPartsTopEquiv D E)).symm.toModuleIso ≪≫
        cechCohomologyZeroIso (principalPartsSheaf D E) := (rfl)

variable {D' E' : WeilDivisor X}

/-- The identification of families of principal parts with degree-zero cohomology is natural in
`D ≤ D'` and `E ≤ E'`. -/
private theorem principalPartsCechIso_naturality (hD : D ≤ D') (hE : E ≤ E')
    (c : ∀ x : X, boundedBy D E x) :
    ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).map
        (principalPartsSheafMap hD hE).hom).hom ((principalPartsCechIso D E).hom.hom c) =
      (principalPartsCechIso D' E').hom.hom (PrincipalParts.boundedFamilyMap hD hE c) := by
  obtain ⟨s, hs⟩ := (principalPartsSheafSectionsEquiv D E ⊤).surjective
    ((principalPartsTopEquiv D E).symm c)
  rw [principalPartsCechIso_hom_apply c s fun x ↦ by rw [hs, principalPartsTopEquiv_symm_apply],
    principalPartsCechIso_hom_apply _ ((principalPartsSheafMap hD hE).hom.app (op ⊤) s)
      fun x ↦ Subtype.ext (by
        rw [principalPartsSheafMap_app_apply, hs, principalPartsTopEquiv_symm_apply,
          PrincipalParts.coe_boundedFamilyMap_apply])]
  exact (congrArg (fun g ↦ g.hom s) (cechCohomologyZeroIso_hom_naturality _
    (principalPartsSheafMap hD hE))).symm

variable [IsManifold 𝓘(ℂ) 1 X]

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem globalPrincipalParts_augmentation :
    ModuleCat.ofHom (globalPrincipalParts D E) ≫ (principalPartsCechIso D E).hom =
      (cechCohomologyZeroIso (divisorSheaf E)).hom ≫
        (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).map (principalPartsMap D E).hom := by
  rw [← cechCohomologyZeroIso_hom_naturality]
  -- Both composites send a global section to its principal parts in degree-zero cohomology.
  ext f
  rfl

variable [CompactSpace X] [T2Space X]

/-- The **connecting map of the principal-parts sequence**: a family of principal parts relative
to `D` with poles bounded by `E` is sent to its obstruction in `H¹(X, 𝒪_D)` to being the family of
principal parts of a global section of `𝒪_E`. -/
def principalPartsConnecting (h : D ≤ E) :
    (∀ x : X, boundedBy D E x) →ₗ[ℂ] divisorCechCohomology D 1 :=
  ((principalPartsCechIso D E).hom ≫
    (principalPartsSequence_shortExact h).cechCohomologyδ 0).hom

/-- The connecting map of principal parts is the Čech connecting map of the principal-parts
sequence, after identifying families of principal parts with degree-zero cohomology. -/
theorem principalPartsConnecting_def (h : D ≤ E) :
    principalPartsConnecting h = ((principalPartsCechIso D E).hom ≫
      (principalPartsSequence_shortExact h).cechCohomologyδ 0).hom := (rfl)

/-- A family of principal parts bounded by `E` is the family of principal parts of a global
section of `𝒪_E` if and only if its connecting obstruction vanishes. -/
theorem exact_principalParts_connecting (h : D ≤ E) :
    Function.Exact (globalPrincipalParts D E) (principalPartsConnecting h) := by
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((principalPartsSequence_shortExact h).cechCohomology_exact₃ 0)
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := (cechCohomologyZeroIso (divisorSheaf E)).toLinearEquiv)
    (e₂ := (principalPartsCechIso D E).toLinearEquiv)
    (e₃ := LinearEquiv.refl ℂ _)
    (congrArg ModuleCat.Hom.hom globalPrincipalParts_augmentation).symm
    (by rfl)).mp he

/-- The kernel of `H¹(𝒪_D) → H¹(𝒪_E)` consists exactly of the connecting obstructions of
principal parts bounded by `E`. -/
theorem exact_principalPartsConnecting_cohomologyMap (h : D ≤ E) :
    Function.Exact (principalPartsConnecting h) (divisorCechCohomologyMapOfLE h 1) := by
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((principalPartsSequence_shortExact h).cechCohomology_exact₁ 0)
  rw [divisorCechCohomologyMapOfLE_def]
  exact (LinearEquiv.precomp_exact_iff_exact (N := divisorCechCohomology D 1)
    (e := (principalPartsCechIso D E).toLinearEquiv)).mpr he

/-- **Naturality of the principal-parts connecting maps** in `D ≤ D'` and `E ≤ E'`. -/
theorem principalPartsConnecting_naturality (hDE : D ≤ E) (hDE' : D' ≤ E') (hD : D ≤ D')
    (hE : E ≤ E') (c : ∀ x : X, boundedBy D E x) :
    principalPartsConnecting hDE' (PrincipalParts.boundedFamilyMap hD hE c) =
      divisorCechCohomologyMapOfLE hD 1 (principalPartsConnecting hDE c) := by
  have h := congrArg (fun g ↦ g.hom ((principalPartsCechIso D E).hom.hom c))
    ((principalPartsSequence_shortExact hDE).cechCohomologyδ_naturality
      (principalPartsSequence_shortExact hDE') (principalPartsSequenceMap hDE hDE' hD hE) 0)
  rw [principalPartsConnecting_def, principalPartsConnecting_def, divisorCechCohomologyMapOfLE_def]
  exact (congrArg ((principalPartsSequence_shortExact hDE').cechCohomologyδ 0).hom
    (principalPartsCechIso_naturality hD hE c).symm).trans h.symm

/-- The finite-level connecting map does not depend on the bounding divisor. -/
theorem principalPartsConnecting_boundedFamilyMap_refl (hDE : D ≤ E) (hEE' : E ≤ E')
    (c : ∀ x : X, boundedBy D E x) :
    principalPartsConnecting (hDE.trans hEE') (PrincipalParts.boundedFamilyMap le_rfl hEE' c) =
      principalPartsConnecting hDE c := by
  rw [principalPartsConnecting_naturality hDE (hDE.trans hEE') le_rfl hEE',
    divisorCechCohomologyMapOfLE_refl, LinearMap.id_apply]

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] in
/-- The principal-parts sheaf has no first Čech cohomology, so the sequence ends with the
surjection `H¹(𝒪_D) → H¹(𝒪_E)` (`divisorCechCohomologyMapOfLE_one_surjective`). -/
theorem isZero_cechCohomology_one_principalPartsSheaf :
    IsZero ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
      (principalPartsSheaf D E).obj) :=
  isZero_cechCohomology_succ_of_isFlasque (principalPartsSheaf D E) 0

end Cohomology

end TauCeti.RiemannSurface
