/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Divisor
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sheaf
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sheaf
import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Normalize
import TauCeti.Analysis.Complex.RiemannSurface.Differential.Ratio
import TauCeti.Topology.ContinuousOn.PuncturedNhds

/-!
# Differential sheaves as twisted divisor sheaves

Let `ω` be a `1`-form on a Riemann surface `X` which is meromorphic everywhere, and suppose its
order at every point is `E x - D x` for two divisors `D` and `E`. Division by `ω` identifies the
sheaf `Ω_D` of meromorphic `1`-forms with divisor at least `-D` with the sheaf `𝒪_E` of meromorphic
functions with divisor at least `-E` (`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheaf`):
a section `η` goes to the function `η / ω`, and a function `f` goes back to the `1`-form `f ω`.
On a compact surface, every `1`-form which is meromorphic and of finite order everywhere gives
`Ω_D ≅ 𝒪_(D + div ω)` (`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd`). In the
language of line bundles, `Ω_D` is the divisor sheaf of `D + K` for the canonical divisor
`K = div ω`.

Both sheaves normalize the values of their sections at the finitely many special points, so the
two maps fill in removable singularities and reset the values at allowed poles. Off a closed
discrete set they are the pointwise operations `η ↦ η / ω` and `f ↦ f ω`
(`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheaf_hom_app_smul` and
`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheaf_inv_app`, and for the compact form
`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd_hom_app_smul` and
`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd_inv_app`).

Consequently, on a compact Riemann surface the holomorphic `1`-forms are the global sections of
`𝒪_(div ω)` (`TauCeti.RiemannSurface.holomorphicOneFormsEquivDivisorSections`). The resulting
finite-dimensionality of the global sections of every `Ω_D` is in
`TauCeti.Analysis.Complex.RiemannSurface.Differential.FiniteDimensional`.

## Main definitions

* `TauCeti.RiemannSurface.differentialSectionsEquivDivisorSections`: division by `ω` on sections
  over an open set.
* `TauCeti.RiemannSurface.differentialSheafIsoDivisorSheaf`: the isomorphism `Ω_D ≅ 𝒪_E`.
* `TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd`: `Ω_D ≅ 𝒪_(D + div ω)` on a
  compact surface.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16–17 (the sheaves `𝒪_D` and `Ω_D`, and `Ω_D ≅ 𝒪_(D + K)`).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter V §3 (`L^(1)(D) ≅ L(D + K)`).
-/

public noncomputable section

open CategoryTheory Filter Function IsManifold Opposite Set TopologicalSpace Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open _root_.TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-! ### Normalized quotients and products -/

section Normalize

variable {D E : WeilDivisor X} {ω η θ : OneForm X} {x : X}

/-- The `1`-form `θ` normalized as a section of `Ω_D`: at the poles allowed by `D` its value is
`0`, and elsewhere its coefficient in the preferred chart is put in normal form, filling a
removable singularity. -/
private def normalizeForm (D : WeilDivisor X) (θ : OneForm X) : OneForm X :=
  fun y ↦ if D y ≤ 0 then
    toMeromorphicNFAt (θ.coeff (chartAt ℂ y)) (chartAt ℂ y y) (chartAt ℂ y y) •
      mvfderiv 𝓘(ℂ) (chartAt ℂ y) y
  else 0

private theorem normalizeForm_apply_of_holomorphicAt (hθ : θ.HolomorphicAt x) (hD : D x ≤ 0) :
    normalizeForm D θ x = θ x := by
  rw [normalizeForm, ite_eq_left hD,
    toMeromorphicNFAt_eq_self.2 ((θ.holomorphicAt_def x).1 hθ).meromorphicNFAt]
  exact (OneForm.coeff_eq_iff θ (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)).1 rfl

private theorem normalizeForm_eventuallyEq (hθ : θ.MeromorphicAt x) :
    ∀ᶠ y in 𝓝[≠] x, normalizeForm D θ y = θ y := by
  have := ChartedSpace.t1Space ℂ X
  filter_upwards [hθ.eventually_holomorphicAt, D.eventually_eq_zero_nhdsNE x] with y hy hD
  exact normalizeForm_apply_of_holomorphicAt hy hD.le

private theorem isDifferentialSectionAt_normalizeForm (hθ : θ.MeromorphicAt x)
    (ho : ((-D x : ℤ) : WithTop ℤ) ≤ θ.order x) :
    IsDifferentialSectionAt D (normalizeForm D θ) x := by
  have hev := normalizeForm_eventuallyEq (D := D) hθ
  refine ⟨hθ.congr (hev.mono fun _ h ↦ h.symm), by rwa [OneForm.order_congr hev], fun hD ↦ ?_,
    fun hD ↦ by rw [normalizeForm, ite_eq_right (not_le.2 hD)]⟩
  -- In the chart at `x`, the coefficient is the normal form of the coefficient of `θ`.
  have hθ' := (θ.meromorphicAt_def x).1 hθ
  have hval : (normalizeForm D θ).coeff (chartAt ℂ x) (chartAt ℂ x x) =
      toMeromorphicNFAt (θ.coeff (chartAt ℂ x)) (chartAt ℂ x x) (chartAt ℂ x x) :=
    (OneForm.coeff_eq_iff _ (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)).2
      (by rw [normalizeForm, ite_eq_left hD])
  have hnf : AnalyticAt ℂ (toMeromorphicNFAt (θ.coeff (chartAt ℂ x)) (chartAt ℂ x x))
      (chartAt ℂ x x) :=
    hθ'.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1
      (le_trans (by exact_mod_cast neg_nonneg.2 hD : (0 : WithTop ℤ) ≤ ((-D x : ℤ) : WithTop ℤ))
        (by rwa [OneForm.order_def] at ho))
  exact (OneForm.holomorphicAt_def _ x).2 <| hnf.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    ((OneForm.coeff_chartAt_eventuallyEq hev).trans hθ'.eq_nhdsNE_toMeromorphicNFAt) hval).symm

/-- If `η` is a local section of `Ω_D` at `x` and `ord_x ω = E x - D x`, the normalized quotient
`η / ω` is a local section of `𝒪_E` at `x`. -/
private theorem isDivisorSectionAt_toDivisorSection_ratio (hη : IsDifferentialSectionAt D η x)
    (hω : ω.MeromorphicAt x) (ho : ω.order x = ((E x - D x : ℤ) : WithTop ℤ)) :
    IsDivisorSectionAt E (toDivisorSection E (OneForm.ratio η ω)) x := by
  refine isDivisorSectionAt_toDivisorSection (OneForm.meromorphicAt_ratio hη.meromorphicAt hω) ?_
  have h := OneForm.meromorphicOrderAt_ratio_add_order hη.meromorphicAt hω
    (by rw [ho]; exact WithTop.coe_ne_top)
  have hle := hη.neg_le_order
  rw [← h, ho] at hle
  generalize meromorphicOrderAt (OneForm.ratio η ω) x = r at hle ⊢
  cases r with
  | top => exact le_top
  | coe r =>
    norm_cast at hle ⊢
    omega

end Normalize

/-! ### Sections over an open set -/

section Sections

variable {D E : WeilDivisor X} {ω : OneForm X} {U : Opens X}

open Classical in
/-- A section of `Ω_D` over `U`, extended by zero to a `1`-form on `X`. -/
private def extendSection (s : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ) : OneForm X :=
  fun y ↦ if h : y ∈ U then s ⟨y, h⟩ else 0

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem extendSection_apply (s : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ) (y : U) :
    extendSection s y = s y := by
  simp [extendSection, y.2]

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem isDifferentialSectionAt_extendSection
    {s : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ} (hs : s ∈ differentialSections D U)
    (x : U) : IsDifferentialSectionAt D (extendSection s) x := by
  obtain ⟨η, hη, e⟩ := mem_differentialSections_iff.1 hs x
  refine hη.congr ?_
  rw [← U.isOpenEmbedding'.map_nhds_eq x, eventually_map]
  filter_upwards [e] with y hy
  rw [extendSection_apply, hy]

private theorem differentialSections_ext_nhdsNE {s t : differentialSections D U}
    (h : ∀ x : U, ∀ᶠ y in 𝓝[≠] x, s.1 y = t.1 y) : s = t :=
  Subtype.ext (eq_of_eventually_codiscrete s.2 t.2
    (eventually_codiscrete_iff_forall_eventually_nhdsNE.2 h))

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem divisorSections_ext_nhdsNE {f g : divisorSections E U}
    (h : ∀ x : U, ∀ᶠ y in 𝓝[≠] x, f.1 y = g.1 y) : f = g :=
  Subtype.ext (eq_of_eventuallyEq_codiscrete f.2 g.2
    (eventually_codiscrete_iff_forall_eventually_nhdsNE.2 h))

variable (hω : ∀ x, ω.MeromorphicAt x)
  (ho : ∀ x, ω.order x = ((E x - D x : ℤ) : WithTop ℤ))
include hω ho

omit ho in
private theorem eventually_apply_ne_zero (ho : ∀ x, ω.order x ≠ ⊤) (x : U) :
    ∀ᶠ y : U in 𝓝[≠] x, ω y ≠ 0 :=
  (continuous_subtype_val.continuousAt.tendsto_nhdsNE Subtype.val_injective).eventually
    ((hω x).eventually_apply_ne_zero (ho x))

/-- Division of a section of `Ω_D` by `ω`, as a function. -/
private def divideSection (s : differentialSections D U) : divisorSections E U :=
  ⟨toDivisorSection E (OneForm.ratio (extendSection s.1) ω) ∘ Subtype.val,
    comp_val_mem_divisorSections fun x hx ↦ isDivisorSectionAt_toDivisorSection_ratio
      (isDifferentialSectionAt_extendSection s.2 ⟨x, hx⟩) (hω x) (ho x)⟩

private theorem divideSection_apply (s : differentialSections D U) (y : U) :
    (divideSection hω ho s).1 y = toDivisorSection E (OneForm.ratio (extendSection s.1) ω) y :=
  rfl

private theorem divideSection_smul_eventuallyEq (s : differentialSections D U) (x : U) :
    ∀ᶠ y in 𝓝[≠] x, (divideSection hω ho s).1 y • ω y = s.1 y := by
  have ht := continuous_subtype_val.continuousAt.tendsto_nhdsNE (x := x) Subtype.val_injective
  filter_upwards [ht.eventually
      (toDivisorSection_eventuallyEq E (OneForm.meromorphicAt_ratio
        (isDifferentialSectionAt_extendSection s.2 x).meromorphicAt (hω x))),
    eventually_apply_ne_zero hω (fun x ↦ by rw [ho x]; exact WithTop.coe_ne_top) x] with y hy hne
  rw [divideSection_apply, hy, OneForm.ratio_smul hne, extendSection_apply]

/-- Multiplication of a section of `𝒪_E` by `ω`, as a function. -/
private def multiplySection (f : divisorSections E U) : differentialSections D U :=
  ⟨fun y ↦ normalizeForm D ((Subtype.val.extend f.1 0 : X → ℂ) • ω) y,
    restrict_mem_differentialSections fun x hx ↦ by
      have hf := isDivisorSectionAt_extend f.2 ⟨x, hx⟩
      refine isDifferentialSectionAt_normalizeForm ((hω x).smul hf.meromorphicAt) ?_
      rw [OneForm.order_smul hf.meromorphicAt (hω x), ho x]
      calc ((-D x : ℤ) : WithTop ℤ) = ((-E x : ℤ) : WithTop ℤ) + ((E x - D x : ℤ) : WithTop ℤ) := by
            norm_cast
            ring
        _ ≤ _ := add_le_add_left hf.neg_le_meromorphicOrderAt _⟩

private theorem multiplySection_apply (f : divisorSections E U) (y : U) :
    (multiplySection hω ho f).1 y = normalizeForm D ((Subtype.val.extend f.1 0 : X → ℂ) • ω) y :=
  rfl

private theorem multiplySection_eventuallyEq (f : divisorSections E U) (x : U) :
    ∀ᶠ y in 𝓝[≠] x, (multiplySection hω ho f).1 y = f.1 y • ω y := by
  have ht := continuous_subtype_val.continuousAt.tendsto_nhdsNE (x := x) Subtype.val_injective
  filter_upwards [ht.eventually
      (normalizeForm_eventuallyEq (D := D)
        ((hω x).smul (isDivisorSectionAt_extend f.2 x).meromorphicAt))] with y hy
  rw [multiplySection_apply, hy, Pi.smul_apply', Subtype.val_injective.extend_apply]

/-- **Division by `ω` on sections.** If `ω` is meromorphic everywhere with `ord_x ω = E x - D x`,
then `η ↦ η / ω` identifies the sections of `Ω_D` over `U` with the sections of `𝒪_E` over `U`.
Off a closed discrete set it is the pointwise quotient
(`TauCeti.RiemannSurface.differentialSectionsEquivDivisorSections_smul`), and its inverse is
`f ↦ f ω` (`TauCeti.RiemannSurface.differentialSectionsEquivDivisorSections_symm_apply`). -/
def differentialSectionsEquivDivisorSections (U : Opens X) :
    differentialSections D U ≃ₗ[ℂ] divisorSections E U where
  toFun := divideSection hω ho
  invFun := multiplySection hω ho
  map_add' s t := divisorSections_ext_nhdsNE fun x ↦ by
    filter_upwards [divideSection_smul_eventuallyEq hω ho (s + t) x,
      divideSection_smul_eventuallyEq hω ho s x, divideSection_smul_eventuallyEq hω ho t x,
      eventually_apply_ne_zero hω (fun x ↦ by rw [ho x]; exact WithTop.coe_ne_top) x]
      with y hst hs ht hne
    refine smul_left_injective ℂ hne ?_
    simp only [Submodule.coe_add, Pi.add_apply] at hst ⊢
    rw [hst, add_smul, hs, ht]
  map_smul' c s := divisorSections_ext_nhdsNE fun x ↦ by
    filter_upwards [divideSection_smul_eventuallyEq hω ho (c • s) x,
      divideSection_smul_eventuallyEq hω ho s x,
      eventually_apply_ne_zero hω (fun x ↦ by rw [ho x]; exact WithTop.coe_ne_top) x]
      with y hcs hs hne
    refine smul_left_injective ℂ hne ?_
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul] at hcs ⊢
    rw [hcs, mul_smul, hs]
  left_inv s := differentialSections_ext_nhdsNE fun x ↦ by
    filter_upwards [multiplySection_eventuallyEq hω ho (divideSection hω ho s) x,
      divideSection_smul_eventuallyEq hω ho s x] with y h₁ h₂
    exact h₁.trans h₂
  right_inv f := divisorSections_ext_nhdsNE fun x ↦ by
    filter_upwards [divideSection_smul_eventuallyEq hω ho (multiplySection hω ho f) x,
      multiplySection_eventuallyEq hω ho f x,
      eventually_apply_ne_zero hω (fun x ↦ by rw [ho x]; exact WithTop.coe_ne_top) x]
      with y h₁ h₂ hne
    exact smul_left_injective ℂ hne (h₁.trans h₂)

/-- Off a closed discrete set, `differentialSectionsEquivDivisorSections` is the quotient by `ω`:
`(η / ω) ω = η`. -/
theorem differentialSectionsEquivDivisorSections_smul (s : differentialSections D U) :
    ∀ᶠ y in codiscrete U,
      (differentialSectionsEquivDivisorSections hω ho U s).1 y • ω y = s.1 y :=
  eventually_codiscrete_iff_forall_eventually_nhdsNE.2 (divideSection_smul_eventuallyEq hω ho s)

/-- Off a closed discrete set, the inverse of `differentialSectionsEquivDivisorSections` is
multiplication by `ω`. -/
theorem differentialSectionsEquivDivisorSections_symm_apply (f : divisorSections E U) :
    ∀ᶠ y in codiscrete U,
      ((differentialSectionsEquivDivisorSections hω ho U).symm f).1 y = f.1 y • ω y :=
  eventually_codiscrete_iff_forall_eventually_nhdsNE.2 (multiplySection_eventuallyEq hω ho f)

/-- `differentialSectionsEquivDivisorSections` commutes with restriction to a smaller open set. -/
private theorem differentialSectionsEquivDivisorSections_restrict {V : Opens X} (h : V ≤ U)
    (s : differentialSections D U) :
    (differentialSectionsEquivDivisorSections hω ho V
      ⟨fun y ↦ s.1 (Opens.inclusion h y), comp_inclusion_mem_differentialSections h s.2⟩).1 =
      (differentialSectionsEquivDivisorSections hω ho U s).1 ∘ Opens.inclusion h := by
  refine congrArg Subtype.val (divisorSections_ext_nhdsNE (f := ⟨_, _⟩)
    (g := ⟨_, comp_inclusion_mem_divisorSections h
      (differentialSectionsEquivDivisorSections hω ho U s).2⟩) fun x ↦ ?_)
  have ht : Tendsto (Opens.inclusion h) (𝓝[≠] x) (𝓝[≠] (Opens.inclusion h x)) :=
    (continuous_inclusion h).continuousAt.tendsto_nhdsNE (Set.inclusion_injective h)
  filter_upwards [divideSection_smul_eventuallyEq hω ho
      (⟨fun y ↦ s.1 (Opens.inclusion h y), comp_inclusion_mem_differentialSections h s.2⟩ :
        differentialSections D V) x,
    ht.eventually (divideSection_smul_eventuallyEq hω ho s (Opens.inclusion h x)),
    eventually_apply_ne_zero hω (fun x ↦ by rw [ho x]; exact WithTop.coe_ne_top) x]
    with y h₁ h₂ hne
  exact smul_left_injective ℂ hne (h₁.trans h₂.symm)

end Sections

/-! ### The sheaf isomorphism -/

section Sheaf

variable {D E : WeilDivisor X} {ω : OneForm X}

/-- The component of `differentialSheafIsoDivisorSheaf` on the sections over `U`. -/
private def differentialSheafIsoDivisorSheafComponent (hω : ∀ x, ω.MeromorphicAt x)
    (ho : ∀ x, ω.order x = ((E x - D x : ℤ) : WithTop ℤ)) (U : Opens X) :
    (differentialSheaf D).obj.obj (op U) ≅ (divisorSheaf E).obj.obj (op U) :=
  ((differentialSheafSectionsEquiv D U).trans
    ((differentialSectionsEquivDivisorSections hω ho U).trans
      (divisorSheafSectionsEquiv E U).symm)).toModuleIso

private theorem differentialSheafIsoDivisorSheafComponent_hom_apply
    (hω : ∀ x, ω.MeromorphicAt x) (ho : ∀ x, ω.order x = ((E x - D x : ℤ) : WithTop ℤ))
    (U : Opens X) (s : (differentialSheaf D).obj.obj (op U)) :
    divisorSheafSectionsEquiv E U ((differentialSheafIsoDivisorSheafComponent hω ho U).hom s) =
      differentialSectionsEquivDivisorSections hω ho U (differentialSheafSectionsEquiv D U s) := by
  simp [differentialSheafIsoDivisorSheafComponent]

private theorem differentialSheafIsoDivisorSheafComponent_inv_apply
    (hω : ∀ x, ω.MeromorphicAt x) (ho : ∀ x, ω.order x = ((E x - D x : ℤ) : WithTop ℤ))
    (U : Opens X) (f : (divisorSheaf E).obj.obj (op U)) :
    differentialSheafSectionsEquiv D U ((differentialSheafIsoDivisorSheafComponent hω ho U).inv f) =
      (differentialSectionsEquivDivisorSections hω ho U).symm
        (divisorSheafSectionsEquiv E U f) := by
  simp [differentialSheafIsoDivisorSheafComponent]

/-- **`Ω_D ≅ 𝒪_E` by division by `ω`.** If `ω` is a `1`-form meromorphic everywhere with
`ord_x ω = E x - D x` at every point, then `η ↦ η / ω` is an isomorphism from the sheaf `Ω_D` of
meromorphic `1`-forms with divisor at least `-D` to the sheaf `𝒪_E` of meromorphic functions with
divisor at least `-E`, with inverse `f ↦ f ω`. -/
def differentialSheafIsoDivisorSheaf (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x)
    (ho : ∀ x, ω.order x = ((E x - D x : ℤ) : WithTop ℤ)) :
    differentialSheaf D ≅ divisorSheaf E :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso <|
    NatIso.ofComponents (fun U ↦ differentialSheafIsoDivisorSheafComponent hω ho U.unop)
      fun {U V} i ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        apply (divisorSheafSectionsEquiv E V.unop).injective
        apply Subtype.ext
        -- The square is stated for the underlying presheaves (`sheafToPresheaf`), composition in
        -- `ModuleCat` and the opposite morphism `i`. The section lemmas
        -- `differentialSheafSectionsEquiv_map` and `divisorSheafSectionsEquiv_map` are stated for
        -- `F.obj.map i.unop.op` with the concrete-category coercion, which rewriting cannot
        -- produce from these wrappers; restate both composites in that form.
        change (divisorSheafSectionsEquiv E V.unop
            ((differentialSheafIsoDivisorSheafComponent hω ho V.unop).hom
              ((differentialSheaf D).obj.map i.unop.op s))).1 =
          (divisorSheafSectionsEquiv E V.unop ((divisorSheaf E).obj.map i.unop.op
            ((differentialSheafIsoDivisorSheafComponent hω ho U.unop).hom s))).1
        have hres : differentialSheafSectionsEquiv D V.unop
            ((differentialSheaf D).obj.map i.unop.op s) =
            ⟨fun y ↦ (differentialSheafSectionsEquiv D U.unop s).1 (Opens.inclusion i.unop.le y),
              comp_inclusion_mem_differentialSections i.unop.le
                (differentialSheafSectionsEquiv D U.unop s).2⟩ :=
          Subtype.ext (funext fun y ↦ differentialSheafSectionsEquiv_map D i.unop s y)
        rw [differentialSheafIsoDivisorSheafComponent_hom_apply, divisorSheafSectionsEquiv_map,
          differentialSheafIsoDivisorSheafComponent_hom_apply, hres]
        exact differentialSectionsEquivDivisorSections_restrict hω ho i.unop.le
          (differentialSheafSectionsEquiv D U.unop s)

variable (hω : ∀ x, ω.MeromorphicAt x) (ho : ∀ x, ω.order x = ((E x - D x : ℤ) : WithTop ℤ))

/-- On sections, `differentialSheafIsoDivisorSheaf` is
`differentialSectionsEquivDivisorSections`. -/
theorem differentialSheafIsoDivisorSheaf_hom_app (U : Opens X)
    (s : (differentialSheaf D).obj.obj (op U)) :
    divisorSheafSectionsEquiv E U
        ((differentialSheafIsoDivisorSheaf ω hω ho).hom.hom.app (op U) s) =
      differentialSectionsEquivDivisorSections hω ho U (differentialSheafSectionsEquiv D U s) :=
  differentialSheafIsoDivisorSheafComponent_hom_apply hω ho U s

/-- On sections, the inverse of `differentialSheafIsoDivisorSheaf` is the inverse of
`differentialSectionsEquivDivisorSections`. -/
theorem differentialSheafIsoDivisorSheaf_inv_app_eq (U : Opens X)
    (f : (divisorSheaf E).obj.obj (op U)) :
    differentialSheafSectionsEquiv D U
        ((differentialSheafIsoDivisorSheaf ω hω ho).inv.hom.app (op U) f) =
      (differentialSectionsEquivDivisorSections hω ho U).symm (divisorSheafSectionsEquiv E U f) :=
  differentialSheafIsoDivisorSheafComponent_inv_apply hω ho U f

/-- Off a closed discrete set, a section `η` of `Ω_D` and its image `η / ω` in `𝒪_E` satisfy
`(η / ω) ω = η`. -/
theorem differentialSheafIsoDivisorSheaf_hom_app_smul (U : Opens X)
    (s : (differentialSheaf D).obj.obj (op U)) :
    ∀ᶠ y in codiscrete U,
      (divisorSheafSectionsEquiv E U
        ((differentialSheafIsoDivisorSheaf ω hω ho).hom.hom.app (op U) s)).1 y • ω y =
        (differentialSheafSectionsEquiv D U s).1 y :=
  differentialSheafIsoDivisorSheaf_hom_app hω ho U s ▸
    differentialSectionsEquivDivisorSections_smul hω ho _

/-- Off a closed discrete set, the inverse of `differentialSheafIsoDivisorSheaf` sends a section
`f` of `𝒪_E` to `f ω`. -/
theorem differentialSheafIsoDivisorSheaf_inv_app (U : Opens X)
    (f : (divisorSheaf E).obj.obj (op U)) :
    ∀ᶠ y in codiscrete U,
      (differentialSheafSectionsEquiv D U
        ((differentialSheafIsoDivisorSheaf ω hω ho).inv.hom.app (op U) f)).1 y =
        (divisorSheafSectionsEquiv E U f).1 y • ω y :=
  differentialSheafIsoDivisorSheaf_inv_app_eq hω ho U f ▸
    differentialSectionsEquivDivisorSections_symm_apply hω ho _

end Sheaf

/-! ### Compact surfaces -/

section Compact

variable [CompactSpace X] {ω : OneForm X}

/-- On a compact surface, the order of a `1`-form meromorphic and of finite order everywhere is
`(D + div ω) x - D x`. -/
private theorem order_eq_coeff_add_divisor_sub (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) (D : WeilDivisor X) (x : X) :
    ω.order x = (((D + ω.divisor) x - D x : ℤ) : WithTop ℤ) := by
  rw [← OneForm.coe_coeff_divisor hω (hω₀ x)]
  simp [AlgebraicGeometry.WeilDivisor.coeff]

private theorem order_eq_coeff_divisor_sub_zero (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) (x : X) :
    ω.order x = ((ω.divisor x - (0 : WeilDivisor X) x : ℤ) : WithTop ℤ) := by
  simpa using order_eq_coeff_add_divisor_sub hω hω₀ 0 x

/-- **`Ω_D ≅ 𝒪_(D + div ω)`.** On a compact Riemann surface, a `1`-form `ω` which is meromorphic
and of finite order everywhere identifies the sheaf `Ω_D` with the divisor sheaf of `D + div ω`,
by `η ↦ η / ω`. -/
def differentialSheafIsoDivisorSheafAdd (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) (D : WeilDivisor X) :
    differentialSheaf D ≅ divisorSheaf (D + ω.divisor) :=
  differentialSheafIsoDivisorSheaf ω hω (order_eq_coeff_add_divisor_sub hω hω₀ D)

/-- Off a closed discrete set, a section `η` of `Ω_D` and its image `η / ω` in `𝒪_(D + div ω)`
under `differentialSheafIsoDivisorSheafAdd` satisfy `(η / ω) ω = η`. -/
theorem differentialSheafIsoDivisorSheafAdd_hom_app_smul (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) {D : WeilDivisor X} (U : Opens X)
    (s : (differentialSheaf D).obj.obj (op U)) :
    ∀ᶠ y in codiscrete U,
      (divisorSheafSectionsEquiv (D + ω.divisor) U
        ((differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).hom.hom.app (op U) s)).1 y • ω y =
        (differentialSheafSectionsEquiv D U s).1 y :=
  differentialSheafIsoDivisorSheaf_hom_app_smul hω _ U s

/-- Off a closed discrete set, the inverse of `differentialSheafIsoDivisorSheafAdd` sends a
section `f` of `𝒪_(D + div ω)` to `f ω`. -/
theorem differentialSheafIsoDivisorSheafAdd_inv_app (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) {D : WeilDivisor X} (U : Opens X)
    (f : (divisorSheaf (D + ω.divisor)).obj.obj (op U)) :
    ∀ᶠ y in codiscrete U,
      (differentialSheafSectionsEquiv D U
        ((differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).inv.hom.app (op U) f)).1 y =
        (divisorSheafSectionsEquiv (D + ω.divisor) U f).1 y • ω y :=
  differentialSheafIsoDivisorSheaf_inv_app hω _ U f

/-- **Holomorphic `1`-forms are divisor sections.** On a compact Riemann surface, a `1`-form `ω`
which is meromorphic and of finite order everywhere identifies the holomorphic `1`-forms with the
global sections of `𝒪_(div ω)`, by `η ↦ η / ω`. -/
def holomorphicOneFormsEquivDivisorSections (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) :
    holomorphicOneForms X ≃ₗ[ℂ] divisorSections ω.divisor ⊤ :=
  differentialSectionsZeroEquiv.symm.trans <|
    differentialSectionsEquivDivisorSections hω (order_eq_coeff_divisor_sub_zero hω hω₀) ⊤

/-- Off a closed discrete set, `holomorphicOneFormsEquivDivisorSections` is the quotient by `ω`. -/
theorem holomorphicOneFormsEquivDivisorSections_smul (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) (η : holomorphicOneForms X) :
    ∀ᶠ y in codiscrete (⊤ : Opens X),
      (holomorphicOneFormsEquivDivisorSections ω hω hω₀ η).1 y • ω y = η.1 y :=
  (differentialSectionsEquivDivisorSections_smul hω (order_eq_coeff_divisor_sub_zero hω hω₀)
    (differentialSectionsZeroEquiv.symm η)).mono
    fun y hy ↦ by rwa [differentialSectionsZeroEquiv_symm_apply] at hy

end Compact

end TauCeti.RiemannSurface
