/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Basic
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# The sheaf `Ω_D` of meromorphic `1`-forms bounded by a divisor

Let `X` be a Riemann surface and `D` a divisor on `X`. The sheaf `Ω_D` assigns to an open set `U`
the meromorphic `1`-forms `ω` on `U` with `ord_x ω ≥ -D x` at every `x ∈ U`: poles of order at most
`D x` are allowed where `D x > 0`, and zeros of order at least `-D x` are required where `D x < 0`.
These are the sheaves in Serre duality `H¹(X, 𝒪_D)^* ≅ H⁰(X, Ω_{-D})` on a compact surface, and
`Ω_0` is the sheaf of holomorphic `1`-forms.

The construction mirrors that of the sheaf `𝒪_D` of a divisor
(`TauCeti.RiemannSurface.divisorSheaf`). A section of `Ω_D` over `U` is represented by an honest
field of covectors over `U`, normalized as follows
(`TauCeti.RiemannSurface.IsDifferentialSectionAt`): near each point it is a meromorphic `1`-form
of order at least `-D x`, at the points where `D x ≤ 0` it is holomorphic, and at the finitely many
points where `D x > 0` its value is `0`.
Values are pinned at every point, so a section is determined by its values outside a closed
discrete set (`TauCeti.RiemannSurface.eq_of_eventually_codiscrete`). The normalization does not
depend on the form, so these fields form a complex vector space under the pointwise operations,
and a sheaf, by Mathlib's sheaf of sections satisfying a local predicate
(`TopCat.subsheafToTypes`).

For `D ≤ E` the inclusion `Ω_D ⟶ Ω_E` sets to `0` the values at the new poles allowed by `E`
(`TauCeti.RiemannSurface.differentialSheafMapOfLE_app`). It is injective on sections and
functorial in the divisor.

## Main definitions

* `TauCeti.RiemannSurface.IsDifferentialSectionAt D ω x`: `ω` is a local section of `Ω_D` at `x`.
* `TauCeti.RiemannSurface.differentialSections D U`: the complex vector space of sections of `Ω_D`
  over an open set `U`, as fields of covectors on `U`.
* `TauCeti.RiemannSurface.differentialSheaf D`: the sheaf `Ω_D` of complex vector spaces.
* `TauCeti.RiemannSurface.differentialSectionsZeroEquiv`: the global sections of `Ω_0` are the
  holomorphic `1`-forms `TauCeti.RiemannSurface.holomorphicOneForms`.
* `TauCeti.RiemannSurface.differentialSheafMapOfLE`: the inclusion `Ω_D ⟶ Ω_E` for `D ≤ E`, a
  monomorphism.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the sheaves `Ω_D` and Serre duality).
* The sheaf of vector spaces is assembled from a sheaf of types as for
  `TauCeti.RiemannSurface.divisorSheaf`, following `smoothSheafCommRing` in
  `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`, by Heather Macbeth and Adam Topaz.
-/

public noncomputable section

open CategoryTheory Filter Opposite Set TopologicalSpace Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open _root_.TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

section

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A `1`-form `ω` is a *local section of `Ω_D` at `x`* when it is meromorphic at `x` with order at
least `-D x`, it is holomorphic at `x` when `D x ≤ 0`, and it takes the value `0` at `x` when
`0 < D x`. -/
structure IsDifferentialSectionAt (D : WeilDivisor X) (ω : OneForm X) (x : X) : Prop where
  /-- The `1`-form is meromorphic at `x`. -/
  meromorphicAt : ω.MeromorphicAt x
  /-- The order at `x` is at least `-D x`: a pole of order at most `D x` when `0 < D x`, a zero
  of order at least `-D x` when `D x < 0`. -/
  neg_le_order : ((-D x : ℤ) : WithTop ℤ) ≤ ω.order x
  /-- Where `D` allows no pole, the `1`-form is holomorphic at `x`. -/
  holomorphicAt : D x ≤ 0 → ω.HolomorphicAt x
  /-- Where `D` allows a pole, the value at `x` is the normalized value `0`. -/
  apply_eq_zero : 0 < D x → ω x = 0

namespace IsDifferentialSectionAt

variable {D : WeilDivisor X} {ω η : OneForm X} {x : X}

/-- Being a local section of `Ω_D` at `x` only depends on the germ at `x`. -/
theorem congr (hω : IsDifferentialSectionAt D ω x) (h : ∀ᶠ y in 𝓝 x, ω y = η y) :
    IsDifferentialSectionAt D η x where
  meromorphicAt := hω.meromorphicAt.congr (h.filter_mono nhdsWithin_le_nhds)
  neg_le_order := OneForm.order_congr (h.filter_mono nhdsWithin_le_nhds) ▸ hω.neg_le_order
  holomorphicAt hD := (hω.holomorphicAt hD).congr h
  apply_eq_zero hD := h.self_of_nhds ▸ hω.apply_eq_zero hD

variable (D x) in
/-- The zero `1`-form is a local section of `Ω_D`. -/
theorem zero : IsDifferentialSectionAt D 0 x where
  meromorphicAt := OneForm.meromorphicAt_zero x
  neg_le_order := by simp
  holomorphicAt _ := OneForm.holomorphicAt_zero x
  apply_eq_zero _ := rfl

/-- Local sections of `Ω_D` are closed under addition. -/
theorem add (hω : IsDifferentialSectionAt D ω x) (hη : IsDifferentialSectionAt D η x) :
    IsDifferentialSectionAt D (ω + η) x where
  meromorphicAt := hω.meromorphicAt.add hη.meromorphicAt
  neg_le_order := (le_min hω.neg_le_order hη.neg_le_order).trans
    (OneForm.order_add hω.meromorphicAt hη.meromorphicAt)
  holomorphicAt hD := (hω.holomorphicAt hD).add (hη.holomorphicAt hD)
  apply_eq_zero hD := by simp [hω.apply_eq_zero hD, hη.apply_eq_zero hD]

/-- Local sections of `Ω_D` are closed under multiplication by constants. -/
theorem const_smul (hω : IsDifferentialSectionAt D ω x) (c : ℂ) :
    IsDifferentialSectionAt D (c • ω) x := by
  rcases eq_or_ne c 0 with rfl | hc
  · -- `rw [zero_smul]` does not match the scalar-action instance found through `TangentSpace`
    -- (see below), but the term `zero_smul ℂ ω` elaborates against it.
    exact (zero_smul ℂ ω).symm ▸ zero D x
  exact
  { meromorphicAt := hω.meromorphicAt.const_smul c
    neg_le_order := by simpa [OneForm.order_const_smul hc] using hω.neg_le_order
    holomorphicAt := fun hD ↦ (hω.holomorphicAt hD).const_smul c
    apply_eq_zero := fun hD ↦ by
      rw [Pi.smul_apply, hω.apply_eq_zero hD]
      -- `simp` and `rw [smul_zero]` do not fire here: the scalar action on the fibre is found as
      -- `ContinuousLinearMap.instSMul` through `TangentSpace`, which does not unify with the
      -- `SMulZeroClass` path at reducible transparency, so the fibre type is supplied explicitly.
      exact smul_zero (A := TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ) c }

/-- **Increasing the divisor.** For `D ≤ E`, a local section of `Ω_D` gives a local section of
`Ω_E` after its values at the poles allowed by `E` are set to `0`. -/
theorem ite_le_zero (hω : IsDifferentialSectionAt D ω x) {E : WeilDivisor X} (h : D ≤ E) :
    IsDifferentialSectionAt E (fun y ↦ if E y ≤ 0 then ω y else 0) x := by
  have hev : ∀ᶠ y in 𝓝[≠] x, ω y = if E y ≤ 0 then ω y else 0 := by
    have := ChartedSpace.t1Space ℂ X
    filter_upwards [E.eventually_eq_zero_nhdsNE x] with y hy
    rw [ite_eq_left hy.le]
  exact
  { meromorphicAt := hω.meromorphicAt.congr hev
    neg_le_order := by
      rw [← OneForm.order_congr hev]
      exact le_trans (by exact_mod_cast neg_le_neg (h x)) hω.neg_le_order
    holomorphicAt := fun hE ↦ (hω.holomorphicAt ((h x).trans hE)).congr <| by
      rw [← nhdsNE_sup_pure x, eventually_sup, eventually_pure, ite_eq_left hE]
      exact ⟨hev, rfl⟩
    apply_eq_zero := fun hE ↦ ite_eq_right (not_le.2 hE) }

end IsDifferentialSectionAt

/-- Away from the support of `D`, the local sections of `Ω_D` are the holomorphic `1`-forms. -/
theorem isDifferentialSectionAt_iff_of_eq_zero {D : WeilDivisor X} {ω : OneForm X} {x : X}
    (hD : D x = 0) : IsDifferentialSectionAt D ω x ↔ ω.HolomorphicAt x :=
  ⟨fun hω ↦ hω.holomorphicAt hD.le, fun hω ↦
    { meromorphicAt := hω.meromorphicAt
      neg_le_order := by simpa [hD] using hω.order_nonneg
      holomorphicAt := fun _ ↦ hω
      apply_eq_zero := fun h ↦ absurd hD h.ne' }⟩

/-- The sections of `Ω_D` over an open set `U`, as fields of covectors over `U`: near each point
of `U` they agree with a local section of `Ω_D` in the sense of `IsDifferentialSectionAt`. -/
def differentialSections (D : WeilDivisor X) (U : Opens X) :
    Submodule ℂ ((x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ) where
  carrier := {s | ∀ x : U, ∃ ω : OneForm X, IsDifferentialSectionAt D ω x ∧
    ∀ᶠ y in 𝓝 x, s y = ω y}
  zero_mem' x := ⟨0, .zero D x, Eventually.of_forall fun _ ↦ rfl⟩
  add_mem' {s₁ s₂} hs₁ hs₂ x := by
    obtain ⟨ω₁, h₁, e₁⟩ := hs₁ x
    obtain ⟨ω₂, h₂, e₂⟩ := hs₂ x
    refine ⟨ω₁ + ω₂, h₁.add h₂, ?_⟩
    filter_upwards [e₁, e₂] with y hy₁ hy₂
    rw [Pi.add_apply, Pi.add_apply, hy₁, hy₂]
  smul_mem' c s hs x := by
    obtain ⟨ω, h, e⟩ := hs x
    refine ⟨c • ω, h.const_smul c, ?_⟩
    filter_upwards [e] with y hy
    rw [Pi.smul_apply, Pi.smul_apply, hy]

variable {D : WeilDivisor X}

/-- Membership in `differentialSections D U`: near every point of `U` the covector field agrees
with a local section of `Ω_D` on `X`. -/
@[simp]
theorem mem_differentialSections_iff {U : Opens X}
    {s : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ} :
    s ∈ differentialSections D U ↔
      ∀ x : U, ∃ ω : OneForm X, IsDifferentialSectionAt D ω x ∧ ∀ᶠ y in 𝓝 x, s y = ω y :=
  Iff.rfl

/-- A `1`-form on `X` which is a local section of `Ω_D` at every point of `U` restricts to a
section of `Ω_D` over `U`. -/
theorem restrict_mem_differentialSections {U : Opens X} {ω : OneForm X}
    (hω : ∀ x ∈ U, IsDifferentialSectionAt D ω x) :
    (fun x : U ↦ ω x) ∈ differentialSections D U :=
  fun x ↦ ⟨ω, hω x x.2, Eventually.of_forall fun _ ↦ rfl⟩

/-- Sections of `Ω_D` restrict to smaller open sets. -/
theorem comp_inclusion_mem_differentialSections {U V : Opens X} (h : V ≤ U)
    {s : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ} (hs : s ∈ differentialSections D U) :
    (fun x : V ↦ s (Opens.inclusion h x)) ∈ differentialSections D V := by
  intro x
  obtain ⟨ω, hω, e⟩ := hs (Opens.inclusion h x)
  exact ⟨ω, hω, ((continuous_inclusion h).tendsto x).eventually e⟩

/-- A section of `Ω_D` vanishes at the poles allowed by `D`. -/
theorem apply_eq_zero_of_mem_differentialSections {U : Opens X}
    {s : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ} (hs : s ∈ differentialSections D U)
    {x : U} (hx : 0 < D x) : s x = 0 := by
  obtain ⟨ω, hω, e⟩ := hs x
  rw [e.self_of_nhds, hω.apply_eq_zero hx]

/-- Membership in `differentialSections D U` is local on `U`. -/
private theorem mem_differentialSections_of_local {U : Opens X}
    (s : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ)
    (hs : ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (i : V ⟶ U),
      (fun y : V ↦ s (Opens.inclusion i.le y)) ∈ differentialSections D V) :
    s ∈ differentialSections D U := by
  intro x
  obtain ⟨V, hxV, i, hV⟩ := hs x
  obtain ⟨ω, hω, e⟩ := hV ⟨x, hxV⟩
  refine ⟨ω, hω, ?_⟩
  have hmap := (Opens.isOpenEmbedding_of_le i.le).map_nhds_eq ⟨x, hxV⟩
  rw [Set.inclusion_right] at hmap
  rw [← hmap]
  exact e

/-- Membership in `differentialSections` as a local predicate on covector fields. -/
private def differentialLocalPredicate (D : WeilDivisor X) :
    TopCat.LocalPredicate (fun x : TopCat.of X ↦ TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ) where
  pred {U} s := s ∈ differentialSections D U
  res {_ _} i _ hs := comp_inclusion_mem_differentialSections i.le hs
  locality {_} s hs := mem_differentialSections_of_local s hs

/-- Restriction of sections of `Ω_D` to a smaller open set. -/
private def differentialRestrict (D : WeilDivisor X) {U V : Opens X} (i : V ⟶ U) :
    differentialSections D U →ₗ[ℂ] differentialSections D V where
  toFun s :=
    ⟨fun y ↦ s.1 (Opens.inclusion i.le y), comp_inclusion_mem_differentialSections i.le s.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The presheaf of complex vector spaces of sections of `Ω_D`. -/
private def differentialPresheaf (D : WeilDivisor X) :
    TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj U := ModuleCat.of ℂ (differentialSections D U.unop)
  map h := ModuleCat.ofHom (differentialRestrict D h.unop)
  map_id _ := by
    apply ModuleCat.hom_ext
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    rfl

variable (D) in
/-- The sheaf `Ω_D` of meromorphic `1`-forms with divisor at least `-D` on a Riemann surface, as a
sheaf of complex vector spaces. Its sections over `U` are the covector fields of
`differentialSections D U`: the normalized representatives of meromorphic `1`-forms on `U` with
divisor at least `-D`. -/
def differentialSheaf : TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj := differentialPresheaf D
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{u} ℂ))]
    -- The underlying presheaf of sets is the subsheaf of covector fields cut out by the predicate.
    exact TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun _ ↦ (Equiv.refl _).toIso)
      fun _ ↦ rfl) (TopCat.subsheafToTypes (differentialLocalPredicate D)).property

/-- The sections of `Ω_D` over `U` are the sections of the submodule `differentialSections D U`. -/
theorem differentialSheaf_obj (D : WeilDivisor X) (U : Opens X) :
    (differentialSheaf D).obj.obj (op U) = ModuleCat.of ℂ (differentialSections D U) := (rfl)

/-- Read a section of `Ω_D` over `U` as a covector field on `U` in `differentialSections D U`. -/
def differentialSheafSectionsEquiv (D : WeilDivisor X) (U : Opens X) :
    (differentialSheaf D).obj.obj (op U) ≃ₗ[ℂ] differentialSections D U :=
  LinearEquiv.refl ℂ _

/-- Restriction of sections of `Ω_D` is restriction of covector fields. -/
@[simp]
theorem differentialSheafSectionsEquiv_map (D : WeilDivisor X) {U V : Opens X} (h : V ⟶ U)
    (s : (differentialSheaf D).obj.obj (op U)) (y : V) :
    (differentialSheafSectionsEquiv D V ((differentialSheaf D).obj.map h.op s)).1 y =
      (differentialSheafSectionsEquiv D U s).1 (Opens.inclusion h.le y) := (rfl)

section IsManifold

variable [IsManifold 𝓘(ℂ) 1 X]

/-- **Sections of `Ω_D` are meromorphic `1`-forms up to discrete sets.** Two sections of `Ω_D`
over `U` which agree outside a closed discrete subset of `U` are equal. -/
theorem eq_of_eventually_codiscrete {U : Opens X}
    {s t : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ} (hs : s ∈ differentialSections D U)
    (ht : t ∈ differentialSections D U) (h : ∀ᶠ y in codiscrete U, s y = t y) : s = t := by
  funext x
  obtain ⟨ω, hω, es⟩ := hs x
  obtain ⟨η, hη, et⟩ := ht x
  rcases lt_or_ge 0 (D x) with hD | hD
  · rw [es.self_of_nhds, et.self_of_nhds, hω.apply_eq_zero hD, hη.apply_eq_zero hD]
  -- Near `x`, the two local `1`-forms agree off `x`, so their values at `x` agree by holomorphy.
  have hst : ∀ᶠ y : U in 𝓝[≠] x, s y = t y :=
    (eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.1 h x (mem_univ _)).mono
      fun y hy ↦ hy (mem_univ y)
  have hωη : ∀ᶠ y in 𝓝[≠] (x : X), ω y = η y := by
    have hloc : ∀ᶠ y : U in 𝓝[≠] x, ω y = η y := by
      filter_upwards [hst, es.filter_mono nhdsWithin_le_nhds, et.filter_mono nhdsWithin_le_nhds]
        with y hy hsy hty
      rw [← hsy, ← hty, hy]
    rw [eventually_nhdsWithin_iff] at hloc ⊢
    rw [← U.isOpenEmbedding'.map_nhds_eq x, eventually_map]
    filter_upwards [hloc] with y hy hne
    exact hy fun h ↦ hne (congrArg Subtype.val h)
  rw [es.self_of_nhds, et.self_of_nhds]
  exact (hω.holomorphicAt hD).apply_eq_of_eventually (hη.holomorphicAt hD) hωη

end IsManifold

/-- The global sections of `Ω_0`, read as `1`-forms on `X`, are holomorphic. -/
private theorem holomorphicAt_of_mem_differentialSections_zero
    {s : (x : (⊤ : Opens X)) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ}
    (hs : s ∈ differentialSections (0 : WeilDivisor X) ⊤) (x : X) :
    OneForm.HolomorphicAt (fun y ↦ s ⟨y, trivial⟩) x := by
  obtain ⟨η, hη, e⟩ := hs ⟨x, trivial⟩
  refine ((isDifferentialSectionAt_iff_of_eq_zero rfl).1 hη).congr ?_
  rw [← (⊤ : Opens X).isOpenEmbedding'.map_nhds_eq ⟨x, trivial⟩, eventually_map]
  exact e.mono fun y hy ↦ hy.symm

/-- **`H⁰(X, Ω) ≅` holomorphic `1`-forms.** The global sections of `Ω_0` are the holomorphic
`1`-forms on `X`. -/
def differentialSectionsZeroEquiv :
    differentialSections (0 : WeilDivisor X) ⊤ ≃ₗ[ℂ] holomorphicOneForms X where
  toFun s := ⟨fun y ↦ s.1 ⟨y, trivial⟩,
    mem_holomorphicOneForms.2 (holomorphicAt_of_mem_differentialSections_zero s.2)⟩
  invFun ω := ⟨fun y ↦ ω.1 y, restrict_mem_differentialSections fun x _ ↦
    (isDifferentialSectionAt_iff_of_eq_zero rfl).2 (mem_holomorphicOneForms.1 ω.2 x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem differentialSectionsZeroEquiv_apply (s : differentialSections (0 : WeilDivisor X) ⊤)
    (x : X) : (differentialSectionsZeroEquiv s).1 x = s.1 ⟨x, trivial⟩ :=
  (rfl)

@[simp]
theorem differentialSectionsZeroEquiv_symm_apply (ω : holomorphicOneForms X)
    (x : (⊤ : Opens X)) : (differentialSectionsZeroEquiv.symm ω).1 x = ω.1 x :=
  (rfl)

/-! ### Increasing the divisor -/

/-- For `D ≤ E`, a section of `Ω_D` gives a section of `Ω_E` after its values at the poles
allowed by `E` are set to `0`. -/
theorem ite_mem_differentialSections {E : WeilDivisor X} (h : D ≤ E) {U : Opens X}
    {s : (x : U) → TangentSpace 𝓘(ℂ) (x : X) →L[ℂ] ℂ} (hs : s ∈ differentialSections D U) :
    (fun y : U ↦ if E y ≤ 0 then s y else 0) ∈ differentialSections E U := by
  intro x
  obtain ⟨ω, hω, e⟩ := hs x
  refine ⟨_, hω.ite_le_zero h, ?_⟩
  filter_upwards [e] with y hy
  by_cases hy' : E y ≤ 0
  · rw [ite_eq_left hy', ite_eq_left hy', hy]
  · rw [ite_eq_right hy', ite_eq_right hy']

/-- The map `Ω_D(U) → Ω_E(U)` for `D ≤ E`. -/
private def differentialSectionsMapOfLE {E : WeilDivisor X} (h : D ≤ E) (U : Opens X) :
    differentialSections D U →ₗ[ℂ] differentialSections E U where
  toFun s := ⟨fun y ↦ if E y ≤ 0 then s.1 y else 0, ite_mem_differentialSections h s.2⟩
  map_add' s t := by
    apply Subtype.ext
    funext y
    by_cases hy : E y ≤ 0
    · simp [hy]
    · simp [hy]
  map_smul' c s := by
    apply Subtype.ext
    funext y
    by_cases hy : E y ≤ 0
    · simp [hy]
    · simp only [hy, ite_false, Submodule.coe_smul_of_tower, RingHom.id_apply, Pi.smul_apply]
      -- As in `IsDifferentialSectionAt.const_smul`, `smul_zero` needs the fibre type explicitly.
      exact (smul_zero (A := TangentSpace 𝓘(ℂ) (y : X) →L[ℂ] ℂ) c).symm

/-- **The inclusion `Ω_D ⟶ Ω_E` for `D ≤ E`.** On sections it is the identity on meromorphic
`1`-forms; as covector fields, the values at the poles allowed by `E` are set to `0`
(`differentialSheafMapOfLE_app`). -/
def differentialSheafMapOfLE {E : WeilDivisor X} (h : D ≤ E) :
    differentialSheaf D ⟶ differentialSheaf E where
  hom.app U := ModuleCat.ofHom (differentialSectionsMapOfLE h U.unop)
  hom.naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext y
    rfl

-- Index past the unexposed section carriers, so that simp applies the lemma downstream.
/-- The map of sections underlying `differentialSheafMapOfLE`. -/
@[simp]
theorem differentialSheafMapOfLE_app {E : WeilDivisor X} (h : D ≤ E) (U : Opens X)
    (s : (differentialSheaf D).obj.obj (op U)) (y : U) :
    (no_index (differentialSheafSectionsEquiv E U
      ((differentialSheafMapOfLE h).hom.app (op U) s))).1 y =
      if E y ≤ 0 then (differentialSheafSectionsEquiv D U s).1 y else 0 := (rfl)

section IsManifold

variable [IsManifold 𝓘(ℂ) 1 X]

/-- The inclusion `Ω_D ⟶ Ω_E` is injective on sections. -/
theorem differentialSheafMapOfLE_app_injective {E : WeilDivisor X} (h : D ≤ E) (U : Opens X) :
    Function.Injective ((differentialSheafMapOfLE h).hom.app (op U)) := by
  intro s t hst
  apply (differentialSheafSectionsEquiv D U).injective
  apply Subtype.ext
  refine eq_of_eventually_codiscrete (differentialSheafSectionsEquiv D U s).2
    (differentialSheafSectionsEquiv D U t).2 ?_
  have hst' (y : U) := congrArg (fun r ↦ (differentialSheafSectionsEquiv E U r).1 y) hst
  simp only [differentialSheafMapOfLE_app] at hst'
  refine eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun x _ ↦ ?_
  -- Near `x`, every point other than `x` lies off the poles allowed by `E`.
  have hval : Tendsto (Subtype.val : U → X) (𝓝[≠] x) (𝓝[≠] (x : X)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (continuous_subtype_val.continuousAt.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ hy ↦ Subtype.coe_injective.ne hy)
  have := ChartedSpace.t1Space ℂ X
  have hev : ∀ᶠ y : U in 𝓝[≠] x, E y ≤ 0 :=
    hval.eventually ((E.eventually_eq_zero_nhdsNE x).mono fun _ hy ↦ hy.le)
  filter_upwards [hev] with y hy _
  simpa [ite_eq_left hy] using hst' y

end IsManifold

/-- The map `Ω_D ⟶ Ω_D` is the identity. -/
@[simp]
theorem differentialSheafMapOfLE_refl :
    differentialSheafMapOfLE (le_refl D) = 𝟙 (differentialSheaf D) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply (differentialSheafSectionsEquiv D U.unop).injective
  apply Subtype.ext
  funext y
  rw [differentialSheafMapOfLE_app]
  by_cases hy : D y ≤ 0
  · exact ite_eq_left hy
  · exact (ite_eq_right hy).trans (apply_eq_zero_of_mem_differentialSections
      (differentialSheafSectionsEquiv D U.unop s).2 (not_le.1 hy)).symm

/-- The maps `Ω_D ⟶ Ω_E` compose. -/
@[reassoc (attr := simp)]
theorem differentialSheafMapOfLE_comp {E F : WeilDivisor X} (hDE : D ≤ E) (hEF : E ≤ F) :
    differentialSheafMapOfLE hDE ≫ differentialSheafMapOfLE hEF =
      differentialSheafMapOfLE (hDE.trans hEF) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply (differentialSheafSectionsEquiv F U.unop).injective
  apply Subtype.ext
  funext y
  rw [TopCat.Sheaf.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, differentialSheafMapOfLE_app,
    differentialSheafMapOfLE_app, differentialSheafMapOfLE_app]
  by_cases hy : F y ≤ 0
  · rw [ite_eq_left hy, ite_eq_left hy, ite_eq_left ((hEF y).trans hy)]
  · rw [ite_eq_right hy, ite_eq_right hy]

section IsManifold

variable [IsManifold 𝓘(ℂ) 1 X]

/-- The map `Ω_D ⟶ Ω_E` is a monomorphism of sheaves. -/
instance differentialSheafMapOfLE_mono {E : WeilDivisor X} (h : D ≤ E) :
    Mono (differentialSheafMapOfLE h) := by
  have (U : (Opens X)ᵒᵖ) : Mono ((differentialSheafMapOfLE h).hom.app U) :=
    ConcreteCategory.mono_of_injective _ (differentialSheafMapOfLE_app_injective h U.unop)
  exact (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} ℂ)).mono_of_mono_map
    (NatTrans.mono_of_mono_app (differentialSheafMapOfLE h).hom)

end IsManifold

end

end TauCeti.RiemannSurface
