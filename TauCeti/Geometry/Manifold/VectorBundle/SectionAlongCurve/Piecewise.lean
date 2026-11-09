/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PiecewisePath
public import TauCeti.Geometry.Manifold.VectorBundle.Translate
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Piecewise smooth sections along an interval

A continuous piecewise `C^n` field along a curve has a finite partition on whose closed pieces
its total-space lift is `C^n`. Different fields need not use the same partition: pairing their
lifts supplies a common refinement, so addition preserves this regularity.

`TauCeti.Manifold.piecewiseContMDiffSectionAlong` is the real submodule of fields defined only
on the closed parameter interval. Membership is witnessed by a piecewise smooth extension;
neither that extension nor its partition is part of a field's identity. Thus pointwise equality
on the interval is extensional, and no values outside the interval are retained. Evaluation
and restriction are linear, and `PiecewiseContMDiffSectionAlong.endpointZero` is the kernel of
the two endpoint evaluations. This gives the ambient field space and its fixed-endpoint
subspace for index forms; other endpoint conditions can be imposed on the same ambient space.

The construction works for arbitrary real vector bundles and piecewise smooth base curves,
without a metric or connection. In particular it applies to tangent fields along geodesics.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press
  (1963), §13: continuous piecewise smooth fields and endpoint constraints.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {γ : ℝ → M} {n : ℕ∞ω} {a b : ℝ}

/-- Addition of piecewise `C^n` fields along the same curve preserves piecewise regularity,
even when their witnessing partitions are different. -/
theorem IsPiecewiseContMDiffOn.add_sectionAlong {U W : ∀ t, V (γ t)}
    (hU : IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (U t)) a b)
    (hW : IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (W t)) a b) :
    IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (U t + W t)) a b := by
  obtain ⟨k, τ, hτa, hτb, hτ, hpair⟩ := (hU.prodMk hW).exists_partition
  exact .of_partition τ hτa hτb hτ fun i ↦
    (contMDiff_fst.comp_contMDiffOn (hpair i)).add_sectionAlong
      (contMDiff_snd.comp_contMDiffOn (hpair i))

/-- Multiplication of a piecewise `C^n` field by a piecewise `C^n` real function preserves
piecewise regularity. -/
theorem IsPiecewiseContMDiffOn.smul_sectionAlong {U : ∀ t, V (γ t)} {f : ℝ → ℝ}
    (hU : IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (U t)) a b)
    (hf : IsPiecewiseContMDiffOn 𝓘(ℝ, ℝ) n f a b) :
    IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (f t • U t)) a b := by
  obtain ⟨k, τ, hτa, hτb, hτ, hpair⟩ := (hf.prodMk hU).exists_partition
  exact .of_partition τ hτa hτb hτ fun i ↦
    (contMDiff_fst.comp_contMDiffOn (hpair i)).smul_totalSpace
      (contMDiff_snd.comp_contMDiffOn (hpair i))

/-- The real submodule of continuous piecewise `C^n` sections along `γ` on `[a,b]`.
Only interval values are carried; the extension and partition witnessing membership are
existential. The base curve is assumed piecewise `C^n` so that the zero field belongs. -/
def piecewiseContMDiffSectionAlong (hγ : IsPiecewiseContMDiffOn I n γ a b) :
    Submodule ℝ (∀ t : Icc a b, V (γ t)) where
  carrier := {W | ∃ U : ∀ t, V (γ t),
    IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (U t)) a b ∧ ∀ t : Icc a b, U t = W t}
  zero_mem' := by
    obtain ⟨k, τ, hτa, hτb, hτ, hpieces⟩ := hγ.exists_partition
    refine ⟨0, .of_partition τ hτa hτb hτ (fun i ↦ ?_), fun _ ↦ rfl⟩
    exact (Bundle.contMDiff_zeroSection ℝ V).comp_contMDiffOn (hpieces i)
  add_mem' := by
    rintro U W ⟨U', hU, hU'⟩ ⟨W', hW, hW'⟩
    exact ⟨U' + W', hU.add_sectionAlong hW, fun t ↦ by simp [hU', hW']⟩
  smul_mem' := by
    rintro c W ⟨U, hU, hU'⟩
    refine ⟨c • U, ?_, fun t ↦ by simp [hU']⟩
    exact hU.smul_sectionAlong (.of_contMDiffOn hγ.lt contMDiffOn_const)

/-- Membership in the interval section submodule is exactly the existence of a piecewise
`C^n` total-space lift extending the given interval values. -/
@[simp]
theorem mem_piecewiseContMDiffSectionAlong_iff (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (W : ∀ t : Icc a b, V (γ t)) :
    W ∈ piecewiseContMDiffSectionAlong (F := F) (V := V) hγ ↔
      ∃ U : ∀ t, V (γ t), IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
        (fun t ↦ TotalSpace.mk' F (γ t) (U t)) a b ∧ ∀ t : Icc a b, U t = W t :=
  (Iff.rfl)

/-- Continuous piecewise `C^n` sections of a real vector bundle along a compact interval. -/
abbrev PiecewiseContMDiffSectionAlong (hγ : IsPiecewiseContMDiffOn I n γ a b) :=
  ↥(piecewiseContMDiffSectionAlong (F := F) (V := V) hγ)

namespace PiecewiseContMDiffSectionAlong

variable {hγ : IsPiecewiseContMDiffOn I n γ a b}

/-- Restrict a piecewise smooth field on the real parameter line to its interval. -/
def ofPiecewise (U : ∀ t, V (γ t))
    (hU : IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (U t)) a b) :
    PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ :=
  ⟨fun t ↦ U t, U, hU, fun _ ↦ rfl⟩

/-- The field constructed from an extension has that extension's interval values. -/
@[simp]
theorem ofPiecewise_apply (U : ∀ t, V (γ t))
    (hU : IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (U t)) a b) (t : Icc a b) :
    (ofPiecewise (hγ := hγ) U hU).val t = U t :=
  (rfl)

/-- Every bundled field has a piecewise smooth extension agreeing on its interval. -/
theorem exists_extension (W : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ) :
    ∃ U : ∀ t, V (γ t), IsPiecewiseContMDiffOn (I.prod 𝓘(ℝ, F)) n
      (fun t ↦ TotalSpace.mk' F (γ t) (U t)) a b ∧ ∀ t : Icc a b, U t = W.val t :=
  W.property

/-- Bundled fields are determined by their interval values. -/
@[ext]
theorem ext {U W : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ}
    (h : ∀ t, U.val t = W.val t) : U = W :=
  Subtype.ext (funext h)

/-- The total-space lift of a piecewise smooth interval field is continuous, including at
partition vertices and both endpoints. -/
theorem continuous (W : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ) :
    Continuous (fun t : Icc a b ↦ TotalSpace.mk' F (γ t) (W.val t)) := by
  obtain ⟨U, hU, hUW⟩ := W.exists_extension
  have h := hU.continuousOn.comp_continuous continuous_subtype_val (fun t ↦ t.property)
  exact h.congr fun t ↦ congrArg (TotalSpace.mk' F (γ t)) (hUW t)

/-- Evaluation at an interval parameter is a real linear map into its fibre. -/
def eval (t : Icc a b) : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ →ₗ[ℝ] V (γ t) :=
  (LinearMap.proj t).comp (piecewiseContMDiffSectionAlong (F := F) (V := V) hγ).subtype

/-- Evaluation returns the field's value at the specified parameter. -/
@[simp]
theorem eval_apply (t : Icc a b) (W : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ) :
    eval t W = W.val t :=
  (rfl)

/-- The pair of endpoint values, as a real linear map. -/
def endpointValues : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ →ₗ[ℝ]
    V (γ a) × V (γ b) :=
  (eval ⟨a, le_rfl, hγ.lt.le⟩).prod (eval ⟨b, hγ.lt.le, le_rfl⟩)

/-- The endpoint map evaluates the same field at the two ends of the interval. -/
@[simp]
theorem endpointValues_apply (W : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ) :
    endpointValues W = (W.val ⟨a, le_rfl, hγ.lt.le⟩, W.val ⟨b, hγ.lt.le, le_rfl⟩) :=
  (rfl)

/-- The fixed-endpoint field space is the kernel of the pair of endpoint evaluations. -/
def endpointZero : Submodule ℝ (PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ) :=
  LinearMap.ker endpointValues

/-- A field belongs to the fixed-endpoint subspace exactly when both endpoint values vanish. -/
@[simp]
theorem mem_endpointZero_iff (W : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ) :
    W ∈ endpointZero ↔
      W.val ⟨a, le_rfl, hγ.lt.le⟩ = 0 ∧ W.val ⟨b, hγ.lt.le, le_rfl⟩ = 0 := by
  simp [endpointZero, Prod.ext_iff]

/-- Restrict a field linearly to a nondegenerate closed subinterval. The extension witnessing
regularity can be retained, while its witnessing partition is restricted. -/
def restrict {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) :
    PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ →ₗ[ℝ]
      PiecewiseContMDiffSectionAlong (F := F) (V := V) (hγ.mono hac hcd hdb) where
  toFun W := ⟨fun t ↦ W.val ⟨t, hac.trans t.property.1, t.property.2.trans hdb⟩, by
    obtain ⟨U, hU, hUW⟩ := W.exists_extension
    exact ⟨U, hU.mono hac hcd hdb, fun t ↦
      hUW ⟨t, hac.trans t.property.1, t.property.2.trans hdb⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction evaluates at the same real parameter in the larger interval. -/
@[simp]
theorem restrict_apply {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (W : PiecewiseContMDiffSectionAlong (F := F) (V := V) hγ) (t : Icc c d) :
    (restrict hac hcd hdb W).val t =
      W.val ⟨t, hac.trans t.property.1, t.property.2.trans hdb⟩ :=
  (rfl)

/-- Restricting to the original interval is the identity linear map. -/
@[simp]
theorem restrict_self :
    restrict (hγ := hγ) (V := V) (F := F) le_rfl hγ.lt le_rfl = LinearMap.id := by
  ext W t
  rfl

/-- Successive restrictions to nested nondegenerate intervals equal direct restriction. -/
theorem restrict_comp {c d e f : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hce : c ≤ e) (hef : e < f) (hfd : f ≤ d) :
    (restrict (hγ := hγ.mono hac hcd hdb) (F := F) (V := V) hce hef hfd).comp
        (restrict hac hcd hdb) =
      restrict (hγ := hγ) (hac.trans hce) hef (hfd.trans hdb) := by
  ext W t
  rfl

end PiecewiseContMDiffSectionAlong

end TauCeti.Manifold
