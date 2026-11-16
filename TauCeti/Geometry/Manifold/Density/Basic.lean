/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Orientation
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Topology.PartitionOfUnity.Basic

/-!
# Rough densities on manifolds and the density of an oriented top form

A rough density of degree `m` on a manifold assigns to each point a density of degree `m` on
its tangent space, with no regularity in the base point; in top degree these are sections of
the density line bundle `TauCeti.DensityBundle`. On an oriented manifold, a top form `φ`
determines the rough density `φ.toDensity o`. At each point it agrees with `φ` on positively
oriented bases of the tangent space and with `-φ` on negatively oriented ones. It is additive
and homogeneous in `φ`, negated by reversing the orientation, and determines `φ` once the
orientation is fixed. This is the comparison through which oriented integration of top forms
becomes a special case of the orientation-free integration of densities.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16,
  Densities.
-/

public section

noncomputable section

open Module Set

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]

/-- A rough density of degree `m`: a density of degree `m` on each tangent space, with no
regularity in the base point. -/
abbrev RoughDensity (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (m : ℕ) : Type _ :=
  (x : M) → Density (TangentSpace I x) m

namespace RoughDensity

variable {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- A point lies in the support of `μ` (in `Density E m`) iff `μ x ≠ 0`. -/
theorem mem_support_iff {μ : RoughDensity I M m} {x : M} :
    x ∈ Function.support (M := Density E m) μ ↔ μ x ≠ 0 := Iff.rfl

/-- Pointwise scalar multiplication does not enlarge the topological support of `μ`. -/
theorem tsupport_fun_smul_subset_right (f : M → ℝ) (μ : RoughDensity I M m) :
    _root_.tsupport (α := Density E m) (fun x ↦ f x • μ x : RoughDensity I M m) ⊆
      _root_.tsupport (α := Density E m) μ :=
  -- `TangentSpace I x` is definitionally `E`, giving fixed codomain `Density E m`.
  _root_.tsupport_smul_subset_right f (show M → Density E m from μ)

/-- Pointwise scalar multiplication has support contained in `tsupport f`. -/
theorem tsupport_fun_smul_subset_left (f : M → ℝ) (μ : RoughDensity I M m) :
    _root_.tsupport (α := Density E m) (fun x ↦ f x • μ x : RoughDensity I M m) ⊆
      _root_.tsupport f :=
  -- `TangentSpace I x` is definitionally `E`, giving fixed codomain `Density E m`.
  _root_.tsupport_smul_subset_left f (show M → Density E m from μ)

/-- Constant scalar multiplication does not enlarge `tsupport μ`. -/
theorem tsupport_smul_subset (c : ℝ) (μ : RoughDensity I M m) :
    _root_.tsupport (α := Density E m) (c • μ) ⊆ _root_.tsupport (α := Density E m) μ :=
  tsupport_fun_smul_subset_right (fun _ ↦ c) μ

/-- Multiplication by a nonzero constant preserves `tsupport μ`. -/
theorem tsupport_smul (c : ℝ) (μ : RoughDensity I M m) (hc : c ≠ 0) :
    _root_.tsupport (α := Density E m) (c • μ) = _root_.tsupport (α := Density E m) μ :=
  Subset.antisymm (tsupport_smul_subset c μ) <| by
    simpa only [inv_smul_smul₀ hc] using tsupport_smul_subset c⁻¹ (c • μ)

/-- The topological support of `μ + ν` lies in `tsupport μ ∪ tsupport ν`. -/
theorem tsupport_add (μ ν : RoughDensity I M m) :
    _root_.tsupport (α := Density E m) (μ + ν) ⊆
      _root_.tsupport (α := Density E m) μ ∪ _root_.tsupport (α := Density E m) ν :=
  -- `TangentSpace I x` is definitionally `E`, giving fixed codomain `Density E m`.
  _root_.tsupport_add (show M → Density E m from μ) (show M → Density E m from ν)

/-- The zero rough density has compact topological support. -/
theorem isCompact_tsupport_zero :
    IsCompact (_root_.tsupport (α := Density E m) (0 : RoughDensity I M m)) := by
  -- View the dependent zero section with fixed codomain `Density E m` for `_root_.tsupport_zero`.
  change IsCompact (_root_.tsupport (0 : M → Density E m)); simp

/-- The sum of two compactly supported rough densities has compact topological support. -/
theorem isCompact_tsupport_add {μ ν : RoughDensity I M m}
    (hμ : IsCompact (_root_.tsupport (α := Density E m) μ))
    (hν : IsCompact (_root_.tsupport (α := Density E m) ν)) :
    IsCompact (_root_.tsupport (α := Density E m) (μ + ν)) :=
  -- `TangentSpace I x` is definitionally `E`, giving fixed codomain `Density E m`.
  HasCompactSupport.add (f := (show M → Density E m from μ)) hμ hν

/-- A partition of unity covering `tsupport μ` localizes a compactly supported `μ` into finitely
many terms, with all remaining terms vanishing identically. -/
theorem exists_finset_partition_eq {ι : Type*} (μ : RoughDensity I M m)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ)) {t : Set M}
    (ρ : PartitionOfUnity ι M t) (ht : _root_.tsupport (α := Density E m) μ ⊆ t) :
    ∃ s : Finset ι, μ = (fun x ↦ ∑ i ∈ s, ρ i x • μ x) ∧
      ∀ i ∉ s, (fun x ↦ ρ i x • μ x : RoughDensity I M m) = 0 :=
  -- `TangentSpace I x` is definitionally `E`, giving fixed codomain `Density E m`.
  ρ.exists_finset_eq_sum_smul (show M → Density E m from μ) hc ht

end RoughDensity

variable [FiniteDimensional ℝ E] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] {m : ℕ}

namespace RoughForm

/-- The density of a top form on an oriented manifold: at each point, the density of the
form with respect to the tangent orientation. -/
def toDensity (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    RoughDensity I M m := fun x ↦
  haveI := o.fact_finrank_tangentSpace x
  (φ x).toAlternatingMap.toDensity (o.orientationAt x)

/-- The density of a top form on a basis of a tangent space: the value of the form, negated
when the basis is negatively oriented. -/
theorem toDensity_apply (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : Basis (Fin m) ℝ (TangentSpace I x)) [Decidable (b.orientation = o.orientationAt x)] :
    φ.toDensity o x b = if b.orientation = o.orientationAt x then φ x b else -φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply (φ x).toAlternatingMap (o.orientationAt x) b

/-- Evaluating `φ.toDensity o x` on any tangent basis gives `φ x` on that basis weighted by its
sign relative to `o.orientationAt x`, including in dimension zero. -/
theorem toDensity_apply_basis (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m))
    (x : M) (b : Basis (Fin m) ℝ (TangentSpace I x)) :
    φ.toDensity o x b = (Orientation.signBasis (o.orientationAt x) b : ℝ) * φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply_basis (φ x).toAlternatingMap (o.orientationAt x) b

/-- On a positively oriented basis of a tangent space, the density of a top form is the form
itself. -/
@[simp]
theorem toDensity_apply_of_orientation_eq (φ : RoughForm I M ℝ m)
    {o : Manifold.Orientation I M (Fin m)} {x : M} {b : Basis (Fin m) ℝ (TangentSpace I x)}
    (hb : b.orientation = o.orientationAt x) : φ.toDensity o x b = φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply_of_orientation_eq _ hb

/-- On a negatively oriented basis of a tangent space, the density of a top form is the
negated form. -/
@[simp]
theorem toDensity_apply_of_orientation_eq_neg (φ : RoughForm I M ℝ m)
    {o : Manifold.Orientation I M (Fin m)} {x : M} {b : Basis (Fin m) ℝ (TangentSpace I x)}
    (hb : b.orientation = -o.orientationAt x) : φ.toDensity o x b = -φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply_of_orientation_eq_neg _ hb

/-- The density of a top form on an arbitrary tuple of tangent vectors is the absolute
determinant of the tuple in any positively oriented basis, times the value of the form on that
basis. -/
theorem toDensity_apply_eq_abs_det_mul (φ : RoughForm I M ℝ m)
    {o : Manifold.Orientation I M (Fin m)} {x : M} {b : Basis (Fin m) ℝ (TangentSpace I x)}
    (hb : b.orientation = o.orientationAt x) (v : Fin m → TangentSpace I x) :
    φ.toDensity o x v = |b.det v| * φ x b :=
  have := o.fact_finrank_tangentSpace x
  AlternatingMap.toDensity_apply_eq_abs_det_mul _ hb v

/-- Reversing the orientation negates the density of a top form. -/
@[simp]
theorem toDensity_neg_orientation (φ : RoughForm I M ℝ m)
    (o : Manifold.Orientation I M (Fin m)) : φ.toDensity (-o) = -φ.toDensity o := by
  funext x
  have := o.fact_finrank_tangentSpace x
  simp only [toDensity, Manifold.Orientation.orientationAt_neg,
    AlternatingMap.toDensity_neg_orientation, Pi.neg_apply]

/-- The density of a sum of top forms is the sum of their densities. -/
@[simp]
theorem toDensity_add (φ ψ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    (φ + ψ).toDensity o = φ.toDensity o + ψ.toDensity o := by
  funext x
  have := o.fact_finrank_tangentSpace x
  simp only [toDensity, Pi.add_apply, ContinuousAlternatingMap.toAlternatingMap_add,
    AlternatingMap.toDensity_add]

/-- The density of a scalar multiple of a top form is the scalar multiple of its density. -/
@[simp]
theorem toDensity_smul (c : ℝ) (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    (c • φ).toDensity o = c • φ.toDensity o := by
  funext x
  have := o.fact_finrank_tangentSpace x
  simp only [toDensity, Pi.smul_apply, ContinuousAlternatingMap.toAlternatingMap_smul,
    AlternatingMap.toDensity_smul]

/-- The density of the zero top form is zero. -/
@[simp]
theorem toDensity_zero (o : Manifold.Orientation I M (Fin m)) :
    (0 : RoughForm I M ℝ m).toDensity o = 0 := by
  rw [← zero_smul ℝ (0 : RoughForm I M ℝ m), toDensity_smul, zero_smul]

/-- The density of a negated top form is the negated density. -/
@[simp]
theorem toDensity_neg (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    (-φ).toDensity o = -φ.toDensity o := by
  rw [← neg_one_smul ℝ φ, toDensity_smul, neg_one_smul]

/-- On an oriented manifold, a top form is determined by its density. -/
theorem toDensity_injective (o : Manifold.Orientation I M (Fin m)) :
    Function.Injective fun φ : RoughForm I M ℝ m ↦ φ.toDensity o := by
  intro φ ψ h
  funext x
  have := o.fact_finrank_tangentSpace x
  have hx : (φ x).toAlternatingMap.toDensity (o.orientationAt x) =
      (ψ x).toAlternatingMap.toDensity (o.orientationAt x) := congrFun h x
  rw [← Orientation.densityEquiv_apply, ← Orientation.densityEquiv_apply] at hx
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    ((Orientation.densityEquiv (o.orientationAt x)).injective hx)

/-- Passing from a top form to its density preserves the topological support. -/
@[simp] theorem tsupport_toDensity (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    _root_.tsupport (α := Density E m) (φ.toDensity o) =
      _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) φ := by
  simp only [_root_.tsupport]; congr 1; ext x
  -- `TangentSpace I x` is definitionally `E`, giving fixed model codomain for `Function.support`.
  rw [RoughDensity.mem_support_iff,
    Function.mem_support (f := (show M → E [⋀^Fin m]→L[ℝ] ℝ from φ))]
  have := o.fact_finrank_tangentSpace x
  have h0 : (0 : TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ).toAlternatingMap = 0 := by ext; simp
  refine not_congr ?_
  rw [toDensity, ← Orientation.densityEquiv_apply,
    (Orientation.densityEquiv (o.orientationAt x)).map_eq_zero_iff, ← h0,
    ContinuousAlternatingMap.toAlternatingMap_injective.eq_iff]; rfl

end RoughForm

end TauCeti
