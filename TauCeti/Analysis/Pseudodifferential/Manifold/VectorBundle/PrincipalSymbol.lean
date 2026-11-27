/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Elliptic
import TauCeti.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Dual
import TauCeti.Topology.FiberBundle.Trivialization
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The principal symbol of a pseudodifferential operator between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F` smooth complex vector bundles over `M` with
finite-dimensional model fibres `V` and `W`. A classical pseudodifferential operator `P` of order
`m` from `E` to `F` (`TauCeti.sectionClassicalPseudodifferentialOperators`) has scalar matrix
entries `f ↦ χ · ℓ(t' (P (f · ψ t⁻¹ v)))` (`TauCeti.sectionEntry`), each a classical
pseudodifferential operator of order `m` on `M` with a principal symbol on the cotangent bundle
(`TauCeti.classicalPrincipalSymbol`). This file assembles them into the **principal symbol** of
`P`, a complex-linear map

`σ_m(P)(x, ξ) : E_x → F_x`

for every covector `ξ ∈ T*ₓM` (`TauCeti.sectionClassicalPrincipalSymbol`), so that `σ_m(P)` is a
pointwise `Hom(E_x, F_x)`-valued function on the cotangent bundle that does not depend on the
frames. Its regularity in `(x, ξ)` is not proved here.

It is read off in the preferred trivializations of `E` and `F` at `x`, with the matrix whose
entries are the principal symbols of the matrix entries of `P` in these frames. That it does not
depend on this choice is the **transformation law** of the principal symbol: for all
trivializations `t` of `E` and `t'` of `F` in their atlases, all cutoffs `ψ`, `χ` supported in
their base sets, all `v ∈ V` and all complex-linear `ℓ : W → ℂ`,

`σ_m(χ ℓ t' P ψ t⁻¹ v)(x, ξ) = χ(x) ψ(x) ℓ(t'ₓ (σ_m(P)(x, ξ) (t⁻¹ₓ v)))`

(`TauCeti.classicalPrincipalSymbol_sectionEntry`). The proof changes frames on both sides. On the
output side a frame change multiplies the entries by smooth functions near `x`
(`Bundle.Trivialization.cutoffFrameCoeff_apply_eq_sum`), and the principal symbol of a product
with a function `g` on the left is `g(x)` times that of the operator
(`TauCeti.classicalPrincipalSymbol_mulLeft_comp`). On the input side the section `ψ t⁻¹ v` is a
combination of the preferred frame sections near `x`, plus a section vanishing near `x`
(`Bundle.Trivialization.smul_eq_sum_smul_cutoffFrameSection_add`); the principal symbol of a
product with `g` on the right is that of the operator times `g(x)`
(`TauCeti.classicalPrincipalSymbol_comp_mulLeft`), so the remainder does not contribute.

The principal symbol is linear in the operator, vanishes exactly on the operators of order `m - 1`
(`TauCeti.sectionClassicalPrincipalSymbol_eq_zero_iff`), vanishes at the zero covector and is
positively homogeneous of degree `m` in `ξ`.

For a **differential operator** `P` of order at most `k` between the bundles, in Grothendieck's
sense for commutators with multiplication by complex-valued smooth functions, the principal symbol
is read from iterated commutators, in the angular-frequency convention `σ(∂ⱼ) = i ξⱼ`: at the
nonzero differential `df_x` of a real-valued smooth function `f`,
`σ_k(P)(x, df_x) (s x) = (i ^ k / k!) ([⋯[P, f], …, f] s)(x)` for every smooth section `s`
(`TauCeti.sectionClassicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators`). The `k`-fold
commutator is linear over the functions, so its value at `x` only depends on `s(x)`
(`TauCeti.apply_eq_apply_of_map_smul`), and in frames this is the scalar statement
`TauCeti.classicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators` for the matrix entries.

An operator is **elliptic at** `x` (`TauCeti.IsSectionClassicalEllipticAt`) when `σ_m(P)(x, ξ)` is
bijective for every nonzero covector `ξ`. Ellipticity is unchanged by perturbations of order
`m - 1` and by nonzero scalars, and over a manifold of positive dimension it forces the two bundles
to have the same rank (`TauCeti.IsSectionClassicalEllipticAt.finrank_eq`). In dimension zero there
are no nonzero covectors, every operator is elliptic and the ranks are unconstrained.

A differential operator `P : Γ(E) → Γ(F)` of order at most `k`, in Grothendieck's sense for
commutators with complex-valued smooth functions, is a classical pseudodifferential operator of
order `k`. When the real structures of the fibres are those underlying their complex structures,
`P` also has a geometric principal symbol `σ_geom(P)` (`TauCeti.sectionPrincipalSymbol`), defined
by `σ_geom(P)(df_x) s(x) = (1 / k!) ([⋯[P, f], …, f] s)(x)` for real-valued functions `f`, and

`σ_k(P)(x, ξ) = i ^ k σ_geom(P)(ξ)`

at every nonzero covector `ξ`
(`TauCeti.sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators`). This is the
angular-frequency convention `σ(∂ⱼ) = i ξⱼ`. The matrix entries of `P` are complex differential
operators on functions, whose principal symbols are `i ^ k / k!` times their iterated commutators
with a real function `f` at `df_x`
(`TauCeti.classicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators`), and these commutators
are the entries of the iterated commutators of `P` with `f`. Since `i ^ k` is invertible, `P` is
elliptic as a pseudodifferential operator exactly when it is elliptic as a differential operator
(`TauCeti.isSectionClassicalElliptic_iff_isSectionElliptic`), so the elliptic theory of
pseudodifferential operators between bundles applies to elliptic differential operators.

## Main definitions

* `TauCeti.sectionClassicalPrincipalSymbol m P x ξ`: the principal symbol `E_x →ₗ[ℂ] F_x`.
* `TauCeti.IsSectionClassicalEllipticAt m P x`, `TauCeti.IsSectionClassicalElliptic m P`:
  ellipticity at a point and everywhere.

## Main results

* `TauCeti.classicalPrincipalSymbol_sectionEntry`: the principal symbols of the matrix entries of
  `P` in arbitrary frames are read off from `σ_m(P)`.
* `TauCeti.sectionClassicalPrincipalSymbol_eq_iff`: conversely, `σ_m(P)(x, ξ)` is the linear map
  whose readings in one pair of frames are the principal symbols of these entries.
* `TauCeti.sectionClassicalPrincipalSymbol_add`, `TauCeti.sectionClassicalPrincipalSymbol_smul`,
  `TauCeti.sectionClassicalPrincipalSymbol_zero`, `TauCeti.sectionClassicalPrincipalSymbol_neg`,
  `TauCeti.sectionClassicalPrincipalSymbol_sub`, `TauCeti.sectionClassicalPrincipalSymbol_sum`:
  linearity in the operator.
* `TauCeti.sectionClassicalPrincipalSymbol_eq_zero_iff`: the principal symbol of an operator of
  order `m` vanishes exactly when the operator has order `m - 1`.
* `TauCeti.sectionClassicalPrincipalSymbol_zero_covector`,
  `TauCeti.sectionClassicalPrincipalSymbol_smul_covector`: homogeneity in the covector.
* `TauCeti.sectionClassicalPrincipalSymbol_id`, `TauCeti.isSectionClassicalElliptic_id`: the
  identity of `Γ(E)` has principal symbol the identity of `E_x` and is elliptic of order `0`.
* `TauCeti.sectionClassicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators`: the principal
  symbol of a differential operator at `df_x` is `i ^ k / k!` times its `k`-fold commutator with
  `f`, evaluated at `x`.
* `TauCeti.isSectionClassicalEllipticAt_add_iff`: ellipticity only depends on the principal symbol.
* `TauCeti.isSectionClassicalEllipticAt_smul_iff`: ellipticity is unchanged by nonzero scalars.
* `TauCeti.IsSectionClassicalEllipticAt.finrank_eq`: in positive dimension, ellipticity at a
  point forces `rank E = rank F`.
* `TauCeti.IsSectionClassicalEllipticAt.mem_or_subsingleton`: in positive dimension, ellipticity at
  a point forces order `m` unless both model fibres are trivial.
* `TauCeti.sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators`: the principal
  symbol of a differential operator of order at most `k` is `i ^ k` times its geometric principal
  symbol.
* `TauCeti.isSectionClassicalEllipticAt_iff_isSectionEllipticAt`,
  `TauCeti.isSectionClassicalElliptic_iff_isSectionElliptic`: a differential operator is elliptic
  as a pseudodifferential operator exactly when it is elliptic as a differential operator.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (the principal
  symbol of a pseudodifferential operator between sections of vector bundles, after Definition
  18.1.20).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Bundle Filter Module Set TauCeti
open scoped ContDiff Manifold Topology

namespace TauCeti

/-! ### The preferred frames at a point -/

section Frame

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

variable (n) {V : Type*} [NormedAddCommGroup V] (E : M → Type*) [TopologicalSpace (TotalSpace V E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  {W : Type*} [NormedAddCommGroup W] (F : M → Type*) [TopologicalSpace (TotalSpace W F)]
  [∀ x, TopologicalSpace (F x)] [FiberBundle W F]

private theorem exists_frameCutoff (x : M) :
    ∃ ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯,
      tsupport ρ ⊆ (trivializationAt V E x).baseSet ∩ (trivializationAt W F x).baseSet ∧
        ∀ᶠ y in 𝓝 x, ρ y = 1 :=
  ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (inter_mem ((trivializationAt V E x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt V E x))
      ((trivializationAt W F x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt W F x)))

/-- The cutoff through which the principal symbol at `x` is read off: a real smooth function equal
to `1` near `x`, supported in the base sets of the preferred trivializations of `E` and `F` at
`x`. -/
private def frameCutoff (x : M) : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ :=
  (exists_frameCutoff (V := V) (W := W) n E F x).choose

private theorem tsupport_frameCutoff_subset_left (x : M) :
    tsupport (frameCutoff (V := V) (W := W) n E F x) ⊆ (trivializationAt V E x).baseSet :=
  (exists_frameCutoff n E F x).choose_spec.1.trans inter_subset_left

private theorem tsupport_frameCutoff_subset_right (x : M) :
    tsupport (frameCutoff (V := V) (W := W) n E F x) ⊆ (trivializationAt W F x).baseSet :=
  (exists_frameCutoff n E F x).choose_spec.1.trans inter_subset_right

private theorem frameCutoff_eventually_eq_one (x : M) :
    ∀ᶠ y in 𝓝 x, frameCutoff (V := V) (W := W) n E F x y = 1 :=
  (exists_frameCutoff n E F x).choose_spec.2

private theorem frameCutoff_self (x : M) : frameCutoff (V := V) (W := W) n E F x x = 1 :=
  (frameCutoff_eventually_eq_one n E F x).self_of_nhds

end Frame

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {m : ℝ}
  {P Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-! ### The principal symbol -/

variable (m P) in
/-- The matrix of principal symbols of the entries of `P` in the preferred frames at `x`: its entry
in row `j` and column `i` is the principal symbol at `ξ` of the entry of `P` from the `i`-th frame
vector of `E` to the `j`-th frame coordinate of `F`. -/
private def framePrincipalSymbolMatrix (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    Matrix (Fin (finrank ℂ W)) (Fin (finrank ℂ V)) ℂ :=
  Matrix.of fun j i ↦ classicalPrincipalSymbol m
    (sectionEntry (trivializationAt V E x) (frameCutoff (V := V) (W := W) n E F x)
      (tsupport_frameCutoff_subset_left (V := V) (W := W) n E F x) (finBasis ℂ V i)
      (trivializationAt W F x) (frameCutoff (V := V) (W := W) n E F x)
      (tsupport_frameCutoff_subset_right (V := V) (W := W) n E F x)
      ((finBasis ℂ W).coord j).toContinuousLinearMap P) x ξ

variable (m P) in
/-- **The principal symbol** of order `m` of a classical pseudodifferential operator
`P : Γ(E) → Γ(F)` of order `m`, at a covector `ξ ∈ T*ₓM`: a complex-linear map `E_x → F_x`. It
is read off in the preferred trivializations of `E` and `F` at `x` from the principal symbols of
the matrix entries of `P` (`TauCeti.sectionEntry`); by
`TauCeti.classicalPrincipalSymbol_sectionEntry` the same map is read off in every pair of frames.
It is `0` when `P` is not a classical pseudodifferential operator of order `m`. -/
def sectionClassicalPrincipalSymbol (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) : E x →ₗ[ℂ] F x :=
  open Classical in
  if P ∈ sectionClassicalPseudodifferentialOperators m then
    (trivializationAt W F x).symmₗ ℂ x ∘ₗ
      Matrix.toLin (finBasis ℂ V) (finBasis ℂ W) (framePrincipalSymbolMatrix m P x ξ) ∘ₗ
      (trivializationAt V E x).linearMapAt ℂ x
  else 0

/-- The principal symbol of an operator that is not a classical pseudodifferential operator of
order `m` is `0`, by convention. -/
theorem sectionClassicalPrincipalSymbol_of_notMem
    (hP : P ∉ sectionClassicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m P x ξ = 0 := by
  simp [sectionClassicalPrincipalSymbol, hP]

/-- The coordinates in the preferred frame of `F` at `x` of `σ_m(P)(x, ξ) u` are the matrix of
principal symbols applied to the coordinates of `u` in the preferred frame of `E`. -/
private theorem repr_sectionClassicalPrincipalSymbol
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) (u : E x) :
    ⇑((finBasis ℂ W).repr ((trivializationAt W F x).continuousLinearMapAt ℂ x
        (sectionClassicalPrincipalSymbol m P x ξ u))) =
      (framePrincipalSymbolMatrix m P x ξ).mulVec
        ⇑((finBasis ℂ V).repr ((trivializationAt V E x).continuousLinearMapAt ℂ x u)) := by
  simp [sectionClassicalPrincipalSymbol, hP,
    Trivialization.linearMapAt_symmₗ _ (FiberBundle.mem_baseSet_trivializationAt W F x),
    Matrix.repr_toLin]

/-! ### Changes of frames -/

omit [FiniteDimensional ℂ V] in
/-- **Changing the output frame.** The principal symbol of an entry of `P` with output frame
`(t', χ, ℓ)` is a combination of the principal symbols of the entries with the same input and the
preferred output frame at `x`, with the coefficients `χ(x) ℓ(t'ₓ t₀'⁻¹ bⱼ)`. -/
private theorem classicalPrincipalSymbol_sectionEntry_eq_sum_output
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (sectionEntry t ψ hψ v t' χ hχ ℓ P) x ξ =
      ∑ j, (χ x : ℂ) * ℓ (t'.continuousLinearMapAt ℂ x
          ((trivializationAt W F x).symmL ℂ x (finBasis ℂ W j))) *
        classicalPrincipalSymbol m (sectionEntry t ψ hψ v (trivializationAt W F x)
          (frameCutoff (V := V) (W := W) n E F x)
          (tsupport_frameCutoff_subset_right (V := V) (W := W) n E F x)
          ((finBasis ℂ W).coord j).toContinuousLinearMap P) x ξ := by
  have hρ := tsupport_frameCutoff_subset_right (V := V) (W := W) n E F x
  have hx := FiberBundle.mem_baseSet_trivializationAt W F x
  have hE (j : Fin (finrank ℂ W)) := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2
    t ψ hψ v _ _ hρ ((finBasis ℂ W).coord j).toContinuousLinearMap
  -- The coefficients `g j = χ ℓ(t' ρ t₀⁻¹ bⱼ)` are smooth, and equal `χ ℓ(t' t₀⁻¹ bⱼ)` near `x`.
  set g : Fin (finrank ℂ W) → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ := fun j ↦
    t'.cutoffFrameCoeff χ hχ ℓ ((trivializationAt W F x).cutoffFrameSection _ hρ (finBasis ℂ W j))
  have hloc : ∀ᶠ y in 𝓝 x, ∀ f, sectionEntry t ψ hψ v t' χ hχ ℓ P f y =
      (∑ j, LinearMap.mulLeft ℂ (g j) ∘ₗ sectionEntry t ψ hψ v _ _ hρ
        ((finBasis ℂ W).coord j).toContinuousLinearMap P) f y := by
    filter_upwards [frameCutoff_eventually_eq_one (V := V) (W := W) n E F x,
      (trivializationAt W F x).open_baseSet.mem_nhds hx] with y hρy hy f
    simp only [sectionEntry_apply_eq_cutoffFrameCoeff, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, ContMDiffMap.coe_sum, Finset.sum_apply, ContMDiffMap.coe_mul,
      Pi.mul_apply, g]
    exact t'.cutoffFrameCoeff_apply_eq_sum χ hχ ℓ _ _ hρ (finBasis ℂ W) hy hρy _
  have hgE (j : Fin (finrank ℂ W)) :=
    mulLeft_comp_mem_classicalPseudodifferentialOperators (hE j) (g j)
  rw [classicalPrincipalSymbol_eq_of_eventually_apply_eq
    ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ψ hψ v t' χ hχ ℓ)
    (Submodule.sum_mem _ fun j _ ↦ hgE j) hloc ξ, classicalPrincipalSymbol_sum _ fun j _ ↦ hgE j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [classicalPrincipalSymbol_mulLeft_comp (hE j)]
  simp [g, frameCutoff_self (V := V) (W := W) n E F x, Complex.real_smul,
    (trivializationAt W F x).symmL_apply (R := ℂ) hx]

omit [FiniteDimensional ℂ W] in
/-- **Changing the input frame.** The principal symbol of an entry of `P` with input frame
`(t, ψ, v)` is a combination of the principal symbols of the entries with the preferred input frame
at `x` and the same output, with the coefficients `ψ(x) bᵢ*(t₀ₓ t⁻¹ₓ v)`. -/
private theorem classicalPrincipalSymbol_sectionEntry_eq_sum_input
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (sectionEntry t ψ hψ v t' χ hχ ℓ P) x ξ =
      ∑ i, (ψ x : ℂ) * (finBasis ℂ V).coord i
          ((trivializationAt V E x).continuousLinearMapAt ℂ x (t.symm x v)) *
        classicalPrincipalSymbol m (sectionEntry (trivializationAt V E x)
          (frameCutoff (V := V) (W := W) n E F x)
          (tsupport_frameCutoff_subset_left (V := V) (W := W) n E F x) (finBasis ℂ V i)
          t' χ hχ ℓ P) x ξ := by
  have hρ := tsupport_frameCutoff_subset_left (V := V) (W := W) n E F x
  have hx := FiberBundle.mem_baseSet_trivializationAt V E x
  have hmem := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2
  -- The coefficients `k i = ρ bᵢ*(t₀ ψ t⁻¹ v)` of the input section in the preferred frame `t₀`,
  -- and a cutoff `θ` equal to `1` near `x`, supported where `ρ = 1` inside the base set of `t₀`.
  set k : Fin (finrank ℂ V) → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ := fun i ↦
    (trivializationAt V E x).cutoffFrameCoeff _ hρ ((finBasis ℂ V).coord i).toContinuousLinearMap
      (t.cutoffFrameSection ψ hψ v)
  obtain ⟨θ, hθU, hθ⟩ :=
    ContMDiffMap.exists_tsupport_subset_eventually_eq_one (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
      (inter_mem (frameCutoff_eventually_eq_one (V := V) (W := W) n E F x)
        ((trivializationAt V E x).open_baseSet.mem_nhds hx))
  set θc := ContMDiffMap.ofReal θ
  -- Near `x` the input section is `∑ᵢ kᵢ ρ t₀⁻¹ bᵢ`; the rest is cut off by `1 - θ`.
  have hs := (trivializationAt V E x).smul_eq_sum_smul_cutoffFrameSection_add _ hρ
    (finBasis ℂ V) θ hθU (t.cutoffFrameSection ψ hψ v)
  have hop : sectionEntry t ψ hψ v t' χ hχ ℓ P =
      ∑ i, sectionEntry _ _ hρ (finBasis ℂ V i) t' χ hχ ℓ P ∘ₗ LinearMap.mulLeft ℂ (θc * k i) +
        sectionEntry t ψ hψ v t' χ hχ ℓ P ∘ₗ LinearMap.mulLeft ℂ (1 - θc) := by
    refine LinearMap.ext fun f ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, sectionEntry_apply_eq_cutoffFrameCoeff]
    rw [hs f, map_add, map_sum, map_add, map_sum]
  have hE (i : Fin (finrank ℂ V)) := hmem _ _ hρ (finBasis ℂ V i) t' χ hχ ℓ
  have hE₀ := hmem t ψ hψ v t' χ hχ ℓ
  conv_lhs => rw [hop]
  rw [classicalPrincipalSymbol_add
      (Submodule.sum_mem _ fun i _ ↦
        comp_mulLeft_mem_classicalPseudodifferentialOperators (hE i) _)
      (comp_mulLeft_mem_classicalPseudodifferentialOperators hE₀ _),
    classicalPrincipalSymbol_sum _
      fun i _ ↦ comp_mulLeft_mem_classicalPseudodifferentialOperators (hE i) _,
    classicalPrincipalSymbol_comp_mulLeft hE₀]
  have hθx : θ x = 1 := hθ.self_of_nhds
  simp only [ContMDiffMap.coe_sub, ContMDiffMap.coe_one, Pi.sub_apply, Pi.one_apply, θc,
    ContMDiffMap.ofReal_apply, hθx, Complex.ofReal_one, sub_self, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [classicalPrincipalSymbol_comp_mulLeft (hE i)]
  simp [k, ContMDiffMap.ofReal_apply, hθx, frameCutoff_self (V := V) (W := W) n E F x,
    ← Bundle.Trivialization.coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt ℝ ℂ, map_smul]
  ring

/-! ### The transformation law -/

/-- **The transformation law of the principal symbol.** For all trivializations `t` of `E` and `t'`
of `F` in their atlases, real smooth functions `ψ`, `χ` supported in their base sets, `v ∈ V` and
complex-linear `ℓ : W → ℂ`, the principal symbol of the matrix entry
`f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` of `P` at `ξ ∈ T*ₓM` is
`χ(x) ψ(x) ℓ(t'ₓ (σ_m(P)(x, ξ) (t⁻¹ₓ v)))`. So `σ_m(P)(x, ξ)` does not depend on the frames it is
read off in. -/
theorem classicalPrincipalSymbol_sectionEntry
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (sectionEntry t ψ hψ v t' χ hχ ℓ P) x ξ =
      ((χ x * ψ x : ℝ) : ℂ) * ℓ (t'.continuousLinearMapAt ℂ x
        (sectionClassicalPrincipalSymbol m P x ξ (t.symm x v))) := by
  rw [classicalPrincipalSymbol_sectionEntry_eq_sum_output hP]
  refine (Finset.sum_congr rfl fun j _ ↦ by
    rw [classicalPrincipalSymbol_sectionEntry_eq_sum_input hP t ψ hψ v]).trans ?_
  have hx := FiberBundle.mem_baseSet_trivializationAt W F x
  conv_rhs => rw [← (trivializationAt W F x).sum_repr_smul_symmL (finBasis ℂ W) hx
    (sectionClassicalPrincipalSymbol m P x ξ (t.symm x v))]
  simp only [map_sum, map_smul, Basis.coord_apply, repr_sectionClassicalPrincipalSymbol hP,
    Matrix.mulVec, dotProduct, framePrincipalSymbolMatrix, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  ring

/-- **Characterization of the principal symbol.** Fix trivializations `t` of `E` and `t'` of `F`
in their atlases and cutoffs `ψ`, `χ` supported in their base sets and nonzero at `x`. Then
`σ_m(P)(x, ξ)` is the linear map `A : E_x → F_x` exactly when the principal symbol of every matrix
entry `f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` of `P` at `ξ` is `χ(x) ψ(x) ℓ(t'ₓ (A (t⁻¹ₓ v)))`. -/
theorem sectionClassicalPrincipalSymbol_eq_iff
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) {x : M}
    (hψx : ψ x ≠ 0) (hχx : χ x ≠ 0) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ)
    (A : E x →ₗ[ℂ] F x) :
    sectionClassicalPrincipalSymbol m P x ξ = A ↔ ∀ (v : V) (ℓ : W →L[ℂ] ℂ),
      classicalPrincipalSymbol m (sectionEntry t ψ hψ v t' χ hχ ℓ P) x ξ =
        ((χ x * ψ x : ℝ) : ℂ) * ℓ (t'.continuousLinearMapAt ℂ x (A (t.symm x v))) := by
  refine ⟨fun h v ℓ ↦ h ▸ classicalPrincipalSymbol_sectionEntry hP t ψ hψ v t' χ hχ ℓ x ξ,
    fun h ↦ t.linearMap_ext ℂ t' (hψ (subset_tsupport _ hψx)) (hχ (subset_tsupport _ hχx))
      fun v ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_⟩
  have hc : ((χ x * ψ x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (mul_ne_zero hχx hψx)
  exact mul_left_cancel₀ hc
    ((classicalPrincipalSymbol_sectionEntry hP t ψ hψ v t' χ hχ ℓ x ξ).symm.trans (h v ℓ))

omit [T2Space M] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [∀ x, Module ℝ (E x)]
  [VectorBundle ℝ V E] [∀ x, Module ℝ (F x)] [VectorBundle ℝ W F] in
variable (V W) in
/-- Two linear maps `E_x → F_x` are equal when every functional `ℓ` takes the same value on their
readings `t₀'ₓ (A (t₀⁻¹ₓ v))` in the preferred trivializations at `x`. -/
private theorem linearMap_ext_trivializationAt {x : M} {A B : E x →ₗ[ℂ] F x}
    (h : ∀ (v : V) (ℓ : W →L[ℂ] ℂ),
      ℓ ((trivializationAt W F x).continuousLinearMapAt ℂ x
          (A ((trivializationAt V E x).symm x v))) =
        ℓ ((trivializationAt W F x).continuousLinearMapAt ℂ x
          (B ((trivializationAt V E x).symm x v)))) :
    A = B :=
  (trivializationAt V E x).linearMap_ext ℂ (trivializationAt W F x)
    (FiberBundle.mem_baseSet_trivializationAt' x) (FiberBundle.mem_baseSet_trivializationAt' x)
      fun v ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 (h v)

/-- In the preferred frames at `x`, the coordinates of the principal symbol are the principal
symbols of the entries of `P`. -/
private theorem coord_sectionClassicalPrincipalSymbol
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) (v : V) (ℓ : W →L[ℂ] ℂ) :
    ℓ ((trivializationAt W F x).continuousLinearMapAt ℂ x
        (sectionClassicalPrincipalSymbol m P x ξ ((trivializationAt V E x).symm x v))) =
      classicalPrincipalSymbol m (sectionEntry (trivializationAt V E x)
        (frameCutoff (V := V) (W := W) n E F x)
        (tsupport_frameCutoff_subset_left (V := V) (W := W) n E F x) v (trivializationAt W F x)
        (frameCutoff (V := V) (W := W) n E F x)
        (tsupport_frameCutoff_subset_right (V := V) (W := W) n E F x) ℓ P) x ξ := by
  rw [classicalPrincipalSymbol_sectionEntry hP, frameCutoff_self (V := V) (W := W) n E F x]
  simp

/-! ### Linearity and order -/

/-- The principal symbol is additive in the operator. -/
theorem sectionClassicalPrincipalSymbol_add
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (P + Q) x ξ =
      sectionClassicalPrincipalSymbol m P x ξ + sectionClassicalPrincipalSymbol m Q x ξ := by
  have hmem := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2
  have hmem' := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hQ).2
  refine linearMap_ext_trivializationAt V W fun v ℓ ↦ ?_
  rw [coord_sectionClassicalPrincipalSymbol (add_mem hP hQ), map_add,
    classicalPrincipalSymbol_add (hmem _ _ _ _ _ _ _ _) (hmem' _ _ _ _ _ _ _ _),
    ← coord_sectionClassicalPrincipalSymbol hP, ← coord_sectionClassicalPrincipalSymbol hQ,
    LinearMap.add_apply, map_add, map_add]

/-- The principal symbol is homogeneous in the operator: `σ_m(c P) = c σ_m(P)`. -/
theorem sectionClassicalPrincipalSymbol_smul
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (c : ℂ) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (c • P) x ξ =
      c • sectionClassicalPrincipalSymbol m P x ξ := by
  have hmem := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2
  refine linearMap_ext_trivializationAt V W fun v ℓ ↦ ?_
  rw [coord_sectionClassicalPrincipalSymbol (Submodule.smul_mem _ c hP), map_smul,
    classicalPrincipalSymbol_smul (hmem _ _ _ _ _ _ _ _),
    ← coord_sectionClassicalPrincipalSymbol hP,
    LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul]

/-- The principal symbol of the zero operator is `0`. -/
@[simp]
theorem sectionClassicalPrincipalSymbol_zero (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (0 : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) x ξ = 0 := by
  simpa using sectionClassicalPrincipalSymbol_smul (m := m)
    (zero_mem (sectionClassicalPseudodifferentialOperators (V := V) (E := E) (W := W) (F := F) m))
    0 x ξ

/-- The principal symbol of `-P` is the negative of that of `P`. -/
theorem sectionClassicalPrincipalSymbol_neg (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (-P) x ξ = -sectionClassicalPrincipalSymbol m P x ξ := by
  by_cases hP : P ∈ sectionClassicalPseudodifferentialOperators m
  · rw [← neg_one_smul ℂ P, sectionClassicalPrincipalSymbol_smul hP, neg_one_smul]
  · rw [sectionClassicalPrincipalSymbol_of_notMem hP,
      sectionClassicalPrincipalSymbol_of_notMem (by rwa [neg_mem_iff]), neg_zero]

/-- The principal symbol of `P - Q` is the difference of those of `P` and `Q`. -/
theorem sectionClassicalPrincipalSymbol_sub
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (P - Q) x ξ =
      sectionClassicalPrincipalSymbol m P x ξ - sectionClassicalPrincipalSymbol m Q x ξ := by
  rw [sub_eq_add_neg, sectionClassicalPrincipalSymbol_add hP (neg_mem hQ),
    sectionClassicalPrincipalSymbol_neg, ← sub_eq_add_neg]

/-- The principal symbol of a finite sum of operators of order `m` between bundles is the sum of
their principal symbols. -/
theorem sectionClassicalPrincipalSymbol_sum {ι : Type*} (s : Finset ι)
    {P : ι → Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hP : ∀ i ∈ s, P i ∈ sectionClassicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (∑ i ∈ s, P i) x ξ =
      ∑ i ∈ s, sectionClassicalPrincipalSymbol m (P i) x ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      sectionClassicalPrincipalSymbol_add (hP i (Finset.mem_insert_self i s))
        (Submodule.sum_mem _ fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)]

/-- **Operators of lower order.** A classical pseudodifferential operator between bundles of order
`m - 1` has principal symbol `0` in order `m`. -/
theorem sectionClassicalPrincipalSymbol_eq_zero_of_mem_sub_one
    (hP : P ∈ sectionClassicalPseudodifferentialOperators (m - 1)) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m P x ξ = 0 := by
  have hPm := sectionClassicalPseudodifferentialOperators_le (m := m) 1 (by norm_num) hP
  refine linearMap_ext_trivializationAt V W fun v ℓ ↦ ?_
  rw [coord_sectionClassicalPrincipalSymbol hPm, classicalPrincipalSymbol_eq_zero_of_mem_sub_one
    ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 _ _ _ _ _ _ _ _)]
  simp

/-- **The kernel of the principal symbol.** The principal symbol of a classical
pseudodifferential operator of order `m` between bundles vanishes exactly when the operator has
order `m - 1`. -/
theorem sectionClassicalPrincipalSymbol_eq_zero_iff
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    (∀ x ξ, sectionClassicalPrincipalSymbol m P x ξ = 0) ↔
      P ∈ sectionClassicalPseudodifferentialOperators (m - 1) := by
  have hmem := mem_sectionClassicalPseudodifferentialOperators_iff.1 hP
  refine ⟨fun h ↦ mem_sectionClassicalPseudodifferentialOperators_iff.2 ⟨hmem.1,
    fun t _ ψ hψ v t' _ χ hχ ℓ ↦ (classicalPrincipalSymbol_eq_zero_iff
      (hmem.2 t ψ hψ v t' χ hχ ℓ)).1 fun x ξ ↦ ?_⟩,
    fun h x ξ ↦ sectionClassicalPrincipalSymbol_eq_zero_of_mem_sub_one h x ξ⟩
  rw [classicalPrincipalSymbol_sectionEntry hP, h]
  simp

/-- Two classical pseudodifferential operators of order `m` between bundles with the same
principal symbol differ by an operator of order `m - 1`. -/
theorem sub_mem_sectionClassicalPseudodifferentialOperators_of_sectionClassicalPrincipalSymbol_eq
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m)
    (h : ∀ x ξ,
      sectionClassicalPrincipalSymbol m P x ξ = sectionClassicalPrincipalSymbol m Q x ξ) :
    P - Q ∈ sectionClassicalPseudodifferentialOperators (m - 1) := by
  refine (sectionClassicalPrincipalSymbol_eq_zero_iff (sub_mem hP hQ)).1 fun x ξ ↦ ?_
  rw [sectionClassicalPrincipalSymbol_sub hP hQ, h x ξ, sub_self]

/-- Adding an operator of order `m - 1` does not change the principal symbol of order `m`. -/
theorem sectionClassicalPrincipalSymbol_add_of_mem_sub_one
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators (m - 1)) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (P + Q) x ξ = sectionClassicalPrincipalSymbol m P x ξ := by
  have hQm := sectionClassicalPseudodifferentialOperators_le (m := m) 1 (by norm_num) hQ
  by_cases hP : P ∈ sectionClassicalPseudodifferentialOperators m
  · rw [sectionClassicalPrincipalSymbol_add hP hQm,
      sectionClassicalPrincipalSymbol_eq_zero_of_mem_sub_one hQ, add_zero]
  · have hPQ : P + Q ∉ sectionClassicalPseudodifferentialOperators m := fun h ↦
      hP (by simpa using sub_mem h hQm)
    rw [sectionClassicalPrincipalSymbol_of_notMem hP, sectionClassicalPrincipalSymbol_of_notMem hPQ]

omit [FiniteDimensional ℂ W] in
/-- **The principal symbol of the identity.** The identity of `Γ(E)` has principal symbol of order
`0` the identity of `E_x` at every nonzero covector `ξ ∈ T*ₓM`. -/
@[simp]
theorem sectionClassicalPrincipalSymbol_id (x : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    sectionClassicalPrincipalSymbol 0 (LinearMap.id : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) x ξ = LinearMap.id := by
  refine linearMap_ext_trivializationAt V V fun v ℓ ↦ ?_
  rw [coord_sectionClassicalPrincipalSymbol id_mem_sectionClassicalPseudodifferentialOperators]
  -- Each entry of the identity is the multiplication by its value on the constant function `1`.
  set T := sectionEntry (trivializationAt V E x) (frameCutoff (V := V) (W := V) n E E x)
    (tsupport_frameCutoff_subset_left (V := V) (W := V) n E E x) v (trivializationAt V E x)
    (frameCutoff (V := V) (W := V) n E E x)
    (tsupport_frameCutoff_subset_right (V := V) (W := V) n E E x) ℓ
  have hT : T LinearMap.id = LinearMap.mulLeft ℂ (T LinearMap.id 1) ∘ₗ LinearMap.id := by
    ext f y
    simp only [T, sectionEntry_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply, one_smul,
      ContMDiffSection.smul_apply_of_normedAlgebra, map_smul, smul_eq_mul, Complex.real_smul]
    ring
  rw [hT, classicalPrincipalSymbol_mulLeft_comp id_mem_classicalPseudodifferentialOperators,
    classicalPrincipalSymbol_id x hξ, mul_one]
  simp [T, frameCutoff_self (V := V) (W := V) n E E x]

/-! ### Homogeneity -/

/-- The principal symbol vanishes at the zero covector. -/
@[simp]
theorem sectionClassicalPrincipalSymbol_zero_covector (x : M) :
    sectionClassicalPrincipalSymbol m P x 0 = 0 := by
  by_cases hP : P ∈ sectionClassicalPseudodifferentialOperators m
  · refine linearMap_ext_trivializationAt V W fun v ℓ ↦ ?_
    rw [coord_sectionClassicalPrincipalSymbol hP, classicalPrincipalSymbol_zero_covector]
    simp
  · exact sectionClassicalPrincipalSymbol_of_notMem hP x 0

/-- **Homogeneity.** The principal symbol of order `m` is positively homogeneous of degree `m` in
the covector: `σ_m(P)(x, t ξ) = t ^ m σ_m(P)(x, ξ)` for `t > 0`. -/
theorem sectionClassicalPrincipalSymbol_smul_covector (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) {t : ℝ} (ht : 0 < t) :
    sectionClassicalPrincipalSymbol m P x (t • ξ) =
      ((t ^ m : ℝ) : ℂ) • sectionClassicalPrincipalSymbol m P x ξ := by
  by_cases hP : P ∈ sectionClassicalPseudodifferentialOperators m
  · refine linearMap_ext_trivializationAt V W fun v ℓ ↦ ?_
    rw [coord_sectionClassicalPrincipalSymbol hP, classicalPrincipalSymbol_smul_covector x ξ ht,
      ← coord_sectionClassicalPrincipalSymbol hP, LinearMap.smul_apply, map_smul, map_smul,
      smul_eq_mul]
  · simp [sectionClassicalPrincipalSymbol_of_notMem hP]

/-! ### Differential operators -/

/-- **The principal symbol of a differential operator between bundles.** Let `P : Γ(E) → Γ(F)` be a
differential operator of order at most `k` in Grothendieck's sense, for commutators with
multiplication by complex-valued smooth functions, so that `P` is a classical pseudodifferential
operator of order `k`
(`TauCeti.mem_sectionClassicalPseudodifferentialOperators_of_mem_differentialOperators`). At the
differential `df_x` of a real-valued smooth function `f`, if it is nonzero, its principal
symbol of order `k` is read from the `k`-fold commutator of `P` with multiplication by `f`:

`σ_k(P)(x, df_x) (s x) = (i ^ k / k!) ([⋯[P, f], …, f] s)(x)`

for every smooth section `s` of `E`. This is the angular-frequency convention `σ(∂ⱼ) = i ξⱼ`;
the scalar case is `TauCeti.classicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators`. -/
theorem sectionClassicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators {k : ℕ}
    (hP : P ∈ differentialOperators ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ k)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) {x : M}
    (hf : mvfderiv 𝓘(ℝ, CoordinateSpace n) f x ≠ 0) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    sectionClassicalPrincipalSymbol k P x (mvfderiv 𝓘(ℝ, CoordinateSpace n) f x) (s x) =
      (Complex.I ^ k / k.factorial) • (smulCommutator ℂ (ContMDiffMap.ofReal f) ^ k) P s x := by
  set R := (smulCommutator ℂ (ContMDiffMap.ofReal f) ^ k) P with hRdef
  -- The `k`-fold commutator `R` has order `0`: it is linear over the functions.
  have hR : ∀ (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) σ, R (g • σ) = g • R σ :=
    mem_differentialOperators_zero_iff.1
      (smulCommutator_pow_mem_differentialOperators (m := 0) (by simpa using hP) _)
  -- Read both sides in the preferred frames at `x`, with the frame cutoff `ρ`, equal to `1` at `x`.
  set t := trivializationAt V E x
  set t' := trivializationAt W F x
  have hxt : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt V E x
  have hxt' : x ∈ t'.baseSet := FiberBundle.mem_baseSet_trivializationAt W F x
  set ρ := frameCutoff (V := V) (W := W) n E F x
  have hρ := tsupport_frameCutoff_subset_left (V := V) (W := W) n E F x
  have hρ' := tsupport_frameCutoff_subset_right (V := V) (W := W) n E F x
  have hρx : ρ x = 1 := frameCutoff_self (V := V) (W := W) n E F x
  set v := t.continuousLinearMapAt ℂ x (s x)
  have hv : t.symm x v = s x := by
    rw [← t.symmL_apply (R := ℂ) hxt, t.symmL_continuousLinearMapAt (R := ℂ) hxt]
  refine (t'.continuousLinearEquivAt ℂ x hxt').injective
    ((SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_)
  simp only [t'.coe_continuousLinearEquivAt_eq (R := ℂ) hxt']
  -- The entry of `P` is a scalar differential operator, whose `k`-fold commutator with `f` is the
  -- entry of `R`, and the value of `R` at `x` on the cut-off frame section `ρ t⁻¹ v` is its value
  -- on `s`.
  have hentry := sectionEntry_mem_differentialOperators t ρ hρ v t' ρ hρ' ℓ hP
  have hRs : R (t.cutoffFrameSection ρ hρ v) x = R s x :=
    apply_eq_apply_of_map_smul hR (by rw [t.cutoffFrameSection_apply, hρx, one_smul, hv])
  rw [← hv, coord_sectionClassicalPrincipalSymbol
      (mem_sectionClassicalPseudodifferentialOperators_of_mem_differentialOperators hP),
    classicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators hentry f hf,
    ← sectionEntry_smulCommutator_pow]
  simp [sectionEntry_apply, ← hRdef, hRs, hρx]

/-! ### Ellipticity -/

variable (m P) in
/-- A classical pseudodifferential operator `P : Γ(E) → Γ(F)` of order `m` is **elliptic at** `x`
if its principal symbol `σ_m(P)(x, ξ) : E_x → F_x` (`TauCeti.sectionClassicalPrincipalSymbol`)
is bijective at every nonzero covector `ξ ∈ T*ₓM`. -/
def IsSectionClassicalEllipticAt (x : M) : Prop :=
  ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
    Function.Bijective (sectionClassicalPrincipalSymbol m P x ξ)

variable (m P) in
/-- A classical pseudodifferential operator between bundles is **elliptic** if it is elliptic at
every point (`TauCeti.IsSectionClassicalEllipticAt`). -/
def IsSectionClassicalElliptic : Prop :=
  ∀ x : M, IsSectionClassicalEllipticAt m P x

theorem isSectionClassicalEllipticAt_iff {x : M} :
    IsSectionClassicalEllipticAt m P x ↔ ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ,
      ξ ≠ 0 → Function.Bijective (sectionClassicalPrincipalSymbol m P x ξ) :=
  Iff.rfl

theorem isSectionClassicalElliptic_iff :
    IsSectionClassicalElliptic m P ↔ ∀ x : M, IsSectionClassicalEllipticAt m P x :=
  Iff.rfl

/-- **Ellipticity only sees the principal symbol.** Adding an operator of order `m - 1` does not
change ellipticity at a point. -/
theorem isSectionClassicalEllipticAt_add_iff
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators (m - 1)) {x : M} :
    IsSectionClassicalEllipticAt m (P + Q) x ↔ IsSectionClassicalEllipticAt m P x := by
  simp only [isSectionClassicalEllipticAt_iff,
    sectionClassicalPrincipalSymbol_add_of_mem_sub_one hQ]

/-- **Ellipticity only sees the principal symbol.** Adding an operator of order `m - 1` does not
change ellipticity. -/
theorem isSectionClassicalElliptic_add_iff
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators (m - 1)) :
    IsSectionClassicalElliptic m (P + Q) ↔ IsSectionClassicalElliptic m P :=
  forall_congr' fun _ ↦ isSectionClassicalEllipticAt_add_iff hQ

/-- Multiplying by a nonzero complex number does not change ellipticity at a point. -/
@[simp]
theorem isSectionClassicalEllipticAt_smul_iff {c : ℂ} (hc : c ≠ 0) {x : M} :
    IsSectionClassicalEllipticAt m (c • P) x ↔ IsSectionClassicalEllipticAt m P x := by
  by_cases hP : P ∈ sectionClassicalPseudodifferentialOperators m
  · refine forall₂_congr fun ξ _ ↦ ?_
    rw [sectionClassicalPrincipalSymbol_smul hP, LinearMap.coe_smul]
    exact (MulAction.bijective (Units.mk0 c hc)).of_comp_iff' _
  · -- Neither `P` nor `c • P` is of order `m`, so both principal symbols vanish.
    have hcP : c • P ∉ sectionClassicalPseudodifferentialOperators m := fun h ↦ hP <| by
      simpa [smul_smul, inv_mul_cancel₀ hc] using Submodule.smul_mem _ c⁻¹ h
    simp [isSectionClassicalEllipticAt_iff, sectionClassicalPrincipalSymbol_of_notMem hP,
      sectionClassicalPrincipalSymbol_of_notMem hcP]

/-- Multiplying by a nonzero complex number does not change ellipticity. -/
@[simp]
theorem isSectionClassicalElliptic_smul_iff {c : ℂ} (hc : c ≠ 0) :
    IsSectionClassicalElliptic m (c • P) ↔ IsSectionClassicalElliptic m P :=
  forall_congr' fun _ ↦ isSectionClassicalEllipticAt_smul_iff hc

/-- **Ellipticity forces equal ranks.** Over a manifold of positive dimension, if `P : Γ(E) → Γ(F)`
is elliptic at some point, then `E` and `F` have the same rank: the principal symbol at a nonzero
covector is a linear isomorphism between the fibres. -/
theorem IsSectionClassicalEllipticAt.finrank_eq [Nontrivial (CoordinateSpace n)] {x : M}
    (hPx : IsSectionClassicalEllipticAt m P x) : finrank ℂ V = finrank ℂ W := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ)
  rw [← ((trivializationAt V E x).continuousLinearEquivAt ℂ x
      (FiberBundle.mem_baseSet_trivializationAt V E x)).toLinearEquiv.finrank_eq,
    ← ((trivializationAt W F x).continuousLinearEquivAt ℂ x
      (FiberBundle.mem_baseSet_trivializationAt W F x)).toLinearEquiv.finrank_eq]
  exact (LinearEquiv.ofBijective _ (hPx _ hξ)).finrank_eq

/-- **Ellipticity forces the order.** Over a manifold of positive dimension, an operator between
bundles elliptic at some point is a classical pseudodifferential operator of order `m` unless both
model fibres are trivial: otherwise its principal symbol vanishes, and the zero map between the
fibres is not bijective. -/
theorem IsSectionClassicalEllipticAt.mem_or_subsingleton [Nontrivial (CoordinateSpace n)] {x : M}
    (hPx : IsSectionClassicalEllipticAt m P x) :
    P ∈ sectionClassicalPseudodifferentialOperators m ∨ (Subsingleton V ∧ Subsingleton W) := by
  refine or_iff_not_imp_left.2 fun hP ↦ ?_
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ)
  have h0 := isSectionClassicalEllipticAt_iff.1 hPx _ hξ
  rw [sectionClassicalPrincipalSymbol_of_notMem hP] at h0
  -- The zero map `E_x → F_x` is bijective, so both fibres are trivial.
  have hE : Subsingleton (E x) := ⟨fun u v ↦ h0.1 (by simp)⟩
  have hF : Subsingleton (F x) := ⟨fun u v ↦ by
    obtain ⟨u', rfl⟩ := h0.2 u
    obtain ⟨v', rfl⟩ := h0.2 v
    simp⟩
  exact ⟨((trivializationAt V E x).continuousLinearEquivAt ℂ x
      (FiberBundle.mem_baseSet_trivializationAt V E x)).symm.toEquiv.subsingleton,
    ((trivializationAt W F x).continuousLinearEquivAt ℂ x
      (FiberBundle.mem_baseSet_trivializationAt W F x)).symm.toEquiv.subsingleton⟩

/-- In dimension zero every covector vanishes, so every operator between bundles is elliptic at
every point, whatever the ranks of the bundles. -/
theorem isSectionClassicalEllipticAt_of_subsingleton [Subsingleton (CoordinateSpace n)] (x : M) :
    IsSectionClassicalEllipticAt m P x := fun ξ hξ ↦ by
  -- The tangent space at `x` is `ℝ⁰`.
  have : Subsingleton (TangentSpace 𝓘(ℝ, CoordinateSpace n) x) :=
    inferInstanceAs (Subsingleton (CoordinateSpace n))
  exact absurd (ContinuousLinearMap.ext fun v ↦ by simp [Subsingleton.elim v 0]) hξ

/-- Between bundles whose model fibres are both trivial, every operator is elliptic at every point:
every linear map between the trivial fibres is bijective. -/
theorem isSectionClassicalEllipticAt_of_subsingleton_fiber [Subsingleton V] [Subsingleton W]
    (x : M) : IsSectionClassicalEllipticAt m P x := fun _ _ ↦ by
  have := subsingleton_fiber_of_subsingleton V E x
  have := subsingleton_fiber_of_subsingleton W F x
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

omit [FiniteDimensional ℂ W] in
/-- **The identity is elliptic** of order `0`: its principal symbol at a nonzero covector is the
identity of the fibre. -/
theorem isSectionClassicalElliptic_id :
    IsSectionClassicalElliptic 0 (LinearMap.id : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) := fun x ξ hξ ↦ by
  rw [sectionClassicalPrincipalSymbol_id x hξ]
  exact Function.bijective_id

/-! ### Differential operators and their geometric principal symbols -/

section DifferentialOperator

variable [∀ x, IsScalarTower ℝ ℂ (E x)] [∀ x, IsScalarTower ℝ ℂ (F x)] {k : ℕ}

omit [FiniteDimensional ℂ W] in
/-- The matrix entries of a differential operator `P : Γ(E) → Γ(F)` of order at most `k` have
principal symbol `i ^ k` times the reading in the frames of the geometric principal symbol of
`P`. -/
private theorem classicalPrincipalSymbol_sectionEntry_of_mem_differentialOperators
    (hP : P ∈ differentialOperators ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ k)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ)
    (x : M) {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    classicalPrincipalSymbol k (sectionEntry t ψ hψ v t' χ hχ ℓ P) x ξ =
      ((χ x * ψ x : ℝ) : ℂ) * ℓ (t'.continuousLinearMapAt ℂ x (Complex.I ^ k •
        sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
          ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_of_complex hP⟩ ξ
          (t.symm x v))) := by
  -- Write `ξ = df_x` for a real smooth function `f`, acting on sections as the complex `g`.
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯,
      mvfderiv 𝓘(ℝ, CoordinateSpace n) f x = ξ :=
    ⟨_, mvfderiv_covectorLift BoundarylessManifold.isInteriorPoint ξ⟩
  set g := ContMDiffMap.ofReal f
  set s := t.cutoffFrameSection ψ hψ v
  set C := (smulCommutator ℂ g ^ k) P
  -- The iterated commutators of the entry with `g` are the entries of those of `P` with `g`.
  have hentry : (smulCommutator ℂ g ^ k) (sectionEntry t ψ hψ v t' χ hχ ℓ P) 1 x =
      χ x • ℓ (t'.continuousLinearMapAt ℂ x (C s x)) := by
    have h := smulCommutator_pow_comp_comp (R := ℂ) (a := g) (b := g)
      (ρ := (LinearMap.toSpanSingleton _ _ s).restrictScalars ℂ)
      (fun u ↦ map_smul (LinearMap.toSpanSingleton _ _ s) g u)
      (t'.cutoffFrameCoeff_smul_of_normedAlgebra χ hχ ℓ g) P k
    have hP' : sectionEntry t ψ hψ v t' χ hχ ℓ P = t'.cutoffFrameCoeff χ hχ ℓ ∘ₗ P ∘ₗ
        (LinearMap.toSpanSingleton _ _ s).restrictScalars ℂ := by
      ext u y
      simp [s]
    rw [hP', h]
    simp [C]
  -- The iterated commutators of `P` with `f` are those with `g`, so the geometric principal
  -- symbol at `df_x` is read from `C`.
  have hgeom : (smulCommutator ℝ f ^ k) (P.restrictScalars ℝ) = C.restrictScalars ℝ := by
    have h := smulCommutator_pow_comp_comp (R := ℝ) (a := g) (b := f) (ρ := LinearMap.id)
      (σ := LinearMap.id) (fun u ↦ by simp [g]) (fun u ↦ by simp [g]) (P.restrictScalars ℝ) k
    simpa [C] using h
  have hσ := sectionPrincipalSymbol_mvfderiv (x := x) BoundarylessManifold.isInteriorPoint
    ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_of_complex hP⟩ f s
  rw [hgeom] at hσ
  simp only [s, Bundle.Trivialization.cutoffFrameSection_apply, map_smul,
    LinearMap.coe_restrictScalars] at hσ
  set w := sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
    ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_of_complex hP⟩
    (mvfderiv 𝓘(ℝ, CoordinateSpace n) f x) (t.symm x v)
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hC : C s x = ((k.factorial : ℝ) * ψ x) • w := by
    rw [mul_smul, hσ, smul_inv_smul₀ hk]
  rw [classicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators
    (sectionEntry_mem_differentialOperators t ψ hψ v t' χ hχ ℓ hP) f hξ, hentry, hC]
  simp only [ContinuousLinearMap.map_smul_of_tower, map_smul, smul_eq_mul, Complex.real_smul]
  have hk' : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  push_cast
  field_simp

/-- **The principal symbol of a differential operator between bundles.** Let the real structures
of the fibres of `E` and `F` be those underlying their complex structures, and let
`P : Γ(E) → Γ(F)` be a differential operator of order at most `k` in Grothendieck's sense, for
commutators with multiplication by complex-valued smooth functions, so that `P` is a classical
pseudodifferential operator of order `k`
(`TauCeti.mem_sectionClassicalPseudodifferentialOperators_of_mem_differentialOperators`). At every
nonzero covector `ξ ∈ T*ₓM` its principal symbol of order `k` is `i ^ k` times its geometric
principal symbol (`TauCeti.sectionPrincipalSymbol`), defined by iterated commutators with
real-valued functions:

`σ_k(P)(x, ξ) = i ^ k σ_geom(P)(ξ)`.

This is the angular-frequency convention `σ(∂ⱼ) = i ξⱼ`, as for scalar operators
(`TauCeti.classicalPrincipalSymbol_complexifyLinearMap`). -/
theorem sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators
    (hP : P ∈ differentialOperators ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ k)
    (x : M) {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) (u : E x) :
    sectionClassicalPrincipalSymbol k P x ξ u =
      Complex.I ^ k • sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n)
        BoundarylessManifold.isInteriorPoint
        ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_of_complex hP⟩ ξ u := by
  have hx := FiberBundle.mem_baseSet_trivializationAt V E x
  have hx' := FiberBundle.mem_baseSet_trivializationAt W F x
  -- Read both sides in the preferred frames at `x`, along every functional `ℓ`.
  obtain ⟨v, rfl⟩ : ∃ v, (trivializationAt V E x).symm x v = u :=
    ⟨_, (trivializationAt V E x).symm_apply_apply_mk hx u⟩
  rw [← (trivializationAt W F x).symmL_continuousLinearMapAt (R := ℂ) hx'
      (sectionClassicalPrincipalSymbol _ P x ξ _),
    ← (trivializationAt W F x).symmL_continuousLinearMapAt (R := ℂ) hx' (Complex.I ^ k • _)]
  refine congrArg _ ((SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_)
  rw [coord_sectionClassicalPrincipalSymbol
      (mem_sectionClassicalPseudodifferentialOperators_of_mem_differentialOperators hP),
    classicalPrincipalSymbol_sectionEntry_of_mem_differentialOperators hP _ _ _ _ _ _ _ _ x hξ,
    frameCutoff_self (V := V) (W := W) n E F x]
  simp

/-- **Ellipticity of a differential operator between bundles.** A differential operator
`P : Γ(E) → Γ(F)` of order at most `k`, as in
`TauCeti.sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators`, is elliptic at `x` as
a classical pseudodifferential operator of order `k` exactly when it is elliptic at `x` in the
sense of its geometric principal symbol (`TauCeti.IsSectionEllipticAt`). -/
theorem isSectionClassicalEllipticAt_iff_isSectionEllipticAt
    (hP : P ∈ differentialOperators ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ k) {x : M} :
    IsSectionClassicalEllipticAt k P x ↔
      IsSectionEllipticAt ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_of_complex
        hP⟩ x := by
  have hc : Complex.I ^ k ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
      Function.Bijective (sectionClassicalPrincipalSymbol k P x ξ) ↔
        Function.Bijective (sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n)
          BoundarylessManifold.isInteriorPoint
          ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_of_complex hP⟩ ξ) := by
    rw [show ⇑(sectionClassicalPrincipalSymbol k P x ξ) = (fun w ↦ Complex.I ^ k • w) ∘
      ⇑(sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
        ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_of_complex hP⟩ ξ) from
      funext (sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators hP x hξ)]
    exact (MulAction.bijective (Units.mk0 _ hc)).of_comp_iff' _
  rw [isSectionEllipticAt_iff]
  exact ⟨fun hP' _ ξ hξ ↦ (h ξ hξ).1 (hP' ξ hξ),
    fun hP' ξ hξ ↦ (h ξ hξ).2 (hP' BoundarylessManifold.isInteriorPoint ξ hξ)⟩

/-- **Ellipticity of a differential operator between bundles.** A differential operator
`P : Γ(E) → Γ(F)` of order at most `k` is elliptic as a classical pseudodifferential operator of
order `k` exactly when it is elliptic in the sense of its geometric principal symbol
(`TauCeti.IsSectionElliptic`). So the elliptic theory of pseudodifferential operators applies to
elliptic differential operators, such as operators of Laplace type
(`TauCeti.IsSectionLaplaceType.isSectionElliptic`). -/
theorem isSectionClassicalElliptic_iff_isSectionElliptic
    (hP : P ∈ differentialOperators ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ k) :
    IsSectionClassicalElliptic k P ↔
      IsSectionElliptic ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_of_complex
        hP⟩ := by
  rw [isSectionElliptic_iff]
  exact forall_congr' fun _ ↦ isSectionClassicalEllipticAt_iff_isSectionEllipticAt hP

end DifferentialOperator

end TauCeti
