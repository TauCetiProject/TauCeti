/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# The coordinate frame of a chart, and symmetry of the Christoffel symbols

The canonical trivialization of the tangent bundle at `x₀` is read off the chart at `x₀`, so the
local frame it induces from a basis `b` of the model space is the classical *coordinate frame*
`∂/∂x¹, …, ∂/∂xⁿ` of that chart: over the chart source, `e.localFrame b i` is the pullback along
the extended chart of the constant model-space vector field with value `b i`.  Constant vector
fields on a normed space commute, and the manifold Lie bracket is natural under pullback, so the
coordinate frame commutes as well.

Torsion-freedom of a covariant derivative on the tangent bundle says that `∇_X Y - ∇_Y X` is the
Lie bracket `[X, Y]`.  Applied to the coordinate frame it therefore gives `∇_{∂ᵢ} ∂ⱼ = ∇_{∂ⱼ} ∂ᵢ`,
that is, the classical symmetry `Γᵏᵢⱼ = Γᵏⱼᵢ` of the Christoffel symbols in a chart, and the
corresponding symmetry of the model-space Christoffel map.  This symmetry is what lets a
two-parameter map be differentiated covariantly in either order.

## Main results

* `TauCeti.Manifold.inverse_mfderiv_extChartAt`: the inverse of the differential of an extended
  chart is the inverse of the canonical tangent-bundle trivialization at its centre.
* `TauCeti.Manifold.eqOn_localFrame_trivializationAt_mpullbackWithin`: over the chart source, the
  local frame of the canonical trivialization at `x₀` is the pullback along the extended chart of
  a constant model-space vector field.
* `TauCeti.Manifold.mlieBracket_localFrame_trivializationAt`: the coordinate frame commutes.
* `TauCeti.Manifold.covariantDerivative_localFrame_comm`: a torsion-free covariant derivative
  differentiates the coordinate frame symmetrically.
* `TauCeti.Manifold.christoffelSymbol_comm` and `TauCeti.Manifold.christoffelMap_comm`: for a
  torsion-free covariant derivative the Christoffel symbols and the Christoffel map in a chart are
  symmetric in their two lower arguments, with
  `TauCeti.Manifold.christoffelMap_leviCivita_comm` the case of the Levi-Civita connection.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, §3, the symmetry of the
  Riemannian connection in a coordinate system.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4, Prop. 7.6 and the
  symmetry of the connection coefficients of a symmetric connection.
-/

public section

open Bundle Filter Manifold Module Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {x : M}

/-! ### The coordinate frame of a chart -/

section Frame

variable [IsManifold I 1 M]

/-- The differential of the extended chart at `x₀`, at a point `x` of its source, is inverted by
the inverse of the canonical tangent-bundle trivialization at `x₀`.  This is the inverse form of
`TangentBundle.symmL_trivializationAt`. -/
theorem inverse_mfderiv_extChartAt (x₀ : M) (hx : x ∈ (extChartAt I x₀).source) :
    (mfderiv% (extChartAt I x₀) x).inverse =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x := by
  rw [ContinuousLinearMap.inverse_eq
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hx)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx),
    ← TangentBundle.symmL_trivializationAt (by simpa using hx)]

/-- **The local frame of the canonical trivialization is the coordinate frame of the chart.**  Over
the source of the chart at `x₀`, the `i`-th section of the local frame induced by a basis `b` is
the pullback, along the extended chart, of the constant model-space vector field with value
`b i`. -/
theorem eqOn_localFrame_trivializationAt_mpullbackWithin (b : Basis ι 𝕜 E) (x₀ : M) (i : ι) :
    EqOn ((trivializationAt E (TangentSpace I) x₀).localFrame b i)
      (mpullbackWithin I 𝓘(𝕜, E) (extChartAt I x₀)
        (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z) (extChartAt I x₀).source)
      (extChartAt I x₀).source := by
  intro y hy
  -- No rewrite reaches the pullback here: `TangentSpace 𝓘(𝕜, E) z` is only definitionally the
  -- model space, so the constant field makes the goal ill-typed at `implicit` transparency.
  have hpull : mpullbackWithin I 𝓘(𝕜, E) (extChartAt I x₀)
      (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z) (extChartAt I x₀).source y =
      (mfderiv[(extChartAt I x₀).source] (extChartAt I x₀) y).inverse (b i) := rfl
  rw [hpull, mfderivWithin_of_isOpen (isOpen_extChartAt_source x₀) hy,
    inverse_mfderiv_extChartAt x₀ hy]
  exact (symmL_basis_eq_localFrame b (by simpa using hy) i).symm

end Frame

variable [CompleteSpace E] [IsManifold I (minSmoothness 𝕜 2) M]

/-- **The coordinate frame of a chart commutes.**  The local frame that a basis of the model space
induces through the canonical tangent-bundle trivialization at `x₀` has vanishing Lie brackets on
the source of the chart at `x₀`. -/
theorem mlieBracket_localFrame_trivializationAt (b : Basis ι 𝕜 E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (i j : ι) :
    mlieBracket I ((trivializationAt E (TangentSpace I) x₀).localFrame b i)
      ((trivializationAt E (TangentSpace I) x₀).localFrame b j) x = 0 := by
  have hsopen : IsOpen (extChartAt I x₀).source := isOpen_extChartAt_source x₀
  -- Naturality of the manifold Lie bracket under the pullback along the chart at `x₀`.
  have key := mpullbackWithin_mlieBracketWithin (I := I) (I' := 𝓘(𝕜, E))
    (f := (extChartAt I x₀ : M → E))
    (V := (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z))
    (W := (fun _ ↦ b j : Π z : E, TangentSpace 𝓘(𝕜, E) z))
    (s := (extChartAt I x₀).source) (t := univ) (x₀ := x) (n := minSmoothness 𝕜 2)
    (hV := ((contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt (n := 1)).2
      contDiffWithinAt_const).mdifferentiableWithinAt one_ne_zero)
    (hW := ((contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt (n := 1)).2
      contDiffWithinAt_const).mdifferentiableWithinAt one_ne_zero)
    (hu := hsopen.uniqueMDiffOn)
    (hf := (contMDiffAt_extChartAt' (by simpa using hx)).contMDiffWithinAt)
    (hx₀ := hx) (hn := le_rfl) (hst := by simp)
    (h'x₀ := by rw [hsopen.interior_eq]; exact subset_closure hx)
  -- Constant vector fields on the model space commute.
  have hconst : mlieBracketWithin 𝓘(𝕜, E)
      (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z)
      (fun _ ↦ b j : Π z : E, TangentSpace 𝓘(𝕜, E) z) univ =
      (0 : Π z : E, TangentSpace 𝓘(𝕜, E) z) := by
    refine (mlieBracketWithin_univ (I := 𝓘(𝕜, E))
      (V := (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z))
      (W := (fun _ ↦ b j : Π z : E, TangentSpace 𝓘(𝕜, E) z))).trans ?_
    funext z
    exact mlieBracket_const_model_space (𝕜 := 𝕜) (F := E) (b i) (b j) z
  rw [hconst] at key
  -- As above, the pullback of the zero field is reached definitionally rather than by rewriting.
  have hpull : mpullbackWithin I 𝓘(𝕜, E) (extChartAt I x₀)
      (0 : Π z : E, TangentSpace 𝓘(𝕜, E) z) (extChartAt I x₀).source x =
      (mfderiv[(extChartAt I x₀).source] (extChartAt I x₀) x).inverse 0 := rfl
  rw [hpull, map_zero] at key
  rw [← mlieBracketWithin_of_isOpen (I := I) hsopen hx,
    mlieBracketWithin_congr' (eqOn_localFrame_trivializationAt_mpullbackWithin b x₀ i)
      (eqOn_localFrame_trivializationAt_mpullbackWithin b x₀ j) hx]
  exact key.symm

/-! ### Symmetry of the Christoffel symbols of a torsion-free connection -/

section Christoffel

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- **A torsion-free connection differentiates the coordinate frame symmetrically**: in the chart
at `x₀`, `∇_{∂ᵢ} ∂ⱼ = ∇_{∂ⱼ} ∂ᵢ`. -/
theorem covariantDerivative_localFrame_comm (ht : cov.IsTorsionFree) (b : Basis ι 𝕜 E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (i j : ι) :
    cov ((trivializationAt E (TangentSpace I) x₀).localFrame b j) x
        ((trivializationAt E (TangentSpace I) x₀).localFrame b i x) =
      cov ((trivializationAt E (TangentSpace I) x₀).localFrame b i) x
        ((trivializationAt E (TangentSpace I) x₀).localFrame b j x) := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  have hframe (l : ι) :
      MDiffAt (T% ((trivializationAt E (TangentSpace I) x₀).localFrame b l)) x :=
    (((trivializationAt E (TangentSpace I) x₀).contMDiffOn_localFrame_baseSet 1 b l).contMDiffAt
      ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hbase)).mdifferentiableAt
      one_ne_zero
  have h := (CovariantDerivative.isTorsionFree_iff cov).mp ht (hframe i) (hframe j)
  rwa [mlieBracket_localFrame_trivializationAt b x₀ hx i j, sub_eq_zero] at h

/-- **The Christoffel symbols of a torsion-free connection are symmetric in their lower indices**:
`Γᵏᵢⱼ = Γᵏⱼᵢ` in the frame of the canonical tangent-bundle trivialization at `x₀`. -/
theorem christoffelSymbol_comm (ht : cov.IsTorsionFree) (b : Basis ι 𝕜 E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (i j k : ι) :
    christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov i j k x =
      christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov j i k x := by
  rw [christoffelSymbol_apply, christoffelSymbol_apply,
    covariantDerivative_localFrame_comm ht b x₀ hx i j]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype ι]

/-- **The Christoffel map of a torsion-free connection is symmetric.**  Read in the canonical
tangent-bundle trivialization at `x₀`, the model-space Christoffel map of a torsion-free covariant
derivative is a symmetric bilinear map. -/
theorem christoffelMap_comm (ht : cov.IsTorsionFree) (b : Basis ι 𝕜 E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (v w : E) :
    christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x v w =
      christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x w v := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  -- A continuous bilinear map is determined by its values on a pair of basis vectors.
  have hsymm : christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x =
      (christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x).flip := by
    refine ContinuousLinearMap.coe_injective (b.ext fun j ↦ ?_)
    simp only [ContinuousLinearMap.coe_coe]
    refine ContinuousLinearMap.coe_injective (b.ext fun i ↦ ?_)
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply]
    rw [christoffelMap_apply_basis b _ hbase i j, christoffelMap_apply_basis b _ hbase j i]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [christoffelSymbol_comm ht b x₀ hx i j k]
  conv_lhs => rw [hsymm]
  rw [ContinuousLinearMap.flip_apply]

end Christoffel

/-! ### The Levi-Civita connection -/

section LeviCivita

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] {x : M}

/-- **The Christoffel map of the Levi-Civita connection is symmetric.**  The Levi-Civita
connection is torsion-free, so in every chart its Christoffel map is a symmetric bilinear map on
the model space.  This is the form in which the symmetry enters the second-order geodesic equation
and the covariant differentiation of a two-parameter map. -/
theorem christoffelMap_leviCivita_comm (b : Basis ι ℝ E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (v w : E) :
    christoffelMap b ((CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x v w =
      christoffelMap b ((CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x w v := by
  -- Over `ℝ` the symmetry threshold `minSmoothness ℝ 2` is just `2`.
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  exact christoffelMap_comm ((CovariantDerivative.isTorsionFree_iff _).mpr fun hX hY ↦
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection
      (I := I) (M := M)).sub_eq_mlieBracket hX hY) b x₀ hx v w

end LeviCivita

end TauCeti.Manifold
