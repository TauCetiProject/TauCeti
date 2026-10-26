/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

import Mathlib.Analysis.Calculus.TangentCone.Real
import TauCeti.Analysis.Convex.StdSimplex

/-!
# Smooth triangulations of manifolds

A *smooth triangulation* of a manifold `M` (Whitehead's `C¹`-triangulation, Munkres' `Cʳ`
triangulation) is a homeomorphism `f : |K| ≃ₜ M` from the geometric realization of a simplicial
complex such that on every closed simplex `f` is `Cⁿ` with injective differential. These are the
triangulations through which a smooth manifold acquires its PL structure: by Whitehead's theorem
every smooth manifold, with or without boundary, has one, and any two have linearly isomorphic
subdivisions (Munkres, Theorems 10.5 and 10.6).

A closed simplex is not open in any ambient space, so smoothness on it is smoothness within a set.
We read a map on the closed coordinate simplex `StandardSimplex σ` in barycentric coordinates,
that is, as a map on the set of weight vectors of Mathlib's `Convexity.StdSimplex ℝ σ` inside the
finite-dimensional space `σ → ℝ`. The map is a `Cⁿ` *immersion of the simplex* if it is the
restriction of a map `(σ → ℝ) → M` which is `Cⁿ` within that set and has, at every point of the
simplex, a derivative within the simplex that is injective on the directions of the simplex, the
vectors with coordinate sum zero; all derivatives within the simplex agree on these directions.
Munkres calls such maps non-degenerate. The notion is meant for `1 ≤ n`, as in Munkres; for
`n = 0` it still asks for an injective derivative. Munkres asks for an extension to a
neighbourhood of the simplex in its plane rather than smoothness within the closed simplex; for a
closed simplex the two agree by Whitney's extension theorem, and the formulation within the
simplex also makes sense when `M` has boundary or corners.

Munkres defines a `Cʳ` triangulation as a homeomorphism onto `M` whose differential is injective
on the closed star of every point, not only on every closed simplex. By his Theorem 8.4 the two
conditions agree for homeomorphisms, and we use the simplexwise one, which is Whitehead's.

## Main definitions

* `TauCeti.IsSimplexImmersion I n g`: a map from a closed coordinate simplex into a manifold is a
  `Cⁿ` immersion of the simplex.
* `TauCeti.IsSmoothTriangulation I n f`: a homeomorphism from a realization onto a manifold is a
  `Cⁿ` triangulation.

## Main results

* `TauCeti.IsSimplexImmersion.comp`: post-composing with a `Cⁿ` map with injective
  differentials preserves immersions of simplices.
* `TauCeti.IsSmoothTriangulation.trans_diffeomorph`: a smooth triangulation can be pushed forward
  along a diffeomorphism.
* `TauCeti.isSmoothTriangulation_realizationOneSimplexHomeomorphUnitInterval`: the standard
  one-simplex is a smooth triangulation of the unit interval, for every smoothness exponent.
* `TauCeti.exists_contMDiff_not_isSmoothTriangulation_trans`: following that triangulation by the
  smooth homeomorphism `t ↦ t ^ 2` of the interval does not give a smooth triangulation, so the
  injectivity of the differential is a genuine condition.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Definitions 8.1–8.3, Theorem 8.4, and Theorems 10.5–10.6.
-/

public section

noncomputable section

open Set Function AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {m n : WithTop ℕ∞}

variable (I n) in
/-- A map `g` from the closed coordinate simplex on `σ` into a manifold `M` is a `Cⁿ` immersion of
the simplex if, in barycentric coordinates, it is the restriction of a map `F : (σ → ℝ) → M` that
is `Cⁿ` within the standard simplex (the weight vectors of `Convexity.StdSimplex ℝ σ`) and that
has, at every point of the simplex, a derivative within the simplex which is injective on the
directions of the simplex, the vectors with coordinate sum zero. -/
def IsSimplexImmersion {σ : Finset ι} (g : StandardSimplex σ → M) : Prop :=
  ∃ F : (σ → ℝ) → M, (∀ x : StandardSimplex σ, F (fun a => x.1 a) = g x) ∧
    ContMDiffOn 𝓘(ℝ, σ → ℝ) I n F (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) ∧
    ∀ t : Convexity.StdSimplex ℝ σ, ∃ F' : (σ → ℝ) →L[ℝ] E,
      HasMFDerivWithinAt 𝓘(ℝ, σ → ℝ) I F (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights)
        t.weights F' ∧
        ∀ v : σ → ℝ, ∑ a, v a = 0 → F' v = 0 → v = 0

/-- Unfold `TauCeti.IsSimplexImmersion` into its defining witness. -/
theorem isSimplexImmersion_iff {σ : Finset ι} {g : StandardSimplex σ → M} :
    IsSimplexImmersion I n g ↔
      ∃ F : (σ → ℝ) → M, (∀ x : StandardSimplex σ, F (fun a => x.1 a) = g x) ∧
        ContMDiffOn 𝓘(ℝ, σ → ℝ) I n F (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) ∧
        ∀ t : Convexity.StdSimplex ℝ σ, ∃ F' : (σ → ℝ) →L[ℝ] E,
          HasMFDerivWithinAt 𝓘(ℝ, σ → ℝ) I F
            (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) t.weights F' ∧
            ∀ v : σ → ℝ, ∑ a, v a = 0 → F' v = 0 → v = 0 :=
  Iff.rfl

namespace IsSimplexImmersion

variable {σ : Finset ι} {g : StandardSimplex σ → M}

/-- An immersion of a simplex of class `Cⁿ` is one of every lower class `Cᵐ`. -/
theorem of_le (h : IsSimplexImmersion I n g) (hmn : m ≤ n) : IsSimplexImmersion I m g := by
  obtain ⟨F, hFg, hF, hF'⟩ := h
  exact ⟨F, hFg, hF.of_le hmn, hF'⟩

/-- Post-composing an immersion of a simplex with a `Cⁿ` map whose differential is injective at
every point gives an immersion of the simplex. -/
theorem comp (h : IsSimplexImmersion I n g) {φ : M → N} (hφ : ContMDiff I J n φ)
    (hφ' : ∀ x, Injective (mfderiv I J φ x)) :
    IsSimplexImmersion J n (φ ∘ g) := by
  obtain ⟨F, hFg, hF, hF'⟩ := h
  refine ⟨φ ∘ F, fun x => by simp [hFg], hφ.comp_contMDiffOn hF, fun t => ?_⟩
  obtain ⟨F', hFt, hinj⟩ := hF' t
  -- An injective `mfderiv` forces differentiability: otherwise it is `0`, so `E` is trivial.
  have hφt : MDifferentiableAt I J φ (F t.weights) := by
    by_contra hd
    have : Subsingleton E := ⟨fun a b => hφ' (F t.weights) <| by
      rw [mfderiv_zero_of_not_mdifferentiableAt hd]; rfl⟩
    exact hd (mdifferentiable_of_subsingleton _)
  refine ⟨(mfderiv I J φ (F t.weights)).comp F', hφt.hasMFDerivAt.comp_hasMFDerivWithinAt _ hFt,
    fun v hv hv0 => hinj v hv (hφ' (F t.weights) ?_)⟩
  exact hv0.trans (map_zero _).symm

end IsSimplexImmersion

variable (I n) in
/-- A homeomorphism `f` from the realization of a simplicial complex `K` onto a manifold `M` is a
`Cⁿ` triangulation of `M` if it is a `Cⁿ` immersion on every closed simplex of `K`. This is
Whitehead's notion of a `C¹`-triangulation, in class `Cⁿ`. -/
def IsSmoothTriangulation {K : AbstractSimplicialComplex ι} (f : Realization K ≃ₜ M) : Prop :=
  ∀ σ : Face K, IsSimplexImmersion I n (f ∘ faceInclusion K σ)

/-- Unfold `TauCeti.IsSmoothTriangulation`: `f` is an immersion on every closed simplex. -/
theorem isSmoothTriangulation_iff {K : AbstractSimplicialComplex ι} {f : Realization K ≃ₜ M} :
    IsSmoothTriangulation I n f ↔ ∀ σ : Face K, IsSimplexImmersion I n (f ∘ faceInclusion K σ) :=
  Iff.rfl

namespace IsSmoothTriangulation

variable {K : AbstractSimplicialComplex ι} {f : Realization K ≃ₜ M}

/-- A smooth triangulation of class `Cⁿ` is one of every lower class `Cᵐ`. -/
theorem of_le (h : IsSmoothTriangulation I n f) (hmn : m ≤ n) : IsSmoothTriangulation I m f :=
  fun σ => (h σ).of_le hmn

/-- A smooth triangulation of `M` followed by a diffeomorphism `M ≃ N` is a smooth triangulation
of `N`. -/
theorem trans_diffeomorph (h : IsSmoothTriangulation I n f) (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    IsSmoothTriangulation J n (f.trans Φ.toHomeomorph) := fun σ =>
  -- `(f.trans Φ.toHomeomorph) ∘ faceInclusion K σ` is `Φ ∘ (f ∘ faceInclusion K σ)` by definition.
  (h σ).comp (φ := Φ) Φ.contMDiff (fun x => by
    rw [← Φ.mfderivToContinuousLinearEquiv_coe hn]
    exact (Φ.mfderivToContinuousLinearEquiv hn x).injective)

end IsSmoothTriangulation

/-! ### The standard one-simplex triangulates the unit interval -/

section UnitInterval

/-- On a face `σ` of the standard one-simplex, the barycentric coordinate at the vertex `1`, as a
linear functional on `σ → ℝ`; it vanishes when `1 ∉ σ`. -/
private def coordOne (σ : Finset (Fin 2)) : (σ → ℝ) →L[ℝ] ℝ :=
  if h : (1 : Fin 2) ∈ σ then ContinuousLinearMap.proj (⟨1, h⟩ : σ) else 0

private theorem coordOne_apply_coe {σ : Finset (Fin 2)} (x : StandardSimplex σ) :
    coordOne σ (fun a => x.1 a) = x.1 1 := by
  by_cases h : (1 : Fin 2) ∈ σ
  · simp [coordOne, h]
  · simpa [coordOne, h] using
      (Finsupp.notMem_support_iff.mp fun h' => h (StandardSimplex.support_subset x h')).symm

private theorem coordOne_weights_mem_Icc {σ : Finset (Fin 2)} (t : Convexity.StdSimplex ℝ σ) :
    coordOne σ t.weights ∈ Icc (0 : ℝ) 1 := by
  by_cases h : (1 : Fin 2) ∈ σ
  · simp [coordOne, h, t.weights_apply_le_one]
  · simp [coordOne, h]

/-- The coordinate at the vertex `1` is injective on the directions of every face of the standard
one-simplex. -/
private theorem eq_zero_of_coordOne_eq_zero {σ : Finset (Fin 2)} {v : σ → ℝ}
    (hv : ∑ a, v a = 0) (hv1 : coordOne σ v = 0) : v = 0 := by
  have h1 : ∀ b : σ, (b : Fin 2) = 1 → v b = 0 := by
    intro b hb
    have h : (1 : Fin 2) ∈ σ := hb ▸ b.2
    obtain rfl : b = ⟨1, h⟩ := Subtype.ext hb
    simpa [coordOne, h] using hv1
  have key : ∀ c d : Fin 2, c ≠ 1 → d ≠ c → d = 1 := by decide
  funext a
  by_cases ha : (a : Fin 2) = 1
  · exact h1 a ha
  · rwa [Finset.sum_eq_single a (fun b _ hba => h1 b (key a b ha fun h => hba (Subtype.ext h)))
      (by simp)] at hv

variable [Fact ((0 : ℝ) < 1)]

/-- The standard one-simplex, realized as the unit interval through its second barycentric
coordinate, is a `Cⁿ` triangulation of the unit interval for every `n`. -/
theorem isSmoothTriangulation_realizationOneSimplexHomeomorphUnitInterval :
    IsSmoothTriangulation (𝓡∂ 1) n realizationOneSimplexHomeomorphUnitInterval := by
  intro σ
  refine ⟨fun y => projIcc 0 1 zero_le_one (coordOne σ.1 y), fun x => ?_, ?_, fun t => ?_⟩
  · apply Subtype.ext
    dsimp only
    rw [coordOne_apply_coe, comp_apply, realizationOneSimplexHomeomorphUnitInterval_coe,
      faceInclusion_val, projIcc_of_mem]
    have hle := Realization.le_one _ (faceInclusion _ σ x) 1
    rw [faceInclusion_val] at hle
    exact ⟨StandardSimplex.nonneg x 1, hle⟩
  · exact contMDiffOn_projIcc.comp (coordOne σ.1).contMDiff.contMDiffOn
      (by rintro _ ⟨t, rfl⟩; exact coordOne_weights_mem_Icc t)
  · have hz := coordOne_weights_mem_Icc t
    have hp := ((contMDiffOn_projIcc (n := 1) _ hz).mdifferentiableWithinAt one_ne_zero)
    refine ⟨(mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (projIcc 0 1 zero_le_one) (Icc 0 1)
      (coordOne σ.1 t.weights)).comp (coordOne σ.1),
      hp.hasMFDerivWithinAt.comp _ (coordOne σ.1).hasMFDerivWithinAt
        (by rintro _ ⟨t, rfl⟩; exact coordOne_weights_mem_Icc t), fun v hv hv0 => ?_⟩
    refine eq_zero_of_coordOne_eq_zero hv ?_
    -- The tangent spaces of `ℝ` are `ℝ` itself, and their unit vector is `1 : ℝ`.
    have hsmul : coordOne σ.1 v • (1 : TangentSpace 𝓘(ℝ) (coordOne σ.1 t.weights)) =
        coordOne σ.1 v :=
      mul_one (M := ℝ) _
    have hv0' : mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (projIcc 0 1 zero_le_one) (Icc 0 1)
        (coordOne σ.1 t.weights) (coordOne σ.1 v • 1) = 0 := by
      rw [hsmul]
      exact hv0
    rw [map_smul, mfderivWithin_projIcc_one hz] at hv0'
    refine (smul_eq_zero.mp hv0').resolve_right fun h1 => ?_
    -- The unit tangent vector of the interval is nonzero, since its image in `ℝ` is `1`.
    have h := mfderiv_subtypeVal_Icc_one (projIcc 0 1 zero_le_one (coordOne σ.1 t.weights))
    rw [h1, map_zero] at h
    exact zero_ne_one (α := ℝ) h

/-- Squaring, as a self-homeomorphism of the unit interval. -/
private def sqHomeomorph : unitInterval ≃ₜ unitInterval where
  toFun t := ⟨(t : ℝ) ^ 2, by simpa [sq] using unitInterval.mul_mem t.2 t.2⟩
  invFun t := ⟨√(t : ℝ), Real.sqrt_nonneg _, Real.sqrt_le_one.mpr t.2.2⟩
  left_inv t := Subtype.ext (Real.sqrt_sq t.2.1)
  right_inv t := Subtype.ext (Real.sq_sqrt t.2.1)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem contMDiff_sqHomeomorph : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ sqHomeomorph :=
  contMDiff_iff_comp_subtypeVal_Icc.mpr
    ⟨sqHomeomorph.continuous,
      (contDiff_id.pow 2).contMDiff.comp (contMDiff_subtypeVal_Icc (x := 0) (y := 1))⟩

omit [Fact ((0 : ℝ) < 1)] in
/-- If `F` extends the standard triangulation of the unit interval followed by squaring on a face
`σ`, then, read in `ℝ`, `F` is the square of the barycentric coordinate at the vertex `1` on the
standard simplex. -/
private theorem eqOn_sq_of_trans_sqHomeomorph {σ : Face (⊤ : AbstractSimplicialComplex (Fin 2))}
    {F : (σ.1 → ℝ) → unitInterval} (hFg : ∀ x : StandardSimplex σ.1, F (fun a => x.1 a) =
      (realizationOneSimplexHomeomorphUnitInterval.trans sqHomeomorph ∘ faceInclusion ⊤ σ) x)
    (i₁ : σ.1) (hi₁ : (i₁ : Fin 2) = 1) :
    EqOn (fun y => (y i₁) ^ 2) (Subtype.val ∘ F)
      (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights) := by
  rintro _ ⟨t, rfl⟩
  have hcoe : (fun a : σ.1 => ((Finset.standardSimplexHomeomorph σ.1).symm t).1 a) = t.weights :=
    funext fun a => by simp [Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
  have h := congrArg Subtype.val (hFg ((Finset.standardSimplexHomeomorph σ.1).symm t))
  rw [hcoe] at h
  simp only [comp_apply, h, Homeomorph.trans_apply]
  simp [sqHomeomorph, ← hi₁, Finsupp.mapDomain_apply_of_injective Subtype.val_injective t.weights]

/-- Smoothness of a triangulating homeomorphism on every simplex does not make it a smooth
triangulation: following the standard triangulation of the unit interval by the smooth
homeomorphism `t ↦ t ^ 2`, whose derivative vanishes at `0`, gives a homeomorphism that is not a
`Cⁿ` triangulation for any `n`. In particular, `IsSmoothTriangulation.trans_diffeomorph` fails for
smooth homeomorphisms. -/
theorem exists_contMDiff_not_isSmoothTriangulation_trans :
    ∃ h : unitInterval ≃ₜ unitInterval, ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ h ∧
      ¬IsSmoothTriangulation (𝓡∂ 1) n (realizationOneSimplexHomeomorphUnitInterval.trans h) := by
  refine ⟨sqHomeomorph, contMDiff_sqHomeomorph, fun hT => ?_⟩
  let σ : Face (⊤ : AbstractSimplicialComplex (Fin 2)) := ⟨Finset.univ, Finset.univ_nonempty⟩
  let S := range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights
  let i₀ : σ.1 := ⟨0, Finset.mem_univ _⟩
  let i₁ : σ.1 := ⟨1, Finset.mem_univ _⟩
  let t₀ : Convexity.StdSimplex ℝ σ.1 := .single i₀
  let t₁ : Convexity.StdSimplex ℝ σ.1 := .single i₁
  obtain ⟨F, hFg, -, hF'⟩ := hT σ
  obtain ⟨F', hFt₀, hinj⟩ := hF' t₀
  -- Read in `ℝ`, the map is `y ↦ (y i₁) ^ 2` on the simplex.
  have hformula : EqOn (fun y => (y i₁) ^ 2) (Subtype.val ∘ F) S :=
    eqOn_sq_of_trans_sqHomeomorph hFg i₁ rfl
  -- Its derivative at the vertex `i₀` is zero within the simplex.
  have hzero : HasFDerivWithinAt (Subtype.val ∘ F) (0 : (σ.1 → ℝ) →L[ℝ] ℝ) S t₀.weights := by
    have hsq := ((ContinuousLinearMap.proj (R := ℝ) i₁).hasFDerivAt (x := ⇑t₀.weights)).mul
      ((ContinuousLinearMap.proj (R := ℝ) i₁).hasFDerivAt (x := ⇑t₀.weights))
    have hi : t₀.weights i₁ = 0 := by simp [t₀, i₀, i₁]
    simp only [ContinuousLinearMap.proj_apply, hi, zero_smul, add_zero] at hsq
    have hsq' : HasFDerivWithinAt (fun y : σ.1 → ℝ => (y i₁) ^ 2) (0 : (σ.1 → ℝ) →L[ℝ] ℝ) S
        t₀.weights :=
      hsq.hasFDerivWithinAt.congr (fun y _ => sq _) (sq _)
    exact hsq'.congr hformula.symm (hformula ⟨t₀, rfl⟩).symm
  -- The derivative supplied by `hT`, read in `ℝ`, is a second derivative there.
  -- Typed into `ℝ` rather than a tangent space of `ℝ`, so that `ℝ`'s own instances are used.
  let L : (σ.1 → ℝ) →L[ℝ] ℝ := (mfderiv (𝓡∂ 1) 𝓘(ℝ) Subtype.val (F t₀.weights)).comp F'
  have hG : HasFDerivWithinAt (Subtype.val ∘ F) L S t₀.weights :=
    ((((contMDiff_subtypeVal_Icc (x := 0) (y := 1) (n := 1)) (F t₀.weights)).mdifferentiableAt
      one_ne_zero).hasMFDerivAt.comp_hasMFDerivWithinAt _ hFt₀).hasFDerivWithinAt
  -- The edge direction from `i₀` to `i₁` is tangent to the simplex at `i₀`, so both derivatives
  -- agree on it.
  have hseg : segment ℝ (⇑t₀.weights) (⇑t₁.weights) ⊆ S :=
    (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ.1).segment_subset ⟨t₀, rfl⟩
      ⟨t₁, rfl⟩
  have hcone : ⇑t₁.weights - ⇑t₀.weights ∈ tangentConeAt ℝ S t₀.weights :=
    mem_tangentConeAt_of_segment_subset hseg
  have hv : L (⇑t₁.weights - ⇑t₀.weights) = 0 :=
    hG.unique_on hzero hcone
  have hF'v : F' (⇑t₁.weights - ⇑t₀.weights) = 0 :=
    (isImmersionOfComplement_subtypeVal_Icc (n := 1)).mfderiv_injective one_ne_zero _
      (hv.trans (map_zero _).symm)
  have hsum : ∑ a, (⇑t₁.weights - ⇑t₀.weights) a = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Convexity.StdSimplex.total_of_fintype,
      sub_self]
  have := congrFun (hinj _ hsum hF'v) i₁
  simp [t₀, t₁, i₀, i₁] at this

end UnitInterval

end TauCeti
