/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Descent
public import TauCeti.Geometry.Toric.Delzant.Quotient.Manifold

/-!
# The symplectic form of the Delzant quotient

Let `i : N →+ V` be an integral lattice and `(u, c)` the facet presentation of a Delzant polytope
`Δ` with `d` facets in a space `V` of dimension `n`. Delzant's construction realizes `Δ` as the
moment polytope of the symplectic reduction `M_Δ = Z / N_Δ` of `ℂ^ι`: `Z` is the zero level of the
moment map `z ↦ μ(z)|_𝔫` of the kernel torus `N_Δ ⊆ (ℝ / 2πℤ)^ι`, whose Lie algebra is
`𝔫 = ker β_ℝ`. `TauCeti.Geometry.Toric.Delzant.Quotient.Manifold` makes `M_Δ` a smooth manifold
for which the projection `Z → M_Δ` is a submersion. This file puts the reduced symplectic form on
it: the restriction `i^* ω` to `Z` of the standard symplectic form `ω = Σ dq_j ∧ dp_j` of `ℂ^ι`
descends to a symplectic form `ω_Δ` on `M_Δ`
(`TauCeti.Toric.IsDelzant.delzantQuotientSymplecticForm`,
`TauCeti.Toric.IsDelzant.isSymplectic_delzantQuotientSymplecticForm`), the unique two-form with
`π^* ω_Δ = i^* ω` (`TauCeti.Toric.IsDelzant.eq_delzantQuotientSymplecticForm_iff`). This is the
Marsden–Weinstein–Meyer reduced form of the Delzant quotient.

The descent `TauCeti.SmoothForm.descendedForm` along the surjective submersion `Z → M_Δ` needs
`i^* ω` to be basic, and is symplectic exactly when the null directions of `i^* ω` are the
vertical directions of the projection (`TauCeti.SmoothTwoForm.isSymplectic_descendedForm_iff`).
Both are identified with the orbit directions `𝔫 · x` of the kernel torus
(`TauCeti.Toric.kernelTorusOrbitTangent`).

* **The vertical directions of the projection.** The vertical tangent vectors of `Z → M_Δ` are
  exactly those carried by the inclusion into `𝔫 · x`
  (`TauCeti.Toric.IsDelzant.ker_mfderiv_delzantQuotientMk_eq_comap`, in
  `TauCeti.Geometry.Toric.Delzant.Quotient.Manifold`).
* **The null directions of `i^* ω`.** By the moment map equation `ω(t_M(x), v) = d⟨μ, t⟩_x(v)`
  (`TauCeti.Toric.hamiltonianVectorField_delzantMomentMap`),
  the tangent space `ker dμ_𝔫` of the level is the symplectic orthogonal of `𝔫 · x`
  (`TauCeti.Toric.ker_fderiv_delzantMomentMap_comp`). So the null directions of `i^* ω` at `x`
  are the vectors carried by the inclusion into `(𝔫 · x)^ω^ω = 𝔫 · x`
  (`TauCeti.Toric.IsDelzant.ker_bilinFormAt_mpullback_coe_delzantLevel`).
* **Basicness.** The torus `(ℝ / 2πℤ)^ι` acts by rotations, which preserve `ω`, so it preserves
  `i^* ω` (`TauCeti.Toric.IsDelzant.mpullback_vadd_mpullback_coe_delzantLevel`), and so does the
  kernel torus (`TauCeti.Toric.IsDelzant.mpullback_smul_mpullback_coe_delzantLevel`); its orbits
  are the fibres of the projection, and the vertical vectors are null for `i^* ω`
  (`TauCeti.Toric.IsDelzant.isBasic_mpullback_coe_delzantLevel`).

## Main definitions

* `TauCeti.Toric.IsDelzant.delzantQuotientSymplecticForm hΔ hi`: the symplectic form `ω_Δ` of the
  Delzant quotient.

## Main results

* `TauCeti.Toric.IsDelzant.isSymplectic_delzantQuotientSymplecticForm`: `ω_Δ` is symplectic.
* `TauCeti.Toric.IsDelzant.mpullback_delzantQuotientMk_delzantQuotientSymplecticForm`,
  `TauCeti.Toric.IsDelzant.eq_delzantQuotientSymplecticForm_iff`: `ω_Δ` is the unique two-form
  pulling back along `Z → M_Δ` to the restriction of the standard symplectic form of `ℂ^ι`.
* `TauCeti.Toric.IsDelzant.ker_bilinFormAt_mpullback_coe_delzantLevel`: the null directions of
  the restricted form are those carried into the orbit directions `𝔫 · x`.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 23 and 29.
-/

public section

noncomputable section

open Module Set Real
open scoped Manifold ContDiff

namespace TauCeti.Toric

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### The orbit directions and the tangent spaces of the level -/

/-- **The tangent space of the level is the symplectic orthogonal of the orbit directions.** The
kernel of the derivative at `x` of the moment map `z ↦ μ(z)|_𝔫` of the kernel torus is the
symplectic orthogonal of the tangent space `𝔫 · x` of its orbit through `x`. -/
theorem ker_fderiv_delzantMomentMap_comp (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (fderiv ℝ (fun y ↦ (delzantMomentMap c y).comp
        (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtypeL) x).ker =
      stdSymplecticForm.orthogonal (kernelTorusOrbitTangent i u x) := by
  set f := fun y ↦ (delzantMomentMap c y).comp
    (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtypeL
  have hf : DifferentiableAt ℝ f x :=
    ((contDiff_delzantMomentMap c (n := 1)).clm_comp contDiff_const).differentiable one_ne_zero x
  -- The component of `df_x` at `t ∈ 𝔫` is the derivative of the component `⟨μ, t⟩`.
  have hcomp (t) (v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
      fderiv ℝ f x v t = fderiv ℝ (fun y ↦ delzantMomentMap c y t) x v := by
    -- `delzantMomentMap c y t` is the component `f y t`, with `t` read in `ℝ^ι`.
    change _ = fderiv ℝ (fun y ↦ f y t) x v
    rw [fderiv_clm_apply hf (differentiableAt_const t)]
    simp
  -- The moment map equation `ω(t_M(x), v) = d⟨μ, t⟩_x(v)`.
  have hmom (t : ι → ℝ) (v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
      stdSymplecticForm (weightGenerator (-t) x) v =
        fderiv ℝ (fun y ↦ delzantMomentMap c y t) x v := by
    rw [← hamiltonianVectorField_delzantMomentMap, SymplecticForm.apply_hamiltonianVectorField]
  ext v
  rw [LinearMap.mem_ker, SymplecticForm.mem_orthogonal_iff]
  simp only [mem_kernelTorusOrbitTangent, forall_exists_index, and_imp]
  constructor
  · rintro h _ t ht rfl
    have h' : fderiv ℝ f x v ⟨t, ht⟩ = 0 := congrArg (fun L ↦ L ⟨t, ht⟩) h
    exact (hmom t v).trans ((hcomp ⟨t, ht⟩ v).symm.trans h')
  · intro h
    ext t
    exact (hcomp t v).trans ((hmom t v).symm.trans
      (h _ t t.property rfl))

variable [FiniteDimensional ℝ V]

namespace IsDelzant

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-- **The tangent space of the level.** The tangent space at `x` of the level `Z`, embedded in
`ℂ^ι` by the differential of the inclusion, is the symplectic orthogonal of the tangent space
`𝔫 · x` of the orbit of the kernel torus through `x`. -/
theorem range_mfderiv_coe_delzantLevel_eq_orthogonal (x : delzantLevel i u c) :
    letI := hΔ.delzantLevelChartedSpace hi
    LinearMap.range (mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x).toLinearMap =
      stdSymplecticForm.orthogonal (kernelTorusOrbitTangent i u x) := by
  rw [← ker_fderiv_delzantMomentMap_comp]
  exact hΔ.range_mfderiv_coe_delzantLevel hi x

/-! ### The restricted form on the level -/

/-- **The null directions of the restricted form are the orbit directions.** The kernel at `x` of
the restriction `i^* ω` to the level `Z` of the standard symplectic form `ω` of `ℂ^ι` consists of
the tangent vectors whose image in `ℂ^ι` lies in the tangent space `𝔫 · x` of the orbit of the
kernel torus: the tangent space of the level is the symplectic orthogonal of `𝔫 · x`. -/
theorem ker_bilinFormAt_mpullback_coe_delzantLevel (x : delzantLevel i u c) :
    letI := hΔ.delzantLevelChartedSpace hi
    haveI := hΔ.isManifold_delzantLevel hi ∞
    LinearMap.ker ((SmoothForm.mpullback
        ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth).bilinFormAt x) =
      (kernelTorusOrbitTangent i u x).comap
        (mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x).toLinearMap := by
  let _ := hΔ.delzantLevelChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  -- The differential of the inclusion, with values in `ℂ^ι`.
  let D : TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x →L[ℝ]
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x
  have heval (v w : TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x) :
      (SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth).bilinFormAt x v w =
      stdSymplecticForm (D v) (D w) := by
    rw [SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback,
      SymplecticForm.fromTangentSpace_constSmooth_apply]
    -- Tangent vectors of `ℂ^ι` are read in `ℂ^ι` by the identity `fromTangentSpace`.
    rfl
  -- The tangent space of the level is the symplectic orthogonal of the orbit directions.
  exact (SymplecticForm.ker_eq_comap_orthogonal_range stdSymplecticForm (ι := D.toLinearMap)
    fun v w ↦ (heval v w).symm).trans (congrArg (Submodule.comap D.toLinearMap)
      ((congrArg stdSymplecticForm.orthogonal
        (hΔ.range_mfderiv_coe_delzantLevel_eq_orthogonal hi x)).trans
        (SymplecticForm.orthogonal_orthogonal stdSymplecticForm (kernelTorusOrbitTangent i u x))))

/-- **The torus preserves the restricted form.** Each element `θ` of the torus acts on `ℂ^ι` by a
rotation, which preserves the standard symplectic form `ω`, so it preserves the restriction
`i^* ω` of `ω` to the level. -/
theorem mpullback_vadd_mpullback_coe_delzantLevel (θ : ι → AddCircle (2 * π)) :
    letI := hΔ.delzantLevelChartedSpace hi
    haveI := hΔ.isManifold_delzantLevel hi ∞
    haveI := hΔ.contMDiffVAdd_delzantLevel hi
    SmoothForm.mpullback (fun z : delzantLevel i u c ↦ θ +ᵥ z)
        (ContMDiffVAdd.contMDiff_const_vadd (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) θ)
        (SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth) =
      SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth := by
  let _ := hΔ.delzantLevelChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.contMDiffVAdd_delzantLevel hi
  set R := torusRotation θ
  have hRs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞ R := R.contMDiff
  have hR : SmoothForm.mpullback R hRs stdSymplecticForm.constSmooth =
      stdSymplecticForm.constSmooth := by
    refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
    rw [SmoothForm.eval₂_mpullback, SymplecticForm.eval₂_constSmooth_mfderiv_eq,
      SymplecticForm.fromTangentSpace_constSmooth_apply, mvfderiv_eq_fderiv, R.fderiv]
    exact stdSymplecticForm_torusRotation _ v w
  -- The inclusion intertwines the action on the level with the rotation `R` of `ℂ^ι`.
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ (hΔ.contMDiff_coe_delzantLevel hi) hRs
    (funext fun z ↦ coe_vadd_delzantLevel θ z), hR]

/-- **The restricted form is invariant under the kernel torus**, which acts on the level through
its angles. -/
theorem mpullback_smul_mpullback_coe_delzantLevel (k : kernelTorus i u) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := (kernelTorusData i u hi).chartedSpace
    haveI := hΔ.isManifold_delzantLevel hi ∞
    haveI := hΔ.contMDiffSMul_kernelTorus hi
    SmoothForm.mpullback (fun z : delzantLevel i u c ↦ k • z)
        (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, kernelTorusLieAlgebra i u)) k)
        (SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth) =
      SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth :=
  -- `k • z` is `(k : Multiplicative (ι → AddCircle (2 * π))).toAdd +ᵥ z` by definition of the
  -- actions of a subgroup and of a multiplicative type tag.
  hΔ.mpullback_vadd_mpullback_coe_delzantLevel hi (k : Multiplicative (ι → AddCircle (2 * π))).toAdd

/-- **The restricted form is basic** for the projection onto the Delzant quotient: it is invariant
under the kernel torus, whose orbits are the fibres of the projection, and the vertical tangent
vectors of the projection are its null directions. -/
theorem isBasic_mpullback_coe_delzantLevel :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantLevel hi ∞
    RoughForm.IsBasic (V := ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c)
      (SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth).val := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  let _ := (kernelTorusData i u hi).chartedSpace
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ.contMDiffSMul_kernelTorus hi
  -- Vertical vectors are null directions of the restricted form.
  have hnull (z : delzantLevel i u c) (v w : TangentSpace
      𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) z)
      (hv : mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) z v = 0) :
      SmoothBundleForm.eval₂ (SmoothForm.mpullback
        ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth) z v w = 0 := by
    have hv' : v ∈ LinearMap.ker ((SmoothForm.mpullback
        ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth).bilinFormAt z) := by
      rw [hΔ.ker_bilinFormAt_mpullback_coe_delzantLevel hi z,
        ← hΔ.ker_mfderiv_delzantQuotientMk_eq_comap hi z]
      exact hv
    rw [← SmoothForm.bilinFormAt_apply, LinearMap.mem_ker.1 hv', LinearMap.zero_apply]
  refine RoughForm.isBasic_of_mpullback_eq (σ := fun (k : kernelTorus i u) z ↦ k • z)
    ((hΔ.isSubmersion_delzantQuotientMk hi).contMDiff.mdifferentiable (by simp))
    (fun k ↦ (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, kernelTorusLieAlgebra i u)) k
      (n := ∞)).mdifferentiable (by simp))
    (fun k ↦ funext fun z ↦ DelzantQuotient.mk_eq_mk_iff_exists_smul.2 ⟨k, rfl⟩)
    (fun z z' h ↦ .inr (DelzantQuotient.mk_eq_mk_iff_exists_smul.1 h.symm))
    (fun z v j hj ↦ ?_) fun k ↦ by
      simpa only [SmoothForm.coe_mpullback] using
        congrArg Subtype.val (hΔ.mpullback_smul_mpullback_coe_delzantLevel hi k)
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv, ← SmoothBundleForm.eval₂_apply]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · exact hnull _ _ _ hj
  · rw [SmoothBundleForm.eval₂_swap, hnull _ _ _ hj, neg_zero]

/-! ### The symplectic form of the Delzant quotient -/

/-- **The symplectic form of the Delzant quotient** `M_Δ = Z / N_Δ`: the descent along the
projection `Z → M_Δ` of the restriction `i^* ω` to the level `Z` of the standard symplectic form
`ω = Σ dq_j ∧ dp_j` of `ℂ^ι`. It is the unique two-form on `M_Δ` pulling back to `i^* ω`
(`TauCeti.Toric.IsDelzant.eq_delzantQuotientSymplecticForm_iff`), and it is symplectic
(`TauCeti.Toric.IsDelzant.isSymplectic_delzantQuotientSymplecticForm`). -/
def delzantQuotientSymplecticForm :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (DelzantQuotient i u c) :=
  letI := hΔ.delzantLevelChartedSpace hi
  letI := hΔ.delzantQuotientChartedSpace hi
  haveI := hΔ.isManifold_delzantLevel hi ∞
  haveI := hΔ.isManifold_delzantQuotient hi
  SmoothForm.descendedForm (hΔ.isSubmersion_delzantQuotientMk hi) DelzantQuotient.mk_surjective
    _ (hΔ.isBasic_mpullback_coe_delzantLevel hi)

/-- The symplectic form of the Delzant quotient pulls back along the projection `Z → M_Δ` to the
restriction to the level `Z` of the standard symplectic form of `ℂ^ι`. -/
theorem mpullback_delzantQuotientMk_delzantQuotientSymplecticForm :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantLevel hi ∞
    haveI := hΔ.isManifold_delzantQuotient hi
    SmoothForm.mpullback (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c)
        (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff (hΔ.delzantQuotientSymplecticForm hi) =
      SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  exact SmoothForm.mpullback_descendedForm

/-- **The symplectic form of the Delzant quotient is characterized by its pullback**: a two-form on
`M_Δ` is the symplectic form of the Delzant quotient exactly when it pulls back along the
projection `Z → M_Δ` to the restriction to `Z` of the standard symplectic form of `ℂ^ι`. -/
theorem eq_delzantQuotientSymplecticForm_iff
    {η : letI := hΔ.delzantQuotientChartedSpace hi
      haveI := hΔ.isManifold_delzantQuotient hi
      SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (DelzantQuotient i u c)} :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantLevel hi ∞
    haveI := hΔ.isManifold_delzantQuotient hi
    η = hΔ.delzantQuotientSymplecticForm hi ↔
      SmoothForm.mpullback (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c)
          (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff η =
        SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  exact SmoothForm.eq_descendedForm_iff

/-- **The Delzant quotient is a symplectic manifold.** The descent of the standard symplectic form
of `ℂ^ι` to `M_Δ` is closed and nondegenerate: closed because the restriction to the level is, and
nondegenerate because the null directions of the restriction are exactly the orbit directions of
the kernel torus, the vertical directions of the projection. -/
theorem isSymplectic_delzantQuotientSymplecticForm :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    (hΔ.delzantQuotientSymplecticForm hi).IsSymplectic := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  exact SmoothTwoForm.isSymplectic_descendedForm_iff.2
    ⟨(SymplecticForm.isClosed_constSmooth stdSymplecticForm).mpullback _
      (hΔ.contMDiff_coe_delzantLevel hi), fun x ↦
      (hΔ.ker_bilinFormAt_mpullback_coe_delzantLevel hi x).trans
        (hΔ.ker_mfderiv_delzantQuotientMk_eq_comap hi x).symm⟩


end IsDelzant

end TauCeti.Toric
