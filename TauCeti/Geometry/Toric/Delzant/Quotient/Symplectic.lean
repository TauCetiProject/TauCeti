/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Inclusion
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.IsManifold.Basic
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
Both come from identifying the two with the orbit directions `𝔫 · x` of the kernel torus, the
generators `t_M(x)` of the rotations `z_j ↦ exp(-i s t_j) z_j` for `t ∈ 𝔫`
(`TauCeti.Toric.kernelTorusOrbitTangent`).

* **The null directions of `i^* ω`.** By the moment map equation `ω(t_M(x), v) = d⟨μ, t⟩_x(v)`
  (`TauCeti.Toric.hamiltonianVectorField_delzantMomentMap`),
  the tangent space `ker dμ_𝔫` of the level is the symplectic orthogonal of `𝔫 · x`
  (`TauCeti.Toric.ker_fderiv_delzantMomentMap_comp`). So the null directions of `i^* ω` at `x`
  are the vectors carried by the inclusion into `(𝔫 · x)^ω^ω = 𝔫 · x`
  (`TauCeti.Toric.IsDelzant.ker_bilinFormAt_mpullback_coe_delzantLevel`).
* **The vertical directions of the projection.** The projection `Z → M_Δ` is constant along the
  orbit curves `s ↦ exp(-i s t) x`, so `𝔫 · x` consists of images of vertical vectors
  (`TauCeti.Toric.IsDelzant.exists_mfderiv_delzantQuotientMk_eq_zero`). Conversely, the vertical
  vectors are the fundamental vector fields of the kernel torus
  (`TauCeti.Toric.IsDelzant.ker_mfderiv_delzantQuotientMk`), and these are generators of
  elements of `𝔫` (`TauCeti.Toric.IsDelzant.mfderiv_coe_fundamentalVectorField_mem`): a chart of
  the torus lifts the kernel torus near the identity to angles `t` with `β_ℝ t ∈ 2π i(N)`, and as
  this lattice is discrete, `β_ℝ t` is constant along the lift, so every tangent vector of the
  kernel torus at the identity lies in `𝔫`
  (`TauCeti.Toric.IsIntegralLattice.mfderiv_toAdd_coe_kernelTorus_mem`). Hence the vertical
  vectors are exactly those carried into `𝔫 · x`
  (`TauCeti.Toric.IsDelzant.ker_mfderiv_delzantQuotientMk_eq_comap`).
* **Basicness.** The kernel torus acts by rotations, which preserve `ω`, so it preserves `i^* ω`
  (`TauCeti.Toric.IsDelzant.mpullback_smul_mpullback_coe_delzantLevel`); its orbits are the fibres
  of the projection, and the vertical vectors are null for `i^* ω`
  (`TauCeti.Toric.IsDelzant.isBasic_mpullback_coe_delzantLevel`).

Counting dimensions with the same identification, `M_Δ` has dimension `(d + n) - (d - n) = 2n`
(`TauCeti.Toric.IsDelzant.finrank_delzantQuotientModelSpace`).

## Main definitions

* `TauCeti.Toric.kernelTorusOrbitTangent i u x`: the orbit directions `𝔫 · x` of the kernel torus
  at `x ∈ ℂ^ι`.
* `TauCeti.Toric.IsDelzant.delzantQuotientSymplecticForm hΔ hi`: the symplectic form `ω_Δ` of the
  Delzant quotient.

## Main results

* `TauCeti.Toric.IsDelzant.isSymplectic_delzantQuotientSymplecticForm`: `ω_Δ` is symplectic.
* `TauCeti.Toric.IsDelzant.mpullback_delzantQuotientMk_delzantQuotientSymplecticForm`,
  `TauCeti.Toric.IsDelzant.eq_delzantQuotientSymplecticForm_iff`: `ω_Δ` is the unique two-form
  pulling back along `Z → M_Δ` to the restriction of the standard symplectic form of `ℂ^ι`.
* `TauCeti.Toric.IsDelzant.ker_mfderiv_delzantQuotientMk_eq_comap`: the vertical tangent vectors
  of `Z → M_Δ` are those carried into the orbit directions `𝔫 · x`.
* `TauCeti.Toric.IsDelzant.finrank_delzantQuotientModelSpace`: `M_Δ` has dimension `2 dim V`.

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

/-! ### The orbit directions of the kernel torus in `ℂ^ι` -/

variable (i u) in
/-- The tangent space at `x` of the orbit of the kernel torus `N_Δ` through `x` in `ℂ^ι`: the
generators `t_M(x)` of the elements `t` of its Lie algebra `𝔫 = ker β_ℝ`. -/
def kernelTorusOrbitTangent (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    Submodule ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).map
    (weightInfinitesimalAction (fun j ↦ -ContinuousLinearMap.proj j) x)

/-- A vector lies in the orbit directions `𝔫 · x` exactly when it is the generator `t_M(x)` of an
element `t` of `𝔫`. -/
@[simp]
theorem mem_kernelTorusOrbitTangent {x v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} :
    v ∈ kernelTorusOrbitTangent i u x ↔
      ∃ t ∈ LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)),
        weightGenerator (-t) x = v := by
  simp only [kernelTorusOrbitTangent, Submodule.mem_map, weightInfinitesimalAction_apply]
  refine exists_congr fun t ↦ and_congr_right fun _ ↦ ?_
  rw [show (fun j ↦ (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j) t) = -t from
    funext fun j ↦ by simp]

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

/-! ### The Lie algebra of the kernel torus -/

/-- **The Lie algebra of the kernel torus lies in `𝔫`.** Read in the angle coordinates `ℝ^ι` of
the torus `(ℝ / 2πℤ)^ι`, every tangent vector at the identity of the kernel torus `N_Δ`, with its
Lie group structure as a closed subgroup, lies in `𝔫 = ker β_ℝ`. Near the identity, a chart of the
torus lifts `N_Δ` to angles `t` with `β_ℝ t ∈ 2π i(N)`, and since the lattice is discrete, `β_ℝ t`
is constant along this lift. -/
theorem IsIntegralLattice.mfderiv_toAdd_coe_kernelTorus_mem (hi : IsIntegralLattice i)
    (ξ : kernelTorusLieAlgebra i u) :
    letI := (kernelTorusData i u hi).chartedSpace
    mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (fun k : kernelTorus i u ↦ (k : Multiplicative (ι → AddCircle (2 * π))).toAdd) 1 ξ ∈
      LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)) := by
  let _ := (kernelTorusData i u hi).chartedSpace
  have := (kernelTorusData i u hi).lieGroup
  set J : kernelTorus i u → ι → AddCircle (2 * π) :=
    fun k ↦ (k : Multiplicative (ι → AddCircle (2 * π))).toAdd
  have hJ : ContMDiff 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ J :=
    Multiplicative.contMDiff_toAdd.comp (kernelTorusData i u hi).contMDiff_subtypeVal
  have hJ1 : J 1 = 0 := rfl
  set e := extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (0 : ι → AddCircle (2 * π))
  set β := Fintype.linearCombination ℝ fun j ↦ i (u j)
  have hsrc : ∀ᶠ k in nhds (1 : kernelTorus i u), J k ∈ e.source :=
    hJ.continuous.continuousAt.preimage_mem_nhds
      (hJ1 ▸ (isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source _))
  -- Along the lift `e ∘ J` of the kernel torus to angles, `β_ℝ` takes values in `2π i(N)`, so it
  -- is constant near the identity.
  have hmem : ∀ᶠ k in nhds (1 : kernelTorus i u), β (e (J k)) ∈ ((2 * π) • i).range :=
    hsrc.mono fun k hk ↦ by
      have h0 : facetTorusHom i u (2 * π) (fun j ↦ (e (J k) j : AddCircle (2 * π))) = 0 := by
        rw [AddCircle.coe_extChartAt_pi_apply _ _ hk]
        exact mem_kernelTorus.1 k.property
      rw [facetTorusHom_coe] at h0
      exact (QuotientAddGroup.eq_zero_iff _).1 h0
  have hcont : ContinuousAt (fun k ↦ β (e (J k))) 1 :=
    (LinearMap.continuous_of_finiteDimensional β).continuousAt.comp
      (ContinuousAt.comp_of_eq (continuousAt_extChartAt (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (0 : ι → AddCircle (2 * π))) (hJ.continuous.continuousAt (x := 1)) hJ1)
  have hconst := hi.eventually_eq_of_eventually_mem_range_smul hcont (2 * π) hmem
  -- Differentiate: the lift has derivative `τ`, and `β_ℝ τ = 0`.
  have hs : MDifferentiableAt 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, ι → ℝ) (e ∘ J) 1 :=
    (mdifferentiableAt_extChartAt (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (hJ1 ▸ mem_chart_source _ _)).comp 1 (hJ.mdifferentiableAt (by simp))
  have hτ : mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) J 1 ξ =
      mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, ι → ℝ) (e ∘ J) 1 ξ := by
    have hJeq : J =ᶠ[nhds 1] (fun t : ι → ℝ ↦ fun j ↦ (t j : AddCircle (2 * π))) ∘ (e ∘ J) :=
      hsrc.mono fun k hk ↦ (AddCircle.coe_extChartAt_pi_apply _ _ hk).symm
    have h := ((AddCircle.hasMFDerivAt_coe_pi (2 * π) ((e ∘ J) 1)).comp 1
      hs.hasMFDerivAt).congr_of_eventuallyEq_abuse hJeq
    -- The derivative of the covering map is the identity of `ℝ^ι`, so `id ∘L L` is `L`.
    exact (congrArg (fun L ↦ L ξ) h.mfderiv).trans rfl
  have hβ' : HasMFDerivAt 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, V) (fun k ↦ β (e (J k))) 1
      ((LinearMap.toContinuousLinearMap β).comp
        (mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, ι → ℝ) (e ∘ J) 1)) :=
    (LinearMap.toContinuousLinearMap β).hasMFDerivAt.comp 1 hs.hasMFDerivAt
  -- Membership in `ker β_ℝ`, for a tangent vector of the torus read in `ℝ^ι`.
  change β (mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    J 1 ξ) = 0
  rw [hτ]
  exact congrArg (fun L : kernelTorusLieAlgebra i u →L[ℝ] V ↦ L ξ) (hβ'.mfderiv.symm.trans
    ((hasMFDerivAt_const (β (e (J 1))) 1).congr_of_eventuallyEq_abuse hconst).mfderiv)

/-! ### The tangent spaces of the level -/

variable [FiniteDimensional ℝ V]

namespace IsDelzant

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-- **The orbits of the kernel torus in the level have dimension `dim 𝔫`.** At a point `x` of the
level the infinitesimal action of `𝔫` is injective, so the orbit directions `𝔫 · x` have the
dimension `d - n` of `𝔫`. -/
theorem finrank_kernelTorusOrbitTangent {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : x ∈ delzantLevel i u c) :
    finrank ℝ (kernelTorusOrbitTangent i u x) =
      finrank ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))) := by
  let g := (weightInfinitesimalAction (fun j ↦ -ContinuousLinearMap.proj j) x).comp
    (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtype
  have hgt (t : ι → ℝ) (ht) : g ⟨t, ht⟩ = weightGenerator (-t) x := by
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, weightInfinitesimalAction_apply]
    congr 1
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun ⟨t, ht⟩ h ↦ Subtype.ext ?_
    rw [hgt] at h
    exact (hΔ.weightGenerator_neg_eq_zero_iff hi hx ht).1 h
  have h := LinearMap.finrank_range_of_inj hg
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

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

/-- **The orbit directions are vertical.** For `t` in the Lie algebra `𝔫` of the kernel torus,
the generator `t_M(x)` is the image in `ℂ^ι` of a tangent vector of the level at `x` killed by the
differential of the projection onto the Delzant quotient: the velocity of the orbit curve
`s ↦ exp(-i s t) x`, along which the projection is constant. -/
theorem exists_mfderiv_delzantQuotientMk_eq_zero (x : delzantLevel i u c) {t : ι → ℝ}
    (ht : t ∈ LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    ∃ v : TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x,
      mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
            (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
          (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) x v = 0 ∧
        mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x v =
            weightGenerator (-t) x := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  -- The orbit curve `s ↦ exp(-i s t) x` in `ℂ^ι` is the rotation by the angles `[s t]`.
  set g : ℝ → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι := fun s ↦ weightRotation (s • -t) x
  have hg_eq : g = fun s ↦ torusRotation (fun j ↦ ((s • t) j : AddCircle (2 * π))) x := by
    funext s
    rw [torusRotation_coe, ← smul_neg]
  have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞ g := by
    rw [hg_eq]
    exact contMDiff_torusRotation.comp (((AddCircle.contMDiff_coe_pi (2 * π) ∞).comp
      (contMDiff_id.smul contMDiff_const)).prodMk contMDiff_const)
  have hgZ (s : ℝ) : g s ∈ delzantLevel i u c :=
    (weightRotation_mem_delzantLevel_iff _).2 x.property
  set γ : ℝ → delzantLevel i u c := fun s ↦ ⟨g s, hgZ s⟩
  have hγ : ContMDiff 𝓘(ℝ) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞ γ :=
    hΔ.contMDiff_codRestrict_delzantLevel hi hg hgZ
  have hγ0 : γ 0 = x := Subtype.ext (by simp [γ, g, weightRotation_zero])
  -- The projection is constant along the orbit curve.
  have hpγ : (DelzantQuotient.mk ∘ γ) = fun _ ↦ DelzantQuotient.mk x := by
    funext s
    refine DelzantQuotient.mk_eq_mk_iff.2 ⟨fun j ↦ ((s • t) j : AddCircle (2 * π)), ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, facetTorusHom_coe, map_smul, LinearMap.mem_ker.1 ht, smul_zero,
        QuotientAddGroup.mk_zero]
    · exact Subtype.ext ((coe_vadd_delzantLevel _ x).trans (congrFun hg_eq s).symm)
  have hp := (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff.mdifferentiable (by simp)
  have hi' := (hΔ.contMDiff_coe_delzantLevel hi (m := ∞)).mdifferentiable (by simp)
  have hγ' := hγ.mdifferentiable (by simp)
  refine ⟨mfderiv 𝓘(ℝ) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) γ 0 (1 : ℝ), ?_, ?_⟩
  · have h := (mfderiv_comp_apply_of_eq (0 : ℝ) (hp x) (hγ' 0) hγ0 (1 : ℝ)).symm
    rw [hpγ, mfderiv_const] at h
    -- The zero map between tangent spaces sends `1` to the zero tangent vector.
    exact h.trans rfl
  · have h := (mfderiv_comp_apply_of_eq (0 : ℝ) (hi' x) (hγ' 0) hγ0 (1 : ℝ)).symm
    have hcomp : (Subtype.val ∘ γ) = g := rfl
    have h0 := (hasDerivAt_weightRotation_smul (-t) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      0).hasFDerivAt
    rw [zero_smul, weightRotation_zero, ContinuousLinearMap.id_apply] at h0
    rw [hcomp, (hasMFDerivAt_iff_hasFDerivAt.2 h0).mfderiv] at h
    -- The derivative of a curve, as a linear map on `ℝ`, sends `1` to the velocity.
    exact h.trans (one_smul ℝ _)

/-- **The fundamental vector fields of the kernel torus are orbit directions.** The fundamental
vector field on the level `Z` of an element `ξ` of the Lie algebra of the kernel torus, embedded in
`ℂ^ι`, is the generator `t_M` of an element `t` of `𝔫`: the image of `ξ` in the angle coordinates
of the torus `(ℝ / 2πℤ)^ι`. -/
theorem mfderiv_coe_fundamentalVectorField_mem (x : delzantLevel i u c)
    (ξ : kernelTorusLieAlgebra i u) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := (kernelTorusData i u hi).chartedSpace
    mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x
        (fundamentalVectorField (I := 𝓘(ℝ, kernelTorusLieAlgebra i u)) (G := kernelTorus i u)
          𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ξ x) ∈
      kernelTorusOrbitTangent i u x := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := (kernelTorusData i u hi).chartedSpace
  have := (kernelTorusData i u hi).lieGroup
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.contMDiffSMul_kernelTorus hi
  set J : kernelTorus i u → ι → AddCircle (2 * π) :=
    fun k ↦ (k : Multiplicative (ι → AddCircle (2 * π))).toAdd
  have hJ : ContMDiff 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ J :=
    Multiplicative.contMDiff_toAdd.comp (kernelTorusData i u hi).contMDiff_subtypeVal
  set F := fun θ : ι → AddCircle (2 * π) ↦ torusRotation θ x
  have hF : ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞ F :=
    contMDiff_torusRotation.comp (contMDiff_id.prodMk contMDiff_const)
  -- In `ℂ^ι`, the orbit map of `x` is the orbit map of the rotation torus along `J`.
  have hval : (Subtype.val ∘ fun k : kernelTorus i u ↦ k • x) = F ∘ J :=
    funext fun k ↦ coe_kernelTorus_smul k x
  have ho := (ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℝ, kernelTorusLieAlgebra i u))
    (G := kernelTorus i u) (I' := 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (n := ∞)
      x).mdifferentiableAt
      (x := 1) (by simp)
  have hi' := (hΔ.contMDiff_coe_delzantLevel hi (m := ∞)).mdifferentiable (by simp) x
  have h1 := mfderiv_comp_apply_of_eq (1 : kernelTorus i u) hi' ho (one_smul (kernelTorus i u) x) ξ
  have h2 := mfderiv_comp_apply_of_eq (1 : kernelTorus i u)
    ((hF 0).mdifferentiableAt (by simp)) (hJ.mdifferentiableAt (by simp)) rfl ξ
  have h2' := h2.trans (mfderiv_torusRotation_zero (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) J 1 ξ))
  have h3 : mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      (Subtype.val ∘ fun k : kernelTorus i u ↦ k • x) 1 ξ =
      mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (F ∘ J) 1 ξ := by
    rw [hval]
  have h4 : mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) Subtype.val x
        (fundamentalVectorField (I := 𝓘(ℝ, kernelTorusLieAlgebra i u)) (G := kernelTorus i u)
          𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ξ x) =
      mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) Subtype.val x
        (mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          (fun k : kernelTorus i u ↦ k • x) 1 ξ) :=
    congrArg _ (fundamentalVectorField_apply (I := 𝓘(ℝ, kernelTorusLieAlgebra i u))
      (G := kernelTorus i u) (I' := 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ξ x)
  exact mem_kernelTorusOrbitTangent.2
    ⟨_, hi.mfderiv_toAdd_coe_kernelTorus_mem ξ, h2'.symm.trans (h3.symm.trans (h1.trans h4.symm))⟩

/-- **The vertical tangent vectors of the Delzant quotient.** A tangent vector of the level `Z` at
`x` is killed by the differential of the projection onto the Delzant quotient exactly when its
image in `ℂ^ι` lies in the tangent space `𝔫 · x` of the orbit of the kernel torus. -/
theorem ker_mfderiv_delzantQuotientMk_eq_comap (x : delzantLevel i u c) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    (mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) x).ker =
      (kernelTorusOrbitTangent i u x).comap
        (mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x).toLinearMap := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  let _ := (kernelTorusData i u hi).chartedSpace
  have := (kernelTorusData i u hi).lieGroup
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.contMDiffSMul_kernelTorus hi
  ext v
  constructor
  · intro hv
    rw [hΔ.ker_mfderiv_delzantQuotientMk hi x] at hv
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hv
    refine Submodule.mem_comap.2 ?_
    rw [InfinitesimalAction.fundamental_apply]
    exact hΔ.mfderiv_coe_fundamentalVectorField_mem hi x ξ
  · intro hv
    obtain ⟨t, ht, hvt⟩ := mem_kernelTorusOrbitTangent.1 hv
    obtain ⟨w, hw0, hwi⟩ := hΔ.exists_mfderiv_delzantQuotientMk_eq_zero hi x ht
    obtain rfl : w = v := hΔ.injective_mfderiv_coe_delzantLevel hi x (hwi.trans hvt)
    exact hw0

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
  -- The tangent space of the level is the symplectic orthogonal of the orbit directions.
  have hrange (y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
      y ∈ stdSymplecticForm.orthogonal (kernelTorusOrbitTangent i u x) ↔ ∃ w, D w = y :=
    (SetLike.ext_iff.1 (hΔ.range_mfderiv_coe_delzantLevel_eq_orthogonal hi x) y).symm.trans
      (LinearMap.mem_range (f := D.toLinearMap))
  have heval (v w : TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x) :
      (SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth).bilinFormAt x v w =
      stdSymplecticForm (D v) (D w) := by
    rw [SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback,
      SymplecticForm.fromTangentSpace_constSmooth_apply]
    -- Tangent vectors of `ℂ^ι` are read in `ℂ^ι` by the identity `fromTangentSpace`.
    rfl
  ext v
  refine LinearMap.mem_ker.trans (?_ : _ ↔ D v ∈ kernelTorusOrbitTangent i u x)
  constructor
  · intro h
    rw [← SymplecticForm.orthogonal_orthogonal stdSymplecticForm (kernelTorusOrbitTangent i u x)]
    refine SymplecticForm.mem_orthogonal_iff'.2 fun y hy ↦ ?_
    obtain ⟨w, rfl⟩ := (hrange y).1 hy
    exact (heval v w).symm.trans (LinearMap.congr_fun h w)
  · intro h
    refine LinearMap.ext fun w ↦ ?_
    exact (heval v w).trans (SymplecticForm.mem_orthogonal_iff.1 ((hrange _).2 ⟨w, rfl⟩) _ h)

/-- **The restricted form is invariant under the kernel torus.** Each element of the kernel torus
acts on `ℂ^ι` by a rotation, which preserves the standard symplectic form `ω`, so it preserves the
restriction `i^* ω` of `ω` to the level. -/
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
        (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := (kernelTorusData i u hi).chartedSpace
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.contMDiffSMul_kernelTorus hi
  set R := torusRotation (k : Multiplicative (ι → AddCircle (2 * π))).toAdd
  have hRs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞ R := R.contMDiff
  have hR : SmoothForm.mpullback R hRs stdSymplecticForm.constSmooth =
      stdSymplecticForm.constSmooth := by
    refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
    rw [SmoothForm.eval₂_mpullback, SymplecticForm.eval₂_constSmooth_mfderiv_eq,
      SymplecticForm.fromTangentSpace_constSmooth_apply, mvfderiv_eq_fderiv, R.fderiv]
    exact stdSymplecticForm_torusRotation _ v w
  calc _ = SmoothForm.mpullback
        (((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∘
          fun z : delzantLevel i u c ↦ k • z)
        ((hΔ.contMDiff_coe_delzantLevel hi).comp
          (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, kernelTorusLieAlgebra i u)) k))
        stdSymplecticForm.constSmooth :=
        SmoothForm.mpullback_mpullback _ _ _ _ _
    _ = SmoothForm.mpullback
        (R ∘ ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
        (hRs.comp (hΔ.contMDiff_coe_delzantLevel hi)) stdSymplecticForm.constSmooth :=
        Subtype.ext (by
          simp only [SmoothForm.coe_mpullback, Function.comp_def, coe_kernelTorus_smul, R])
    _ = SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (hΔ.contMDiff_coe_delzantLevel hi)
        (SmoothForm.mpullback R hRs stdSymplecticForm.constSmooth) :=
        (SmoothForm.mpullback_mpullback _ _ _ hRs _).symm
    _ = _ := by rw [hR]

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

/-- **The Delzant quotient has dimension `2 dim V`.** At a point `x` of the level, the projection
`Z → M_Δ` is a submersion whose vertical tangent vectors are carried by the inclusion
isomorphically onto the orbit directions `𝔫 · x`, of dimension `dim 𝔫 = d - n` since the
infinitesimal action of the kernel torus is free on the level. As `Z` has dimension `d + n`, the
model space of `M_Δ` has dimension `2n`, where `n = dim V`. -/
theorem finrank_delzantQuotientModelSpace (x : delzantLevel i u c) :
    finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) = 2 * finrank ℝ V := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  let D : TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x →L[ℝ]
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x
  set P := mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
    𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
    (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) x
  -- Rank–nullity for the surjective differential of the projection.
  have hrn := LinearMap.finrank_range_add_finrank_ker P.toLinearMap
  rw [LinearMap.range_eq_top.2 ((hΔ.isSubmersion_delzantQuotientMk hi).surjective_mfderiv
    (x := x) (by simp)), finrank_top] at hrn
  -- The inclusion identifies the vertical tangent space with the orbit directions `𝔫 · x`.
  have hD : Function.Injective D := hΔ.injective_mfderiv_coe_delzantLevel hi x
  have hrange : LinearMap.range (D.toLinearMap.domRestrict (LinearMap.ker P.toLinearMap)) =
      kernelTorusOrbitTangent i u x := by
    refine le_antisymm ?_ fun y hy ↦ ?_
    · rintro _ ⟨⟨v, hv⟩, rfl⟩
      exact (SetLike.ext_iff.1 (hΔ.ker_mfderiv_delzantQuotientMk_eq_comap hi x) v).1 hv
    · obtain ⟨t, ht, rfl⟩ := mem_kernelTorusOrbitTangent.1 hy
      obtain ⟨w, hw0, hwi⟩ := hΔ.exists_mfderiv_delzantQuotientMk_eq_zero hi x ht
      exact ⟨⟨w, hw0⟩, hwi⟩
  have hker : finrank ℝ (LinearMap.ker P.toLinearMap) =
      finrank ℝ (kernelTorusOrbitTangent i u x) := by
    rw [← hrange, LinearMap.finrank_range_of_inj fun v w h ↦ Subtype.ext (hD h)]
  have hO := hΔ.finrank_kernelTorusOrbitTangent hi x.property
  have hdim := hΔ.finrank_ker_linearCombination_real_add_finrank hi
  rw [hker, hO] at hrn
  have h1 : finrank ℝ (TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x) =
      Fintype.card ι + finrank ℝ V :=
    (finrank_tangentSpace x).trans (finrank_fin_fun ℝ)
  have h2 : finrank ℝ (TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (DelzantQuotient.mk x)) =
      finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) :=
    finrank_tangentSpace _
  omega

end IsDelzant

end TauCeti.Toric
