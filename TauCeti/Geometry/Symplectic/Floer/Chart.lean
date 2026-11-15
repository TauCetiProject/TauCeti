/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# The Floer equation in a symplectic chart

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `φ : M → V` be a map into a vector space with a constant symplectic
form `ω₀` which pulls `ω₀` back to `ω` at a point `x`:

`ω_x(v, w) = ω₀(dφ_x v, dφ_x w)`.

A Darboux chart (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`) has this property at
every point of its source. This file shows that, at such a point, every ingredient of the
inhomogeneous Floer equation `(du - X_K)^{0,1} = 0` on the manifold is carried by `dφ_x` to the
corresponding ingredient of the Floer equation on `(V, ω₀)` for the coordinate expressions
`K'(z, y)` of the Hamiltonians, with `K(z, ·) = K'(z, ·) ∘ φ` near `x`. So solutions of the
Floer equation in `M` whose image stays in the chart are, read in the chart, solutions of the
Floer equation of a symplectic vector space, with the same energy density. This is how the
analysis of `TauCeti.Geometry.Symplectic.Floer`, carried out for a symplectic vector space target,
applies to a manifold target.

The pointwise symplectic linear algebra of such a map is in
`TauCeti.Geometry.Symplectic.Manifold.TwoForm` and
`TauCeti.Geometry.Symplectic.Hamiltonian.Manifold`: `dφ_x` is injective
(`TauCeti.SmoothTwoForm.IsNondegenerate.injective_mvfderiv`), and if it is also surjective it
carries the Hamiltonian vector field of `g ∘ φ` at `x` to the Hamiltonian vector field of `g` for
`ω₀` at `φ x` (`TauCeti.SmoothTwoForm.IsNondegenerate.mvfderiv_hamiltonianVectorField_comp`) and a
structure `J` tamed by `ω_x` to a structure tamed by `ω₀`
(`TauCeti.SmoothTwoForm.IsNondegenerate.tames_of_isComplexLinearMap_mvfderiv`). This file applies
them to the Floer equation.

* For `u : ℝ × ℝ → M` with `u z = x`, the perturbed derivative `d(φ ∘ u) - X_{K'}` of the coordinate
  map is `dφ_x ∘ (du - X_K)` (`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`), and
  the Floer energy densities agree
  (`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp`).
* If `dφ_x ∘ J = J' ∘ dφ_x`, that is, `J'` is the structure `J` read in the chart, then `φ ∘ u`
  solves the coordinate Floer equation for `J'` at `z` exactly when `u` solves the Floer equation
  for `J` (`TauCeti.SmoothTwoForm.IsNondegenerate.isComplexLinearMap_perturbedFDeriv_comp_iff`).

All statements are pointwise and need differentiability only at the point; the chart is any map
with the pullback property there, not necessarily a chart of the manifold structure.

For a partial diffeomorphism `φ` into `V`, such as a Darboux chart, the coordinate Hamiltonians
are `K'(z, y) = K(z, φ⁻¹ y)`, and the transfer only needs `K'` to be differentiable at
`(z, φ (u z))`
(`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp_of_mem_source`,
`TauCeti.SmoothTwoForm.IsNondegenerate.isComplexLinearMap_perturbedFDeriv_comp_iff_of_mem_source`).
Consequently, for `φ` pulling `ω₀` back to `ω` on a set `C` of its source and `C¹` coordinate
Hamiltonians, the energy density of a `C¹` map is continuous where the map lies in the interior of
`C` (`TauCeti.SmoothTwoForm.IsNondegenerate.continuousAt_floerEnergyDensity`), and for compact `C`
and a continuous family of tamed structures it bounds the derivative of the coordinate map,
`‖d(φ ∘ u)‖² ≤ L (e + 1)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_comp_sq_le`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 8.1
  (the inhomogeneous Cauchy–Riemann equation and its energy).
-/

public section

open Function
open scoped Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {φ : M → V}
  {Ks Kt : ℝ × ℝ → M → ℝ} {Ks' Kt' : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → M} {z : ℝ × ℝ}

/-- **The perturbed derivative in a symplectic chart.** Let `φ` be differentiable at `u z` with
surjective differential there, pulling the symplectic form `ω₀` back to the nondegenerate form `ω`
at `u z`, and let the Hamiltonians `Ks z`, `Kt z` agree near `u z` with `Ks' z ∘ φ`, `Kt' z ∘ φ`
for functions `Ks' z`, `Kt' z` differentiable at `φ (u z)`. If `u` is differentiable at `z`, the
perturbed derivative `d(φ ∘ u) - X_{K'}` of the coordinate map for `ω₀` is the differential of `φ`
applied to the perturbed derivative `du - X_K` of `u` for `ω`. -/
theorem perturbedFDeriv_comp (hω : ω.IsNondegenerate) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z)) (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z))) :
    ω₀.perturbedFDeriv Ks' Kt' (φ ∘ u) z =
      (mvfderiv I φ (u z)).comp (ω.perturbedMFDeriv Ks Kt u z) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hd : fderiv ℝ (φ ∘ u) z v = mvfderiv I φ (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z v) :=
    (mvfderiv_eq_fderiv_apply (φ ∘ u) z v).symm.trans (mvfderiv_comp_apply z hφ hu v)
  rw [SymplecticForm.perturbedFDeriv_apply, ContinuousLinearMap.comp_apply, perturbedMFDeriv_apply,
    map_sub, map_sub, map_smul, map_smul, hd, comp_apply, hKs.hamiltonianVectorField_eq,
    hKt.hamiltonianVectorField_eq, hω.mvfderiv_hamiltonianVectorField_comp hφ hsurj hform hKs',
    hω.mvfderiv_hamiltonianVectorField_comp hφ hsurj hform hKt', mvfderiv_apply_eq_mfderiv_apply]

/-- **The energy density in a symplectic chart.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`, the Floer energy density of the
coordinate map `φ ∘ u` for `ω₀` and the coordinate Hamiltonians is the Floer energy density of `u`
for `ω`. -/
theorem floerEnergyDensity_comp (hω : ω.IsNondegenerate)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z))
    (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z))) :
    ω₀.floerEnergyDensity Ks' Kt' (φ ∘ u) z = ω.floerEnergyDensity Ks Kt u z := by
  rw [SymplecticForm.floerEnergyDensity_def, floerEnergyDensity_def,
    hω.perturbedFDeriv_comp hu hφ hsurj hform hKs hKt hKs' hKt', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hform]

/-- **The Floer equation in a symplectic chart.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`, let `J'` be the structure `J` on
`T_(u z) M` read in the chart, `dφ ∘ J = J' ∘ dφ`. Then the coordinate map `φ ∘ u` solves the
Floer equation for `ω₀` and `J'` at `z` exactly when `u` solves the Floer equation for `ω` and
`J`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_iff (hω : ω.IsNondegenerate)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z))
    (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z)))
    {J : AlmostComplexStructure (TangentSpace I (u z))} {J' : AlmostComplexStructure V}
    (hJ : IsComplexLinearMap J J' (mvfderiv I φ (u z)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
        (ω₀.perturbedFDeriv Ks' Kt' (φ ∘ u) z).toLinearMap ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap := by
  rw [hω.perturbedFDeriv_comp hu hφ hsurj hform hKs hKt hKs' hKt']
  refine ⟨fun h ↦ ?_, fun h ↦ hJ.comp h⟩
  -- The differential of `φ` is injective and intertwines `J` with `J'`.
  rw [isComplexLinearMap_stdComplexLine_iff] at h ⊢
  refine hω.injective_mvfderiv hform ?_
  have hJv := LinearMap.congr_fun hJ (ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal)
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp] at h hJv ⊢
  exact h.trans hJv.symm

section PartialDiffeomorph

/-! ### Partial diffeomorphisms

For a partial diffeomorphism `φ` into `V` and a point of its source, the hypotheses of the
statements above on `φ` and on the Hamiltonians hold for the coordinate Hamiltonians
`K'(z, y) = K(z, φ⁻¹ y)`, so they only require `K'` to be differentiable. -/

variable {m : WithTop ℕ∞}

omit [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Near a point `x` of the source of `φ`, a function `g` on `M` is its coordinate expression
`g ∘ φ⁻¹` composed with `φ`. -/
private theorem eventuallyEq_comp_symm_comp (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) {x : M}
    (hx : x ∈ φ.source) (g : M → ℝ) : g =ᶠ[𝓝 x] (fun y ↦ g (φ.symm y)) ∘ φ :=
  (φ.toOpenPartialHomeomorph.eventually_left_inverse hx).mono fun _ hy ↦ congrArg g hy.symm

/-- **The energy density through a partial diffeomorphism.** Let `φ` be a partial diffeomorphism
into `V` pulling `ω₀` back to the nondegenerate form `ω` at `u z ∈ φ.source`, and let the
coordinate Hamiltonians `(z, y) ↦ K(z, φ⁻¹ y)` be differentiable at `(z, φ (u z))`. If `u` is
differentiable at `z`, the coordinate map `φ ∘ u` has the energy density of `u` at `z`.
For Hamiltonians whose coordinate expressions are only differentiable in `y`, use
`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp`. -/
theorem floerEnergyDensity_comp_of_mem_source (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hm : m ≠ 0)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hx : u z ∈ φ.source)
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : DifferentiableAt ℝ (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) (z, φ (u z)))
    (hKt : DifferentiableAt ℝ (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) (z, φ (u z))) :
    ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u) z =
      ω.floerEnergyDensity Ks Kt u z :=
  hω.floerEnergyDensity_comp hu (φ.mdifferentiableAt hm hx) (φ.bijective_mvfderiv hm hx).surjective
    hform (eventuallyEq_comp_symm_comp φ hx (Ks z)) (eventuallyEq_comp_symm_comp φ hx (Kt z))
    (hKs.comp _ ((differentiableAt_const z).prodMk differentiableAt_id))
    (hKt.comp _ ((differentiableAt_const z).prodMk differentiableAt_id))

/-- **The Floer equation through a partial diffeomorphism.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp_of_mem_source`, let `J'` be the
structure `J` on `T_(u z) M` read in the chart, `dφ ∘ J = J' ∘ dφ`. Then the coordinate map
`φ ∘ u` solves the Floer equation for `ω₀`, the coordinate Hamiltonians and `J'` at `z` exactly
when `u` solves the Floer equation for `ω` and `J`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_iff_of_mem_source (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hm : m ≠ 0)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hx : u z ∈ φ.source)
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : DifferentiableAt ℝ (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) (z, φ (u z)))
    (hKt : DifferentiableAt ℝ (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) (z, φ (u z)))
    {J : AlmostComplexStructure (TangentSpace I (u z))} {J' : AlmostComplexStructure V}
    (hJ : IsComplexLinearMap J J' (mvfderiv I φ (u z)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
        (ω₀.perturbedFDeriv (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u)
          z).toLinearMap ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap :=
  hω.isComplexLinearMap_perturbedFDeriv_comp_iff hu (φ.mdifferentiableAt hm hx)
    (φ.bijective_mvfderiv hm hx).surjective hform (eventuallyEq_comp_symm_comp φ hx (Ks z))
    (eventuallyEq_comp_symm_comp φ hx (Kt z))
    (hKs.comp _ ((differentiableAt_const z).prodMk differentiableAt_id))
    (hKt.comp _ ((differentiableAt_const z).prodMk differentiableAt_id)) hJ

/-- **Continuity of the energy density through a symplectic chart.** Let `φ` be a partial
diffeomorphism into `V` pulling `ω₀` back to `ω` on `C ⊆ φ.source`, and let the coordinate
Hamiltonians `(z, y) ↦ K(z, φ⁻¹ y)` be `C¹` on an open set `W` containing `D × φ(C)`. The energy
density of a map `u` that is `C¹` on an open set `U ⊆ D` is continuous at every point `z ∈ U` with
`u z` in the interior of `C`: near `z` it is the energy density of the coordinate map `φ ∘ u`. -/
theorem continuousAt_floerEnergyDensity (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hm : m ≠ 0) {W : Set ((ℝ × ℝ) × V)}
    {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w)) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUD : U ⊆ D) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hz : z ∈ U)
    (hzC : u z ∈ interior C) :
    ContinuousAt (ω.floerEnergyDensity Ks Kt u) z := by
  set N := U ∩ u ⁻¹' interior C
  have hN : IsOpen N := hu.continuousOn.isOpen_inter_preimage hU isOpen_interior
  have hNC {y : ℝ × ℝ} (hy : y ∈ N) : u y ∈ C := interior_subset hy.2
  have hNW {y : ℝ × ℝ} (hy : y ∈ N) : (y, φ (u y)) ∈ W := hDCW ⟨hUD hy.1, u y, hNC hy, rfl⟩
  have hcont := ω₀.continuousOn_floerEnergyDensity_of_continuousOn_hamiltonianOneForm
    (Ks := fun z y ↦ Ks z (φ.symm y)) (Kt := fun z y ↦ Kt z (φ.symm y)) hN
    (contMDiffOn_iff_contDiffOn.1 <| (φ.contMDiffOn.of_le
      (ENat.one_le_iff_ne_zero_withTop.2 hm)).comp (hu.mono Set.inter_subset_left)
      fun y hy ↦ hCφ (hNC hy))
    (ω₀.contDiffOn_hamiltonianOneForm_uncurry (n := 0) (Ks := fun z y ↦ Ks z (φ.symm y))
      (Kt := fun z y ↦ Kt z (φ.symm y)) hW (by rw [zero_add]; exact hKs)
      (by rw [zero_add]; exact hKt)).continuousOn
    fun _ hy ↦ hNW hy
  refine (hcont.congr fun y hy ↦ ?_).continuousAt (hN.mem_nhds ⟨hz, hzC⟩)
  exact (hω.floerEnergyDensity_comp_of_mem_source φ hm
    ((hu.contMDiffAt (hU.mem_nhds hy.1)).mdifferentiableAt one_ne_zero) (hCφ (hNC hy))
    (hφ _ (hNC hy)) ((hKs.differentiableOn one_ne_zero _ (hNW hy)).differentiableAt
      (hW.mem_nhds (hNW hy)))
    ((hKt.differentiableOn one_ne_zero _ (hNW hy)).differentiableAt (hW.mem_nhds (hNW hy)))).symm

/-- **The energy density bounds the derivative in a symplectic chart.** Let `φ` be a partial
diffeomorphism into `V` pulling `ω₀` back to `ω` on a compact set `C ⊆ φ.source`, let the
coordinate Hamiltonians `(z, y) ↦ K(z, φ⁻¹ y)` be `C¹` on an open set `W` containing `D × φ(C)`
for a compact `D ⊆ ℝ × ℝ`, and let the family `J'` reading `J` in the chart be continuous on
`D × φ(C)`, with `J` tamed by `ω` over `D × C`. There is a constant `L ≥ 0` such that every
solution `u` of the Floer equation for `J(z, u)` at a point `z ∈ D` where it is differentiable,
with `u z ∈ C`, satisfies `‖d(φ ∘ u)(z)‖² ≤ L (e + 1)` for its energy density
`e = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` at `z`. -/
theorem exists_forall_norm_fderiv_comp_sq_le (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hm : m ≠ 0) {W : Set ((ℝ × ℝ) × V)}
    {D : Set (ℝ × ℝ)} {C : Set M} {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {J' : ℝ × ℝ → V → AlmostComplexStructure V}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hJ' : ContinuousOn
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) (D ×ˢ (φ '' C)))
    (hD : IsCompact D) (hC : IsCompact C) (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ L ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄, z ∈ D → u z ∈ C →
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap →
      ‖fderiv ℝ (φ ∘ u) z‖ ^ 2 ≤ L * (ω.floerEnergyDensity Ks Kt u z + 1) := by
  have hφC : IsCompact (φ '' C) := hC.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hCφ)
  obtain ⟨L, hL0, hL⟩ := ω₀.exists_forall_norm_fderiv_sq_le_and_floerEnergyDensity_le
    (Ks := fun z y ↦ Ks z (φ.symm y)) (Kt := fun z y ↦ Kt z (φ.symm y)) hD hφC hJ'
    ((ω₀.contDiffOn_hamiltonianOneForm_uncurry (n := 0) (Ks := fun z y ↦ Ks z (φ.symm y))
      (Kt := fun z y ↦ Kt z (φ.symm y)) hW (by rw [zero_add]; exact hKs)
      (by rw [zero_add]; exact hKt)).continuousOn.mono hDCW)
    fun z hz ↦ hω.tames_of_mem_image φ hm hφ (hJJ' z hz) hCφ (hJt z hz)
  refine ⟨L, hL0, fun u z hz hu hdu hfl ↦ ?_⟩
  have hzW : (z, φ (u z)) ∈ W := hDCW ⟨hz, u z, hu, rfl⟩
  have hdKs := (hKs.differentiableOn one_ne_zero _ hzW).differentiableAt (hW.mem_nhds hzW)
  have hdKt := (hKt.differentiableOn one_ne_zero _ hzW).differentiableAt (hW.mem_nhds hzW)
  rw [← hω.floerEnergyDensity_comp_of_mem_source φ hm hdu (hCφ hu) (hφ _ hu) hdKs hdKt]
  exact (hL hz ⟨u z, hu, rfl⟩ ((hω.isComplexLinearMap_perturbedFDeriv_comp_iff_of_mem_source φ hm
    hdu (hCφ hu) (hφ _ hu) hdKs hdKt (hJJ' z hz _ hu)).2 hfl)).1

end PartialDiffeomorph

end TauCeti.SmoothTwoForm.IsNondegenerate
