/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure

/-!
# The `L²` estimate of the linearized Floer operator on compact parts of the domain

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J(z, y)` a family of almost complex
structures on `V` depending on the domain point `z = (s, t)` and the target point `y`, and
`Ks ds + Kt dt` a Hamiltonian perturbation. The linearized Floer operator along a map `u`
(`TauCeti.SymplecticForm.floerLinearization`) is

`D_u ξ = ∂s ξ - dX_Ks(u) ξ + (dJ(u) ξ)(∂t u - X_Kt(u)) + J(u)(∂t ξ - dX_Kt(u) ξ)`,

that is, `∂s ξ + J(z, u z) ∂t ξ` plus a zeroth-order term in `ξ` with coefficients continuous in
`z`. When `J(z, u z)` is `ω`-compatible, the `L²` estimate for Cauchy--Riemann operators with
domain-dependent compatible structures applies
(`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure`): on a compact set `K` of the
domain there is a constant `C`, depending only on the data, the map `u` and `K`, such that

`∫_K (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫_K (‖D_u ξ‖² + ‖ξ‖²)`

for every `C²` section `ξ` with support in `K`
(`exists_forall_setIntegral_norm_fderiv_sq_le_floerLinearization_of_tsupport_subset`),
and on a finite cylinder `[a, b] × [0, 1]` for every `C²` section of period one in `t` vanishing on
the slices `s = a` and `s = b`
(`exists_forall_setIntegral_norm_fderiv_sq_le_floerLinearization_of_periodic`).

No nondegeneracy, no Floer equation for `u` and no smallness of the data is assumed: the regularity
needed is only at the points of `K`. The estimate controls the derivative of `ξ` and not `ξ`
itself. On the cylindrical ends of a Floer domain the operator converges to a translation
invariant one, and at a nondegenerate orbit the stationary cylinder estimate
(`TauCeti.Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`) controls
`ξ` as well. The estimate here is the one on the compact part of the domain in the semi-Fredholm
estimate of the linearized operator, which bounds the `W^{1,2}` norm of a section by the `L²` norms
of `D_u ξ` and of `ξ` on a compact set; patching it with estimates on the ends is not done here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.1
  and Appendix B.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

namespace TauCeti.SymplecticForm

open ContinuousLinearMap Function Set MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The zeroth-order part `ξ ↦ (dJ(u) ξ)(∂t u - X_Kt(u)) - dX_Ks(u) ξ - J(u) dX_Kt(u) ξ` of the
linearized Floer operator at the domain point `z`. -/
private noncomputable def floerLinearizationCoeff (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    V →L[ℝ] V :=
  (fderiv ℝ (J z) (u z)).flip
      (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) -
    fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) -
    (J z (u z)).comp (fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z))

/-- The linearized Floer operator is `∂s ξ + J(z, u z) ∂t ξ` plus its zeroth-order part. -/
private theorem floerLinearization_eq_add (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization J Ks Kt u ξ z =
      fderiv ℝ ξ z stdComplexLineReal + J z (u z) (fderiv ℝ ξ z stdComplexLineImag) +
        floerLinearizationCoeff ω J Ks Kt u z (ξ z) := by
  simp only [floerLinearization_def, floerLinearizationCoeff, sub_apply, flip_apply, map_sub]
  abel

/-- The zeroth-order part of the linearized Floer operator is continuous on `K` when the data are
`C¹` (and the Hamiltonians `C²`) at the points `(z, u z)` with `z ∈ K`, and `u` is `C¹` on `K`. -/
private theorem continuousOn_floerLinearizationCoeff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {K : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) :
    ContinuousOn (floerLinearizationCoeff ω J Ks Kt u) K := by
  intro z hz
  have hu₀ : ContDiffAt ℝ 0 u z := (hu z hz).of_le (by norm_num)
  have hgraph : ContinuousAt (fun z ↦ (z, u z)) z := continuousAt_id.prodMk hu₀.continuousAt
  have hXs := ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) (hKs z hz)
  have hXt := ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) (hKt z hz)
  have hdJ : ContinuousAt (fun z ↦ fderiv ℝ (J z) (u z)) z :=
    ((hJ z hz).fderiv (f := fun z y ↦ J z y) hu₀ le_rfl).continuousAt
  have hdXs : ContinuousAt (fun z ↦ fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z)) z :=
    (hXs.fderiv (f := fun z y ↦ ω.hamiltonianVectorField (Ks z) y) hu₀ le_rfl).continuousAt
  have hdXt : ContinuousAt (fun z ↦ fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z)) z :=
    (hXt.fderiv (f := fun z y ↦ ω.hamiltonianVectorField (Kt z) y) hu₀ le_rfl).continuousAt
  have hut : ContinuousAt (fun z ↦ fderiv ℝ u z stdComplexLineImag) z :=
    ((hu z hz).fderiv_right (m := 0) le_rfl).continuousAt.clm_apply continuousAt_const
  have hXtu : ContinuousAt (fun z ↦ ω.hamiltonianVectorField (Kt z) (u z)) z :=
    hXt.continuousAt.comp (f := fun z ↦ (z, u z)) hgraph
  have hJu : ContinuousAt (fun z ↦ J z (u z)) z :=
    (hJ z hz).continuousAt.comp (f := fun z ↦ (z, u z)) hgraph
  have hflip : ContinuousAt (fun z ↦ (fderiv ℝ (J z) (u z)).flip) z :=
    (flipₗᵢ ℝ V V V).continuous.continuousAt.comp hdJ
  exact (((hflip.clm_apply (hut.sub hXtu)).sub hdXs).sub (hJu.clm_comp hdXt)).continuousWithinAt

/-- **The `L²` estimate of the linearized Floer operator on compactly supported sections.** Let
`K ⊆ ℝ × ℝ` be compact, and suppose that at every `z ∈ K` the structure `J(z, u z)` is
`ω`-compatible, `J` is `C¹` and the Hamiltonians `Ks`, `Kt` are `C²` at `(z, u z)`, and `u` is
`C¹` at `z`. Then there is a constant `C ≥ 0` such that every `C²` section `ξ` with support in
`K` satisfies `∫_K (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫_K (‖D_u ξ‖² + ‖ξ‖²)` for the linearized Floer
operator `D_u`. -/
theorem exists_forall_setIntegral_norm_fderiv_sq_le_floerLinearization_of_tsupport_subset
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) (hc : ∀ z ∈ K, ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → tsupport ξ ⊆ K →
      ∫ z in K, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C * ∫ z in K, (‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 +
          ‖ξ z‖ ^ 2) := by
  have hJc : ContinuousOn (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) K :=
    fun z hz ↦ ((hJ z hz).continuousAt.comp (f := fun z ↦ (z, u z))
      (continuousAt_id.prodMk (hu z hz).continuousAt)).continuousWithinAt
  obtain ⟨C, hC, h⟩ := exists_forall_setIntegral_norm_fderiv_sq_le_of_tsupport_subset hK hc hJc
    (continuousOn_floerLinearizationCoeff ω
      (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu)
  refine ⟨C, hC, fun ξ hξ hξK ↦ (h hξ hξK).trans_eq ?_⟩
  simp only [floerLinearization_eq_add, LinearMap.coe_toContinuousLinearMap']

/-- **The `L²` estimate of the linearized Floer operator on a finite cylinder.** Under the
hypotheses of
`exists_forall_setIntegral_norm_fderiv_sq_le_floerLinearization_of_tsupport_subset` on the
rectangle `[a, b] × [0, 1]`, there is a constant `C ≥ 0` such that every `C²` section `ξ` of period
one in `t` that vanishes on the slices `s = a` and `s = b` satisfies
`∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫ (‖D_u ξ‖² + ‖ξ‖²)` over the rectangle. -/
theorem exists_forall_setIntegral_norm_fderiv_sq_le_floerLinearization_of_periodic
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {a b : ℝ} (hab : a ≤ b)
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
      ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C * ∫ z in Icc a b ×ˢ Icc 0 1, (‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 +
          ‖ξ z‖ ^ 2) := by
  have hJc : ContinuousOn (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap)
      (Icc a b ×ˢ Icc 0 1) :=
    fun z hz ↦ ((hJ z hz).continuousAt.comp (f := fun z ↦ (z, u z))
      (continuousAt_id.prodMk (hu z hz).continuousAt)).continuousWithinAt
  obtain ⟨C, hC, h⟩ := exists_forall_setIntegral_norm_fderiv_sq_le_of_periodic hab hc hJc
    (continuousOn_floerLinearizationCoeff ω
      (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu)
  refine ⟨C, hC, fun ξ hξ hper ha hb ↦ (h hξ hper ha hb).trans_eq ?_⟩
  simp only [floerLinearization_eq_add, LinearMap.coe_toContinuousLinearMap']

end TauCeti.SymplecticForm
