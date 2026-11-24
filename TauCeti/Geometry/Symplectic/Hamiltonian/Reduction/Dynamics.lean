/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

/-!
# Hamiltonian dynamics on the Marsden–Weinstein–Meyer reduced space

Let a Lie group `G` act smoothly and properly by symplectomorphisms on a symplectic manifold
`(M, σ)` with coadjoint-equivariant moment map `μ`, let `c` be a regular value of `μ` such that
the coadjoint stabilizer `G_c` acts freely on the level `Z = μ⁻¹(c)`, and let
`π : Z → Z / G_c` be the orbit projection onto the reduced space and `i : Z → M` the inclusion.
The reduced space carries the reduced symplectic form `ω_red`, with `π^* ω_red = i^* σ`
(`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`). This file shows that the
Hamiltonian dynamics of invariant functions passes to the reduced space. All declarations named
here are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* A `C^m` map `f` on `M` whose restriction to `Z` is `G_c`-invariant descends to a unique `C^m`
  map `f'` on `Z / G_c` with `f ∘ i = f' ∘ π`
  (`existsUnique_contMDiff_comp_coe_eq_comp_quotientMk`). Conversely, any map `f'` with
  `f ∘ i = f' ∘ π` is `C^m` when `f` is (`contMDiff_of_comp_coe_eq_comp_quotientMk`), so the
  reduced function of a smooth function needs no separate smoothness hypothesis below.
* For a `G`-invariant differentiable function `f`, every Hamiltonian vector field `X` of `f` is
  tangent to the level (**Noether's theorem**,
  `mem_range_mfderiv_coe_levelSubMulAction_of_smul_invariant`), and for a `C¹` function `f` with
  reduced function `f'`, the projection of any lift of `X` is the Hamiltonian vector field of `f'`
  for `ω_red` (`mfderiv_quotientMk_eq_hamiltonianVectorField`).
* **The bracket of reduced functions is the reduced function of the bracket**: for `C¹`
  functions `f` and `g` with reduced functions `f'` and `g'`, where `g` is `G`-invariant,
  `{f, g} ∘ i = {f', g'} ∘ π` (`poissonBracket_comp_coe_eq_comp_quotientMk`).
* **Hamiltonian flows descend**: an integral curve `γ` of a Hamiltonian vector field of a
  `G`-invariant `C¹` function `f` which meets the level stays in it, since `μ` is conserved, and
  its projection to the reduced space is an integral curve of the Hamiltonian vector field of the
  reduced function `f'` (`exists_isMIntegralCurve_quotientMk_comp`).

The module `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction` states these facts for arbitrary
reduction data `p^* η = i^* σ`, with the differentiability of the functions on `Q` and the
tangency of Hamiltonian vector fields to `Z` as hypotheses. Here they are stated for the actual
reduced manifold of `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace`, where the
reduced functions of smooth functions are smooth and invariance gives the tangency.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130 (reduction of Hamiltonian dynamics).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 24 (reduction for invariant Hamiltonians).
* J. Marsden, T. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer, 1999,
  Section 1.2 (reduction of dynamics and of Poisson brackets).
-/

public section

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] [ProperSMul G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {n : ℕ}
  (h : σ.IsEquivariantMomentMap μ)
  (hreg : ∀ x, μ x = c → Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) E₀)

/-! ### Reduced functions -/

section Descent

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {K : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] {m : ℕ∞ω}

/-- **Reduced functions of smooth functions are smooth.** If `f` is a `C^m` map on `M` with
`m ≤ ∞` and `f ∘ i = f' ∘ π` for the inclusion `i` of the level `μ⁻¹(c)` and the orbit projection
`π` onto the reduced space `μ⁻¹(c) / G_c`, then `f'` is `C^m`. -/
theorem contMDiff_of_comp_coe_eq_comp_quotientMk (hm : m ≤ ∞) {f : M → P}
    (hf : ContMDiff I' K m f)
    {f' : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c) → P}
    (hff' : f ∘ Subtype.val = f' ∘ Quotient.mk
      (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c))) :
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace E₀ (Fin n → ℝ)) K m f' := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  refine ((h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff_comp_iff
    Quotient.mk_surjective hm).1 ?_
  rw [← hff']
  exact hf.comp ((h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff.of_le hm)

/-- **Invariant functions descend to the reduced space.** A `C^m` map `f` on `M`, with `m ≤ ∞`,
whose restriction to the level `μ⁻¹(c)` is invariant under the coadjoint stabilizer `G_c` has a
unique reduced function: a map `f'` on the reduced space `μ⁻¹(c) / G_c` with `f ∘ i = f' ∘ π`, and
`f'` is `C^m`. -/
theorem existsUnique_contMDiff_comp_coe_eq_comp_quotientMk (hm : m ≤ ∞) {f : M → P}
    (hf : ContMDiff I' K m f)
    (hfc : ∀ (k : (Lie.coadjointRepresentation ℝ I G).stabilizer c) (z : h.levelSubMulAction c),
      f ↑(k • z) = f z) :
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    ∃! f' : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) → P,
      ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace E₀ (Fin n → ℝ)) K m f' ∧
        f ∘ Subtype.val = f' ∘ Quotient.mk
          (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
            (h.levelSubMulAction c)) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  obtain ⟨f', ⟨hf', hcomp⟩, huniq⟩ :=
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).existsUnique_contMDiff_comp_eq
      Quotient.mk_surjective hm
      (hf.comp ((h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff.of_le hm))
      (fun z z' hzz' ↦ by
        obtain ⟨k, rfl⟩ :=
          MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hzz'.symm))
        exact (hfc k z).symm)
  exact ⟨f', ⟨hf', hcomp.symm⟩, fun f'' hf'' ↦ huniq f'' ⟨hf''.1, hf''.2.symm⟩⟩

end Descent

/-! ### Hamiltonian vector fields and brackets -/

section Hamiltonian

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- **Noether's theorem on the level.** A Hamiltonian vector field `X` of a `G`-invariant function
`f` differentiable at a point `z` of the level `μ⁻¹(c)` is tangent to the level at `z`: `X z` lies
in the image of the differential of the inclusion. -/
theorem mem_range_mfderiv_coe_levelSubMulAction_of_smul_invariant {f : M → ℝ}
    (hfG : ∀ (g : G) (x : M), f (g • x) = f x) {X : (x : M) → TangentSpace I' x}
    (hX : σ.IsHamiltonianVectorField f X) (z : h.levelSubMulAction c)
    (hf : MDifferentiableAt I' 𝓘(ℝ) f z) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    X z ∈ LinearMap.range
      (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.levelSubMulAction c → M) z).toLinearMap := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  rw [h.range_mfderiv_coe_levelSubMulAction hreg hn]
  refine (h.mem_ker_differential_iff_of_isHamiltonianVectorField hX (z : M)).2 fun ξ ↦ ?_
  rw [InfinitesimalAction.fundamental_apply]
  exact mvfderiv_fundamentalVectorField_eq_zero_of_smul_invariant hf
    ((ContMDiffSMul.contMDiff_smul_const (n := ∞) (z : M)).mdifferentiableAt (by simp))
    (fun g ↦ hfG g z) ξ

/-- **The reduced Hamiltonian vector field.** Let `η` be a nondegenerate two-form on the reduced
space with `π^* η = i^* σ`, such as the reduced symplectic form, let `X` be a Hamiltonian vector
field of a `C¹` function `f`, and let `f'` be its reduced function, `f ∘ i = f' ∘ π`. If a tangent
vector `Y` of the level at `z` is a lift of `X z`, then `dπ Y` is the Hamiltonian vector field of
`f'` at `π z`. For `G`-invariant `f` such a lift exists
(`mem_range_mfderiv_coe_levelSubMulAction_of_smul_invariant`). -/
theorem mfderiv_quotientMk_eq_hamiltonianVectorField {f : M → ℝ} (hf : ContMDiff I' 𝓘(ℝ) 1 f)
    {X : (x : M) → TangentSpace I' x} (hX : σ.IsHamiltonianVectorField f X)
    {f' : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c) → ℝ}
    (hff' : f ∘ Subtype.val = f' ∘ Quotient.mk
      (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c))) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E₀ (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      η.IsNondegenerate →
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
        SmoothForm.mpullback Subtype.val
          (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
      ∀ (z : h.levelSubMulAction c) (Y : TangentSpace 𝓘(ℝ, Fin n → ℝ) z),
        mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.levelSubMulAction c → M) z Y = X z →
        mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E₀ (Fin n → ℝ))
            (Quotient.mk (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
              (h.levelSubMulAction c))) z Y =
          η.hamiltonianVectorField f' (Quotient.mk _ z) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hsub := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  intro η hη hpi z Y hY
  exact hη.mfderiv_eq_hamiltonianVectorField_of_mpullback_eq _ _ hpi hX hff'
    ((hf z).mdifferentiableAt one_ne_zero)
    ((h.contMDiff_of_comp_coe_eq_comp_quotientMk hreg hn d (by simp) hf hff' _).mdifferentiableAt
      one_ne_zero)
    (hsub.surjective_mfderiv (by simp) z) hY

/-- **The bracket of reduced functions is the reduced function of the bracket.** Let `η` be a
nondegenerate two-form on the reduced space with `π^* η = i^* σ`, such as the reduced symplectic
form, and let `f'` and `g'` be the reduced functions of `C¹` functions `f` and `g`,
`f ∘ i = f' ∘ π` and `g ∘ i = g' ∘ π`. If `g` is `G`-invariant, then
`{f, g} ∘ i = {f', g'} ∘ π`: the Poisson bracket `{f', g'}` is the reduced function of `{f, g}`. -/
theorem poissonBracket_comp_coe_eq_comp_quotientMk (hσ : σ.IsNondegenerate) {f g : M → ℝ}
    (hf : ContMDiff I' 𝓘(ℝ) 1 f) (hg : ContMDiff I' 𝓘(ℝ) 1 g)
    (hgG : ∀ (a : G) (x : M), g (a • x) = g x)
    {f' g' : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c) → ℝ}
    (hff' : f ∘ Subtype.val = f' ∘ Quotient.mk
      (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c)))
    (hgg' : g ∘ Subtype.val = g' ∘ Quotient.mk
      (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c))) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E₀ (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      η.IsNondegenerate →
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
        SmoothForm.mpullback Subtype.val
          (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
      σ.poissonBracket f g ∘ Subtype.val =
        η.poissonBracket f' g' ∘ Quotient.mk
          (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
            (h.levelSubMulAction c)) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hsub := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  intro η hη hpi
  funext z
  -- The Hamiltonian vector field of `g` is tangent to the level, by Noether's theorem.
  have htan := h.mem_range_mfderiv_coe_levelSubMulAction_of_smul_invariant hreg hn hgG
    (hσ.isHamiltonianVectorField_hamiltonianVectorField g) z
    ((hg z).mdifferentiableAt one_ne_zero)
  exact (hη.poissonBracket_eq_of_mpullback_eq _ _ hpi hσ hff' hgg'
    ((hf z).mdifferentiableAt one_ne_zero)
    ((h.contMDiff_of_comp_coe_eq_comp_quotientMk hreg hn d (by simp) hf hff' _).mdifferentiableAt
      one_ne_zero)
    ((hg z).mdifferentiableAt one_ne_zero)
    ((h.contMDiff_of_comp_coe_eq_comp_quotientMk hreg hn d (by simp) hg hgg' _).mdifferentiableAt
      one_ne_zero)
    (hsub.surjective_mfderiv (by simp) z) htan).symm

end Hamiltonian

/-! ### Hamiltonian flows -/

/-- **Hamiltonian flows descend to the reduced space.** Let `η` be a nondegenerate two-form on the
reduced space with `π^* η = i^* σ`, such as the reduced symplectic form, let `X` be a Hamiltonian
vector field of a `G`-invariant `C¹` function `f`, and let `f'` be the reduced function of `f`,
`f ∘ i = f' ∘ π`. An integral curve `γ` of `X` which meets the level `μ⁻¹(c)` stays in it, since
`μ` is conserved, so it is a curve `γ'` in the level, and `π ∘ γ'` is an integral curve of the
Hamiltonian vector field of `f'`. -/
theorem exists_isMIntegralCurve_quotientMk_comp {f : M → ℝ} (hf : ContMDiff I' 𝓘(ℝ) 1 f)
    (hfG : ∀ (g : G) (x : M), f (g • x) = f x) {X : (x : M) → TangentSpace I' x}
    (hX : σ.IsHamiltonianVectorField f X)
    {f' : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c) → ℝ}
    (hff' : f ∘ Subtype.val = f' ∘ Quotient.mk
      (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c)))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) {t₀ : ℝ} (hγt₀ : μ (γ t₀) = c) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E₀ (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      η.IsNondegenerate →
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
        SmoothForm.mpullback Subtype.val
          (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
      ∃ γ' : ℝ → h.levelSubMulAction c, Subtype.val ∘ γ' = γ ∧
        IsMIntegralCurve (Quotient.mk
          (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
            (h.levelSubMulAction c)) ∘ γ') (η.hamiltonianVectorField f') := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hemb := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  have hsub := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  intro η hη hpi
  -- By Noether's theorem `μ` is constant along `γ`, so `γ` stays in the level.
  have hμ (t : ℝ) : μ (γ t) = c :=
    (h.toIsMomentMap.apply_eq_of_isMIntegralCurveOn_of_smul_invariant hfG hX isPreconnected_univ
      (hγ.isMIntegralCurveOn _) (fun u _ ↦ (hf (γ u)).mdifferentiableAt one_ne_zero)
      (Set.mem_univ t₀) (Set.mem_univ t)).trans hγt₀
  let γ' : ℝ → h.levelSubMulAction c := fun t ↦ ⟨γ t, h.mem_levelSubMulAction.2 (hμ t)⟩
  have hγ'cont : Continuous γ' := hγ.continuous.subtype_mk _
  -- The curve `γ'` in the level is differentiable, since the inclusion is an immersion.
  have hγ'diff (t : ℝ) : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Fin n → ℝ) γ' t :=
    ((hemb.isImmersion.isDiffImmersionAt (by simp) (γ' t)).mdifferentiableAt_iff_comp).2
      ⟨hγ'cont.continuousAt, (hγ t).mdifferentiableAt⟩
  refine ⟨γ', rfl, ?_⟩
  exact hη.isMIntegralCurve_comp_of_mpullback_eq _ _ hpi hX hff' hγ'diff hγ
    (fun t ↦ hsub.surjective_mfderiv (by simp) (γ' t))
    (fun t ↦ (hf (γ t)).mdifferentiableAt one_ne_zero)
    (fun t ↦ (h.contMDiff_of_comp_coe_eq_comp_quotientMk hreg hn d (by simp) hf hff'
      _).mdifferentiableAt one_ne_zero)

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
