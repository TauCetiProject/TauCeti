/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.IsotropicSection
public import TauCeti.Topology.ConnectedComponents

/-!
# Action–angle coordinates as a chart into the cotangent bundle of a torus

Let `σ` be a symplectic form on a boundaryless Hausdorff manifold `M` of dimension `2 |ι|`, and
let `F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions with complete
Hamiltonian vector fields, with the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g)`. Let
`L` be the connected component of `x` in its level `F⁻¹(F x)`, and suppose that `L` is compact and
consists of regular points of `F`. This file proves the **Liouville–Arnold action–angle
theorem** in the form of a chart into the model phase space `T*Tⁿ`, `Tⁿ = ι → AddCircle p`, with
its canonical symplectic form `ω = -dλ` (`TauCeti.CotangentBundle.symplecticForm`), for every
period `p > 0` (`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`): there are an open
neighbourhood `U` of `L`, an open set `D ⊆ ℝ^ι` and a map `φ : M → T*Tⁿ` which

* is injective on `U` and a smooth local diffeomorphism at every point of `U`;
* maps `U` onto the covectors whose actions `ξ(eᵢ)` lie in `D`;
* pulls `ω = ∑ᵢ dθᵢ ∧ dIᵢ` back to `σ` on `U`;
* makes `F` a smooth function of the actions on `U`.

So `U` is symplectomorphic to `Tⁿ × D ⊆ T*Tⁿ`, and `F` depends on the actions alone. The chart is
assembled from the local angle-map charts: an isotropic section `s` through `x`, smooth periods
`λ⁽ⁱ⁾` and action variables `A` near `F x`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_eval₂_mfderiv_angleMap_eq_of_isCompact`) give the
angle map `Ψ(θ, c) = (∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)) • s(c)`, a local diffeomorphism on `ℝ^ι × V` for a
small open `V ∋ F x` (`TauCeti.SmoothTwoForm.IsSymplectic.isLocalDiffeomorphAt_angleMap`) which
identifies two points exactly when they lie over the same `c` with angles differing by `2πℤ^ι`
(`TauCeti.SmoothTwoForm.IsSymplectic.angleMap_eq_angleMap_iff_of_section`). The model map
`(θ, c) ↦ ([pθ / 2π], ∑ᵢ (2π / p) Aᵢ(c) dθᵢ)` into `T*Tⁿ`, through the cover
`TauCeti.CotangentBundle.torusCover`, makes the same identifications and pulls `ω` back to the same
form `∑ᵢ dθᵢ ∧ dAᵢ` as `Ψ` pulls back `σ`, so it descends along `Ψ` to `φ` on `U = Ψ(ℝ^ι × V)`.
The image `U` contains `L`, since the Hamiltonian flows act transitively on `L`.

The flows are assumed complete on all of `M`. For a proper integrable system this holds
(`IsIntegrableSystem.isCompleteVectorField_hamiltonianVectorField_of_isProperMap`, in the namespace
`TauCeti.SmoothTwoForm`), and the compactness of `L` is automatic, which gives
`TauCeti.SmoothTwoForm.IsIntegrableSystem.exists_actionAngle_of_isProperMap`.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`: action–angle coordinates near a compact
  regular component of a level, as a symplectic chart into `T*Tⁿ` along which `F` is a function of
  the actions.
* `TauCeti.SmoothTwoForm.IsIntegrableSystem.exists_actionAngle_of_isProperMap`: the same for a
  proper integrable system.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the Liouville–Arnold theorem and action–angle
  variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (action–angle coordinates from a Lagrangian section).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

noncomputable section

open Set Filter Function Module Real Bundle
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

/-! ### The model chart of `T*Tⁿ` in angles of period `2π` -/

section Model

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The point of `T*Tⁿ`, `Tⁿ = ι → AddCircle p`, with angles `θ` of period `2π` and with
`(2π / p) A c` as actions. -/
private def actionAngleChart (A : (ι → ℝ) → ι → ℝ) (q : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  CotangentBundle.torusCover p ((p / (2 * π)) • q.1,
    (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm ((p / (2 * π))⁻¹ • A q.2))

/-- The actions of the model chart at `(θ, c)` are `(2π / p) A c`. -/
private theorem actions_actionAngleChart (A : (ι → ℝ) → ι → ℝ) (q : (ι → ℝ) × (ι → ℝ)) :
    (fun i ↦ (actionAngleChart p A q).2 (Pi.single i 1)) = (p / (2 * π))⁻¹ • A q.2 := by
  rw [actionAngleChart, CotangentBundle.torusCover_snd]
  -- The fibres of `T*Tⁿ` are type synonyms of `(ι → ℝ) →L[ℝ] ℝ`, so the actions are read by
  -- `ContinuousLinearEquiv.piRing`.
  exact funext fun i ↦ (ContinuousLinearEquiv.piRing_apply _ i).symm.trans
    (congrFun ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).apply_symm_apply _) i)

/-- The model chart identifies two points exactly when their angles differ by `2πℤ^ι` and `A` takes
the same value at their second coordinates. -/
private theorem actionAngleChart_eq_iff {A : (ι → ℝ) → ι → ℝ} {q q' : (ι → ℝ) × (ι → ℝ)} :
    actionAngleChart p A q = actionAngleChart p A q' ↔
      (∃ m : ι → ℤ, q'.1 = q.1 + fun i ↦ 2 * π * m i) ∧ A q'.2 = A q.2 := by
  have hκ : p / (2 * π) ≠ 0 := (div_pos (Fact.out : 0 < p) two_pi_pos).ne'
  rw [actionAngleChart, actionAngleChart, CotangentBundle.torusCover_eq_torusCover_iff,
    (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm.injective.eq_iff,
    smul_right_injective _ (inv_ne_zero hκ) |>.eq_iff]
  refine and_congr_left' (exists_congr fun m ↦ ?_)
  -- `p / 2π` times `2π m` is `p m`.
  have hm : (p / (2 * π)) • (fun i ↦ 2 * π * (m i : ℝ)) = fun i ↦ m i • p := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
    field_simp
  rw [← hm, ← smul_add, (smul_right_injective _ hκ).eq_iff]

/-- The model chart is smooth on `ℝ^ι × V` when `A` is smooth on `V`. -/
private theorem contMDiffOn_actionAngleChart {A : (ι → ℝ) → ι → ℝ} {V : Set (ι → ℝ)}
    (hA : ContDiffOn ℝ ∞ A V) :
    ContMDiffOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (actionAngleChart p A) (univ ×ˢ V) := by
  have hG : ContDiffOn ℝ ∞ (fun q : (ι → ℝ) × (ι → ℝ) ↦ ((p / (2 * π)) • q.1,
      (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm ((p / (2 * π))⁻¹ • A q.2)))
      (univ ×ˢ V) :=
    (contDiff_fst.const_smul _).contDiffOn.prodMk
      ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm.contDiff.comp_contDiffOn
        ((hA.comp contDiffOn_snd fun q hq ↦ (mem_prod.1 hq).2).const_smul _))
  exact (CotangentBundle.contMDiff_torusCover p).comp_contMDiffOn hG.contMDiffOn

/-- The model chart pulls `ω` back to `∑ᵢ dθᵢ ∧ dAᵢ`: on `(a, b)` and `(a', b')` it is
`∑ᵢ (aᵢ A'(b')ᵢ - a'ᵢ A'(b)ᵢ)`, where `A'` is the derivative of `A`. -/
private theorem eval₂_mfderiv_actionAngleChart {A : (ι → ℝ) → ι → ℝ}
    {A' : (ι → ℝ) →L[ℝ] ι → ℝ} {q : (ι → ℝ) × (ι → ℝ)} (hA : HasFDerivAt A A' q.2)
    (a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (actionAngleChart p A q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (actionAngleChart p A) q (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (actionAngleChart p A) q (a', b')) =
      ∑ i, (a i * A' b' i - a' i * A' b i) := by
  set e := (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm
  set κ := p / (2 * π)
  have hκ : κ ≠ 0 := (div_pos (Fact.out : 0 < p) two_pi_pos).ne'
  -- The map `(θ, c) ↦ (κ θ, e (κ⁻¹ A c))` in front of the cover, and its derivative.
  set G' : (ι → ℝ) × (ι → ℝ) →L[ℝ] (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) :=
    (κ • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
      ((e : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) ∘L
        (κ⁻¹ • (A' ∘L ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))))
  have hG : HasFDerivAt (fun q : (ι → ℝ) × (ι → ℝ) ↦ (κ • q.1, e (κ⁻¹ • A q.2))) G' q :=
    (hasFDerivAt_fst.const_smul κ).prodMk
      (e.hasFDerivAt.comp q ((hA.comp q hasFDerivAt_snd).const_smul κ⁻¹))
  have hχ := ((CotangentBundle.contMDiff_torusCover p (ι := ι) _).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp q hG.hasMFDerivAt
  have hdef : actionAngleChart p A =
      CotangentBundle.torusCover p ∘ fun q ↦ (κ • q.1, e (κ⁻¹ • A q.2)) := (rfl)
  rw [hdef, hχ.mfderiv]
  refine (CotangentBundle.eval₂_symplecticForm_mfderiv_torusCover p _ (G' (a, b))
    (G' (a', b'))).trans ?_
  rw [strongDualCotangentSymplecticForm_apply]
  simp only [G', ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearEquiv.coe_coe, e, ContinuousLinearEquiv.piRing_symm_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- The image of `ℝ^ι × V` under the model chart consists of the covectors whose actions lie in
`(2π / p) A(V)`. -/
private theorem image_actionAngleChart (A : (ι → ℝ) → ι → ℝ) (V : Set (ι → ℝ)) :
    actionAngleChart p A '' (univ ×ˢ V) =
      {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ (fun a ↦ (p / (2 * π))⁻¹ • a) '' (A '' V)} := by
  have hκ : p / (2 * π) ≠ 0 := (div_pos (Fact.out : 0 < p) two_pi_pos).ne'
  ext ξ
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_ofPred_eq, actions_actionAngleChart]
    exact ⟨A q.2, ⟨q.2, hq.2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hcV, rfl⟩, hcξ⟩
    obtain ⟨q₀, rfl⟩ := CotangentBundle.torusCover_surjective p ξ
    refine ⟨((p / (2 * π))⁻¹ • q₀.1, c), ⟨mem_univ _, hcV⟩, ?_⟩
    rw [actionAngleChart, smul_inv_smul₀ hκ]
    -- The actions of `q₀` are `(2π / p) A c`, and a covector is determined by its actions.
    have hq₀ : (p / (2 * π))⁻¹ • A c = ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι q₀.2 :=
      hcξ.trans ((congrArg (fun ℓ : (ι → ℝ) →L[ℝ] ℝ ↦ fun i ↦ ℓ (Pi.single i 1))
        (CotangentBundle.torusCover_snd p q₀)).trans
          (funext fun i ↦ (ContinuousLinearEquiv.piRing_apply q₀.2 i).symm))
    rw [hq₀, ContinuousLinearEquiv.symm_apply_apply]

end Model

/-! ### Action–angle coordinates into `T*Tⁿ` -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] [DecidableEq ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))

include hσ hF hcomm hc

omit [DecidableEq ι] in
/-- The angle map over a neighbourhood `V` of `F x` reaches the whole connected component of `x`
in its level, when the periods at `F x` are linearly independent and the section passes through
`x`. -/
private theorem connectedComponentIn_subset_image_angleMap
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    {s : (ι → ℝ) → M} {l : ι → (ι → ℝ) → ι → ℝ} {V : Set (ι → ℝ)} (hsx : s (F x) = x)
    (hxV : F x ∈ V) (hli : LinearIndependent ℝ fun i ↦ l i (F x)) :
    connectedComponentIn (F ⁻¹' {F x}) x ⊆ hσ.angleMap hF hcomm hc s l '' (univ ×ˢ V) := by
  intro y hy
  rw [← hσ.range_hamiltonianFlowAction_apply hF hcomm hc hdim hreg] at hy
  obtain ⟨v, rfl⟩ := hy
  -- The periods `l i (F x)` form a basis, in which `v` has coordinates `a`.
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
    ((hli.span_eq_top_of_card_eq_finrank' (by simp)) ▸ Submodule.mem_top (x := v))
  refine ⟨(fun i ↦ 2 * π * a i, F x), ⟨mem_univ _, hxV⟩, ?_⟩
  rw [hσ.angleMap_apply hF hcomm hc, hsx, ← ha]
  congr 3
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_assoc, inv_mul_cancel₀ two_pi_pos.ne', one_mul]

/-- **The Liouville–Arnold theorem: action–angle coordinates.** On a boundaryless Hausdorff
manifold of dimension `2 |ι|` with symplectic form `σ`, let `F : M → ℝ^ι` be smooth, with pairwise
Poisson-commuting components whose Hamiltonian vector fields are complete, and let the connected
component `L` of `x` in its level `F⁻¹(F x)` be compact and consist of regular points of `F`. Let
`p > 0` and let `Tⁿ = ι → AddCircle p`. Then there are an open neighbourhood `U` of `L`, an open set
`D ⊆ ℝ^ι` and a map `φ : M → T*Tⁿ` which is injective on `U` and a smooth local diffeomorphism at
every point of `U`, maps `U` onto the covectors whose actions `ξ(eᵢ)` lie in `D`, pulls the
canonical symplectic form `ω = ∑ᵢ dθᵢ ∧ dIᵢ` of `T*Tⁿ` back to `σ` on `U`, and along which `F` is
a smooth function `h` of the actions on `U`. -/
theorem exists_actionAngle (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) (p : ℝ) [Fact (0 < p)] :
    ∃ U : Set M, IsOpen U ∧ connectedComponentIn (F ⁻¹' {F x}) x ⊆ U ∧
      ∃ D : Set (ι → ℝ), IsOpen D ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        (∀ y ∈ U, ∀ v w : TangentSpace I y,
          SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm
              (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (φ y)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
              𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
              𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y w) =
          SmoothBundleForm.eval₂ σ y v w) ∧
        ∃ h : (ι → ℝ) → ι → ℝ, ContDiffOn ℝ ∞ h D ∧
          ∀ y ∈ U, F y = h fun i ↦ (φ y).2 (Pi.single i 1) := by
  /- The proof has four steps: choose the local data of the angle map over a small open `V ∋ F x`;
  descend the model chart `χ` along the angle map `Ψ` to `φ` on `U = Ψ(ℝ^ι × V)`; compare the
  pulled-back forms; and read off `F` from the actions through a local inverse `g` of `A`. -/
  have hκ : p / (2 * π) ≠ 0 := (div_pos (Fact.out : 0 < p) two_pi_pos).ne'
  -- Step 1: an isotropic section `s` through `x`, periods `l` and action variables `A` near
  -- `F x`, with a local inverse `g` of `A`, all valid on an open `V ∋ F x`.
  obtain ⟨s, l, A, hsx, hA, hev⟩ :=
    hσ.exists_eval₂_mfderiv_angleMap_eq_of_isCompact hF hcomm hc hdim hreg hK
  set g := hA.localInverse
  have hev' : ∀ᶠ c in 𝓝 (F x), c ∈ g.target ∧ A c ∈ g.source ∧ ContDiffAt ℝ ∞ A c :=
    (g.open_target.eventually_mem hA.localInverse_mem_target).and
      ((hA.contMDiffAt.continuousAt.eventually_mem
        (g.open_source.mem_nhds hA.localInverse_mem_source)).and
      (hA.eventually.mono fun c hcA ↦ contMDiffAt_iff_contDiffAt.1 hcA.contMDiffAt))
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.1 (hev.and hev')
  choose hFs hsc hiso hlc hli hstab hAd _ hΨform using fun c (hcV : c ∈ V) ↦ (hVsub hcV).1
  have hVg := fun c (hcV : c ∈ V) ↦ (hVsub hcV).2
  have hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s V := fun c hcV ↦ (hsc c hcV).contMDiffWithinAt
  have hl : ∀ i, ContDiffOn ℝ ∞ (l i) V := fun i c hcV ↦ (hlc c hcV i).contDiffWithinAt
  have hps (i : ι) (c : ι → ℝ) (hcV : c ∈ V) :
      ∀ᶠ c' in 𝓝 c, l i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c') :=
    eventually_of_mem (hV.mem_nhds hcV) fun c' hc' ↦
      hstab c' hc' ▸ AddSubgroup.subset_closure (mem_range_self i)
  set S : Set ((ι → ℝ) × (ι → ℝ)) := univ ×ˢ V
  have hSo : IsOpen S := isOpen_univ.prod hV
  set Ψ := hσ.angleMap hF hcomm hc s l with hΨ
  set χ := actionAngleChart p A
  have hΨloc (q) (hq : q ∈ S) : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ q :=
    hσ.isLocalDiffeomorphAt_angleMap hF hcomm hc hdim hV hq.2 hs hFs (hiso _ hq.2) hl
      (fun i ↦ hps i _ hq.2) (hli _ hq.2) q.1
  have hΨeq (q) (hq : q ∈ S) (q') (hq' : q' ∈ S) :
      Ψ q = Ψ q' ↔ q'.2 = q.2 ∧ ∃ m : ι → ℤ, q'.1 = q.1 + fun i ↦ 2 * π * m i :=
    hσ.angleMap_eq_angleMap_iff_of_section hF hcomm hc (hFs _ hq.2) (hFs _ hq'.2)
      (hli _ hq.2) (hstab _ hq.2)
  have hAinj : InjOn A V := fun c hcV c' hc'V h ↦ by
    rw [← hA.localInverse_left_inv (hVg c hcV).1, ← hA.localInverse_left_inv (hVg c' hc'V).1, h]
  have hχs : ContMDiffOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ χ S :=
    contMDiffOn_actionAngleChart p fun c hcV ↦ (hVg c hcV).2.2.contDiffWithinAt
  -- Step 2: `χ` makes the same identifications as `Ψ`, so it descends to `φ` along `Ψ`.
  obtain ⟨φ, hφΨ, hφs⟩ := exists_comp_eq_of_isLocalDiffeomorphAt hSo hΨloc hχs
    fun q hq q' hq' h ↦ by
      obtain ⟨h2, h1⟩ := (hΨeq q hq q' hq').1 h
      exact (actionAngleChart_eq_iff p).2 ⟨h1, by rw [h2]⟩
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ S := fun q ↦ hΨloc q q.2
  have hWo : IsOpen (Ψ '' S) := by
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [← hloc.isLocalHomeomorphOn.map_nhds_eq hq]
    exact image_mem_map (hSo.mem_nhds hq)
  have hinj : InjOn φ (Ψ '' S) := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ h
    rw [hφΨ q hq, hφΨ q' hq'] at h
    obtain ⟨h1, h2⟩ := (actionAngleChart_eq_iff p).1 h
    exact (hΨeq q hq q' hq').2 ⟨hAinj hq'.2 hq.2 h2, h1⟩
  have hAV : A '' V = g.source ∩ g ⁻¹' V := by
    ext a
    constructor
    · rintro ⟨c, hcV, rfl⟩
      exact ⟨(hVg c hcV).2.1, by rwa [mem_preimage, hA.localInverse_left_inv (hVg c hcV).1]⟩
    · rintro ⟨has, hav⟩
      exact ⟨g a, hav, hA.localInverse_right_inv has⟩
  -- Step 3: `φ` pulls `ω` back to `σ`, since `χ` and `Ψ` pull `ω` and `σ` back to the same form.
  have hdφ (q) (hq : q ∈ S) (a : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) q) :
      mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ (Ψ q)
          (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q a) =
        mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) χ q a := by
    obtain ⟨O, hO, hqO, hφO⟩ := hφs q hq
    -- The chain rule for `χ = φ ∘ Ψ` near `q`.
    have h := ((((hφO.contMDiffAt (hO.mem_nhds hqO)).mdifferentiableAt (by simp)).hasMFDerivAt.comp
      q ((hΨloc q hq).mdifferentiableAt (by simp)).hasMFDerivAt).congr_of_eventuallyEq_abuse
      (f₁ := χ) (eventually_of_mem (hSo.mem_nhds hq) fun q' hq' ↦ (hφΨ q' hq').symm)).mfderiv
    rw [h]
    -- A composite of continuous linear maps applied to `a`; `ContinuousLinearMap.comp_apply` does
    -- not match through the tangent-space type synonyms.
    rfl
  have hform (q) (hq : q ∈ S) (v w : TangentSpace I (Ψ q)) :
      SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm
          (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (φ (Ψ q))
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ (Ψ q) v)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ (Ψ q) w) =
      SmoothBundleForm.eval₂ σ (Ψ q) v w := by
    have hsurj := ((hΨloc q hq).isInvertible_mfderiv (by simp)).surjective
    obtain ⟨a, rfl⟩ := hsurj v
    obtain ⟨b, rfl⟩ := hsurj w
    have hD := hAd _ hq.2
    have hA' : HasFDerivAt A (ContinuousLinearMap.pi fun i ↦
        (2 * π)⁻¹ • ∑ j, l i q.2 j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j)
        q.2 := hasFDerivAt_pi.2 hD
    rw [hdφ q hq, hdφ q hq, hφΨ q hq]
    -- Both sides are `∑ᵢ dθᵢ ∧ dAᵢ` on `a = (a.1, a.2)` and `b = (b.1, b.2)`; the formula for `Ψ`
    -- is stated at `(q.1, q.2)`, which is `q` by eta for pairs.
    refine (eval₂_mfderiv_actionAngleChart p hA' a.1 b.1 a.2 b.2).trans
      (Eq.trans ?_ (hΨform _ hq.2 q.1 a.1 b.1 a.2 b.2).symm)
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(hD i).fderiv, ContinuousLinearMap.pi_apply, ContinuousLinearMap.pi_apply]
  have hlocdiff : IsLocalDiffeomorphOn I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ (Ψ '' S) := by
    rintro ⟨_, q, hq, rfl⟩
    obtain ⟨O, hO, hqO, hφO⟩ := hφs q hq
    -- The differential is injective, since it pulls `ω` back to the nondegenerate form `σ`.
    refine isLocalDiffeomorphAt_of_injective_mfderiv hφO hO hqO
      BoundarylessManifold.isInteriorPoint (by simp) ?_ ?_
    · rw [injective_iff_map_eq_zero]
      intro v hv
      refine (isNondegenerate_iff_separatingLeft.1 hσ.isNondegenerate) _ v fun w ↦ ?_
      rw [← hform q hq v w, hv]
      exact SmoothBundleForm.eval₂_zero_left _ _ _
    · rw [← hdim, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
        (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).toLinearEquiv.finrank_eq,
        Module.finrank_fintype_fun_eq_card, two_mul]
  -- Step 4: `F` is `g` of the rescaled actions.
  refine ⟨Ψ '' S, hWo,
    connectedComponentIn_subset_image_angleMap hσ hF hcomm hc hdim hreg hsx hxV
      (hli _ hxV),
    _, isOpenMap_smul₀ (inv_ne_zero hκ) _
      (hAV ▸ g.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage g.open_source hV),
    φ, hinj, hlocdiff, ?_, ?_, fun a ↦ g ((p / (2 * π)) • a), ?_, ?_⟩
  · rw [image_image, image_congr fun q hq ↦ hφΨ q hq, image_actionAngleChart]
  · rintro _ ⟨q, hq, rfl⟩ v w
    exact hform q hq v w
  · have hgs : ContDiffOn ℝ ∞ g g.source := contMDiffOn_iff_contDiffOn.1 g.contMDiffOn_toFun
    refine hgs.comp (contDiff_const_smul _).contDiffOn ?_
    rintro _ ⟨_, ⟨c, hcV, rfl⟩, rfl⟩
    simpa only [smul_inv_smul₀ hκ] using (hVg c hcV).2.1
  · rintro _ ⟨q, hq, rfl⟩
    rw [hφΨ q hq, actions_actionAngleChart]
    dsimp only
    rw [smul_inv_smul₀ hκ, hA.localInverse_left_inv (hVg _ hq.2).1, hΨ,
      hσ.apply_angleMap hF hcomm hc, hFs _ hq.2]

end IsSymplectic

/-! ### Proper integrable systems -/

namespace IsIntegrableSystem

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] [DecidableEq ι] {F : M → ι → ℝ}

/-- **Action–angle coordinates for a proper integrable system.** For a completely integrable system
`F` on a symplectic manifold that is a proper map, the connected component `L` of `x` in its level
is compact, and the Hamiltonian flows are complete. So if `L` consists of regular points, there
are action–angle coordinates near `L`: a chart `φ` into `T*Tⁿ`, `Tⁿ = ι → AddCircle p`, as in
`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`. -/
theorem exists_actionAngle_of_isProperMap (h : σ.IsIntegrableSystem F) (hσ : σ.IsSymplectic)
    (hFp : IsProperMap F) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (p : ℝ) [Fact (0 < p)] :
    ∃ U : Set M, IsOpen U ∧ connectedComponentIn (F ⁻¹' {F x}) x ⊆ U ∧
      ∃ D : Set (ι → ℝ), IsOpen D ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        (∀ y ∈ U, ∀ v w : TangentSpace I y,
          SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm
              (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (φ y)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
              𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
              𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y w) =
          SmoothBundleForm.eval₂ σ y v w) ∧
        ∃ h : (ι → ℝ) → ι → ℝ, ContDiffOn ℝ ∞ h D ∧
          ∀ y ∈ U, F y = h fun i ↦ (φ y).2 (Pi.single i 1) :=
  hσ.exists_actionAngle h.contMDiff h.poissonBracket_eq_zero
    (h.isCompleteVectorField_hamiltonianVectorField_of_isProperMap hσ.isNondegenerate hFp)
    h.two_mul_card_eq_finrank hreg
    ((hFp.isCompact_preimage isCompact_singleton).of_isClosed_subset
      ((isClosed_singleton.preimage h.contMDiff.continuous).connectedComponentIn)
      (connectedComponentIn_subset _ _)) p

end IsIntegrableSystem

end SmoothTwoForm

end TauCeti
