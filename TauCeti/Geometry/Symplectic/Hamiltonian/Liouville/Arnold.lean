/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow

import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Geometry.Manifold.RegularValue.Section
import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive

/-!
# The Hamiltonian flow action on a regular level: the topological Liouville–Arnold theorem

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2n`, and let
`F : M → (ι → ℝ)`, `|ι| = n`, be a smooth family of pairwise Poisson-commuting functions with
complete Hamiltonian vector fields `X_{Fᵢ}`. Their flows generate an action `v • y` of the vector
group `ι → ℝ` on `M` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`) preserving `F`.
This file proves that the action is transitive on every connected component `L` of a level
`F⁻¹(c)` consisting of regular points of `F`, with discrete stabilizer `Λ`, and that the orbit map
`v ↦ v • x` descends to a homeomorphism `(ι → ℝ) ⧸ Λ ≃ₜ L`. When `L` is compact, `Λ` is therefore
cocompact: `L` is the torus `ℝⁿ/Λ` of the Liouville–Arnold theorem. For a proper map `F` every
component of a level is compact, and every `X_{Fᵢ}` is complete when `F` is an integrable system
(`IsIntegrableSystem.isCompleteVectorField_hamiltonianVectorField_of_isProperMap`).

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.isLocalDiffeomorphAt_hamiltonianFlowAction_section`: sweeping
  a local section of `F` through a regular point by the action is a local diffeomorphism.
* `TauCeti.SmoothTwoForm.IsSymplectic.eventually_exists_hamiltonianFlowAction_apply_eq`: small
  elements of the action reach every nearby point of a regular level.
* `TauCeti.SmoothTwoForm.IsSymplectic.range_hamiltonianFlowAction_apply`: the orbit of `x` is
  the connected component of `x` in its level, when that component is regular.
* `TauCeti.SmoothTwoForm.IsSymplectic.injective_mfderiv_hamiltonianFlowAction_apply`: the orbit
  map has injective derivative at every vector carrying `x` to a regular point.
* `TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowStabilizer` and
  `TauCeti.SmoothTwoForm.IsSymplectic.discreteTopology_hamiltonianFlowStabilizer`: the stabilizer
  of a regular point is discrete.
* `TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction_apply_eq_iff`: two vectors act alike
  on `x` exactly when they differ by an element of its stabilizer.
* `eval₂_mfderiv_hamiltonianFlowAction_of_mem_hamiltonianFlowStabilizer`, in the namespace
  `TauCeti.SmoothTwoForm.IsSymplectic`: the derivative of the action of an element of the
  stabilizer of `y` at `y` is a linear symplectic map of `T_y M`.
* `TauCeti.SmoothTwoForm.IsSymplectic.quotientHamiltonianFlowStabilizerHomeomorph`: the regular
  component is homeomorphic to `(ι → ℝ) ⧸ Λ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.compactSpace_quotient_hamiltonianFlowStabilizer`: the
  stabilizer of a point of a compact regular component is cocompact.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (the action of commuting flows on a level and its
  stabilizer).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4 (the Arnold–Liouville theorem).
-/

/- Proof outline. At a regular point `x`, the `X_{Fᵢ}(x)` are linearly independent and lie in
`ker dF_x`. Sweeping a local section `s` of `F` through `x`
(`TauCeti.IsRegularPoint.exists_contMDiffOn_section`) by the action gives a map
`(v, c) ↦ v • s c` whose derivative `(a, b) ↦ ∑ i, aᵢ X_{Fᵢ}(x) + ds(b)` is injective, hence
invertible since `dim M = 2n`. By the inverse function theorem the sweep is a local
diffeomorphism, and its restriction to `c = F x` shows that small elements of the action reach
every point of the level near `x`. So the orbits are open in the level, the orbit map is open onto
`L`, and connectedness of `L` makes the action transitive. The orbit map is an immersion at `0`,
hence injective near `0`, so the stabilizer is discrete; this needs no dimension count. -/

public section

noncomputable section

open Function Set Filter Module
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))

include hσ hF hcomm hc

/-- **Sweeping a section through a regular point is a local diffeomorphism.** Let `s` be a smooth
local section of `F` through a regular point `x`, defined on an open set `t`. Sweeping it by the
Hamiltonian flow action, `(v, c) ↦ v • s c`, is a smooth local diffeomorphism at `(0, F x)` when
`dim M = 2 · |ι|`. -/
theorem isLocalDiffeomorphAt_hamiltonianFlowAction_section
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) {t : Set (ι → ℝ)} (ht : IsOpen t) (hxt : F x ∈ t)
    {s : (ι → ℝ) → M} (hsx : s (F x) = x) (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t)
    (hFs : ∀ c ∈ t, F (s c) = c) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I ∞
      (fun p : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc p.1).toMul (s p.2))
      (0, F x) := by
  classical
  set P : (ι → ℝ) × (ι → ℝ) → M :=
    fun p ↦ (hσ.hamiltonianFlowAction hF hcomm hc p.1).toMul (s p.2) with hP
  have hPs : ContMDiffOn (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I ∞ P (univ ×ˢ t) :=
    (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).comp_contMDiffOn
      (contMDiffOn_fst.prodMk (hs.comp contMDiffOn_snd fun (_ : (ι → ℝ) × (ι → ℝ)) hp ↦
        (mem_prod.1 hp).2))
  have hopen : IsOpen (univ ×ˢ t : Set ((ι → ℝ) × (ι → ℝ))) := isOpen_univ.prod ht
  have hmem : ((0 : ι → ℝ), F x) ∈ univ ×ˢ t := ⟨mem_univ _, hxt⟩
  have hPd : MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I P (0, F x) :=
    (hPs.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)
  have hsd : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s (F x) :=
    (hs.contMDiffAt (ht.mem_nhds hxt)).mdifferentiableAt (by simp)
  -- All derivatives are taken at `x' = P (0, F x)`, which is `x`; the tangent spaces at the two
  -- spellings of this point are only identified up to the `TangentSpace` instances, so the
  -- computations below are stated in the model spaces.
  set x' := P (0, F x) with hx'
  have hx'x : x' = x := by simp only [hx', hP, hσ.hamiltonianFlowAction_zero_apply, hsx]
  have hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x' := hx'x ▸ hx
  have hFd : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x' := hF.mdifferentiableAt (by simp)
  let S : (ι → ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ι → ℝ) I s (F x)
  let dF : E →L[ℝ] (ι → ℝ) := mfderiv I 𝓘(ℝ, ι → ℝ) F x'
  -- `dF ∘ ds = id`, since `F ∘ s` is the identity near `F x`.
  have hdFs (b : ι → ℝ) : dF (S b) = b := by
    have hid : F ∘ s =ᶠ[𝓝 (F x)] id :=
      eventually_of_mem (ht.mem_nhds hxt) fun c hc ↦ hFs c hc
    have hm : mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (F ∘ s) (F x) =
        mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) id (F x) := hid.mfderiv_eq
    have := congrArg (· b) hm
    rw [mfderiv_comp_apply_of_eq (F x) hFd hsd (hsx.trans hx'x.symm) b, mfderiv_id] at this
    exact this
  let X : ι → E := fun i ↦ σ.hamiltonianVectorField (F · i) x'
  -- `dF` kills the Hamiltonian vectors of the Poisson-commuting `Fᵢ`.
  have hdFX (i : ι) : dF (X i) = 0 :=
    (hσ.isNondegenerate.hamiltonianVectorField_mem_ker_mfderiv_iff hFd i).2 fun j ↦ hcomm j i x'
  -- The derivative of the sweep, read as a map between the model spaces. It is injective: `dF`
  -- kills the `X_{Fᵢ}` and inverts `ds`, and the `X_{Fᵢ}(x)` are independent at the regular
  -- point `x`.
  let L : (ι → ℝ) × (ι → ℝ) →L[ℝ] E := mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I P (0, F x)
  have hL (a b : ι → ℝ) :
      L (a, b) = ∑ i, a i • X i + S b := by
    -- `P` moves `c ↦ s c.2` by `Prod.fst`, and the action of `0` is the identity.
    have hB : mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I (fun q : (ι → ℝ) × (ι → ℝ) ↦ s q.2)
        (0, F x) (a, b) = S b := by
      have h := hsd.hasMFDerivAt.comp (0, F x) (hasMFDerivAt_snd (I := 𝓘(ℝ, ι → ℝ))
        (I' := 𝓘(ℝ, ι → ℝ)) ((0 : ι → ℝ), F x))
      exact congrArg (fun L ↦ L (a, b)) h.mfderiv
    have hφ (v : E) :
        mfderiv I I (hσ.hamiltonianFlowAction hF hcomm hc 0).toMul (s (F x)) v = v := by
      rw [show ((hσ.hamiltonianFlowAction hF hcomm hc 0).toMul : M → M) = id from
        funext (hσ.hamiltonianFlowAction_zero_apply hF hcomm hc), mfderiv_id]
      rfl
    refine (hσ.mfderiv_hamiltonianFlowAction_comp hF hcomm hc (h := Prod.fst)
      (g := fun q ↦ s q.2) mdifferentiableAt_fst (hsd.comp (0, F x) mdifferentiableAt_snd)
      (a, b)).trans ?_
    rw [mfderiv_fst, hB, hφ]
    rfl
  -- `L` is injective: `dF` recovers `b` from `L (a, b)`, and then `a = 0` by independence.
  have hinj : Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun ⟨a, b⟩ h ↦ ?_
    rw [hL] at h
    have hb : b = 0 := by
      have := congrArg dF h
      simpa only [map_add, map_sum, map_smul, hdFX, smul_zero, Finset.sum_const_zero, zero_add,
        hdFs, map_zero] using this
    subst hb
    rw [map_zero, add_zero] at h
    have ha := Fintype.linearIndependent_iff.1
      (hσ.isNondegenerate.linearIndependent_hamiltonianVectorField hreg) a h
    exact Prod.ext (funext ha) rfl
  have hfin : finrank ℝ ((ι → ℝ) × (ι → ℝ)) = finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, ← hdim, two_mul]
  exact isLocalDiffeomorphAt_of_mfderiv_eq hPs hopen hmem
    BoundarylessManifold.isInteriorPoint (by simp)
    (e := (LinearMap.linearEquivOfInjective L.toLinearMap hinj hfin).toContinuousLinearEquiv)
    (ContinuousLinearMap.ext fun w ↦ LinearMap.linearEquivOfInjective_apply hinj hfin w)

/-- **Small elements of the Hamiltonian flow action reach every nearby point of a regular level.**
Let `x` be a regular point of `F` on a manifold of dimension `2 · |ι|`. For every neighbourhood
`V` of `0` in `ι → ℝ`, every point `y` near `x` with `F y = F x` is `v • x` for some `v ∈ V`. -/
theorem eventually_exists_hamiltonianFlowAction_apply_eq
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M} (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    {V : Set (ι → ℝ)} (hV : V ∈ 𝓝 0) :
    ∀ᶠ y in 𝓝 x, F y = F x → ∃ v ∈ V, (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = y := by
  obtain ⟨t, ht, hxt, s, hsx, hs, hFs⟩ :=
    hx.exists_contMDiffOn_section hF.contMDiffOn isOpen_univ (mem_univ x) (by simp)
  have hL := hσ.isLocalDiffeomorphAt_hamiltonianFlowAction_section hF hcomm hc hdim hx ht hxt hsx
    hs hFs
  set P : (ι → ℝ) × (ι → ℝ) → M :=
    fun p ↦ (hσ.hamiltonianFlowAction hF hcomm hc p.1).toMul (s p.2) with hP
  have hPx : P (0, F x) = x := by simp only [hP, hσ.hamiltonianFlowAction_zero_apply, hsx]
  -- A local inverse `g` of the sweep `P` near `x` sends the points near `x` into `V ×ˢ t`.
  set g := hL.localInverse
  have hg0 : g (P (0, F x)) = (0, F x) := hL.localInverse_left_inv hL.localInverse_mem_target
  have hcont : Tendsto g (𝓝 x) (𝓝 (0, F x)) := by
    have := hL.continuousAt_localInverse
    rwa [ContinuousAt, hg0, hPx] at this
  have hsrc : g.source ∈ 𝓝 x :=
    hPx ▸ hL.localInverse_open_source.mem_nhds hL.localInverse_mem_source
  filter_upwards [hcont (prod_mem_nhds hV (ht.mem_nhds hxt)), hsrc] with y hy hys hFy
  have hPy : P (g y) = y := hL.localInverse_right_inv hys
  -- The sweep preserves the second coordinate under `F`, so `g y` lies over `F y = F x`.
  have hF2 : F y = (g y).2 := by
    calc F y = F (P (g y)) := by rw [hPy]
      _ = (g y).2 := by simp only [hP, hσ.apply_hamiltonianFlowAction hF hcomm hc, hFs _ hy.2]
  refine ⟨(g y).1, hy.1, ?_⟩
  calc (hσ.hamiltonianFlowAction hF hcomm hc (g y).1).toMul x = P (g y) := by
        simp only [hP]
        rw [← hF2, hFy, hsx]
    _ = y := hPy

/-- **The Hamiltonian flow action preserves the connected components of the level sets of `F`.**
Every `v • x` lies in the connected component of `x` in its level `F⁻¹(F x)`. -/
theorem hamiltonianFlowAction_apply_mem_connectedComponentIn (x : M) (v : ι → ℝ) :
    (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x ∈ connectedComponentIn (F ⁻¹' {F x}) x :=
  (isPreconnected_range
    (hσ.continuous_hamiltonianFlowAction_apply hF hcomm hc x)).subset_connectedComponentIn
    ⟨0, by simp⟩ (by rintro _ ⟨w, rfl⟩; exact hσ.apply_hamiltonianFlowAction hF hcomm hc w x)
    ⟨v, rfl⟩

/-- **The Hamiltonian flow action is transitive on a regular connected component of a level.**
On a manifold of dimension `2 · |ι|`, if every point of the connected component `L` of `x` in its
level `F⁻¹(F x)` is a regular point of `F`, then every point of `L` is `v • x` for some
`v : ι → ℝ`. -/
theorem exists_hamiltonianFlowAction_apply_eq (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    {y : M} (hy : y ∈ connectedComponentIn (F ⁻¹' {F x}) x) :
    ∃ v, (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = y := by
  set C := connectedComponentIn (F ⁻¹' {F x}) x
  set O := range fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x
  have hFC {z : M} (hz : z ∈ C) : F z = F x := connectedComponentIn_subset _ _ hz
  -- Near each point `z` of `C`, the level is filled out by the orbit of `z`, which is either
  -- `O` or disjoint from `O`. So `C` is covered by the two open sets where nearby points of the
  -- level lie in `O`, respectively outside `O`.
  have hloc {z : M} (hz : z ∈ C) : ∀ᶠ y' in 𝓝 z, F y' = F x →
      ∃ v, (hσ.hamiltonianFlowAction hF hcomm hc v).toMul z = y' := by
    filter_upwards [hσ.eventually_exists_hamiltonianFlowAction_apply_eq hF hcomm hc hdim
      (hreg z hz) univ_mem] with y' hy' hFy'
    obtain ⟨v, -, hv⟩ := hy' (hFy'.trans (hFC hz).symm)
    exact ⟨v, hv⟩
  have hu : IsOpen {z | ∀ᶠ y' in 𝓝 z, F y' = F x → y' ∈ O} := isOpen_setOfPred_eventually_nhds
  have hv : IsOpen {z | ∀ᶠ y' in 𝓝 z, F y' = F x → y' ∉ O} := isOpen_setOfPred_eventually_nhds
  have hcover : C ⊆ {z | ∀ᶠ y' in 𝓝 z, F y' = F x → y' ∈ O} ∪
      {z | ∀ᶠ y' in 𝓝 z, F y' = F x → y' ∉ O} := by
    intro z hz
    by_cases hzO : z ∈ O
    · obtain ⟨w, rfl⟩ := hzO
      refine Or.inl ((hloc hz).mono fun y' hy' hFy' ↦ ?_)
      obtain ⟨v, rfl⟩ := hy' hFy'
      exact ⟨v + w, hσ.hamiltonianFlowAction_add_apply hF hcomm hc v w x⟩
    · refine Or.inr ((hloc hz).mono fun y' hy' hFy' ⟨w, hw⟩ ↦ hzO ?_)
      obtain ⟨v, rfl⟩ := hy' hFy'
      refine ⟨-v + w, ?_⟩
      dsimp only at hw ⊢
      rw [hσ.hamiltonianFlowAction_add_apply hF hcomm hc, hw,
        hσ.hamiltonianFlowAction_neg_apply_apply]
  have hdisj : C ∩ ({z | ∀ᶠ y' in 𝓝 z, F y' = F x → y' ∈ O} ∩
      {z | ∀ᶠ y' in 𝓝 z, F y' = F x → y' ∉ O}) = ∅ := by
    refine eq_empty_of_forall_notMem fun z ⟨hz, h₁, h₂⟩ ↦ ?_
    exact h₂.self_of_nhds (hFC hz) (h₁.self_of_nhds (hFC hz))
  have hxO : x ∈ O := ⟨0, by simp⟩
  have hxC : x ∈ C := mem_connectedComponentIn rfl
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn _ _ hu hv
    hcover hdisj with h | h
  · exact (h hy).self_of_nhds (hFC hy)
  · exact ((h hxC).self_of_nhds rfl hxO).elim

/-- **The orbit of a point with regular connected level component is that component.** On a
manifold of dimension `2 · |ι|`, if every point of the connected component of `x` in its level
`F⁻¹(F x)` is a regular point of `F`, then this component is the orbit of `x` under the
Hamiltonian flow action. -/
theorem range_hamiltonianFlowAction_apply (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) :
    range (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) =
      connectedComponentIn (F ⁻¹' {F x}) x := by
  refine subset_antisymm ?_ fun y hy ↦
    hσ.exists_hamiltonianFlowAction_apply_eq hF hcomm hc hdim hreg hy
  rintro _ ⟨v, rfl⟩
  exact hσ.hamiltonianFlowAction_apply_mem_connectedComponentIn hF hcomm hc x v

/-! ### The stabilizer and the quotient description of a regular component -/

/-- The **stabilizer** of `x` for the Hamiltonian flow action: the subgroup of the vectors
`v : ι → ℝ` with `v • x = x`. It is discrete when `x` is a regular point of `F`
(`discreteTopology_hamiltonianFlowStabilizer`). On a manifold of dimension `2 · |ι|`, it is
cocompact when moreover the connected component of `x` in its level is compact and regular
(`compactSpace_quotient_hamiltonianFlowStabilizer`); it is then the period lattice of the
Liouville torus. -/
def hamiltonianFlowStabilizer (x : M) : AddSubgroup (ι → ℝ) :=
  letI := hσ.hamiltonianFlowAddAction hF hcomm hc
  AddAction.stabilizer (ι → ℝ) x

@[simp]
theorem mem_hamiltonianFlowStabilizer {x : M} {v : ι → ℝ} :
    v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x ↔
      (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = x :=
  Iff.rfl

/-- Two vectors act alike on `x` exactly when they differ by an element of the stabilizer. -/
theorem hamiltonianFlowAction_apply_eq_iff {x : M} {v w : ι → ℝ} :
    (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x =
        (hσ.hamiltonianFlowAction hF hcomm hc w).toMul x ↔
      -v + w ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x :=
  letI := hσ.hamiltonianFlowAddAction hF hcomm hc
  (AddAction.injective_ofQuotientStabilizer (ι → ℝ) x).eq_iff
    (a := (v : (ι → ℝ) ⧸ AddAction.stabilizer (ι → ℝ) x)) (b := w) |>.trans QuotientAddGroup.eq

/-- **The linearized return map of a period is symplectic.** If `v` is a period of `y`, the action
of `v` fixes `y`, and its derivative at `y` is a linear symplectic map of `T_y M`. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_of_mem_hamiltonianFlowStabilizer {y : M}
    {v : ι → ℝ} (hv : v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc y) (a b : TangentSpace I y) :
    SmoothBundleForm.eval₂ σ y
        (mfderiv I I (hσ.hamiltonianFlowAction hF hcomm hc v).toMul y a)
        (mfderiv I I (hσ.hamiltonianFlowAction hF hcomm hc v).toMul y b) =
      SmoothBundleForm.eval₂ σ y a b := by
  have hφ := SmoothForm.eval₂_mpullback _ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul.contMDiff
    σ y a b
  rw [hσ.mpullback_hamiltonianFlowAction] at hφ
  rw [hφ]
  -- The derivative lands in `T_{v • y} M`, which is `T_y M` since `v • y = y`.
  have key : ∀ z, z = y → ∀ a' b' : E,
      SmoothBundleForm.eval₂ σ z a' b' = SmoothBundleForm.eval₂ σ y a' b' := by
    rintro _ rfl _ _
    rfl
  exact (key _ ((hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 hv) _ _).symm

/-- **The orbit map has injective derivative at regular points.** If `v • x` is a regular point of
`F`, the derivative `w ↦ ∑ i, wᵢ X_{Fᵢ}(v • x)` of the orbit map `v ↦ v • x` at `v` is injective,
since the `X_{Fᵢ}(v • x)` are linearly independent. -/
theorem injective_mfderiv_hamiltonianFlowAction_apply {x : M} {v : ι → ℝ}
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul x)) :
    Injective
      (mfderiv 𝓘(ℝ, ι → ℝ) I (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) v) :=
  (injective_iff_map_eq_zero _).2 fun w hw ↦ funext <| Fintype.linearIndependent_iff.1
    (hσ.isNondegenerate.linearIndependent_hamiltonianVectorField hx) w <|
      (hσ.mfderiv_hamiltonianFlowAction_apply hF hcomm hc x v w).symm.trans hw

/-- **The orbit map is injective near `0` at a regular point.** If `x` is a regular point of `F`,
then no vector near `0` other than `0` fixes `x`. -/
theorem eventually_eq_zero_of_hamiltonianFlowAction_apply_eq {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) :
    ∀ᶠ v in 𝓝 (0 : ι → ℝ), (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = x → v = 0 := by
  set o : (ι → ℝ) → M := fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x with ho
  have ho0 : o 0 = x := hσ.hamiltonianFlowAction_zero_apply hF hcomm hc x
  have hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F (o 0) := ho0 ▸ hx
  have hinj : Injective (mfderiv 𝓘(ℝ, ι → ℝ) I o 0) :=
    hσ.injective_mfderiv_hamiltonianFlowAction_apply hF hcomm hc hreg
  have hoc : ContMDiffAt 𝓘(ℝ, ι → ℝ) I ∞ o 0 :=
    hσ.contMDiff_hamiltonianFlowAction_apply hF hcomm hc x 0
  obtain ⟨t, ht, hinjt⟩ := hoc.exists_mem_nhds_injOn (by simp) hinj
  filter_upwards [ht] with v hv hvx
  exact hinjt hv (mem_of_mem_nhds ht) (hvx.trans ho0.symm)

/-- **The stabilizer of a regular point is discrete.** The stabilizer of a regular point of `F`
is a discrete subgroup of `ι → ℝ`. -/
theorem discreteTopology_hamiltonianFlowStabilizer {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) :
    DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x) := by
  obtain ⟨U, hU, hUo, hU0⟩ := eventually_nhds_iff.1
    (hσ.eventually_eq_zero_of_hamiltonianFlowAction_apply_eq hF hcomm hc hx)
  refine discreteTopology_of_isOpen_singleton_zero (isOpen_induced_iff.2 ⟨U, hUo, ?_⟩)
  ext ⟨v, hv⟩
  simp only [mem_preimage, mem_singleton_iff, AddSubgroup.mk_eq_zero]
  exact ⟨fun h ↦ hU v h hv, fun h ↦ h ▸ hU0⟩

/-- On a regular connected component of a level, the orbit map is open onto the component. -/
private theorem isOpenMap_hamiltonianFlowAction_apply (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) :
    IsOpenMap fun v : ι → ℝ ↦ (⟨(hσ.hamiltonianFlowAction hF hcomm hc v).toMul x,
      hσ.hamiltonianFlowAction_apply_mem_connectedComponentIn hF hcomm hc x v⟩ :
        connectedComponentIn (F ⁻¹' {F x}) x) := by
  intro W hW
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨v, hvW, rfl⟩
  set z := (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x
  have hzC := hσ.hamiltonianFlowAction_apply_mem_connectedComponentIn hF hcomm hc x v
  have hFC {y : M} (hy : y ∈ connectedComponentIn (F ⁻¹' {F x}) x) : F y = F x :=
    connectedComponentIn_subset _ _ hy
  -- The translate of `W` by `-v` is a neighbourhood of `0`, whose action on `z` fills out the
  -- level near `z`.
  have hV : (· + v) ⁻¹' W ∈ 𝓝 (0 : ι → ℝ) :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using hW.mem_nhds hvW)
  rw [mem_nhds_subtype]
  refine ⟨_, hσ.eventually_exists_hamiltonianFlowAction_apply_eq hF hcomm hc hdim (hreg z hzC) hV,
    fun ⟨y, hyC⟩ hy ↦ ?_⟩
  obtain ⟨u, hu, huy⟩ := hy ((hFC hyC).trans (hFC hzC).symm)
  refine ⟨u + v, hu, Subtype.ext ?_⟩
  dsimp only
  rw [hσ.hamiltonianFlowAction_add_apply hF hcomm hc]
  exact huy

/-- **A regular connected component of a level is the quotient of `ι → ℝ` by the stabilizer.** On
a manifold of dimension `2 · |ι|`, if every point of the connected component `L` of `x` in its
level `F⁻¹(F x)` is a regular point of `F`, the orbit map `v ↦ v • x` descends to a
homeomorphism from `(ι → ℝ) ⧸ Λ` onto `L`, where `Λ` is the stabilizer of `x`. -/
def quotientHamiltonianFlowStabilizerHomeomorph (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) :
    (ι → ℝ) ⧸ hσ.hamiltonianFlowStabilizer hF hcomm hc x ≃ₜ connectedComponentIn (F ⁻¹' {F x}) x :=
  letI := hσ.hamiltonianFlowAddAction hF hcomm hc
  -- The orbit–stabilizer bijection, followed by the identification of the orbit with `L`.
  let e : (ι → ℝ) ⧸ hσ.hamiltonianFlowStabilizer hF hcomm hc x ≃
      connectedComponentIn (F ⁻¹' {F x}) x :=
    (AddAction.orbitEquivQuotientStabilizer (ι → ℝ) x).symm.trans
      (Set.equivOfEq (hσ.range_hamiltonianFlowAction_apply hF hcomm hc hdim hreg))
  -- Composed with the quotient map, `e` is the orbit map.
  have he : e ∘ QuotientAddGroup.mk = fun v ↦ ⟨(hσ.hamiltonianFlowAction hF hcomm hc v).toMul x,
      hσ.hamiltonianFlowAction_apply_mem_connectedComponentIn hF hcomm hc x v⟩ := rfl
  e.toHomeomorphOfContinuousOpen
    ((QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 <| he ▸
      (hσ.continuous_hamiltonianFlowAction_apply hF hcomm hc x).subtype_mk _)
    (IsOpenMap.of_comp QuotientAddGroup.continuous_mk QuotientAddGroup.mk_surjective <|
      he ▸ hσ.isOpenMap_hamiltonianFlowAction_apply hF hcomm hc hdim hreg)

@[simp]
theorem coe_quotientHamiltonianFlowStabilizerHomeomorph_mk
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (v : ι → ℝ) :
    (hσ.quotientHamiltonianFlowStabilizerHomeomorph hF hcomm hc hdim hreg v : M) =
      (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x :=
  (rfl)

/-- **The stabilizer of a compact regular component is cocompact.** On a manifold of dimension
`2 · |ι|`, if the connected component `L` of `x` in its level `F⁻¹(F x)` is compact and consists
of regular points of `F`, the quotient of `ι → ℝ` by the stabilizer of `x` is compact. -/
theorem compactSpace_quotient_hamiltonianFlowStabilizer (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hL : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    CompactSpace ((ι → ℝ) ⧸ hσ.hamiltonianFlowStabilizer hF hcomm hc x) :=
  have := isCompact_iff_compactSpace.1 hL
  (hσ.quotientHamiltonianFlowStabilizerHomeomorph hF hcomm hc hdim hreg).symm.compactSpace

end IsSymplectic

end SmoothTwoForm

end TauCeti
