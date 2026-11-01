/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow

import TauCeti.Geometry.Manifold.MFDeriv.Curve
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

The proof is local. The action is jointly smooth, and the derivative of the orbit map at `v` is
`w ↦ ∑ i, wᵢ X_{Fᵢ}(v • x)`. At a regular point `x`, the `X_{Fᵢ}(x)` are linearly independent and
lie in `ker dF_x`. Sweeping a local section `s` of `F` through `x`
(`TauCeti.IsRegularPoint.exists_contMDiffOn_section`) by the action gives a map
`(v, c) ↦ v • s c` whose derivative `(a, b) ↦ ∑ i, aᵢ X_{Fᵢ}(x) + ds(b)` is injective, hence
invertible since `dim M = 2n`. By the inverse function theorem the sweep is a local
diffeomorphism, and its restriction to `c = F x` shows that small elements of the action reach
every point of the level near `x`. So the orbits are open in the level, the orbit map is open onto
`L`, and connectedness of `L` makes the action transitive. The orbit map is an immersion at `0`,
hence injective near `0`, so the stabilizer is discrete; this needs no dimension count.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.contMDiff_hamiltonianFlowAction_uncurry`: the action is
  jointly smooth.
* `TauCeti.SmoothTwoForm.IsSymplectic.mfderiv_hamiltonianFlowAction_apply`: the derivative of an
  orbit map.
* `TauCeti.SmoothTwoForm.IsSymplectic.eventually_exists_hamiltonianFlowAction_apply_eq`: small
  elements of the action reach every nearby point of a regular level.
* `TauCeti.SmoothTwoForm.IsSymplectic.range_hamiltonianFlowAction_apply`: the orbit of `x` is
  the connected component of `x` in its level, when that component is regular.
* `TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowStabilizer` and
  `TauCeti.SmoothTwoForm.IsSymplectic.discreteTopology_hamiltonianFlowStabilizer`: the stabilizer
  of a regular point is discrete.
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

omit hcomm hc [I.Boundaryless] [T2Space M] [BoundarylessManifold I M] in
/-- The Hamiltonian vector fields of the components of `F` are smooth. -/
private theorem contMDiff_hamiltonianVectorField_component (i : ι) :
    ContMDiff I I.tangent (⊤ : ℕ∞)
      (fun y ↦ (⟨y, σ.hamiltonianVectorField (F · i) y⟩ : TangentBundle I M)) :=
  hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl
    (by simpa using contMDiff_pi_module_iff.1 hF i)

/-- **The Hamiltonian flow action is jointly smooth.** The map `(v, y) ↦ v • y`, where `v : ι → ℝ`
acts by the composite of the time-`vᵢ` maps of the flows of the `Fᵢ`, is smooth on
`(ι → ℝ) × M`. -/
theorem contMDiff_hamiltonianFlowAction_uncurry :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod I) I ∞
      fun p : (ι → ℝ) × M ↦ (hσ.hamiltonianFlowAction hF hcomm hc p.1).toMul p.2 := by
  classical
  have hv := hσ.contMDiff_hamiltonianVectorField_component hF
  -- Add the coordinate axes one at a time: on `Pi.single j (v j) + w` the action is the flow of
  -- `F j` for time `v j` after the action of `w`.
  have key (s : Finset ι) : ContMDiff (𝓘(ℝ, ι → ℝ).prod I) I ∞ fun p : (ι → ℝ) × M ↦
      (hσ.hamiltonianFlowAction hF hcomm hc (∑ i ∈ s, Pi.single i (p.1 i))).toMul p.2 := by
    induction s using Finset.induction_on with
    | empty => simpa using contMDiff_snd
    | insert j s hj ih =>
      have heq : (fun p : (ι → ℝ) × M ↦
          (hσ.hamiltonianFlowAction hF hcomm hc (∑ i ∈ insert j s, Pi.single i (p.1 i))).toMul
            p.2) = fun p ↦ globalFlow (σ.hamiltonianVectorField (F · j))
              ((hv j).of_le (by exact_mod_cast le_top)) (hc j) (p.1 j)
              ((hσ.hamiltonianFlowAction hF hcomm hc (∑ i ∈ s, Pi.single i (p.1 i))).toMul
                p.2) := by
        funext p
        rw [Finset.sum_insert hj, map_add, toMul_add, Diffeomorph.mul_apply,
          hσ.hamiltonianFlowAction_single_apply hF hcomm hc]
      rw [heq]
      exact (contMDiff_globalFlow_uncurry (hc j) le_top (hv j)).comp
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).contMDiff.comp
          contMDiff_fst).prodMk ih)
  simpa only [Finset.univ_sum_single] using key Finset.univ

/-- **The derivative of an orbit map of the Hamiltonian flow action.** The orbit map
`v ↦ v • x` has derivative `w ↦ ∑ i, wᵢ X_{Fᵢ}(v • x)` at every `v : ι → ℝ`: moving `v` along the
`i`-th coordinate axis moves `v • x` along the flow of `Fᵢ`. -/
theorem mfderiv_hamiltonianFlowAction_apply (x : M) (v w : ι → ℝ) :
    mfderiv 𝓘(ℝ, ι → ℝ) I (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) v w =
      ∑ i, w i •
        σ.hamiltonianVectorField (F · i) ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) := by
  classical
  set o : (ι → ℝ) → M := fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x with ho
  have hv := hσ.contMDiff_hamiltonianVectorField_component hF
  have hd (u : ι → ℝ) : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I o u :=
    ((hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
  -- Along the `i`-th coordinate axis through `v`, the orbit map is the flow line of `Fᵢ`
  -- through `v • x`.
  have hax (i : ι) : mfderiv 𝓘(ℝ, ι → ℝ) I o v (Pi.single i 1) =
      σ.hamiltonianVectorField (F · i) (o v) := by
    have hcd : HasDerivAt (fun t : ℝ ↦ v + t • Pi.single i (1 : ℝ)) (Pi.single i 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add v
    have hflow : (o ∘ fun t : ℝ ↦ v + t • Pi.single i 1) = fun t ↦
        globalFlow (σ.hamiltonianVectorField (F · i))
          ((hv i).of_le (by exact_mod_cast le_top)) (hc i) t (o v) := by
      funext t
      simp only [comp_apply, ho, add_comm v, map_add, toMul_add, Diffeomorph.mul_apply]
      rw [← Pi.single_smul', smul_eq_mul, mul_one,
        hσ.hamiltonianFlowAction_single_apply hF hcomm hc]
    have hvel := Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
      (isMIntegralCurve_globalFlow ((hv i).of_le (by exact_mod_cast le_top)) (hc i) (o v)
        0).hasMFDerivWithinAt uniqueDiffWithinAt_univ
    rw [Manifold.curveVelocityWithin_univ] at hvel
    have h1 := MDifferentiableAt.curveVelocity_comp_mfderiv (hd _) hcd
    have h0 : v + (0 : ℝ) • Pi.single i (1 : ℝ) = v := by simp
    rw [hflow, hvel, h0] at h1
    rw [← h1]
    -- The flow line starts at `o v`; its time-zero value is the structure field `map_zero'`.
    exact congrArg (fun y ↦ (σ.hamiltonianVectorField (F · i) y : E))
      ((globalFlow _ _ (hc i)).map_zero' (o v))
  -- Expand `w` in the coordinate basis. The tangent spaces involved are `ι → ℝ` and `E` with
  -- their own `TangentSpace` instances, which block rewriting with the coordinate expansion of
  -- `w`; the `change` reads the derivative as a map between the model spaces.
  let L : (ι → ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ι → ℝ) I o v
  change L w = ∑ i, w i • (σ.hamiltonianVectorField (F · i) (o v) : E)
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show Pi.single i (w i) = w i • Pi.single i (1 : ℝ) by
    rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul]
  exact congrArg (w i • ·) (hax i)

/-- Sweeping a local section `s` of `F` through a regular point `x` by the Hamiltonian flow action,
`(v, c) ↦ v • s c`, is a local diffeomorphism at `(0, F x)` when `dim M = 2 · |ι|`. Its derivative
`(a, b) ↦ ∑ i, aᵢ X_{Fᵢ}(x) + ds(b)` is injective: `dF` kills the `X_{Fᵢ}` and inverts `ds`, and
the `X_{Fᵢ}(x)` are independent at the regular point `x`. -/
private theorem isLocalDiffeomorphAt_hamiltonianFlowAction_section
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) {t : Set (ι → ℝ)} (ht : IsOpen t) (hxt : F x ∈ t)
    {s : (ι → ℝ) → M} (hsx : s (F x) = x) (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t)
    (hFs : ∀ c ∈ t, F (s c) = c) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I 1
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
  have hFd : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F x := hF.mdifferentiableAt (by simp)
  -- All derivatives are taken at `x' = P (0, F x)`, which is `x`; the tangent spaces at the two
  -- spellings of this point are only identified up to the `TangentSpace` instances, so the
  -- computations below are stated in the model spaces.
  set x' := P (0, F x) with hx'
  have hx'x : x' = x := by simp only [hx', hP, map_zero, toMul_zero, Diffeomorph.one_apply, hsx]
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
  -- The derivative of the sweep, read as a map between the model spaces.
  let L : (ι → ℝ) × (ι → ℝ) →L[ℝ] E := mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I P (0, F x)
  have hL (a b : ι → ℝ) :
      L (a, b) = ∑ i, a i • X i + S b := by
    have hA : (mfderiv 𝓘(ℝ, ι → ℝ) I (fun z ↦ P (z, F x)) 0 : (ι → ℝ) →L[ℝ] E) a =
        ∑ i, a i • X i :=
      hσ.mfderiv_hamiltonianFlowAction_apply hF hcomm hc (s (F x)) 0 a
    have hB : (mfderiv 𝓘(ℝ, ι → ℝ) I (fun z ↦ P (0, z)) (F x) : (ι → ℝ) →L[ℝ] E) b = S b :=
      congrArg (fun g : (ι → ℝ) → M ↦ (mfderiv 𝓘(ℝ, ι → ℝ) I g (F x) : (ι → ℝ) →L[ℝ] E) b)
        (funext fun z ↦ by simp only [hP, map_zero, toMul_zero, Diffeomorph.one_apply])
    rw [← hA, ← hB]
    exact mfderiv_prod_eq_add_apply (v := ((a, b) : (ι → ℝ) × (ι → ℝ))) hPd
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
  exact isLocalDiffeomorphAt_of_mfderiv_eq (hPs.of_le (by simp)) hopen hmem
    BoundarylessManifold.isInteriorPoint le_rfl
    (e := (LinearMap.linearEquivOfInjective L.toLinearMap hinj hfin).toContinuousLinearEquiv)
    (ContinuousLinearMap.ext fun _ ↦ rfl)

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
  have hPx : P (0, F x) = x := by simp only [hP, map_zero, toMul_zero, Diffeomorph.one_apply, hsx]
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

/-- The action of `v + w` is the action of `v` after that of `w`. -/
private theorem hamiltonianFlowAction_add_apply (v w : ι → ℝ) (x : M) :
    (hσ.hamiltonianFlowAction hF hcomm hc (v + w)).toMul x =
      (hσ.hamiltonianFlowAction hF hcomm hc v).toMul
        ((hσ.hamiltonianFlowAction hF hcomm hc w).toMul x) := by
  rw [map_add, toMul_add, Diffeomorph.mul_apply]

/-- The orbit maps of the Hamiltonian flow action are continuous. -/
private theorem continuous_hamiltonianFlowAction_apply (x : M) :
    Continuous fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x :=
  ((hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).comp
    (contMDiff_id.prodMk contMDiff_const)).continuous

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
        ← hσ.hamiltonianFlowAction_add_apply hF hcomm hc, neg_add_cancel, map_zero, toMul_zero,
        Diffeomorph.one_apply]
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
`v : ι → ℝ` with `v • x = x`. It is discrete when `x` is a regular point of `F`, and cocompact when
moreover the connected component of `x` in its level is compact and regular; it is then the period
lattice of the Liouville torus. -/
def hamiltonianFlowStabilizer (x : M) : AddSubgroup (ι → ℝ) where
  carrier := {v | (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = x}
  add_mem' {v w} hv hw := by
    simp only [mem_ofPred_eq] at hv hw ⊢
    rw [hσ.hamiltonianFlowAction_add_apply hF hcomm hc, hw, hv]
  zero_mem' := by simp
  neg_mem' {v} hv := by
    simp only [mem_ofPred_eq] at hv ⊢
    conv_lhs => rw [← hv]
    rw [← hσ.hamiltonianFlowAction_add_apply hF hcomm hc, neg_add_cancel, map_zero, toMul_zero,
      Diffeomorph.one_apply]

@[simp]
theorem mem_hamiltonianFlowStabilizer {x : M} {v : ι → ℝ} :
    v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x ↔
      (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = x :=
  Iff.rfl

/-- Two vectors act alike on `x` exactly when they differ by an element of the stabilizer. -/
private theorem hamiltonianFlowAction_apply_eq_iff {x : M} {v w : ι → ℝ} :
    (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x =
        (hσ.hamiltonianFlowAction hF hcomm hc w).toMul x ↔
      -v + w ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x := by
  rw [mem_hamiltonianFlowStabilizer, hσ.hamiltonianFlowAction_add_apply hF hcomm hc]
  constructor
  · intro h
    rw [← h, ← hσ.hamiltonianFlowAction_add_apply hF hcomm hc, neg_add_cancel, map_zero,
      toMul_zero, Diffeomorph.one_apply]
  · intro h
    calc (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x
        = (hσ.hamiltonianFlowAction hF hcomm hc v).toMul
            ((hσ.hamiltonianFlowAction hF hcomm hc (-v)).toMul
              ((hσ.hamiltonianFlowAction hF hcomm hc w).toMul x)) := by rw [h]
      _ = _ := by
        rw [← hσ.hamiltonianFlowAction_add_apply hF hcomm hc, add_neg_cancel, map_zero,
          toMul_zero, Diffeomorph.one_apply]

/-- **The orbit map is injective near `0` at a regular point.** If `x` is a regular point of `F`,
then no vector near `0` other than `0` fixes `x`: the derivative `w ↦ ∑ i, wᵢ X_{Fᵢ}(x)` of the
orbit map at `0` is injective, since the `X_{Fᵢ}(x)` are linearly independent. -/
theorem eventually_eq_zero_of_hamiltonianFlowAction_apply_eq {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) :
    ∀ᶠ v in 𝓝 (0 : ι → ℝ), (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = x → v = 0 := by
  set o : (ι → ℝ) → M := fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x with ho
  have ho0 : o 0 = x := by simp only [ho, map_zero, toMul_zero, Diffeomorph.one_apply]
  have hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F (o 0) := ho0 ▸ hx
  have hinj : Injective (mfderiv 𝓘(ℝ, ι → ℝ) I o 0) := by
    refine (injective_iff_map_eq_zero _).2 fun w hw ↦ funext <| Fintype.linearIndependent_iff.1
      (hσ.isNondegenerate.linearIndependent_hamiltonianVectorField hreg) w ?_
    exact (hσ.mfderiv_hamiltonianFlowAction_apply hF hcomm hc x 0 w).symm.trans hw
  have hoc : ContMDiffAt 𝓘(ℝ, ι → ℝ) I ∞ o 0 :=
    ((hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).comp
      (contMDiff_id.prodMk contMDiff_const)) 0
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
  let f : (ι → ℝ) → connectedComponentIn (F ⁻¹' {F x}) x := fun v ↦
    ⟨(hσ.hamiltonianFlowAction hF hcomm hc v).toMul x,
      hσ.hamiltonianFlowAction_apply_mem_connectedComponentIn hF hcomm hc x v⟩
  have hf : ∀ a b, QuotientAddGroup.leftRel (hσ.hamiltonianFlowStabilizer hF hcomm hc x) a b →
      f a = f b := fun a b h ↦ Subtype.ext <|
    (hσ.hamiltonianFlowAction_apply_eq_iff hF hcomm hc).2 (QuotientAddGroup.leftRel_apply.1 h)
  have hbij : Bijective (Quotient.lift f hf) := by
    refine ⟨fun a b ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
    · induction a using Quotient.inductionOn with | h a => ?_
      induction b using Quotient.inductionOn with | h b => ?_
      intro h
      exact QuotientAddGroup.eq.2
        ((hσ.hamiltonianFlowAction_apply_eq_iff hF hcomm hc).1 (congrArg Subtype.val h))
    · obtain ⟨v, hv⟩ := hσ.exists_hamiltonianFlowAction_apply_eq hF hcomm hc hdim hreg hy
      exact ⟨QuotientAddGroup.mk v, Subtype.ext hv⟩
  (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousOpen
    (continuous_quot_lift hf ((hσ.continuous_hamiltonianFlowAction_apply hF hcomm hc
      x).subtype_mk _))
    fun U hU ↦ by
      have himage : Quotient.lift f hf '' U = f '' (QuotientAddGroup.mk ⁻¹' U) := by
        ext y
        constructor
        · rintro ⟨q, hq, rfl⟩
          induction q using Quotient.inductionOn with | h v => exact ⟨v, hq, rfl⟩
        · rintro ⟨v, hv, rfl⟩
          exact ⟨_, hv, rfl⟩
      simpa only [Equiv.ofBijective_apply, himage] using
        hσ.isOpenMap_hamiltonianFlowAction_apply hF hcomm hc hdim hreg _
          (hU.preimage QuotientAddGroup.continuous_mk)

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
