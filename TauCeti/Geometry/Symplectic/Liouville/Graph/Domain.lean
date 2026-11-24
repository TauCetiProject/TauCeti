/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.ClosedCharacteristic
public import TauCeti.Geometry.Symplectic.Liouville.Graph.Basic
public import TauCeti.Geometry.Symplectic.Liouville.Retraction

/-!
# The domain bounded by a Liouville graph

Let `M` be a completion of the Liouville domain `W` (`TauCeti.IsLiouvilleCompletion`), with
Liouville field `Z`, Liouville flow `ψ` and radial coordinate `r`
(`TauCeti.liouvilleRadialCoordinate`), and let `π` be the Liouville retraction
(`TauCeti.liouvilleRetraction`), which sends a point of the cylindrical end `M \ int W` to the
boundary point of its Liouville trajectory and is the identity on `W`.

For a function `f` on `M`, positive on `W`, the **Liouville graph function**
(`TauCeti.liouvilleGraphFunction`) is

`F(x) = r(x) / f(π(x))`.

On the cylindrical end, in the coordinates `(r, y) ↦ ψ_{log r}(y)` of the symplectization of `∂W`,
it is `r / f(y)`: the Liouville flow multiplies it by `e^t`
(`TauCeti.IsLiouvilleCompletion.liouvilleGraphFunction_flowOf_of_notMem_interior`), and the
Liouville field differentiates it to itself
(`TauCeti.IsLiouvilleCompletion.mvfderiv_liouvilleGraphFunction_apply`). Its level `1` meets the
end in the Liouville graph `y ↦ ψ_{log f(y)}(y)` of `f` over `∂W` (`TauCeti.liouvilleGraph`). If
`f` is continuous on `W` and greater than `1` there, then:

* the level `{F = 1}` is exactly the Liouville graph of `f` over `∂W`
  (`TauCeti.IsLiouvilleCompletion.setOf_liouvilleGraphFunction_eq_one`), and it is the frontier of
  the sublevel set `{F ≤ 1}`
  (`TauCeti.IsLiouvilleCompletion.frontier_setOf_liouvilleGraphFunction_le`), whose interior is
  `{F < 1}` (`TauCeti.IsLiouvilleCompletion.interior_setOf_liouvilleGraphFunction_le`) and
  contains `W` (`TauCeti.IsLiouvilleCompletion.subset_interior_setOf_liouvilleGraphFunction_le`);
* all sublevel sets of `F` are compact
  (`TauCeti.IsLiouvilleCompletion.isCompact_setOf_liouvilleGraphFunction_le`), and the deformation
  retraction onto `W` does not increase `F`
  (`TauCeti.IsLiouvilleCompletion.liouvilleGraphFunction_liouvilleRetractionHomotopy_le`), so it
  restricts to a deformation retraction of `{F ≤ 1}` and of `{F < 1}` onto `W`;
* when `f` is moreover smooth along `∂W`, the sublevel set `{F ≤ 1}` is a Liouville domain for
  the same form and primitive
  (`TauCeti.IsLiouvilleCompletion.isLiouvilleDomain_setOf_liouvilleGraphFunction_le`);
* when `f` is differentiable along `∂W`, the logarithm `log F` is translated by the Liouville flow
  near its level `0`, so the contact-type argument applies to the graph: if this level has the
  contractible almost existence property in `U`, then the graph carries a closed characteristic
  contractible in `ψ_t(U)` for some time `t`
  (`IsLiouvilleCompletion.exists_hasContractibleClosedCharacteristic_log_liouvilleGraphFunction`).

The graph pulls the primitive back to `f` times its restriction to `∂W`
(`TauCeti.mpullback_liouvilleGraph_apply`), so the primitive restricts on the boundary of this
domain to the contact form `f α|∂W`. This is the graph construction of Barraud, Damian, Humilière
and Oancea in their proof of Corollary E: the domain `{F < 1}`, which contains `W` and retracts
onto it, is bounded by a regular level of a function with compact sublevel sets that equals `r / f`
on the cylindrical end. The matching of the closed characteristics of the graph with the closed
Reeb orbits of `f α|∂W`, which that proof also uses, is not part of this file.

## Main definitions

* `TauCeti.liouvilleGraphFunction Z W f`: the function `x ↦ r(x) / f(π(x))`.

## Main results

* `TauCeti.IsLiouvilleCompletion.isLiouvilleDomain_setOf_liouvilleGraphFunction_le`: the domain
  bounded by a Liouville graph is a Liouville domain.
* `TauCeti.IsLiouvilleCompletion.frontier_setOf_liouvilleGraphFunction_le`: its boundary is the
  graph.
* `TauCeti.IsLiouvilleCompletion.isCompact_setOf_liouvilleGraphFunction_le`: the graph function
  has compact sublevel sets.
* `IsLiouvilleCompletion.exists_hasContractibleClosedCharacteristic_log_liouvilleGraphFunction`:
  almost existence near the graph gives a closed characteristic on the graph.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary E and its proof.
-/

public section

open Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Z : (x : M) → TangentSpace I x} {W : Set M} {f : M → ℝ}

variable (Z W f) in
/-- The **Liouville graph function** of `f` on a completion of the Liouville domain `W` with
Liouville field `Z`: the radial coordinate divided by the value of `f` at the Liouville
retraction. On the cylindrical end it is `r / f(y)` at the point `ψ_{log r}(y)`, `y ∈ ∂W`, so for
`f > 1` on `W` its level `1` is the Liouville graph of `f` over `∂W`
(`TauCeti.IsLiouvilleCompletion.setOf_liouvilleGraphFunction_eq_one`). -/
noncomputable def liouvilleGraphFunction (x : M) : ℝ :=
  liouvilleRadialCoordinate Z W x / f (liouvilleRetraction Z W x)

theorem liouvilleGraphFunction_apply (x : M) :
    liouvilleGraphFunction Z W f x =
      liouvilleRadialCoordinate Z W x / f (liouvilleRetraction Z W x) :=
  (rfl)

namespace IsLiouvilleCompletion

variable [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {x y : M} {t : ℝ}

/-! ### The Liouville graph function -/

section GraphFunction

variable (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
include h hZ

/-- On the Liouville domain, the Liouville graph function of `f` is `1 / f`. -/
theorem liouvilleGraphFunction_of_mem (hx : x ∈ W) : liouvilleGraphFunction Z W f x = (f x)⁻¹ := by
  rw [liouvilleGraphFunction_apply, h.liouvilleRetraction_of_mem hZ hx,
    (h.liouvilleRadialCoordinate_eq_one_iff hZ).2 hx, one_div]

/-- **The Liouville flow rescales the Liouville graph function** on the cylindrical end: if `x`
lies outside the interior of the Liouville domain and `0 ≤ log r(x) + t`, then
`F(ψ_t x) = e^t F(x)`. -/
theorem liouvilleGraphFunction_flowOf_of_notMem_interior (hx : x ∉ interior W)
    (ht : 0 ≤ Real.log (liouvilleRadialCoordinate Z W x) + t) :
    liouvilleGraphFunction Z W f (flowOf Z t x) = Real.exp t * liouvilleGraphFunction Z W f x := by
  have hr : liouvilleRadialCoordinate Z W (flowOf Z t x) =
      Real.exp t * liouvilleRadialCoordinate Z W x := by
    rw [← Real.exp_log (liouvilleRadialCoordinate_pos Z W (flowOf Z t x)),
      h.log_liouvilleRadialCoordinate_flowOf hZ hx ht, Real.exp_add,
      Real.exp_log (liouvilleRadialCoordinate_pos Z W x), mul_comm]
  rw [liouvilleGraphFunction_apply, liouvilleGraphFunction_apply, hr,
    h.liouvilleRetraction_flowOf_of_notMem_interior hZ hx ht, mul_div_assoc]

/-- **The Liouville graph lies on the level `1`.** At the point of the Liouville graph of `f` over a
boundary point `y` with `f(y) ≥ 1`, the Liouville graph function of `f` is `1`. -/
theorem liouvilleGraphFunction_liouvilleGraph (hy : y ∈ frontier W) (hfy : 1 ≤ f y) :
    liouvilleGraphFunction Z W f (liouvilleGraph Z id f y) = 1 := by
  have hpos : 0 < f y := zero_lt_one.trans_le hfy
  rw [liouvilleGraph_apply, id, liouvilleGraphFunction_apply,
    h.liouvilleRadialCoordinate_flowOf hZ hy (Real.log_nonneg hfy), Real.exp_log hpos,
    h.liouvilleRetraction_flowOf hZ hy (Real.log_nonneg hfy), div_self hpos.ne']

/-- The Liouville graph function of a function continuous and nowhere zero on the Liouville domain
is continuous. -/
theorem continuous_liouvilleGraphFunction (hf : ContinuousOn f W) (hf₀ : ∀ x ∈ W, f x ≠ 0) :
    Continuous (liouvilleGraphFunction Z W f) :=
  (h.continuous_liouvilleRadialCoordinate hZ).div
    (hf.comp_continuous (h.continuous_liouvilleRetraction hZ) (h.liouvilleRetraction_mem hZ))
    fun x ↦ hf₀ _ (h.liouvilleRetraction_mem hZ x)

/-- The Liouville graph function is `C^n` at every point outside the Liouville domain whose
retraction is a point where `f` is `C^n` and nonzero. -/
theorem contMDiffAt_liouvilleGraphFunction {n : ℕ∞} (hx : x ∉ W)
    (hf : ContMDiffAt I 𝓘(ℝ) n f (liouvilleRetraction Z W x))
    (hf₀ : f (liouvilleRetraction Z W x) ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) n (liouvilleGraphFunction Z W f) x :=
  (contDiffAt_fst.div contDiffAt_snd hf₀).contMDiffAt.comp x
    (((h.contMDiffAt_liouvilleRadialCoordinate hZ hx).of_le (by exact_mod_cast le_top)).prodMk_space
      (hf.comp x ((h.contMDiffAt_liouvilleRetraction hZ hx).of_le (by exact_mod_cast le_top))))

/-- The Liouville graph function is differentiable at every point outside the Liouville domain
whose retraction is a point where `f` is differentiable and nonzero. -/
theorem mdifferentiableAt_liouvilleGraphFunction (hx : x ∉ W)
    (hf : MDifferentiableAt I 𝓘(ℝ) f (liouvilleRetraction Z W x))
    (hf₀ : f (liouvilleRetraction Z W x) ≠ 0) :
    MDifferentiableAt I 𝓘(ℝ) (liouvilleGraphFunction Z W f) x := by
  have hdiv : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ p.1 / p.2)
      (liouvilleRadialCoordinate Z W x, f (liouvilleRetraction Z W x)) :=
    (contDiffAt_fst.div contDiffAt_snd hf₀ (n := 1)).differentiableAt one_ne_zero
  exact hdiv.comp_mdifferentiableAt (x := x)
    (((h.contMDiffAt_liouvilleRadialCoordinate hZ hx).mdifferentiableAt (by simp)).prodMk_space
      (hf.comp x ((h.contMDiffAt_liouvilleRetraction hZ hx).mdifferentiableAt (by simp))))

/-- **The Liouville field differentiates the Liouville graph function to itself** outside the
Liouville domain, `dF(Z) = F`, at a point whose retraction is a point where `f` is
differentiable. -/
theorem mvfderiv_liouvilleGraphFunction_apply (hx : x ∉ W)
    (hf : MDifferentiableAt I 𝓘(ℝ) f (liouvilleRetraction Z W x)) :
    mvfderiv I (liouvilleGraphFunction Z W f) x (Z x) = liouvilleGraphFunction Z W f x := by
  -- If `F` is not differentiable at `x`, then `f` vanishes at the retraction, and both sides are
  -- `0`.
  by_cases hFx : MDifferentiableAt I 𝓘(ℝ) (liouvilleGraphFunction Z W f) x
  swap
  · have hf₀ : f (liouvilleRetraction Z W x) = 0 := by
      by_contra hf₀
      exact hFx (h.mdifferentiableAt_liouvilleGraphFunction hZ hx hf hf₀)
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_zero_of_not_mdifferentiableAt hFx,
      liouvilleGraphFunction_apply, hf₀, div_zero]
    rfl
  -- Along the trajectory through `x`, `F(ψ_s x) = e^s F(x)` for `s > -log r(x)`, a neighbourhood
  -- of `0`.
  have hF : MDifferentiableAt I 𝓘(ℝ) (liouvilleGraphFunction Z W f) (flowOf Z 0 x) := by
    rwa [flowOf_zero Z]
  have hcurve := hasDerivAt_comp_flowOf ((h.contMDiff_of_interior_eq hZ).of_le (by simp))
    ((h.isCompleteVectorField hZ).mem_flowDomain 0 x) hF
  rw [flowOf_zero Z] at hcurve
  have hx' : x ∉ interior W := fun hi ↦ hx (interior_subset hi)
  have hτ : 0 < Real.log (liouvilleRadialCoordinate Z W x) :=
    Real.log_pos ((h.one_lt_liouvilleRadialCoordinate_iff hZ).2 hx)
  have heq : (liouvilleGraphFunction Z W f ∘ fun s ↦ flowOf Z s x) =ᶠ[𝓝 0]
      fun s ↦ Real.exp s * liouvilleGraphFunction Z W f x := by
    filter_upwards [Ioi_mem_nhds (neg_lt_zero.2 hτ)] with s hs
    exact h.liouvilleGraphFunction_flowOf_of_notMem_interior hZ hx'
      (by linarith [mem_Ioi.1 hs])
  refine hcurve.unique (HasDerivAt.congr_of_eventuallyEq ?_ heq)
  simpa using (Real.hasDerivAt_exp 0).mul_const (liouvilleGraphFunction Z W f x)

/-- **The sublevel sets of a Liouville graph function are compact**, when `f` is continuous and
positive on the Liouville domain: they lie in sublevel sets of the radial coordinate. -/
theorem isCompact_setOf_liouvilleGraphFunction_le (hf : ContinuousOn f W)
    (hf₀ : ∀ x ∈ W, 0 < f x) (c : ℝ) :
    IsCompact {x | liouvilleGraphFunction Z W f x ≤ c} := by
  obtain ⟨B, hB⟩ := h.isCompact.bddAbove_image hf
  refine (h.isCompact_setOf_liouvilleRadialCoordinate_le hZ (max c 0 * B)).of_isClosed_subset
    (isClosed_le (h.continuous_liouvilleGraphFunction hZ hf fun x hx ↦ (hf₀ x hx).ne')
      continuous_const) fun x (hx : _ ≤ c) ↦ ?_
  -- `r(x) ≤ c f(π x) ≤ max c 0 * B`, since `0 < f(π x) ≤ B`.
  have hπ := h.liouvilleRetraction_mem hZ x
  have hfx := hf₀ _ hπ
  have hfB : f (liouvilleRetraction Z W x) ≤ B := hB (mem_image_of_mem f hπ)
  rw [liouvilleGraphFunction_apply, div_le_iff₀ hfx] at hx
  exact hx.trans ((mul_le_mul_of_nonneg_right (le_max_left c 0) hfx.le).trans
    (mul_le_mul_of_nonneg_left hfB (le_max_right c 0)))

/-- **The Liouville deformation retraction does not increase the Liouville graph function**, when
`f` is nonnegative on the Liouville domain. So it maps every sublevel set `{F ≤ c}` and every strict
sublevel set `{F < c}` into itself. -/
theorem liouvilleGraphFunction_liouvilleRetractionHomotopy_le (hf₀ : ∀ x ∈ W, 0 ≤ f x)
    (p : unitInterval × M) :
    liouvilleGraphFunction Z W f (h.liouvilleRetractionHomotopy hZ p) ≤
      liouvilleGraphFunction Z W f p.2 := by
  rw [liouvilleGraphFunction_apply, liouvilleGraphFunction_apply,
    h.liouvilleRetraction_liouvilleRetractionHomotopy hZ]
  refine div_le_div_of_nonneg_right ?_ (hf₀ _ (h.liouvilleRetraction_mem hZ p.2))
  rw [← Real.log_le_log_iff (liouvilleRadialCoordinate_pos Z W _)
    (liouvilleRadialCoordinate_pos Z W _),
    h.log_liouvilleRadialCoordinate_liouvilleRetractionHomotopy hZ]
  exact mul_le_of_le_one_left (Real.log_nonneg (one_le_liouvilleRadialCoordinate Z W p.2))
    (sub_le_self _ (unitInterval.nonneg p.1))

end GraphFunction

/-! ### The domain bounded by a Liouville graph -/

section Domain

variable (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
include h hZ

/-- If `f > 1` on the Liouville domain, the Liouville graph function is less than `1` there. -/
private theorem liouvilleGraphFunction_lt_one_of_mem (hf1 : ∀ x ∈ W, 1 < f x) (hx : x ∈ W) :
    liouvilleGraphFunction Z W f x < 1 := by
  rw [h.liouvilleGraphFunction_of_mem hZ hx]
  exact inv_lt_one_of_one_lt₀ (hf1 x hx)

/-- **The level `1` of a Liouville graph function is the Liouville graph.** If `f > 1` on the
Liouville domain `W`, the points where the Liouville graph function of `f` equals `1` are exactly
the points `ψ_{log f(y)}(y)` of the Liouville graph of `f` over the boundary of `W`. -/
theorem setOf_liouvilleGraphFunction_eq_one (hf1 : ∀ x ∈ W, 1 < f x) :
    {x | liouvilleGraphFunction Z W f x = 1} = liouvilleGraph Z id f '' frontier W := by
  refine Subset.antisymm (fun x (hx : _ = 1) ↦ ?_) ?_
  · -- The point lies outside `W`, on the trajectory of `y = π(x)` at the time `log r(x)`, and
    -- `r(x) = f(y)`.
    have hxW : x ∉ W := fun hxW ↦ (h.liouvilleGraphFunction_lt_one_of_mem hZ hf1 hxW).ne hx
    have hπ := h.liouvilleRetraction_mem_frontier hZ fun hi ↦ hxW (interior_subset hi)
    have hf₀ := zero_lt_one.trans (hf1 _ (h.isClosed.frontier_subset hπ))
    rw [liouvilleGraphFunction_apply, div_eq_one_iff_eq hf₀.ne'] at hx
    refine ⟨liouvilleRetraction Z W x, hπ, ?_⟩
    rw [liouvilleGraph_apply, id, ← hx,
      h.flowOf_log_liouvilleRadialCoordinate_liouvilleRetraction hZ]
  · rintro _ ⟨y, hy, rfl⟩
    exact h.liouvilleGraphFunction_liouvilleGraph hZ hy
      (hf1 y (h.isClosed.frontier_subset hy)).le

/-- **The boundary of the domain bounded by a Liouville graph is the graph.** If `f` is continuous
on the Liouville domain `W` and greater than `1` there, the frontier of the sublevel set `{F ≤ 1}`
of the Liouville graph function is its level `1`, the Liouville graph of `f` over the boundary of
`W`: the Liouville flow multiplies `F` by `e^t`, so it pushes every point of the level out of the
sublevel set. -/
theorem frontier_setOf_liouvilleGraphFunction_le (hf : ContinuousOn f W)
    (hf1 : ∀ x ∈ W, 1 < f x) :
    frontier {x | liouvilleGraphFunction Z W f x ≤ 1} = liouvilleGraph Z id f '' frontier W := by
  rw [← h.setOf_liouvilleGraphFunction_eq_one hZ hf1]
  refine (frontier_le_subset_eq (h.continuous_liouvilleGraphFunction hZ hf
    fun x hx ↦ (zero_lt_one.trans (hf1 x hx)).ne') continuous_const).antisymm
    fun x (hx : _ = 1) ↦ ?_
  -- Flowing `x` forward for a small time `t > 0` gives `F = e^t > 1`.
  have hxW : x ∉ W := fun hxW ↦ (h.liouvilleGraphFunction_lt_one_of_mem hZ hf1 hxW).ne hx
  have h0 := Real.log_nonneg (one_le_liouvilleRadialCoordinate Z W x)
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  have hcont : Continuous fun t ↦ flowOf Z t x := by
    simp only [hψ]
    exact ψ.continuous continuous_id continuous_const
  have htend : Tendsto (fun t ↦ flowOf Z t x) (𝓝[>] 0) (𝓝 x) := by
    simpa [flowOf_zero Z] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (show x ∈ {x | liouvilleGraphFunction Z W f x ≤ 1} from hx.le),
    mem_closure_of_tendsto htend ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [mem_compl_iff, mem_ofPred_eq, not_le,
    h.liouvilleGraphFunction_flowOf_of_notMem_interior hZ (fun hi ↦ hxW (interior_subset hi))
      (by linarith), hx, mul_one]
  exact Real.one_lt_exp_iff.2 ht

/-- **The interior of the domain bounded by a Liouville graph** is the strict sublevel set
`{F < 1}` of the Liouville graph function, if `f` is continuous on the Liouville domain and
greater than `1` there. -/
theorem interior_setOf_liouvilleGraphFunction_le (hf : ContinuousOn f W)
    (hf1 : ∀ x ∈ W, 1 < f x) :
    interior {x | liouvilleGraphFunction Z W f x ≤ 1} =
      {x | liouvilleGraphFunction Z W f x < 1} := by
  rw [← self_sdiff_frontier, h.frontier_setOf_liouvilleGraphFunction_le hZ hf hf1,
    ← h.setOf_liouvilleGraphFunction_eq_one hZ hf1]
  ext x
  simp [lt_iff_le_and_ne]

/-- **The domain bounded by a Liouville graph contains the Liouville domain in its interior**, when
`f` is continuous on the Liouville domain and greater than `1` there. -/
theorem subset_interior_setOf_liouvilleGraphFunction_le (hf : ContinuousOn f W)
    (hf1 : ∀ x ∈ W, 1 < f x) : W ⊆ interior {x | liouvilleGraphFunction Z W f x ≤ 1} :=
  fun _ hx ↦ interior_maximal (fun _ hy ↦ le_of_lt hy)
    (isOpen_lt (h.continuous_liouvilleGraphFunction hZ hf
      fun x hx ↦ (zero_lt_one.trans (hf1 x hx)).ne') continuous_const)
    (h.liouvilleGraphFunction_lt_one_of_mem hZ hf1 hx)

/-- **The domain bounded by a Liouville graph is a Liouville domain.** Let `M` be a completion of
the Liouville domain `W` and let `f` be continuous on `W`, smooth along its boundary and
greater than `1` on `W`. Then the sublevel set `{F ≤ 1}` of the Liouville graph function of `f`,
bounded by the Liouville graph of `f` over the boundary of `W`, is a Liouville domain for the same
form and primitive. -/
theorem isLiouvilleDomain_setOf_liouvilleGraphFunction_le (hf : ContinuousOn f W)
    (hfs : ∀ y ∈ frontier W, ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) f y) (hf1 : ∀ x ∈ W, 1 < f x) :
    IsLiouvilleDomain ω α {x | liouvilleGraphFunction Z W f x ≤ 1} := by
  refine ⟨h.isNondegenerate, h.mextDeriv_eq,
    h.isCompact_setOf_liouvilleGraphFunction_le hZ hf (fun x hx ↦ zero_lt_one.trans (hf1 x hx)) 1,
    by simp [ModelWithCorners.interior_eq_univ], Z, h.contMDiff_of_interior_eq hZ, hZ,
    liouvilleGraphFunction Z W f, 1, h.continuous_liouvilleGraphFunction hZ hf
      fun x hx ↦ (zero_lt_one.trans (hf1 x hx)).ne', rfl, fun x hx ↦ ?_⟩
  -- On the level `1`, which lies outside `W`, the graph function is as smooth as `f` is along
  -- the boundary, and `dF(Z) = F = 1`.
  have hxW : x ∉ W := fun hxW ↦ (h.liouvilleGraphFunction_lt_one_of_mem hZ hf1 hxW).ne hx
  have hπ := h.liouvilleRetraction_mem_frontier hZ fun hi ↦ hxW (interior_subset hi)
  refine ⟨h.contMDiffAt_liouvilleGraphFunction hZ hxW (hfs _ hπ)
      (zero_lt_one.trans (hf1 _ (h.isClosed.frontier_subset hπ))).ne', ?_⟩
  rw [h.mvfderiv_liouvilleGraphFunction_apply hZ hxW
    ((hfs _ hπ).mdifferentiableAt (by simp)), hx]
  exact zero_lt_one

/-- **Almost existence gives existence on a Liouville graph.** Let `M` be a completion of the
Liouville domain `W`, with Liouville flow `ψ`, and let `f` be continuous on `W`, differentiable
along its boundary and greater than `1` on `W`. The logarithm of the Liouville graph function of
`f` is translated by the Liouville flow near its level `0`, the Liouville graph of `f` over the
boundary of `W`. So if this level has the contractible almost existence property in `U`, then it
carries a closed characteristic contractible in `ψ_t(U)` for some time `t`. -/
theorem exists_hasContractibleClosedCharacteristic_log_liouvilleGraphFunction
    (hf : ContinuousOn f W) (hfs : ∀ y ∈ frontier W, MDifferentiableAt I 𝓘(ℝ) f y)
    (hf1 : ∀ x ∈ W, 1 < f x) {U : Set M}
    (hae : ω.HasContractibleAlmostExistence U
      (fun x ↦ Real.log (liouvilleGraphFunction Z W f x)) 0) :
    ∃ t, ω.HasContractibleClosedCharacteristic (flowOf Z t '' U)
      (fun x ↦ Real.log (liouvilleGraphFunction Z W f x)) 0 := by
  -- On the compact set `W`, `log f ≥ ε` for some `ε > 0`, so `log F ≤ -ε` there.
  obtain ⟨ε, hε, hεf⟩ := h.isCompact.exists_forall_le'
    (hf.log fun x hx ↦ (zero_lt_one.trans (hf1 x hx)).ne') fun x hx ↦ Real.log_pos (hf1 x hx)
  have hπW (x : M) := h.liouvilleRetraction_mem hZ x
  have hfπ (x : M) : 0 < f (liouvilleRetraction Z W x) := zero_lt_one.trans (hf1 _ (hπW x))
  have hFpos (x : M) : 0 < liouvilleGraphFunction Z W f x :=
    div_pos (liouvilleRadialCoordinate_pos Z W x) (hfπ x)
  have hlog (x : M) : Real.log (liouvilleGraphFunction Z W f x) =
      Real.log (liouvilleRadialCoordinate Z W x) - Real.log (f (liouvilleRetraction Z W x)) :=
    Real.log_div (liouvilleRadialCoordinate_pos Z W x).ne' (hfπ x).ne'
  -- On the band `-ε < log F < ε`, the points lie outside `W`.
  have hband (x : M) (hx : Real.log (liouvilleGraphFunction Z W f x) ∈ Ioo (0 - ε) (0 + ε)) :
      x ∉ W := fun hxW ↦ by
    have := hx.1
    rw [h.liouvilleGraphFunction_of_mem hZ hxW, Real.log_inv, zero_sub, neg_lt_neg_iff] at this
    exact (hεf x hxW).not_gt this
  -- Outside `W` the graph function is differentiable and positive, so is its logarithm.
  have hF (x : M) (hx : Real.log (liouvilleGraphFunction Z W f x) ∈ Ioo (0 - ε) (0 + ε)) :
      MDifferentiableAt I 𝓘(ℝ) (fun x ↦ Real.log (liouvilleGraphFunction Z W f x)) x := by
    have hxW := hband x hx
    have hπ := h.liouvilleRetraction_mem_frontier hZ fun hi ↦ hxW (interior_subset hi)
    exact (Real.differentiableAt_log (hFpos x).ne').comp_mdifferentiableAt
      (h.mdifferentiableAt_liouvilleGraphFunction hZ hxW (hfs _ hπ) (hfπ x).ne')
  -- The trajectory stays on the end, `0 ≤ log r(x) + t`, since `log F(x) + t > -ε` and
  -- `log f(π x) ≥ ε`; there the flow multiplies `F` by `e^t`.
  have hFZ (x : M) (t : ℝ) (hx : Real.log (liouvilleGraphFunction Z W f x) ∈ Ioo (0 - ε) (0 + ε))
      (hxt : Real.log (liouvilleGraphFunction Z W f x) + t ∈ Ioo (0 - ε) (0 + ε)) :
      Real.log (liouvilleGraphFunction Z W f (flowOf Z t x)) =
        Real.log (liouvilleGraphFunction Z W f x) + t := by
    have hx' : x ∉ interior W := fun hi ↦ hband x hx (interior_subset hi)
    have hπ := hεf _ (hπW x)
    have ht : 0 ≤ Real.log (liouvilleRadialCoordinate Z W x) + t := by
      have := hxt.1
      rw [hlog] at this
      linarith
    rw [h.liouvilleGraphFunction_flowOf_of_notMem_interior hZ hx' ht,
      Real.log_mul (Real.exp_pos t).ne' (hFpos x).ne', Real.log_exp, add_comm]
  obtain ⟨t, -, ht⟩ :=
    (h.isLiouvilleVectorField hZ).exists_hasContractibleClosedCharacteristic_image_flowOf
      h.isNondegenerate (h.isCompleteVectorField hZ) (h.contMDiff_of_interior_eq hZ) hε hF hFZ hae
  exact ⟨t, ht⟩

/-- **Almost existence gives existence on a Liouville graph**, for contractibility in the
completion: under the hypotheses of
`IsLiouvilleCompletion.exists_hasContractibleClosedCharacteristic_log_liouvilleGraphFunction`, if
the level `0` of `log F` has the contractible almost existence property in `M`, then the
Liouville graph of `f` carries a closed characteristic contractible in `M`. -/
theorem hasContractibleClosedCharacteristic_univ_log_liouvilleGraphFunction
    (hf : ContinuousOn f W) (hfs : ∀ y ∈ frontier W, MDifferentiableAt I 𝓘(ℝ) f y)
    (hf1 : ∀ x ∈ W, 1 < f x)
    (hae : ω.HasContractibleAlmostExistence univ
      (fun x ↦ Real.log (liouvilleGraphFunction Z W f x)) 0) :
    ω.HasContractibleClosedCharacteristic univ
      (fun x ↦ Real.log (liouvilleGraphFunction Z W f x)) 0 := by
  obtain ⟨t, ht⟩ :=
    h.exists_hasContractibleClosedCharacteristic_log_liouvilleGraphFunction hZ hf hfs
      hf1 hae
  rwa [image_univ_of_surjective (flowOf_surjective ((h.contMDiff_of_interior_eq hZ).of_le
    (by simp)) (h.isCompleteVectorField hZ) t)] at ht

end Domain

end IsLiouvilleCompletion

end TauCeti
