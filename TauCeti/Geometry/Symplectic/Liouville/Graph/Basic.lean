/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Flow.Out
public import TauCeti.Geometry.Symplectic.Liouville.Scaling
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reeb.Basic
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Contact.ClosedOrbit.Rescale
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Contact.Transition

/-!
# Graphs over the boundary of a Liouville domain

Let `Z` be a smooth complete vector field on a manifold `M`, the Liouville field of a one-form `α`,
`ι_Z dα = α`, with flow `φ`, and let `ι : S → M` be a smooth map, typically the inclusion of the
boundary `Σ` of a Liouville domain `W`. For a smooth positive function `f` on `S`, the
**Liouville graph** of `f` (`TauCeti.liouvilleGraph`) is the map

`j_f : S → M`,  `j_f(s) = φ_{log f(s)}(ι s)`,

which pushes each point of `ι` along its Liouville trajectory to the radius `r = f(s)` of the
symplectization `((0, ∞) × Σ, d(r α|_Σ))`, the coordinate `r` being `eᵗ` for the time `t` of the
flow. Since the flow rescales the primitive and the primitive vanishes on its Liouville field, the
graph pulls `α` back to `f` times its restriction to `ι`
(`TauCeti.mpullback_liouvilleGraph_apply`):

`j_f^* α = f ι^* α`.

So every contact form `f ι^* α` defining the same cooriented contact structure as `ι^* α` is the
restriction of the single ambient primitive `α` to the graph `j_f`. This is the graph
construction of Barraud, Damian, Humilière and Oancea in their proof of Corollary E, which turns
a closed Reeb orbit of `f ι^* α` into a closed characteristic of the hypersurface `j_f(S)`.

The graph keeps the transversality of the Liouville field: if `ι` is an immersion and `Z` is
transverse to it, then `j_f` is an immersion (`TauCeti.injective_mfderiv_liouvilleGraph`) and `Z`
is transverse to it (`TauCeti.isTransverseAlong_liouvilleGraph`). Indeed the differential of
`j_f` at `s` is `w ↦ dφₜ(d(log f)(w) Z + dι(w))`, and `dφₜ` carries `Z` to `Z`. For the boundary
of a Liouville domain `W`, along which `Z` points outwards, transversality along `ι` is automatic
(`TauCeti.IsLiouvilleDomain.isTransverseAlong`), and the graph is of restricted contact type with
the same primitive and the same Liouville field
(`TauCeti.IsLiouvilleDomain.isRestrictedContactType_liouvilleGraph`); on a completion of `W` the
restriction of the primitive to it is a contact form
(`TauCeti.IsLiouvilleCompletion.isContactForm_mpullback_liouvilleGraph`). For `f > 1` it lies
outside `W` (`TauCeti.IsLiouvilleDomain.liouvilleGraph_notMem`), it is injective when `ι` is
(`TauCeti.IsLiouvilleDomain.injective_liouvilleGraph`), hence a closed embedding when `S` is
compact (`TauCeti.IsLiouvilleDomain.isClosedEmbedding_liouvilleGraph`). On a completion of `W`,
the graph over a boundary point `ι s` with `f s ≥ 1` lies on the level `f s` of the radial
coordinate (`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_liouvilleGraph`). Moving `f`
linearly to the constant `1` deforms the graph back to `ι` through the graphs of the functions
`(1 - τ) f + τ` (`TauCeti.liouvilleGraphHomotopy`).

Closed characteristics of the graph come from closed Reeb orbits of `f ι^* α`. Let `S` be compact,
of one dimension less than `M`, let `ι` be an injective immersion into the boundary of `W`, and let
the graph be a regular level `K⁻¹(c)`. If this level carries a closed characteristic, contractible
in some set, then the contact form `j_f^* α = f ι^* α` has a closed Reeb orbit `γ` whose loop
`ι ∘ γ` on `Σ`, run at another speed, is contractible in `M`; see
`IsLiouvilleDomain.exists_isMIntegralCurve_reebVectorField_of_hasContractibleClosedCharacteristic`.
This is how Corollary E brings a closed characteristic of the hypersurface `Σ_α = j_f(S)` back to
a closed Reeb orbit of the contact form `f ι^* α` on `Σ`, contractible in the ambient manifold.

Every contact form `β` defining the contact structure `ker ι^* α`, with either coorientation, is
of this form up to a nonzero constant factor on each component of `S`: when `S` is compact,
`c β = f ι^* α` for a locally constant `c` and a smooth `f > 1`
(`TauCeti.SmoothForm.exists_isLocallyConstant_smul_eq_smul`), and this rescaling only changes the
speed and possibly the direction of the Reeb orbits. So if the graph of every smooth `f > 1` is a
regular level of a `C²` function and carries a closed characteristic contractible in `V`, every
such `β` has a closed Reeb orbit whose loop on `Σ` is contractible in `M`; see
`IsLiouvilleDomain.exists_isMIntegralCurve_reebVectorField_of_kerDistribution_eq`.

## Main definitions

* `TauCeti.liouvilleGraph Z ι f`: the map `s ↦ φ_{log f(s)}(ι s)`.
* `TauCeti.liouvilleGraphHomotopy`: the homotopy from `j_f` to `ι` through the graphs of the
  functions `(1 - τ) f + τ`.

## Main results

* `TauCeti.mfderiv_liouvilleGraph_apply`: the differential `w ↦ dφₜ(d(log f)(w) Z + dι(w))`.
* `TauCeti.mpullback_liouvilleGraph_apply`: `j_f^* α = f ι^* α`.
* `TauCeti.injective_mfderiv_liouvilleGraph`, `TauCeti.isTransverseAlong_liouvilleGraph`: the
  graph of an immersion transverse to `Z` is an immersion transverse to `Z`.
* `TauCeti.IsLiouvilleDomain.isRestrictedContactType_liouvilleGraph`: a graph over the boundary of
  a Liouville domain is of restricted contact type.
* `TauCeti.IsLiouvilleCompletion.isContactForm_mpullback_liouvilleGraph`: on a completion, the
  primitive restricts to a contact form on a graph over the boundary.
* `TauCeti.IsLiouvilleDomain.liouvilleGraph_notMem`,
  `TauCeti.IsLiouvilleDomain.injective_liouvilleGraph`,
  `TauCeti.IsLiouvilleDomain.isClosedEmbedding_liouvilleGraph`: for `f > 1` it is an injective map
  into the complement of the domain, and a closed embedding of a compact boundary.
* `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_liouvilleGraph`: on a completion, for a
  boundary point `ι s` and `f s ≥ 1`, the radial coordinate of `j_f(s)` is `f(s)`.
* `IsLiouvilleDomain.exists_isMIntegralCurve_reebVectorField_of_hasContractibleClosedCharacteristic`
  in `TauCeti`: a contractible closed characteristic of a graph which is a regular level comes
  from a closed Reeb orbit `γ` of `f ι^* α` whose loop `ι ∘ γ` is contractible in `M`.
* `IsLiouvilleDomain.exists_isMIntegralCurve_reebVectorField_of_kerDistribution_eq` in
  `TauCeti`: if the graphs of all smooth `f > 1` are regular levels of `C²` functions and carry
  contractible closed characteristics, every one-form with the kernel of `ι^* α` has a closed Reeb
  orbit whose loop on `Σ` is contractible in `M`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary E and its proof (the graph of a
  contact form in the symplectization of a hypersurface of restricted contact type).
-/

public section

open Function Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Z : (x : M) → TangentSpace I x} {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {ι : S → M} {f : S → ℝ}

variable (Z ι f) in
/-- The **Liouville graph** of a function `f` over a map `ι : S → M`: the point `ι s` flowed along
the vector field `Z` for the time `log f(s)`. For the Liouville field of a primitive `α` and
positive `f`, it pulls `α` back to `f ι^* α` (`TauCeti.mpullback_liouvilleGraph_apply`). -/
noncomputable def liouvilleGraph (s : S) : M :=
  flowOf Z (Real.log (f s)) (ι s)

@[simp]
theorem liouvilleGraph_apply (s : S) : liouvilleGraph Z ι f s = flowOf Z (Real.log (f s)) (ι s) :=
  (rfl)

/-- The Liouville graph as a function: `s ↦ φ_{log f(s)}(ι s)`. -/
theorem liouvilleGraph_def : liouvilleGraph Z ι f = fun s ↦ flowOf Z (Real.log (f s)) (ι s) :=
  funext liouvilleGraph_apply

/-- The Liouville graph of the constant function `1` is the map itself. -/
@[simp]
theorem liouvilleGraph_one : liouvilleGraph Z ι (fun _ ↦ 1) = ι :=
  funext fun s ↦ by simp

section Domain

variable [IsManifold I (⊤ : ℕ∞) M] [T2Space M] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1}
  {W : Set M}

namespace IsLiouvilleDomain

variable [I.Boundaryless]

/-- **A graph over the boundary of a Liouville domain lies outside the domain.** If `ι s` is not an
interior point of the Liouville domain `W` and `f s > 1`, then the Liouville graph of `f` at `s`,
the point `ι s` flowed for the positive time `log f(s)`, is not in `W`. -/
theorem liouvilleGraph_notMem (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) {s : S}
    (hp : (Real.log (f s), ι s) ∈ flowDomain Z) (hιW : ι s ∉ interior W) (hfs : 1 < f s) :
    liouvilleGraph Z ι f s ∉ W :=
  h.flowOf_notMem hZ hιW (Real.log_pos hfs) hp

/-- **A graph over the boundary of a Liouville domain is injective** when the boundary map `ι` is,
since the Liouville flow-out `(t, s) ↦ φₜ(ι s)` of the boundary is injective. -/
theorem injective_liouvilleGraph (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hc : IsCompleteVectorField Z) (hι : Injective ι)
    (hιW : ∀ s, ι s ∈ frontier W) : Injective (liouvilleGraph Z ι f) := fun s s' hss' ↦
  congrArg Prod.snd (h.injective_flowOf_comp hZ hc hι hιW
    (a₁ := (Real.log (f s), s)) (a₂ := (Real.log (f s'), s')) hss')

end IsLiouvilleDomain

/-- **A graph over the boundary lies on the level `f` of the radial coordinate.** On a completion of
the Liouville domain `W`, the radial coordinate of the Liouville graph of `f` at a boundary point
`ι s` is `f s`, as soon as `f s ≥ 1`. -/
theorem IsLiouvilleCompletion.liouvilleRadialCoordinate_liouvilleGraph [FiniteDimensional ℝ E]
    [I.Boundaryless] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) {s : S} (hιW : ι s ∈ frontier W) (hfs : 1 ≤ f s) :
    liouvilleRadialCoordinate Z W (liouvilleGraph Z ι f s) = f s := by
  rw [liouvilleGraph_apply, h.liouvilleRadialCoordinate_flowOf hZ hιW (Real.log_nonneg hfs),
    Real.exp_log (zero_lt_one.trans_le hfs)]

end Domain

variable [TopologicalSpace S] [ChartedSpace H' S]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]

section Flow

variable [IsManifold I 1 M] (hZ : ContMDiff I I.tangent 1 (T% Z)) (hc : IsCompleteVectorField Z)
include hZ hc

/-- The Liouville graph of a continuous nowhere vanishing function over a continuous map is
continuous. -/
theorem continuous_liouvilleGraph (hι : Continuous ι) (hf : Continuous f) (hf₀ : ∀ s, f s ≠ 0) :
    Continuous (liouvilleGraph Z ι f) := by
  rw [liouvilleGraph_def]
  exact (continuous_flowOf_comp hc hZ hι).comp ((hf.log hf₀).prodMk continuous_id)

/-- **The radial homotopy.** For a continuous positive function `f`, the Liouville graphs of the
functions `(1 - τ) f + τ`, `τ ∈ [0, 1]`, form a homotopy from the Liouville graph of `f` to the map
`ι` itself, the graph of the constant `1`. Composed with a loop of `S`, it joins the loop of the
graph to the loop of `ι` along the trajectories of `Z`. -/
noncomputable def liouvilleGraphHomotopy (hι : Continuous ι) (hf : Continuous f)
    (hf₀ : ∀ s, 0 < f s) :
    ContinuousMap.Homotopy ⟨liouvilleGraph Z ι f,
      continuous_liouvilleGraph hZ hc hι hf fun s ↦ (hf₀ s).ne'⟩ ⟨ι, hι⟩ where
  toFun := liouvilleGraph Z (ι ∘ Prod.snd) fun p : unitInterval × S ↦ (1 - (p.1 : ℝ)) * f p.2 + p.1
  continuous_toFun := by
    have hpos (p : unitInterval × S) : 0 < (1 - (p.1 : ℝ)) * f p.2 + p.1 := by
      nlinarith [unitInterval.nonneg p.1, hf₀ p.2,
        mul_nonneg (sub_nonneg.2 (unitInterval.le_one p.1)) (hf₀ p.2).le]
    exact continuous_liouvilleGraph hZ hc (hι.comp continuous_snd) (by fun_prop)
      fun p ↦ (hpos p).ne'
  map_zero_left s := by simp
  map_one_left s := by simp

@[simp]
theorem liouvilleGraphHomotopy_apply (hι : Continuous ι) (hf : Continuous f) (hf₀ : ∀ s, 0 < f s)
    (p : unitInterval × S) :
    liouvilleGraphHomotopy hZ hc hι hf hf₀ p =
      liouvilleGraph Z ι (fun s ↦ (1 - (p.1 : ℝ)) * f s + p.1) p.2 :=
  (rfl)

omit hc in
/-- **The differential of the Liouville graph.** At a point `s` where `ι` and `f` are
differentiable and `f s ≠ 0`, it sends `w` to `dφₜ(d(log f)(w) Z + dι(w))`, where
`t = log f(s)`, provided `ι s` stays in the flow domain up to time `t`. -/
theorem mfderiv_liouvilleGraph_apply {s : S} (hp : (Real.log (f s), ι s) ∈ flowDomain Z)
    (hι : MDifferentiableAt J I ι s) (hf : MDifferentiableAt J 𝓘(ℝ) f s) (hf₀ : f s ≠ 0)
    (w : TangentSpace J s) :
    mfderiv J I (liouvilleGraph Z ι f) s w =
      mfderiv I I (flowOf Z (Real.log (f s))) (ι s)
        (mvfderiv J (fun s ↦ Real.log (f s)) s w • Z (ι s) + mfderiv J I ι s w) := by
  have hτ : MDifferentiableAt J 𝓘(ℝ) (fun s ↦ Real.log (f s)) s :=
    (Real.differentiableAt_log hf₀).comp_mdifferentiableAt hf
  rw [liouvilleGraph_def, mfderiv_flowOf_comp_prodMk_apply hZ hτ hι hp w,
    map_add, map_smul, mfderiv_flowOf_apply_self hZ hp]

/-- **The graph of an immersion is an immersion.** Let `ι` be transverse to `Z`, and at `s` let
`ι` have injective differential, `f` be differentiable and `f s ≠ 0`. Then the Liouville graph of
`f` over `ι` has injective differential at `s`. -/
theorem injective_mfderiv_liouvilleGraph {s : S} (hι : MDifferentiableAt J I ι s)
    (hf : MDifferentiableAt J 𝓘(ℝ) f s) (hf₀ : f s ≠ 0) (hιs : Injective (mfderiv J I ι s))
    (hZι : IsTransverseAlong J Z ι) : Injective (mfderiv J I (liouvilleGraph Z ι f) s) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  rw [mfderiv_liouvilleGraph_apply hZ (hc.mem_flowDomain _ _) hι hf hf₀] at hw
  exact (hZι.eq_zero_of_smul_add_eq_zero hιs <| injective_mfderiv_flowOf hZ hc
    (Real.log (f s)) (ι s) (hw.trans (map_zero _).symm)).2

/-- **The graph keeps transversality.** If `ι` is a differentiable immersion transverse to `Z`,
then `Z` is transverse to the Liouville graph of every differentiable nowhere vanishing function
over `ι`. -/
theorem isTransverseAlong_liouvilleGraph (hι : MDifferentiable J I ι)
    (hf : MDifferentiable J 𝓘(ℝ) f) (hf₀ : ∀ s, f s ≠ 0)
    (hιs : ∀ s, Injective (mfderiv J I ι s)) (hZι : IsTransverseAlong J Z ι) :
    IsTransverseAlong J Z (liouvilleGraph Z ι f) := by
  refine isTransverseAlong_iff.2 fun s ⟨w, hw⟩ ↦ ?_
  rw [ContinuousLinearMap.coe_coe] at hw
  set t := Real.log (f s)
  set a := mvfderiv J (fun s ↦ Real.log (f s)) s w
  -- `Z` at the graph point is the image of `Z (ι s)` under `dφₜ`.
  have hZt : Z (liouvilleGraph Z ι f s) = mfderiv I I (flowOf Z t) (ι s) (Z (ι s)) :=
    (mfderiv_flowOf_apply_self hZ (hc.mem_flowDomain t (ι s))).symm
  rw [mfderiv_liouvilleGraph_apply hZ (hc.mem_flowDomain t (ι s)) (hι s) (hf s) (hf₀ s), hZt] at hw
  have h : (a - 1) • Z (ι s) + mfderiv J I ι s w = 0 := by
    refine injective_mfderiv_flowOf hZ hc t (ι s) ?_
    rw [liouvilleGraph_apply] at hw
    -- Keep `mvfderiv` folded, so that its value stays a real scalar.
    simpa [-mvfderiv_apply_eq_mfderiv_apply, sub_smul, sub_add_eq_add_sub, map_sub, a] using
      sub_eq_zero.2 hw
  obtain ⟨ha, hw0⟩ := hZι.eq_zero_of_smul_add_eq_zero (hιs s) h
  subst hw0
  rw [show a = 0 from map_zero _, zero_sub] at ha
  exact absurd ha (by norm_num)

end Flow

/-- **The graph restricts the primitive to `f` times its restriction.** If `Z` is the Liouville
field of a differentiable one-form `α`, `ι_Z dα = α`, then the Liouville graph
`s ↦ φ_{log f(s)}(ι s)` pulls `α` back to `f ι^* α` at every point `s` where `ι` and `f` are
differentiable, `f s > 0` and `ι s` stays in the flow domain up to time `log f(s)`: the flow
rescales the primitive by `e^{log f} = f`, and the primitive vanishes on its Liouville field. For a
smooth form `α`, apply it to `α.val` with `α.mdifferentiable`. -/
theorem mpullback_liouvilleGraph_apply [IsManifold I 2 M] (hZ : ContMDiff I I.tangent 1 (T% Z))
    {α : RoughForm I M ℝ 1} {σ : RoughForm I M ℝ 2}
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ Bundle.TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)))
    (hdα : mextDeriv α = σ) (hZα : σ.interior Z = α) {s : S}
    (hp : (Real.log (f s), ι s) ∈ flowDomain Z) (hι : MDifferentiableAt J I ι s)
    (hf : MDifferentiableAt J 𝓘(ℝ) f s) (hfs : 0 < f s) :
    mpullback J I (liouvilleGraph Z ι f) α s = f s • mpullback J I ι α s := by
  -- The flow rescales the primitive: `(φₜ^* α)_x = eᵗ α_x`.
  have hscale := mpullback_flowOf_apply_eq_exp_smul_of_interior_eq hZ hα hdα hZα hp
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  have hs := congrArg (fun β ↦ β ![mvfderiv J (fun s ↦ Real.log (f s)) s w • Z (ι s) +
    mfderiv J I ι s w]) hscale
  simp only [mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    Matrix.cons_val_fin_one, ← Matrix.vec_single_eq_const] at hs ⊢
  -- Differentiate the graph, then use that `α` is linear and vanishes on `Z`.
  rw [mfderiv_liouvilleGraph_apply hZ hp hι hf hfs.ne', liouvilleGraph_apply, hs]
  simp [-mvfderiv_apply_eq_mfderiv_apply, Real.exp_log hfs, ContinuousAlternatingMap.vecCons_add,
    ContinuousAlternatingMap.vecCons_smul, RoughForm.apply_eq_zero_of_interior_eq hZα]

/-- The Liouville graph of a `C^n` nowhere vanishing function over a `C^n` map, for a complete
`C^n` field `Z` and `1 ≤ n`, is `C^n`. -/
theorem contMDiff_liouvilleGraph {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I 1 M] [IsManifold I n M]
    (hZ : ContMDiff I I.tangent n (T% Z)) (hc : IsCompleteVectorField Z) (hι : ContMDiff J I n ι)
    (hf : ContMDiff J 𝓘(ℝ) n f) (hf₀ : ∀ s, f s ≠ 0) :
    ContMDiff J I n (liouvilleGraph Z ι f) := fun _ ↦
  contMDiffAt_flowOf_comp hn hZ ((hf.log hf₀).contMDiffAt) hι.contMDiffAt (hc.mem_flowDomain _ _)

namespace IsLiouvilleDomain

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M}

/-- **A graph over the boundary of a Liouville domain is of restricted contact type.** Let `ι` be a
differentiable immersion into the frontier of a Liouville domain `W` whose Liouville field `Z` is
complete. For every differentiable nowhere vanishing function `f`, the Liouville graph of `f` over
`ι` is of restricted contact type, with the same primitive `α` and the same Liouville field `Z`.
For positive `f` its restriction of `α` is `f ι^* α` (`TauCeti.mpullback_liouvilleGraph_apply`). -/
theorem isRestrictedContactType_liouvilleGraph (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hc : IsCompleteVectorField Z)
    (hι : MDifferentiable J I ι) (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hιW : ∀ s, ι s ∈ frontier W) (hf : MDifferentiable J 𝓘(ℝ) f) (hf₀ : ∀ s, f s ≠ 0) :
    IsRestrictedContactType J ω.val α.val (liouvilleGraph Z ι f) :=
  isRestrictedContactType_iff.2 ⟨h.mextDeriv_eq, Z, h.contMDiff_of_interior_eq hZ, hZ,
    isTransverseAlong_liouvilleGraph ((h.contMDiff_of_interior_eq hZ).of_le (by simp)) hc hι hf
      hf₀ hιs (h.isTransverseAlong hZ hι hιW)⟩

/-- **A graph over a compact boundary is a closed embedding.** If `S` is compact and `ι` is an
injective continuous map into the frontier of a Liouville domain whose Liouville field `Z` is
smooth and complete, then the Liouville graph of every continuous nowhere vanishing function over
`ι` is a closed embedding of `S` into `M`. -/
theorem isClosedEmbedding_liouvilleGraph [CompactSpace S] (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hc : IsCompleteVectorField Z) (hι : Continuous ι)
    (hιi : Injective ι) (hιW : ∀ s, ι s ∈ frontier W) (hf : Continuous f) (hf₀ : ∀ s, f s ≠ 0) :
    Topology.IsClosedEmbedding (liouvilleGraph Z ι f) :=
  (continuous_liouvilleGraph ((h.contMDiff_of_interior_eq hZ).of_le (by simp)) hc hι hf
    hf₀).isClosedEmbedding (h.injective_liouvilleGraph hZ hc hιi hιW)

/-! ### Closed characteristics of a graph and closed Reeb orbits -/

section ClosedCharacteristic

variable [BoundarylessManifold J S] [CompactSpace S] [IsManifold J (⊤ : ℕ∞) S]

/-- A contractible map into a set, with values on a Liouville graph over a compact boundary, lifts
through the graph to a map into `S` whose composite with `ι` is contractible in `M`: the radial
homotopy joins the two composites. -/
private theorem exists_nullhomotopic_of_forall_mem_range_liouvilleGraph
    (h : IsLiouvilleDomain ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hc : IsCompleteVectorField Z) (hι : Continuous ι) (hιi : Injective ι)
    (hιW : ∀ s, ι s ∈ frontier W) (hf : Continuous f) (hf₀ : ∀ s, 0 < f s) {X : Type*}
    [TopologicalSpace X] {V : Set M} (g : C(X, V)) (hg : g.Nullhomotopic)
    (hgj : ∀ x, (g x : M) ∈ range (liouvilleGraph Z ι f)) :
    ∃ ℓ : C(X, S), (∀ x, liouvilleGraph Z ι f (ℓ x) = g x) ∧
      (ContinuousMap.comp ⟨ι, hι⟩ ℓ).Nullhomotopic := by
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
  choose ℓ hℓ using hgj
  have hℓc : Continuous ℓ :=
    (h.isClosedEmbedding_liouvilleGraph hZ hc hι hιi hιW hf fun s ↦ (hf₀ s).ne').isInducing
      |>.continuous_iff.2 <| (continuous_subtypeVal.comp g.continuous).congr fun x ↦ (hℓ x).symm
  obtain ⟨y, hy⟩ := hg.comp_right ⟨Subtype.val, continuous_subtypeVal⟩
  refine ⟨⟨ℓ, hℓc⟩, hℓ, y, (ContinuousMap.Homotopic.symm ⟨(liouvilleGraphHomotopy hZ1 hc hι hf
    hf₀).compContinuousMap ⟨ℓ, hℓc⟩⟩).trans ?_⟩
  convert hy using 1
  ext x
  exact hℓ x

/-- **Closed characteristics of a Liouville graph come from contractible closed Reeb orbits.**
Let `ι` be a smooth injective immersion of a compact manifold `S`, of one dimension less than `M`,
into the frontier of a Liouville domain `W` with complete Liouville field `Z`, let `f > 0` be
smooth, and let the Liouville graph `j_f` of `f` over `ι` be the regular level `K⁻¹(c)` of a `C²`
function `K`. If this level carries a closed characteristic, contractible in some set `V`, then
the contact form `j_f^* α`, which is `f ι^* α` (`TauCeti.mpullback_liouvilleGraph_apply`), has a
closed Reeb orbit `γ` whose loop `ι ∘ γ` on the boundary of `W`, run at another speed, is
contractible in `M`.

This is the step of the proof of Corollary E of Barraud–Damian–Humilière–Oancea that brings a
closed characteristic of the graph `Σ_α` back to a closed Reeb orbit of the contact form
`f ι^* α` on `Σ`. -/
theorem exists_isMIntegralCurve_reebVectorField_of_hasContractibleClosedCharacteristic
    (h : IsLiouvilleDomain ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hc : IsCompleteVectorField Z) (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιi : Injective ι)
    (hιs : ∀ s, Injective (mfderiv J I ι s)) (hιW : ∀ s, ι s ∈ frontier W)
    (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (hf₀ : ∀ s, 0 < f s)
    (hdim : Module.finrank ℝ E' + 1 = Module.finrank ℝ E)
    {K : M → ℝ} {c : ℝ} (hK : ContMDiff I 𝓘(ℝ) 2 K) (hreg : IsRegularValue I 𝓘(ℝ) K c)
    (hlevel : {x | K x = c} = range (liouvilleGraph Z ι f)) {V : Set M}
    (hV : ω.HasContractibleClosedCharacteristic V K c) :
    ∃ γ : ℝ → S, IsMIntegralCurve γ (SmoothForm.mpullback (liouvilleGraph Z ι f)
        (contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ) hc hι hf
          fun s ↦ (hf₀ s).ne') α).reebVectorField ∧ (∃ τ, τ ≠ 0 ∧ Periodic γ τ) ∧
      ∃ (T : ℝ) (ψ : ℝ ≃ₜ ℝ), 0 < T ∧
        ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = ι (γ (ψ t)) := by
  have : T2Space S := T2Space.of_injective_continuous hιi hι.continuous
  set j := liouvilleGraph Z ι f
  have hZs := h.contMDiff_of_interior_eq hZ
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := hZs.of_le (by simp)
  have hj : ContMDiff J I (⊤ : ℕ∞) j :=
    contMDiff_liouvilleGraph le_top hZs hc hι hf fun s ↦ (hf₀ s).ne'
  have hιd : MDifferentiable J I ι := hι.mdifferentiable (by simp)
  have hfd : MDifferentiable J 𝓘(ℝ) f := hf.mdifferentiable (by simp)
  have hjs (s : S) : Injective (mfderiv J I j s) :=
    injective_mfderiv_liouvilleGraph hZ1 hc (hιd s) (hfd s) (hf₀ s).ne' (hιs s)
      (h.isTransverseAlong hZ hιd hιW)
  have hji : Injective j := h.injective_liouvilleGraph hZ hc hιi hιW
  -- The graph carries the contact form `j^* α`, and its negative `j^* (-α)`, with `d(-α) = -ω`.
  have hα : (SmoothForm.mpullback j hj α).IsContactForm :=
    (h.isRestrictedContactType_liouvilleGraph hZ hc hιd hιs hιW hfd fun s ↦ (hf₀ s).ne')
      |>.isContactType.isContactForm_mpullback h.isNondegenerate hj hjs hdim
  have hαneg : (SmoothForm.mpullback j hj (-α)).IsContactForm :=
    (SmoothForm.isContactForm_mpullback_neg_iff hj α).2 hα
  have hdθ (s : S) : mextDeriv (-α).val (j s) = -ω.val (j s) := by
    rw [NegMemClass.coe_neg, mextDeriv_neg, h.mextDeriv_eq, Pi.neg_apply]
  have hKj (s : S) : (mfderiv J I j s).range = (mvfderiv I K (j s)).ker := by
    have hjK : ∀ s, K (j s) = c := fun s ↦ (hlevel.symm ▸ mem_range_self s : j s ∈ {x | K x = c})
    rw [ker_mvfderiv]
    exact (hreg.isRegularPoint (hjK s)).range_mfderiv_eq_ker_mfderiv
      (Filter.Eventually.of_forall hjK) (hjs s) (by simpa using hdim)
  -- The closed characteristic is a closed Reeb orbit of `j^* (-α)` run at another speed.
  obtain ⟨T, δ, hT, hδ, hper, -, hδK, g, hg, hgδ⟩ :=
    SmoothTwoForm.hasContractibleClosedCharacteristic_iff.1 hV
  have hδj (t : ℝ) : δ t ∈ range j := hlevel ▸ hδK t
  obtain ⟨γ, hγ, ⟨τ, hτ, hγτ⟩, ψ, -, hδeq⟩ :=
    h.isNondegenerate.exists_isMIntegralCurve_reebVectorField_comp_eq hj hji hαneg hK hdθ hKj hδ
      (hδj 0) hT.ne' hper
  -- Reversing time turns it into a closed Reeb orbit of `j^* α`.
  refine ⟨γ ∘ (· * -1), ?_, ⟨τ / -1, by simpa using hτ, hγτ.mul_const' (-1)⟩, T,
    ψ.trans (Homeomorph.neg ℝ), hT, ?_⟩
  · refine (isMIntegralCurve_congr_vectorField fun t ↦ ?_).1 (hγ.comp_mul (-1))
    rw [Pi.smul_apply, map_neg, hα.reebVectorField_neg, neg_one_smul, neg_neg]
  -- The loop of the closed characteristic lies on the graph, through a loop `ℓ` of `S`, and the
  -- radial homotopy joins it to the loop `ι ∘ ℓ`.
  obtain ⟨ℓ, hℓ, hιℓ⟩ := exists_nullhomotopic_of_forall_mem_range_liouvilleGraph h hZ hc
    hι.continuous hιi hιW hf.continuous hf₀ g hg fun x ↦ by
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact hgδ t ▸ hδj t
  refine ⟨_, hιℓ, fun t ↦ congrArg ι (hji ((hℓ t).trans ?_))⟩
  rw [hgδ, hδeq]
  simp

/-- **Closed Reeb orbits of every contact form defining the contact structure of the boundary.**
Let `ι` be a smooth injective immersion of a compact manifold `S`, of one dimension less than `M`,
into the frontier of a Liouville domain `W` with complete Liouville field `Z`, and let `β` be a
smooth one-form on `S` with the same kernel as the contact form `ι^* α`, such as any contact form
defining the same contact structure, with either coorientation. Suppose that the Liouville graph of
every smooth function `f > 1` over `ι` is a regular level `K⁻¹(c)` of a `C²` function `K`, carrying
a closed characteristic contractible in `V`. Then `β` has a closed Reeb orbit `γ` whose loop
`ι ∘ γ` on the boundary of `W`, run at another speed, is contractible in `M`.

This is the reduction, in the proof of Corollary E of Barraud–Damian–Humilière–Oancea, of the
contact forms defining the contact structure of `∂W` to the forms `f ι^* α` with `f > 1`: up to a
nonzero constant factor on each component of `S`, `β` is the restriction of `α` to the graph of such
an `f`. -/
theorem exists_isMIntegralCurve_reebVectorField_of_kerDistribution_eq
    (h : IsLiouvilleDomain ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hc : IsCompleteVectorField Z) (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιi : Injective ι)
    (hιs : ∀ s, Injective (mfderiv J I ι s)) (hιW : ∀ s, ι s ∈ frontier W)
    (hdim : Module.finrank ℝ E' + 1 = Module.finrank ℝ E) {V : Set M}
    (hV : ∀ f : S → ℝ, ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f → (∀ s, 1 < f s) →
      ∃ (K : M → ℝ) (c : ℝ), ContMDiff I 𝓘(ℝ) 2 K ∧ IsRegularValue I 𝓘(ℝ) K c ∧
        {x | K x = c} = range (liouvilleGraph Z ι f) ∧ ω.HasContractibleClosedCharacteristic V K c)
    {β : SmoothForm J S ℝ 1}
    (hβ : β.kerDistribution = (SmoothForm.mpullback ι hι α).kerDistribution) :
    ∃ γ : ℝ → S, IsMIntegralCurve γ β.reebVectorField ∧ (∃ τ, τ ≠ 0 ∧ Periodic γ τ) ∧
      ∃ (T : ℝ) (ψ : ℝ ≃ₜ ℝ), 0 < T ∧
        ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = ι (γ (ψ t)) := by
  have hZs := h.contMDiff_of_interior_eq hZ
  have hιd : MDifferentiable J I ι := hι.mdifferentiable (by simp)
  -- `ι^* α` is a contact form, since `ι` is the Liouville graph of the constant `1`.
  have hα₀ : (SmoothForm.mpullback ι hι α).IsContactForm := by
    have h₁ := h.isRestrictedContactType_liouvilleGraph hZ hc hιd hιs hιW (f := fun _ ↦ 1)
      mdifferentiable_const fun _ ↦ one_ne_zero
    rw [liouvilleGraph_one] at h₁
    exact h₁.isContactType.isContactForm_mpullback h.isNondegenerate hι hιs hdim
  -- Up to a locally constant factor `c`, `β` is `f ι^* α` with `f > 1`, the restriction of `α` to
  -- the graph of `f`, which carries a closed Reeb orbit `γ`.
  obtain ⟨c, f, hcl, hc₀, hf, hf₁, hcf⟩ :=
    SmoothForm.exists_isLocallyConstant_smul_eq_smul hα₀.apply_ne_zero hβ 1
  have hf₀ (s : S) : 0 < f s := one_pos.trans (hf₁ s)
  obtain ⟨K, k, hK, hreg, hlevel, hVK⟩ := hV f hf hf₁
  obtain ⟨γ, hγ, ⟨τ, hτ, hγτ⟩, T, ψ, hT, g, hg, hgγ⟩ :=
    h.exists_isMIntegralCurve_reebVectorField_of_hasContractibleClosedCharacteristic hZ hc hι hιi
      hιs hιW hf hf₀ hdim hK hreg hlevel hVK
  set θ := SmoothForm.mpullback (liouvilleGraph Z ι f)
    (contMDiff_liouvilleGraph le_top hZs hc hι hf fun s ↦ (hf₀ s).ne') α with hθdef
  have hθ (s : S) : θ.val s = f s • (SmoothForm.mpullback ι hι α).val s := by
    rw [hθdef, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
    exact mpullback_liouvilleGraph_apply (hZs.of_le (by simp)) α.mdifferentiable h.mextDeriv_eq
      hZ (hc.mem_flowDomain _ _) (hιd s) ((hf s).mdifferentiableAt (by simp)) (hf₀ s)
  have hθc : θ.IsContactForm :=
    (SmoothForm.isContactForm_iff_of_eq_smul (hf.of_le (by simp)) (fun s ↦ (hf₀ s).ne') hθ).2 hα₀
  have hβθ (s : S) : β.val s = (c s)⁻¹ • θ.val s := by
    rw [hθ, ← hcf, smul_smul, inv_mul_cancel₀ (hc₀ s), one_smul]
  have : FiniteDimensional ℝ E' :=
    SmoothForm.finiteDimensional_of_isContactForm_mpullback hι hα₀ (γ 0)
  -- Run at the constant speed `c (γ 0)`, `γ` is a closed Reeb orbit of `β = c⁻¹ θ`.
  have hδ := hθc.isMIntegralCurve_comp_mul_reebVectorField_of_eq_smul
    (hcl.comp fun a : ℝ ↦ a⁻¹) hβθ hγ
  simp only [Function.comp_apply, inv_inv] at hδ
  have ha := hc₀ (γ 0)
  refine ⟨γ ∘ (· * c (γ 0)), hδ, ⟨τ / c (γ 0), div_ne_zero hτ ha, hγτ.mul_const' _⟩, T,
    ψ.trans (Homeomorph.mulRight₀ (c (γ 0))⁻¹ (inv_ne_zero ha)), hT, g, hg, fun t ↦ ?_⟩
  simp [hgγ, ha]

end ClosedCharacteristic

end IsLiouvilleDomain

namespace IsLiouvilleCompletion

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M}

/-- The Liouville graph of a smooth nowhere vanishing function over a smooth map is smooth, on a
completion of a Liouville domain, whose Liouville field is smooth and complete. -/
theorem contMDiff_liouvilleGraph (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (hf₀ : ∀ s, f s ≠ 0) :
    ContMDiff J I (⊤ : ℕ∞) (liouvilleGraph Z ι f) :=
  TauCeti.contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ)
    (h.isCompleteVectorField hZ) hι hf hf₀

/-- **A graph over the boundary of a Liouville domain is a contact hypersurface.** Let `ι` be a
smooth immersion into the frontier of a Liouville domain `W`, from a manifold of one dimension
less, on a completion of `W`. For every smooth nowhere vanishing function `f`, the restriction
`j^* α` of the primitive to the Liouville graph `j` of `f` over `ι` is a contact form; for positive
`f` it is `f ι^* α` (`TauCeti.mpullback_liouvilleGraph_apply`). -/
theorem isContactForm_mpullback_liouvilleGraph [IsManifold J (⊤ : ℕ∞) S]
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hdim : Module.finrank ℝ E' + 1 = Module.finrank ℝ E) (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f)
    (hf₀ : ∀ s, f s ≠ 0) :
    (SmoothForm.mpullback (liouvilleGraph Z ι f) (h.contMDiff_liouvilleGraph hZ hι hf hf₀)
      α).IsContactForm := by
  have hZs := h.contMDiff_of_interior_eq hZ
  have hc := h.isCompleteVectorField hZ
  exact (h.isRestrictedContactType_liouvilleGraph hZ hc (hι.mdifferentiable (by simp)) hιs hιW
    (hf.mdifferentiable (by simp)) hf₀).isContactType.isContactForm_mpullback h.isNondegenerate _
    (fun s ↦ injective_mfderiv_liouvilleGraph (hZs.of_le (by simp)) hc
      ((hι s).mdifferentiableAt (by simp)) ((hf s).mdifferentiableAt (by simp)) (hf₀ s) (hιs s)
      (h.isTransverseAlong hZ (hι.mdifferentiable (by simp)) hιW)) hdim

end IsLiouvilleCompletion

end TauCeti
