/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Collar
public import TauCeti.Geometry.Symplectic.Liouville.Flow.Out
public import Mathlib.Topology.Homotopy.Basic

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
(`TauCeti.IsLiouvilleDomain.isRestrictedContactType_liouvilleGraph`). For `f > 1` it lies outside
`W` (`TauCeti.IsLiouvilleDomain.liouvilleGraph_notMem`), it is injective when `ι` is
(`TauCeti.IsLiouvilleDomain.injective_liouvilleGraph`), hence a closed embedding when `S` is
compact (`TauCeti.IsLiouvilleDomain.isClosedEmbedding_liouvilleGraph`), and on a completion of `W`
it lies on the level `f` of the radial coordinate
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_liouvilleGraph`). Moving `f` linearly to
the constant `1` deforms the graph back to `ι` through graphs
(`TauCeti.liouvilleGraphHomotopy`); this is the radial homotopy that joins a closed characteristic
of `j_f(S)` to the corresponding closed Reeb orbit of `f ι^* α` on `Σ`.

## Main definitions

* `TauCeti.liouvilleGraph Z ι f`: the map `s ↦ φ_{log f(s)}(ι s)`.
* `TauCeti.liouvilleGraphHomotopy`: the homotopy from `j_f` to `ι` through the graphs of the
  functions `(1 - τ) f + τ`.

## Main results

* `TauCeti.mpullback_liouvilleGraph_apply`: `j_f^* α = f ι^* α`.
* `TauCeti.injective_mfderiv_liouvilleGraph`, `TauCeti.isTransverseAlong_liouvilleGraph`: the
  graph of an immersion transverse to `Z` is an immersion transverse to `Z`.
* `TauCeti.IsLiouvilleDomain.isRestrictedContactType_liouvilleGraph`: a graph over the boundary of
  a Liouville domain is of restricted contact type.
* `TauCeti.IsLiouvilleDomain.liouvilleGraph_notMem`,
  `TauCeti.IsLiouvilleDomain.injective_liouvilleGraph`,
  `TauCeti.IsLiouvilleDomain.isClosedEmbedding_liouvilleGraph`: for `f > 1` it is an injective map
  into the complement of the domain, and a closed embedding of a compact boundary.
* `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_liouvilleGraph`: on a completion, the
  radial coordinate of `j_f(s)` is `f(s)`.

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
    (hZ : RoughForm.interior Z ω.val = α.val) (hc : IsCompleteVectorField Z) {s : S}
    (hιW : ι s ∉ interior W) (hfs : 1 < f s) : liouvilleGraph Z ι f s ∉ W :=
  h.flowOf_notMem hZ hιW (Real.log_pos hfs) (hc.mem_flowDomain _ _)

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

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I (⊤ : ℕ∞) M]

section Flow

variable (hZ : ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z)) (hc : IsCompleteVectorField Z)
include hZ hc

/-- The time-`t` map of a complete smooth vector field has injective differential. -/
private theorem injective_mfderiv_flowOf (t : ℝ) (x : M) :
    Injective (mfderiv I I (flowOf Z t) x) := by
  rw [flowOf_eq_globalFlow (hZ.of_le (by simp)) hc, ← coe_globalFlowDiffeomorph hc le_top hZ t]
  exact ((globalFlowDiffeomorph hc le_top hZ t).isInvertible_mfderiv (by simp)).injective

/-- The Liouville graph of a continuous nowhere vanishing function over a continuous map is
continuous. -/
theorem continuous_liouvilleGraph (hι : Continuous ι) (hf : Continuous f) (hf₀ : ∀ s, f s ≠ 0) :
    Continuous (liouvilleGraph Z ι f) := by
  rw [show liouvilleGraph Z ι f = fun s ↦ flowOf Z (Real.log (f s)) (ι s) from rfl,
    flowOf_eq_globalFlow (hZ.of_le (by simp)) hc]
  exact (contMDiff_globalFlow_uncurry hc le_top hZ).continuous.comp
    ((hf.log hf₀).prodMk hι)

/-- **The radial homotopy.** For a continuous positive function `f`, the Liouville graphs of the
functions `(1 - τ) f + τ`, `τ ∈ [0, 1]`, form a homotopy from the Liouville graph of `f` to the map
`ι` itself, the graph of the constant `1`. Composed with a loop of `S`, it joins the loop of the
graph to the loop of `ι` along the trajectories of `Z`. -/
noncomputable def liouvilleGraphHomotopy (hι : Continuous ι) (hf : Continuous f)
    (hf₀ : ∀ s, 0 < f s) :
    ContinuousMap.Homotopy ⟨liouvilleGraph Z ι f,
      continuous_liouvilleGraph hZ hc hι hf fun s ↦ (hf₀ s).ne'⟩ ⟨ι, hι⟩ where
  toFun p := liouvilleGraph Z ι (fun s ↦ (1 - (p.1 : ℝ)) * f s + p.1) p.2
  continuous_toFun := by
    have hpos (p : unitInterval × S) : 0 < (1 - (p.1 : ℝ)) * f p.2 + p.1 := by
      rcases eq_or_lt_of_le (unitInterval.le_one p.1) with h | h
      · rw [h, sub_self, zero_mul, zero_add]
        exact one_pos
      · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 h) (hf₀ p.2))
          (unitInterval.nonneg p.1)
    simp only [liouvilleGraph_apply]
    rw [flowOf_eq_globalFlow (hZ.of_le (by simp)) hc]
    refine (contMDiff_globalFlow_uncurry hc le_top hZ).continuous.comp
      (Continuous.prodMk (Continuous.log ?_ fun p ↦ (hpos p).ne') (hι.comp continuous_snd))
    exact ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).mul
      (hf.comp continuous_snd)).add (continuous_subtypeVal.comp continuous_fst)
  map_zero_left s := by simp
  map_one_left s := by simp

@[simp]
theorem liouvilleGraphHomotopy_apply (hι : Continuous ι) (hf : Continuous f) (hf₀ : ∀ s, 0 < f s)
    (p : unitInterval × S) :
    liouvilleGraphHomotopy hZ hc hι hf hf₀ p =
      liouvilleGraph Z ι (fun s ↦ (1 - (p.1 : ℝ)) * f s + p.1) p.2 :=
  (rfl)

variable (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (hf₀ : ∀ s, f s ≠ 0)
include hι hf hf₀

/-- The Liouville graph of a smooth nowhere vanishing function over a smooth map is smooth. -/
theorem contMDiff_liouvilleGraph : ContMDiff J I (⊤ : ℕ∞) (liouvilleGraph Z ι f) := fun _ ↦
  contMDiffAt_flowOf_comp le_top hZ ((hf.log hf₀).contMDiffAt) hι.contMDiffAt
    (hc.mem_flowDomain _ _)

/-- The differential of the Liouville graph: at `s` it sends `w` to
`dφₜ(d(log f)(w) Z + dι(w))`, where `t = log f(s)`. -/
private theorem mfderiv_liouvilleGraph_apply (s : S) (w : TangentSpace J s) :
    mfderiv J I (liouvilleGraph Z ι f) s w =
      mfderiv I I (flowOf Z (Real.log (f s))) (ι s)
        (mvfderiv J (fun s ↦ Real.log (f s)) s w • Z (ι s) + mfderiv J I ι s w) := by
  have hp := hc.mem_flowDomain (Real.log (f s)) (ι s)
  have hτ : MDifferentiableAt J 𝓘(ℝ) (fun s ↦ Real.log (f s)) s :=
    ((hf.log hf₀) s).mdifferentiableAt (by simp)
  have h := mfderiv_flowOf_comp_prodMk_apply (hZ.of_le (by simp)) hτ
    ((hι s).mdifferentiableAt (by simp)) hp w
  rw [map_add, map_smul, mfderiv_flowOf_apply_self (hZ.of_le (by simp)) hp]
  exact h

/-- **The graph of an immersion is an immersion.** If `ι` is an immersion transverse to `Z`, then
the Liouville graph of every smooth nowhere vanishing function over `ι` is an immersion. -/
theorem injective_mfderiv_liouvilleGraph (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hZι : IsTransverseAlong J Z ι) (s : S) :
    Injective (mfderiv J I (liouvilleGraph Z ι f) s) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  rw [mfderiv_liouvilleGraph_apply hZ hc hι hf hf₀] at hw
  have h := injective_mfderiv_flowOf hZ hc (Real.log (f s)) (ι s) (hw.trans (map_zero _).symm)
  have h' : mvfderiv J (fun s ↦ Real.log (f s)) s w • Z (ι s) + mfderiv J I ι s w =
      (0 : ℝ) • Z (ι s) + mfderiv J I ι s (0 : TangentSpace J s) := by
    rw [h, zero_smul, map_zero, add_zero]
  exact (Prod.ext_iff.1 (hZι.injective_smul_add (hιs s) (a₁ := (_, w)) (a₂ := (0, 0)) h')).2

/-- **The graph keeps transversality.** If `ι` is an immersion transverse to `Z`, then `Z` is
transverse to the Liouville graph of every smooth nowhere vanishing function over `ι`. -/
theorem isTransverseAlong_liouvilleGraph (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hZι : IsTransverseAlong J Z ι) : IsTransverseAlong J Z (liouvilleGraph Z ι f) := by
  refine isTransverseAlong_iff.2 fun s ⟨w, hw⟩ ↦ ?_
  rw [ContinuousLinearMap.coe_coe] at hw
  set t := Real.log (f s)
  set a := mvfderiv J (fun s ↦ Real.log (f s)) s w
  -- `Z` at the graph point is the image of `Z (ι s)` under `dφₜ`.
  have hZt : Z (liouvilleGraph Z ι f s) = mfderiv I I (flowOf Z t) (ι s) (Z (ι s)) :=
    (mfderiv_flowOf_apply_self (hZ.of_le (by simp)) (hc.mem_flowDomain t (ι s))).symm
  rw [mfderiv_liouvilleGraph_apply hZ hc hι hf hf₀, hZt] at hw
  have h : (a - 1) • Z (ι s) + mfderiv J I ι s w = 0 := by
    refine injective_mfderiv_flowOf hZ hc t (ι s) ?_
    rw [map_zero, sub_smul, one_smul, sub_add_eq_add_sub, map_sub, hw, sub_self]
  have h' : (a - 1) • Z (ι s) + mfderiv J I ι s w =
      (0 : ℝ) • Z (ι s) + mfderiv J I ι s (0 : TangentSpace J s) := by
    rw [h, zero_smul, map_zero, add_zero]
  obtain ⟨ha, hw0⟩ := Prod.ext_iff.1 (hZι.injective_smul_add (hιs s) (a₁ := (a - 1, w))
    (a₂ := (0, 0)) h')
  subst hw0
  rw [show a = 0 from map_zero _, zero_sub] at ha
  exact absurd ha (by norm_num)

variable {α : SmoothForm I M ℝ 1}

/-- **The graph restricts the primitive to `f` times its restriction.** If `Z` is the Liouville
field of `α`, `ι_Z dα = α`, then the Liouville graph `s ↦ φ_{log f(s)}(ι s)` pulls `α` back to
`f ι^* α`: the flow rescales the primitive by `e^{log f} = f`, and the primitive vanishes on its
Liouville field. -/
theorem mpullback_liouvilleGraph_apply (hZα : (mextDeriv α.val).interior Z = α.val) {s : S}
    (hfs : 0 < f s) :
    mpullback J I (liouvilleGraph Z ι f) α.val s = f s • mpullback J I ι α.val s := by
  have hp := hc.mem_flowDomain (Real.log (f s)) (ι s)
  -- The flow rescales the primitive: `(φₜ^* α)_x = eᵗ α_x`.
  have hscale := mpullback_flowOf_apply_eq_exp_smul_of_interior_eq (hZ.of_le (by simp))
    α.mdifferentiable rfl hZα hp
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  have hs := congrArg (fun β ↦ β ![mfderiv J I ι s w]) hscale
  simp only [mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    Matrix.cons_val_fin_one, ← Matrix.vec_single_eq_const] at hs
  rw [Real.exp_log hfs] at hs
  -- Differentiate the graph, then use that `α` is linear and vanishes on `Z`.
  have hτ : MDifferentiableAt J 𝓘(ℝ) (fun s ↦ Real.log (f s)) s :=
    ((hf.log hf₀) s).mdifferentiableAt (by simp)
  have hd := mfderiv_flowOf_comp_prodMk_apply (hZ.of_le (by simp)) hτ
    ((hι s).mdifferentiableAt (by simp)) hp w
  simp only [mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    Matrix.cons_val_fin_one, ← Matrix.vec_single_eq_const]
  change α.val (flowOf Z (Real.log (f s)) (ι s))
    ![mfderiv J I (fun s ↦ flowOf Z (Real.log (f s)) (ι s)) s w] = _
  rw [hd, ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul,
    RoughForm.apply_eq_zero_of_interior_eq hZα, smul_zero, zero_add, hs]

end Flow

namespace IsLiouvilleDomain

variable {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M}

/-- **A graph over the boundary of a Liouville domain is of restricted contact type.** Let `ι` be a
smooth immersion into the frontier of a Liouville domain `W` whose Liouville field `Z` is complete.
For every smooth nowhere vanishing function `f`, the Liouville graph of `f` over `ι` is of
restricted contact type, with the same primitive `α` and the same Liouville field `Z`. For positive
`f` its restriction of `α` is `f ι^* α` (`TauCeti.mpullback_liouvilleGraph_apply`). -/
theorem isRestrictedContactType_liouvilleGraph (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hc : IsCompleteVectorField Z)
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hιW : ∀ s, ι s ∈ frontier W) (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (hf₀ : ∀ s, f s ≠ 0) :
    IsRestrictedContactType J ω.val α.val (liouvilleGraph Z ι f) :=
  isRestrictedContactType_iff.2 ⟨h.mextDeriv_eq, Z, h.contMDiff_of_interior_eq hZ, hZ,
    isTransverseAlong_liouvilleGraph (h.contMDiff_of_interior_eq hZ) hc hι hf hf₀ hιs
      (h.isTransverseAlong hZ (hι.mdifferentiable (by simp)) hιW)⟩

/-- **A graph over a compact boundary is a closed embedding.** If `S` is compact and `ι` is an
injective continuous map into the frontier of a Liouville domain whose Liouville field `Z` is
smooth and complete, then the Liouville graph of every continuous nowhere vanishing function over
`ι` is a closed embedding of `S` into `M`. -/
theorem isClosedEmbedding_liouvilleGraph [CompactSpace S] (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hc : IsCompleteVectorField Z) (hι : Continuous ι)
    (hιi : Injective ι) (hιW : ∀ s, ι s ∈ frontier W) (hf : Continuous f) (hf₀ : ∀ s, f s ≠ 0) :
    Topology.IsClosedEmbedding (liouvilleGraph Z ι f) :=
  (continuous_liouvilleGraph (h.contMDiff_of_interior_eq hZ) hc hι hf hf₀).isClosedEmbedding
    (h.injective_liouvilleGraph hZ hc hιi hιW)

end IsLiouvilleDomain

end TauCeti
