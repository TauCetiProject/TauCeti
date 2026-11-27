/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.PartitionOfUnity.MVFDeriv
public import TauCeti.Geometry.Manifold.Boundary.TangentSpace
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Boundary defining functions

Let `M` be a manifold modelled on the half-space `𝓡∂ (n + 1)`. A **boundary defining function**
on an open set `U ⊆ M` (`TauCeti.IsBoundaryDefiningFunctionOn`) is a function `ρ : M → ℝ`,
smooth on `U`, positive at the interior points of `U`, zero at the boundary points of `U`, with
nonzero differential at the boundary points of `U`. The normal coordinate `x⁰` of a chart of the
smooth maximal atlas is a boundary defining function on the chart source
(`TauCeti.isBoundaryDefiningFunctionOn_normal`), so boundary defining functions exist locally.
A smooth partition of unity `φ` subordinate to the domains of boundary defining functions `ρ i`
glues them into the global boundary defining function `∑ᶠ i, φ i • ρ i`
(`TauCeti.isBoundaryDefiningFunctionOn_finsum_smul`): at a boundary point `q` the glued
differential is `∑ φ_i(q) dρ_i`, a convex combination of forms that are positive on the inward
vectors. A Hausdorff σ-compact smooth manifold has such partitions of unity, hence a global
boundary defining function (`TauCeti.exists_isBoundaryDefiningFunctionOn_univ`).

A boundary defining function has a local minimum at each boundary point of its domain, so by
Fermat's theorem at a boundary point (`TauCeti.isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin`,
in `Boundary/Orientation.lean`) the sign of its differential at a boundary point `q` detects the
three kinds of tangent vectors: `dρ_q v` is strictly negative exactly on the outward vectors, zero
exactly on the tangent space `T_q∂M` of the boundary and strictly positive exactly on the inward
vectors. Since
local diffeomorphisms preserve interior and boundary points, boundary defining functions pull back
along them (`TauCeti.IsBoundaryDefiningFunctionOn.comp_isLocalDiffeomorph`).

## Main declarations

* `TauCeti.IsBoundaryDefiningFunctionOn`: boundary defining functions on an open set.
* `TauCeti.IsBoundaryDefiningFunctionOn.pos_iff` and
  `TauCeti.IsBoundaryDefiningFunctionOn.eq_zero_iff`: the zero set is the boundary.
* `TauCeti.IsBoundaryDefiningFunctionOn.isOutwardPointing_iff_mvfderiv_neg`,
  `TauCeti.IsBoundaryDefiningFunctionOn.isOutwardPointing_neg_iff_mvfderiv_pos` and
  `TauCeti.IsBoundaryDefiningFunctionOn.ker_mvfderiv`: the sign test.
* `TauCeti.isBoundaryDefiningFunctionOn_normal`: local existence, from the normal coordinate of a
  chart.
* `TauCeti.isBoundaryDefiningFunctionOn_finsum_smul` and
  `TauCeti.exists_isBoundaryDefiningFunctionOn_univ`: gluing and global existence.
* `TauCeti.IsBoundaryDefiningFunctionOn.mul_left`: a positive smooth multiple of a boundary
  defining function is one; `TauCeti.IsBoundaryDefiningFunctionOn.not_mul_self` and
  `TauCeti.IsBoundaryDefiningFunctionOn.not_neg`: its square and its negative are not.
* `TauCeti.IsBoundaryDefiningFunctionOn.mono`, `TauCeti.IsBoundaryDefiningFunctionOn.congr`,
  `TauCeti.IsBoundaryDefiningFunctionOn.comp_isLocalDiffeomorph` and
  `TauCeti.IsBoundaryDefiningFunctionOn.comp_diffeomorph`: restriction to open subsets, congruence
  and pullback along local diffeomorphisms.

## References

* G. Uhlmann, A. Vasy, *The inverse problem for the local geodesic ray transform*, Invent. Math.
  205 (2016), 83–120, Section 1 (the boundary defining function `ρ`).
* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Section 3.1.
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-! ### Boundary defining functions -/

variable (n) in
/-- `ρ` is a **boundary defining function** on the open set `U ⊆ M`: it is smooth on `U`, positive
at the interior points of `U`, zero at the boundary points of `U`, and has nonzero differential at
the boundary points of `U`. A global boundary defining function is one on `U = univ`. -/
structure IsBoundaryDefiningFunctionOn (ρ : M → ℝ) (U : Set M) : Prop where
  /-- The domain of a boundary defining function is open. -/
  isOpen : IsOpen U
  /-- A boundary defining function is smooth on its domain. -/
  contMDiffOn : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ ρ U
  /-- A boundary defining function is positive at interior points. -/
  pos : ∀ x ∈ U, x ∈ (𝓡∂ (n + 1)).interior M → 0 < ρ x
  /-- A boundary defining function vanishes at boundary points. -/
  eq_zero : ∀ x ∈ U, x ∈ (𝓡∂ (n + 1)).boundary M → ρ x = 0
  /-- A boundary defining function has nonzero differential at boundary points. -/
  mvfderiv_ne_zero : ∀ x ∈ U, x ∈ (𝓡∂ (n + 1)).boundary M → mvfderiv (𝓡∂ (n + 1)) ρ x ≠ 0

namespace IsBoundaryDefiningFunctionOn

variable {ρ : M → ℝ} {U : Set M}

/-- A boundary defining function is nonnegative on its domain. -/
theorem nonneg (hρ : IsBoundaryDefiningFunctionOn n ρ U) {x : M} (hx : x ∈ U) : 0 ≤ ρ x := by
  rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint x with h | h
  · exact (hρ.pos x hx h).le
  · exact (hρ.eq_zero x hx h).ge

/-- A boundary defining function is positive exactly at the interior points of its domain. -/
theorem pos_iff (hρ : IsBoundaryDefiningFunctionOn n ρ U) {x : M} (hx : x ∈ U) :
    0 < ρ x ↔ x ∈ (𝓡∂ (n + 1)).interior M := by
  refine ⟨fun h ↦ ?_, hρ.pos x hx⟩
  rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint x with hi | hb
  · exact hi
  · exact absurd (hρ.eq_zero x hx hb) h.ne'

/-- A boundary defining function vanishes exactly at the boundary points of its domain. -/
theorem eq_zero_iff (hρ : IsBoundaryDefiningFunctionOn n ρ U) {x : M} (hx : x ∈ U) :
    ρ x = 0 ↔ x ∈ (𝓡∂ (n + 1)).boundary M := by
  refine ⟨fun h ↦ ?_, hρ.eq_zero x hx⟩
  rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint x with hi | hb
  · exact absurd h (hρ.pos x hx hi).ne'
  · exact hb

/-- A boundary defining function has a local minimum at each boundary point of its domain. -/
theorem isLocalMin (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : M} (hqU : q ∈ U)
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) : IsLocalMin ρ q := by
  filter_upwards [hρ.isOpen.mem_nhds hqU] with y hy
  rw [hρ.eq_zero q hqU hq]
  exact hρ.nonneg hy

/-- A boundary defining function is differentiable at each point of its domain. -/
theorem mdifferentiableAt (hρ : IsBoundaryDefiningFunctionOn n ρ U) {x : M} (hx : x ∈ U) :
    MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) ρ x :=
  ((hρ.contMDiffOn x hx).contMDiffAt (hρ.isOpen.mem_nhds hx)).mdifferentiableAt
    (by simp)

/-- **Sign test.** At a boundary point `q` of its domain, a boundary defining function `ρ` has
`dρ_q v` strictly negative exactly for the outward vectors `v`. -/
theorem isOutwardPointing_iff_mvfderiv_neg (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : M}
    (hqU : q ∈ U) (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔ mvfderiv (𝓡∂ (n + 1)) ρ q v < 0 :=
  isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hq (hρ.isLocalMin hqU hq)
    (hρ.mvfderiv_ne_zero q hqU hq) v

/-- **Sign test.** At a boundary point `q` of its domain, a boundary defining function `ρ` has
`dρ_q v` strictly positive exactly for the inward vectors `v`, those with `-v` outward. -/
theorem isOutwardPointing_neg_iff_mvfderiv_pos (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : M}
    (hqU : q ∈ U) (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q (-v) ↔ 0 < mvfderiv (𝓡∂ (n + 1)) ρ q v :=
  isOutwardPointing_neg_iff_mvfderiv_pos_of_isLocalMin hq (hρ.isLocalMin hqU hq)
    (hρ.mvfderiv_ne_zero q hqU hq) v

/-- At a boundary point of its domain, the differential of a boundary defining function vanishes
exactly on the tangent space of the boundary. -/
theorem mvfderiv_eq_zero_iff (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    {q : (𝓡∂ (n + 1)).boundary M} (hqU : (q : M) ∈ U) (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    mvfderiv (𝓡∂ (n + 1)) ρ q v = 0 ↔ v ∈ boundaryTangentSpace q :=
  mvfderiv_eq_zero_iff_mem_boundaryTangentSpace_of_isLocalMin (hρ.isLocalMin hqU q.property)
    (hρ.mvfderiv_ne_zero q hqU q.property) v

/-- At a boundary point of its domain, the kernel of the differential of a boundary defining
function is the tangent space of the boundary. -/
theorem ker_mvfderiv (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    {q : (𝓡∂ (n + 1)).boundary M} (hqU : (q : M) ∈ U) :
    LinearMap.ker (mvfderiv (𝓡∂ (n + 1)) ρ q).toLinearMap = boundaryTangentSpace q := by
  ext v
  exact hρ.mvfderiv_eq_zero_iff hqU v

/-- A boundary defining function restricts to a boundary defining function on every open subset of
its domain. -/
theorem mono (hρ : IsBoundaryDefiningFunctionOn n ρ U) {V : Set M} (hV : IsOpen V)
    (hVU : V ⊆ U) : IsBoundaryDefiningFunctionOn n ρ V where
  isOpen := hV
  contMDiffOn := hρ.contMDiffOn.mono hVU
  pos x hx := hρ.pos x (hVU hx)
  eq_zero x hx := hρ.eq_zero x (hVU hx)
  mvfderiv_ne_zero x hx := hρ.mvfderiv_ne_zero x (hVU hx)

/-- A function agreeing with a boundary defining function on its domain is a boundary defining
function there. -/
theorem congr (hρ : IsBoundaryDefiningFunctionOn n ρ U) {ρ' : M → ℝ} (h : EqOn ρ ρ' U) :
    IsBoundaryDefiningFunctionOn n ρ' U where
  isOpen := hρ.isOpen
  contMDiffOn := hρ.contMDiffOn.congr fun y hy ↦ (h hy).symm
  pos x hx hint := h hx ▸ hρ.pos x hx hint
  eq_zero x hx hb := h hx ▸ hρ.eq_zero x hx hb
  mvfderiv_ne_zero x hx hb := by
    rw [← (Filter.eventuallyEq_of_mem (hρ.isOpen.mem_nhds hx) h).mvfderiv_eq]
    exact hρ.mvfderiv_ne_zero x hx hb

/-- A boundary defining function pulls back along a smooth local diffeomorphism `f` of manifolds
with boundary to a boundary defining function on the preimage of its domain. -/
theorem comp_isLocalDiffeomorph {M' : Type*} [TopologicalSpace M']
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M'] {f : M' → M}
    (hf : IsLocalDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ f)
    (hρ : IsBoundaryDefiningFunctionOn n ρ U) :
    IsBoundaryDefiningFunctionOn n (ρ ∘ f) (f ⁻¹' U) where
  isOpen := hρ.isOpen.preimage hf.contMDiff.continuous
  contMDiffOn := hρ.contMDiffOn.comp hf.contMDiff.contMDiffOn (mapsTo_preimage f U)
  pos x hx hint := hρ.pos (f x) hx (by rwa [← mem_preimage, hf.preimage_interior (by simp)])
  eq_zero x hx hb :=
    hρ.eq_zero (f x) hx (by rwa [← mem_preimage, hf.preimage_boundary (by simp)])
  mvfderiv_ne_zero x hx hb :=
    mt (mvfderiv_comp_eq_zero_iff_of_isInvertible (hρ.mdifferentiableAt hx)
      ((hf x).isInvertible_mfderiv (by simp))).mp
      (hρ.mvfderiv_ne_zero (f x) hx (by rwa [← mem_preimage, hf.preimage_boundary (by simp)]))

/-- A boundary defining function pulls back along a smooth diffeomorphism `Φ` of manifolds with
boundary to a boundary defining function on the preimage of its domain. -/
theorem comp_diffeomorph {M' : Type*} [TopologicalSpace M']
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M'] (Φ : M' ≃ₘ^∞⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M)
    (hρ : IsBoundaryDefiningFunctionOn n ρ U) :
    IsBoundaryDefiningFunctionOn n (ρ ∘ Φ) (Φ ⁻¹' U) :=
  hρ.comp_isLocalDiffeomorph Φ.isLocalDiffeomorph

/-- The product `u ρ` of a boundary defining function `ρ` with a smooth function `u` that is
positive on its domain is a boundary defining function: at a boundary point its differential is
`u dρ`. -/
theorem mul_left (hρ : IsBoundaryDefiningFunctionOn n ρ U) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u U) (hpos : ∀ x ∈ U, 0 < u x) :
    IsBoundaryDefiningFunctionOn n (fun x ↦ u x * ρ x) U where
  isOpen := hρ.isOpen
  contMDiffOn := hu.smul hρ.contMDiffOn
  pos x hx hint := mul_pos (hpos x hx) (hρ.pos x hx hint)
  eq_zero x hx hb := by rw [hρ.eq_zero x hx hb, mul_zero]
  mvfderiv_ne_zero x hx hb := by
    have hud : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) u x :=
      ((hu x hx).contMDiffAt (hρ.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
    rw [mvfderiv_fun_mul hud (hρ.mdifferentiableAt hx), hρ.eq_zero x hx hb, zero_smul, add_zero]
    exact smul_ne_zero (hpos x hx).ne' (hρ.mvfderiv_ne_zero x hx hb)

/-- The square `ρ²` of a boundary defining function is not a boundary defining function on a
domain containing a boundary point `q`: its differential `2 ρ(q) dρ_q` vanishes there. -/
theorem not_mul_self (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : M} (hqU : q ∈ U)
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) :
    ¬IsBoundaryDefiningFunctionOn n (fun x ↦ ρ x * ρ x) U := fun h ↦ by
  have hd := h.mvfderiv_ne_zero q hqU hq
  rw [mvfderiv_fun_mul (hρ.mdifferentiableAt hqU) (hρ.mdifferentiableAt hqU),
    hρ.eq_zero q hqU hq, zero_smul, add_zero] at hd
  exact hd rfl

/-- The negative `-ρ` of a boundary defining function is not a boundary defining function on a
domain containing an interior point, where it is negative. -/
theorem not_neg (hρ : IsBoundaryDefiningFunctionOn n ρ U) {x : M} (hxU : x ∈ U)
    (hx : x ∈ (𝓡∂ (n + 1)).interior M) :
    ¬IsBoundaryDefiningFunctionOn n (fun y ↦ -ρ y) U := fun h ↦ by
  have h₁ := h.pos x hxU hx
  have h₂ := hρ.pos x hxU hx
  linarith

end IsBoundaryDefiningFunctionOn

/-- **Local existence.** The normal coordinate `x⁰` of a chart of the smooth maximal atlas is a
boundary defining function on the chart source. -/
theorem isBoundaryDefiningFunctionOn_normal
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) ∞ M) :
    IsBoundaryDefiningFunctionOn n (fun y ↦ (e y).val 0) e.source where
  isOpen := e.open_source
  contMDiffOn := by
    have h := ((EuclideanSpace.proj (0 : Fin (n + 1)) :
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contMDiff.comp_contMDiffOn
        (e.contMDiffOn_extend he))
    exact h.congr fun y _ ↦ by simp
  pos x hx hint := (ModelWithCorners.isInteriorPoint_euclideanHalfSpace_iff hx).mp hint
  eq_zero x hx hb := (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hx).mp hb
  mvfderiv_ne_zero x hx _ :=
    mvfderiv_normal_ne_zero (IsManifold.maximalAtlas_subset_of_le (by simp) he) hx

/-- On an open set of interior points, the constant `1` is a boundary defining function. -/
theorem isBoundaryDefiningFunctionOn_one {U : Set M} (hU : IsOpen U)
    (hUi : U ⊆ (𝓡∂ (n + 1)).interior M) :
    IsBoundaryDefiningFunctionOn n (fun _ ↦ (1 : ℝ)) U where
  isOpen := hU
  contMDiffOn := contMDiffOn_const
  pos _ _ _ := one_pos
  eq_zero _ hx hb := absurd (hUi hx) fun hi ↦
    (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ (n + 1))).ne_of_mem hi hb rfl
  mvfderiv_ne_zero _ hx hb := absurd (hUi hx) fun hi ↦
    (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ (n + 1))).ne_of_mem hi hb rfl

/-- **Gluing.** For a smooth partition of unity `φ` on `M` subordinate to the domains of boundary
defining functions `ρ i`, the sum `∑ᶠ i, φ i • ρ i` is a global boundary defining function. -/
theorem isBoundaryDefiningFunctionOn_finsum_smul {ι : Type*} {U : ι → Set M} {ρ : ι → M → ℝ}
    (hρ : ∀ i, IsBoundaryDefiningFunctionOn n (ρ i) (U i))
    {φ : SmoothPartitionOfUnity ι (𝓡∂ (n + 1)) M univ} (hφ : φ.IsSubordinate U) :
    IsBoundaryDefiningFunctionOn n (fun x ↦ ∑ᶠ i, φ i x • ρ i x) univ := by
  have hmem {i : ι} {x : M} (hx : φ i x ≠ 0) : x ∈ U i := hφ i (subset_tsupport _ hx)
  refine ⟨isOpen_univ,
    (hφ.contMDiff_finsum_smul (fun i ↦ (hρ i).isOpen) fun i ↦ (hρ i).contMDiffOn).contMDiffOn,
    fun x _ hx ↦ ?_, fun x _ hx ↦ ?_, fun q _ hq h0 ↦ ?_⟩
  · exact φ.finsum_smul_mem_convex (g := ρ) (mem_univ x) (fun i hi ↦ (hρ i).pos x (hmem hi) hx)
      (convex_Ioi 0)
  · exact φ.finsum_smul_mem_convex (g := ρ) (t := {0}) (mem_univ x)
      (fun i hi ↦ (hρ i).eq_zero x (hmem hi) hx) (convex_singleton 0)
  · -- The differential is positive on the inward vector `e₀` of the preferred chart, since each
    -- `ρ i` with `q ∈ U i` vanishes at `q` and is positive on inward vectors there.
    have h := φ.mvfderiv_finsum_smul_pos hφ (mem_univ q) (fun i hi ↦ (hρ i).mdifferentiableAt hi)
      (fun i hi ↦ (hρ i).eq_zero q hi hq) fun i hi ↦
        ((hρ i).isOutwardPointing_neg_iff_mvfderiv_pos hi hq _).mp
          (isOutwardPointing_neg_single_zero hq)
    rw [h0] at h
    exact h.ne rfl

/-- **Global existence.** A Hausdorff σ-compact smooth manifold modelled on the half-space, for
instance a Hausdorff second-countable one, has a global boundary defining function. -/
theorem exists_isBoundaryDefiningFunctionOn_univ [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M]
    [SigmaCompactSpace M] : ∃ ρ : M → ℝ, IsBoundaryDefiningFunctionOn n ρ univ := by
  classical
  -- Glue the normal coordinates of the preferred charts at boundary points and the constant `1`
  -- on the interior.
  let U : M → Set M := fun x ↦ if x ∈ (𝓡∂ (n + 1)).boundary M then
    (chartAt (EuclideanHalfSpace (n + 1)) x).source else (𝓡∂ (n + 1)).interior M
  let ρ : M → M → ℝ := fun x ↦ if x ∈ (𝓡∂ (n + 1)).boundary M then
    (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0) else fun _ ↦ 1
  have hρ (x : M) : IsBoundaryDefiningFunctionOn n (ρ x) (U x) := by
    by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary M
    · simpa only [U, ρ, hx, ↓reduceIte] using
        isBoundaryDefiningFunctionOn_normal (IsManifold.chart_mem_maximalAtlas x)
    · simpa only [U, ρ, hx, ↓reduceIte] using isBoundaryDefiningFunctionOn_one
        ((𝓡∂ (n + 1)).isOpen_interior (M := M) (n := ∞) (by simp)) subset_rfl
  have hU : univ ⊆ ⋃ x, U x := fun x _ ↦ mem_iUnion.mpr ⟨x, by
    by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary M
    · simpa only [U, hx, ↓reduceIte] using mem_chart_source _ x
    · simp only [U, hx, ↓reduceIte]
      rw [← ModelWithCorners.compl_boundary]
      exact hx⟩
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓡∂ (n + 1)) isClosed_univ U
    (fun x ↦ (hρ x).isOpen) hU
  exact ⟨_, isBoundaryDefiningFunctionOn_finsum_smul hρ hφ⟩

end TauCeti
