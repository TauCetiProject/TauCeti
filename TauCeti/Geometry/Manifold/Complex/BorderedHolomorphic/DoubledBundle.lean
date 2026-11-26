/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.DoubleAlong
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# The doubled bundle over the Schottky double

Let `M` be a Riemann surface with boundary and `C` a complex point-indexed core over `M` whose
transitions are real at the boundary points (`TauCeti.FiniteRankBundleCore.IsRealAlong`). The real
coordinate subspaces over the boundary form a maximal totally real subbundle `F`, and the pair
`(C, F)` is a bundle pair in the sense of McDuff and Salamon.

`TauCeti.SchottkyDouble.doubledBundleCore C hC` is the doubled bundle `E_F` over the Schottky double
`TauCeti.SchottkyDouble M`: the core `C` on the first copy of `M` glued along the boundary to its
conjugate on the second copy, through the antilinear involution of `C` over the boundary with
fixed set `F`. It is `TauCeti.FiniteRankBundleCore.doubleAlong` along the boundary
(`doubledBundleCore_eq`), and `TauCeti.SchottkyDouble M` is a reducible abbreviation of the double
along the boundary, so after rewriting with `doubledBundleCore_eq` the general API applies:

* `TauCeti.FiniteRankBundleCore.doubleAlongInlIso` and
  `TauCeti.FiniteRankBundleCore.doubleAlongInrIso`: the doubled bundle is `C` on the first copy and
  its conjugate on the second copy.
* `TauCeti.FiniteRankBundleCore.doubleAlongSwap`: the lift of the antiholomorphic involution
  `TauCeti.DoubleAlong.swap` of the Schottky double to a conjugate-linear involution of the
  doubled bundle (`proj_doubleAlongSwap`, `doubleAlongSwap_doubleAlongSwap`).
* `TauCeti.FiniteRankBundleCore.doubleAlongSwap_mk_inl_eq_self_iff`: over a boundary point the
  fixed vectors of the lift are exactly the vectors of `F`.

## Smoothness through a collar projection

The doubled transitions are the transitions of `C` on the first copy and their conjugates on the
second copy, so they are continuous but in general not differentiable across the seam. They are
smooth when `C` is constant along the fibres of a collar projection near the boundary:

* `TauCeti.SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore`: if the transitions of `C` are
  real `C^n` on `M`, and constant along the fibres of a map `ρ` from an open neighbourhood of the
  boundary into the boundary which is `C^n` when read on the double through the fold, then the
  transitions of the doubled bundle are real `C^n` on the Schottky double.
* `TauCeti.SchottkyDouble.contMDiff_doubleAlongSwap`: the lifted involution is real `C^n` on the
  total space of the doubled bundle, with no regularity hypothesis on `C`.

Every smooth bundle pair is isomorphic to one constant along a collar projection
(`TauCeti.SchottkyDouble.exists_iso_contMDiffOn_coordChange_doubledBundleCore`, in
`TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle.CollarForm`). Not treated
here: independence of that choice up to isomorphism.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.3.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SchottkyDouble

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]

/-- The doubled bundle `E_F` over the Schottky double of a Riemann surface with boundary `M`, for a
complex core `C` over `M` whose transitions are real at the boundary: `C` on the first copy of `M`
and its conjugate on the second copy, glued along the boundary. -/
noncomputable def doubledBundleCore (C : FiniteRankBundleCore ℂ M)
    (hC : C.IsRealAlong (borderedInterior M : Set M)ᶜ) :
    FiniteRankBundleCore ℂ (SchottkyDouble M) :=
  C.doubleAlong hC

theorem doubledBundleCore_eq (C : FiniteRankBundleCore ℂ M)
    (hC : C.IsRealAlong (borderedInterior M : Set M)ᶜ) :
    doubledBundleCore C hC = C.doubleAlong hC := (rfl)

@[simp] theorem rank_doubledBundleCore (C : FiniteRankBundleCore ℂ M)
    (hC : C.IsRealAlong (borderedInterior M : Set M)ᶜ) :
    (doubledBundleCore C hC).rank = C.rank := (rfl)

/-! ### Smoothness through a collar projection -/

local notation "A" => (borderedInterior M : Set M)ᶜ

open Filter Topology in
/-- Off the seam, a doubled transition is `C^n` where the transition of `C` is: the fold is a local
diffeomorphism onto the interior, followed on the second copy by conjugation of operators. -/
private theorem contMDiffAt_doubleAlongCoordChange_of_mem_borderedInterior
    (C : FiniteRankBundleCore ℂ M) {n : ℕ∞ω} {i j y : SchottkyDouble M}
    (hg : ContMDiffAt closedUpperHalfPlaneModel 𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) n
      (C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j)) (DoubleAlong.fold A y))
    (hyI : DoubleAlong.fold A y ∈ borderedInterior M) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) n
      (FiniteRankBundleCore.doubleAlongCoordChange C A i j) y := by
  induction y using DoubleAlong.induction_on with
  | hl x =>
    simp only [DoubleAlong.fold_inl] at hyI hg
    have hN : Set.range (interiorInl M) ∈ 𝓝 (DoubleAlong.inl A x) :=
      isOpenEmbedding_interiorInl.isOpen_range.mem_nhds ⟨⟨x, hyI⟩, interiorInl_apply _⟩
    refine (hg.comp_of_eq (contMDiffAt_fold_inl hyI)
      (DoubleAlong.fold_inl A x)).congr_of_eventuallyEq ?_
    filter_upwards [hN] with z hz
    obtain ⟨u, rfl⟩ := hz
    simp only [interiorInl_apply, Function.comp_apply, DoubleAlong.fold_inl,
      FiniteRankBundleCore.doubleAlongCoordChange_inl]
  | hr x =>
    simp only [DoubleAlong.fold_inr] at hyI hg
    have hN : Set.range (interiorInr M) ∈ 𝓝 (DoubleAlong.inr A x) :=
      isOpenEmbedding_interiorInr.isOpen_range.mem_nhds ⟨⟨x, hyI⟩, interiorInr_apply _⟩
    refine ((ContinuousLinearMap.intrinsicStarL (E := Fin C.rank → ℂ)
      (F := Fin C.rank → ℂ)).contMDiff.contMDiffAt.comp _ (hg.comp_of_eq
        (contMDiffAt_fold_inr hyI) (DoubleAlong.fold_inr A x))).congr_of_eventuallyEq ?_
    filter_upwards [hN] with z hz
    obtain ⟨u, rfl⟩ := hz
    simp only [interiorInr_apply, Function.comp_apply, DoubleAlong.fold_inr]
    rw [FiniteRankBundleCore.doubleAlongCoordChange_inr_of_notMem C i j fun h ↦ h u.property,
      ContinuousLinearMap.intrinsicStarL_apply]

open Filter Topology in
/-- **Smoothness of the doubled bundle through a collar projection.** Let the transitions of `C` be
real `C^n` on `M`, and let `ρ : M → M` be a collar projection on an open neighbourhood `U` of the
boundary: it maps `U` into the boundary, it is `C^n` when read on the Schottky double through the
fold, and the transitions of `C` are constant along its fibres in `U`. Then the transitions of the
doubled bundle are real `C^n` on the Schottky double.

Near the seam both copies of a doubled transition are the transition of `C` at the collar
projection, which is real there. Away from the seam the fold is a local diffeomorphism onto the
interior of `M`, followed on the second copy by conjugation of operators. -/
theorem contMDiffOn_coordChange_doubledBundleCore (C : FiniteRankBundleCore ℂ M)
    (hC : C.IsRealAlong (borderedInterior M : Set M)ᶜ) {n : ℕ∞ω}
    (hg : ∀ i j, ContMDiffOn closedUpperHalfPlaneModel
      𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) n
      (C.core.coordChange i j) (C.core.baseSet i ∩ C.core.baseSet j))
    {U : Set M} (hU : IsOpen U) (hAU : (borderedInterior M : Set M)ᶜ ⊆ U) {ρ : M → M}
    (hρA : Set.MapsTo ρ U (borderedInterior M : Set M)ᶜ)
    (hρ : ContMDiffOn 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel n
      (ρ ∘ DoubleAlong.fold (borderedInterior M : Set M)ᶜ)
      (DoubleAlong.fold (borderedInterior M : Set M)ᶜ ⁻¹' U))
    (hCρ : ∀ i j x, x ∈ U → x ∈ C.core.baseSet i → x ∈ C.core.baseSet j →
      ρ x ∈ C.core.baseSet i ∧ ρ x ∈ C.core.baseSet j ∧
        C.core.coordChange i j (ρ x) = C.core.coordChange i j x)
    (i j : SchottkyDouble M) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin (doubledBundleCore C hC).rank → ℂ) →L[ℂ]
      (Fin (doubledBundleCore C hC).rank → ℂ)) n
      ((doubledBundleCore C hC).core.coordChange i j)
      ((doubledBundleCore C hC).core.baseSet i ∩ (doubledBundleCore C hC).core.baseSet j) := by
  set i' := DoubleAlong.fold A i
  set j' := DoubleAlong.fold A j
  set g := C.core.coordChange i' j'
  set S := C.core.baseSet i' ∩ C.core.baseSet j'
  have hS : IsOpen S := (C.core.isOpen_baseSet _).inter (C.core.isOpen_baseSet _)
  have hfold := (DoubleAlong.fold A).continuous
  have hgS : ∀ x ∈ S, ContMDiffAt closedUpperHalfPlaneModel
      𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) n g x :=
    fun x hx ↦ (hg i' j').contMDiffAt (hS.mem_nhds hx)
  intro y hy
  rw [doubledBundleCore_eq, Set.mem_inter_iff, FiniteRankBundleCore.mem_baseSet_doubleAlong,
    FiniteRankBundleCore.mem_baseSet_doubleAlong] at hy
  have hyS : DoubleAlong.fold A y ∈ S := hy
  refine ContMDiffAt.contMDiffWithinAt ?_
  -- The doubled core has rank `C.rank` and transitions `doubleAlongCoordChange C A`, both by
  -- definition (`doubledBundleCore_eq`, `rank_doubleAlong`, `coordChange_doubleAlong`). The rank
  -- occurs in the model of the target, so the statement is restated rather than rewritten.
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) n
    (FiniteRankBundleCore.doubleAlongCoordChange C A i j) y
  by_cases hyU : DoubleAlong.fold A y ∈ U
  · -- Near the seam the doubled transition is the transition of `C` at the collar projection.
    have hN : DoubleAlong.fold A ⁻¹' (U ∩ S) ∈ 𝓝 y :=
      ((hU.inter hS).preimage hfold).mem_nhds ⟨hyU, hyS⟩
    have hρy := hCρ i' j' _ hyU hyS.1 hyS.2
    refine ((hgS _ ⟨hρy.1, hρy.2.1⟩).comp y
      (hρ.contMDiffAt ((hU.preimage hfold).mem_nhds hyU))).congr_of_eventuallyEq ?_
    filter_upwards [hN] with z hz
    obtain ⟨hzU, hzi, hzj⟩ := hz
    obtain ⟨hρi, hρj, hρg⟩ := hCρ i' j' _ hzU hzi hzj
    simp only [Function.comp_apply]
    induction z using DoubleAlong.induction_on with
    | hl x =>
      simp only [DoubleAlong.fold_inl] at hρg ⊢
      rw [FiniteRankBundleCore.doubleAlongCoordChange_inl, ← hρg]
    | hr x =>
      simp only [DoubleAlong.fold_inr] at hzU hzi hzj hρg hρi hρj ⊢
      rw [FiniteRankBundleCore.doubleAlongCoordChange_inr hC hzi hzj, ← hρg]
      ext v : 1
      rw [ContinuousLinearMap.intrinsicStar_apply, WithConv.ofConv_toConv,
        hC.coordChange_star (hρA hzU) hρi hρj, star_star]
  · exact contMDiffAt_doubleAlongCoordChange_of_mem_borderedInterior C (hgS _ hyS)
      (not_not.1 fun h ↦ hyU (hAU h))

open Bundle Filter Topology in
/-- **The lifted involution is smooth.** The lift `FiniteRankBundleCore.doubleAlongSwap` of the
sheet swap to the doubled bundle is real `C^n` on the total space for every `n`. In the
trivialization at a point it is coordinatewise conjugation of the coordinates in the
trivialization at the swapped point, so no regularity of the transitions of `C` is needed. -/
theorem contMDiff_doubleAlongSwap (C : FiniteRankBundleCore ℂ M) (hC : C.IsRealAlong A)
    {n : ℕ∞ω} :
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, Fin (C.doubleAlong hC).rank → ℂ))
      (𝓘(ℝ, ℂ).prod 𝓘(ℝ, Fin (C.doubleAlong hC).rank → ℂ)) n (C.doubleAlongSwap hC) := by
  set D := C.doubleAlong hC
  intro p
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨?_, ?_⟩
  · simp only [FiniteRankBundleCore.proj_doubleAlongSwap]
    exact (contMDiff_swap.comp (contMDiff_proj D.core.Fiber)).contMDiffAt
  have hsrc : (D.core.localTriv p.proj).source ∈ 𝓝 p :=
    (D.core.localTriv p.proj).open_source.mem_nhds (D.mem_baseSet_self p.proj)
  refine ((starL' ℝ : (Fin D.rank → ℂ) ≃L[ℝ] _).contDiff.comp_contMDiffAt
    (p.contMDiffAt_trivializationAt_snd (IB := 𝓘(ℝ, ℂ)))).congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with q hq
  rw [VectorBundleCore.mem_localTriv_source] at hq
  simp only [FiniteRankBundleCore.proj_doubleAlongSwap, D.trivializationAt_core,
    Function.comp_apply, starL'_apply, VectorBundleCore.localTriv_apply, D.indexAt_eq,
    FiniteRankBundleCore.snd_doubleAlongSwap]
  exact FiniteRankBundleCore.doubleAlongCoordChange_swap C hC (D.mem_baseSet_self q.proj) hq
    q.snd

end TauCeti.SchottkyDouble
