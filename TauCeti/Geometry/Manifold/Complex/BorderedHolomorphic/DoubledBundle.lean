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

* `TauCeti.SchottkyDouble.contMDiffOn_of_eq_sheets_of_collar`: an operator-valued function on the
  Schottky double which, over an open set `S ⊆ M`, is `g` on the first copy and the intrinsic
  conjugate of `g` on the second copy is real `C^n` on the preimage of `S` under the fold, if `g`
  is real `C^n` on `S` and, on `U ∩ S`, constant along the fibres of a map `ρ` from an open
  neighbourhood `U` of the boundary which maps `U` into the boundary and `U ∩ S` into `S`, and is
  `C^n` when read on the double through the fold.
* `TauCeti.SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore`: if the transitions of `C` are
  real `C^n` on `M`, and constant along the fibres of such a `ρ`, then the transitions of the
  doubled bundle are real `C^n` on the Schottky double.
* `TauCeti.SchottkyDouble.contMDiff_doubleAlongSwap`: the lifted involution is real `C^n` on the
  total space of the doubled bundle, with no regularity hypothesis on `C`.

If `M` is Hausdorff (`T2Space`) and second countable (`SecondCountableTopology`) with compact
boundary, every bundle pair `(C, F)` with real `C^n` transitions is isomorphic, by an isomorphism
with real `C^n` chart operators in both directions which commutes with conjugation over the
boundary, to a bundle pair with real `C^n` transitions and smooth doubled transitions, real `C^n`
on the Schottky double
(`TauCeti.SchottkyDouble.exists_iso_contMDiffOn_coordChange_doubledBundleCore`, in
`TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle.CollarForm`). Its doubled
bundle is isomorphic to `doubledBundleCore C hC`, compatibly with the lifted involutions, through
`TauCeti.FiniteRankBundleCore.doubleAlongIso`, whatever choices the collar form was built from.

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

section Collar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [StarAddMonoid E]
  [StarModule ℂ E] [ContinuousStar E] [FiniteDimensional ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F] [ContinuousStar F]

open Filter Topology WithConv in
/-- Off the seam, an operator-valued function on the Schottky double which is `g` on the first copy
and its intrinsic conjugate on the second copy is `C^n` where `g` is: the fold is a local
diffeomorphism onto the interior, followed on the second copy by conjugation of operators. -/
private theorem contMDiffAt_of_eq_sheets_of_mem_borderedInterior {n : ℕ∞ω} {S : Set M}
    (hS : IsOpen S) {g : M → E →L[ℂ] F} {h : SchottkyDouble M → E →L[ℂ] F}
    (hl : ∀ x ∈ S, h (DoubleAlong.inl A x) = g x)
    (hr : ∀ x ∈ S, h (DoubleAlong.inr A x) = (star (toConv (g x))).ofConv) {y : SchottkyDouble M}
    (hg : ContMDiffAt closedUpperHalfPlaneModel 𝓘(ℝ, E →L[ℂ] F) n g (DoubleAlong.fold A y))
    (hyS : DoubleAlong.fold A y ∈ S) (hyI : DoubleAlong.fold A y ∈ borderedInterior M) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E →L[ℂ] F) n h y := by
  have hSN : DoubleAlong.fold A ⁻¹' S ∈ 𝓝 y :=
    (hS.preimage (DoubleAlong.fold A).continuous).mem_nhds hyS
  induction y using DoubleAlong.induction_on with
  | hl x =>
    simp only [DoubleAlong.fold_inl] at hyI hg
    have hN : Set.range (interiorInl M) ∈ 𝓝 (DoubleAlong.inl A x) :=
      isOpenEmbedding_interiorInl.isOpen_range.mem_nhds ⟨⟨x, hyI⟩, interiorInl_apply _⟩
    refine (hg.comp_of_eq (contMDiffAt_fold_inl hyI)
      (DoubleAlong.fold_inl A x)).congr_of_eventuallyEq ?_
    filter_upwards [hN, hSN] with z hz hzS
    obtain ⟨u, rfl⟩ := hz
    simp only [interiorInl_apply, Set.mem_preimage, DoubleAlong.fold_inl] at hzS ⊢
    rw [hl _ hzS, Function.comp_apply, DoubleAlong.fold_inl]
  | hr x =>
    simp only [DoubleAlong.fold_inr] at hyI hg
    have hN : Set.range (interiorInr M) ∈ 𝓝 (DoubleAlong.inr A x) :=
      isOpenEmbedding_interiorInr.isOpen_range.mem_nhds ⟨⟨x, hyI⟩, interiorInr_apply _⟩
    refine ((ContinuousLinearMap.intrinsicStarL (E := E) (F := F)).contMDiff.contMDiffAt.comp _
      (hg.comp_of_eq (contMDiffAt_fold_inr hyI)
        (DoubleAlong.fold_inr A x))).congr_of_eventuallyEq ?_
    filter_upwards [hN, hSN] with z hz hzS
    obtain ⟨u, rfl⟩ := hz
    simp only [interiorInr_apply, Set.mem_preimage, DoubleAlong.fold_inr] at hzS ⊢
    rw [hr _ hzS, Function.comp_apply, ContinuousLinearMap.intrinsicStarL_apply,
      Function.comp_apply, DoubleAlong.fold_inr]

open Filter Topology WithConv in
/-- **Smoothness on the Schottky double through a collar projection.** Let `h` be an
operator-valued function on the Schottky double which, over an open set `S ⊆ M`, is `g` on the
first copy of `M` and the intrinsic conjugate `star ∘ g ∘ star` of `g` on the second copy. Let `g`
be real `C^n` on `S`, and let `ρ : M → M` be a collar projection on an open neighbourhood `U` of the
boundary: it maps `U` into the boundary and `U ∩ S` into `S`, it is `C^n` when read on the double
through the fold, and `g` is constant along its fibres in `U ∩ S`. Then `h` is real `C^n` on the
preimage of `S` under the fold. Applied to the transitions of a bundle pair this is
`contMDiffOn_coordChange_doubledBundleCore`. -/
theorem contMDiffOn_of_eq_sheets_of_collar {n : ℕ∞ω} {S : Set M} (hS : IsOpen S)
    {g : M → E →L[ℂ] F} (hg : ContMDiffOn closedUpperHalfPlaneModel 𝓘(ℝ, E →L[ℂ] F) n g S)
    {h : SchottkyDouble M → E →L[ℂ] F} (hl : ∀ x ∈ S, h (DoubleAlong.inl A x) = g x)
    (hr : ∀ x ∈ S, h (DoubleAlong.inr A x) = (star (toConv (g x))).ofConv)
    {U : Set M} (hU : IsOpen U) (hAU : (borderedInterior M : Set M)ᶜ ⊆ U) {ρ : M → M}
    (hρA : Set.MapsTo ρ U (borderedInterior M : Set M)ᶜ)
    (hρ : ContMDiffOn 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel n
      (ρ ∘ DoubleAlong.fold (borderedInterior M : Set M)ᶜ)
      (DoubleAlong.fold (borderedInterior M : Set M)ᶜ ⁻¹' U))
    (hgρ : ∀ x ∈ U ∩ S, ρ x ∈ S ∧ g (ρ x) = g x) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E →L[ℂ] F) n h (DoubleAlong.fold A ⁻¹' S) := by
  have hfold := (DoubleAlong.fold A).continuous
  intro y hyS
  refine ContMDiffAt.contMDiffWithinAt ?_
  by_cases hyU : DoubleAlong.fold A y ∈ U
  · -- Near the seam `h` is `g` at the collar projection on both copies, since `g` is constant
    -- along `ρ` and real on its image: the boundary points of `S` lie on both copies.
    obtain ⟨hρS, -⟩ := hgρ _ ⟨hyU, hyS⟩
    refine ((hg.contMDiffAt (hS.mem_nhds hρS)).comp y
      (hρ.contMDiffAt ((hU.preimage hfold).mem_nhds hyU))).congr_of_eventuallyEq ?_
    filter_upwards [((hU.inter hS).preimage hfold).mem_nhds ⟨hyU, hyS⟩] with z hz
    obtain ⟨hzρS, hzρ⟩ := hgρ _ hz
    simp only [Function.comp_apply]
    induction z using DoubleAlong.induction_on with
    | hl x =>
      simp only [Set.mem_preimage, Set.mem_inter_iff, DoubleAlong.fold_inl] at hz hzρS hzρ ⊢
      rw [hl x hz.2, hzρ]
    | hr x =>
      simp only [Set.mem_preimage, Set.mem_inter_iff, DoubleAlong.fold_inr] at hz hzρS hzρ ⊢
      -- `g` is real at the boundary point `ρ x`, which lies on both copies.
      rw [hr x hz.2, ← hzρ, ← hr _ hzρS, ← DoubleAlong.inl_coe_eq_inr A ⟨ρ x, hρA hz.1⟩,
        hl _ hzρS]
  · -- Away from the seam the fold is a local diffeomorphism onto the interior of `M`, followed on
    -- the second copy by conjugation of operators.
    exact contMDiffAt_of_eq_sheets_of_mem_borderedInterior hS hl hr
      (hg.contMDiffAt (hS.mem_nhds hyS)) hyS (not_not.1 fun h ↦ hyU (hAU h))

end Collar

/-- **Smoothness of the doubled bundle through a collar projection.** Let the transitions of `C` be
real `C^n` on `M`, and let `ρ : M → M` be a collar projection on an open neighbourhood `U` of the
boundary: it maps `U` into the boundary, it is `C^n` when read on the Schottky double through the
fold, and the transitions of `C` are constant along its fibres in `U`. Then the transitions of the
doubled bundle are real `C^n` on the Schottky double.

The doubled transitions are those of `C` on the first copy and their conjugates on the second copy,
so this is `contMDiffOn_of_eq_sheets_of_collar`. -/
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
  -- The chart domains of the doubled core are the preimages of those of `C` under the fold.
  have hdom : (doubledBundleCore C hC).core.baseSet i ∩ (doubledBundleCore C hC).core.baseSet j =
      DoubleAlong.fold A ⁻¹' (C.core.baseSet (DoubleAlong.fold A i) ∩
        C.core.baseSet (DoubleAlong.fold A j)) := by
    ext y
    rw [doubledBundleCore_eq, Set.mem_inter_iff, FiniteRankBundleCore.mem_baseSet_doubleAlong,
      FiniteRankBundleCore.mem_baseSet_doubleAlong, Set.mem_preimage, Set.mem_inter_iff]
  rw [hdom]
  -- The doubled core has rank `C.rank` and transitions `doubleAlongCoordChange C A`, both by
  -- definition (`doubledBundleCore_eq`, `rank_doubleAlong`, `coordChange_doubleAlong`). The rank
  -- occurs in the model of the target, so the statement is restated rather than rewritten.
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) n
    (FiniteRankBundleCore.doubleAlongCoordChange C A i j) _
  exact contMDiffOn_of_eq_sheets_of_collar
    ((C.core.isOpen_baseSet _).inter (C.core.isOpen_baseSet _)) (hg _ _)
    (fun x _ ↦ FiniteRankBundleCore.doubleAlongCoordChange_inl C i j x)
    (fun x hx ↦ FiniteRankBundleCore.doubleAlongCoordChange_inr hC hx.1 hx.2) hU hAU hρA hρ
    fun x hx ↦ by
      obtain ⟨hρi, hρj, hρg⟩ := hCρ _ _ x hx.1 hx.2.1 hx.2.2
      exact ⟨⟨hρi, hρj⟩, hρg⟩

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
