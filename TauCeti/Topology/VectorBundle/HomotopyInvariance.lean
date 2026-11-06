/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.VectorBundle.Constructions
import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.Homotopy.CylinderSubdivision
import TauCeti.Topology.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Pullback

/-!
# Homotopy invariance of vector bundles over paracompact bases

Let `X` be a paracompact R₁ space, for instance a paracompact Hausdorff space, and let `E` be a
vector bundle over the cylinder `X × I` whose model fibre is a Banach space over a normed field
`𝕜` which is a normed `ℝ`-algebra, such as `ℝ` or `ℂ`.
`TauCeti.exists_continuousLinearEquiv_cylinder` identifies `E` with the pullback of its restriction
to `X × {0}` along `(x, t) ↦ (x, 0)`. The identification consists of continuous linear
equivalences `E (x, 0) ≃L[𝕜] E (x, t)` which are the identity at time `0`, and it is continuous on
total spaces together with its inverse. Consequently the pullbacks of a vector bundle along
homotopic maps out of `X` are isomorphic
(`ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`), so that isomorphism classes of
pulled-back bundles depend only on the homotopy class of the map, as homotopy invariance of
topological K-theory requires.

No finite cover, bounded rank or compactness of `X` is assumed. The proof transports fibres along
the time direction in three steps.

* On `X × I × I`, a partition of unity subordinate to the chart domains of `E`, with sum one on the
  closed diagonal `s = t`, averages the chart transports `E (x, s) → E (x, t)` into a family
  `T (x, s, t)` which is continuous in coordinates and is the identity on the diagonal. The
  average is not claimed to be invertible everywhere: invertibility is an open condition along such
  a family, so it holds on a neighbourhood of the diagonal.
* The locally terminating subdivision `TauCeti.exists_continuous_cylinder_subdivision` of this
  neighbourhood supplies a positive continuous step size `δ` on `X` and times
  `τ n (x, t) = min t (n * δ x / 2)`, with consecutive times in the neighbourhood.
* The transport from time `0` to time `t` composes the maps `T` between consecutive times. Near
  each base point a fixed number of steps reaches every time, after which all factors are
  identities, so locally the transport is a fixed finite composite.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.6, for homotopy invariance of
  pullbacks over paracompact bases, proved there by a different argument.
-/

public section

open Bundle Set Function ContinuousLinearMap
open scoped Topology unitInterval

namespace TauCeti

section Cylinder

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : X × I → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module 𝕜 (E q)]
  [∀ q, TopologicalSpace (E q)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

variable (𝕜 F E) in
/-- The transport from time `s` to time `t` over `x` given by one trivialization of `E`. -/
private noncomputable def chartTransport (z : X × I) (p : X × I × I) :
    E (p.1, p.2.1) →L[𝕜] E (p.1, p.2.2) :=
  ((trivializationAt F E z).symmL 𝕜 (p.1, p.2.2)).comp
    ((trivializationAt F E z).continuousLinearMapAt 𝕜 (p.1, p.2.1))

private theorem inCoordinates_chartTransport (z : X × I) {p : X × I × I}
    (ha : (p.1, p.2.1) ∈ (trivializationAt F E z).baseSet)
    (hb : (p.1, p.2.2) ∈ (trivializationAt F E z).baseSet) :
    inCoordinates F E F E z (p.1, p.2.1) z (p.1, p.2.2) (chartTransport 𝕜 F E z p) =
      ContinuousLinearMap.id 𝕜 F := by
  ext v
  simp [inCoordinates, chartTransport, Trivialization.continuousLinearMapAt_symmL _ ha,
    Trivialization.continuousLinearMapAt_symmL _ hb]

/-- In coordinates centred at `p₀`, a chart transport is continuous at every point of the region
where its chart is defined. -/
private theorem continuousAt_inCoordinates_chartTransport (z : X × I) {p₀ : X × I × I}
    (ha : (p₀.1, p₀.2.1) ∈ (trivializationAt F E z).baseSet)
    (hb : (p₀.1, p₀.2.2) ∈ (trivializationAt F E z).baseSet) :
    ContinuousAt (fun p : X × I × I ↦ inCoordinates F E F E (p₀.1, p₀.2.1) (p.1, p.2.1)
      (p₀.1, p₀.2.2) (p.1, p.2.2) (chartTransport 𝕜 F E z p)) p₀ := by
  set e := trivializationAt F E z
  set ea := trivializationAt F E (p₀.1, p₀.2.1)
  set eb := trivializationAt F E (p₀.1, p₀.2.2)
  have ha₀ : (p₀.1, p₀.2.1) ∈ ea.baseSet := mem_baseSet_trivializationAt F E _
  have hb₀ : (p₀.1, p₀.2.2) ∈ eb.baseSet := mem_baseSet_trivializationAt F E _
  have hfa : Continuous fun p : X × I × I ↦ (p.1, p.2.1) := by fun_prop
  have hfb : Continuous fun p : X × I × I ↦ (p.1, p.2.2) := by fun_prop
  have hA : ContinuousAt (fun p : X × I × I ↦ (ea.coordChangeL 𝕜 e (p.1, p.2.1) : F →L[𝕜] F)) p₀ :=
    ((continuousOn_coordChange 𝕜 ea e).continuousAt
      ((ea.open_baseSet.inter e.open_baseSet).mem_nhds ⟨ha₀, ha⟩)).comp
        (f := fun p : X × I × I ↦ (p.1, p.2.1)) hfa.continuousAt
  have hB : ContinuousAt (fun p : X × I × I ↦ (e.coordChangeL 𝕜 eb (p.1, p.2.2) : F →L[𝕜] F)) p₀ :=
    ((continuousOn_coordChange 𝕜 e eb).continuousAt
      ((e.open_baseSet.inter eb.open_baseSet).mem_nhds ⟨hb, hb₀⟩)).comp
        (f := fun p : X × I × I ↦ (p.1, p.2.2)) hfb.continuousAt
  refine (hB.clm_comp hA).congr ?_
  filter_upwards [hfa.continuousAt.preimage_mem_nhds
      ((ea.open_baseSet.inter e.open_baseSet).mem_nhds ⟨ha₀, ha⟩),
    hfb.continuousAt.preimage_mem_nhds
      ((e.open_baseSet.inter eb.open_baseSet).mem_nhds ⟨hb, hb₀⟩)] with p hpa hpb
  rw [inCoordinates_eq_coordChangeL_comp (x₁ := z) (y₁ := z) _ hpa.1 hpa.2 hpb.2 hpb.1,
    inCoordinates_chartTransport z hpa.2 hpb.1, ContinuousLinearMap.id_comp]

variable [NormedAlgebra ℝ 𝕜] [R1Space X] [ParacompactSpace X]
  [∀ q, IsTopologicalAddGroup (E q)] [∀ q, ContinuousSMul 𝕜 (E q)] in
/-- **Transport near the diagonal.** There is a continuous family of fibre maps from time `s` to
time `t` over each point of `X`, equal to the identity whenever `s = t`. It is a partition-of-unity
average of chart transports. -/
private theorem exists_diagonalTransport :
    ∃ T : ∀ p : X × I × I, E (p.1, p.2.1) →L[𝕜] E (p.1, p.2.2),
      (∀ p₀ : X × I × I, ContinuousAt (fun p : X × I × I ↦ inCoordinates F E F E
        (p₀.1, p₀.2.1) (p.1, p.2.1) (p₀.1, p₀.2.2) (p.1, p.2.2) (T p)) p₀) ∧
      ∀ x s, T (x, s, s) = ContinuousLinearMap.id 𝕜 (E (x, s)) := by
  classical
  let e : X × I → Trivialization F (π F E) := fun z ↦ trivializationAt F E z
  let V : X × I → Set (X × I × I) := fun z ↦
    {p | (p.1, p.2.1) ∈ (e z).baseSet ∧ (p.1, p.2.2) ∈ (e z).baseSet}
  have hV (z : X × I) : IsOpen (V z) :=
    ((e z).open_baseSet.preimage (by fun_prop)).inter ((e z).open_baseSet.preimage (by fun_prop))
  let D : Set (X × I × I) := {p | p.2.1 = p.2.2}
  have hD : IsClosed D := isClosed_eq (by fun_prop) (by fun_prop)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate hD V hV fun p hp ↦ by
    refine mem_iUnion.2 ⟨(p.1, p.2.1), mem_baseSet_trivializationAt F E _, ?_⟩
    rw [show p.2.2 = p.2.1 from (show p.2.1 = p.2.2 from hp).symm]
    exact mem_baseSet_trivializationAt F E _
  let w : X × I → X × I × I → 𝕜 := fun z p ↦ algebraMap ℝ 𝕜 (ρ z p)
  have hw (p : X × I × I) : support (fun z ↦ w z p • chartTransport 𝕜 F E z p) ⊆
      ρ.finsupport p := fun z hz ↦ (ρ.mem_finsupport p).2 fun h ↦ hz (by
        simp only [w]; rw [show ρ z p = 0 from h, map_zero, zero_smul])
  refine ⟨fun p ↦ ∑ᶠ z, w z p • chartTransport 𝕜 F E z p, fun p₀ ↦ ?_, fun x s ↦ ?_⟩
  · obtain ⟨J, hJ⟩ := ρ.locallyFinite.exists_finset_support p₀
    refine ContinuousAt.congr (f := fun p ↦ ∑ z ∈ J, w z p • inCoordinates F E F E
      (p₀.1, p₀.2.1) (p.1, p.2.1) (p₀.1, p₀.2.2) (p.1, p.2.2) (chartTransport 𝕜 F E z p))
      (tendsto_finsetSum J fun z _ ↦ ?_) ?_
    · by_cases hz : p₀ ∈ tsupport (ρ z)
      · exact ((continuous_algebraMap ℝ 𝕜).comp (ρ z).continuous).continuousAt.smul
          (continuousAt_inCoordinates_chartTransport z (hρ z hz).1 (hρ z hz).2)
      · refine (continuousAt_const (y := (0 : F →L[𝕜] F))).congr ?_
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz] with p hp
        simp [w, hp]
    · filter_upwards [hJ, (by fun_prop : Continuous fun p : X × I × I ↦ (p.1, p.2.2)).continuousAt
        |>.preimage_mem_nhds ((trivializationAt F E (p₀.1, p₀.2.2)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt F E _))] with p hp hpb
      rw [finsum_eq_sum_of_support_subset _ fun z hz ↦ hp ((ρ.mem_finsupport p).1 (hw p hz)),
        inCoordinates_finset_sum]
      exact Finset.sum_congr rfl fun z _ ↦ (inCoordinates_smul _ _ hpb).symm
  · have hp : ((x, s, s) : X × I × I) ∈ D := rfl
    have hterm (z : X × I) : w z (x, s, s) • chartTransport 𝕜 F E z (x, s, s) =
        w z (x, s, s) • ContinuousLinearMap.id 𝕜 (E (x, s)) := by
      by_cases h : ρ z (x, s, s) = 0
      · simp [w, h]
      · have hm := (hρ z (subset_tsupport _ h)).1
        congr 1
        exact ContinuousLinearMap.ext fun v ↦ Trivialization.symmL_continuousLinearMapAt _ hm v
    dsimp only
    rw [finsum_eq_sum_of_support_subset _ (hw _)]
    simp only [hterm, ← Finset.sum_smul, w, ← map_sum, ρ.sum_finsupport hp, map_one, one_smul]

section Chain

variable (T : ∀ p : X × I × I, E (p.1, p.2.1) →L[𝕜] E (p.1, p.2.2)) (τ : ℕ → C(X × I, I))

/-- The composite of the transports from time `0` through the subdivision times `τ 0`, …,
`τ n`. -/
private noncomputable def chain : (n : ℕ) → ∀ q : X × I, E (q.1, 0) →L[𝕜] E (q.1, τ n q)
  | 0, q => T (q.1, 0, τ 0 q)
  | n + 1, q => (T (q.1, τ n q, τ (n + 1) q)).comp (chain n q)

/-- The transport from time `0` to time `t` through the first `n + 1` subdivision times. -/
private noncomputable def transport (n : ℕ) (q : X × I) : E (q.1, 0) →L[𝕜] E q :=
  (T (q.1, τ n q, q.2)).comp (chain T τ n q)

variable {T τ} (hdiag : ∀ x s, T (x, s, s) = ContinuousLinearMap.id 𝕜 (E (x, s)))
include hdiag

omit [TopologicalSpace X] in
/-- Two transports between equal times compose to the transport between the outer times. -/
private theorem comp_eq_of_eq (x : X) {a b c : I} (hab : a = b) (hbc : b = c) :
    (T (x, b, c)).comp (T (x, a, b)) = T (x, a, c) := by
  subst hab hbc
  rw [hdiag, ContinuousLinearMap.id_comp]

omit [TopologicalSpace X] in
private theorem isInvertible_of_eq (x : X) {a b : I} (hab : a = b) :
    (T (x, a, b)).IsInvertible := by
  subst hab
  rw [hdiag]
  exact ⟨ContinuousLinearEquiv.refl 𝕜 _, rfl⟩

private theorem transport_eq_of_forall {q : X × I} {n m : ℕ} (hnm : n ≤ m)
    (h : ∀ k, n ≤ k → τ k q = q.2) :
    transport T τ m q = transport T τ n q := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    simp only [transport, chain, ← ContinuousLinearMap.comp_assoc] at ih ⊢
    rw [comp_eq_of_eq hdiag _ ((h m hm).trans (h (m + 1) (by omega)).symm) (h (m + 1) (by omega)),
      ih]

/-- Once the subdivision times have reached `t`, further steps do not change the transport. -/
private theorem transport_eq_transport {q : X × I} {n m : ℕ} (hn : ∀ k, n ≤ k → τ k q = q.2)
    (hm : ∀ k, m ≤ k → τ k q = q.2) :
    transport T τ n q = transport T τ m q := by
  have h (k : ℕ) (hk : min n m ≤ k) : τ k q = q.2 := by
    rcases (show n ≤ k ∨ m ≤ k by omega) with h | h
    exacts [hn k h, hm k h]
  rw [transport_eq_of_forall hdiag (min_le_left n m) h,
    transport_eq_of_forall hdiag (min_le_right n m) h]

/-- At time `0`, when all subdivision times are `0`, the transport is the identity. -/
private theorem transport_time_zero (x : X) (h : ∀ k, τ k (x, 0) = 0) (n : ℕ) :
    transport T τ n (x, 0) = ContinuousLinearMap.id 𝕜 (E (x, 0)) := by
  rw [transport_eq_of_forall hdiag (Nat.zero_le n) fun k _ ↦ h k]
  exact (comp_eq_of_eq hdiag x (h 0).symm (h 0)).trans (hdiag x 0)

omit hdiag in
private theorem isInvertible_chain (h₀ : ∀ q, (T (q.1, 0, τ 0 q)).IsInvertible)
    (hstep : ∀ n q, (T (q.1, τ n q, τ (n + 1) q)).IsInvertible) (n : ℕ) (q : X × I) :
    (chain T τ n q).IsInvertible := by
  induction n with
  | zero => exact h₀ q
  | succ n ih => exact (hstep n q).comp ih

variable (hcont : ∀ p₀ : X × I × I, ContinuousAt (fun p : X × I × I ↦ inCoordinates F E F E
  (p₀.1, p₀.2.1) (p.1, p.2.1) (p₀.1, p₀.2.2) (p.1, p.2.2) (T p)) p₀)
include hcont

omit hdiag in
private theorem continuousAt_chain (n : ℕ) (q₀ : X × I) :
    ContinuousAt (fun q : X × I ↦ inCoordinates F E F E (q₀.1, 0) (q.1, 0)
      (q₀.1, τ n q₀) (q.1, τ n q) (chain T τ n q)) q₀ := by
  induction n with
  | zero =>
    have h₀ := (τ 0).continuous
    exact (hcont _).comp (f := fun q : X × I ↦ (q.1, 0, τ 0 q)) (by fun_prop)
  | succ n ih =>
    have h₁ := (τ n).continuous
    have h₂ := (τ (n + 1)).continuous
    simp only [chain]
    exact ContinuousAt.inCoordinates_clm_comp (b₁ := fun q : X × I ↦ (q.1, (0 : I)))
      (b₂ := fun q : X × I ↦ (q.1, τ n q)) (b₃ := fun q : X × I ↦ (q.1, τ (n + 1) q))
      ((hcont _).comp (f := fun q : X × I ↦ (q.1, τ n q, τ (n + 1) q)) (by fun_prop)) ih
      (by fun_prop)

omit hdiag in
private theorem continuousAt_transport (n : ℕ) (q₀ : X × I) :
    ContinuousAt (fun q : X × I ↦ inCoordinates F E F E (q₀.1, 0) (q.1, 0) q₀ q
      (transport T τ n q)) q₀ := by
  have h₁ := (τ n).continuous
  exact ContinuousAt.inCoordinates_clm_comp (b₁ := fun q : X × I ↦ (q.1, (0 : I)))
    (b₂ := fun q : X × I ↦ (q.1, τ n q)) (b₃ := fun q : X × I ↦ q)
    ((hcont _).comp (f := fun q : X × I ↦ (q.1, τ n q, q.2)) (by fun_prop))
    (continuousAt_chain hcont n q₀) (by fun_prop)

end Chain

variable [NormedAlgebra ℝ 𝕜] [R1Space X] [ParacompactSpace X]
  [∀ q, IsTopologicalAddGroup (E q)] [∀ q, ContinuousSMul 𝕜 (E q)]

/-- **Cylinder transport.** There is a family of invertible fibre maps
`E (x, 0) →L[𝕜] E (x, t)`, continuous in coordinates and equal to the identity at time `0`. It is
the composite of transports near the diagonal along a locally terminating subdivision of `[0, t]`.
-/
private theorem exists_cylinderTransport [CompleteSpace F] :
    ∃ Φ : ∀ q : X × I, E (q.1, 0) →L[𝕜] E q, (∀ q, (Φ q).IsInvertible) ∧
      (∀ q₀ : X × I, ContinuousAt
        (fun q ↦ inCoordinates F E F E (q₀.1, 0) (q.1, 0) q₀ q (Φ q)) q₀) ∧
      ∀ x, Φ (x, 0) = ContinuousLinearMap.id 𝕜 (E (x, 0)) := by
  obtain ⟨T, hTc, hTd⟩ := exists_diagonalTransport (𝕜 := 𝕜) (F := F) (E := E)
  have hW : IsOpen {p : X × I × I | (T p).IsInvertible} := isOpen_iff_mem_nhds.2 fun p hp ↦
    ContinuousAt.eventually_isInvertible_of_inCoordinates
      (b₁ := fun p : X × I × I ↦ (p.1, p.2.1)) (b₂ := fun p : X × I × I ↦ (p.1, p.2.2))
      (hTc p) (by fun_prop) (by fun_prop) hp
  obtain ⟨δ, τ, hδ, -, hτ, hτ₀, hτW, hterm⟩ :=
    exists_continuous_cylinder_subdivision hW fun x t ↦ isInvertible_of_eq hTd x rfl
  -- Near each base point, a fixed number `N x` of steps reaches every time.
  choose N hN using hterm
  have hNq (q : X × I) : ∀ k, N q.1 ≤ k → τ k q = q.2 := fun k hk ↦ (hN q.1).self_of_nhds k hk q.2
  refine ⟨fun q ↦ transport T τ (N q.1) q, fun q ↦ ?_, fun q₀ ↦ ?_, fun x ↦ ?_⟩
  · exact (isInvertible_of_eq hTd _ (hNq q _ le_rfl)).comp (isInvertible_chain
      (fun q ↦ isInvertible_of_eq hTd _ (hτ₀ q.1 q.2).symm) (fun n q ↦ hτW n q.1 q.2) _ _)
  · refine (continuousAt_transport (τ := τ) hTc (N q₀.1) q₀).congr ?_
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hN q₀.1)] with q hq
    exact congrArg (inCoordinates F E F E (q₀.1, 0) (q.1, 0) q₀ q)
      (transport_eq_transport hTd (fun k hk ↦ hq k hk q.2) (hNq q))
  · refine transport_time_zero hTd x (fun k ↦ Subtype.ext ?_) _
    rw [hτ, Icc.coe_zero, min_eq_left (by have := (hδ x).1; positivity)]

/-- **Homotopy invariance of vector bundles over a cylinder.** Let `X` be paracompact and R₁, for
instance paracompact Hausdorff. A vector bundle `E` over `X × I` is isomorphic to the pullback of
its restriction to `X × {0}` along `(x, t) ↦ (x, 0)`: there are fibrewise continuous linear
equivalences `Φ (x, t) : E (x, 0) ≃L[𝕜] E (x, t)`, equal to the identity at time `0`, such that `Φ`
and its inverse are continuous on total spaces. The model fibre `F` may be any Banach space. -/
theorem exists_continuousLinearEquiv_cylinder [CompleteSpace F] :
    ∃ Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q,
      Continuous (fun v : TotalSpace F ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) ↦
        TotalSpace.mk' F v.proj (Φ v.proj v.2)) ∧
      Continuous (fun v : TotalSpace F E ↦ TotalSpace.mk' F
        (E := (fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) v.proj ((Φ v.proj).symm v.2)) ∧
      ∀ x, Φ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0)) := by
  obtain ⟨Φ', hinv, hc, h0⟩ := exists_cylinderTransport (𝕜 := 𝕜) (F := F) (E := E)
  choose Φ hΦ using hinv
  have hΦc (q₀ : X × I) : ContinuousAt (fun q ↦ inCoordinates F E F E (q₀.1, 0) (q.1, 0) q₀ q
      (Φ q : E (q.1, 0) →L[𝕜] E q)) q₀ := by
    simpa only [hΦ] using hc q₀
  have hΦi (q₀ : X × I) : ContinuousAt (fun q ↦ inCoordinates F E F E q₀ q (q₀.1, 0) (q.1, 0)
      ((Φ q).symm : E q →L[𝕜] E (q.1, 0))) q₀ := by
    simpa only [← inverse_equiv] using ContinuousAt.inCoordinates_clm_inverse
      (b₁ := fun q : X × I ↦ (q.1, (0 : I))) (b₂ := fun q : X × I ↦ q)
      (hΦc q₀) (by fun_prop) continuousAt_id isInvertible_equiv
  refine ⟨Φ, continuous_iff_continuousAt.2 fun v₀ ↦ ?_,
    Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj F E,
      continuous_iff_continuousAt.2 fun v₀ ↦ ?_⟩, fun x ↦ ?_⟩
  · exact ContinuousAt.clm_apply_of_inCoordinates
      (b₁ := fun v : TotalSpace F ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) ↦ (v.proj.1, (0 : I)))
      (b₂ := TotalSpace.proj) (ϕ := fun v ↦ (Φ v.proj : E (v.proj.1, 0) →L[𝕜] E v.proj))
      (v := fun v ↦ v.2)
      ((hΦc v₀.proj).comp (Pullback.continuous_proj F E _).continuousAt)
      (Pullback.continuous_lift F E _).continuousAt (Pullback.continuous_proj F E _).continuousAt
  · exact ContinuousAt.clm_apply_of_inCoordinates
      (b₁ := TotalSpace.proj) (b₂ := fun v : TotalSpace F E ↦ (v.proj.1, (0 : I)))
      (ϕ := fun v ↦ ((Φ v.proj).symm : E v.proj →L[𝕜] E (v.proj.1, 0))) (v := fun v ↦ v.2)
      ((hΦi v₀.proj).comp (FiberBundle.continuous_proj F E).continuousAt) continuousAt_id
      ((continuous_fst.comp (FiberBundle.continuous_proj F E)).prodMk continuous_const).continuousAt
  · ext v
    rw [ContinuousLinearEquiv.refl_apply, ← ContinuousLinearEquiv.coe_coe, hΦ, h0,
      ContinuousLinearMap.id_apply]

end Cylinder

section Homotopy

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {X : Type*} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type*} [TopologicalSpace Y]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
  [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ y, IsTopologicalAddGroup (E y)] [∀ y, ContinuousSMul 𝕜 (E y)]

/-- The endpoint form of the cylinder theorem: for a continuous `G : X × I → Y`, the pullbacks of
`E` along `G (·, 0)` and `G (·, 1)` are isomorphic. The two maps are given by functions `g₀`, `g₁`
equal to them. -/
private theorem exists_continuousLinearEquiv_pullback_of_eq (G : C(X × I, Y)) {g₀ g₁ : X → Y}
    (h₀ : ∀ x, G (x, 0) = g₀ x) (h₁ : ∀ x, G (x, 1) = g₁ x) :
    ∃ Φ : ∀ x, E (g₀ x) ≃L[𝕜] E (g₁ x),
      Continuous (fun v : TotalSpace F (g₀ *ᵖ E) ↦
        TotalSpace.mk' F (E := g₁ *ᵖ E) v.proj (Φ v.proj v.2)) ∧
      Continuous (fun v : TotalSpace F (g₁ *ᵖ E) ↦
        TotalSpace.mk' F (E := g₀ *ᵖ E) v.proj ((Φ v.proj).symm v.2)) := by
  obtain rfl : g₀ = fun x ↦ G (x, 0) := (funext h₀).symm
  obtain rfl : g₁ = fun x ↦ G (x, 1) := (funext h₁).symm
  obtain ⟨Φ, hΦ₁, hΦ₂, -⟩ :=
    exists_continuousLinearEquiv_cylinder (𝕜 := 𝕜) (F := F) (E := (G : X × I → Y) *ᵖ E)
  refine ⟨fun x ↦ Φ (x, 1), Pullback.continuous_iff.2 ⟨Pullback.continuous_proj F E _, ?_⟩,
    Pullback.continuous_iff.2 ⟨Pullback.continuous_proj F E _, ?_⟩⟩
  · -- Insert the fibre over `x` as the fibre over `(x, 1)` of the pulled-back cylinder.
    have hι : Continuous fun v : TotalSpace F ((fun x ↦ G (x, 0)) *ᵖ E) ↦
        (TotalSpace.mk' F (E := (fun q : X × I ↦ (q.1, (0 : I))) *ᵖ ((G : X × I → Y) *ᵖ E))
          (v.proj, 1) v.2) :=
      Pullback.continuous_iff.2 ⟨(Pullback.continuous_proj F E _).prodMk continuous_const,
        Pullback.continuous_iff.2 ⟨(Pullback.continuous_proj F E _).prodMk continuous_const,
          Pullback.continuous_lift F E _⟩⟩
    exact (Pullback.continuous_lift F E (G : X × I → Y)).comp (hΦ₁.comp hι)
  · have hι : Continuous fun v : TotalSpace F ((fun x ↦ G (x, 1)) *ᵖ E) ↦
        (TotalSpace.mk' F (E := (G : X × I → Y) *ᵖ E) (v.proj, 1) v.2) :=
      Pullback.continuous_iff.2 ⟨(Pullback.continuous_proj F E _).prodMk continuous_const,
        Pullback.continuous_lift F E _⟩
    exact (Pullback.continuous_lift F E (G : X × I → Y)).comp
      ((Pullback.continuous_lift F ((G : X × I → Y) *ᵖ E) _).comp (hΦ₂.comp hι))

/-- **Homotopy invariance of vector bundles.** Over a paracompact Hausdorff space `X`, the
pullbacks of a vector bundle `E` along homotopic maps `f₀ f₁ : C(X, Y)` are isomorphic: there are
fibrewise continuous linear equivalences `E (f₀ x) ≃L[𝕜] E (f₁ x)`, continuous on total spaces
together with their inverses. -/
theorem _root_.ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback {f₀ f₁ : C(X, Y)}
    (h : f₀.Homotopic f₁) :
    ∃ Φ : ∀ x, E (f₀ x) ≃L[𝕜] E (f₁ x),
      Continuous (fun v : TotalSpace F ((f₀ : X → Y) *ᵖ E) ↦
        TotalSpace.mk' F (E := (f₁ : X → Y) *ᵖ E) v.proj (Φ v.proj v.2)) ∧
      Continuous (fun v : TotalSpace F ((f₁ : X → Y) *ᵖ E) ↦
        TotalSpace.mk' F (E := (f₀ : X → Y) *ᵖ E) v.proj ((Φ v.proj).symm v.2)) := by
  obtain ⟨H⟩ := h
  exact exists_continuousLinearEquiv_pullback_of_eq (H.toContinuousMap.comp .prodSwap)
    H.apply_zero H.apply_one

end Homotopy

end TauCeti
