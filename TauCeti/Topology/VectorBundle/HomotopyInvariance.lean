/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Pullback
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Topology.Homotopy.CylinderSubdivision
import TauCeti.Topology.VectorBundle.Extension
import TauCeti.Topology.VectorBundle.Hom

/-!
# Homotopy invariance of vector bundles over paracompact bases

Let `X` be a paracompact R₁ space, for instance a paracompact Hausdorff space, and let `E` be a
vector bundle over the cylinder `X × I` whose model fibre is a Banach space over a normed field
`𝕜` which is a normed `ℝ`-algebra, such as `ℝ` or `ℂ`.
`TauCeti.exists_continuousLinearEquiv_cylinder` identifies `E` with the pullback of its restriction
to `X × {0}` along `(x, t) ↦ (x, 0)`. The identification consists of continuous linear
equivalences `E (x, 0) ≃L[𝕜] E (x, t)` which are the identity at time `0`; they form a continuous
section of the Hom bundle (`TauCeti.exists_continuous_hom_bundle_cylinder`) and are continuous on
total spaces together with their inverses. Consequently the pullbacks of a vector bundle along
homotopic maps out of `X` are isomorphic
(`ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`), so that isomorphism classes of
pulled-back bundles depend only on the homotopy class of the map, as homotopy invariance of
topological K-theory requires.

When the model endomorphism space `F →L[𝕜] F` has the Tietze extension property (in particular for
every finite-rank real or complex vector bundle), a cylinder identification already specified over
`s × I` for a closed subset `s ⊆ X` and equal to the identity on `s × {0}` extends to all of
`X × I` (`TauCeti.exists_continuousLinearEquiv_cylinder_of_isClosed` and the finite-rank total-space
version `TauCeti.exists_continuousLinearEquiv_cylinder_of_isClosed_of_continuous`). Applied to a
homotopy relative to `s`, this yields pullback bundle equivalences along homotopic-rel-`s` maps that
are the identity over `s` (`ContinuousMap.HomotopicRel.exists_continuousLinearEquiv_pullback`).

No finite cover, bounded rank or compactness of `X` is assumed. The unconstrained proof transports
fibres along the time direction in three steps, and the relative extension compares a given partial
transport with an unconstrained global transport via Tietze extension and the tube lemma.

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
* Given `Φ₀` over `s × I` equal to the identity at time `0`, composing `(Ψ₁ (x, t))⁻¹ ∘ Φ₀ (x, t)`
  on `s × I` with the identity on `X × {0}` defines a continuous invertible endomorphism of the
  zero-slice pullback bundle on the closed union `(s ×ˢ univ) ∪ (univ ×ˢ {0})`. Tietze section
  extension (`TauCeti.exists_continuous_section_extension`) extends it to `X × I`, invertible on an
  open neighbourhood `W`. By the generalized tube lemma on compact `I` and Urysohn's lemma on normal
  `X`, a continuous cutoff `ρ : C(X, ℝ)` with `ρ = 1` on `s` and `ρ = 0` outside `{x | {x} × I ⊆ W}`
  retracts `X × I` into `W` via `(x, t) ↦ (x, ρ x * t)`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.6 and Proposition 1.7, for cylinder
  transport, relative extension from closed subsets, and homotopy invariance of pullbacks over
  paracompact bases.
* M. F. Atiyah, *K-Theory*, §1.4, Lemma 1.4.3, for homotopy invariance and extension of bundle
  isomorphisms from closed subsets.
-/

public section

open Bundle FiberBundle Set Function ContinuousLinearMap
open scoped Topology unitInterval

namespace TauCeti

/-- Projection `(x, t) ↦ (x, 0)` of a cylinder onto its time-zero slice. -/
@[expose]
def cylinderZero (X : Type*) [TopologicalSpace X] : C(X × I, X × I) :=
  ⟨fun q ↦ (q.1, 0), continuous_fst.prodMk continuous_const⟩

@[simp]
theorem cylinderZero_apply {X : Type*} [TopologicalSpace X] (q : X × I) :
    cylinderZero X q = (q.1, 0) :=
  (rfl)

/-- Inclusion `s × I → X × I` of the cylinder over a subset `s ⊆ X`. -/
@[expose]
def cylinderSetIncl {X : Type*} [TopologicalSpace X] (s : Set X) : C(s × I, X × I) :=
  ⟨fun q ↦ (q.1.1, q.2), (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩

@[simp]
theorem cylinderSetIncl_apply {X : Type*} [TopologicalSpace X] (s : Set X) (q : s × I) :
    cylinderSetIncl s q = (q.1.1, q.2) :=
  (rfl)

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
    · filter_upwards [hJ] with p hp
      rw [finsum_eq_sum_of_support_subset _ fun z hz ↦ hp ((ρ.mem_finsupport p).1 (hw p hz)),
        inCoordinates_finset_sum]
      exact Finset.sum_congr rfl fun z _ ↦ (inCoordinates_smul _ _).symm
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

/-- **Hom-bundle continuity of cylinder transport.** Over a paracompact R₁ space `X`, a Banach
vector bundle `E` over `X × I` admits fibrewise continuous linear equivalences
`Φ (x, t) : E (x, 0) ≃L[𝕜] E (x, t)`, equal to the identity at time `0`, whose underlying
continuous linear maps form a continuous section of the Hom bundle from the zero-slice pullback
`(cylinderZero X : X × I → X × I) *ᵖ E` to `E`. -/
theorem exists_continuous_hom_bundle_cylinder [CompleteSpace F] :
    ∃ Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q,
      Continuous (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
        (E := fun r : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) r →L[𝕜] E r)
        q (Φ q : E (q.1, 0) →L[𝕜] E q)) ∧
      ∀ x, Φ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0)) := by
  obtain ⟨Φ', hinv, hc, h0⟩ := exists_cylinderTransport (𝕜 := 𝕜) (F := F) (E := E)
  choose Φ hΦ using hinv
  refine ⟨Φ, continuous_iff_continuousAt.2 fun q₀ ↦ ?_, fun x ↦ ?_⟩
  · rw [continuousAt_hom_bundle]
    refine ⟨continuousAt_id, ((hc q₀).congr ?_)⟩
    filter_upwards [(cylinderZero X).continuous.continuousAt.preimage_mem_nhds
        ((trivializationAt F E (q₀.1, 0)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt F E (q₀.1, 0))),
      (trivializationAt F E q₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E q₀)]
      with q hq₀ hq
    rw [← hΦ q]
    exact (inCoordinates_pullback_of_mem (cylinderZero X) (ContinuousMap.id (X × I)) q₀ q _
      hq₀ hq).symm
  · ext v
    rw [ContinuousLinearEquiv.refl_apply, ← ContinuousLinearEquiv.coe_coe, hΦ, h0,
      ContinuousLinearMap.id_apply]

omit [NormedAlgebra ℝ 𝕜] [R1Space X] [ParacompactSpace X] in
/-- Forward and inverse total-space continuity of a cylinder equivalence whose forward maps form a
continuous section of the Hom bundle. -/
private theorem continuous_totalSpace_of_hom_bundle_cylinder [CompleteSpace F]
    {Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q}
    (hΦ : Continuous (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun r : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) r →L[𝕜] E r)
      q (Φ q : E (q.1, 0) →L[𝕜] E q))) :
    Continuous (fun v : TotalSpace F ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) ↦
      TotalSpace.mk' F v.proj (Φ v.proj v.2)) ∧
    Continuous (fun v : TotalSpace F E ↦ TotalSpace.mk' F
      (E := (fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) v.proj ((Φ v.proj).symm v.2)) := by
  have hΦi : Continuous (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun r : X × I ↦ E r →L[𝕜] ((cylinderZero X : X × I → X × I) *ᵖ E) r)
      q ((Φ q).symm : E q →L[𝕜] E (q.1, 0))) :=
    (Continuous.clm_bundle_inverse
      (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E) (E₂ := E) (b := id) hΦ
      (fun q ↦ ⟨Φ q, rfl⟩)).congr fun q ↦
      congrArg (TotalSpace.mk' (F →L[𝕜] F) q) (inverse_equiv (Φ q))
  exact ⟨Continuous.clm_bundle_apply
      (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E) (E₂ := E)
      (hΦ.comp (Pullback.continuous_proj F E (cylinderZero X : X × I → X × I))) continuous_id,
    Continuous.clm_bundle_apply
      (E₁ := E) (E₂ := (cylinderZero X : X × I → X × I) *ᵖ E)
      (hΦi.comp (FiberBundle.continuous_proj F E)) continuous_id⟩

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
  obtain ⟨Φ, hΦ, h0⟩ := exists_continuous_hom_bundle_cylinder (𝕜 := 𝕜) (F := F) (E := E)
  obtain ⟨h₁, h₂⟩ := continuous_totalSpace_of_hom_bundle_cylinder hΦ
  exact ⟨Φ, h₁, h₂, h0⟩

end Cylinder

section RelativeCylinder

universe u v w

/-- Given a closed set `s ⊆ X` and an open neighbourhood `W ⊆ X × I` of
`(s ×ˢ univ) ∪ (univ ×ˢ {0})` over a normal base `X`, a Urysohn cutoff on the tube neighbourhood
`{x | {x} ×ˢ univ ⊆ W}` retracts `X × I` into `W` along `(x, t) ↦ (x, ρ x * t)`, fixing `X × {0}`
and `s × I`. -/
private theorem exists_continuousMap_cylinder_retraction {X : Type u} [TopologicalSpace X]
    [NormalSpace X] {s : Set X} (hs : IsClosed s) {W : Set (X × I)} (hW : IsOpen W)
    (hsW : s ×ˢ (univ : Set I) ⊆ W) (h0W : (univ : Set X) ×ˢ {(0 : I)} ⊆ W) :
    ∃ r : C(X × I, X × I), (∀ q, (r q).1 = q.1) ∧ (∀ q, r q ∈ W) ∧
      (∀ x, r (x, 0) = (x, 0)) ∧ ∀ x ∈ s, ∀ t : I, r (x, t) = (x, t) := by
  let U : Set X := {x | ({x} : Set X) ×ˢ (univ : Set I) ⊆ W}
  have hU : IsOpen U := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨u, v, huo, _, hxu, htv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_univ hW hx
    exact ⟨u, fun y hy _ ⟨rfl, _⟩ ↦ huv ⟨hy, htv (mem_univ _)⟩, huo, hxu (mem_singleton x)⟩
  have hsU : s ⊆ U := fun x hx _ ⟨hy, ht⟩ ↦ hsW ⟨hy.symm ▸ hx, ht⟩
  obtain ⟨ρ, hρ₀, hρ₁, hρI⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl hs
    (disjoint_compl_left_iff_subset.2 hsU)
  refine ⟨⟨fun q ↦ (q.1, ⟨ρ q.1 * q.2.1, unitInterval.mul_mem (hρI q.1) q.2.2⟩),
      continuous_fst.prodMk
        (((ρ.continuous.comp continuous_fst).mul
          (continuous_subtype_val.comp continuous_snd)).subtype_mk _)⟩,
    fun _ ↦ rfl, fun q ↦ ?_, fun x ↦ Prod.ext rfl (Subtype.ext (mul_zero _)),
    fun x hx t ↦ Prod.ext rfl (Subtype.ext (by simp [hρ₁ hx]))⟩
  by_cases hq : q.1 ∈ U
  · exact hq ⟨mem_singleton _, mem_univ _⟩
  · have h0 : ρ q.1 = 0 := hρ₀ hq
    have hq0 : (q.1, (⟨ρ q.1 * q.2.1, unitInterval.mul_mem (hρI q.1) q.2.2⟩ : I)) = (q.1, 0) :=
      Prod.ext rfl (Subtype.ext (by simp [h0]))
    simpa only [ContinuousMap.coe_mk, hq0] using h0W ⟨mem_univ _, mem_singleton _⟩

private theorem transport_beta_eq {𝕜 X : Type*} [Semiring 𝕜]
    {E : X × I → Type*} [∀ q, AddCommMonoid (E q)] [∀ q, Module 𝕜 (E q)]
    [∀ q, TopologicalSpace (E q)] {q q' : X × I} (hq : q' = q) (h1 : q'.1 = q.1)
    (β : ∀ p : X × I, E (p.1, 0) →L[𝕜] E (p.1, 0)) :
    (show E (q.1, 0) →L[𝕜] E (q.1, 0) from h1 ▸ β q') = β q := by
  cases hq
  rfl

private theorem isInvertible_transport {𝕜 X : Type*} [Semiring 𝕜] [TopologicalSpace X]
    {E : X × I → Type*} [∀ q, AddCommMonoid (E q)] [∀ q, Module 𝕜 (E q)]
    [∀ q, TopologicalSpace (E q)] {q' q : X × I} (h1 : q'.1 = q.1)
    {f : ((cylinderZero X : X × I → X × I) *ᵖ E) q' →L[𝕜]
      ((cylinderZero X : X × I → X × I) *ᵖ E) q'}
    (hf : f.IsInvertible) :
    (show E (q.1, 0) →L[𝕜] E (q.1, 0) from h1 ▸ f).IsInvertible := by
  obtain ⟨x', t'⟩ := q'
  obtain ⟨x, t⟩ := q
  dsimp only at h1 ⊢
  cases h1
  exact hf

private theorem inCoordinates_transport_zero {𝕜 X F : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : X × I → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module 𝕜 (E q)]
    [∀ q, TopologicalSpace (E q)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    {x₀' x₀ x' x : X} (hx₀ : x₀' = x₀) (hx : x' = x)
    (f : E (x', 0) →L[𝕜] E (x', 0)) :
    inCoordinates F E F E (x₀', 0) (x', 0) (x₀', 0) (x', 0) f =
      inCoordinates F E F E (x₀, 0) (x, 0) (x₀, 0) (x, 0)
        (show E (x, 0) →L[𝕜] E (x, 0) from hx ▸ f) := by
  cases hx₀
  cases hx
  rfl

section General

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {X : Type u} [TopologicalSpace X]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : X × I → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module 𝕜 (E q)]
  [∀ q, TopologicalSpace (E q)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ q, IsTopologicalAddGroup (E q)] [∀ q, ContinuousSMul 𝕜 (E q)]

omit [NormedAlgebra ℝ 𝕜] in
/-- Re-indexing a continuous endomorphism section of the zero-slice pullback bundle along a
fibre-preserving map `r : C(X × I, X × I)` yields a continuous section over `id`. -/
private theorem continuous_hom_bundle_comp_retraction
    {β : ∀ q : X × I, ((cylinderZero X : X × I → X × I) *ᵖ E) q →L[𝕜]
      ((cylinderZero X : X × I → X × I) *ᵖ E) q}
    (hβ : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
        ((cylinderZero X : X × I → X × I) *ᵖ E) z) q (β q))
    {r : C(X × I, X × I)} (hr₁ : ∀ q, (r q).1 = q.1) :
    Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
        ((cylinderZero X : X × I → X × I) *ᵖ E) z) q
      (show E (q.1, 0) →L[𝕜] E (q.1, 0) from hr₁ q ▸ β (r q)) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  rw [continuousAt_hom_bundle]
  have hc := (hβ.comp r.continuous).continuousAt (x := q₀)
  rw [continuousAt_hom_bundle] at hc
  refine ⟨continuousAt_id, hc.2.congr ?_⟩
  have hmem₀ : (q₀.1, (0 : I)) ∈ (trivializationAt F E (q₀.1, 0)).baseSet :=
    mem_baseSet_trivializationAt F E (q₀.1, 0)
  filter_upwards [(cylinderZero X).continuous.continuousAt.preimage_mem_nhds
    ((trivializationAt F E (q₀.1, 0)).open_baseSet.mem_nhds hmem₀)] with q hq
  have hrq₀ : cylinderZero X (r q₀) = (q₀.1, 0) := Prod.ext (hr₁ q₀) rfl
  have hrq : cylinderZero X (r q) = (q.1, 0) := Prod.ext (hr₁ q) rfl
  have hq' : cylinderZero X (r q) ∈ (trivializationAt F E (cylinderZero X (r q₀))).baseSet := by
    rwa [hrq₀, hrq]
  exact (inCoordinates_pullback_of_mem (cylinderZero X) (cylinderZero X) (r q₀) (r q) (β (r q))
      hq' hq').trans
    ((inCoordinates_transport_zero (hr₁ q₀) (hr₁ q) (β (r q))).trans
      (inCoordinates_pullback_of_mem (cylinderZero X) (cylinderZero X) q₀ q
        (show E (q.1, 0) →L[𝕜] E (q.1, 0) from hr₁ q ▸ β (r q)) hq hq).symm)

omit [NormedAlgebra ℝ 𝕜] in
private theorem continuous_hom_bundle_id_cylinderZero :
    Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
        ((cylinderZero X : X × I → X × I) *ᵖ E) z) q
      (ContinuousLinearMap.id 𝕜 (((cylinderZero X : X × I → X × I) *ᵖ E) q)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const
    (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E)
    (E₂ := (cylinderZero X : X × I → X × I) *ᵖ E)
    (c := fun _ ↦ ContinuousLinearMap.id 𝕜 F)
    fun _ _ hx _ ↦ by
      rw [inCoordinates_eq hx hx]
      ext v
      simp only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, id_apply]

omit [NormedAlgebra ℝ 𝕜] in
/-- Compatibility on `(s ×ˢ univ) ∪ (univ ×ˢ {0})` of the partial transition endomorphism
`(Ψ₁ q)⁻¹ ∘ Φ₀ q` over `s × I` and the identity over `X × {0}`. -/
private theorem continuousOn_transition_union [CompleteSpace F] {s : Set X} (hs : IsClosed s)
    {Ψ₁ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q}
    (hΨ₁ : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      q (Ψ₁ q : E (q.1, 0) →L[𝕜] E q))
    {Φ₀ : ∀ q : s × I, E (q.1.1, 0) ≃L[𝕜] E (q.1.1, q.2)}
    (hΦ₀ : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      (q.1.1, q.2) (Φ₀ q : E (q.1.1, 0) →L[𝕜] E (q.1.1, q.2)))
    {α : ∀ q : X × I, ((cylinderZero X : X × I → X × I) *ᵖ E) q →L[𝕜]
      ((cylinderZero X : X × I → X × I) *ᵖ E) q}
    (hαs : ∀ (x : s) (t : I), α (x.1, t) =
      ((Ψ₁ (x.1, t)).symm : E (x.1, t) →L[𝕜] E (x.1, 0)).comp
        (Φ₀ (x, t) : E (x.1, 0) →L[𝕜] E (x.1, t)))
    (hα0 : ∀ x : X, α (x, 0) = ContinuousLinearMap.id 𝕜 (E (x, 0))) :
    ContinuousOn (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
        ((cylinderZero X : X × I → X × I) *ᵖ E) z) q (α q))
      ((s ×ˢ (univ : Set I)) ∪ ((univ : Set X) ×ˢ {(0 : I)})) := by
  have hΨi : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ E z →L[𝕜] ((cylinderZero X : X × I → X × I) *ᵖ E) z) q
      ((Ψ₁ q).symm : E q →L[𝕜] E (q.1, 0)) :=
    (Continuous.clm_bundle_inverse
      (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E) (E₂ := E) (b := id) hΨ₁
      (fun q ↦ ⟨Ψ₁ q, rfl⟩)).congr fun q ↦
      congrArg (TotalSpace.mk' (F →L[𝕜] F) q) (inverse_equiv (Ψ₁ q))
  have hcomp : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
        ((cylinderZero X : X × I → X × I) *ᵖ E) z) (q.1.1, q.2)
      (((Ψ₁ (q.1.1, q.2)).symm : E (q.1.1, q.2) →L[𝕜] E (q.1.1, 0)).comp
        (Φ₀ q : E (q.1.1, 0) →L[𝕜] E (q.1.1, q.2))) :=
    Continuous.clm_bundle_comp
      (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E) (E₂ := E)
      (E₃ := (cylinderZero X : X × I → X × I) *ᵖ E) (b := cylinderSetIncl s)
      (hΨi.comp (cylinderSetIncl s).continuous) hΦ₀
  refine ContinuousOn.union_of_isClosed ?_ ?_ (hs.prod isClosed_univ)
    (isClosed_univ.prod isClosed_singleton)
  · rw [continuousOn_iff_continuous_domRestrict]
    refine (hcomp.comp ((continuous_fst.comp continuous_subtype_val).subtype_mk
      (fun q ↦ q.2.1) |>.prodMk (continuous_snd.comp continuous_subtype_val))).congr fun q ↦ ?_
    exact congrArg (TotalSpace.mk' (F →L[𝕜] F) q.1) (hαs ⟨q.1.1, q.2.1⟩ q.1.2).symm
  · refine continuous_hom_bundle_id_cylinderZero.continuousOn.congr fun q hq ↦ ?_
    obtain ⟨x, t⟩ := q
    obtain ⟨_, rfl⟩ : x ∈ (univ : Set X) ∧ t = 0 := hq
    exact congrArg (TotalSpace.mk' (F →L[𝕜] F) (x, 0)) (hα0 x)

variable [R1Space X] [ParacompactSpace X]

/-- Extend the partial transition `(Ψ₁ q)⁻¹ ∘ Φ₀ q` from `(s ×ˢ univ) ∪ (univ ×ˢ {0})` to a
continuous invertible zero-slice endomorphism `γ` over `X × I` by Tietze extension followed by a
tube-lemma cylinder retraction into the invertible locus. -/
private theorem exists_retracted_transition_equiv [CompleteSpace F]
    [TietzeExtension.{u, w} (F →L[𝕜] F)] {s : Set X} (hs : IsClosed s)
    {Ψ₁ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q}
    (hΨ₁ : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      q (Ψ₁ q : E (q.1, 0) →L[𝕜] E q))
    (hΨ₁0 : ∀ x : X, Ψ₁ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0)))
    (Φ₀ : ∀ q : s × I, E (q.1.1, 0) ≃L[𝕜] E (q.1.1, q.2))
    (hΦ₀ : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      (q.1.1, q.2) (Φ₀ q : E (q.1.1, 0) →L[𝕜] E (q.1.1, q.2)))
    (hΦ₀0 : ∀ x : s, Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x.1, 0))) :
    ∃ γ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E (q.1, 0),
      Continuous (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
        (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
          ((cylinderZero X : X × I → X × I) *ᵖ E) z)
        q (γ q : E (q.1, 0) →L[𝕜] E (q.1, 0))) ∧
      (∀ x : X, γ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0))) ∧
      ∀ (x : s) (t : I), γ (x.1, t) = (Φ₀ (x, t)).trans (Ψ₁ (x.1, t)).symm := by
  classical
  let α : ∀ q : X × I, ((cylinderZero X : X × I → X × I) *ᵖ E) q →L[𝕜]
      ((cylinderZero X : X × I → X × I) *ᵖ E) q := fun q ↦
    if hq : q.1 ∈ s then
      ((Ψ₁ q).symm : E q →L[𝕜] E (q.1, 0)).comp (Φ₀ (⟨q.1, hq⟩, q.2) : E (q.1, 0) →L[𝕜] E q)
    else ContinuousLinearMap.id 𝕜 (E (q.1, 0))
  have hα0 (x : X) : α (x, 0) = ContinuousLinearMap.id 𝕜 (E (x, 0)) := by
    by_cases hx : x ∈ s <;> simp [α, hx, hΨ₁0, hΦ₀0] <;> rfl
  obtain ⟨β, hβ, hβα⟩ := exists_continuous_section_extension 𝕜
    ((hs.prod isClosed_univ).union (isClosed_univ.prod isClosed_singleton))
    (continuousOn_transition_union hs hΨ₁ hΦ₀
      (α := α) (fun x t ↦ by simp only [α, x.2, ↓reduceDIte]; rfl) hα0)
  obtain ⟨r, hr₁, hrW, hr0, hrs⟩ := exists_continuousMap_cylinder_retraction hs
    hβ.isOpen_setOf_clm_bundle_isInvertible
    (fun q hq ↦ by
      change (β q).IsInvertible
      rw [hβα q (Or.inl hq)]
      simp only [α, hq.1, ↓reduceDIte]
      exact ⟨(Φ₀ (⟨q.1, hq.1⟩, q.2)).trans (Ψ₁ q).symm, rfl⟩)
    (fun ⟨x, t⟩ ⟨hx, ht⟩ ↦ by
      obtain rfl : t = 0 := ht
      change (β (x, 0)).IsInvertible
      rw [hβα (x, 0) (Or.inr ⟨hx, rfl⟩), hα0]
      exact ⟨ContinuousLinearEquiv.refl 𝕜 _, rfl⟩)
  choose γ hγ using fun q : X × I ↦ isInvertible_transport (hr₁ q) (hrW q)
  refine ⟨γ, (continuous_hom_bundle_comp_retraction hβ hr₁).congr fun q ↦
      congrArg (TotalSpace.mk' (F →L[𝕜] F) q) (hγ q).symm, fun x ↦ ?_, fun x t ↦ ?_⟩
  · exact ContinuousLinearEquiv.coe_injective ((hγ (x, 0)).trans
      ((transport_beta_eq (hr0 x) (hr₁ (x, 0)) β).trans
        ((hβα (x, 0) (Or.inr ⟨mem_univ x, mem_singleton 0⟩)).trans (hα0 x))))
  · exact ContinuousLinearEquiv.coe_injective ((hγ (x.1, t)).trans
      ((transport_beta_eq (hrs x.1 x.2 t) (hr₁ (x.1, t)) β).trans
        ((hβα (x.1, t) (Or.inl ⟨x.2, mem_univ t⟩)).trans
          (by simp only [α, x.2, ↓reduceDIte]; rfl))))

/-- **Relative homotopy invariance of vector bundles over a cylinder.** Over a paracompact R₁
base `X`, let `E` be a Banach vector bundle over `X × I` whose model endomorphism space
`F →L[𝕜] F` has the Tietze extension property, and let `s ⊆ X` be closed. Every Hom-bundle
continuous family of fibrewise linear equivalences `Φ₀ (x, t) : E (x, 0) ≃L[𝕜] E (x, t)` over
`s × I` equal to the identity on `s × {0}` extends to a Hom-bundle continuous family
`Φ (x, t) : E (x, 0) ≃L[𝕜] E (x, t)` over `X × I`, continuous on total spaces together with its
inverse and equal to the identity on `X × {0}`. -/
theorem exists_continuousLinearEquiv_cylinder_of_isClosed [CompleteSpace F]
    [TietzeExtension.{u, w} (F →L[𝕜] F)] {s : Set X} (hs : IsClosed s)
    (Φ₀ : ∀ q : s × I, E (q.1.1, 0) ≃L[𝕜] E (q.1.1, q.2))
    (hΦ₀ : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      (q.1.1, q.2) (Φ₀ q : E (q.1.1, 0) →L[𝕜] E (q.1.1, q.2)))
    (hΦ₀0 : ∀ x : s, Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x.1, 0))) :
    ∃ Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q,
      Continuous (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
        (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
        q (Φ q : E (q.1, 0) →L[𝕜] E q)) ∧
      Continuous (fun v : TotalSpace F ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) ↦
        TotalSpace.mk' F v.proj (Φ v.proj v.2)) ∧
      Continuous (fun v : TotalSpace F E ↦ TotalSpace.mk' F
        (E := (fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) v.proj ((Φ v.proj).symm v.2)) ∧
      (∀ x, Φ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0))) ∧
      ∀ (x : s) (t : I), Φ (x.1, t) = Φ₀ (x, t) := by
  obtain ⟨Ψ₁, hΨ₁, hΨ₁0⟩ := exists_continuous_hom_bundle_cylinder (𝕜 := 𝕜) (F := F) (E := E)
  obtain ⟨γ, hγc, hγ0, hγs⟩ := exists_retracted_transition_equiv hs hΨ₁ hΨ₁0 Φ₀ hΦ₀ hΦ₀0
  let Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q := fun q ↦ (γ q).trans (Ψ₁ q)
  have hΦhom : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      q (Φ q : E (q.1, 0) →L[𝕜] E q) :=
    (Continuous.clm_bundle_comp
      (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E)
      (E₂ := (cylinderZero X : X × I → X × I) *ᵖ E)
      (E₃ := E) (b := id) hΨ₁ hγc).congr fun _ ↦ rfl
  obtain ⟨hfwd, hinv⟩ := continuous_totalSpace_of_hom_bundle_cylinder hΦhom
  refine ⟨Φ, hΦhom, hfwd, hinv, fun x ↦ ?_, fun x t ↦ ?_⟩
  · ext v
    simp [Φ, hγ0 x, hΨ₁0 x]
  · ext v
    simp [Φ, hγs x t]

end General

section FiniteDimensional

variable {𝕜 : Type v} [RCLike 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X × I → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module 𝕜 (E q)]
  [∀ q, TopologicalSpace (E q)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ q, IsTopologicalAddGroup (E q)] [∀ q, ContinuousSMul 𝕜 (E q)]

/-- **Finite-rank relative cylinder theorem.** For a finite-rank real or complex vector bundle `E`
over `X × I` with `X` paracompact and R₁, a family of fibrewise continuous linear equivalences
`Φ₀ (x, t) : E (x, 0) ≃L[𝕜] E (x, t)` over `s × I` (`s ⊆ X` closed) which is continuous on total
spaces and equal to the identity on `s × {0}` extends to a global cylinder trivialization `Φ` over
`X × I`, continuous on total spaces together with its inverse. -/
theorem exists_continuousLinearEquiv_cylinder_of_isClosed_of_continuous {s : Set X}
    (hs : IsClosed s) (Φ₀ : ∀ q : s × I, E (q.1.1, 0) ≃L[𝕜] E (q.1.1, q.2))
    (hΦ₀ : Continuous fun v : TotalSpace F ((fun q : s × I ↦ (q.1.1, (0 : I))) *ᵖ E) ↦
      TotalSpace.mk' F (E := (fun q : s × I ↦ (q.1.1, q.2)) *ᵖ E) v.proj (Φ₀ v.proj v.2))
    (hΦ₀0 : ∀ x : s, Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x.1, 0))) :
    ∃ Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q,
      Continuous (fun v : TotalSpace F ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) ↦
        TotalSpace.mk' F v.proj (Φ v.proj v.2)) ∧
      Continuous (fun v : TotalSpace F E ↦ TotalSpace.mk' F
        (E := (fun q : X × I ↦ (q.1, (0 : I))) *ᵖ E) v.proj ((Φ v.proj).symm v.2)) ∧
      (∀ x, Φ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0))) ∧
      ∀ (x : s) (t : I), Φ (x.1, t) = Φ₀ (x, t) := by
  have := FiniteDimensional.completeSpace 𝕜 F
  have hhom := (continuous_hom_bundle_iff (F₁ := F) (F₂ := F)
    (E₁ := (((cylinderZero X).comp (cylinderSetIncl s) : C(s × I, X × I)) : s × I → X × I) *ᵖ E)
    (E₂ := (cylinderSetIncl s : s × I → X × I) *ᵖ E)
    (fun q : s × I ↦ (Φ₀ q : E (q.1.1, 0) →L[𝕜] E (q.1.1, q.2)))).2 hΦ₀
  have hΦ₀' : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      (cylinderSetIncl s q) (Φ₀ q : E (q.1.1, 0) →L[𝕜] E (q.1.1, q.2)) := by
    refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
    rw [continuousAt_hom_bundle]
    have hc := hhom.continuousAt (x := q₀)
    rw [continuousAt_hom_bundle] at hc
    refine ⟨(cylinderSetIncl s).continuous.continuousAt, hc.2.congr ?_⟩
    filter_upwards [((cylinderZero X).comp (cylinderSetIncl s)).continuous.continuousAt
        |>.preimage_mem_nhds
          ((trivializationAt F E (q₀.1.1, 0)).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt F E (q₀.1.1, 0))),
      (cylinderSetIncl s).continuous.continuousAt.preimage_mem_nhds
        ((trivializationAt F E (cylinderSetIncl s q₀)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt F E (cylinderSetIncl s q₀)))] with q hq₀ hq
    exact ((inCoordinates_pullback_of_mem ((cylinderZero X).comp (cylinderSetIncl s))
        (cylinderSetIncl s) q₀ q _ hq₀ hq).trans
      (inCoordinates_pullback_of_mem (cylinderZero X) (ContinuousMap.id (X × I))
        (cylinderSetIncl s q₀) (cylinderSetIncl s q) _ hq₀ hq).symm).symm
  obtain ⟨Φ, -, hfwd, hinv, h0, hs'⟩ :=
    exists_continuousLinearEquiv_cylinder_of_isClosed hs Φ₀ hΦ₀' hΦ₀0
  exact ⟨Φ, hfwd, hinv, h0, hs'⟩

end FiniteDimensional

end RelativeCylinder

section Homotopy

/-- Evaluating a continuous cylinder equivalence on `G *ᵖ E` at time `1` gives forward and inverse
continuous total-space maps between the endpoint pullbacks `(G (·, 0)) *ᵖ E` and
`(G (·, 1)) *ᵖ E`. -/
private theorem continuous_pullback_slice_one {𝕜 : Type*} [Semiring 𝕜]
    {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {E : Y → Type*} [∀ y, AddCommMonoid (E y)] [∀ y, Module 𝕜 (E y)]
    [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace F E)]
    (G : C(X × I, Y))
    {Φ : ∀ q : X × I, ((G : X × I → Y) *ᵖ E) (q.1, 0) ≃L[𝕜] ((G : X × I → Y) *ᵖ E) q}
    (hΦ₁ : Continuous fun v : TotalSpace F ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ
        ((G : X × I → Y) *ᵖ E)) ↦ TotalSpace.mk' F v.proj (Φ v.proj v.2))
    (hΦ₂ : Continuous fun v : TotalSpace F ((G : X × I → Y) *ᵖ E) ↦ TotalSpace.mk' F
        (E := (fun q : X × I ↦ (q.1, (0 : I))) *ᵖ ((G : X × I → Y) *ᵖ E)) v.proj
        ((Φ v.proj).symm v.2)) :
    Continuous (fun v : TotalSpace F ((fun x ↦ G (x, 0)) *ᵖ E) ↦
      TotalSpace.mk' F (E := (fun x ↦ G (x, 1)) *ᵖ E) v.proj (Φ (v.proj, 1) v.2)) ∧
    Continuous (fun v : TotalSpace F ((fun x ↦ G (x, 1)) *ᵖ E) ↦
      TotalSpace.mk' F (E := (fun x ↦ G (x, 0)) *ᵖ E) v.proj ((Φ (v.proj, 1)).symm v.2)) := by
  refine ⟨(inducing_pullbackTotalSpaceEmbedding F E _).continuous_iff.2
      ((Pullback.continuous_proj F E _).prodMk ?_),
    (inducing_pullbackTotalSpaceEmbedding F E _).continuous_iff.2
      ((Pullback.continuous_proj F E _).prodMk ?_)⟩
  · -- Insert the fibre over `x` as the fibre over `(x, 1)` of the pulled-back cylinder.
    have hι : Continuous fun v : TotalSpace F ((fun x ↦ G (x, 0)) *ᵖ E) ↦
        (TotalSpace.mk' F (E := (fun q : X × I ↦ (q.1, (0 : I))) *ᵖ ((G : X × I → Y) *ᵖ E))
          (v.proj, 1) v.2) :=
      (inducing_pullbackTotalSpaceEmbedding F _ _).continuous_iff.2
        (((Pullback.continuous_proj F E _).prodMk continuous_const).prodMk
          ((inducing_pullbackTotalSpaceEmbedding F E _).continuous_iff.2
            (((Pullback.continuous_proj F E _).prodMk continuous_const).prodMk
              (Pullback.continuous_lift F E _))))
    have h := (Pullback.continuous_lift F E (G : X × I → Y)).comp (hΦ₁.comp hι)
    -- The fibre of `(fun q ↦ (q.1, 0)) *ᵖ (G *ᵖ E)` over `(x, 1)` is `E (G (x, 0))` by definition
    -- of pullback fibres, so both sides lift the same vectors.
    simp only [comp_def] at h ⊢
    exact h
  · have hι : Continuous fun v : TotalSpace F ((fun x ↦ G (x, 1)) *ᵖ E) ↦
        (TotalSpace.mk' F (E := (G : X × I → Y) *ᵖ E) (v.proj, 1) v.2) :=
      (inducing_pullbackTotalSpaceEmbedding F E _).continuous_iff.2
        (((Pullback.continuous_proj F E _).prodMk continuous_const).prodMk
          (Pullback.continuous_lift F E _))
    have h := (Pullback.continuous_lift F E (G : X × I → Y)).comp
      ((Pullback.continuous_lift F ((G : X × I → Y) *ᵖ E) _).comp (hΦ₂.comp hι))
    simp only [comp_def] at h ⊢
    exact h

private theorem totalSpace_mk_eq_of_eq {𝕜 Y F : Type*} [Semiring 𝕜]
    {E : Y → Type*} [∀ y, AddCommMonoid (E y)] [∀ y, Module 𝕜 (E y)] [∀ y, TopologicalSpace (E y)]
    {y₀ y₁ : Y} (h : y₀ = y₁) (v : E y₀) :
    (⟨y₁, (h ▸ ContinuousLinearEquiv.refl 𝕜 (E y₀) : E y₀ ≃L[𝕜] E y₁) v⟩ : TotalSpace F E) =
      ⟨y₀, v⟩ := by
  cases h
  rfl

section Free

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
  exact ⟨fun x ↦ Φ (x, 1), continuous_pullback_slice_one G hΦ₁ hΦ₂⟩

/-- **Homotopy invariance of vector bundles.** Over a paracompact R₁ space `X`, for instance a
paracompact Hausdorff space, the pullbacks of a vector bundle `E` along homotopic maps
`f₀ f₁ : C(X, Y)` are isomorphic: there are fibrewise continuous linear equivalences
`E (f₀ x) ≃L[𝕜] E (f₁ x)`, continuous on total spaces together with their inverses. Here `𝕜` is a
normed `ℝ`-algebra, such as `ℝ` or `ℂ`, and the model fibre `F` may be any Banach space. -/
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

end Free

private theorem inCoordinates_transport_refl {𝕜 Y F : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace Y] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
    [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    {y₀ y₀' y₁ y₁' : Y} (hy₀ : y₀ = y₀') (hy₁ : y₁ = y₁')
    (hq : y₁ ∈ (trivializationAt F E y₀).baseSet) :
    inCoordinates F E F E y₀ y₁ y₀' y₁'
      ((hy₁ ▸ ContinuousLinearEquiv.refl 𝕜 (E y₁) : E y₁ ≃L[𝕜] E y₁')) =
      ContinuousLinearMap.id 𝕜 F := by
  cases hy₀
  cases hy₁
  ext v
  simp [inCoordinates, Trivialization.continuousLinearMapAt_symmL _ hq]

section Relative

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type z} [TopologicalSpace Y]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TietzeExtension.{u, w} (F →L[𝕜] F)]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
  [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ y, IsTopologicalAddGroup (E y)] [∀ y, ContinuousSMul 𝕜 (E y)]

omit [NormedAlgebra ℝ 𝕜] [R1Space X] [ParacompactSpace X] [CompleteSpace F]
  [TietzeExtension.{u, w} (F →L[𝕜] F)] in
/-- Along a homotopy stationary on `s`, transporting each fibre over `(x, t) : s × I` by the
base-point equality `G (x, 0) = G (x, t)` defines a continuous section of the cylinder Hom
bundle. -/
private theorem continuous_hom_bundle_stationary_pullback (G : C(X × I, Y)) {s : Set X}
    (hs : ∀ (x : s) (t : I), G (x.1, 0) = G (x.1, t)) :
    Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦
        ((cylinderZero X : X × I → X × I) *ᵖ ((G : X × I → Y) *ᵖ E)) z →L[𝕜]
          ((G : X × I → Y) *ᵖ E) z)
      (q.1.1, q.2)
      ((hs q.1 q.2 ▸ ContinuousLinearEquiv.refl 𝕜 (E (G (q.1.1, 0))) :
        E (G (q.1.1, 0)) ≃L[𝕜] E (G (q.1.1, q.2))) :
        E (G (q.1.1, 0)) →L[𝕜] E (G (q.1.1, q.2))) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨(cylinderSetIncl s).continuous.continuousAt,
    (continuousAt_const (y := ContinuousLinearMap.id 𝕜 F)).congr ?_⟩
  have hmem₀ : G (q₀.1.1, 0) ∈ (trivializationAt F E (G (q₀.1.1, 0))).baseSet :=
    mem_baseSet_trivializationAt F E _
  filter_upwards [(G.comp ((cylinderZero X).comp (cylinderSetIncl s))).continuous.continuousAt
      |>.preimage_mem_nhds
        ((trivializationAt F E (G (q₀.1.1, 0))).open_baseSet.mem_nhds hmem₀)] with q hq
  have hq₀'' : cylinderSetIncl s q ∈
      (trivializationAt F ((cylinderZero X : X × I → X × I) *ᵖ ((G : X × I → Y) *ᵖ E))
        (cylinderSetIncl s q₀)).baseSet := hq
  have hG₁ : G (q.1.1, q.2) ∈ (trivializationAt F E (G (q₀.1.1, q₀.2))).baseSet := by
    rwa [← hs q₀.1 q₀.2, ← hs q.1 q.2]
  have hq₁' : cylinderSetIncl s q ∈
      (trivializationAt F ((G : X × I → Y) *ᵖ E) (cylinderSetIncl s q₀)).baseSet := hG₁
  let L : E (G (q.1.1, 0)) →L[𝕜] E (G (q.1.1, q.2)) :=
    (hs q.1 q.2 ▸ ContinuousLinearEquiv.refl 𝕜 (E (G (q.1.1, 0))) :
      E (G (q.1.1, 0)) ≃L[𝕜] E (G (q.1.1, q.2)))
  have hcoord : inCoordinates F
      ((cylinderZero X : X × I → X × I) *ᵖ ((G : X × I → Y) *ᵖ E))
      F ((G : X × I → Y) *ᵖ E)
      (cylinderSetIncl s q₀) (cylinderSetIncl s q)
      (cylinderSetIncl s q₀) (cylinderSetIncl s q) L =
      inCoordinates F E F E (G (q₀.1.1, 0)) (G (q.1.1, 0)) (G (q₀.1.1, q₀.2)) (G (q.1.1, q.2))
        L := by
    erw [inCoordinates_eq hq₀'' hq₁', inCoordinates_eq hq hG₁]
    simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
      Trivialization.continuousLinearEquivAt_pullback]
    rfl
  exact (hcoord.trans (inCoordinates_transport_refl (hs q₀.1 q₀.2) (hs q.1 q.2) hq)).symm

/-- Endpoint form of the relative cylinder theorem along `G : C(X × I, Y)` stationary on `s`. -/
private theorem exists_continuousLinearEquiv_pullback_rel_of_eq (G : C(X × I, Y)) {s : Set X}
    (hs : IsClosed s) {g₀ g₁ : X → Y} (h₀ : ∀ x, G (x, 0) = g₀ x) (h₁ : ∀ x, G (x, 1) = g₁ x)
    (hGs : ∀ x ∈ s, ∀ t : I, G (x, t) = g₀ x) :
    ∃ Φ : ∀ x, E (g₀ x) ≃L[𝕜] E (g₁ x),
      Continuous (fun v : TotalSpace F (g₀ *ᵖ E) ↦
        TotalSpace.mk' F (E := g₁ *ᵖ E) v.proj (Φ v.proj v.2)) ∧
      Continuous (fun v : TotalSpace F (g₁ *ᵖ E) ↦
        TotalSpace.mk' F (E := g₀ *ᵖ E) v.proj ((Φ v.proj).symm v.2)) ∧
      ∀ x ∈ s, ∀ v : E (g₀ x), (⟨g₁ x, Φ x v⟩ : TotalSpace F E) = ⟨g₀ x, v⟩ := by
  obtain rfl : g₀ = fun x ↦ G (x, 0) := (funext h₀).symm
  obtain rfl : g₁ = fun x ↦ G (x, 1) := (funext h₁).symm
  have hGs' (x : s) (t : I) : G (x.1, 0) = G (x.1, t) := (hGs x.1 x.2 t).symm
  obtain ⟨Φ, -, hΦ₁, hΦ₂, -, hΦs⟩ := exists_continuousLinearEquiv_cylinder_of_isClosed
    (𝕜 := 𝕜) (F := F) (E := (G : X × I → Y) *ᵖ E) hs
    (fun q ↦ (hGs' q.1 q.2 ▸ ContinuousLinearEquiv.refl 𝕜 (E (G (q.1.1, 0))) :
      E (G (q.1.1, 0)) ≃L[𝕜] E (G (q.1.1, q.2))))
    (continuous_hom_bundle_stationary_pullback G hGs')
    (fun x ↦ rfl)
  obtain ⟨hfwd, hinv⟩ := continuous_pullback_slice_one G hΦ₁ hΦ₂
  refine ⟨fun x ↦ Φ (x, 1), hfwd, hinv, fun x hx v ↦ ?_⟩
  change (⟨G (x, 1), Φ (x, 1) v⟩ : TotalSpace F E) = ⟨G (x, 0), v⟩
  rw [hΦs ⟨x, hx⟩ 1]
  exact totalSpace_mk_eq_of_eq (hGs' ⟨x, hx⟩ 1) v

/-- **Relative homotopy invariance of vector bundles.** Over a paracompact R₁ space `X`, let
`s ⊆ X` be closed and let `f₀ f₁ : C(X, Y)` be homotopic relative to `s`. If `F` is a Banach space
whose endomorphism space `F →L[𝕜] F` has the Tietze extension property (for instance any
finite-dimensional space over `ℝ` or `ℂ`), there are fibrewise continuous linear equivalences
`Φ x : E (f₀ x) ≃L[𝕜] E (f₁ x)`, continuous on total spaces together with their inverses, that act
as the identity over every point of `s`. -/
theorem _root_.ContinuousMap.HomotopicRel.exists_continuousLinearEquiv_pullback {s : Set X}
    {f₀ f₁ : C(X, Y)} (h : f₀.HomotopicRel f₁ s) (hs : IsClosed s) :
    ∃ Φ : ∀ x, E (f₀ x) ≃L[𝕜] E (f₁ x),
      Continuous (fun v : TotalSpace F ((f₀ : X → Y) *ᵖ E) ↦
        TotalSpace.mk' F (E := (f₁ : X → Y) *ᵖ E) v.proj (Φ v.proj v.2)) ∧
      Continuous (fun v : TotalSpace F ((f₁ : X → Y) *ᵖ E) ↦
        TotalSpace.mk' F (E := (f₀ : X → Y) *ᵖ E) v.proj ((Φ v.proj).symm v.2)) ∧
      ∀ x ∈ s, ∀ v : E (f₀ x), (⟨f₁ x, Φ x v⟩ : TotalSpace F E) = ⟨f₀ x, v⟩ := by
  obtain ⟨H⟩ := h
  exact exists_continuousLinearEquiv_pullback_rel_of_eq (H.toContinuousMap.comp .prodSwap) hs
    H.apply_zero H.apply_one fun x hx t ↦ H.eq_fst t hx

end Relative

end Homotopy

end TauCeti
