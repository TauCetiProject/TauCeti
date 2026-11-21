/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Coordinates
public import TauCeti.Analysis.Sobolev.Local.Wkp
public import TauCeti.Analysis.Sobolev.Local.Wkp.HalfDisc
public import TauCeti.Analysis.Sobolev.Wkp.Local.Compactness
public import TauCeti.MeasureTheory.Function.Gluing
public import TauCeti.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Planar
import TauCeti.Analysis.Sobolev.Wkp.FiniteCover

/-!
# Local Rellich compactness for local Sobolev classes

Let `Ω` be an open subset of `ℂ` and `1 ≤ p ≤ ∞`. A sequence of functions `u m : ℂ → F`, with
`F` a finite-dimensional real vector space, which is bounded in `W^{k+1,p}` on every relatively
compact open subset of `Ω` has a subsequence converging in `W^{k,p}` on every relatively compact
open subset of `Ω`, to a limit in `MemWkpLoc p Ω k`.

The same holds up to the real axis, for the relatively open subset `Ω ∩ {0 ≤ im}` of the closed
upper half-plane. There the relatively compact pieces are the upper halves `W⁺ = W ∩ {0 < im}`
(`TopologicalSpace.Opens.upperHalf W`) of the open sets `W` whose closure is compact and contained
in `Ω`, which may meet the real axis: a sequence bounded in `W^{k+1,p}` on every such `W⁺` has a
subsequence converging in `W^{k,p}` on every such `W⁺`, to a limit in
`MemWkpLoc p (Ω ∩ {0 ≤ im}) k`.

Boundedness and convergence are expressed through the scalar Sobolev spaces `TauCeti.Wkp` on
these open sets, applied to the coordinates of `u m` in a basis of `F`; no local norm is
introduced. By `TauCeti.memWkpLoc_iff_forall_wkp` and `Module.Basis.memWkpLoc_iff`, in the interior
case the boundedness hypothesis already places every `u m` in `MemWkpLoc p Ω (k + 1)`, and by
`TauCeti.memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp` in the half-disc case it places every
`u m` in `MemWkpLoc p (Ω ∩ {0 ≤ im}) (k + 1)`.

Both proofs exhaust `Ω` by an increasing sequence of relatively compact open sets `E n`, each with
closure inside the next. Restriction from `E (n + 1)` to `E n` while forgetting one derivative is
a compact operator, `TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`, so the sequence lies in
a compact subset of the countable product of the spaces `Wkp volume (E n) p k`, one factor for each
level `n` and each coordinate. A single subsequence therefore converges in every factor at once,
which replaces the diagonal argument. The limits on the different `E n` agree under restriction,
by uniqueness of limits, and glue to one function by
`TauCeti.exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter`.

In the half-disc case the factors are the spaces `Wkp volume (E n)⁺ p k`, and the compactness of
the restriction from `(E (n + 1))⁺` to `(E n)⁺` forgetting one derivative is
`TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL_upperHalf`. The closure of `(E n)⁺` reaches
the real axis, so it is not a relatively compact subset of `(E (n + 1))⁺` and the interior
theorem does not apply. Instead the compact set `closure (E n) ∩ {0 ≤ im}` is covered by finitely
many discs: discs inside `(E (n + 1))⁺` around its points off the axis, and around its points
`x` on the axis discs inside `E (n + 1)` centred at `x`, whose upper halves are Lipschitz domains.
On each of these pieces forgetting one derivative is compact by the Rellich–Kondrachov theorem
for Lipschitz domains (`TauCeti.Wkp.isCompactOperator_lowerOrderL_complexBall` and
`TauCeti.Wkp.isCompactOperator_lowerOrderL_upperHalf_complexBall`), and compactness of a map into
`W^{k,p}` is local on a finite open cover (`TauCeti.Wkp.isCompactOperator_of_restrictL`).

## Main declarations

* `TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`: local Rellich for real functions.
* `Module.Basis.exists_subseq_memWkpLoc_tendsto_wkp`: local Rellich for functions valued in a
  finite-dimensional real vector space, through the coordinates in a basis.
* `TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL_upperHalf`: restriction from `W⁺` to the
  upper half of a relatively compact open subset of `W`, forgetting one derivative, is compact.
* `TauCeti.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp` and
  `Module.Basis.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp`: local Rellich up to
  the real axis, for real and for vector-valued functions.
* `TauCeti.memWkpLoc_of_forall_exists_wkp_norm_le`: the boundedness hypothesis places every member
  of the sequence in the local Sobolev class.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and Rellich's theorem).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.16.
-/

public section

noncomputable section

open Filter Metric Set MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace TauCeti

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℂ} {k : ℕ}

/-! ### Extraction along an exhaustion -/

/-- Elements `a n` of `W^{k,p}(O n)` over an increasing sequence of open sets, each the restriction
of the next, are represented by one function: their values agree almost everywhere on each `O n`
with a single `v`. -/
private theorem exists_ae_eq_of_restrictL_eq {O : ℕ → Opens ℂ} (hmono : Monotone O)
    {a : ∀ n, Wkp volume (O n) p k}
    (ha : ∀ {n n'} (h : n ≤ n'), Wkp.restrictL (hmono h) k (a n') = a n) :
    ∃ v : ℂ → ℝ, ∀ n, Wkp.value k (a n) =ᵐ[volume.restrict (O n)] v := by
  have ha_ae : ∀ {n n'} (h : n ≤ n'),
      Wkp.value k (a n) =ᵐ[volume.restrict (O n)] Wkp.value k (a n') := fun h => by
    rw [← ha h]
    exact Wkp.value_restrictL_ae (hmono h) k _
  obtain ⟨v, hv⟩ := exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter (μ := volume)
    (a := fun n => Wkp.value k (a n)) (fun n => (O n).isOpen.measurableSet) fun n n' => by
      rcases le_total n n' with h | h
      · rw [inter_eq_left.2 (SetLike.coe_subset_coe.2 (hmono h))]
        exact ha_ae h
      · rw [inter_eq_right.2 (SetLike.coe_subset_coe.2 (hmono h))]
        exact (ha_ae h).symm
  exact ⟨v, fun n => (hv n).symm⟩

/-- **Extraction along an exhaustion with compact restrictions.** Let `O n` be an increasing
sequence of open sets such that restriction from `O (n + 1)` to `O n` forgetting one derivative is
a compact operator. A countable family of sequences of real functions, each bounded in
`W^{k+1,p}(O n)` for every `n`, has a common subsequence along which every member converges in
`W^{k,p}(W)` for every open `W` inside some `O n`, to a limit represented in `W^{k,p}(W)`. -/
private theorem exists_subseq_tendsto_wkp_of_isCompactOperator {ι : Type*} [Countable ι]
    {O : ℕ → Opens ℂ} (hle : ∀ n, O n ≤ O (n + 1))
    (hT : ∀ n, IsCompactOperator
      ((Wkp.restrictL (mu := volume) (p := p) (hle n) k).comp (Wkp.lowerOrderL k)))
    {u : ι → ℕ → ℂ → ℝ}
    (hu : ∀ n i, ∃ R : ℝ, ∀ m, ∃ v : Wkp volume (O (n + 1)) p (k + 1),
      ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (O (n + 1))] u i m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ι → ℂ → ℝ, ∀ n i (W : Opens ℂ), W ≤ O n →
      (∃ w : Wkp volume W p k, Wkp.value k w =ᵐ[volume.restrict W] v i) ∧
      ∀ (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict W] u i (φ j)) →
        Wkp.value k w =ᵐ[volume.restrict W] v i → Tendsto y atTop (𝓝 w) := by
  have hmono : Monotone O := monotone_nat_of_le_succ hle
  choose R V hVR hVu using hu
  -- The compact operators from `O (n + 1)` to `O n`.
  let T : ∀ n : ℕ, Wkp volume (O (n + 1)) p (k + 1) →L[ℝ] Wkp volume (O n) p k := fun n =>
    (Wkp.restrictL (hle n) k).comp (Wkp.lowerOrderL k)
  have hTval : ∀ n (w : Wkp volume (O (n + 1)) p (k + 1)),
      Wkp.value k (T n w) =ᵐ[volume.restrict (O n)] Wkp.value (k + 1) w := fun n w => by
    have hTw : T n w = Wkp.restrictL (hle n) k (Wkp.lowerOrder k w) := by
      simp only [T, ContinuousLinearMap.comp_apply]
      rw [Wkp.lowerOrderL_apply]
    rw [hTw, Wkp.value_succ]
    exact Wkp.value_restrictL_ae _ k _
  -- The sequence in the product over levels and coordinates, and its values.
  let x : ℕ → ∀ q : ℕ × ι, Wkp volume (O q.1) p k := fun m q => T q.1 (V q.1 q.2 m)
  have hxval : ∀ m (q : ℕ × ι), Wkp.value k (x m q) =ᵐ[volume.restrict (O q.1)] u q.2 m :=
    fun m q => (hTval q.1 _).trans (ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.2 (hle q.1)) (hVu q.1 q.2 m))
  have hS : IsCompact (univ.pi fun q : ℕ × ι => closure (T q.1 '' closedBall 0 (R q.1 q.2))) :=
    isCompact_univ_pi fun q => (hT q.1).isCompact_closure_image_closedBall _
  obtain ⟨a, -, φ, hφ, hxa⟩ := hS.tendsto_subseq (x := x) fun m q _ =>
    subset_closure ⟨V q.1 q.2 m, mem_closedBall_zero_iff.2 (hVR q.1 q.2 m), rfl⟩
  have hxa' : ∀ q, Tendsto (fun j => x (φ j) q) atTop (𝓝 (a q)) := tendsto_pi_nhds.1 hxa
  -- The limits on the different levels agree under restriction, so they glue.
  have hcompat : ∀ i {n n'} (h : n ≤ n'),
      Wkp.restrictL (hmono h) k (a (n', i)) = a (n, i) := fun i n n' h => by
    have hres : ∀ m, Wkp.restrictL (hmono h) k (x m (n', i)) = x m (n, i) :=
      fun m => Wkp.restrictL_eq_of_value_ae_eq_restrict _ k (hxval m (n', i)) (hxval m (n, i))
    refine tendsto_nhds_unique ?_ (hxa' (n, i))
    simpa only [Function.comp_def, hres] using
      ((Wkp.restrictL (hmono h) k).continuous.tendsto _).comp (hxa' (n', i))
  choose v hv using fun i => exists_ae_eq_of_restrictL_eq hmono (hcompat i)
  refine ⟨φ, hφ, v, fun n i W hWn => ⟨⟨Wkp.restrictL hWn k (a (n, i)),
    (Wkp.value_restrictL_ae hWn k _).trans (ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.2 hWn) (hv i n))⟩, fun y w hy hw => ?_⟩⟩
  have hy' : ∀ j, Wkp.restrictL hWn k (x (φ j) (n, i)) = y j := fun j =>
    Wkp.restrictL_eq_of_value_ae_eq_restrict hWn k (hxval (φ j) (n, i)) (hy j)
  have hw' : Wkp.restrictL hWn k (a (n, i)) = w :=
    Wkp.restrictL_eq_of_value_ae_eq_restrict hWn k (hv i n) hw
  simpa only [Function.comp_def, hy', hw'] using
    ((Wkp.restrictL hWn k).continuous.tendsto _).comp (hxa' (n, i))

/-! ### Local Rellich compactness -/

/-- Under the boundedness hypothesis of `TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`, every member
of the family lies in `MemWkpLoc p Ω k`: only the existence of a representative on each relatively
compact open subset is used, not the uniform bound. -/
theorem memWkpLoc_of_forall_exists_wkp_norm_le {ι : Type*} {u : ι → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p k,
        ‖y‖ ≤ R ∧ Wkp.value k y =ᵐ[volume.restrict W] u m) (m : ι) :
    MemWkpLoc p Ω k (u m) :=
  memWkpLoc_of_forall_wkp fun W hWc hWΩ => by
    obtain ⟨R, hR⟩ := hu W hWc hWΩ
    obtain ⟨y, -, hy⟩ := hR m
    exact ⟨y, hy⟩

/-- **Local Rellich compactness for a countable family of sequences.** A countable family of
sequences of real functions, each bounded in `W^{k+1,p}` on every relatively compact open subset
of `Ω`, has a common subsequence along which every member converges in `W^{k,p}` on every
relatively compact open subset of `Ω`, to a limit in `MemWkpLoc p Ω k`. -/
private theorem exists_subseq_memWkpLoc_tendsto_wkp_family {ι : Type*} [Countable ι]
    {u : ι → ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict W] u i m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ι → ℂ → ℝ, (∀ i, MemWkpLoc p Ω k (v i)) ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ i (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict W] u i (φ j)) →
          Wkp.value k w =ᵐ[volume.restrict W] v i → Tendsto y atTop (𝓝 w) := by
  obtain ⟨E, hEc, hEsucc, hEΩ, hWE⟩ := Ω.exists_isCompact_closure_subset_succ_forall_exists_le
  have hEle : ∀ n, E n ≤ E (n + 1) := fun n =>
    SetLike.coe_subset_coe.1 (subset_closure.trans (hEsucc n))
  obtain ⟨φ, hφ, v, hv⟩ := exists_subseq_tendsto_wkp_of_isCompactOperator hEle
    (fun n => Wkp.isCompactOperator_restrictL_lowerOrderL (hEc n) (hEsucc n) k)
    fun n i => hu (E (n + 1)) (hEc (n + 1)) (hEΩ (n + 1)) i
  refine ⟨φ, hφ, v, fun i => memWkpLoc_of_forall_wkp fun W hWc hWΩ => ?_,
    fun W hWc hWΩ i => ?_⟩
  · obtain ⟨n, hWn⟩ := hWE W hWc hWΩ
    exact (hv n i W hWn).1
  · obtain ⟨n, hWn⟩ := hWE W hWc hWΩ
    exact (hv n i W hWn).2

/-- **Local Rellich compactness.** Let `1 ≤ p ≤ ∞` and let `u m` be real functions bounded in
`W^{k+1,p}` on every relatively compact open subset `W` of `Ω`: each `u m` is represented on `W`
by an element of `Wkp volume W p (k + 1)` of norm at most a bound depending only on `W`. Then a
subsequence `u (φ j)` converges in `W^{k,p}` on every such `W` to a limit `v ∈ MemWkpLoc p Ω k`:
any representatives of `u (φ j)` in `Wkp volume W p k` converge to the representative of `v`.
Representatives exist by `TauCeti.memWkpLoc_iff_forall_wkp`, and are unique by `TauCeti.Wkp.ext`. -/
theorem exists_subseq_memWkpLoc_tendsto_wkp {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict W] u m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℝ, MemWkpLoc p Ω k v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict W] u (φ j)) →
          Wkp.value k w =ᵐ[volume.restrict W] v → Tendsto y atTop (𝓝 w) := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := exists_subseq_memWkpLoc_tendsto_wkp_family (ι := Unit)
    (u := fun _ => u) fun W hWc hWΩ _ => hu W hWc hWΩ
  exact ⟨φ, hφ, v (), hv (), fun W hWc hWΩ => hlim W hWc hWΩ ()⟩

/-- **Local Rellich compactness for vector-valued functions.** Let `F` be a finite-dimensional
real vector space with basis `b`, let `1 ≤ p ≤ ∞`, and let `u m : ℂ → F` have coordinates bounded
in `W^{k+1,p}` on every relatively compact open subset `W` of `Ω`. Then a subsequence `u (φ j)`
converges in `W^{k,p}` on every such `W`, coordinate by coordinate, to a limit
`v ∈ MemWkpLoc p Ω k`. -/
theorem _root_.Module.Basis.exists_subseq_memWkpLoc_tendsto_wkp {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ F)
    {u : ℕ → ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict W] fun z => b.repr (u m z) i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F, MemWkpLoc p Ω k v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ i (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict W] fun z => b.repr (u (φ j) z) i) →
          Wkp.value k w =ᵐ[volume.restrict W] (fun z => b.repr (v z) i) →
          Tendsto y atTop (𝓝 w) := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := exists_subseq_memWkpLoc_tendsto_wkp_family (Ω := Ω)
    (u := fun i m z => b.repr (u m z) i) hu
  obtain ⟨V, hV, hVv⟩ := b.exists_memWkpLoc_repr_eq hv
  exact ⟨φ, hφ, V, hV, fun W hWc hWΩ i y w hy hw => hlim W hWc hWΩ i y w hy (hVv i ▸ hw)⟩

/-! ### Local Rellich compactness up to the real axis -/

/-- Each point `z` of `closure V ∩ {0 ≤ im}` has an open neighbourhood `O` such that `V⁺ ∩ O` lies
in an open subset `P` of `W⁺` on which forgetting one derivative is compact: a disc inside `W⁺`
when `z` is off the real axis, and the upper half of a disc inside `W` centred at `z` when `z` is
on it. -/
private theorem exists_piece_isCompactOperator_lowerOrderL {V W : Opens ℂ}
    (hVW : closure (V : Set ℂ) ⊆ W) {z : ℂ} (hz : z ∈ closure (V : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im})
    (k : ℕ) :
    ∃ O : Opens ℂ, z ∈ O ∧ ∃ P : Opens ℂ, V.upperHalf ⊓ O ≤ P ∧ P ≤ W.upperHalf ∧
      IsCompactOperator (Wkp.lowerOrderL (mu := volume) (p := p) (Omega := P) k) := by
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 W.isOpen z (hVW hz.1)
  have hz0 : 0 ≤ z.im := hz.2
  rcases hz0.lt_or_eq with hz0 | hz0
  · -- Off the axis, a disc around `z` small enough to stay in `W⁺`.
    refine ⟨⟨ball z (min r z.im), isOpen_ball⟩, mem_ball_self (lt_min hr hz0),
      ⟨ball z (min r z.im), isOpen_ball⟩, inf_le_right, fun y hy => ?_,
      Wkp.isCompactOperator_lowerOrderL_complexBall z _ k⟩
    rw [Opens.mem_mk, mem_ball, dist_eq_norm] at hy
    have him := (Complex.abs_im_le_norm (y - z)).trans_lt (hy.trans_le (min_le_right _ _))
    rw [Complex.sub_im, abs_lt] at him
    refine Opens.mem_upperHalf.2 ⟨hrW ?_, by linarith⟩
    rw [mem_ball, dist_eq_norm]
    exact hy.trans_le (min_le_left _ _)
  · -- On the axis, the upper half of a disc in `W` centred at `z`.
    have hzx : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [← hz0])
    refine ⟨⟨ball z r, isOpen_ball⟩, mem_ball_self hr,
      (⟨ball (z.re : ℂ) r, isOpen_ball⟩ : Opens ℂ).upperHalf, fun y hy => ?_,
      Opens.upperHalf_mono fun y hy => hrW ?_,
      Wkp.isCompactOperator_lowerOrderL_upperHalf_complexBall z.re r k⟩
    · obtain ⟨hyV, hyO⟩ := Opens.mem_inf.1 hy
      rw [Opens.mem_mk, ← hzx] at hyO
      exact Opens.mem_upperHalf.2 ⟨Opens.mem_mk.2 hyO, (Opens.mem_upperHalf.1 hyV).2⟩
    · rwa [Opens.mem_mk, hzx] at hy

/-- **Rellich compactness up to the real axis.** Let `V` and `W` be open sets with `closure V`
compact and contained in `W`. Restriction from the upper half `W⁺ = W ∩ {0 < im}` to the upper
half `V⁺`, forgetting one derivative, is a compact operator `W^{k+1,p}(W⁺) → W^{k,p}(V⁺)` for
every `k` and every `1 ≤ p ≤ ∞`. The closure of `V⁺` may reach the real axis, where it leaves
`W⁺`. -/
theorem Wkp.isCompactOperator_restrictL_lowerOrderL_upperHalf {V W : Opens ℂ}
    (hVc : IsCompact (closure (V : Set ℂ))) (hVW : closure (V : Set ℂ) ⊆ W) (k : ℕ) :
    IsCompactOperator ((Wkp.restrictL (mu := volume) (p := p)
      (Opens.upperHalf_mono (SetLike.coe_subset_coe.1 (subset_closure.trans hVW))) k).comp
        (Wkp.lowerOrderL k)) := by
  set K := closure (V : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}
  have hK : IsCompact K := hVc.inter_right (isClosed_le continuous_const Complex.continuous_im)
  choose! O hzO P hOP hPW hPc using fun z (hz : z ∈ K) =>
    exists_piece_isCompactOperator_lowerOrderL (p := p) hVW hz k
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => (O z : Set ℂ)) (fun _ => (O _).isOpen)
    fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, hzO z hz⟩
  -- The finite open cover of `V⁺` by the traces of the chosen neighbourhoods.
  let C : t → Opens ℂ := fun i => V.upperHalf ⊓ O i.val.val
  have hCle : ∀ i, C i ≤ V.upperHalf := fun _ => inf_le_left
  have hcov : V.upperHalf ≤ ⨆ i, C i := fun y hy => by
    obtain ⟨hyV, hy0⟩ := Opens.mem_upperHalf.1 hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (ht ⟨subset_closure hyV, hy0.le⟩)
    exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, Opens.mem_inf.2 ⟨hy, hyi⟩⟩
  refine Wkp.isCompactOperator_of_restrictL hCle hcov fun i => ?_
  -- On each piece the map factors through forgetting a derivative on `P`.
  have hCP : C i ≤ P i.val.val := hOP i.val.val i.val.property
  have hPW' : P i.val.val ≤ W.upperHalf := hPW i.val.val i.val.property
  have hfac : (fun v => Wkp.restrictL (hCle i) k (((Wkp.restrictL (mu := volume) (p := p)
      (Opens.upperHalf_mono (SetLike.coe_subset_coe.1 (subset_closure.trans hVW))) k).comp
        (Wkp.lowerOrderL k)) v)) =
      Wkp.restrictL hCP k ∘ Wkp.lowerOrderL k ∘ Wkp.restrictL hPW' (k + 1) := by
    funext v
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
    rw [Wkp.lowerOrderL_apply, Wkp.lowerOrderL_apply, Wkp.lowerOrder_restrictL,
      Wkp.restrictL_restrictL, Wkp.restrictL_restrictL]
  rw [hfac]
  exact ((hPc i.val.val i.val.property).comp_clm (Wkp.restrictL hPW' (k + 1))).clm_comp
    (Wkp.restrictL hCP k)

/-- **Local Rellich compactness up to the real axis for a countable family of sequences.** A
countable family of sequences of real functions, each bounded in `W^{k+1,p}` on the upper half
`W⁺` of every open `W` whose closure is compact and contained in `Ω`, has a common subsequence
along which every member converges in `W^{k,p}` on every such `W⁺`, to a limit in
`MemWkpLoc p (Ω ∩ {0 ≤ im}) k`. -/
private theorem exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp_family {ι : Type*}
    [Countable ι] {u : ι → ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W.upperHalf p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u i m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ι → ℂ → ℝ,
      (∀ i, MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k (v i)) ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ i (y : ℕ → Wkp volume W.upperHalf p k) (w : Wkp volume W.upperHalf p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u i (φ j)) →
          Wkp.value k w =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] v i →
          Tendsto y atTop (𝓝 w) := by
  obtain ⟨E, hEc, hEsucc, hEΩ, hWE⟩ := Ω.exists_isCompact_closure_subset_succ_forall_exists_le
  have hEle : ∀ n, (E n).upperHalf ≤ (E (n + 1)).upperHalf := fun n =>
    Opens.upperHalf_mono (SetLike.coe_subset_coe.1 (subset_closure.trans (hEsucc n)))
  obtain ⟨φ, hφ, v, hv⟩ := exists_subseq_tendsto_wkp_of_isCompactOperator hEle
    (fun n => Wkp.isCompactOperator_restrictL_lowerOrderL_upperHalf (hEc n) (hEsucc n) k)
    fun n i => hu (E (n + 1)) (hEc (n + 1)) (hEΩ (n + 1)) i
  refine ⟨φ, hφ, v, fun i => memWkpLoc_inter_setOf_im_nonneg_of_forall_wkp fun W hWc hWΩ => ?_,
    fun W hWc hWΩ i => ?_⟩
  · obtain ⟨n, hWn⟩ := hWE W hWc hWΩ
    exact (hv n i W.upperHalf (Opens.upperHalf_mono hWn)).1
  · obtain ⟨n, hWn⟩ := hWE W hWc hWΩ
    exact (hv n i W.upperHalf (Opens.upperHalf_mono hWn)).2

/-- **Local Rellich compactness up to the real axis.** Let `1 ≤ p ≤ ∞` and let `u m` be real
functions bounded in `W^{k+1,p}` on the upper half `W⁺ = W ∩ {0 < im}` of every open `W` whose
closure is compact and contained in `Ω`: each `u m` is represented on `W⁺` by an element of
`Wkp volume W⁺ p (k + 1)` of norm at most a bound depending only on `W`. Such a `W` may meet the
real axis. Then a subsequence `u (φ j)` converges in `W^{k,p}` on every such `W⁺` to a limit
`v ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k`: any representatives of `u (φ j)` in `Wkp volume W⁺ p k`
converge to the representative of `v`. Representatives exist by
`TauCeti.memWkpLoc_inter_setOf_im_nonneg_iff_forall_wkp`. -/
theorem exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W.upperHalf p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℝ,
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ (y : ℕ → Wkp volume W.upperHalf p k) (w : Wkp volume W.upperHalf p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u (φ j)) →
          Wkp.value k w =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] v →
          Tendsto y atTop (𝓝 w) := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ :=
    exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp_family (ι := Unit)
      (u := fun _ => u) fun W hWc hWΩ _ => hu W hWc hWΩ
  exact ⟨φ, hφ, v (), hv (), fun W hWc hWΩ => hlim W hWc hWΩ ()⟩

/-- **Local Rellich compactness up to the real axis for vector-valued functions.** Let `F` be a
finite-dimensional real vector space with basis `b`, let `1 ≤ p ≤ ∞`, and let `u m : ℂ → F` have
coordinates bounded in `W^{k+1,p}` on the upper half `W⁺` of every open `W` whose closure is
compact and contained in `Ω`. Then a subsequence `u (φ j)` converges in `W^{k,p}` on every such
`W⁺`, coordinate by coordinate, to a limit `v ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k`. -/
theorem _root_.Module.Basis.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ F) {u : ℕ → ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W.upperHalf p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)]
          fun z => b.repr (u m z) i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F,
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ i (y : ℕ → Wkp volume W.upperHalf p k) (w : Wkp volume W.upperHalf p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict (W.upperHalf : Set ℂ)]
            fun z => b.repr (u (φ j) z) i) →
          Wkp.value k w =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] (fun z => b.repr (v z) i) →
          Tendsto y atTop (𝓝 w) := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ :=
    exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp_family (Ω := Ω)
      (u := fun i m z => b.repr (u m z) i) hu
  obtain ⟨V, hV, hVv⟩ := b.exists_memWkpLoc_repr_eq hv
  exact ⟨φ, hφ, V, hV, fun W hWc hWΩ i y w hy hw => hlim W hWc hWΩ i y w hy (hVv i ▸ hw)⟩

end TauCeti
