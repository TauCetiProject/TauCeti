/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Coordinates
public import TauCeti.Analysis.Sobolev.Local.Wkp
public import TauCeti.Analysis.Sobolev.Wkp.Local.Compactness
public import TauCeti.MeasureTheory.Function.Gluing
public import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# Local Rellich compactness for local Sobolev classes

Let `Ω` be an open subset of `ℂ` and `1 ≤ p ≤ ∞`. A sequence of functions `u m : ℂ → F`, with
`F` a finite-dimensional real vector space, which is bounded in `W^{k+1,p}` on every relatively
compact open subset of `Ω` has a subsequence converging in `W^{k,p}` on every relatively compact
open subset of `Ω`, to a limit in `MemWkpLoc p Ω k`.

Boundedness and convergence are expressed through the scalar Sobolev spaces `TauCeti.Wkp` on
the relatively compact open subsets `W` of `Ω` (open sets whose closure is compact and contained
in `Ω`), applied to the coordinates of `u m` in a basis of `F`; no local norm is introduced. By
`TauCeti.memWkpLoc_iff_forall_wkp` and `Module.Basis.memWkpLoc_iff`, the boundedness hypothesis
already places every `u m` in `MemWkpLoc p Ω (k + 1)`.

The proof exhausts `Ω` by an increasing sequence of relatively compact open sets `E n`, each with
closure inside the next. Restriction from `E (n + 1)` to `E n` while forgetting one derivative is
a compact operator, `TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`, so the sequence lies in
a compact subset of the countable product of the spaces `Wkp volume (E n) p k`, one factor for each
level `n` and each coordinate. A single subsequence therefore converges in every factor at once,
which replaces the diagonal argument. The limits on the different `E n` agree under restriction,
by uniqueness of limits, and glue to one function by
`TauCeti.exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter`.

## Main declarations

* `TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`: local Rellich for real functions.
* `Module.Basis.exists_subseq_memWkpLoc_tendsto_wkp`: local Rellich for functions valued in a
  finite-dimensional real vector space, through the coordinates in a basis.

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

/-! ### Local Rellich compactness -/

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
  obtain ⟨E, hEc, hEsucc, hEU⟩ := Ω.exists_isCompact_closure_subset_succ_iUnion_eq
  have hEle : ∀ n, E n ≤ E (n + 1) := fun n =>
    SetLike.coe_subset_coe.1 (subset_closure.trans (hEsucc n))
  have hEmono : Monotone E := monotone_nat_of_le_succ hEle
  have hEΩ : ∀ n, closure (E n : Set ℂ) ⊆ Ω := fun n =>
    (hEsucc n).trans (hEU ▸ subset_iUnion (fun n => (E n : Set ℂ)) (n + 1))
  -- Every relatively compact open subset of `Ω` lies in some `E n`.
  have hWE : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ n, W ≤ E n := fun W hWc hWΩ => by
    obtain ⟨n, hn⟩ := hWc.elim_directed_cover (fun n => (E n : Set ℂ)) (fun n => (E n).isOpen)
      (hWΩ.trans hEU.symm.subset)
      (Monotone.directed_le fun _ _ h => SetLike.coe_subset_coe.2 (hEmono h))
    exact ⟨n, SetLike.coe_subset_coe.1 (subset_closure.trans hn)⟩
  choose R V hVR hVu using fun (n : ℕ) i => hu (E (n + 1)) (hEc (n + 1)) (hEΩ (n + 1)) i
  -- The compact operators from `E (n + 1)` to `E n`.
  let T : ∀ n : ℕ, Wkp volume (E (n + 1)) p (k + 1) →L[ℝ] Wkp volume (E n) p k := fun n =>
    (Wkp.restrictL (hEle n) k).comp (Wkp.lowerOrderL k)
  have hT : ∀ n, IsCompactOperator (T n) := fun n =>
    Wkp.isCompactOperator_restrictL_lowerOrderL (hEc n) (hEsucc n) k
  have hTval : ∀ n (w : Wkp volume (E (n + 1)) p (k + 1)),
      Wkp.value k (T n w) =ᵐ[volume.restrict (E n)] Wkp.value (k + 1) w := fun n w => by
    have hTw : T n w = Wkp.restrictL (hEle n) k (Wkp.lowerOrder k w) := by
      simp only [T, ContinuousLinearMap.comp_apply]
      rw [Wkp.lowerOrderL_apply]
    rw [hTw, Wkp.value_succ]
    exact Wkp.value_restrictL_ae _ k _
  -- The sequence in the product over levels and coordinates, and its values.
  let x : ℕ → ∀ q : ℕ × ι, Wkp volume (E q.1) p k := fun m q => T q.1 (V q.1 q.2 m)
  have hxval : ∀ m (q : ℕ × ι), Wkp.value k (x m q) =ᵐ[volume.restrict (E q.1)] u q.2 m :=
    fun m q => (hTval q.1 _).trans (ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.2 (hEle q.1)) (hVu q.1 q.2 m))
  have hS : IsCompact (univ.pi fun q : ℕ × ι => closure (T q.1 '' closedBall 0 (R q.1 q.2))) :=
    isCompact_univ_pi fun q => (hT q.1).isCompact_closure_image_closedBall _
  obtain ⟨a, -, φ, hφ, hxa⟩ := hS.tendsto_subseq (x := x) fun m q _ =>
    subset_closure ⟨V q.1 q.2 m, mem_closedBall_zero_iff.2 (hVR q.1 q.2 m), rfl⟩
  have hxa' : ∀ q, Tendsto (fun j => x (φ j) q) atTop (𝓝 (a q)) := tendsto_pi_nhds.1 hxa
  -- The limits on the different levels agree under restriction.
  have hcompat : ∀ i {n n'} (h : n ≤ n'),
      Wkp.restrictL (hEmono h) k (a (n', i)) = a (n, i) := fun i n n' h => by
    have hres : ∀ m, Wkp.restrictL (hEmono h) k (x m (n', i)) = x m (n, i) :=
      fun m => Wkp.restrictL_eq_of_value_ae_eq_restrict _ k (hxval m (n', i)) (hxval m (n, i))
    refine tendsto_nhds_unique ?_ (hxa' (n, i))
    simpa only [Function.comp_def, hres] using
      ((Wkp.restrictL (hEmono h) k).continuous.tendsto _).comp (hxa' (n', i))
  -- Glue the limits.
  have hcompat_ae : ∀ i {n n'} (h : n ≤ n'),
      Wkp.value k (a (n, i)) =ᵐ[volume.restrict (E n)] Wkp.value k (a (n', i)) :=
    fun i n n' h => by
      rw [← hcompat i h]
      exact Wkp.value_restrictL_ae (hEmono h) k _
  choose v hv' using fun i => exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter (μ := volume)
    (a := fun n => Wkp.value k (a (n, i))) (fun n => (E n).isOpen.measurableSet) fun n n' => by
      rcases le_total n n' with h | h
      · rw [inter_eq_left.2 (SetLike.coe_subset_coe.2 (hEmono h))]
        exact hcompat_ae i h
      · rw [inter_eq_right.2 (SetLike.coe_subset_coe.2 (hEmono h))]
        exact (hcompat_ae i h).symm
  have hv : ∀ i n, Wkp.value k (a (n, i)) =ᵐ[volume.restrict (E n)] v i := fun i n =>
    (hv' i n).symm
  refine ⟨φ, hφ, v, fun i => ?_, ?_⟩
  · refine memWkpLoc_of_forall_wkp fun W hWc hWΩ => ?_
    obtain ⟨n, hWn⟩ := hWE W hWc hWΩ
    exact ⟨Wkp.restrictL hWn k (a (n, i)), (Wkp.value_restrictL_ae hWn k _).trans
      (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hWn) (hv i n))⟩
  · intro W hWc hWΩ i y w hy hw
    obtain ⟨n, hWn⟩ := hWE W hWc hWΩ
    have hy' : ∀ j, Wkp.restrictL hWn k (x (φ j) (n, i)) = y j := fun j =>
      Wkp.restrictL_eq_of_value_ae_eq_restrict hWn k (hxval (φ j) (n, i)) (hy j)
    have hw' : Wkp.restrictL hWn k (a (n, i)) = w :=
      Wkp.restrictL_eq_of_value_ae_eq_restrict hWn k (hv i n) hw
    simpa only [Function.comp_def, hy', hw'] using
      ((Wkp.restrictL hWn k).continuous.tendsto _).comp (hxa' (n, i))

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
  have := Fintype.ofFinite ι
  obtain ⟨φ, hφ, v, hv, hlim⟩ := exists_subseq_memWkpLoc_tendsto_wkp_family (Ω := Ω)
    (u := fun i m z => b.repr (u m z) i) hu
  have hrepr : ∀ z i, b.repr (b.equivFun.symm (fun j => v j z)) i = v i z := fun z i => by
    rw [← b.equivFun_apply, b.equivFun.apply_symm_apply]
  refine ⟨φ, hφ, fun z => b.equivFun.symm fun j => v j z, ?_, fun W hWc hWΩ i y w hy hw =>
    hlim W hWc hWΩ i y w hy ?_⟩
  · exact b.memWkpLoc_iff.2 fun i => by simpa only [hrepr] using hv i
  · simpa only [hrepr] using hw

end TauCeti
