/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Coordinates
public import TauCeti.Analysis.Sobolev.Local.Wkp
public import TauCeti.Analysis.Sobolev.Wkp.Local.Compactness

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
by uniqueness of limits, and glue to one function.

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

/-! ### An exhaustion by relatively compact open sets -/

/-- The `n`th set of the exhaustion of `Ω`: points of norm less than `n` at extended distance
more than `1 / (n + 1)` from the complement of `Ω`. -/
private def exhaustion (Ω : Opens ℂ) (n : ℕ) : Opens ℂ :=
  ⟨{z | ‖z‖ < n} ∩ {z | ((n : ℝ≥0∞) + 1)⁻¹ < infEDist z (Ω : Set ℂ)ᶜ},
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const continuous_infEDist)⟩

private theorem mem_exhaustion {n : ℕ} {z : ℂ} :
    z ∈ (exhaustion Ω n : Set ℂ) ↔
      ‖z‖ < n ∧ ((n : ℝ≥0∞) + 1)⁻¹ < infEDist z (Ω : Set ℂ)ᶜ :=
  mem_inter_iff ..

/-- Points of the closure of the `n`th set of the exhaustion have norm at most `n` and extended
distance at least `1 / (n + 1)` from the complement of `Ω`. -/
private theorem closure_exhaustion_subset (n : ℕ) {z : ℂ}
    (hz : z ∈ closure (exhaustion Ω n : Set ℂ)) :
    ‖z‖ ≤ n ∧ ((n : ℝ≥0∞) + 1)⁻¹ ≤ infEDist z (Ω : Set ℂ)ᶜ := by
  have hsub : (exhaustion Ω n : Set ℂ) ⊆
      {z | ‖z‖ ≤ n} ∩ {z | ((n : ℝ≥0∞) + 1)⁻¹ ≤ infEDist z (Ω : Set ℂ)ᶜ} := fun x hx => by
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨(mem_exhaustion.1 hx).1.le, (mem_exhaustion.1 hx).2.le⟩
  have h := closure_minimal hsub ((isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const continuous_infEDist)) hz
  simpa only [mem_inter_iff, mem_ofPred_eq] using h

private theorem isCompact_closure_exhaustion (n : ℕ) :
    IsCompact (closure (exhaustion Ω n : Set ℂ)) :=
  (isCompact_closedBall (0 : ℂ) n).of_isClosed_subset isClosed_closure fun _ hz =>
    mem_closedBall_zero_iff.2 (closure_exhaustion_subset n hz).1

private theorem closure_exhaustion_subset_succ (n : ℕ) :
    closure (exhaustion Ω n : Set ℂ) ⊆ exhaustion Ω (n + 1) := fun z hz => by
  obtain ⟨hz₁, hz₂⟩ := closure_exhaustion_subset n hz
  refine mem_exhaustion.2 ⟨by push_cast; linarith, lt_of_lt_of_le ?_ hz₂⟩
  refine ENNReal.inv_lt_inv.2 ?_
  push_cast
  exact ENNReal.lt_add_right (by finiteness) one_ne_zero

private theorem exhaustion_le_succ (n : ℕ) : exhaustion Ω n ≤ exhaustion Ω (n + 1) :=
  SetLike.coe_subset_coe.1 (subset_closure.trans (closure_exhaustion_subset_succ n))

private theorem monotone_exhaustion : Monotone (exhaustion Ω) :=
  monotone_nat_of_le_succ exhaustion_le_succ

private theorem closure_exhaustion_subset_self (n : ℕ) :
    closure (exhaustion Ω n : Set ℂ) ⊆ Ω := fun z hz => by
  by_contra hzΩ
  have h := (closure_exhaustion_subset n hz).2
  rw [infEDist_zero_of_mem hzΩ, nonpos_iff_eq_zero, ENNReal.inv_eq_zero] at h
  exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩ h

private theorem iUnion_exhaustion : ⋃ n, (exhaustion Ω n : Set ℂ) = Ω := by
  refine subset_antisymm (iUnion_subset fun n => subset_closure.trans
    (closure_exhaustion_subset_self n)) fun z hz => ?_
  have hpos : infEDist z (Ω : Set ℂ)ᶜ ≠ 0 := fun h =>
    ((mem_iff_infEDist_zero_of_closed Ω.isOpen.isClosed_compl).2 h) hz
  obtain ⟨M, hM⟩ := ENNReal.exists_inv_nat_lt hpos
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  refine mem_iUnion.2 ⟨max N M, mem_exhaustion.2
    ⟨lt_of_lt_of_le hN (by exact_mod_cast le_max_left N M), lt_of_le_of_lt ?_ hM⟩⟩
  refine ENNReal.inv_le_inv.2 ?_
  exact le_add_right (by exact_mod_cast le_max_right N M)

/-- Every relatively compact open subset of `Ω` lies in some set of the exhaustion. -/
private theorem exists_subset_exhaustion {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) : ∃ n, W ≤ exhaustion Ω n := by
  obtain ⟨n, hn⟩ := hWc.elim_directed_cover (fun n => (exhaustion Ω n : Set ℂ))
    (fun n => (exhaustion Ω n).isOpen) (hWΩ.trans iUnion_exhaustion.symm.subset)
    (Monotone.directed_le fun _ _ h => SetLike.coe_subset_coe.2 (monotone_exhaustion h))
  exact ⟨n, SetLike.coe_subset_coe.1 (subset_closure.trans hn)⟩

/-! ### Local Rellich compactness -/

/-- Two scalar Sobolev elements on nested open sets whose values agree almost everywhere with the
same function agree after restriction. -/
private theorem restrictL_eq_of_value_ae_eq {W W' : Opens ℂ} (h : W ≤ W')
    {y : Wkp volume W p k} {y' : Wkp volume W' p k} {f : ℂ → ℝ}
    (hy : Wkp.value k y =ᵐ[volume.restrict W] f) (hy' : Wkp.value k y' =ᵐ[volume.restrict W'] f) :
    Wkp.restrictL h k y' = y :=
  Wkp.ext k (Lp.ext ((Wkp.value_restrictL_ae h k y').trans
    (EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 h) hy')
      hy.symm)))

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
  set E := exhaustion Ω
  choose R V hVR hVu using fun (n : ℕ) i =>
    hu (E (n + 1)) (isCompact_closure_exhaustion (n + 1)) (closure_exhaustion_subset_self (n + 1)) i
  -- The compact operators from `E (n + 1)` to `E n`.
  let T : ∀ n : ℕ, Wkp volume (E (n + 1)) p (k + 1) →L[ℝ] Wkp volume (E n) p k := fun n =>
    (Wkp.restrictL (exhaustion_le_succ n) k).comp (Wkp.lowerOrderL k)
  have hT : ∀ n, IsCompactOperator (T n) := fun n =>
    Wkp.isCompactOperator_restrictL_lowerOrderL (isCompact_closure_exhaustion n)
      (closure_exhaustion_subset_succ n) k
  have hTval : ∀ n (w : Wkp volume (E (n + 1)) p (k + 1)),
      Wkp.value k (T n w) =ᵐ[volume.restrict (E n)] Wkp.value (k + 1) w := fun n w => by
    have hTw : T n w = Wkp.restrictL (exhaustion_le_succ n) k (Wkp.lowerOrder k w) := by
      change Wkp.restrictL _ k (Wkp.lowerOrderL k w) = _
      rw [Wkp.lowerOrderL_apply]
    rw [hTw, Wkp.value_succ]
    exact Wkp.value_restrictL_ae _ k _
  -- The sequence in the product over levels and coordinates, and its values.
  let x : ℕ → ∀ q : ℕ × ι, Wkp volume (E q.1) p k := fun m q => T q.1 (V q.1 q.2 m)
  have hxval : ∀ m (q : ℕ × ι), Wkp.value k (x m q) =ᵐ[volume.restrict (E q.1)] u q.2 m :=
    fun m q => (hTval q.1 _).trans (ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.2 (exhaustion_le_succ q.1)) (hVu q.1 q.2 m))
  have hS : IsCompact (univ.pi fun q : ℕ × ι => closure (T q.1 '' closedBall 0 (R q.1 q.2))) :=
    isCompact_univ_pi fun q => (hT q.1).isCompact_closure_image_closedBall _
  obtain ⟨a, -, φ, hφ, hxa⟩ := hS.tendsto_subseq (x := x) fun m q _ =>
    subset_closure ⟨V q.1 q.2 m, mem_closedBall_zero_iff.2 (hVR q.1 q.2 m), rfl⟩
  have hxa' : ∀ q, Tendsto (fun j => x (φ j) q) atTop (𝓝 (a q)) := tendsto_pi_nhds.1 hxa
  -- The limits on the different levels agree under restriction.
  have hcompat : ∀ i {n n'} (h : n ≤ n'),
      Wkp.restrictL (monotone_exhaustion h) k (a (n', i)) = a (n, i) := fun i n n' h => by
    have hres : ∀ m, Wkp.restrictL (monotone_exhaustion h) k (x m (n', i)) = x m (n, i) :=
      fun m => restrictL_eq_of_value_ae_eq _ (hxval m (n, i)) (hxval m (n', i))
    refine tendsto_nhds_unique ?_ (hxa' (n, i))
    simpa only [Function.comp_def, hres] using
      ((Wkp.restrictL (monotone_exhaustion h) k).continuous.tendsto _).comp (hxa' (n', i))
  -- Glue the limits.
  classical
  let v : ι → ℂ → ℝ := fun i z =>
    if h : ∃ n, z ∈ E n then Wkp.value k (a (Nat.find h, i)) z else 0
  have hv : ∀ i n, Wkp.value k (a (n, i)) =ᵐ[volume.restrict (E n)] v i := fun i n => by
    have hm : ∀ m, ∀ᵐ z ∂volume, z ∈ E n → z ∈ E m →
        Wkp.value k (a (m, i)) z = Wkp.value k (a (n, i)) z := by
      intro m
      rcases le_total m n with hmn | hnm
      · have h := (Wkp.value_restrictL_ae (monotone_exhaustion hmn) k (a (n, i))).symm.trans
          (by rw [hcompat i hmn])
        filter_upwards [(ae_restrict_iff' (E m).isOpen.measurableSet).1 h] with z hz _ hzm
        exact (hz hzm).symm
      · have h := (Wkp.value_restrictL_ae (monotone_exhaustion hnm) k (a (m, i))).symm.trans
          (by rw [hcompat i hnm])
        filter_upwards [(ae_restrict_iff' (E n).isOpen.measurableSet).1 h] with z hz hzn _
        exact hz hzn
    filter_upwards [ae_restrict_of_ae (ae_all_iff.2 hm), ae_restrict_mem (E n).isOpen.measurableSet]
      with z hz hzn
    have hex : ∃ n, z ∈ E n := ⟨n, hzn⟩
    simp only [v, hex, ↓reduceDIte]
    exact (hz (Nat.find hex) hzn (Nat.find_spec hex)).symm
  refine ⟨φ, hφ, v, fun i => ?_, ?_⟩
  · refine memWkpLoc_of_forall_wkp fun W hWc hWΩ => ?_
    obtain ⟨n, hWn⟩ := exists_subset_exhaustion hWc hWΩ
    exact ⟨Wkp.restrictL hWn k (a (n, i)), (Wkp.value_restrictL_ae hWn k _).trans
      (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hWn) (hv i n))⟩
  · intro W hWc hWΩ i y w hy hw
    obtain ⟨n, hWn⟩ := exists_subset_exhaustion hWc hWΩ
    have hy' : ∀ j, Wkp.restrictL hWn k (x (φ j) (n, i)) = y j := fun j =>
      restrictL_eq_of_value_ae_eq hWn (hy j) (hxval (φ j) (n, i))
    have hw' : Wkp.restrictL hWn k (a (n, i)) = w := restrictL_eq_of_value_ae_eq hWn hw (hv i n)
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
