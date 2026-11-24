/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.QuasiIso
import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Relative

/-!
# Semi-free models along a filtration, one stage of cells at a time

Let `M` be a differential graded left module over a differential graded algebra `A`, with an
increasing sequence `F 0 ≤ F 1 ≤ ⋯` of homogeneous `A`-submodules. Suppose that every cycle in
`F 0` is the differential of an element of `F 0`, and that for each `k` a graded set `Q k` of
**cells** is given, with elements `c₀ k q ∈ F (k + 1)` of degree `-indQ k q` whose differentials
lie in `F k`, such that, for the free module on `Q k` with its coefficient differential alone,
every relative cycle of `c₀ k` with target in `F (k + 1)` modulo `F k` is a relative boundary
there. These elementwise hypotheses do not require the `F k` to be stable under the differential.
When they are, so that the `F k` are subcomplexes, the hypotheses say that `F 0` is acyclic and
that `c₀ k` is a quasi-isomorphism onto `F (k + 1)` modulo `F k`. This is the situation of the
chains on the based path space of a CW complex, filtered by the preimages of the skeleta, with
one cell for each cell of the complex: the relative chains over the `k`-skeleton modulo the
`(k - 1)`-skeleton are quasi-isomorphic to a free module over the chains on the loop space with
one generator per `k`-cell.

Attaching the cells of `Q k` to the model of `F k` along cycles, by the single attachment step
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, and iterating over `k`, builds
a **cell-filtered semi-free model** (`TauCeti.exists_semifreeModel_of_filtration`): a row-finite
twisting cocycle `m` on all the cells `Σ k, Q k` together with an augmentation `g` to `M` such
that

* the cell `⟨k, q⟩` has index `indQ k q`, and `g ⟨k, q⟩ ∈ F (k + 1)` agrees with `c₀ k q` modulo
  `F k`;
* `g` is a chain map, given on the generators;
* the row of a cell of stage `k`, its attaching cycle, only involves cells of stages `< k`, so the
  row relation is well-founded and the model is semi-free;
* for every `k`, on the cells of stages `< k`, which span a differential submodule
  (`TauCeti.rowFiniteTwistedDifferential_mem_supported`), relative cycles of `g` with target in
  `F k` are relative boundaries with target in `F k`; when the `F k` are stable under the
  differential, this says that these cells are quasi-isomorphic through `g` to `F k`.

The cell sets are arbitrary, and no finiteness is assumed: every vector of the model involves
finitely many cells, so lies in some finite stage. When the filtration is exhaustive, the
statements for the stages therefore assemble into the same statement with target in `M`
(`TauCeti.exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported`), which is a
quasi-isomorphism onto `M` when the `F k` are stable under the differential.

The attaching cycles are not given: they are found, stage by stage, from the representatives
`c₀ k q`, which are corrected modulo `F k` so that their differentials become images of cycles of
the previous stage. The finite coefficients of these cycles are the rows of the model.

The model is the case of the empty base of the relative construction
`TauCeti.exists_rowFiniteTwistingCocycle_sum_of_forall_exists` (`RowFinite/Attach/Relative.lean`),
with the cells `Σ k, Q k` staged by `Sigma.fst`: since every cycle in `F 0` bounds in `F 0`, the
module with no generators is a base model of `F 0`.

## Main results

* `TauCeti.exists_semifreeModel_of_filtration`: the cell-filtered semi-free model.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6 (semifree modules).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

open Finsupp

namespace TauCeti

universe uR uA uM uP uQ

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} {dM : M →ₗ[R] M}

omit [IsScalarTower R A M] in
/-- **Relative cycles modulo a submodule along a relabelling of the cells.** Let an equivalence
`e : Q' ≃ Q` match the elements `c'` with `c`. If every relative cycle of `c`, for the coefficient
differential, with target in `N'` modulo `N` is a relative boundary there, then the same holds
for `c'`. -/
private theorem exists_mapRange_eq_of_equiv {Q Q' : Type uQ} (e : Q' ≃ Q) {c : Q → M}
    {c' : Q' → M} (hc : ∀ q, c q = c' (e.symm q)) {N N' : Submodule A M}
    (H : ∀ (y : Q →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ N' →
      linearCombination A c y - dM w ∈ N → ∃ (y' : Q →₀ A) (w' : M), w' ∈ N' ∧
        mapRange.linearMap d y' = y ∧ linearCombination A c y' + dM w' - w ∈ N)
    (y : Q' →₀ A) (w : M) (hy : mapRange.linearMap d y = 0) (hw : w ∈ N')
    (hyw : linearCombination A c' y - dM w ∈ N) :
    ∃ (y' : Q' →₀ A) (w' : M), w' ∈ N' ∧ mapRange.linearMap d y' = y ∧
      linearCombination A c' y' + dM w' - w ∈ N := by
  have hce : c ∘ e = c' := funext fun q ↦ by rw [Function.comp_apply, hc, e.symm_apply_apply]
  obtain ⟨y', w', hw', hy', hyw'⟩ := H (equivMapDomain e y) w
    (by ext q; simpa using DFunLike.congr_fun hy (e.symm q)) hw
    (by rwa [linearCombination_equivMapDomain, hce])
  refine ⟨equivMapDomain e.symm y', w', hw', ?_, ?_⟩
  · ext q
    simpa using DFunLike.congr_fun hy' (e q)
  · rwa [linearCombination_equivMapDomain, ← hce, Function.comp_assoc, e.self_comp_symm,
      Function.comp_id]

variable [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] {h : IsDGAlgebra 𝒜 d}

/-- **The cell-filtered semi-free model of a filtered differential graded module.** Let `M` be a
differential graded left module with an increasing sequence of homogeneous submodules `F k`, such
that every cycle in `F 0` is the differential of an element of `F 0`. For each `k`, let `Q k` be a
graded set of cells with representatives `c₀ k q` of degree `-indQ k q` in `F (k + 1)`, whose
differentials lie in `F k`, such that, for the free module on `Q k` with its coefficient
differential, every relative cycle of `c₀ k` with target in `F (k + 1)` modulo `F k` is a relative
boundary there. When the `F k` are stable under `dM`, these hypotheses say that `F 0` is acyclic
and that `c₀ k` is a quasi-isomorphism onto `F (k + 1)` modulo `F k`.

Then there are a row-finite twisting cocycle `m` on all the cells `Σ k, Q k`, the cell `⟨k, q⟩`
of index `indQ k q`, and an augmentation `g` to `M` such that:
* `g` preserves degrees, sends the cell `⟨k, q⟩` into `F (k + 1)`, congruent to `c₀ k q` modulo
  `F k`, and is a chain map;
* the row of a cell of stage `k` only involves cells of stages `< k`, so the row relation is
  well-founded: the model is semi-free;
* for every `k`, the restriction of `g` to the cells of stages `< k` has relative cycles, with
  target in `F k`, that are relative boundaries with target in `F k`; when the `F k` are stable
  under `dM`, this says that it is a quasi-isomorphism onto `F k`.

When the filtration is exhaustive, the last property gives the same statement with target in `M`
(`TauCeti.exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported`), a quasi-isomorphism
onto `M` when the `F k` are stable under `dM`. -/
theorem exists_semifreeModel_of_filtration (hM : IsDGLeftModule h ℳ dM) {F : ℕ → Submodule A M}
    (hF : Monotone F) (hFhom : ∀ k, (F k).IsHomogeneous ℳ)
    (hF₀ : ∀ w ∈ F 0, dM w = 0 → ∃ w' ∈ F 0, dM w' = w) {Q : ℕ → Type uQ}
    {indQ : ∀ k, Q k → ℤ} {c₀ : ∀ k, Q k → M} (hc₀ : ∀ k q, c₀ k q ∈ ℳ (-indQ k q))
    (hc₀F : ∀ k q, c₀ k q ∈ F (k + 1)) (hdc₀ : ∀ k q, dM (c₀ k q) ∈ F k)
    (hQ : ∀ k (y : Q k →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ F (k + 1) →
      linearCombination A (c₀ k) y - dM w ∈ F k → ∃ (y' : Q k →₀ A) (w' : M), w' ∈ F (k + 1) ∧
        mapRange.linearMap d y' = y ∧ linearCombination A (c₀ k) y' + dM w' - w ∈ F k) :
    ∃ (m : RowFiniteTwistingCocycle 𝒜 d (Σ k, Q k) fun x ↦ indQ x.1 x.2) (g : (Σ k, Q k) → M),
      (∀ x, g x ∈ ℳ (-indQ x.1 x.2)) ∧ (∀ x, g x ∈ F (x.1 + 1)) ∧
      (∀ x, g x - c₀ x.1 x.2 ∈ F x.1) ∧ (∀ x, linearCombination A g (m.m x) = dM (g x)) ∧
      (∀ x, m.m x ∈ supported A A {y | y.1 < x.1}) ∧
      WellFounded (fun y x ↦ y ∈ (m.m x).support) ∧
      ∀ (k : ℕ) (f : (Σ k, Q k) →₀ A) (w : M), f ∈ supported A A {y | y.1 < k} →
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0 →
        linearCombination A g f = dM w → w ∈ F k → ∃ (f' : (Σ k, Q k) →₀ A) (w' : M),
          f' ∈ supported A A {y | y.1 < k} ∧ w' ∈ F k ∧
            rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
              linearCombination A g f' + dM w' = w := by
  -- The cells of stage `k` are those of `Q k`.
  have hQ' (k : ℕ) := exists_mapRange_eq_of_equiv (Equiv.sigmaSubtype k)
    (c' := fun x ↦ c₀ x.val.1 x.val.2) (fun _ ↦ rfl) (hQ k)
  obtain ⟨m, c, -, hlt, hcdeg, hcF, hcc₀, hc, hstage, -⟩ :=
    exists_rowFiniteTwistingCocycle_sum_of_forall_exists (ind := fun x ↦ indQ x.1 x.2)
      (indP := Empty.elim) hM 0 Sigma.fst hF hFhom (g := Empty.elim) nofun nofun nofun
      -- The module with no generators is a base model of `F 0`, whose cycles bound in `F 0`.
      (fun u w _ huw hw ↦ by
        have hu : u = 0 := ext fun x ↦ x.elim
        obtain ⟨w', hw', rfl⟩ := hF₀ w hw (by rw [← huw, hu, map_zero])
        exact ⟨0, w', hw', by rw [map_zero, hu], by simp⟩) (c₀ := fun x ↦ c₀ x.1 x.2)
      (fun x ↦ hc₀ x.1 x.2) (fun x ↦ hc₀F x.1 x.2) (fun x ↦ hdc₀ x.1 x.2) hQ'
  -- Read the model back on the cells, along `Sum.inr`.
  have hrange (f : Empty ⊕ (Σ k, Q k) →₀ A) :
      ↑f.support ⊆ Set.range (Sum.inr : (Σ k, Q k) → Empty ⊕ (Σ k, Q k)) := by
    rintro (p | x) -
    exacts [p.elim, ⟨x, rfl⟩]
  let m' : RowFiniteTwistingCocycle 𝒜 d (Σ k, Q k) fun x ↦ indQ x.1 x.2 :=
    .ofComapDomain m.m Sum.inr Sum.inr_injective (fun _ ↦ hrange _)
      (fun x y ↦ m.mem_graded (.inr x) (.inr y)) (fun x ↦ m.differential_row (.inr x))
  have hm' (x : Σ k, Q k) : mapDomain Sum.inr (m'.m x) = m.m (.inr x) :=
    RowFiniteTwistingCocycle.mapDomain_ofComapDomain_m x
  have hD (f : (Σ k, Q k) →₀ A) :
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (mapDomain Sum.inr f) =
        mapDomain Sum.inr (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m'.m f) :=
    RowFiniteTwistingCocycle.rowFiniteTwistedDifferential_mapDomain_ofComapDomain f
  have hL (f : (Σ k, Q k) →₀ A) :
      linearCombination A (Sum.elim Empty.elim c) (mapDomain Sum.inr f) =
        linearCombination A c f := by
    rw [linearCombination_mapDomain, Sum.elim_comp_inr]
  have hsupp (f : (Σ k, Q k) →₀ A) (x : Σ k, Q k) :
      (Sum.inr x : Empty ⊕ (Σ k, Q k)) ∈ (mapDomain Sum.inr f).support ↔ x ∈ f.support := by
    rw [mem_support_iff, mem_support_iff, mapDomain_apply_of_injective Sum.inr_injective]
  have hlt' (x y : Σ k, Q k) (hy : y ∈ (m'.m x).support) : y.1 < x.1 :=
    hlt x y (by rw [← hm']; exact (hsupp _ y).2 hy)
  refine ⟨m', c, hcdeg, hcF, hcc₀, fun x ↦ ?_, fun x ↦ (mem_supported A _).2 (hlt' x),
    Subrelation.wf (fun {y x} ↦ hlt' x y) (InvImage.wf Sigma.fst wellFounded_lt),
    fun k f w hf hDf hfw hw ↦ ?_⟩
  · rw [← hL, hm']
    exact hc x
  -- A relative cycle below stage `k` is one of the relative model.
  · obtain ⟨f', w', hf', hw', hDf', hfw'⟩ := hstage k (mapDomain Sum.inr f) w
      (fun x hx ↦ (mem_supported A f).1 hf ((hsupp f x).1 hx))
      (by rw [hD, hDf, mapDomain_zero]) (by rwa [hL]) hw
    rw [← mapDomain_comapDomain _ Sum.inr_injective f' (hrange f')] at hf' hDf' hfw'
    refine ⟨_, w', (mem_supported A _).2 fun x hx ↦ hf' x ((hsupp _ x).2 hx), hw',
      mapDomain_injective Sum.inr_injective (by rw [← hD, hDf']), by rwa [← hL]⟩

end TauCeti
