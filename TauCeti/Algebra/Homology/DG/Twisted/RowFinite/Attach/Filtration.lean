/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.QuasiIso
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Tower
public import TauCeti.LinearAlgebra.Finsupp.Supported

/-!
# Semi-free models along a filtration, one stage of cells at a time

Let `M` be a differential graded left module over a differential graded algebra `A`, with an
increasing sequence `F 0 ≤ F 1 ≤ ⋯` of homogeneous `A`-submodules. Suppose that `F 0` is acyclic,
and that for each `k` a graded set `Q k` of **cells** is given, with elements `c₀ k q ∈ F (k + 1)`
of degree `-indQ k q` whose differentials lie in `F k`, through which the free module on `Q k`,
with its coefficient differential alone, is quasi-isomorphic to `F (k + 1)` modulo `F k`. This is
the situation of the chains on the based path space of a CW complex, filtered by the preimages of
the skeleta, with one cell for each cell of the complex: the relative chains over the
`k`-skeleton modulo the `(k - 1)`-skeleton are quasi-isomorphic to a free module over the chains
on the loop space with one generator per `k`-cell.

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
* for every `k`, the cells of stages `< k`, which span a differential submodule
  (`TauCeti.rowFiniteTwistedDifferential_mem_supported`), are quasi-isomorphic through `g` to
  `F k`: relative cycles with target in `F k` are relative boundaries with target in `F k`.

The cell sets are arbitrary, and no finiteness is assumed: every vector of the model involves
finitely many cells, so lies in some finite stage. When the filtration is exhaustive, the
quasi-isomorphisms onto the stages therefore assemble into a quasi-isomorphism onto `M`
(`TauCeti.exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported`).

The attaching cycles are not given: they are found, stage by stage, from the representatives
`c₀ k q`, which are corrected modulo `F k` so that their differentials become images of cycles of
the previous stage. The finite coefficients of these cycles are the rows of the model.

The stages and their union form a tower of cell attachments
(`TauCeti.RowFiniteAugmentedModule.tower`), the stage-tower construction behind the semi-free
resolution `TauCeti.semifreeResolution` (`RowFinite/Resolution.lean`), which this file follows.
There each stage attaches its own homogeneous relative cycles; here the cells are prescribed, and
each stage carries the quasi-isomorphism onto `F k` that the next attachment step needs.

## Main results

* `TauCeti.exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported`: quasi-isomorphisms
  onto the stages of an exhaustive filtration, from the generators of rank `< k`, give a
  quasi-isomorphism onto the union.
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
/-- **Quasi-isomorphisms onto the stages of an exhaustive filtration assemble.** Let the
generators carry a rank `r` in `ℕ`, and let `F` be an increasing, exhaustive sequence of
submodules of `M`. If for every `k` the map `g`, restricted to the generators of rank `< k`, has
relative cycles with target in `F k` that are relative boundaries, then every relative cycle of
`g` is a relative boundary. -/
theorem exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported (m : P → P →₀ A)
    {g : P → M} (r : P → ℕ) {F : ℕ → Submodule A M} (hF : Monotone F)
    (hFex : ∀ w, ∃ k, w ∈ F k)
    (hK : ∀ (k : ℕ) (f : P →₀ A) (w : M), f ∈ supported A A {y | r y < k} →
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f = 0 →
      linearCombination A g f = dM w → w ∈ F k → ∃ (f' : P →₀ A) (w' : M),
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f' = f ∧
          linearCombination A g f' + dM w' = w)
    {f : P →₀ A} {w : M} (hf : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f = 0)
    (hfw : linearCombination A g f = dM w) :
    ∃ (f' : P →₀ A) (w' : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f' = f ∧
      linearCombination A g f' + dM w' = w := by
  obtain ⟨k₁, hk₁⟩ := hFex w
  -- `f` involves finitely many generators, so it lies below some rank.
  obtain ⟨k₀, hk₀⟩ := exists_mem_supported_lt (R := A) r f
  exact hK (max k₀ k₁) f w
    (supported_mono (Set.ofPred_subset_ofPred.2 fun _ ↦ lt_max_of_lt_left) hk₀) hf hfw
    (hF (le_max_right k₀ k₁) hk₁)

/-! ### The stages of the construction -/

variable [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] {h : IsDGAlgebra 𝒜 d}

/-- An augmented module is a quasi-isomorphism onto `N` when the images of its generators lie in
`N` and its relative cycles with target in `N` are relative boundaries with target in `N`. -/
private def IsQuasiIsoOnto (S : RowFiniteAugmentedModule.{uR, uA, uM, uQ} 𝒜 d ℳ dM)
    (N : Submodule A M) : Prop :=
  (∀ x, S.g x ∈ N) ∧ ∀ (u : S.P →₀ A) (w : M),
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) S.m.m u = 0 →
    linearCombination A S.g u = dM w → w ∈ N → ∃ (u' : S.P →₀ A) (w' : M), w' ∈ N ∧
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) S.m.m u' = u ∧
        linearCombination A S.g u' + dM w' = w

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- The module with no generators is a quasi-isomorphism onto an acyclic submodule. -/
private theorem isQuasiIsoOnto_empty {N : Submodule A M}
    (hN : ∀ w ∈ N, dM w = 0 → ∃ w' ∈ N, dM w' = w) :
    IsQuasiIsoOnto (RowFiniteAugmentedModule.empty.{uR, uA, uM, uQ} 𝒜 d ℳ dM) N := by
  refine ⟨nofun, fun u w _ huw hw ↦ ?_⟩
  have hu : u = 0 := ext fun x ↦ PEmpty.elim x
  obtain ⟨w', hw', rfl⟩ := hN w hw (by rw [← huw, hu, map_zero])
  exact ⟨0, w', hw', by rw [map_zero, hu], by simp⟩

/-- The trivial attachment of new generators, along zero cycles and with zero images. -/
private def zeroAttachment (S : RowFiniteAugmentedModule.{uR, uA, uM, uQ} 𝒜 d ℳ dM)
    {Q : Type uQ} (indQ : Q → ℤ) : S.Attachment indQ where
  a := 0
  ha _ _ := zero_mem _
  hca _ := map_zero _
  c := 0
  c_mem _ := zero_mem _
  g_a _ := by simp

/-- The input of the construction: a differential graded left module with an increasing sequence
of homogeneous submodules `F k`, with `F 0` acyclic, and for each `k` cells `Q k` with
representatives `c₀ k q` of relative cycles of `F (k + 1)` modulo `F k`, through which the free
module on `Q k` is quasi-isomorphic to `F (k + 1)` modulo `F k`. -/
private structure FilteredCells (Q : ℕ → Type uQ) where
  /-- The module is a differential graded left module. -/
  isDGLeftModule : IsDGLeftModule h ℳ dM
  /-- The filtration. -/
  F : ℕ → Submodule A M
  /-- The filtration is increasing. -/
  mono : Monotone F
  /-- The stages of the filtration are homogeneous. -/
  isHomogeneous : ∀ k, (F k).IsHomogeneous ℳ
  /-- The first stage is acyclic. -/
  acyclic : ∀ w ∈ F 0, dM w = 0 → ∃ w' ∈ F 0, dM w' = w
  /-- The indices of the cells. -/
  indQ : ∀ k, Q k → ℤ
  /-- The representatives of the cells. -/
  c₀ : ∀ k, Q k → M
  /-- The representatives have the degrees of the cells. -/
  c₀_deg : ∀ k q, c₀ k q ∈ ℳ (-indQ k q)
  /-- The representatives of the cells of stage `k` lie in `F (k + 1)`. -/
  c₀_mem : ∀ k q, c₀ k q ∈ F (k + 1)
  /-- The representatives are relative cycles modulo the previous stage. -/
  dM_c₀_mem : ∀ k q, dM (c₀ k q) ∈ F k
  /-- The cells of stage `k` are quasi-isomorphic to `F (k + 1)` modulo `F k`. -/
  rel : ∀ k (y : Q k →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ F (k + 1) →
    linearCombination A (c₀ k) y - dM w ∈ F k → ∃ (y' : Q k →₀ A) (w' : M), w' ∈ F (k + 1) ∧
      mapRange.linearMap d y' = y ∧ linearCombination A (c₀ k) y' + dM w' - w ∈ F k

namespace FilteredCells

variable {Q : ℕ → Type uQ}

/-- An attachment of the cells of stage `k` is good when the images of the cells lie in
`F (k + 1)`, agree with their representatives modulo `F k`, and the attached module is a
quasi-isomorphism onto `F (k + 1)`. -/
private def IsGood (C : FilteredCells (h := h) (ℳ := ℳ) (dM := dM) Q) (k : ℕ)
    (S : RowFiniteAugmentedModule.{uR, uA, uM, uQ} 𝒜 d ℳ dM)
    (T : S.Attachment (C.indQ k)) : Prop :=
  (∀ q, T.c q ∈ C.F (k + 1)) ∧ (∀ q, T.c q - C.c₀ k q ∈ C.F k) ∧
    IsQuasiIsoOnto (S.attach T) (C.F (k + 1))

/-- The cells of stage `k` can be attached well to a quasi-isomorphism onto `F k`, by the single
attachment step. -/
private theorem exists_isGood (C : FilteredCells (h := h) (ℳ := ℳ) (dM := dM) Q) (k : ℕ)
    {S : RowFiniteAugmentedModule.{uR, uA, uM, uQ} 𝒜 d ℳ dM} (hS : IsQuasiIsoOnto S (C.F k)) :
    ∃ T, C.IsGood k S T := by
  obtain ⟨a, ha, hca, c, hcdeg, hcN, hcc₀, hca', hrel⟩ :=
    S.m.exists_attach_of_forall_exists C.isDGLeftModule (C.isHomogeneous k) (C.mono k.le_succ)
      hS.1 S.g_mem S.g_m hS.2 (C.c₀_deg k) (C.c₀_mem k) (C.dM_c₀_mem k) (C.rel k)
  refine ⟨⟨a, ha, hca, c, hcdeg, hca'⟩, hcN, hcc₀, ?_, hrel⟩
  rintro (x | q)
  · rw [RowFiniteAugmentedModule.attach_g_inl]
    exact C.mono k.le_succ (hS.1 x)
  · rw [RowFiniteAugmentedModule.attach_g_inr]
    exact hcN q

/-- The attachment of the cells of stage `k`: a good one whenever one exists. -/
private noncomputable def step (C : FilteredCells (h := h) (ℳ := ℳ) (dM := dM) Q) (k : ℕ)
    (S : RowFiniteAugmentedModule.{uR, uA, uM, uQ} 𝒜 d ℳ dM) :
    S.Attachment (C.indQ k) :=
  @Classical.epsilon _ ⟨zeroAttachment S (C.indQ k)⟩ (C.IsGood k S)

/-- The stages of the construction are quasi-isomorphisms onto the stages of the filtration. -/
private theorem isQuasiIsoOnto_tower (C : FilteredCells (h := h) (ℳ := ℳ) (dM := dM) Q) :
    ∀ k, IsQuasiIsoOnto (RowFiniteAugmentedModule.tower C.step k) (C.F k)
  | 0 => isQuasiIsoOnto_empty C.acyclic
  | k + 1 => by
    rw [RowFiniteAugmentedModule.tower_succ]
    exact (Classical.epsilon_spec (C.exists_isGood k (isQuasiIsoOnto_tower C k))).2.2

/-- The attachment of the cells of stage `k` to the stage `k` of the construction is good. -/
private theorem isGood_step (C : FilteredCells (h := h) (ℳ := ℳ) (dM := dM) Q)
    (k : ℕ) :
    C.IsGood k _ (C.step k (RowFiniteAugmentedModule.tower C.step k)) :=
  Classical.epsilon_spec (C.exists_isGood k (C.isQuasiIsoOnto_tower k))

/-- Stage `k` of the model is a quasi-isomorphism onto `F k`. -/
private theorem exists_towerCocycle_eq (C : FilteredCells (h := h) (ℳ := ℳ) (dM := dM) Q)
    (k : ℕ) (f : (Σ j, Q j) →₀ A) (w : M) (hf : f ∈ supported A A {y | y.1 < k})
    (hDf : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d)
      (RowFiniteAugmentedModule.towerCocycle C.step).m f = 0)
    (hfw : linearCombination A (RowFiniteAugmentedModule.towerAugmentation C.step) f = dM w)
    (hw : w ∈ C.F k) :
    ∃ (f' : (Σ j, Q j) →₀ A) (w' : M), f' ∈ supported A A {y | y.1 < k} ∧ w' ∈ C.F k ∧
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d)
        (RowFiniteAugmentedModule.towerCocycle C.step).m f' = f ∧
        linearCombination A (RowFiniteAugmentedModule.towerAugmentation C.step) f' + dM w' = w := by
  obtain ⟨f₀, rfl⟩ := RowFiniteAugmentedModule.exists_mapDomain_towerOf_eq C.step hf
  rw [RowFiniteAugmentedModule.rowFiniteTwistedDifferential_towerCocycle_mapDomain_eq_zero_iff]
    at hDf
  rw [RowFiniteAugmentedModule.linearCombination_towerAugmentation_mapDomain] at hfw
  obtain ⟨u', w', hw', hu', huw⟩ := (C.isQuasiIsoOnto_tower k).2 f₀ w hDf hfw hw
  refine ⟨mapDomain (RowFiniteAugmentedModule.towerOf C.step k) u', w',
    RowFiniteAugmentedModule.mapDomain_towerOf_mem_supported C.step k u', hw', ?_, ?_⟩
  · rw [RowFiniteAugmentedModule.rowFiniteTwistedDifferential_towerCocycle_mapDomain, hu']
  · rwa [RowFiniteAugmentedModule.linearCombination_towerAugmentation_mapDomain]

end FilteredCells

/-- **The cell-filtered semi-free model of a filtered differential graded module.** Let `M` be a
differential graded left module with an increasing sequence of homogeneous submodules `F k`, with
`F 0` acyclic. For each `k`, let `Q k` be a graded set of cells with representatives `c₀ k q` of
degree `-indQ k q` in `F (k + 1)`, whose differentials lie in `F k`, through which the free module
on `Q k`, with its coefficient differential, is quasi-isomorphic to `F (k + 1)` modulo `F k`.

Then there are a row-finite twisting cocycle `m` on all the cells `Σ k, Q k`, the cell `⟨k, q⟩`
of index `indQ k q`, and an augmentation `g` to `M` such that:
* `g` preserves degrees, sends the cell `⟨k, q⟩` into `F (k + 1)`, congruent to `c₀ k q` modulo
  `F k`, and is a chain map;
* the row of a cell of stage `k` only involves cells of stages `< k`, so the row relation is
  well-founded: the model is semi-free;
* for every `k`, the restriction of `g` to the cells of stages `< k` has relative cycles, with
  target in `F k`, that are relative boundaries with target in `F k`: it is a quasi-isomorphism
  onto `F k`.

When the filtration is exhaustive, the last property gives a quasi-isomorphism onto `M`
(`TauCeti.exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported`). -/
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
  let C : FilteredCells (h := h) (ℳ := ℳ) (dM := dM) Q :=
    ⟨hM, F, hF, hFhom, hF₀, indQ, c₀, hc₀, hc₀F, hdc₀, hQ⟩
  exact ⟨RowFiniteAugmentedModule.towerCocycle C.step,
    RowFiniteAugmentedModule.towerAugmentation C.step,
    RowFiniteAugmentedModule.towerAugmentation_mem C.step,
    fun ⟨k, q⟩ ↦ by
      rw [RowFiniteAugmentedModule.towerAugmentation_mk]
      exact (C.isGood_step k).1 q,
    fun ⟨k, q⟩ ↦ by
      rw [RowFiniteAugmentedModule.towerAugmentation_mk]
      exact (C.isGood_step k).2.1 q,
    RowFiniteAugmentedModule.linearCombination_towerAugmentation_m C.step,
    RowFiniteAugmentedModule.towerCocycle_m_mem_supported C.step,
    RowFiniteAugmentedModule.wellFounded_mem_support_towerCocycle C.step,
    C.exists_towerCocycle_eq⟩

end TauCeti
