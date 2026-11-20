/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.QuasiIso

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
  set k₀ := f.support.sup fun y ↦ r y + 1
  have hf₀ : f ∈ supported A A {y | r y < max k₀ k₁} := fun y hy ↦
    lt_max_of_lt_left (Nat.lt_of_succ_le (Finset.le_sup (f := fun y ↦ r y + 1) hy))
  exact hK (max k₀ k₁) f w hf₀ hf hfw (hF (le_max_right k₀ k₁) hk₁)

/-! ### The stages of the construction -/

variable [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] {h : IsDGAlgebra 𝒜 d}

variable (𝒜 d ℳ dM) in
/-- A stage of the construction: a row-finite twisted module with a degree-preserving chain map to
`M`, given on the generators and landing in `N`, whose relative cycles with target in `N` are
relative boundaries with target in `N`, so that it is a quasi-isomorphism onto `N`. -/
private structure FiltrationStage (N : Submodule A M) where
  /-- The generators. -/
  P : Type uQ
  /-- The indices of the generators. -/
  ind : P → ℤ
  /-- The rows of the generators. -/
  m : RowFiniteTwistingCocycle 𝒜 d P ind
  /-- The images of the generators. -/
  g : P → M
  /-- The images of the generators lie in `N`. -/
  g_mem : ∀ x, g x ∈ N
  /-- The images of the generators have the degrees of the generators. -/
  g_deg : ∀ x, g x ∈ ℳ (-ind x)
  /-- The map given by the images of the generators is a chain map. -/
  g_m : ∀ x, linearCombination A g (m.m x) = dM (g x)
  /-- Relative cycles with target in `N` are relative boundaries with target in `N`. -/
  rel : ∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u = 0 →
    linearCombination A g u = dM w → w ∈ N → ∃ (u' : P →₀ A) (w' : M), w' ∈ N ∧
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u' = u ∧
        linearCombination A g u' + dM w' = w

namespace FiltrationStage

variable {N₀ : Submodule A M}

/-- The data of one cell attachment to a stage: the attaching cycles `a` of the new generators,
the corrected images `c` of the new generators, and the properties produced by
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`. -/
private structure AttachStep (S : FiltrationStage.{uR, uA, uM, uQ} 𝒜 d ℳ dM N₀) (N₁ : Submodule A M)
    {Q : Type uQ} (indQ : Q → ℤ) (c₀ : Q → M) where
  /-- The attaching cycles. -/
  a : Q → S.P →₀ A
  /-- The attaching cycles have the degrees of differentials of the new generators. -/
  ha : ∀ q y, a q y ∈ 𝒜 (S.ind y - indQ q + 1)
  /-- The attaching vectors are cycles. -/
  hca : ∀ q, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) S.m.m (a q) = 0
  /-- The corrected images of the new generators. -/
  c : Q → M
  /-- The corrected images have the degrees of the new generators. -/
  c_deg : ∀ q, c q ∈ ℳ (-indQ q)
  /-- The corrected images lie in `N₁`. -/
  c_mem : ∀ q, c q ∈ N₁
  /-- The corrected images agree with the representatives modulo `N₀`. -/
  c_sub : ∀ q, c q - c₀ q ∈ N₀
  /-- The corrected image of a new generator bounds the image of its attaching cycle. -/
  g_a : ∀ q, linearCombination A S.g (a q) = dM (c q)
  /-- The extended map has relative cycles, with target in `N₁`, that are relative boundaries. -/
  rel : ∀ (f : S.P ⊕ Q →₀ A) (w : M),
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (S.m.attach a ha hca).m f = 0 →
    linearCombination A (Sum.elim S.g c) f = dM w → w ∈ N₁ → ∃ (f' : S.P ⊕ Q →₀ A) (w' : M),
      w' ∈ N₁ ∧ rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (S.m.attach a ha hca).m f' = f ∧
        linearCombination A (Sum.elim S.g c) f' + dM w' = w

/-- The cells can be attached to a stage, by the single attachment step. -/
private theorem nonempty_attachStep (hM : IsDGLeftModule h ℳ dM)
    (S : FiltrationStage.{uR, uA, uM, uQ} 𝒜 d ℳ dM N₀) {N₁ : Submodule A M}
    (hN₀ : N₀.IsHomogeneous ℳ)
    (hN : N₀ ≤ N₁) {Q : Type uQ} {indQ : Q → ℤ} {c₀ : Q → M} (hc₀ : ∀ q, c₀ q ∈ ℳ (-indQ q))
    (hc₀N : ∀ q, c₀ q ∈ N₁) (hdc₀ : ∀ q, dM (c₀ q) ∈ N₀)
    (hQ : ∀ (y : Q →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ N₁ →
      linearCombination A c₀ y - dM w ∈ N₀ → ∃ (y' : Q →₀ A) (w' : M), w' ∈ N₁ ∧
        mapRange.linearMap d y' = y ∧ linearCombination A c₀ y' + dM w' - w ∈ N₀) :
    Nonempty (S.AttachStep N₁ indQ c₀) := by
  obtain ⟨a, ha, hca, c, hcdeg, hcN, hcc₀, hca', hrel⟩ :=
    S.m.exists_attach_of_forall_exists hM hN₀ hN S.g_mem S.g_deg S.g_m S.rel hc₀ hc₀N hdc₀ hQ
  exact ⟨⟨a, ha, hca, c, hcdeg, hcN, hcc₀, hca', hrel⟩⟩

/-- The stage obtained by attaching the cells. -/
private noncomputable def AttachStep.toStage {S : FiltrationStage.{uR, uA, uM, uQ} 𝒜 d ℳ dM N₀}
    {N₁ : Submodule A M} {Q : Type uQ} {indQ : Q → ℤ} {c₀ : Q → M}
    (T : S.AttachStep N₁ indQ c₀) (hN : N₀ ≤ N₁) :
    FiltrationStage.{uR, uA, uM, uQ} 𝒜 d ℳ dM N₁ where
  P := S.P ⊕ Q
  ind := Sum.elim S.ind indQ
  m := S.m.attach T.a T.ha T.hca
  g := Sum.elim S.g T.c
  g_mem := by
    rintro (x | q)
    · exact hN (S.g_mem x)
    · exact T.c_mem q
  g_deg := by
    rintro (x | q)
    · exact S.g_deg x
    · exact T.c_deg q
  g_m := by
    rintro (x | q)
    · simpa [linearCombination_mapDomain] using S.g_m x
    · simpa [linearCombination_mapDomain] using T.g_a q
  rel := T.rel

variable (𝒜 d ℳ dM) in
/-- The stage with no generators, a quasi-isomorphism onto an acyclic submodule. -/
private def zero (hN₀ : ∀ w ∈ N₀, dM w = 0 → ∃ w' ∈ N₀, dM w' = w) :
    FiltrationStage.{uR, uA, uM, uQ} 𝒜 d ℳ dM N₀ where
  P := PEmpty
  ind := PEmpty.elim
  m := 0
  g := PEmpty.elim
  g_mem := nofun
  g_deg := nofun
  g_m := nofun
  rel u w _ huw hw := by
    obtain ⟨w', hw', rfl⟩ := hN₀ w hw (by rw [← huw, Subsingleton.elim u 0, map_zero])
    exact ⟨0, w', hw', Subsingleton.elim _ _, by simp⟩

end FiltrationStage

/-- The input of the construction: an increasing sequence of homogeneous submodules `F k`, with
`F 0` acyclic, and for each `k` cells `Q k` with representatives `c₀ k q` of relative cycles of
`F (k + 1)` modulo `F k`, through which the free module on `Q k` is quasi-isomorphic to
`F (k + 1)` modulo `F k`. -/
private structure FilteredCells (Q : ℕ → Type uQ) where
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

/-- The stages of the construction, each obtained from the previous one by attaching the next
cells. -/
private noncomputable def stage (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) :
    (k : ℕ) → FiltrationStage.{uR, uA, uM, uQ} 𝒜 d ℳ dM (C.F k)
  | 0 => .zero 𝒜 d ℳ dM C.acyclic
  | k + 1 => (Classical.choice ((stage hM C k).nonempty_attachStep hM (C.isHomogeneous k)
      (C.mono k.le_succ) (C.c₀_deg k) (C.c₀_mem k) (C.dM_c₀_mem k) (C.rel k))).toStage
        (C.mono k.le_succ)

/-- The attachment of the cells of stage `k`. -/
private noncomputable def step (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (k : ℕ) :
    (C.stage hM k).AttachStep (C.F (k + 1)) (C.indQ k) (C.c₀ k) :=
  Classical.choice ((C.stage hM k).nonempty_attachStep hM (C.isHomogeneous k) (C.mono k.le_succ)
    (C.c₀_deg k) (C.c₀_mem k) (C.dM_c₀_mem k) (C.rel k))

private theorem stage_succ (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (k : ℕ) :
    C.stage hM (k + 1) = (C.step hM k).toStage (C.mono k.le_succ) :=
  (rfl)

private theorem stage_succ_m_inl (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (k : ℕ)
    (x : (C.stage hM k).P) :
    (C.stage hM (k + 1)).m.m (.inl x) = mapDomain Sum.inl ((C.stage hM k).m.m x) :=
  RowFiniteTwistingCocycle.attach_m_inl _ _ _ x

private theorem stage_succ_m_inr (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (k : ℕ) (q : Q k) :
    (C.stage hM (k + 1)).m.m (.inr q) = mapDomain Sum.inl ((C.step hM k).a q) :=
  RowFiniteTwistingCocycle.attach_m_inr _ _ _ q

/-- The generators of a stage, among all the cells. -/
private def stageEmb (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) : (k : ℕ) → (C.stage hM k).P → Σ j, Q j
  | 0 => PEmpty.elim
  | k + 1 => Sum.elim (stageEmb hM C k) fun q ↦ ⟨k, q⟩

/-- The generators of stage `k` are the cells of stages `< k`. -/
private theorem fst_stageEmb_lt (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) :
    ∀ (k : ℕ) (x : (C.stage hM k).P), (C.stageEmb hM k x).1 < k
  | 0, x => x.elim
  | k + 1, .inl x => (fst_stageEmb_lt hM C k x).trans (Nat.lt_succ_self k)
  | _ + 1, .inr _ => Nat.lt_succ_self _

private theorem stageEmb_injective (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) :
    ∀ k : ℕ, Function.Injective (C.stageEmb hM k)
  | 0 => fun x ↦ x.elim
  | k + 1 => by
    rintro (x | q) (y | q') hxy
    · exact congrArg Sum.inl (stageEmb_injective hM C k hxy)
    · exact absurd (congrArg Sigma.fst hxy) (C.fst_stageEmb_lt hM k x).ne
    · exact absurd (congrArg Sigma.fst hxy) (C.fst_stageEmb_lt hM k y).ne'
    · cases hxy
      rfl

private theorem range_stageEmb (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) :
    ∀ k : ℕ, Set.range (C.stageEmb hM k) = {y | y.1 < k}
  | 0 => by
    refine Set.Subset.antisymm ?_ fun y hy ↦ absurd hy (Nat.not_lt_zero _)
    rintro _ ⟨x, -⟩
    exact PEmpty.elim x
  | k + 1 => by
    ext ⟨j, q⟩
    refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun hj ↦ ?_⟩
    · have hx' := C.fst_stageEmb_lt hM (k + 1) x
      rwa [hx] at hx'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨x, hx⟩ : (⟨j, q⟩ : Σ j, Q j) ∈ Set.range (C.stageEmb hM k) := by
          rw [range_stageEmb hM C k]
          exact hj
        exact ⟨.inl x, hx⟩
      · exact ⟨.inr q, rfl⟩

private theorem indQ_stageEmb (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) : ∀ (k : ℕ) (x : (C.stage hM k).P),
    C.indQ (C.stageEmb hM k x).1 (C.stageEmb hM k x).2 = (C.stage hM k).ind x
  | 0, x => x.elim
  | k + 1, .inl x => indQ_stageEmb hM C k x
  | _ + 1, .inr _ => rfl

/-- The rows of the cells: the cell `⟨k, q⟩` has row its attaching cycle, relabelled. -/
private noncomputable def row (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (x : Σ j, Q j) : (Σ j, Q j) →₀ A :=
  mapDomain (C.stageEmb hM x.1) ((C.step hM x.1).a x.2)

/-- The images of the cells: the cell `⟨k, q⟩` is sent to the corrected representative. -/
private noncomputable def aug (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (x : Σ j, Q j) : M :=
  (C.step hM x.1).c x.2

private theorem row_stageEmb (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) : ∀ (k : ℕ) (x : (C.stage hM k).P),
    C.row hM (C.stageEmb hM k x) = mapDomain (C.stageEmb hM k) ((C.stage hM k).m.m x)
  | 0, x => x.elim
  -- `stageEmb (k + 1) ∘ Sum.inl` is `stageEmb k` by definition, and the rows of stage `k + 1` are
  -- those of stage `k` and the attaching cycles, both relabelled along `Sum.inl`.
  | k + 1, .inl x => by
    refine (row_stageEmb hM C k x).trans ?_
    rw [stage_succ_m_inl]
    exact mapDomain_comp (v := (C.stage hM k).m.m x) (f := Sum.inl) (g := C.stageEmb hM (k + 1))
  | k + 1, .inr q => by
    rw [stage_succ_m_inr]
    exact mapDomain_comp (v := (C.step hM k).a q) (f := Sum.inl) (g := C.stageEmb hM (k + 1))

private theorem aug_stageEmb (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) : ∀ (k : ℕ) (x : (C.stage hM k).P),
    C.aug hM (C.stageEmb hM k x) = (C.stage hM k).g x
  | 0, x => x.elim
  | k + 1, .inl x => aug_stageEmb hM C k x
  | _ + 1, .inr _ => rfl

private theorem rowFiniteTwistedDifferential_mapDomain_stageEmb (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (k : ℕ)
    (f : (C.stage hM k).P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (C.row hM) (mapDomain (C.stageEmb hM k) f) =
      mapDomain (C.stageEmb hM k)
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (C.stage hM k).m.m f) :=
  rowFiniteTwistedDifferential_mapDomain _ _ (C.row_stageEmb hM k) f

private theorem linearCombination_aug_mapDomain (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (k : ℕ)
    (f : (C.stage hM k).P →₀ A) :
    linearCombination A (C.aug hM) (mapDomain (C.stageEmb hM k) f) =
      linearCombination A (C.stage hM k).g f := by
  rw [linearCombination_mapDomain, Function.comp_def]
  simp only [aug_stageEmb]

private theorem row_mem_graded (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (x y : Σ j, Q j) :
    C.row hM x y ∈ 𝒜 (C.indQ y.1 y.2 - C.indQ x.1 x.2 + 1) := by
  have hrow : (C.step hM x.1).a x.2 ∈
      rowFiniteTotalGrading 𝒜 (C.stage hM x.1).ind (1 - C.indQ x.1 x.2) :=
    (mem_rowFiniteTotalGrading_iff 𝒜 _).2 fun y ↦ by
      convert (C.step hM x.1).ha x.2 y using 2
      ring
  have h := (mem_rowFiniteTotalGrading_iff 𝒜 _).1
    ((mapDomain_mem_rowFiniteTotalGrading_iff 𝒜 _ (ind' := fun y : Σ j, Q j ↦ C.indQ y.1 y.2)
      (C.stageEmb_injective hM x.1) (C.indQ_stageEmb hM x.1)).2 hrow) y
  rw [row]
  convert h using 2
  ring

/-- The cell-filtered semi-free model: the twisting cocycle on all the cells. -/
private noncomputable def model (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) :
    RowFiniteTwistingCocycle 𝒜 d (Σ j, Q j) fun x ↦ C.indQ x.1 x.2 where
  m := C.row hM
  mem_graded := C.row_mem_graded hM
  twisting x := by
    refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
      (C.row_mem_graded hM x)).2 ?_
    rw [row, rowFiniteTwistedDifferential_mapDomain_stageEmb, (C.step hM x.1).hca x.2,
      mapDomain_zero]

private theorem model_m (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) : (C.model hM).m = C.row hM :=
  (rfl)

/-- The vectors supported on the cells of stages `< k` are those of stage `k`. -/
private theorem exists_mapDomain_stageEmb_eq (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) {k : ℕ} {f : (Σ j, Q j) →₀ A}
    (hf : f ∈ supported A A {y | y.1 < k}) :
    ∃ f' : (C.stage hM k).P →₀ A, mapDomain (C.stageEmb hM k) f' = f := by
  rw [mem_supported', ← C.range_stageEmb hM k] at hf
  exact (mem_range_mapDomain_iff _ (C.stageEmb_injective hM k) f).2 hf

private theorem mapDomain_stageEmb_mem_supported (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (k : ℕ)
    (f : (C.stage hM k).P →₀ A) :
    mapDomain (C.stageEmb hM k) f ∈ supported A A {y | y.1 < k} := by
  classical
  intro y hy
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hy)
  exact C.fst_stageEmb_lt hM k x

/-- Stage `k` of the model is a quasi-isomorphism onto `F k`. -/
private theorem exists_model_eq (hM : IsDGLeftModule h ℳ dM)
    (C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q) (k : ℕ)
    (f : (Σ j, Q j) →₀ A) (w : M)
    (hf : f ∈ supported A A {y | y.1 < k})
    (hDf : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (C.model hM).m f = 0)
    (hfw : linearCombination A (C.aug hM) f = dM w) (hw : w ∈ C.F k) :
    ∃ (f' : (Σ j, Q j) →₀ A) (w' : M), f' ∈ supported A A {y | y.1 < k} ∧ w' ∈ C.F k ∧
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (C.model hM).m f' = f ∧
        linearCombination A (C.aug hM) f' + dM w' = w := by
  obtain ⟨f₀, rfl⟩ := C.exists_mapDomain_stageEmb_eq hM hf
  have hDf₀ : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (C.stage hM k).m.m f₀ = 0 := by
    apply mapDomain_injective (C.stageEmb_injective hM k)
    rw [← rowFiniteTwistedDifferential_mapDomain_stageEmb, mapDomain_zero]
    exact hDf
  rw [linearCombination_aug_mapDomain] at hfw
  obtain ⟨u', w', hw', hu', huw⟩ := (C.stage hM k).rel f₀ w hDf₀ hfw hw
  refine ⟨mapDomain (C.stageEmb hM k) u', w', C.mapDomain_stageEmb_mem_supported hM k u', hw', ?_,
    ?_⟩
  · exact (C.rowFiniteTwistedDifferential_mapDomain_stageEmb hM k u').trans (by rw [hu'])
  · rwa [linearCombination_aug_mapDomain]

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
  let C : FilteredCells (ℳ := ℳ) (dM := dM) (d := d) Q :=
    ⟨F, hF, hFhom, hF₀, indQ, c₀, hc₀, hc₀F, hdc₀, hQ⟩
  have hrow (x : Σ k, Q k) : (C.model hM).m x ∈ supported A A {y | y.1 < x.1} :=
    C.mapDomain_stageEmb_mem_supported hM x.1 _
  refine ⟨C.model hM, C.aug hM, fun x ↦ (C.step hM x.1).c_deg x.2,
    fun x ↦ (C.step hM x.1).c_mem x.2, fun x ↦ (C.step hM x.1).c_sub x.2, fun x ↦ ?_, hrow,
    Subrelation.wf (r := InvImage (· < ·) Sigma.fst) (fun {y x} hy ↦ hrow x hy)
      (InvImage.wf _ wellFounded_lt), C.exists_model_eq hM⟩
  rw [FilteredCells.model_m, FilteredCells.row, FilteredCells.linearCombination_aug_mapDomain,
    FilteredCells.aug]
  exact (C.step hM x.1).g_a x.2

end TauCeti
