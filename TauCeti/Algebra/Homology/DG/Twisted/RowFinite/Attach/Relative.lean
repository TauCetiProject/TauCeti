/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.QuasiIso
import TauCeti.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.LinearAlgebra.Finsupp.Supported

/-!
# Semi-free models along a filtration, relative to a base model

Let `M` be a differential graded left module over a DG algebra `A`, filtered by an increasing
sequence of homogeneous `A`-submodules `N 0 ≤ N 1 ≤ ⋯`, and let `g : K_{m₀} → M` be a base model
of `N 0`: a map from the free module of a twisting cocycle `m₀` on base generators `P`, landing in
`N 0`, whose relative cycles with target in `N 0` are relative boundaries. Let `G` be a graded set
of cells with a stage `st : G → ℕ`, and prescribed elements `c₀ x ∈ N (n + 1)` with
`d (c₀ x) ∈ N n` for the cells `x` of stage `n`. Suppose that, for the free module on the cells of
stage `n` with its coefficient differential, every relative cycle of `c₀` with target in
`N (n + 1)` modulo `N n` is a relative boundary there, the elementwise hypothesis of
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`; when the `N n` are stable
under the differential, this says that `c₀` is a quasi-isomorphism onto `N (n + 1)` modulo `N n`.
This is the situation of the chains on the based path space of a relative CW complex, filtered by
the preimages of the skeleta, with one generator for each cell outside the base.

This file attaches the cells one stage at a time, keeping the base rows `m₀`, and passes to the
union. The result (`TauCeti.exists_rowFiniteTwistingCocycle_sum_of_forall_exists`) is a row-finite
twisting cocycle `m` on `P ⊕ G` extending `m₀`, whose rows of cells strictly lower the stage of
the cells, together with images `c x ≡ c₀ x` modulo `N (st x)`, such that `Sum.elim g c : K_m → M`
commutes with the differentials and:

* for every `n`, every relative cycle of its restriction to the base and the cells of stage `< n`
  with target in `N n` is a relative boundary with target in `N n`, the elementwise form used by
  `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`;
* every relative cycle of `Sum.elim g c` with target in the union `⨆ n, N n` is a relative
  boundary with target in the union.

The absolute case, over the empty base with `N 0` acyclic, is
`TauCeti.exists_semifreeModel_of_filtration` (`RowFinite/Attach/Filtration.lean`), derived from
this one. In general the base generators keep their prescribed rows `m₀`, which need not lower
any stage.

These elementwise statements do not require the `N n` to be stable under the differential. When
they are, so that the `N n` and their union are subcomplexes, a relative cycle being a relative
boundary is the acyclicity of the mapping cone, and the two statements say that the restriction of
the model is a quasi-isomorphism onto each `N n`, and that the model is one onto `⨆ n, N n`,
hence onto `M` when the filtration is exhaustive. The same reading applies to the hypotheses: the
base model is a quasi-isomorphism onto `N 0`, and the quasi-isomorphisms of the stages are
elementwise. No finiteness is assumed on the cells of a stage: the union is a direct sum of
finite-support vectors, and a relative cycle of the union already lives at a finite stage of both
the cells and the filtration.

The inductive step is `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, applied
to the base together with the cells of stages `< n`, restricted to these generators by
`TauCeti.RowFiniteTwistingCocycle.ofComapDomain`, and the new cells of stage `n`. The successive
models are chosen to agree on the earlier cells, so they assemble to a single model on `P ⊕ G`.

## Main results

* `TauCeti.exists_rowFiniteTwistingCocycle_sum_of_forall_exists`: the semi-free extension of a
  base model built along the filtration, whose relative cycles with target in each stage, or in
  the union, are relative boundaries there; when the `N n` are stable under the differential,
  this makes it a quasi-isomorphism onto each stage and onto the union.
* `TauCeti.exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported`: relative boundaries
  with target in the stages of a filtration, from the generators of rank `< k`, give relative
  boundaries with target in the union.

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

universe uR uA uM uG uP

variable {R : Type uR} {A : Type uA} {G : Type uG} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : G → ℤ} {indP : P → ℤ}
  {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M} {h : IsDGAlgebra 𝒜 d}

/-- The rows on `P ⊕ G` of the base rows `m₀`, relabelled along `Sum.inl`, and of the rows `m` of
the cells. -/
private noncomputable def fullRows (m₀ : RowFiniteTwistingCocycle 𝒜 d P indP)
    (m : G → P ⊕ G →₀ A) : P ⊕ G → P ⊕ G →₀ A :=
  Sum.elim (fun p ↦ mapDomain Sum.inl (m₀.m p)) m

/-- The base generators together with the cells of stage `< n`. -/
private def below (P : Type uP) (st : G → ℕ) (n : ℕ) : Set (P ⊕ G) :=
  {z | Sum.elim (fun _ ↦ True) (fun x ↦ st x < n) z}

section Below

variable {st : G → ℕ} {n : ℕ}

/-- Every base generator lies below every stage. -/
private theorem inl_mem_below (p : P) : (Sum.inl p : P ⊕ G) ∈ below P st n :=
  trivial

/-- A cell lies below stage `n` when its stage is `< n`. -/
private theorem inr_mem_below {x : G} : (Sum.inr x : P ⊕ G) ∈ below P st n ↔ st x < n :=
  Iff.rfl

/-- The generators below a stage increase with the stage. -/
private theorem below_mono {k : ℕ} (hnk : n ≤ k) : below P st n ⊆ below P st k := by
  rintro (p | x) hx
  exacts [inl_mem_below p, inr_mem_below.2 (lt_of_lt_of_le (inr_mem_below.1 hx) hnk)]

/-- A vector is supported below stage `n` when every cell in its support has stage `< n`. -/
private theorem subset_below_iff {f : P ⊕ G →₀ A} :
    ↑f.support ⊆ below P st n ↔ ∀ x, Sum.inr x ∈ f.support → st x < n :=
  ⟨fun hf x hx ↦ inr_mem_below.1 (hf hx), fun hf z hz ↦ by
    rcases z with p | x
    exacts [inl_mem_below p, inr_mem_below.2 (hf x hz)]⟩

end Below

section Base

variable (m₀ : RowFiniteTwistingCocycle 𝒜 d P indP) (m : G → P ⊕ G →₀ A)

omit [GradedAlgebra 𝒜] in
/-- The base rows keep their degrees on `P ⊕ G`. -/
private theorem fullRows_inl_mem_graded (p : P) (z : P ⊕ G) :
    fullRows m₀ m (Sum.inl p) z ∈ 𝒜 (Sum.elim indP ind z - indP p + 1) := by
  rcases z with q | y
  · simp only [fullRows, Sum.elim_inl]
    rw [mapDomain_apply_of_injective Sum.inl_injective]
    exact m₀.mem_graded p q
  · simp only [fullRows, Sum.elim_inl]
    rw [mapDomain_of_notMem_range _ _ (by rintro ⟨q, ⟨⟩⟩)]
    exact zero_mem _

/-- Relabelling along `Sum.inl` intertwines the differential of `m₀` with that of the full
rows. -/
private theorem rowFiniteTwistedDifferential_fullRows_mapDomain_inl (u : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) (mapDomain Sum.inl u) =
      mapDomain Sum.inl (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m₀.m u) :=
  rowFiniteTwistedDifferential_mapDomain Sum.inl _ (fun _ ↦ rfl) u

/-- The base rows are cycles of the full rows. -/
private theorem rowFiniteTwistedDifferential_fullRows_inl (p : P) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) (fullRows m₀ m (Sum.inl p)) =
      0 := by
  rw [fullRows, Sum.elim_inl, ← fullRows, rowFiniteTwistedDifferential_fullRows_mapDomain_inl,
    m₀.differential_row p, mapDomain_zero]

omit [GradedAlgebra 𝒜] [IsScalarTower R A M] in
/-- The images `Sum.elim g c` commute with the differentials on the base generators. -/
private theorem linearCombination_fullRows_inl {g : P → M}
    (hg : ∀ p, linearCombination A g (m₀.m p) = dM (g p)) (c : G → M) (p : P) :
    linearCombination A (Sum.elim g c) (fullRows m₀ m (Sum.inl p)) = dM (g p) := by
  rw [fullRows, Sum.elim_inl, linearCombination_mapDomain, Sum.elim_comp_inl, hg p]

end Base

omit [IsScalarTower R A M] in
/-- **Relative boundaries below the stages of a filtration assemble.** Let the generators carry a
rank `r` in `ℕ`, and let `F` be an increasing sequence of submodules of `M`. If for every `k` the
map `g`, restricted to the generators of rank `< k`, has relative cycles with target in `F k` that
are relative boundaries with target in `F k`, then every relative cycle of `g` with target in
`⨆ k, F k` is a relative boundary with target in `⨆ k, F k`. -/
theorem exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported (m : P → P →₀ A)
    {g : P → M} (r : P → ℕ) {F : ℕ → Submodule A M} (hF : Monotone F)
    (hK : ∀ (k : ℕ) (f : P →₀ A) (w : M), f ∈ supported A A {y | r y < k} →
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f = 0 →
      linearCombination A g f = dM w → w ∈ F k → ∃ (f' : P →₀ A) (w' : M), w' ∈ F k ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f' = f ∧
          linearCombination A g f' + dM w' = w)
    {f : P →₀ A} {w : M} (hf : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f = 0)
    (hfw : linearCombination A g f = dM w) (hw : w ∈ ⨆ k, F k) :
    ∃ (f' : P →₀ A) (w' : M), w' ∈ ⨆ k, F k ∧
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f' = f ∧
        linearCombination A g f' + dM w' = w := by
  obtain ⟨k₁, hk₁⟩ := (Submodule.mem_iSup_of_directed F hF.directed_le).1 hw
  -- `f` involves finitely many generators, so it lies below some rank.
  obtain ⟨k₀, hk₀⟩ := exists_mem_supported_lt (R := A) r f
  obtain ⟨f', w', hw', hf', hfw'⟩ := hK (max k₀ k₁) f w
    (supported_mono (Set.ofPred_subset_ofPred.2 fun _ ↦ lt_max_of_lt_left) hk₀) hf hfw
    (hF (le_max_right k₀ k₁) hk₁)
  exact ⟨f', w', Submodule.mem_iSup_of_mem _ hw', hf', hfw'⟩

variable (st : G → ℕ) (N : ℕ → Submodule A M) (c₀ : G → M)
  (m₀ : RowFiniteTwistingCocycle 𝒜 d P indP) (g : P → M)

/-- The invariants of a single cell `x` of a semi-free model along the filtration `N`, relative to
the base model `(m₀, g)`: its row `m x`, on `P ⊕ G`, lowers the stage of the cells and has the
degrees and twisting equation of a cocycle, and its image `c x` is congruent to `c₀ x` and commutes
with the differentials. -/
private structure IsCell (m : G → P ⊕ G →₀ A) (c : G → M) (x : G) : Prop where
  lt : ∀ y, Sum.inr y ∈ (m x).support → st y < st x
  mem_graded : ∀ z, m x z ∈ 𝒜 (Sum.elim indP ind z - ind x + 1)
  twisting : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) (m x) = 0
  mem : c x ∈ ℳ (-ind x)
  mem_succ : c x ∈ N (st x + 1)
  sub_mem : c x - c₀ x ∈ N (st x)
  hom : linearCombination A (Sum.elim g c) (m x) = dM (c x)

/-- The first `n` stages of a semi-free model along the filtration `N`, relative to the base
model `(m₀, g)`: rows `m x`, on `P ⊕ G`, and images `c x` of the cells `x` of stage `< n`, each
satisfying the invariants of `IsCell`, with every relative cycle of the restriction to the base
and these cells with target in `N n` a relative boundary with target in `N n`. The values on
cells of stage `≥ n` are irrelevant. -/
private structure IsStage (n : ℕ) (m : G → P ⊕ G →₀ A) (c : G → M) : Prop where
  cell : ∀ x, st x < n → IsCell (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g m c x
  exists_eq : ∀ (f : P ⊕ G →₀ A) (w : M), ↑f.support ⊆ below P st n →
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) f = 0 →
      linearCombination A (Sum.elim g c) f = dM w → w ∈ N n →
        ∃ (f' : P ⊕ G →₀ A) (w' : M), ↑f'.support ⊆ below P st n ∧ w' ∈ N n ∧
          rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) f' = f ∧
            linearCombination A (Sum.elim g c) f' + dM w' = w

variable {st N c₀ m₀ g}

/-- On vectors supported below stage `k`, the full rows only matter on the cells of stage
`< k`. -/
private theorem rowFiniteTwistedDifferential_fullRows_congr {k : ℕ} {m m' : G → P ⊕ G →₀ A}
    (hm : ∀ x, st x < k → m' x = m x) {f : P ⊕ G →₀ A} (hf : ↑f.support ⊆ below P st k) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m') f =
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) f := by
  refine rowFiniteTwistedDifferential_congr fun z hz ↦ ?_
  rcases z with p | x
  exacts [rfl, hm x (inr_mem_below.1 (hf hz))]

/-- On vectors supported below stage `k`, the images only matter on the cells of stage `< k`. -/
private theorem linearCombination_sumElim_congr {k : ℕ} {c c' : G → M}
    (hc : ∀ x, st x < k → c' x = c x) {f : P ⊕ G →₀ A} (hf : ↑f.support ⊆ below P st k) :
    linearCombination A (Sum.elim g c') f = linearCombination A (Sum.elim g c) f := by
  refine linearCombination_congr fun z hz ↦ ?_
  rcases z with p | x
  exacts [rfl, hc x (inr_mem_below.1 (hf hz))]

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- The invariants of a cell of stage `< k` only see the rows and images of the cells of stage
`< k`. -/
private theorem IsCell.congr {k : ℕ} {m m' : G → P ⊕ G →₀ A} {c c' : G → M} {x : G}
    (hcx : IsCell (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g m c x) (hx : st x < k)
    (hm : ∀ y, st y < k → m' y = m y) (hc : ∀ y, st y < k → c' y = c y) :
    IsCell (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g m' c' x := by
  have hsupp : ↑(m x).support ⊆ below P st k :=
    subset_below_iff.2 fun y hy ↦ (hcx.lt y hy).trans hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm x hx]
    exact hcx.lt
  · rw [hm x hx]
    exact hcx.mem_graded
  · rw [hm x hx, rowFiniteTwistedDifferential_fullRows_congr hm hsupp]
    exact hcx.twisting
  · rw [hc x hx]
    exact hcx.mem
  · rw [hc x hx]
    exact hcx.mem_succ
  · rw [hc x hx]
    exact hcx.sub_mem
  · rw [hm x hx, linearCombination_sumElim_congr hc hsupp, hc x hx]
    exact hcx.hom

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- The rows of the cells of stage `< n` only involve the base and the cells of stage `< n`. -/
private theorem IsStage.support_subset {n : ℕ} {m : G → P ⊕ G →₀ A} {c : G → M}
    (hs : IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n m c) {x : G} (hx : st x < n) :
    ↑(m x).support ⊆ below P st n :=
  subset_below_iff.2 fun y hy ↦ ((hs.cell x hx).lt y hy).trans hx

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- The first `n` stages only see the rows and images of the cells of stage `< n`. -/
private theorem IsStage.congr {n : ℕ} {m m' : G → P ⊕ G →₀ A} {c c' : G → M}
    (hs : IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n m c)
    (hm : ∀ x, st x < n → m' x = m x) (hc : ∀ x, st x < n → c' x = c x) :
    IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n m' c' := by
  refine ⟨fun x hx ↦ (hs.cell x hx).congr hx hm hc, fun f w hf hDf hfw hw ↦ ?_⟩
  obtain ⟨f', w', hf', hw', hDf', hfw'⟩ := hs.exists_eq f w hf
    (by rwa [← rowFiniteTwistedDifferential_fullRows_congr hm hf])
    (by rwa [← linearCombination_sumElim_congr hc hf]) hw
  exact ⟨f', w', hf', hw', by rwa [rowFiniteTwistedDifferential_fullRows_congr hm hf'],
    by rwa [linearCombination_sumElim_congr hc hf']⟩

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- No cell has stage `< 0`, so the base model, whose relative cycles with target in `N 0` are
relative boundaries, is the zeroth stage. -/
private theorem isStage_zero
    (hK : ∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m₀.m u = 0 →
      linearCombination A g u = dM w → w ∈ N 0 → ∃ (u' : P →₀ A) (w' : M), w' ∈ N 0 ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m₀.m u' = u ∧
          linearCombination A g u' + dM w' = w) :
    IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g 0 0 0 := by
  refine ⟨fun x hx ↦ absurd hx (Nat.not_lt_zero _), ?_⟩
  -- With no cells, the vectors supported below stage `0` are those of the base.
  have hrange : Set.range (Sum.inl : P → P ⊕ G) = below P st 0 := by
    ext (p | x)
    · exact ⟨fun _ ↦ inl_mem_below p, fun _ ↦ ⟨p, rfl⟩⟩
    · exact ⟨by rintro ⟨p, ⟨⟩⟩, fun hx ↦ absurd (inr_mem_below.1 hx) (Nat.not_lt_zero _)⟩
  rw [← hrange]
  exact (forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain Sum.inl
    Sum.inl_injective (rowFiniteTwistedDifferential_fullRows_mapDomain_inl m₀ 0)
    (fun _ ↦ rfl) (N 0 : Set M)).1 hK

/-- **One more stage of cells.** The first `n` stages of a semi-free model extend to the first
`n + 1`, without changing the rows and images of the cells of stage `< n`, by attaching the cells
of stage `n` (`RowFiniteTwistingCocycle.exists_attach_of_forall_exists`). -/
private theorem IsStage.exists_succ (hM : IsDGLeftModule h ℳ dM) (hN : Monotone N)
    {n : ℕ} (hNn : (N n).IsHomogeneous ℳ) (hgN : ∀ p, g p ∈ N 0)
    (hgdeg : ∀ p, g p ∈ ℳ (-indP p)) (hg : ∀ p, linearCombination A g (m₀.m p) = dM (g p))
    (hc₀ : ∀ x, c₀ x ∈ ℳ (-ind x))
    (hc₀N : ∀ x, c₀ x ∈ N (st x + 1)) (hdc₀ : ∀ x, dM (c₀ x) ∈ N (st x))
    (hQ : ∀ (y : {x // st x = n} →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ N (n + 1) →
      linearCombination A (fun x ↦ c₀ x.val) y - dM w ∈ N n →
        ∃ (y' : {x // st x = n} →₀ A) (w' : M), w' ∈ N (n + 1) ∧
          mapRange.linearMap d y' = y ∧ linearCombination A (fun x ↦ c₀ x.val) y' + dM w' - w ∈ N n)
    {m : G → P ⊕ G →₀ A} {c : G → M}
    (hs : IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n m c) :
    ∃ (m' : G → P ⊕ G →₀ A) (c' : G → M),
      IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g (n + 1) m' c' ∧
        (∀ x, st x < n → m' x = m x) ∧ (∀ x, st x < n → c' x = c x) := by
  classical
  -- Outline: restrict the first `n` stages to a cocycle `mL` on the subtype `L` of the base and
  -- the cells of stage `< n`, attach the cells `Q` of stage `n` to it, and read the attached
  -- cocycle on `L ⊕ Q` back on `P ⊕ G` through the injection `φ : L ⊕ Q → P ⊕ G`, whose image
  -- is the base and the cells of stage `≤ n`.
  let L := ↥(below P st n)
  let Q := {x : G // st x = n}
  have hrow (z : L) : ↑(fullRows m₀ m z.val).support ⊆ Set.range (Subtype.val : L → P ⊕ G) := by
    rw [Subtype.range_coe]
    rcases z with ⟨p | x, hz⟩
    · intro y hy
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hy)
      exact inl_mem_below q
    · exact hs.support_subset (inr_mem_below.1 hz)
  have hgr (z y : L) :
      fullRows m₀ m z.val y.val ∈ 𝒜 (Sum.elim indP ind y.val - Sum.elim indP ind z.val + 1) := by
    rcases z with ⟨p | x, hz⟩
    exacts [fullRows_inl_mem_graded m₀ m p y.val, (hs.cell x (inr_mem_below.1 hz)).mem_graded y.val]
  have htw (z : L) : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m)
      (fullRows m₀ m z.val) = 0 := by
    rcases z with ⟨p | x, hz⟩
    exacts [rowFiniteTwistedDifferential_fullRows_inl m₀ m p,
      (hs.cell x (inr_mem_below.1 hz)).twisting]
  let mL : RowFiniteTwistingCocycle 𝒜 d L (fun z ↦ Sum.elim indP ind z.val) :=
    .ofComapDomain (fullRows m₀ m) Subtype.val Subtype.val_injective hrow hgr htw
  have hmL (z : L) : mapDomain Subtype.val (mL.m z) = fullRows m₀ m z.val :=
    RowFiniteTwistingCocycle.mapDomain_ofComapDomain_m z
  let cL : L → M := fun z ↦ Sum.elim g c z.val
  -- The relative cycles of the restriction with target in `N n` are relative boundaries.
  have hK := (forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain Subtype.val
    Subtype.val_injective (mP := mL.m)
    RowFiniteTwistingCocycle.rowFiniteTwistedDifferential_mapDomain_ofComapDomain
    (fun z : L ↦ rfl) (N n : Set M)).2 (by rw [Subtype.range_coe]; exact hs.exists_eq)
  -- Attach the cells of stage `n`.
  have hgL (z : L) : linearCombination A cL (mL.m z) = dM (cL z) := by
    have : linearCombination A (Sum.elim g c) (fullRows m₀ m z.val) = dM (cL z) := by
      rcases z with ⟨p | x, hz⟩
      exacts [linearCombination_fullRows_inl m₀ m hg c p, (hs.cell x (inr_mem_below.1 hz)).hom]
    rwa [← hmL z, linearCombination_mapDomain] at this
  have hgLN (z : L) : cL z ∈ N n := by
    rcases z with ⟨p | x, hz⟩
    exacts [hN (Nat.zero_le n) (hgN p),
      hN (Nat.succ_le_of_lt (inr_mem_below.1 hz)) (hs.cell x (inr_mem_below.1 hz)).mem_succ]
  have hgLdeg (z : L) : cL z ∈ ℳ (-Sum.elim indP ind z.val) := by
    rcases z with ⟨p | x, hz⟩
    exacts [hgdeg p, (hs.cell x (inr_mem_below.1 hz)).mem]
  obtain ⟨a, ha, hca, cQ, hcQ, hcQN, hcQsub, hak, hext⟩ :=
    mL.exists_attach_of_forall_exists (Q := Q) (indQ := fun x ↦ ind x.val) hM hNn
      (hN n.le_succ) hgLN hgLdeg hgL hK (c₀ := fun x ↦ c₀ x.val) (fun x ↦ hc₀ x.val)
      (fun x ↦ by have := hc₀N x.val; rwa [x.property] at this)
      (fun x ↦ by have := hdc₀ x.val; rwa [x.property] at this) hQ
  -- The new rows and images of the cells: the old ones below stage `n`, the attached ones at
  -- stage `n`.
  let m' : G → P ⊕ G →₀ A := fun x ↦
    if st x < n then m x else if hx' : st x = n then mapDomain Subtype.val (a ⟨x, hx'⟩) else 0
  let c' : G → M := fun x ↦
    if st x < n then c x else if hx' : st x = n then cQ ⟨x, hx'⟩ else 0
  have hm'P (x : G) (hx : st x < n) : m' x = m x := by simp [m', hx]
  have hc'P (x : G) (hx : st x < n) : c' x = c x := by simp [c', hx]
  have hm'Q (x : Q) : m' x.val = mapDomain Subtype.val (a x) := by
    simp [m', x.property]
  have hc'Q (x : Q) : c' x.val = cQ x := by
    simp [c', x.property]
  have hfr (z : L) : fullRows m₀ m' z.val = fullRows m₀ m z.val := by
    rcases z with ⟨p | x, hz⟩
    exacts [rfl, hm'P x (inr_mem_below.1 hz)]
  have hcL (z : L) : Sum.elim g c' z.val = cL z := by
    rcases z with ⟨p | x, hz⟩
    exacts [rfl, hc'P x (inr_mem_below.1 hz)]
  have hDL (f : L →₀ A) : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m')
      (mapDomain Subtype.val f) =
        mapDomain Subtype.val (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mL.m f) :=
    rowFiniteTwistedDifferential_mapDomain Subtype.val _ (fun z ↦ (hfr z).trans (hmL z).symm) f
  -- `φ : L ⊕ Q → P ⊕ G` identifies the attached module with the base and the cells of stage
  -- `≤ n`.
  let φ : L ⊕ Q → P ⊕ G := Sum.elim Subtype.val (Sum.inr ∘ Subtype.val)
  have hφ : Function.Injective φ := Subtype.val_injective.sumElim
    (Sum.inr_injective.comp Subtype.val_injective) fun z y hzy ↦ by
      have hz := z.property
      rw [hzy] at hz
      exact (inr_mem_below.1 hz).ne y.property
  have hDφ (f : L ⊕ Q →₀ A) :
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m') (mapDomain φ f) =
        mapDomain φ (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (mL.attach a ha hca).m f) := by
    refine rowFiniteTwistedDifferential_mapDomain φ _ (fun z ↦ ?_) f
    rcases z with z | x
    · rw [RowFiniteTwistingCocycle.attach_m_inl, ← mapDomain_comp]
      exact (hfr z).trans (hmL z).symm
    · rw [RowFiniteTwistingCocycle.attach_m_inr, ← mapDomain_comp]
      exact hm'Q x
  have hcφ (z : L ⊕ Q) : Sum.elim g c' (φ z) = Sum.elim cL cQ z := by
    rcases z with z | x
    exacts [hcL z, hc'Q x]
  refine ⟨m', c', ⟨fun x hx ↦ ?_, ?_⟩, hm'P, hc'P⟩
  -- The old cells keep their rows and images, the new cells get the attached ones.
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · exact (hs.cell x hx).congr hx hm'P hc'P
    obtain ⟨x, rfl⟩ : ∃ y : Q, y.val = x := ⟨⟨x, hx⟩, rfl⟩
    refine ⟨fun y hy ↦ ?_, fun z ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- The rows of the new cells involve only the base and the old cells.
    · rw [hm'Q] at hy
      obtain ⟨z, -, hzy⟩ := Finset.mem_image.1 (mapDomain_support hy)
      have hz : Sum.inr y ∈ below P st n := hzy ▸ z.property
      rw [x.property]
      exact inr_mem_below.1 hz
    · rw [hm'Q]
      by_cases hz : z ∈ below P st n
      · obtain ⟨p, rfl⟩ : ∃ p : L, p.val = z := ⟨⟨z, hz⟩, rfl⟩
        rw [mapDomain_apply_of_injective Subtype.val_injective]
        exact ha x p
      · rw [mapDomain_of_notMem_range _ _ (by rintro ⟨p, rfl⟩; exact hz p.property)]
        exact zero_mem _
    · rw [hm'Q, hDL, hca, mapDomain_zero]
    · rw [hc'Q]
      exact hcQ x
    · rw [hc'Q, x.property]
      exact hcQN x
    · rw [hc'Q, x.property]
      exact hcQsub x
    -- On the base and the old cells, the new images are the old ones.
    · have hcLfun : Sum.elim g c' ∘ Subtype.val = cL := funext hcL
      rw [hm'Q, linearCombination_mapDomain, hc'Q, hcLfun]
      exact hak x
  -- A relative cycle on the base and the cells of stage `≤ n` is one of the attached module.
  · have hrange : Set.range φ = below P st (n + 1) := by
      ext y
      refine ⟨?_, fun hy ↦ ?_⟩
      · rintro ⟨z | x, rfl⟩
        exacts [below_mono n.le_succ z.property, inr_mem_below.2 (Nat.lt_succ_of_le x.property.le)]
      · rcases y with p | x
        · exact ⟨Sum.inl ⟨Sum.inl p, inl_mem_below p⟩, rfl⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 (inr_mem_below.1 hy) with hx | hx
          exacts [⟨Sum.inl ⟨Sum.inr x, inr_mem_below.2 hx⟩, rfl⟩, ⟨Sum.inr ⟨x, hx⟩, rfl⟩]
    rw [← hrange]
    exact (forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain φ hφ hDφ hcφ
      (N (n + 1) : Set M)).1 hext

/-- **A semi-free model along a filtration, relative to a base model.** Let `M` be a DG left
module, filtered by homogeneous submodules `N 0 ≤ N 1 ≤ ⋯`, and let `g : K_{m₀} → M` be a base
model of `N 0`: it sends each base generator `p` into `N 0` in degree `-indP p`, commutes with the
differentials, and every relative cycle of `g` with target in `N 0` is a relative boundary with
target in `N 0`. Let the cells `G` carry a stage `st : G → ℕ`, with elements `c₀ x ∈ N (n + 1)`
of degree `-ind x` and `d (c₀ x) ∈ N n` for the cells `x` of stage `n`. Suppose that, for the free
module on the cells of stage `n` with its coefficient differential, every relative cycle of `c₀`
with target in `N (n + 1)` modulo `N n` is a relative boundary there, the elementwise hypothesis of
`RowFiniteTwistingCocycle.exists_attach_of_forall_exists`; when the `N n` are stable under `dM`,
this says that `c₀` is a quasi-isomorphism onto `N (n + 1)` modulo `N n`.

Then there are a row-finite twisting cocycle `m` on `P ⊕ G` extending `m₀`, whose rows of cells
strictly lower the stage of the cells, and images `c x ≡ c₀ x` modulo `N (st x)`, of degree
`-ind x` and in `N (st x + 1)`, such that `Sum.elim g c : K_m → M` commutes with the differentials
and:

* for every `n`, every relative cycle of `Sum.elim g c` on the base and the cells of stage `< n`
  with target in `N n` is a relative boundary there, with target in `N n`;
* every relative cycle of `Sum.elim g c` with target in `⨆ n, N n` is a relative boundary with
  target in `⨆ n, N n`.

No stability of the `N n` under `dM` is needed. When the `N n` are subcomplexes, these say that
the restriction of `Sum.elim g c` is a quasi-isomorphism onto `N n` and that `Sum.elim g c` is one
onto the union. -/
theorem exists_rowFiniteTwistingCocycle_sum_of_forall_exists (hM : IsDGLeftModule h ℳ dM)
    (m₀ : RowFiniteTwistingCocycle 𝒜 d P indP) (st : G → ℕ) {N : ℕ → Submodule A M}
    (hN : Monotone N) (hNh : ∀ n, (N n).IsHomogeneous ℳ) {g : P → M} (hgN : ∀ p, g p ∈ N 0)
    (hgdeg : ∀ p, g p ∈ ℳ (-indP p)) (hg : ∀ p, linearCombination A g (m₀.m p) = dM (g p))
    (hK : ∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m₀.m u = 0 →
      linearCombination A g u = dM w → w ∈ N 0 → ∃ (u' : P →₀ A) (w' : M), w' ∈ N 0 ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m₀.m u' = u ∧
          linearCombination A g u' + dM w' = w)
    {c₀ : G → M} (hc₀ : ∀ x, c₀ x ∈ ℳ (-ind x)) (hc₀N : ∀ x, c₀ x ∈ N (st x + 1))
    (hdc₀ : ∀ x, dM (c₀ x) ∈ N (st x))
    (hQ : ∀ n (y : {x // st x = n} →₀ A) (w : M), mapRange.linearMap d y = 0 →
      w ∈ N (n + 1) → linearCombination A (fun x ↦ c₀ x.val) y - dM w ∈ N n →
        ∃ (y' : {x // st x = n} →₀ A) (w' : M), w' ∈ N (n + 1) ∧
          mapRange.linearMap d y' = y ∧
            linearCombination A (fun x ↦ c₀ x.val) y' + dM w' - w ∈ N n) :
    ∃ (m : RowFiniteTwistingCocycle 𝒜 d (P ⊕ G) (Sum.elim indP ind)) (c : G → M),
      (∀ p, m.m (Sum.inl p) = mapDomain Sum.inl (m₀.m p)) ∧
      (∀ x y, Sum.inr y ∈ (m.m (Sum.inr x)).support → st y < st x) ∧
      (∀ x, c x ∈ ℳ (-ind x)) ∧ (∀ x, c x ∈ N (st x + 1)) ∧ (∀ x, c x - c₀ x ∈ N (st x)) ∧
      (∀ x, linearCombination A (Sum.elim g c) (m.m (Sum.inr x)) = dM (c x)) ∧
      (∀ n (f : P ⊕ G →₀ A) (w : M), (∀ x, Sum.inr x ∈ f.support → st x < n) →
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0 →
          linearCombination A (Sum.elim g c) f = dM w → w ∈ N n →
            ∃ (f' : P ⊕ G →₀ A) (w' : M), (∀ x, Sum.inr x ∈ f'.support → st x < n) ∧
              w' ∈ N n ∧ rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
                linearCombination A (Sum.elim g c) f' + dM w' = w) ∧
      ∀ (f : P ⊕ G →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0 →
        linearCombination A (Sum.elim g c) f = dM w → w ∈ ⨆ n, N n →
          ∃ (f' : P ⊕ G →₀ A) (w' : M), w' ∈ ⨆ n, N n ∧
            rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
              linearCombination A (Sum.elim g c) f' + dM w' = w := by
  classical
  -- Extend each stage to the next, and iterate from the base model.
  have hstep (n : ℕ) (q : (G → P ⊕ G →₀ A) × (G → M))
      (hq : IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n q.1 q.2) :
      ∃ q' : (G → P ⊕ G →₀ A) × (G → M),
        IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g (n + 1) q'.1 q'.2 ∧
          (∀ x, st x < n → q'.1 x = q.1 x) ∧ (∀ x, st x < n → q'.2 x = q.2 x) := by
    obtain ⟨m', c', h₁, h₂, h₃⟩ :=
      hq.exists_succ hM hN (hNh n) hgN hgdeg hg hc₀ hc₀N hdc₀ (hQ n)
    exact ⟨(m', c'), h₁, h₂, h₃⟩
  choose! next hnext using hstep
  let seq : ℕ → (G → P ⊕ G →₀ A) × (G → M) := fun n ↦ Nat.rec (0, 0) next n
  have hseq_zero : seq 0 = (0, 0) := rfl
  have hseq_succ (n : ℕ) : seq (n + 1) = next n (seq n) := rfl
  have hseq (n : ℕ) :
      IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n (seq n).1 (seq n).2 := by
    induction n with
    | zero =>
      rw [hseq_zero]
      exact isStage_zero hK
    | succ n ih =>
      rw [hseq_succ]
      exact (hnext n _ ih).1
  -- Later stages keep the rows and images of the earlier cells.
  have hagree (x : G) {n : ℕ} (hx : st x < n) (k : ℕ) (hnk : n ≤ k) :
      (seq k).1 x = (seq n).1 x ∧ (seq k).2 x = (seq n).2 x := by
    induction k, hnk using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ k hnk ih =>
      have hk : st x < k := lt_of_lt_of_le hx hnk
      rw [hseq_succ]
      exact ⟨((hnext k _ (hseq k)).2.1 x hk).trans ih.1, ((hnext k _ (hseq k)).2.2 x hk).trans ih.2⟩
  let mG : G → P ⊕ G →₀ A := fun x ↦ (seq (st x + 1)).1 x
  let c : G → M := fun x ↦ (seq (st x + 1)).2 x
  have hlt (x : G) : st x < st x + 1 := Nat.lt_succ_self _
  have hfin (n : ℕ) :
      IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n mG c :=
    (hseq n).congr (fun x hx ↦ (hagree x (hlt x) n hx).1.symm)
      (fun x hx ↦ (hagree x (hlt x) n hx).2.symm)
  have hcell (x : G) := (hfin (st x + 1)).cell x (hlt x)
  have hgr (z y : P ⊕ G) :
      fullRows m₀ mG z y ∈ 𝒜 (Sum.elim indP ind y - Sum.elim indP ind z + 1) := by
    rcases z with p | x
    exacts [fullRows_inl_mem_graded m₀ mG p y, (hcell x).mem_graded y]
  let m : RowFiniteTwistingCocycle 𝒜 d (P ⊕ G) (Sum.elim indP ind) :=
    { m := fullRows m₀ mG
      mem_graded := hgr
      twisting := fun z ↦ (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
        (hgr z)).2 (by
          rcases z with p | x
          exacts [rowFiniteTwistedDifferential_fullRows_inl m₀ mG p,
            (hcell x).twisting]) }
  refine ⟨m, c, fun p ↦ rfl, fun x ↦ (hcell x).lt, fun x ↦ (hcell x).mem,
    fun x ↦ (hcell x).mem_succ, fun x ↦ (hcell x).sub_mem, fun x ↦ (hcell x).hom,
    fun n f w hf hDf hfw hw ↦ ?_, fun f w hf hfw hw ↦ ?_⟩
  · obtain ⟨f', w', hf', hw', hDf', hfw'⟩ :=
      (hfin n).exists_eq f w (subset_below_iff.2 hf) hDf hfw hw
    exact ⟨f', w', subset_below_iff.1 hf', hw', hDf', hfw'⟩
  -- A relative cycle of the union lives at a finite stage of the cells and the filtration.
  · refine exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported m.m
      (Sum.elim (fun _ ↦ 0) st) hN (fun k f w hf hDf hfw hw ↦ ?_) hf hfw hw
    obtain ⟨f', w', -, hw', hDf', hfw'⟩ := (hfin k).exists_eq f w
      (subset_below_iff.2 fun x hx ↦ (mem_supported A f).1 hf hx) hDf hfw hw
    exact ⟨f', w', hw', hDf', hfw'⟩

end TauCeti
