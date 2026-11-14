/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.QuasiIso
import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# Semi-free models along a filtration, one stage of cells at a time

Let `M` be a differential graded left module over a DG algebra `A`, filtered by an increasing
sequence of homogeneous `A`-submodules `N 0 ≤ N 1 ≤ ⋯`, and let `g : K_{m₀} → M` be a base model
of `N 0`: a map from the free module of a twisting cocycle `m₀` on base generators `P`, landing in
`N 0`, whose relative cycles with target in `N 0` are relative boundaries. Let `G` be a graded set
of cells with a stage `st : G → ℕ`, and suppose that the free module on the cells of stage `n`,
with its coefficient differential, is quasi-isomorphic to `N (n + 1)` modulo `N n` through
prescribed relative cycles `c₀ x ∈ N (n + 1)` with `d (c₀ x) ∈ N n`. This is the situation of the
chains on the based path space of a relative CW complex, filtered by the preimages of the skeleta,
with one generator for each cell outside the base; for an absolute CW complex the base is empty
and `N 0` is acyclic.

This file attaches the cells one stage at a time and passes to the union. The result
(`TauCeti.exists_rowFiniteTwistingCocycle_sum_of_forall_exists`) is a row-finite twisting cocycle
`m` on `P ⊕ G` extending `m₀`, whose rows of cells strictly lower the stage of the cells, together
with images `c x ≡ c₀ x` modulo `N (st x)`, such that `Sum.elim g c : K_m → M` commutes with the
differentials and:

* for every `n`, every relative cycle of its restriction to the base and the cells of stage `< n`
  with target in `N n` is a relative boundary with target in `N n`, the elementwise form used by
  `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`;
* every relative cycle of `Sum.elim g c` with target in the union `⨆ n, N n` is a relative
  boundary with target in the union.

Over the empty base this is `TauCeti.exists_rowFiniteTwistingCocycle_of_forall_exists`, a model
on `G` alone from an acyclic `N 0`.

These elementwise statements do not require the `N n` to be stable under the differential. When
they are, so that the `N n` and their union are subcomplexes, a relative cycle being a relative
boundary is the acyclicity of the mapping cone, and the two statements say that the restriction of
the model is a quasi-isomorphism onto each `N n`, and that the model is one onto `⨆ n, N n`,
hence onto `M` when the filtration is exhaustive. The same reading applies to the hypotheses: the
base model is a quasi-isomorphism onto `N 0` (for the empty base, `N 0` acyclic means that every
cycle of `N 0` bounds in `N 0`), and the quasi-isomorphisms of the stages are elementwise.

Over the empty base the rows strictly lower the stage, so the model is semi-free
(`TauCeti.RowFiniteTwistingCocycle.wellFounded_mem_support_of_lt`), and the lifting properties of
`TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Lifting` apply to `K_m`. No finiteness is assumed
on the cells of a stage: the union is a direct sum of finite-support vectors, and a relative
cycle of the union already lives at a finite stage of both the cells and the filtration.

The inductive step is `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, applied
to the base together with the cells of stages `< n`, and the new cells of stage `n`. The
successive models are chosen to agree on the earlier cells, so they assemble to a single model on
`P ⊕ G`.

## Main results

* `TauCeti.exists_rowFiniteTwistingCocycle_sum_of_forall_exists`: the semi-free extension of a
  base model built along the filtration, a quasi-isomorphism onto each stage and onto the union.
* `TauCeti.exists_rowFiniteTwistingCocycle_of_forall_exists`: its case of the empty base, a
  semi-free model on the cells alone.

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
    (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _ (m₀.mem_graded p)).1
      (m₀.twisting p), mapDomain_zero]

omit [GradedAlgebra 𝒜] [IsScalarTower R A M] in
/-- The images `Sum.elim g c` commute with the differentials on the base generators. -/
private theorem linearCombination_fullRows_inl {g : P → M}
    (hg : ∀ p, linearCombination A g (m₀.m p) = dM (g p)) (c : G → M) (p : P) :
    linearCombination A (Sum.elim g c) (fullRows m₀ m (Sum.inl p)) = dM (g p) := by
  rw [fullRows, Sum.elim_inl, linearCombination_mapDomain, Sum.elim_comp_inl, hg p]

end Base

variable (st : G → ℕ) (N : ℕ → Submodule A M) (c₀ : G → M)
  (m₀ : RowFiniteTwistingCocycle 𝒜 d P indP) (g : P → M)

/-- The first `n` stages of a semi-free model along the filtration `N`, relative to the base
model `(m₀, g)`: rows `m x`, on `P ⊕ G`, and images `c x` of the cells `x` of stage `< n`, with
rows lowering the stage of the cells, the degrees and twisting equation of a cocycle, images
congruent to `c₀` and commuting with the differentials, and every relative cycle of the
restriction to the base and these cells with target in `N n` a relative boundary with target in
`N n`. The values on cells of stage `≥ n` are irrelevant. -/
private structure IsStage (n : ℕ) (m : G → P ⊕ G →₀ A) (c : G → M) : Prop where
  lt : ∀ x, st x < n → ∀ y, Sum.inr y ∈ (m x).support → st y < st x
  mem_graded : ∀ x, st x < n → ∀ z, m x z ∈ 𝒜 (Sum.elim indP ind z - ind x + 1)
  twisting : ∀ x, st x < n →
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) (m x) = 0
  mem : ∀ x, st x < n → c x ∈ ℳ (-ind x)
  mem_succ : ∀ x, st x < n → c x ∈ N (st x + 1)
  sub_mem : ∀ x, st x < n → c x - c₀ x ∈ N (st x)
  hom : ∀ x, st x < n → linearCombination A (Sum.elim g c) (m x) = dM (c x)
  exists_eq : ∀ (f : P ⊕ G →₀ A) (w : M), ↑f.support ⊆ below P st n →
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) f = 0 →
      linearCombination A (Sum.elim g c) f = dM w → w ∈ N n →
        ∃ (f' : P ⊕ G →₀ A) (w' : M), ↑f'.support ⊆ below P st n ∧ w' ∈ N n ∧
          rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) f' = f ∧
            linearCombination A (Sum.elim g c) f' + dM w' = w

variable {st N c₀ m₀ g}

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- The rows of the cells of stage `< n` only involve the base and the cells of stage `< n`. -/
private theorem IsStage.support_subset {n : ℕ} {m : G → P ⊕ G →₀ A} {c : G → M}
    (hs : IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n m c) {x : G} (hx : st x < n) :
    ↑(m x).support ⊆ below P st n :=
  subset_below_iff.2 fun y hy ↦ (hs.lt x hx y hy).trans hx

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- The first `n` stages only see the rows and images of the cells of stage `< n`. -/
private theorem IsStage.congr {n : ℕ} {m m' : G → P ⊕ G →₀ A} {c c' : G → M}
    (hs : IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n m c)
    (hm : ∀ x, st x < n → m' x = m x) (hc : ∀ x, st x < n → c' x = c x) :
    IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n m' c' := by
  have hD {f : P ⊕ G →₀ A} (hf : ↑f.support ⊆ below P st n) :
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m') f =
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m) f := by
    refine rowFiniteTwistedDifferential_congr fun z hz ↦ ?_
    rcases z with p | x
    exacts [rfl, hm x (inr_mem_below.1 (hf hz))]
  have hL {f : P ⊕ G →₀ A} (hf : ↑f.support ⊆ below P st n) :
      linearCombination A (Sum.elim g c') f = linearCombination A (Sum.elim g c) f := by
    refine linearCombination_congr fun z hz ↦ ?_
    rcases z with p | x
    exacts [rfl, hc x (inr_mem_below.1 (hf hz))]
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun f w hf hDf hfw hw ↦ ?_⟩
  · rw [hm x hx]
    exact hs.lt x hx
  · rw [hm x hx]
    exact hs.mem_graded x hx
  · rw [hm x hx, hD (hs.support_subset hx)]
    exact hs.twisting x hx
  · rw [hc x hx]
    exact hs.mem x hx
  · rw [hc x hx]
    exact hs.mem_succ x hx
  · rw [hc x hx]
    exact hs.sub_mem x hx
  · rw [hm x hx, hL (hs.support_subset hx), hc x hx]
    exact hs.hom x hx
  · obtain ⟨f', w', hf', hw', hDf', hfw'⟩ := hs.exists_eq f w hf (by rwa [← hD hf])
      (by rwa [← hL hf]) hw
    exact ⟨f', w', hf', hw', by rwa [hD hf'], by rwa [hL hf']⟩

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- No cell has stage `< 0`, so the base model, whose relative cycles with target in `N 0` are
relative boundaries, is the zeroth stage. -/
private theorem isStage_zero
    (hK : ∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m₀.m u = 0 →
      linearCombination A g u = dM w → w ∈ N 0 → ∃ (u' : P →₀ A) (w' : M), w' ∈ N 0 ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m₀.m u' = u ∧
          linearCombination A g u' + dM w' = w) :
    IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g 0 0 0 := by
  refine ⟨fun x hx ↦ absurd hx (Nat.not_lt_zero _), fun x hx ↦ absurd hx (Nat.not_lt_zero _),
    fun x hx ↦ absurd hx (Nat.not_lt_zero _), fun x hx ↦ absurd hx (Nat.not_lt_zero _),
    fun x hx ↦ absurd hx (Nat.not_lt_zero _), fun x hx ↦ absurd hx (Nat.not_lt_zero _),
    fun x hx ↦ absurd hx (Nat.not_lt_zero _), ?_⟩
  -- With no cells, the vectors supported below stage `0` are those of the base.
  have hrange : Set.range (Sum.inl : P → P ⊕ G) = below P st 0 := by
    ext (p | x)
    · exact ⟨fun _ ↦ inl_mem_below p, fun _ ↦ ⟨p, rfl⟩⟩
    · exact ⟨by rintro ⟨p, ⟨⟩⟩, fun hx ↦ absurd (inr_mem_below.1 hx) (Nat.not_lt_zero _)⟩
  rw [← hrange]
  exact (forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain Sum.inl
    Sum.inl_injective (rowFiniteTwistedDifferential_fullRows_mapDomain_inl m₀ 0)
    (fun _ ↦ rfl) (N 0)).1 hK

/-- **One more stage of cells.** The first `n` stages of a semi-free model extend to the first
`n + 1`, without changing the rows and images of the cells of stage `< n`, by attaching the cells
of stage `n` (`RowFiniteTwistingCocycle.exists_attach_of_forall_exists`). -/
private theorem IsStage.exists_succ (hM : IsDGLeftModule h ℳ dM) (hN : Monotone N)
    {n : ℕ} (hNn : (N n).IsHomogeneous ℳ) (hgN : ∀ p, g p ∈ N 0)
    (hgdeg : ∀ p, g p ∈ ℳ (-indP p)) (hg : ∀ p, linearCombination A g (m₀.m p) = dM (g p))
    (hc₀ : ∀ x, c₀ x ∈ ℳ (-ind x))
    (hc₀N : ∀ x, c₀ x ∈ N (st x + 1)) (hdc₀ : ∀ x, dM (c₀ x) ∈ N (st x))
    (hQ : ∀ (y : {x // st x = n} →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ N (n + 1) →
      linearCombination A (fun x ↦ c₀ x.1) y - dM w ∈ N n →
        ∃ (y' : {x // st x = n} →₀ A) (w' : M), w' ∈ N (n + 1) ∧
          mapRange.linearMap d y' = y ∧ linearCombination A (fun x ↦ c₀ x.1) y' + dM w' - w ∈ N n)
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
  have hrow (z : L) : ↑(fullRows m₀ m z.1).support ⊆ Set.range (Subtype.val : L → P ⊕ G) := by
    rw [Subtype.range_coe]
    rcases z with ⟨p | x, hz⟩
    · intro y hy
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hy)
      exact inl_mem_below q
    · exact hs.support_subset (inr_mem_below.1 hz)
  have hgr (z y : L) :
      fullRows m₀ m z.1 y.1 ∈ 𝒜 (Sum.elim indP ind y.1 - Sum.elim indP ind z.1 + 1) := by
    rcases z with ⟨p | x, hz⟩
    exacts [fullRows_inl_mem_graded m₀ m p y.1, hs.mem_graded x (inr_mem_below.1 hz) y.1]
  have htw (z : L) : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (fullRows m₀ m)
      (fullRows m₀ m z.1) = 0 := by
    rcases z with ⟨p | x, hz⟩
    exacts [rowFiniteTwistedDifferential_fullRows_inl m₀ m p, hs.twisting x (inr_mem_below.1 hz)]
  let mL : RowFiniteTwistingCocycle 𝒜 d L (fun z ↦ Sum.elim indP ind z.1) :=
    .ofComapDomain (fullRows m₀ m) Subtype.val Subtype.val_injective hrow hgr htw
  have hmL (z : L) : mapDomain Subtype.val (mL.m z) = fullRows m₀ m z.1 :=
    RowFiniteTwistingCocycle.mapDomain_ofComapDomain_m z
  let cL : L → M := fun z ↦ Sum.elim g c z.1
  -- The relative cycles of the restriction with target in `N n` are relative boundaries.
  have hK := (forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain Subtype.val
    Subtype.val_injective (mP := mL.m)
    RowFiniteTwistingCocycle.rowFiniteTwistedDifferential_mapDomain_ofComapDomain
    (fun z : L ↦ rfl) (N n)).2 (by rw [Subtype.range_coe]; exact hs.exists_eq)
  -- Attach the cells of stage `n`.
  have hgL (z : L) : linearCombination A cL (mL.m z) = dM (cL z) := by
    have : linearCombination A (Sum.elim g c) (fullRows m₀ m z.1) = dM (cL z) := by
      rcases z with ⟨p | x, hz⟩
      exacts [linearCombination_fullRows_inl m₀ m hg c p, hs.hom x (inr_mem_below.1 hz)]
    rwa [← hmL z, linearCombination_mapDomain] at this
  have hgLN (z : L) : cL z ∈ N n := by
    rcases z with ⟨p | x, hz⟩
    exacts [hN (Nat.zero_le n) (hgN p),
      hN (Nat.succ_le_of_lt (inr_mem_below.1 hz)) (hs.mem_succ x (inr_mem_below.1 hz))]
  have hgLdeg (z : L) : cL z ∈ ℳ (-Sum.elim indP ind z.1) := by
    rcases z with ⟨p | x, hz⟩
    exacts [hgdeg p, hs.mem x (inr_mem_below.1 hz)]
  obtain ⟨a, ha, hca, cQ, hcQ, hcQN, hcQsub, hak, hext⟩ :=
    mL.exists_attach_of_forall_exists (Q := Q) (indQ := fun x ↦ ind x.1) hM hNn
      (hN n.le_succ) hgLN hgLdeg hgL hK (c₀ := fun x ↦ c₀ x.1) (fun x ↦ hc₀ x.1)
      (fun x ↦ by have := hc₀N x.1; rwa [x.2] at this)
      (fun x ↦ by have := hdc₀ x.1; rwa [x.2] at this) hQ
  -- The new rows and images of the cells: the old ones below stage `n`, the attached ones at
  -- stage `n`.
  let m' : G → P ⊕ G →₀ A := fun x ↦
    if st x < n then m x else if hx' : st x = n then mapDomain Subtype.val (a ⟨x, hx'⟩) else 0
  let c' : G → M := fun x ↦
    if st x < n then c x else if hx' : st x = n then cQ ⟨x, hx'⟩ else 0
  have hm'P (x : G) (hx : st x < n) : m' x = m x := by simp [m', hx]
  have hc'P (x : G) (hx : st x < n) : c' x = c x := by simp [c', hx]
  have hm'Q (x : Q) : m' x.1 = mapDomain Subtype.val (a x) := by
    simp [m', x.2]
  have hc'Q (x : Q) : c' x.1 = cQ x := by
    simp [c', x.2]
  have hfr (z : L) : fullRows m₀ m' z.1 = fullRows m₀ m z.1 := by
    rcases z with ⟨p | x, hz⟩
    exacts [rfl, hm'P x (inr_mem_below.1 hz)]
  have hcL (z : L) : Sum.elim g c' z.1 = cL z := by
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
      have hz := z.2
      rw [hzy] at hz
      exact (inr_mem_below.1 hz).ne y.2
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
  refine ⟨m', c', ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x hx ↦ ?_, ?_⟩, hm'P, hc'P⟩
  -- The rows of the new cells involve only the base and the old cells.
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · rw [hm'P x hx]
      exact hs.lt x hx
    · obtain ⟨x, rfl⟩ : ∃ y : Q, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
      rw [hm'Q]
      intro y hy
      obtain ⟨z, -, hzy⟩ := Finset.mem_image.1 (mapDomain_support hy)
      have hz : Sum.inr y ∈ below P st n := hzy ▸ z.2
      rw [x.2]
      exact inr_mem_below.1 hz
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · rw [hm'P x hx]
      exact hs.mem_graded x hx
    · obtain ⟨x, rfl⟩ : ∃ y : Q, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
      rw [hm'Q]
      intro z
      by_cases hz : z ∈ below P st n
      · obtain ⟨p, rfl⟩ : ∃ p : L, p.1 = z := ⟨⟨z, hz⟩, rfl⟩
        rw [mapDomain_apply_of_injective Subtype.val_injective]
        exact ha x p
      · rw [mapDomain_of_notMem_range _ _ (by rintro ⟨p, rfl⟩; exact hz p.2)]
        exact zero_mem _
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · rw [hm'P x hx, rowFiniteTwistedDifferential_congr (m' := fullRows m₀ m)
        fun z hz ↦ hfr ⟨z, hs.support_subset hx hz⟩]
      exact hs.twisting x hx
    · obtain ⟨x, rfl⟩ : ∃ y : Q, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
      rw [hm'Q, hDL, hca, mapDomain_zero]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · rw [hc'P x hx]
      exact hs.mem x hx
    · obtain ⟨x, rfl⟩ : ∃ y : Q, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
      rw [hc'Q]
      exact hcQ x
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · rw [hc'P x hx]
      exact hs.mem_succ x hx
    · obtain ⟨x, rfl⟩ : ∃ y : Q, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
      rw [hc'Q, x.2]
      exact hcQN x
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · rw [hc'P x hx]
      exact hs.sub_mem x hx
    · obtain ⟨x, rfl⟩ : ∃ y : Q, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
      rw [hc'Q, x.2]
      exact hcQsub x
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · rw [hm'P x hx, linearCombination_congr (v' := Sum.elim g c)
        fun z hz ↦ hcL ⟨z, hs.support_subset hx hz⟩, hc'P x hx]
      exact hs.hom x hx
    · obtain ⟨x, rfl⟩ : ∃ y : Q, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
      -- On the base and the old cells, the new images are the old ones.
      have hcLfun : Sum.elim g c' ∘ Subtype.val = cL := funext hcL
      rw [hm'Q, linearCombination_mapDomain, hc'Q, hcLfun]
      exact hak x
  -- A relative cycle on the base and the cells of stage `≤ n` is one of the attached module.
  · have hrange : Set.range φ = below P st (n + 1) := by
      ext y
      refine ⟨?_, fun hy ↦ ?_⟩
      · rintro ⟨z | x, rfl⟩
        exacts [below_mono n.le_succ z.2, inr_mem_below.2 (Nat.lt_succ_of_le x.2.le)]
      · rcases y with p | x
        · exact ⟨Sum.inl ⟨Sum.inl p, inl_mem_below p⟩, rfl⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 (inr_mem_below.1 hy) with hx | hx
          exacts [⟨Sum.inl ⟨Sum.inr x, inr_mem_below.2 hx⟩, rfl⟩, ⟨Sum.inr ⟨x, hx⟩, rfl⟩]
    rw [← hrange]
    exact (forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain φ hφ hDφ hcφ
      (N (n + 1))).1 hext

/-- **A semi-free model along a filtration, relative to a base model.** Let `M` be a DG left
module, filtered by homogeneous submodules `N 0 ≤ N 1 ≤ ⋯`, and let `g : K_{m₀} → M` be a base
model of `N 0`: it sends each base generator `p` into `N 0` in degree `-indP p`, commutes with the
differentials, and every relative cycle of `g` with target in `N 0` is a relative boundary with
target in `N 0`. Let the cells `G` carry a stage `st : G → ℕ`, and suppose that the free module on
the cells of stage `n`, with its coefficient differential, is quasi-isomorphic to `N (n + 1)`
modulo `N n` through elements `c₀ x ∈ N (n + 1)` of degree `-ind x` with `d (c₀ x) ∈ N n`, in the
elementwise form of `RowFiniteTwistingCocycle.exists_attach_of_forall_exists`.

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
      w ∈ N (n + 1) → linearCombination A (fun x ↦ c₀ x.1) y - dM w ∈ N n →
        ∃ (y' : {x // st x = n} →₀ A) (w' : M), w' ∈ N (n + 1) ∧
          mapRange.linearMap d y' = y ∧
            linearCombination A (fun x ↦ c₀ x.1) y' + dM w' - w ∈ N n) :
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
  have hseq (n : ℕ) :
      IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n (seq n).1 (seq n).2 := by
    induction n with
    | zero => exact isStage_zero hK
    | succ n ih => exact (hnext n _ ih).1
  -- Later stages keep the rows and images of the earlier cells.
  have hagree (x : G) (k : ℕ) :
      (seq (st x + k + 1)).1 x = (seq (st x + 1)).1 x ∧
        (seq (st x + k + 1)).2 x = (seq (st x + 1)).2 x := by
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      have hk : st x < st x + k + 1 := by omega
      exact ⟨((hnext _ _ (hseq _)).2.1 x hk).trans ih.1, ((hnext _ _ (hseq _)).2.2 x hk).trans ih.2⟩
  let mG : G → P ⊕ G →₀ A := fun x ↦ (seq (st x + 1)).1 x
  let c : G → M := fun x ↦ (seq (st x + 1)).2 x
  have hfin (n : ℕ) :
      IsStage (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ m₀ g n mG c := by
    refine (hseq n).congr (fun x hx ↦ ?_) (fun x hx ↦ ?_) <;>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hx
    exacts [(hagree x k).1.symm, (hagree x k).2.symm]
  have hlt (x : G) : st x < st x + 1 := Nat.lt_succ_self _
  have hgr (z y : P ⊕ G) :
      fullRows m₀ mG z y ∈ 𝒜 (Sum.elim indP ind y - Sum.elim indP ind z + 1) := by
    rcases z with p | x
    exacts [fullRows_inl_mem_graded m₀ mG p y, (hfin _).mem_graded x (hlt x) y]
  let m : RowFiniteTwistingCocycle 𝒜 d (P ⊕ G) (Sum.elim indP ind) :=
    { m := fullRows m₀ mG
      mem_graded := hgr
      twisting := fun z ↦ (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
        (hgr z)).2 (by
          rcases z with p | x
          exacts [rowFiniteTwistedDifferential_fullRows_inl m₀ mG p,
            (hfin _).twisting x (hlt x)]) }
  refine ⟨m, c, fun p ↦ rfl, fun x ↦ (hfin _).lt x (hlt x), fun x ↦ (hfin _).mem x (hlt x),
    fun x ↦ (hfin _).mem_succ x (hlt x), fun x ↦ (hfin _).sub_mem x (hlt x),
    fun x ↦ (hfin _).hom x (hlt x), fun n f w hf hDf hfw hw ↦ ?_, fun f w hf hfw hw ↦ ?_⟩
  · obtain ⟨f', w', hf', hw', hDf', hfw'⟩ :=
      (hfin n).exists_eq f w (subset_below_iff.2 hf) hDf hfw hw
    exact ⟨f', w', subset_below_iff.1 hf', hw', hDf', hfw'⟩
  -- A relative cycle of the union lives at a finite stage of the cells and the filtration.
  · obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed N hN.directed_le).1 hw
    let n := f.support.sup (Sum.elim (fun _ ↦ 0) st) + 1 + k
    obtain ⟨f', w', -, hw', hDf', hfw'⟩ := (hfin n).exists_eq f w
      (subset_below_iff.2 fun x hx ↦ by
        have := Finset.le_sup (f := Sum.elim (fun _ ↦ 0) st) hx
        simp only [Sum.elim_inr] at this
        omega)
      hf hfw (hN (by omega) hk)
    exact ⟨f', w', Submodule.mem_iSup_of_mem _ hw', hDf', hfw'⟩

/-- **A semi-free model along a filtration, built one stage of cells at a time.** Let `M` be a
DG left module, filtered by homogeneous submodules `N 0 ≤ N 1 ≤ ⋯` with `N 0` acyclic, and let
the generators `G` carry a stage `st : G → ℕ`. Suppose that the free module on the generators of
stage `n`, with its coefficient differential, is quasi-isomorphic to `N (n + 1)` modulo `N n`
through elements `c₀ x ∈ N (n + 1)` of degree `-ind x` with `d (c₀ x) ∈ N n`, in the elementwise
form of `RowFiniteTwistingCocycle.exists_attach_of_forall_exists`.

Then there are a row-finite twisting cocycle `m` on `G`, whose rows strictly lower the stage, and
images `c x ≡ c₀ x` modulo `N (st x)`, of degree `-ind x` and in `N (st x + 1)`, such that
`c : K_m → M` commutes with the differentials and:

* for every `n`, every relative cycle of `c` on the generators of stage `< n` with target in
  `N n` is a relative boundary there, with target in `N n`;
* every relative cycle of `c` with target in `⨆ n, N n` is a relative boundary with target in
  `⨆ n, N n`.

No stability of the `N n` under `dM` is needed. When the `N n` are subcomplexes, these say that
the restriction of `c` is a quasi-isomorphism onto `N n` and that `c` is one onto the union. This
is `exists_rowFiniteTwistingCocycle_sum_of_forall_exists` over the empty base. -/
theorem exists_rowFiniteTwistingCocycle_of_forall_exists (hM : IsDGLeftModule h ℳ dM)
    (st : G → ℕ) {N : ℕ → Submodule A M} (hN : Monotone N) (hNh : ∀ n, (N n).IsHomogeneous ℳ)
    (hN₀ : ∀ w ∈ N 0, dM w = 0 → ∃ w' ∈ N 0, dM w' = w)
    {c₀ : G → M} (hc₀ : ∀ x, c₀ x ∈ ℳ (-ind x)) (hc₀N : ∀ x, c₀ x ∈ N (st x + 1))
    (hdc₀ : ∀ x, dM (c₀ x) ∈ N (st x))
    (hQ : ∀ n (y : {x // st x = n} →₀ A) (w : M), mapRange.linearMap d y = 0 →
      w ∈ N (n + 1) → linearCombination A (fun x ↦ c₀ x.1) y - dM w ∈ N n →
        ∃ (y' : {x // st x = n} →₀ A) (w' : M), w' ∈ N (n + 1) ∧
          mapRange.linearMap d y' = y ∧
            linearCombination A (fun x ↦ c₀ x.1) y' + dM w' - w ∈ N n) :
    ∃ (m : RowFiniteTwistingCocycle 𝒜 d G ind) (c : G → M),
      (∀ x y, y ∈ (m.m x).support → st y < st x) ∧ (∀ x, c x ∈ ℳ (-ind x)) ∧
      (∀ x, c x ∈ N (st x + 1)) ∧ (∀ x, c x - c₀ x ∈ N (st x)) ∧
      (∀ x, linearCombination A c (m.m x) = dM (c x)) ∧
      (∀ n (f : G →₀ A) (w : M), ↑f.support ⊆ {x | st x < n} →
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0 →
          linearCombination A c f = dM w → w ∈ N n →
            ∃ (f' : G →₀ A) (w' : M), ↑f'.support ⊆ {x | st x < n} ∧ w' ∈ N n ∧
              rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
                linearCombination A c f' + dM w' = w) ∧
      ∀ (f : G →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0 →
        linearCombination A c f = dM w → w ∈ ⨆ n, N n →
          ∃ (f' : G →₀ A) (w' : M), w' ∈ ⨆ n, N n ∧
            rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
              linearCombination A c f' + dM w' = w := by
  classical
  -- Over the empty base, the relative cycles with target in `N 0` are the cycles of `N 0`.
  obtain ⟨mX, c, -, hlt, hc, hcN, hcsub, hom, hstage, hunion⟩ :=
    exists_rowFiniteTwistingCocycle_sum_of_forall_exists hM
      (0 : RowFiniteTwistingCocycle 𝒜 d Empty Empty.elim) st hN hNh (g := Empty.elim)
      (fun p ↦ p.elim) (fun p ↦ p.elim) (fun p ↦ p.elim) (fun u w _ huw hw ↦ by
        obtain ⟨w', hw', rfl⟩ := hN₀ w hw (by rw [← huw, Subsingleton.elim u 0, map_zero])
        exact ⟨0, w', hw', Subsingleton.elim _ _, by simp⟩)
      hc₀ hc₀N hdc₀ hQ
  -- Every generator of `Empty ⊕ G` is a cell, so `mX` restricts to a cocycle on `G`.
  have hrange (f : Empty ⊕ G →₀ A) : ↑f.support ⊆ Set.range (Sum.inr : G → Empty ⊕ G) := by
    rintro (e | x) -
    exacts [e.elim, ⟨x, rfl⟩]
  let m : RowFiniteTwistingCocycle 𝒜 d G ind :=
    mX.comap Sum.inr Sum.inr_injective fun x ↦ hrange _
  have hD (f : G →₀ A) := mX.rowFiniteTwistedDifferential_mapDomain_comap
    (he := Sum.inr_injective) (hsupp := fun x ↦ hrange (mX.m (Sum.inr x))) f
  have hL (f : G →₀ A) :
      linearCombination A (Sum.elim Empty.elim c) (mapDomain Sum.inr f) =
        linearCombination A c f := by
    rw [linearCombination_mapDomain, Sum.elim_comp_inr]
  -- Relative cycles of `c` on a set `S` of generators are those of `Sum.elim Empty.elim c`.
  have htransport (S : Set G) (N' : Submodule A M)
      (H : ∀ (F : Empty ⊕ G →₀ A) (w : M), (∀ x, Sum.inr x ∈ F.support → x ∈ S) →
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mX.m F = 0 →
          linearCombination A (Sum.elim Empty.elim c) F = dM w → w ∈ N' →
            ∃ (F' : Empty ⊕ G →₀ A) (w' : M), (∀ x, Sum.inr x ∈ F'.support → x ∈ S) ∧
              w' ∈ N' ∧ rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mX.m F' = F ∧
                linearCombination A (Sum.elim Empty.elim c) F' + dM w' = w)
      (f : G →₀ A) (w : M) (hf : ↑f.support ⊆ S)
      (hDf : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0)
      (hfw : linearCombination A c f = dM w) (hw : w ∈ N') :
      ∃ (f' : G →₀ A) (w' : M), ↑f'.support ⊆ S ∧ w' ∈ N' ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
          linearCombination A c f' + dM w' = w := by
    obtain ⟨F', w', hF', hw', hDF', hFw'⟩ := H (mapDomain Sum.inr f) w (fun x hx ↦ by
        obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 (mapDomain_support hx)
        exact Sum.inr_injective hyx ▸ hf hy)
      (by rw [hD, hDf, mapDomain_zero]) (by rwa [hL]) hw
    have hF'eq : mapDomain Sum.inr (comapDomain Sum.inr F' Sum.inr_injective.injOn) = F' :=
      mapDomain_comapDomain _ Sum.inr_injective _ (hrange F')
    refine ⟨comapDomain Sum.inr F' Sum.inr_injective.injOn, w', fun x hx ↦ hF' x ?_, hw',
      mapDomain_injective (Sum.inr_injective (α := Empty)) ?_, ?_⟩
    · simpa using hx
    · rw [← hD, hF'eq, hDF']
    · rw [← hL, hF'eq, hFw']
  refine ⟨m, c, fun x y hy ↦ hlt x y (by simpa [m] using hy), hc, hcN, hcsub, fun x ↦ ?_,
    fun n ↦ htransport {x | st x < n} (N n) (hstage n), fun f w hDf hfw hw ↦ ?_⟩
  · have := hom x
    rwa [← mX.mapDomain_comap_m (he := Sum.inr_injective)
      (hsupp := fun x ↦ hrange (mX.m (Sum.inr x))) x, hL] at this
  · obtain ⟨f', w', -, hf'⟩ := htransport Set.univ (⨆ n, N n) (fun F w _ hDF hFw hw ↦ by
      obtain ⟨F', w', hF'⟩ := hunion F w hDF hFw hw
      exact ⟨F', w', fun _ _ ↦ trivial, hF'⟩) f w (Set.subset_univ _) hDf hfw hw
    exact ⟨f', w', hf'⟩

end TauCeti
