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
sequence of homogeneous `A`-submodules `N 0 ≤ N 1 ≤ ⋯`, with `N 0` acyclic. Let `G` be a graded
set of generators with a stage `st : G → ℕ`, and suppose that the free module on the generators of
stage `n`, with its coefficient differential, is quasi-isomorphic to `N (n + 1)` modulo `N n`
through prescribed relative cycles `c₀ x ∈ N (n + 1)` with `d (c₀ x) ∈ N n`. This is the situation
of the chains on the based path space of a CW complex, filtered by the preimages of the skeleta,
with one generator for each cell.

This file attaches the generators one stage at a time and passes to the union. The result
(`TauCeti.exists_rowFiniteTwistingCocycle_of_forall_exists`) is a row-finite twisting cocycle `m`
on all of `G`, whose rows strictly lower the stage, together with images `c x ≡ c₀ x` modulo
`N (st x)`, such that `c : K_m → M` commutes with the differentials and:

* for every `n`, its restriction to the generators of stage `< n` is a quasi-isomorphism onto
  `N n`, in the elementwise form used by
  `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`: every relative cycle with
  target in `N n` is a relative boundary with target in `N n`;
* it is a quasi-isomorphism onto the union `⨆ n, N n`, and so onto `M` when the filtration is
  exhaustive.

Since the rows strictly lower the stage, `m` is semi-free
(`TauCeti.RowFiniteTwistingCocycle.wellFounded_mem_support_of_lt`), so the lifting properties of
`TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Lifting` apply to `K_m`. No finiteness is assumed
on the generators of a stage: the union is a direct sum of finite-support vectors, and a relative
cycle of the union already lives at a finite stage of both the generators and the filtration.

The inductive step is `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, applied
to the generators of stages `< n` and the new generators of stage `n`. The successive models are
chosen to agree on the earlier generators, so they assemble to a single model on `G`.

## Main results

* `TauCeti.exists_rowFiniteTwistingCocycle_of_forall_exists`: the semi-free model built along the
  filtration, a quasi-isomorphism onto each stage and onto the union.

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

universe uR uA uM uG

variable {R : Type uR} {A : Type uA} {G : Type uG}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : G → ℤ}
  {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M} {h : IsDGAlgebra 𝒜 d}

variable (st : G → ℕ) (N : ℕ → Submodule A M) (c₀ : G → M)

/-- The first `n` stages of a semi-free model along the filtration `N`: rows `m x` and images
`c x` of the generators of stage `< n`, with rows lowering the stage, the degrees and twisting
equation of a cocycle, images congruent to `c₀` and commuting with the differentials, and the
restriction to these generators a quasi-isomorphism onto `N n`. The values on generators of stage
`≥ n` are irrelevant. -/
private structure IsStage (n : ℕ) (m : G → G →₀ A) (c : G → M) : Prop where
  lt : ∀ x, st x < n → ∀ y ∈ (m x).support, st y < st x
  mem_graded : ∀ x, st x < n → ∀ y, m x y ∈ 𝒜 (ind y - ind x + 1)
  twisting : ∀ x, st x < n → rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (m x) = 0
  mem : ∀ x, st x < n → c x ∈ ℳ (-ind x)
  mem_succ : ∀ x, st x < n → c x ∈ N (st x + 1)
  sub_mem : ∀ x, st x < n → c x - c₀ x ∈ N (st x)
  hom : ∀ x, st x < n → linearCombination A c (m x) = dM (c x)
  exists_eq : ∀ (f : G →₀ A) (w : M), ↑f.support ⊆ {x | st x < n} →
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f = 0 → linearCombination A c f = dM w →
      w ∈ N n → ∃ (f' : G →₀ A) (w' : M), ↑f'.support ⊆ {x | st x < n} ∧ w' ∈ N n ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f' = f ∧
          linearCombination A c f' + dM w' = w

variable {st N c₀}

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- The first `n` stages only see the rows and images of the generators of stage `< n`. -/
private theorem IsStage.congr {n : ℕ} {m m' : G → G →₀ A} {c c' : G → M}
    (hs : IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ n m c)
    (hm : ∀ x, st x < n → m' x = m x) (hc : ∀ x, st x < n → c' x = c x) :
    IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ n m' c' := by
  have hD {f : G →₀ A} (hf : ↑f.support ⊆ {x | st x < n}) :
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m' f =
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f :=
    rowFiniteTwistedDifferential_congr fun x hx ↦ hm x (hf hx)
  have hL {f : G →₀ A} (hf : ↑f.support ⊆ {x | st x < n}) :
      linearCombination A c' f = linearCombination A c f :=
    linearCombination_congr fun x hx ↦ hc x (hf hx)
  -- The rows of generators of stage `< n` only involve generators of stage `< n`.
  have hrow {x : G} (hx : st x < n) : ↑(m x).support ⊆ {x | st x < n} :=
    fun y hy ↦ (hs.lt x hx y hy).trans hx
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun f w hf hDf hfw hw ↦ ?_⟩
  · rw [hm x hx]
    exact hs.lt x hx
  · rw [hm x hx]
    exact hs.mem_graded x hx
  · rw [hm x hx, hD (hrow hx)]
    exact hs.twisting x hx
  · rw [hc x hx]
    exact hs.mem x hx
  · rw [hc x hx]
    exact hs.mem_succ x hx
  · rw [hc x hx]
    exact hs.sub_mem x hx
  · rw [hm x hx, hL (hrow hx), hc x hx]
    exact hs.hom x hx
  · obtain ⟨f', w', hf', hw', hDf', hfw'⟩ := hs.exists_eq f w hf (by rwa [← hD hf])
      (by rwa [← hL hf]) hw
    exact ⟨f', w', hf', hw', by rwa [hD hf'], by rwa [hL hf']⟩

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- No generator has stage `< 0`, so an acyclic `N 0` is the zeroth stage. -/
private theorem isStage_zero (hN₀ : ∀ w ∈ N 0, dM w = 0 → ∃ w' ∈ N 0, dM w' = w) :
    IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ 0 0 0 := by
  refine ⟨fun x hx ↦ absurd hx (Nat.not_lt_zero _), fun x hx ↦ absurd hx (Nat.not_lt_zero _),
    fun x hx ↦ absurd hx (Nat.not_lt_zero _), fun x hx ↦ absurd hx (Nat.not_lt_zero _),
    fun x hx ↦ absurd hx (Nat.not_lt_zero _), fun x hx ↦ absurd hx (Nat.not_lt_zero _),
    fun x hx ↦ absurd hx (Nat.not_lt_zero _), fun f w hf _ hfw hw ↦ ?_⟩
  obtain rfl : f = 0 := Finsupp.support_eq_empty.1 <| Finset.coe_eq_empty.1 <|
    Set.subset_empty_iff.1 fun x hx ↦ Nat.not_lt_zero _ (hf hx)
  obtain ⟨w', hw', rfl⟩ := hN₀ w hw (by rw [← hfw, map_zero])
  exact ⟨0, w', by simp, hw', by simp, by simp⟩

/-- **One more stage of cells.** The first `n` stages of a semi-free model extend to the first
`n + 1`, without changing the rows and images of the generators of stage `< n`, by attaching the
generators of stage `n` (`RowFiniteTwistingCocycle.exists_attach_of_forall_exists`). -/
private theorem IsStage.exists_succ (hM : IsDGLeftModule h ℳ dM) (hN : Monotone N)
    {n : ℕ} (hNn : (N n).IsHomogeneous ℳ) (hc₀ : ∀ x, c₀ x ∈ ℳ (-ind x))
    (hc₀N : ∀ x, c₀ x ∈ N (st x + 1)) (hdc₀ : ∀ x, dM (c₀ x) ∈ N (st x))
    (hQ : ∀ (y : {x // st x = n} →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ N (n + 1) →
      linearCombination A (fun x ↦ c₀ x.1) y - dM w ∈ N n →
        ∃ (y' : {x // st x = n} →₀ A) (w' : M), w' ∈ N (n + 1) ∧
          mapRange.linearMap d y' = y ∧ linearCombination A (fun x ↦ c₀ x.1) y' + dM w' - w ∈ N n)
    {m : G → G →₀ A} {c : G → M}
    (hs : IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ n m c) :
    ∃ (m' : G → G →₀ A) (c' : G → M),
      IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ (n + 1) m' c' ∧
        (∀ x, st x < n → m' x = m x) ∧ (∀ x, st x < n → c' x = c x) := by
  classical
  -- Outline: restrict the first `n` stages to a cocycle `mP` on the subtype `P` of generators of
  -- stage `< n`, attach the generators `Q` of stage `n` to it, and read the attached cocycle on
  -- `P ⊕ Q` back on `G` through the injection `φ : P ⊕ Q → G`, whose image is stage `≤ n`.
  -- The generators of stage `< n` and the restriction of the cocycle to them.
  let P := {x : G // st x < n}
  let Q := {x : G // st x = n}
  have hsupp (x : P) : ↑(m x.1).support ⊆ Set.range (Subtype.val : P → G) :=
    fun y hy ↦ ⟨⟨y, (hs.lt x.1 x.2 y hy).trans x.2⟩, rfl⟩
  have hmP (x : P) : mapDomain Subtype.val
      (comapDomain Subtype.val (m x.1) Subtype.val_injective.injOn) = m x.1 :=
    mapDomain_comapDomain _ Subtype.val_injective _ (hsupp x)
  have hD (f : P →₀ A) : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (mapDomain Subtype.val f)
      = mapDomain Subtype.val (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d)
        (fun x : P ↦ comapDomain Subtype.val (m x.1) Subtype.val_injective.injOn) f) :=
    rowFiniteTwistedDifferential_mapDomain Subtype.val _ (fun x ↦ (hmP x).symm) f
  let mP : RowFiniteTwistingCocycle 𝒜 d P (fun x ↦ ind x.1) :=
    { m := fun x ↦ comapDomain Subtype.val (m x.1) Subtype.val_injective.injOn
      mem_graded := fun x y ↦ hs.mem_graded x.1 x.2 y.1
      twisting := fun x ↦ by
        refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero
          (ind := fun x : P ↦ ind x.1) _ fun y ↦ hs.mem_graded x.1 x.2 y.1).2 ?_
        apply mapDomain_injective Subtype.val_injective
        rw [← hD, hmP, mapDomain_zero]
        exact hs.twisting x.1 x.2 }
  have hmapsupp (f : P →₀ A) : ↑(mapDomain Subtype.val f).support ⊆ {x | st x < n} := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hy)
    exact x.2
  -- The first `n` stages make the restriction a quasi-isomorphism onto `N n`.
  have hK : ∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u = 0 →
      linearCombination A (fun x : P ↦ c x.1) u = dM w → w ∈ N n →
        ∃ (u' : P →₀ A) (w' : M), w' ∈ N n ∧
          rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u' = u ∧
            linearCombination A (fun x : P ↦ c x.1) u' + dM w' = w := by
    intro u w hu huw hw
    obtain ⟨f', w', hf', hw', hDf', hfw'⟩ := hs.exists_eq (mapDomain Subtype.val u) w
      (hmapsupp u) (by rw [hD]; exact (congrArg _ hu).trans (mapDomain_zero))
      (by rwa [linearCombination_mapDomain]) hw
    have hf'r : ↑f'.support ⊆ Set.range (Subtype.val : P → G) := fun y hy ↦ ⟨⟨y, hf' hy⟩, rfl⟩
    refine ⟨comapDomain Subtype.val f' Subtype.val_injective.injOn, w', hw', ?_, ?_⟩
    · apply mapDomain_injective Subtype.val_injective
      rw [← hD, mapDomain_comapDomain _ Subtype.val_injective _ hf'r, hDf']
    · have := linearCombination_mapDomain A (v' := c) (Subtype.val : P → G)
        (comapDomain Subtype.val f' Subtype.val_injective.injOn)
      rw [mapDomain_comapDomain _ Subtype.val_injective _ hf'r, Function.comp_def] at this
      rw [← this, hfw']
  -- Attach the generators of stage `n`.
  have hg (x : P) : linearCombination A (fun x : P ↦ c x.1) (mP.m x) = dM (c x.1) := by
    have := hs.hom x.1 x.2
    rwa [← hmP x, linearCombination_mapDomain] at this
  obtain ⟨a, ha, hca, cQ, hcQ, hcQN, hcQsub, hak, hext⟩ :=
    mP.exists_attach_of_forall_exists (Q := Q) (indQ := fun x ↦ ind x.1) hM hNn
      (hN n.le_succ) (fun x ↦ hN (Nat.succ_le_of_lt x.2) (hs.mem_succ x.1 x.2))
      (fun x ↦ hs.mem x.1 x.2) hg hK (c₀ := fun x ↦ c₀ x.1) (fun x ↦ hc₀ x.1)
      (fun x ↦ by have := hc₀N x.1; rwa [x.2] at this)
      (fun x ↦ by have := hdc₀ x.1; rwa [x.2] at this) hQ
  -- The new rows and images on `G`: the old ones below stage `n`, the attached ones at stage `n`.
  let m' : G → G →₀ A := fun x ↦
    if hx : st x < n then m x else if hx' : st x = n then mapDomain Subtype.val (a ⟨x, hx'⟩) else 0
  let c' : G → M := fun x ↦
    if hx : st x < n then c x else if hx' : st x = n then cQ ⟨x, hx'⟩ else 0
  have hm'P (x : P) : m' x.1 = m x.1 := by simp [m', x.2]
  have hc'P (x : P) : c' x.1 = c x.1 := by simp [c', x.2]
  have hm'Q (x : Q) : m' x.1 = mapDomain Subtype.val (a x) := by
    simp [m', x.2]
  have hc'Q (x : Q) : c' x.1 = cQ x := by
    simp [c', x.2]
  have hcases (x : G) (hx : st x < n + 1) : (∃ y : P, y.1 = x) ∨ ∃ y : Q, y.1 = x := by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    exacts [Or.inl ⟨⟨x, hx⟩, rfl⟩, Or.inr ⟨⟨x, hx⟩, rfl⟩]
  have hDP (f : P →₀ A) : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m'
      (mapDomain Subtype.val f) =
        mapDomain Subtype.val (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m f) :=
    rowFiniteTwistedDifferential_mapDomain Subtype.val _ (fun x ↦ (hm'P x).trans (hmP x).symm) f
  -- `φ : P ⊕ Q → G` identifies the attached module with the generators of stage `≤ n`.
  let φ : P ⊕ Q → G := Sum.elim Subtype.val Subtype.val
  have hφ : Function.Injective φ := Subtype.val_injective.sumElim Subtype.val_injective
    fun x y hxy ↦ by
      have h₁ := x.2
      have h₂ := y.2
      simp only [hxy] at h₁
      omega
  have hDφ (f : P ⊕ Q →₀ A) : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m' (mapDomain φ f) =
      mapDomain φ (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (mP.attach a ha hca).m f) := by
    refine rowFiniteTwistedDifferential_mapDomain φ _ (fun z ↦ ?_) f
    rcases z with x | x
    · rw [RowFiniteTwistingCocycle.attach_m_inl, ← mapDomain_comp]
      exact (hm'P x).trans (hmP x).symm
    · rw [RowFiniteTwistingCocycle.attach_m_inr, ← mapDomain_comp]
      exact hm'Q x
  have hcφ : c' ∘ φ = Sum.elim (fun x : P ↦ c x.1) cQ := by
    funext z
    rcases z with x | x
    exacts [hc'P x, hc'Q x]
  refine ⟨m', c', ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun f w hf hDf hfw hw ↦ ?_⟩,
    fun x hx ↦ hm'P ⟨x, hx⟩, fun x hx ↦ hc'P ⟨x, hx⟩⟩
  -- The rows of the new generators involve only old generators.
  · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := hcases x hx
    · rw [hm'P]
      exact hs.lt y.1 y.2
    · rw [hm'Q]
      intro z hz
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hz)
      rw [y.2]
      exact p.2
  · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := hcases x hx
    · rw [hm'P]
      exact hs.mem_graded y.1 y.2
    · rw [hm'Q]
      intro z
      by_cases hz : st z < n
      · obtain ⟨p, rfl⟩ : ∃ p : P, p.1 = z := ⟨⟨z, hz⟩, rfl⟩
        rw [mapDomain_apply_of_injective Subtype.val_injective]
        exact ha y p
      · rw [mapDomain_of_notMem_range _ _ (by rintro ⟨p, rfl⟩; exact hz p.2)]
        exact zero_mem _
  · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := hcases x hx
    · rw [hm'P, rowFiniteTwistedDifferential_congr (m' := m)
        fun z hz ↦ hm'P ⟨z, (hs.lt y.1 y.2 z hz).trans y.2⟩]
      exact hs.twisting y.1 y.2
    · rw [hm'Q, hDP, hca, mapDomain_zero]
  · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := hcases x hx
    · rw [hc'P]
      exact hs.mem y.1 y.2
    · rw [hc'Q]
      exact hcQ y
  · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := hcases x hx
    · rw [hc'P]
      exact hs.mem_succ y.1 y.2
    · rw [hc'Q, y.2]
      exact hcQN y
  · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := hcases x hx
    · rw [hc'P]
      exact hs.sub_mem y.1 y.2
    · rw [hc'Q, y.2]
      exact hcQsub y
  · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := hcases x hx
    · rw [hm'P, linearCombination_congr (v' := c)
        fun z hz ↦ hc'P ⟨z, (hs.lt y.1 y.2 z hz).trans y.2⟩, hc'P]
      exact hs.hom y.1 y.2
    · rw [hm'Q, linearCombination_mapDomain, hc'Q,
        show c' ∘ Subtype.val = fun x : P ↦ c x.1 from funext hc'P]
      exact hak y
  -- A relative cycle on the generators of stage `≤ n` is one of the attached module.
  · obtain ⟨v, rfl⟩ : ∃ v, mapDomain φ v = f := by
      refine ⟨comapDomain φ f hφ.injOn, mapDomain_comapDomain _ hφ _ fun y hy ↦ ?_⟩
      obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := hcases y (hf hy)
      exacts [⟨Sum.inl z, rfl⟩, ⟨Sum.inr z, rfl⟩]
    have hDv : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (mP.attach a ha hca).m v = 0 :=
      mapDomain_injective hφ (by rw [← hDφ, hDf, mapDomain_zero])
    rw [linearCombination_mapDomain, hcφ] at hfw
    obtain ⟨f', w', hw', hDf', hfw'⟩ := hext v w hDv hfw hw
    refine ⟨mapDomain φ f', w', fun y hy ↦ ?_, hw', by rw [hDφ, hDf'], ?_⟩
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hy)
      rcases z with z | z
      · exact Nat.lt_succ_of_lt z.2
      · exact Nat.lt_succ_of_le z.2.le
    · rw [linearCombination_mapDomain, hcφ]
      exact hfw'

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
  `N n` is a relative boundary there, with target in `N n`: the restriction of `c` is a
  quasi-isomorphism onto `N n`;
* every relative cycle of `c` with target in `⨆ n, N n` is a relative boundary with target in
  `⨆ n, N n`: `c` is a quasi-isomorphism onto the union. -/
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
  -- Extend each stage to the next, and iterate from the empty stage.
  have hstep (n : ℕ) (p : (G → G →₀ A) × (G → M))
      (hp : IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ n p.1 p.2) :
      ∃ q : (G → G →₀ A) × (G → M),
        IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ (n + 1) q.1 q.2 ∧
          (∀ x, st x < n → q.1 x = p.1 x) ∧ (∀ x, st x < n → q.2 x = p.2 x) := by
    obtain ⟨m', c', h₁, h₂, h₃⟩ := hp.exists_succ hM hN (hNh n) hc₀ hc₀N hdc₀ (hQ n)
    exact ⟨(m', c'), h₁, h₂, h₃⟩
  choose! next hnext using hstep
  let seq : ℕ → (G → G →₀ A) × (G → M) := fun n ↦ Nat.rec (0, 0) next n
  have hseq (n : ℕ) :
      IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ n (seq n).1 (seq n).2 := by
    induction n with
    | zero => exact isStage_zero hN₀
    | succ n ih => exact (hnext n _ ih).1
  -- Later stages keep the rows and images of the earlier generators.
  have hagree (x : G) (k : ℕ) :
      (seq (st x + k + 1)).1 x = (seq (st x + 1)).1 x ∧
        (seq (st x + k + 1)).2 x = (seq (st x + 1)).2 x := by
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      have hk : st x < st x + k + 1 := by omega
      exact ⟨((hnext _ _ (hseq _)).2.1 x hk).trans ih.1, ((hnext _ _ (hseq _)).2.2 x hk).trans ih.2⟩
  let m₀ : G → G →₀ A := fun x ↦ (seq (st x + 1)).1 x
  let c : G → M := fun x ↦ (seq (st x + 1)).2 x
  have hfin (n : ℕ) :
      IsStage (𝒜 := 𝒜) (d := d) (ind := ind) (ℳ := ℳ) (dM := dM) st N c₀ n m₀ c := by
    refine (hseq n).congr (fun x hx ↦ ?_) (fun x hx ↦ ?_) <;>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hx
    exacts [(hagree x k).1.symm, (hagree x k).2.symm]
  have hlt (x : G) : st x < st x + 1 := Nat.lt_succ_self _
  let m : RowFiniteTwistingCocycle 𝒜 d G ind :=
    { m := m₀
      mem_graded := fun x ↦ (hfin _).mem_graded x (hlt x)
      twisting := fun x ↦ (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
        ((hfin _).mem_graded x (hlt x))).2 ((hfin _).twisting x (hlt x)) }
  refine ⟨m, c, fun x ↦ (hfin _).lt x (hlt x), fun x ↦ (hfin _).mem x (hlt x),
    fun x ↦ (hfin _).mem_succ x (hlt x), fun x ↦ (hfin _).sub_mem x (hlt x),
    fun x ↦ (hfin _).hom x (hlt x), fun n ↦ (hfin n).exists_eq, fun f w hf hfw hw ↦ ?_⟩
  -- A relative cycle of the union lives at a finite stage of the generators and the filtration.
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed N hN.directed_le).1 hw
  obtain ⟨f', w', -, hw', hDf', hfw'⟩ := (hfin (f.support.sup st + 1 + k)).exists_eq f w
    (fun x hx ↦ by have := Finset.le_sup (f := st) hx; simp only [Set.mem_ofPred_eq]; omega)
    hf hfw (hN (by omega) hk)
  exact ⟨f', w', Submodule.mem_iSup_of_mem _ hw', hDf', hfw'⟩

end TauCeti
