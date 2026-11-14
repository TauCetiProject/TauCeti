/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.QuasiIso
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Relabel

/-!
# Semi-free models of filtered differential graded modules, one stage at a time

Let `M` be a differential graded left module over a DG algebra `A`, with an increasing filtration
`N 0 ≤ N 1 ≤ ⋯` by homogeneous `A`-submodules closed under the differential, and suppose `N 0` is
acyclic. Let `P` be a graded set of generators, each with a **stage** `s x : ℕ`, and for every
generator `x` of stage `n` let `c₀ x` be an element of `N (n + 1)` of degree `-ind x`, with
`d (c₀ x) ∈ N n`. Suppose that, for every `n`, the free module on the generators of stage `n`,
with its coefficient differential, is quasi-isomorphic through `c₀` to `N (n + 1)` modulo `N n`.
This is the situation of a CW complex filtered by its skeleta, with one generator for each cell:
for the chains on the based path space, filtered by the preimages of the skeleta of the base,
the relative chains over the `n`-cells are quasi-isomorphic to a free module over the chains on
the loop space with one generator per `n`-cell, through the relative fundamental chains of the
cells. Brown's twisted tensor product, a semi-free resolution of the ground ring, is built from
these data.

The main result (`TauCeti.exists_rowFiniteTwistingCocycle_of_filtration`) attaches the
generators one stage at a time and passes to the union: there are a row-finite twisting cocycle
`m` on `(P, ind)` and corrected images `c x ≡ c₀ x` modulo `N (s x)`, such that

* the row of each generator only involves generators of strictly smaller stage, so that `m` is
  semi-free (`TauCeti.RowFiniteTwistingCocycle.wellFounded_mem_support_of_lt`) and its free module
  `K_m` is K-projective and K-flat;
* `c : K_m → M` commutes with the differentials and sends the generators of stage below `n` into
  `N n`;
* for every `n`, the vectors of `K_m` supported on the generators of stage below `n` map
  quasi-isomorphically onto `N n`: their relative cycles, with target in `N n`, are relative
  boundaries.

The rows of the stage-`n` generators are found by the single attachment step
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, applied to the subcocycle on
the earlier stages (`TauCeti.RowFiniteTwistingCocycle.restrict`), and the result is relabelled back
into `P` (`TauCeti.RowFiniteTwistingCocycle.extend`). Since every vector of `K_m` is supported on
finitely many generators, and the filtration is increasing, `c` is then a quasi-isomorphism onto
the union `⨆ n, N n`
(`TauCeti.RowFiniteTwistingCocycle.exists_rowFiniteTwistedDifferential_eq_of_iSup`), in
particular onto `M` when the filtration is exhaustive. No finiteness of the stages is assumed.

## Main results

* `TauCeti.exists_rowFiniteTwistingCocycle_of_filtration`: the semi-free model of a filtered DG
  module, attached stage by stage.
* `TauCeti.RowFiniteTwistingCocycle.exists_rowFiniteTwistedDifferential_eq_of_iSup`: stagewise
  quasi-isomorphisms onto an increasing filtration give a quasi-isomorphism onto its union.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6 (semifree modules and Proposition 6.6).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

open Finsupp Function

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ}
  {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M} {h : IsDGAlgebra 𝒜 d}

namespace RowFiniteTwistingCocycle

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- **Quasi-isomorphisms onto the union of a filtration.** Let `N` be an increasing filtration of
`M`, and suppose that for every `n` the relative cycles of `g : K_m → M` supported on the
generators of stage below `n`, with target in `N n`, are relative boundaries supported there, with
target in `N n`. Then every relative cycle of `g` with target in `⨆ n, N n` is a relative
boundary with target in `⨆ n, N n`. -/
theorem exists_rowFiniteTwistedDifferential_eq_of_iSup (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (s : P → ℕ) {N : ℕ → Submodule A M} (hN : Monotone N) {g : P → M}
    (hg : ∀ (n : ℕ) (f : P →₀ A) (w : M), f ∈ supported A A {x | s x < n} →
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0 →
      linearCombination A g f = dM w → w ∈ N n → ∃ (f' : P →₀ A) (w' : M),
        f' ∈ supported A A {x | s x < n} ∧ w' ∈ N n ∧
          rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
            linearCombination A g f' + dM w' = w)
    {f : P →₀ A} {w : M} (hf : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0)
    (hfw : linearCombination A g f = dM w) (hw : w ∈ ⨆ n, N n) :
    ∃ (f' : P →₀ A) (w' : M), w' ∈ ⨆ n, N n ∧
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
        linearCombination A g f' + dM w' = w := by
  classical
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed N hN.directed_le).1 hw
  -- Both `f` and `w` live at the stage `max k (sup (s + 1))`.
  have hfn : f ∈ supported A A {x | s x < max k (f.support.sup fun x ↦ s x + 1)} :=
    (mem_supported A f).2 fun x hx ↦
      (Nat.lt_succ_self _).trans_le ((Finset.le_sup (f := fun x ↦ s x + 1) hx).trans
        (le_max_right _ _))
  obtain ⟨f', w', -, hw', hf', hfw'⟩ := hg _ f w hfn hf hfw (hN (le_max_left _ _) hk)
  exact ⟨f', w', Submodule.mem_iSup_of_mem _ hw', hf', hfw'⟩

end RowFiniteTwistingCocycle

variable (ℳ dM) in
/-- The invariant of the stage-by-stage construction after `n` stages: the rows and images of the
generators of stage below `n` have their final properties, and the vectors supported on these
generators map quasi-isomorphically onto `N n`. -/
private structure IsStage (s : P → ℕ) (N : ℕ → Submodule A M) (c₀ : P → M) (n : ℕ)
    (m : RowFiniteTwistingCocycle 𝒜 d P ind) (g : P → M) : Prop where
  lt : ∀ x, s x < n → ∀ y ∈ (m.m x).support, s y < s x
  mem_deg : ∀ x, s x < n → g x ∈ ℳ (-ind x)
  mem : ∀ x, s x < n → g x ∈ N (s x + 1)
  sub_mem : ∀ x, s x < n → g x - c₀ x ∈ N (s x)
  chain : ∀ x, s x < n → linearCombination A g (m.m x) = dM (g x)
  qi : ∀ (f : P →₀ A) (w : M), f ∈ supported A A {x | s x < n} →
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0 →
    linearCombination A g f = dM w → w ∈ N n → ∃ (f' : P →₀ A) (w' : M),
      f' ∈ supported A A {x | s x < n} ∧ w' ∈ N n ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
          linearCombination A g f' + dM w' = w

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- Before the first stage nothing has been attached, and the acyclicity of `N 0` is the
quasi-isomorphism property. -/
private theorem isStage_zero {s : P → ℕ} {N : ℕ → Submodule A M} {c₀ : P → M}
    (hN₀ : ∀ w ∈ N 0, dM w = 0 → ∃ w' ∈ N 0, dM w' = w) :
    IsStage ℳ dM s N c₀ 0 (0 : RowFiniteTwistingCocycle 𝒜 d P ind) c₀ where
  lt _ hx := absurd hx (Nat.not_lt_zero _)
  mem_deg _ hx := absurd hx (Nat.not_lt_zero _)
  mem _ hx := absurd hx (Nat.not_lt_zero _)
  sub_mem _ hx := absurd hx (Nat.not_lt_zero _)
  chain _ hx := absurd hx (Nat.not_lt_zero _)
  qi f w hf _ hfw hw := by
    obtain rfl : f = 0 := Finsupp.ext fun x ↦ (mem_supported' A f).1 hf x (Nat.not_lt_zero _)
    obtain ⟨w', hw', rfl⟩ := hN₀ w hw (hfw.symm.trans (map_zero _))
    exact ⟨0, w', zero_mem _, hw', map_zero _, by simp⟩

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- The relative quasi-isomorphism hypothesis on the generators of stage `n`, read on the
subtype of these generators. -/
private theorem exists_of_mem_supported_eq {s : P → ℕ} {N : ℕ → Submodule A M} {c₀ : P → M}
    {n : ℕ} (hQ : ∀ (y : P →₀ A) (w : M), y ∈ supported A A {x | s x = n} →
      mapRange.linearMap d y = 0 → w ∈ N (n + 1) → linearCombination A c₀ y - dM w ∈ N n →
      ∃ (y' : P →₀ A) (w' : M), y' ∈ supported A A {x | s x = n} ∧ w' ∈ N (n + 1) ∧
        mapRange.linearMap d y' = y ∧ linearCombination A c₀ y' + dM w' - w ∈ N n)
    (y : {x | s x = n} →₀ A) (w : M) (hy : mapRange.linearMap d y = 0) (hw : w ∈ N (n + 1))
    (hyw : linearCombination A (c₀ ∘ (↑)) y - dM w ∈ N n) :
    ∃ (y' : {x | s x = n} →₀ A) (w' : M), w' ∈ N (n + 1) ∧ mapRange.linearMap d y' = y ∧
      linearCombination A (c₀ ∘ (↑)) y' + dM w' - w ∈ N n := by
  have hsupp (y : P →₀ A) : y ∈ supported A A {x | s x = n} ↔
      ∃ y₀ : {x | s x = n} →₀ A, mapDomain (↑) y₀ = y := by
    rw [← mem_supported_range_iff (R := A), Subtype.range_coe]
  -- Relabelling along the inclusion commutes with the coefficient differential.
  have hd (y : {x | s x = n} →₀ A) : mapRange.linearMap d (mapDomain (↑) y) =
      mapDomain ((↑) : {x | s x = n} → P) (mapRange.linearMap d y) := by
    simp only [mapRange.linearMap_apply]
    exact (mapDomain_mapRange _ _ _ _ (map_add d)).symm
  obtain ⟨y', w', hy', hw', hdy', hyw'⟩ := hQ (mapDomain (↑) y) w ((hsupp _).2 ⟨y, rfl⟩)
    (by rw [hd, hy, mapDomain_zero]) hw (by rwa [linearCombination_mapDomain])
  obtain ⟨y₀, rfl⟩ := (hsupp y').1 hy'
  exact ⟨y₀, w', hw', mapDomain_injective Subtype.val_injective (by rw [← hd, hdy']),
    by rwa [linearCombination_mapDomain] at hyw'⟩

open RowFiniteTwistingCocycle in
/-- **The inductive step.** The generators of stage `n` are attached to the subcocycle on the
earlier stages along cycles found by `exists_attach_of_forall_exists`, with corrected images, and
the attached cocycle is relabelled into `P`. Nothing changes on the earlier stages. -/
private theorem IsStage.exists_succ (hM : IsDGLeftModule h ℳ dM) {s : P → ℕ}
    {N : ℕ → Submodule A M} (hN : Monotone N) (hNh : ∀ n, (N n).IsHomogeneous ℳ) {c₀ : P → M}
    (hc₀ : ∀ x, c₀ x ∈ ℳ (-ind x)) (hc₀N : ∀ x, c₀ x ∈ N (s x + 1))
    (hdc₀ : ∀ x, dM (c₀ x) ∈ N (s x))
    (hQ : ∀ (n : ℕ) (y : P →₀ A) (w : M), y ∈ supported A A {x | s x = n} →
      mapRange.linearMap d y = 0 → w ∈ N (n + 1) → linearCombination A c₀ y - dM w ∈ N n →
      ∃ (y' : P →₀ A) (w' : M), y' ∈ supported A A {x | s x = n} ∧ w' ∈ N (n + 1) ∧
        mapRange.linearMap d y' = y ∧ linearCombination A c₀ y' + dM w' - w ∈ N n)
    {n : ℕ} {m : RowFiniteTwistingCocycle 𝒜 d P ind} {g : P → M}
    (hst : IsStage ℳ dM s N c₀ n m g) :
    ∃ (m' : RowFiniteTwistingCocycle 𝒜 d P ind) (g' : P → M),
      IsStage ℳ dM s N c₀ (n + 1) m' g' ∧ ∀ x, s x < n → m'.m x = m.m x ∧ g' x = g x := by
  classical
  -- The subcocycle on the generators of the earlier stages, which are closed under the rows.
  have hS : ∀ x ∈ {x | s x < n}, ∀ y ∈ (m.m x).support, y ∈ {x | s x < n} :=
    fun x hx y hy ↦ (hst.lt x hx y hy).trans hx
  let mS := m.restrict _ hS
  have hmS (x : {x | s x < n}) : m.m x = mapDomain (↑) (mS.m x) :=
    (m.mapDomain_restrict_m _ hS x).symm
  -- Attach the generators of stage `n` to it.
  obtain ⟨a, ha, hca, c, hcdeg, hcN, hcsub, hac, hqi⟩ :=
    mS.exists_attach_of_forall_exists hM (Q := {x | s x = n}) (indQ := fun q ↦ ind q)
      (N₀ := N n) (N₁ := N (n + 1)) (g := g ∘ (↑)) (hNh n) (hN n.le_succ)
      (fun x ↦ hN (Nat.succ_le_of_lt x.2) (hst.mem x x.2)) (fun x ↦ hst.mem_deg x x.2)
      (fun x ↦ by rw [← linearCombination_mapDomain, ← hmS]; exact hst.chain x x.2)
      ((m.forall_exists_iff_forall_mem_supported_exists mS Subtype.val_injective hmS g
        (N n)).2 (by rw [Subtype.range_coe]; exact hst.qi))
      (c₀ := c₀ ∘ (↑)) (fun q ↦ hc₀ q)
      (fun q ↦ by simpa only [Function.comp_apply, show s q = n from q.2] using hc₀N q)
      (fun q ↦ by simpa only [Function.comp_apply, show s q = n from q.2] using hdc₀ q)
      (exists_of_mem_supported_eq (hQ n))
  -- Relabel the attached cocycle into `P`.
  let e : {x | s x < n} ⊕ {x | s x = n} → P := Sum.elim (↑) (↑)
  have he : Injective e := Subtype.val_injective.sumElim Subtype.val_injective
    fun x q hxq ↦ by
      have h₁ : s x < n := x.2
      have h₂ : s q = n := q.2
      rw [hxq] at h₁
      omega
  have hrange : Set.range e = {x | s x < n + 1} := by
    rw [Set.Sum.elim_range, Subtype.range_coe, Subtype.range_coe]
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    omega
  -- The new cocycle and map: the attached rows and images, relabelled along `e`. Since
  -- `e ∘ Sum.inl` and `e ∘ Sum.inr` are the inclusions by construction of `e`, they recover the
  -- old rows and images on the earlier stages and the attached ones on stage `n`.
  let m' := (mS.attach a ha hca).extend he (by rintro (x | q) <;> rfl)
  let g' := Function.extend e (Sum.elim (g ∘ (↑)) c) g
  have hge : g' ∘ e = Sum.elim (g ∘ (↑)) c := funext (he.extend_apply _ _)
  have hm'e := (mS.attach a ha hca).extend_m_apply he (by rintro (x | q) <;> rfl)
  have hm'S (x : P) (hx : s x < n) : m'.m x = m.m x :=
    (hm'e (Sum.inl ⟨x, hx⟩)).trans (by rw [attach_m_inl, ← mapDomain_comp]; exact (hmS _).symm)
  have hm'X (x : P) (hx : s x = n) : m'.m x = mapDomain (↑) (a ⟨x, hx⟩) :=
    (hm'e (Sum.inr ⟨x, hx⟩)).trans (by rw [attach_m_inr, ← mapDomain_comp]; rfl)
  have hg'S (x : P) (hx : s x < n) : g' x = g x := congrFun hge (Sum.inl ⟨x, hx⟩)
  have hg'X (x : P) (hx : s x = n) : g' x = c ⟨x, hx⟩ := congrFun hge (Sum.inr ⟨x, hx⟩)
  have hchain (z : {x | s x < n} ⊕ {x | s x = n}) :
      linearCombination A g' (m'.m (e z)) = dM (g' (e z)) := by
    rw [hm'e, linearCombination_mapDomain, hge, ← Function.comp_apply (f := g'), hge]
    rcases z with x | q
    · rw [attach_m_inl, linearCombination_mapDomain, Sum.elim_comp_inl, Sum.elim_inl,
        Function.comp_apply, ← hst.chain x x.2, hmS, linearCombination_mapDomain]
    · rw [attach_m_inr, linearCombination_mapDomain, Sum.elim_comp_inl, Sum.elim_inr, hac]
  -- Each property of stage `n + 1` holds on the earlier stages by `hst`, and on stage `n` by the
  -- attachment step; the quasi-isomorphism property is transported back along `e`.
  refine ⟨m', g', ⟨fun x hx y hy ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x hx ↦ ?_, ?_⟩, fun x hx ↦ ⟨hm'S x hx, hg'S x hx⟩⟩
  · rcases (Nat.lt_succ_iff_lt_or_eq.1 hx) with hx | hx
    · exact hst.lt x hx y (hm'S x hx ▸ hy)
    · obtain ⟨y₀, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support (hm'X x hx ▸ hy))
      exact hx ▸ y₀.2
  · rcases (Nat.lt_succ_iff_lt_or_eq.1 hx) with hx | hx
    · exact hg'S x hx ▸ hst.mem_deg x hx
    · rw [hg'X x hx]
      exact hcdeg ⟨x, hx⟩
  · rcases (Nat.lt_succ_iff_lt_or_eq.1 hx) with hx | hx
    · exact hg'S x hx ▸ hst.mem x hx
    · rw [hg'X x hx, hx]
      exact hcN _
  · rcases (Nat.lt_succ_iff_lt_or_eq.1 hx) with hx | hx
    · exact hg'S x hx ▸ hst.sub_mem x hx
    · rw [hg'X x hx, hx]
      exact hcsub _
  · obtain ⟨z, rfl⟩ : x ∈ Set.range e := hrange ▸ hx
    exact hchain z
  · rw [← hrange]
    exact (m'.forall_exists_iff_forall_mem_supported_exists (mS.attach a ha hca) he hm'e g'
      (N (n + 1))).1 (by rw [hge]; exact hqi)

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- **Passing to the limit of the stages.** The rows and images of a sequence of stages that
agree on the earlier stages define a single cocycle and map with the properties of every stage. -/
private theorem exists_of_isStage {s : P → ℕ} {N : ℕ → Submodule A M} {c₀ : P → M}
    (m : ℕ → RowFiniteTwistingCocycle 𝒜 d P ind) (g : ℕ → P → M)
    (hst : ∀ n, IsStage ℳ dM s N c₀ n (m n) (g n))
    (hagree : ∀ n x, s x < n → (m (n + 1)).m x = (m n).m x ∧ g (n + 1) x = g n x) :
    ∃ (m' : RowFiniteTwistingCocycle 𝒜 d P ind) (c : P → M),
      (∀ x, ∀ y ∈ (m'.m x).support, s y < s x) ∧ (∀ x, c x ∈ ℳ (-ind x)) ∧
      (∀ x, c x ∈ N (s x + 1)) ∧ (∀ x, c x - c₀ x ∈ N (s x)) ∧
      (∀ x, linearCombination A c (m'.m x) = dM (c x)) ∧
      ∀ (n : ℕ) (f : P →₀ A) (w : M), f ∈ supported A A {x | s x < n} →
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m'.m f = 0 →
        linearCombination A c f = dM w → w ∈ N n → ∃ (f' : P →₀ A) (w' : M),
          f' ∈ supported A A {x | s x < n} ∧ w' ∈ N n ∧
            rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m'.m f' = f ∧
              linearCombination A c f' + dM w' = w := by
  -- Once a generator has been attached, its row and image no longer change.
  have hstab (x : P) (n : ℕ) (hn : s x < n) :
      (m n).m x = (m (s x + 1)).m x ∧ g n x = g (s x + 1) x := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hn)
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      obtain ⟨h₁, h₂⟩ := hagree (s x + 1 + k) x (by omega)
      exact ⟨h₁.trans (ih (by omega)).1, h₂.trans (ih (by omega)).2⟩
  have hlt (x : P) : ∀ y ∈ ((m (s x + 1)).m x).support, s y < s x :=
    (hst (s x + 1)).lt x (Nat.lt_succ_self _)
  let m' : RowFiniteTwistingCocycle 𝒜 d P ind :=
    { m x := (m (s x + 1)).m x
      mem_graded x := (m (s x + 1)).mem_graded x
      twisting x := ((m (s x + 1)).twisting x).trans (Finsupp.sum_congr fun y hy ↦ by
        rw [(hstab y (s x + 1) ((hlt x y hy).trans (Nat.lt_succ_self _))).1]) }
  refine ⟨m', fun x ↦ g (s x + 1) x, fun x ↦ hlt x, fun x ↦ (hst _).mem_deg x (Nat.lt_succ_self _),
    fun x ↦ (hst _).mem x (Nat.lt_succ_self _), fun x ↦ (hst _).sub_mem x (Nat.lt_succ_self _),
    fun x ↦ ?_, fun n f w hf hDf hfw hw ↦ ?_⟩
  · refine (Eq.trans ?_ ((hst (s x + 1)).chain x (Nat.lt_succ_self _)))
    simp only [linearCombination_apply]
    exact Finsupp.sum_congr fun y hy ↦ by
      rw [(hstab y (s x + 1) ((hlt x y hy).trans (Nat.lt_succ_self _))).2]
  · -- On the vectors supported on the stages below `n`, the limit agrees with stage `n`.
    have hcongr (f : P →₀ A) (hf : f ∈ supported A A {x | s x < n}) :
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m'.m f =
            rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m n).m f ∧
          linearCombination A (fun x ↦ g (s x + 1) x) f = linearCombination A (g n) f := by
      have hfs (x : P) (hx : x ∈ f.support) : s x < n := (mem_supported A f).1 hf hx
      refine ⟨rowFiniteTwistedDifferential_congr fun x hx ↦ (hstab x n (hfs x hx)).1.symm, ?_⟩
      simp only [linearCombination_apply]
      exact Finsupp.sum_congr fun x hx ↦ by rw [(hstab x n (hfs x hx)).2]
    rw [(hcongr f hf).1] at hDf
    rw [(hcongr f hf).2] at hfw
    obtain ⟨f', w', hf', hw', hDf', hfw'⟩ := (hst n).qi f w hf hDf hfw hw
    exact ⟨f', w', hf', hw', (hcongr f' hf').1.trans hDf', (hcongr f' hf').2 ▸ hfw'⟩

/-- **Semi-free models of filtered differential graded modules.** Let `N` be an increasing
filtration of a differential graded left module `M` by homogeneous submodules, with `N 0`
acyclic, and let `P` be a graded set of generators, the generator `x` having stage `s x`. Let
`c₀ x ∈ N (s x + 1)`, of degree `-ind x`, be relative cycles modulo `N (s x)` through which, for
each `n`, the free module on the generators of stage `n`, with its coefficient differential, is
quasi-isomorphic to `N (n + 1)` modulo `N n`.

Then there are a row-finite twisting cocycle `m` on `(P, ind)`, whose rows only involve generators
of strictly smaller stage, and images `c x ≡ c₀ x` modulo `N (s x)`, of degree `-ind x` and in
`N (s x + 1)`, such that `c : K_m → M` commutes with the differentials and, for every `n`, the
vectors supported on the generators of stage below `n` map quasi-isomorphically onto `N n`: their
relative cycles, with target in `N n`, are relative boundaries supported on these generators, with
target in `N n`. -/
theorem exists_rowFiniteTwistingCocycle_of_filtration (hM : IsDGLeftModule h ℳ dM) (s : P → ℕ)
    {N : ℕ → Submodule A M} (hN : Monotone N) (hNh : ∀ n, (N n).IsHomogeneous ℳ)
    (hN₀ : ∀ w ∈ N 0, dM w = 0 → ∃ w' ∈ N 0, dM w' = w) {c₀ : P → M}
    (hc₀ : ∀ x, c₀ x ∈ ℳ (-ind x)) (hc₀N : ∀ x, c₀ x ∈ N (s x + 1))
    (hdc₀ : ∀ x, dM (c₀ x) ∈ N (s x))
    (hQ : ∀ (n : ℕ) (y : P →₀ A) (w : M), y ∈ supported A A {x | s x = n} →
      mapRange.linearMap d y = 0 → w ∈ N (n + 1) → linearCombination A c₀ y - dM w ∈ N n →
      ∃ (y' : P →₀ A) (w' : M), y' ∈ supported A A {x | s x = n} ∧ w' ∈ N (n + 1) ∧
        mapRange.linearMap d y' = y ∧ linearCombination A c₀ y' + dM w' - w ∈ N n) :
    ∃ (m : RowFiniteTwistingCocycle 𝒜 d P ind) (c : P → M),
      (∀ x, ∀ y ∈ (m.m x).support, s y < s x) ∧ (∀ x, c x ∈ ℳ (-ind x)) ∧
      (∀ x, c x ∈ N (s x + 1)) ∧ (∀ x, c x - c₀ x ∈ N (s x)) ∧
      (∀ x, linearCombination A c (m.m x) = dM (c x)) ∧
      ∀ (n : ℕ) (f : P →₀ A) (w : M), f ∈ supported A A {x | s x < n} →
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f = 0 →
        linearCombination A c f = dM w → w ∈ N n → ∃ (f' : P →₀ A) (w' : M),
          f' ∈ supported A A {x | s x < n} ∧ w' ∈ N n ∧
            rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f' = f ∧
              linearCombination A c f' + dM w' = w := by
  classical
  have : Nonempty (RowFiniteTwistingCocycle 𝒜 d P ind) := ⟨0⟩
  choose! F G hFG hagree using fun (n : ℕ) (m : RowFiniteTwistingCocycle 𝒜 d P ind) (g : P → M)
    (hst : IsStage ℳ dM s N c₀ n m g) ↦ hst.exists_succ hM hN hNh hc₀ hc₀N hdc₀ hQ
  -- The stages, defined by recursion from the empty cocycle.
  let stage : ℕ → RowFiniteTwistingCocycle 𝒜 d P ind × (P → M) := fun n ↦
    Nat.rec (motive := fun _ ↦ RowFiniteTwistingCocycle 𝒜 d P ind × (P → M)) (0, c₀)
      (fun k p ↦ (F k p.1 p.2, G k p.1 p.2)) n
  have hstage (n : ℕ) : IsStage ℳ dM s N c₀ n (stage n).1 (stage n).2 := by
    induction n with
    | zero => exact isStage_zero hN₀
    | succ n ih => exact hFG n _ _ ih
  exact exists_of_isStage (fun n ↦ (stage n).1) (fun n ↦ (stage n).2) hstage
    fun n x hx ↦ hagree n _ _ (hstage n) x hx

end TauCeti
