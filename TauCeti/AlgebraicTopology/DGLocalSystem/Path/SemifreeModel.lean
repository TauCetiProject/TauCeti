/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Filtration
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Relative
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BrownModel
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.PositiveCell
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.ZeroCell
public import TauCeti.Topology.CWComplex.Classical.PathComponent
public import TauCeti.Topology.PathSpace.Moore.Comparison.Between

/-!
# Brown's semi-free model of the chains on the based path space of a CW complex

Let `B` be a space with a point `b`, and `C` a CW complex in `B` containing the path component of
`b`, for instance all of `B` when `B` is a path-connected CW complex. The normalized cubical chains
`C_*(P_b B; R)` on the Moore paths starting at `b` form a differential graded left module over the
chain algebra `C_*(Ω_b B; R)` of the Moore loops at `b`, which act by concatenation in front
(`TauCeti.pathFromChain_isDGLeftModule`). Brown's twisted tensor product models this module by a
semi-free one with one free generator for each cell of `C`: there are a row-finite twisting cocycle
`m` on the cells, the generator of an `n`-cell having index `n`, and a map `g` from its free module
`K_m` to `C_*(P_b B; R)`, linear over `C_*(Ω_b B; R)`, which commutes with the differentials and is
a quasi-isomorphism, that is a Brown model `TauCeti.BrownModel`
(`TauCeti.exists_semifreeModel_pathFromChain`). `TauCeti.brownModel` is a choice of it.

The model is built along the filtration of `C_*(P_b B; R)` by the chains over the skeleta of `C`
(`TauCeti.pathFromChainSkeleton`), one dimension of cells at a time. For this, choose a Moore path
`τ n j` from `b` to the centre of every cell `j` of every dimension `n`. The **chain of the
cell** (`TauCeti.cellPathChain H R τ n j`) is the point chain of `τ 0 j` for a `0`-cell, and the
cube of the paths `τ n j` continued radially to the points of the disk of `j` for a cell of
positive dimension (`TauCeti.cellSectionPathChain`). The free module on the `n`-cells, with the
generator of `j` sent to its chain, is quasi-isomorphic to the chains over the `n`-skeleton modulo
those over the `(n - 1)`-skeleton (for the `0`-cells, this is
`exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton`, and
its `_succ` form for the others). Attaching these generators along cycles, stage by stage, is the
general construction `TauCeti.exists_semifreeModel_of_filtration`, whose output is the model:

* the generator of the cell `⟨n, j⟩` goes to a chain over the `n`-skeleton which agrees with the
  chain of the cell modulo the chains over the `(n - 1)`-skeleton;
* the row of an `n`-cell, its attaching cycle, only involves cells of dimension `< n`, so the model
  is semi-free;
* for every `k`, the cells of dimension `< k` span a submodule of `K_m` which `g` maps
  quasi-isomorphically onto the chains over the `(k - 1)`-skeleton;
* since a chain on the based path space has compact support, and so lies over a finite skeleton,
  `g` is a quasi-isomorphism onto all of `C_*(P_b B; R)`.

Quasi-isomorphisms are stated on elements, as for the attachment step
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`: every relative cycle `(u, w)`,
with `D u = 0` and `g(u) = d w`, is a relative boundary `(D u', g(u') + d w')`. The augmentation of
`C_*(P_b B; R)` onto `R` is a quasi-isomorphism as well, the based path space being contractible
(`TauCeti.exists_pathFromChainDifferential_eq_of_augmentation_eq_zero`); this is why Brown's model
resolves `R` over `C_*(Ω_b B; R)`.

The construction only needs the CW complex to contain the path component of `b`, where the paths
from `b` stay. When `B` is not path connected, there are no paths from `b` to the cells of the
other path components, and the model is built on the cells of the path component of `b`, a
subcomplex (`Topology.CWComplex.pathComponentInSubcomplex`), as
`TauCeti.pathComponentBrownModel`. With a basepoint chosen in each path component, these models
together have one generator for each cell of `B`
(`Topology.CWComplex.sigmaPathComponentCellEquiv`).

## Main definitions

* `TauCeti.cellPathChain H R τ n j`: the chain of the `n`-cell `j` in the based path space.
* `TauCeti.brownModel H R τ hC`: a choice of Brown's model of `C_*(P_b B; R)`.
* `TauCeti.pathComponentBrownModel H R hC`: Brown's model on the cells of the path component of
  `b`, for a CW complex that need not be path connected.

## Main results

* `TauCeti.exists_semifreeModel_pathFromChain`: Brown's semi-free model of `C_*(P_b B; R)`.
* `TauCeti.brownModel_comparison_mem_pathFromChainSkeleton`,
  `TauCeti.brownModel_comparison_sub_cellPathChain_mem_pathFromChainSkeleton`,
  `TauCeti.brownModel_cocycle_m_mem_supported`,
  `TauCeti.exists_differential_eq_and_brownModel_comparison_add_eq_of_mem_supported`: the
  compatibility of the chosen model with the cells and the skeleta.
* `TauCeti.nonempty_rowFiniteHomologous_brownModel_brownModel`: the chosen model does not depend on
  the CW structure, the paths to the cells or the phantom parameter, up to homology.
* `TauCeti.pathComponentBrownModel_eq`: Brown's model on the path component of `b` is the chosen
  model of that subcomplex.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex Finsupp

namespace TauCeti

variable {B : Type} [TopologicalSpace B] [T2Space B] {b : B} {C : Set B} [CWComplex C]
  {H : Type*} {R : Type} [CommRing R]

variable (H R) in
/-- The **chain of a cell in the based path space**, for a choice of Moore paths `τ n j` from `b`
to the centre of every cell `j` of every dimension `n`. For a `0`-cell it is the point chain of
`τ 0 j`; for a cell of positive dimension it is `TauCeti.cellSectionPathChain`, the cube of the
paths `τ n j` continued radially to the points of the disk of `j`. Brown's semi-free model of the
chains on the based path space sends the generator of each cell to this chain, modulo the chains
over the lower skeleta (`TauCeti.exists_semifreeModel_pathFromChain`). -/
def cellPathChain (τ : ∀ (n : ℕ) (j : cell C n), MoorePathBetween B b (map n j 0)) :
    ∀ (n : ℕ), cell C n → cubicalChainModule (MoorePathFrom B b) H R
  | 0, q => cubicalChainModuleLinearMap (G' := H) R (MoorePathBetween.toMoorePathFrom b _)
      (pathChainPoint R (τ 0 q))
  | m + 1, j => cellSectionPathChain (H := H) (R := R) (τ (m + 1)) j

variable (τ : ∀ (n : ℕ) (j : cell C n), MoorePathBetween B b (map n j 0))

omit [T2Space B] in
/-- The chain of a `0`-cell is the point chain of the chosen path to it. -/
@[simp]
theorem cellPathChain_zero (q : cell C 0) :
    cellPathChain H R τ 0 q = cubicalChainModuleLinearMap (G' := H) R
      (MoorePathBetween.toMoorePathFrom b _) (pathChainPoint R (τ 0 q)) := (rfl)

omit [T2Space B] in
/-- The chain of a cell of positive dimension is its section cube in the based path space. -/
@[simp]
theorem cellPathChain_succ (m : ℕ) (j : cell C (m + 1)) :
    cellPathChain H R τ (m + 1) j = cellSectionPathChain (H := H) (R := R) (τ (m + 1)) j := (rfl)

/-- The chosen path to the centre of a `0`-cell, as a path to the point of the cell. -/
private def zeroCellPath (q : cell C 0) : MoorePathBetween B b (zeroCellPoint C q) :=
  (τ 0 q).cast rfl (by rw [coe_zeroCellPoint, Subsingleton.elim (0 : Fin 0 → ℝ) ![]])

/-- The chain of a `0`-cell is the point chain of the path to the point of the cell. -/
private theorem cellPathChain_zero_eq (q : cell C 0) :
    cellPathChain H R τ 0 q = cubicalChainModuleLinearMap (G' := H) R
      (MoorePathBetween.toMoorePathFrom b _) (pathChainPoint R (zeroCellPath τ q)) := by
  -- Changing the end point along an equality `c = map 0 q 0` with `c` free is the identity.
  have h {c : B} (hc : c = map 0 q 0) : cubicalChainModuleLinearMap (G' := H) R
      (MoorePathBetween.toMoorePathFrom b c) (pathChainPoint R ((τ 0 q).cast rfl hc)) =
        cellPathChain H R τ 0 q := by
    subst hc
    rw [MoorePathBetween.cast_rfl_rfl, cellPathChain_zero]
  exact (h _).symm

omit [T2Space B] in
/-- The chain of an `n`-cell has dimension `n`. -/
theorem cellPathChain_mem_cubicalChainModuleGrading (n : ℕ) (j : cell C n) :
    cellPathChain H R τ n j ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-(n : ℤ)) := by
  cases n with
  | zero =>
    rw [cellPathChain_zero, Nat.cast_zero, neg_zero]
    exact cubicalChainModuleLinearMap_mem _ (pathChainPoint_mem _)
  | succ m => exact cellSectionPathChain_mem_cubicalChainModuleGrading _ j

/-- The chain of an `n`-cell lies over the `n`-skeleton. -/
theorem cellPathChain_mem_pathFromChainSkeleton (n : ℕ) (j : cell C n) :
    cellPathChain H R τ n j ∈ pathFromChainSkeleton b C H R n := by
  cases n with
  | zero =>
    rw [cellPathChain_zero_eq]
    exact cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom_mem_pathFromChainSkeleton_zero
      j _
  | succ m => exact cellSectionPathChain_mem_pathFromChainSkeleton _ j

/-- The boundary of the chain of an `n`-cell lies over the `(n - 1)`-skeleton. -/
theorem cubicalChainModuleDifferential_cellPathChain_mem_pathFromChainSkeleton (n : ℕ)
    (j : cell C n) :
    cubicalChainModuleDifferential (MoorePathFrom B b) H R (cellPathChain H R τ n j) ∈
      pathFromChainSkeleton b C H R ((n : ℤ) - 1) := by
  cases n with
  | zero =>
    rw [pathFromChainSkeleton_eq_bot_of_neg (by norm_num), Submodule.mem_bot, cellPathChain_zero,
      cubicalChainModuleDifferential_linearMap, cubicalChainModuleDifferential_pathChainPoint,
      map_zero]
  | succ m =>
    exact cubicalChainModuleDifferential_cellSectionPathChain_mem_pathFromChainSkeleton _ j

/-- **The free module on the `n`-cells is quasi-isomorphic to the `n`-th quotient of the skeletal
filtration**, through the chains of the cells: every relative cycle `(y, w)` of the map
`(α_j)_j ↦ ∑_j α_j · cⱼ`, with `w` over the `n`-skeleton, is a relative boundary modulo the chains
over the `(n - 1)`-skeleton. -/
private theorem exists_mapRange_eq_and_linearCombination_cellPathChain_add_differential_sub_mem
    (n : ℕ) (y : cell C n →₀ loopChainAlgebra B b R)
    (w : cubicalChainModule (MoorePathFrom B b) H R)
    (hy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    (hw : w ∈ pathFromChainSkeleton b C H R n)
    (hyw : linearCombination (loopChainAlgebra B b R) (cellPathChain H R τ n) y -
      cubicalChainModuleDifferential (MoorePathFrom B b) H R w ∈
        pathFromChainSkeleton b C H R ((n : ℤ) - 1)) :
    ∃ (y' : cell C n →₀ loopChainAlgebra B b R) (w' : cubicalChainModule (MoorePathFrom B b) H R),
      w' ∈ pathFromChainSkeleton b C H R n ∧
        mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y ∧
          linearCombination (loopChainAlgebra B b R) (cellPathChain H R τ n) y' +
              cubicalChainModuleDifferential (MoorePathFrom B b) H R w' - w ∈
            pathFromChainSkeleton b C H R ((n : ℤ) - 1) := by
  cases n with
  | zero =>
    have h : cellPathChain H R τ 0 = fun q ↦ cubicalChainModuleLinearMap (G' := H) R
        (MoorePathBetween.toMoorePathFrom b _) (pathChainPoint R (zeroCellPath τ q)) :=
      funext (cellPathChain_zero_eq τ)
    rw [Nat.cast_zero, zero_sub, h] at hyw ⊢
    exact exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton
      (zeroCellPath τ) y w hy hw hyw
  | succ m =>
    exact
      exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton_succ
        (τ (m + 1)) y w hy hw hyw

/-- **Brown's semi-free model of the chains on the based path space of a CW complex.** Let `C` be
a CW complex in `B` containing the path component of a point `b`, for instance all of `B` when `B`
is path connected, and choose a Moore path `τ n j` from `b` to the centre of every `n`-cell `j`.
There is a Brown model `M` of `C_*(P_b B; R)` over `C_*(Ω_b B; R)` on the cells of `C`, the cell
`⟨n, j⟩` of index `n`: a semi-free twisting cocycle `m` with images `g ⟨n, j⟩` of the generators,
such that `g : K_m → C_*(P_b B; R)` is a quasi-isomorphism. Moreover:

* `g ⟨n, j⟩` is a chain over the `n`-skeleton, congruent to the chain of the cell
  `TauCeti.cellPathChain τ n j` modulo the chains over the `(n - 1)`-skeleton;
* the row of an `n`-cell only involves cells of dimension `< n`;
* for every `k`, the restriction of `g` to the cells of dimension `< k` is a quasi-isomorphism
  onto the chains over the `(k - 1)`-skeleton: relative cycles `(u, w)` with `w` over the
  `(k - 1)`-skeleton are relative boundaries `(D u', g(u') + d w')` with `u'` on the same cells
  and `w'` over the same skeleton. -/
theorem exists_semifreeModel_pathFromChain (hC : pathComponent b ⊆ C) :
    ∃ M : BrownModel B b H R (Σ n, cell C n) fun x ↦ (x.1 : ℤ),
      (∀ x, M.comparison x ∈ pathFromChainSkeleton b C H R x.1) ∧
      (∀ x, M.comparison x - cellPathChain H R τ x.1 x.2 ∈
        pathFromChainSkeleton b C H R ((x.1 : ℤ) - 1)) ∧
      (∀ x, M.cocycle.m x ∈
        supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < x.1}) ∧
      ∀ (k : ℕ) (u : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
          (w : cubicalChainModule (MoorePathFrom B b) H R),
        u ∈ supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < k} →
        rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) M.cocycle.m u = 0 →
        linearCombination (loopChainAlgebra B b R) M.comparison u =
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w →
        w ∈ pathFromChainSkeleton b C H R ((k : ℤ) - 1) →
        ∃ (u' : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
          (w' : cubicalChainModule (MoorePathFrom B b) H R),
          u' ∈ supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < k} ∧
            w' ∈ pathFromChainSkeleton b C H R ((k : ℤ) - 1) ∧
            rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
              (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
              (d := cubicalChainDifferential (MooreLoopSpace B b) R) M.cocycle.m u' = u ∧
            linearCombination (loopChainAlgebra B b R) M.comparison u' +
              cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w := by
  -- The filtration: the stage `k` is the chains over the `(k - 1)`-skeleton.
  set F : ℕ → Submodule (loopChainAlgebra B b R) (cubicalChainModule (MoorePathFrom B b) H R) :=
    fun k ↦ pathFromChainSkeleton b C H R ((k : ℤ) - 1) with hF
  have hFsucc (k : ℕ) : F (k + 1) = pathFromChainSkeleton b C H R k := by
    simp only [hF, Nat.cast_succ, add_sub_cancel_right]
  have hFmono : Monotone F := fun k l hkl ↦
    monotone_pathFromChainSkeleton b C H R (by simpa using hkl)
  obtain ⟨m, g, hgdeg, hgF, hgc, hgm, hms, hwf, hK⟩ :=
    exists_semifreeModel_of_filtration (pathFromChain_isDGLeftModule B b H R) hFmono
      (fun k ↦ isHomogeneous_pathFromChainSkeleton b C H R _)
      (fun w hw _ ↦ ⟨w, hw, by
        simp only [hF, Nat.cast_zero, zero_sub,
          pathFromChainSkeleton_eq_bot_of_neg (by norm_num : (-1 : ℤ) < 0), Submodule.mem_bot] at hw
        rw [hw, map_zero]⟩)
      (cellPathChain_mem_cubicalChainModuleGrading τ)
      (fun k j ↦ hFsucc k ▸ cellPathChain_mem_pathFromChainSkeleton τ k j)
      (cubicalChainModuleDifferential_cellPathChain_mem_pathFromChainSkeleton τ)
      (fun k y w hy hw hyw ↦ by
        rw [hFsucc] at hw ⊢
        exact exists_mapRange_eq_and_linearCombination_cellPathChain_add_differential_sub_mem
          τ k y w hy hw hyw)
  refine ⟨⟨m, hwf, g, hgdeg, hgm, fun u w hu huw ↦ ?_⟩, fun x ↦ hFsucc x.1 ▸ hgF x, hgc, hms, hK⟩
  -- A chain on the based path space lies over a finite skeleton, so in some stage `F k`.
  have hFex (w : cubicalChainModule (MoorePathFrom B b) H R) : ∃ k, w ∈ F k := by
    have hw : w ∈ ⨆ q, pathFromChainSkeleton b C H R q := by
      rw [iSup_pathFromChainSkeleton_eq_top b H R hC]
      exact Submodule.mem_top
    obtain ⟨q, hq⟩ := (Submodule.mem_iSup_of_directed _
      (monotone_pathFromChainSkeleton b C H R).directed_le).1 hw
    refine ⟨q.toNat + 1, monotone_pathFromChainSkeleton b C H R ?_ hq⟩
    push_cast
    lia
  obtain ⟨k, hk⟩ := hFex w
  obtain ⟨u', w', -, hu', huw'⟩ := exists_rowFiniteTwistedDifferential_eq_of_forall_mem_supported
    m.m Sigma.fst hFmono (fun k f w hf hDf hfw hw ↦ by
      obtain ⟨f', w', -, hw', hf', hfw'⟩ := hK k f w hf hDf hfw hw
      exact ⟨f', w', hw', hf', hfw'⟩) hu huw (Submodule.mem_iSup_of_mem k hk)
  exact ⟨u', w', hu', huw'⟩

variable (H R) in
/-- **Brown's model of a CW complex**: a choice of the Brown model of
`TauCeti.exists_semifreeModel_pathFromChain` of the chains `C_*(P_b B; R)` on the based path space,
for a CW complex `C` in `B` containing the path component of `b` (for instance all of `B` when `B`
is path connected) and Moore paths `τ n j` from `b` to the centres of the cells. It has one free
generator for each cell of `C`, of index the dimension of the cell. Any two such models, for
instance for two choices of paths or two CW structures, are homologous
(`TauCeti.BrownModel.exists_rowFiniteHomologous_homotopy`), and each computes the derived tensor
product with `R` (`TauCeti.BrownModel.nonempty_localizedFunctor_iso_derivedTensor`). -/
def brownModel (hC : pathComponent b ⊆ C) : BrownModel B b H R (Σ n, cell C n) fun x ↦ (x.1 : ℤ) :=
  (exists_semifreeModel_pathFromChain τ hC).choose

/-- The generator of an `n`-cell in Brown's model of a CW complex goes to a chain over the
`n`-skeleton. -/
theorem brownModel_comparison_mem_pathFromChainSkeleton (hC : pathComponent b ⊆ C)
    (x : Σ n, cell C n) :
    (brownModel H R τ hC).comparison x ∈ pathFromChainSkeleton b C H R x.1 :=
  (exists_semifreeModel_pathFromChain τ hC).choose_spec.1 x

/-- The generator of an `n`-cell in Brown's model of a CW complex goes to the chain of the cell
`TauCeti.cellPathChain τ n j`, modulo the chains over the `(n - 1)`-skeleton. -/
theorem brownModel_comparison_sub_cellPathChain_mem_pathFromChainSkeleton (hC : pathComponent b ⊆ C)
    (x : Σ n, cell C n) :
    (brownModel H R τ hC).comparison x - cellPathChain H R τ x.1 x.2 ∈
      pathFromChainSkeleton b C H R ((x.1 : ℤ) - 1) :=
  (exists_semifreeModel_pathFromChain τ hC).choose_spec.2.1 x

/-- The row of an `n`-cell in Brown's model of a CW complex only involves cells of dimension
`< n`. -/
theorem brownModel_cocycle_m_mem_supported (hC : pathComponent b ⊆ C) (x : Σ n, cell C n) :
    (brownModel H R τ hC).cocycle.m x ∈
      supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < x.1} :=
  (exists_semifreeModel_pathFromChain τ hC).choose_spec.2.2.1 x

/-- **Brown's model of a CW complex respects the skeleta.** For every `k`, the restriction of its
comparison to the cells of dimension `< k` is a quasi-isomorphism onto the chains over the
`(k - 1)`-skeleton: relative cycles `(u, w)` with `w` over the `(k - 1)`-skeleton are relative
boundaries `(D u', g(u') + d w')` with `u'` on the same cells and `w'` over the same skeleton. -/
theorem exists_differential_eq_and_brownModel_comparison_add_eq_of_mem_supported
    (hC : pathComponent b ⊆ C) (k : ℕ) (u : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
    (w : cubicalChainModule (MoorePathFrom B b) H R)
    (hu : u ∈ supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < k})
    (hDu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) (brownModel H R τ hC).cocycle.m u = 0)
    (huw : linearCombination (loopChainAlgebra B b R) (brownModel H R τ hC).comparison u =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R w)
    (hw : w ∈ pathFromChainSkeleton b C H R ((k : ℤ) - 1)) :
    ∃ (u' : (Σ n, cell C n) →₀ loopChainAlgebra B b R)
      (w' : cubicalChainModule (MoorePathFrom B b) H R),
      u' ∈ supported (loopChainAlgebra B b R) (loopChainAlgebra B b R) {y | y.1 < k} ∧
        w' ∈ pathFromChainSkeleton b C H R ((k : ℤ) - 1) ∧
        rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R)
          (brownModel H R τ hC).cocycle.m u' = u ∧
        linearCombination (loopChainAlgebra B b R) (brownModel H R τ hC).comparison u' +
          cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w :=
  (exists_semifreeModel_pathFromChain τ hC).choose_spec.2.2.2 k u w hu hDu huw hw

/-- **Brown's model of a CW complex does not depend on the choices.** For two CW complexes `C` and
`C'` in `B` containing the path component of `b`, for instance two CW structures on `B`, any
choices of Moore paths `τ` and `τ'` from `b` to the centres of their cells and any two phantom
parameters `H` and `H'` of the chains on the path space, the cocycles of the two Brown models are
homologous, so their twisted complexes with coefficients in any DG right module are homotopy
equivalent (`TauCeti.RowFiniteHomologous.homotopyEquiv`), through specified continuation maps. -/
theorem nonempty_rowFiniteHomologous_brownModel_brownModel (hC : pathComponent b ⊆ C) {C' : Set B}
    [CWComplex C'] {H' : Type*} (τ' : ∀ (n : ℕ) (j : cell C' n), MoorePathBetween B b (map n j 0))
    (hC' : pathComponent b ⊆ C') :
    Nonempty (RowFiniteHomologous (loopChain_isDGAlgebra B b R) (brownModel H R τ hC).cocycle
      (brownModel H' R τ' hC').cocycle) := by
  obtain ⟨E, -⟩ := (brownModel H R τ hC).exists_rowFiniteHomologous_homotopy
    ((brownModel H' R τ' hC').changePhantom H)
  rw [BrownModel.changePhantom_cocycle] at E
  exact ⟨E⟩

/-! ### Complexes that are not path connected -/

variable (b) in
/-- A Moore path from `b` to the centre of every cell of the path component of `b` in the CW complex
`C`, the subcomplex `Topology.CWComplex.pathComponentInSubcomplex C b`, whose cells have their
centres joined to `b` inside `C`. -/
def pathComponentCellPath (n : ℕ) (j : cell (CWComplex.pathComponentInSubcomplex C b : Set B) n) :
    MoorePathBetween B b (map n j 0) :=
  (nonempty_moorePathBetween_iff.2
    ((CWComplex.mem_pathComponentInSubcomplex_I_iff C).1 j.property).joined).some

variable (H R) in
/-- **Brown's model of a CW complex that need not be path connected.** Let `C` be a CW complex in
`B` containing the path component of `b`. The paths from `b` never leave the path component of `b`,
so the chains `C_*(P_b B; R)` are modelled by the cells of that path component alone, which form
the subcomplex `Topology.CWComplex.pathComponentInSubcomplex C b`: this is Brown's model
`TauCeti.brownModel` of that subcomplex, with the paths `TauCeti.pathComponentCellPath` to its
cells. On a CW complex `B` with several path components, a basepoint chosen in each of them gives
one such model for each component, and their generators together are the cells of `B`, each once
(`Topology.CWComplex.sigmaPathComponentCellEquiv`). -/
def pathComponentBrownModel (hC : pathComponent b ⊆ C) :
    BrownModel B b H R (Σ n, cell (CWComplex.pathComponentInSubcomplex C b : Set B) n)
      fun x ↦ (x.1 : ℤ) :=
  brownModel H R (pathComponentCellPath b)
    (CWComplex.pathComponent_subset_pathComponentInSubcomplex C hC)

/-- Brown's model on the path component of `b` is Brown's model `TauCeti.brownModel` of the
subcomplex `Topology.CWComplex.pathComponentInSubcomplex C b`, with the paths
`TauCeti.pathComponentCellPath`, so the properties of `TauCeti.brownModel` apply to it. -/
theorem pathComponentBrownModel_eq (hC : pathComponent b ⊆ C) :
    pathComponentBrownModel H R hC = brownModel H R (pathComponentCellPath b)
      (CWComplex.pathComponent_subset_pathComponentInSubcomplex C hC) :=
  (rfl)

end TauCeti
