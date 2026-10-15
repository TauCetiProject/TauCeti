/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.Embedding.ExtendSubobject
public import TauCeti.Algebra.Homology.ModuleCat.Subcomplex
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.Subobject
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex

/-!
# The Serre filtration of cubical chains

Let `p : E → B` be a continuous map.  Following Serre, *Homologie singulière des espaces fibrés*,
Chapter II, a singular `n`-cube `c : Iⁿ → E` has **Serre weight at most `s`** when `s ≥ 0` and
`p ∘ c` depends only on the first `s` coordinates, that is, does not depend on the last `n - s`
ones (`TauCeti.SingularCube.IsSerreWeightLE`).  A face of such a cube again has weight at most
`s`: fixing a coordinate among the first `s` leaves `p ∘ c` depending on the first `s - 1`
coordinates of the face, and fixing a later coordinate leaves the first `s` coordinates alone.
Hence the chains of the cubes of weight at most `s` form a subcomplex `F_s` of the cubical chains
of `E`, and their images form a subcomplex of the normalized cubical chains.  This increasing
filtration is

* zero for `s < 0`, while `F_0` is spanned by the cubes whose composite with `p` is constant,
  each lying in some fibre;
* everything in degrees `n ≤ s`, so it is finite in each degree;
* natural in maps over `B`.

Serre normalizes cubical chains by the cubes independent of their last coordinate, while the
normalized chains of `TauCeti.AlgebraicTopology.Singular.Cubical.Normalized` divide out the cubes
independent of any coordinate (Massey's convention).  The filtration is defined on the
unnormalized chains, where the two conventions do not intervene, and transported to the
normalized chains as an image.

The spectral sequence of a filtered complex is set up for cochain complexes indexed by `ℤ`, so the
chain complex indexed by `ℕ` is extended along `ComplexShape.embeddingUpIntLE 0`: chains of degree
`n` sit in cochain degree `-n`.  The **Serre spectral sequence** is the spectral sequence of the
resulting filtration (`TauCeti.serreSpectralSequence`).  In Mathlib's numbering, where the first
page is page `2`, the object at `(p, q)` is `H^{p+q}(F_{q+1}/F_q)`, that is Serre's `E¹_{s,t}`
with `s = q + 1` and `s + t = -(p + q)`.  Since the filtration is finite in each degree, the
spectral sequence converges strongly to the homology of the cubical chains of `E`
(`TauCeti.serreSpectralSequencePageXIsoGraded`, `TauCeti.serreAbutmentIso`), which is the singular
homology of `E` by `TauCeti.singularCubicalHomologyIso`.

## Main definitions

* `TauCeti.SingularCube.IsSerreWeightLE p s c`: the cube `c` has Serre weight at most `s`.
* `TauCeti.CubicalChain.serreFiltration`, `TauCeti.NormalizedCubicalChain.serreFiltration`: the
  filtration on chains, as submodules.
* `TauCeti.serreFiltration R p s`: the Serre filtration of the cubical cochain complex of `E`, by
  subcomplexes.
* `TauCeti.serreSpectralSequence R p`: the Serre spectral sequence, with its first page
  `TauCeti.serreSpectralSequenceFirstPageXIsoCokernel`.

## Main results

* `TauCeti.SingularCube.IsSerreWeightLE.face`: faces do not increase the Serre weight.
* `TauCeti.NormalizedCubicalChain.boundary_mem_serreFiltration`: the filtration is by
  subcomplexes.
* `TauCeti.monotone_serreFiltration`, `TauCeti.serreFiltration_eq_bot`,
  `TauCeti.epi_serreFiltration_arrow_f`: the filtration is increasing, zero below `0`, and
  everything in cochain degrees `m ≥ -s`.
* `TauCeti.mem_range_serreFiltration_arrow_f_iff`: in cochain degree `-n`, the `s`-th piece
  consists of the normalized `n`-chains in `NormalizedCubicalChain.serreFiltration`.
* `TauCeti.serreFiltration_factors`: naturality in maps over `B`.
* `TauCeti.serreSpectralSequencePageXIsoGraded`, `TauCeti.isZero_serreAbutmentFiltration`,
  `TauCeti.isIso_serreAbutmentFiltrationι`, `TauCeti.serreAbutmentIso`: strong convergence to
  the homology of the cubical chains of `E`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980.
* J. McCleary, *A User's Guide to Spectral Sequences*, Chapter 5.
-/

public section

noncomputable section

open CategoryTheory Limits unitInterval

namespace TauCeti

variable {E B E' : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E']

namespace SingularCube

/-- A singular cube `c` of `E` has **Serre weight at most `s`** over `p : E → B` when `s ≥ 0` and
`p ∘ c` depends only on the coordinates of index less than `s`. -/
def IsSerreWeightLE (p : C(E, B)) (s : ℤ) {n : ℕ} (c : SingularCube E n) : Prop :=
  0 ≤ s ∧ ∀ x y : Fin n → I, (∀ i : Fin n, (i : ℤ) < s → x i = y i) → p (c x) = p (c y)

variable {p : C(E, B)} {s t : ℤ} {n : ℕ}

/-- The characterization of a cube of Serre weight at most `s`: `s ≥ 0`, and `p ∘ c` takes the
same value at two points which agree in their coordinates of index less than `s`. -/
theorem isSerreWeightLE_iff {c : SingularCube E n} : c.IsSerreWeightLE p s ↔
    0 ≤ s ∧ ∀ x y : Fin n → I, (∀ i : Fin n, (i : ℤ) < s → x i = y i) → p (c x) = p (c y) := by
  rw [IsSerreWeightLE]

/-- The Serre weight bound is monotone in the bound. -/
theorem IsSerreWeightLE.mono {c : SingularCube E n} (h : c.IsSerreWeightLE p s) (hst : s ≤ t) :
    c.IsSerreWeightLE p t := by
  rw [isSerreWeightLE_iff] at h ⊢
  exact ⟨h.1.trans hst, fun x y hxy ↦ h.2 x y fun i hi ↦ hxy i (hi.trans_le hst)⟩

/-- No cube has negative Serre weight. -/
theorem not_isSerreWeightLE_of_neg (c : SingularCube E n) (hs : s < 0) : ¬ c.IsSerreWeightLE p s :=
  fun h ↦ ((isSerreWeightLE_iff.1 h).1.trans_lt hs).false

/-- Every `n`-cube has Serre weight at most `s` for `s ≥ n`. -/
theorem isSerreWeightLE_of_le (c : SingularCube E n) (hs : (n : ℤ) ≤ s) :
    c.IsSerreWeightLE p s :=
  isSerreWeightLE_iff.2 ⟨(Int.natCast_nonneg n).trans hs, fun _ _ hxy ↦
    congrArg (p ∘ c) (funext fun i ↦ hxy i ((Int.ofNat_lt.2 i.2).trans_le hs))⟩

/-- A face of a cube of Serre weight at most `s` has Serre weight at most `s`. -/
theorem IsSerreWeightLE.face {c : SingularCube E (n + 1)} (h : c.IsSerreWeightLE p s)
    (i : Fin (n + 1)) (t : I) : (face i t c).IsSerreWeightLE p s := by
  rw [isSerreWeightLE_iff] at h ⊢
  refine ⟨h.1, fun x y hxy ↦ ?_⟩
  rw [face_apply, face_apply]
  refine h.2 _ _ fun j hj ↦ ?_
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
  · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    refine hxy k (lt_of_le_of_lt ?_ hj)
    have : (k : ℕ) ≤ (i.succAbove k : ℕ) := by
      unfold Fin.succAbove
      split <;> simp
    exact_mod_cast this

/-- A map `f` over `B` preserves the Serre weight. -/
theorem IsSerreWeightLE.comp {c : SingularCube E n} (h : c.IsSerreWeightLE p s) (f : C(E, E'))
    {p' : C(E', B)} (hf : p'.comp f = p) : IsSerreWeightLE p' s (f.comp c) := by
  subst hf
  rw [isSerreWeightLE_iff] at h ⊢
  exact h

end SingularCube

namespace CubicalChain

variable (R : Type*) [Ring R] (p : C(E, B))

/-- The **Serre filtration** of the unnormalized cubical `n`-chains: the chains supported on the
cubes of Serre weight at most `s`. -/
def serreFiltration (s : ℤ) (n : ℕ) : Submodule R (CubicalChain E R n) :=
  Finsupp.supported R R {c : SingularCube E n | c.IsSerreWeightLE p s}

variable {R p}

/-- A chain lies in the `s`-th piece of the Serre filtration when every cube in its support has
Serre weight at most `s`. -/
@[simp]
theorem mem_serreFiltration_iff {s : ℤ} {n : ℕ} (f : CubicalChain E R n) :
    f ∈ serreFiltration R p s n ↔ ∀ c, f c ≠ 0 → c.IsSerreWeightLE p s := by
  rw [serreFiltration, Finsupp.mem_supported']
  exact forall_congr' fun c ↦ not_imp_comm

/-- A cube of Serre weight at most `s`, with any coefficient, lies in the `s`-th piece. -/
theorem single_mem_serreFiltration {s : ℤ} {n : ℕ} {c : SingularCube E n}
    (hc : c.IsSerreWeightLE p s) (a : R) : Finsupp.single c a ∈ serreFiltration R p s n :=
  Finsupp.single_mem_supported R a hc

/-- The Serre filtration is increasing. -/
theorem serreFiltration_mono {s t : ℤ} (hst : s ≤ t) (n : ℕ) :
    serreFiltration R p s n ≤ serreFiltration R p t n :=
  Finsupp.supported_mono fun _ hc ↦ SingularCube.IsSerreWeightLE.mono hc hst

/-- The boundary preserves the Serre filtration. -/
theorem boundary_mem_serreFiltration {s : ℤ} {n : ℕ} {f : CubicalChain E R (n + 1)}
    (hf : f ∈ serreFiltration R p s (n + 1)) : boundary E R n f ∈ serreFiltration R p s n := by
  rw [serreFiltration, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hc, rfl⟩ := hf
    rw [boundary_single]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.sub_mem _
      (single_mem_serreFiltration (hc.face i 0) 1) (single_mem_serreFiltration (hc.face i 1) 1))
  | zero => simp
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [map_smul]; exact Submodule.smul_mem _ a hf

/-- A map over `B` preserves the Serre filtration. -/
theorem map_mem_serreFiltration {s : ℤ} {n : ℕ} (f : C(E, E')) {p' : C(E', B)}
    (hf : p'.comp f = p) {g : CubicalChain E R n} (hg : g ∈ serreFiltration R p s n) :
    map R f n g ∈ serreFiltration R p' s n := by
  -- `map R f n` is `lmapDomain R R f.comp` by definition, but its body is not exposed outside
  -- its defining module, so the two are identified on single cubes.
  rw [show map R f n = Finsupp.lmapDomain R R f.comp from
    Finsupp.lhom_ext fun c a ↦ by simp]
  have hmap := Submodule.mem_map_of_mem (f := Finsupp.lmapDomain R R f.comp) hg
  rw [serreFiltration, Finsupp.lmapDomain_supported] at hmap
  exact Finsupp.supported_mono (Set.image_subset_iff.2 fun _ hc ↦ hc.comp f hf) hmap

/-- Below `0`, the Serre filtration is zero. -/
theorem serreFiltration_eq_bot {s : ℤ} (hs : s < 0) (n : ℕ) : serreFiltration R p s n = ⊥ := by
  rw [serreFiltration, Finsupp.supported_eq_span_single, Submodule.span_eq_bot]
  rintro _ ⟨c, hc, rfl⟩
  exact (c.not_isSerreWeightLE_of_neg hs hc).elim

/-- In degrees `n ≤ s`, the Serre filtration is everything. -/
theorem serreFiltration_eq_top {s : ℤ} {n : ℕ} (hs : (n : ℤ) ≤ s) :
    serreFiltration R p s n = ⊤ := by
  rw [serreFiltration, ← Finsupp.supported_univ]
  congr 1
  exact Set.eq_univ_of_forall fun c ↦ c.isSerreWeightLE_of_le hs

end CubicalChain

namespace NormalizedCubicalChain

open CubicalChain

variable (R : Type*) [Ring R] (p : C(E, B))

/-- The **Serre filtration** of the normalized cubical `n`-chains: the image of the chains
supported on the cubes of Serre weight at most `s`. -/
def serreFiltration (s : ℤ) (n : ℕ) : Submodule R (NormalizedCubicalChain E R n) :=
  (CubicalChain.serreFiltration R p s n).map (degenerate E R n).mkQ

variable {R p}

/-- A normalized chain lies in the `s`-th piece of the Serre filtration exactly when it is the
class of an unnormalized chain supported on cubes of Serre weight at most `s`. -/
@[simp]
theorem mem_serreFiltration_iff {s : ℤ} {n : ℕ} (x : NormalizedCubicalChain E R n) :
    x ∈ serreFiltration R p s n ↔ ∃ g : CubicalChain E R n,
      (∀ c, g c ≠ 0 → c.IsSerreWeightLE p s) ∧ Submodule.Quotient.mk g = x := by
  simp only [serreFiltration, Submodule.mem_map, CubicalChain.mem_serreFiltration_iff,
    Submodule.mkQ_apply]

/-- The class of a cube of Serre weight at most `s` lies in the `s`-th piece of the filtration. -/
theorem ofCube_mem_serreFiltration {s : ℤ} {n : ℕ} {c : SingularCube E n}
    (hc : c.IsSerreWeightLE p s) : ofCube E R c ∈ serreFiltration R p s n :=
  ⟨_, single_mem_serreFiltration hc 1, (ofCube_def R c).symm⟩

/-- The Serre filtration is increasing. -/
theorem serreFiltration_mono {s t : ℤ} (hst : s ≤ t) (n : ℕ) :
    serreFiltration R p s n ≤ serreFiltration R p t n :=
  Submodule.map_mono (CubicalChain.serreFiltration_mono hst n)

/-- The boundary preserves the Serre filtration: it is a filtration by subcomplexes. -/
theorem boundary_mem_serreFiltration {s : ℤ} {n : ℕ} {f : NormalizedCubicalChain E R (n + 1)}
    (hf : f ∈ serreFiltration R p s (n + 1)) : boundary E R n f ∈ serreFiltration R p s n := by
  obtain ⟨g, hg, rfl⟩ := hf
  exact ⟨_, CubicalChain.boundary_mem_serreFiltration hg, (boundary_mk R g).symm⟩

/-- A map over `B` preserves the Serre filtration. -/
theorem map_mem_serreFiltration {s : ℤ} {n : ℕ} (f : C(E, E')) {p' : C(E', B)}
    (hf : p'.comp f = p) {g : NormalizedCubicalChain E R n} (hg : g ∈ serreFiltration R p s n) :
    map R f n g ∈ serreFiltration R p' s n := by
  obtain ⟨g, hg, rfl⟩ := hg
  exact ⟨_, CubicalChain.map_mem_serreFiltration f hf hg, (map_mk R f g).symm⟩

/-- Below `0`, the Serre filtration is zero. -/
theorem serreFiltration_eq_bot {s : ℤ} (hs : s < 0) (n : ℕ) : serreFiltration R p s n = ⊥ := by
  rw [serreFiltration, CubicalChain.serreFiltration_eq_bot hs, Submodule.map_bot]

/-- In degrees `n ≤ s`, the Serre filtration is everything. -/
theorem serreFiltration_eq_top {s : ℤ} {n : ℕ} (hs : (n : ℤ) ≤ s) :
    serreFiltration R p s n = ⊤ := by
  rw [serreFiltration, CubicalChain.serreFiltration_eq_top hs, Submodule.map_top,
    Submodule.range_mkQ]

end NormalizedCubicalChain

section Complex

universe u

variable (R : Type u) [Ring R] {E B E' : TopCat.{u}} (p : E ⟶ B)

/-- The Serre filtration in chain degree `n`, as a submodule of the term of the chain complex. -/
private def serreSubmodule (s : ℤ) (n : ℕ) :
    Submodule R (((normalizedCubicalChainComplex R).obj E).X n) :=
  NormalizedCubicalChain.serreFiltration R p.hom s n

/-- The Serre filtration of the normalized cubical chain complex of `E`, indexed by `ℕ`, by
subcomplexes. -/
def serreChainFiltration (s : ℤ) : Subobject ((normalizedCubicalChainComplex R).obj E) :=
  HomologicalComplex.subobjectOfSubmodules _ (serreSubmodule R p s) fun i j x hx ↦ by
      by_cases hij : i = j + 1
      · subst hij
        exact (congrArg (· ∈ NormalizedCubicalChain.serreFiltration R p.hom s j)
          (normalizedCubicalChainComplex_obj_d_apply E j x)).mpr
            (NormalizedCubicalChain.boundary_mem_serreFiltration hx)
      · rw [HomologicalComplex.shape _ _ _ (fun (h : (ComplexShape.down ℕ).Rel i j) ↦ hij h.symm)]
        exact Submodule.zero_mem _

/-- The **Serre filtration** of the cubical chains of `E`, as a filtration by subcomplexes of the
normalized cubical chain complex placed in nonpositive cochain degrees: its `s`-th piece is
spanned in cochain degree `-n` by the classes of the singular `n`-cubes of Serre weight at most
`s`. -/
def serreFiltration (s : ℤ) :
    Subobject (((normalizedCubicalChainComplex R).obj E).extend
      (ComplexShape.embeddingUpIntLE 0)) :=
  (serreChainFiltration R p s).extend _

variable {R p}

/-- In chain degree `n`, the `s`-th piece of the Serre filtration of the chain complex consists
of the elements of `NormalizedCubicalChain.serreFiltration`. -/
theorem mem_range_serreChainFiltration_arrow_f_iff (s : ℤ) (n : ℕ)
    (x : NormalizedCubicalChain E R n) :
    x ∈ LinearMap.range ((serreChainFiltration R p s).arrow.f n).hom ↔
      x ∈ NormalizedCubicalChain.serreFiltration R p.hom s n := by
  rw [serreChainFiltration]
  exact HomologicalComplex.mem_range_subobjectOfSubmodules_arrow_f_iff
    ((normalizedCubicalChainComplex R).obj E) (serreSubmodule R p s) _ n x

/-- In cochain degree `-n`, the `s`-th piece of the Serre filtration consists of the elements whose
image in the normalized cubical `n`-chains, under the identification of the extended complex with
the chain complex, lies in `NormalizedCubicalChain.serreFiltration`. -/
theorem mem_range_serreFiltration_arrow_f_iff (s : ℤ) (n : ℕ)
    (x : (((normalizedCubicalChainComplex R).obj E).extend
      (ComplexShape.embeddingUpIntLE 0)).X (-n)) :
    x ∈ LinearMap.range ((serreFiltration R p s).arrow.f (-n)).hom ↔
      (((normalizedCubicalChainComplex R).obj E).extendXIso _
        (by simp : (ComplexShape.embeddingUpIntLE 0).f n = -n)).hom x ∈
          NormalizedCubicalChain.serreFiltration R p.hom s n := by
  rw [serreFiltration, Subobject.mem_range_extend_arrow_f_iff _ _ (i := n) (by simp)]
  -- The term of the chain complex in degree `n` is the module of normalized chains by
  -- definition (`normalizedCubicalChainComplex_obj_X`).
  exact mem_range_serreChainFiltration_arrow_f_iff s n _

variable (R p) in
/-- The Serre filtration is increasing. -/
theorem monotone_serreFiltration : Monotone (serreFiltration R p) := fun _ _ hst ↦
  Subobject.extend_mono _ (HomologicalComplex.subobjectOfSubmodules_mono fun n ↦
    NormalizedCubicalChain.serreFiltration_mono hst n)

/-- Below `0`, the Serre filtration is zero. -/
theorem serreFiltration_eq_bot {s : ℤ} (hs : s < 0) : serreFiltration R p s = ⊥ := by
  rw [serreFiltration, serreChainFiltration, HomologicalComplex.subobjectOfSubmodules_eq_bot _ _ _
    fun n ↦ NormalizedCubicalChain.serreFiltration_eq_bot (R := R) (p := p.hom) hs n,
    Subobject.extend_bot]

/-- In cochain degrees `m ≥ -s`, that is in chain degrees at most `s`, the `s`-th piece of the
Serre filtration is everything. -/
theorem epi_serreFiltration_arrow_f {s m : ℤ} (hm : -s ≤ m) :
    Epi ((serreFiltration R p s).arrow.f m) := by
  by_cases h : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE 0).f n = m
  · obtain ⟨n, hn⟩ := h
    have : Epi ((serreChainFiltration R p s).arrow.f n) :=
      HomologicalComplex.epi_subobjectOfSubmodules_arrow_f _ _ _
        (NormalizedCubicalChain.serreFiltration_eq_top (by simp at hn; lia))
    exact Subobject.epi_extend_arrow_f _ _ hn
  · exact Subobject.epi_extend_arrow_f_of_notMem _ _ fun n hn ↦ h ⟨n, hn⟩

/-- **Naturality of the Serre filtration** in maps over `B`: a map `f : E ⟶ E'` with
`f ≫ p' = p` carries the `s`-th piece of the filtration of `E` into that of `E'`. -/
theorem serreFiltration_factors (f : E ⟶ E') {p' : E' ⟶ B} (hf : f ≫ p' = p) (s : ℤ) :
    (serreFiltration R p' s).Factors ((serreFiltration R p s).arrow ≫
      HomologicalComplex.extendMap ((normalizedCubicalChainComplex R).map f) _) :=
  Subobject.extend_factors _ _ (HomologicalComplex.subobjectOfSubmodules_factors _
    fun _ _ hx ↦ NormalizedCubicalChain.map_mem_serreFiltration f.hom
      (congrArg TopCat.Hom.hom hf) hx)

variable (R p) in
/-- The **Serre spectral sequence** of `p : E ⟶ B`: the spectral sequence of the Serre filtration
of the cubical chains of `E`.  On its first page, numbered `2`, the object at `(p, q)` is the
cohomology `H^{p+q}(F_{q+1} / F_q)` of a graded piece of the filtration
(`TauCeti.serreSpectralSequenceFirstPageXIsoCokernel`). -/
def serreSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor (serreFiltration R p) (monotone_serreFiltration R p))

/-- The first page of the Serre spectral sequence, numbered `2`: at `pq = (p, q)` it is the
cohomology `H^{p+q}(F_{q+1} / F_q)` of a graded piece of the Serre filtration. -/
def serreSpectralSequenceFirstPageXIsoCokernel (pq : ℤ × ℤ) :
    ((serreSpectralSequence R p).page 2).X pq ≅
      (cokernel ((CochainComplex.filtrationFunctor (serreFiltration R p)
        (monotone_serreFiltration R p)).map (homOfLE
          (CochainComplex.coe_le_coe_of_eq_add_one (rfl : pq.2 = pq.2) rfl)))).homology
            (pq.1 + pq.2) :=
  eqToIso (by rw [serreSpectralSequence]) ≪≫
    CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq _ _ rfl rfl _ rfl

/-- **Strong convergence of the Serre spectral sequence.** On every page `r ≥ 2` with
`q - r + 2 < 0` and `-(q + r - 1) ≤ p + q - 1`, the object at `pq = (p, q)` is the graded piece
`F_{q+1} H^{p+q} / F_q H^{p+q}` of the filtration of the abutment, the homology of the cubical
chains of `E` in degree `-(p + q)` (`TauCeti.serreAbutmentIso`). -/
def serreSpectralSequencePageXIsoGraded (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (h₀ : pq.2 - r + 2 < 0) (h₃ : -(pq.2 + r - 1) ≤ pq.1 + pq.2 - 1) :
    ((serreSpectralSequence R p).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor
        (serreFiltration R p) (monotone_serreFiltration R p))).abutmentFiltrationMap pq.2
          (pq.1 + pq.2)) :=
  have : Epi ((serreFiltration R p (pq.2 + r - 1)).arrow.f (pq.1 + pq.2 - 1)) :=
    epi_serreFiltration_arrow_f h₃
  eqToIso (by rw [serreSpectralSequence]) ≪≫
  CochainComplex.filtrationSpectralSequencePageXIsoEInfty _ _ r hr pq _ rfl
    ((serreFiltration R p _).isZero_homology_of_eq_bot (serreFiltration_eq_bot h₀) _)
    ((serreFiltration R p _).isZero_homology_cokernel_of_epi_arrow_f _) ≪≫
    (CochainComplex.spectralObject _).EInftyIsoCokernel _ _

/-- The filtration of the abutment of the Serre spectral sequence is zero at `-1`. -/
theorem isZero_serreAbutmentFiltration (n : ℤ) :
    IsZero ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor (serreFiltration R p)
      (monotone_serreFiltration R p))).abutmentFiltration (-1) n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration _ _ (serreFiltration_eq_bot (by norm_num)) n

/-- The filtration of the abutment of the Serre spectral sequence in degree `n` is everything at
every `b ≥ -n`. -/
theorem isIso_serreAbutmentFiltrationι {b n : ℤ} (hb : -b ≤ n) :
    IsIso ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor (serreFiltration R p)
      (monotone_serreFiltration R p))).abutmentFiltrationι b n) :=
  have : Epi ((serreFiltration R p b).arrow.f n) := epi_serreFiltration_arrow_f hb
  Abelian.SpectralObject.isIso_abutmentFiltrationι _
    (CochainComplex.isZero_spectralObject_H_top _ _ b n
      ((serreFiltration R p b).isZero_homology_cokernel_of_epi_arrow_f n))

variable (R p) in
/-- The abutment of the Serre spectral sequence in cochain degree `-n` is the homology of the
normalized cubical chains of `E` in degree `n`. -/
def serreAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor (serreFiltration R p)
      (monotone_serreFiltration R p))).abutment (-n) ≅
      ((normalizedCubicalChainComplex R).obj E).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ (-n) ≪≫
    ((normalizedCubicalChainComplex R).obj E).extendHomologyIso _ (by simp)

end Complex

end TauCeti
