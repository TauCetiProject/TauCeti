/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# The Serre filtration of cubical chains

Let `p : E → B` be a map.  Following Serre, *Homologie singulière des espaces fibrés*,
Chapter II, a singular `n`-cube `c : Iⁿ → E` has **Serre weight at most `s`** when `s ≥ 0` and
`p ∘ c` depends only on the first `s` coordinates, that is, does not depend on the last `n - s`
ones (`TauCeti.SingularCube.IsSerreWeightLE`).  A face of such a cube again has weight at most
`s`: fixing a coordinate among the first `s` leaves `p ∘ c` depending on the first `s - 1`
coordinates of the face, and fixing a later coordinate leaves the first `s` coordinates alone.
Hence the chains of the cubes of weight at most `s` are preserved by the boundary, and so are
their images in the normalized cubical chains.  This increasing filtration is

* zero for `s < 0`, while `F_0` is spanned by the cubes whose composite with `p` is constant,
  each lying in some fiber;
* everything in degrees `n ≤ s`, so it is finite in each degree;
* natural in maps from `p` to another map `p' : E' → B'`, covering any map of bases.

Serre normalizes cubical chains by the cubes independent of their last coordinate, while the
normalized chains of `TauCeti.AlgebraicTopology.Singular.Cubical.Normalized` divide out the cubes
independent of any coordinate (Massey's convention).  The filtration is defined on the
unnormalized chains, where the two conventions do not intervene, and transported to the
normalized chains as an image.  The Serre spectral sequence is the spectral sequence of this
filtration of the normalized cubical chain complex.

## Main definitions

* `TauCeti.SingularCube.IsSerreWeightLE p s c`: the cube `c` has Serre weight at most `s`.
* `TauCeti.CubicalChain.serreFiltration`, `TauCeti.NormalizedCubicalChain.serreFiltration`: the
  filtration on chains, as submodules.

## Main results

* `TauCeti.SingularCube.IsSerreWeightLE.face`: faces do not increase the Serre weight.
* `TauCeti.CubicalChain.boundary_mem_serreFiltration`,
  `TauCeti.NormalizedCubicalChain.boundary_mem_serreFiltration`: the boundary preserves the
  filtration.
* `TauCeti.NormalizedCubicalChain.serreFiltration_mono`,
  `TauCeti.NormalizedCubicalChain.serreFiltration_eq_bot`,
  `TauCeti.NormalizedCubicalChain.serreFiltration_eq_top`: the filtration is increasing, zero
  below `0`, and everything in degrees at most `s`.
* `TauCeti.NormalizedCubicalChain.map_mem_serreFiltration`: naturality in maps of maps.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980.
* J. McCleary, *A User's Guide to Spectral Sequences*, Chapter 5.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

variable {E B E' B' : Type*} [TopologicalSpace E] [TopologicalSpace E']

namespace SingularCube

/-- A singular cube `c` of `E` has **Serre weight at most `s`** over `p : E → B` when `s ≥ 0` and
`p ∘ c` depends only on the coordinates of index less than `s`. -/
structure IsSerreWeightLE (p : E → B) (s : ℤ) {n : ℕ} (c : SingularCube E n) : Prop where
  /-- The weight bound is nonnegative. -/
  nonneg : 0 ≤ s
  /-- `p ∘ c` depends only on the coordinates of index less than `s`. -/
  dependsOn : DependsOn (p ∘ c) {i : Fin n | (i : ℤ) < s}

variable {p : E → B} {s t : ℤ} {n : ℕ}

/-- The Serre weight bound is monotone in the bound. -/
theorem IsSerreWeightLE.mono {c : SingularCube E n} (h : c.IsSerreWeightLE p s) (hst : s ≤ t) :
    c.IsSerreWeightLE p t :=
  ⟨h.nonneg.trans hst, h.dependsOn.mono fun i (hi : i ∈ {i : Fin n | (i : ℤ) < s}) ↦ by
    rw [Set.mem_ofPred_eq] at hi ⊢
    exact hi.trans_le hst⟩

/-- No cube has negative Serre weight. -/
theorem not_isSerreWeightLE_of_neg (c : SingularCube E n) (hs : s < 0) : ¬ c.IsSerreWeightLE p s :=
  fun h ↦ (h.nonneg.trans_lt hs).false

/-- Every `n`-cube has Serre weight at most `s` for `s ≥ n`. -/
theorem isSerreWeightLE_of_le (c : SingularCube E n) (hs : (n : ℤ) ≤ s) :
    c.IsSerreWeightLE p s :=
  ⟨(Int.natCast_nonneg n).trans hs, (dependsOn_univ _).mono fun i _ ↦
    Set.mem_ofPred.2 ((Int.ofNat_lt.2 i.2).trans_le hs)⟩

/-- A face of a cube of Serre weight at most `s` has Serre weight at most `s`. -/
theorem IsSerreWeightLE.face {c : SingularCube E (n + 1)} (h : c.IsSerreWeightLE p s)
    (i : Fin (n + 1)) (t : I) : (face i t c).IsSerreWeightLE p s := by
  refine ⟨h.nonneg, fun x y hxy ↦ ?_⟩
  simp only [Function.comp_apply, face_apply]
  refine h.dependsOn fun j (hj : (j : ℤ) < s) ↦ ?_
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
  · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    refine hxy k (lt_of_le_of_lt ?_ hj)
    exact_mod_cast Fin.le_iff_val_le_val.1 (Fin.castSucc_le_succAbove i k)

/-- A map from `p` to `p'`, that is `f` and `b` with `p' ∘ f = b ∘ p`, preserves the Serre
weight. -/
theorem IsSerreWeightLE.comp {c : SingularCube E n} (h : c.IsSerreWeightLE p s) (f : C(E, E'))
    {p' : E' → B'} {b : B → B'} (hf : p' ∘ f = b ∘ p) : IsSerreWeightLE p' s (f.comp c) := by
  refine ⟨h.nonneg, fun x y hxy ↦ ?_⟩
  rw [ContinuousMap.coe_comp, ← Function.comp_assoc, hf, Function.comp_assoc]
  exact congrArg b (h.dependsOn hxy)

end SingularCube

namespace CubicalChain

section Semiring

variable (R : Type*) [Semiring R] (p : E → B)

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

/-- A map from `p` to `p'`, that is `f` and `b` with `p' ∘ f = b ∘ p`, preserves the Serre
filtration. -/
theorem map_mem_serreFiltration {s : ℤ} {n : ℕ} (f : C(E, E')) {p' : E' → B'} {b : B → B'}
    (hf : p' ∘ f = b ∘ p) {g : CubicalChain E R n} (hg : g ∈ serreFiltration R p s n) :
    map R f n g ∈ serreFiltration R p' s n := by
  exact map_mem_supported R f (fun (c : SingularCube E n) (hc : c.IsSerreWeightLE p s) ↦
    hc.comp f hf) hg

/-- Below `0`, the Serre filtration is zero. -/
@[simp]
theorem serreFiltration_eq_bot {s : ℤ} (hs : s < 0) (n : ℕ) : serreFiltration R p s n = ⊥ := by
  rw [serreFiltration, Finsupp.supported_eq_span_single, Submodule.span_eq_bot]
  rintro _ ⟨c, hc, rfl⟩
  exact (c.not_isSerreWeightLE_of_neg hs hc).elim

/-- In degrees `n ≤ s`, the Serre filtration is everything. -/
@[simp]
theorem serreFiltration_eq_top {s : ℤ} {n : ℕ} (hs : (n : ℤ) ≤ s) :
    serreFiltration R p s n = ⊤ := by
  rw [serreFiltration, ← Finsupp.supported_univ]
  congr 1
  exact Set.eq_univ_of_forall fun c ↦ c.isSerreWeightLE_of_le hs

end Semiring

section Ring

variable {R : Type*} [Ring R] {p : E → B}

/-- The boundary preserves the Serre filtration. -/
theorem boundary_mem_serreFiltration {s : ℤ} {n : ℕ} {f : CubicalChain E R (n + 1)}
    (hf : f ∈ serreFiltration R p s (n + 1)) : boundary E R n f ∈ serreFiltration R p s n := by
  rw [serreFiltration, Finsupp.supported_eq_span_single] at hf
  refine Submodule.span_le (p := (serreFiltration R p s n).comap (boundary E R n)) |>.2 ?_ hf
  rintro _ ⟨c, hc, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, boundary_single]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.sub_mem _
    (single_mem_serreFiltration (hc.face i 0) 1) (single_mem_serreFiltration (hc.face i 1) 1))

end Ring

end CubicalChain

namespace NormalizedCubicalChain

open CubicalChain

variable (R : Type*) [Ring R] (p : E → B)

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

/-- A map from `p` to `p'`, that is `f` and `b` with `p' ∘ f = b ∘ p`, preserves the Serre
filtration. -/
theorem map_mem_serreFiltration {s : ℤ} {n : ℕ} (f : C(E, E')) {p' : E' → B'} {b : B → B'}
    (hf : p' ∘ f = b ∘ p) {g : NormalizedCubicalChain E R n} (hg : g ∈ serreFiltration R p s n) :
    map R f n g ∈ serreFiltration R p' s n := by
  obtain ⟨g, hg, rfl⟩ := hg
  exact ⟨_, CubicalChain.map_mem_serreFiltration f hf hg, (map_mk R f g).symm⟩

/-- Below `0`, the Serre filtration is zero. -/
@[simp]
theorem serreFiltration_eq_bot {s : ℤ} (hs : s < 0) (n : ℕ) : serreFiltration R p s n = ⊥ := by
  rw [serreFiltration, CubicalChain.serreFiltration_eq_bot hs, Submodule.map_bot]

/-- In degrees `n ≤ s`, the Serre filtration is everything. -/
@[simp]
theorem serreFiltration_eq_top {s : ℤ} {n : ℕ} (hs : (n : ℤ) ≤ s) :
    serreFiltration R p s n = ⊤ := by
  rw [serreFiltration, CubicalChain.serreFiltration_eq_top hs, Submodule.map_top,
    Submodule.range_mkQ]

end NormalizedCubicalChain

end TauCeti
