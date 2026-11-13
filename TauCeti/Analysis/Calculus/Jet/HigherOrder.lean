/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
public import TauCeti.Analysis.Calculus.Jet.Nonlinear
import TauCeti.Analysis.Calculus.ContDiff.TaylorInverse
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
import TauCeti.Analysis.Calculus.Jet.Realization

/-!
# Nonlinear higher-order jet coordinate changes

In local bundle coordinates an `r`-jet at a base point is represented by a tuple
`j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F` of value and derivative data through order `r`, where
`j 0 0` is the field value. If `h : E' → E` changes base coordinates and `g : E' × F → G` changes
fibre coordinates (possibly nonlinearly and depending on the base point), a local section `s`
transforms into `y ↦ g (y, s (h y))`.

We package `j` into its unnormalized formal Taylor series `TauCeti.jetSeries` (without factorial
denominators, matching `ftaylorSeries`, in contrast to the factorial-normalized power series
`TauCeti.finiteJetSeries` in `Realization.lean`) and define `TauCeti.jetCoordChange` by Faà di
Bruno composition along the graph formal series
`(FormalMultilinearSeries.id 𝕜 E' x).prod ((jetSeries r j).taylorComp (ftaylorSeries 𝕜 h x))`.

The main results are:

* `TauCeti.firstJetCoordChange_eq_jetCoordChange`: compatibility with `TauCeti.firstJetCoordChange`
  at order `1`;
* `TauCeti.jetTruncate_jetCoordChange`: naturality with respect to jet truncation `jetTruncate`;
* `TauCeti.jetCoordChange_iteratedFDeriv`: the higher-order chain rule on `C^r` local sections;
* `TauCeti.jetCoordChange_id`, `TauCeti.jetCoordChange_comp`, `TauCeti.jetCoordChange_inverse`:
  identity, cocycle, and local germ-inverse laws for arbitrary jet tuples;
* `TauCeti.jetCoordChange_comp_perm`: preservation of slot symmetry;
* `TauCeti.jetCoordChange_sub_of_eq_lt` and `TauCeti.jetCoordChange_last_sub`: when two jets agree
  strictly below a positive order, all nonlinear partition terms cancel and their difference at
  that order transforms linearly by the vertical derivative of `g` and the base derivative of `h`
  (exhibiting the affine bundle model `J^{r+1}E → J^rE`);
* `TauCeti.jetCoordChange_last_bijective` and `TauCeti.jetCoordChange_last_symm_bijective`:
  bijectivity of the top-order transition over a fixed lower `r`-jet;
* `TauCeti.contDiffOn_jetCoordChange`: `C^m` smoothness on open bundle-chart domains when `h` and
  `g` are `C^n` with `m + r ≤ n`.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A.
* Ivan Kolář, Peter W. Michor and Jan Slovák, *Natural Operations in Differential Geometry*,
  Chapter 12.
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 E E' E'' F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-! ### Truncation, top-order extension, and unnormalized formal Taylor series of jet tuples -/

/-- Truncate an `r₂`-jet coordinate tuple to an `r₁`-jet coordinate tuple for `r₁ ≤ r₂`. -/
def jetTruncate {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) :
    (i : Fin (r₁ + 1)) → E [×i.val]→L[𝕜] F :=
  fun i ↦ j (i.castLE (Nat.add_le_add_right hle 1))

@[simp]
theorem jetTruncate_apply {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) (i : Fin (r₁ + 1)) :
    jetTruncate hle j i = j (i.castLE (Nat.add_le_add_right hle 1)) :=
  (rfl)

theorem jetTruncate_zero {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) :
    jetTruncate hle j 0 = j 0 :=
  (rfl)

@[simp]
theorem jetTruncate_refl (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    jetTruncate (le_refl r) j = j := by
  funext i
  simp

theorem jetTruncate_trans {r₁ r₂ r₃ : ℕ} (h₁₂ : r₁ ≤ r₂) (h₂₃ : r₂ ≤ r₃)
    (j : (i : Fin (r₃ + 1)) → E [×i.val]→L[𝕜] F) :
    jetTruncate h₁₂ (jetTruncate h₂₃ j) = jetTruncate (h₁₂.trans h₂₃) j :=
  (rfl)

/-- Append a top-order `(r + 1)`-multilinear map `A` to a lower `r`-jet tuple `j₀`. -/
def jetSnoc {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) : (i : Fin (r + 2)) → E [×i.val]→L[𝕜] F :=
  Fin.snoc (α := fun i : Fin (r + 2) ↦ E [×i.val]→L[𝕜] F) j₀ A

@[simp]
theorem jetSnoc_castSucc {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) (i : Fin (r + 1)) :
    jetSnoc j₀ A i.castSucc = j₀ i := by
  simp [jetSnoc]

@[simp]
theorem jetSnoc_zero {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) :
    jetSnoc j₀ A 0 = j₀ 0 :=
  jetSnoc_castSucc j₀ A 0

@[simp]
theorem jetSnoc_last {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) :
    jetSnoc j₀ A (Fin.last (r + 1)) = A := by
  simp [jetSnoc]

@[simp]
theorem jetTruncate_jetSnoc {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) :
    jetTruncate (Nat.le_succ r) (jetSnoc j₀ A) = j₀ := by
  funext i
  exact jetSnoc_castSucc j₀ A i

/-- Jet truncation is a smooth continuous linear projection on coordinate tuples. -/
theorem contDiff_jetTruncate {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) {n : ℕ∞ω} :
    ContDiff 𝕜 n
      (jetTruncate hle : ((i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) →
        (i : Fin (r₁ + 1)) → E [×i.val]→L[𝕜] F) :=
  contDiff_pi.mpr fun i ↦ contDiff_apply 𝕜 _ (i.castLE (Nat.add_le_add_right hle 1))

/-- The unnormalized formal derivative series of an `r`-jet tuple `j`, equal to `j i` in orders
`i ≤ r` and `0` above `r`. Unlike `TauCeti.finiteJetSeries`, no factorial factors are inserted, so
this matches `ftaylorSeries` under `FormalMultilinearSeries.taylorComp`. -/
def jetSeries (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E F :=
  fun n ↦ if h : n < r + 1 then j ⟨n, h⟩ else 0

@[simp]
theorem jetSeries_apply (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (i : Fin (r + 1)) :
    jetSeries r j i.val = j i := by
  simp [jetSeries, i.isLt]

@[simp]
theorem jetSeries_zero (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    jetSeries r j 0 = j 0 :=
  jetSeries_apply r j 0

theorem jetSeries_eq_zero_of_le (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (n : ℕ) (hn : r + 1 ≤ n) :
    jetSeries r j n = 0 := by
  simp [jetSeries, not_lt.mpr hn]

theorem jetSeries_jetTruncate {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) {n : ℕ} (hn : n ≤ r₁) :
    jetSeries r₁ (jetTruncate hle j) n = jetSeries r₂ j n := by
  have h₁ : n < r₁ + 1 := Nat.lt_succ_of_le hn
  have h₂ : n < r₂ + 1 := Nat.lt_succ_of_le (hn.trans hle)
  simp [jetSeries, h₁, h₂]

theorem jetSeries_iteratedFDeriv (r : ℕ) (s : E → F) (x : E) {n : ℕ} (hn : n ≤ r) :
    jetSeries r (fun i ↦ iteratedFDeriv 𝕜 i.val s x) n = ftaylorSeries 𝕜 s x n := by
  have h : n < r + 1 := Nat.lt_succ_of_le hn
  simp [jetSeries, h, ftaylorSeries]

/-! ### Auxiliary lemmas on formal Taylor series of continuous linear maps -/

private theorem ftaylorSeries_clm_taylorComp (L : F →L[𝕜] G)
    (p : FormalMultilinearSeries 𝕜 E F) :
    (ftaylorSeries 𝕜 L (p 0 0)).taylorComp p = L.compFormalMultilinearSeries p := by
  classical
  funext m
  rcases m.eq_zero_or_pos with rfl | hm
  · ext v
    simp [ftaylorSeries, Subsingleton.elim v 0]
  · rw [FormalMultilinearSeries.taylorComp,
      Finset.sum_eq_single (OrderedFinpartition.indiscrete m hm)]
    · rw [FormalMultilinearSeries.compAlongOrderedFinpartition_indiscrete]
      ext v
      simp [ftaylorSeries, continuousMultilinearCurryFin1_iteratedFDeriv_one]
    · intro c _ hc
      have hlen_pos : 0 < c.length := by
        by_contra! h0
        have hsum : ∑ i, c.partSize i = m := OrderedFinpartition.sum_partSize c
        obtain hlen0 : c.length = 0 := Nat.eq_zero_of_le_zero h0
        rw [Finset.sum_eq_zero fun i _ ↦ (Fin.elim0 (hlen0 ▸ i))] at hsum
        omega
      have hlen_ne : c.length ≠ 1 := mt (c.length_eq_one_iff hm).mp hc
      obtain ⟨d, hd⟩ : ∃ d, c.length = d + 2 := ⟨c.length - 2, by omega⟩
      have hzero : ftaylorSeries 𝕜 L (p 0 0) c.length = 0 := by
        rw [ftaylorSeries, hd, L.iteratedFDeriv_add_two]
      ext v
      rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, hzero]
      rfl
    · simp

private theorem ftaylorSeries_id (x : E) :
    ftaylorSeries 𝕜 (id : E → E) x = FormalMultilinearSeries.id 𝕜 E x := by
  have h := ftaylorSeries_clm_taylorComp (ContinuousLinearMap.id 𝕜 E)
    (FormalMultilinearSeries.id 𝕜 E x)
  rw [FormalMultilinearSeries.id_apply_zero, FormalMultilinearSeries.taylorComp_id,
    ContinuousLinearMap.coe_id'] at h
  exact h.trans (by funext m; ext v; rfl)

/-! ### Nonlinear higher-order jet coordinate changes -/

/-- Transform an `r`-jet coordinate tuple `j` along a base map `h : E' → E` and a possibly
nonlinear, base-dependent fibre map `g : E' × F → G` at `x : E'`. This implements the derivatives
through order `r` of the transformed section `y ↦ g (y, s (h y))` via Faà di Bruno composition. -/
def jetCoordChange (r : ℕ) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    (i : Fin (r + 1)) → E' [×i.val]→L[𝕜] G :=
  fun i ↦ ((ftaylorSeries 𝕜 g (x, j 0 0)).taylorComp
    ((FormalMultilinearSeries.id 𝕜 E' x).prod
      ((jetSeries r j).taylorComp (ftaylorSeries 𝕜 h x)))) i.val

theorem jetCoordChange_zero_apply (r : ℕ) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (v : Fin (0 : Fin (r + 1)).val → E') :
    jetCoordChange r h g x j 0 v = g (x, j 0 0) :=
  (FormalMultilinearSeries.taylorComp_zero_apply (ftaylorSeries 𝕜 g (x, j 0 0)) _ v).trans
    (iteratedFDeriv_zero_apply _)

theorem jetCoordChange_zero (r : ℕ) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    jetCoordChange r h g x j 0 = (continuousMultilinearCurryFin0 𝕜 E' G).symm (g (x, j 0 0)) := by
  ext v
  exact jetCoordChange_zero_apply r h g x j v

theorem jetCoordChange_one_apply {r : ℕ} (hr : 1 ≤ r) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (v : Fin 1 → E') :
    jetCoordChange r h g x j ⟨1, Nat.lt_succ_of_le hr⟩ v =
      fderiv 𝕜 g (x, j 0 0) (v 0, j ⟨1, Nat.lt_succ_of_le hr⟩ ![fderiv 𝕜 h x (v 0)]) := by
  have hj1 : jetSeries r j 1 = j ⟨1, Nat.lt_succ_of_le hr⟩ :=
    jetSeries_apply r j ⟨1, Nat.lt_succ_of_le hr⟩
  simp only [jetCoordChange, FormalMultilinearSeries.taylorComp_one_apply,
    FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply,
    FormalMultilinearSeries.id_apply_one, hj1]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  congr 3

/-- At order `1`, `TauCeti.jetCoordChange` agrees with `TauCeti.firstJetCoordChange` under currying
of order-zero and order-one multilinear maps. -/
theorem firstJetCoordChange_eq_jetCoordChange (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin 2) → E [×i.val]→L[𝕜] F) :
    firstJetCoordChange h g x (j 0 0, continuousMultilinearCurryFin1 𝕜 E F (j 1)) =
      (jetCoordChange 1 h g x j 0 0,
        continuousMultilinearCurryFin1 𝕜 E' G (jetCoordChange 1 h g x j 1)) := by
  refine Prod.ext ((firstJetCoordChange_fst h g x _).trans
    (jetCoordChange_zero_apply 1 h g x j 0).symm) ?_
  ext w
  simpa using (jetCoordChange_one_apply (le_refl 1) h g x j ![w]).symm

/-- Higher-order jet coordinate changes depend only on the germs of the coordinate maps. -/
theorem jetCoordChange_congr {r : ℕ} {h h' : E' → E} {g g' : E' × F → G} {x : E'}
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hh : h =ᶠ[𝓝 x] h') (hg : g =ᶠ[𝓝 (x, j 0 0)] g') :
    jetCoordChange r h g x j = jetCoordChange r h' g' x j := by
  funext i
  refine FormalMultilinearSeries.taylorComp_congr
    (fun k _ ↦ (hg.iteratedFDeriv 𝕜 k).eq_of_nhds) (fun k _ _ ↦ ?_)
  simp only [FormalMultilinearSeries.prod]
  congr 1
  exact FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl)
    (fun m _ _ ↦ (hh.iteratedFDeriv 𝕜 m).eq_of_nhds)

/-- Nonlinear jet coordinate changes commute with truncation to any lower order. -/
@[simp]
theorem jetTruncate_jetCoordChange {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) :
    jetTruncate hle (jetCoordChange r₂ h g x j) =
      jetCoordChange r₁ h g x (jetTruncate hle j) := by
  funext i
  refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) (fun k _ hk ↦ ?_)
  simp only [FormalMultilinearSeries.prod]
  congr 1
  exact FormalMultilinearSeries.taylorComp_congr
    (fun m hm ↦ (jetSeries_jetTruncate hle j (hm.trans (hk.trans (Nat.le_of_lt_succ i.isLt)))).symm)
    (fun _ _ _ ↦ rfl)

/-- **Higher-order chain rule on local sections.** Transforming the `r`-jet of a `C^r` section `s`
by `jetCoordChange` gives the `r`-jet of the transformed section `y ↦ g (y, s (h y))`. -/
theorem jetCoordChange_iteratedFDeriv {r : ℕ} {h : E' → E} {g : E' × F → G} {s : E → F} {x : E'}
    (hh : ContDiffAt 𝕜 r h x) (hs : ContDiffAt 𝕜 r s (h x))
    (hg : ContDiffAt 𝕜 r g (x, s (h x))) :
    jetCoordChange r h g x (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s (h x)) =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val (fun y ↦ g (y, s (h y))) x := by
  funext i
  have hi_le : i.val ≤ r := Nat.le_of_lt_succ i.isLt
  have hi : (i.val : ℕ∞ω) ≤ r := Nat.cast_le.mpr hi_le
  have hsh : ContDiffAt 𝕜 r (s ∘ h) x := hs.comp x hh
  have hgraph : ContDiffAt 𝕜 r (fun y ↦ (y, (s ∘ h) y)) x := contDiffAt_id.prodMk hsh
  change _ = iteratedFDeriv 𝕜 i.val (g ∘ fun y ↦ (y, (s ∘ h) y)) x
  rw [iteratedFDeriv_comp (f := fun y ↦ (y, (s ∘ h) y)) hg hgraph hi]
  have hv0 : iteratedFDeriv 𝕜 ((0 : Fin (r + 1)).val) s (h x) 0 = s (h x) :=
    iteratedFDeriv_zero_apply _
  refine FormalMultilinearSeries.taylorComp_congr
    (fun k _ ↦ by rw [hv0]; rfl) (fun k _ hk ↦ ?_)
  have hk_r : (k : ℕ∞ω) ≤ r := Nat.cast_le.mpr (hk.trans hi_le)
  refine (congrArg₂ ContinuousMultilinearMap.prod
    (congrFun (ftaylorSeries_id x).symm k) ?_).trans
      (iteratedFDeriv_prodMk contDiffAt_id hsh hk_r).symm
  rw [iteratedFDeriv_comp hs hh hk_r]
  exact FormalMultilinearSeries.taylorComp_congr
    (fun m hm ↦ jetSeries_iteratedFDeriv r s (h x) (hm.trans (hk.trans hi_le)))
    (fun _ _ _ ↦ rfl)

/-- Identity base and fibre coordinate changes act as the identity on all `r`-jet tuples. -/
@[simp]
theorem jetCoordChange_id (r : ℕ) (x : E) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    jetCoordChange r (id : E → E) (Prod.snd : E × F → F) x j = j := by
  funext i
  simp only [jetCoordChange, ftaylorSeries_id, FormalMultilinearSeries.taylorComp_id]
  let P : FormalMultilinearSeries 𝕜 E (E × F) :=
    (FormalMultilinearSeries.id 𝕜 E x).prod (jetSeries r j)
  have hP0 : P 0 0 = (x, j 0 0) := rfl
  have hsnd := ftaylorSeries_clm_taylorComp (ContinuousLinearMap.snd 𝕜 E F) P
  rw [hP0] at hsnd
  change ((ftaylorSeries 𝕜 (ContinuousLinearMap.snd 𝕜 E F) (x, j 0 0)).taylorComp P) i.val = j i
  rw [hsnd]
  ext v
  simp [P, FormalMultilinearSeries.prod]

/-- **Cocycle law for nonlinear higher-order jet coordinate changes.** Composing two nonlinear
bundle coordinate changes agrees with the coordinate change of the composite base and fibre maps,
with no symmetry or characteristic assumptions on the jet tuple `j`. -/
theorem jetCoordChange_comp {r : ℕ} {h : E' → E} {k : E'' → E'}
    {g : E' × F → G} {l : E'' × G → H} {y : E''}
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hh : ContDiffAt 𝕜 r h (k y)) (hk : ContDiffAt 𝕜 r k y)
    (hg : ContDiffAt 𝕜 r g (k y, j 0 0))
    (hl : ContDiffAt 𝕜 r l (y, g (k y, j 0 0))) :
    jetCoordChange r k l y (jetCoordChange r h g (k y) j) =
      jetCoordChange r (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) y j := by
  funext i
  have hi_le : i.val ≤ r := Nat.le_of_lt_succ i.isLt
  let J₁ := jetCoordChange r h g (k y) j
  let G₁ : FormalMultilinearSeries 𝕜 E' (E' × F) :=
    (FormalMultilinearSeries.id 𝕜 E' (k y)).prod
      ((jetSeries r j).taylorComp (ftaylorSeries 𝕜 h (k y)))
  let P : FormalMultilinearSeries 𝕜 E'' F :=
    (jetSeries r j).taylorComp (ftaylorSeries 𝕜 (h ∘ k) y)
  let Q : FormalMultilinearSeries 𝕜 E'' (E'' × F) :=
    (FormalMultilinearSeries.id 𝕜 E'' y).prod P
  have hQ0 : Q 0 0 = (y, j 0 0) :=
    Prod.ext rfl ((FormalMultilinearSeries.taylorComp_zero_apply (jetSeries r j) _ 0).trans
      (by rw [jetSeries_zero]; rfl))
  have hJ₁_zero : J₁ 0 0 = g (k y, j 0 0) := jetCoordChange_zero_apply r h g (k y) j 0
  have hJ₁_series (m : ℕ) (hm : m ≤ r) :
      jetSeries r J₁ m = ((ftaylorSeries 𝕜 g (k y, j 0 0)).taylorComp G₁) m := by
    have hlt : m < r + 1 := Nat.lt_succ_of_le hm
    simp [jetSeries, hlt, J₁, jetCoordChange, G₁]
  -- Simplify the left-hand side into a single nested `taylorComp`.
  have hLHS : jetCoordChange r k l y J₁ i =
      ((ftaylorSeries 𝕜 l (y, g (k y, j 0 0))).taylorComp
        ((FormalMultilinearSeries.id 𝕜 E'' y).prod
          ((ftaylorSeries 𝕜 g (k y, j 0 0)).taylorComp ((ftaylorSeries 𝕜 k y).prod P)))) i.val := by
    dsimp only [jetCoordChange]
    rw [hJ₁_zero]
    refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) (fun m _ hm ↦ ?_)
    simp only [FormalMultilinearSeries.prod]
    congr 1
    have h1 : ((jetSeries r J₁).taylorComp (ftaylorSeries 𝕜 k y)) m =
        (((ftaylorSeries 𝕜 g (k y, j 0 0)).taylorComp G₁).taylorComp
          (ftaylorSeries 𝕜 k y)) m :=
      FormalMultilinearSeries.taylorComp_congr
        (fun a ha ↦ hJ₁_series a (ha.trans (hm.trans hi_le))) (fun _ _ _ ↦ rfl)
    rw [h1, FormalMultilinearSeries.taylorComp_assoc]
    refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) (fun n _ hn_le ↦ ?_)
    have hk0 : ftaylorSeries 𝕜 k y 0 ![] = k y := iteratedFDeriv_zero_apply _
    have hG₁ : (G₁.taylorComp (ftaylorSeries 𝕜 k y)) n =
        ((ftaylorSeries 𝕜 k y).prod
          ((jetSeries r j).taylorComp
            ((ftaylorSeries 𝕜 h (k y)).taylorComp (ftaylorSeries 𝕜 k y)))) n := by
      simp only [G₁, FormalMultilinearSeries.prod_taylorComp,
        ← hk0, FormalMultilinearSeries.id_taylorComp, FormalMultilinearSeries.taylorComp_assoc]
    rw [hG₁]
    simp only [FormalMultilinearSeries.prod]
    congr 1
    exact FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) fun a _ ha ↦
      (iteratedFDeriv_comp hh hk (Nat.cast_le.mpr (ha.trans (hn_le.trans (hm.trans hi_le))))).symm
  -- Simplify the right-hand side to the exact same series.
  let ψ : E'' × F → E' × F := fun p ↦ ((k ∘ Prod.fst) p, p.2)
  let Φ : E'' × F → E'' × G := fun p ↦ (p.1, (g ∘ ψ) p)
  have hψ : ContDiffAt 𝕜 r ψ (y, j 0 0) :=
    (hk.comp (y, j 0 0) contDiffAt_fst).prodMk contDiffAt_snd
  have hgψ : ContDiffAt 𝕜 r (g ∘ ψ) (y, j 0 0) := hg.comp (y, j 0 0) hψ
  have hΦ : ContDiffAt 𝕜 r Φ (y, j 0 0) := contDiffAt_fst.prodMk hgψ
  have hfstQ : (ftaylorSeries 𝕜 (Prod.fst : E'' × F → E'') (y, j 0 0)).taylorComp Q =
      FormalMultilinearSeries.id 𝕜 E'' y := by
    have h := ftaylorSeries_clm_taylorComp (ContinuousLinearMap.fst 𝕜 E'' F) Q
    rw [hQ0] at h
    refine h.trans ?_
    funext m; ext v; simp [Q, FormalMultilinearSeries.prod]
  have hsndQ : (ftaylorSeries 𝕜 (Prod.snd : E'' × F → F) (y, j 0 0)).taylorComp Q = P := by
    have h := ftaylorSeries_clm_taylorComp (ContinuousLinearMap.snd 𝕜 E'' F) Q
    rw [hQ0] at h
    refine h.trans ?_
    funext m; ext v; simp [Q, FormalMultilinearSeries.prod]
  have hRHS : jetCoordChange r (h ∘ k) (l ∘ Φ) y j i =
      ((ftaylorSeries 𝕜 l (y, g (k y, j 0 0))).taylorComp
        ((FormalMultilinearSeries.id 𝕜 E'' y).prod
          ((ftaylorSeries 𝕜 g (k y, j 0 0)).taylorComp ((ftaylorSeries 𝕜 k y).prod P)))) i.val := by
    dsimp only [jetCoordChange]
    have hcomp_l : ((ftaylorSeries 𝕜 (l ∘ Φ) (y, j 0 0)).taylorComp Q) i.val =
        (((ftaylorSeries 𝕜 l (y, g (k y, j 0 0))).taylorComp
          (ftaylorSeries 𝕜 Φ (y, j 0 0))).taylorComp Q) i.val :=
      FormalMultilinearSeries.taylorComp_congr
        (fun a ha ↦ iteratedFDeriv_comp (f := Φ) hl hΦ (Nat.cast_le.mpr (ha.trans hi_le)))
        (fun _ _ _ ↦ rfl)
    change ((ftaylorSeries 𝕜 (l ∘ Φ) (y, j 0 0)).taylorComp Q) i.val = _
    rw [hcomp_l, FormalMultilinearSeries.taylorComp_assoc]
    refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) (fun m _ hm ↦ ?_)
    have hΦ_m : ((ftaylorSeries 𝕜 Φ (y, j 0 0)).taylorComp Q) m =
        (((ftaylorSeries 𝕜 (Prod.fst : E'' × F → E'') (y, j 0 0)).prod
          (ftaylorSeries 𝕜 (g ∘ ψ) (y, j 0 0))).taylorComp Q) m :=
      FormalMultilinearSeries.taylorComp_congr
        (fun a ha ↦ iteratedFDeriv_prodMk contDiffAt_fst hgψ
          (Nat.cast_le.mpr (ha.trans (hm.trans hi_le))))
        (fun _ _ _ ↦ rfl)
    rw [hΦ_m, FormalMultilinearSeries.prod_taylorComp, hfstQ]
    simp only [FormalMultilinearSeries.prod]
    congr 1
    have hgψ_m : ((ftaylorSeries 𝕜 (g ∘ ψ) (y, j 0 0)).taylorComp Q) m =
        (((ftaylorSeries 𝕜 g (k y, j 0 0)).taylorComp
          (ftaylorSeries 𝕜 ψ (y, j 0 0))).taylorComp Q) m :=
      FormalMultilinearSeries.taylorComp_congr
        (fun a ha ↦ iteratedFDeriv_comp (f := ψ) hg hψ
          (Nat.cast_le.mpr (ha.trans (hm.trans hi_le))))
        (fun _ _ _ ↦ rfl)
    rw [hgψ_m, FormalMultilinearSeries.taylorComp_assoc]
    refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) (fun n _ hn ↦ ?_)
    have hψ_n : ((ftaylorSeries 𝕜 ψ (y, j 0 0)).taylorComp Q) n =
        ((((ftaylorSeries 𝕜 k y).taylorComp
            (ftaylorSeries 𝕜 (Prod.fst : E'' × F → E'') (y, j 0 0))).prod
          (ftaylorSeries 𝕜 (Prod.snd : E'' × F → F) (y, j 0 0))).taylorComp Q) n :=
      FormalMultilinearSeries.taylorComp_congr
        (fun b hb ↦ by
          have hb_r : (b : ℕ∞ω) ≤ r := Nat.cast_le.mpr (hb.trans (hn.trans (hm.trans hi_le)))
          change iteratedFDeriv 𝕜 b ψ (y, j 0 0) = _
          rw [iteratedFDeriv_prodMk (hk.comp (y, j 0 0) contDiffAt_fst) contDiffAt_snd hb_r,
            iteratedFDeriv_comp (f := Prod.fst) hk contDiffAt_fst hb_r]
          rfl)
        (fun _ _ _ ↦ rfl)
    rw [hψ_n, FormalMultilinearSeries.prod_taylorComp, FormalMultilinearSeries.taylorComp_assoc,
      hfstQ, FormalMultilinearSeries.taylorComp_id, hsndQ]
  exact hLHS.trans hRHS.symm

/-- Coordinate maps that are inverse as germs induce inverse transformations of `r`-jets. -/
theorem jetCoordChange_inverse {r : ℕ} {h : E' → E} {k : E → E'}
    {g : E' × F → G} {l : E × G → F} {x : E}
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hh : ContDiffAt 𝕜 r h (k x)) (hk : ContDiffAt 𝕜 r k x)
    (hg : ContDiffAt 𝕜 r g (k x, j 0 0))
    (hl : ContDiffAt 𝕜 r l (x, g (k x, j 0 0)))
    (hbase : h ∘ k =ᶠ[𝓝 x] id)
    (hfibre : (fun p : E × F ↦ l (p.1, g (k p.1, p.2))) =ᶠ[𝓝 (x, j 0 0)] Prod.snd) :
    jetCoordChange r k l x (jetCoordChange r h g (k x) j) = j := by
  rw [jetCoordChange_comp j hh hk hg hl]
  exact (jetCoordChange_congr j hbase hfibre).trans (jetCoordChange_id r x j)

/-! ### Symmetry preservation -/

/-- Over a nontrivially normed field of characteristic zero, `jetCoordChange` preserves slot
symmetry of `r`-jets whenever `h` and `g` have smoothness at least `minSmoothness 𝕜 r`. -/
theorem jetCoordChange_comp_perm [CharZero 𝕜] {r : ℕ} {n : ℕ∞ω}
    {h : E' → E} {g : E' × F → G} {x : E'}
    {j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F}
    (hn : minSmoothness 𝕜 r ≤ n) (hh : ContDiffAt 𝕜 n h x)
    (hg : ContDiffAt 𝕜 n g (x, j 0 0))
    (hj : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), j i (v ∘ σ) = j i v)
    (i : Fin (r + 1)) (v : Fin i.val → E') (σ : Equiv.Perm (Fin i.val)) :
    jetCoordChange r h g x j i (v ∘ σ) = jetCoordChange r h g x j i v := by
  let s := finiteJetPolynomial r j (h x)
  have hs_self : s (h x) = j 0 0 :=
    (finiteJetPolynomial_self r j (h x)).trans (congrArg (j 0) (funext fun a ↦ Fin.elim0 a))
  have hs_jet : (fun k : Fin (r + 1) ↦ iteratedFDeriv 𝕜 k.val s (h x)) = j :=
    funext fun k ↦ iteratedFDeriv_finiteJetPolynomial_self r j (h x) k (hj k)
  have hr_le : (r : ℕ∞ω) ≤ n := le_minSmoothness.trans hn
  have hs_smooth : ContDiffAt 𝕜 n s (h x) := (contDiff_finiteJetPolynomial r j (h x)).contDiffAt
  have hg' : ContDiffAt 𝕜 n g (x, s (h x)) := by simpa only [hs_self] using hg
  have hcomp : ContDiffAt 𝕜 n (fun y ↦ g (y, s (h y))) x :=
    hg'.comp x (contDiffAt_id.prodMk (hs_smooth.comp x hh))
  have hchange := jetCoordChange_iteratedFDeriv (hh.of_le hr_le) (hs_smooth.of_le hr_le)
    (hg'.of_le hr_le)
  rw [hs_jet] at hchange
  rw [congrFun hchange i]
  exact hcomp.iteratedFDeriv_comp_perm_of_minSmoothness
    ((minSmoothness_monotone (Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt))).trans hn) v σ

/-- Over `ℝ` or `ℂ` (`IsRCLikeNormedField 𝕜`), `C^r` coordinate maps preserve slot symmetry of
`r`-jets. -/
theorem jetCoordChange_comp_perm_of_isRCLikeNormedField [IsRCLikeNormedField 𝕜] {r : ℕ}
    {h : E' → E} {g : E' × F → G} {x : E'}
    {j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F}
    (hh : ContDiffAt 𝕜 r h x) (hg : ContDiffAt 𝕜 r g (x, j 0 0))
    (hj : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), j i (v ∘ σ) = j i v)
    (i : Fin (r + 1)) (v : Fin i.val → E') (σ : Equiv.Perm (Fin i.val)) :
    jetCoordChange r h g x j i (v ∘ σ) = jetCoordChange r h g x j i v := by
  let := IsRCLikeNormedField.rclike 𝕜
  exact jetCoordChange_comp_perm (by rw [minSmoothness_of_isRCLikeNormedField]) hh hg hj i v σ

/-! ### Top-order affine structure -/

/-- When two `r`-jet tuples agree in all orders strictly below a positive order `i`, all nonlinear
Faà di Bruno partition terms cancel at `i`, and their difference transforms linearly by the
vertical derivative `(fderiv 𝕜 g (x, j₁ 0 0)).comp (inr 𝕜 E' F)` and precomposition in every slot
with `fderiv 𝕜 h x`. No differentiability hypotheses are needed on `h` or `g`. -/
theorem jetCoordChange_sub_of_eq_lt {r : ℕ} (h : E' → E) (g : E' × F → G) (x : E')
    {j₁ j₂ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F} {i : Fin (r + 1)} (hi : 0 < i.val)
    (hj : ∀ k : Fin (r + 1), k.val < i.val → j₁ k = j₂ k) :
    jetCoordChange r h g x j₁ i - jetCoordChange r h g x j₂ i =
      ((fderiv 𝕜 g (x, j₁ 0 0)).comp (inr 𝕜 E' F)).compContinuousMultilinearMap
        ((j₁ i - j₂ i).compContinuousLinearMap fun _ ↦ fderiv 𝕜 h x) := by
  classical
  have hj0 : j₁ 0 = j₂ 0 := hj 0 hi
  let Q := ftaylorSeries 𝕜 g (x, j₁ 0 0)
  let H := ftaylorSeries 𝕜 h x
  let G₁ := (FormalMultilinearSeries.id 𝕜 E' x).prod ((jetSeries r j₁).taylorComp H)
  let G₂ := (FormalMultilinearSeries.id 𝕜 E' x).prod ((jetSeries r j₂).taylorComp H)
  have hG_lt (k : ℕ) (_ : 1 ≤ k) (hk : k < i.val) : G₁ k = G₂ k := by
    simp only [G₁, G₂, FormalMultilinearSeries.prod]
    congr 1
    refine FormalMultilinearSeries.taylorComp_congr (fun m hm ↦ ?_) (fun _ _ _ ↦ rfl)
    have hm_lt : m < r + 1 := (hm.trans_lt hk).trans i.isLt
    simp only [jetSeries, hm_lt, ↓reduceDIte]
    exact hj ⟨m, hm_lt⟩ (hm.trans_lt hk)
  change Q.taylorComp G₁ i.val -
      (ftaylorSeries 𝕜 g (x, j₂ 0 0)).taylorComp G₂ i.val = _
  rw [← hj0, FormalMultilinearSeries.taylorComp_sub_of_eq_lt Q hi hG_lt]
  have hQ1 : continuousMultilinearCurryFin1 𝕜 (E' × F) G (Q 1) = fderiv 𝕜 g (x, j₁ 0 0) :=
    continuousMultilinearCurryFin1_iteratedFDeriv_one g (x, j₁ 0 0)
  rw [hQ1]
  have hinner : (jetSeries r j₁).taylorComp H i.val - (jetSeries r j₂).taylorComp H i.val =
      (j₁ i - j₂ i).compContinuousLinearMap fun _ ↦ fderiv 𝕜 h x := by
    let c₀ := OrderedFinpartition.atomic i.val
    rw [FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.taylorComp,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ c₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ c₀)]
    have hrest : ∑ c ∈ Finset.univ.erase c₀, (jetSeries r j₁).compAlongOrderedFinpartition H c =
        ∑ c ∈ Finset.univ.erase c₀, (jetSeries r j₂).compAlongOrderedFinpartition H c := by
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      have hlt : c.length < i.val :=
        c.length_lt_of_ne_atomic (Finset.mem_erase.mp hc).1
      have hlt_r : c.length < r + 1 := hlt.trans i.isLt
      unfold FormalMultilinearSeries.compAlongOrderedFinpartition
      simp only [jetSeries, hlt_r, ↓reduceDIte, hj ⟨c.length, hlt_r⟩ hlt]
    rw [hrest, add_sub_add_right_eq_sub,
      FormalMultilinearSeries.compAlongOrderedFinpartition_atomic,
      FormalMultilinearSeries.compAlongOrderedFinpartition_atomic,
      jetSeries_apply, jetSeries_apply]
    have hH1 : continuousMultilinearCurryFin1 𝕜 E' E (H 1) = fderiv 𝕜 h x :=
      continuousMultilinearCurryFin1_iteratedFDeriv_one h x
    rw [hH1]
    ext v
    rfl
  ext v
  have hG_diff : (G₁ i.val - G₂ i.val) v =
      (0, ((j₁ i - j₂ i).compContinuousLinearMap (fun _ ↦ fderiv 𝕜 h x)) v) := by
    rw [_root_.sub_apply]
    simp only [G₁, G₂, FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply,
      Prod.mk_sub_mk, sub_self, ← _root_.sub_apply, hinner]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, hG_diff,
    comp_apply, inr_apply]

/-- **Affine bundle transition at top order.** If two `(r + 1)`-jets have the same `r`-jet
truncation, their top-order difference transforms linearly by the vertical derivative of `g` and
the base derivative of `h`; all lower-order inhomogeneous terms cancel. -/
theorem jetCoordChange_last_sub {r : ℕ} (h : E' → E) (g : E' × F → G) (x : E')
    {j₁ j₂ : (i : Fin (r + 2)) → E [×i.val]→L[𝕜] F}
    (hj : jetTruncate (Nat.le_succ r) j₁ = jetTruncate (Nat.le_succ r) j₂) :
    jetCoordChange (r + 1) h g x j₁ (Fin.last (r + 1)) -
        jetCoordChange (r + 1) h g x j₂ (Fin.last (r + 1)) =
      ((fderiv 𝕜 g (x, j₁ 0 0)).comp (inr 𝕜 E' F)).compContinuousMultilinearMap
        ((j₁ (Fin.last (r + 1)) - j₂ (Fin.last (r + 1))).compContinuousLinearMap
          fun _ ↦ fderiv 𝕜 h x) := by
  refine jetCoordChange_sub_of_eq_lt h g x (Nat.succ_pos r) fun k hk ↦ ?_
  have hk' : k.val < r + 1 := by simpa using hk
  simpa using congrFun hj ⟨k.val, hk'⟩

private theorem jetSnoc_zero_zero {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) :
    jetSnoc j₀ A 0 0 = j₀ 0 0 := by
  change (jetSnoc j₀ A (0 : Fin (r + 1)).castSucc) 0 = j₀ 0 0
  rw [jetSnoc_castSucc]

/-- Over a fixed lower `r`-jet `j₀`, if the vertical derivative of `g` and the base derivative of
`h` are invertible continuous linear maps, the affine map on the top-order multilinear coordinate
is bijective. -/
theorem jetCoordChange_last_bijective {r : ℕ} (h : E' → E) (g : E' × F → G) (x : E')
    (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (a : F ≃L[𝕜] G) (c : E' ≃L[𝕜] E)
    (ha : (fderiv 𝕜 g (x, j₀ 0 0)).comp (inr 𝕜 E' F) = a.toContinuousLinearMap)
    (hc : fderiv 𝕜 h x = c.toContinuousLinearMap) :
    Function.Bijective (fun A : E [×(r + 1)]→L[𝕜] F ↦
      jetCoordChange (r + 1) h g x (jetSnoc j₀ A) (Fin.last (r + 1))) := by
  let linEquiv : (E [×(r + 1)]→L[𝕜] F) ≃ (E' [×(Fin.last (r + 1)).val]→L[𝕜] G) :=
    { toFun A := a.toContinuousLinearMap.compContinuousMultilinearMap
        (A.compContinuousLinearMap fun _ ↦ c.toContinuousLinearMap)
      invFun B := a.symm.toContinuousLinearMap.compContinuousMultilinearMap
        (B.compContinuousLinearMap fun _ ↦ c.symm.toContinuousLinearMap)
      left_inv A := by ext v; simp
      right_inv B := by ext v; simp }
  have heq : (fun A : E [×(r + 1)]→L[𝕜] F ↦
        jetCoordChange (r + 1) h g x (jetSnoc j₀ A) (Fin.last (r + 1))) =
      fun A ↦ linEquiv A + jetCoordChange (r + 1) h g x (jetSnoc j₀ 0) (Fin.last (r + 1)) := by
    funext A
    have htr : jetTruncate (Nat.le_succ r) (jetSnoc j₀ A) =
        jetTruncate (Nat.le_succ r) (jetSnoc j₀ 0) := by simp
    have hd := jetCoordChange_last_sub h g x htr
    rw [jetSnoc_zero_zero, jetSnoc_last, jetSnoc_last, sub_zero, ha, hc] at hd
    exact sub_eq_iff_eq_add.mp hd
  rw [heq]
  exact (Equiv.addRight _).bijective.comp linEquiv.bijective

/-- Over a fixed symmetric lower `r`-jet `j₀`, if `h` and `g` preserve top-order symmetry and have
invertible base and vertical derivatives, the induced affine map on symmetric `(r + 1)`-multilinear
maps (the model fibre of `J^{r+1}E → J^rE`) is bijective. -/
theorem jetCoordChange_last_symm_bijective [CharZero 𝕜] {r : ℕ} {n : ℕ∞ω}
    {h : E' → E} {g : E' × F → G} {x : E'}
    {j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F}
    (hn : minSmoothness 𝕜 (r + 1) ≤ n) (hh : ContDiffAt 𝕜 n h x)
    (hg : ContDiffAt 𝕜 n g (x, j₀ 0 0))
    (hj₀ : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), j₀ i (v ∘ σ) = j₀ i v)
    (a : F ≃L[𝕜] G) (c : E' ≃L[𝕜] E)
    (ha : (fderiv 𝕜 g (x, j₀ 0 0)).comp (inr 𝕜 E' F) = a.toContinuousLinearMap)
    (hc : fderiv 𝕜 h x = c.toContinuousLinearMap) :
    Function.Bijective
      (fun A : {A : E [×(r + 1)]→L[𝕜] F //
          ∀ (v : Fin (r + 1) → E) (σ : Equiv.Perm (Fin (r + 1))), A (v ∘ σ) = A v} ↦
        (⟨jetCoordChange (r + 1) h g x (jetSnoc j₀ A.1) (Fin.last (r + 1)),
          by
            have hg' : ContDiffAt 𝕜 n g (x, jetSnoc j₀ A.1 0 0) := by
              simpa only [jetSnoc_zero_zero] using hg
            refine jetCoordChange_comp_perm hn hh hg' (fun i ↦ ?_) (Fin.last (r + 1))
            refine Fin.lastCases ?_ (fun k ↦ ?_) i
            · simpa using A.2
            · simpa using hj₀ k⟩ :
          {B : E' [×(Fin.last (r + 1)).val]→L[𝕜] G //
            ∀ (v : Fin (Fin.last (r + 1)).val → E')
              (σ : Equiv.Perm (Fin (Fin.last (r + 1)).val)), B (v ∘ σ) = B v})) := by
  have hbij := jetCoordChange_last_bijective h g x j₀ a c ha hc
  refine ⟨fun A₁ A₂ hEq ↦ Subtype.ext (hbij.1 (congrArg Subtype.val hEq)), fun B ↦ ?_⟩
  obtain ⟨A, hA⟩ := hbij.2 B.1
  have htr : jetTruncate (Nat.le_succ r) (jetSnoc j₀ A) =
      jetTruncate (Nat.le_succ r) (jetSnoc j₀ 0) := by simp
  have hd := jetCoordChange_last_sub h g x htr
  rw [jetSnoc_zero_zero, jetSnoc_last, jetSnoc_last, sub_zero, ha, hc] at hd
  have hB0_symm : ∀ (w : Fin (Fin.last (r + 1)).val → E')
      (σ : Equiv.Perm (Fin (Fin.last (r + 1)).val)),
      jetCoordChange (r + 1) h g x (jetSnoc j₀ 0) (Fin.last (r + 1)) (w ∘ σ) =
        jetCoordChange (r + 1) h g x (jetSnoc j₀ 0) (Fin.last (r + 1)) w := by
    have hg0 : ContDiffAt 𝕜 n g (x, jetSnoc j₀ 0 0 0) := by
      simpa only [jetSnoc_zero_zero] using hg
    refine jetCoordChange_comp_perm hn hh hg0 (fun i ↦ ?_) (Fin.last (r + 1))
    refine Fin.lastCases (by simp) (fun k ↦ ?_) i
    simpa using hj₀ k
  have hA_symm (v : Fin (r + 1) → E) (σ : Equiv.Perm (Fin (r + 1))) : A (v ∘ σ) = A v := by
    apply a.injective
    have hv1 : a (A (v ∘ σ)) =
        (B.1 - jetCoordChange (r + 1) h g x (jetSnoc j₀ 0) (Fin.last (r + 1)))
          ((c.symm ∘ v) ∘ σ) := by
      rw [← hA, hd]
      simp [Function.comp_def]
    have hv2 : a (A v) =
        (B.1 - jetCoordChange (r + 1) h g x (jetSnoc j₀ 0) (Fin.last (r + 1))) (c.symm ∘ v) := by
      rw [← hA, hd]
      simp [Function.comp_def]
    rw [hv1, hv2, _root_.sub_apply, _root_.sub_apply]
    exact congrArg₂ (· - ·) (B.2 (c.symm ∘ v) σ) (hB0_symm (c.symm ∘ v) σ)
  exact ⟨⟨A, hA_symm⟩, Subtype.ext hA⟩

/-! ### Smoothness on open bundle-chart domains -/

/-- Smooth base and nonlinear fibre maps induce `C^m` transitions of `r`-jet coordinates on open
bundle-chart domains whenever `h` and `g` are `C^n` with `m + r ≤ n` (the `r`-jet transition
consumes `r` derivatives). -/
theorem contDiffOn_jetCoordChange {r : ℕ} {n m : ℕ∞ω} {u : Set E'} {v : Set (E' × F)}
    {h : E' → E} {g : E' × F → G} (hu : IsOpen u) (hv : IsOpen v)
    (hh : ContDiffOn 𝕜 n h u) (hg : ContDiffOn 𝕜 n g v) (hmn : m + r ≤ n) :
    ContDiffOn 𝕜 m
      (fun p : E' × ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) ↦ jetCoordChange r h g p.1 p.2)
      {p | p.1 ∈ u ∧ (p.1, p.2 0 0) ∈ v} := by
  let S : Set (E' × ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)) :=
    {p | p.1 ∈ u ∧ (p.1, p.2 0 0) ∈ v}
  refine contDiffOn_pi.mpr fun i ↦ ?_
  have hi_le : i.val ≤ r := Nat.le_of_lt_succ i.isLt
  have hx : ContDiffOn 𝕜 m Prod.fst S := contDiff_fst.contDiffOn
  have hv0 : ContDiff 𝕜 m
      (fun p : E' × ((k : Fin (r + 1)) → E [×k.val]→L[𝕜] F) ↦ p.2 0 0) :=
    (continuousMultilinearCurryFin0 𝕜 E F).contDiff.comp
      ((contDiff_apply 𝕜 _ (0 : Fin (r + 1))).comp contDiff_snd)
  have hxv : ContDiffOn 𝕜 m
      (fun p : E' × ((k : Fin (r + 1)) → E [×k.val]→L[𝕜] F) ↦ (p.1, p.2 0 0)) S :=
    hx.prodMk hv0.contDiffOn
  refine ContDiffOn.taylorComp (fun k hk ↦ ?_) (fun k hk_pos hk_le ↦ ?_)
  · have hmk : m + k ≤ n := (add_le_add_right (Nat.cast_le.mpr (hk.trans hi_le)) m).trans hmn
    have hgk : ContDiffOn 𝕜 m (iteratedFDeriv 𝕜 k g) v := fun y hy ↦
      ((hg.contDiffAt (hv.mem_nhds hy)).iteratedFDeriv_right hmk).contDiffWithinAt
    exact hgk.comp hxv fun _ hp ↦ hp.2
  · have hid_k : ContDiffOn 𝕜 m
        (fun p : E' × ((a : Fin (r + 1)) → E [×a.val]→L[𝕜] F) ↦
          FormalMultilinearSeries.id 𝕜 E' p.1 k) S := by
      rcases eq_or_lt_of_le hk_pos with rfl | hgt
      · exact contDiffOn_const
      · simp only [FormalMultilinearSeries.id_apply_of_one_lt _ _ _ hgt]
        exact contDiffOn_const
    have hcomp_k : ContDiffOn 𝕜 m
        (fun p : E' × ((a : Fin (r + 1)) → E [×a.val]→L[𝕜] F) ↦
          ((jetSeries r p.2).taylorComp (ftaylorSeries 𝕜 h p.1)) k) S := by
      refine ContDiffOn.taylorComp (fun a ha ↦ ?_) (fun a _ ha ↦ ?_)
      · have ha_lt : a < r + 1 := Nat.lt_succ_of_le (ha.trans (hk_le.trans hi_le))
        have heq : (fun p : E' × ((b : Fin (r + 1)) → E [×b.val]→L[𝕜] F) ↦ jetSeries r p.2 a) =
            fun p ↦ p.2 (⟨a, ha_lt⟩ : Fin (r + 1)) := by
          funext p
          simp [jetSeries, ha_lt]
        rw [heq]
        exact ((contDiff_apply 𝕜 _ (⟨a, ha_lt⟩ : Fin (r + 1))).comp contDiff_snd).contDiffOn
      · have hma : m + a ≤ n :=
          (add_le_add_right (Nat.cast_le.mpr (ha.trans (hk_le.trans hi_le))) m).trans hmn
        have hha : ContDiffOn 𝕜 m (iteratedFDeriv 𝕜 a h) u := fun y hy ↦
          ((hh.contDiffAt (hu.mem_nhds hy)).iteratedFDeriv_right hma).contDiffWithinAt
        exact hha.comp hx fun _ hp ↦ hp.1
    exact (ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin k ↦ E') E' F).contDiff.comp_contDiffOn
      (hid_k.prodMk hcomp_k)

end TauCeti
