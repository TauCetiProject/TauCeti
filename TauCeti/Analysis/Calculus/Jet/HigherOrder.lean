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
import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList

/-!
# Nonlinear higher-order jet coordinate changes

In local bundle coordinates an `r`-jet at a base point is represented by a tuple
`j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F` of value and derivative data through order `r`, where
`j 0 0` is the field value. If `h : E' → E` changes base coordinates and `g : E' × F → G` changes
fibre coordinates (possibly nonlinearly and depending on the base point), a local section `s`
transforms into `y ↦ g (y, s (h y))`.

We package `j` into its unnormalized formal Taylor series `TauCeti.jetFTaylorSeries` (without
factorial denominators, matching `ftaylorSeries`, in contrast to the factorial-normalized power
series `TauCeti.finiteJetSeries` in `Realization.lean`) and define `TauCeti.jetCoordChange` by
Faà di Bruno composition along the graph formal series `(FormalMultilinearSeries.id 𝕜 E' x).prod
((jetFTaylorSeries r j).taylorComp (ftaylorSeries 𝕜 h x))`.

The main results are:

* `TauCeti.firstJetCoordChange_eq_jetCoordChange`: compatibility with `TauCeti.firstJetCoordChange`
  at order `1`;
* `TauCeti.jetTruncate_jetCoordChange`: naturality with respect to jet truncation `jetTruncate`;
* `TauCeti.jetCoordChange_iteratedFDeriv`: the higher-order chain rule on `C^r` local sections;
* `TauCeti.jetCoordChange_id`, `TauCeti.jetCoordChange_comp`, `TauCeti.jetCoordChange_inverse`:
  identity, cocycle, and local germ-inverse laws for arbitrary jet tuples;
* `TauCeti.jetCoordChange_comp_perm`: preservation of slot symmetry over any nontrivially normed
  field;
* `TauCeti.jetCoordChange_sub_of_eq_lt`, `TauCeti.jetCoordChange_last_sub`, and
  `TauCeti.jetCoordChange_jetSnoc_last_eq`: when two jets agree strictly below a positive order, all
  nonlinear partition terms cancel and their difference at that order transforms linearly by the
  vertical derivative of `g` and the base derivative of `h` (exhibiting the affine bundle model
  `J^{r+1}E → J^rE`);
* `TauCeti.jetCoordChange_last_bijective` and `TauCeti.jetCoordChange_last_symmetric_bijective`:
  bijectivity of the top-order transition over a fixed lower `r`-jet;
* `TauCeti.contDiffAt_jetCoordChange` and `TauCeti.contDiffOn_jetCoordChange`: `C^m` smoothness
  pointwise and on open bundle-chart domains when `h` and `g` are `C^n` with `m + r ≤ n`.

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
    jetTruncate hle j i = j (i.castLE (Nat.add_le_add_right hle 1)) := (rfl)

theorem jetTruncate_zero {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) : jetTruncate hle j 0 = j 0 := (rfl)

theorem jetTruncate_zero_apply {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) (v : Fin (0 : Fin (r₁ + 1)).val → E) :
    jetTruncate hle j 0 v = j 0 0 :=
  congrArg (j 0) (funext fun a ↦ Fin.elim0 a)

@[simp]
theorem jetTruncate_refl (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    jetTruncate (le_refl r) j = j :=
  funext fun _ ↦ rfl

@[simp]
theorem jetTruncate_trans {r₁ r₂ r₃ : ℕ} (h₁₂ : r₁ ≤ r₂) (h₂₃ : r₂ ≤ r₃)
    (j : (i : Fin (r₃ + 1)) → E [×i.val]→L[𝕜] F) :
    jetTruncate h₁₂ (jetTruncate h₂₃ j) = jetTruncate (h₁₂.trans h₂₃) j := (rfl)

/-- Append a top-order `(r + 1)`-multilinear map `A` to a lower `r`-jet tuple `j₀`. -/
def jetSnoc {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) : (i : Fin (r + 2)) → E [×i.val]→L[𝕜] F :=
  Fin.snoc (α := fun i : Fin (r + 2) ↦ E [×i.val]→L[𝕜] F) j₀ A

@[simp]
theorem jetSnoc_castSucc {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) (i : Fin (r + 1)) :
    jetSnoc j₀ A i.castSucc = j₀ i := by simp [jetSnoc]

@[simp]
theorem jetSnoc_zero {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) : jetSnoc j₀ A 0 = j₀ 0 :=
  jetSnoc_castSucc j₀ A 0

theorem jetSnoc_zero_apply {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) (v : Fin (0 : Fin (r + 2)).val → E) :
    jetSnoc j₀ A 0 v = j₀ 0 0 := by
  rw [jetSnoc_zero]; exact congrArg (j₀ 0) (funext fun a ↦ Fin.elim0 a)

@[simp]
theorem jetSnoc_last {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) : jetSnoc j₀ A (Fin.last (r + 1)) = A := by simp [jetSnoc]

@[simp]
theorem jetTruncate_jetSnoc {r : ℕ} (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (A : E [×(r + 1)]→L[𝕜] F) : jetTruncate (Nat.le_succ r) (jetSnoc j₀ A) = j₀ :=
  funext (jetSnoc_castSucc j₀ A)

/-- Jet truncation `jetTruncate hle` is `C^n` on coordinate tuples for every `n : ℕ∞ω`. -/
theorem contDiff_jetTruncate {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) {n : ℕ∞ω} :
    ContDiff 𝕜 n
      (jetTruncate hle : ((i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) →
        (i : Fin (r₁ + 1)) → E [×i.val]→L[𝕜] F) :=
  contDiff_pi.mpr fun i ↦ contDiff_apply 𝕜 _ (i.castLE (Nat.add_le_add_right hle 1))

/-- The unnormalized formal derivative series of an `r`-jet tuple `j`, equal to `j i` in orders
`i ≤ r` and `0` above `r`. Unlike `TauCeti.finiteJetSeries`, no factorial factors are inserted, so
this matches `ftaylorSeries` under `FormalMultilinearSeries.taylorComp`. -/
def jetFTaylorSeries (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E F :=
  fun n ↦ if h : n < r + 1 then j ⟨n, h⟩ else 0

@[simp]
theorem jetFTaylorSeries_apply (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (i : Fin (r + 1)) : jetFTaylorSeries r j i.val = j i := by simp [jetFTaylorSeries, i.isLt]

theorem jetFTaylorSeries_apply_of_lt (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    {n : ℕ} (hn : n < r + 1) : jetFTaylorSeries r j n = j ⟨n, hn⟩ :=
  jetFTaylorSeries_apply r j ⟨n, hn⟩

@[simp]
theorem jetFTaylorSeries_zero (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    jetFTaylorSeries r j 0 = j 0 :=
  jetFTaylorSeries_apply r j 0

@[simp]
theorem jetFTaylorSeries_eq_zero_of_le (r : ℕ) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (n : ℕ) (hn : r + 1 ≤ n) : jetFTaylorSeries r j n = 0 := by
  simp [jetFTaylorSeries, not_lt.mpr hn]

theorem jetFTaylorSeries_jetTruncate {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) {n : ℕ} (hn : n ≤ r₁) :
    jetFTaylorSeries r₁ (jetTruncate hle j) n = jetFTaylorSeries r₂ j n := by
  simp [jetFTaylorSeries, Nat.lt_succ_of_le hn, Nat.lt_succ_of_le (hn.trans hle)]

theorem jetFTaylorSeries_iteratedFDeriv (r : ℕ) (s : E → F) (x : E) {n : ℕ} (hn : n ≤ r) :
    jetFTaylorSeries r (fun i ↦ iteratedFDeriv 𝕜 i.val s x) n = ftaylorSeries 𝕜 s x n := by
  simp [jetFTaylorSeries, Nat.lt_succ_of_le hn, ftaylorSeries]

/-! ### Nonlinear higher-order jet coordinate changes -/

/-- Transform an `r`-jet coordinate tuple `j` along a base map `h : E' → E` and a possibly
nonlinear, base-dependent fibre map `g : E' × F → G` at `x : E'`. This implements the derivatives
through order `r` of the transformed section `y ↦ g (y, s (h y))` via Faà di Bruno composition. -/
def jetCoordChange (r : ℕ) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    (i : Fin (r + 1)) → E' [×i.val]→L[𝕜] G :=
  fun i ↦ ((ftaylorSeries 𝕜 g (x, j 0 0)).taylorComp
    ((FormalMultilinearSeries.id 𝕜 E' x).prod
      ((jetFTaylorSeries r j).taylorComp (ftaylorSeries 𝕜 h x)))) i.val

/-- Unfold `jetCoordChange` at order `i` into its Faà di Bruno formal series expression. -/
theorem jetCoordChange_apply (r : ℕ) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (i : Fin (r + 1)) :
    jetCoordChange r h g x j i = ((ftaylorSeries 𝕜 g (x, j 0 0)).taylorComp
      ((FormalMultilinearSeries.id 𝕜 E' x).prod
        ((jetFTaylorSeries r j).taylorComp (ftaylorSeries 𝕜 h x)))) i.val := (rfl)

theorem jetCoordChange_zero_apply (r : ℕ) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (v : Fin (0 : Fin (r + 1)).val → E') :
    jetCoordChange r h g x j 0 v = g (x, j 0 0) :=
  (FormalMultilinearSeries.taylorComp_zero_apply (ftaylorSeries 𝕜 g (x, j 0 0)) _ v).trans
    (iteratedFDeriv_zero_apply _)

theorem jetCoordChange_zero (r : ℕ) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    jetCoordChange r h g x j 0 = (continuousMultilinearCurryFin0 𝕜 E' G).symm (g (x, j 0 0)) :=
  ContinuousMultilinearMap.ext (jetCoordChange_zero_apply r h g x j)

theorem jetCoordChange_one_apply {r : ℕ} (hr : 1 ≤ r) (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (v : Fin 1 → E') :
    jetCoordChange r h g x j ⟨1, Nat.lt_succ_of_le hr⟩ v =
      fderiv 𝕜 g (x, j 0 0) (v 0, j ⟨1, Nat.lt_succ_of_le hr⟩ ![fderiv 𝕜 h x (v 0)]) := by
  rw [jetCoordChange_apply]
  simp [TauCeti.ftaylorSeries_apply, FormalMultilinearSeries.id_apply_one,
    iteratedFDeriv_one_apply, jetFTaylorSeries_apply_of_lt r j (Nat.lt_succ_of_le hr)]

/-- At order `1`, `TauCeti.jetCoordChange` agrees with `TauCeti.firstJetCoordChange` under currying
of order-zero and order-one multilinear maps. -/
theorem firstJetCoordChange_eq_jetCoordChange (h : E' → E) (g : E' × F → G) (x : E')
    (j : (i : Fin 2) → E [×i.val]→L[𝕜] F) :
    firstJetCoordChange h g x (j 0 0, continuousMultilinearCurryFin1 𝕜 E F (j 1)) =
      (jetCoordChange 1 h g x j 0 0,
        continuousMultilinearCurryFin1 𝕜 E' G (jetCoordChange 1 h g x j 1)) :=
  Prod.ext ((firstJetCoordChange_fst h g x _).trans (jetCoordChange_zero_apply 1 h g x j 0).symm)
    (ContinuousLinearMap.ext fun w ↦ by
      simpa using (jetCoordChange_one_apply (le_refl 1) h g x j ![w]).symm)

/-- Higher-order jet coordinate changes depend only on the germs of the coordinate maps. -/
theorem jetCoordChange_congr {r : ℕ} {h h' : E' → E} {g g' : E' × F → G} {x : E'}
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hh : h =ᶠ[𝓝 x] h') (hg : g =ᶠ[𝓝 (x, j 0 0)] g') :
    jetCoordChange r h g x j = jetCoordChange r h' g' x j := by
  funext _
  simp only [jetCoordChange_apply, (hh.ftaylorSeries 𝕜).eq_of_nhds,
    (hg.ftaylorSeries 𝕜).eq_of_nhds]

/-- Nonlinear jet coordinate changes commute with truncation to any lower order. -/
@[simp]
theorem jetTruncate_jetCoordChange {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂)
    (h : E' → E) (g : E' × F → G) (x : E') (j : (i : Fin (r₂ + 1)) → E [×i.val]→L[𝕜] F) :
    jetTruncate hle (jetCoordChange r₂ h g x j) =
      jetCoordChange r₁ h g x (jetTruncate hle j) := by
  funext i
  refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) fun _ _ hk ↦ ?_
  simp only [FormalMultilinearSeries.prod_apply]
  exact congrArg _ <| FormalMultilinearSeries.taylorComp_congr
    (fun _ hm ↦ (jetFTaylorSeries_jetTruncate hle j
      (hm.trans (hk.trans (Nat.le_of_lt_succ i.isLt)))).symm) (fun _ _ _ ↦ rfl)

/-- **Higher-order chain rule on local sections.** Transforming the `r`-jet of a `C^r` section `s`
by `jetCoordChange` gives the `r`-jet of the transformed section `y ↦ g (y, s (h y))`. -/
theorem jetCoordChange_iteratedFDeriv {r : ℕ} {h : E' → E} {g : E' × F → G} {s : E → F} {x : E'}
    (hh : ContDiffAt 𝕜 r h x) (hs : ContDiffAt 𝕜 r s (h x))
    (hg : ContDiffAt 𝕜 r g (x, s (h x))) :
    jetCoordChange r h g x (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s (h x)) =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val (fun y ↦ g (y, s (h y))) x := by
  funext i
  have hi_le : i.val ≤ r := Nat.le_of_lt_succ i.isLt
  have hsh : ContDiffAt 𝕜 r (s ∘ h) x := hs.comp x hh
  have hgraph : ContDiffAt 𝕜 r (fun y ↦ (y, (s ∘ h) y)) x := contDiffAt_id.prodMk hsh
  have hcomp : (fun y ↦ g (y, s (h y))) = g ∘ fun y ↦ (y, (s ∘ h) y) :=
    funext fun _ ↦ by simp only [Function.comp_apply]
  rw [jetCoordChange_apply, hcomp,
    iteratedFDeriv_comp (f := fun y ↦ (y, (s ∘ h) y)) hg hgraph (Nat.cast_le.mpr hi_le)]
  refine FormalMultilinearSeries.taylorComp_congr (fun k _ ↦ by
    rw [Function.comp_apply]
    exact congrArg (fun z ↦ ftaylorSeries 𝕜 g (x, z) k) (iteratedFDeriv_zero_apply _))
    fun k _ hk ↦ ?_
  have hk_r : (k : ℕ∞ω) ≤ r := Nat.cast_le.mpr (hk.trans hi_le)
  refine (congrArg₂ ContinuousMultilinearMap.prod
    (congrFun (TauCeti.ftaylorSeries_id x).symm k) ?_).trans
      (iteratedFDeriv_prodMk contDiffAt_id hsh hk_r).symm
  rw [iteratedFDeriv_comp hs hh hk_r]
  exact FormalMultilinearSeries.taylorComp_congr
    (fun _ hm ↦ jetFTaylorSeries_iteratedFDeriv r s (h x) (hm.trans (hk.trans hi_le)))
    (fun _ _ _ ↦ rfl)

/-- Identity base and fibre coordinate changes act as the identity on all `r`-jet tuples. -/
@[simp]
theorem jetCoordChange_id (r : ℕ) (x : E) (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    jetCoordChange r (id : E → E) (Prod.snd : E × F → F) x j = j := by
  funext i
  rw [jetCoordChange_apply, TauCeti.ftaylorSeries_id, FormalMultilinearSeries.taylorComp_id]
  have hsnd := FormalMultilinearSeries.ftaylorSeries_snd_taylorComp_prod
    (FormalMultilinearSeries.id 𝕜 E x) (jetFTaylorSeries r j) x 0
  rw [jetFTaylorSeries_zero] at hsnd
  exact (congrFun hsnd i.val).trans (jetFTaylorSeries_apply r j i)

/-- Common Faà di Bruno series normal form for the two sides of `jetCoordChange_comp`. -/
private def jetCoordChangeCompSeries (r : ℕ) (h : E' → E) (k : E'' → E')
    (g : E' × F → G) (l : E'' × G → H) (y : E'')
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E'' H :=
  (ftaylorSeries 𝕜 l (y, g (k y, j 0 0))).taylorComp
    ((FormalMultilinearSeries.id 𝕜 E'' y).prod
      ((ftaylorSeries 𝕜 g (k y, j 0 0)).taylorComp
        ((ftaylorSeries 𝕜 k y).prod
          ((jetFTaylorSeries r j).taylorComp (ftaylorSeries 𝕜 (h ∘ k) y)))))

private theorem jetCoordChange_comp_lhs {r : ℕ} {h : E' → E} {k : E'' → E'}
    {g : E' × F → G} {l : E'' × G → H} {y : E''}
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hh : ContDiffAt 𝕜 r h (k y)) (hk : ContDiffAt 𝕜 r k y) (i : Fin (r + 1)) :
    jetCoordChange r k l y (jetCoordChange r h g (k y) j) i =
      jetCoordChangeCompSeries r h k g l y j i.val := by
  have hi_le : i.val ≤ r := Nat.le_of_lt_succ i.isLt
  let G₁ := (FormalMultilinearSeries.id 𝕜 E' (k y)).prod
    ((jetFTaylorSeries r j).taylorComp (ftaylorSeries 𝕜 h (k y)))
  rw [jetCoordChange_apply, jetCoordChange_zero_apply, jetCoordChangeCompSeries]
  refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) fun m _ hm ↦ ?_
  simp only [FormalMultilinearSeries.prod_apply]
  congr 1
  rw [FormalMultilinearSeries.taylorComp_congr
    (q₂ := (ftaylorSeries 𝕜 g (k y, j 0 0)).taylorComp G₁)
    (fun a ha ↦ jetFTaylorSeries_apply_of_lt r _ (Nat.lt_succ_of_le (ha.trans (hm.trans hi_le))))
    (fun _ _ _ ↦ rfl), FormalMultilinearSeries.taylorComp_assoc]
  refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) fun n _ hn_le ↦ ?_
  have hk0 : ftaylorSeries 𝕜 k y 0 ![] = k y := iteratedFDeriv_zero_apply _
  simp only [G₁, FormalMultilinearSeries.prod_taylorComp, ← hk0,
    FormalMultilinearSeries.id_taylorComp, FormalMultilinearSeries.taylorComp_assoc,
    FormalMultilinearSeries.prod_apply]
  exact congrArg _ <| FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) fun _ _ ha ↦
    (iteratedFDeriv_comp hh hk (Nat.cast_le.mpr (ha.trans (hn_le.trans (hm.trans hi_le))))).symm

private theorem jetCoordChange_comp_rhs {r : ℕ} {h : E' → E} {k : E'' → E'}
    {g : E' × F → G} {l : E'' × G → H} {y : E''}
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hk : ContDiffAt 𝕜 r k y) (hg : ContDiffAt 𝕜 r g (k y, j 0 0))
    (hl : ContDiffAt 𝕜 r l (y, g (k y, j 0 0))) (i : Fin (r + 1)) :
    jetCoordChange r (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) y j i =
      jetCoordChangeCompSeries r h k g l y j i.val := by
  have hi_le : i.val ≤ r := Nat.le_of_lt_succ i.isLt
  let P := (jetFTaylorSeries r j).taylorComp (ftaylorSeries 𝕜 (h ∘ k) y)
  let Q := (FormalMultilinearSeries.id 𝕜 E'' y).prod P
  have hfstQ : (ftaylorSeries 𝕜 (Prod.fst : E'' × F → E'') (y, j 0 0)).taylorComp Q =
      FormalMultilinearSeries.id 𝕜 E'' y := by
    simpa [FormalMultilinearSeries.id_apply_zero] using
      FormalMultilinearSeries.ftaylorSeries_fst_taylorComp_prod
        (FormalMultilinearSeries.id 𝕜 E'' y) P 0 (j 0 0)
  have hsndQ : (ftaylorSeries 𝕜 (Prod.snd : E'' × F → F) (y, j 0 0)).taylorComp Q = P := by
    have hP0 : P 0 ![] = j 0 0 :=
      (FormalMultilinearSeries.taylorComp_zero_apply _ _ ![]).trans
        (by rw [jetFTaylorSeries_zero]; exact congrArg (j 0) (funext fun a ↦ Fin.elim0 a))
    simpa [hP0] using FormalMultilinearSeries.ftaylorSeries_snd_taylorComp_prod
      (FormalMultilinearSeries.id 𝕜 E'' y) P y 0
  let ψ : E'' × F → E' × F := fun p ↦ ((k ∘ Prod.fst) p, p.2)
  have hψ : ContDiffAt 𝕜 r ψ (y, j 0 0) :=
    (hk.comp (y, j 0 0) contDiffAt_fst).prodMk contDiffAt_snd
  have hgψ : ContDiffAt 𝕜 r (g ∘ ψ) (y, j 0 0) := hg.comp (y, j 0 0) hψ
  have hcomp : (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) = l ∘ fun p ↦ (p.1, (g ∘ ψ) p) :=
    funext fun _ ↦ by simp only [ψ, Function.comp_apply]
  rw [jetCoordChange_apply, hcomp, jetCoordChangeCompSeries,
    hl.ftaylorSeries_comp_taylorComp (f := fun p ↦ (p.1, (g ∘ ψ) p))
      (contDiffAt_fst.prodMk hgψ) Q (Nat.cast_le.mpr hi_le)]
  refine FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) fun m _ hm ↦ ?_
  rw [contDiffAt_fst.ftaylorSeries_prodMk_taylorComp hgψ Q (Nat.cast_le.mpr (hm.trans hi_le)),
    FormalMultilinearSeries.prod_apply, FormalMultilinearSeries.prod_apply, hfstQ,
    hg.ftaylorSeries_comp_taylorComp (f := ψ) hψ Q (Nat.cast_le.mpr (hm.trans hi_le))]
  refine congrArg _ <| FormalMultilinearSeries.taylorComp_congr (fun _ _ ↦ rfl) fun n _ hn ↦ ?_
  have hn_r : (n : ℕ∞ω) ≤ r := Nat.cast_le.mpr (hn.trans (hm.trans hi_le))
  rw [(hk.comp (y, j 0 0) contDiffAt_fst).ftaylorSeries_prodMk_taylorComp contDiffAt_snd Q hn_r,
    FormalMultilinearSeries.prod_apply, FormalMultilinearSeries.prod_apply,
    hk.ftaylorSeries_comp_taylorComp (f := Prod.fst) contDiffAt_fst Q hn_r,
    hfstQ, FormalMultilinearSeries.taylorComp_id, hsndQ]

/-- **Cocycle law for nonlinear higher-order jet coordinate changes.** Composing two nonlinear
bundle coordinate changes agrees with the coordinate change of the composite base and fibre maps,
with no symmetry or characteristic assumptions on the jet tuple `j`. -/
theorem jetCoordChange_comp {r : ℕ} {h : E' → E} {k : E'' → E'}
    {g : E' × F → G} {l : E'' × G → H} {y : E''}
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hh : ContDiffAt 𝕜 r h (k y)) (hk : ContDiffAt 𝕜 r k y)
    (hg : ContDiffAt 𝕜 r g (k y, j 0 0)) (hl : ContDiffAt 𝕜 r l (y, g (k y, j 0 0))) :
    jetCoordChange r k l y (jetCoordChange r h g (k y) j) =
      jetCoordChange r (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) y j :=
  funext fun i ↦
    (jetCoordChange_comp_lhs j hh hk i).trans (jetCoordChange_comp_rhs j hk hg hl i).symm

/-- Coordinate maps that are inverse as germs induce inverse transformations of `r`-jets. -/
theorem jetCoordChange_inverse {r : ℕ} {h : E' → E} {k : E → E'}
    {g : E' × F → G} {l : E × G → F} {x : E}
    (j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hh : ContDiffAt 𝕜 r h (k x)) (hk : ContDiffAt 𝕜 r k x)
    (hg : ContDiffAt 𝕜 r g (k x, j 0 0)) (hl : ContDiffAt 𝕜 r l (x, g (k x, j 0 0)))
    (hbase : h ∘ k =ᶠ[𝓝 x] id)
    (hfibre : (fun p : E × F ↦ l (p.1, g (k p.1, p.2))) =ᶠ[𝓝 (x, j 0 0)] Prod.snd) :
    jetCoordChange r k l x (jetCoordChange r h g (k x) j) = j := by
  rw [jetCoordChange_comp j hh hk hg hl]
  exact (jetCoordChange_congr j hbase hfibre).trans (jetCoordChange_id r x j)

/-! ### Symmetry preservation -/

/-- Over any nontrivially normed field, `jetCoordChange` preserves slot symmetry of `r`-jets
whenever `h` and `g` have smoothness at least `minSmoothness 𝕜 r`. -/
theorem jetCoordChange_comp_perm {r : ℕ} {n : ℕ∞ω}
    {h : E' → E} {g : E' × F → G} {x : E'}
    {j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F}
    (hn : minSmoothness 𝕜 r ≤ n) (hh : ContDiffAt 𝕜 n h x) (hg : ContDiffAt 𝕜 n g (x, j 0 0))
    (hj : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), j i (v ∘ σ) = j i v)
    (i : Fin (r + 1)) (v : Fin i.val → E') (σ : Equiv.Perm (Fin i.val)) :
    jetCoordChange r h g x j i (v ∘ σ) = jetCoordChange r h g x j i v := by
  have hi_le : i.val ≤ r := Nat.le_of_lt_succ i.isLt
  refine FormalMultilinearSeries.taylorComp_comp_perm _ _
    (fun _ _ hk w π ↦ hg.iteratedFDeriv_comp_perm_of_minSmoothness
      ((minSmoothness_monotone (Nat.cast_le.mpr (hk.trans hi_le))).trans hn) w π)
    (fun k hk2 hk u τ ↦ Prod.ext
      (by simp [FormalMultilinearSeries.id_apply_of_one_lt _ _ _
        (Nat.lt_of_lt_of_le Nat.one_lt_two hk2)])
      (FormalMultilinearSeries.taylorComp_comp_perm _ _
        (fun m _ hm w π ↦ by
          have hm_lt : m < r + 1 := Nat.lt_succ_of_le (hm.trans (hk.trans hi_le))
          simpa [jetFTaylorSeries_apply_of_lt r j hm_lt] using hj ⟨m, hm_lt⟩ w π)
        (fun _ _ hm w π ↦ hh.iteratedFDeriv_comp_perm_of_minSmoothness
          ((minSmoothness_monotone (Nat.cast_le.mpr (hm.trans (hk.trans hi_le)))).trans hn) w π)
        u τ)) v σ

/-- Over `ℝ` or `ℂ` (`IsRCLikeNormedField 𝕜`), `C^r` coordinate maps preserve slot symmetry of
`r`-jets. -/
theorem jetCoordChange_comp_perm_of_isRCLikeNormedField [IsRCLikeNormedField 𝕜] {r : ℕ}
    {h : E' → E} {g : E' × F → G} {x : E'}
    {j : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F}
    (hh : ContDiffAt 𝕜 r h x) (hg : ContDiffAt 𝕜 r g (x, j 0 0))
    (hj : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), j i (v ∘ σ) = j i v)
    (i : Fin (r + 1)) (v : Fin i.val → E') (σ : Equiv.Perm (Fin i.val)) :
    jetCoordChange r h g x j i (v ∘ σ) = jetCoordChange r h g x j i v :=
  jetCoordChange_comp_perm (by rw [minSmoothness_of_isRCLikeNormedField]) hh hg hj i v σ

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
  have hj0 : j₁ 0 = j₂ 0 := hj 0 hi
  have hj_lt {m : ℕ} (hm : m < i.val) : jetFTaylorSeries r j₁ m = jetFTaylorSeries r j₂ m := by
    have hm_lt : m < r + 1 := hm.trans i.isLt
    rw [jetFTaylorSeries_apply_of_lt r j₁ hm_lt, jetFTaylorSeries_apply_of_lt r j₂ hm_lt]
    exact hj ⟨m, hm_lt⟩ hm
  have hG_lt (k : ℕ) (_ : 1 ≤ k) (hk : k < i.val) :
      ((FormalMultilinearSeries.id 𝕜 E' x).prod
          ((jetFTaylorSeries r j₁).taylorComp (ftaylorSeries 𝕜 h x))) k =
        ((FormalMultilinearSeries.id 𝕜 E' x).prod
          ((jetFTaylorSeries r j₂).taylorComp (ftaylorSeries 𝕜 h x))) k := by
    simp only [FormalMultilinearSeries.prod_apply]
    exact congrArg _ <| FormalMultilinearSeries.taylorComp_congr
      (fun _ hm ↦ hj_lt (hm.trans_lt hk)) (fun _ _ _ ↦ rfl)
  rw [jetCoordChange_apply, jetCoordChange_apply, ← hj0,
    FormalMultilinearSeries.taylorComp_sub_taylorComp_of_eq_lt_right _ hi hG_lt]
  have hinner : (jetFTaylorSeries r j₁).taylorComp (ftaylorSeries 𝕜 h x) i.val -
      (jetFTaylorSeries r j₂).taylorComp (ftaylorSeries 𝕜 h x) i.val =
      (j₁ i - j₂ i).compContinuousLinearMap fun _ ↦ fderiv 𝕜 h x := by
    rw [FormalMultilinearSeries.taylorComp_sub_taylorComp_of_eq_lt_left _ fun _ _ hm ↦ hj_lt hm,
      jetFTaylorSeries_apply, jetFTaylorSeries_apply]
    simp only [TauCeti.ftaylorSeries_apply, continuousMultilinearCurryFin1_iteratedFDeriv_one]
  ext v
  simp only [TauCeti.ftaylorSeries_apply, continuousMultilinearCurryFin1_iteratedFDeriv_one,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, comp_apply,
    inr_apply, _root_.sub_apply, FormalMultilinearSeries.prod_apply,
    ContinuousMultilinearMap.prod_apply, Prod.mk_sub_mk, sub_self]
  rw [← _root_.sub_apply, hinner]

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
          fun _ ↦ fderiv 𝕜 h x) :=
  jetCoordChange_sub_of_eq_lt h g x (Nat.succ_pos r) fun k hk ↦ by
    have hk' : k.val < r + 1 := by simpa using hk
    simpa using congrFun hj ⟨k.val, hk'⟩

/-- Over a fixed lower `r`-jet `j₀`, the top-order coordinate of `jetCoordChange` on `jetSnoc j₀ A`
equals its linear action on `A` plus the inhomogeneous term at `A = 0`. -/
theorem jetCoordChange_jetSnoc_last_eq {r : ℕ} (h : E' → E) (g : E' × F → G) (x : E')
    (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (A : E [×(r + 1)]→L[𝕜] F) :
    jetCoordChange (r + 1) h g x (jetSnoc j₀ A) (Fin.last (r + 1)) =
      ((fderiv 𝕜 g (x, j₀ 0 0)).comp (inr 𝕜 E' F)).compContinuousMultilinearMap
        (A.compContinuousLinearMap fun _ : Fin (Fin.last (r + 1)).val ↦ fderiv 𝕜 h x) +
        jetCoordChange (r + 1) h g x (jetSnoc j₀ 0) (Fin.last (r + 1)) := by
  have hd := jetCoordChange_last_sub h g x (j₁ := jetSnoc j₀ A) (j₂ := jetSnoc j₀ 0) (by simp)
  rw [jetSnoc_zero_apply, jetSnoc_last, jetSnoc_last, sub_zero] at hd
  exact sub_eq_iff_eq_add.mp hd

/-- Over a fixed lower `r`-jet `j₀`, if the vertical derivative of `g` and the base derivative of
`h` are invertible continuous linear maps, the affine map on the top-order multilinear coordinate
is bijective. -/
theorem jetCoordChange_last_bijective {r : ℕ} (h : E' → E) (g : E' × F → G) (x : E')
    (j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (a : F ≃L[𝕜] G) (c : E' ≃L[𝕜] E)
    (ha : (fderiv 𝕜 g (x, j₀ 0 0)).comp (inr 𝕜 E' F) = a.toContinuousLinearMap)
    (hc : fderiv 𝕜 h x = c.toContinuousLinearMap) :
    Function.Bijective (fun A : E [×(r + 1)]→L[𝕜] F ↦
      jetCoordChange (r + 1) h g x (jetSnoc j₀ A) (Fin.last (r + 1))) := by
  let e := (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F
    (fun _ : Fin (Fin.last (r + 1)).val ↦ c)).trans (a.continuousMultilinearMapCongrRight _)
  suffices (fun A ↦ jetCoordChange (r + 1) h g x (jetSnoc j₀ A) (Fin.last (r + 1))) =
      fun A ↦ e A + jetCoordChange (r + 1) h g x (jetSnoc j₀ 0) (Fin.last (r + 1)) from
    this ▸ (Equiv.addRight _).bijective.comp e.bijective
  funext A
  rw [jetCoordChange_jetSnoc_last_eq h g x j₀ A, ha, hc]
  simp [e]

/-- Appending a slot-symmetric top-order multilinear map to a slot-symmetric `r`-jet yields a
slot-symmetric `(r + 1)`-jet. -/
theorem jetSnoc_comp_perm {r : ℕ}
    {j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F} {A : E [×(r + 1)]→L[𝕜] F}
    (hj₀ : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), j₀ i (v ∘ σ) = j₀ i v)
    (hA : ∀ (v : Fin (r + 1) → E) (σ : Equiv.Perm (Fin (r + 1))), A (v ∘ σ) = A v)
    (i : Fin (r + 2)) (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)) :
    jetSnoc j₀ A i (v ∘ σ) = jetSnoc j₀ A i v :=
  Fin.lastCases (by simpa using hA) (fun k ↦ by simpa using hj₀ k) i v σ

/-- Over a fixed slot-symmetric `r`-jet `j₀`, `jetCoordChange` sends any slot-symmetric top-order
multilinear map `A` to a slot-symmetric top-order multilinear map. -/
theorem jetCoordChange_jetSnoc_last_comp_perm {r : ℕ} {n : ℕ∞ω}
    {h : E' → E} {g : E' × F → G} {x : E'}
    {j₀ : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F} {A : E [×(r + 1)]→L[𝕜] F}
    (hn : minSmoothness 𝕜 (r + 1) ≤ n) (hh : ContDiffAt 𝕜 n h x)
    (hg : ContDiffAt 𝕜 n g (x, j₀ 0 0))
    (hj₀ : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), j₀ i (v ∘ σ) = j₀ i v)
    (hA : ∀ (v : Fin (r + 1) → E) (σ : Equiv.Perm (Fin (r + 1))), A (v ∘ σ) = A v)
    (v : Fin (Fin.last (r + 1)).val → E') (σ : Equiv.Perm (Fin (Fin.last (r + 1)).val)) :
    jetCoordChange (r + 1) h g x (jetSnoc j₀ A) (Fin.last (r + 1)) (v ∘ σ) =
      jetCoordChange (r + 1) h g x (jetSnoc j₀ A) (Fin.last (r + 1)) v :=
  jetCoordChange_comp_perm hn hh (by simpa only [jetSnoc_zero_apply] using hg)
    (jetSnoc_comp_perm hj₀ hA) (Fin.last (r + 1)) v σ

/-- Over any nontrivially normed field, if `h` and `g` have smoothness at least
`minSmoothness 𝕜 (r + 1)` and invertible base and vertical derivatives, then over a fixed symmetric
lower `r`-jet `j₀` the induced affine map on symmetric `(r + 1)`-multilinear maps (the model fibre
of `J^{r+1}E → J^rE`) is bijective. -/
theorem jetCoordChange_last_symmetric_bijective {r : ℕ} {n : ℕ∞ω}
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
        (⟨jetCoordChange (r + 1) h g x (jetSnoc j₀ A.val) (Fin.last (r + 1)),
          jetCoordChange_jetSnoc_last_comp_perm hn hh hg hj₀ A.property⟩ :
          {B : E' [×(Fin.last (r + 1)).val]→L[𝕜] G //
            ∀ (v : Fin (Fin.last (r + 1)).val → E')
              (σ : Equiv.Perm (Fin (Fin.last (r + 1)).val)), B (v ∘ σ) = B v})) := by
  have hbij := jetCoordChange_last_bijective h g x j₀ a c ha hc
  refine ⟨fun _ _ hEq ↦ Subtype.ext (hbij.1 (congrArg Subtype.val hEq)), fun B ↦ ?_⟩
  obtain ⟨A, hA⟩ := hbij.2 B.val
  dsimp only at hA
  have hB0 := jetCoordChange_jetSnoc_last_comp_perm hn hh hg hj₀
    (A := (0 : E [×(r + 1)]→L[𝕜] F)) (fun _ _ ↦ rfl)
  have hv (u : Fin (r + 1) → E) : a (A u) =
      (B.val - jetCoordChange (r + 1) h g x (jetSnoc j₀ 0) (Fin.last (r + 1))) (c.symm ∘ u) := by
    rw [← hA, jetCoordChange_jetSnoc_last_eq h g x j₀ A, ha, hc, add_sub_cancel_right]
    simp [Function.comp_def]
  refine ⟨⟨A, fun v σ ↦ a.injective ?_⟩, Subtype.ext hA⟩
  rw [hv (v ∘ σ), hv v, _root_.sub_apply, _root_.sub_apply]
  exact congrArg₂ (· - ·) (B.property (c.symm ∘ v) σ) (hB0 (c.symm ∘ v) σ)

/-! ### Smoothness on bundle-chart domains -/

/-- Smooth base and nonlinear fibre maps induce `C^m` transitions of `r`-jet coordinates at any
point `p₀` where `h` is `C^n` at `p₀.1` and `g` is `C^n` at `(p₀.1, p₀.2 0 0)` with `m + r ≤ n`
(the `r`-jet transition consumes `r` derivatives). -/
theorem contDiffAt_jetCoordChange {r : ℕ} {n m : ℕ∞ω} {h : E' → E} {g : E' × F → G}
    {p₀ : E' × ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)}
    (hh : ContDiffAt 𝕜 n h p₀.1) (hg : ContDiffAt 𝕜 n g (p₀.1, p₀.2 0 0)) (hmn : m + r ≤ n) :
    ContDiffAt 𝕜 m
      (fun p : E' × ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) ↦ jetCoordChange r h g p.1 p.2)
      p₀ := by
  refine contDiffAt_pi.mpr fun i ↦ ?_
  have hi_le : i.val ≤ r := Nat.le_of_lt_succ i.isLt
  have hxv : ContDiffAt 𝕜 m
      (fun p : E' × ((k : Fin (r + 1)) → E [×k.val]→L[𝕜] F) ↦ (p.1, p.2 0 0)) p₀ :=
    contDiffAt_fst.prodMk ((continuousMultilinearCurryFin0 𝕜 E F).contDiff.comp
      ((contDiff_apply 𝕜 _ (0 : Fin (r + 1))).comp contDiff_snd)).contDiffAt
  refine ContDiffAt.taylorComp
    (fun _ hk ↦ (hg.iteratedFDeriv_right
      ((add_le_add_right (Nat.cast_le.mpr (hk.trans hi_le)) m).trans hmn)).comp p₀ hxv)
    (fun k hk_pos hk_le ↦ (ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin k ↦ E') E' F)
      |>.contDiff.contDiffAt.comp p₀ (ContDiffAt.prodMk ?_ (ContDiffAt.taylorComp
        (fun a ha ↦ by
          have ha_lt : a < r + 1 := Nat.lt_succ_of_le (ha.trans (hk_le.trans hi_le))
          simp only [jetFTaylorSeries_apply_of_lt r _ ha_lt]
          exact ((contDiff_apply 𝕜 _ (⟨a, ha_lt⟩ : Fin (r + 1))).comp contDiff_snd).contDiffAt)
        (fun _ _ ha ↦ (hh.iteratedFDeriv_right
          ((add_le_add_right (Nat.cast_le.mpr (ha.trans (hk_le.trans hi_le))) m).trans hmn)).comp
          p₀ contDiffAt_fst))))
  rcases k with _ | _ | k
  · omega
  · exact contDiffAt_const
  · exact contDiffAt_const

/-- Smooth base and nonlinear fibre maps induce `C^m` transitions of `r`-jet coordinates on open
bundle-chart domains whenever `h` and `g` are `C^n` with `m + r ≤ n` (the `r`-jet transition
consumes `r` derivatives). -/
theorem contDiffOn_jetCoordChange {r : ℕ} {n m : ℕ∞ω} {u : Set E'} {v : Set (E' × F)}
    {h : E' → E} {g : E' × F → G} (hu : IsOpen u) (hv : IsOpen v)
    (hh : ContDiffOn 𝕜 n h u) (hg : ContDiffOn 𝕜 n g v) (hmn : m + r ≤ n) :
    ContDiffOn 𝕜 m
      (fun p : E' × ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) ↦ jetCoordChange r h g p.1 p.2)
      {p | p.1 ∈ u ∧ (p.1, p.2 0 0) ∈ v} := fun _ hp ↦
  (contDiffAt_jetCoordChange (hh.contDiffAt (hu.mem_nhds hp.1))
    (hg.contDiffAt (hv.mem_nhds hp.2)) hmn).contDiffWithinAt

end TauCeti
