/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.ContinuousLinearMap
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousMultilinearMap
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Parametric
public import TauCeti.Analysis.Calculus.IteratedFDeriv.SymmetricFinite
public import TauCeti.Analysis.Calculus.Jet.Equivalence
public import TauCeti.Analysis.Calculus.Jet.Realization

/-!
# Coordinate changes of finite jets of vector bundle sections

In local coordinates, the `r`-jet of a section `s : E → F` of a vector bundle at a point `y` is
the tuple `(D⁰ s(y), D¹ s(y), …, Dʳ s(y))` of its iterated derivatives, a tuple
`A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F` of continuous multilinear maps. A change of base
coordinates `h : E' → E` together with a base-dependent linear change of fibre coordinates
`g : E' → F →L[𝕜] G` transforms the section into `z ↦ g z (s (h z))`.
`TauCeti.linearJetCoordChange r h g x` is the continuous linear map on `r`-jets taking the jet
of `s` at `h x` to the jet of the transformed section at `x`. It is the `r`-th order version of
`ContinuousLinearMap.firstJetPullback`.

It is defined by realizing a jet `A` at `h x` by its Taylor polynomial `P` of degree `r`
(`TauCeti.finiteJetPolynomial`) and differentiating `z ↦ g z (P (h z))` at `x`. By the chain
rule for jets (`TauCeti.SameJetAt.coordChange`), the result depends only on the jet of `P`, so on
actual sections it computes the transformed jet. Writing the polynomial as a continuous linear
function of its coefficients (`TauCeti.finiteJetPolynomialCLM`) makes the transformation linear
and continuous with no smoothness assumption, and smooth in `x` when `h` and `g` are.

These are the local coordinate results from which the bundle of `r`-jets of a vector bundle is
glued: its coordinate changes satisfy the identity and cocycle laws on symmetric jets, depend
only on the germs of the coordinate maps, are smooth on chart overlaps, and commute with
truncation of jets to lower order. Iterated derivatives of maps which are not analytic are
symmetric only over `ℝ` and `ℂ`, so the laws which apply the transformation to transformed jets
assume the maps are `C^n` with `minSmoothness 𝕜 r ≤ n`: `C^r` over `ℝ` or `ℂ`, analytic
otherwise.

## Main declarations

* `TauCeti.linearJetCoordChange`: the coordinate change of `r`-jets.
* `TauCeti.linearJetCoordChange_iteratedFDeriv`: it transforms the jet of a section into the jet
  of the transformed section.
* `TauCeti.linearJetCoordChange_id`, `TauCeti.linearJetCoordChange_comp`: the identity and
  cocycle laws.
* `TauCeti.linearJetCoordChange_apply_zero`: the value of a jet transforms by `g x`.
* `TauCeti.linearJetCoordChange_apply_comp_perm`: coordinate changes take values in symmetric
  jets.
* `TauCeti.linearJetCoordChange_truncate`: coordinate changes commute with truncation.
* `TauCeti.linearJetCoordChange_congr`: they depend only on the germs of `h` and `g`.
* `ContDiffAt.linearJetCoordChange`, `ContDiffOn.linearJetCoordChange`: they are smooth in the
  base point, as continuous linear maps.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5 and 12.16–12.17, for jets of vector bundles and their coordinate transformations.
-/

public section

noncomputable section

open Equiv Filter Function
open scoped ContDiff Topology

variable {𝕜 E E' E'' F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

namespace TauCeti

/-- The order of a component of an `r`-jet is at most `r`. -/
private theorem natCast_val_le {r : ℕ} (i : Fin (r + 1)) : (i.val : ℕ∞ω) ≤ r := by
  exact_mod_cast i.is_le

/-! ### The coordinate change of finite jets -/

/-- The transformed Taylor polynomial `(x, z) ↦ g z ∘ P(h x, h z)`, as a function of the center
parameter `x` and the evaluation point `z`, is as smooth as `h` and `g`. -/
private theorem contDiffAt_jetTransform {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G}
    {n : ℕ∞ω} {p : E' × E'} (hh₁ : ContDiffAt 𝕜 n h p.1) (hh₂ : ContDiffAt 𝕜 n h p.2)
    (hg : ContDiffAt 𝕜 n g p.2) :
    ContDiffAt 𝕜 n (uncurry fun x z : E' ↦
      (g z).comp (finiteJetPolynomialCLM (𝕜 := 𝕜) (F := F) r (h x) (h z))) p := by
  have hhp : ContDiffAt 𝕜 n (fun q : E' × E' ↦ (h q.1, h q.2)) p :=
    (hh₁.comp p contDiffAt_fst).prodMk (hh₂.comp p contDiffAt_snd)
  have hP := (contDiff_finiteJetPolynomialCLM (𝕜 := 𝕜) (E := E) (F := F) r
    (n := n)).comp_contDiffAt p hhp
  have hg' : ContDiffAt 𝕜 n (fun q : E' × E' ↦ g q.2) p := hg.comp p contDiffAt_snd
  exact hg'.clm_comp hP

/-- The **coordinate change of `r`-jets** under a change of base coordinates `h : E' → E` and a
base-dependent linear change of fibre coordinates `g : E' → F →L[𝕜] G`, at the point `x : E'`.
It is defined by realizing a jet `A` at `h x` by its Taylor polynomial `P` of degree `r` and
taking the `r`-jet at `x` of `z ↦ g z (P (h z))` (`TauCeti.linearJetCoordChange_apply_apply`);
this makes sense for all `h` and `g`, and is continuous linear in the jet. When `h` and `g` are
`C^r` and `s : E → F` is `C^n` with `minSmoothness 𝕜 r ≤ n` (`C^r` over `ℝ` or `ℂ`, analytic
otherwise), it takes the `r`-jet `(Dⁱ s (h x))ᵢ` of `s` at `h x` to the `r`-jet at `x` of the
transformed section `z ↦ g z (s (h z))` (`TauCeti.linearJetCoordChange_iteratedFDeriv`). -/
def linearJetCoordChange (r : ℕ) (h : E' → E) (g : E' → F →L[𝕜] G) (x : E') :
    ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) →L[𝕜] ((i : Fin (r + 1)) → E' [×i.val]→L[𝕜] G) :=
  ContinuousLinearMap.pi fun i ↦ (iteratedFDeriv 𝕜 i.val
    (fun z ↦ (g z).comp (finiteJetPolynomialCLM r (h x) (h z))) x).flipLinear

/-- Unfolding the coordinate change of jets: the component of order `i` of a transformed jet `A`
is obtained by applying the derivative of order `i` at `x` of the operator-valued map
`z ↦ g z ∘ P(h x, h z)` to `A`, where `P(c, y)` evaluates Taylor polynomials with center `c`
at `y`. -/
theorem linearJetCoordChange_apply_apply (r : ℕ) (h : E' → E) (g : E' → F →L[𝕜] G) (x : E')
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (i : Fin (r + 1)) (v : Fin i.val → E') :
    linearJetCoordChange r h g x A i v =
      iteratedFDeriv 𝕜 i.val (fun z ↦ (g z).comp (finiteJetPolynomialCLM r (h x) (h z))) x v A := by
  simp [linearJetCoordChange]

/-- The component of order `i` of a transformed jet `A` is the derivative of order `i` at `x` of
the transformed Taylor polynomial `z ↦ g z (P_A (h z))` of `A`. -/
theorem linearJetCoordChange_apply {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G} {x : E'}
    (i : Fin (r + 1)) (hh : ContDiffAt 𝕜 i.val h x) (hg : ContDiffAt 𝕜 i.val g x)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    linearJetCoordChange r h g x A i =
      iteratedFDeriv 𝕜 i.val (fun z ↦ g z (finiteJetPolynomial r A (h x) (h z))) x := by
  have hP := (contDiff_finiteJetPolynomialCLM (𝕜 := 𝕜) (E := E) (F := F) r
    (n := i.val)).comp_contDiffAt x (contDiffAt_const (c := h x) |>.prodMk hh)
  have hT : ContDiffAt 𝕜 i.val (fun z ↦ (g z).comp (finiteJetPolynomialCLM r (h x) (h z))) x :=
    hg.clm_comp hP
  have hfun : (fun z ↦ g z (finiteJetPolynomial r A (h x) (h z))) =
      ContinuousLinearMap.apply 𝕜 G A ∘
        fun z ↦ (g z).comp (finiteJetPolynomialCLM r (h x) (h z)) := by
    funext z
    simp
  rw [hfun, (ContinuousLinearMap.apply 𝕜 G A).iteratedFDeriv_comp_left hT le_rfl]
  ext v
  simp [linearJetCoordChange_apply_apply]

/-- The component of order `0` of a transformed jet: the value `A 0 0` of a jet transforms by
`g x`. -/
theorem linearJetCoordChange_apply_zero (r : ℕ) (h : E' → E) (g : E' → F →L[𝕜] G) (x : E')
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (v : Fin 0 → E') :
    linearJetCoordChange r h g x A 0 v = g x (A 0 0) := by
  -- The component of order `0` is the value at `x` of the transformed Taylor polynomial; the
  -- order is `(0 : Fin (r + 1)).val`, so state the value of a derivative of any order `k = 0`.
  have hval : ∀ (k : ℕ), k = 0 → ∀ w : Fin k → E', iteratedFDeriv 𝕜 k
      (fun z ↦ (g z).comp (finiteJetPolynomialCLM r (h x) (h z))) x w =
        (g x).comp (finiteJetPolynomialCLM r (h x) (h x)) := by
    rintro _ rfl w
    exact iteratedFDeriv_zero_apply w
  rw [linearJetCoordChange_apply_apply r h g x A 0 v, hval _ (Fin.val_zero _) v]
  simp

/-- **Coordinate changes take values in symmetric jets.** If `h` and `g` are `C^n` at `x` with
`minSmoothness 𝕜 i ≤ n` (`C^i` over `ℝ` or `ℂ`, analytic otherwise), then the component of order
`i` of any transformed jet is symmetric. -/
theorem linearJetCoordChange_apply_comp_perm {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G} {x : E'}
    {n : ℕ∞ω} (i : Fin (r + 1)) (hh : ContDiffAt 𝕜 n h x) (hg : ContDiffAt 𝕜 n g x)
    (hn : minSmoothness 𝕜 i.val ≤ n) (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (v : Fin i.val → E') (σ : Perm (Fin i.val)) :
    linearJetCoordChange r h g x A i (v ∘ σ) = linearJetCoordChange r h g x A i v := by
  have hi : (i.val : ℕ∞ω) ≤ n := le_minSmoothness.trans hn
  rw [linearJetCoordChange_apply i (hh.of_le hi) (hg.of_le hi)]
  exact (hg.clm_apply ((contDiff_finiteJetPolynomial r A (h x)).contDiffAt.comp x hh))
    |>.iteratedFDeriv_comp_perm_of_le hn v σ

/-- Coordinate changes of jets depend only on the germs of the coordinate maps. -/
theorem linearJetCoordChange_congr {r : ℕ} {h h' : E' → E} {g g' : E' → F →L[𝕜] G} {x : E'}
    (hh : h =ᶠ[𝓝 x] h') (hg : g =ᶠ[𝓝 x] g') :
    linearJetCoordChange r h g x = linearJetCoordChange r h' g' x := by
  have hT : (fun z ↦ (g z).comp (finiteJetPolynomialCLM (𝕜 := 𝕜) r (h x) (h z))) =ᶠ[𝓝 x]
      fun z ↦ (g' z).comp (finiteJetPolynomialCLM r (h' x) (h' z)) := by
    filter_upwards [hh, hg] with z hhz hgz
    rw [hhz, hgz, hh.eq_of_nhds]
  simp only [linearJetCoordChange, (hT.iteratedFDeriv 𝕜 _).eq_of_nhds]

/-- **The chain rule for jets.** If the Taylor polynomial of the jet `A` at `h x` has the same
`r`-jet at `h x` as a map `s`, then the transformed jet is the `r`-jet at `x` of the transformed
map `z ↦ g z (s (h z))`. -/
theorem linearJetCoordChange_eq_of_sameJetAt {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G}
    {x : E'} {s : E → F} {A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F}
    (hA : SameJetAt 𝕜 r (h x) (finiteJetPolynomial r A (h x)) s)
    (hs : ContDiffAt 𝕜 r s (h x)) (hh : ContDiffAt 𝕜 r h x) (hg : ContDiffAt 𝕜 r g x) :
    linearJetCoordChange r h g x A =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val (fun z ↦ g z (s (h z))) x := by
  funext i
  rw [linearJetCoordChange_apply i (hh.of_le (natCast_val_le i)) (hg.of_le (natCast_val_le i))]
  -- The fibre map `(z, v) ↦ g z v` is smooth, so the chain rule for jets applies.
  have ha : ContDiffAt 𝕜 r (fun p : E' × F ↦ g p.1 p.2)
      (x, finiteJetPolynomial r A (h x) (h x)) :=
    (hg.comp _ contDiffAt_fst).clm_apply contDiffAt_snd
  exact (hA.coordChange (a := fun p : E' × F ↦ g p.1 p.2)
    (contDiff_finiteJetPolynomial r A (h x)).contDiffAt hs hh ha).iteratedFDeriv_eq
      i.is_le

/-- **Coordinate changes of jets of sections.** If `h` and `g` are `C^r` at `x` and `s` is `C^n`
at `h x` with `minSmoothness 𝕜 r ≤ n` (`C^r` over `ℝ` or `ℂ`, analytic otherwise), the coordinate
change of `r`-jets takes the `r`-jet of `s` at `h x` to the `r`-jet at `x` of the transformed map
`z ↦ g z (s (h z))`. -/
theorem linearJetCoordChange_iteratedFDeriv [CharZero 𝕜] {r : ℕ} {n : ℕ∞ω} {h : E' → E}
    {g : E' → F →L[𝕜] G} {x : E'} {s : E → F} (hs : ContDiffAt 𝕜 n s (h x))
    (hn : minSmoothness 𝕜 r ≤ n) (hh : ContDiffAt 𝕜 r h x) (hg : ContDiffAt 𝕜 r g x) :
    linearJetCoordChange r h g x (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s (h x)) =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val (fun z ↦ g z (s (h z))) x :=
  linearJetCoordChange_eq_of_sameJetAt (sameJetAt_finiteJetPolynomial_iteratedFDeriv hs hn)
    (hs.of_le (le_minSmoothness.trans hn)) hh hg

/-- **The identity law.** The identity coordinate change fixes every symmetric jet. -/
theorem linearJetCoordChange_id [CharZero 𝕜] {r : ℕ} (x : E)
    {A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F}
    (hA : ∀ i (v : Fin i.val → E) (σ : Perm (Fin i.val)), A i (v ∘ σ) = A i v) :
    linearJetCoordChange r id (fun _ ↦ ContinuousLinearMap.id 𝕜 F) x A = A := by
  funext i
  rw [linearJetCoordChange_apply i contDiffAt_id contDiffAt_const]
  exact iteratedFDeriv_finiteJetPolynomial_self r A x i (hA i)

/-- **The cocycle law.** If `h₁` and `g₁` are `C^n` at `h₂ x` with `minSmoothness 𝕜 r ≤ n`
(`C^r` over `ℝ` or `ℂ`, analytic otherwise) and `h₂` and `g₂` are `C^r` at `x`, then transforming
a jet first by `(h₁, g₁)` at `h₂ x` and then by `(h₂, g₂)` at `x` is transforming it by the
composite coordinate change `(h₁ ∘ h₂, z ↦ g₂ z ∘ g₁ (h₂ z))` at `x`. -/
theorem linearJetCoordChange_comp [CharZero 𝕜] {r : ℕ} {n : ℕ∞ω}
    {h₁ : E' → E} {g₁ : E' → F →L[𝕜] G} {h₂ : E'' → E'} {g₂ : E'' → G →L[𝕜] H} {x : E''}
    (hh₁ : ContDiffAt 𝕜 n h₁ (h₂ x)) (hg₁ : ContDiffAt 𝕜 n g₁ (h₂ x))
    (hn : minSmoothness 𝕜 r ≤ n) (hh₂ : ContDiffAt 𝕜 r h₂ x) (hg₂ : ContDiffAt 𝕜 r g₂ x)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    linearJetCoordChange r h₂ g₂ x (linearJetCoordChange r h₁ g₁ (h₂ x) A) =
      linearJetCoordChange r (h₁ ∘ h₂) (fun z ↦ (g₂ z).comp (g₁ (h₂ z))) x A := by
  -- The first transformation is the jet of the transformed Taylor polynomial `σ` of `A`.
  set σ : E' → G := fun t ↦ g₁ t (finiteJetPolynomial r A (h₁ (h₂ x)) (h₁ t))
  have hσd : ContDiffAt 𝕜 n σ (h₂ x) :=
    hg₁.clm_apply ((contDiff_finiteJetPolynomial r A _).contDiffAt.comp _ hh₁)
  replace hh₁ := hh₁.of_le (le_minSmoothness.trans hn)
  replace hg₁ := hg₁.of_le (le_minSmoothness.trans hn)
  have h₁A : linearJetCoordChange r h₁ g₁ (h₂ x) A =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val σ (h₂ x) := by
    funext i
    exact linearJetCoordChange_apply i (hh₁.of_le (natCast_val_le i)) (hg₁.of_le (natCast_val_le i))
      A
  rw [h₁A, linearJetCoordChange_iteratedFDeriv hσd hn hh₂ hg₂]
  funext i
  rw [linearJetCoordChange_apply (g := fun z ↦ (g₂ z).comp (g₁ (h₂ z))) i
    ((hh₁.comp x hh₂).of_le (natCast_val_le i))
    ((hg₂.clm_comp (hg₁.comp x hh₂)).of_le (natCast_val_le i))]
  simp [σ]

/-- **Truncation commutes with coordinate changes.** Truncating a transformed `r`-jet to order
`r' ≤ r` gives the transformed truncated jet. -/
theorem linearJetCoordChange_truncate {r r' : ℕ} (hr : r' ≤ r) {h : E' → E}
    {g : E' → F →L[𝕜] G} {x : E'} (hh : ContDiffAt 𝕜 r' h x) (hg : ContDiffAt 𝕜 r' g x)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    (fun i : Fin (r' + 1) ↦ linearJetCoordChange r h g x A (Fin.castLE (by omega) i)) =
      linearJetCoordChange r' h g x (fun i ↦ A (Fin.castLE (by omega) i)) := by
  -- The Taylor polynomials of `A` and of its truncation have the same `r'`-jet at `h x`.
  rw [linearJetCoordChange_eq_of_sameJetAt (sameJetAt_finiteJetPolynomial_castLE hr A (h x)).symm
    (contDiff_finiteJetPolynomial r A (h x)).contDiffAt hh hg]
  funext i
  have hi : ((Fin.castLE (by omega) i : Fin (r + 1)).val : ℕ∞ω) ≤ r' := by
    rw [Fin.val_castLE]
    exact natCast_val_le i
  exact linearJetCoordChange_apply _ (hh.of_le hi) (hg.of_le hi) A

end TauCeti

open TauCeti

/-- **Smoothness of jet coordinate changes.** If the coordinate maps `h` and `g` are `C^n` at `x₀`,
then the coordinate change of `r`-jets is `C^m` at `x₀` as a continuous linear map, provided
`m + r ≤ n`. -/
theorem ContDiffAt.linearJetCoordChange {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G} {x₀ : E'}
    {n m : ℕ∞ω} (hh : ContDiffAt 𝕜 n h x₀) (hg : ContDiffAt 𝕜 n g x₀) (hmn : m + r ≤ n) :
    ContDiffAt 𝕜 m (linearJetCoordChange r h g) x₀ := by
  refine ContDiffAt.continuousLinearMapPi fun i ↦ ?_
  have hi : m + i.val ≤ n := le_trans (add_le_add le_rfl (TauCeti.natCast_val_le i)) hmn
  exact (ContDiffAt.iteratedFDeriv
    (f := fun x z ↦ (g z).comp (finiteJetPolynomialCLM (𝕜 := 𝕜) (F := F) r (h x) (h z)))
    (g := id) (contDiffAt_jetTransform (p := (x₀, x₀)) hh hh hg) contDiffAt_id
      hi).continuousMultilinearMap_flipLinear

/-- **Smoothness of jet coordinate changes on open sets.** If the coordinate maps `h` and `g` are
`C^n` on an open set `u`, such as a chart overlap, then the coordinate change of `r`-jets is `C^m`
on `u` as a continuous linear map, provided `m + r ≤ n`. -/
theorem ContDiffOn.linearJetCoordChange {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G}
    {u : Set E'} {n m : ℕ∞ω} (hu : IsOpen u) (hh : ContDiffOn 𝕜 n h u) (hg : ContDiffOn 𝕜 n g u)
    (hmn : m + r ≤ n) :
    ContDiffOn 𝕜 m (linearJetCoordChange r h g) u := fun _ hx ↦
  ((hh.contDiffAt (hu.mem_nhds hx)).linearJetCoordChange (hg.contDiffAt (hu.mem_nhds hx))
    hmn).contDiffWithinAt
