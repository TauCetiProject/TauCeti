/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Analysis.Complex.ContinuousLog.Basic
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Piecewise

/-!
# Borsuk's separation criterion and Janiszewski's theorem

Two points `a`, `b` of the plane lie in the same connected component of the complement of a compact
set `K` **exactly when** the *Borsuk map* `z ↦ (z - a) / (z - b)` admits a continuous logarithm on
`K`. `TauCeti/Analysis/Complex/ContinuousLog/Basic.lean` introduces the predicate
`TauCeti.HasContinuousLogOn` and proves the implication that needs no duality — a logarithm exists
as soon as the two points are joined inside `Kᶜ` (`TauCeti.hasContinuousLogOn_sub_div_sub`) — and
records the converse as the missing input. This file proves the converse,
`TauCeti.mem_connectedComponentIn_of_hasContinuousLogOn`, and reads the resulting equivalence off
as **Janiszewski's theorem**: two bounded closed sets whose intersection is preconnected, neither of
which separates `a` from `b`, have a union that does not separate them either.

## The argument

Boundedness of `K` is essential: the real axis separates `i` from `-i`, yet the Borsuk map of that
pair is a homeomorphism of `ℝ` onto the circle minus a point and so has a logarithm. What
boundedness buys is that at most one component of `Kᶜ` is unbounded
(`TauCeti.connectedComponentIn_compl_eq_of_unbounded_component`), so of two points in *different*
components at least one — say `a`, after exchanging them and inverting the Borsuk map — has a
**bounded** component `V`.

Suppose then that the Borsuk map has a logarithm `h` on `K`. Extend `h` to a continuous
`H : ℂ → ℂ` by Tietze and put `G = exp ∘ H`: a *nowhere-vanishing* continuous function on the whole
plane agreeing with `(z - a) / (z - b)` on `K`. The component `V` is open, its frontier lies in `K`
(`TauCeti.frontier_connectedComponentIn_subset_compl`), and `b` misses `closure V = V ∪ frontier V`.
The globally continuous functions `z ↦ G z * (z - b)` and `z ↦ z - a` agree on
`frontier (closure V) ⊆ frontier V ⊆ K`, because there
`G z * (z - b) = ((z - a) / (z - b)) * (z - b) = z - a`. Therefore
`Continuous.piecewise` shows that their piecewise combination

> `Φ = (closure V).piecewise (fun z => G z * (z - b)) (fun z => z - a)`

is continuous, and it vanishes nowhere: on `closure V` because `G` is zero-free and
`b ∉ closure V`, off `closure V` because `a ∈ V`.

A zero-free continuous function on the plane has a continuous logarithm by
`Complex.exists_continuousOn_eqOn_exp_comp`, hence so does its restriction to any circle. But `V`
is bounded, so a large enough circle about `a` misses `closure V`, and there `Φ z = z - a`, which
has **no** continuous logarithm on a circle about `a`
(`TauCeti.not_hasContinuousLogOn_sub_sphere`) — the classical winding obstruction, proved here by
following `t ↦ h (a + r * exp (t * I)) - t * I - log r` once around and finding it both constant and
shifted by `2 * π * I`. That contradiction is the theorem.

Nothing in the argument looks at curves inside `K`, or asks `K` to be connected, locally connected,
or to contain an arc; `K` enters only through the frontier of one component of its complement.

## Roadmap role

**Plane separation for Jordan curves** was the open frontier item of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Carathéodory boundary correspondence.
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton` of
`TauCeti/Analysis/Complex/Conformal/Crosscut/Inside.lean` avoids the plane-separation hypothesis
entirely by taking `IsPreconnected (K \ {f z₀})` instead, which
`IsJordanCurve.isPathConnected_sdiff_singleton` discharges; `Caratheodory.lean` is now
unconditional. `TauCeti/Analysis/Complex/ContinuousLog/Basic.lean` names the remaining open
statement on the classical route through Janiszewski's theorem — the converse direction — and
this file supplies it, so `TauCeti.janiszewski` is available to that route as well.

Mathlib has no separation theory for the plane and no Jordan curve theorem, and layer L5 is absent
from [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort. The lifting of a zero-free continuous function
through `Complex.exp` is supplied by Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp`.

## Janiszewski's second theorem

The same logarithms give the companion statement: if `S` and `T` are closed and connected and their
intersection is bounded but **not** connected, then `S ∪ T` separates the plane. Split `S ∩ T` into
two disjoint closed pieces `P ∋ a` and `Q ∋ b`; the frontier `Z` of a thin neighbourhood of `P` is a
compact set missing `S ∩ T` that separates `a` from `b`, so by Borsuk's theorem the Borsuk map of
`a` and `b` has no continuous logarithm on `Z`. If the complement of `S ∪ T` were connected, one
would exist: cut `Z` into the closed part `Z_S` nearer to `T` than to `S`, which misses `S`, and the
closed part `Z_T` nearer to `S`, which misses `T`; their overlap misses `S ∪ T`, so it lies in a
compact connected set `L` off `S ∪ T`. Then `Z_S ∪ L` misses the connected set `S` through `a` and
`b`, so the map has a logarithm there, likewise on `Z_T ∪ L`, and the two logarithms glue along
their connected overlap `L`. The argument is the Mayer–Vietoris sequence for `Sᶜ` and `Tᶜ`, read in
degree zero through continuous logarithms.

## Filled hulls and simply connected sets

Taking for `b` a point far to the left of a bounded closed set `K`, Borsuk's theorem says that
`z ↦ z - a` has a continuous logarithm on `K` exactly when `a` lies outside the filled hull of `K`.
On a simply connected open set `U` every zero-free continuous function has a continuous logarithm,
by Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp`; for `a` in a bounded component of `Uᶜ`
that component is cut out by an open set whose frontier is a compact subset of `U` enclosing `a`,
which is impossible. So a simply connected open set has no holes.

## Main results

* `TauCeti.not_hasContinuousLogOn_sub_sphere` — `z ↦ z - a` has no continuous logarithm on a circle
  centred at `a`.
* `TauCeti.mem_connectedComponentIn_of_hasContinuousLogOn` — **Borsuk's separation theorem**: a
  continuous logarithm of the Borsuk map on a bounded closed set puts the two points in one
  component of the complement.
* `TauCeti.hasContinuousLogOn_sub_div_sub_iff` — the resulting equivalence.
* `TauCeti.janiszewski` — **Janiszewski's theorem**.
* `TauCeti.hasContinuousLogOn_sub_div_sub_of_isPreconnected_compl_union` — if two closed connected
  sets do not together separate the plane, the Borsuk map of two of their common points has a
  continuous logarithm on every compact set missing their intersection.
* `TauCeti.not_isPreconnected_compl_union_of_not_isPreconnected_inter` — **Janiszewski's second
  theorem**: two closed connected sets with bounded disconnected intersection separate the plane.
* `TauCeti.hasContinuousLogOn_sub_iff_notMem_filledHull` — a point lies outside the filled hull of a
  bounded closed set exactly when the map to it has a continuous logarithm there.
* `IsSimplyConnected.filledHull_subset` — a simply connected open subset of the plane has no holes.

## References

* K. Borsuk, *Über Schnitte der euklidischen Räume*, Math. Ann. **106** (1932), 239–248.
* S. Janiszewski, *Sur les coupures du plan faites par les continus*, Prace Mat.-Fiz. **26** (1913).
* R. B. Burckel, *An Introduction to Classical Complex Analysis I*, §4.
* J. R. Munkres, *Topology*, §61–63.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.11.
-/

public section

namespace TauCeti

open Bornology Complex Metric Set

open scoped Real

variable {K : Set ℂ} {a b : ℂ}

/-! ## The winding obstruction on a circle -/

/-- **A circle carries no continuous logarithm of the map to its centre.** This is the winding
obstruction used in the plane-separation argument. -/
theorem not_hasContinuousLogOn_sub_sphere {r : ℝ} (hr : 0 ≤ r) (a : ℂ) :
    ¬ HasContinuousLogOn (fun z => z - a) (sphere a r) := by
  rcases hr.eq_or_lt with rfl | hr
  · intro hlog
    exact (hlog.ne_zero (by simp : a ∈ sphere a 0)) (sub_self a)
  rw [hasContinuousLogOn_iff]
  rintro ⟨h, hcont, heq⟩
  set γ : ℝ → ℂ := circleMap a r with hγdef
  have hγsub : ∀ t, γ t - a = circleMap 0 r t := fun t => by
    rw [hγdef, circleMap_sub_center]
  have hγmem : ∀ t, γ t ∈ sphere a r := fun t => by
    simpa only [hγdef] using circleMap_mem_sphere a hr.le t
  have hγc : Continuous γ := by
    simpa only [hγdef] using continuous_circleMap a r
  set k : ℝ → ℂ := fun t => h (γ t) - t * Complex.I - Real.log r with hkdef
  have hkc : Continuous k := by
    have hhγ : Continuous fun t : ℝ => h (γ t) := hcont.comp_continuous hγc hγmem
    exact (hhγ.sub (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const
  have hexpr : Complex.exp ((Real.log r : ℝ) : ℂ) = (r : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hr]
  have hk1 : ∀ t, Complex.exp (k t) = 1 := fun t => by
    rw [hkdef]
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [Complex.exp_sub, Complex.exp_sub, heq _ (hγmem t), hγsub, circleMap_zero, hexpr]
    field_simp
  have hpre : IsPreconnected (range k) := isPreconnected_range hkc
  have hconst : k 0 = k (2 * π) :=
    eq_of_isPreconnected_of_forall_exp_eq_one hpre (by rintro w ⟨t, rfl⟩; exact hk1 t)
      (mem_range_self 0) (mem_range_self (2 * π))
  have hγ2 : γ (2 * π) = γ 0 := by
    simpa [hγdef] using periodic_circleMap a r 0
  rw [hkdef] at hconst
  simp only [hγ2, Complex.ofReal_zero, zero_mul, sub_zero] at hconst
  have hzero : ((2 * π : ℝ) : ℂ) * Complex.I = 0 := by linear_combination hconst
  rcases mul_eq_zero.mp hzero with hπ | hI
  · exact (by positivity : (0 : ℝ) < 2 * π).ne' (by exact_mod_cast hπ)
  · exact Complex.I_ne_zero hI

/-! ## Borsuk's separation theorem -/

/-- The heart of `TauCeti.mem_connectedComponentIn_of_hasContinuousLogOn`, in the case where the
component of the *first* point is bounded. The two points are then exchanged, and the Borsuk map
inverted, to cover the other case. -/
private theorem not_hasContinuousLogOn_of_isBounded_connectedComponentIn (hK : IsClosed K)
    (ha : a ∉ K) (hb : b ∉ K) (hab : b ∉ connectedComponentIn Kᶜ a)
    (hVb : IsBounded (connectedComponentIn Kᶜ a)) :
    ¬ HasContinuousLogOn (fun z => (z - a) / (z - b)) K := by
  classical
  rw [hasContinuousLogOn_iff]
  rintro ⟨h, hcont, heq⟩
  set V := connectedComponentIn Kᶜ a with hVdef
  have haV : a ∈ V := mem_connectedComponentIn ha
  have hfr : frontier V ⊆ K := by
    simpa [hVdef] using frontier_connectedComponentIn_subset_compl (X := ℂ) hK.isOpen_compl a
  have hclV : closure V ⊆ V ∪ K := by
    rw [closure_eq_self_union_frontier]
    exact union_subset_union_right _ hfr
  have hbcl : b ∉ closure V := fun hmem => (hclV hmem).elim hab hb
  -- extend the logarithm to the whole plane and exponentiate it
  obtain ⟨H, hH⟩ :=
    ContinuousMap.exists_restrict_eq (Y := ℂ) hK ⟨K.domRestrict h, hcont.domRestrict⟩
  have hHK : ∀ z ∈ K, H z = h z := fun z hz => by
    simpa using DFunLike.congr_fun hH ⟨z, hz⟩
  set G : ℂ → ℂ := fun z => Complex.exp (H z) with hGdef
  have hGK : ∀ z ∈ K, G z = (z - a) / (z - b) := fun z hz => by
    simp only [hGdef]
    rw [hHK z hz]
    exact heq z hz
  -- the two sides of `closure V` glue into a zero-free continuous function
  set Φ : ℂ → ℂ := (closure V).piecewise (fun z => G z * (z - b)) (fun z => z - a) with hΦdef
  have hglue : ∀ z ∈ frontier (closure V), G z * (z - b) = z - a := fun z hz => by
    have hzK : z ∈ K := hfr (frontier_closure_subset hz)
    have hzb : z - b ≠ 0 := sub_ne_zero.mpr fun hzeq => hb (hzeq ▸ hzK)
    rw [hGK z hzK, div_mul_cancel₀ _ hzb]
  have hΦc : Continuous Φ := by
    have h₁ : Continuous fun z : ℂ => G z * (z - b) := by
      have : Continuous G := Complex.continuous_exp.comp H.continuous
      fun_prop
    exact h₁.piecewise hglue (by fun_prop)
  have hΦ0 : ∀ z, Φ z ≠ 0 := by
    intro z
    by_cases hz : z ∈ closure V
    · rw [hΦdef, piecewise_eq_of_mem _ _ _ hz]
      exact mul_ne_zero (Complex.exp_ne_zero _)
        (sub_ne_zero.mpr fun hzeq => hbcl (hzeq ▸ hz))
    · rw [hΦdef, piecewise_eq_of_notMem _ _ _ hz]
      refine sub_ne_zero.mpr fun hzeq => hz ?_
      rw [hzeq]
      exact subset_closure haV
  -- a large circle about `a` misses `closure V`, and there `Φ` is the map to the centre
  obtain ⟨R, hR, hRsub⟩ := hVb.closure.subset_ball_lt 0 a
  have hsphere : EqOn Φ (fun z => z - a) (sphere a R) := by
    intro z hz
    have hzcl : z ∉ closure V := fun hmem => by
      have h₁ : dist z a < R := mem_ball.mp (hRsub hmem)
      have h₂ : dist z a = R := mem_sphere.mp hz
      exact absurd h₂ h₁.ne
    rw [hΦdef, piecewise_eq_of_notMem _ _ _ hzcl]
  have hΦlog : HasContinuousLogOn Φ univ := by
    have hUc : IsSimplyConnected (univ : Set ℂ) :=
      (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
    obtain ⟨h, hcont, heq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc isOpen_univ
      hΦc.continuousOn (by rintro ⟨z, -, hz⟩; exact hΦ0 z hz)
    exact hasContinuousLogOn_iff.mpr
      ⟨h, hcont, fun z hz => by simpa only [Function.comp_apply] using heq hz⟩
  exact not_hasContinuousLogOn_sub_sphere hR.le a
    ((hΦlog.mono (subset_univ _)).congr hsphere)

/-- **Borsuk's separation theorem.** If the Borsuk map `z ↦ (z - a) / (z - b)` of two points
outside a bounded closed set `K ⊆ ℂ` has a continuous logarithm on `K`, then `K` does not separate
them: `b` lies in the connected component of `a` in `Kᶜ`.

That the two points lie outside `K` is not assumed: the Borsuk map vanishes at `a` and, by the
division convention, at `b` as well, so a logarithm on `K` already excludes both from `K`.

This is the converse of `TauCeti.hasContinuousLogOn_sub_div_sub`, and the direction that fails
without boundedness — the real axis separates `i` from `-i` while carrying a logarithm of their
Borsuk map. -/
theorem mem_connectedComponentIn_of_hasContinuousLogOn (hK : IsClosed K) (hKb : IsBounded K)
    (hlog : HasContinuousLogOn (fun z => (z - a) / (z - b)) K) :
    b ∈ connectedComponentIn Kᶜ a := by
  have ha : a ∉ K := fun hmem => hlog.ne_zero hmem (by simp)
  have hb : b ∉ K := fun hmem => hlog.ne_zero hmem (by simp)
  by_contra hab
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  rcases mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn hrank hKb hab with
    hA | hB
  · exact not_hasContinuousLogOn_of_isBounded_connectedComponentIn hK ha hb hab
      (mem_filledHull_iff.mp hA) hlog
  · have hba : a ∉ connectedComponentIn Kᶜ b := fun hmem =>
      hab (connectedComponentIn_eq hmem ▸ mem_connectedComponentIn hb)
    refine not_hasContinuousLogOn_of_isBounded_connectedComponentIn hK hb ha hba
      (mem_filledHull_iff.mp hB) ?_
    exact hlog.inv.congr fun z _ => inv_div _ _

/-- **The Borsuk criterion.** For two points outside a bounded closed set `K ⊆ ℂ`, the Borsuk map
`z ↦ (z - a) / (z - b)` has a continuous logarithm on `K` exactly when `K` fails to separate the
two points; both sides already force `a` and `b` outside `K`. The easy direction is
`TauCeti.hasContinuousLogOn_sub_div_sub`, the hard one
`TauCeti.mem_connectedComponentIn_of_hasContinuousLogOn`. -/
theorem hasContinuousLogOn_sub_div_sub_iff (hK : IsClosed K) (hKb : IsBounded K) :
    HasContinuousLogOn (fun z => (z - a) / (z - b)) K ↔ b ∈ connectedComponentIn Kᶜ a :=
  ⟨mem_connectedComponentIn_of_hasContinuousLogOn hK hKb, hasContinuousLogOn_sub_div_sub hK⟩

/-! ## Janiszewski's theorem -/

/-- **Janiszewski's theorem.** If two bounded closed subsets `S`, `T` of the plane have preconnected
intersection and neither separates `a` from `b`, then their union does not separate them either. -/
theorem janiszewski {S T : Set ℂ} (hS : IsClosed S) (hT : IsClosed T) (hSb : IsBounded S)
    (hTb : IsBounded T) (hST : IsPreconnected (S ∩ T))
    (hSsep : b ∈ connectedComponentIn Sᶜ a) (hTsep : b ∈ connectedComponentIn Tᶜ a) :
    b ∈ connectedComponentIn (S ∪ T)ᶜ a :=
  mem_connectedComponentIn_of_hasContinuousLogOn (hS.union hT) (hSb.union hTb)
    ((hasContinuousLogOn_sub_div_sub hS hSsep).union hS hT hST
      (hasContinuousLogOn_sub_div_sub hT hTsep))

/-! ## Janiszewski's second theorem -/

/-- **If two closed connected sets do not separate the plane, logarithms of the Borsuk map of two
common points exist off their intersection.** Let `S`, `T` be closed and preconnected, both
containing `a` and `b`, with `(S ∪ T)ᶜ` preconnected. Then `z ↦ (z - a) / (z - b)` has a continuous
logarithm on every compact `Z` disjoint from `S ∩ T`. -/
theorem hasContinuousLogOn_sub_div_sub_of_isPreconnected_compl_union {S T Z : Set ℂ}
    (hS : IsClosed S) (hT : IsClosed T) (hSc : IsPreconnected S) (hTc : IsPreconnected T)
    (ha : a ∈ S ∩ T) (hb : b ∈ S ∩ T) (hD : IsPreconnected (S ∪ T)ᶜ) (hZ : IsCompact Z)
    (hZST : Disjoint Z (S ∩ T)) : HasContinuousLogOn (fun z => (z - a) / (z - b)) Z := by
  -- cut `Z` into the closed part `ZS` nearer to `T`, which misses `S`, and the part `ZT` nearer
  -- to `S`, which misses `T`
  set ZS := Z ∩ {z | infDist z T ≤ infDist z S}
  set ZT := Z ∩ {z | infDist z S ≤ infDist z T}
  have hZS : IsClosed ZS :=
    hZ.isClosed.inter (isClosed_le (continuous_infDist_pt T) (continuous_infDist_pt S))
  have hZT : IsClosed ZT :=
    hZ.isClosed.inter (isClosed_le (continuous_infDist_pt S) (continuous_infDist_pt T))
  have hmiss : ∀ {U V : Set ℂ}, IsClosed U → IsClosed V → a ∈ U → a ∈ V → Disjoint Z (U ∩ V) →
      Disjoint (Z ∩ {z | infDist z V ≤ infDist z U}) U := by
    intro U V hU hV haU haV hZUV
    refine disjoint_left.mpr fun z ⟨hzZ, hz⟩ hzU => disjoint_left.mp hZUV hzZ ⟨hzU, ?_⟩
    have h0 : infDist z U = 0 := (hU.mem_iff_infDist_zero ⟨a, haU⟩).mp hzU
    exact (hV.mem_iff_infDist_zero ⟨a, haV⟩).mpr (le_antisymm (h0 ▸ hz) infDist_nonneg)
  have hZSS : Disjoint ZS S := hmiss hS hT ha.1 ha.2 hZST
  have hZTT : Disjoint ZT T := hmiss hT hS ha.2 ha.1 (inter_comm S T ▸ hZST)
  -- their overlap misses `S ∪ T`, so it lies in a compact connected set `L` off `S ∪ T`
  have hE : ZS ∩ ZT ⊆ (S ∪ T)ᶜ := fun z hz hzST =>
    hzST.elim (disjoint_left.mp hZSS hz.1) (disjoint_left.mp hZTT hz.2)
  obtain ⟨L, hLc, hLp, hEL, hLD⟩ := exists_isCompact_isPreconnected_between
    (hZ.of_isClosed_subset (hZS.inter hZT) (inter_subset_left.trans inter_subset_left))
    (hS.union hT).isOpen_compl hD hE
  -- on `ZS ∪ L`, which misses the connected set `S` through `a` and `b`, the Borsuk map has a
  -- logarithm, and likewise on `ZT ∪ L`
  have hlog : ∀ {U Y : Set ℂ}, IsPreconnected U → a ∈ U → b ∈ U → U ⊆ S ∪ T → IsClosed Y →
      Disjoint Y U → HasContinuousLogOn (fun z => (z - a) / (z - b)) (Y ∪ L) :=
    fun {U Y} hUc haU hbU hUST hY hYU => hasContinuousLogOn_sub_div_sub (hY.union hLc.isClosed)
      (hUc.subset_connectedComponentIn (F := (Y ∪ L)ᶜ) haU (fun z hzU (hz : z ∈ Y ∪ L) => hz.elim
        (fun h => disjoint_left.mp hYU h hzU) fun h => hLD h (hUST hzU)) hbU)
  have hinter : (ZS ∪ L) ∩ (ZT ∪ L) = L := by
    rw [← inter_union_distrib_right]
    exact union_eq_right.mpr (hEL.trans interior_subset)
  refine ((hlog hSc ha.1 hb.1 subset_union_left hZS hZSS).union (hZS.union hLc.isClosed)
    (hZT.union hLc.isClosed) (hinter.symm ▸ hLp)
    (hlog hTc ha.2 hb.2 subset_union_right hZT hZTT)).mono fun z hz => ?_
  rcases le_total (infDist z T) (infDist z S) with h | h
  · exact Or.inl (Or.inl ⟨hz, h⟩)
  · exact Or.inr (Or.inl ⟨hz, h⟩)

/-- **Janiszewski's second theorem.** If two closed preconnected subsets `S`, `T` of the plane have
a bounded intersection that is not preconnected, then their union separates the plane: the
complement of `S ∪ T` is not preconnected. -/
theorem not_isPreconnected_compl_union_of_not_isPreconnected_inter {S T : Set ℂ}
    (hS : IsClosed S) (hT : IsClosed T) (hSc : IsPreconnected S) (hTc : IsPreconnected T)
    (hSTb : IsBounded (S ∩ T)) (hST : ¬ IsPreconnected (S ∩ T)) : ¬ IsPreconnected (S ∪ T)ᶜ := by
  intro hD
  -- split `S ∩ T` into disjoint closed pieces `P ∋ a`, compact, and `Q ∋ b`
  simp only [isPreconnected_iff_subset_of_disjoint_closed, not_forall, not_or] at hST
  obtain ⟨u, v, hu, hv, hsub, hdisj, hnu, hnv⟩ := hST
  obtain ⟨a, haST, hav⟩ := not_subset.mp hnv
  obtain ⟨b, hbST, hbu⟩ := not_subset.mp hnu
  set P := S ∩ T ∩ u
  set Q := S ∩ T ∩ v
  have hP : IsCompact P :=
    isCompact_of_isClosed_isBounded ((hS.inter hT).inter hu) (hSTb.subset inter_subset_left)
  have hPQ : Disjoint P Q := disjoint_left.mpr fun z hzP hzQ =>
    (hdisj ▸ ⟨hzP.1, hzP.2, hzQ.2⟩ : z ∈ (∅ : Set ℂ))
  obtain ⟨δ, hδ, hthick⟩ := hPQ.exists_thickenings hP ((hS.inter hT).inter hv)
  -- the frontier `Z` of the open neighbourhood `W` of `P` misses `S ∩ T`
  set W := thickening δ P
  have hW : IsOpen W := isOpen_thickening
  have hWQ : Disjoint (closure W) (thickening δ Q) := hthick.closure_left isOpen_thickening
  have haW : a ∈ W := self_subset_thickening hδ P ⟨haST, (hsub haST).resolve_right hav⟩
  have hbW : b ∉ closure W := fun hbW => disjoint_left.mp hWQ hbW
    (self_subset_thickening hδ Q ⟨hbST, (hsub hbST).resolve_left hbu⟩)
  set Z := frontier W
  have hZW : Z = closure W \ W := hW.frontier_eq
  have hZ : IsCompact Z := isCompact_of_isClosed_isBounded isClosed_frontier
    (hP.isBounded.thickening.closure.subset frontier_subset_closure)
  have hZST : Disjoint Z (S ∩ T) := by
    refine disjoint_left.mpr fun z hzZ hz => ?_
    rw [hZW] at hzZ
    rcases hsub hz with hzu | hzv
    · exact hzZ.2 (self_subset_thickening hδ P ⟨hz, hzu⟩)
    · exact disjoint_left.mp hWQ hzZ.1 (self_subset_thickening hδ Q ⟨hz, hzv⟩)
  -- `Z` separates `a ∈ W` from `b ∉ closure W`, so it carries no logarithm of their Borsuk map
  have haZ : a ∉ Z := fun haZ => (hZW ▸ haZ).2 haW
  refine hbW (subset_closure (isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hW
    ⟨a, mem_connectedComponentIn haZ, haW⟩ (fun z ⟨hzW, hz⟩ => ?_)
    (mem_connectedComponentIn_of_hasContinuousLogOn hZ.isClosed hZ.isBounded
      (hasContinuousLogOn_sub_div_sub_of_isPreconnected_compl_union hS hT hSc hTc haST hbST hD hZ
        hZST))))
  by_contra hzW'
  exact connectedComponentIn_subset _ _ hz (hZW ▸ ⟨hzW, hzW'⟩)


/-! ## Filled hulls through logarithms -/

/-- Some point `b` outside the filled hull of a bounded set `K ⊆ ℂ` makes `z ↦ z - b` have a
continuous logarithm on `K`: far to the left of `K`, the values `z - b` lie in the right
half-plane. -/
private theorem exists_notMem_filledHull_hasContinuousLogOn_sub (hKb : IsBounded K) :
    ∃ b ∉ filledHull K, HasContinuousLogOn (fun z => z - b) K := by
  obtain ⟨R, hR⟩ := (isBounded_filledHull.mpr hKb).subset_closedBall 0
  refine ⟨-((|R| + 1 : ℝ) : ℂ), fun hb => ?_,
    hasContinuousLogOn_of_mapsTo_slitPlane (by fun_prop) fun z hz => ?_⟩
  · have hnorm := mem_closedBall_zero_iff.mp (hR hb)
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hnorm
    linarith [le_abs_self R]
  · have hz' := mem_closedBall_zero_iff.mp (hR (subset_filledHull hz))
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [sub_re, neg_re, ofReal_re]
    linarith [neg_abs_le z.re, abs_re_le_norm z, le_abs_self R]

/-- **A point lies outside the filled hull of a bounded closed set exactly when the map to it has a
continuous logarithm there.** For `K ⊆ ℂ` bounded and closed, `z ↦ z - a` has a continuous
logarithm on `K` if and only if `a` lies in the unbounded component of `Kᶜ`. -/
theorem hasContinuousLogOn_sub_iff_notMem_filledHull (hK : IsClosed K) (hKb : IsBounded K) :
    HasContinuousLogOn (fun z => z - a) K ↔ a ∉ filledHull K := by
  obtain ⟨b, hb, hlogb⟩ := exists_notMem_filledHull_hasContinuousLogOn_sub hKb
  have hbK : b ∉ K := fun h => hb (subset_filledHull h)
  refine ⟨fun hlog ha => hb ?_, fun ha => ?_⟩
  · -- `K` does not separate `a` from `b`, so they share a component, bounded since `a` is enclosed
    have hab := mem_connectedComponentIn_of_hasContinuousLogOn hK hKb (hlog.div hlogb)
    rw [mem_filledHull_iff, ← connectedComponentIn_eq hab]
    exact mem_filledHull_iff.mp ha
  · -- `a` and `b` lie in the unbounded component of `Kᶜ`, so their Borsuk map has a logarithm
    have hlogab : HasContinuousLogOn (fun z => (z - a) / (z - b)) K := by_contra fun h =>
      (mem_filledHull_or_mem_filledHull_of_not_hasContinuousLogOn hK hKb h).elim ha hb
    refine (hlogab.mul hlogb).congr fun z hz => ?_
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr fun h => hbK (h ▸ hz))

/-- **A simply connected open subset of the plane has no holes**: it contains its filled hull, that
is, every connected component of its complement is unbounded. Consequently `filledHull K ⊆ U`
for every `K ⊆ U`, by `TauCeti.filledHull_mono`. -/
theorem _root_.IsSimplyConnected.filledHull_subset {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) : filledHull U ⊆ U := by
  intro a ha
  by_contra haU
  -- `z ↦ z - a` has a continuous logarithm on the simply connected set `U`
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hUo
    (g := fun z => z - a) (by fun_prop) (by rintro ⟨z, hz, h0⟩; exact haU (sub_eq_zero.mp h0 ▸ hz))
  -- the bounded component of `Uᶜ` through `a` is cut out by an open set `V` with frontier in `U`
  obtain ⟨V, -, haV, hVc, hVU⟩ :=
    hUo.isClosed_compl.exists_isOpen_isCompact_closure_disjoint_frontier
      (isCompact_of_isClosed_isBounded hUo.isClosed_compl.connectedComponentIn
        (mem_filledHull_iff.mp ha))
  have hKU : frontier V ⊆ U := fun z hz => by
    by_contra hzU
    exact disjoint_left.mp hVU hz hzU
  -- so `frontier V` encloses `a` while carrying a logarithm of `z ↦ z - a`
  refine (hasContinuousLogOn_sub_iff_notMem_filledHull isClosed_frontier
    (hVc.isBounded.subset frontier_subset_closure)).mp
      (hasContinuousLogOn_iff.mpr ⟨L, hLc.mono hKU, fun z hz => hL (hKU hz)⟩) ?_
  exact subset_filledHull_of_frontier_subset (hVc.isBounded.subset subset_closure) subset_rfl
    (haV (mem_connectedComponentIn haU))

end TauCeti
