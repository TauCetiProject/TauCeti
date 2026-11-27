/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Disc
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Symplectic.Manifold.PositiveCohomologyAssignment
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Homotopy.Contractible
import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
import TauCeti.Analysis.Complex.UnitDisc.Basic
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.CauchyRiemann.NearlyHolomorphic
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Analysis.Complex.Conformal.LocalIndex

/-!
# The zero charges of discs and the zero set of a pseudoholomorphic function

Let `f : Y → ℂ` be a continuous function on a space `Y`. A continuous disc `σ : 𝔻 → Y` meets the
zero set `Z = f⁻¹(0)` in `σ⁻¹(Z)`, the zero set of `f ∘ σ`. Its **zero charge**
`ContinuousMap.zeroCharge f σ` is the local degree of `f ∘ σ : 𝔻 → ℂ` at `0`
(`TauCeti.HomologicalOrientation.localDegree`): the number of zeros of `f ∘ σ`, counted with their
topological multiplicities. It is defined with the canonical orientation of `ℂ` on the target and
its restriction to `𝔻` on the source, and does not depend on that choice
(`ContinuousMap.zeroCharge_eq_localDegree`). On open subsets of `ℂ`, local degrees at `0` are
winding numbers along circles enclosing the zeros
(`TauCeti.HomologicalOrientation.localDegree_comap_eq_degree_toBasedLoop`). So the zero charge is
the winding number of `f ∘ σ` along any circle in `𝔻` enclosing its zeros
(`ContinuousMap.zeroCharge_eq_degree_toBasedLoop`), and when `f` is the framing section of a
trivialized line it is the framed charge of `σ`. It only depends on `σ` near the zeros of `f ∘ σ`
(`ContinuousMap.zeroCharge_congr`), and it does not change when `f` is multiplied by a function
vanishing nowhere along `σ` (`ContinuousMap.zeroCharge_mul_left`), since on the contractible disc
such a function is homotopic to `1` through nonvanishing functions. So the framed charge does not
depend on the trivialization of the line.

When `σ⁻¹(Z)` is compact, the zero charge obeys the laws of a positive cohomology assignment
(`TauCeti.PositiveCohomologyAssignment`) other than positivity, for every continuous `f`:

* **vacuum**: it vanishes when `σ` misses `Z`
  (`ContinuousMap.zeroCharge_eq_zero_of_forall_ne_zero`);
* **homotopy**: it is constant along a homotopy whose total preimage of `Z` is compact
  (`ContinuousMap.zeroCharge_eq_of_homotopy`);
* **degree**: it multiplies by the degree of a proper reparametrization `θ : 𝔻 → 𝔻`
  (`ContinuousMap.zeroCharge_comp`);
* **additivity**: it is the sum of the zero charges of finitely many disjoint round subdiscs
  containing `σ⁻¹(Z)` (`ContinuousMap.zeroCharge_eq_sum`).

These are the local degree's naturality under proper maps, invariance under homotopies with
compact fibre, and additivity over disjoint open sets. For additivity, the subdisc maps
`z ↦ c + r z` with `r > 0` preserve the canonical orientation of `ℂ`, being holomorphic
(`TauCeti.comap_coe_comp_subdisc_complexHomologicalOrientation`).

If `f ∘ σ` extends to a function `φ` holomorphic on the unit disc, a compact `σ⁻¹(Z)` is finite
(`TauCeti.finite_preimage_preimage_zero`). The zero charge is then the sum of the orders of
vanishing of `φ` at the points of `σ⁻¹(Z)`
(`ContinuousMap.zeroCharge_eq_sum_analyticOrderNatAt`), which are the local intersection
multiplicities of the disc with `Z`, and it is positive as soon as `σ` meets `Z`
(`ContinuousMap.zeroCharge_pos`).

The same positivity holds when `f ∘ σ` only extends to a `C¹` function `b` satisfying a
Cauchy–Riemann inequality `‖∂ₛb + i ∂ₜb‖ ≤ M ‖b‖` with `M` locally bounded
(`ContinuousMap.zeroCharge_pos_of_norm_le`). By the similarity principle
(`TauCeti.exists_eventually_eq_mul_of_norm_le`) such a `b` is, near each of its zeros, a
continuous nonvanishing function times a holomorphic one, so its zeros are isolated unless it
vanishes identically, and each has positive local index. This is the case of the normal
coordinate of a pseudoholomorphic disc in coordinates adapted to another, immersed,
pseudoholomorphic disc, for an almost complex structure that need not be integrable
(`TauCeti.zeroCharge_pos_of_cauchyRiemann`).

Now let `Y` carry an almost complex structure `J` and let `f` be `J`-holomorphic. If `σ` is the
restriction of a map `u` that is `J`-holomorphic on the unit disc, then `f ∘ u` is holomorphic
(`TauCeti.IsPseudoholomorphicOn.differentiableOn_comp`). Hence the zero charges form a positive
cohomology assignment to the zero set of `f` (`TauCeti.PositiveCohomologyAssignment.zeroSet`),
whose integer of a holomorphic disc is the sum of the orders of vanishing of `f` along it. No
hypothesis that `σ` is nonconstant is needed.

## Main definitions

* `ContinuousMap.zeroCharge f σ`: the local degree of `f ∘ σ` at `0`.
* `TauCeti.PositiveCohomologyAssignment.zeroSet`: the positive cohomology assignment to the zero
  set of a `J`-holomorphic function.

## Main results

* `ContinuousMap.zeroCharge_comp`, `ContinuousMap.zeroCharge_eq_of_homotopy`,
  `ContinuousMap.zeroCharge_eq_sum`: the degree, homotopy and additivity laws.
* `ContinuousMap.zeroCharge_congr`: discs agreeing near the zeros of both have the same zero
  charge.
* `ContinuousMap.zeroCharge_mul_left`: gauge invariance under nonvanishing multipliers.
* `ContinuousMap.zeroCharge_eq_degree_toBasedLoop`: the zero charge is the winding number along a
  circle enclosing the zeros.
* `TauCeti.finite_preimage_preimage_zero`: if `f ∘ σ` extends holomorphically, a compact
  `σ⁻¹(Z)` is finite.
* `ContinuousMap.zeroCharge_eq_sum_analyticOrderNatAt`: if `f ∘ σ` extends holomorphically, the
  zero charge is the sum of the orders of vanishing.
* `ContinuousMap.zeroCharge_pos`: it is positive on such discs meeting `Z`.
* `ContinuousMap.zeroCharge_pos_of_norm_le`: it is positive on discs meeting `Z` along which
  `f` satisfies a Cauchy–Riemann inequality.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section 2.3 (the similarity principle).
-/

public section

noncomputable section

open Filter Metric Set Topology TauCeti
open TauCeti.Complex.UnitDisc
open scoped Complex.UnitDisc Manifold ContDiff

section ZeroCharge

variable {Y : Type*} [TopologicalSpace Y]

/-! ### The zero charge of a disc -/

namespace ContinuousMap

/-- The **zero charge** of a disc `σ : 𝔻 → Y` for a continuous function `f : Y → ℂ`: the local
degree at `0` of `f ∘ σ`, for the canonical orientation of `ℂ` on the target and its restriction to
`𝔻` on the source. It counts the zeros of `f ∘ σ` with their topological multiplicities, and is `0`
when the zero set of `f ∘ σ` is not compact. -/
def zeroCharge (f : C(Y, ℂ)) (σ : C(𝔻, Y)) : ℤ :=
  ((complexHomologicalOrientation ℂ).comap Complex.UnitDisc.isOpenEmbedding_coe).localDegree
    (complexHomologicalOrientation ℂ) Complex.finrank_real_complex (f.comp σ) 0

/-- **The zero charge does not depend on the orientation.** It is the local degree of `f ∘ σ` at
`0` for every orientation `o` of `ℂ`, used on the target and restricted to `𝔻` on the source:
reversing `o` reverses both. -/
theorem zeroCharge_eq_localDegree (o : HomologicalOrientation ℂ ℂ 2) (f : C(Y, ℂ))
    (σ : C(𝔻, Y)) :
    zeroCharge f σ = (o.comap Complex.UnitDisc.isOpenEmbedding_coe).localDegree o
      Complex.finrank_real_complex (f.comp σ) 0 :=
  (HomologicalOrientation.localDegree_comap_self_eq _ Complex.finrank_real_complex o _ _ _).symm

/-- The zero charge vanishes when the zero set of `f ∘ σ` is not compact. -/
@[simp]
theorem zeroCharge_of_not_isCompact {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    (h : ¬IsCompact (σ ⁻¹' (f ⁻¹' {0}))) : zeroCharge f σ = 0 :=
  HomologicalOrientation.localDegree_of_not_isCompact _ _ _ _ h

/-- **Vacuum.** The zero charge of a disc missing the zero set of `f` vanishes. -/
theorem zeroCharge_eq_zero_of_forall_ne_zero {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    (h : ∀ z, f (σ z) ≠ 0) : zeroCharge f σ = 0 :=
  HomologicalOrientation.localDegree_eq_zero_of_notMem_range _ _ _ Complex.finrank_real_complex _
    fun ⟨z, hz⟩ ↦ h z hz

/-- **Homotopy invariance.** The zero charge is constant along a homotopy of discs whose total
preimage of the zero set of `f` in `[0, 1] × 𝔻` is compact. -/
theorem zeroCharge_eq_of_homotopy (f : C(Y, ℂ)) {σ₀ σ₁ : C(𝔻, Y)} (F : σ₀.Homotopy σ₁)
    (hF : IsCompact ((F : unitInterval × 𝔻 → Y) ⁻¹' (f ⁻¹' {0}))) :
    zeroCharge f σ₀ = zeroCharge f σ₁ :=
  HomologicalOrientation.localDegree_eq_of_homotopy_of_isCompact _ _ _ Complex.finrank_real_complex
    ((ContinuousMap.Homotopy.refl f).comp F) hF

/-- **The degree law.** For a proper reparametrization `θ : 𝔻 → 𝔻` of a disc `σ` with compact
preimage of the zero set of `f`, the zero charge of `σ ∘ θ` is `deg θ` times that of `σ`, the
degree being taken for any orientation `o` of `𝔻` on both sides. -/
theorem zeroCharge_comp (o : HomologicalOrientation 𝔻 ℂ 2) {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) {θ : C(𝔻, 𝔻)} (hθ : IsProperMap θ) :
    zeroCharge f (σ.comp θ) = o.degree o Complex.finrank_real_complex θ * zeroCharge f σ := by
  set O := (complexHomologicalOrientation ℂ).comap Complex.UnitDisc.isOpenEmbedding_coe
  rw [O.degree_self_eq Complex.finrank_real_complex o, zeroCharge, zeroCharge,
    ← ContinuousMap.comp_assoc]
  exact O.localDegree_comp O _ Complex.finrank_real_complex Complex.finrank_real_complex
    Complex.finrank_real_complex h hθ

/-- **Additivity.** If finitely many disjoint round discs `B(cᵢ, rᵢ) ⊆ 𝔻` contain the compact
preimage `σ⁻¹(f⁻¹(0))`, the zero charge of `σ` is the sum of the zero charges of its restrictions
`σ ∘ sᵢ` to them, where `sᵢ = TauCeti.Complex.UnitDisc.subdisc cᵢ rᵢ`. The family may be empty. -/
theorem zeroCharge_eq_sum {ι : Type} [Fintype ι] {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) (c : ι → ℂ) (r : ι → ℝ) (hc : ∀ i, ‖c i‖ + r i ≤ 1)
    (hr : ∀ i, 0 < r i) (hdisj : Pairwise fun i j ↦ Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (hcov : ∀ z, f (σ z) = 0 → ∃ i, (z : ℂ) ∈ ball (c i) (r i)) :
    zeroCharge f σ = ∑ i, zeroCharge f (σ.comp (subdisc (c i) (r i) (hc i) (hr i))) := by
  set o := complexHomologicalOrientation ℂ
  set O := o.comap Complex.UnitDisc.isOpenEmbedding_coe
  -- The subdiscs, as open subsets of `𝔻`.
  let U (i : ι) : TopologicalSpace.Opens 𝔻 :=
    ⟨((↑) : 𝔻 → ℂ) ⁻¹' ball (c i) (r i), isOpen_ball.preimage Complex.UnitDisc.continuous_coe⟩
  have hU : Pairwise fun i j ↦ Disjoint (U i : Set 𝔻) (U j) := fun i j hij ↦
    (hdisj hij).preimage _
  rw [zeroCharge, O.localDegree_eq_sum o _ Complex.finrank_real_complex (f.comp σ) h (U := U)
    (fun i j hij ↦ (hU hij).mono inter_subset_right inter_subset_right)
    fun z hz ↦ mem_iUnion.2 (hcov z hz)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- The subdisc map, read as a map onto the open subset `U i`.
  set s := subdisc (c i) (r i) (hc i) (hr i)
  let e : C(𝔻, U i) := ⟨fun z ↦ ⟨s z, mem_range_subdisc.1 ⟨z, rfl⟩⟩,
    (s.continuous.subtype_mk _)⟩
  -- `Subtype.val ∘ e` is `s` by the construction of `e`.
  have he : IsOpenEmbedding e := (IsOpenEmbedding.of_comp_iff _
    (Complex.UnitDisc.isOpenEmbedding_coe.comp (U i).isOpenEmbedding')).1
    isOpenEmbedding_coe_comp_subdisc
  have hsurj : Function.Surjective e := fun w ↦ by
    obtain ⟨z, hz⟩ := (mem_range_subdisc (hc := hc i) (hr := hr i)).2 w.property
    exact ⟨z, Subtype.ext hz⟩
  have hO : (O.comap (U i).isOpenEmbedding').comap he = O := by
    rw [HomologicalOrientation.comap_comap, HomologicalOrientation.comap_comap]
    exact comap_coe_comp_subdisc_complexHomologicalOrientation
  rw [← O.comap (U i).isOpenEmbedding' |>.localDegree_comap o _ Complex.finrank_real_complex he _
    fun z _ ↦ hsurj z, hO, zeroCharge]
  -- `Subtype.val ∘ e` is `s` by the construction of `e`.
  congr 1

/-- **The zero charge only depends on the disc near its zeros.** If two discs `σ` and `σ'` agree
on an open set `W ⊆ 𝔻` containing the zeros of both `f ∘ σ` and `f ∘ σ'`, they have the same
zero charge. -/
theorem zeroCharge_congr {f : C(Y, ℂ)} {σ σ' : C(𝔻, Y)} {W : Set 𝔻} (hW : IsOpen W)
    (hσσ' : ∀ z ∈ W, σ z = σ' z) (hσ : ∀ z, f (σ z) = 0 → z ∈ W)
    (hσ' : ∀ z, f (σ' z) = 0 → z ∈ W) :
    zeroCharge f σ = zeroCharge f σ' := by
  refine HomologicalOrientation.localDegree_congr _ _ _ Complex.finrank_real_complex
    (eventually_nhdsSet_iff_exists.2 ⟨W, hW, fun z hz ↦ hσ z hz, fun z hz ↦ ?_⟩) fun z hz ↦ ?_
  · simp [hσσ' z hz]
  · simp only [Set.mem_preimage, ContinuousMap.comp_apply, Set.mem_singleton_iff] at hz ⊢
    rwa [hσσ' z (hσ' z hz)]

/-- The zero charge of `σ` for `f` is the zero charge of the disc `f ∘ σ` in `ℂ` for the
identity of `ℂ`. -/
@[simp]
theorem id_zeroCharge_comp (f : C(Y, ℂ)) (σ : C(𝔻, Y)) :
    (ContinuousMap.id ℂ).zeroCharge (f.comp σ) = f.zeroCharge σ := by
  rw [zeroCharge, zeroCharge, ContinuousMap.id_comp]

/-- **Gauge invariance.** Multiplying `f` by a function `u` that vanishes nowhere along `σ` does
not change the zero charge of `σ`. In particular the framed charge of a disc does not depend on the
trivialization of the line in which the framing section is read. -/
theorem zeroCharge_mul_left {u : C(Y, ℂ)} (f : C(Y, ℂ)) {σ : C(𝔻, Y)} (hu : ∀ z, u (σ z) ≠ 0) :
    zeroCharge (u * f) σ = zeroCharge f σ := by
  -- On the contractible disc, `u ∘ σ` is homotopic to the constant `1` through nonvanishing
  -- functions, and multiplying `f ∘ σ` by such a homotopy does not move its zeros.
  have hfib : σ ⁻¹' ((u * f) ⁻¹' {0}) = σ ⁻¹' (f ⁻¹' {0}) := by
    ext z
    simp [hu z]
  by_cases hc : IsCompact (σ ⁻¹' (f ⁻¹' {0}))
  swap
  · rw [zeroCharge_of_not_isCompact hc, zeroCharge_of_not_isCompact (hfib ▸ hc)]
  -- The unit `u ∘ σ` is null-homotopic, since `𝔻` is contractible and `ℂˣ` is path connected.
  let v : C(𝔻, ℂˣ) := ⟨fun z ↦ Units.mk0 (u (σ z)) (hu z),
    Units.isEmbedding_val₀.continuous_iff.2 <| by
      simpa [Function.comp_def] using (u.comp σ).continuous⟩
  obtain ⟨w, hw⟩ := (id_nullhomotopic 𝔻).comp_right v
  obtain ⟨G⟩ := hw.trans (ContinuousMap.homotopic_const_iff.2 (PathConnectedSpace.joined w 1))
  -- Multiplying `f ∘ σ` by `G` moves `(u * f) ∘ σ` to `f ∘ σ` and keeps the zeros in place.
  let H : ((u * f).comp σ).Homotopy (f.comp σ) :=
    { toFun := fun p ↦ (G p : ℂ) * f (σ p.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun z ↦ by simp [v]
      map_one_left := fun z ↦ by simp }
  have hHp (p : unitInterval × 𝔻) : H p = (G p : ℂ) * f (σ p.2) := rfl
  have hH : (H : unitInterval × 𝔻 → ℂ) ⁻¹' {0} = univ ×ˢ (σ ⁻¹' (f ⁻¹' {0})) := by
    ext p
    simp [hHp]
  exact HomologicalOrientation.localDegree_eq_of_homotopy_of_isCompact _ _ _
    Complex.finrank_real_complex H (hH ▸ isCompact_univ.prod hc)

/-- **Gauge invariance for discs in `ℂ`.** Multiplying a disc `c : 𝔻 → ℂ` by a function `u` that
vanishes nowhere does not change its zero charge for the identity of `ℂ`. -/
theorem id_zeroCharge_mul_left {u : C(𝔻, ℂ)} (c : C(𝔻, ℂ)) (hu : ∀ z, u z ≠ 0) :
    (ContinuousMap.id ℂ).zeroCharge (u * c) = (ContinuousMap.id ℂ).zeroCharge c := by
  have h := zeroCharge_mul_left c (σ := ContinuousMap.id 𝔻) hu
  rwa [← id_zeroCharge_comp (u * c) (ContinuousMap.id 𝔻), ← id_zeroCharge_comp c,
    ContinuousMap.comp_id, ContinuousMap.comp_id] at h

/-- **The zero charge is a winding number.** If every zero of `f ∘ σ` lies in the open disc of
radius `r > 0` about `z₀`, whose closure lies in `𝔻`, then the zero charge of `σ` is the degree
of the boundary direction map `ζ ↦ f(σ(z₀ + r ζ)) / ‖f(σ(z₀ + r ζ))‖`: the number of times `f`
winds around `0` along the image of the circle. -/
theorem zeroCharge_eq_degree_toBasedLoop {f : C(Y, ℂ)} {σ : C(𝔻, Y)} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hz₀ : closedBall z₀ r ⊆ ball 0 1)
    (hzero : ∀ z : 𝔻, f (σ z) = 0 → (z : ℂ) ∈ ball z₀ r) {u : C(Circle, Circle)}
    (hu : ∀ (ζ : Circle) (hζ : ‖z₀ + r * ζ‖ < 1),
      (u ζ : ℂ) = f (σ (Complex.UnitDisc.mk _ hζ)) / ‖f (σ (Complex.UnitDisc.mk _ hζ))‖) :
    zeroCharge f σ = Circle.degree u.toBasedLoop := by
  set o := complexHomologicalOrientation ℂ
  -- The unit disc, as an open subset of `ℂ`, and the identification of `𝔻` with it.
  let U : TopologicalSpace.Opens ℂ := ⟨ball 0 1, isOpen_ball⟩
  let e : C(𝔻, U) := ⟨fun z ↦ ⟨z, mem_ball_zero_iff.2 z.norm_lt_one⟩,
    Complex.UnitDisc.continuous_coe.subtype_mk _⟩
  let e' : C(U, 𝔻) := ⟨fun w ↦ Complex.UnitDisc.mk w (mem_ball_zero_iff.1 w.property),
    Complex.UnitDisc.isEmbedding_coe.continuous_iff.2 continuous_subtypeVal⟩
  have he : IsOpenEmbedding e := (IsOpenEmbedding.of_comp_iff _ U.isOpenEmbedding').1
    Complex.UnitDisc.isOpenEmbedding_coe
  have hcomp : f.comp σ = ((f.comp σ).comp e').comp e := ContinuousMap.ext fun z ↦ by
    simp [e, e', Complex.UnitDisc.mk_coe]
  rw [zeroCharge, hcomp, ← o.comap_comap_of_comp_eq U.isOpenEmbedding' he
      Complex.UnitDisc.isOpenEmbedding_coe rfl,
    (o.comap U.isOpenEmbedding').localDegree_comap o _ Complex.finrank_real_complex he _
      fun w _ ↦ ⟨e' w, rfl⟩]
  refine o.localDegree_comap_eq_degree_toBasedLoop hr hz₀ (fun w hw ↦ ?_) fun ζ hζ ↦ ?_
  · exact hzero (e' w) hw
  · exact hu ζ (mem_ball_zero_iff.1 hζ)

end ContinuousMap

/-! ### Discs along which `f` is holomorphic -/

namespace TauCeti

/-- If `σ⁻¹(f⁻¹(0))` is compact, an extension `φ` of `f ∘ σ` to `ℂ` does not vanish identically on
the unit disc: otherwise the whole disc, which is not compact, would be that preimage. -/
private theorem exists_mem_ball_ne_zero {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) {φ : ℂ → ℂ} (hφ : ∀ z : 𝔻, φ z = f (σ z)) :
    ∃ w ∈ ball (0 : ℂ) 1, φ w ≠ 0 := by
  by_contra! hzero
  have huniv : σ ⁻¹' (f ⁻¹' {0}) = univ := eq_univ_of_forall fun z ↦ by
    simpa [hφ z] using hzero z (mem_ball_zero_iff.2 z.norm_lt_one)
  exact noncompact_univ 𝔻 (huniv ▸ h)

/-- **Finiteness.** If `f ∘ σ` extends to a function `φ` holomorphic on the unit disc, a compact
preimage `σ⁻¹(f⁻¹(0))` is finite: the zeros of `φ` are isolated. -/
theorem finite_preimage_preimage_zero {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
    (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) {φ : ℂ → ℂ} (hφ : ∀ z : 𝔻, φ z = f (σ z))
    (hφd : DifferentiableOn ℂ φ (ball 0 1)) :
    (σ ⁻¹' (f ⁻¹' {0})).Finite := by
  obtain ⟨w, hw, hφw⟩ := exists_mem_ball_ne_zero h hφ
  have hfin := (hφd.analyticOnNhd isOpen_ball).finite_setOf_mem_and_eq_zero_of_isCompact
    (convex_ball _ _).isPreconnected hw hφw (h.image Complex.UnitDisc.continuous_coe)
    (image_subset_iff.2 fun z _ ↦ mem_ball_zero_iff.2 z.norm_lt_one)
  refine (hfin.preimage Complex.UnitDisc.coe_injective.injOn).subset fun z hz ↦
    ⟨mem_image_of_mem _ hz, ?_⟩
  simpa [hφ z] using hz

/-- The local index of `f ∘ σ` at a zero `z` is the order of vanishing at `z` of a holomorphic
extension `φ` of `f ∘ σ`. -/
private theorem localIndex_eq_analyticOrderNatAt {f : C(Y, ℂ)} {σ : C(𝔻, Y)} {φ : ℂ → ℂ}
    (hφ : ∀ z : 𝔻, φ z = f (σ z)) (hφd : DifferentiableOn ℂ φ (ball 0 1)) {z : 𝔻}
    (hz : f (σ z) = 0) :
    ((complexHomologicalOrientation ℂ).comap Complex.UnitDisc.isOpenEmbedding_coe).localIndex
      (complexHomologicalOrientation ℂ) (f.comp σ) z = analyticOrderNatAt φ z := by
  have key := HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub
    (complexHomologicalOrientation ℂ) Complex.UnitDisc.isOpenEmbedding_coe IsOpenEmbedding.id
    (f := f.comp σ) (φ := φ) (x := z) (Eventually.of_forall fun w ↦ hφ w)
    (hφd.analyticAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 z.norm_lt_one)))
  rw [HomologicalOrientation.comap_id] at key
  rw [key, hφ z, hz]
  simp only [sub_zero]

end TauCeti

namespace ContinuousMap

/-- **The zero charge counts orders of vanishing.** If `f ∘ σ` extends to a function `φ`
holomorphic on the unit disc, and `σ⁻¹(f⁻¹(0))` is the finite set `s`, then the zero charge of `σ`
is the sum over `s` of the orders of vanishing of `φ`: the local intersection multiplicities of the
disc with `f⁻¹(0)`. -/
theorem zeroCharge_eq_sum_analyticOrderNatAt {f : C(Y, ℂ)} {σ : C(𝔻, Y)} {φ : ℂ → ℂ}
    (hφ : ∀ z : 𝔻, φ z = f (σ z)) (hφd : DifferentiableOn ℂ φ (ball 0 1)) (s : Finset 𝔻)
    (hs : ∀ z, f (σ z) = 0 ↔ z ∈ s) :
    zeroCharge f σ = ∑ z ∈ s, (analyticOrderNatAt φ z : ℤ) := by
  have hfib : (f.comp σ) ⁻¹' {0} = s := by
    ext z
    simp [hs z]
  have hfin : ((f.comp σ) ⁻¹' {0}).Finite := hfib ▸ s.finite_toSet
  have hs' : hfin.toFinset = s := by
    ext z
    simp [hs z]
  rw [zeroCharge, HomologicalOrientation.localDegree_eq_sum_localIndex _ _ _
    Complex.finrank_real_complex _ hfin, hs']
  exact Finset.sum_congr rfl fun z hz ↦
    TauCeti.localIndex_eq_analyticOrderNatAt hφ hφd ((hs z).2 hz)

/-- **Positivity.** If `f ∘ σ` extends to a function `φ` holomorphic on the unit disc, with
`σ⁻¹(f⁻¹(0))` compact and nonempty, the zero charge of `σ` is positive: by the identity theorem, `φ`
vanishes to finite, positive order at each zero. -/
theorem zeroCharge_pos {f : C(Y, ℂ)} {σ : C(𝔻, Y)} (h : IsCompact (σ ⁻¹' (f ⁻¹' {0})))
    {φ : ℂ → ℂ} (hφ : ∀ z : 𝔻, φ z = f (σ z)) (hφd : DifferentiableOn ℂ φ (ball 0 1))
    (hZ : ∃ z, f (σ z) = 0) :
    0 < zeroCharge f σ := by
  have hfin := TauCeti.finite_preimage_preimage_zero h hφ hφd
  rw [zeroCharge_eq_sum_analyticOrderNatAt hφ hφd hfin.toFinset fun z ↦ by simp]
  obtain ⟨z, hz⟩ := hZ
  refine Finset.sum_pos (fun x hx ↦ ?_) ⟨z, hfin.mem_toFinset.2 hz⟩
  have hx0 : φ x = 0 := (hφ x).trans (hfin.mem_toFinset.1 hx)
  have hx := mem_ball_zero_iff.2 x.norm_lt_one
  have han := hφd.analyticOnNhd isOpen_ball
  obtain ⟨w, hw, hφw⟩ := TauCeti.exists_mem_ball_ne_zero h hφ
  -- The order at `x` is finite since it is zero at `w`, where `φ` does not vanish.
  exact Nat.cast_pos.2 (ENat.toNat_pos ((han x hx).analyticOrderAt_ne_zero.2 hx0)
    (han.analyticOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected hw hx
      (by simp [(han w hw).analyticOrderAt_eq_zero.2 hφw])))

end ContinuousMap

/-! ### Discs along which `f` satisfies a Cauchy–Riemann inequality -/

namespace ContinuousMap

variable {f : C(Y, ℂ)} {σ : C(𝔻, Y)} {b : ℂ → ℂ} {M : ℂ → ℝ}

/-- At a zero `z` of `f ∘ σ`, if `f ∘ σ` extends near `z` to `b = v * s` with `v` continuous and
nonzero at `z` and `s` analytic at `z`, and the zeros of `b` do not accumulate at `z`, the local
index of `f ∘ σ` at `z` is positive. -/
private theorem localIndex_pos_of_eventually_eq_mul (hb : ∀ z : 𝔻, b z = f (σ z)) {z : 𝔻}
    (hz : f (σ z) = 0) (hiso : ∀ᶠ w in 𝓝[≠] (z : ℂ), b w ≠ 0) {v s : ℂ → ℂ}
    (hv : ContinuousAt v z) (hv₀ : v z ≠ 0) (hs : AnalyticAt ℂ s z)
    (hbvs : ∀ᶠ w in 𝓝 (z : ℂ), b w = v w * s w) :
    0 < ((complexHomologicalOrientation ℂ).comap Complex.UnitDisc.isOpenEmbedding_coe).localIndex
      (complexHomologicalOrientation ℂ) (f.comp σ) z := by
  have hs₀ : s z = 0 := by
    have h := hbvs.self_of_nhds
    rw [hb z, hz] at h
    exact (mul_eq_zero.1 h.symm).resolve_left hv₀
  have key := HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_of_eventually_eq_mul
    (complexHomologicalOrientation ℂ) Complex.UnitDisc.isOpenEmbedding_coe IsOpenEmbedding.id
    (f := f.comp σ) (φ := b) (x := z) (Eventually.of_forall fun w ↦ hb w) hv hv₀ hs hs₀ hbvs
  rw [HomologicalOrientation.comap_id] at key
  rw [key, Nat.cast_pos]
  -- The order of `s` at `z` is positive since `s z = 0`, and finite since otherwise `s`, hence
  -- `b`, would vanish near `z`, whose zeros do not accumulate there.
  refine ENat.toNat_pos (hs.analyticOrderAt_ne_zero.2 hs₀) fun htop ↦ ?_
  obtain ⟨w, hw, hbw⟩ := ((eventually_nhdsWithin_of_eventually_nhds
    ((analyticOrderAt_eq_top.1 htop).and hbvs)).and hiso).exists
  exact hbw (by rw [hw.2, hw.1, mul_zero])

/-- **Positivity of the zero charge for nearly holomorphic discs.** Suppose `f ∘ σ` extends to a
function `b` of class `C¹` on the unit disc satisfying the Cauchy–Riemann inequality
`‖∂ₛb + i ∂ₜb‖ ≤ M ‖b‖`, for a function `M` bounded above near every point of the disc. If
`σ⁻¹(f⁻¹(0))` is compact and nonempty, the zero charge of `σ` is positive.

By the similarity principle, `b` is near each of its zeros a continuous nonvanishing function
times a holomorphic one, and its zeros are isolated unless it vanishes identically, which
compactness excludes; so each zero has positive local index. For `M = 0` this is
`ContinuousMap.zeroCharge_pos`. The inequality holds for the normal component of a
pseudoholomorphic disc in coordinates adapted to another, immersed, one, and this theorem is then
the positivity of their intersections. -/
theorem zeroCharge_pos_of_norm_le (h : IsCompact (σ ⁻¹' (f ⁻¹' {0})))
    (hb : ∀ z : 𝔻, b z = f (σ z)) (hbC : ContDiffOn ℝ 1 b (ball 0 1))
    (hM : ∀ z ∈ ball (0 : ℂ) 1, ∃ K, ∀ᶠ w in 𝓝 z, M w ≤ K)
    (hle : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ b z 1 + Complex.I • fderiv ℝ b z Complex.I‖ ≤
      M z * ‖b z‖)
    (hZ : ∃ z, f (σ z) = 0) : 0 < f.zeroCharge σ := by
  -- The zeros of `b` do not accumulate in the disc: otherwise `b` would vanish on it, while by
  -- compactness it does not vanish at some `w₀`.
  obtain ⟨w₀, hw₀, hbw₀⟩ := TauCeti.exists_mem_ball_ne_zero h hb
  have hiso (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : ∀ᶠ w in 𝓝[≠] z, b w ≠ 0 := by
    by_contra hfreq
    have h0 := eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le isOpen_ball
      (convex_ball _ _).isPreconnected hbC hM hle hz (by simpa using hfreq)
    exact hbw₀ (h0 hw₀)
  -- Hence the image of the preimage in `ℂ` is compact and discrete, so finite.
  have himg : IsDiscrete (((↑) : 𝔻 → ℂ) '' (σ ⁻¹' (f ⁻¹' {0}))) := by
    refine isDiscrete_iff_nhdsNE.2 fun _ ⟨z, _, hzx⟩ ↦ inf_principal_eq_bot.2 ?_
    subst hzx
    filter_upwards [hiso z (mem_ball_zero_iff.2 z.norm_lt_one)] with w hw ⟨w', hw', hww'⟩
    subst hww'
    exact hw (by simpa [hb w'] using hw')
  have hfin : (σ ⁻¹' (f ⁻¹' {0})).Finite :=
    ((h.image Complex.UnitDisc.continuous_coe).finite himg).of_finite_image
      Complex.UnitDisc.coe_injective.injOn
  have hfib : (f.comp σ) ⁻¹' {0} = σ ⁻¹' (f ⁻¹' {0}) := by
    rw [ContinuousMap.coe_comp, Set.preimage_comp]
  rw [ContinuousMap.zeroCharge, HomologicalOrientation.localDegree_eq_sum_localIndex _ _ _
    Complex.finrank_real_complex _ (hfib ▸ hfin)]
  obtain ⟨z₀, hz₀⟩ := hZ
  refine Finset.sum_pos (fun z hz ↦ ?_) ⟨z₀, by simpa using hz₀⟩
  have hz' : f (σ z) = 0 := by simpa using hz
  -- Near `z`, `b` is a nonvanishing continuous function times a holomorphic one.
  obtain ⟨v, s', hv, hv₀, hs', hbvs⟩ := exists_eventually_eq_mul_of_norm_le isOpen_ball hbC hM hle
    (mem_ball_zero_iff.2 z.norm_lt_one)
  exact localIndex_pos_of_eventually_eq_mul hb hz' (hiso z (mem_ball_zero_iff.2 z.norm_lt_one))
    hv hv₀ hs' hbvs

end ContinuousMap

end ZeroCharge

/-! ### Zero sets of pseudoholomorphic functions -/

namespace TauCeti

section Pseudoholomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  [IsManifold I ∞ Y] {J : SmoothAlmostComplexStructure I Y} {f : C(Y, ℂ)}

/-- **The positive cohomology assignment of the zero set of a `J`-holomorphic function.** For a
`J`-holomorphic `f : Y → ℂ`, the zero charges `ContinuousMap.zeroCharge f σ` of the discs `σ` with
compact `σ⁻¹(f⁻¹(0))` form a positive cohomology assignment to `f⁻¹(0)`: its integer of a
holomorphic disc is the sum of the orders of vanishing of `f` along the disc. -/
def PositiveCohomologyAssignment.zeroSet
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f) :
    PositiveCohomologyAssignment J (f ⁻¹' {0}) where
  charge σ _ := f.zeroCharge σ
  charge_eq_zero _ _ hZ := ContinuousMap.zeroCharge_eq_zero_of_forall_ne_zero hZ
  charge_eq_of_homotopy F hF _ _ := f.zeroCharge_eq_of_homotopy F hF
  charge_comp o _ h _ hθ _ := ContinuousMap.zeroCharge_comp o h hθ
  charge_eq_sum _ h c r hc hr hdisj hcov _ := ContinuousMap.zeroCharge_eq_sum h c r hc hr hdisj hcov
  charge_pos _ h _ hu hhol _ hZ := ContinuousMap.zeroCharge_pos h (fun z ↦ congrArg f (hu z))
    ((hf.isPseudoholomorphicOn univ).differentiableOn_comp hhol (mapsTo_univ _ _)) hZ

/-- The integer of a disc for the zero set of a `J`-holomorphic function is its zero charge. -/
@[simp]
theorem PositiveCohomologyAssignment.charge_zeroSet
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (σ : C(𝔻, Y)) (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) :
    (PositiveCohomologyAssignment.zeroSet hf).charge σ h = f.zeroCharge σ :=
  (rfl)

end Pseudoholomorphic

end TauCeti
