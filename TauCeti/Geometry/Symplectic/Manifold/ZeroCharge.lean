/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Symplectic.Manifold.PositiveCohomologyAssignment
import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.Conformal.LocalIndex

/-!
# The zero charges of discs and the zero set of a pseudoholomorphic function

Let `f : Y → ℂ` be a continuous function on a space `Y`. A continuous disc `σ : 𝔻 → Y` meets the
zero set `Z = f⁻¹(0)` in `σ⁻¹(Z)`, the zero set of `f ∘ σ`. Its **zero charge**
`TauCeti.zeroCharge f σ` is the local degree of `f ∘ σ : 𝔻 → ℂ` at `0`
(`TauCeti.HomologicalOrientation.localDegree`): the number of zeros of `f ∘ σ`, counted with their
topological multiplicities. It is defined with the canonical orientation of `ℂ` on the target and
its restriction to `𝔻` on the source, and does not depend on that choice
(`TauCeti.zeroCharge_eq_localDegree`). On open subsets of `ℂ`, local degrees at `0` are winding
numbers along circles enclosing the zeros
(`TauCeti.HomologicalOrientation.localDegree_comap_eq_degree_toBasedLoop`), so when `f` is the
framing section of a trivialized line, the zero charge is the framed charge of `σ`.

When `σ⁻¹(Z)` is compact, the zero charge obeys the laws of a positive cohomology assignment
(`TauCeti.PositiveCohomologyAssignment`) other than positivity, for every continuous `f`:

* **vacuum**: it vanishes when `σ` misses `Z` (`TauCeti.zeroCharge_eq_zero_of_forall_ne_zero`);
* **homotopy**: it is constant along a homotopy whose total preimage of `Z` is compact
  (`TauCeti.zeroCharge_eq_of_homotopy`);
* **degree**: it multiplies by the degree of a proper reparametrization `θ : 𝔻 → 𝔻`
  (`TauCeti.zeroCharge_comp`);
* **additivity**: it is the sum of the zero charges of finitely many disjoint round subdiscs
  containing `σ⁻¹(Z)` (`TauCeti.zeroCharge_eq_sum`).

These are the local degree's naturality under proper maps, invariance under homotopies with
compact fibre, and additivity over disjoint open sets. For additivity, the subdisc maps
`z ↦ c + r z` with `r > 0` preserve the canonical orientation of `ℂ`, being holomorphic
(`TauCeti.comap_coe_comp_subdisc_complexHomologicalOrientation`).

If `f ∘ σ` extends to a function `φ` holomorphic on the unit disc, a compact `σ⁻¹(Z)` is finite
(`TauCeti.finite_preimage_preimage_zero`). The zero charge is then the sum of the orders of
vanishing of `φ` at the points of `σ⁻¹(Z)` (`TauCeti.zeroCharge_eq_sum_analyticOrderNatAt`), which
are the local intersection multiplicities of the disc with `Z`, and it is positive as soon as `σ`
meets `Z` (`TauCeti.zeroCharge_pos`).

Now let `Y` carry an almost complex structure `J` and let `f` be `J`-holomorphic. If `σ` is the
restriction of a map `u` that is `J`-holomorphic on the unit disc, then `f ∘ u` is holomorphic
(`TauCeti.IsPseudoholomorphicOn.differentiableOn_comp`). Hence the zero charges form a positive
cohomology assignment to the zero set of `f` (`TauCeti.PositiveCohomologyAssignment.zeroSet`),
whose integer of a holomorphic disc is the sum of the orders of vanishing of `f` along it. No
hypothesis that `σ` is nonconstant is needed.

## Main definitions

* `TauCeti.zeroCharge f σ`: the local degree of `f ∘ σ` at `0`.
* `TauCeti.PositiveCohomologyAssignment.zeroSet`: the positive cohomology assignment to the zero
  set of a `J`-holomorphic function.

## Main results

* `TauCeti.zeroCharge_comp`, `TauCeti.zeroCharge_eq_of_homotopy`, `TauCeti.zeroCharge_eq_sum`:
  the degree, homotopy and additivity laws.
* `TauCeti.finite_preimage_preimage_zero`: if `f ∘ σ` extends holomorphically, a compact
  `σ⁻¹(Z)` is finite.
* `TauCeti.zeroCharge_eq_sum_analyticOrderNatAt`: if `f ∘ σ` extends holomorphically, the zero
  charge is the sum of the orders of vanishing.
* `TauCeti.zeroCharge_pos`: it is positive on such discs meeting `Z`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4.
-/

public section

noncomputable section

open Filter Metric Set Topology
open TauCeti.Complex.UnitDisc
open scoped Complex.UnitDisc Manifold ContDiff

namespace TauCeti

/-! ### The zero charge of a disc -/

section ZeroCharge

variable {Y : Type*} [TopologicalSpace Y]

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
  rw [zeroCharge, O.localDegree_eq_sum o _ Complex.finrank_real_complex (f.comp σ) h (U := U) hU
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

/-! ### Discs along which `f` is holomorphic -/

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
  exact Finset.sum_congr rfl fun z hz ↦ localIndex_eq_analyticOrderNatAt hφ hφd ((hs z).2 hz)

/-- **Positivity.** If `f ∘ σ` extends to a function `φ` holomorphic on the unit disc, with
`σ⁻¹(f⁻¹(0))` compact and nonempty, the zero charge of `σ` is positive: by the identity theorem, `φ`
vanishes to finite, positive order at each zero. -/
theorem zeroCharge_pos {f : C(Y, ℂ)} {σ : C(𝔻, Y)} (h : IsCompact (σ ⁻¹' (f ⁻¹' {0})))
    {φ : ℂ → ℂ} (hφ : ∀ z : 𝔻, φ z = f (σ z)) (hφd : DifferentiableOn ℂ φ (ball 0 1))
    (hZ : ∃ z, f (σ z) = 0) :
    0 < zeroCharge f σ := by
  have hfin := finite_preimage_preimage_zero h hφ hφd
  rw [zeroCharge_eq_sum_analyticOrderNatAt hφ hφd hfin.toFinset fun z ↦ by simp]
  obtain ⟨z, hz⟩ := hZ
  refine Finset.sum_pos (fun x hx ↦ ?_) ⟨z, hfin.mem_toFinset.2 hz⟩
  have hx0 : φ x = 0 := (hφ x).trans (hfin.mem_toFinset.1 hx)
  have hx := mem_ball_zero_iff.2 x.norm_lt_one
  have han := hφd.analyticOnNhd isOpen_ball
  obtain ⟨w, hw, hφw⟩ := exists_mem_ball_ne_zero h hφ
  -- The order at `x` is finite since it is zero at `w`, where `φ` does not vanish.
  exact Nat.cast_pos.2 (ENat.toNat_pos ((han x hx).analyticOrderAt_ne_zero.2 hx0)
    (han.analyticOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected hw hx
      (by simp [(han w hw).analyticOrderAt_eq_zero.2 hφw])))

end ZeroCharge

/-! ### Zero sets of pseudoholomorphic functions -/

section Pseudoholomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  [IsManifold I ∞ Y] {J : SmoothAlmostComplexStructure I Y} {f : C(Y, ℂ)}

/-- **The positive cohomology assignment of the zero set of a `J`-holomorphic function.** For a
`J`-holomorphic `f : Y → ℂ`, the zero charges `TauCeti.zeroCharge f σ` of the discs `σ` with
compact `σ⁻¹(f⁻¹(0))` form a positive cohomology assignment to `f⁻¹(0)`: its integer of a
holomorphic disc is the sum of the orders of vanishing of `f` along the disc. -/
def PositiveCohomologyAssignment.zeroSet
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f) :
    PositiveCohomologyAssignment J (f ⁻¹' {0}) where
  charge σ _ := zeroCharge f σ
  charge_eq_zero _ _ hZ := zeroCharge_eq_zero_of_forall_ne_zero hZ
  charge_eq_of_homotopy F hF _ _ := zeroCharge_eq_of_homotopy f F hF
  charge_comp o _ h _ hθ _ := zeroCharge_comp o h hθ
  charge_eq_sum _ h c r hc hr hdisj hcov _ := zeroCharge_eq_sum h c r hc hr hdisj hcov
  charge_pos _ h _ hu hhol _ hZ := zeroCharge_pos h (fun z ↦ congrArg f (hu z))
    ((hf.isPseudoholomorphicOn univ).differentiableOn_comp hhol (mapsTo_univ _ _)) hZ

/-- The integer of a disc for the zero set of a `J`-holomorphic function is its zero charge. -/
@[simp]
theorem PositiveCohomologyAssignment.charge_zeroSet
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (σ : C(𝔻, Y)) (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) :
    (PositiveCohomologyAssignment.zeroSet hf).charge σ h = zeroCharge f σ :=
  (rfl)

end Pseudoholomorphic

end TauCeti
