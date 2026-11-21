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
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Deriv

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
`z ↦ c + r z` with `r > 0` preserve the canonical orientation of `ℂ`, being holomorphic.

Now let `Y` carry an almost complex structure `J` and let `f` be `J`-holomorphic. If `σ` is the
restriction of a map `u` that is `J`-holomorphic on the unit disc, then `f ∘ u` is holomorphic,
and a compact `σ⁻¹(Z)` is finite. The zero charge is then the sum of the orders of vanishing of
`f ∘ u` at the points of `σ⁻¹(Z)` (`TauCeti.zeroCharge_eq_sum_analyticOrderNatAt`), which are the
local intersection multiplicities of the disc with `Z`, and it is positive as soon as `σ` meets
`Z` (`TauCeti.zeroCharge_pos`). Hence the zero charges form a positive cohomology assignment to the
zero set of `f` (`TauCeti.PositiveCohomologyAssignment.zeroSet`), whose integer of a holomorphic
disc is the sum of the orders of vanishing of `f` along it. No hypothesis that `σ` is nonconstant
is needed.

## Main definitions

* `TauCeti.zeroCharge f σ`: the local degree of `f ∘ σ` at `0`.
* `TauCeti.PositiveCohomologyAssignment.zeroSet`: the positive cohomology assignment to the zero
  set of a `J`-holomorphic function.

## Main results

* `TauCeti.zeroCharge_comp`, `TauCeti.zeroCharge_eq_of_homotopy`, `TauCeti.zeroCharge_eq_sum`:
  the degree, homotopy and additivity laws.
* `TauCeti.finite_preimage_preimage_zero`: for holomorphic `f ∘ u`, a compact `σ⁻¹(Z)` is finite.
* `TauCeti.zeroCharge_eq_sum_analyticOrderNatAt`: for holomorphic `f ∘ u`, the zero charge is the
  sum of the orders of vanishing.
* `TauCeti.zeroCharge_pos`: it is positive on holomorphic discs meeting `Z`.

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
      Complex.finrank_real_complex (f.comp σ) 0 := by
  rw [zeroCharge]
  rcases HomologicalOrientation.eq_or_eq_neg Complex.finrank_real_complex
    (complexHomologicalOrientation ℂ) o with rfl | rfl
  · rfl
  · rw [HomologicalOrientation.comap_neg,
      HomologicalOrientation.localDegree_neg_left _ _ _ Complex.finrank_real_complex,
      HomologicalOrientation.localDegree_neg_right _ _ _ Complex.finrank_real_complex, neg_neg]

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
  have hdeg : o.degree o Complex.finrank_real_complex θ =
      O.degree O Complex.finrank_real_complex θ := by
    rcases HomologicalOrientation.eq_or_eq_neg Complex.finrank_real_complex O o with rfl | rfl
    · rfl
    · rw [HomologicalOrientation.degree_neg_left _ _ _ Complex.finrank_real_complex,
        HomologicalOrientation.degree_neg_right _ _ _ Complex.finrank_real_complex, neg_neg]
  rw [hdeg, zeroCharge, zeroCharge, ← ContinuousMap.comp_assoc]
  exact O.localDegree_comp O _ Complex.finrank_real_complex Complex.finrank_real_complex
    Complex.finrank_real_complex h hθ

/-- The subdisc maps `z ↦ c + r z`, `r > 0`, pull the orientation of `𝔻` restricted from the
canonical orientation of `ℂ` back to itself: the affine map `w ↦ c + r w` of `ℂ` is a holomorphic
diffeomorphism, so it preserves the canonical orientation. -/
private theorem comap_eq_comap_coe_of_eq_add_mul (c : ℂ) {r : ℝ} (hr : 0 < r) {k : 𝔻 → ℂ}
    (hk : IsOpenEmbedding k) (hkc : ∀ z, k z = c + r * z) :
    (complexHomologicalOrientation ℂ).comap hk =
      (complexHomologicalOrientation ℂ).comap Complex.UnitDisc.isOpenEmbedding_coe := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set A : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (r : ℂ) hr0).trans (Homeomorph.addLeft c)
  have hA : ⇑A = fun w ↦ c + r * w := rfl
  have hloc : IsLocalDiffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) 1 A :=
    isLocalDiffeomorph_of_deriv_ne_zero (by rw [hA]; fun_prop) le_rfl fun w ↦ by
      simpa [hA] using hr0
  rw [← HomologicalOrientation.comap_comap_of_comp_eq _ A.isOpenEmbedding
      Complex.UnitDisc.isOpenEmbedding_coe hk (funext fun z ↦ (hkc z).symm),
    comap_complexHomologicalOrientation A.isOpenEmbedding hloc]

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
  have hs : IsOpenEmbedding (((↑) : 𝔻 → ℂ) ∘ Subtype.val ∘ e) := by
    have hr0 : (r i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hr i).ne'
    set A := (Homeomorph.mulLeft₀ (r i : ℂ) hr0).trans (Homeomorph.addLeft (c i))
    convert A.isOpenEmbedding.comp Complex.UnitDisc.isOpenEmbedding_coe using 1
    exact funext fun z ↦ coe_subdisc_apply z
  have he : IsOpenEmbedding e := (IsOpenEmbedding.of_comp_iff _
    (Complex.UnitDisc.isOpenEmbedding_coe.comp (U i).isOpenEmbedding')).1 hs
  have hsurj : Function.Surjective e := fun w ↦ by
    obtain ⟨z, hz⟩ := (mem_range_subdisc (hc := hc i) (hr := hr i)).2 w.property
    exact ⟨z, Subtype.ext hz⟩
  have hO : (O.comap (U i).isOpenEmbedding').comap he = O := by
    rw [HomologicalOrientation.comap_comap, HomologicalOrientation.comap_comap]
    exact comap_eq_comap_coe_of_eq_add_mul (c i) (hr i) _ fun z ↦ coe_subdisc_apply z
  rw [← O.comap (U i).isOpenEmbedding' |>.localDegree_comap o _ Complex.finrank_real_complex he _
    fun z _ ↦ hsurj z, hO, zeroCharge]
  -- `Subtype.val ∘ e` is `s` by the construction of `e`.
  congr 1

end ZeroCharge

/-! ### Zero sets of pseudoholomorphic functions -/

section Pseudoholomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  [IsManifold I ∞ Y] {J : SmoothAlmostComplexStructure I Y} {f : C(Y, ℂ)} {σ : C(𝔻, Y)}
  {u : ℂ → Y}

/-- A `J`-holomorphic function composed with a disc that is `J`-holomorphic on the unit disc is
holomorphic there. -/
private theorem differentiableOn_comp
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1)) :
    DifferentiableOn ℂ (f ∘ u) (ball 0 1) :=
  isConstStructureJHolomorphicOn_ofComplexModule_iff.1
    ((isPseudoholomorphicOn_constSmooth_iff _ _ _ _).1
      ((hf.isPseudoholomorphicOn univ).comp hhol (mapsTo_univ _ _)))

/-- If `σ⁻¹(f⁻¹(0))` is compact, the extension `f ∘ u` of `f ∘ σ` does not vanish identically on
the unit disc: otherwise the whole noncompact disc would be that preimage. -/
private theorem exists_mem_ball_ne_zero (h : IsCompact (σ ⁻¹' (f ⁻¹' {0})))
    (hu : ∀ z : 𝔻, u z = σ z) : ∃ w ∈ ball (0 : ℂ) 1, f (u w) ≠ 0 := by
  by_contra! hzero
  have huniv : σ ⁻¹' (f ⁻¹' {0}) = univ := eq_univ_of_forall fun z ↦ by
    simpa [← hu z] using hzero z (mem_ball_zero_iff.2 z.norm_lt_one)
  -- The open unit disc would be compact, hence closed in `ℂ`, so it would contain `1`.
  have hcl : IsClosed (ball (0 : ℂ) 1) := by
    convert (huniv ▸ h).image Complex.UnitDisc.continuous_coe |>.isClosed using 1
    ext w
    exact ⟨fun hw ↦ ⟨Complex.UnitDisc.mk w (mem_ball_zero_iff.1 hw), trivial, rfl⟩,
      fun ⟨z, _, hz⟩ ↦ hz ▸ mem_ball_zero_iff.2 z.norm_lt_one⟩
  have h1 : (1 : ℂ) ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball _ one_ne_zero]
    simp
  rw [hcl.closure_eq] at h1
  simp at h1

/-- At a zero in the unit disc, the extension `f ∘ u` of `f ∘ σ` is not locally constant, as soon
as `σ⁻¹(f⁻¹(0))` is compact: by the identity theorem it would vanish on the whole disc. -/
private theorem not_eventuallyConst
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1)) {x : ℂ} (hx : x ∈ ball (0 : ℂ) 1) (hx0 : f (u x) = 0) :
    ¬EventuallyConst (f ∘ u) (𝓝 x) := fun hc ↦ by
  obtain ⟨w, hw, hfw⟩ := exists_mem_ball_ne_zero h hu
  obtain ⟨a, ha⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hc
  have ha0 : a = 0 := ha.self_of_nhds.symm.trans hx0
  subst ha0
  exact hfw (((differentiableOn_comp hf hhol).analyticOnNhd isOpen_ball)
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hx ha hw)

/-- **Finiteness.** If `f` is `J`-holomorphic and `σ` is the restriction to `𝔻` of a map `u` that
is `J`-holomorphic on the unit disc, a compact preimage `σ⁻¹(f⁻¹(0))` is finite: the zeros of the
holomorphic function `f ∘ u` are isolated. -/
theorem finite_preimage_preimage_zero
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1)) :
    (σ ⁻¹' (f ⁻¹' {0})).Finite := by
  obtain ⟨w, hw, hfw⟩ := exists_mem_ball_ne_zero h hu
  have hfin := ((differentiableOn_comp hf hhol).analyticOnNhd isOpen_ball)
    |>.finite_setOf_mem_and_eq_zero_of_isCompact (convex_ball _ _).isPreconnected hw hfw
      (h.image Complex.UnitDisc.continuous_coe)
      (image_subset_iff.2 fun z _ ↦ mem_ball_zero_iff.2 z.norm_lt_one)
  refine (hfin.preimage Complex.UnitDisc.coe_injective.injOn).subset fun z hz ↦
    ⟨mem_image_of_mem _ hz, ?_⟩
  simpa [hu z] using hz

/-- The local index of `f ∘ σ` at a zero `z` is the order of vanishing of `f ∘ u` at `z`. -/
private theorem localIndex_eq_analyticOrderNatAt
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1)) {z : 𝔻} (hz : f (σ z) = 0) :
    ((complexHomologicalOrientation ℂ).comap Complex.UnitDisc.isOpenEmbedding_coe).localIndex
      (complexHomologicalOrientation ℂ) (f.comp σ) z = analyticOrderNatAt (f ∘ u) z := by
  have key := HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub
    (complexHomologicalOrientation ℂ) Complex.UnitDisc.isOpenEmbedding_coe IsOpenEmbedding.id
    (f := f.comp σ) (φ := f ∘ u) (x := z) (Eventually.of_forall fun w ↦ by simp [hu w])
    ((differentiableOn_comp hf hhol).analyticAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 z.norm_lt_one)))
  rw [HomologicalOrientation.comap_id] at key
  rw [key]
  simp only [Function.comp_apply, hu z, hz, sub_zero]
  rfl

/-- **The zero charge counts orders of vanishing.** If `f` is `J`-holomorphic, `σ` is the
restriction to `𝔻` of a map `u` that is `J`-holomorphic on the unit disc, and `σ⁻¹(f⁻¹(0))` is the
finite set `s`, then the zero charge of `σ` is the sum over `s` of the orders of vanishing of the
holomorphic function `f ∘ u`: the local intersection multiplicities of the disc with `f⁻¹(0)`. -/
theorem zeroCharge_eq_sum_analyticOrderNatAt
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1)) (s : Finset 𝔻) (hs : ∀ z, f (σ z) = 0 ↔ z ∈ s) :
    zeroCharge f σ = ∑ z ∈ s, (analyticOrderNatAt (f ∘ u) z : ℤ) := by
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
    localIndex_eq_analyticOrderNatAt hf hu hhol ((hs z).2 hz)

/-- **Positivity.** If `f` is `J`-holomorphic and `σ` is the restriction to `𝔻` of a map that is
`J`-holomorphic on the unit disc, with `σ⁻¹(f⁻¹(0))` compact and nonempty, the zero charge of `σ`
is positive. -/
theorem zeroCharge_pos
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1)) (hZ : ∃ z, f (σ z) = 0) :
    0 < zeroCharge f σ := by
  have hfin := finite_preimage_preimage_zero hf h hu hhol
  rw [zeroCharge_eq_sum_analyticOrderNatAt hf hu hhol hfin.toFinset fun z ↦ by simp]
  obtain ⟨z, hz⟩ := hZ
  refine Finset.sum_pos (fun x hx ↦ ?_) ⟨z, hfin.mem_toFinset.2 hz⟩
  have hx0 : f (σ x) = 0 := hfin.mem_toFinset.1 hx
  rw [← localIndex_eq_analyticOrderNatAt hf hu hhol hx0]
  have key := HomologicalOrientation.localIndex_comap_pos_iff_of_analyticAt
    (complexHomologicalOrientation ℂ) Complex.UnitDisc.isOpenEmbedding_coe IsOpenEmbedding.id
    (f := f.comp σ) (φ := f ∘ u) (x := x) (Eventually.of_forall fun w ↦ by simp [hu w])
    ((differentiableOn_comp hf hhol).analyticAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 x.norm_lt_one)))
  rw [HomologicalOrientation.comap_id] at key
  exact key.2 (not_eventuallyConst hf h hu hhol (mem_ball_zero_iff.2 x.norm_lt_one)
    (by simpa [hu x] using hx0))

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
  charge_pos _ h _ hu hhol _ hZ := zeroCharge_pos hf h hu hhol hZ

/-- The integer of a disc for the zero set of a `J`-holomorphic function is its zero charge. -/
@[simp]
theorem PositiveCohomologyAssignment.charge_zeroSet
    (hf : IsPseudoholomorphic J (AlmostComplexStructure.ofComplexModule ℂ).constSmooth f)
    (σ : C(𝔻, Y)) (h : IsCompact (σ ⁻¹' (f ⁻¹' {0}))) :
    (PositiveCohomologyAssignment.zeroSet hf).charge σ h = zeroCharge f σ :=
  (rfl)

end Pseudoholomorphic

end TauCeti
