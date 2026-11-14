/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Infinite.ClassifyingCoordinates
public import TauCeti.Topology.VectorBundle.Core.Hom
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance
public import Mathlib.CategoryTheory.IsomorphismClasses
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Universal vector bundle classification over paracompact bases

Over `RCLike 𝕜`, homotopy classes of continuous maps from a paracompact `R₁` space `X` to the
infinite Grassmannian `TauCeti.infiniteGrassmannian 𝕜 k` classify rank-`k` `𝕜`-vector bundles over
`X` up to isomorphism via pullback of `TauCeti.infiniteGrassmannian.Tautological 𝕜 k`.

* `TauCeti.infiniteGrassmannian.homotopic_id_mapContinuousMap_lmapDomain`,
  `TauCeti.IsClassifyingCoordinates.homotopic_classifyContinuousMap`, and
  `TauCeti.infiniteGrassmannian.homotopic_id_classifyContinuousMap_tautological`: coordinate-shift
  homotopies and homotopy uniqueness of classifying maps.
* `TauCeti.infiniteGrassmannian.homotopic_of_pullback_equiv` and
  `homotopic_iff_exists_pullbackEquiv`: homotopy invariance and classification of tautological
  pullbacks.
* `TauCeti.infiniteGrassmannian.tautologicalCore` and `classificationEquiv`: the universal core and
  natural bijection `[X, infiniteGrassmannian 𝕜 k] ≃ Iso_{=k}(FiniteRankBundleCore 𝕜 X)`.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5, Theorem 5.6 and Lemma 5.9.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.16.
-/

public noncomputable section

open Bundle Set Function Filter CategoryTheory _root_.Finsupp
open scoped Topology unitInterval

namespace TauCeti

section HomotopyUniqueness

namespace infiniteGrassmannian

/-- The image of `Tautological.subtype W` is the underlying submodule `W.1`. -/
@[simp] theorem Tautological.range_subtype {𝕜 : Type*} [Field 𝕜] {k : ℕ}
    (W : infiniteGrassmannian 𝕜 k) :
    LinearMap.range (Tautological.subtype W) = W.1 :=
  le_antisymm (by rintro _ ⟨v, rfl⟩; rw [Tautological.subtype_apply]; exact v.property)
    fun w hw ↦ ⟨⟨w, hw⟩, Tautological.subtype_apply _ _⟩

/-- A map out of `Y × infiniteGrassmannian 𝕜 k` for a locally compact space `Y` is continuous if and
only if its restriction to `Y × finiteGrassmannian 𝕜 k n` is continuous for every stage `n : ℕ`. -/
theorem continuous_prod_left_iff {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] {k : ℕ}
    {Y Z : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [TopologicalSpace Z]
    {g : Y × infiniteGrassmannian 𝕜 k → Z} :
    Continuous g ↔
      ∀ n, Continuous fun q : Y × finiteGrassmannian 𝕜 k n ↦
        g (q.1, finiteGrassmannian.toInfinite q.2) := by
  refine ⟨fun hg n ↦ hg.comp (continuous_id.prodMap finiteGrassmannian.continuous_toInfinite),
    fun hg ↦ isQuotientMap_sigmaToInfinite.continuous_lift_prod_right ?_⟩
  let G : C(Σ n, finiteGrassmannian 𝕜 k n, C(Y, Z)) :=
    ⟨fun s ↦ ContinuousMap.curry
      ⟨fun r : finiteGrassmannian 𝕜 k s.1 × Y ↦ g (r.2, finiteGrassmannian.toInfinite r.1),
        (hg s.1).comp continuous_swap⟩ s.2,
      continuous_sigma fun n ↦ (ContinuousMap.curry ⟨_, (hg n).comp continuous_swap⟩).continuous⟩
  exact ((ContinuousMap.continuous_uncurry_of_continuous G).comp continuous_swap).congr
    fun ⟨_, ⟨_, _⟩⟩ ↦ by simp [G, Function.uncurry]

section Shifts

private def shiftInterp (𝕜 : Type*) [CommRing 𝕜] (s : ℕ → ℕ) (c : 𝕜) : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  (1 - c) • LinearMap.id + c • Finsupp.lmapDomain 𝕜 𝕜 s

private theorem shiftInterp_injective {𝕜 : Type*} [CommRing 𝕜] [IsDomain 𝕜]
    {s : ℕ → ℕ} (hs : StrictMono s) (c : 𝕜) : Injective (shiftInterp 𝕜 s c) := by
  refine LinearMap.ker_eq_bot.1 <| LinearMap.ker_eq_bot'.2 fun v hv ↦ ?_
  by_contra hv0
  let m := v.support.max' (Finsupp.support_nonempty_iff.2 hv0)
  have hvm : v m ≠ 0 := Finsupp.mem_support_iff.1 (Finset.max'_mem _ _)
  rcases (hs.id_le m : m ≤ s m).eq_or_lt with h_eq | h_lt
  · have heval := congrArg (fun w : ℕ →₀ 𝕜 ↦ w m) hv
    have hmap : Finsupp.mapDomain s v m = v m :=
      (congrArg (Finsupp.mapDomain s v) h_eq).trans
        (Finsupp.mapDomain_apply_of_injective hs.injective v m)
    simp only [shiftInterp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, coe_add,
      coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finsupp.zero_apply, lmapDomain_apply,
      hmap, ← add_mul, sub_add_cancel, one_mul] at heval
    exact hvm heval
  · by_cases hc : c = 0
    · exact hv0 (by simpa [shiftInterp, hc] using hv)
    · have heval := congrArg (fun w : ℕ →₀ 𝕜 ↦ w (s m)) hv
      have hv_sm : v (s m) = 0 := Finsupp.notMem_support_iff.1 fun hsm ↦
        (lt_irrefl m) (h_lt.trans_le (Finset.le_max' _ _ hsm))
      simp only [shiftInterp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        coe_add, coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finsupp.zero_apply,
        lmapDomain_apply, hv_sm, mul_zero, zero_add,
        mapDomain_apply_of_injective hs.injective v m] at heval
      exact (mul_ne_zero hc hvm) heval

private def stageTautologicalLinearMap {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k n : ℕ}
    (V : finiteGrassmannian 𝕜 k n) :
    ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k)) V →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Tautological.subtype (finiteGrassmannian.toInfinite V)

private theorem isClassifyingCoordinates_stageTautological
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k n : ℕ} :
    IsClassifyingCoordinates 𝕜 (Fin k → 𝕜)
      ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k))
      (stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) (n := n)) where
  continuous_coord m :=
    ((continuous_evalCoord m).comp
      (Pullback.continuous_lift (Fin k → 𝕜) (Tautological 𝕜 k)
        (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _))).congr
          fun ⟨_, v⟩ ↦ by
            simp only [Function.comp_apply, Pullback.lift, stageTautologicalLinearMap]
            exact (congrArg (fun w : ℕ →₀ 𝕜 ↦ w m) (Tautological.subtype_apply _ v)).symm
  locally_supported _ :=
    ⟨n, Filter.Eventually.of_forall fun V v m hm ↦ by
      obtain ⟨u, -, hu⟩ := Submodule.mem_map.1 ((finiteGrassmannian.coe_toInfinite V) ▸ v.2)
      have hv : stageTautologicalLinearMap V v = v.val := Tautological.subtype_apply _ v
      rw [hv, ← hu] at hm
      exact Finset.mem_range.2 (lt_of_not_ge fun hge ↦
        (Finsupp.mem_support_iff.1 hm) (coordinateInclusion_apply_of_le u hge))⟩
  injective V := Tautological.subtype_injective (finiteGrassmannian.toInfinite V)

end Shifts

/-- Any strictly monotone coordinate shift `s : ℕ → ℕ` induces a self-map of
`infiniteGrassmannian 𝕜 k` homotopic to the identity. -/
theorem homotopic_id_mapContinuousMap_lmapDomain
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ} {s : ℕ → ℕ}
    (hs : StrictMono s)
    (hφ : Injective (Finsupp.lmapDomain 𝕜 𝕜 s) := Finsupp.mapDomain_injective hs.injective) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (mapContinuousMap (Finsupp.lmapDomain 𝕜 𝕜 s) hφ) := by
  let H : I × infiniteGrassmannian 𝕜 k → infiniteGrassmannian 𝕜 k := fun p ↦
    map (shiftInterp 𝕜 s (algebraMap ℝ 𝕜 p.1.1)) (shiftInterp_injective hs _) p.2
  refine ⟨{
    toFun := H
    continuous_toFun := continuous_prod_left_iff.2 fun n ↦ by
      let E_n := (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k)
      let hj₀ := isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)
      let hj₁ := hj₀.postcomp (FiberBundle.continuous_proj (Fin k → 𝕜) E_n)
        (Finsupp.lmapDomain 𝕜 𝕜 s) hφ
      have heq (c : 𝕜) (V : finiteGrassmannian 𝕜 k n) :
          (1 - c) • stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) V +
            c • (Finsupp.lmapDomain 𝕜 𝕜 s).comp (stageTautologicalLinearMap V) =
          (shiftInterp 𝕜 s c).comp (stageTautologicalLinearMap V) := by ext; simp [shiftInterp]
      have hinj (t : I) (V : finiteGrassmannian 𝕜 k n) :
          Injective ((1 - algebraMap ℝ 𝕜 t.1) • stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) V +
            (algebraMap ℝ 𝕜 t.1) • (Finsupp.lmapDomain 𝕜 𝕜 s).comp
              (stageTautologicalLinearMap V)) := by
        rw [heq]; exact (shiftInterp_injective hs _).comp (Tautological.subtype_injective _)
      refine ((hj₀.cylinderInterp hj₁ hinj).continuous_classify (Module.finrank_fin_fun 𝕜)).congr
        fun q ↦ Subtype.ext ?_
      have hrange : LinearMap.range (stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) q.2) =
          (finiteGrassmannian.toInfinite q.2).1 := Tautological.range_subtype _
      refine (IsClassifyingCoordinates.coe_classify _ _ q).trans
        ((congrArg LinearMap.range (heq (algebraMap ℝ 𝕜 q.1.1) q.2)).trans ?_)
      rw [LinearMap.range_comp, hrange, ← coe_map]
    map_zero_left W := Subtype.ext <| by
      have h0 : shiftInterp 𝕜 s 0 = LinearMap.id := by ext; simp [shiftInterp]
      simp [H, h0]
    map_one_left W := Subtype.ext <| by
      have h1 : shiftInterp 𝕜 s 1 = Finsupp.lmapDomain 𝕜 𝕜 s := by ext; simp [shiftInterp]
      rw [mapContinuousMap_apply]; simp [H, h1] }⟩

private def evenLinear (𝕜 : Type*) [Semiring 𝕜] : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m)
private def oddLinear (𝕜 : Type*) [Semiring 𝕜] : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m + 1)
private theorem strictMono_even : StrictMono (fun m : ℕ ↦ 2 * m) :=
  fun _ _ h ↦ Nat.mul_lt_mul_of_pos_left h Nat.two_pos
private theorem strictMono_odd : StrictMono (fun m : ℕ ↦ 2 * m + 1) :=
  fun _ _ h ↦ Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left h Nat.two_pos)
private theorem evenLinear_injective (𝕜 : Type*) [Semiring 𝕜] : Injective (evenLinear 𝕜) :=
  Finsupp.mapDomain_injective strictMono_even.injective
private theorem oddLinear_injective (𝕜 : Type*) [Semiring 𝕜] : Injective (oddLinear 𝕜) :=
  Finsupp.mapDomain_injective strictMono_odd.injective

private theorem even_odd_interp_injective {𝕜 M : Type*} [CommRing 𝕜] [IsDomain 𝕜]
    [AddCommMonoid M] [Module 𝕜 M] {f₀ f₁ : M →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hf₀ : Injective f₀) (hf₁ : Injective f₁) (c : 𝕜) :
    Injective ((1 - c) • (evenLinear 𝕜).comp f₀ + c • (oddLinear 𝕜).comp f₁) := fun v w hvw ↦ by
  by_cases hc : c = 0
  · subst hc; refine hf₀ <| Finsupp.ext fun m ↦ ?_
    simpa [evenLinear, mapDomain_apply_of_injective strictMono_even.injective] using
      congrArg (fun z : ℕ →₀ 𝕜 ↦ z (2 * m)) hvw
  · refine hf₁ <| Finsupp.ext fun m ↦ ?_
    have hod := congrArg (fun z : ℕ →₀ 𝕜 ↦ z (2 * m + 1)) hvw
    have hev0 (u : ℕ →₀ 𝕜) : evenLinear 𝕜 u (2 * m + 1) = 0 :=
      Finsupp.mapDomain_of_notMem_range u _ (by rintro ⟨r, hr⟩; dsimp only at hr; omega)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, coe_add, coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, hev0, mul_zero, zero_add, oddLinear,
      lmapDomain_apply, mapDomain_apply_of_injective strictMono_odd.injective] at hod
    exact mul_left_cancel₀ hc hod

end infiniteGrassmannian

/-- Any two families of classifying coordinates on the same vector bundle `E` over an arbitrary
topological space `X` induce homotopic classifying maps to `infiniteGrassmannian 𝕜 k`. -/
theorem IsClassifyingCoordinates.homotopic_classifyContinuousMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hk : Module.finrank 𝕜 F = k) :
    (hj₀.classifyContinuousMap hk).Homotopic (hj₁.classifyContinuousMap hk) := by
  have hπ : Continuous (π F E) := FiberBundle.continuous_proj F E
  let hev := hj₀.postcomp hπ (infiniteGrassmannian.evenLinear 𝕜)
    (infiniteGrassmannian.evenLinear_injective 𝕜)
  let hod := hj₁.postcomp hπ (infiniteGrassmannian.oddLinear 𝕜)
    (infiniteGrassmannian.oddLinear_injective 𝕜)
  have hmid : (hev.classifyContinuousMap hk).Homotopic (hod.classifyContinuousMap hk) :=
    ⟨hev.homotopyOfLinearCombinationInjective hod
      (fun t x ↦ infiniteGrassmannian.even_odd_interp_injective
        (hj₀.injective x) (hj₁.injective x) (algebraMap ℝ 𝕜 t.1)) hk⟩
  rw [hj₀.classifyContinuousMap_postcomp _ (infiniteGrassmannian.evenLinear_injective 𝕜) hk,
    hj₁.classifyContinuousMap_postcomp _ (infiniteGrassmannian.oddLinear_injective 𝕜) hk] at hmid
  exact (ContinuousMap.Homotopic.comp
    (infiniteGrassmannian.homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k)
      infiniteGrassmannian.strictMono_even) (.refl _)).trans
    (hmid.trans (ContinuousMap.Homotopic.comp
      (infiniteGrassmannian.homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k)
        infiniteGrassmannian.strictMono_odd) (.refl _)).symm)

namespace infiniteGrassmannian

/-- Any family of classifying coordinates on `Tautological 𝕜 k` itself induces a classifying map
homotopic to the identity of `infiniteGrassmannian 𝕜 k`. -/
theorem homotopic_id_classifyContinuousMap_tautological
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    {j : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) j) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (hj.classifyContinuousMap (Module.finrank_fin_fun 𝕜)) := by
  let c := hj.classifyContinuousMap (Module.finrank_fin_fun 𝕜)
  let J (t : I) (W : infiniteGrassmannian 𝕜 k) : Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜) :=
    (1 - algebraMap ℝ 𝕜 t.1) • (evenLinear 𝕜).comp (Tautological.subtype W) +
      (algebraMap ℝ 𝕜 t.1) • (oddLinear 𝕜).comp (j W)
  have hJ_inj (t : I) (W : infiniteGrassmannian 𝕜 k) : Injective (J t W) :=
    even_odd_interp_injective (Tautological.subtype_injective W) (hj.injective W)
      (algebraMap ℝ 𝕜 t.1)
  let H : I × infiniteGrassmannian 𝕜 k → infiniteGrassmannian 𝕜 k := fun p ↦
    ⟨LinearMap.range (J p.1 p.2),
      (LinearEquiv.ofInjective (J p.1 p.2) (hJ_inj p.1 p.2)).symm.rank_eq.trans
        ((tautologicalEquiv 𝕜 k p.2).rank_eq.trans p.2.2)⟩
  have hcont : Continuous H := continuous_prod_left_iff.2 fun n ↦ by
    let E_n := (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k)
    have hπ_n : Continuous (π (Fin k → 𝕜) E_n) := FiberBundle.continuous_proj (Fin k → 𝕜) E_n
    let hj_stage := (isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)).postcomp
      hπ_n (evenLinear 𝕜) (evenLinear_injective 𝕜)
    let hj_pull := (hj.pullback finiteGrassmannian.toInfiniteContinuousMap).postcomp
      hπ_n (oddLinear 𝕜) (oddLinear_injective 𝕜)
    exact ((hj_stage.cylinderInterp hj_pull fun t _ ↦ hJ_inj t _).continuous_classify
      (Module.finrank_fin_fun 𝕜)).congr fun _ ↦ Subtype.ext rfl
  have hmid : (mapContinuousMap (evenLinear 𝕜) (evenLinear_injective 𝕜)).Homotopic
      ((mapContinuousMap (oddLinear 𝕜) (oddLinear_injective 𝕜)).comp c) :=
    ⟨{ toFun := H, continuous_toFun := hcont
       map_zero_left W := Subtype.ext <| by
         have h0 : J 0 W = (evenLinear 𝕜).comp (Tautological.subtype W) := by ext; simp [J]
         simp [H, h0, LinearMap.range_comp]
       map_one_left W := Subtype.ext <| by
         have h1 : J 1 W = (oddLinear 𝕜).comp (j W) := by ext; simp [J]
         simp [H, c, h1, LinearMap.range_comp] }⟩
  exact (homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k) strictMono_even).trans
    (hmid.trans (ContinuousMap.Homotopic.comp
      (homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k) strictMono_odd) (.refl c)).symm)

/-- Over `RCLike 𝕜` and an arbitrary topological space `X`, if the pullbacks of `Tautological 𝕜 k`
along `f₀, f₁ : C(X, _)` admit a continuous fibrewise linear equivalence, then `f₀` and `f₁` are
homotopic. -/
theorem homotopic_of_pullback_equiv {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) p.proj (Φ p.proj p.2)) :
    f₀.Homotopic f₁ := by
  obtain ⟨j_univ, hj_univ⟩ := exists_isClassifyingCoordinates (𝕜 := 𝕜)
    (X := infiniteGrassmannian 𝕜 k) (F := Fin k → 𝕜) (E := Tautological 𝕜 k)
  have hk := Module.finrank_fin_fun (R := 𝕜) (n := k)
  let c := hj_univ.classifyContinuousMap hk
  have hc := homotopic_id_classifyContinuousMap_tautological hj_univ
  let hj₁' := (hj_univ.pullback f₁).compLinearMap (G := Fin k → 𝕜)
    (E' := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) (fun x ↦ (Φ x).toLinearMap) (fun x ↦ (Φ x).injective)
    hΦ
  have hmid : (c.comp f₀).Homotopic (c.comp f₁) := by
    rw [← hj_univ.classifyContinuousMap_pullback f₀ hk,
      ← hj_univ.classifyContinuousMap_pullback f₁ hk,
      ← (hj_univ.pullback f₁).classifyContinuousMap_compLinearEquiv (G := Fin k → 𝕜)
          (E' := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) (fun x ↦ (Φ x).toLinearEquiv) hΦ hk hk]
    exact (hj_univ.pullback f₀).homotopic_classifyContinuousMap hj₁' hk
  exact (ContinuousMap.Homotopic.comp hc (.refl f₀)).trans
    (hmid.trans (ContinuousMap.Homotopic.comp hc (.refl f₁)).symm)

/-- Over `RCLike 𝕜` and a paracompact `R₁` base `X`, two continuous maps
`f₀, f₁ : C(X, infiniteGrassmannian 𝕜 k)` are homotopic if and only if the pullbacks of
`Tautological 𝕜 k` along `f₀` and `f₁` are isomorphic as vector bundles. -/
theorem homotopic_iff_exists_pullbackEquiv
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X] [ParacompactSpace X] [R1Space X]
    {k : ℕ} {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)} :
    f₀.Homotopic f₁ ↔
      ∃ Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x),
        Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
          TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
            p.proj (Φ p.proj p.2) :=
  ⟨fun h ↦
    let ⟨Φ, hΦ, _⟩ := h.exists_continuousLinearEquiv_pullback (F := Fin k → 𝕜)
      (E := Tautological 𝕜 k)
    ⟨Φ, hΦ⟩,
   fun ⟨Φ, hΦ⟩ ↦ homotopic_of_pullback_equiv Φ hΦ⟩

end infiniteGrassmannian

end HomotopyUniqueness

section SmallClassification

namespace infiniteGrassmannian

section CoreComparisons

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]

variable (𝕜) in
/-- The universal tautological bundle over `infiniteGrassmannian 𝕜 k` packaged as a point-indexed
finite-rank coordinate core in `FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k)`. -/
@[expose, implicit_reducible]
def tautologicalCore (k : ℕ) : FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k) where
  rank := k
  core := pointIndexedCore 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  indexAt_eq := pointIndexedCore_indexAt 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)

@[simp] theorem rank_tautologicalCore (k : ℕ) : (tautologicalCore 𝕜 k).rank = k := (rfl)

@[simp] theorem core_tautologicalCore (k : ℕ) :
    (tautologicalCore 𝕜 k).core = pointIndexedCore 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) := (rfl)

theorem tautologicalCore_eq_ofBundle (k : ℕ) :
    tautologicalCore 𝕜 k = .ofBundle 𝕜 k (Tautological 𝕜 k) := (rfl)

private abbrev PullbackTaut {k : ℕ} (f : C(X, infiniteGrassmannian 𝕜 k)) :=
  (f : _ → _) *ᵖ (Tautological 𝕜 k)

private def tautologicalPullbackPointCore {k : ℕ} (f : C(X, infiniteGrassmannian 𝕜 k)) :
    FiniteRankBundleCore 𝕜 X where
  rank := k
  core := pointIndexedCore 𝕜 (Fin k → 𝕜) (PullbackTaut f)
  indexAt_eq := pointIndexedCore_indexAt 𝕜 (Fin k → 𝕜) (PullbackTaut f)

private def coreIsoOfContinuousEquiv [CompleteSpace 𝕜] {A D : FiniteRankBundleCore 𝕜 X}
    (ψ : X → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hψ : Continuous fun p : A.core.TotalSpace ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) p.proj (ψ p.proj p.2)) : A ≅ D := by
  let hom : A ⟶ D := VectorBundleCore.CoordinateHom.ofContinuous
    (fun x ↦ (ψ x).toContinuousLinearMap)
    ((continuous_hom_bundle_iff (E₁ := A.core.Fiber) (E₂ := D.core.Fiber) _).2 hψ)
  have : IsIso hom := (FiniteRankBundleCore.isIso_iff_bijective hom).2 fun x ↦ by
    rw [congrFun (VectorBundleCore.CoordinateHom.fiberMap_ofContinuous _ _) x]
    exact (ψ x).bijective
  exact asIso hom

private def tautologicalPullbackIso [CompleteSpace 𝕜] {k : ℕ}
    (f : C(X, infiniteGrassmannian 𝕜 k)) :
    (tautologicalCore 𝕜 k).pullback f ≅ tautologicalPullbackPointCore f := by
  let eT := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  let eP := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (PullbackTaut f)
  let hT := pointIndexedCoreHomeomorph 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  let hP := pointIndexedCoreHomeomorph 𝕜 (Fin k → 𝕜) (PullbackTaut f)
  let hp := (tautologicalCore 𝕜 k).pullbackHomeomorph f
  have hmid : Continuous fun p : TotalSpace (Fin k → 𝕜)
      ((f : _ → _) *ᵖ (tautologicalCore 𝕜 k).core.Fiber) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := PullbackTaut f) p.proj (eT (f p.proj) p.2) :=
    Bundle.Pullback.continuous_iff (F := Fin k → 𝕜) (E := Tautological 𝕜 k)
      (f := (f : X → infiniteGrassmannian 𝕜 k)).2
        ⟨Pullback.continuous_proj (Fin k → 𝕜) (tautologicalCore 𝕜 k).core.Fiber f,
          (hT.continuous.comp
            (Pullback.continuous_lift (Fin k → 𝕜) (tautologicalCore 𝕜 k).core.Fiber f)).congr
              fun ⟨_, _⟩ ↦ by simp [hT, eT, Pullback.lift]⟩
  exact coreIsoOfContinuousEquiv (fun x ↦ (eT (f x)).trans (eP x).symm)
    ((hP.symm.continuous.comp (hmid.comp hp.continuous)).congr fun ⟨_, _⟩ ↦ by
      dsimp only [Function.comp_def, hP, hp]
      rw [FiniteRankBundleCore.pullbackHomeomorph_apply, pointIndexedCoreHomeomorph_symm_apply]
      rfl)

/-- Two pullbacks of `Tautological 𝕜 k` with a continuous fibrewise linear equivalence have
isomorphic `tautologicalCore` pullbacks in `FiniteRankBundleCore 𝕜 X`. -/
theorem nonempty_pullbackIso_of_pullbackEquiv [CompleteSpace 𝕜] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) p.proj (Φ p.proj p.2)) :
    Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) := by
  let φ_pair : {φ : ∀ x, PullbackTaut f₀ x →L[𝕜] PullbackTaut f₁ x //
      Continuous fun p : TotalSpace (Fin k → 𝕜) (PullbackTaut f₀) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := PullbackTaut f₁) p.proj (φ p.proj p.2)} :=
    ⟨fun x ↦ (Φ x).toContinuousLinearMap, hΦ⟩
  let hom₀ : VectorBundleCore.CoordinateHom (pointIndexedCore 𝕜 (Fin k → 𝕜) (PullbackTaut f₀))
      (pointIndexedCore 𝕜 (Fin k → 𝕜) (PullbackTaut f₁)) := pointIndexedCoreHomEquiv.symm φ_pair
  let hom : tautologicalPullbackPointCore f₀ ⟶ tautologicalPullbackPointCore f₁ := hom₀
  have hbij : ∀ x, Bijective (hom₀.fiberMap x) := fun x ↦ by
    let ψ_x := (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (PullbackTaut f₀) x).trans
      ((Φ x).trans (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (PullbackTaut f₁) x).symm)
    rw [funext (pointIndexedCoreHomEquiv_symm_fiberMap φ_pair x)]
    exact ψ_x.bijective
  have : IsIso hom := (FiniteRankBundleCore.isIso_iff_bijective hom).2 hbij
  exact ⟨(tautologicalPullbackIso f₀).trans ((asIso hom).trans (tautologicalPullbackIso f₁).symm)⟩

/-- Conversely, an isomorphism in `FiniteRankBundleCore 𝕜 X` between two pullbacks of
`tautologicalCore 𝕜 k` yields a continuous fibrewise linear equivalence between the actual pullback
bundles. -/
theorem exists_pullbackEquiv_of_pullbackIso [CompleteSpace 𝕜] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (α : (tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :
    ∃ Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x),
      Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (Φ p.proj p.2) := by
  let β : tautologicalPullbackPointCore f₀ ≅ tautologicalPullbackPointCore f₁ :=
    (tautologicalPullbackIso f₀).symm.trans (α.trans (tautologicalPullbackIso f₁))
  let β_hom : VectorBundleCore.CoordinateHom (pointIndexedCore 𝕜 (Fin k → 𝕜) (PullbackTaut f₀))
      (pointIndexedCore 𝕜 (Fin k → 𝕜) (PullbackTaut f₁)) := β.hom
  let β_inv : VectorBundleCore.CoordinateHom (pointIndexedCore 𝕜 (Fin k → 𝕜) (PullbackTaut f₁))
      (pointIndexedCore 𝕜 (Fin k → 𝕜) (PullbackTaut f₀)) := β.inv
  let g := pointIndexedCoreHomEquiv β_hom
  let g_inv := pointIndexedCoreHomEquiv β_inv
  have hleft (x : X) (v : PullbackTaut f₀ x) : g_inv.1 x (g.1 x v) = v := by
    have hid : β_inv.comp β_hom = VectorBundleCore.CoordinateHom.id _ := β.hom_inv_id
    rw [← ContinuousLinearMap.comp_apply, ← pointIndexedCoreHomEquiv_comp β_inv β_hom x, hid,
      pointIndexedCoreHomEquiv_id, ContinuousLinearMap.id_apply]
  have hright (x : X) (w : PullbackTaut f₁ x) : g.1 x (g_inv.1 x w) = w := by
    have hid : β_hom.comp β_inv = VectorBundleCore.CoordinateHom.id _ := β.inv_hom_id
    rw [← ContinuousLinearMap.comp_apply, ← pointIndexedCoreHomEquiv_comp β_hom β_inv x, hid,
      pointIndexedCoreHomEquiv_id, ContinuousLinearMap.id_apply]
  exact ⟨fun x ↦ ContinuousLinearEquiv.equivOfInverse (g.1 x) (g_inv.1 x) (hleft x) (hright x), g.2⟩

/-- Over a complete scalar field, any family of classifying coordinates `j` on `A.core.Fiber` for a
rank-`k` core `A : FiniteRankBundleCore 𝕜 X` canonically identifies the pulled-back universal core
`(tautologicalCore 𝕜 k).pullback (hj.classifyContinuousMap hk)` with `A`. -/
def tautologicalPullbackIsoOfClassifyingCoordinates [CompleteSpace 𝕜] {k : ℕ}
    {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k) {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j)
    (hk : Module.finrank 𝕜 (Fin A.rank → 𝕜) = k := (Module.finrank_fin_fun 𝕜).trans hA) :
    (tautologicalCore 𝕜 k).pullback (hj.classifyContinuousMap hk) ≅ A := by
  subst hA
  let f := hj.classifyContinuousMap hk
  let hclass := hj.classifyTautologicalHomeomorph hk
  let hP := pointIndexedCoreHomeomorph 𝕜 (Fin A.rank → 𝕜) (PullbackTaut f)
  let eP := pointIndexedCoreFiberEquiv 𝕜 (Fin A.rank → 𝕜) (PullbackTaut f)
  exact (tautologicalPullbackIso f).trans
    (coreIsoOfContinuousEquiv (A := A) (D := tautologicalPullbackPointCore f)
      (fun x ↦ (hj.classifyTautologicalEquiv hk x).trans (eP x).symm)
      ((hP.symm.continuous.comp hclass.continuous).congr fun ⟨_, _⟩ ↦ by
        dsimp only [Function.comp_def, hP, hclass]
        rw [hj.classifyTautologicalHomeomorph_apply hk, pointIndexedCoreHomeomorph_symm_apply]
        rfl)).symm

/-- Over a complete normed `ℝ`-algebra field and a paracompact normal base `X`, every object
`A : FiniteRankBundleCore 𝕜 X` of rank `k` is isomorphic to `(tautologicalCore 𝕜 k).pullback f` for
some continuous map `f : C(X, infiniteGrassmannian 𝕜 k)`. -/
theorem exists_tautologicalPullbackIso [CompleteSpace 𝕜] [NormedAlgebra ℝ 𝕜]
    [ParacompactSpace X] [NormalSpace X] {k : ℕ} (A : FiniteRankBundleCore 𝕜 X) (hA : A.rank = k) :
    ∃ f : C(X, infiniteGrassmannian 𝕜 k), Nonempty ((tautologicalCore 𝕜 k).pullback f ≅ A) :=
  let ⟨_, hj⟩ := exists_isClassifyingCoordinates (𝕜 := 𝕜) (X := X)
    (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  ⟨_, ⟨tautologicalPullbackIsoOfClassifyingCoordinates hA hj⟩⟩

end CoreComparisons

section Bijection

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X]

/-- Over `RCLike 𝕜` and a paracompact `R₁` space `X`, two continuous maps
`f₀, f₁ : C(X, infiniteGrassmannian 𝕜 k)` are homotopic if and only if the pulled-back cores
`(tautologicalCore 𝕜 k).pullback f₀` and `(tautologicalCore 𝕜 k).pullback f₁` are isomorphic in
`FiniteRankBundleCore 𝕜 X`. -/
theorem homotopic_iff_nonempty_pullbackIso [ParacompactSpace X] [R1Space X] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)} :
    f₀.Homotopic f₁ ↔
      Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :=
  homotopic_iff_exists_pullbackEquiv.trans
    ⟨fun ⟨Φ, hΦ⟩ ↦ nonempty_pullbackIso_of_pullbackEquiv Φ hΦ,
     fun ⟨α⟩ ↦ exists_pullbackEquiv_of_pullbackIso α⟩

variable (𝕜 X) in
/-- **Universal vector bundle classification (`BO(k)` / `BU(k)`).**
Over `RCLike 𝕜` and a paracompact `R₁` base `X`, pulling back `tautologicalCore 𝕜 k` induces a
bijection from homotopy classes of maps `C(X, infiniteGrassmannian 𝕜 k)` to isomorphism classes of
rank-`k` vector bundles in `FiniteRankBundleCore 𝕜 X`. -/
def classificationEquiv [ParacompactSpace X] [R1Space X] (k : ℕ) :
    Quotient ⟨ContinuousMap.Homotopic (X := X) (Y := infiniteGrassmannian 𝕜 k),
        ContinuousMap.Homotopic.equivalence⟩ ≃
      Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _)) :=
  Equiv.ofBijective
    (Quotient.map
      (sa := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
      (sb := (CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap Subtype.val)
      (fun f : C(X, infiniteGrassmannian 𝕜 k) ↦
        (⟨(tautologicalCore 𝕜 k).pullback f, rfl⟩ : {A : FiniteRankBundleCore 𝕜 X // A.rank = k}))
      fun _ _ h ↦ homotopic_iff_nonempty_pullbackIso.1 h)
    ⟨Quotient.ind₂ fun _ _ h ↦
        Quotient.sound (homotopic_iff_nonempty_pullbackIso.2 (Quotient.exact h)),
     Quotient.ind fun A ↦
        let ⟨f, hf⟩ := exists_tautologicalPullbackIso A.1 A.2; ⟨Quotient.mk _ f, Quotient.sound hf⟩⟩

@[simp] theorem classificationEquiv_mk [ParacompactSpace X] [R1Space X] (k : ℕ)
    (f : C(X, infiniteGrassmannian 𝕜 k)) :
    classificationEquiv 𝕜 X k (Quotient.mk _ f) =
      Quotient.mk _ ⟨(tautologicalCore 𝕜 k).pullback f, rfl⟩ := (rfl)

/-- Inverse characterization of `classificationEquiv`: the inverse sends the isomorphism class of a
rank-`k` bundle core `A` to the homotopy class of the classifying map associated to any classifying
coordinates `j` on `A.core.Fiber`. -/
theorem classificationEquiv_symm_mk_of_isClassifyingCoordinates [ParacompactSpace X] [R1Space X]
    {k : ℕ} (A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k})
    {j : ∀ x, A.1.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.1.rank → 𝕜) A.1.core.Fiber j)
    (hk : Module.finrank 𝕜 (Fin A.1.rank → 𝕜) = k := (Module.finrank_fin_fun 𝕜).trans A.2) :
    (classificationEquiv 𝕜 X k).symm (Quotient.mk _ A) =
      Quotient.mk _ (hj.classifyContinuousMap hk) :=
  (classificationEquiv 𝕜 X k).injective <| by
    rw [Equiv.apply_symm_apply, classificationEquiv_mk]
    exact Quotient.sound ⟨(tautologicalPullbackIsoOfClassifyingCoordinates A.2 hj hk).symm⟩

/-- Pullback of isomorphism classes of rank-`k` vector-bundle cores along a continuous map
`g : C(X', X)`. -/
def pullbackRankClass {X' : Type*} [TopologicalSpace X'] (g : C(X', X)) (k : ℕ) :
    Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _)) →
      Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X')).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X' // A.rank = k} → _)) :=
  Quotient.map
    (fun A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} ↦
      (⟨A.1.pullback g, A.2⟩ : {A : FiniteRankBundleCore 𝕜 X' // A.rank = k}))
    fun _ _ ⟨α⟩ ↦ ⟨(FiniteRankBundleCore.pullbackFunctor g).mapIso α⟩

@[simp] theorem pullbackRankClass_mk {X' : Type*} [TopologicalSpace X'] (g : C(X', X)) (k : ℕ)
    (A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k}) :
    pullbackRankClass g k (Quotient.mk _ A) = Quotient.mk _ ⟨A.1.pullback g, A.2⟩ := (rfl)

/-- Naturality of `classificationEquiv`: precomposing a classifying map with `g : C(X', X)`
corresponds to pulling back the classified rank-`k` bundle core along `g`. -/
theorem classificationEquiv_comp {X' : Type*} [TopologicalSpace X']
    [ParacompactSpace X] [R1Space X] [ParacompactSpace X'] [R1Space X']
    (g : C(X', X)) (k : ℕ) (f : C(X, infiniteGrassmannian 𝕜 k)) :
    classificationEquiv 𝕜 X' k (Quotient.mk _ (f.comp g)) =
      pullbackRankClass g k (classificationEquiv 𝕜 X k (Quotient.mk _ f)) := (rfl)

/-- Contravariant naturality of `(classificationEquiv 𝕜 X k).symm`: pulling back a rank-`k` bundle
class along `g : C(X', X)` corresponds to precomposing its classifying homotopy class with `g`. -/
theorem classificationEquiv_symm_pullbackRankClass {X' : Type*} [TopologicalSpace X']
    [ParacompactSpace X] [R1Space X] [ParacompactSpace X'] [R1Space X'] (g : C(X', X)) (k : ℕ)
    (c : Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
      (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _))) :
    (classificationEquiv 𝕜 X' k).symm (pullbackRankClass g k c) =
      Quotient.map (sa := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
        (sb := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
        (fun f : C(X, infiniteGrassmannian 𝕜 k) ↦ f.comp g) (fun _ _ h ↦ h.comp (.refl g))
        ((classificationEquiv 𝕜 X k).symm c) := by
  rcases (classificationEquiv 𝕜 X k).surjective c with ⟨q, rfl⟩
  refine Quotient.inductionOn q fun f ↦ ?_
  rw [← classificationEquiv_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply]; rfl

end Bijection

end infiniteGrassmannian

end SmallClassification

end TauCeti
