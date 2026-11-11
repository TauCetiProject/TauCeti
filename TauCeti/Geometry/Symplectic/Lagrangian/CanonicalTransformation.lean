/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Graph
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Lagrangian relations with diffeomorphic projections

Let `σ` and `τ` be nondegenerate two-forms on `M` and `N`. A relation between `M` and `N`
parametrized by a manifold `L` is a pair of maps `a : L → M` and `b : L → N`, that is the map
`x ↦ (a x, b x)` into `M × N`; it is Lagrangian when this map is Lagrangian for the twisted
product `pr₁*σ - pr₂*τ`. This file shows that such a relation is the graph of a canonical
transformation wherever its projections `a` and `b` are diffeomorphisms.

* The relation is isotropic exactly when `a^* σ = b^* τ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_prodMk_iff`). This needs no hypothesis on
  the projections.
* When the differentials of `a` and `b` are invertible at every point, its tangent images are
  graphs of linear isomorphisms, so it is Lagrangian exactly when it is isotropic
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_prodMk_iff`). For finite-dimensional
  `M` and `N` of the same dimension, invertibility of the differentials of `a` suffices: along an
  isotropic relation, the differential of `b` is then invertible as well
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isInvertible_mfderiv_of_isIsotropic`), and so `b` is a
  local diffeomorphism wherever `a` is, at interior points near which `b` is smooth
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isLocalDiffeomorphAt_of_isIsotropic`).
* When `a` and `b` are diffeomorphisms, the relation is the graph of `φ = b ∘ a⁻¹`, and it is
  Lagrangian exactly when `φ^* τ = σ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_prodMk_diffeomorph_iff`).
* When `a` and `b` are only local diffeomorphisms at a point `x`, an isotropic (for instance
  Lagrangian) relation is near `x` the graph of a partial diffeomorphism `Φ` between open subsets
  of `M` and `N` with `Φ^* τ = σ` on its source
  (`TauCeti.SmoothTwoForm.IsNondegenerate.IsIsotropicMap.exists_partialDiffeomorph`). This is a
  statement about one branch near one point; no global canonical transformation is asserted.

These are the statements by which Lagrangian correspondences with diffeomorphic projections, such
as those cut out by generating functions with nondegenerate mixed Hessian, become (local)
symplectomorphisms.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 3 and 4.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.4.
-/

public section

noncomputable section

open Filter Module
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F G N EL HL L : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [NormedAddCommGroup EL] [NormedSpace ℝ EL] [TopologicalSpace HL]
  {K : ModelWithCorners ℝ EL HL} [TopologicalSpace L] [ChartedSpace HL L]
  {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N} {a : L → M} {b : L → N}

/-! ### Pointwise criteria -/

section Pointwise

variable (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) {x : L}

/-- The tangent image of `y ↦ (a y, b y)` at `x` is isotropic for the twisted product exactly when
`σ(da v, da w) = τ(db v, db w)` for all tangent vectors `v` and `w` at `x`. -/
theorem isIsotropic_range_mfderiv_prodMk_iff (ha : MDifferentiableAt K I a x)
    (hb : MDifferentiableAt K J b x) :
    ((hσ.twistedProd hτ).symplecticFormAt (a x, b x)).IsIsotropic
        (LinearMap.range (mfderiv K (I.prod J) (fun y ↦ (a y, b y)) x).toLinearMap) ↔
      ∀ v w : TangentSpace K x,
        SmoothBundleForm.eval₂ σ (a x) (mfderiv K I a x v) (mfderiv K I a x w) =
          SmoothBundleForm.eval₂ τ (b x) (mfderiv K J b x v) (mfderiv K J b x w) := by
  have hf : MDifferentiableAt K (I.prod J) (fun y ↦ (a y, b y)) x := ha.prodMk hb
  have h₁ (v : TangentSpace K x) : (Manifold.tangentSpaceProdEquiv (a x, b x)
      (mfderiv K (I.prod J) (fun y ↦ (a y, b y)) x v)).1 = mfderiv K I a x v :=
    (congrArg Prod.fst (Manifold.tangentSpaceProdEquiv_apply _ _)).trans
      (hf.mfderiv_fst_apply v).symm
  have h₂ (v : TangentSpace K x) : (Manifold.tangentSpaceProdEquiv (a x, b x)
      (mfderiv K (I.prod J) (fun y ↦ (a y, b y)) x v)).2 = mfderiv K J b x v :=
    (congrArg Prod.snd (Manifold.tangentSpaceProdEquiv_apply _ _)).trans
      (hf.mfderiv_snd_apply v).symm
  simp only [SymplecticForm.isIsotropic_iff, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, symplecticFormAt_apply, ContinuousLinearMap.coe_coe,
    eval₂_twistedProd, h₁, h₂, sub_eq_zero]

/-- **Pointwise canonical relations.** Where the differentials of `a` and `b` are invertible, the
tangent image of `y ↦ (a y, b y)` is Lagrangian for the twisted product exactly when
`σ(da v, da w) = τ(db v, db w)` for all tangent vectors `v` and `w`. It is then the graph of the
linear symplectomorphism `db ∘ da⁻¹`. -/
theorem isLagrangian_range_mfderiv_prodMk_iff (ha : MDifferentiableAt K I a x)
    (hb : MDifferentiableAt K J b x) (ha' : (mfderiv K I a x).IsInvertible)
    (hb' : (mfderiv K J b x).IsInvertible) :
    ((hσ.twistedProd hτ).symplecticFormAt (a x, b x)).IsLagrangian
        (LinearMap.range (mfderiv K (I.prod J) (fun y ↦ (a y, b y)) x).toLinearMap) ↔
      ∀ v w : TangentSpace K x,
        SmoothBundleForm.eval₂ σ (a x) (mfderiv K I a x v) (mfderiv K I a x w) =
          SmoothBundleForm.eval₂ τ (b x) (mfderiv K J b x v) (mfderiv K J b x w) := by
  refine ⟨fun h ↦ (isIsotropic_range_mfderiv_prodMk_iff hσ hτ ha hb).mp h.isIsotropic,
    fun h ↦ ?_⟩
  obtain ⟨ea, hea⟩ := ha'
  obtain ⟨eb, heb⟩ := hb'
  -- In the product of the tangent spaces, the tangent image is the graph of `db ∘ da⁻¹`.
  have hrange : (LinearMap.range (mfderiv K (I.prod J) (fun y ↦ (a y, b y)) x).toLinearMap).map
      (Manifold.tangentSpaceProdEquiv (a x, b x)).toLinearEquiv.toLinearMap =
      (ea.symm.trans eb).toLinearEquiv.toLinearMap.graph := by
    rw [Manifold.map_range_mfderiv_prodMk ha hb, LinearMap.graph_eq_range_prod]
    have hcomp : (mfderiv K I a x).toLinearMap.prod (mfderiv K J b x).toLinearMap =
        (LinearMap.id.prod (ea.symm.trans eb).toLinearEquiv.toLinearMap) ∘ₗ
          ea.toLinearEquiv.toLinearMap := by
      ext v <;> simp [← hea, ← heb]
    rw [hcomp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  rw [← SymplecticForm.isLagrangian_map_transport_iff
      (e := (Manifold.tangentSpaceProdEquiv (a x, b x)).toLinearEquiv),
    symplecticFormAt_twistedProd hσ hτ, hrange, SymplecticForm.isLagrangian_graph_iff,
    SymplecticForm.isSymplectomorphism_iff]
  intro u u'
  obtain ⟨v, rfl⟩ := ea.surjective u
  obtain ⟨w, rfl⟩ := ea.surjective u'
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply, symplecticFormAt_apply]
  rw [← ContinuousLinearEquiv.coe_coe ea, ← ContinuousLinearEquiv.coe_coe eb, hea, heb]
  exact (h v w).symm

/-- In equal finite dimensions, where the tangent image of `y ↦ (a y, b y)` is isotropic for the
twisted product (for instance Lagrangian), the differential of `b` is invertible wherever that of
`a` is: the tangent image is the graph of a linear map preserving the nondegenerate forms, which
is injective, hence bijective. -/
theorem isInvertible_mfderiv_of_isIsotropic [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hEF : finrank ℝ E = finrank ℝ F) (ha : MDifferentiableAt K I a x)
    (hb : MDifferentiableAt K J b x)
    (h : ((hσ.twistedProd hτ).symplecticFormAt (a x, b x)).IsIsotropic
      (LinearMap.range (mfderiv K (I.prod J) (fun y ↦ (a y, b y)) x).toLinearMap))
    (ha' : (mfderiv K I a x).IsInvertible) : (mfderiv K J b x).IsInvertible := by
  obtain ⟨ea, hea⟩ := ha'
  have hiso := (isIsotropic_range_mfderiv_prodMk_iff hσ hτ ha hb).mp h
  have : FiniteDimensional ℝ (TangentSpace K x) := ea.symm.toLinearEquiv.finiteDimensional
  -- If `db v = 0`, then `σ(da v, da w) = 0` for every `w`, and `da` is onto, so `da v = 0`.
  have hinj : Function.Injective (mfderiv K J b x) := by
    refine (injective_iff_map_eq_zero (mfderiv K J b x)).2 fun v hv ↦ ?_
    apply ea.injective
    rw [map_zero]
    refine (isNondegenerate_iff_separatingLeft.1 hσ (a x) (ea v) fun u ↦ ?_)
    obtain ⟨w, rfl⟩ := ea.surjective u
    rw [← ContinuousLinearEquiv.coe_coe ea, hea, hiso v w, ← symplecticFormAt_apply hτ, hv]
    exact LinearMap.map_zero₂ _ _
  have : FiniteDimensional ℝ (TangentSpace J (b x)) := inferInstanceAs (FiniteDimensional ℝ F)
  have hdim : finrank ℝ (TangentSpace K x) = finrank ℝ (TangentSpace J (b x)) :=
    ea.toLinearEquiv.finrank_eq.trans hEF
  -- `TangentSpace K x` is definitionally the model space `EL` (and `TangentSpace J (b x)` is `F`),
  -- so the helper is applied at the model spaces, where `FiniteDimensional ℝ EL` is needed.
  have : FiniteDimensional ℝ EL := inferInstanceAs (FiniteDimensional ℝ (TangentSpace K x))
  exact ContinuousLinearMap.isInvertible_of_injective_of_finrank_eq (U := EL) (G := F)
    (mfderiv K J b x) hdim hinj

/-- **Isotropic relations project to local diffeomorphisms together.** In equal finite
dimensions, if the tangent image of `y ↦ (a y, b y)` at an interior point `x` is isotropic for the
twisted product (for instance Lagrangian), `a` is a local diffeomorphism at `x` and `b` is smooth
on an open neighbourhood of `x`, then `b` is a local diffeomorphism at `x` too. -/
theorem isLocalDiffeomorphAt_of_isIsotropic [IsManifold K ∞ L] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (hEF : finrank ℝ E = finrank ℝ F)
    (h : ((hσ.twistedProd hτ).symplecticFormAt (a x, b x)).IsIsotropic
      (LinearMap.range (mfderiv K (I.prod J) (fun y ↦ (a y, b y)) x).toLinearMap))
    (ha : IsLocalDiffeomorphAt K I ∞ a x) {s : Set L} (hb : ContMDiffOn K J ∞ b s)
    (hs : IsOpen s) (hxs : x ∈ s) (hx : K.IsInteriorPoint x) :
    IsLocalDiffeomorphAt K J ∞ b x := by
  obtain ⟨ea, hea⟩ := ha.isInvertible_mfderiv (by simp)
  have : FiniteDimensional ℝ EL := ea.symm.toLinearEquiv.finiteDimensional
  have : CompleteSpace EL := FiniteDimensional.complete ℝ EL
  obtain ⟨eb, heb⟩ := isInvertible_mfderiv_of_isIsotropic hσ hτ hEF
    (ha.mdifferentiableAt (by simp))
    ((hb.contMDiffAt (hs.mem_nhds hxs)).mdifferentiableAt (by simp)) h ⟨ea, hea⟩
  exact isLocalDiffeomorphAt_of_mfderiv_eq hb hs hxs hx (by simp) heb

end Pointwise

/-! ### Global criteria -/

section Global

variable [IsManifold K ∞ L] (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate)

/-- **Isotropic relations.** The relation `x ↦ (a x, b x)` is isotropic for the twisted product
`pr₁*σ - pr₂*τ` exactly when `a^* σ = b^* τ`. -/
theorem isIsotropicMap_prodMk_iff (ha : ContMDiff K I ∞ a) (hb : ContMDiff K J ∞ b) :
    (hσ.twistedProd hτ).IsIsotropicMap K (fun x ↦ (a x, b x)) ↔
      SmoothForm.mpullback a ha σ = SmoothForm.mpullback b hb τ := by
  rw [isIsotropicMap_iff_forall, SmoothBundleForm.ext_eval₂_iff]
  refine forall_congr' fun x ↦ ?_
  simp only [isIsotropic_range_mfderiv_prodMk_iff hσ hτ (ha.mdifferentiableAt (by simp))
    (hb.mdifferentiableAt (by simp)), SmoothForm.eval₂_mpullback]

/-- **Lagrangian relations with invertible differentials.** If the differentials of `a` and `b`
are invertible everywhere, the relation `x ↦ (a x, b x)` is Lagrangian for the twisted product
`pr₁*σ - pr₂*τ` exactly when `a^* σ = b^* τ`. -/
theorem isLagrangianMap_prodMk_iff (ha : ContMDiff K I ∞ a) (hb : ContMDiff K J ∞ b)
    (ha' : ∀ x, (mfderiv K I a x).IsInvertible) (hb' : ∀ x, (mfderiv K J b x).IsInvertible) :
    (hσ.twistedProd hτ).IsLagrangianMap K (fun x ↦ (a x, b x)) ↔
      SmoothForm.mpullback a ha σ = SmoothForm.mpullback b hb τ := by
  rw [isLagrangianMap_iff_forall, SmoothBundleForm.ext_eval₂_iff]
  refine forall_congr' fun x ↦ ?_
  simp only [isLagrangian_range_mfderiv_prodMk_iff hσ hτ (ha.mdifferentiableAt (by simp))
    (hb.mdifferentiableAt (by simp)) (ha' x) (hb' x), SmoothForm.eval₂_mpullback]

/-- **Lagrangian relations in equal finite dimensions.** If `M` and `N` are finite-dimensional of
the same dimension and the differential of `a` is invertible everywhere, the relation
`x ↦ (a x, b x)` is Lagrangian for the twisted product exactly when `a^* σ = b^* τ`. -/
theorem isLagrangianMap_prodMk_iff_of_finrank_eq [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hEF : finrank ℝ E = finrank ℝ F) (ha : ContMDiff K I ∞ a) (hb : ContMDiff K J ∞ b)
    (ha' : ∀ x, (mfderiv K I a x).IsInvertible) :
    (hσ.twistedProd hτ).IsLagrangianMap K (fun x ↦ (a x, b x)) ↔
      SmoothForm.mpullback a ha σ = SmoothForm.mpullback b hb τ := by
  refine ⟨fun h ↦ (isIsotropicMap_prodMk_iff hσ hτ ha hb).mp h.isIsotropicMap, fun h ↦ ?_⟩
  have hiso := (isIsotropicMap_prodMk_iff hσ hτ ha hb).mpr h
  refine (isLagrangianMap_prodMk_iff hσ hτ ha hb ha' fun x ↦ ?_).mpr h
  exact isInvertible_mfderiv_of_isIsotropic hσ hτ hEF (ha.mdifferentiableAt (by simp))
    (hb.mdifferentiableAt (by simp)) (isIsotropicMap_iff_forall.mp hiso x) (ha' x)

end Global

/-! ### Diffeomorphic projections -/

section Diffeomorph

variable (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate)

/-- **Canonical transformations from Lagrangian relations.** If both projections of the relation
`x ↦ (a x, b x)` are diffeomorphisms, it is the graph of `φ = b ∘ a⁻¹`, and it is Lagrangian for
the twisted product `pr₁*σ - pr₂*τ` exactly when `φ^* τ = σ`. -/
@[simp]
theorem isLagrangianMap_prodMk_diffeomorph_iff (e₁ : L ≃ₘ⟮K, I⟯ M) (e₂ : L ≃ₘ⟮K, J⟯ N) :
    (hσ.twistedProd hτ).IsLagrangianMap K (fun x ↦ (e₁ x, e₂ x)) ↔
      SmoothForm.mpullback (e₁.symm.trans e₂) (e₁.symm.trans e₂).contMDiff τ = σ := by
  have hf : (fun x ↦ (e₁ x, e₂ x)) = (fun p ↦ (p, e₁.symm.trans e₂ p)) ∘ e₁ := by
    funext x
    simp
  rw [hf, isLagrangianMap_comp_diffeomorph_iff e₁ (by simp),
    isLagrangianMap_graph_iff hσ hτ]

end Diffeomorph

/-! ### Local diffeomorphic projections -/

section Local

variable (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate)

/-- **Local canonical transformations from Lagrangian relations.** If both projections of an
isotropic (for instance Lagrangian) relation `x ↦ (a x, b x)` are local diffeomorphisms at `x`,
then near `x` the relation is the graph of a partial diffeomorphism `Φ` from an open neighbourhood
of `a x` in `M` onto an open subset of `N` which pulls `τ` back to `σ` at every point of its
source. -/
theorem IsIsotropicMap.exists_partialDiffeomorph
    (h : (hσ.twistedProd hτ).IsIsotropicMap K (fun x ↦ (a x, b x))) {x : L}
    (ha : IsLocalDiffeomorphAt K I ∞ a x) (hb : IsLocalDiffeomorphAt K J ∞ b x) :
    ∃ Φ : PartialDiffeomorph I J M N ∞, a x ∈ Φ.source ∧ (∀ᶠ y in 𝓝 x, Φ (a y) = b y) ∧
      ∀ p ∈ Φ.source, ∀ v w : TangentSpace I p,
        SmoothBundleForm.eval₂ τ (Φ p) (mfderiv I J Φ p v) (mfderiv I J Φ p w) =
          SmoothBundleForm.eval₂ σ p v w := by
  obtain ⟨Φa, hxa, hΦa⟩ := ha
  obtain ⟨Φb, hxb, hΦb⟩ := hb
  -- On `U = Φa.source ∩ Φb.source` the projections are `Φa` and `Φb`, and `Φ = Φb ∘ Φa⁻¹`.
  set U := Φa.source ∩ Φb.source with hU_def
  have hU : IsOpen U := Φa.open_source.inter Φb.open_source
  have hcoe (p : M) : Φa.symm.trans Φb p = Φb (Φa.symm p) := rfl
  have hleft {z : L} (hz : z ∈ Φa.source) : Φa.symm (Φa z) = z := Φa.left_inv hz
  have hmem {p : M} :
      p ∈ (Φa.symm.trans Φb).source ↔ p ∈ Φa.target ∧ Φa.symm p ∈ Φb.source :=
    Iff.rfl
  refine ⟨Φa.symm.trans Φb, ?_, ?_, ?_⟩
  · rw [hΦa hxa, hmem, hleft hxa]
    exact ⟨Φa.map_source hxa, hxb⟩
  · filter_upwards [hU.mem_nhds ⟨hxa, hxb⟩] with y hy
    rw [hcoe, hΦa hy.1, hleft hy.1, hΦb hy.2]
  · intro p hp v w
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ U, Φa y = p :=
      ⟨Φa.symm p, ⟨Φa.map_target (hmem.mp hp).1, (hmem.mp hp).2⟩, Φa.right_inv (hmem.mp hp).1⟩
    have hUy : U ∈ 𝓝 y := hU.mem_nhds hy
    have haΦ : a =ᶠ[𝓝 y] Φa := eventuallyEq_of_mem hUy fun z hz ↦ hΦa hz.1
    have hbΦ : b =ᶠ[𝓝 y] Φb := eventuallyEq_of_mem hUy fun z hz ↦ hΦb hz.2
    have hΦΦa : (Φa.symm.trans Φb ∘ Φa) =ᶠ[𝓝 y] Φb :=
      eventuallyEq_of_mem hUy fun z hz ↦ by rw [Function.comp_apply, hcoe, hleft hz.1]
    have hΦa' : MDifferentiableAt K I Φa y := Φa.mdifferentiableAt (by simp) hy.1
    have hΦb' : MDifferentiableAt K J Φb y := Φb.mdifferentiableAt (by simp) hy.2
    -- The pointwise isotropy of the relation at `y`, read through `Φa` and `Φb`.
    have hiso := (isIsotropic_range_mfderiv_prodMk_iff hσ hτ
      (hΦa'.congr_of_eventuallyEq haΦ) (hΦb'.congr_of_eventuallyEq hbΦ)).mp
      (isIsotropicMap_iff_forall.mp h y)
    rw [haΦ.mfderiv_eq, hbΦ.mfderiv_eq, hΦa hy.1, hΦb hy.2] at hiso
    obtain ⟨ea, hea⟩ := (Φa.isLocalDiffeomorphAt _ _ _ hy.1).isInvertible_mfderiv (by simp)
    obtain ⟨u, rfl⟩ := ea.surjective v
    obtain ⟨u', rfl⟩ := ea.surjective w
    rw [← ContinuousLinearEquiv.coe_coe ea, hea,
      ← mfderiv_comp_apply y ((Φa.symm.trans Φb).mdifferentiableAt (by simp) hp) hΦa',
      ← mfderiv_comp_apply y ((Φa.symm.trans Φb).mdifferentiableAt (by simp) hp) hΦa',
      hΦΦa.mfderiv_eq, hcoe, hleft hy.1]
    exact (hiso u u').symm

end Local

end TauCeti.SmoothTwoForm.IsNondegenerate
