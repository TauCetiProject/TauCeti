/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Lattice
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.CoordinateCover

/-!
# The section map of a regular Lagrangian torus fibration

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
onto a boundaryless Hausdorff manifold `B` of dimension `n`. Every cotangent space `T*_b B` acts on
the fibre `π⁻¹(b)` (`IsLagrangianTorusFibration.fiberAction`): a covector `dg_b` acts by the
time-one map of the Hamiltonian flow of `g ∘ π`. Given a section `s` of `π`, this file studies the
**section map**

`Φ_s : T*B → M`, `Φ_s(ξ) = (-ξ) • s(b)` for a covector `ξ` at `b`

(`IsLagrangianTorusFibration.sectionMap`). It lies over `B`, sends the zero section to `s`, is
equivariant for the actions of the cotangent spaces, and is onto. Its fibre over `b` is a coset
space of the period lattice `Λ_b`: two covectors at `b` have the same image exactly when they
differ by an element of `Λ_b` (`IsLagrangianTorusFibration.sectionMap_mk_eq_sectionMap_mk_iff`).

For a smooth section `s`, the section map is a smooth local diffeomorphism
(`IsLagrangianTorusFibration.isLocalDiffeomorph_sectionMap`), and it pulls `σ` back to

`Φ_s^* σ = ω + π^* (s^* σ)`

(`IsLagrangianTorusFibration.mpullback_sectionMap`), where `ω = -dλ` is the canonical symplectic
form of `T*B` and `π : T*B → B` is the bundle projection. The sign in `(-ξ) • s(b)` is the one for
which the canonical form appears with a plus sign. In particular, if `s` is a Lagrangian section,
`s^* σ = 0`, then `Φ_s` is a symplectic local diffeomorphism from `(T*B, ω)` onto `M`
(`IsLagrangianTorusFibration.mpullback_sectionMap_eq_symplecticForm`). Together with the
description of its fibres, this says that `Φ_s` induces a bijective symplectic local
diffeomorphism from `T*B / Λ` onto `M`, which is how Duistermaat identifies a regular Lagrangian
torus fibration with a Lagrangian section with its period torus bundle. The quotient `T*B / Λ` of
an arbitrary period lattice is not constructed here.

## Implementation notes

The statements are proved in coordinates `κ : B → ℝⁿ` around a point of the base. On the covers
`(c, x) ↦ ∑ j, c_j dκ_j` of `T*B` (`TauCeti.CotangentBundle.coordinateCover`) and
`(c, x) ↦ (-c) • s x` of `M`, the second being the Hamiltonian flow action of `κ ∘ π`
(`IsLagrangianTorusFibration.hamiltonianFlowActionComp`), the section map is the second cover read
through the first. The pullback of `σ` along the second cover is computed by
`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_hamiltonianFlowAction_comp`, and the pullback of
`ω` along the first cover is `∑ j, dκ_j ∧ dc_j`
(`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_coordinateCover`).

## Main definitions

* `IsLagrangianTorusFibration.sectionMap`: the section map `Φ_s : T*B → M`.

## Main results

* `IsLagrangianTorusFibration.proj_sectionMap`, `IsLagrangianTorusFibration.sectionMap_mk_zero`,
  `IsLagrangianTorusFibration.sectionMap_mk_add`: `Φ_s` lies over `B`, extends `s` and is
  equivariant.
* `IsLagrangianTorusFibration.sectionMap_mk_eq_sectionMap_mk_iff`,
  `IsLagrangianTorusFibration.surjective_sectionMap`: the fibres of `Φ_s` are the cosets of the
  period lattice, and `Φ_s` is onto.
* `IsLagrangianTorusFibration.isLocalDiffeomorph_sectionMap`,
  `IsLagrangianTorusFibration.contMDiff_sectionMap`: for a smooth section, `Φ_s` is a smooth local
  diffeomorphism.
* `IsLagrangianTorusFibration.eval₂_mfderiv_sectionMap`,
  `IsLagrangianTorusFibration.mpullback_sectionMap`: `Φ_s^* σ = ω + π^* (s^* σ)`.
* `IsLagrangianTorusFibration.mpullback_sectionMap_eq_symplecticForm`: for a Lagrangian section,
  `Φ_s^* σ = ω`.

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Sections 1 and 2 (the action of `T*B` on the fibres, and the symplectic
  identification of a fibration with a Lagrangian section with `T*B / Λ`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
-/

public section

noncomputable section

open Bundle (TotalSpace)
open Function Set Module
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

variable (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed) {s : B → M}
  (hs : ∀ b, π (s b) = b)

/-! ### The section map -/

/-- **The section map** `Φ_s : T*B → M` of a section `s` of the fibration: a covector `ξ` at `b`
goes to the point `(-ξ) • s(b)` of the fibre over `b`, for the action of `T*_b B` on that fibre
(`fiberAction`). With this sign it pulls `σ` back to `ω + π^* (s^* σ)` for the canonical form
`ω = -dλ` of `T*B` (`mpullback_sectionMap`). -/
def sectionMap (ξ : CotangentBundle J B) : M :=
  h.fiberAction hσc ξ.proj (-ξ.snd) ⟨s ξ.proj, hs ξ.proj⟩

/-- The section map at a covector `α` at `b` is the action of `-α` on `s b`. -/
theorem sectionMap_mk (b : B) (α : F →L[ℝ] ℝ) :
    h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b α) =
      (h.fiberAction hσc b (-α) ⟨s b, hs b⟩ : M) :=
  (rfl)

/-- **The section map lies over the base**: `π (Φ_s ξ)` is the base point of `ξ`. -/
theorem proj_sectionMap (ξ : CotangentBundle J B) : π (h.sectionMap hσc hs ξ) = ξ.proj :=
  (h.fiberAction hσc ξ.proj (-ξ.snd) ⟨s ξ.proj, hs ξ.proj⟩).property

/-- **The section map lies over the base**: `π ∘ Φ_s` is the bundle projection of `T*B`. -/
@[simp]
theorem proj_comp_sectionMap : π ∘ h.sectionMap hσc hs = TotalSpace.proj :=
  funext (h.proj_sectionMap hσc hs)

/-- **The section map sends the zero section to the section `s`.** -/
@[simp]
theorem sectionMap_mk_zero (b : B) :
    h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b 0) = s b :=
  -- The covector of `TotalSpace.mk' _ b α` is `α`, read in `F →L[ℝ] ℝ`.
  congrArg Subtype.val ((congrArg (h.fiberAction hσc b · ⟨s b, hs b⟩)
    (neg_zero : -(0 : F →L[ℝ] ℝ) = 0)).trans (h.fiberAction_zero hσc b _))

/-- **The section map is equivariant**: adding `α` to a covector at `b` moves its image by the
action of `-α`. -/
theorem sectionMap_mk_add (b : B) (α β : F →L[ℝ] ℝ) :
    h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b (α + β)) =
      (h.fiberAction hσc b (-α)
        ⟨h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b β), h.proj_sectionMap hσc hs _⟩ : M) :=
  congrArg Subtype.val ((congrArg (h.fiberAction hσc b · ⟨s b, hs b⟩) (neg_add α β)).trans
    (h.fiberAction_add hσc b _ _ _))

/-- **The fibres of the section map are the cosets of the period lattice**: two covectors at `b`
have the same image exactly when they differ by an element of `Λ_b`. -/
theorem sectionMap_mk_eq_sectionMap_mk_iff (b : B) (α β : F →L[ℝ] ℝ) :
    h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b α) =
        h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b β) ↔
      α - β ∈ h.periodLattice hσc b :=
  Subtype.ext_iff.symm.trans ((h.fiberAction_eq_fiberAction_iff hσc b _).trans
    (Iff.of_eq (congrArg (· ∈ h.periodLattice hσc b)
      (by rw [neg_neg, ← sub_eq_add_neg] : - -α + -β = α - β))))

/-- **The section map is surjective.** -/
theorem surjective_sectionMap : Surjective (h.sectionMap hσc hs) := fun y ↦ by
  obtain ⟨α, hα⟩ := h.exists_fiberAction_eq hσc (π y) ⟨s (π y), hs (π y)⟩ ⟨y, rfl⟩
  refine ⟨TotalSpace.mk' (F →L[ℝ] ℝ) (π y) (-α), ?_⟩
  exact congrArg Subtype.val ((congrArg (h.fiberAction hσc (π y) · _) (neg_neg α)).trans hα)

/-! ### The section map in coordinates -/

section Coordinates

open CotangentBundle (coordinateCover coordinateCover_snd_apply contMDiff_coordinateCover
  eval₂_symplecticForm_mfderiv_coordinateCover isLocalDiffeomorphAt_coordinateCover)

variable {ι : Type*} [Fintype ι] {κ : B → ι → ℝ} (hκ : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ κ)

/-- **The section map on `∑ j, c_j dκ_j`** is the action of `-c` on `s x` for the Hamiltonian
flow action of `κ ∘ π`. -/
private theorem sectionMap_coordinateCover (q : (ι → ℝ) × B) :
    h.sectionMap hσc hs (coordinateCover J κ q) =
      h.hamiltonianFlowActionComp hσc hκ (-q.1) (s q.2) := by
  classical
  -- The covector `-∑ j, c_j dκ_j` is the differential of `g = (-c) ⬝ᵥ κ`.
  let L : (ι → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductEquiv ℝ ι (-q.1))
  have hg : ContMDiff J 𝓘(ℝ) 2 (L ∘ κ) := (L.contMDiff.comp hκ).of_le (by simp)
  have hgd : mvfderiv J (L ∘ κ) (coordinateCover J κ q).proj = -(coordinateCover J κ q).snd := by
    rw [CotangentBundle.proj_coordinateCover]
    ext u
    rw [L.mvfderiv_comp_apply ((hκ _).mdifferentiableAt (by simp)),
      mvfderiv_apply_eq_mfderiv_apply]
    refine Eq.trans ?_ (neg_apply (coordinateCover J κ q).snd u).symm
    refine Eq.trans ?_ (congrArg Neg.neg
      (coordinateCover_snd_apply ((hκ _).mdifferentiableAt (by simp)) u).symm)
    simp only [L, LinearMap.coe_toContinuousLinearMap']
    exact neg_dotProduct _ _
  have hfun : (L ∘ κ) ∘ π = fun y ↦ -q.1 ⬝ᵥ (κ ∘ π) y :=
    funext fun y ↦ by simp [L, dotProductEquiv]
  rw [sectionMap, h.coe_fiberAction_eq_flowOf hσc (coordinateCover J κ q).proj hg hgd, hfun,
    h.hamiltonianFlowActionComp_apply]
  -- The point `⟨s x, hs x⟩` of the fibre over `(coordinateCover J κ q).proj = x` is `s x`.
  exact congrArg (fun b ↦ flowOf _ 1 (s b)) (CotangentBundle.proj_coordinateCover J κ q)

variable (s) in
/-- The point `(-c) • s x` of the Hamiltonian flow action of `κ ∘ π`, as a function of
`(c, x)`. -/
private def coverSection (q : (ι → ℝ) × B) : M :=
  h.hamiltonianFlowActionComp hσc hκ (-q.1) (s q.2)

omit [FiniteDimensional ℝ F] [T2Space B] in
include hs in
/-- **The pullback along `(c, x) ↦ (-c) • s x`.** It pulls `σ` back to `s^* σ` plus the form
`(w, u), (w', u') ↦ w' ⬝ᵥ dκ u - w ⬝ᵥ dκ u'`. -/
private theorem eval₂_mfderiv_coverSection (hsm : ContMDiff J I ∞ s) (q : (ι → ℝ) × B)
    (v v' : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
    SmoothBundleForm.eval₂ σ (h.coverSection hσc s hκ q)
        (mfderiv (𝓘(ℝ, ι → ℝ).prod J) I (h.coverSection hσc s hκ) q v)
        (mfderiv (𝓘(ℝ, ι → ℝ).prod J) I (h.coverSection hσc s hκ) q v') =
      SmoothBundleForm.eval₂ σ (s q.2) (mfderiv J I s q.2 v.2) (mfderiv J I s q.2 v'.2) +
        (v'.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v.2 - v.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v'.2) := by
  -- The derivatives of `(c, x) ↦ -c`, `(c, x) ↦ s x` and `(c, x) ↦ κ (π (s x)) = κ x`.
  have hneg : HasMFDerivAt (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, ι → ℝ) (fun q : (ι → ℝ) × B ↦ -q.1) q
      ((-ContinuousLinearMap.id ℝ (ι → ℝ)).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) F)) :=
    ((-ContinuousLinearMap.id ℝ (ι → ℝ)).hasMFDerivAt.comp q
      (hasMFDerivAt_fst (I := 𝓘(ℝ, ι → ℝ)) (I' := J) q)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ ↦ by simp)
  have hneg' (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, ι → ℝ) (fun q : (ι → ℝ) × B ↦ -q.1) q w = -w.1 := by
    rw [hneg.mfderiv]
    -- `((-id) ∘L fst) w = -w.1` by `ContinuousLinearMap.comp_apply`, `neg_apply` and `coe_fst'`,
    -- which do not rewrite here because `w` is typed as a tangent vector of the product model.
    rfl
  have hsd : MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod J) I (s ∘ Prod.snd) q :=
    ((hsm.comp contMDiff_snd) q).mdifferentiableAt (by simp)
  -- In `hsnd` and `hκs`, `ContinuousLinearMap.snd` applied to the tangent vector `w` of the
  -- product model is `w.2` by definition.
  have hsnd (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (𝓘(ℝ, ι → ℝ).prod J) I (s ∘ Prod.snd) q w = mfderiv J I s q.2 w.2 := by
    rw [mfderiv_comp_snd]
    rfl
  have hκs (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, ι → ℝ) ((κ ∘ π) ∘ (s ∘ Prod.snd)) q w =
        mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 w.2 := by
    have hcomp : (κ ∘ π) ∘ (s ∘ Prod.snd) = κ ∘ (Prod.snd : (ι → ℝ) × B → B) :=
      funext fun q ↦ by simp [hs]
    rw [hcomp, mfderiv_comp_snd]
    rfl
  refine (h.eval₂_mfderiv_hamiltonianFlowActionComp_comp hσc hκ hneg.mdifferentiableAt hsd v
    v').trans ?_
  rw [hneg', hneg', hsnd, hsnd, hκs, hκs]
  -- `(-a) ⬝ᵥ b = -(a ⬝ᵥ b)`, where the negation is taken in the tangent space of `ι → ℝ`, a
  -- type synonym of `ι → ℝ`.
  have e (a a' b b' : ι → ℝ) : -a ⬝ᵥ b' - -a' ⬝ᵥ b = a' ⬝ᵥ b - a ⬝ᵥ b' := by
    rw [neg_dotProduct, neg_dotProduct]
    ring
  exact congrArg₂ (· + ·) rfl (e _ _ _ _)

omit [FiniteDimensional ℝ F] [T2Space B] in
/-- The map `(c, x) ↦ (-c) • s x` is smooth. -/
private theorem contMDiff_coverSection (hsm : ContMDiff J I ∞ s) :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod J) I ∞ (h.coverSection hσc s hκ) :=
  (h.contMDiff_hamiltonianFlowActionComp_uncurry hσc hκ).comp
    ((contDiff_neg.contMDiff.comp contMDiff_fst).prodMk (hsm.comp contMDiff_snd))

variable [BoundarylessManifold J B]

include hs hκ in
/-- **The section map is a local diffeomorphism** at the image `∑ j, c_j dκ_j` of every point
`(c, x)` where `dκ_x` is bijective, when `ι` has `dim B` elements. -/
private theorem isLocalDiffeomorphAt_sectionMap_coordinateCover (hsm : ContMDiff J I ∞ s)
    {q : (ι → ℝ) × B} (hq : Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2))
    (hι : Fintype.card ι = finrank ℝ F) :
    IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I ∞ (h.sectionMap hσc hs)
      (coordinateCover J κ q) := by
  have : Nonempty M := ⟨s q.2⟩
  have hΨ := isLocalDiffeomorphAt_coordinateCover hκ hq hι
  have hCS := h.contMDiff_coverSection hσc hκ hsm
  refine isLocalDiffeomorphAt_of_eqOn_comp isOpen_univ (mem_univ q)
    BoundarylessManifold.isInteriorPoint (by simp)
    (κ := h.coverSection hσc s hκ) (fun q' _ ↦ h.sectionMap_coordinateCover hσc hs hκ q')
    hCS.contMDiffOn ?_ ?_ hΨ
  · refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
    -- The base component of `v` vanishes, since `(c, x) ↦ (-c) • s x` lies over `x`.
    have hv₂ : v.2 = 0 := by
      have hπ : π ∘ h.coverSection hσc s hκ = Prod.snd := funext fun q' ↦
        ((congrArg π (h.sectionMap_coordinateCover hσc hs hκ q').symm).trans
          (h.proj_sectionMap hσc hs _)).trans (CotangentBundle.proj_coordinateCover J κ q')
      have H := mfderiv_comp_apply q (h.mdifferentiableAt _)
        ((hCS q).mdifferentiableAt (by simp)) v
      rw [hπ, mfderiv_snd, hv, map_zero] at H
      -- `ContinuousLinearMap.snd` applied to the tangent vector `v` of the product model is `v.2`.
      exact H
    -- So `dΨ v` pairs to zero with every `dΨ v'` under the canonical form `ω`, where `Ψ` is the
    -- cover: `ω(dΨ v, dΨ v') = σ(d(Φ_s ∘ Ψ) v, d(Φ_s ∘ Ψ) v') - (s^* σ)(v.2, v'.2) = 0`.
    let dΨ := hΨ.mfderivToContinuousLinearEquiv (by simp)
    have hω (v' : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
        SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm J B) (coordinateCover J κ q)
          (dΨ v) (dΨ v') = 0 := by
      have H := h.eval₂_mfderiv_coverSection hσc hs hκ hsm q v v'
      have hs₀ : SmoothBundleForm.eval₂ σ (s q.2) (mfderiv J I s q.2 v.2)
          (mfderiv J I s q.2 v'.2) = 0 := by
        -- `hv₂` states `v.2 = 0` in the model space `F`; restate it in `TangentSpace J q.2`, where
        -- `mfderiv J I s q.2` takes its argument, so that `map_zero` applies after rewriting.
        have hz : v.2 = (0 : TangentSpace J q.2) := hv₂
        rw [hz, map_zero, SmoothBundleForm.eval₂_zero_left]
      rw [hv, SmoothBundleForm.eval₂_zero_left, hs₀, zero_add,
        ← eval₂_symplecticForm_mfderiv_coordinateCover hκ] at H
      -- `dΨ` is `mfderiv (coordinateCover J κ) q` as a continuous linear equivalence.
      exact H.symm
    -- `ω` is nondegenerate and `dΨ` is bijective, so `v = 0`.
    refine dΨ.injective ((dΨ.map_zero).symm ▸ ?_)
    refine SmoothTwoForm.isNondegenerate_iff_separatingLeft.1
      CotangentBundle.isSymplectic_symplecticForm.isNondegenerate _ _ fun W ↦ ?_
    obtain ⟨v', rfl⟩ := dΨ.surjective W
    exact hω v'
  · rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hι, ← h.two_mul_finrank]
    ring

include hs hκ in
/-- **The pullback formula at the image of the cover.** -/
private theorem eval₂_mfderiv_sectionMap_coordinateCover (hsm : ContMDiff J I ∞ s)
    {q : (ι → ℝ) × B} (hq : Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2))
    (hι : Fintype.card ι = finrank ℝ F)
    (V W : TangentSpace (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (coordinateCover J κ q)) :
    SmoothBundleForm.eval₂ σ (h.sectionMap hσc hs (coordinateCover J κ q))
        (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) (coordinateCover J κ q) V)
        (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) (coordinateCover J κ q) W) =
      SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm J B) (coordinateCover J κ q) V W +
        SmoothBundleForm.eval₂ σ (s (coordinateCover J κ q).proj)
          (mfderiv J I s (coordinateCover J κ q).proj
            (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J TotalSpace.proj (coordinateCover J κ q) V))
          (mfderiv J I s (coordinateCover J κ q).proj
            (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J TotalSpace.proj (coordinateCover J κ q) W)) := by
  have hΨ := isLocalDiffeomorphAt_coordinateCover hκ hq hι
  have hΦ := h.isLocalDiffeomorphAt_sectionMap_coordinateCover hσc hs hκ hsm hq hι
  -- Every tangent vector at `coordinateCover J κ q` is the image of one at `q`.
  have hsurj : Surjective
      (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (coordinateCover J κ) q) :=
    (hΨ.mfderivToContinuousLinearEquiv (by simp)).surjective
  obtain ⟨v, rfl⟩ := hsurj V
  obtain ⟨w, rfl⟩ := hsurj W
  -- The section map after the cover is `(c, x) ↦ (-c) • s x`, and the projection after it is
  -- `Prod.snd`.
  have hcomp : h.sectionMap hσc hs ∘ coordinateCover J κ = h.coverSection hσc s hκ :=
    funext (h.sectionMap_coordinateCover hσc hs hκ)
  have hΦΨ (u : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) (coordinateCover J κ q)
          (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (coordinateCover J κ) q u) =
        mfderiv (𝓘(ℝ, ι → ℝ).prod J) I (h.coverSection hσc s hκ) q u := by
    rw [← hcomp, mfderiv_comp_apply q (hΦ.mdifferentiableAt (by simp))
      (hΨ.mdifferentiableAt (by simp))]
  have hπΨ (u : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J (TotalSpace.proj : CotangentBundle J B → B)
          (coordinateCover J κ q)
          (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (coordinateCover J κ) q u) =
        u.2 := by
    rw [← mfderiv_comp_apply q ((Bundle.contMDiff_proj
      (fun x : B ↦ TangentSpace J x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
      (hΨ.mdifferentiableAt (by simp))]
    -- The projection after the cover is `Prod.snd`.
    rw [show TotalSpace.proj ∘ coordinateCover J κ = Prod.snd from
      funext (CotangentBundle.proj_coordinateCover J κ)]
    exact congrArg (· u) (mfderiv_snd (I := 𝓘(ℝ, ι → ℝ)) (I' := J) (x := q))
  rw [hΦΨ, hΦΨ, hπΨ, hπΨ, eval₂_symplecticForm_mfderiv_coordinateCover hκ q v w,
    CotangentBundle.proj_coordinateCover]
  have hA := h.eval₂_mfderiv_coverSection hσc hs hκ hsm q v w
  rw [← congrFun hcomp q] at hA
  exact hA.trans (add_comm _ _)

end Coordinates

/-! ### Smoothness and the pullback of the symplectic form -/

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
include h in
/-- Every covector `ξ` is `∑ j, c_j dκ_j` at its base point, for smooth coordinates
`κ : B → ℝⁿ`, `n = dim B`, with bijective differential at the base point of `ξ`. -/
private theorem exists_coordinateCover_eq_self (ξ : CotangentBundle J B) :
    ∃ (κ : B → Fin (finrank ℝ F) → ℝ) (c : Fin (finrank ℝ F) → ℝ),
      ContMDiff J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ κ ∧
        Bijective (mfderiv J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) κ ξ.proj) ∧
        CotangentBundle.coordinateCover J κ (c, ξ.proj) = ξ := by
  obtain ⟨κ, e, hκ, hdκ, -, -⟩ := h.exists_coordinates ξ.proj
  have hb : Bijective (mfderiv J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) κ ξ.proj) := hdκ ▸ e.bijective
  obtain ⟨c, hc⟩ := CotangentBundle.exists_coordinateCover_eq
    ((hκ ξ.proj).mdifferentiableAt (by simp)) hb ξ.snd
  exact ⟨κ, c, hκ, hb, hc.trans (TotalSpace.eta ξ)⟩

variable [BoundarylessManifold J B]

/-- **The section map of a smooth section is a local diffeomorphism** `T*B → M`. -/
theorem isLocalDiffeomorph_sectionMap (hsm : ContMDiff J I ∞ s) :
    IsLocalDiffeomorph (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I ∞ (h.sectionMap hσc hs) := fun ξ ↦ by
  obtain ⟨κ, c, hκ, hb, hξ⟩ := h.exists_coordinateCover_eq_self ξ
  rw [← hξ]
  exact h.isLocalDiffeomorphAt_sectionMap_coordinateCover hσc hs hκ hsm hb (Fintype.card_fin _)

/-- **The section map of a smooth section is smooth.** -/
theorem contMDiff_sectionMap (hsm : ContMDiff J I ∞ s) :
    ContMDiff (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I ∞ (h.sectionMap hσc hs) :=
  (h.isLocalDiffeomorph_sectionMap hσc hs hsm).contMDiff

/-- **The section map pulls `σ` back to the canonical form plus the pullback of `s^* σ`.** For a
smooth section `s`, at every covector `ξ` and on tangent vectors `V` and `W` of `T*B`,

`σ(dΦ_s V, dΦ_s W) = ω(V, W) + σ(ds (dπ V), ds (dπ W))`,

where `ω = -dλ` is the canonical symplectic form of `T*B` and `π : T*B → B` is the bundle
projection. -/
theorem eval₂_mfderiv_sectionMap (hsm : ContMDiff J I ∞ s) (ξ : CotangentBundle J B)
    (V W : TangentSpace (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ξ) :
    SmoothBundleForm.eval₂ σ (h.sectionMap hσc hs ξ)
        (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) ξ V)
        (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) ξ W) =
      SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm J B) ξ V W +
        SmoothBundleForm.eval₂ σ (s ξ.proj)
          (mfderiv J I s ξ.proj (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J TotalSpace.proj ξ V))
          (mfderiv J I s ξ.proj (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J TotalSpace.proj ξ W)) := by
  obtain ⟨κ, c, hκ, hb, hξ⟩ := h.exists_coordinateCover_eq_self ξ
  revert V W
  rw [← hξ]
  exact h.eval₂_mfderiv_sectionMap_coordinateCover hσc hs hκ hsm hb (Fintype.card_fin _)

/-- **The section map pulls `σ` back to the canonical form plus the pullback of `s^* σ`**:
`Φ_s^* σ = ω + π^* (s^* σ)`, where `ω = -dλ` is the canonical symplectic form of `T*B` and
`π : T*B → B` is the bundle projection. -/
theorem mpullback_sectionMap (hsm : ContMDiff J I ∞ s) :
    SmoothForm.mpullback (h.sectionMap hσc hs) (h.contMDiff_sectionMap hσc hs hsm) σ =
      CotangentBundle.symplecticForm J B +
        SmoothForm.mpullback TotalSpace.proj
          (Bundle.contMDiff_proj (fun x : B ↦ TangentSpace J x →L[ℝ] ℝ))
          (SmoothForm.mpullback s hsm σ) :=
  SmoothBundleForm.ext_eval₂ fun ξ V W ↦ by
    rw [SmoothForm.eval₂_mpullback, h.eval₂_mfderiv_sectionMap hσc hs hsm,
      SmoothBundleForm.eval₂_add, SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback]

/-- **A Lagrangian section gives a symplectic section map.** If the smooth section `s` pulls `σ`
back to zero, as the section of a Lagrangian submanifold does, then `Φ_s` pulls `σ` back to the
canonical symplectic form `ω = -dλ` of `T*B`. -/
theorem mpullback_sectionMap_eq_symplecticForm (hsm : ContMDiff J I ∞ s)
    (hsσ : SmoothForm.mpullback s hsm σ = 0) :
    SmoothForm.mpullback (h.sectionMap hσc hs) (h.contMDiff_sectionMap hσc hs hsm) σ =
      CotangentBundle.symplecticForm J B := by
  rw [h.mpullback_sectionMap hσc hs hsm, hsσ, map_zero, add_zero]

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
