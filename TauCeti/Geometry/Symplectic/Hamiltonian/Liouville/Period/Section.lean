/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Lattice
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle

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
`(c, x) ↦ ∑ j, c_j dκ_j` of `T*B` and `(c, x) ↦ (-c) • s x` of `M`, the second being the
Hamiltonian flow action of `κ ∘ π`, the section map is the second cover read through the first.
The pullback of `σ` along the second cover is computed by
`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_hamiltonianFlowAction_comp`. The pullback of `ω`
along the first cover is `∑ j, dκ_j ∧ dc_j`: it pulls the Liouville form back to `∑ j, c_j dκ_j`,
as does the action–angle covering map `TauCeti.CotangentBundle.actionAngleCover` of the cotangent
bundle of a torus at the angles `κ x`, whose canonical form is known in these coordinates.

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
  h.fiberAction hσc ξ.proj (-ξ.2) ⟨s ξ.proj, hs ξ.proj⟩

/-- The section map at a covector `α` at `b` is the action of `-α` on `s b`. -/
theorem sectionMap_mk (b : B) (α : F →L[ℝ] ℝ) :
    h.sectionMap hσc hs (TotalSpace.mk' (F →L[ℝ] ℝ) b α) =
      (h.fiberAction hσc b (-α) ⟨s b, hs b⟩ : M) :=
  (rfl)

/-- **The section map lies over the base**: `π (Φ_s ξ)` is the base point of `ξ`. -/
theorem proj_sectionMap (ξ : CotangentBundle J B) : π (h.sectionMap hσc hs ξ) = ξ.proj :=
  (h.fiberAction hσc ξ.proj (-ξ.2) ⟨s ξ.proj, hs ξ.proj⟩).2

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

variable {ι : Type*} [Fintype ι] {κ : B → ι → ℝ} (hκ : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ κ)

omit [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] [FiniteDimensional ℝ F]
  [IsManifold J ∞ B] [T2Space B] in
include h hκ in
/-- The components of `κ ∘ π` Poisson-commute. -/
private theorem poissonBracket_comp (i j : ι) (y : M) :
    σ.poissonBracket ((κ ∘ π) · i) ((κ ∘ π) · j) y = 0 :=
  h.poissonBracket_comp_apply_eq_zero ((hκ _).mdifferentiableAt (by simp)) i j

omit [I.Boundaryless] [FiniteDimensional ℝ F] [T2Space B] in
include h hκ in
/-- The components of `κ ∘ π` have complete Hamiltonian vector fields. -/
private theorem isCompleteVectorField_comp (i : ι) :
    IsCompleteVectorField (σ.hamiltonianVectorField ((κ ∘ π) · i)) :=
  h.isCompleteVectorField_hamiltonianVectorField_comp (g := fun b ↦ κ b i) h.isProperMap
    ((contMDiff_pi_module_iff.1 hκ i).of_le (by simp))

/-- The Hamiltonian flow action of `ℝ^ι` generated by the components of `κ ∘ π`. -/
private def compAction (v : ι → ℝ) : M → M :=
  ((⟨hσc, hσ⟩ : σ.IsSymplectic).hamiltonianFlowAction (hκ.comp h.contMDiff)
    (h.poissonBracket_comp hκ) (h.isCompleteVectorField_comp hκ) v).toMul

/-- The covector `∑ j, c_j dκ_j` at `x`. -/
private def cover (κ : B → ι → ℝ) (q : (ι → ℝ) × B) : CotangentBundle J B :=
  TotalSpace.mk' (F →L[ℝ] ℝ) q.2 (∑ j, q.1 j • mvfderiv J (κ · j) q.2)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [I.Boundaryless] [FiniteDimensional ℝ F] [IsManifold J ∞ B] [T2Space B] in
include hκ in
/-- The covector `∑ j, c_j dκ_j` evaluates a tangent vector `u` as `c ⬝ᵥ dκ u`. -/
private theorem cover_snd_apply (q : (ι → ℝ) × B) (u : TangentSpace J q.2) :
    (cover κ q).2 u = q.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 u := by
  have hd (j : ι) : mvfderiv J (κ · j) q.2 u = mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 u j := by
    rw [mvfderiv_apply ((hκ _).mdifferentiableAt (by simp)) j, ContinuousLinearMap.comp_apply,
      mvfderiv_apply_eq_mfderiv_apply]
    rfl
  -- Read `u` as a tangent vector at `q.2`, so that `sum_apply` applies to the covectors on
  -- `TangentSpace J q.2`; each summand `(c • φ) u = c * φ u` then holds by definition.
  refine (sum_apply Finset.univ (fun j ↦ q.1 j • mvfderiv J (κ · j) q.2) u).trans ?_
  exact Finset.sum_congr rfl fun j _ ↦ congrArg (q.1 j * ·) (hd j)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [I.Boundaryless] [FiniteDimensional ℝ F] [T2Space B] in
include hκ in
/-- The cover `(c, x) ↦ ∑ j, c_j dκ_j` is smooth. -/
private theorem contMDiff_cover :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ (cover (J := J) κ) :=
  ContMDiff.sum_sectionAlong Finset.univ _ contMDiff_snd fun j _ ↦
    ((contDiff_apply ℝ (fun _ : ι ↦ ℝ) j).contMDiff.comp contMDiff_fst).smul_totalSpace
      ((ContMDiff.contMDiff_totalSpaceMk_mvfderiv (n := ∞)
        ((contMDiff_pi_module_iff.1 hκ j).of_le (by simp))).comp contMDiff_snd)

/-- **The section map on `∑ j, c_j dκ_j`** is the action of `-c` on `s x` for the Hamiltonian
flow action of `κ ∘ π`. -/
private theorem sectionMap_cover (q : (ι → ℝ) × B) :
    h.sectionMap hσc hs (cover κ q) = h.compAction hσc hκ (-q.1) (s q.2) := by
  classical
  -- The covector `-∑ j, c_j dκ_j` is the differential of `g = (-c) ⬝ᵥ κ`.
  let L : (ι → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductEquiv ℝ ι (-q.1))
  have hg : ContMDiff J 𝓘(ℝ) 2 (L ∘ κ) := (L.contMDiff.comp hκ).of_le (by simp)
  have hgd : mvfderiv J (L ∘ κ) q.2 = -(cover κ q).2 := by
    ext u
    rw [L.mvfderiv_comp_apply ((hκ _).mdifferentiableAt (by simp)),
      mvfderiv_apply_eq_mfderiv_apply]
    refine Eq.trans ?_ (neg_apply (cover κ q).2 u).symm
    refine Eq.trans ?_ (congrArg Neg.neg (cover_snd_apply hκ q u).symm)
    simp only [L, LinearMap.coe_toContinuousLinearMap']
    exact neg_dotProduct _ _
  have hfun : (L ∘ κ) ∘ π = fun y ↦ -q.1 ⬝ᵥ (κ ∘ π) y :=
    funext fun y ↦ by simp [L, dotProductEquiv]
  rw [sectionMap, h.coe_fiberAction_eq_flowOf hσc (cover κ q).proj hg hgd, compAction, hfun,
    (⟨hσc, hσ⟩ : σ.IsSymplectic).flowOf_hamiltonianVectorField_dotProduct, one_smul]
  rfl

variable (s) in
/-- The point `(-c) • s x` of the Hamiltonian flow action of `κ ∘ π`, as a function of
`(c, x)`. -/
private def coverSection (q : (ι → ℝ) × B) : M := h.compAction hσc hκ (-q.1) (s q.2)

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
    rfl
  have hsd : MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod J) I (s ∘ Prod.snd) q :=
    ((hsm.comp contMDiff_snd) q).mdifferentiableAt (by simp)
  have hsnd (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (𝓘(ℝ, ι → ℝ).prod J) I (s ∘ Prod.snd) q w = mfderiv J I s q.2 w.2 := by
    rw [mfderiv_comp_apply q ((hsm q.2).mdifferentiableAt (by simp)) mdifferentiableAt_snd,
      mfderiv_snd]
    rfl
  have hκs (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, ι → ℝ) ((κ ∘ π) ∘ (s ∘ Prod.snd)) q w =
        mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 w.2 := by
    have hcomp : (κ ∘ π) ∘ (s ∘ Prod.snd) = κ ∘ (Prod.snd : (ι → ℝ) × B → B) :=
      funext fun q ↦ by simp [hs]
    rw [hcomp, mfderiv_comp_apply q ((hκ q.2).mdifferentiableAt (by simp)) mdifferentiableAt_snd,
      mfderiv_snd]
    rfl
  refine ((⟨hσc, hσ⟩ : σ.IsSymplectic).eval₂_mfderiv_hamiltonianFlowAction_comp
    (hκ.comp h.contMDiff) (h.poissonBracket_comp hκ) (h.isCompleteVectorField_comp hκ)
    hneg.mdifferentiableAt hsd v v').trans ?_
  rw [hneg', hneg', hsnd, hsnd, hκs, hκs]
  -- `(-a) ⬝ᵥ b = -(a ⬝ᵥ b)`, where the negation is taken in the tangent space of `ι → ℝ`, a
  -- type synonym of `ι → ℝ`.
  have e (a a' b b' : ι → ℝ) : -a ⬝ᵥ b' - -a' ⬝ᵥ b = a' ⬝ᵥ b - a ⬝ᵥ b' := by
    rw [neg_dotProduct, neg_dotProduct]
    ring
  exact congrArg₂ (· + ·) rfl (e _ _ _ _)


/-- The angles and actions `(κ x, c)` of `(c, x)`. -/
private def anglesActions (κ : B → ι → ℝ) (q : (ι → ℝ) × B) : (ι → ℝ) × (ι → ℝ) := (κ q.2, q.1)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [I.Boundaryless] [FiniteDimensional ℝ F] [IsManifold J ∞ B] [T2Space B] in
include hκ in
/-- The map `(c, x) ↦ (κ x, c)` is smooth. -/
private theorem contMDiff_anglesActions :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ∞ (anglesActions (B := B) κ) :=
  (hκ.comp contMDiff_snd).prodMk_space contMDiff_fst

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [I.Boundaryless] [FiniteDimensional ℝ F] [IsManifold J ∞ B] [T2Space B] in
include hκ in
/-- The map `(c, x) ↦ (κ x, c)` has derivative `(w, u) ↦ (dκ u, w)`. -/
private theorem hasMFDerivAt_anglesActions (q : (ι → ℝ) × B) :
    HasMFDerivAt (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions κ) q
      (((mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) F)).prod
        (ContinuousLinearMap.fst ℝ (ι → ℝ) F)) := by
  have h₁ := ((hκ q.2).mdifferentiableAt (by simp)).hasMFDerivAt.comp q
    (hasMFDerivAt_snd (I := 𝓘(ℝ, ι → ℝ)) (I' := J) q)
  have h₂ := hasMFDerivAt_fst (I := 𝓘(ℝ, ι → ℝ)) (I' := J) q
  -- The model of `(ι → ℝ) × (ι → ℝ)` is that of a normed space, so the derivatives pair up.
  exact ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [I.Boundaryless] [FiniteDimensional ℝ F] [T2Space B] in
include hκ in
/-- **The canonical form on the cover.** The cover `(c, x) ↦ ∑ j, c_j dκ_j` pulls the canonical
symplectic form of `T*B` back to `∑ j, dκ_j ∧ dc_j`, which takes the value
`w' ⬝ᵥ dκ u - w ⬝ᵥ dκ u'` on `(w, u), (w', u')`. It pulls the Liouville form back to
`∑ j, c_j dκ_j`, as does `(c, x) ↦ ∑ j, c_j dθ_j` at the angles `θ = κ x` on the cotangent
bundle of a torus, so the canonical forms agree after pullback as well. -/
private theorem eval₂_symplecticForm_mfderiv_cover (q : (ι → ℝ) × B)
    (v v' : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
    SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm J B) (cover κ q)
        (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (cover κ) q v)
        (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (cover κ) q v') =
      v'.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v.2 - v.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v'.2 := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hΞ := contMDiff_anglesActions hκ
  have hT := CotangentBundle.contMDiff_actionAngleCover (ι := ι) 1
  -- Both maps pull the Liouville forms back to `∑ j, c_j dκ_j`.
  have hlv : SmoothForm.mpullback (cover κ) (contMDiff_cover hκ)
        (CotangentBundle.liouvilleForm J B) =
      SmoothForm.mpullback (CotangentBundle.actionAngleCover 1 ∘ anglesActions κ) (hT.comp hΞ)
        (CotangentBundle.liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (ι → AddCircle (1 : ℝ))) := by
    refine SmoothBundleForm.ext fun x w ↦ ?_
    obtain ⟨u, rfl⟩ : ∃ u, w = ![u] := ⟨w 0, by ext i; fin_cases i; rfl⟩
    rw [SmoothForm.coe_mpullback, CotangentBundle.mpullback_liouvilleForm_apply_of_proj_comp_eq
        (g := Prod.snd) (fun _ ↦ rfl) (((contMDiff_cover hκ) x).mdifferentiableAt (by simp)),
      Matrix.cons_val_zero, mfderiv_snd, ← SmoothForm.mpullback_mpullback _ _ hΞ hT,
      SmoothForm.mpullback_apply_one, SmoothForm.coe_mpullback,
      CotangentBundle.mpullback_liouvilleForm_actionAngleCover_apply,
      (hasMFDerivAt_anglesActions hκ x).mfderiv]
    exact (cover_snd_apply hκ x u.2).trans (Finset.sum_congr rfl fun j _ ↦ rfl)
  -- `ω = -dλ`, and `d` commutes with both pullbacks.
  have hB := SmoothForm.mextDeriv_mpullback_apply_two (cover κ) (contMDiff_cover hκ)
    (CotangentBundle.liouvilleForm J B) q v v'
  have hTq := SmoothForm.mextDeriv_mpullback_apply_two _ (hT.comp hΞ)
    (CotangentBundle.liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle (1 : ℝ))) q v v'
  rw [hlv, hTq] at hB
  have hG (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (𝓘(ℝ, ι → ℝ).prod J) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (CotangentBundle.actionAngleCover 1 ∘ anglesActions κ) q w =
        mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (CotangentBundle.actionAngleCover 1) (anglesActions κ q)
          (mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions κ) q w) :=
    mfderiv_comp_apply q ((hT _).mdifferentiableAt (by simp))
      ((hΞ q).mdifferentiableAt (by simp)) w
  have hω := CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleCover (ι := ι) 1
    (anglesActions κ q)
    (mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions κ) q v)
    (mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions κ) q v')
  rw [← hG, ← hG, SmoothBundleForm.eval₂_apply, CotangentBundle.symplecticForm_eq_neg_mextDeriv,
    Pi.neg_apply, ContinuousAlternatingMap.neg_apply] at hω
  rw [SmoothBundleForm.eval₂_apply, CotangentBundle.symplecticForm_eq_neg_mextDeriv, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, ← hB]
  -- `hω` is the value of `-dλ` after the second map; read it with `(w, u) ↦ (dκ u, w)`.
  refine (congrArg Neg.neg ?_).trans (hω.trans ?_)
  · -- The base points `(f ∘ g) q` and `f (g q)` agree by definition.
    rfl
  rw [(hasMFDerivAt_anglesActions hκ q).mfderiv]
  simp only [dotProduct, ← Finset.sum_sub_distrib]
  -- The derivative `(w, u) ↦ (dκ u, w)` has these coordinates by definition.
  exact Finset.sum_congr rfl fun j _ ↦ congrArg₂ (· - ·) (mul_comm _ _) (mul_comm _ _)

/-- If `Q(u, u') + (w' ⬝ᵥ D u - w ⬝ᵥ D u')` vanishes for all `(w', u')`, for a bijective map `D`
with `D 0 = 0` and a function `Q` vanishing when either argument is zero, then `w = 0` and
`u = 0`. -/
private theorem eq_zero_of_forall_add_dotProduct_sub_eq_zero {V : Type*} [Zero V]
    {D : V → ι → ℝ} (hD : Bijective D) (hD₀ : D 0 = 0) {Q : V → V → ℝ} (hQ₁ : ∀ u, Q u 0 = 0)
    (hQ₂ : ∀ u', Q 0 u' = 0) {w : ι → ℝ} {u : V}
    (H : ∀ w' u', Q u u' + (w' ⬝ᵥ D u - w ⬝ᵥ D u') = 0) : w = 0 ∧ u = 0 := by
  classical
  -- Pairing with `(eᵢ, 0)` gives `(D u)ᵢ = 0`, so `u = 0`.
  have hu : u = 0 := hD.1 <| hD₀.symm ▸ funext fun i ↦ by
    simpa [hQ₁, hD₀] using H (Pi.single i 1) 0
  -- Pairing with `(0, D⁻¹ eᵢ)` then gives `wᵢ = 0`.
  refine ⟨funext fun i ↦ ?_, hu⟩
  obtain ⟨u', hu'⟩ := hD.2 (Pi.single i 1)
  simpa [hu, hQ₂, hu', hD₀] using H 0 u'

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [I.Boundaryless] [FiniteDimensional ℝ F] [IsManifold J ∞ B] [T2Space B] in
include hκ in
/-- Where `dκ_x` is bijective, every covector at `x` is `∑ j, c_j dκ_j` for some `c`. -/
private theorem exists_cover_eq {x : B} (hx : Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ x))
    (α : TangentSpace J x →L[ℝ] ℝ) : ∃ c, cover κ (c, x) = TotalSpace.mk' (F →L[ℝ] ℝ) x α := by
  classical
  let D : TangentSpace J x ≃ₗ[ℝ] (ι → ℝ) :=
    LinearEquiv.ofBijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ x).toLinearMap hx
  refine ⟨fun j ↦ α (D.symm (Pi.single j 1)), congrArg (TotalSpace.mk' (F →L[ℝ] ℝ) x) ?_⟩
  ext u
  -- `∑ j, α (D⁻¹ eⱼ) (D u)ⱼ = α (D⁻¹ (D u)) = α u`.
  refine (cover_snd_apply hκ (_, x) u).trans ?_
  have hu : u = ∑ j, (D u) j • D.symm (Pi.single j 1) := by
    conv_lhs => rw [← D.symm_apply_apply u, pi_eq_sum_univ' (D u)]
    rw [map_sum]
    simp only [map_smul]
  conv_rhs => rw [hu]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

omit [FiniteDimensional ℝ F] [T2Space B] in
/-- The map `(c, x) ↦ (-c) • s x` is smooth. -/
private theorem contMDiff_coverSection (hsm : ContMDiff J I ∞ s) :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod J) I ∞ (h.coverSection hσc s hκ) :=
  ((⟨hσc, hσ⟩ : σ.IsSymplectic).contMDiff_hamiltonianFlowAction_uncurry (hκ.comp h.contMDiff)
    (h.poissonBracket_comp hκ) (h.isCompleteVectorField_comp hκ)).comp
    ((contDiff_neg.contMDiff.comp contMDiff_fst).prodMk (hsm.comp contMDiff_snd))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [I.Boundaryless] in
/-- The dimension count `dim ℝ^ι + dim B = 2 dim B = dim T*B` when `ι` has `dim B` elements. -/
private theorem finrank_prod_eq (hι : Fintype.card ι = finrank ℝ F) :
    finrank ℝ ((ι → ℝ) × F) = finrank ℝ (F × (F →L[ℝ] ℝ)) := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hι,
    ← (LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] ℝ) ≃ₗ[ℝ] F →L[ℝ] ℝ).finrank_eq,
    Subspace.dual_finrank_eq]

variable [BoundarylessManifold J B]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space B] in
include hκ in
/-- **The cover is a local diffeomorphism** at every point `(c, x)` where `dκ_x` is bijective, when
`ι` has `dim B` elements: its pullback of the canonical form is nondegenerate there. -/
private theorem isLocalDiffeomorphAt_cover {q : (ι → ℝ) × B}
    (hq : Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2)) (hι : Fintype.card ι = finrank ℝ F) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ (cover (J := J) κ) q := by
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_cover hκ).contMDiffOn isOpen_univ
    (mem_univ q) BoundarylessManifold.isInteriorPoint (by simp) ?_ (finrank_prod_eq hι)
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  -- A vector killed by the derivative pairs to zero with everything under the pulled-back form.
  have H (w' : ι → ℝ) (u' : TangentSpace J q.2) :
      (fun _ _ ↦ (0 : ℝ)) v.2 u' + (w' ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v.2 -
        v.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 u') = 0 := by
    have := eval₂_symplecticForm_mfderiv_cover hκ q v (w', u')
    rw [← SmoothForm.bilinFormAt_apply, hv, map_zero, LinearMap.zero_apply] at this
    exact (zero_add _).trans this.symm
  obtain ⟨h₁, h₂⟩ := eq_zero_of_forall_add_dotProduct_sub_eq_zero hq (map_zero _)
    (Q := fun _ _ ↦ 0) (w := v.1) (u := v.2) (fun _ ↦ rfl) (fun _ ↦ rfl) H
  exact Prod.ext h₁ h₂

include hs hκ in
/-- **The section map is a local diffeomorphism** at the image `∑ j, c_j dκ_j` of every point
`(c, x)` where `dκ_x` is bijective, when `ι` has `dim B` elements. -/
private theorem isLocalDiffeomorphAt_sectionMap_cover (hsm : ContMDiff J I ∞ s)
    {q : (ι → ℝ) × B} (hq : Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2))
    (hι : Fintype.card ι = finrank ℝ F) :
    IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I ∞ (h.sectionMap hσc hs) (cover κ q) := by
  have : Nonempty M := ⟨s q.2⟩
  refine isLocalDiffeomorphAt_of_eqOn_comp isOpen_univ (mem_univ q)
    BoundarylessManifold.isInteriorPoint (by simp)
    (κ := h.coverSection hσc s hκ) (fun q' _ ↦ h.sectionMap_cover hσc hs hκ q')
    (h.contMDiff_coverSection hσc hκ hsm).contMDiffOn
    ?_ ?_ (isLocalDiffeomorphAt_cover hκ hq hι)
  · refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
    -- A vector killed by the derivative pairs to zero with everything under the pullback of `σ`.
    have H (w' : ι → ℝ) (u' : TangentSpace J q.2) :
        (fun u u' ↦ SmoothBundleForm.eval₂ σ (s q.2) (mfderiv J I s q.2 u)
            (mfderiv J I s q.2 u')) v.2 u' +
          (w' ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v.2 - v.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 u') = 0 := by
      have := h.eval₂_mfderiv_coverSection hσc hs hκ hsm q v (w', u')
      rw [← SmoothForm.bilinFormAt_apply, hv, map_zero, LinearMap.zero_apply] at this
      exact this.symm
    obtain ⟨h₁, h₂⟩ := eq_zero_of_forall_add_dotProduct_sub_eq_zero hq (map_zero _)
      (Q := fun u u' ↦ SmoothBundleForm.eval₂ σ (s q.2) (mfderiv J I s q.2 u)
        (mfderiv J I s q.2 u')) (w := v.1) (u := v.2)
      (fun u ↦ by rw [map_zero, ← SmoothForm.bilinFormAt_apply, map_zero])
      (fun u' ↦ by
        rw [map_zero, ← SmoothForm.bilinFormAt_apply, map_zero, LinearMap.zero_apply])
      H
    exact Prod.ext h₁ h₂
  · rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hι, ← h.two_mul_finrank]
    ring

include hs hκ in
/-- **The pullback formula at the image of the cover.** -/
private theorem eval₂_mfderiv_sectionMap_cover (hsm : ContMDiff J I ∞ s) {q : (ι → ℝ) × B}
    (hq : Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2)) (hι : Fintype.card ι = finrank ℝ F)
    (V W : TangentSpace (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (cover κ q)) :
    SmoothBundleForm.eval₂ σ (h.sectionMap hσc hs (cover κ q))
        (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) (cover κ q) V)
        (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) (cover κ q) W) =
      SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm J B) (cover κ q) V W +
        SmoothBundleForm.eval₂ σ (s (cover κ q).proj)
          (mfderiv J I s (cover κ q).proj
            (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J TotalSpace.proj (cover κ q) V))
          (mfderiv J I s (cover κ q).proj
            (mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J TotalSpace.proj (cover κ q) W)) := by
  have hΨ := isLocalDiffeomorphAt_cover hκ hq hι
  have hΦ := h.isLocalDiffeomorphAt_sectionMap_cover hσc hs hκ hsm hq hι
  -- Every tangent vector at `cover κ q` is the image of one at `q`.
  have hsurj : Surjective (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (cover κ) q) :=
    (hΨ.mfderivToContinuousLinearEquiv (by simp)).surjective
  obtain ⟨v, rfl⟩ := hsurj V
  obtain ⟨w, rfl⟩ := hsurj W
  -- The section map after the cover is `(c, x) ↦ (-c) • s x`, and the projection after it is
  -- `Prod.snd`.
  have hcomp : h.sectionMap hσc hs ∘ cover κ = h.coverSection hσc s hκ :=
    funext (h.sectionMap_cover hσc hs hκ)
  have hΦΨ (u : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I (h.sectionMap hσc hs) (cover κ q)
          (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (cover κ) q u) =
        mfderiv (𝓘(ℝ, ι → ℝ).prod J) I (h.coverSection hσc s hκ) q u := by
    rw [← hcomp, mfderiv_comp_apply q (hΦ.mdifferentiableAt (by simp))
      (hΨ.mdifferentiableAt (by simp))]
  have hπΨ (u : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J (TotalSpace.proj : CotangentBundle J B → B) (cover κ q)
          (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (cover κ) q u) = u.2 := by
    rw [← mfderiv_comp_apply q ((Bundle.contMDiff_proj
      (fun x : B ↦ TangentSpace J x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
      (hΨ.mdifferentiableAt (by simp))]
    -- The projection after the cover is `Prod.snd`.
    exact congrArg (· u) (mfderiv_snd (I := 𝓘(ℝ, ι → ℝ)) (I' := J) (x := q))
  rw [hΦΨ, hΦΨ, hπΨ, hπΨ, eval₂_symplecticForm_mfderiv_cover hκ q v w]
  have hA := h.eval₂_mfderiv_coverSection hσc hs hκ hsm q v w
  rw [← congrFun hcomp q] at hA
  exact hA.trans (add_comm _ _)

end Coordinates

/-! ### Smoothness and the pullback of the symplectic form -/

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
include h in
/-- Every point of the base has smooth coordinates `κ : B → ℝⁿ`, `n = dim B`, with bijective
differential at that point. -/
private theorem exists_contMDiff_bijective_mfderiv (b : B) :
    ∃ κ : B → Fin (finrank ℝ F) → ℝ, ContMDiff J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ κ ∧
      Bijective (mfderiv J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) κ b) := by
  obtain ⟨κ, e, hκ, hdκ, -, -⟩ := h.exists_coordinates b
  exact ⟨κ, hκ, hdκ ▸ e.bijective⟩

variable [BoundarylessManifold J B]

/-- **The section map of a smooth section is a local diffeomorphism** `T*B → M`. -/
theorem isLocalDiffeomorph_sectionMap (hsm : ContMDiff J I ∞ s) :
    IsLocalDiffeomorph (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I ∞ (h.sectionMap hσc hs) := fun ξ ↦ by
  obtain ⟨κ, hκ, hb⟩ := h.exists_contMDiff_bijective_mfderiv ξ.proj
  obtain ⟨c, hc⟩ := exists_cover_eq hκ hb ξ.2
  -- `ξ` is the covector `∑ j, c_j dκ_j` at its base point.
  have hc' : cover κ (c, ξ.proj) = ξ := hc
  rw [← hc']
  exact h.isLocalDiffeomorphAt_sectionMap_cover hσc hs hκ hsm hb (Fintype.card_fin _)

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
  obtain ⟨κ, hκ, hb⟩ := h.exists_contMDiff_bijective_mfderiv ξ.proj
  obtain ⟨c, hc⟩ := exists_cover_eq hκ hb ξ.2
  -- `ξ` is the covector `∑ j, c_j dκ_j` at its base point.
  have hc' : cover κ (c, ξ.proj) = ξ := hc
  revert V W
  rw [← hc']
  exact h.eval₂_mfderiv_sectionMap_cover hσc hs hκ hsm hb (Fintype.card_fin _)

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
