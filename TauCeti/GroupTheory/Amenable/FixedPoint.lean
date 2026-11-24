/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.Analysis.LocallyConvex.Barycenter
public import TauCeti.GroupTheory.Amenable.WeakStar
public import TauCeti.Topology.Algebra.Group.UCB.Orbit

import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv
import TauCeti.Topology.Algebra.GroupAction.Convex

/-!
# The Day–Rickert affine fixed-point characterization of amenable topological groups

A topological group `G` is amenable—meaning `TauCeti.UCB G` carries a left-invariant mean—if and
only if every jointly continuous affine action of `G` on a nonempty compact convex subset `K` of a
Hausdorff locally convex real topological vector space `E` has a fixed point. Neither local
compactness nor separation is needed on `G`, and the ambient real space `E` is completely
universe-polymorphic (`E : Type v` in the forward direction, and `E : Type (max u v)` for arbitrary
`v` in the equivalence).

Both implications connect `TauCeti.Mean G` to affine `G`-actions on compact convex sets:

* **Averaging by a mean (`Amenable G →` fixed point).** Suppose `G` acts jointly continuously on a
  nonempty compact convex set `K ⊆ E` preserving binary convex combinations. For any `x₀ : K` and
  `m : Mean G`, pulling `m` back along `TauCeti.UCB.orbitPositiveLinearMap G x₀` gives a normalized
  positive functional `m.pullbackOrbit x₀` on `C(K, ℝ)`, whose Choquet–Rudin barycenter
  `m.orbitBarycenter K hK x₀` lies in `K`. Acting by `g : G` on `m.orbitBarycenter K hK x₀` gives
  `(g • m).orbitBarycenter K hK x₀`, so when `m` is left invariant (`g • m = m`),
  `m.orbitBarycenter K hK x₀` is fixed by every `g : G`.
* **Action on the compact convex space of means (fixed point `→ Amenable G`).** Left translation
  induces the contragredient action `(g • m) f = m (L_{g⁻¹} f)` on `Mean G` and the weak-*
  continuous linear action `TauCeti.UCB.leftTranslationWeakDual` on `WeakDual ℝ (UCB G)` (developed
  in `TauCeti.Topology.Algebra.Group.UCB.WeakDual`, `TauCeti.GroupTheory.Amenable.Basic`, and
  `TauCeti.GroupTheory.Amenable.WeakStar`), whose fixed points in `Mean G` are the left-invariant
  means and whose action on `G × Mean G` is jointly continuous. Embedding `Mean G` as constant
  functions in `PUnit.{v + 1} → WeakDual ℝ (UCB G)` yields a fixed point in `Type (max u v)`, hence
  a left-invariant mean on `UCB G`.

## Main definitions

* `TauCeti.Mean.pullbackOrbit m x`: the normalized positive linear functional on `C(X, ℝ)` obtained
  by pulling `m` back along `TauCeti.UCB.orbitPositiveLinearMap G x` (equivalently, pushing `m`
  forward along the orbit map `g ↦ g • x : G → X` of a compact `G`-space `X`).
* `TauCeti.Mean.orbitBarycenter m K hK x`: the Choquet–Rudin barycenter in `K` of
  `m.pullbackOrbit x`.

## Main results

* `TauCeti.Mean.pullbackOrbit_eval`, `TauCeti.Mean.orbitBarycenter_eval`: evaluating
  `pullbackOrbit` and `orbitBarycenter` at `Mean.eval G g` recovers point evaluation and `g • x`.
* `TauCeti.Mean.pullbackOrbit_smul`, `TauCeti.Mean.smul_orbitBarycenter`,
  `TauCeti.Mean.IsLeftInvariant.smul_orbitBarycenter`: `G`-equivariance of `pullbackOrbit` and
  `orbitBarycenter`, and `G`-invariance of the orbit barycenter of a left-invariant mean.
* `TauCeti.Amenable.exists_fixedPoint_subtype`, `TauCeti.Amenable.exists_fixedPoint_of_mapsTo`,
  `TauCeti.Amenable.exists_fixedPoint_affineMap`, `TauCeti.Amenable.exists_fixedPoint_affineEquiv`:
  forward Day–Rickert fixed-point theorems in arbitrary universe `Type v`.
* `TauCeti.Amenable.of_forall_exists_fixedPoint_affineEquiv`,
  `TauCeti.Amenable.of_forall_exists_fixedPoint_affineMap`,
  `TauCeti.Amenable.of_forall_exists_fixedPoint_subtype`: converse from fixed points in
  `Type (max u v)`.
* `TauCeti.amenable_iff_forall_exists_fixedPoint_affineMap`,
  `TauCeti.amenable_iff_forall_exists_fixedPoint_affineEquiv`,
  `TauCeti.amenable_iff_forall_exists_fixedPoint_subtype`: universe-polymorphic Day–Rickert
  fixed-point characterizations of `Amenable G`.

## References

* M. M. Day, *Fixed-point theorems for compact convex sets*, Illinois J. Math. **5** (1961),
  585–590.
* N. W. Rickert, *Amenable groups and groups with the fixed point property*, Trans. Amer. Math.
  Soc. **127** (1967), 221–232, Theorem 4.2.
* V. Runde, *Lectures on Amenability*, Lecture Notes in Mathematics **1774**, Springer, 2002,
  Theorem 1.3.2.
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti

universe u v

namespace Mean

section OrbitBarycenter

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section CompactSpace

variable {X : Type v} [TopologicalSpace X] [CompactSpace X] [MulAction G X] [ContinuousSMul G X]

/-- Pullback of a mean `m : Mean G` along `UCB.orbitPositiveLinearMap G x : C(X, ℝ) →ₚ[ℝ] UCB G`
(equivalently, pushforward of `m` along the orbit map `g ↦ g • x : G → X` in a compact `G`-space
`X`), as a positive linear functional on `C(X, ℝ)`. -/
def pullbackOrbit (m : Mean G) (x : X) : C(X, ℝ) →ₚ[ℝ] ℝ :=
  m.toPositiveLinearMap.comp (UCB.orbitPositiveLinearMap G x)

@[simp]
theorem pullbackOrbit_apply (m : Mean G) (x : X) (f : C(X, ℝ)) :
    m.pullbackOrbit x f = m (UCB.orbitPositiveLinearMap G x f) := by
  simp [pullbackOrbit]

/-- `m.pullbackOrbit x` is normalized (`m.pullbackOrbit x 1 = 1`). -/
theorem pullbackOrbit_one (m : Mean G) (x : X) : m.pullbackOrbit x 1 = 1 := by
  simp

/-- Pulling back the point-evaluation mean `eval G g` along `UCB.orbitPositiveLinearMap G x` gives
point evaluation at `g • x`. -/
@[simp]
theorem pullbackOrbit_eval (g : G) (x : X) :
    (eval G g).pullbackOrbit x = ContinuousMap.evalPositiveLinearMap ℝ ℝ (g • x) := by
  ext f
  simp

/-- Pulling back `g • m` along `UCB.orbitPositiveLinearMap G x` precomposes `m.pullbackOrbit x`
with `Homeomorph.smul g : X ≃ₜ X`. -/
theorem pullbackOrbit_smul (g : G) (m : Mean G) (x : X) :
    (g • m).pullbackOrbit x =
      (m.pullbackOrbit x).comp
        (ContinuousMap.compPositiveLinearMap ℝ ℝ (Homeomorph.smul g : X ≃ₜ X)) := by
  ext f
  simp only [pullbackOrbit_apply, PositiveLinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
    ContinuousMap.compPositiveLinearMap_apply, smul_apply,
    UCB.leftTranslation_orbitPositiveLinearMap, inv_inv]

/-- Pulling back a left-invariant mean along `UCB.orbitPositiveLinearMap G x` produces a functional
on `C(X, ℝ)` invariant under precomposition with `Homeomorph.smul g`. -/
theorem IsLeftInvariant.pullbackOrbit_comp_smul {m : Mean G} (hm : m.IsLeftInvariant) (g : G)
    (x : X) (f : C(X, ℝ)) :
    m.pullbackOrbit x (f.comp (Homeomorph.smul g : X ≃ₜ X)) = m.pullbackOrbit x f := by
  have h := DFunLike.congr_fun (m.pullbackOrbit_smul g x) f
  simpa [hm.smul_eq g] using h.symm

end CompactSpace

section Barycenter

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The Choquet–Rudin barycenter in `K` of the functional `m.pullbackOrbit x` obtained by averaging
along the orbit `g ↦ g • x` of `x : K` under a mean `m : Mean G`. -/
def orbitBarycenter (m : Mean G) (K : Set E) [MulAction G K] [ContinuousSMul G K]
    (hK : IsCompact K) (x : K) : E :=
  letI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  barycenter K (m.pullbackOrbit x)

/-- On a compact space `K`, `m.orbitBarycenter K hK x` is `barycenter K (m.pullbackOrbit x)`. -/
theorem orbitBarycenter_eq_barycenter (m : Mean G) {K : Set E} [CompactSpace K] [MulAction G K]
    [ContinuousSMul G K] (hK : IsCompact K) (x : K) :
    m.orbitBarycenter K hK x = barycenter K (m.pullbackOrbit x) :=
  (rfl)

/-- The orbit barycenter `m.orbitBarycenter K hK x` lies in `K` whenever `K` is compact and convex.
-/
theorem orbitBarycenter_mem (m : Mean G) {K : Set E} [MulAction G K] [ContinuousSMul G K]
    (hK : IsCompact K) (hKc : Convex ℝ K) (x : K) :
    m.orbitBarycenter K hK x ∈ K := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  rw [orbitBarycenter_eq_barycenter]
  exact barycenter_mem hK hKc (m.pullbackOrbit x) (m.pullbackOrbit_one x)

/-- Every continuous linear functional `ℓ : StrongDual ℝ E` evaluates at `m.orbitBarycenter K hK x`
to the mean `m` applied to the orbit function `g ↦ ℓ (g • x)`. -/
theorem strongDual_orbitBarycenter (m : Mean G) {K : Set E} [MulAction G K]
    [ContinuousSMul G K] (hK : IsCompact K) (hKc : Convex ℝ K) (x : K) (ℓ : StrongDual ℝ E) :
    letI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    ℓ (m.orbitBarycenter K hK x) =
      m (UCB.orbitPositiveLinearMap G x ((ℓ : C(E, ℝ)).restrict K)) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  rw [orbitBarycenter_eq_barycenter, strongDual_barycenter hK hKc _ (m.pullbackOrbit_one x),
    pullbackOrbit_apply]

/-- In a space with separating continuous dual, the orbit barycenter of the point-evaluation mean
`eval G g` at `x : K` is `g • x`. -/
@[simp]
theorem orbitBarycenter_eval [SeparatingDual ℝ E] (g : G) {K : Set E} [MulAction G K]
    [ContinuousSMul G K] (hK : IsCompact K) (x : K) :
    (eval G g).orbitBarycenter K hK x = (g • x : K) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  rw [orbitBarycenter_eq_barycenter, pullbackOrbit_eval, barycenter_evalPositiveLinearMap]

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- Equivariance of `orbitBarycenter`: if the `G`-action on a compact convex subset `K` of a
Hausdorff locally convex real space `E` preserves binary convex combinations in `E`, acting by
`g : G` on `m.orbitBarycenter K hK x` gives `(g • m).orbitBarycenter K hK x`. -/
theorem smul_orbitBarycenter (m : Mean G) {K : Set E} [MulAction G K] [ContinuousSMul G K]
    (hK : IsCompact K) (hKc : Convex ℝ K)
    (hcomb : ∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      ((g • (⟨a • (y : E) + b • (z : E), hKc y.property z.property ha hb hab⟩ : K) : K) : E) =
        a • ((g • y : K) : E) + b • ((g • z : K) : E))
    (g : G) (x : K) :
    ((g • (⟨m.orbitBarycenter K hK x, m.orbitBarycenter_mem hK hKc x⟩ : K) : K) : E) =
      (g • m).orbitBarycenter K hK x := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hcov := map_barycenter_of_map_smul_add_smul hK hKc (m.pullbackOrbit x)
    (m.pullbackOrbit_one x) (T := ((Homeomorph.smul g : K ≃ₜ K) : C(K, K)))
    (fun y z a b ha hb hab => hcomb g y z a b ha hb hab)
  simpa [orbitBarycenter_eq_barycenter, pullbackOrbit_smul] using hcov

/-- If `m` is a left-invariant mean and the `G`-action on `K` preserves binary convex combinations
in `E`, then `m.orbitBarycenter K hK x` is fixed by every `g : G`. -/
theorem IsLeftInvariant.smul_orbitBarycenter {m : Mean G} (hm : m.IsLeftInvariant) {K : Set E}
    [MulAction G K] [ContinuousSMul G K] (hK : IsCompact K) (hKc : Convex ℝ K)
    (hcomb : ∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      ((g • (⟨a • (y : E) + b • (z : E), hKc y.property z.property ha hb hab⟩ : K) : K) : E) =
        a • ((g • y : K) : E) + b • ((g • z : K) : E))
    (g : G) (x : K) :
    ((g • (⟨m.orbitBarycenter K hK x, m.orbitBarycenter_mem hK hKc x⟩ : K) : K) : E) =
      m.orbitBarycenter K hK x := by
  rw [m.smul_orbitBarycenter hK hKc hcomb g x, hm.smul_eq]

end Barycenter

end OrbitBarycenter

end Mean

/-! ### The Day–Rickert fixed-point theorem and characterizations of amenability -/

section FixedPoint

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Day–Rickert fixed-point theorem** (intrinsic action on `K`). If an amenable topological group
`G` acts jointly continuously on a nonempty compact convex subset `K` of a Hausdorff locally convex
real space `E` preserving binary convex combinations in `E`, then `K` has a `G`-fixed point. -/
theorem Amenable.exists_fixedPoint_subtype [Amenable G] {E : Type v} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {K : Set E} [MulAction G K] [ContinuousSMul G K] (hKne : K.Nonempty)
    (hK : IsCompact K) (hKc : Convex ℝ K)
    (hcomb : ∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      ((g • (⟨a • (y : E) + b • (z : E), hKc y.property z.property ha hb hab⟩ : K) : K) : E) =
        a • ((g • y : K) : E) + b • ((g • z : K) : E)) :
    ∃ x : K, ∀ g : G, g • x = x := by
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  obtain ⟨x₀, hx₀⟩ := hKne
  refine ⟨⟨m.orbitBarycenter K hK ⟨x₀, hx₀⟩, m.orbitBarycenter_mem hK hKc ⟨x₀, hx₀⟩⟩,
    fun g => Subtype.ext (hm.smul_orbitBarycenter hK hKc hcomb g ⟨x₀, hx₀⟩)⟩

/-- **Day–Rickert fixed-point theorem** (ambient `MulAction` leaving `K` invariant). If `G` is
amenable and acts on `E` leaving a nonempty compact convex subset `K` invariant, jointly
continuously on `G × K` and preserving binary convex combinations on `K`, then `K` contains a
`G`-fixed point. -/
theorem Amenable.exists_fixedPoint_of_mapsTo [Amenable G] {E : Type v} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] [MulAction G E] {K : Set E} (hKne : K.Nonempty)
    (hK : IsCompact K) (hKc : Convex ℝ K) (hmaps : ∀ g : G, MapsTo (g • ·) K K)
    (hcont : Continuous fun p : G × K => p.fst • (p.snd : E))
    (hcomb : ∀ (g : G) {y : E}, y ∈ K → ∀ {z : E}, z ∈ K → ∀ {a b : ℝ},
      0 ≤ a → 0 ≤ b → a + b = 1 → g • (a • y + b • z) = a • (g • y) + b • (g • z)) :
    ∃ x ∈ K, ∀ g : G, g • x = x :=
  hKc.exists_fixedPoint_of_subtype MulAction.toEndHom hmaps hcont hcomb fun hcomb' =>
    Amenable.exists_fixedPoint_subtype hKne hK hKc hcomb'

/-- **Day–Rickert fixed-point theorem** (monoid homomorphism into `E →ᵃ[ℝ] E`). Every jointly
continuous affine action of an amenable topological group `G` on a nonempty compact convex subset
`K` of a Hausdorff locally convex real space `E` has a fixed point in `K`. -/
theorem Amenable.exists_fixedPoint_affineMap [Amenable G] {E : Type v} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E} (hKne : K.Nonempty) (hK : IsCompact K)
    (hKc : Convex ℝ K) (π : G →* (E →ᵃ[ℝ] E)) (hmaps : ∀ g : G, MapsTo (π g) K K)
    (hcont : Continuous fun p : G × K => π p.fst (p.snd : E)) :
    ∃ x ∈ K, ∀ g : G, π g x = x :=
  hKc.exists_fixedPoint_affineMap_of_subtype π hmaps hcont fun hcomb =>
    Amenable.exists_fixedPoint_subtype hKne hK hKc hcomb

/-- **Day–Rickert fixed-point theorem** (group homomorphism into `E ≃ᵃ[ℝ] E`). Every jointly
continuous action by affine equivalences of an amenable topological group `G` on a nonempty compact
convex subset `K` of a Hausdorff locally convex real space `E` has a fixed point in `K`. -/
theorem Amenable.exists_fixedPoint_affineEquiv [Amenable G] {E : Type v} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E} (hKne : K.Nonempty) (hK : IsCompact K)
    (hKc : Convex ℝ K) (π : G →* (E ≃ᵃ[ℝ] E)) (hmaps : ∀ g : G, MapsTo (π g) K K)
    (hcont : Continuous fun p : G × K => π p.fst (p.snd : E)) :
    ∃ x ∈ K, ∀ g : G, π g x = x := by
  simpa using Amenable.exists_fixedPoint_affineMap hKne hK hKc
    (AffineEquiv.toAffineMapHom.comp π)
    (fun g x hx => by simpa using hmaps g hx) (by simpa using hcont)

/-- Pointwise action of `UCB.leftTranslationWeakDual` on functions from an index type `ι` into
`WeakDual ℝ (UCB G)`, as a group homomorphism into affine equivalences. -/
private def piLeftTranslationAffineEquiv (ι : Type*) :
    G →* ((ι → WeakDual ℝ (UCB G)) ≃ᵃ[ℝ] (ι → WeakDual ℝ (UCB G))) where
  toFun g :=
    (LinearEquiv.piCongrRight fun _ : ι =>
      (UCB.leftTranslationWeakDual g).toLinearEquiv).toAffineEquiv
  map_one' := by
    ext x i
    simp [← ContinuousLinearEquiv.toLinearEquivMonoidHom_apply]
  map_mul' g h := by
    ext x i
    simp

@[simp]
private theorem piLeftTranslationAffineEquiv_apply {ι : Type*} (g : G)
    (x : ι → WeakDual ℝ (UCB G)) (i : ι) :
    piLeftTranslationAffineEquiv ι g x i = UCB.leftTranslationWeakDual g (x i) := by
  simp [piLeftTranslationAffineEquiv]

/-- **Converse of the Day–Rickert fixed-point theorem.** If every jointly continuous action of `G`
by affine equivalences on a nonempty compact convex subset of a Hausdorff locally convex real space
in `Type (max u v)` has a fixed point, then `G` is amenable. -/
theorem Amenable.of_forall_exists_fixedPoint_affineEquiv
    (hfp : ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
      ∀ (π : G →* (E ≃ᵃ[ℝ] E)), (∀ g : G, MapsTo (π g) K K) →
        (Continuous fun p : G × K => π p.fst (p.snd : E)) → ∃ x ∈ K, ∀ g : G, π g x = x) :
    Amenable G := by
  -- Embed `Mean G` as constant functions `PUnit.{v + 1} → WeakDual ℝ (UCB G)` so the ambient
  -- Hausdorff locally convex real space lives in `Type (max u v)`.
  let lift : Mean G → (PUnit.{v + 1} → WeakDual ℝ (UCB G)) := fun m _ => m.toWeakDual
  have hlift_cont : Continuous lift := continuous_pi fun _ => Mean.continuous_toWeakDual
  let K₀ : Set (PUnit.{v + 1} → WeakDual ℝ (UCB G)) := Set.range lift
  have hK₀_cvx : Convex ℝ K₀ := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ a b ha hb hab
    obtain ⟨k, hk⟩ := Mean.convex_range_toWeakDual ⟨m, rfl⟩ ⟨n, rfl⟩ ha hb hab
    refine ⟨k, funext fun _ => ?_⟩
    exact hk
  have hmaps (g : G) : MapsTo (piLeftTranslationAffineEquiv (G := G) PUnit.{v + 1} g) K₀ K₀ := by
    rintro _ ⟨m, rfl⟩
    refine ⟨g • m, funext fun _ => ?_⟩
    simp [lift]
  have hcont : Continuous fun p : G × K₀ =>
      piLeftTranslationAffineEquiv (G := G) PUnit.{v + 1} p.fst p.snd.val := by
    refine continuous_pi fun i => ?_
    have heval : Continuous
        (fun x : K₀ => (⟨x.val i, by obtain ⟨m, hm⟩ := x.property; exact ⟨m, congr_fun hm i⟩⟩ :
          Set.range (Mean.toWeakDual : Mean G → WeakDual ℝ (UCB G)))) :=
      ((continuous_apply i).comp continuous_subtypeVal).subtype_mk _
    exact Mean.continuous_leftTranslationWeakDual_range_toWeakDual.comp
      (continuous_fst.prodMk (heval.comp continuous_snd))
  obtain ⟨_, ⟨m, rfl⟩, hx⟩ := hfp (PUnit.{v + 1} → WeakDual ℝ (UCB G)) K₀
    (Set.range_nonempty lift) (isCompact_range hlift_cont) hK₀_cvx
    (piLeftTranslationAffineEquiv PUnit.{v + 1}) hmaps hcont
  refine ⟨⟨m, Mean.isLeftInvariant_iff_forall_smul_eq.2 fun g => ?_⟩⟩
  apply Mean.toWeakDual_injective
  have hxg := congr_fun (hx g) PUnit.unit
  simpa [lift] using hxg

/-- If every jointly continuous affine action of `G` on a nonempty compact convex subset of a
Hausdorff locally convex real space in `Type (max u v)` has a fixed point, then `G` is amenable. -/
theorem Amenable.of_forall_exists_fixedPoint_affineMap
    (hfp : ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
      ∀ (π : G →* (E →ᵃ[ℝ] E)), (∀ g : G, MapsTo (π g) K K) →
        (Continuous fun p : G × K => π p.fst (p.snd : E)) → ∃ x ∈ K, ∀ g : G, π g x = x) :
    Amenable G :=
  Amenable.of_forall_exists_fixedPoint_affineEquiv.{u, v} fun E _ _ _ _ _ _ _ K hKne hK hKc π
    hmaps hcont => by
    simpa using hfp E K hKne hK hKc (AffineEquiv.toAffineMapHom.comp π)
      (fun g x hx => by simpa using hmaps g hx) (by simpa using hcont)

/-- If every jointly continuous action of `G` on a nonempty compact convex subset `K` of a Hausdorff
locally convex real space in `Type (max u v)` preserving binary convex combinations in `E` has a
fixed point, then `G` is amenable. -/
theorem Amenable.of_forall_exists_fixedPoint_subtype
    (hfp : ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      (K : Set E) [MulAction G K] [ContinuousSMul G K],
      K.Nonempty → IsCompact K → (hKc : Convex ℝ K) →
      (∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
        ((g • (⟨a • (y : E) + b • (z : E), hKc y.property z.property ha hb hab⟩ : K) : K) : E) =
          a • ((g • y : K) : E) + b • ((g • z : K) : E)) →
      ∃ x : K, ∀ g : G, g • x = x) :
    Amenable G :=
  Amenable.of_forall_exists_fixedPoint_affineMap.{u, v}
    fun E _ _ _ _ _ _ _ K hKne hK hKc π hmaps hcont =>
      hKc.exists_fixedPoint_affineMap_of_subtype π hmaps hcont (hfp E K hKne hK hKc)

/-- **Day–Rickert fixed-point characterization of amenability** (`AffineMap` form, universe
polymorphic in `v`). A topological group `G : Type u` is amenable if and only if every jointly
continuous affine action of `G` on a nonempty compact convex subset of a Hausdorff locally convex
real space `E : Type (max u v)` has a fixed point. -/
theorem amenable_iff_forall_exists_fixedPoint_affineMap :
    Amenable G ↔
      ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
        [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
        (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
        ∀ (π : G →* (E →ᵃ[ℝ] E)), (∀ g : G, MapsTo (π g) K K) →
          (Continuous fun p : G × K => π p.fst (p.snd : E)) → ∃ x ∈ K, ∀ g : G, π g x = x :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hKne hK hKc π hmaps hcont =>
      Amenable.exists_fixedPoint_affineMap hKne hK hKc π hmaps hcont,
    Amenable.of_forall_exists_fixedPoint_affineMap.{u, v}⟩

/-- **Day–Rickert fixed-point characterization of amenability** (`AffineEquiv` form, universe
polymorphic in `v`). A topological group `G : Type u` is amenable if and only if every jointly
continuous action of `G` by affine equivalences on a nonempty compact convex subset of a Hausdorff
locally convex real space `E : Type (max u v)` has a fixed point. -/
theorem amenable_iff_forall_exists_fixedPoint_affineEquiv :
    Amenable G ↔
      ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
        [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
        (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
        ∀ (π : G →* (E ≃ᵃ[ℝ] E)), (∀ g : G, MapsTo (π g) K K) →
          (Continuous fun p : G × K => π p.fst (p.snd : E)) → ∃ x ∈ K, ∀ g : G, π g x = x :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hKne hK hKc π hmaps hcont =>
      Amenable.exists_fixedPoint_affineEquiv hKne hK hKc π hmaps hcont,
    Amenable.of_forall_exists_fixedPoint_affineEquiv.{u, v}⟩

/-- **Day–Rickert fixed-point characterization of amenability** (intrinsic `MulAction G K` form,
universe polymorphic in `v`). A topological group `G : Type u` is amenable if and only if every
jointly continuous action of `G` on a nonempty compact convex subset `K` of a Hausdorff locally
convex real space `E : Type (max u v)` preserving binary convex combinations in `E` has a fixed
point. -/
theorem amenable_iff_forall_exists_fixedPoint_subtype :
    Amenable G ↔
      ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
        [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
        (K : Set E) [MulAction G K] [ContinuousSMul G K],
        K.Nonempty → IsCompact K → (hKc : Convex ℝ K) →
        (∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
          ((g • (⟨a • (y : E) + b • (z : E), hKc y.property z.property ha hb hab⟩ : K) : K) : E) =
            a • ((g • y : K) : E) + b • ((g • z : K) : E)) →
        ∃ x : K, ∀ g : G, g • x = x :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hKne hK hKc hcomb =>
      Amenable.exists_fixedPoint_subtype hKne hK hKc hcomb,
    Amenable.of_forall_exists_fixedPoint_subtype.{u, v}⟩

end FixedPoint

end TauCeti
