/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Pulling back continuous bilinear maps, and their quadratic maps

A continuous linear map `u : W →L[𝕜] V` pulls a continuous bilinear map `B` on `V` back to the
bilinear map `B (u ·) (u ·)` on `W`. This operation is itself continuous and linear in `B`
(`ContinuousLinearMap.pullbackBilinL`), so that it commutes with derivatives of families of
bilinear maps, such as the coordinate expressions of metrics. In particular, pulling back each
value of a continuous family of multilinear maps valued in bilinear maps, along `u` in every
argument, gives a continuous family
(`Continuous.pullbackBilinL_compContinuousMultilinearMap`). Pulling back along a bijection preserves
nondegeneracy (`ContinuousLinearMap.injective_bilinearComp`).

The quadratic map `x ↦ B x x` of a continuous bilinear map is Lipschitz on every ball, with a
constant proportional to the radius: `‖B x x - B y y‖ ≤ ‖B‖ (‖x‖ + ‖y‖) ‖x - y‖`
(`ContinuousLinearMap.norm_apply_apply_sub_apply_apply_le`). This is the quadratic estimate on the
nonlinear terms of an equation that is quadratic in its unknown.

Pulling back along continuous linear equivalences keeps a bilinear map `B₀ : V →L V' →L G`
invertible as a map to the dual (`ContinuousLinearMap.IsInvertible.bilinearComp`), and it
conjugates the comparison operator `B₀⁻¹ ∘ B` of two such maps by the equivalence in the first
slot (`ContinuousLinearMap.inverse_bilinearComp_comp_bilinearComp`). This is how operators built
from a pair of bilinear forms, such as the Morse congruence of a form with a reference form,
transform under a linear change of coordinates.

An invertible bilinear map `B₀ : V →L V →L G` determines adjoints of operators on `V`: the
adjoint `ContinuousLinearMap.pairingAdjoint B₀ X` is characterized by
`B₀ (adj X w) w' = B₀ w (X w')` (`ContinuousLinearMap.IsInvertible.pairingAdjoint_apply`). It
reverses products, fixes the identity, and tends to the identity as `B₀` stays near an
invertible map and `X` tends to the identity. On Banach spaces the comparison operator
`B₀⁻¹ ∘ B` also tends to the identity as both maps tend to the same invertible map
(`ContinuousLinearMap.IsInvertible.tendsto_inverse_comp`).
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V W G : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pulling a continuous bilinear map back along a continuous linear map `u`,
`B ↦ B (u ·) (u ·)`, as a continuous linear map in `B`. -/
def pullbackBilinL (u : W →L[𝕜] V) : (V →L[𝕜] V →L[𝕜] G) →L[𝕜] W →L[𝕜] W →L[𝕜] G :=
  (compL 𝕜 W (V →L[𝕜] G) (W →L[𝕜] G) ((compL 𝕜 W V G).flip u)).comp
    ((compL 𝕜 W V (V →L[𝕜] G)).flip u)

@[simp]
theorem pullbackBilinL_apply (u : W →L[𝕜] V) (B : V →L[𝕜] V →L[𝕜] G) (v w : W) :
    pullbackBilinL u B v w = B (u v) (u w) :=
  (rfl)

/-- `pullbackBilinL u` precomposes a bilinear map with `u`, and then each of its values with `u`.
In this form it is visibly built from `u` by continuous linear operations, so that, for instance,
its regularity in `u` follows from that of the precomposition maps `compL`. -/
theorem pullbackBilinL_eq_comp (u : W →L[𝕜] V) :
    pullbackBilinL (G := G) u =
      (compL 𝕜 W (V →L[𝕜] G) (W →L[𝕜] G) ((compL 𝕜 W V G).flip u)).comp
        ((compL 𝕜 W V (V →L[𝕜] G)).flip u) :=
  (rfl)

/-- The quadratic map `x ↦ B x x` of a continuous bilinear map `B` satisfies
`‖B x x - B y y‖ ≤ ‖B‖ (‖x‖ + ‖y‖) ‖x - y‖`. -/
theorem norm_apply_apply_sub_apply_apply_le (B : V →L[𝕜] V →L[𝕜] G) (x y : V) :
    ‖B x x - B y y‖ ≤ ‖B‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have h : B x x - B y y = B x (x - y) + B (x - y) y := by
    simp only [map_sub, sub_apply]
    abel
  rw [h]
  calc ‖B x (x - y) + B (x - y) y‖ ≤ ‖B‖ * ‖x‖ * ‖x - y‖ + ‖B‖ * ‖x - y‖ * ‖y‖ :=
        (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))
    _ = ‖B‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

/-- Pulling a nondegenerate bilinear map back along a bijective continuous linear map keeps it
nondegenerate. -/
theorem injective_bilinearComp {B : V →L[𝕜] V →L[𝕜] G} (hB : Function.Injective B)
    {u : W →L[𝕜] V} (hu : Function.Bijective u) : Function.Injective (B.bilinearComp u u) := by
  intro w w' hww'
  refine hu.1 (hB ?_)
  ext v
  obtain ⟨v, rfl⟩ := hu.2 v
  exact congrArg (fun φ ↦ φ v) hww'

section Invertible

variable {V' W' : Type*} [SeminormedAddCommGroup V'] [NormedSpace 𝕜 V']
  [SeminormedAddCommGroup W'] [NormedSpace 𝕜 W']

/-- Pulling a bilinear map that is invertible, as a map to the space of linear maps on its
second argument, back along continuous linear equivalences in both arguments keeps it
invertible. -/
theorem IsInvertible.bilinearComp {B₀ : V →L[𝕜] V' →L[𝕜] G} (hB₀ : B₀.IsInvertible)
    (e₁ : W ≃L[𝕜] V) (e₂ : W' ≃L[𝕜] V') :
    (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).IsInvertible := by
  refine .of_inverse (g := (e₁.symm : V →L[𝕜] W) ∘L B₀.inverse ∘L
    (compL 𝕜 V' W' G).flip (e₂.symm : V' →L[𝕜] W')) ?_ ?_
  · ext φ x
    simp [hB₀.self_apply_inverse]
  · ext x
    have h : (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V') x).comp
        (e₂.symm : V' →L[𝕜] W') = B₀ (e₁ x) := by
      ext y
      simp
    simp [h, hB₀.inverse_apply_self]

/-- Pulling two bilinear maps back along continuous linear equivalences conjugates their
comparison operator `B₀⁻¹ ∘ B` by the equivalence `e₁` in the first argument. -/
theorem inverse_bilinearComp_comp_bilinearComp {B₀ : V →L[𝕜] V' →L[𝕜] G}
    (hB₀ : B₀.IsInvertible) (B : V →L[𝕜] V' →L[𝕜] G) (e₁ : W ≃L[𝕜] V) (e₂ : W' ≃L[𝕜] V') :
    (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).inverse ∘L
        B.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V') =
      (e₁.symm : V →L[𝕜] W) ∘L (B₀.inverse ∘L B) ∘L (e₁ : W →L[𝕜] V) := by
  ext w
  rw [comp_apply, (hB₀.bilinearComp e₁ e₂).inverse_apply_eq]
  ext w'
  simp [hB₀.self_apply_inverse]

end Invertible

section PairingAdjoint

open Filter Topology

/-- The adjoint of an operator `X` on `V` for the pairing `B₀`, `B₀⁻¹ ∘ (· ∘ X) ∘ B₀`. When
`B₀` is invertible it is characterized by `B₀ (adj X w) w' = B₀ w (X w')`
(`ContinuousLinearMap.IsInvertible.pairingAdjoint_apply`). -/
def pairingAdjoint (B₀ : V →L[𝕜] V →L[𝕜] G) (X : V →L[𝕜] V) : V →L[𝕜] V :=
  B₀.inverse ∘L ((compL 𝕜 V V G).flip X ∘L B₀)

/-- The adjoint for the pairing `B₀` is `B₀⁻¹ ∘ (· ∘ X) ∘ B₀`. -/
theorem pairingAdjoint_def (B₀ : V →L[𝕜] V →L[𝕜] G) (X : V →L[𝕜] V) :
    pairingAdjoint B₀ X = B₀.inverse ∘L ((compL 𝕜 V V G).flip X ∘L B₀) := by
  rw [pairingAdjoint]

variable {B₀ : V →L[𝕜] V →L[𝕜] G}

/-- The defining property of the adjoint for an invertible pairing. -/
@[simp] theorem IsInvertible.pairingAdjoint_apply (hB₀ : B₀.IsInvertible) (X : V →L[𝕜] V)
    (w w' : V) :
    B₀ (pairingAdjoint B₀ X w) w' = B₀ w (X w') := by
  simp [pairingAdjoint, hB₀.self_apply_inverse]

/-- Operators are determined by their pairings against an invertible bilinear map. -/
theorem IsInvertible.ext_of_pairing (hB₀ : B₀.IsInvertible) {X Y : V →L[𝕜] V}
    (h : ∀ w w', B₀ (X w) w' = B₀ (Y w) w') : X = Y :=
  ext fun w ↦ hB₀.bijective.injective (ext (h w))

/-- The adjoint for an invertible pairing reverses products. -/
theorem IsInvertible.pairingAdjoint_mul (hB₀ : B₀.IsInvertible) (X Y : V →L[𝕜] V) :
    pairingAdjoint B₀ (X * Y) = pairingAdjoint B₀ Y * pairingAdjoint B₀ X :=
  hB₀.ext_of_pairing fun w w' ↦ by
    simp only [hB₀.pairingAdjoint_apply, mul_apply_eq_comp]

/-- The adjoint of the identity for an invertible pairing is the identity. -/
@[simp] theorem IsInvertible.pairingAdjoint_one (hB₀ : B₀.IsInvertible) :
    pairingAdjoint B₀ (1 : V →L[𝕜] V) = 1 :=
  hB₀.ext_of_pairing fun w w' ↦ by simp [hB₀.pairingAdjoint_apply]

end PairingAdjoint

section Tendsto

open Filter Topology

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The comparison operator `e₀⁻¹ ∘ e` tends to the identity as both maps tend to the same
invertible map. -/
theorem IsInvertible.tendsto_inverse_comp {e : E →L[𝕜] F} (he : e.IsInvertible) :
    Tendsto (fun p : (E →L[𝕜] F) × (E →L[𝕜] F) ↦ p.1.inverse ∘L p.2) (𝓝 (e, e)) (𝓝 1) := by
  have h₁ : ContinuousAt (fun p : (E →L[𝕜] F) × (E →L[𝕜] F) ↦ p.1.inverse) (e, e) :=
    ContinuousAt.comp (f := Prod.fst) (x := (e, e))
      (he.contDiffAt_map_inverse (n := 0)).continuousAt continuousAt_fst
  have h := h₁.clm_comp continuousAt_snd
  simpa only [he.inverse_comp_self, ← one_def] using h.tendsto

/-- The adjoint of `X` for the pairing `B₀` tends to the identity as `B₀` tends to an
invertible pairing and `X` tends to the identity. -/
theorem IsInvertible.tendsto_pairingAdjoint {B₀ : E →L[𝕜] E →L[𝕜] H} (hB₀ : B₀.IsInvertible) :
    Tendsto (fun q : (E →L[𝕜] E →L[𝕜] H) × (E →L[𝕜] E) ↦ pairingAdjoint q.1 q.2)
      (𝓝 (B₀, 1)) (𝓝 1) := by
  have h₁ : ContinuousAt (fun q : (E →L[𝕜] E →L[𝕜] H) × (E →L[𝕜] E) ↦ q.1.inverse) (B₀, 1) :=
    ContinuousAt.comp (f := Prod.fst) (x := (B₀, 1))
      (hB₀.contDiffAt_map_inverse (n := 0)).continuousAt continuousAt_fst
  have h₂ : ContinuousAt (fun q : (E →L[𝕜] E →L[𝕜] H) × (E →L[𝕜] E) ↦
      (compL 𝕜 E E H).flip q.2) (B₀, 1) :=
    ((compL 𝕜 E E H).flip).continuous.continuousAt.comp continuousAt_snd
  have h : ContinuousAt (fun q : (E →L[𝕜] E →L[𝕜] H) × (E →L[𝕜] E) ↦
      pairingAdjoint q.1 q.2) (B₀, 1) :=
    h₁.clm_comp (h₂.clm_comp continuousAt_fst)
  simpa only [hB₀.pairingAdjoint_one] using h.tendsto

end Tendsto

end ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V W G : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pulling back each value of a continuous family `f` of multilinear maps valued in bilinear
maps, both in its arguments and in its values, along a continuous linear map `u` gives a
continuous family. Applied to iterated derivatives of a family of bilinear forms, this is the
pullback of all their coordinate derivatives along `u`. -/
theorem Continuous.pullbackBilinL_compContinuousMultilinearMap {X ι : Type*} [TopologicalSpace X]
    {f : X → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V) (V →L[𝕜] V →L[𝕜] G)} (hf : Continuous f)
    (u : W →L[𝕜] V) :
    Continuous fun x ↦ (ContinuousLinearMap.pullbackBilinL u).compContinuousMultilinearMap
      ((f x).compContinuousLinearMap fun _ ↦ u) :=
  ((ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : ι ↦ W) _ _
    (ContinuousLinearMap.pullbackBilinL u)).continuous.comp
    ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ u).continuous.comp hf) :)
