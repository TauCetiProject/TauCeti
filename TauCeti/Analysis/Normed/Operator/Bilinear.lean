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
# Continuous bilinear maps

A family of continuous bilinear maps gives a continuous bilinear map into the product
(`ContinuousLinearMap.piBilin`), with coordinatewise evaluation.

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

For a continuous map of two variables, semilinear in each argument with respect to isometric
scalar homomorphisms (for instance sesquilinear), the diagonal sum `∑ i ∈ s, A (v i) (v i)` along
vectors of norm at most one, such as an orthonormal family, is bounded by `#s * ‖A‖`
(`ContinuousLinearMap.norm_sum_apply_apply_le`), and every value satisfies the Young-type bound
`‖B u v‖ ≤ ‖B‖ * ((c⁻¹ * ‖u‖ ^ 2 + c * ‖v‖ ^ 2) / 2)` for `c > 0`
(`ContinuousLinearMap.norm_apply_apply_le_mul_add_sq`).

Pulling back along continuous linear equivalences keeps a bilinear map `B₀ : V →L V' →L G`
invertible as a map to the dual (`ContinuousLinearMap.IsInvertible.bilinearComp`), and
conversely (`ContinuousLinearMap.isInvertible_bilinearComp_iff`). It conjugates the comparison
operator `B₀⁻¹ ∘ B` of two such maps by the equivalence in the first slot
(`ContinuousLinearMap.inverse_bilinearComp_comp_bilinearComp`). This is how operators built from a
pair of bilinear forms, such as the Morse congruence of a form with a reference form, transform
under a linear change of coordinates.

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

/-- A family of continuous bilinear maps is a continuous bilinear map into the product. -/
def piBilin {ι : Type*} {G : ι → Type*}
    [∀ i, SeminormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
    (B : ∀ i, V →L[𝕜] W →L[𝕜] G i) : V →L[𝕜] W →L[𝕜] ∀ i, G i :=
  (ContinuousLinearMap.piEquivL 𝕜 W G).toContinuousLinearMap.comp (ContinuousLinearMap.pi B)

@[simp]
theorem piBilin_apply {ι : Type*} {G : ι → Type*}
    [∀ i, SeminormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
    (B : ∀ i, V →L[𝕜] W →L[𝕜] G i) (x : V) (y : W) (i : ι) :
    piBilin B x y i = B i x y :=
  (rfl)

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

/-- A bilinear map is invertible, as a map to the space of linear maps on its second argument,
exactly when its pullback along continuous linear equivalences in both arguments is. -/
@[simp]
theorem isInvertible_bilinearComp_iff {B₀ : V →L[𝕜] V' →L[𝕜] G} (e₁ : W ≃L[𝕜] V)
    (e₂ : W' ≃L[𝕜] V') :
    (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).IsInvertible ↔ B₀.IsInvertible := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.bilinearComp e₁ e₂⟩
  have hB₀ : B₀ = (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).bilinearComp
      (e₁.symm : V →L[𝕜] W) (e₂.symm : V' →L[𝕜] W') := by
    ext x y
    simp
  rw [hB₀]
  exact h.bilinearComp e₁.symm e₂.symm

/-- Pulling two bilinear maps back along continuous linear equivalences conjugates their
comparison operator `B₀⁻¹ ∘ B` by the equivalence `e₁` in the first argument. If `B₀` is not
invertible, both sides vanish. -/
theorem inverse_bilinearComp_comp_bilinearComp (B₀ B : V →L[𝕜] V' →L[𝕜] G) (e₁ : W ≃L[𝕜] V)
    (e₂ : W' ≃L[𝕜] V') :
    (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).inverse ∘L
        B.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V') =
      (e₁.symm : V →L[𝕜] W) ∘L (B₀.inverse ∘L B) ∘L (e₁ : W →L[𝕜] V) := by
  by_cases hB₀ : B₀.IsInvertible
  swap
  · rw [inverse_of_not_isInvertible (by rwa [isInvertible_bilinearComp_iff]),
      inverse_of_not_isInvertible hB₀]
    simp
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

namespace ContinuousLinearMap

section Semilinear₂

variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NontriviallyNormedField 𝕜₃] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F] [SeminormedAddCommGroup G] [NormedSpace 𝕜₃ G]
  {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomIsometric σ₁₃]

/-- The diagonal sum `∑ i ∈ s, A (v i) (v i)` of a continuous map `A`, semilinear in each argument
with respect to isometric scalar homomorphisms (for instance sesquilinear), along vectors of norm
at most one is bounded by `#s * ‖A‖`. Along an orthonormal basis this bounds the diagonal sum by
the dimension times `‖A‖`. -/
theorem norm_sum_apply_apply_le {τ : 𝕜 →+* 𝕜₃} [RingHomIsometric τ] {ι : Type*} (s : Finset ι)
    (A : E →SL[σ₁₃] E →SL[τ] G) {v : ι → E} (hv : ∀ i ∈ s, ‖v i‖ ≤ 1) :
    ‖∑ i ∈ s, A (v i) (v i)‖ ≤ s.card * ‖A‖ := by
  refine (norm_sum_le _ _).trans <|
    (Finset.sum_le_card_nsmul _ _ _ fun i hi ↦ ?_).trans_eq (nsmul_eq_mul _ _)
  simpa only [mul_one] using A.le_of_opNorm₂_le_of_le le_rfl (hv i hi) (hv i hi)

/-- A Young-type bound for a continuous map `B` of two variables, semilinear in each argument with
respect to isometric scalar homomorphisms: for every `c > 0`,
`‖B u v‖ ≤ ‖B‖ * ((c⁻¹ * ‖u‖ ^ 2 + c * ‖v‖ ^ 2) / 2)`. -/
theorem norm_apply_apply_le_mul_add_sq {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomIsometric σ₂₃]
    (B : E →SL[σ₁₃] F →SL[σ₂₃] G) {c : ℝ} (hc : 0 < c) (u : E) (v : F) :
    ‖B u v‖ ≤ ‖B‖ * ((c⁻¹ * ‖u‖ ^ 2 + c * ‖v‖ ^ 2) / 2) := by
  refine (B.le_opNorm₂ _ _).trans ?_
  rw [mul_assoc]
  gcongr
  have h := two_mul_le_add_mul_sq (a := ‖u‖) (b := ‖v‖) (inv_pos.2 hc)
  rw [inv_inv] at h
  linarith

end Semilinear₂

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
