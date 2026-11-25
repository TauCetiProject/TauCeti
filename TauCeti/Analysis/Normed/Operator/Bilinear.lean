/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pairing
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
nondegeneracy (`ContinuousLinearMap.injective_bilinearComp`). Pulling back a continuous family
of bilinear maps along two fixed maps is also a continuous linear operation
(`ContinuousLinearMap.bilinearCompL`), giving `ContinuousOn.bilinearComp` and
`Continuous.bilinearComp` even when all spaces are only seminormed.

The quadratic map `x ↦ B x x` of a continuous bilinear map is Lipschitz on every ball, with a
constant proportional to the radius: `‖B x x - B y y‖ ≤ ‖B‖ (‖x‖ + ‖y‖) ‖x - y‖`
(`ContinuousLinearMap.norm_apply_apply_sub_apply_apply_le`). This is the quadratic estimate on the
nonlinear terms of an equation that is quadratic in its unknown.

For a continuous map of two variables, semilinear in each argument with respect to isometric
scalar homomorphisms (for instance sesquilinear), the sum `∑ i ∈ s, A (u i) (v i)` is bounded by
`‖A‖ * ∑ i ∈ s, ‖u i‖ * ‖v i‖` (`ContinuousLinearMap.norm_sum_apply_apply_le`); along a finite
orthonormal basis taken twice, this is the dimension times `‖A‖`. Every value satisfies the
Young-type bound `‖B u v‖ ≤ ‖B‖ * ((c⁻¹ * ‖u‖ ^ 2 + c * ‖v‖ ^ 2) / 2)` for `c > 0`
(`ContinuousLinearMap.norm_apply_apply_le_mul_add_sq`).

For a continuous bilinear map `B : G × V → H`, the expression `B(A ∘ D, v)` is linear in each of
`A`, `D` and `v`; `ContinuousLinearMap.compPrecompL E F B` is the continuous bilinear map
`(D, v) ↦ (A ↦ B(A ∘ D, v))` that treats `A` as a separate factor
(`ContinuousLinearMap.compPrecompL_apply`).

Composing a bilinear map `f` with linear maps `g` and `h` gives a bilinear map of norm at most
`‖f‖ ‖g‖ ‖h‖` (`ContinuousLinearMap.norm_bilinearComp_le`), and the bilinear map
`(h, k) ↦ B h k • c` has norm at most `‖c‖ ‖B‖`
(`ContinuousLinearMap.norm_smulRightL_flip_comp_le`).

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

On normable spaces over nontrivially normed fields, with isometric scalar homomorphisms `σ₁₃`,
`σ₂₃` and `σ₂₃` surjective, the flip of a continuous pairing `μ : E →SL[σ₁₃] F →SL[σ₂₃] H` is
Mathlib's flip: `μ.toLinearMap.pairingFlip hμ = μ.flip`, where `hμ` is a proof of joint continuity
of `μ`, that is, continuity of `Function.uncurry fun x y ↦ μ x y`, which callers supply
explicitly (`ContinuousLinearMap.pairingFlip_eq_flip`). Forgetting continuity via
`ContinuousLinearMap.toLinearMap₁₂` commutes with `flip` and `bilinearComp`
(`ContinuousLinearMap.toLinearMap₁₂_flip`, `ContinuousLinearMap.toLinearMap₁₂_bilinearComp`).
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

section BilinearComp

variable {V' W' : Type*} [SeminormedAddCommGroup V'] [NormedSpace 𝕜 V']
  [SeminormedAddCommGroup W'] [NormedSpace 𝕜 W']

/-- Pull back a bilinear map along `e` in the first slot and `f` in the second slot, as a
continuous linear map in the bilinear map. -/
def bilinearCompL (e : V' →L[𝕜] V) (f : W' →L[𝕜] W) :
    (V →L[𝕜] W →L[𝕜] G) →L[𝕜] V' →L[𝕜] W' →L[𝕜] G :=
  (compL 𝕜 V' (W →L[𝕜] G) (W' →L[𝕜] G) ((compL 𝕜 W' W G).flip f)).comp
    ((compL 𝕜 V' V (W →L[𝕜] G)).flip e)

/-- The bundled pullback acts by precomposition in both slots. -/
@[simp]
theorem bilinearCompL_apply (e : V' →L[𝕜] V) (f : W' →L[𝕜] W)
    (B : V →L[𝕜] W →L[𝕜] G) : bilinearCompL e f B = B.bilinearComp e f := by
  ext v w
  simp only [bilinearCompL, comp_apply, compL_apply, flip_apply, bilinearComp_apply]

end BilinearComp

section CompPrecompL

variable {E F H : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

variable (E F) in
/-- For a continuous bilinear map `B : G × V → H`, the continuous bilinear map
`(D, v) ↦ (A ↦ B.precompL E (A ∘L D) v)`. It writes the expression `B(A ∘ D, v)`, which is linear
in each of `A`, `D` and `v`, as `compPrecompL E F B D v` applied to `A`, so that `A` can be
treated as one factor of a product and `(D, v)` as the other. In the chain rule
`D B(g ∘ u, v) = B(Dg(u) ∘ Du, v) + B(g ∘ u, Dv)` this separates `Dg(u)` from `Du` and `v`. -/
def compPrecompL (B : G →L[𝕜] V →L[𝕜] H) :
    (E →L[𝕜] F) →L[𝕜] V →L[𝕜] (F →L[𝕜] G) →L[𝕜] E →L[𝕜] H :=
  (((compL 𝕜 (F →L[𝕜] G) (E →L[𝕜] G) (E →L[𝕜] H)).comp (B.precompL E).flip).flip).comp
    (compL 𝕜 E F G).flip

@[simp]
theorem compPrecompL_apply (B : G →L[𝕜] V →L[𝕜] H) (D : E →L[𝕜] F) (v : V)
    (A : F →L[𝕜] G) : compPrecompL E F B D v A = B.precompL E (A.comp D) v :=
  (rfl)

end CompPrecompL

/-- Pulling a continuous bilinear map back along a continuous linear map `u`,
`B ↦ B (u ·) (u ·)`, as a continuous linear map in `B`. -/
def pullbackBilinL (u : W →L[𝕜] V) : (V →L[𝕜] V →L[𝕜] G) →L[𝕜] W →L[𝕜] W →L[𝕜] G :=
  bilinearCompL u u

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

section PairingFlip

variable {𝕜₂ 𝕜₃ E F H : Type*} [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  {σ₁₃ : 𝕜 →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]
  [RingHomSurjective σ₂₃]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsNormableSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F] [IsNormableSpace 𝕜₂ F]
  [AddCommGroup H] [Module 𝕜₃ H] [TopologicalSpace H] [IsNormableSpace 𝕜₃ H]

/-- On normable spaces, when both scalar homomorphisms are isometric and the second is
surjective, the flip of a continuous pairing `μ` is Mathlib's flip:
`μ.toLinearMap.pairingFlip hμ = μ.flip`, where the caller supplies `hμ`, a proof of joint
continuity of `μ` (continuity of the uncurried pairing `Function.uncurry fun x y ↦ μ x y`). The
topological additive group structures of `F` and `H` used by `LinearMap.pairingFlip`, by
Mathlib's flip and by the topology of `F →SL[σ₂₃] H` come from their normability
(`PolynormableSpace.isTopologicalAddGroup`). -/
@[simp]
theorem pairingFlip_eq_flip
    (μ : haveI := PolynormableSpace.isTopologicalAddGroup 𝕜₃ H; E →SL[σ₁₃] F →SL[σ₂₃] H)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    haveI := PolynormableSpace.isTopologicalAddGroup 𝕜₂ F
    haveI := PolynormableSpace.isTopologicalAddGroup 𝕜₃ H
    μ.toLinearMap.pairingFlip hμ = μ.flip := by
  have := PolynormableSpace.isTopologicalAddGroup 𝕜₂ F
  have := PolynormableSpace.isTopologicalAddGroup 𝕜₃ H
  ext
  rw [LinearMap.pairingFlip_apply, coe_coe, flip_apply]

end PairingFlip

end ContinuousLinearMap

namespace ContinuousLinearMap

section Semilinear₂

variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NontriviallyNormedField 𝕜₃] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F] [SeminormedAddCommGroup G] [NormedSpace 𝕜₃ G]
  {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomIsometric σ₁₃]

/-- The sum `∑ i ∈ s, A (u i) (v i)` of a continuous map `A`, semilinear in each argument with
respect to isometric scalar homomorphisms (for instance sesquilinear), is bounded by
`‖A‖ * ∑ i ∈ s, ‖u i‖ * ‖v i‖`. When `u = v` is a finite orthonormal basis and `s` indexes the
whole basis, the bound is the dimension times `‖A‖`. -/
theorem norm_sum_apply_apply_le {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomIsometric σ₂₃] {ι : Type*}
    (s : Finset ι) (A : E →SL[σ₁₃] F →SL[σ₂₃] G) (u : ι → E) (v : ι → F) :
    ‖∑ i ∈ s, A (u i) (v i)‖ ≤ ‖A‖ * ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
  rw [Finset.mul_sum]
  exact norm_sum_le_of_le s fun i _ ↦ (A.le_opNorm₂ (u i) (v i)).trans_eq (mul_assoc _ _ _)

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

section Comp

variable {𝕜 E E' E'' F F' G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The operator norm of a bilinear map composed with two linear maps is at most the product of
the three operator norms. -/
theorem norm_bilinearComp_le (f : E →L[𝕜] F →L[𝕜] G) (g : E' →L[𝕜] E) (h : F' →L[𝕜] F) :
    ‖f.bilinearComp g h‖ ≤ ‖f‖ * ‖g‖ * ‖h‖ :=
  (f.bilinearComp g h).opNorm_le_bound₂ (by positivity) fun x y => by
    rw [bilinearComp_apply]
    calc ‖f (g x) (h y)‖ ≤ ‖f‖ * ‖g x‖ * ‖h y‖ := f.le_opNorm₂ _ _
      _ ≤ ‖f‖ * (‖g‖ * ‖x‖) * (‖h‖ * ‖y‖) := by
        gcongr
        exacts [g.le_opNorm x, h.le_opNorm y]
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ‖x‖ * ‖y‖ := by ring

/-- The bilinear map `(h, k) ↦ B h k • c` has norm at most `‖c‖ ‖B‖`. -/
theorem norm_smulRightL_flip_comp_le (c : H) (B : E →L[𝕜] StrongDual 𝕜 E'') :
    ‖((StrongDual.smulRightL 𝕜 E'' H).flip c).comp B‖ ≤ ‖c‖ * ‖B‖ := by
  refine (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (le_opNorm _ c).trans (mul_le_of_le_one_left (norm_nonneg _) ?_)
  rw [opNorm_flip]
  exact norm_smulRightL_le

end Comp

section ToLinearMap₁₂Flip

variable {𝕜 𝕜₂ 𝕜₃ : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NontriviallyNormedField 𝕜₃] {σ₁₃ : 𝕜 →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}
  [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]
  {E F G : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsNormableSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F] [IsNormableSpace 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace G] [IsNormableSpace 𝕜₃ G]
  [IsTopologicalAddGroup G]

/-- Forgetting continuity commutes with transposing the arguments. -/
@[simp]
theorem toLinearMap₁₂_flip (L : E →SL[σ₁₃] F →SL[σ₂₃] G) :
    toLinearMap₁₂ L.flip = (toLinearMap₁₂ L).flip :=
  LinearMap.ext₂ fun _ _ ↦ by
    simp only [toLinearMap₁₂_apply_apply_apply, LinearMap.flip_apply, flip_apply]

end ToLinearMap₁₂Flip

section ToLinearMap₁₂BilinearComp

variable {𝕜 𝕜₂ 𝕜₃ 𝕜₁' 𝕜₂' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NontriviallyNormedField 𝕜₃] [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
  {σ₁₃ : 𝕜 →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁' : 𝕜₁' →+* 𝕜} {σ₁₃' : 𝕜₁' →+* 𝕜₃}
  {σ₂' : 𝕜₂' →+* 𝕜₂} {σ₂₃' : 𝕜₂' →+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃']
  [RingHomCompTriple σ₂' σ₂₃ σ₂₃'] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃']
  [RingHomIsometric σ₂₃']
  {E F G E' F' : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F] [IsNormableSpace 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace G] [IsNormableSpace 𝕜₃ G]
  [IsTopologicalAddGroup G]
  [AddCommGroup E'] [Module 𝕜₁' E'] [TopologicalSpace E'] [IsNormableSpace 𝕜₁' E']
  [AddCommGroup F'] [Module 𝕜₂' F'] [TopologicalSpace F'] [IsNormableSpace 𝕜₂' F']

/-- Forgetting continuity commutes with precomposition in both arguments: the continuous pullback
`L.bilinearComp f g` becomes the algebraic pullback `(L.comp f).compl₂ g`. For linear maps this is
`L.compl₁₂ f g`, by definition of `LinearMap.compl₁₂`. -/
@[simp]
theorem toLinearMap₁₂_bilinearComp (L : E →SL[σ₁₃] F →SL[σ₂₃] G) (f : E' →SL[σ₁'] E)
    (g : F' →SL[σ₂'] F) :
    toLinearMap₁₂ (L.bilinearComp f g) =
      ((toLinearMap₁₂ L).comp (f : E' →ₛₗ[σ₁'] E)).compl₂ (g : F' →ₛₗ[σ₂'] F) :=
  LinearMap.ext₂ fun _ _ ↦ by
    simp only [toLinearMap₁₂_apply_apply_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      bilinearComp_apply, coe_coe]

end ToLinearMap₁₂BilinearComp

end ContinuousLinearMap

section BilinearComp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X V W F G F' : Type*} [TopologicalSpace X]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {c : X → V →L[𝕜] W →L[𝕜] F'}

/-- Pulling back a continuous family of bilinear maps along fixed trial maps preserves
continuity on a set. All spaces need only seminorms. -/
theorem ContinuousOn.bilinearComp {s : Set X} (hc : ContinuousOn c s)
    (e : F →L[𝕜] V) (f : G →L[𝕜] W) :
    ContinuousOn (fun r ↦ (c r).bilinearComp e f) s := by
  simpa only [Function.comp_def, ContinuousLinearMap.bilinearCompL_apply] using
    (ContinuousLinearMap.bilinearCompL (G := F') e f).continuous.comp_continuousOn hc

/-- Pulling back a continuous family of bilinear maps along fixed trial maps preserves
continuity. All spaces need only seminorms. -/
theorem Continuous.bilinearComp (hc : Continuous c)
    (e : F →L[𝕜] V) (f : G →L[𝕜] W) :
    Continuous (fun r ↦ (c r).bilinearComp e f) :=
  continuousOn_univ.mp (hc.continuousOn.bilinearComp e f)

end BilinearComp

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
