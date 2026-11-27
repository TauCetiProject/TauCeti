/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Topology.MetricSpace.Polish
public import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.InnerProductSpace.Continuous
import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.Topology.Separation.Hausdorff

/-!
# The unitary group in the strong operator topology

For a complete real or complex inner product space `H` over `𝕜`, `TauCeti.StrongUnitary 𝕜 H` is a
type synonym of `unitary (H →L[𝕜] H)` equipped with the strong operator topology, defined as the
topology induced via `ContinuousLinearMap.toPointwiseConvergenceCLM` from `H →Lₚₜ[𝕜] H`. Keeping a
separate type leaves Mathlib's operator-norm topology on `unitary (H →L[𝕜] H)` intact (the norm
topology is strictly finer whenever `H` is infinite-dimensional).

On unitary operators, the squared-norm identity
`‖u ξ - v ξ‖ ^ 2 = 2 * ‖ξ‖ ^ 2 - 2 * RCLike.re ⟪u ξ, v ξ⟫_𝕜`
implies that the strong and weak operator topologies coincide: a filter converges strongly in
`StrongUnitary 𝕜 H` if and only if all matrix coefficients `⟪ξ, u η⟫_𝕜` converge. Joint continuity
of evaluation `(u, ξ) ↦ u ξ` makes multiplication jointly continuous, and continuity of the adjoint
in `H →WOT[𝕜] H` makes inversion continuous; thus `StrongUnitary 𝕜 H` is a Hausdorff topological
group whose action on `H` is jointly continuous.

When `H` is separable with dense sequence `d : ℕ → H`, the strong* evaluation map
`u ↦ (fun n => u (d n), fun n => u⁻¹ (d n))` embeds `StrongUnitary 𝕜 H` as the closed subset of
`(ℕ → H) × (ℕ → H)` cut out by isometricity on `d` and the adjoint relation
`⟪u (d m), d n⟫_𝕜 = ⟪d m, u⁻¹ (d n)⟫_𝕜`, making `StrongUnitary 𝕜 H` a `PolishSpace`.

## Main definitions and results

* `TauCeti.StrongUnitary 𝕜 H`: unitary operators on `H` with the strong operator topology, carrying
  `Group`, `IsTopologicalGroup`, `T2Space`, `LinearIsometryClass`, `ContinuousEval`, scalar actions
  of `unitary 𝕜` and (for `𝕜 = ℂ`) `Circle`, and `[SeparableSpace H] → PolishSpace`.
* `TauCeti.StrongUnitary.tendsto_iff_forall_inner_tendsto` and
  `TauCeti.StrongUnitary.isEmbedding_toWOT`: strong and weak operator topologies agree on unitaries.
* `TauCeti.StrongUnitary.tendsto_iff_forall_tendsto_of_dense`: strong convergence of unitaries is
  tested on any dense subset of `H`.
* `TauCeti.StrongUnitary.unitaryEquivStrongUnitary` and
  `TauCeti.StrongUnitary.circleEquivStrongUnitary`: topological group isomorphisms identifying the
  one-dimensional strong unitary group `StrongUnitary 𝕜 𝕜` with `unitary 𝕜` and `StrongUnitary ℂ ℂ`
  with `Circle`.

## References

* D. P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs 134, AMS,
  2007, Lemmas D.37 and D.42.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, §9.B(6).
-/

public noncomputable section

open Filter Set Topology TopologicalSpace
open scoped InnerProductSpace ComplexConjugate

namespace TauCeti

/-- The unitary group `U(H)_s` of a complete real or complex inner product space `H`, equipped with
the strong operator topology (the topology of pointwise convergence induced via
`ContinuousLinearMap.toPointwiseConvergenceCLM`).

This is a type synonym of `unitary (H →L[𝕜] H)`, leaving the operator-norm topology on
`unitary (H →L[𝕜] H)` unchanged. -/
structure StrongUnitary (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] where
  /-- Equip a unitary operator with the strong operator topology. -/
  ofUnitary ::
  /-- The underlying element of `unitary (H →L[𝕜] H)`. -/
  toUnitary : unitary (H →L[𝕜] H)

namespace StrongUnitary

section General

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem toUnitary_injective : Function.Injective (toUnitary (𝕜 := 𝕜) (H := H)) :=
  fun ⟨_⟩ ⟨_⟩ h => congrArg ofUnitary h

@[simp]
theorem ofUnitary_toUnitary (u : StrongUnitary 𝕜 H) : ofUnitary u.toUnitary = u :=
  (rfl)

@[simp]
theorem toUnitary_ofUnitary (u : unitary (H →L[𝕜] H)) : (ofUnitary u).toUnitary = u :=
  (rfl)

/-! ### Group and operator structure -/

instance : One (StrongUnitary 𝕜 H) := ⟨⟨1⟩⟩
instance : Mul (StrongUnitary 𝕜 H) := ⟨fun u v => ⟨u.toUnitary * v.toUnitary⟩⟩
instance : Inv (StrongUnitary 𝕜 H) := ⟨fun u => ⟨u.toUnitary⁻¹⟩⟩
instance : Div (StrongUnitary 𝕜 H) := ⟨fun u v => ⟨u.toUnitary / v.toUnitary⟩⟩
instance : Pow (StrongUnitary 𝕜 H) ℕ := ⟨fun u n => ⟨u.toUnitary ^ n⟩⟩
instance : Pow (StrongUnitary 𝕜 H) ℤ := ⟨fun u n => ⟨u.toUnitary ^ n⟩⟩

instance : Group (StrongUnitary 𝕜 H) :=
  toUnitary_injective.group toUnitary rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Inhabited (StrongUnitary 𝕜 H) := ⟨1⟩

@[simp] theorem toUnitary_one : (1 : StrongUnitary 𝕜 H).toUnitary = 1 := (rfl)
@[simp] theorem toUnitary_mul (u v : StrongUnitary 𝕜 H) :
    (u * v).toUnitary = u.toUnitary * v.toUnitary := (rfl)
@[simp] theorem toUnitary_inv (u : StrongUnitary 𝕜 H) : u⁻¹.toUnitary = u.toUnitary⁻¹ := (rfl)
@[simp] theorem toUnitary_div (u v : StrongUnitary 𝕜 H) :
    (u / v).toUnitary = u.toUnitary / v.toUnitary := (rfl)
@[simp] theorem toUnitary_pow (u : StrongUnitary 𝕜 H) (n : ℕ) :
    (u ^ n).toUnitary = u.toUnitary ^ n := (rfl)
@[simp] theorem toUnitary_zpow (u : StrongUnitary 𝕜 H) (n : ℤ) :
    (u ^ n).toUnitary = u.toUnitary ^ n := (rfl)

@[simp] theorem ofUnitary_one : ofUnitary (1 : unitary (H →L[𝕜] H)) = 1 := (rfl)
@[simp] theorem ofUnitary_mul (u v : unitary (H →L[𝕜] H)) :
    ofUnitary (u * v) = ofUnitary u * ofUnitary v := (rfl)
@[simp] theorem ofUnitary_inv (u : unitary (H →L[𝕜] H)) :
    ofUnitary u⁻¹ = (ofUnitary u)⁻¹ := (rfl)
@[simp] theorem ofUnitary_div (u v : unitary (H →L[𝕜] H)) :
    ofUnitary (u / v) = ofUnitary u / ofUnitary v := (rfl)
@[simp] theorem ofUnitary_pow (u : unitary (H →L[𝕜] H)) (n : ℕ) :
    ofUnitary (u ^ n) = ofUnitary u ^ n := (rfl)
@[simp] theorem ofUnitary_zpow (u : unitary (H →L[𝕜] H)) (n : ℤ) :
    ofUnitary (u ^ n) = ofUnitary u ^ n := (rfl)

/-- Multiplicative isomorphism between `StrongUnitary 𝕜 H` and `unitary (H →L[𝕜] H)`. -/
def mulEquivUnitary : StrongUnitary 𝕜 H ≃* unitary (H →L[𝕜] H) where
  toFun := toUnitary
  invFun := ofUnitary
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem mulEquivUnitary_apply (u : StrongUnitary 𝕜 H) : mulEquivUnitary u = u.toUnitary :=
  (rfl)

@[simp]
theorem mulEquivUnitary_symm_apply (u : unitary (H →L[𝕜] H)) :
    mulEquivUnitary.symm u = ofUnitary u :=
  (rfl)

/-- Multiplicative isomorphism between `StrongUnitary 𝕜 H` and the group `H ≃ₗᵢ[𝕜] H` of linear
isometric equivalences of `H`. -/
def linearIsometryEquiv : StrongUnitary 𝕜 H ≃* (H ≃ₗᵢ[𝕜] H) :=
  mulEquivUnitary.trans Unitary.linearIsometryEquiv

/-- The underlying continuous linear operator of `u : StrongUnitary 𝕜 H`. -/
def toCLM (u : StrongUnitary 𝕜 H) : H →L[𝕜] H :=
  (u.toUnitary : H →L[𝕜] H)

theorem toCLM_injective : Function.Injective (toCLM (𝕜 := 𝕜) (H := H)) :=
  fun _ _ h => toUnitary_injective (Subtype.ext h)

@[simp]
theorem coe_toUnitary (u : StrongUnitary 𝕜 H) : (u.toUnitary : H →L[𝕜] H) = u.toCLM :=
  (rfl)

@[simp]
theorem toCLM_mem_unitary (u : StrongUnitary 𝕜 H) : u.toCLM ∈ unitary (H →L[𝕜] H) :=
  u.toUnitary.property

instance : FunLike (StrongUnitary 𝕜 H) H H where
  coe u := ⇑u.toCLM
  coe_injective _ _ h := toCLM_injective (ContinuousLinearMap.ext (congrFun h))

instance : ContinuousLinearMapClass (StrongUnitary 𝕜 H) 𝕜 H H where
  map_add u := u.toCLM.map_add
  map_smulₛₗ u := u.toCLM.map_smul
  map_continuous u := u.toCLM.cont

instance : LinearIsometryClass (StrongUnitary 𝕜 H) 𝕜 H H where
  norm_map u := Unitary.norm_map u.toUnitary

@[ext]
theorem ext {u v : StrongUnitary 𝕜 H} (h : ∀ ξ, u ξ = v ξ) : u = v :=
  DFunLike.ext u v h

@[simp] theorem coe_toCLM (u : StrongUnitary 𝕜 H) : ⇑u.toCLM = u := (rfl)
theorem toCLM_apply (u : StrongUnitary 𝕜 H) (ξ : H) : u.toCLM ξ = u ξ := (rfl)
@[simp] theorem toCLM_ofUnitary (u : unitary (H →L[𝕜] H)) :
    (ofUnitary u).toCLM = (u : H →L[𝕜] H) := (rfl)
@[simp] theorem ofUnitary_apply (u : unitary (H →L[𝕜] H)) (ξ : H) :
    ofUnitary u ξ = (u : H →L[𝕜] H) ξ := (rfl)
@[simp] theorem toCLM_one : (1 : StrongUnitary 𝕜 H).toCLM = 1 := (rfl)
@[simp] theorem toCLM_mul (u v : StrongUnitary 𝕜 H) : (u * v).toCLM = u.toCLM * v.toCLM := (rfl)

@[simp]
theorem toCLM_pow (u : StrongUnitary 𝕜 H) (n : ℕ) : (u ^ n).toCLM = u.toCLM ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, toCLM_mul, ih]

/-- Evaluation into `H →L[𝕜] H` as a monoid homomorphism on `StrongUnitary 𝕜 H`. -/
def toCLMMonoidHom : StrongUnitary 𝕜 H →* (H →L[𝕜] H) where
  toFun := toCLM
  map_one' := toCLM_one
  map_mul' := toCLM_mul

@[simp]
theorem toCLMMonoidHom_apply (u : StrongUnitary 𝕜 H) : toCLMMonoidHom u = u.toCLM :=
  (rfl)

@[simp]
theorem coe_linearIsometryEquiv (u : StrongUnitary 𝕜 H) :
    (linearIsometryEquiv u : H →L[𝕜] H) = u.toCLM := by
  simp [linearIsometryEquiv]

@[simp]
theorem linearIsometryEquiv_apply (u : StrongUnitary 𝕜 H) (ξ : H) :
    linearIsometryEquiv u ξ = u ξ := by
  rw [← toCLM_apply, ← coe_linearIsometryEquiv, LinearIsometryEquiv.coe_coe'']

@[simp]
theorem toCLM_linearIsometryEquiv_symm (e : H ≃ₗᵢ[𝕜] H) :
    (linearIsometryEquiv.symm e).toCLM = (e : H →L[𝕜] H) := by
  simp [linearIsometryEquiv]

@[simp]
theorem linearIsometryEquiv_symm_apply (e : H ≃ₗᵢ[𝕜] H) (ξ : H) :
    linearIsometryEquiv.symm e ξ = e ξ := by
  rw [← toCLM_apply, toCLM_linearIsometryEquiv_symm, LinearIsometryEquiv.coe_coe'']

/-- The star of `u.toCLM` in `H →L[𝕜] H` is `u⁻¹.toCLM`. -/
theorem star_toCLM (u : StrongUnitary 𝕜 H) : star u.toCLM = u⁻¹.toCLM := by
  rw [← coe_toUnitary, ← coe_toUnitary, toUnitary_inv, ← Unitary.star_eq_inv, Unitary.coe_star]

/-- The underlying continuous linear map of `u⁻¹` is the Hilbert-space adjoint of `u.toCLM`. -/
theorem toCLM_inv (u : StrongUnitary 𝕜 H) :
    u⁻¹.toCLM = ContinuousLinearMap.adjoint u.toCLM := by
  rw [← ContinuousLinearMap.star_eq_adjoint, star_toCLM]

@[simp] theorem one_apply (ξ : H) : (1 : StrongUnitary 𝕜 H) ξ = ξ := (rfl)
@[simp] theorem mul_apply (u v : StrongUnitary 𝕜 H) (ξ : H) : (u * v) ξ = u (v ξ) := (rfl)

@[simp]
theorem inv_apply_self (u : StrongUnitary 𝕜 H) (ξ : H) : u⁻¹ (u ξ) = ξ := by
  rw [← mul_apply, inv_mul_cancel, one_apply]

@[simp]
theorem apply_inv_self (u : StrongUnitary 𝕜 H) (ξ : H) : u (u⁻¹ ξ) = ξ := by
  rw [← mul_apply, mul_inv_cancel, one_apply]

/-- Every unitary operator has operator norm at most `1`. -/
theorem norm_toCLM_le_one (u : StrongUnitary 𝕜 H) : ‖u.toCLM‖ ≤ 1 :=
  u.toCLM.opNorm_le_bound zero_le_one fun ξ => by
    rw [one_mul, toCLM_apply, SemilinearIsometryClass.norm_map]

/-- Unitary operators preserve the inner product. -/
@[simp]
theorem inner_map_map (u : StrongUnitary 𝕜 H) (ξ η : H) : ⟪u ξ, u η⟫_𝕜 = ⟪ξ, η⟫_𝕜 :=
  Unitary.inner_map_map u.toUnitary ξ η

/-- Moving a unitary operator from the left inner-product slot to the right replaces it by its
inverse. -/
theorem inner_map_left (u : StrongUnitary 𝕜 H) (ξ η : H) : ⟪u ξ, η⟫_𝕜 = ⟪ξ, u⁻¹ η⟫_𝕜 := by
  rw [← u.inner_map_map ξ (u⁻¹ η), u.apply_inv_self]

/-- Moving a unitary operator from the right inner-product slot to the left replaces it by its
inverse. -/
theorem inner_map_right (u : StrongUnitary 𝕜 H) (ξ η : H) : ⟪ξ, u η⟫_𝕜 = ⟪u⁻¹ ξ, η⟫_𝕜 := by
  rw [← u.inner_map_map (u⁻¹ ξ) η, u.apply_inv_self]

/-- The squared-norm identity on unitaries:
`‖u ξ - v ξ‖ ^ 2 = 2 * ‖ξ‖ ^ 2 - 2 * RCLike.re ⟪u ξ, v ξ⟫_𝕜`. -/
theorem norm_sub_sq (u v : StrongUnitary 𝕜 H) (ξ : H) :
    ‖u ξ - v ξ‖ ^ 2 = 2 * ‖ξ‖ ^ 2 - 2 * RCLike.re ⟪u ξ, v ξ⟫_𝕜 := by
  rw [_root_.norm_sub_sq (𝕜 := 𝕜), SemilinearIsometryClass.norm_map,
    SemilinearIsometryClass.norm_map]
  ring

instance [Subsingleton H] : Unique (StrongUnitary 𝕜 H) where
  default := 1
  uniq _ := ext fun _ => Subsingleton.elim _ _

/-! ### Strong operator topology and agreement with WOT -/

/-- Inclusion of `StrongUnitary 𝕜 H` into `H →Lₚₜ[𝕜] H` (continuous linear maps with the topology
of pointwise convergence). -/
def toPointwiseConvergenceCLM (u : StrongUnitary 𝕜 H) : H →Lₚₜ[𝕜] H :=
  ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H u.toCLM

@[simp]
theorem toPointwiseConvergenceCLM_apply (u : StrongUnitary 𝕜 H) (ξ : H) :
    u.toPointwiseConvergenceCLM ξ = u ξ :=
  (rfl)

theorem toPointwiseConvergenceCLM_injective :
    Function.Injective (toPointwiseConvergenceCLM (𝕜 := 𝕜) (H := H)) :=
  fun _ _ h => ext fun ξ => congrArg (fun f : H →Lₚₜ[𝕜] H => f ξ) h

/-- `StrongUnitary 𝕜 H` carries the strong operator topology, induced via
`toPointwiseConvergenceCLM` from `H →Lₚₜ[𝕜] H`. -/
instance : TopologicalSpace (StrongUnitary 𝕜 H) :=
  TopologicalSpace.induced toPointwiseConvergenceCLM inferInstance

theorem isInducing_toPointwiseConvergenceCLM :
    IsInducing (toPointwiseConvergenceCLM (𝕜 := 𝕜) (H := H)) :=
  ⟨rfl⟩

theorem isEmbedding_toPointwiseConvergenceCLM :
    IsEmbedding (toPointwiseConvergenceCLM (𝕜 := 𝕜) (H := H)) :=
  ⟨isInducing_toPointwiseConvergenceCLM, toPointwiseConvergenceCLM_injective⟩

@[continuity, fun_prop]
theorem continuous_toPointwiseConvergenceCLM :
    Continuous (toPointwiseConvergenceCLM (𝕜 := 𝕜) (H := H)) :=
  isInducing_toPointwiseConvergenceCLM.continuous

/-- The identity map from `unitary (H →L[𝕜] H)` (operator-norm topology) to `StrongUnitary 𝕜 H`
(strong operator topology) is continuous. -/
@[continuity, fun_prop]
theorem continuous_ofUnitary : Continuous (ofUnitary (𝕜 := 𝕜) (H := H)) :=
  isInducing_toPointwiseConvergenceCLM.continuous_iff.2 <|
    (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H).continuous.comp
      continuous_subtypeVal

instance : T2Space (StrongUnitary 𝕜 H) :=
  isEmbedding_toPointwiseConvergenceCLM.t2Space

/-- Convergence in `StrongUnitary 𝕜 H` is pointwise convergence on every vector `ξ : H`. -/
theorem tendsto_iff_forall_tendsto {α : Type*} {l : Filter α} {f : α → StrongUnitary 𝕜 H}
    {u : StrongUnitary 𝕜 H} :
    Tendsto f l (𝓝 u) ↔ ∀ ξ, Tendsto (fun a => f a ξ) l (𝓝 (u ξ)) := by
  simp only [isInducing_toPointwiseConvergenceCLM.tendsto_nhds_iff,
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto, Function.comp_apply,
    toPointwiseConvergenceCLM_apply]

/-- Continuity of a map into `StrongUnitary 𝕜 H` is continuity of every orbit `x ↦ f x ξ`. -/
theorem continuous_iff_forall_continuous {X : Type*} [TopologicalSpace X]
    {f : X → StrongUnitary 𝕜 H} :
    Continuous f ↔ ∀ ξ, Continuous fun x => f x ξ := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_tendsto]
  exact forall_comm

instance : ContinuousEvalConst (StrongUnitary 𝕜 H) H H where
  continuous_eval_const ξ := continuous_iff_forall_continuous.1 continuous_id ξ

/-- Evaluation `(u, ξ) ↦ u ξ` is jointly continuous on `StrongUnitary 𝕜 H × H`. -/
instance : ContinuousEval (StrongUnitary 𝕜 H) H H where
  continuous_eval :=
    continuous_prod_of_continuous_lipschitzWith' _ 1
      (fun u => SemilinearIsometryClass.lipschitzWith u)
      fun ξ => continuous_eval_const ξ

/-- Strong convergence in `StrongUnitary 𝕜 H` is determined by pointwise convergence along any dense
family in `H`. -/
theorem tendsto_iff_forall_tendsto_of_dense {ι α : Type*} {d : ι → H} (hd : DenseRange d)
    {l : Filter α} {f : α → StrongUnitary 𝕜 H} {u : StrongUnitary 𝕜 H} :
    Tendsto f l (𝓝 u) ↔ ∀ i, Tendsto (fun a => f a (d i)) l (𝓝 (u (d i))) :=
  ⟨fun h i => (tendsto_iff_forall_tendsto.1 h) (d i), fun h =>
    tendsto_iff_forall_tendsto.2 fun ξ =>
      ContinuousLinearMap.tendsto_apply_of_dense hd
        (Eventually.of_forall fun a => (f a).norm_toCLM_le_one)
        (by rintro _ ⟨i, rfl⟩; exact h i) ξ⟩

/-- Continuity into `StrongUnitary 𝕜 H` is determined by continuity of orbits along any dense
family in `H`. -/
theorem continuous_iff_forall_continuous_of_dense {ι X : Type*} [TopologicalSpace X] {d : ι → H}
    (hd : DenseRange d) {f : X → StrongUnitary 𝕜 H} :
    Continuous f ↔ ∀ i, Continuous fun x => f x (d i) := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_tendsto_of_dense hd]
  exact forall_comm

/-- **Strong and weak operator topologies agree on unitaries** (Williams, Lemma D.42): a filter
tends to `u` in `StrongUnitary 𝕜 H` if and only if every matrix coefficient `⟪ξ, f a η⟫_𝕜` tends
to `⟪ξ, u η⟫_𝕜`. -/
theorem tendsto_iff_forall_inner_tendsto {α : Type*} {l : Filter α} {f : α → StrongUnitary 𝕜 H}
    {u : StrongUnitary 𝕜 H} :
    Tendsto f l (𝓝 u) ↔ ∀ ξ η, Tendsto (fun a => ⟪ξ, f a η⟫_𝕜) l (𝓝 ⟪ξ, u η⟫_𝕜) :=
  ⟨fun h ξ η => tendsto_const_nhds.inner (tendsto_iff_forall_tendsto.1 h η), fun h =>
    tendsto_iff_forall_tendsto.2 fun η =>
      tendsto_of_tendsto_inner_of_norm_eq
        (Eventually.of_forall fun a => by simp only [SemilinearIsometryClass.norm_map])
        (h (u η) η)⟩

/-- Continuity into `StrongUnitary 𝕜 H` is equivalent to continuity of all matrix coefficients
`x ↦ ⟪ξ, f x η⟫_𝕜`. -/
theorem continuous_iff_forall_continuous_inner {X : Type*} [TopologicalSpace X]
    {f : X → StrongUnitary 𝕜 H} :
    Continuous f ↔ ∀ ξ η, Continuous fun x => ⟪ξ, f x η⟫_𝕜 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_inner_tendsto]
  exact ⟨fun h ξ η x => h x ξ η, fun h x ξ η => h ξ η x⟩

/-- Inclusion of `StrongUnitary 𝕜 H` into `H →WOT[𝕜] H` (the weak operator topology). -/
def toWOT (u : StrongUnitary 𝕜 H) : H →WOT[𝕜] H :=
  ContinuousLinearMapWOT.ofCLM u.toCLM

theorem toWOT_def (u : StrongUnitary 𝕜 H) : u.toWOT = ContinuousLinearMapWOT.ofCLM u.toCLM :=
  (rfl)

@[simp]
theorem toCLM_toWOT (u : StrongUnitary 𝕜 H) : ContinuousLinearMapWOT.toCLM u.toWOT = u.toCLM :=
  (rfl)

@[simp]
theorem toWOT_apply (u : StrongUnitary 𝕜 H) (ξ : H) : u.toWOT ξ = u ξ :=
  (rfl)

@[simp]
theorem toWOT_inv (u : StrongUnitary 𝕜 H) : u⁻¹.toWOT = star u.toWOT :=
  ContinuousLinearMapWOT.ext_iff.2 fun ξ => by
    rw [ContinuousLinearMapWOT.star_apply, toCLM_toWOT, star_toCLM, toWOT_apply, toCLM_apply]

/-- Inclusion into `H →WOT[𝕜] H` is a topological embedding: the strong and weak operator
topologies coincide on `StrongUnitary 𝕜 H`. -/
theorem isEmbedding_toWOT : IsEmbedding (toWOT (𝕜 := 𝕜) (H := H)) := by
  refine ⟨isInducing_iff_nhds.2 fun u => le_antisymm ?_ ?_,
    fun _ _ h => toCLM_injective (congrArg ContinuousLinearMapWOT.toCLM h)⟩
  · rw [← tendsto_iff_comap, ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
    exact fun ξ η => (tendsto_iff_forall_inner_tendsto.1 tendsto_id) η ξ
  · have hlim : Tendsto id (comap toWOT (𝓝 u.toWOT)) (𝓝 u) := by
      rw [tendsto_iff_forall_inner_tendsto]
      intro ξ η
      exact (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.1
        (tendsto_iff_comap.2 le_rfl)) η ξ
    rwa [Tendsto, map_id] at hlim

/-- Inclusion of `StrongUnitary 𝕜 H` into `H →WOT[𝕜] H` is continuous. -/
@[continuity, fun_prop]
theorem continuous_toWOT : Continuous (toWOT (𝕜 := 𝕜) (H := H)) :=
  isEmbedding_toWOT.continuous

/-! ### Topological group and scalar actions -/

instance : ContinuousMul (StrongUnitary 𝕜 H) where
  continuous_mul := continuous_iff_forall_continuous.2 fun ξ => by
    simpa only [mul_apply] using continuous_fst.eval (continuous_snd.eval_const ξ)

instance : ContinuousInv (StrongUnitary 𝕜 H) where
  continuous_inv := isEmbedding_toWOT.continuous_iff.2 <| by
    simpa only [Function.comp_def, toWOT_inv] using continuous_star.comp continuous_toWOT

/-- `StrongUnitary 𝕜 H` is a topological group under composition (Williams, Lemma D.42). -/
instance : IsTopologicalGroup (StrongUnitary 𝕜 H) := {}

/-- The pointwise adjoint of a strongly continuous family of unitary operators is strongly
continuous. -/
theorem continuous_adjoint_apply_of_mem_unitary {X : Type*} [TopologicalSpace X]
    {F : X → H →L[𝕜] H} (hF : ∀ v, Continuous fun x ↦ F x v)
    (hU : ∀ x, F x ∈ unitary (H →L[𝕜] H)) (v : H) :
    Continuous fun x ↦ ContinuousLinearMap.adjoint (F x) v := by
  let u (x : X) : StrongUnitary 𝕜 H := ofUnitary ⟨F x, hU x⟩
  have hu : Continuous u := continuous_iff_forall_continuous.2 <| by
    simpa only [u, ofUnitary_apply] using hF
  simpa only [Function.comp_apply, ← toCLM_apply, toCLM_inv, u, toCLM_ofUnitary] using
    continuous_iff_forall_continuous.1 (continuous_inv.comp hu) v

/-- Scalar multiplication of `StrongUnitary 𝕜 H` by `unitary 𝕜`. -/
instance : SMul (unitary 𝕜) (StrongUnitary 𝕜 H) :=
  ⟨fun α u => ofUnitary (α • u.toUnitary)⟩

/-- Scalar action of `unitary 𝕜` on `StrongUnitary 𝕜 H` by scalar multiplication of operators. -/
instance : MulAction (unitary 𝕜) (StrongUnitary 𝕜 H) :=
  toUnitary_injective.mulAction toUnitary fun _ _ => rfl

@[simp]
theorem toCLM_smul (α : unitary 𝕜) (u : StrongUnitary 𝕜 H) :
    (α • u).toCLM = (α : 𝕜) • u.toCLM :=
  (rfl)

@[simp]
theorem smul_apply (α : unitary 𝕜) (u : StrongUnitary 𝕜 H) (ξ : H) :
    (α • u) ξ = (α : 𝕜) • u ξ := by
  rw [← toCLM_apply, toCLM_smul, _root_.smul_apply, toCLM_apply]

instance : IsScalarTower (unitary 𝕜) (StrongUnitary 𝕜 H) (StrongUnitary 𝕜 H) where
  smul_assoc α u v := ext fun ξ => by simp

instance : SMulCommClass (unitary 𝕜) (StrongUnitary 𝕜 H) (StrongUnitary 𝕜 H) where
  smul_comm α u v := ext fun ξ => by simp

instance : ContinuousSMul (unitary 𝕜) (StrongUnitary 𝕜 H) where
  continuous_smul := by
    rw [continuous_iff_forall_continuous]
    intro ξ
    have hc : Continuous fun p : unitary 𝕜 × StrongUnitary 𝕜 H => (p.1 : 𝕜) • p.2 ξ :=
      (continuous_subtypeVal.comp continuous_fst).smul
        ((continuous_eval_const ξ).comp continuous_snd)
    simpa only [smul_apply] using hc

end General

section CircleAction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar action of `Circle` on the complex strong unitary group `StrongUnitary ℂ H`. -/
instance : MulAction Circle (StrongUnitary ℂ H) :=
  MulAction.compHom (StrongUnitary ℂ H) circleEquivUnitary.toMonoidHom

theorem circle_smul_def (z : Circle) (u : StrongUnitary ℂ H) :
    z • u = circleEquivUnitary z • u :=
  MulAction.compHom_smul_def circleEquivUnitary.toMonoidHom z u

@[simp]
theorem toCLM_circle_smul (z : Circle) (u : StrongUnitary ℂ H) :
    (z • u).toCLM = (z : ℂ) • u.toCLM := by
  rw [circle_smul_def, toCLM_smul, coe_circleEquivUnitary]

@[simp]
theorem circle_smul_apply (z : Circle) (u : StrongUnitary ℂ H) (ξ : H) :
    (z • u) ξ = (z : ℂ) • u ξ := by
  rw [circle_smul_def, smul_apply, coe_circleEquivUnitary]

instance : IsScalarTower Circle (StrongUnitary ℂ H) (StrongUnitary ℂ H) where
  smul_assoc z u v := ext fun ξ => by simp

instance : SMulCommClass Circle (StrongUnitary ℂ H) (StrongUnitary ℂ H) where
  smul_comm z u v := ext fun ξ => by simp

instance : ContinuousSMul Circle (StrongUnitary ℂ H) :=
  MulAction.continuousSMul_compHom (f := circleEquivUnitary.toMonoidHom)
    circleEquivUnitary.continuous

end CircleAction

/-! ### One-dimensional identifications -/

section OneDim

/-- Topological group isomorphism `unitary 𝕜 ≃ₜ* StrongUnitary 𝕜 𝕜` sending `α` to `α • 1`, with
inverse `u ↦ u 1`. -/
def unitaryEquivStrongUnitary (𝕜 : Type*) [RCLike 𝕜] :
    unitary 𝕜 ≃ₜ* StrongUnitary 𝕜 𝕜 where
  toFun α := α • 1
  invFun u := ⟨u 1, by
    have hnorm : ‖u 1‖ = 1 := by rw [SemilinearIsometryClass.norm_map, norm_one]
    rw [Unitary.mem_iff, RCLike.star_def, mul_comm (conj (u 1)), RCLike.mul_conj, hnorm]
    norm_num⟩
  left_inv α := Subtype.ext <| by simp
  right_inv u := ext fun x => by
    conv_rhs => rw [← mul_one x, ← smul_eq_mul, map_smul]
    simp [smul_eq_mul, mul_comm]
  map_mul' α β := ext fun x => by
    simp only [mul_apply, smul_apply, one_apply, Submonoid.coe_mul, smul_eq_mul, mul_assoc]
  continuous_toFun := continuous_id.smul continuous_const
  continuous_invFun := (continuous_eval_const (1 : 𝕜)).subtype_mk _

@[simp]
theorem unitaryEquivStrongUnitary_apply {𝕜 : Type*} [RCLike 𝕜] (α : unitary 𝕜) (x : 𝕜) :
    unitaryEquivStrongUnitary 𝕜 α x = (α : 𝕜) * x := by
  simp [unitaryEquivStrongUnitary]

@[simp]
theorem coe_unitaryEquivStrongUnitary_symm {𝕜 : Type*} [RCLike 𝕜] (u : StrongUnitary 𝕜 𝕜) :
    ((unitaryEquivStrongUnitary 𝕜).symm u : 𝕜) = u 1 :=
  (rfl)

/-- For the one-dimensional complex Hilbert space `ℂ`, `StrongUnitary ℂ ℂ` is topologically
isomorphic as a group to `Circle`. -/
def circleEquivStrongUnitary : Circle ≃ₜ* StrongUnitary ℂ ℂ :=
  circleEquivUnitary.trans (unitaryEquivStrongUnitary ℂ)

@[simp]
theorem circleEquivStrongUnitary_apply (z : Circle) (w : ℂ) :
    circleEquivStrongUnitary z w = (z : ℂ) * w := by
  simp [circleEquivStrongUnitary]

@[simp]
theorem coe_circleEquivStrongUnitary_symm (u : StrongUnitary ℂ ℂ) :
    (circleEquivStrongUnitary.symm u : ℂ) = u 1 := by
  simp [circleEquivStrongUnitary]

end OneDim

/-! ### Polish structure for separable `H` -/

section Polish

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Auxiliary construction of an element of `StrongUnitary 𝕜 H` from two linear isometries
`U, V : H →ₗᵢ[𝕜] H` satisfying the adjoint identity `⟪U ξ, η⟫_𝕜 = ⟪ξ, V η⟫_𝕜`. -/
private def ofAdjointPair (U V : H →ₗᵢ[𝕜] H) (hadj : ∀ ξ η, ⟪U ξ, η⟫_𝕜 = ⟪ξ, V η⟫_𝕜) :
    { u : StrongUnitary 𝕜 H // (∀ ξ, u ξ = U ξ) ∧ ∀ ξ, u⁻¹ ξ = V ξ } := by
  let e : H ≃ₗᵢ[𝕜] H :=
    { toFun := U
      map_add' := U.map_add
      map_smul' := U.map_smul
      invFun := V
      left_inv := fun ξ => ext_inner_right 𝕜 fun η => by
        rw [← inner_conj_symm, ← hadj, U.inner_map_map, inner_conj_symm]
      right_inv := fun η => ext_inner_left 𝕜 fun ξ => by
        rw [← inner_conj_symm, hadj, V.inner_map_map, inner_conj_symm]
      norm_map' := U.norm_map }
  refine ⟨linearIsometryEquiv.symm e, fun ξ => ?_, fun ξ => ?_⟩
  · simp [e]
  · rw [← map_inv, LinearIsometryEquiv.inv_def, linearIsometryEquiv_symm_apply,
      ← LinearIsometryEquiv.coe_symm_toLinearEquiv]
    simp [e]

/-- Strong* evaluation `u ↦ (fun n => u (d n), fun n => u⁻¹ (d n))` along a dense sequence
`d : ℕ → H` is a topological embedding into `(ℕ → H) × (ℕ → H)`. -/
private theorem isEmbedding_strongStarEval_of_dense {d : ℕ → H} (hd : DenseRange d) :
    IsEmbedding (fun u : StrongUnitary 𝕜 H => (fun n => u (d n), fun n => u⁻¹ (d n))) := by
  let Φ : StrongUnitary 𝕜 H → (ℕ → H) × (ℕ → H) :=
    fun u => (fun n => u (d n), fun n => u⁻¹ (d n))
  refine ⟨isInducing_iff_nhds.2 fun u => le_antisymm ?_ ?_, fun u v h => ?_⟩
  · rw [← tendsto_iff_comap, Prod.tendsto_iff, tendsto_pi_nhds, tendsto_pi_nhds]
    exact ⟨fun n => (tendsto_iff_forall_tendsto.1 tendsto_id) (d n),
      fun n => (tendsto_iff_forall_tendsto.1 continuous_inv.continuousAt) (d n)⟩
  · have hlim : Tendsto id (comap Φ (𝓝 (Φ u))) (𝓝 u) := by
      rw [tendsto_iff_forall_tendsto_of_dense hd]
      intro n
      exact tendsto_pi_nhds.1 ((Prod.tendsto_iff Φ (Φ u)).1 (tendsto_iff_comap.2 le_rfl)).1 n
    rwa [Tendsto, map_id] at hlim
  · refine ext (congrFun <| hd.equalizer (map_continuous u) (map_continuous v) ?_)
    ext n
    exact congrFun (congrArg Prod.fst h) n

/-- Strong* evaluation `u ↦ (fun n => u (d n), fun n => u⁻¹ (d n))` along a dense sequence
`d : ℕ → H` is a closed embedding into `(ℕ → H) × (ℕ → H)`. -/
private theorem isClosedEmbedding_strongStarEval_of_dense {d : ℕ → H} (hd : DenseRange d) :
    IsClosedEmbedding (fun u : StrongUnitary 𝕜 H => (fun n => u (d n), fun n => u⁻¹ (d n))) := by
  let Φ : StrongUnitary 𝕜 H → (ℕ → H) × (ℕ → H) :=
    fun u => (fun n => u (d n), fun n => u⁻¹ (d n))
  let S : Set ((ℕ → H) × (ℕ → H)) :=
    { p | (∀ m n, ⟪p.1 m, p.1 n⟫_𝕜 = ⟪d m, d n⟫_𝕜) ∧
          (∀ m n, ⟪p.2 m, p.2 n⟫_𝕜 = ⟪d m, d n⟫_𝕜) ∧
          (∀ m n, ⟪p.1 m, d n⟫_𝕜 = ⟪d m, p.2 n⟫_𝕜) }
  have hc1 : ∀ n, Continuous fun p : (ℕ → H) × (ℕ → H) => p.1 n :=
    fun n => (continuous_apply n).comp continuous_fst
  have hc2 : ∀ n, Continuous fun p : (ℕ → H) × (ℕ → H) => p.2 n :=
    fun n => (continuous_apply n).comp continuous_snd
  have hS_closed : IsClosed S :=
    (isClosed_forall₂_eq (fun m n => (hc1 m).inner (hc1 n)) (fun _ _ => continuous_const)).inter <|
      (isClosed_forall₂_eq (fun m n => (hc2 m).inner (hc2 n))
        (fun _ _ => continuous_const)).inter <|
        isClosed_forall₂_eq (fun m _ => (hc1 m).inner continuous_const)
          (fun _ n => continuous_const.inner (hc2 n))
  refine ⟨isEmbedding_strongStarEval_of_dense hd, ?_⟩
  suffices Set.range Φ = S by rwa [this]
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    exact ⟨fun m n => u.inner_map_map (d m) (d n), fun m n => u⁻¹.inner_map_map (d m) (d n),
      fun m n => u.inner_map_left (d m) (d n)⟩
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    dsimp only at hx hy hxy
    have hspan : (Submodule.span 𝕜 (Set.range d)).topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.1 (hd.mono Submodule.subset_span)
    let U : H →ₗᵢ[𝕜] H := linearIsometryOfInnerEq hspan fun m n => (hx m n).symm
    let V : H →ₗᵢ[𝕜] H := linearIsometryOfInnerEq hspan fun m n => (hy m n).symm
    have hUd : ∀ n, U (d n) = x n := linearIsometryOfInnerEq_apply hspan _
    have hVd : ∀ n, V (d n) = y n := linearIsometryOfInnerEq_apply hspan _
    have hadj : ∀ ξ η, ⟪U ξ, η⟫_𝕜 = ⟪ξ, V η⟫_𝕜 := fun ξ η =>
      congrFun ((hd.prodMap hd).equalizer ((U.continuous.comp continuous_fst).inner continuous_snd)
        (continuous_fst.inner (V.continuous.comp continuous_snd)) <| funext fun ⟨m, n⟩ => by
          simp only [Function.comp_apply, Prod.map_apply, hUd m, hVd n, hxy m n]) (ξ, η)
    obtain ⟨u, hu, hu_inv⟩ := ofAdjointPair U V hadj
    exact ⟨u, Prod.ext (funext fun n => (hu (d n)).trans (hUd n))
      (funext fun n => (hu_inv (d n)).trans (hVd n))⟩

/-- When `H` is separable, `StrongUnitary 𝕜 H` is a `PolishSpace` (Williams, Lemmas D.37 and
D.42). -/
instance [SeparableSpace H] : PolishSpace (StrongUnitary 𝕜 H) := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  exact (isClosedEmbedding_strongStarEval_of_dense hd).polishSpace

end Polish

end StrongUnitary

end TauCeti
