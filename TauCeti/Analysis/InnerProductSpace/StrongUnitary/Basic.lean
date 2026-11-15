/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Topology.MetricSpace.Polish
import TauCeti.Analysis.LocallyConvex.StrongOperatorTopology

/-!
# The unitary group in the strong operator topology

For a complete real or complex inner product space `H` over `𝕜`, `TauCeti.StrongUnitary 𝕜 H` is a
type synonym of `unitary (H →L[𝕜] H)` equipped with the strong operator topology, defined as the
topology induced via `ContinuousLinearMap.toPointwiseConvergenceCLM` from `H →Lₚₜ[𝕜] H`. Keeping a
separate type leaves Mathlib's operator-norm topology on `unitary (H →L[𝕜] H)` intact (the norm
topology is strictly finer whenever `H` is infinite-dimensional).

On unitary operators, the norm identity
`‖u ξ - v ξ‖ ^ 2 = 2 * ‖ξ‖ ^ 2 - 2 * RCLike.re ⟪u ξ, v ξ⟫_𝕜`
implies that the strong and weak operator topologies coincide: a filter converges strongly in
`StrongUnitary 𝕜 H` if and only if all matrix coefficients `⟪ξ, u η⟫_𝕜` converge. Since every
unitary operator has operator norm at most `1`, multiplication is jointly continuous, and since
`⟪ξ, u⁻¹ η⟫_𝕜 = conj ⟪η, u ξ⟫_𝕜`, inversion is continuous; thus `StrongUnitary 𝕜 H` is a Hausdorff
topological group whose action `(u, ξ) ↦ u ξ` on `H` is jointly continuous.

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
* `Circle.equivUnitary`, `TauCeti.StrongUnitary.unitaryEquivStrongUnitary`, and
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

namespace Circle

/-- The unit circle `Circle` in `ℂ` is topologically isomorphic as a group to `unitary ℂ`. -/
def equivUnitary : Circle ≃ₜ* unitary ℂ :=
  have hmem : ∀ z : Circle, (z : ℂ) ∈ unitary ℂ := fun z => by
    rw [Unitary.mem_iff, RCLike.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul,
      ← Circle.coe_mul, inv_mul_cancel, mul_inv_cancel, Circle.coe_one, and_self]
  { toFun z := ⟨(z : ℂ), hmem z⟩
    invFun u := ⟨(u : ℂ), mem_sphere_zero_iff_norm.2 <| CStarRing.norm_of_mem_unitary u.2⟩
    left_inv _ := Circle.ext rfl
    right_inv _ := Subtype.ext rfl
    map_mul' _ _ := Subtype.ext rfl
    continuous_toFun := Continuous.subtype_mk
      (continuous_subtype_val : Continuous ((↑) : Circle → ℂ)) hmem
    continuous_invFun := Continuous.subtype_mk continuous_subtype_val _ }

@[simp]
theorem coe_equivUnitary (z : Circle) : (equivUnitary z : ℂ) = z := by
  unfold equivUnitary
  rfl

@[simp]
theorem coe_equivUnitary_symm (u : unitary ℂ) : (equivUnitary.symm u : ℂ) = u := by
  unfold equivUnitary
  rfl

end Circle

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
theorem ofUnitary_toUnitary (u : StrongUnitary 𝕜 H) : ofUnitary u.toUnitary = u := by
  rfl

@[simp]
theorem toUnitary_ofUnitary (u : unitary (H →L[𝕜] H)) : (ofUnitary u).toUnitary = u := by
  rfl

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

@[simp] theorem toUnitary_one : (1 : StrongUnitary 𝕜 H).toUnitary = 1 := by rfl
@[simp] theorem toUnitary_mul (u v : StrongUnitary 𝕜 H) :
    (u * v).toUnitary = u.toUnitary * v.toUnitary := by rfl
@[simp] theorem toUnitary_inv (u : StrongUnitary 𝕜 H) : u⁻¹.toUnitary = u.toUnitary⁻¹ := by rfl
@[simp] theorem toUnitary_div (u v : StrongUnitary 𝕜 H) :
    (u / v).toUnitary = u.toUnitary / v.toUnitary := by rfl
@[simp] theorem toUnitary_pow (u : StrongUnitary 𝕜 H) (n : ℕ) :
    (u ^ n).toUnitary = u.toUnitary ^ n := by rfl
@[simp] theorem toUnitary_zpow (u : StrongUnitary 𝕜 H) (n : ℤ) :
    (u ^ n).toUnitary = u.toUnitary ^ n := by rfl

@[simp] theorem ofUnitary_one : ofUnitary (1 : unitary (H →L[𝕜] H)) = 1 := by rfl
@[simp] theorem ofUnitary_mul (u v : unitary (H →L[𝕜] H)) :
    ofUnitary (u * v) = ofUnitary u * ofUnitary v := by rfl
@[simp] theorem ofUnitary_inv (u : unitary (H →L[𝕜] H)) :
    ofUnitary u⁻¹ = (ofUnitary u)⁻¹ := by rfl

/-- Multiplicative isomorphism between `StrongUnitary 𝕜 H` and `unitary (H →L[𝕜] H)`. -/
def mulEquivUnitary : StrongUnitary 𝕜 H ≃* unitary (H →L[𝕜] H) where
  toFun := toUnitary
  invFun := ofUnitary
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem mulEquivUnitary_apply (u : StrongUnitary 𝕜 H) : mulEquivUnitary u = u.toUnitary := by
  rfl

@[simp]
theorem mulEquivUnitary_symm_apply (u : unitary (H →L[𝕜] H)) :
    mulEquivUnitary.symm u = ofUnitary u := by
  rfl

/-- Multiplicative isomorphism between `StrongUnitary 𝕜 H` and the group `H ≃ₗᵢ[𝕜] H` of linear
isometric equivalences of `H`. -/
def linearIsometryEquiv : StrongUnitary 𝕜 H ≃* (H ≃ₗᵢ[𝕜] H) :=
  mulEquivUnitary.trans Unitary.linearIsometryEquiv

/-- The underlying continuous linear operator of `u : StrongUnitary 𝕜 H`. -/
def toCLM (u : StrongUnitary 𝕜 H) : H →L[𝕜] H :=
  (u.toUnitary : H →L[𝕜] H)

theorem toCLM_injective : Function.Injective (toCLM (𝕜 := 𝕜) (H := H)) :=
  fun _ _ h => toUnitary_injective (Subtype.ext h)

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

@[simp] theorem coe_toCLM (u : StrongUnitary 𝕜 H) : ⇑u.toCLM = u := by rfl
theorem toCLM_apply (u : StrongUnitary 𝕜 H) (ξ : H) : u.toCLM ξ = u ξ := by rfl
@[simp] theorem toCLM_ofUnitary (u : unitary (H →L[𝕜] H)) :
    (ofUnitary u).toCLM = (u : H →L[𝕜] H) := by rfl
@[simp] theorem ofUnitary_apply (u : unitary (H →L[𝕜] H)) (ξ : H) :
    ofUnitary u ξ = (u : H →L[𝕜] H) ξ := by rfl
@[simp] theorem toCLM_one : (1 : StrongUnitary 𝕜 H).toCLM = 1 := by rfl
@[simp] theorem toCLM_mul (u v : StrongUnitary 𝕜 H) : (u * v).toCLM = u.toCLM * v.toCLM := by rfl

@[simp]
theorem coe_linearIsometryEquiv (u : StrongUnitary 𝕜 H) :
    (linearIsometryEquiv u : H →L[𝕜] H) = u.toCLM := by
  rfl

@[simp]
theorem linearIsometryEquiv_apply (u : StrongUnitary 𝕜 H) (ξ : H) :
    linearIsometryEquiv u ξ = u ξ := by
  rfl

@[simp]
theorem toCLM_linearIsometryEquiv_symm (e : H ≃ₗᵢ[𝕜] H) :
    (linearIsometryEquiv.symm e).toCLM = (e : H →L[𝕜] H) := by
  rfl

@[simp]
theorem linearIsometryEquiv_symm_apply (e : H ≃ₗᵢ[𝕜] H) (ξ : H) :
    linearIsometryEquiv.symm e ξ = e ξ := by
  rfl

/-- The underlying continuous linear map of `u⁻¹` is the Hilbert-space adjoint of `u.toCLM`. -/
theorem toCLM_inv (u : StrongUnitary 𝕜 H) :
    u⁻¹.toCLM = ContinuousLinearMap.adjoint u.toCLM := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  rfl

@[simp] theorem one_apply (ξ : H) : (1 : StrongUnitary 𝕜 H) ξ = ξ := by rfl
@[simp] theorem mul_apply (u v : StrongUnitary 𝕜 H) (ξ : H) : (u * v) ξ = u (v ξ) := by rfl

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

/-- The Hilbert-space polarization identity on unitaries:
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
def toPointwiseCLM (u : StrongUnitary 𝕜 H) : H →Lₚₜ[𝕜] H :=
  ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H u.toCLM

@[simp]
theorem toPointwiseCLM_apply (u : StrongUnitary 𝕜 H) (ξ : H) : u.toPointwiseCLM ξ = u ξ := by
  rfl

theorem toPointwiseCLM_injective : Function.Injective (toPointwiseCLM (𝕜 := 𝕜) (H := H)) :=
  fun _ _ h => ext fun ξ => congrArg (fun f : H →Lₚₜ[𝕜] H => f ξ) h

instance : TopologicalSpace (StrongUnitary 𝕜 H) :=
  TopologicalSpace.induced toPointwiseCLM inferInstance

theorem isInducing_toPointwiseCLM : IsInducing (toPointwiseCLM (𝕜 := 𝕜) (H := H)) :=
  ⟨rfl⟩

theorem isEmbedding_toPointwiseCLM : IsEmbedding (toPointwiseCLM (𝕜 := 𝕜) (H := H)) :=
  ⟨isInducing_toPointwiseCLM, toPointwiseCLM_injective⟩

@[continuity, fun_prop]
theorem continuous_toPointwiseCLM : Continuous (toPointwiseCLM (𝕜 := 𝕜) (H := H)) :=
  isInducing_toPointwiseCLM.continuous

/-- The identity map from `unitary (H →L[𝕜] H)` (operator-norm topology) to `StrongUnitary 𝕜 H`
(strong operator topology) is continuous. -/
@[continuity, fun_prop]
theorem continuous_ofUnitary : Continuous (ofUnitary (𝕜 := 𝕜) (H := H)) :=
  isInducing_toPointwiseCLM.continuous_iff.2 <|
    (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H).continuous.comp
      continuous_subtype_val

instance : T2Space (StrongUnitary 𝕜 H) :=
  isEmbedding_toPointwiseCLM.t2Space

/-- Convergence in `StrongUnitary 𝕜 H` is pointwise convergence on every vector `ξ : H`. -/
theorem tendsto_iff_forall_tendsto {α : Type*} {l : Filter α} {f : α → StrongUnitary 𝕜 H}
    {u : StrongUnitary 𝕜 H} :
    Tendsto f l (𝓝 u) ↔ ∀ ξ, Tendsto (fun a => f a ξ) l (𝓝 (u ξ)) := by
  rw [isInducing_toPointwiseCLM.tendsto_nhds_iff,
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  rfl

/-- Continuity of a map into `StrongUnitary 𝕜 H` is continuity of every orbit `x ↦ f x ξ`. -/
theorem continuous_iff_forall_continuous {X : Type*} [TopologicalSpace X]
    {f : X → StrongUnitary 𝕜 H} :
    Continuous f ↔ ∀ ξ, Continuous fun x => f x ξ := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_tendsto]
  exact forall_comm

instance : ContinuousEvalConst (StrongUnitary 𝕜 H) H H where
  continuous_eval_const ξ := continuous_iff_forall_continuous.1 continuous_id ξ

/-- Since unitary operators are `1`-Lipschitz isometries, evaluation `(u, ξ) ↦ u ξ` is jointly
continuous on `StrongUnitary 𝕜 H × H`. -/
instance : ContinuousEval (StrongUnitary 𝕜 H) H H where
  continuous_eval :=
    continuous_prod_of_continuous_lipschitzWith' _ 1
      (fun u => SemilinearIsometryClass.lipschitzWith u)
      fun ξ => continuous_eval_const ξ

/-- Because unitary operators are `1`-Lipschitz, strong convergence in `StrongUnitary 𝕜 H` is
already determined by pointwise convergence on any dense subset of `H`. -/
theorem tendsto_iff_forall_tendsto_of_dense {ι α : Type*} {d : ι → H} (hd : DenseRange d)
    {l : Filter α} {f : α → StrongUnitary 𝕜 H} {u : StrongUnitary 𝕜 H} :
    Tendsto f l (𝓝 u) ↔ ∀ i, Tendsto (fun a => f a (d i)) l (𝓝 (u (d i))) := by
  refine ⟨fun h i => (tendsto_iff_forall_tendsto.1 h) (d i), fun h => ?_⟩
  rw [tendsto_iff_forall_tendsto]
  intro ξ
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨i, hi⟩ := Metric.mem_closure_range_iff.1 (hd ξ) (ε / 3) (by positivity)
  filter_upwards [Metric.tendsto_nhds.1 (h i) (ε / 3) (by positivity)] with a ha
  calc
    dist (f a ξ) (u ξ)
      ≤ dist (f a ξ) (f a (d i)) + dist (f a (d i)) (u (d i)) + dist (u (d i)) (u ξ) :=
        dist_triangle4 _ _ _ _
    _ = dist ξ (d i) + dist (f a (d i)) (u (d i)) + dist (d i) ξ := by
        rw [(SemilinearIsometryClass.isometry (f a)).dist_eq,
          (SemilinearIsometryClass.isometry u).dist_eq]
    _ = dist ξ (d i) + dist (f a (d i)) (u (d i)) + dist ξ (d i) := by rw [dist_comm (d i) ξ]
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

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
    Tendsto f l (𝓝 u) ↔ ∀ ξ η, Tendsto (fun a => ⟪ξ, f a η⟫_𝕜) l (𝓝 ⟪ξ, u η⟫_𝕜) := by
  refine ⟨fun h ξ η => tendsto_const_nhds.inner (tendsto_iff_forall_tendsto.1 h η), fun h => ?_⟩
  rw [tendsto_iff_forall_tendsto]
  intro η
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun a => ‖f a η - u η‖ ^ 2) l (𝓝 0) := by
    have hre : Tendsto (fun a => RCLike.re ⟪f a η, u η⟫_𝕜) l (𝓝 (‖η‖ ^ 2)) := by
      have h1 : Tendsto (fun a => RCLike.re ⟪u η, f a η⟫_𝕜) l (𝓝 (RCLike.re ⟪u η, u η⟫_𝕜)) :=
        (RCLike.continuous_re.tendsto _).comp (h (u η) η)
      have heq : (fun a => RCLike.re ⟪u η, f a η⟫_𝕜) = fun a => RCLike.re ⟪f a η, u η⟫_𝕜 := by
        ext a
        rw [← inner_conj_symm (f a η) (u η), RCLike.conj_re]
      have hlim : RCLike.re ⟪u η, u η⟫_𝕜 = ‖η‖ ^ 2 := by
        rw [u.inner_map_map, inner_self_eq_norm_sq]
      rwa [heq, hlim] at h1
    have hsub : Tendsto (fun a => 2 * ‖η‖ ^ 2 - 2 * RCLike.re ⟪f a η, u η⟫_𝕜) l
        (𝓝 (2 * ‖η‖ ^ 2 - 2 * ‖η‖ ^ 2)) :=
      tendsto_const_nhds.sub (hre.const_mul 2)
    rw [sub_self] at hsub
    exact hsub.congr fun a => ((f a).norm_sub_sq u η).symm
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr fun a => Real.sqrt_sq (norm_nonneg _)

/-- Continuity into `StrongUnitary 𝕜 H` is equivalent to continuity of all matrix coefficients
`x ↦ ⟪ξ, f x η⟫_𝕜`. -/
theorem continuous_iff_forall_inner_continuous {X : Type*} [TopologicalSpace X]
    {f : X → StrongUnitary 𝕜 H} :
    Continuous f ↔ ∀ ξ η, Continuous fun x => ⟪ξ, f x η⟫_𝕜 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_inner_tendsto]
  exact ⟨fun h ξ η x => h x ξ η, fun h x ξ η => h ξ η x⟩

/-- Inclusion of `StrongUnitary 𝕜 H` into `H →WOT[𝕜] H` (the weak operator topology). -/
def toWOT (u : StrongUnitary 𝕜 H) : H →WOT[𝕜] H :=
  ContinuousLinearMapWOT.ofCLM u.toCLM

@[simp]
theorem toWOT_apply (u : StrongUnitary 𝕜 H) (ξ : H) : u.toWOT ξ = u ξ := by
  rfl

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

/-! ### Topological group and scalar actions -/

instance : ContinuousMul (StrongUnitary 𝕜 H) where
  continuous_mul := by
    rw [continuous_iff_forall_continuous]
    intro ξ
    rw [continuous_iff_continuousAt]
    rintro ⟨u₀, v₀⟩
    rw [ContinuousAt]
    have h1 : ∀ η, Tendsto (fun p : StrongUnitary 𝕜 H × StrongUnitary 𝕜 H => p.1.toCLM η)
        (𝓝 (u₀, v₀)) (𝓝 (u₀.toCLM η)) := fun η => by
      simpa only [toCLM_apply] using (continuous_fst.eval_const η).tendsto (u₀, v₀)
    have h2 : ∀ η, Tendsto (fun p : StrongUnitary 𝕜 H × StrongUnitary 𝕜 H => p.2.toCLM η)
        (𝓝 (u₀, v₀)) (𝓝 (v₀.toCLM η)) := fun η => by
      simpa only [toCLM_apply] using (continuous_snd.eval_const η).tendsto (u₀, v₀)
    simpa only [ContinuousLinearMap.comp_apply, mul_apply, toCLM_apply] using
      ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le h1 h2
        (Eventually.of_forall fun p => p.1.norm_toCLM_le_one) ξ

instance : ContinuousInv (StrongUnitary 𝕜 H) where
  continuous_inv := by
    rw [continuous_iff_forall_inner_continuous]
    intro ξ η
    have heq : (fun u : StrongUnitary 𝕜 H => ⟪ξ, u⁻¹ η⟫_𝕜) = fun u => conj ⟪η, u ξ⟫_𝕜 := by
      ext u
      rw [← u.inner_map_left, inner_conj_symm]
    rw [heq]
    exact RCLike.continuous_conj.comp (continuous_const.inner (continuous_eval_const ξ))

/-- `StrongUnitary 𝕜 H` is a topological group under composition (Williams, Lemma D.42). -/
instance : IsTopologicalGroup (StrongUnitary 𝕜 H) := {}

/-- Scalar action of `unitary 𝕜` on `StrongUnitary 𝕜 H` by scalar multiplication of operators. -/
instance : MulAction (unitary 𝕜) (StrongUnitary 𝕜 H) where
  smul α u := ofUnitary ⟨(α : 𝕜) • (u.toUnitary : H →L[𝕜] H), by
    rw [Unitary.mem_iff, star_smul, smul_mul_smul_comm, smul_mul_smul_comm,
      Unitary.star_mul_self_of_mem α.2, Unitary.mul_star_self_of_mem α.2,
      Unitary.star_mul_self_of_mem u.toUnitary.2, Unitary.mul_star_self_of_mem u.toUnitary.2,
      one_smul, and_self]⟩
  one_smul u := by
    apply toUnitary_injective
    ext ξ
    exact one_smul 𝕜 (u ξ)
  mul_smul α β u := by
    apply toUnitary_injective
    ext ξ
    exact mul_smul (α : 𝕜) (β : 𝕜) (u ξ)

@[simp]
theorem toCLM_smul (α : unitary 𝕜) (u : StrongUnitary 𝕜 H) :
    (α • u).toCLM = (α : 𝕜) • u.toCLM := by
  simp [HSMul.hSMul, SMul.smul, toCLM]

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
      (continuous_subtype_val.comp continuous_fst).smul
        ((continuous_eval_const ξ).comp continuous_snd)
    simpa only [smul_apply] using hc

end General

section CircleAction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar action of `Circle` on the complex strong unitary group `StrongUnitary ℂ H`. -/
instance : MulAction Circle (StrongUnitary ℂ H) :=
  MulAction.compHom (StrongUnitary ℂ H) Circle.equivUnitary.toMonoidHom

@[simp]
theorem circle_smul_apply (z : Circle) (u : StrongUnitary ℂ H) (ξ : H) :
    (z • u) ξ = (z : ℂ) • u ξ := by
  -- `MulAction Circle (StrongUnitary ℂ H)` is defined via `MulAction.compHom` along
  -- `Circle.equivUnitary`, so `z • u` is definitionally `Circle.equivUnitary z • u`.
  change (Circle.equivUnitary z • u) ξ = (z : ℂ) • u ξ
  rw [smul_apply, Circle.coe_equivUnitary]

instance : IsScalarTower Circle (StrongUnitary ℂ H) (StrongUnitary ℂ H) where
  smul_assoc z u v := ext fun ξ => by simp

instance : SMulCommClass Circle (StrongUnitary ℂ H) (StrongUnitary ℂ H) where
  smul_comm z u v := ext fun ξ => by simp

instance : ContinuousSMul Circle (StrongUnitary ℂ H) where
  continuous_smul := by
    rw [continuous_iff_forall_continuous]
    intro ξ
    have hc : Continuous fun p : Circle × StrongUnitary ℂ H => (p.1 : ℂ) • p.2 ξ :=
      ((continuous_subtype_val : Continuous ((↑) : Circle → ℂ)).comp continuous_fst).smul
        ((continuous_eval_const ξ).comp continuous_snd)
    simpa only [circle_smul_apply] using hc

end CircleAction

/-! ### One-dimensional identifications -/

section OneDim

/-- In dimension `1`, `StrongUnitary 𝕜 𝕜` is topologically isomorphic as a group to `unitary 𝕜` via
scalar action on `1 : 𝕜`. -/
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
    rw [mul_apply, smul_apply, smul_apply, smul_apply, one_apply, one_apply, Submonoid.coe_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_assoc]
  continuous_toFun := continuous_id.smul continuous_const
  continuous_invFun := (continuous_eval_const (1 : 𝕜)).subtype_mk _

@[simp]
theorem unitaryEquivStrongUnitary_apply {𝕜 : Type*} [RCLike 𝕜] (α : unitary 𝕜) (x : 𝕜) :
    unitaryEquivStrongUnitary 𝕜 α x = (α : 𝕜) * x := by
  simp [unitaryEquivStrongUnitary]

@[simp]
theorem coe_unitaryEquivStrongUnitary_symm {𝕜 : Type*} [RCLike 𝕜] (u : StrongUnitary 𝕜 𝕜) :
    ((unitaryEquivStrongUnitary 𝕜).symm u : 𝕜) = u 1 := by
  rfl

/-- For the one-dimensional complex Hilbert space `ℂ`, `StrongUnitary ℂ ℂ` is topologically
isomorphic as a group to `Circle`. -/
def circleEquivStrongUnitary : Circle ≃ₜ* StrongUnitary ℂ ℂ :=
  Circle.equivUnitary.trans (unitaryEquivStrongUnitary ℂ)

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

/-- Auxiliary extension lemma: a sequence `x : ℕ → H` with the same Gram matrix as a dense sequence
`d : ℕ → H` extends uniquely to a continuous map `H → H` sending `d n` to `x n`. -/
private def extendOfInnerEq {d x : ℕ → H} (hd : DenseRange d)
    (hx : ∀ m n, ⟪x m, x n⟫_𝕜 = ⟪d m, d n⟫_𝕜) :
    { U : H → H // Continuous U ∧ ∀ n, U (d n) = x n } := by
  have hdist : ∀ m n, dist (x m) (x n) = dist (d m) (d n) := fun m n => by
    have hsq : ‖x m - x n‖ ^ 2 = ‖d m - d n‖ ^ 2 := by
      rw [_root_.norm_sub_sq (𝕜 := 𝕜), _root_.norm_sub_sq (𝕜 := 𝕜),
        ← inner_self_eq_norm_sq (𝕜 := 𝕜) (x m), ← inner_self_eq_norm_sq (𝕜 := 𝕜) (x n),
        ← inner_self_eq_norm_sq (𝕜 := 𝕜) (d m), ← inner_self_eq_norm_sq (𝕜 := 𝕜) (d n),
        hx m m, hx n n, hx m n]
    simpa only [dist_eq_norm] using (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  let f : Set.range d → H := fun z => x z.2.choose
  have hf_eq : ∀ n, f ⟨d n, ⟨n, rfl⟩⟩ = x n := fun n => by
    let z : Set.range d := ⟨d n, ⟨n, rfl⟩⟩
    have hz : d z.2.choose = d n := z.2.choose_spec
    exact dist_eq_zero.1 <| (hdist z.2.choose n).trans (by simp [hz])
  have hf_iso : Isometry f := Isometry.of_dist_eq fun z₁ z₂ =>
    (hdist z₁.2.choose z₂.2.choose).trans <| by
      rw [z₁.2.choose_spec, z₂.2.choose_spec]
      rfl
  have hd_set : Dense (Set.range d) := hd
  exact ⟨hd_set.extend f, (hd_set.uniformContinuous_extend hf_iso.uniformContinuous).continuous,
    fun n => (hd_set.extend_of_ind hf_iso.uniformContinuous ⟨d n, ⟨n, rfl⟩⟩).trans (hf_eq n)⟩

/-- When `H` is separable, `StrongUnitary 𝕜 H` is a `PolishSpace` (Williams, Lemmas D.37 and D.42):
for a dense sequence `d : ℕ → H`, `u ↦ (fun n => u (d n), fun n => u⁻¹ (d n))` is a closed
embedding into the Polish product `(ℕ → H) × (ℕ → H)`. -/
instance [SeparableSpace H] : PolishSpace (StrongUnitary 𝕜 H) := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  let Φ : StrongUnitary 𝕜 H → (ℕ → H) × (ℕ → H) :=
    fun u => (fun n => u (d n), fun n => u⁻¹ (d n))
  suffices IsClosedEmbedding Φ from this.polishSpace
  have hEmb : IsEmbedding Φ := by
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
  refine ⟨hEmb, ?_⟩
  let S : Set ((ℕ → H) × (ℕ → H)) :=
    { p | (∀ m n, ⟪p.1 m, p.1 n⟫_𝕜 = ⟪d m, d n⟫_𝕜) ∧
          (∀ m n, ⟪p.2 m, p.2 n⟫_𝕜 = ⟪d m, d n⟫_𝕜) ∧
          (∀ m n, ⟪p.1 m, d n⟫_𝕜 = ⟪d m, p.2 n⟫_𝕜) }
  have hS_closed : IsClosed S := by
    have hc1 : ∀ n, Continuous fun p : (ℕ → H) × (ℕ → H) => p.1 n :=
      fun n => (continuous_apply n).comp continuous_fst
    have hc2 : ∀ n, Continuous fun p : (ℕ → H) × (ℕ → H) => p.2 n :=
      fun n => (continuous_apply n).comp continuous_snd
    have h1 : IsClosed { p : (ℕ → H) × (ℕ → H) | ∀ m n, ⟪p.1 m, p.1 n⟫_𝕜 = ⟪d m, d n⟫_𝕜 } := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun m => isClosed_iInter fun n =>
        isClosed_eq ((hc1 m).inner (hc1 n)) continuous_const
    have h2 : IsClosed { p : (ℕ → H) × (ℕ → H) | ∀ m n, ⟪p.2 m, p.2 n⟫_𝕜 = ⟪d m, d n⟫_𝕜 } := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun m => isClosed_iInter fun n =>
        isClosed_eq ((hc2 m).inner (hc2 n)) continuous_const
    have h3 : IsClosed { p : (ℕ → H) × (ℕ → H) | ∀ m n, ⟪p.1 m, d n⟫_𝕜 = ⟪d m, p.2 n⟫_𝕜 } := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun m => isClosed_iInter fun n =>
        isClosed_eq ((hc1 m).inner continuous_const) (continuous_const.inner (hc2 n))
    exact h1.inter (h2.inter h3)
  suffices Set.range Φ = S by rwa [this]
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    exact ⟨fun m n => u.inner_map_map (d m) (d n),
      fun m n => u⁻¹.inner_map_map (d m) (d n),
      fun m n => u.inner_map_left (d m) (d n)⟩
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    dsimp only at hx hy hxy
    obtain ⟨U, hUc, hUd⟩ := extendOfInnerEq hd hx
    obtain ⟨V, hVc, hVd⟩ := extendOfInnerEq hd hy
    have hd2 : DenseRange (Prod.map d d) := hd.prodMap hd
    have hadj : ∀ ξ η, ⟪U ξ, η⟫_𝕜 = ⟪ξ, V η⟫_𝕜 := fun ξ η => by
      have heq : (fun p : H × H => ⟪U p.1, p.2⟫_𝕜) = fun p => ⟪p.1, V p.2⟫_𝕜 :=
        hd2.equalizer ((hUc.comp continuous_fst).inner continuous_snd)
          (continuous_fst.inner (hVc.comp continuous_snd)) <| funext fun ⟨m, n⟩ => by
            simp only [Function.comp_apply, Prod.map_apply, hUd m, hVd n, hxy m n]
      exact congrFun heq (ξ, η)
    have hU_inner : ∀ ξ η, ⟪U ξ, U η⟫_𝕜 = ⟪ξ, η⟫_𝕜 := fun ξ η => by
      have heq : (fun p : H × H => ⟪U p.1, U p.2⟫_𝕜) = fun p => ⟪p.1, p.2⟫_𝕜 :=
        hd2.equalizer ((hUc.comp continuous_fst).inner (hUc.comp continuous_snd))
          (continuous_fst.inner continuous_snd) <| funext fun ⟨m, n⟩ => by
            simp only [Function.comp_apply, Prod.map_apply, hUd m, hUd n, hx m n]
      exact congrFun heq (ξ, η)
    have hV_inner : ∀ ξ η, ⟪V ξ, V η⟫_𝕜 = ⟪ξ, η⟫_𝕜 := fun ξ η => by
      have heq : (fun p : H × H => ⟪V p.1, V p.2⟫_𝕜) = fun p => ⟪p.1, p.2⟫_𝕜 :=
        hd2.equalizer ((hVc.comp continuous_fst).inner (hVc.comp continuous_snd))
          (continuous_fst.inner continuous_snd) <| funext fun ⟨m, n⟩ => by
            simp only [Function.comp_apply, Prod.map_apply, hVd m, hVd n, hy m n]
      exact congrFun heq (ξ, η)
    let eL : H ≃ₗ[𝕜] H :=
      { toFun := U
        invFun := V
        map_add' := fun ξ₁ ξ₂ => ext_inner_right 𝕜 fun η => by
          rw [hadj, inner_add_left, ← hadj, ← hadj, ← inner_add_left]
        map_smul' := fun c ξ => ext_inner_right 𝕜 fun η => by
          rw [RingHom.id_apply, hadj, inner_smul_left, ← hadj, ← inner_smul_left]
        left_inv := fun ξ => ext_inner_right 𝕜 fun η => by
          rw [← inner_conj_symm, ← hadj, hU_inner, inner_conj_symm]
        right_inv := fun η => ext_inner_left 𝕜 fun ξ => by
          rw [← inner_conj_symm, hadj, hV_inner, inner_conj_symm] }
    let e : H ≃ₗᵢ[𝕜] H :=
      { eL with
        norm_map' := fun ξ => by
          have heL : eL ξ = U ξ := rfl
          rw [heL, norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜), hU_inner] }
    refine ⟨linearIsometryEquiv.symm e, Prod.ext (funext fun n => ?_) (funext fun n => ?_)⟩
    · exact (linearIsometryEquiv_symm_apply e (d n)).trans (hUd n)
    · dsimp only [Φ]
      have hinv : (linearIsometryEquiv.symm e)⁻¹ = linearIsometryEquiv.symm e.symm := by
        rw [← map_inv]; rfl
      rw [hinv, linearIsometryEquiv_symm_apply]
      exact hVd n

end Polish

end StrongUnitary

end TauCeti
