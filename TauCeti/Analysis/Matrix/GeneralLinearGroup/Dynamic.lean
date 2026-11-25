/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.Units
import TauCeti.Analysis.Matrix.Normed
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.Topology.Instances.Matrix

/-!
# Dynamic subgroups of a real matrix

For a subgroup `G` of `GL m ℝ` and a real matrix `X`, conjugating `g ∈ G` by the one-parameter
group `exp (t • X)` gives the family `exp (-t • X) * g * exp (t • X)`. This file defines the
three subgroups of `G` cut out by its behaviour as `t → +∞`:

* `Subgroup.dynamicParabolic G X`: the family is bounded entrywise for `t ≥ 0`;
* `Subgroup.dynamicUnipotent G X`: the family tends to `1`;
* `Subgroup.dynamicLevi G X`: `g` commutes with `X`, so the family is constant.

They are subgroups for every `X`: products of bounded families are bounded, and the inverse of a
bounded family of constant determinant is bounded by the adjugate formula. The unipotent and Levi
subgroups lie in the parabolic one and meet trivially, and the unipotent subgroup is normal in
the parabolic one, since a bounded family times a family tending to `0` tends to `0`.

For symmetric `X` the file proves the Levi decomposition of the dynamic parabolic subgroup.
In an orthonormal eigenbasis of `X` with eigenvalues `d`, entry `(i, j)` of the conjugate family
is `e^{t (d j - d i)}` times that of `g`. So the dynamic parabolic subgroup is block upper
triangular, the unipotent one block unipotent and the Levi one block diagonal, and the first two
are closed when `G` is. When `G` is `θ`-stable, the parabolic subgroup meets its image under
`θ g = (g⁻¹)ᵀ` in the Levi subgroup. When `G` is closed and normalized by every `exp (t • X)`,
every element of the parabolic subgroup is uniquely `l * u` with `l` in the Levi and `u` in the
unipotent subgroup. For every `X`, the conjugates of such a product `l * u` tend to `l`.

For `GL₂(ℝ)` and `X = diag(1, 0)` the conjugates of `((a, b), (c, d))` are
`((a, e^{-t} b), (e^t c, d))`, so the three subgroups are the upper triangular, the upper
unitriangular and the diagonal groups. They are the Lie-group counterparts of the dynamic
parabolic, unipotent and Levi subgroups of a cocharacter of an algebraic group, and the matrix
form of the Levi decomposition `P = L ⋉ N` of the parabolic subgroups of a real reductive group.
Knapp's Langlands decomposition `P = MAN` further splits the Levi factor `L` as `MA`; that split
is not made here.

## Main definitions

* `Subgroup.dynamicParabolic`, `Subgroup.dynamicUnipotent`, `Subgroup.dynamicLevi`.

## Main results

* `Subgroup.dynamicUnipotent_le_dynamicParabolic`, `Subgroup.dynamicLevi_le_dynamicParabolic`.
* `Subgroup.mul_mul_inv_mem_dynamicUnipotent`, `Subgroup.normal_dynamicUnipotent_subgroupOf`:
  the unipotent subgroup is normal in the parabolic one.
* `Subgroup.dynamicLevi_inf_dynamicUnipotent`: the Levi and unipotent subgroups meet trivially.
* `Subgroup.tendsto_dynamicLevi_mul_dynamicUnipotent`: the conjugates of `l * u`, with `l` Levi and
  `u` unipotent, tend to `l`.
* `Subgroup.mem_dynamicParabolic_diagonal_iff`, `Subgroup.mem_dynamicUnipotent_diagonal_iff`,
  `Subgroup.mem_dynamicLevi_diagonal_iff`,
  `Subgroup.mem_dynamicParabolic_units_conj_diagonal_iff`,
  `Subgroup.mem_dynamicUnipotent_units_conj_diagonal_iff`,
  `Subgroup.mem_dynamicLevi_units_conj_diagonal_iff`: the block triangular, block unipotent and
  block diagonal coordinate descriptions for `X = O * diagonal d * O⁻¹`.
* `Subgroup.isClosed_dynamicLevi`, `Subgroup.isClosed_dynamicParabolic`,
  `Subgroup.isClosed_dynamicUnipotent`: closedness, the last two for symmetric `X`.
* `Subgroup.dynamicParabolic_inf_map_inverseTranspose`: for symmetric `X` and `θ`-stable `G`, the
  parabolic subgroup meets its `θ`-image in the Levi subgroup.
* `Subgroup.existsUnique_dynamicLevi_mul_dynamicUnipotent`: the Levi decomposition `l * u`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Ch. VII §7.
-/

public section

noncomputable section

open Filter Topology NormedSpace Matrix

namespace Subgroup

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ### The conjugate family -/

section Flow

/-- The conjugates `exp (-t • X) * A * exp (t • X)` of a matrix `A`. -/
private def flow (X A : Matrix m m ℝ) (t : ℝ) : Matrix m m ℝ :=
  exp ((-t) • X) * A * exp (t • X)

private lemma flow_mul (X A B : Matrix m m ℝ) (t : ℝ) :
    flow X (A * B) t = flow X A t * flow X B t := by
  simp only [flow, neg_smul, Matrix.mul_assoc, exp_mul_exp_neg_mul]

private lemma flow_one (X : Matrix m m ℝ) (t : ℝ) : flow X 1 t = 1 := by
  rw [flow, Matrix.mul_one, neg_smul, exp_neg_mul_exp]

private lemma flow_of_commute {X A : Matrix m m ℝ} (h : Commute A X) (t : ℝ) :
    flow X A t = A := by
  rw [flow, Matrix.mul_assoc, ((h.smul_right t).exp_right).eq, neg_smul, exp_neg_mul_exp_mul]

private lemma det_flow (X A : Matrix m m ℝ) (t : ℝ) : (flow X A t).det = A.det := by
  rw [flow, det_mul_comm, ← Matrix.mul_assoc, neg_smul, exp_mul_exp_neg, Matrix.one_mul]

private lemma flow_inv (X : Matrix m m ℝ) (g : GL m ℝ) (t : ℝ) :
    flow X ((g⁻¹ : GL m ℝ) : Matrix m m ℝ) t = (flow X g t)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← flow_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, flow_one]

private lemma continuous_flow (X A : Matrix m m ℝ) : Continuous (flow X A) := by
  open scoped Matrix.Norms.Operator in
  exact ((exp_continuous.comp (continuous_neg.smul continuous_const)).mul continuous_const).mul
    (exp_continuous.comp (continuous_id.smul continuous_const))

end Flow

/-! ### Entrywise bounds and limits -/

section Bounds

/-- `A` has entrywise bounded conjugates for `t ≥ 0`. -/
private def BddFlow (X A : Matrix m m ℝ) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ i j, |flow X A t i j| ≤ C

private lemma bddFlow_mul {X A B : Matrix m m ℝ} (hA : BddFlow X A) (hB : BddFlow X B) :
    BddFlow X (A * B) := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨D, hD⟩ := hB
  refine ⟨Fintype.card m * (C * D), fun t ht i j ↦ ?_⟩
  rw [flow_mul]
  exact Matrix.abs_mul_apply_le (hC t ht) (hD t ht) i j

private lemma bddFlow_one (X : Matrix m m ℝ) : BddFlow X 1 := by
  refine ⟨1, fun t _ i j ↦ ?_⟩
  rw [flow_one, Matrix.one_apply]
  split_ifs <;> simp

private lemma bddFlow_inv {X : Matrix m m ℝ} {g : GL m ℝ} (hg : BddFlow X g) :
    BddFlow X ((g⁻¹ : GL m ℝ) : Matrix m m ℝ) := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨|(g : Matrix m m ℝ).det|⁻¹ *
    ((Fintype.card m).factorial * max C 1 ^ Fintype.card m), fun t ht i j ↦ ?_⟩
  rw [flow_inv, inv_def, det_flow]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', abs_mul, abs_inv]
  exact mul_le_mul_of_nonneg_left (Matrix.abs_adjugate_apply_le (hC t ht) i j) (by positivity)

section Norm

open scoped Matrix.Norms.Operator

/-- Conjugates with a limit at `+∞` are entrywise bounded for `t ≥ 0`. -/
private lemma bddFlow_of_tendsto {X A L : Matrix m m ℝ} (h : Tendsto (flow X A) atTop (𝓝 L)) :
    BddFlow X A := by
  obtain ⟨C, hC⟩ :=
    TauCeti.exists_forall_ge_norm_le_of_tendsto (continuous_flow X A).continuousOn h
  exact ⟨C, fun t ht i j ↦ (norm_apply_le_linfty_opNorm (flow X A t) i j).trans (hC t ht)⟩

end Norm

private lemma isBoundedUnder_of_bddFlow {X A : Matrix m m ℝ} (hA : BddFlow X A) (i j : m) :
    IsBoundedUnder (· ≤ ·) atTop fun t ↦ ‖flow X A t i j‖ := by
  obtain ⟨C, hC⟩ := hA
  exact isBoundedUnder_of_eventually_le (a := C)
    (eventually_atTop.2 ⟨0, fun t ht ↦ hC t ht i j⟩)

private lemma tendsto_flow_inv {X : Matrix m m ℝ} {g : GL m ℝ}
    (hg : Tendsto (flow X g) atTop (𝓝 1)) :
    Tendsto (flow X ((g⁻¹ : GL m ℝ) : Matrix m m ℝ)) atTop (𝓝 1) := by
  have hc : ContinuousAt Inv.inv (1 : Matrix m m ℝ) :=
    continuousAt_matrix_inv _ (by
      rw [det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero)
  rw [show flow X ((g⁻¹ : GL m ℝ) : Matrix m m ℝ) = Inv.inv ∘ flow X g from funext (flow_inv X g),
    ← inv_one]
  exact hc.tendsto.comp hg

end Bounds

/-! ### The three subgroups -/

/-- The **dynamic parabolic subgroup** of `X` in `G`: the `g ∈ G` whose conjugates
`exp (-t • X) * g * exp (t • X)`, `t ≥ 0`, are bounded entrywise. -/
def dynamicParabolic (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) : Subgroup (GL m ℝ) where
  carrier := {g | g ∈ G ∧ BddFlow X g}
  mul_mem' {g h} hg hh := ⟨G.mul_mem hg.1 hh.1, by
    rw [Units.val_mul]
    exact bddFlow_mul hg.2 hh.2⟩
  one_mem' := ⟨G.one_mem, bddFlow_one X⟩
  inv_mem' hg := ⟨G.inv_mem hg.1, bddFlow_inv hg.2⟩

/-- The **dynamic unipotent subgroup** of `X` in `G`: the `g ∈ G` whose conjugates
`exp (-t • X) * g * exp (t • X)` tend to `1` as `t → +∞`. -/
def dynamicUnipotent (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) : Subgroup (GL m ℝ) where
  carrier := {g | g ∈ G ∧ Tendsto (flow X g) atTop (𝓝 1)}
  mul_mem' {g h} hg hh := ⟨G.mul_mem hg.1 hh.1, by
    rw [Units.val_mul, ← one_mul (1 : Matrix m m ℝ)]
    exact (hg.2.mul hh.2).congr fun t ↦ (flow_mul X g h t).symm⟩
  one_mem' := ⟨G.one_mem, by
    rw [Units.val_one]
    exact tendsto_const_nhds.congr fun t ↦ (flow_one X t).symm⟩
  inv_mem' hg := ⟨G.inv_mem hg.1, tendsto_flow_inv hg.2⟩

/-- The **dynamic Levi subgroup** of `X` in `G`: the `g ∈ G` commuting with `X`. -/
def dynamicLevi (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) : Subgroup (GL m ℝ) where
  carrier := {g | g ∈ G ∧ Commute (g : Matrix m m ℝ) X}
  mul_mem' {g h} hg hh := ⟨G.mul_mem hg.1 hh.1, by
    rw [Units.val_mul]
    exact hg.2.mul_left hh.2⟩
  one_mem' := ⟨G.one_mem, by simpa only [Units.val_one] using Commute.one_left X⟩
  inv_mem' hg := ⟨G.inv_mem hg.1, hg.2.units_inv_left⟩

variable {G : Subgroup (GL m ℝ)} {X : Matrix m m ℝ} {g : GL m ℝ}

-- The carriers are stated with the private `BddFlow` and `flow`; these two restatements are the
-- only places that unfold them to the explicit conjugates `exp (-t • X) * g * exp (t • X)`.
@[simp]
theorem mem_dynamicParabolic : g ∈ G.dynamicParabolic X ↔ g ∈ G ∧ ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    ∀ i j, |(exp ((-t) • X) * (g : Matrix m m ℝ) * exp (t • X)) i j| ≤ C :=
  Iff.rfl

@[simp]
theorem mem_dynamicUnipotent : g ∈ G.dynamicUnipotent X ↔ g ∈ G ∧
    Tendsto (fun t : ℝ ↦ exp ((-t) • X) * (g : Matrix m m ℝ) * exp (t • X)) atTop (𝓝 1) :=
  Iff.rfl

@[simp]
theorem mem_dynamicLevi : g ∈ G.dynamicLevi X ↔ g ∈ G ∧ Commute (g : Matrix m m ℝ) X :=
  Iff.rfl

theorem dynamicParabolic_le (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) :
    G.dynamicParabolic X ≤ G :=
  fun _ hg ↦ hg.1

theorem dynamicUnipotent_le (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) :
    G.dynamicUnipotent X ≤ G :=
  fun _ hg ↦ hg.1

theorem dynamicLevi_le (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) : G.dynamicLevi X ≤ G :=
  fun _ hg ↦ hg.1

/-- The dynamic unipotent subgroup lies in the dynamic parabolic subgroup: conjugates that
converge are bounded. -/
theorem dynamicUnipotent_le_dynamicParabolic (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) :
    G.dynamicUnipotent X ≤ G.dynamicParabolic X :=
  fun _ hg ↦ ⟨hg.1, bddFlow_of_tendsto hg.2⟩

/-- The dynamic Levi subgroup lies in the dynamic parabolic subgroup: an element commuting with
`X` has constant conjugates. -/
theorem dynamicLevi_le_dynamicParabolic (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) :
    G.dynamicLevi X ≤ G.dynamicParabolic X :=
  fun _ hg ↦ ⟨hg.1,
    bddFlow_of_tendsto (tendsto_const_nhds.congr fun t ↦ (flow_of_commute hg.2 t).symm)⟩

/-- The dynamic unipotent subgroup is normal in the dynamic parabolic subgroup: conjugating a
family tending to `1` by a bounded family of bounded inverse gives a family tending to `1`. -/
theorem mul_mul_inv_mem_dynamicUnipotent {u : GL m ℝ} (hg : g ∈ G.dynamicParabolic X)
    (hu : u ∈ G.dynamicUnipotent X) : g * u * g⁻¹ ∈ G.dynamicUnipotent X := by
  refine ⟨G.mul_mem (G.mul_mem hg.1 hu.1) (G.inv_mem hg.1), ?_⟩
  have hginv := ((G.dynamicParabolic X).inv_mem hg).2
  have hu' : Tendsto (fun t ↦ flow X u t - 1) atTop (𝓝 0) := by
    rw [← sub_self (1 : Matrix m m ℝ)]
    exact hu.2.sub_const 1
  have key (t : ℝ) :
      flow X g t * (flow X u t - 1) * flow X ((g⁻¹ : GL m ℝ) : Matrix m m ℝ) t + 1 =
        flow X (g * u * g⁻¹ : GL m ℝ) t := by
    have hFF : flow X g t * flow X ((g⁻¹ : GL m ℝ) : Matrix m m ℝ) t = 1 := by
      rw [← flow_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, flow_one]
    simp only [Units.val_mul, flow_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hFF,
      sub_add_cancel]
  have h := (Matrix.tendsto_zero_mul_isBoundedUnder_le
    (Matrix.isBoundedUnder_le_mul_tendsto_zero (isBoundedUnder_of_bddFlow hg.2) hu')
    (isBoundedUnder_of_bddFlow hginv)).add_const 1
  rw [zero_add] at h
  exact h.congr key

/-- The dynamic unipotent subgroup is a normal subgroup of the dynamic parabolic subgroup. -/
instance normal_dynamicUnipotent_subgroupOf (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) :
    ((G.dynamicUnipotent X).subgroupOf (G.dynamicParabolic X)).Normal :=
  ⟨fun u hu g ↦ by
    rw [mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact mul_mul_inv_mem_dynamicUnipotent g.property (mem_subgroupOf.1 hu)⟩

/-- The dynamic Levi and unipotent subgroups meet trivially: the conjugates of an element
commuting with `X` are constant, so they tend to `1` only for the identity. -/
theorem dynamicLevi_inf_dynamicUnipotent (G : Subgroup (GL m ℝ)) (X : Matrix m m ℝ) :
    G.dynamicLevi X ⊓ G.dynamicUnipotent X = ⊥ := by
  refine eq_bot_iff.2 fun g hg ↦ ?_
  have hflow : flow X g = fun _ ↦ (g : Matrix m m ℝ) := funext (flow_of_commute hg.1.2)
  have h : Tendsto (fun _ : ℝ ↦ (g : Matrix m m ℝ)) atTop (𝓝 1) := hflow ▸ hg.2.2
  exact Units.ext (tendsto_const_nhds_iff.1 h)

/-- If `l` lies in the dynamic Levi and `u` in the dynamic unipotent subgroup, the conjugates
`exp (-t • X) * (l * u) * exp (t • X)` tend to `l` as `t → +∞`. So the Levi factor of an element
of the dynamic parabolic subgroup, as in `existsUnique_dynamicLevi_mul_dynamicUnipotent`, is the
limit of its conjugates. -/
theorem tendsto_dynamicLevi_mul_dynamicUnipotent {l u : GL m ℝ} (hl : l ∈ G.dynamicLevi X)
    (hu : u ∈ G.dynamicUnipotent X) :
    Tendsto (fun t : ℝ ↦ exp ((-t) • X) * ((l * u : GL m ℝ) : Matrix m m ℝ) * exp (t • X)) atTop
      (𝓝 (l : Matrix m m ℝ)) := by
  have h := (tendsto_const_nhds (x := (l : Matrix m m ℝ))).mul hu.2
  rw [Matrix.mul_one] at h
  refine h.congr fun t ↦ ?_
  rw [← flow_of_commute hl.2 t, ← flow_mul, ← Units.val_mul, flow]

/-- The dynamic Levi subgroup of a closed subgroup is closed. -/
theorem isClosed_dynamicLevi (hG : IsClosed (G : Set (GL m ℝ))) (X : Matrix m m ℝ) :
    IsClosed (G.dynamicLevi X : Set (GL m ℝ)) :=
  hG.inter (isClosed_eq (Units.continuous_val.mul continuous_const)
    (continuous_const.mul Units.continuous_val))

/-! ### Symmetric `X`: coordinates in an orthonormal eigenbasis -/

section Symmetric

variable {O : GL m ℝ} {d : m → ℝ}

/-- Conjugating by `O⁻¹` undoes conjugating by `O`. -/
private lemma inv_conj_conj (O : GL m ℝ) (A : Matrix m m ℝ) :
    ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * (O * A * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)) * O = A := by
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]

/-- Conjugating by `O` undoes conjugating by `O⁻¹`. -/
private lemma conj_inv_conj (O : GL m ℝ) (A : Matrix m m ℝ) :
    O * (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * A * O) * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) = A := by
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]

/-- The conjugates of `A` under `X` are those of `O⁻¹ * A * O` under `diagonal d`, conjugated
by `O`. -/
private lemma flow_eq_conj (hX : X = O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ))
    (A : Matrix m m ℝ) (t : ℝ) :
    flow X A t = O * flow (diagonal d) (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * A * O) t *
      ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) := by
  have hexp (s : ℝ) :
      exp (s • X) = O * exp (s • diagonal d) * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) := by
    rw [hX, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.exp_units_conj]
  simp only [flow, hexp, Matrix.mul_assoc]

/-- The conjugates of `A` under `X` are those of `O⁻¹ * A * O` under `diagonal d`, read back. -/
private lemma flow_diagonal_eq (hX : X = O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ))
    (A : Matrix m m ℝ) (t : ℝ) :
    flow (diagonal d) (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * A * O) t =
      ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * flow X A t * O := by
  rw [flow_eq_conj hX, inv_conj_conj]

private lemma flow_diagonal_apply (d : m → ℝ) (B : Matrix m m ℝ) (t : ℝ) (i j : m) :
    flow (diagonal d) B t i j = Real.exp (t * (d j - d i)) * B i j :=
  exp_neg_smul_diagonal_mul_mul_exp_smul_diagonal_apply d B t i j

private lemma bddFlow_iff_diagonal (hX : X = O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ))
    (A : Matrix m m ℝ) :
    BddFlow X A ↔ BddFlow (diagonal d) (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * A * O) := by
  -- Bounds for `t ≥ 0` are bounds on the family indexed by `Set.Ici 0`.
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨C', hC'⟩ := Matrix.exists_abs_mul_mul_apply_le (F := fun t : Set.Ici (0 : ℝ) ↦
      flow X A t) ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) (O : Matrix m m ℝ) ⟨C, fun t ↦ hC t t.property⟩
    exact ⟨C', fun t ht i j ↦ by rw [flow_diagonal_eq hX]; exact hC' ⟨t, ht⟩ i j⟩
  · rintro ⟨C, hC⟩
    obtain ⟨C', hC'⟩ := Matrix.exists_abs_mul_mul_apply_le (F := fun t : Set.Ici (0 : ℝ) ↦
      flow (diagonal d) (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * A * O) t) (O : Matrix m m ℝ)
      ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) ⟨C, fun t ↦ hC t t.property⟩
    exact ⟨C', fun t ht i j ↦ by rw [flow_eq_conj hX]; exact hC' ⟨t, ht⟩ i j⟩

private lemma tendsto_flow_iff_diagonal
    (hX : X = O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)) (A L : Matrix m m ℝ) :
    Tendsto (flow X A) atTop (𝓝 L) ↔
      Tendsto (flow (diagonal d) (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * A * O)) atTop
        (𝓝 (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * L * O)) := by
  rw [show flow (diagonal d) (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * A * O) =
    fun t ↦ ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * flow X A t * O from funext (flow_diagonal_eq hX A)]
  refine ⟨fun h ↦ (tendsto_const_nhds.mul h).mul tendsto_const_nhds, fun h ↦ ?_⟩
  simpa only [conj_inv_conj] using
    (tendsto_const_nhds (x := (O : Matrix m m ℝ))).mul h |>.mul
      (tendsto_const_nhds (x := ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)))

private lemma commute_iff_diagonal (hX : X = O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ))
    (A : Matrix m m ℝ) :
    Commute A X ↔ Commute (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * A * O) (diagonal d) := by
  -- Conjugation by `O⁻¹` is multiplicative and injective.
  have hmul (B C : Matrix m m ℝ) :
      ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * B * O * (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * C * O) =
        ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * (B * C) * O := by
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [show diagonal d = ((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * X * O by rw [hX, inv_conj_conj]]
  simp only [commute_iff_eq, hmul, Units.mul_left_inj, Units.mul_right_inj]

private lemma bddFlow_diagonal_iff (B : Matrix m m ℝ) :
    BddFlow (diagonal d) B ↔ ∀ i j, d i < d j → B i j = 0 := by
  constructor
  · rintro ⟨C, hC⟩ i j hij
    refine TauCeti.eq_zero_of_eventually_abs_exp_mul_le (C := C) (sub_pos.2 hij)
      (eventually_atTop.2 ⟨0, fun t ht ↦ ?_⟩)
    rw [← flow_diagonal_apply]
    exact hC t ht i j
  · intro h
    obtain ⟨c, hc⟩ := Matrix.exists_abs_apply_le B
    refine ⟨c, fun t ht i j ↦ ?_⟩
    rw [flow_diagonal_apply, abs_mul, Real.abs_exp]
    rcases lt_or_ge (d i) (d j) with hij | hij
    · rw [h i j hij, abs_zero, mul_zero]
      exact (abs_nonneg _).trans (hc i j)
    · calc Real.exp (t * (d j - d i)) * |B i j| ≤ 1 * |B i j| := by
            gcongr
            exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.2 hij))
        _ ≤ c := by rw [one_mul]; exact hc i j

/-- The part of `B` in the diagonal blocks of the level sets of `d`. -/
private def diagonalPart (d : m → ℝ) (B : Matrix m m ℝ) : Matrix m m ℝ :=
  of fun i j ↦ if d i = d j then B i j else 0

private lemma tendsto_flow_diagonal {B : Matrix m m ℝ} (h : ∀ i j, d i < d j → B i j = 0) :
    Tendsto (flow (diagonal d) B) atTop (𝓝 (diagonalPart d B)) := by
  rw [Matrix.tendsto_iff_tendsto_apply]
  intro i j
  simp only [flow_diagonal_apply, diagonalPart, of_apply]
  rcases lt_trichotomy (d i) (d j) with hij | hij | hij
  · simp [h i j hij]
  · simp [hij]
  · simp only [hij.ne', ↓reduceIte]
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.atTop_mul_const_of_neg (sub_neg.2 hij))).mul_const (B i j)

private lemma tendsto_flow_diagonal_one_iff (B : Matrix m m ℝ) :
    Tendsto (flow (diagonal d) B) atTop (𝓝 1) ↔
      ∀ i j, d i ≤ d j → B i j = (1 : Matrix m m ℝ) i j := by
  constructor
  · intro hB i j hij
    have hij' := Matrix.tendsto_iff_tendsto_apply.1 hB i j
    simp only [flow_diagonal_apply] at hij'
    rcases hij.lt_or_eq with hlt | heq
    · rw [Matrix.one_apply_ne fun e ↦ hlt.ne (congrArg d e)]
      exact TauCeti.eq_zero_of_eventually_abs_exp_mul_le (sub_pos.2 hlt)
        ((hij'.abs.eventually (gt_mem_nhds (lt_add_one _))).mono fun t ht ↦ ht.le)
    · simp only [heq, sub_self, mul_zero, Real.exp_zero, one_mul] at hij'
      exact tendsto_nhds_unique tendsto_const_nhds hij'
  · intro h
    have h0 (i j : m) (hij : d i < d j) : B i j = 0 :=
      (h i j hij.le).trans (Matrix.one_apply_ne fun e ↦ hij.ne (congrArg d e))
    convert tendsto_flow_diagonal h0
    ext i j
    simp only [diagonalPart, of_apply]
    split_ifs with hij
    · exact (h i j hij.le).symm
    · exact Matrix.one_apply_ne fun e ↦ hij (congrArg d e)

/-- For symmetric `X`, closed `G` normalized by every `exp (t • X)`, and `g` in the dynamic
parabolic subgroup, the conjugates of `g` converge to an element of the dynamic Levi subgroup. -/
private lemma exists_mem_dynamicLevi_tendsto_flow (hG : IsClosed (G : Set (GL m ℝ)))
    (hX : X.IsSymm)
    (hGX : ∀ t : ℝ, ∀ g ∈ G, ∃ h ∈ G, (h : Matrix m m ℝ) = exp ((-t) • X) * g * exp (t • X))
    {g : GL m ℝ} (hg : g ∈ G.dynamicParabolic X) :
    ∃ l ∈ G.dynamicLevi X, Tendsto (flow X g) atTop (𝓝 (l : Matrix m m ℝ)) := by
  obtain ⟨O, d, -, hXd⟩ := hX.exists_orthogonal_diagonal
  set Oi : Matrix m m ℝ := ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)
  have hB := (bddFlow_diagonal_iff _).1 ((bddFlow_iff_diagonal hXd _).1 hg.2)
  -- The limit is the block-diagonal part of `g` in an eigenbasis of `X`, read back.
  set L : Matrix m m ℝ := O * diagonalPart d (Oi * g * O) * Oi
  have hlim : Tendsto (flow X g) atTop (𝓝 L) := by
    rw [tendsto_flow_iff_diagonal hXd]
    simpa only [L, Oi, inv_conj_conj] using tendsto_flow_diagonal hB
  -- The conjugates all have determinant `det g`, so the limit is invertible.
  have hdet : L.det = (g : Matrix m m ℝ).det := by
    have h := (continuous_id.matrix_det.tendsto L).comp hlim
    simp only [Function.comp_def, id, det_flow] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hunit : IsUnit L := (isUnit_iff_isUnit_det L).2 (hdet ▸ (isUnit_iff_isUnit_det _).1 g.isUnit)
  refine ⟨hunit.unit, ⟨?_, ?_⟩, by rwa [IsUnit.unit_spec]⟩
  · -- The conjugates lie in the closed subgroup `G`, so their limit does too.
    let F : ℝ → GL m ℝ := fun t ↦ (isUnit_exp ((-t) • X)).unit * g * (isUnit_exp (t • X)).unit
    have hemb : IsOpenEmbedding (Units.val : GL m ℝ → Matrix m m ℝ) := by
      open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val
    have hF : Tendsto F atTop (𝓝 hunit.unit) := by
      rw [hemb.isEmbedding.tendsto_nhds_iff]
      simp only [F, Function.comp_def, Units.val_mul, IsUnit.unit_spec]
      exact hlim
    refine hG.mem_of_tendsto hF (Eventually.of_forall fun t ↦ ?_)
    obtain ⟨h, hh, he⟩ := hGX t g hg.1
    rwa [show F t = h from Units.ext (by simp [F, he])]
  · rw [IsUnit.unit_spec, commute_iff_diagonal hXd]
    simp only [L, Oi, inv_conj_conj]
    exact (TauCeti.commute_diagonal_of_apply_eq_zero fun i j hij ↦ by
      simp [diagonalPart, hij]).symm

/-- The `g` whose conjugate `P * g * Q` has prescribed entries `c i j` at the positions with
`p i j` form a closed set. -/
private lemma isClosed_iInter_apply_eq (P Q : Matrix m m ℝ) (p : m → m → Prop)
    (c : m → m → ℝ) :
    IsClosed (⋂ i, ⋂ j, {g : GL m ℝ | p i j → (P * g * Q) i j = c i j}) :=
  isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_imp isOpen_const
    (isClosed_eq (((continuous_const.mul Units.continuous_val).mul continuous_const).matrix_elem
      i j) continuous_const)

/-- For diagonal `X = diagonal d`, the dynamic parabolic subgroup is block triangular: `g ∈ G` lies
in it exactly when its entries `(i, j)` with `d i < d j` vanish. -/
theorem mem_dynamicParabolic_diagonal_iff :
    g ∈ G.dynamicParabolic (diagonal d) ↔
      g ∈ G ∧ ∀ i j, d i < d j → (g : Matrix m m ℝ) i j = 0 :=
  and_congr_right fun _ ↦ bddFlow_diagonal_iff _

/-- For diagonal `X = diagonal d`, the dynamic unipotent subgroup is block unipotent: `g ∈ G` lies
in it exactly when `g i j = δ i j` for all `(i, j)` with `d i ≤ d j`. -/
theorem mem_dynamicUnipotent_diagonal_iff :
    g ∈ G.dynamicUnipotent (diagonal d) ↔
      g ∈ G ∧ ∀ i j, d i ≤ d j → (g : Matrix m m ℝ) i j = (1 : Matrix m m ℝ) i j :=
  and_congr_right fun _ ↦ tendsto_flow_diagonal_one_iff _

/-- For `X = O * diagonal d * O⁻¹`, for instance a symmetric `X` in an orthonormal eigenbasis,
`g ∈ G` lies in the dynamic parabolic subgroup exactly when the entries `(i, j)` of
`O⁻¹ * g * O` with `d i < d j` vanish. -/
theorem mem_dynamicParabolic_units_conj_diagonal_iff :
    g ∈ G.dynamicParabolic (O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)) ↔
      g ∈ G ∧ ∀ i j, d i < d j → (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * g * O) i j = 0 :=
  and_congr_right fun _ ↦ (bddFlow_iff_diagonal rfl _).trans (bddFlow_diagonal_iff _)

/-- For `X = O * diagonal d * O⁻¹`, for instance a symmetric `X` in an orthonormal eigenbasis,
`g ∈ G` lies in the dynamic unipotent subgroup exactly when `(O⁻¹ * g * O) i j = δ i j` for all
`(i, j)` with `d i ≤ d j`. -/
theorem mem_dynamicUnipotent_units_conj_diagonal_iff :
    g ∈ G.dynamicUnipotent (O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)) ↔
      g ∈ G ∧ ∀ i j, d i ≤ d j →
        (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * g * O) i j = (1 : Matrix m m ℝ) i j := by
  refine and_congr_right fun _ ↦ ?_
  have h := tendsto_flow_iff_diagonal (O := O) (d := d) rfl (g : Matrix m m ℝ) 1
  rw [Matrix.mul_one, Units.inv_mul] at h
  exact h.trans (tendsto_flow_diagonal_one_iff _)

/-- For diagonal `X = diagonal d`, the dynamic Levi subgroup is block diagonal: `g ∈ G` lies in it
exactly when its entries `(i, j)` with `d i ≠ d j` vanish. -/
theorem mem_dynamicLevi_diagonal_iff :
    g ∈ G.dynamicLevi (diagonal d) ↔
      g ∈ G ∧ ∀ i j, d i ≠ d j → (g : Matrix m m ℝ) i j = 0 :=
  and_congr_right fun _ ↦ Commute.symm_iff.trans TauCeti.commute_diagonal_iff

/-- For `X = O * diagonal d * O⁻¹`, for instance a symmetric `X` in an orthonormal eigenbasis,
`g ∈ G` lies in the dynamic Levi subgroup exactly when the entries `(i, j)` of `O⁻¹ * g * O` with
`d i ≠ d j` vanish. -/
theorem mem_dynamicLevi_units_conj_diagonal_iff :
    g ∈ G.dynamicLevi (O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)) ↔
      g ∈ G ∧ ∀ i j, d i ≠ d j → (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * g * O) i j = 0 :=
  and_congr_right fun _ ↦ (commute_iff_diagonal rfl _).trans
    (Commute.symm_iff.trans TauCeti.commute_diagonal_iff)

end Symmetric

variable {G : Subgroup (GL m ℝ)} {X : Matrix m m ℝ}

/-- For symmetric `X` the dynamic parabolic subgroup of a closed subgroup is closed. In an
orthonormal eigenbasis of `X`, with eigenvalues `d`, it is cut out by the vanishing of the
entries `(i, j)` with `d i < d j`. -/
theorem isClosed_dynamicParabolic (hG : IsClosed (G : Set (GL m ℝ))) (hX : X.IsSymm) :
    IsClosed (G.dynamicParabolic X : Set (GL m ℝ)) := by
  obtain ⟨O, d, -, rfl⟩ := hX.exists_orthogonal_diagonal
  have : (G.dynamicParabolic (O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)) :
      Set (GL m ℝ)) = (G : Set (GL m ℝ)) ∩ ⋂ i, ⋂ j,
        {g | d i < d j → (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * g * O) i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_dynamicParabolic_units_conj_diagonal_iff
  rw [this]
  exact hG.inter (isClosed_iInter_apply_eq _ _ _ _)

/-- For symmetric `X` the dynamic unipotent subgroup of a closed subgroup is closed. In an
orthonormal eigenbasis of `X`, with eigenvalues `d`, it is cut out by the equations
`g i j = δ i j` for `d i ≤ d j`. -/
theorem isClosed_dynamicUnipotent (hG : IsClosed (G : Set (GL m ℝ))) (hX : X.IsSymm) :
    IsClosed (G.dynamicUnipotent X : Set (GL m ℝ)) := by
  obtain ⟨O, d, -, rfl⟩ := hX.exists_orthogonal_diagonal
  have : (G.dynamicUnipotent (O * diagonal d * ((O⁻¹ : GL m ℝ) : Matrix m m ℝ)) :
      Set (GL m ℝ)) = (G : Set (GL m ℝ)) ∩ ⋂ i, ⋂ j,
        {g | d i ≤ d j → (((O⁻¹ : GL m ℝ) : Matrix m m ℝ) * g * O) i j =
          (1 : Matrix m m ℝ) i j} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_dynamicUnipotent_units_conj_diagonal_iff
  rw [this]
  exact hG.inter (isClosed_iInter_apply_eq _ _ _ _)

/-- For symmetric `X` and `G` stable under the inverse transpose `θ g = (g⁻¹)ᵀ`, the dynamic
parabolic subgroup meets its image under `θ` exactly in the dynamic Levi subgroup. -/
theorem dynamicParabolic_inf_map_inverseTranspose
    (hG : ∀ g ∈ G, GeneralLinearGroup.inverseTranspose g ∈ G) (hX : X.IsSymm) :
    G.dynamicParabolic X ⊓
        (G.dynamicParabolic X).map GeneralLinearGroup.inverseTranspose.toMonoidHom =
      G.dynamicLevi X := by
  refine le_antisymm ?_ fun g hg ↦ mem_inf.2 ⟨dynamicLevi_le_dynamicParabolic G X hg, ?_⟩
  · intro g hg
    obtain ⟨hgQ, hgθ⟩ := mem_inf.1 hg
    rw [mem_map_equiv, GeneralLinearGroup.inverseTranspose_symm] at hgθ
    obtain ⟨O, d, hOt, hXd⟩ := hX.exists_orthogonal_diagonal
    -- In the eigenbasis, `g⁻¹` and its transpose both vanish below the eigenvalue order.
    have h1 := (bddFlow_diagonal_iff _).1
      ((bddFlow_iff_diagonal hXd _).1 ((G.dynamicParabolic X).inv_mem hgQ).2)
    have h2 := (bddFlow_diagonal_iff _).1 ((bddFlow_iff_diagonal hXd _).1 hgθ.2)
    rw [GeneralLinearGroup.coe_inverseTranspose, hOt] at h2
    have hc : Commute ((g⁻¹ : GL m ℝ) : Matrix m m ℝ) X := by
      refine (commute_iff_diagonal hXd _).2
        (TauCeti.commute_diagonal_of_apply_eq_zero fun i j hij ↦ ?_).symm
      rcases hij.lt_or_gt with h | h
      · exact h1 i j h
      · have e : (O : Matrix m m ℝ)ᵀ * ((g⁻¹ : GL m ℝ) : Matrix m m ℝ)ᵀ * (O : Matrix m m ℝ) =
            ((O : Matrix m m ℝ)ᵀ * ((g⁻¹ : GL m ℝ) : Matrix m m ℝ) * (O : Matrix m m ℝ))ᵀ := by
          simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
        have := h2 j i h
        rwa [e, transpose_apply, ← hOt] at this
    exact ⟨hgQ.1, by simpa only [inv_inv] using hc.units_inv_left⟩
  · rw [mem_map_equiv, GeneralLinearGroup.inverseTranspose_symm]
    refine dynamicLevi_le_dynamicParabolic G X ⟨hG g hg.1, ?_⟩
    have hc := hg.2.units_inv_left
    rw [GeneralLinearGroup.coe_inverseTranspose, commute_iff_eq, ← hX.eq, ← transpose_mul,
      ← transpose_mul, hc.eq]

/-- **The Levi decomposition of the dynamic parabolic subgroup.** Let `X` be symmetric and let
`G` be closed and normalized by every `exp (t • X)`. Then every element of the dynamic parabolic
subgroup of `X` is uniquely `l * u` with `l` in the dynamic Levi subgroup and `u` in the dynamic
unipotent subgroup. By `tendsto_dynamicLevi_mul_dynamicUnipotent`, the factor `l` is the limit of
the conjugates `exp (-t • X) * g * exp (t • X)` as `t → +∞`. -/
theorem existsUnique_dynamicLevi_mul_dynamicUnipotent (hG : IsClosed (G : Set (GL m ℝ)))
    (hX : X.IsSymm)
    (hGX : ∀ t : ℝ, ∀ g ∈ G, ∃ h ∈ G, (h : Matrix m m ℝ) = exp ((-t) • X) * g * exp (t • X))
    {g : GL m ℝ} (hg : g ∈ G.dynamicParabolic X) :
    ∃! p : GL m ℝ × GL m ℝ,
      p.1 ∈ G.dynamicLevi X ∧ p.2 ∈ G.dynamicUnipotent X ∧ p.1 * p.2 = g := by
  obtain ⟨l, hl, hlim⟩ := exists_mem_dynamicLevi_tendsto_flow hG hX hGX hg
  have hu : l⁻¹ * g ∈ G.dynamicUnipotent X := by
    refine ⟨G.mul_mem (G.inv_mem hl.1) hg.1, ?_⟩
    have h := (tendsto_const_nhds (x := ((l⁻¹ : GL m ℝ) : Matrix m m ℝ))).mul hlim
    rw [Units.inv_mul] at h
    have key (t : ℝ) : ((l⁻¹ : GL m ℝ) : Matrix m m ℝ) * flow X g t = flow X ↑(l⁻¹ * g) t := by
      rw [Units.val_mul, flow_mul, flow_of_commute hl.2.units_inv_left]
    exact h.congr key
  refine ⟨(l, l⁻¹ * g), ⟨hl, hu, mul_inv_cancel_left l g⟩, ?_⟩
  rintro ⟨l', u'⟩ ⟨hl', hu', rfl⟩
  have h : l⁻¹ * l' ∈ G.dynamicLevi X ⊓ G.dynamicUnipotent X := by
    refine mem_inf.2 ⟨(G.dynamicLevi X).mul_mem ((G.dynamicLevi X).inv_mem hl) hl', ?_⟩
    rw [show l⁻¹ * l' = l⁻¹ * (l' * u') * u'⁻¹ by group]
    exact (G.dynamicUnipotent X).mul_mem hu ((G.dynamicUnipotent X).inv_mem hu')
  rw [dynamicLevi_inf_dynamicUnipotent, mem_bot, inv_mul_eq_one] at h
  subst h
  simp

end Subgroup
