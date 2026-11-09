/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.IntegralDomain
public import TauCeti.Algebra.Group.Coprime
public import TauCeti.Analysis.Complex.RootsOfUnity.Circle
public import TauCeti.Topology.Algebra.Projectivization

/-!
# The weighted circle action on `ℂ²` and its ellipsoid quotient

Let `a` and `b` be positive natural numbers. The circle acts on `ℂ²` with weights `a` and `b`,

`u • (z₁, z₂) = (u ^ a z₁, u ^ b z₂)`

(`TauCeti.Toric.weightedRotation a b u`). For the angle `θ` and `u = exp(-i θ)` this is the action
`z_j ↦ exp(-i a_j θ) z_j`, which in the real coordinates `z_j = q_j + i p_j` is the weight model of
`TauCeti.weightMomentMap` with the weights `-a` and `-b`. With the standard symplectic form of
`ℂ²` and the convention `ι_{X_H} ω = dH` it therefore has the moment map
`μ(z) = (a |z₁|² + b |z₂|²) / 2`, whose level `ε` is the ellipsoid

`E = {z ∈ ℂ² | a |z₁|² + b |z₂|² = 2 ε}`

(`TauCeti.Toric.weightedEllipsoid a b ε`). It is compact and preserved by the action, which acts
on it continuously. For `a = b = 1` this is the Hopf action on a round three-sphere.

When `a` and `b` are coprime and `ε > 0`, the reduced space `E / S¹` is a topological sphere with
two points of nontrivial isotropy:

* **Stabilizers.** The circle element `u` fixes `z` exactly when `u ^ a = 1` if `z₁ ≠ 0` and
  `u ^ b = 1` if `z₂ ≠ 0`. Off the two coordinate axes the action is therefore free
  (`TauCeti.Toric.stabilizer_weightedEllipsoid_eq_bot`), while the points of `E` on the axis
  `z₂ = 0` have the cyclic stabilizer of `a`-th roots of unity, of order `a`
  (`TauCeti.Toric.nat_card_stabilizer_weightedEllipsoid_of_snd_eq_zero`), and those on the axis
  `z₁ = 0` the cyclic stabilizer of order `b`.
* **The quotient.** The weighted Hopf map `z ↦ [z₁ ^ b : z₂ ^ a]` to the complex projective line
  is invariant, because `u` multiplies both homogeneous coordinates by `u ^ (a b)`. Its fibres on
  `E` are exactly the orbits: if `(z₁ ^ b, z₂ ^ a) = c (w₁ ^ b, w₂ ^ a)` for `z, w ∈ E`, comparing
  the two sides of the defining equation of `E` forces `|c| = 1` and `|z_j| = |w_j|`, and the
  quotients `z_j / w_j` are circle elements `u₁, u₂` with `u₁ ^ b = u₂ ^ a`. Since `a` and `b` are
  coprime, a Bézout identity produces `v` with `v ^ a = u₁` and `v ^ b = u₂`
  (`TauCeti.exists_pow_eq_and_pow_eq_of_coprime`), so that `z = v • w`. Every line is reached,
  by scaling a choice of roots `(r₁, r₂)` with `r₁ ^ b = v₁` and `r₂ ^ a = v₂` along the weighted
  real dilation `λ ↦ (λ ^ a r₁, λ ^ b r₂)` until it meets `E`. Since `E` is compact and the
  projective line is Hausdorff, the induced continuous bijection is a homeomorphism
  `E / S¹ ≃ₜ ℂℙ¹` (`TauCeti.Toric.weightedOrbitHomeomorph`).
* **The isotropy points.** The axis `z₂ = 0` of `E`, with stabilizers of order `a`, is the fibre
  over `[1 : 0]`, and the axis `z₁ = 0`, with stabilizers of order `b`, is the fibre over
  `[0 : 1]`.

The homeomorphism records only the topology of the quotient; the stabilizers of orders `a` and `b`
over the two poles are recorded separately and are not erased.

## Main definitions

* `TauCeti.Toric.weightedRotation a b u`: the action `(z₁, z₂) ↦ (u ^ a z₁, u ^ b z₂)` of
  `u ∈ S¹` on `ℂ²`.
* `TauCeti.Toric.weightedEllipsoid a b ε`: the level `a |z₁|² + b |z₂|² = 2 ε`, with its action of
  the circle.
* `TauCeti.Toric.weightedHopf hε`: the map `z ↦ [z₁ ^ b : z₂ ^ a]` from the ellipsoid to `ℂℙ¹`.
* `TauCeti.Toric.weightedOrbitHomeomorph`: the homeomorphism of the orbit space with `ℂℙ¹`.

## Main results

* `TauCeti.Toric.weightedRotation_eq_self_iff`: the stabilizer of a point of `ℂ²`.
* `TauCeti.Toric.isCompact_weightedEllipsoid`: the ellipsoid is compact.
* `TauCeti.Toric.stabilizer_weightedEllipsoid_eq_bot`: the action is free off the axes.
* `TauCeti.Toric.nat_card_stabilizer_weightedEllipsoid_of_snd_eq_zero`,
  `TauCeti.Toric.nat_card_stabilizer_weightedEllipsoid_of_fst_eq_zero`: the axial stabilizers
  have orders `a` and `b`; `TauCeti.Toric.finite_stabilizer_weightedEllipsoid` and
  `TauCeti.Toric.isCyclic_stabilizer_weightedEllipsoid`: every stabilizer on the ellipsoid is
  finite cyclic.
* `TauCeti.Toric.weightedHopf_eq_weightedHopf_iff`: the fibres of the weighted Hopf map are the
  orbits.
* `TauCeti.Toric.weightedHopf_surjective`: the weighted Hopf map is surjective.
* `TauCeti.Toric.weightedHopf_eq_mk_iff_snd_eq_zero`,
  `TauCeti.Toric.weightedHopf_eq_mk_iff_fst_eq_zero`: the fibres over the two poles are the axes.

## References

* Eugene Lerman and Susan Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric
  varieties*, Trans. Amer. Math. Soc. 349 (1997), 4201–4230 (weighted projective spaces as
  symplectic quotients).
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer
  (2001), Part IX (symplectic reduction of `ℂⁿ` by circle actions).
-/

public section

noncomputable section

open Set Filter Topology Projectivization
open scoped LinearAlgebra.Projectivization

namespace TauCeti.Toric

variable (a b : ℕ)

/-! ### The weighted circle action -/

/-- The action `(z₁, z₂) ↦ (u ^ a z₁, u ^ b z₂)` of a circle element `u` on `ℂ²`, with weights
`a` and `b`. The rotation by the angle `θ` in the convention `z_j ↦ exp(-i a_j θ) z_j` is the
action of `u = exp(-i θ)`. -/
def weightedRotation (u : Circle) (z : ℂ × ℂ) : ℂ × ℂ :=
  ((u : ℂ) ^ a * z.1, (u : ℂ) ^ b * z.2)

variable {a b}

@[simp]
theorem weightedRotation_fst (u : Circle) (z : ℂ × ℂ) :
    (weightedRotation a b u z).1 = (u : ℂ) ^ a * z.1 :=
  (rfl)

@[simp]
theorem weightedRotation_snd (u : Circle) (z : ℂ × ℂ) :
    (weightedRotation a b u z).2 = (u : ℂ) ^ b * z.2 :=
  (rfl)

@[simp]
theorem weightedRotation_one (z : ℂ × ℂ) : weightedRotation a b 1 z = z := by
  simp [weightedRotation]

theorem weightedRotation_mul (u v : Circle) (z : ℂ × ℂ) :
    weightedRotation a b (u * v) z = weightedRotation a b u (weightedRotation a b v z) := by
  simp [weightedRotation, mul_pow, mul_assoc]

theorem continuous_weightedRotation :
    Continuous fun p : Circle × (ℂ × ℂ) ↦ weightedRotation a b p.1 p.2 := by
  unfold weightedRotation
  fun_prop

/-- **The stabilizer of a point of `ℂ²`.** The circle element `u` fixes `z` exactly when
`u ^ a = 1` in case `z₁ ≠ 0`, and `u ^ b = 1` in case `z₂ ≠ 0`. -/
theorem weightedRotation_eq_self_iff {u : Circle} {z : ℂ × ℂ} :
    weightedRotation a b u z = z ↔ (z.1 ≠ 0 → u ^ a = 1) ∧ (z.2 ≠ 0 → u ^ b = 1) := by
  simp only [Prod.ext_iff, weightedRotation_fst, weightedRotation_snd, mul_left_eq_self₀,
    ← Circle.coe_pow, Circle.coe_eq_one]
  tauto

/-! ### The ellipsoid -/

variable (a b) in
/-- The ellipsoid `a |z₁|² + b |z₂|² = 2 ε` in `ℂ²`, the level `ε` of the moment map
`(a |z₁|² + b |z₂|²) / 2` of the weighted circle action. -/
def weightedEllipsoid (ε : ℝ) : Set (ℂ × ℂ) :=
  {z | a * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2 = 2 * ε}

variable {ε : ℝ}

theorem mem_weightedEllipsoid {z : ℂ × ℂ} :
    z ∈ weightedEllipsoid a b ε ↔ a * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2 = 2 * ε :=
  Iff.rfl

@[simp]
theorem weightedRotation_mem_weightedEllipsoid_iff {u : Circle} {z : ℂ × ℂ} :
    weightedRotation a b u z ∈ weightedEllipsoid a b ε ↔ z ∈ weightedEllipsoid a b ε := by
  simp [mem_weightedEllipsoid]

theorem isClosed_weightedEllipsoid : IsClosed (weightedEllipsoid a b ε) :=
  isClosed_eq (by fun_prop) continuous_const

/-- **The ellipsoid is compact** for positive weights. -/
theorem isCompact_weightedEllipsoid (ha : 0 < a) (hb : 0 < b) :
    IsCompact (weightedEllipsoid a b ε) := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_weightedEllipsoid
    ((Metric.isBounded_closedBall (x := (0 : ℂ × ℂ)) (r := √(2 * ε))).subset fun z hz ↦ ?_)
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have h₁ := sq_nonneg ‖z.1‖
  have h₂ := sq_nonneg ‖z.2‖
  rw [mem_weightedEllipsoid] at hz
  have hε : 0 ≤ 2 * ε := by rw [← hz]; positivity
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  exact ⟨(Real.le_sqrt (norm_nonneg _) hε).2 (by nlinarith),
    (Real.le_sqrt (norm_nonneg _) hε).2 (by nlinarith)⟩

/-- The circle acts on the ellipsoid by the weighted rotations. -/
instance : MulAction Circle (weightedEllipsoid a b ε) where
  smul u z := ⟨weightedRotation a b u z, weightedRotation_mem_weightedEllipsoid_iff.2 z.2⟩
  one_smul z := Subtype.ext (weightedRotation_one (z : ℂ × ℂ))
  mul_smul u v z := Subtype.ext (weightedRotation_mul u v (z : ℂ × ℂ))

@[simp]
theorem coe_smul_weightedEllipsoid (u : Circle) (z : weightedEllipsoid a b ε) :
    ((u • z : weightedEllipsoid a b ε) : ℂ × ℂ) = weightedRotation a b u z :=
  rfl

/-- The weighted circle action on the ellipsoid is continuous. -/
instance : ContinuousSMul Circle (weightedEllipsoid a b ε) :=
  ⟨continuous_induced_rng.2 <| continuous_weightedRotation.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩

/-! ### Stabilizers -/

theorem mem_stabilizer_weightedEllipsoid_iff {z : weightedEllipsoid a b ε} {u : Circle} :
    u ∈ MulAction.stabilizer Circle z ↔
      ((z : ℂ × ℂ).1 ≠ 0 → u ^ a = 1) ∧ ((z : ℂ × ℂ).2 ≠ 0 → u ^ b = 1) := by
  rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj, coe_smul_weightedEllipsoid,
    weightedRotation_eq_self_iff]

/-- **Freeness off the axes.** For coprime weights, a point of the ellipsoid with both coordinates
nonzero has trivial stabilizer. -/
theorem stabilizer_weightedEllipsoid_eq_bot (hab : a.Coprime b) {z : weightedEllipsoid a b ε}
    (h₁ : (z : ℂ × ℂ).1 ≠ 0) (h₂ : (z : ℂ × ℂ).2 ≠ 0) :
    MulAction.stabilizer Circle z = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu ↦ ?_
  obtain ⟨hua, hub⟩ := mem_stabilizer_weightedEllipsoid_iff.1 hu
  simpa [hab.gcd_eq_one] using pow_gcd_eq_one.2 ⟨hua h₁, hub h₂⟩

/-- On the axis `z₂ = 0`, away from the origin, the stabilizer consists of the `a`-th roots of
unity. -/
theorem mem_stabilizer_weightedEllipsoid_iff_of_snd_eq_zero {z : weightedEllipsoid a b ε}
    (h₁ : (z : ℂ × ℂ).1 ≠ 0) (h₂ : (z : ℂ × ℂ).2 = 0) {u : Circle} :
    u ∈ MulAction.stabilizer Circle z ↔ u ^ a = 1 := by
  rw [mem_stabilizer_weightedEllipsoid_iff]
  simp [h₁, h₂]

/-- On the axis `z₁ = 0`, away from the origin, the stabilizer consists of the `b`-th roots of
unity. -/
theorem mem_stabilizer_weightedEllipsoid_iff_of_fst_eq_zero {z : weightedEllipsoid a b ε}
    (h₁ : (z : ℂ × ℂ).1 = 0) (h₂ : (z : ℂ × ℂ).2 ≠ 0) {u : Circle} :
    u ∈ MulAction.stabilizer Circle z ↔ u ^ b = 1 := by
  rw [mem_stabilizer_weightedEllipsoid_iff]
  simp [h₁, h₂]

/-- **The stabilizer on the axis `z₂ = 0` has order `a`.** -/
theorem nat_card_stabilizer_weightedEllipsoid_of_snd_eq_zero (ha : 0 < a)
    {z : weightedEllipsoid a b ε} (h₁ : (z : ℂ × ℂ).1 ≠ 0) (h₂ : (z : ℂ × ℂ).2 = 0) :
    Nat.card (MulAction.stabilizer Circle z) = a := by
  have : NeZero a := ⟨ha.ne'⟩
  refine (Nat.card_congr <| toUnits.toEquiv.subtypeEquiv fun u ↦ ?_).trans
    (Circle.nat_card_rootsOfUnity a)
  simp [mem_stabilizer_weightedEllipsoid_iff_of_snd_eq_zero h₁ h₂, mem_rootsOfUnity, ← map_pow]

/-- **The stabilizer on the axis `z₁ = 0` has order `b`.** -/
theorem nat_card_stabilizer_weightedEllipsoid_of_fst_eq_zero (hb : 0 < b)
    {z : weightedEllipsoid a b ε} (h₁ : (z : ℂ × ℂ).1 = 0) (h₂ : (z : ℂ × ℂ).2 ≠ 0) :
    Nat.card (MulAction.stabilizer Circle z) = b := by
  have : NeZero b := ⟨hb.ne'⟩
  refine (Nat.card_congr <| toUnits.toEquiv.subtypeEquiv fun u ↦ ?_).trans
    (Circle.nat_card_rootsOfUnity b)
  simp [mem_stabilizer_weightedEllipsoid_iff_of_fst_eq_zero h₁ h₂, mem_rootsOfUnity, ← map_pow]

/-- **Every stabilizer on the ellipsoid is finite** for positive weights and `ε > 0`: it is
contained in the group of `a`-th or of `b`-th roots of unity. -/
theorem finite_stabilizer_weightedEllipsoid (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (z : weightedEllipsoid a b ε) : Finite (MulAction.stabilizer Circle z) := by
  obtain h₁ | h₁ := eq_or_ne (z : ℂ × ℂ).1 0
  · have h₂ : (z : ℂ × ℂ).2 ≠ 0 := fun h₂ ↦ by
      have hz := mem_weightedEllipsoid.1 z.2
      simp only [h₁, h₂, norm_zero] at hz
      linarith
    exact Nat.finite_of_card_ne_zero <| by
      rw [nat_card_stabilizer_weightedEllipsoid_of_fst_eq_zero hb h₁ h₂]
      exact hb.ne'
  · have : NeZero a := ⟨ha.ne'⟩
    have : Finite (rootsOfUnity a Circle) := Nat.finite_of_card_ne_zero <| by
      rw [Circle.nat_card_rootsOfUnity]
      exact ha.ne'
    refine Finite.of_injective (β := rootsOfUnity a Circle)
      (fun u ↦ ⟨toUnits (u : Circle), ?_⟩) fun u v h ↦ ?_
    · simp [mem_rootsOfUnity, ← map_pow, (mem_stabilizer_weightedEllipsoid_iff.1 u.2).1 h₁]
    · exact Subtype.ext (toUnits.injective (congrArg Subtype.val h :))

/-- **Every stabilizer on the ellipsoid is cyclic** for positive weights and `ε > 0`, being a
finite subgroup of the circle. -/
theorem isCyclic_stabilizer_weightedEllipsoid (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (z : weightedEllipsoid a b ε) : IsCyclic (MulAction.stabilizer Circle z) := by
  have := finite_stabilizer_weightedEllipsoid ha hb hε z
  exact isCyclic_of_injective_ringHom (Circle.coeHom.comp (MulAction.stabilizer Circle z).subtype)
    (Circle.coe_injective.comp Subtype.val_injective)

/-! ### The weighted Hopf map -/

variable (a b) in
/-- The homogeneous coordinates `(z₁ ^ b, z₂ ^ a)` of the weighted Hopf map. -/
def weightedHopfVector (z : ℂ × ℂ) : Fin 2 → ℂ :=
  ![z.1 ^ b, z.2 ^ a]

@[simp]
theorem weightedHopfVector_zero (z : ℂ × ℂ) : weightedHopfVector a b z 0 = z.1 ^ b :=
  (rfl)

@[simp]
theorem weightedHopfVector_one (z : ℂ × ℂ) : weightedHopfVector a b z 1 = z.2 ^ a :=
  (rfl)

theorem continuous_weightedHopfVector : Continuous (weightedHopfVector a b) :=
  continuous_pi fun i ↦ by fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one,
    weightedHopfVector_zero, weightedHopfVector_one] <;> fun_prop

/-- The weighted rotation by `u` multiplies both homogeneous coordinates by `u ^ (a b)`. -/
theorem weightedHopfVector_weightedRotation (u : Circle) (z : ℂ × ℂ) :
    weightedHopfVector a b (weightedRotation a b u z) =
      ((u : ℂ) ^ (a * b)) • weightedHopfVector a b z := by
  ext i
  fin_cases i <;> simp [mul_pow, ← pow_mul, mul_comm a b]

theorem weightedHopfVector_ne_zero (hε : 0 < ε) {z : ℂ × ℂ} (hz : z ∈ weightedEllipsoid a b ε) :
    weightedHopfVector a b z ≠ 0 := by
  intro h
  have h₁ : z.1 = 0 := eq_zero_of_pow_eq_zero (by simpa using congrFun h 0)
  have h₂ : z.2 = 0 := eq_zero_of_pow_eq_zero (by simpa using congrFun h 1)
  have hz' := mem_weightedEllipsoid.1 hz
  simp only [h₁, h₂, norm_zero] at hz'
  linarith

/-- If the weighted Hopf vectors of two points of the ellipsoid are proportional, the two points
have coordinates of equal moduli. Comparing `|z₁| ^ b = |c| |w₁| ^ b` and `|z₂| ^ a = |c| |w₂| ^ a`
with the defining equation of the ellipsoid forces `|c| = 1`. -/
theorem norm_eq_of_weightedHopfVector_eq_smul (ha : 0 < a) (hb : 0 < b) {z w : ℂ × ℂ}
    (hz : z ∈ weightedEllipsoid a b ε) (hw : w ∈ weightedEllipsoid a b ε) {c : ℂ}
    (h : weightedHopfVector a b z = c • weightedHopfVector a b w) :
    ‖z.1‖ = ‖w.1‖ ∧ ‖z.2‖ = ‖w.2‖ := by
  have h₁ : ‖z.1‖ ^ b = ‖c‖ * ‖w.1‖ ^ b := by
    simpa [norm_pow] using congrArg norm (congrFun h 0)
  have h₂ : ‖z.2‖ ^ a = ‖c‖ * ‖w.2‖ ^ a := by
    simpa [norm_pow] using congrArg norm (congrFun h 1)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hzw := (mem_weightedEllipsoid.1 hz).trans (mem_weightedEllipsoid.1 hw).symm
  -- If the moduli of `z` are coordinatewise at most those of `w`, they are equal.
  have key {x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxx : x ≤ x') (hyy : y ≤ y')
      (hxy : a * x ^ 2 + b * y ^ 2 = a * x' ^ 2 + b * y' ^ 2) : x = x' ∧ y = y' := by
    have hx2 := pow_le_pow_left₀ hx hxx 2
    have hy2 := pow_le_pow_left₀ hy hyy 2
    have hx2' : x ^ 2 = x' ^ 2 := by nlinarith
    have hy2' : y ^ 2 = y' ^ 2 := by nlinarith
    exact ⟨(pow_left_inj₀ hx (hx.trans hxx) two_ne_zero).1 hx2',
      (pow_left_inj₀ hy (hy.trans hyy) two_ne_zero).1 hy2'⟩
  obtain hc | hc := le_total ‖c‖ 1
  · have hle₁ : ‖z.1‖ ≤ ‖w.1‖ := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      hb.ne').1 (h₁ ▸ mul_le_of_le_one_left (by positivity) hc)
    have hle₂ : ‖z.2‖ ≤ ‖w.2‖ := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      ha.ne').1 (h₂ ▸ mul_le_of_le_one_left (by positivity) hc)
    exact key (norm_nonneg _) (norm_nonneg _) hle₁ hle₂ (by linarith)
  · have hle₁ : ‖w.1‖ ≤ ‖z.1‖ := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      hb.ne').1 (h₁ ▸ le_mul_of_one_le_left (by positivity) hc)
    have hle₂ : ‖w.2‖ ≤ ‖z.2‖ := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      ha.ne').1 (h₂ ▸ le_mul_of_one_le_left (by positivity) hc)
    obtain ⟨h₁', h₂'⟩ := key (norm_nonneg _) (norm_nonneg _) hle₁ hle₂ (by linarith)
    exact ⟨h₁'.symm, h₂'.symm⟩

/-- The circle element `z / w`, for complex numbers of equal nonzero modulus. -/
private def circleDiv {z w : ℂ} (hw : w ≠ 0) (h : ‖z‖ = ‖w‖) : Circle :=
  ⟨z / w, mem_sphere_zero_iff_norm.2 <| by rw [norm_div, h, div_self (norm_ne_zero_iff.2 hw)]⟩

private theorem coe_circleDiv {z w : ℂ} (hw : w ≠ 0) (h : ‖z‖ = ‖w‖) :
    (circleDiv hw h : ℂ) = z / w :=
  rfl

/-- **The fibres of the weighted Hopf map are orbits.** For coprime positive weights, if the
weighted Hopf vectors of two points `z` and `w` of the ellipsoid are proportional, then `z` lies in
the orbit of `w`. -/
theorem exists_weightedRotation_eq_of_weightedHopfVector_eq_smul (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) {z w : ℂ × ℂ} (hz : z ∈ weightedEllipsoid a b ε)
    (hw : w ∈ weightedEllipsoid a b ε) {c : ℂ}
    (h : weightedHopfVector a b z = c • weightedHopfVector a b w) :
    ∃ u : Circle, weightedRotation a b u w = z := by
  obtain ⟨n₁, n₂⟩ := norm_eq_of_weightedHopfVector_eq_smul ha hb hz hw h
  have h₁ : z.1 ^ b = c * w.1 ^ b := by simpa using congrFun h 0
  have h₂ : z.2 ^ a = c * w.2 ^ a := by simpa using congrFun h 1
  -- A circle element `v` with `v ^ a = z₁ / w₁` (when `w₁ ≠ 0`) and `v ^ b = z₂ / w₂`
  -- (when `w₂ ≠ 0`) moves `w` to `z`; a vanishing coordinate of `w` vanishes in `z` too.
  have hrot {v : Circle} (hv₁ : ∀ hw₁ : w.1 ≠ 0, v ^ a = circleDiv hw₁ n₁)
      (hv₂ : ∀ hw₂ : w.2 ≠ 0, v ^ b = circleDiv hw₂ n₂) : weightedRotation a b v w = z := by
    refine Prod.ext ?_ ?_
    · obtain hw₁ | hw₁ := eq_or_ne w.1 0
      · simp [hw₁, norm_eq_zero.1 (n₁.trans (by simp [hw₁]))]
      · simp [← Circle.coe_pow, hv₁ hw₁, coe_circleDiv, div_mul_cancel₀ _ hw₁]
    · obtain hw₂ | hw₂ := eq_or_ne w.2 0
      · simp [hw₂, norm_eq_zero.1 (n₂.trans (by simp [hw₂]))]
      · simp [← Circle.coe_pow, hv₂ hw₂, coe_circleDiv, div_mul_cancel₀ _ hw₂]
  obtain hw₁ | hw₁ := eq_or_ne w.1 0
  · obtain ⟨v, hv⟩ := (Circle.exists_pow_eq hb.ne') (if hw₂ : w.2 = 0 then 1 else circleDiv hw₂ n₂)
    exact ⟨v, hrot (fun h ↦ absurd hw₁ h) fun hw₂ ↦ by simpa [hw₂] using hv⟩
  obtain hw₂ | hw₂ := eq_or_ne w.2 0
  · obtain ⟨v, hv⟩ := (Circle.exists_pow_eq ha.ne') (circleDiv hw₁ n₁)
    exact ⟨v, hrot (fun _ ↦ hv) fun h ↦ absurd hw₂ h⟩
  -- Both coordinates of `w` are nonzero: `(z₁ / w₁) ^ b = c = (z₂ / w₂) ^ a`.
  have hpow : circleDiv hw₁ n₁ ^ b = circleDiv hw₂ n₂ ^ a := by
    ext
    simp only [Circle.coe_pow, coe_circleDiv, div_pow, h₁, h₂]
    rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hw₁), mul_div_cancel_right₀ _ (pow_ne_zero _ hw₂)]
  obtain ⟨v, hv₁, hv₂⟩ := exists_pow_eq_and_pow_eq_of_coprime hab hpow
  exact ⟨v, hrot (fun _ ↦ hv₁) fun _ ↦ hv₂⟩

/-- **Weighted dilations reach the ellipsoid.** For positive weights and `ε > 0`, every nonzero
`r ∈ ℂ²` has a positive real multiple `λ` for which `(λ ^ a r₁, λ ^ b r₂)` lies on the ellipsoid. -/
theorem exists_pos_mem_weightedEllipsoid (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) {r : ℂ × ℂ}
    (hr : r ≠ 0) : ∃ t : ℝ, 0 < t ∧
      (((t : ℂ) ^ a * r.1, (t : ℂ) ^ b * r.2) : ℂ × ℂ) ∈ weightedEllipsoid a b ε := by
  set f : ℝ → ℝ := fun t ↦ a * (t ^ a * ‖r.1‖) ^ 2 + b * (t ^ b * ‖r.2‖) ^ 2 with hf
  have hcont : Continuous f := by fun_prop
  have hf0 : f 0 = 0 := by simp [hf, ha.ne', hb.ne']
  have htop : Tendsto f atTop atTop := by
    have hpos (n : ℕ) (hn : 0 < n) (x : ℂ) (hx : x ≠ 0) :
        Tendsto (fun t : ℝ ↦ (n * ‖x‖ ^ 2) * t ^ (2 * n)) atTop atTop :=
      (tendsto_pow_atTop (by omega)).const_mul_atTop (by positivity)
    obtain h₁ | h₁ := ne_or_eq r.1 0
    · refine tendsto_atTop_mono (fun t ↦ ?_) (hpos a ha r.1 h₁)
      have : (t ^ a * ‖r.1‖) ^ 2 = ‖r.1‖ ^ 2 * t ^ (2 * a) := by ring
      simp only [hf, this]
      nlinarith [sq_nonneg (t ^ b * ‖r.2‖), (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
    · have h₂ : r.2 ≠ 0 := fun h₂ ↦ hr (Prod.ext h₁ h₂)
      refine tendsto_atTop_mono (fun t ↦ ?_) (hpos b hb r.2 h₂)
      have : (t ^ b * ‖r.2‖) ^ 2 = ‖r.2‖ ^ 2 * t ^ (2 * b) := by ring
      simp only [hf, this]
      nlinarith [sq_nonneg (t ^ a * ‖r.1‖), (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Ici hcont.continuousOn htop
    (show f 0 ≤ 2 * ε by rw [hf0]; positivity)
  refine ⟨t, lt_of_le_of_ne ht ?_, ?_⟩
  · rintro rfl
    rw [hf0] at hft
    linarith
  · rw [mem_weightedEllipsoid, ← hft]
    simp [hf, norm_pow, abs_of_nonneg (show (0 : ℝ) ≤ t from ht)]

/-! ### The orbit space of the ellipsoid -/

/-- The **weighted Hopf map** `z ↦ [z₁ ^ b : z₂ ^ a]` from the ellipsoid to the complex projective
line, for `ε > 0`. -/
def weightedHopf (hε : 0 < ε) (z : weightedEllipsoid a b ε) : ℙ ℂ (Fin 2 → ℂ) :=
  mk ℂ (weightedHopfVector a b z) (weightedHopfVector_ne_zero hε z.2)

theorem weightedHopf_def (hε : 0 < ε) (z : weightedEllipsoid a b ε) :
    weightedHopf hε z = mk ℂ (weightedHopfVector a b z) (weightedHopfVector_ne_zero hε z.2) :=
  (rfl)

theorem continuous_weightedHopf (hε : 0 < ε) : Continuous (weightedHopf (a := a) (b := b) hε) :=
  continuous_mk (continuous_weightedHopfVector.comp continuous_subtype_val) _

/-- The weighted Hopf map is invariant under the weighted circle action. -/
@[simp]
theorem weightedHopf_smul (hε : 0 < ε) (u : Circle) (z : weightedEllipsoid a b ε) :
    weightedHopf hε (u • z) = weightedHopf hε z := by
  rw [weightedHopf_def, weightedHopf_def, mk_eq_mk_iff']
  exact ⟨(u : ℂ) ^ (a * b), (weightedHopfVector_weightedRotation u z).symm⟩

/-- **The fibres of the weighted Hopf map are the orbits** of the weighted circle action on the
ellipsoid, for coprime positive weights. -/
theorem weightedHopf_eq_weightedHopf_iff (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hε : 0 < ε) {z w : weightedEllipsoid a b ε} :
    weightedHopf hε z = weightedHopf hε w ↔ z ∈ MulAction.orbit Circle w := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨c, hc⟩ := (mk_eq_mk_iff' ℂ _ _ _ _).1 h
    obtain ⟨u, hu⟩ := exists_weightedRotation_eq_of_weightedHopfVector_eq_smul ha hb hab z.2 w.2
      hc.symm
    exact ⟨u, Subtype.ext hu⟩
  · rintro ⟨u, rfl⟩
    exact weightedHopf_smul hε u w

/-- **The weighted Hopf map is surjective** for positive weights: every complex line through
`(v₁, v₂)` contains the weighted Hopf vector of a point of the ellipsoid. Choosing roots
`r₁ ^ b = v₁` and `r₂ ^ a = v₂`, a weighted dilation `(λ ^ a r₁, λ ^ b r₂)` with `λ > 0` lies on the
ellipsoid and has weighted Hopf vector `λ ^ (a b) v`. -/
theorem weightedHopf_surjective (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    Function.Surjective (weightedHopf (a := a) (b := b) hε) := by
  intro x
  obtain ⟨v, hv, rfl⟩ : ∃ v hv, mk ℂ v hv = x := ⟨x.rep, x.rep_ne_zero, x.mk_rep⟩
  set r : ℂ × ℂ := (v 0 ^ ((b : ℂ)⁻¹), v 1 ^ ((a : ℂ)⁻¹)) with hr
  have hrv : weightedHopfVector a b r = v := by
    ext i
    fin_cases i
    · simp [hr, Complex.cpow_nat_inv_pow _ hb.ne']
    · simp [hr, Complex.cpow_nat_inv_pow _ ha.ne']
  have hr0 : r ≠ 0 := by
    rintro h
    refine hv ?_
    rw [← hrv, h]
    ext i
    fin_cases i <;> simp [weightedHopfVector, ha.ne', hb.ne']
  obtain ⟨t, -, ht⟩ := exists_pos_mem_weightedEllipsoid ha hb hε hr0
  refine ⟨⟨_, ht⟩, ?_⟩
  rw [weightedHopf_def, mk_eq_mk_iff']
  refine ⟨(t : ℂ) ^ (a * b), ?_⟩
  rw [← hrv]
  ext i
  fin_cases i <;> simp [mul_pow, ← pow_mul, mul_comm a b]

/-- The weighted Hopf map sends a point of the ellipsoid to `[1 : 0]` exactly when it lies on the
axis `z₂ = 0`, where the stabilizer has order `a`. -/
theorem weightedHopf_eq_mk_iff_snd_eq_zero (ha : 0 < a) (hε : 0 < ε)
    (z : weightedEllipsoid a b ε) :
    weightedHopf hε z = mk ℂ ![1, 0] (by simp) ↔ (z : ℂ × ℂ).2 = 0 := by
  rw [weightedHopf_def, mk_eq_mk_iff']
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ ⟨(z : ℂ × ℂ).1 ^ b, ?_⟩⟩
  · exact eq_zero_of_pow_eq_zero (n := a) (by simpa using (congrFun hc 1).symm)
  · ext i
    fin_cases i <;> simp [h, ha.ne']

/-- The weighted Hopf map sends a point of the ellipsoid to `[0 : 1]` exactly when it lies on the
axis `z₁ = 0`, where the stabilizer has order `b`. -/
theorem weightedHopf_eq_mk_iff_fst_eq_zero (hb : 0 < b) (hε : 0 < ε)
    (z : weightedEllipsoid a b ε) :
    weightedHopf hε z = mk ℂ ![0, 1] (by simp) ↔ (z : ℂ × ℂ).1 = 0 := by
  rw [weightedHopf_def, mk_eq_mk_iff']
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ ⟨(z : ℂ × ℂ).2 ^ a, ?_⟩⟩
  · exact eq_zero_of_pow_eq_zero (n := b) (by simpa using (congrFun hc 0).symm)
  · ext i
    fin_cases i <;> simp [h, hb.ne']

/-- **The weighted quotient of the ellipsoid is a sphere.** For coprime positive weights and
`ε > 0`, the weighted Hopf map induces a homeomorphism from the orbit space of the weighted circle
action on the ellipsoid `a |z₁|² + b |z₂|² = 2 ε` onto the complex projective line. -/
def weightedOrbitHomeomorph (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hε : 0 < ε) :
    MulAction.orbitRel.Quotient Circle (weightedEllipsoid a b ε) ≃ₜ ℙ ℂ (Fin 2 → ℂ) :=
  have : CompactSpace (weightedEllipsoid a b ε) :=
    isCompact_iff_compactSpace.1 (isCompact_weightedEllipsoid ha hb)
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective
      (Quotient.lift (weightedHopf hε) fun z w h ↦
        (weightedHopf_eq_weightedHopf_iff ha hb hab hε).2 h)
      ⟨fun z w h ↦ by
        induction z using Quotient.inductionOn
        induction w using Quotient.inductionOn
        exact Quotient.sound ((weightedHopf_eq_weightedHopf_iff ha hb hab hε).1 h),
      fun x ↦ by
        obtain ⟨z, hz⟩ := weightedHopf_surjective ha hb hε x
        exact ⟨Quotient.mk _ z, hz⟩⟩)
    (continuous_quot_lift _ (continuous_weightedHopf hε))

@[simp]
theorem weightedOrbitHomeomorph_mk (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hε : 0 < ε)
    (z : weightedEllipsoid a b ε) :
    weightedOrbitHomeomorph ha hb hab hε (Quotient.mk _ z) = weightedHopf hε z :=
  (rfl)

end TauCeti.Toric
