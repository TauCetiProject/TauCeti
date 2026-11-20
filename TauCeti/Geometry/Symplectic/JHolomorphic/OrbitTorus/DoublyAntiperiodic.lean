/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Antiperiodic
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.AntiperiodicSobolev

/-!
# The orbit-torus operator twisted along both circle factors

Let `C = S¹ × γ` be the orbit torus of a closed orbit `γ` of the suspension flow of a surface
diffeomorphism, and let `D = ∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, be its normal operator in a unitary
trivialization, as in `TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.AntiperiodicSobolev`.
Of the four real sign characters of the torus, two are nontrivial along the circle factor; for
these `D` acts on maps antiperiodic in `s`. The file `AntiperiodicSobolev` treats the one that is
trivial along `γ`. This file treats the remaining one, nontrivial along both factors, and proves
that `D` is invertible on it, along the whole path to the complex-linear operator `∂s + J₀ ∂t`.

**The spaces.** If `γ` has period `T / 2`, a map twisted along `γ` satisfies
`u (s, t + T / 2) = -u (s, t)`. Such a map has period `T` in `t`, and we realize it on that double
cover of `γ`: in the modes `u = ∑ₖ cos (ωₖ s) aₖ(t) + sin (ωₖ s) bₖ(t)` of
`TauCeti.antiperiodicSobolev F ℓ`, every loop `aₖ, bₖ` of period `T` is antiperiodic of antiperiod
`T / 2`, that is, its even Fourier coefficients vanish (`TauCeti.CircleSobolev.antiperiodic`,
`TauCeti.CircleSobolev.mem_antiperiodic_iff_toContinuousMap`). These maps form the closed subspace
`TauCeti.doublyAntiperiodicSobolev F ℓ` of the Sobolev space `H¹`, and the corresponding mode
sequences in `H⁰(F)²` form the subspace `TauCeti.doublyAntiperiodicL2 F` of the `L²` target.

**The operator.** The loop `S` of the orbit has period `T / 2`; read on the double cover it is a
loop of period `T` with `S (t + T / 2) = S t`. The rotation by `T / 2` then commutes with `A`
(`TauCeti.CircleSobolev.loopOperator_rotate`), so `D` maps the twisted maps to twisted maps, and
restricts to the operator `TauCeti.doublyAntiperiodicTorusOperator T ℓ S` between the two
subspaces.

**Invertibility.** On the double cover the operator `D` is invertible, for every infinitesimally
symplectic loop `S` (`TauCeti.isInvertible_antiperiodicTorusOperator`). It commutes with the half
rotation `R` of every mode, and the twisted maps are the solutions of `R x = -x`. If `D x` is
twisted, then `D (R x) = R (D x) = -D x = D (-x)`, so `R x = -x` by injectivity: the inverse of
`D` maps twisted targets to twisted maps. Hence the restricted operator is invertible
(`TauCeti.isInvertible_doublyAntiperiodicTorusOperator`). For `S = 0` it is complex linear
(`TauCeti.doublyAntiperiodicTorusOperator_zero_apply_smul`). Since `τ • S` is again
infinitesimally symplectic and invariant under the half rotation, every operator of the path
`τ ↦ ∂s + J₀ (∂t - τ S)` is invertible; this is the invertible homotopy to a complex-linear
reference operator along which the determinant line of the doubly twisted orbit-torus operator is
oriented.

## Main definitions

* `TauCeti.doublyAntiperiodicSobolev F ℓ`: the maps of `TauCeti.antiperiodicSobolev F ℓ` whose
  modes are antiperiodic of antiperiod `T / 2` in `t`.
* `TauCeti.doublyAntiperiodicL2 F`: the mode sequences in `H⁰(F)²` whose modes are antiperiodic.
* `TauCeti.doublyAntiperiodicTorusOperator T ℓ S hS`: for a loop `S` invariant under the rotation
  by `T / 2`, the restriction of `∂s + J₀ (∂t - S)` to these subspaces.

## Main results

* `TauCeti.antiperiodicTorusOperator_mem_doublyAntiperiodicL2`: the orbit-torus operator maps
  doubly twisted maps to doubly twisted targets.
* `TauCeti.doublyAntiperiodicTorusOperator_zero_apply_smul`: the reference operator `∂s + J₀ ∂t`
  is complex linear.
* `TauCeti.isInvertible_doublyAntiperiodicTorusOperator`: invertibility for every infinitesimally
  symplectic loop invariant under the rotation by `T / 2`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. Salamon, *Lectures on Floer homology*, in Symplectic Geometry and Topology,
  IAS/Park City Math. Ser. 7 (1999), Section 2, for the operator `∂s + A` with `A` self-adjoint.
-/

public section

noncomputable section

open Complex
open scoped Real lp

namespace TauCeti

open CircleSobolev

/-- The product of the two mode spaces carrying `TauCeti.antiperiodicSobolev`. -/
local notation "𝕏[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 1 F × CircleSobolev 1 F)) ×
  ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

/-- The `L²` space of mode sequences, the target of `TauCeti.antiperiodicTorusOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

section Space

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (F) in
/-- The Sobolev space `H¹` of maps `u(s, t)` antiperiodic of antiperiod `ℓ` in `s` and antiperiodic
of antiperiod `T / 2` in `t`, for any period `T` of the modes: the elements of
`TauCeti.antiperiodicSobolev F ℓ` all of whose modes `aₖ, bₖ` are antiperiodic loops
(`TauCeti.CircleSobolev.antiperiodic`). -/
def doublyAntiperiodicSobolev (ℓ : ℝ) : Submodule ℂ (antiperiodicSobolev F ℓ) where
  carrier := {x | ∀ k, ((x : 𝕏[F]).1 k).fst ∈ antiperiodic 1 F ∧
    ((x : 𝕏[F]).1 k).snd ∈ antiperiodic 1 F}
  add_mem' hx hy k := ⟨add_mem (hx k).1 (hy k).1, add_mem (hx k).2 (hy k).2⟩
  zero_mem' _ := ⟨zero_mem _, zero_mem _⟩
  smul_mem' c _ hx k := ⟨Submodule.smul_mem _ c (hx k).1, Submodule.smul_mem _ c (hx k).2⟩

theorem mem_doublyAntiperiodicSobolev_iff {ℓ : ℝ} {x : antiperiodicSobolev F ℓ} :
    x ∈ doublyAntiperiodicSobolev F ℓ ↔ ∀ k, ((x : 𝕏[F]).1 k).fst ∈ antiperiodic 1 F ∧
      ((x : 𝕏[F]).1 k).snd ∈ antiperiodic 1 F :=
  Iff.rfl

/-- `TauCeti.doublyAntiperiodicSobolev` is closed, as an intersection of preimages of the closed
subspaces of antiperiodic loops. -/
theorem isClosed_doublyAntiperiodicSobolev (ℓ : ℝ) :
    IsClosed (doublyAntiperiodicSobolev F ℓ : Set (antiperiodicSobolev F ℓ)) := by
  have : (doublyAntiperiodicSobolev F ℓ : Set (antiperiodicSobolev F ℓ)) =
      ⋂ k : ℕ, {x : antiperiodicSobolev F ℓ | ((x : 𝕏[F]).1 k).fst ∈ antiperiodic 1 F} ∩
        {x | ((x : 𝕏[F]).1 k).snd ∈ antiperiodic 1 F} := by
    ext x
    simp [mem_doublyAntiperiodicSobolev_iff, Set.mem_iInter]
  rw [this]
  have hk (k : ℕ) : Continuous fun x : antiperiodicSobolev F ℓ ↦ (x : 𝕏[F]).1 k :=
    (lp.evalCLM ℂ _ 2 k).continuous.comp (continuous_fst.comp continuous_subtype_val)
  exact isClosed_iInter fun k ↦
    (isClosed_antiperiodic.preimage (continuous_fst.comp ((WithLp.prod_continuous_ofLp 2 _ _).comp
      (hk k)))).inter
    (isClosed_antiperiodic.preimage (continuous_snd.comp ((WithLp.prod_continuous_ofLp 2 _ _).comp
      (hk k))))

/-- The Sobolev space `H¹` of maps antiperiodic in both factors is complete. -/
instance [CompleteSpace F] (ℓ : ℝ) : CompleteSpace (doublyAntiperiodicSobolev F ℓ) :=
  (isClosed_doublyAntiperiodicSobolev ℓ).completeSpace_coe

variable (F) in
/-- The `L²` space of maps antiperiodic in both factors, in modes: the mode sequences in `H⁰(F)²`
all of whose modes are antiperiodic loops (`TauCeti.CircleSobolev.antiperiodic`). It is the target
of `TauCeti.doublyAntiperiodicTorusOperator`. -/
def doublyAntiperiodicL2 : Submodule ℂ 𝕐[F] where
  carrier := {y | ∀ k, (y k).fst ∈ antiperiodic 0 F ∧ (y k).snd ∈ antiperiodic 0 F}
  add_mem' hx hy k := ⟨add_mem (hx k).1 (hy k).1, add_mem (hx k).2 (hy k).2⟩
  zero_mem' _ := ⟨zero_mem _, zero_mem _⟩
  smul_mem' c _ hx k := ⟨Submodule.smul_mem _ c (hx k).1, Submodule.smul_mem _ c (hx k).2⟩

theorem mem_doublyAntiperiodicL2_iff {y : 𝕐[F]} :
    y ∈ doublyAntiperiodicL2 F ↔
      ∀ k, (y k).fst ∈ antiperiodic 0 F ∧ (y k).snd ∈ antiperiodic 0 F :=
  Iff.rfl

/-- `TauCeti.doublyAntiperiodicL2` is closed, as an intersection of preimages of the closed
subspaces of antiperiodic loops. -/
theorem isClosed_doublyAntiperiodicL2 : IsClosed (doublyAntiperiodicL2 F : Set 𝕐[F]) := by
  have : (doublyAntiperiodicL2 F : Set 𝕐[F]) =
      ⋂ k : ℕ, {y : 𝕐[F] | (y k).fst ∈ antiperiodic 0 F} ∩ {y | (y k).snd ∈ antiperiodic 0 F} := by
    ext y
    simp [mem_doublyAntiperiodicL2_iff, Set.mem_iInter]
  rw [this]
  have hk (k : ℕ) : Continuous fun y : 𝕐[F] ↦ y k := (lp.evalCLM ℂ _ 2 k).continuous
  exact isClosed_iInter fun k ↦
    (isClosed_antiperiodic.preimage (continuous_fst.comp ((WithLp.prod_continuous_ofLp 2 _ _).comp
      (hk k)))).inter
    (isClosed_antiperiodic.preimage (continuous_snd.comp ((WithLp.prod_continuous_ofLp 2 _ _).comp
      (hk k))))

/-- The `L²` space of maps antiperiodic in both factors is complete. -/
instance [CompleteSpace F] : CompleteSpace (doublyAntiperiodicL2 F) :=
  isClosed_doublyAntiperiodicL2.completeSpace_coe

end Space

section Operator

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceDoublyAntiperiodic : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- For a loop `S` invariant under the rotation by `T / 2`, the orbit-torus operator `∂s + A` maps
maps antiperiodic in both factors to targets antiperiodic in both factors. -/
theorem antiperiodicTorusOperator_mem_doublyAntiperiodicL2 {ℓ : ℝ}
    {S : C(AddCircle T, F →L[ℝ] F)} (hS : ∀ t, S (t + (T / 2 : ℝ)) = S t)
    {x : antiperiodicSobolev F ℓ} (hx : x ∈ doublyAntiperiodicSobolev F ℓ) :
    antiperiodicTorusOperator T ℓ S x ∈ doublyAntiperiodicL2 F := fun k ↦ by
  rw [antiperiodicTorusOperator_apply_apply_eq]
  exact ⟨add_mem (Submodule.smul_mem _ I (loopOperator_mem_antiperiodic hS (hx k).1))
      (Submodule.smul_of_tower_mem _ _ (inclusion_mem_antiperiodic _ (hx k).2)),
    sub_mem (Submodule.smul_mem _ I (loopOperator_mem_antiperiodic hS (hx k).2))
      (Submodule.smul_of_tower_mem _ _ (inclusion_mem_antiperiodic _ (hx k).1))⟩

/-- The orbit-torus operator `∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, on maps antiperiodic of antiperiod
`ℓ` in `s` and of antiperiod `T / 2` in `t`, for a loop `S` of period `T` invariant under the
rotation by `T / 2`: the restriction of `TauCeti.antiperiodicTorusOperator T ℓ S` to
`TauCeti.doublyAntiperiodicSobolev F ℓ`, with values in `TauCeti.doublyAntiperiodicL2 F`. -/
def doublyAntiperiodicTorusOperator (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t, S (t + (T / 2 : ℝ)) = S t) :
    doublyAntiperiodicSobolev F ℓ →L[ℝ] doublyAntiperiodicL2 F where
  -- Built by hand rather than with `ContinuousLinearMap.restrict`, which would restrict to the
  -- real subspaces `Submodule.restrictScalars ℝ` and forget their complex structure.
  toFun x := ⟨antiperiodicTorusOperator T ℓ S x,
    antiperiodicTorusOperator_mem_doublyAntiperiodicL2 T hS x.2⟩
  map_add' x y :=
    Subtype.ext ((antiperiodicTorusOperator T ℓ S).map_add (x : antiperiodicSobolev F ℓ) y)
  map_smul' c x :=
    Subtype.ext ((antiperiodicTorusOperator T ℓ S).map_smul c (x : antiperiodicSobolev F ℓ))
  cont := ((antiperiodicTorusOperator T ℓ S).continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_doublyAntiperiodicTorusOperator_apply (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t, S (t + (T / 2 : ℝ)) = S t) (x : doublyAntiperiodicSobolev F ℓ) :
    (doublyAntiperiodicTorusOperator T ℓ S hS x : 𝕐[F]) = antiperiodicTorusOperator T ℓ S x :=
  (rfl)

/-- **The reference operator is complex linear.** For `S = 0` the operator `∂s + J₀ ∂t` on maps
antiperiodic in both factors commutes with multiplication by complex scalars, the complex
structure acting by `J₀`. -/
theorem doublyAntiperiodicTorusOperator_zero_apply_smul (ℓ : ℝ) (c : ℂ)
    (x : doublyAntiperiodicSobolev F ℓ) :
    doublyAntiperiodicTorusOperator T ℓ 0 (fun _ ↦ rfl) (c • x) =
      c • doublyAntiperiodicTorusOperator T ℓ 0 (fun _ ↦ rfl) x :=
  Subtype.ext (antiperiodicTorusOperator_zero_apply_smul T ℓ c (x : antiperiodicSobolev F ℓ))

/-! ### The half rotation -/

/-- The rotation by half the period of both loops of a mode. -/
private def halfRotatePair (s : ℝ) :
    WithLp 2 (CircleSobolev s F × CircleSobolev s F) →L[ℂ]
      WithLp 2 (CircleSobolev s F × CircleSobolev s F) :=
  let r : CircleSobolev s F →L[ℂ] CircleSobolev s F :=
    (rotate ((T / 2 : ℝ) : AddCircle T)).toLinearIsometry.toContinuousLinearMap
  r.withLpProdMap 2 r

omit hT [FiniteDimensional ℂ F] in
@[simp]
private theorem halfRotatePair_apply (s : ℝ)
    (y : WithLp 2 (CircleSobolev s F × CircleSobolev s F)) :
    halfRotatePair T s y = WithLp.toLp 2 (rotate ((T / 2 : ℝ) : AddCircle T) y.fst,
      rotate ((T / 2 : ℝ) : AddCircle T) y.snd) := by
  simp [halfRotatePair]

omit hT [FiniteDimensional ℂ F] in
/-- The half rotation of every mode of an element of `TauCeti.antiperiodicSobolev F ℓ`. -/
private def halfRotate {ℓ : ℝ} (x : antiperiodicSobolev F ℓ) : antiperiodicSobolev F ℓ :=
  ⟨(lp.ampliation ℕ 2 (halfRotatePair T 1) (x : 𝕏[F]).1,
      lp.ampliation ℕ 2 (halfRotatePair T 0) (x : 𝕏[F]).2), mem_antiperiodicSobolev_iff.2 fun k ↦ by
    rw [lp.ampliation_apply_apply, lp.ampliation_apply_apply, mem_antiperiodicSobolev_iff.1 x.2 k]
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;>
      simp [← Complex.coe_smul, map_smul]⟩

/-- For a loop `S` invariant under the rotation by `T / 2`, the orbit-torus operator commutes with
the half rotation of every mode. -/
private theorem antiperiodicTorusOperator_halfRotate {ℓ : ℝ} {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t, S (t + (T / 2 : ℝ)) = S t) (x : antiperiodicSobolev F ℓ) (k : ℕ) :
    antiperiodicTorusOperator T ℓ S (halfRotate T x) k =
      halfRotatePair T 0 (antiperiodicTorusOperator T ℓ S x k) := by
  have hS' : S.comp (ContinuousMap.addRight ((T / 2 : ℝ) : AddCircle T)) = S := by
    ext1 t
    simp [hS]
  rw [antiperiodicTorusOperator_apply_apply_eq, antiperiodicTorusOperator_apply_apply_eq]
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;>
    simp [halfRotate, ← Complex.coe_smul, ← loopOperator_rotate, hS']

end Operator

section Inner

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceDoublyAntiperiodicInner : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- If the orbit-torus operator maps `x` to a target antiperiodic in `t`, then `x` is antiperiodic
in `t`: the half rotation `R x` has image `R (D x) = -D x`, so `R x = -x` by injectivity. -/
private theorem mem_doublyAntiperiodicSobolev_of_mem {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hS' : ∀ t, S (t + (T / 2 : ℝ)) = S t) {x : antiperiodicSobolev F ℓ}
    (hx : antiperiodicTorusOperator T ℓ S x ∈ doublyAntiperiodicL2 F) :
    x ∈ doublyAntiperiodicSobolev F ℓ := by
  have hT : T ≠ 0 := hT.out.ne'
  have hrot : halfRotate T x = -x := by
    refine (isInvertible_antiperiodicTorusOperator T hℓ S hS).injective
      (lp.ext (funext fun k ↦ ?_))
    rw [antiperiodicTorusOperator_halfRotate T hS', map_neg]
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
    · simpa using (rotate_half_period_eq_neg_iff hT).2 (hx k).1
    · simpa using (rotate_half_period_eq_neg_iff hT).2 (hx k).2
  intro k
  have hk := congrArg (fun z : antiperiodicSobolev F ℓ ↦ (z : 𝕏[F]).1 k) hrot
  simp only [halfRotate, lp.ampliation_apply_apply, halfRotatePair_apply] at hk
  exact ⟨(rotate_half_period_eq_neg_iff hT).1 (by simpa using congrArg WithLp.fst hk),
    (rotate_half_period_eq_neg_iff hT).1 (by simpa using congrArg WithLp.snd hk)⟩

/-- **Invertibility along the homotopy to the complex-linear reference.** For every
infinitesimally symplectic loop `S` invariant under the rotation by `T / 2`, the orbit-torus
operator `∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, is invertible from the Sobolev space `H¹` of maps
antiperiodic in both factors onto the corresponding `L²` space. Since `τ • S` satisfies the same
hypotheses, every operator of the path `τ ↦ ∂s + J₀ (∂t - τ S)`, `τ ∈ [0, 1]`, is invertible, and
the path starts at the complex-linear operator `∂s + J₀ ∂t`
(`TauCeti.doublyAntiperiodicTorusOperator_zero_apply_smul`). -/
theorem isInvertible_doublyAntiperiodicTorusOperator {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hS' : ∀ t, S (t + (T / 2 : ℝ)) = S t) :
    (doublyAntiperiodicTorusOperator T ℓ S hS').IsInvertible := by
  have hD := isInvertible_antiperiodicTorusOperator T hℓ S hS
  set D := antiperiodicTorusOperator T ℓ S
  -- The inverse of `D` maps doubly antiperiodic targets to doubly antiperiodic maps.
  let G : doublyAntiperiodicL2 F →L[ℝ] doublyAntiperiodicSobolev F ℓ :=
    { toFun y := ⟨D.inverse y, mem_doublyAntiperiodicSobolev_of_mem T hℓ hS hS'
          (by rw [hD.self_apply_inverse]; exact y.2)⟩
      map_add' y z := Subtype.ext (D.inverse.map_add (y : 𝕐[F]) z)
      map_smul' c y := Subtype.ext (D.inverse.map_smul c (y : 𝕐[F]))
      cont := (D.inverse.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := G) ?_ ?_ <;> ext1 y <;>
    refine Subtype.ext ?_
  · exact hD.self_apply_inverse (y : 𝕐[F])
  · exact hD.inverse_apply_self (y : antiperiodicSobolev F ℓ)

end Inner

end TauCeti
