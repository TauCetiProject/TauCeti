/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.NumberTheory.Height.FamilyOverPairs

/-!
# Twisted lattices

A twisted lattice measures integrality through a family of linear maps, while measuring
sizes through one distinguished map. Each allowed twist has a local integral submodule at
every prime-adic embedding. The pairing of vectors integral at conjugate embeddings is
integral at the original embedding. Rational coordinates for the distinguished target
permit measuring sizes after arbitrary automorphisms of the complex numbers.

The integral vectors are the intersection of the pullbacks of the local submodules. In
particular, membership requires the same vector to be integral for every allowed twist.
Local submodules are recorded only for allowed twists, so there is no unused data at
forbidden twists.

The scalar example has identity maps and the usual integral submodule of the complex line;
it gives a nonzero twisted lattice for any set of twists.

The definitions follow `New.TwistedLattice`, `integralVectors` and `normSqAt` in
`New/Reduction/Lattices/TwistedLattice.lean` of
[grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207`. No source code is copied.
-/

public section

noncomputable section

open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Matrix

namespace TauCeti

/-- Linear maps equipped with compatible local integral submodules and rational coordinates
for the distinguished target. The scalar ring at `ι` consists of the complex numbers whose
images under `ι` have prime-adic norm at most one. -/
structure TwistedLattice (V T : Type*) [AddCommMonoid V] [Module ℂ V] [One T]
    (S : T → Type*) [∀ ξ, NormedAddCommGroup (S ξ)] [∀ ξ, InnerProductSpace ℂ (S ξ)]
    (C : Type*) [Fintype C] where
  /-- The map associated with each twist. -/
  lift : (ξ : T) → V →ₗ[ℂ] S ξ
  /-- The twists permitted at each rational prime. -/
  allowed : T → (p : ℕ) → [Fact p.Prime] → Prop
  /-- The local integral submodule for an allowed twist. -/
  integral : (ξ : T) → (ι : PrimePadicIso) → allowed ξ ι.prime →
    Submodule (Valued.v.comap ι.iso.toRingHom).integer (S ξ)
  /-- Integral vectors at conjugate embeddings have an integral pairing. -/
  integral_inner : ∀ (ξ : T) (ι : PrimePadicIso) (h : allowed ξ ι.prime)
    (x y : S ξ),
    x ∈ integral ξ { ι with iso := (starRingAut : ℂ ≃+* ℂ).trans ι.iso } h →
    y ∈ integral ξ ι h → ‖ι.iso ⟪x, y⟫_ℂ‖ ≤ 1
  /-- Coordinates for the distinguished target. -/
  coord : S 1 →ₗ[ℂ] (C → ℂ)
  /-- The rational metric in these coordinates. -/
  metric : Matrix C C ℚ
  /-- The coordinate metric is positive definite. -/
  metric_posDef : (metric.map (algebraMap ℚ ℂ)).PosDef
  /-- The coordinate metric represents the given inner product. -/
  inner_eq : ∀ x y : S 1,
    ⟪x, y⟫_ℂ = star (coord x) ⬝ᵥ (metric.map (algebraMap ℚ ℂ)) *ᵥ coord y

namespace TwistedLattice

variable {V T : Type*} [AddCommMonoid V] [Module ℂ V] [One T]
  {S : T → Type*} [∀ ξ, NormedAddCommGroup (S ξ)] [∀ ξ, InnerProductSpace ℂ (S ξ)]
  {C : Type*} [Fintype C] (L : TwistedLattice V T S C)

/-- Two twisted lattices agree when their maps, allowed twists, local submodules and
rational coordinate data agree. The proof arguments indexing the local submodules do not
contribute data. -/
@[ext]
theorem ext {L M : TwistedLattice V T S C}
    (hlift : L.lift = M.lift) (hallowed : L.allowed = M.allowed)
    (hintegral : ∀ ξ ι h h', L.integral ξ ι h = M.integral ξ ι h')
    (hcoord : L.coord = M.coord) (hmetric : L.metric = M.metric) : L = M := by
  cases L
  cases M
  cases hlift
  cases hallowed
  cases hcoord
  cases hmetric
  congr
  funext ξ ι h
  exact hintegral ξ ι h h

/-- The vectors integral at `ι` for every twist allowed at its prime. -/
def integralVectors (ι : PrimePadicIso) :
    Submodule (Valued.v.comap ι.iso.toRingHom).integer V :=
  ⨅ (ξ : T) (h : L.allowed ξ ι.prime),
    (L.integral ξ ι h).comap ((L.lift ξ).restrictScalars _)

/-- Integrality is simultaneous membership in the local submodules of all allowed twists. -/
@[simp]
theorem mem_integralVectors {ι : PrimePadicIso} {v : V} :
    v ∈ L.integralVectors ι ↔
      ∀ (ξ : T) (h : L.allowed ξ ι.prime), L.lift ξ v ∈ L.integral ξ ι h := by
  simp only [integralVectors, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

/-- The image of an integral vector under an allowed twist is locally integral. -/
theorem lift_mem_integral {ι : PrimePadicIso} {v : V} (hv : v ∈ L.integralVectors ι)
    {ξ : T} (h : L.allowed ξ ι.prime) : L.lift ξ v ∈ L.integral ξ ι h :=
  (L.mem_integralVectors.mp hv) ξ h

/-- Pair the images of two simultaneously integral vectors at conjugate embeddings. -/
theorem norm_inner_lift_le_one (ξ : T) (ι : PrimePadicIso) (h : L.allowed ξ ι.prime)
    {v w : V}
    (hv : v ∈ L.integralVectors { ι with iso := (starRingAut : ℂ ≃+* ℂ).trans ι.iso })
    (hw : w ∈ L.integralVectors ι) :
    ‖ι.iso ⟪L.lift ξ v, L.lift ξ w⟫_ℂ‖ ≤ 1 :=
  L.integral_inner ξ ι h _ _ (L.lift_mem_integral hv h) (L.lift_mem_integral hw h)

/-- The squared size after applying a complex automorphism to the distinguished coordinates. -/
def normSqAt (σ : ℂ ≃+* ℂ) (v : V) : ℝ :=
  (star (fun c ↦ σ (L.coord (L.lift 1 v) c)) ⬝ᵥ
    (L.metric.map (algebraMap ℚ ℂ)) *ᵥ (fun c ↦ σ (L.coord (L.lift 1 v) c))).re

/-- The coordinate expression for the squared size. -/
theorem normSqAt_def (σ : ℂ ≃+* ℂ) (v : V) :
    L.normSqAt σ v =
      (star (fun c ↦ σ (L.coord (L.lift 1 v) c)) ⬝ᵥ
        (L.metric.map (algebraMap ℚ ℂ)) *ᵥ (fun c ↦ σ (L.coord (L.lift 1 v) c))).re :=
  (rfl)

/-- Squared sizes are nonnegative. -/
theorem normSqAt_nonneg (σ : ℂ ≃+* ℂ) (v : V) : 0 ≤ L.normSqAt σ v := by
  exact (Complex.nonneg_iff.mp (L.metric_posDef.posSemidef.dotProduct_mulVec_nonneg _)).1

/-- At the identity automorphism the squared size is the usual squared norm of the lift. -/
@[simp]
theorem normSqAt_refl (v : V) :
    L.normSqAt (RingEquiv.refl ℂ) v = ‖L.lift 1 v‖ ^ 2 := by
  rw [normSqAt]
  simpa only [RingEquiv.refl_apply] using
    (L.inner_eq (L.lift 1 v) (L.lift 1 v) ▸ inner_self_eq_norm_sq (𝕜 := ℂ) (L.lift 1 v))

/-- Zero has squared size zero at every automorphism. -/
@[simp]
theorem normSqAt_zero (σ : ℂ ≃+* ℂ) : L.normSqAt σ 0 = 0 := by
  simp [normSqAt, dotProduct, mulVec]

/-- Multiplying a vector multiplies its squared size by the squared norm of the
image of the scalar under the same automorphism. -/
theorem normSqAt_smul (σ : ℂ ≃+* ℂ) (a : ℂ) (v : V) :
    L.normSqAt σ (a • v) = ‖σ a‖ ^ 2 * L.normSqAt σ v := by
  let x : C → ℂ := fun c ↦ σ (L.coord (L.lift 1 v) c)
  have hcoords : (fun c ↦ σ (L.coord (L.lift 1 (a • v)) c)) = σ a • x := by
    ext c
    simp [x]
  rw [normSqAt_def, hcoords, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_smul, smul_eq_mul]
  rw [show star (σ a) * σ a = ((‖σ a‖ ^ 2 : ℝ) : ℂ) by
    simpa [Complex.normSq_eq_norm_sq] using (Complex.normSq_eq_conj_mul_self (z := σ a)).symm]
  simp [normSqAt_def, x, pow_two]

/-- The coordinate map of the distinguished target is injective. -/
theorem coord_injective : Function.Injective L.coord := by
  refine (LinearMap.ker_eq_bot).mp ?_
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : L.coord x = 0 := hx
  have hinner : ⟪x, x⟫_ℂ = 0 := by rw [L.inner_eq, hx']; simp
  simpa using hinner

section ComplexLine

variable (T : Type*) [One T]

/-- The complex line with identity lifts at every twist and the usual prime-adic integral
submodules. Every twist is allowed at every prime. -/
def complexLine : TwistedLattice ℂ T (fun _ ↦ ℂ) (Fin 1) where
  lift _ := LinearMap.id
  allowed _ _ _ := True
  integral _ ι _ := (Algebra.linearMap (Valued.v.comap ι.iso.toRingHom).integer ℂ).range
  integral_inner _ ι _ x y hx hy := by
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have ha : ‖ι.iso (star (a : ℂ))‖₊ ≤ 1 := a.property
    have hb : ‖ι.iso (b : ℂ)‖₊ ≤ 1 := b.property
    have hab : ‖ι.iso (star (a : ℂ))‖₊ * ‖ι.iso (b : ℂ)‖₊ ≤ 1 :=
      (mul_le_mul ha hb (by positivity) (by positivity)).trans_eq (one_mul 1)
    exact_mod_cast (by simpa [RCLike.inner_apply, mul_comm, map_mul, nnNorm_mul] using hab :
      ‖ι.iso ⟪(a : ℂ), (b : ℂ)⟫_ℂ‖₊ ≤ 1)
  coord := LinearMap.pi fun _ ↦ LinearMap.id
  metric := 1
  metric_posDef := by simpa using (Matrix.PosDef.one (R := ℂ) (n := Fin 1))
  inner_eq x y := by simp [dotProduct, mulVec, RCLike.inner_apply, mul_comm]

/-- The identity lifts of the complex-line example. -/
@[simp]
theorem complexLine_lift (ξ : T) (z : ℂ) : (complexLine T).lift ξ z = z := (rfl)

/-- All twists of the complex line are allowed. -/
@[simp]
theorem complexLine_allowed (ξ : T) (p : ℕ) [Fact p.Prime] : (complexLine T).allowed ξ p := trivial

/-- The local integral submodule of the complex line is the prime-adic unit ball. -/
@[simp]
theorem mem_complexLine_integral (ξ : T) (ι : PrimePadicIso)
    (h : (complexLine T).allowed ξ ι.prime) (z : ℂ) :
    z ∈ (complexLine T).integral ξ ι h ↔ ‖ι.iso z‖ ≤ 1 := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : ‖ι.iso (a : ℂ)‖₊ ≤ 1 := a.property
    have ha'' : (a : ℂ) = z := ha
    rw [← ha'']
    exact_mod_cast ha'
  · intro hz
    exact ⟨⟨z, (NNReal.coe_le_one).mp hz⟩, rfl⟩

/-- A complex number is simultaneously integral in the complex-line example exactly when
its prime-adic image has norm at most one. -/
@[simp]
theorem mem_integralVectors_complexLine (ι : PrimePadicIso) (z : ℂ) :
    z ∈ (complexLine T).integralVectors ι ↔ ‖ι.iso z‖ ≤ 1 := by
  rw [mem_integralVectors]
  constructor
  · intro hz
    exact (mem_complexLine_integral T 1 ι trivial z).mp (hz 1 trivial)
  · intro hz ξ h
    exact (mem_complexLine_integral T ξ ι h z).mpr hz

/-- The complex-line example contains the nonzero integral vector `1` at every embedding. -/
theorem one_mem_integralVectors_complexLine (ι : PrimePadicIso) :
    (1 : ℂ) ∈ (complexLine T).integralVectors ι := by
  rw [mem_integralVectors_complexLine]
  simp

/-- The squared size on the complex line is the squared norm of the conjugated scalar. -/
@[simp]
theorem normSqAt_complexLine (σ : ℂ ≃+* ℂ) (z : ℂ) :
    (complexLine T).normSqAt σ z = ‖σ z‖ ^ 2 := by
  simp [normSqAt, complexLine, dotProduct, mulVec, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, pow_two]

end ComplexLine

end TwistedLattice

end TauCeti
