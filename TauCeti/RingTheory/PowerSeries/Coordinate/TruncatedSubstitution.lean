/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Jet
public import TauCeti.RingTheory.PowerSeries.Jet
public import Mathlib.RingTheory.Nilpotent.Defs
import TauCeti.RingTheory.Polynomial.Truncated.Basic
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Substitution automorphisms of truncated polynomial algebras

Formal coordinates act by substitution on `R[X]/(X^(N+1))`. The action reverses composition,
and identifies the group of coordinate `N`-jets with the opposite automorphism group when the
coefficient ring is reduced. The reducedness assumption excludes translations by nilpotents.
-/

public section

open scoped Polynomial PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Substitution by a series of zero constant coefficient descends to each finite jet algebra. -/
noncomputable def jetSubstAlgHom (N : ℕ) (a : R⟦X⟧) (ha : constantCoeff a = 0) :
    AdjoinRoot (Polynomial.X ^ N : R[X]) →ₐ[R] AdjoinRoot (Polynomial.X ^ N : R[X]) :=
  AlgHom.liftOfSurjective (jet R N) jet_surjective
    ((jet R N).comp (substAlgHom (.of_constantCoeff_zero' ha))) fun f hf ↦ by
      -- Expose the underlying maps at the kernel boundary before using the jet criterion.
      rw [RingHom.mem_ker]
      change (jet R N) ((substAlgHom (.of_constantCoeff_zero' ha)) f) = 0
      rw [coe_substAlgHom, jet_eq_zero_iff]
      exact X_pow_dvd_subst ha (jet_eq_zero_iff.mp hf)

@[simp]
theorem jetSubstAlgHom_jet (N : ℕ) (a : R⟦X⟧) (ha : constantCoeff a = 0) (f : R⟦X⟧) :
    jetSubstAlgHom N a ha (jet R N f) = jet R N (f.subst a) := by
  simp [jetSubstAlgHom, coe_substAlgHom]

/-- The root is sent to the jet of the substituted series. -/
@[simp]
theorem jetSubstAlgHom_root (N : ℕ) (a : R⟦X⟧) (ha : constantCoeff a = 0) :
    jetSubstAlgHom N a ha (AdjoinRoot.root (Polynomial.X ^ N : R[X])) = jet R N a := by
  rw [← jet_X, jetSubstAlgHom_jet, subst_X (.of_constantCoeff_zero' ha)]

end PowerSeries

namespace TauCeti.FormalCoordinate

open PowerSeries

variable {R : Type*} [CommRing R]

/-- Substitution by a formal coordinate on the truncated polynomial algebra. -/
noncomputable def jetSubstAlgEquiv (N : ℕ) (φ : FormalCoordinate R) :
    AdjoinRoot (Polynomial.X ^ (N + 1) : R[X]) ≃ₐ[R]
      AdjoinRoot (Polynomial.X ^ (N + 1) : R[X]) :=
  .ofAlgHom (jetSubstAlgHom (N + 1) φ.toPowerSeries φ.constantCoeff_toPowerSeries)
    (jetSubstAlgHom (N + 1) φ⁻¹.toPowerSeries φ⁻¹.constantCoeff_toPowerSeries)
    (AlgHom.ext fun x ↦ by
      obtain ⟨f, rfl⟩ := PowerSeries.jet_surjective x
      simp only [AlgHom.comp_apply, jetSubstAlgHom_jet, AlgHom.id_apply]
      rw [subst_subst]
      simp)
    (AlgHom.ext fun x ↦ by
      obtain ⟨f, rfl⟩ := PowerSeries.jet_surjective x
      simp only [AlgHom.comp_apply, jetSubstAlgHom_jet, AlgHom.id_apply]
      rw [subst_subst]
      simp)

@[simp]
theorem jetSubstAlgEquiv_jet (N : ℕ) (φ : FormalCoordinate R) (f : R⟦X⟧) :
    jetSubstAlgEquiv N φ (PowerSeries.jet R (N + 1) f) =
      PowerSeries.jet R (N + 1) (f.subst φ.toPowerSeries) := by
  simp [jetSubstAlgEquiv]

@[simp]
theorem jetSubstAlgEquiv_root (N : ℕ) (φ : FormalCoordinate R) :
    jetSubstAlgEquiv N φ (AdjoinRoot.root (Polynomial.X ^ (N + 1) : R[X])) =
      PowerSeries.jet R (N + 1) φ.toPowerSeries := by
  rw [← PowerSeries.jet_X, jetSubstAlgEquiv_jet, subst_X φ.hasSubst]

@[simp]
theorem jetSubstAlgEquiv_one (N : ℕ) : jetSubstAlgEquiv N (1 : FormalCoordinate R) = 1 := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨f, rfl⟩ := PowerSeries.jet_surjective x
  simp

/-- Substitution reverses multiplication of coordinates. -/
@[simp]
theorem jetSubstAlgEquiv_mul (N : ℕ) (φ ψ : FormalCoordinate R) :
    jetSubstAlgEquiv N (φ * ψ) = jetSubstAlgEquiv N ψ * jetSubstAlgEquiv N φ := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨f, rfl⟩ := PowerSeries.jet_surjective x
  simp [AlgEquiv.mul_apply, subst_subst]

/-- Coordinates induce the same truncated substitution exactly when their jets agree. -/
theorem jetSubstAlgEquiv_eq_iff (N : ℕ) {φ ψ : FormalCoordinate R} :
    jetSubstAlgEquiv N φ = jetSubstAlgEquiv N ψ ↔ jet N φ = jet N ψ := by
  constructor
  · intro h
    rw [jet_eq_jet_iff_coeff]
    have hroot := congrArg (fun e ↦ e (AdjoinRoot.root (Polynomial.X ^ (N + 1) : R[X]))) h
    simp only [jetSubstAlgEquiv_root, PowerSeries.jet_eq_jet_iff] at hroot
    exact fun m hm ↦ hroot m (Nat.lt_succ_of_le hm)
  · intro h
    apply AlgEquiv.coe_toAlgHom_injective
    apply AdjoinRoot.algHom_ext
    simpa [jetSubstAlgEquiv_root, PowerSeries.jet_eq_jet_iff] using
      fun m (hm : m < N + 1) ↦ jet_eq_jet_iff_coeff.mp h m (Nat.le_of_lt_succ hm)

/-- The substitution action on the truncated algebra, as a homomorphism into the opposite
of its automorphism group. -/
private noncomputable def jetSubstAlgEquivHom (N : ℕ) : FormalCoordinate R →*
    (AdjoinRoot (Polynomial.X ^ (N + 1) : R[X]) ≃ₐ[R]
      AdjoinRoot (Polynomial.X ^ (N + 1) : R[X]))ᵐᵒᵖ where
  toFun φ := .op (jetSubstAlgEquiv N φ)
  map_one' := by simp
  map_mul' φ ψ := by simp

namespace Jet

/-- Coordinate jets act faithfully by substitution on the truncated polynomial algebra. -/
noncomputable def substAlgEquivHom (N : ℕ) : Jet R N →*
    (AdjoinRoot (Polynomial.X ^ (N + 1) : R[X]) ≃ₐ[R]
      AdjoinRoot (Polynomial.X ^ (N + 1) : R[X]))ᵐᵒᵖ :=
  (jet (R := R) N).liftOfSurjective (jet_surjective N)
    ⟨jetSubstAlgEquivHom N, fun φ hφ ↦ by
      have hsub : jetSubstAlgEquiv N φ = jetSubstAlgEquiv N 1 :=
        (jetSubstAlgEquiv_eq_iff N).2 (by simpa only [MonoidHom.mem_ker, map_one] using hφ)
      simp [MonoidHom.mem_ker, jetSubstAlgEquivHom, hsub]⟩

@[simp]
theorem substAlgEquivHom_jet (N : ℕ) (φ : FormalCoordinate R) :
    substAlgEquivHom N (jet N φ) = .op (jetSubstAlgEquiv N φ) := by
  simp [substAlgEquivHom, jetSubstAlgEquivHom]

theorem substAlgEquivHom_injective (N : ℕ) :
    Function.Injective (substAlgEquivHom (R := R) N) := by
  intro x y h
  obtain ⟨φ, rfl⟩ := jet_surjective N x
  obtain ⟨ψ, rfl⟩ := jet_surjective N y
  apply (jetSubstAlgEquiv_eq_iff N).mp
  exact MulOpposite.op_injective (by simpa only [substAlgEquivHom_jet] using h)

/-- Truncating jets commutes with their action on truncated polynomial algebras. -/
theorem substAlgEquivHom_truncate {N M : ℕ} (h : N ≤ M) (x : Jet R M)
    (p : AdjoinRoot (Polynomial.X ^ (M + 1) : R[X])) :
    (substAlgEquivHom N (truncate h x)).unop
        (AdjoinRoot.algHomOfDvd R (Polynomial.X ^ (M + 1) : R[X])
          (Polynomial.X ^ (N + 1)) (pow_dvd_pow _ (Nat.succ_le_succ h)) p) =
      AdjoinRoot.algHomOfDvd R (Polynomial.X ^ (M + 1) : R[X])
        (Polynomial.X ^ (N + 1)) (pow_dvd_pow _ (Nat.succ_le_succ h))
        ((substAlgEquivHom M x).unop p) := by
  obtain ⟨φ, rfl⟩ := jet_surjective M x
  obtain ⟨f, rfl⟩ := PowerSeries.jet_surjective p
  simp only [truncate_jet, substAlgEquivHom_jet, MulOpposite.unop_op,
    jetSubstAlgEquiv_jet]
  rw [PowerSeries.algHomOfDvd_jet (Nat.succ_le_succ h), jetSubstAlgEquiv_jet,
    PowerSeries.algHomOfDvd_jet (Nat.succ_le_succ h)]

/-- Over a reduced coefficient ring, every automorphism of the truncated polynomial algebra
is induced by a coordinate jet. -/
theorem substAlgEquivHom_surjective [IsReduced R] (N : ℕ) :
    Function.Surjective (substAlgEquivHom (R := R) N) := by
  intro σ
  let a := σ.unop
  let x := AdjoinRoot.root (Polynomial.X ^ (N + 1) : R[X])
  by_cases hN : N = 0
  · subst N
    have hx0 : AdjoinRoot.root (Polynomial.X ^ (0 + 1) : R[X]) = 0 := by
      rw [pow_one, ← AdjoinRoot.mk_X]
      exact AdjoinRoot.mk_self
    refine ⟨1, ?_⟩
    apply MulOpposite.unop_injective
    rw [map_one, MulOpposite.unop_one]
    apply AlgEquiv.coe_toAlgHom_injective
    exact AdjoinRoot.algHom_ext (by simp [hx0])
  have hx : IsNilpotent x := isNilpotent_root_X_pow _
  obtain ⟨g, hg⟩ := PowerSeries.jet_surjective (a x)
  have hg0 : constantCoeff g = 0 := by
    obtain ⟨n, hn⟩ := (hg ▸ hx.map a : IsNilpotent (PowerSeries.jet R (N + 1) g))
    have hjet : PowerSeries.jet R (N + 1) (g ^ n) = PowerSeries.jet R (N + 1) 0 := by
      simpa using hn
    have hc := PowerSeries.jet_eq_jet_iff.mp hjet 0 (Nat.succ_pos N)
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      map_pow, map_zero] at hc
    exact IsReduced.eq_zero _ ⟨n, hc⟩
  have hga : jetSubstAlgHom (N + 1) g hg0 = a.toAlgHom :=
    AdjoinRoot.algHom_ext (by rw [jetSubstAlgHom_root]; exact hg)
  obtain ⟨f, hf⟩ := PowerSeries.jet_surjective (a.symm x)
  have hcomp : PowerSeries.jet R (N + 1) (f.subst g) = PowerSeries.jet R (N + 1) X := by
    rw [← jetSubstAlgHom_jet (N + 1) g hg0 f, hga, hf, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply, PowerSeries.jet_X]
  have hc := PowerSeries.jet_eq_jet_iff.mp hcomp 1 (Nat.succ_lt_succ (Nat.pos_of_ne_zero hN))
  rw [coeff_one_subst hg0, Algebra.algebraMap_self_apply, coeff_one_X] at hc
  let φ : FormalCoordinate R := ⟨g, hg0, isUnit_iff_exists_inv'.mpr ⟨coeff 1 f, hc⟩⟩
  refine ⟨jet N φ, ?_⟩
  rw [substAlgEquivHom_jet]
  apply MulOpposite.unop_injective
  apply AlgEquiv.coe_toAlgHom_injective
  apply AdjoinRoot.algHom_ext
  exact (jetSubstAlgEquiv_root N φ).trans hg

/-- Over a reduced ring, coordinate jets identify with the opposite automorphism group of
`R[X]/(X^(N+1))`. -/
noncomputable def substAlgEquivMulEquiv [IsReduced R] (N : ℕ) : Jet R N ≃*
    (AdjoinRoot (Polynomial.X ^ (N + 1) : R[X]) ≃ₐ[R]
      AdjoinRoot (Polynomial.X ^ (N + 1) : R[X]))ᵐᵒᵖ :=
  .ofBijective (substAlgEquivHom N)
    ⟨substAlgEquivHom_injective N, substAlgEquivHom_surjective N⟩

theorem substAlgEquivMulEquiv_apply [IsReduced R] (N : ℕ) (x : Jet R N) :
    substAlgEquivMulEquiv N x = substAlgEquivHom N x := (rfl)

@[simp]
theorem substAlgEquivMulEquiv_jet [IsReduced R] (N : ℕ) (φ : FormalCoordinate R) :
    substAlgEquivMulEquiv N (jet N φ) = .op (jetSubstAlgEquiv N φ) := by
  rw [substAlgEquivMulEquiv_apply, substAlgEquivHom_jet]

@[simp]
theorem substAlgEquivMulEquiv_symm_apply_jet [IsReduced R] (N : ℕ)
    (φ : FormalCoordinate R) :
    (substAlgEquivMulEquiv N).symm (.op (jetSubstAlgEquiv N φ)) = jet N φ := by
  rw [← substAlgEquivHom_jet, ← substAlgEquivMulEquiv_apply, MulEquiv.symm_apply_apply]

end Jet

end TauCeti.FormalCoordinate
