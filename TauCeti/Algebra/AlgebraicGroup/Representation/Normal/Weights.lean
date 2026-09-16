/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Normal.Finite
public import TauCeti.RingTheory.FiniteType.FiniteRange
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation

/-!
# Connected affine groups preserve normal-subgroup weight spaces

Let a reduced connected affine group of finite type over an algebraically closed field act on a
finite-dimensional comodule. Its rational points preserve every nonzero joint weight space for
any normal subgroup of the rational point group. The normal subgroup need not be closed.

Normality permutes the finitely many nonzero joint weights. For a weight vector `v`, choose a
functional taking value one on `v`. Evaluating that functional on `g⁻¹ n g v` realizes the
conjugated character at `n` as a regular function of `g`. Its finite image and connectedness make
it constant. This supplies the weight-space invariance used in the Lie--Kolchin induction.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. E. Humphreys, *Linear Algebraic Groups*, §17.6.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

noncomputable section

variable {k H V : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [AddCommGroup V] [Module k V] [Comodule k H V] [FiniteDimensional k V]

/-- A connected affine group acts trivially on the nonzero joint weights of any normal subgroup
of its rational point group, in every finite-dimensional rational representation. -/
theorem nonzeroJointWeightAction_basePointsRepresentation_eq_one
    (N : Subgroup (WithConv (H →ₐ[k] k))) [N.Normal] :
    nonzeroJointWeightAction N (basePointsRepresentation (R := k) (H := H) V) = 1 := by
  classical
  let ρ := basePointsRepresentation (R := k) (H := H) V
  apply MonoidHom.ext
  intro g
  apply Equiv.ext
  intro χ
  apply Subtype.ext
  apply MonoidHom.ext
  intro n
  apply Units.ext
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp χ.2
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv0
  -- The generic point makes conjugation a regular, coordinate-algebra-valued point.
  let u : WithConv (H →ₐ[k] H) := toConv (AlgHom.id k H)
  let q := u⁻¹ * AlgHom.mapValue (H := H) (Algebra.ofId k H) (n : WithConv (H →ₐ[k] k)) * u
  let a := q.ofConv (matrixCoefficient (R := k) (C := H) φ v)
  have hq (x : WithConv (H →ₐ[k] k)) :
      AlgHom.mapValue (H := H) x.ofConv q = x⁻¹ * n * x := by
    simp only [q, map_mul, map_inv]
    rw [AlgHom.mapValue_algebraOfId]
    simp [u, AlgHom.mapValue_apply]
  have heval (x : WithConv (H →ₐ[k] k)) :
      x.ofConv a = ((nonzeroJointWeightAction N ρ x χ).1 n : k) := by
    have h := congrArg
      (fun y : WithConv (H →ₐ[k] k) ↦ y.ofConv (matrixCoefficient (R := k) (C := H) φ v)) (hq x)
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at h
    rw [h, apply_matrixCoefficient]
    have hvn := Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf _).mp hv (MulAut.conjNormal x⁻¹ n))
    have hconj : (MulAut.conjNormal x⁻¹ n : WithConv (H →ₐ[k] k)) = x⁻¹ * n * x := by
      simp
    rw [← hconj, hvn, map_smul, hφ, smul_eq_mul, mul_one]
    simp [nonzeroJointWeightAction_apply_coe, MulEquiv.monoidHomCongrLeftEquiv_apply,
      map_inv, MulAut.inv_def]
  -- Evaluation factors through the finite set of weights, so connectedness forces constancy.
  have hfinite : (Set.range fun f : H →ₐ[k] k ↦ f a).Finite := by
    apply (Set.finite_range fun ψ : NonzeroJointWeight N ρ ↦ (ψ.1 n : k)).subset
    rintro _ ⟨f, rfl⟩
    exact ⟨nonzeroJointWeightAction N ρ (toConv f) χ, (heval (toConv f)).symm⟩
  have ha := eq_algebraMap_of_finite_range_eval a hfinite (1 : WithConv (H →ₐ[k] k)).ofConv
  have hconstant : g.ofConv a = (1 : WithConv (H →ₐ[k] k)).ofConv a := by
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      congrArg g.ofConv ha
  rw [heval, heval] at hconstant
  simpa using hconstant

/-- Every rational point preserves each nonzero normal-subgroup joint weight space in a
finite-dimensional comodule of a reduced connected affine group. -/
theorem map_iInf_eigenspace_basePointsRepresentation_eq_self
    (N : Subgroup (WithConv (H →ₐ[k] k))) [N.Normal]
    (g : WithConv (H →ₐ[k] k))
    (χ : NonzeroJointWeight N (basePointsRepresentation (R := k) (H := H) V)) :
    (⨅ n : N, (basePointsRepresentation (R := k) (H := H) V n).eigenspace (χ.1 n : k)).map
        (basePointsRepresentation (R := k) (H := H) V g) =
      ⨅ n : N, (basePointsRepresentation (R := k) (H := H) V n).eigenspace (χ.1 n : k) := by
  apply map_iInf_eigenspace_unitHom_eq_self_of_nonzeroJointWeightAction_eq
  rw [nonzeroJointWeightAction_basePointsRepresentation_eq_one]
  rfl

/-- A nonzero normal-subgroup joint weight space as an ambient-group subcomodule. -/
def normalWeightSubcomodule
    (N : Subgroup (WithConv (H →ₐ[k] k))) [N.Normal]
    (χ : NonzeroJointWeight N (basePointsRepresentation (R := k) (H := H) V)) :
    Subcomodule k H V :=
  Subcomodule.ofEndOfPointStable (K := k)
    (⨅ n : N, (basePointsRepresentation (R := k) (H := H) V n).eigenspace (χ.1 n : k))
    fun g v hv ↦ by
      rw [endOfPoint_tmul, one_smul,
        endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
      apply Submodule.tmul_mem_baseChange_of_mem
      rw [← map_iInf_eigenspace_basePointsRepresentation_eq_self N (toConv g) χ]
      exact Submodule.mem_map_of_mem hv

/-- The underlying submodule is the joint eigenspace for the specified character. -/
@[simp]
theorem normalWeightSubcomodule_toSubmodule
    (N : Subgroup (WithConv (H →ₐ[k] k))) [N.Normal]
    (χ : NonzeroJointWeight N (basePointsRepresentation (R := k) (H := H) V)) :
    (normalWeightSubcomodule N χ).toSubmodule =
      ⨅ n : N, (basePointsRepresentation (R := k) (H := H) V n).eigenspace (χ.1 n : k) :=
  Subcomodule.ofEndOfPointStable_toSubmodule _ _

/-- Membership in the normal weight subcomodule is the joint eigenvector equation. -/
@[simp]
theorem mem_normalWeightSubcomodule
    (N : Subgroup (WithConv (H →ₐ[k] k))) [N.Normal]
    (χ : NonzeroJointWeight N (basePointsRepresentation (R := k) (H := H) V)) (v : V) :
    v ∈ normalWeightSubcomodule N χ ↔
      ∀ n : N, basePointsRepresentation (R := k) (H := H) V n v = (χ.1 n : k) • v := by
  rw [← Subcomodule.mem_toSubmodule, normalWeightSubcomodule_toSubmodule]
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

end

end TauCeti.Comodule
