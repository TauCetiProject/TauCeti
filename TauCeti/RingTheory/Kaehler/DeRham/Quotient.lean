/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.DeRham.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Descent of the exterior derivative along quotients of Kähler differentials

For a surjective linear map on Kähler differentials, the exterior derivative descends if the
differential of each one-form in the kernel maps to zero. This construction applies to divided
power differentials and to universally finite differentials.
-/

public section

noncomputable section

open CliffordAlgebra KaehlerDifferential

namespace TauCeti.KaehlerDeRham

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]
  [Module R M] [IsScalarTower R S M] (q : Ω[S⁄R] →ₗ[S] M)

/-- The ordinary exterior derivative on one-forms followed by the exterior algebra map of `q`. -/
def preExtDerivOne : Ω[S⁄R] →ₗ[R] ExteriorAlgebra S M :=
  (ExteriorAlgebra.map q).toLinearMap.restrictScalars R ∘ₗ
    extDeriv R S ∘ₗ (ExteriorAlgebra.ι S).restrictScalars R

/-- The pushed-forward derivative is computed by applying the ordinary derivative first. -/
theorem preExtDerivOne_apply (ω : Ω[S⁄R]) :
    preExtDerivOne q ω = ExteriorAlgebra.map q (extDeriv R S (ExteriorAlgebra.ι S ω)) :=
  (rfl)

/-- The pushed-forward derivative of a one-form has exterior degree two. -/
theorem preExtDerivOne_mem (ω : Ω[S⁄R]) : preExtDerivOne q ω ∈ ⋀[S]^2 M :=
  q.exteriorAlgebra_map_mem_exteriorPower
    (extDeriv_mem_exteriorPower (ExteriorAlgebra.ι_mem_exteriorPower_one ω))

/-- Scalar Leibniz rule for the pushed-forward exterior derivative on one-forms. -/
theorem preExtDerivOne_smul (s : S) (ω : Ω[S⁄R]) :
    preExtDerivOne q (s • ω) =
      ExteriorAlgebra.ι S (q (D R S s)) * ExteriorAlgebra.ι S (q ω) + s • preExtDerivOne q ω := by
  simp only [preExtDerivOne_apply, LinearMap.map_smul, extDeriv_smul, map_add, map_mul,
    AlgHom.map_smul_of_tower,
    ExteriorAlgebra.map_apply_ι]

/-- The pushed-forward derivative is linear over the algebra on the kernel of `q`. -/
def preExtDerivOneKer : LinearMap.ker q →ₗ[S] ExteriorAlgebra S M where
  toFun ω := preExtDerivOne q ω
  map_add' ω η := map_add (preExtDerivOne q) (ω : Ω[S⁄R]) (η : Ω[S⁄R])
  map_smul' s ω := by
    rw [Submodule.coe_smul, preExtDerivOne_smul, LinearMap.mem_ker.mp ω.property, map_zero,
      mul_zero, zero_add, RingHom.id_apply]

/-- On the kernel, the restricted linear map computes the pushed-forward derivative. -/
theorem preExtDerivOneKer_apply (ω : LinearMap.ker q) :
    preExtDerivOneKer q ω = preExtDerivOne q ω :=
  (rfl)

variable (hq : Function.Surjective q)
  (hker : ∀ ⦃ω : Ω[S⁄R]⦄, q ω = 0 → preExtDerivOne q ω = 0)

private def extDerivOneDescend : M →ₗ[R] ExteriorAlgebra S M :=
  (q.restrictScalars R).liftOfSurjective hq ⟨preExtDerivOne q, fun _ hω ↦ hker hω⟩

private theorem extDerivOneDescend_apply (ω : Ω[S⁄R]) :
    extDerivOneDescend q hq hker (q ω) = preExtDerivOne q ω :=
  LinearMap.equivOfSurjective_apply (f := q.restrictScalars R) _ _

private theorem extDerivOneDescend_smul (s : S) (m : M) :
    extDerivOneDescend q hq hker (s • m) =
      ExteriorAlgebra.ι S (q (D R S s)) * ExteriorAlgebra.ι S m +
        s • extDerivOneDescend q hq hker m := by
  obtain ⟨ω, rfl⟩ := hq m
  rw [← LinearMap.map_smul q s ω, extDerivOneDescend_apply, extDerivOneDescend_apply,
    preExtDerivOne_smul]

private theorem extDerivOneDescend_mem (m : M) :
    extDerivOneDescend q hq hker m ∈ ⋀[S]^2 M := by
  obtain ⟨ω, rfl⟩ := hq m
  rw [extDerivOneDescend_apply]
  exact preExtDerivOne_mem q ω

/-- The exterior derivative on the exterior algebra of a quotient of the Kähler differentials,
when the pushed-forward derivative kills the kernel in degree one. -/
def extDerivDescend : ExteriorAlgebra S M →ₗ[R] ExteriorAlgebra S M :=
  ExteriorAlgebra.liftTwistedDerivation (involute (Q := (0 : QuadraticForm S M)))
    ((ExteriorAlgebra.ι S).compDer (q.compDer (D R S)))
    (fun s m ↦ by
      simpa only [Derivation.coe_comp, Derivation.coe_to_linearMap_comp,
        LinearMap.comp_apply, LinearMap.restrictScalars_apply, Derivation.coeFn_coe] using
        ExteriorAlgebra.ι_mul_eq_involute_mul (q (D R S s)) (ExteriorAlgebra.ι S m))
    (extDerivOneDescend q hq hker)
    (fun s m ↦ by
      simpa only [Derivation.coe_comp, Derivation.coe_to_linearMap_comp,
        LinearMap.comp_apply, LinearMap.restrictScalars_apply, Derivation.coeFn_coe] using
        extDerivOneDescend_smul q hq hker s m)
    (fun m ↦ ExteriorAlgebra.mul_ι_add_involute_ι_mul_of_mem_exteriorPower even_two
      (extDerivOneDescend_mem q hq hker m) m)

/-- On scalars the descended derivative is the quotient of the universal derivation. -/
theorem extDerivDescend_algebraMap (s : S) :
    extDerivDescend q hq hker (algebraMap S (ExteriorAlgebra S M) s) =
      ExteriorAlgebra.ι S (q (D R S s)) := by
  rw [extDerivDescend, ExteriorAlgebra.liftTwistedDerivation_algebraMap]
  rfl

/-- Exact one-forms are closed under the descended derivative. -/
theorem extDerivDescend_ι_map_D (s : S) :
    extDerivDescend q hq hker (ExteriorAlgebra.ι S (q (D R S s))) = 0 := by
  rw [extDerivDescend, ExteriorAlgebra.liftTwistedDerivation_ι, extDerivOneDescend_apply,
    preExtDerivOne_apply, extDeriv_ι_D, map_zero]

/-- The descended derivative satisfies the graded Leibniz rule. -/
theorem extDerivDescend_mul (x y : ExteriorAlgebra S M) :
    extDerivDescend q hq hker (x * y) = extDerivDescend q hq hker x * y +
      involute (Q := (0 : QuadraticForm S M)) x * extDerivDescend q hq hker y :=
  ExteriorAlgebra.liftTwistedDerivation_mul _ _ _ _ _ _ x y

/-- The quotient map on exterior algebras commutes with exterior differentiation. -/
theorem extDerivDescend_map (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDerivDescend q hq hker (ExteriorAlgebra.map q x) =
      ExteriorAlgebra.map q (extDeriv R S x) := by
  induction x using inductionOn with
  | algebraMap s =>
    rw [AlgHom.commutes, extDerivDescend_algebraMap, extDeriv_algebraMap,
      ExteriorAlgebra.map_apply_ι]
  | ι_D s =>
    rw [ExteriorAlgebra.map_apply_ι, extDerivDescend_ι_map_D, extDeriv_ι_D, map_zero]
  | mul x y hx hy =>
    simp only [map_mul, map_add, extDerivDescend_mul, extDeriv_mul, ExteriorAlgebra.map_involute,
      hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The descended derivative squares to zero. -/
theorem extDerivDescend_sq (x : ExteriorAlgebra S M) :
    extDerivDescend q hq hker (extDerivDescend q hq hker x) = 0 := by
  obtain ⟨x, rfl⟩ := ExteriorAlgebra.map_surjective_iff.mpr hq x
  rw [extDerivDescend_map, extDerivDescend_map, extDeriv_extDeriv, map_zero]

/-- The descended derivative raises the integer exterior degree by one. -/
theorem extDerivDescend_mem_integerGrading {n : ℤ} {x : ExteriorAlgebra S M}
    (hx : x ∈ TauCeti.ExteriorAlgebra.integerGrading S M n) :
    extDerivDescend q hq hker x ∈ TauCeti.ExteriorAlgebra.integerGrading S M (n + 1) :=
  ExteriorAlgebra.liftTwistedDerivation_mem_integerGrading _ _ _ _ _ _ (r := 1)
    (fun m ↦ by
      rw [involute_ι]
      exact neg_mem (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one m))
    (fun s ↦ TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one (q (D R S s)))
    (fun m ↦ by
      rw [one_add_one_eq_two, ← Nat.cast_ofNat (n := 2),
        TauCeti.ExteriorAlgebra.integerGrading_natCast]
      exact extDerivOneDescend_mem q hq hker m)
    hx

end TauCeti.KaehlerDeRham
