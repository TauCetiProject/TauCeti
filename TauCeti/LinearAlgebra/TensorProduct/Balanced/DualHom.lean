/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Evaluation from the balanced tensor product of an opposite dual

For a left module `P` over a possibly noncommutative `k`-algebra `A`, evaluation gives
`Hom_A(P,A) ⊗_A N → Hom_A(P,N)`, sending `φ ⊗ n` to `x ↦ φ(x) • n`.
This map is an isomorphism when `P` is finitely generated projective. It is natural
contravariantly in `P` and covariantly in `N`. If `P` is merely finitely generated,
every map from `P` factoring through a projective module belongs to its image,
even when that intermediate projective is not finitely generated.

The right action on `Hom_A(P,A)` is Mathlib's opposite-scalar action on the codomain.
The tensor product is the existing balanced quotient over `k`; neither `A` nor its
modules need to be finite-dimensional. These identifications allow a projective
presentation's Hom complex to be computed by tensoring its opposite-dual complex,
as in the tensor description of the transpose and Auslander–Reiten duality.

Mathlib's `dualTensorHom` treats commutative scalars. Here the balancing relations
replace commutativity.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace TauCeti

open MulOpposite

variable (k A P N : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommMonoid P] [Module A P]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- Evaluation on the opposite dual tensored over a possibly noncommutative algebra:
`φ ⊗ n` gives the linear map `x ↦ φ(x) • n`. -/
def balancedDualTensorHom :
    BalancedTensorProduct k A (Module.Dual A P) N →ₗ[k] (P →ₗ[A] N) :=
  BalancedTensorProduct.lift
    { toFun := fun φ ↦
        { toFun := fun n ↦
            { toFun := fun x ↦ φ x • n
              map_add' := fun x y ↦ by simp [add_smul]
              map_smul' := fun a x ↦ by simp [mul_smul] }
          map_add' := fun n n' ↦ by ext x; simp [smul_add]
          map_smul' := fun c n ↦ by ext x; exact smul_comm (φ x) c n }
      map_add' := fun φ ψ ↦ by ext n x; simp [add_smul]
      map_smul' := fun c φ ↦ by ext n x; simp [smul_assoc] }
    (fun a φ n ↦ by ext x; simp [MulOpposite.smul_eq_mul_unop, mul_smul])

@[simp]
theorem balancedDualTensorHom_tmul (φ : Module.Dual A P) (n : N) (x : P) :
    balancedDualTensorHom k A P N (BalancedTensorProduct.tmul k A φ n) x = φ x • n := by
  simp [balancedDualTensorHom]

variable {P N}

/-- Evaluation is an isomorphism for finitely generated projective source modules,
over a possibly noncommutative algebra. -/
theorem balancedDualTensorHom_bijective [Module.Finite A P] [Module.Projective A P] :
    Function.Bijective (balancedDualTensorHom k A P N) := by
  classical
  /- The finite-projective argument uses `Module.Finite.exists_comp_eq_id_of_projective`,
  as does the opposite double-dual construction in `TauCeti.LinearAlgebra.Dual.Opposite`. -/
  obtain ⟨d, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let b : Fin d → P := fun i ↦ f (Pi.single i 1)
  let φ : Fin d → Module.Dual A P := fun i ↦ (LinearMap.proj i).comp g
  have hsum (x : P) : ∑ i, φ i x • b i = x := by
    have h := congrArg f ((Pi.basisFun A (Fin d)).sum_repr (g x))
    simpa [b, φ, map_sum, map_smul] using h.trans (LinearMap.congr_fun hfg x)
  have hdual (ψ : Module.Dual A P) : ∑ i, op (ψ (b i)) • φ i = ψ := by
    ext x
    simpa [map_sum, map_smul, MulOpposite.smul_eq_mul_unop] using congrArg ψ (hsum x)
  let inv : (P →ₗ[A] N) →ₗ[k] BalancedTensorProduct k A (Module.Dual A P) N :=
    ∑ i, (BalancedTensorProduct.mk k A (φ i)).comp
      (LinearMap.applyₗ' k (b i))
  have hinv (F : P →ₗ[A] N) :
      inv F = ∑ i, BalancedTensorProduct.tmul k A (φ i) (F (b i)) := by
    simp [inv]
  have hleft : inv.comp (balancedDualTensorHom k A P N) = LinearMap.id := by
    apply BalancedTensorProduct.hom_ext
    intro ψ n
    simp only [LinearMap.comp_apply, hinv, balancedDualTensorHom_tmul, LinearMap.id_apply]
    calc
      (∑ i, BalancedTensorProduct.tmul k A (φ i) (ψ (b i) • n)) =
          ∑ i, BalancedTensorProduct.tmul k A (op (ψ (b i)) • φ i) n := by
        congr 1
        ext i
        exact (BalancedTensorProduct.balance k A _ _ _).symm
      _ = BalancedTensorProduct.tmul k A (∑ i, op (ψ (b i)) • φ i) n := by
        simp only [← BalancedTensorProduct.mk_apply, ← LinearMap.sum_apply, ← map_sum]
      _ = BalancedTensorProduct.tmul k A ψ n := by rw [hdual]
  have hright : (balancedDualTensorHom k A P N).comp inv = LinearMap.id := by
    ext F x
    simp only [LinearMap.comp_apply, hinv, map_sum, LinearMap.sum_apply,
      balancedDualTensorHom_tmul, LinearMap.id_apply]
    simpa [map_sum, map_smul] using congrArg F (hsum x)
  exact ⟨LinearMap.injective_of_comp_eq_id _ _ hleft,
    LinearMap.surjective_of_comp_eq_id _ _ hright⟩

section Naturality

variable {P' N' : Type*} [AddCommMonoid P'] [Module A P']
  [AddCommGroup N'] [Module A N'] [Module k N'] [IsScalarTower k A N']

/-- Evaluation is contravariantly natural in the dualized module and covariantly
natural in the target. In particular, a map of projective presentations gives a
commuting square between the corresponding tensor and Hom maps. -/
theorem balancedDualTensorHom_map (f : P' →ₗ[A] P) (g : N →ₗ[A] N') :
    (balancedDualTensorHom k A P' N').comp
      (BalancedTensorProduct.map (f.lcomp k A) (g.restrictScalars k)
        (fun a φ ↦ by ext x; simp [MulOpposite.smul_eq_mul_unop])
        (fun a n ↦ by simp only [LinearMap.restrictScalars_apply, map_smul])) =
      (g.compRight k).comp ((f.lcomp k N).comp (balancedDualTensorHom k A P N)) := by
  apply BalancedTensorProduct.hom_ext
  intro φ n
  rw [LinearMap.comp_apply, BalancedTensorProduct.map_tmul]
  ext x
  simp

end Naturality

variable (P N)

/-- The canonical tensor–Hom equivalence for a finite projective left module.
The tensor product uses the opposite dual and is balanced over `A`. -/
noncomputable def balancedDualTensorHomEquiv [Module.Finite A P] [Module.Projective A P] :
    BalancedTensorProduct k A (Module.Dual A P) N ≃ₗ[k] (P →ₗ[A] N) :=
  LinearEquiv.ofBijective (balancedDualTensorHom k A P N)
    (balancedDualTensorHom_bijective k A)

@[simp]
theorem balancedDualTensorHomEquiv_toLinearMap [Module.Finite A P] [Module.Projective A P] :
    (balancedDualTensorHomEquiv k A P N).toLinearMap = balancedDualTensorHom k A P N := (rfl)

@[simp]
theorem balancedDualTensorHomEquiv_apply [Module.Finite A P] [Module.Projective A P]
    (z : BalancedTensorProduct k A (Module.Dual A P) N) :
    balancedDualTensorHomEquiv k A P N z = balancedDualTensorHom k A P N z := (rfl)

@[simp]
theorem balancedDualTensorHomEquiv_symm_balancedDualTensorHom
    [Module.Finite A P] [Module.Projective A P]
    (z : BalancedTensorProduct k A (Module.Dual A P) N) :
    (balancedDualTensorHomEquiv k A P N).symm (balancedDualTensorHom k A P N z) = z :=
  (balancedDualTensorHomEquiv k A P N).symm_apply_apply z

@[simp]
theorem balancedDualTensorHom_balancedDualTensorHomEquiv_symm
    [Module.Finite A P] [Module.Projective A P] (F : P →ₗ[A] N) :
    balancedDualTensorHom k A P N ((balancedDualTensorHomEquiv k A P N).symm F) = F :=
  (balancedDualTensorHomEquiv k A P N).apply_symm_apply F

end TauCeti

namespace LinearMap

open TauCeti

variable {k A M P N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommMonoid M] [Module A M] [Module.Finite A M]
  [AddCommGroup P] [Module A P] [Module.Projective A P]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- A map from a finitely generated module that factors through a projective module
lies in the image of balanced tensor evaluation. The projective intermediate module
need not be finitely generated. -/
theorem comp_mem_range_balancedDualTensorHom (f : M →ₗ[A] P) (g : P →ₗ[A] N) :
    g.comp f ∈ range (balancedDualTensorHom k A M N) := by
  classical
  obtain ⟨s, hs⟩ := (Module.projective_def (R := A) (P := P)).mp inferInstance
  obtain ⟨φ, hφ⟩ := (finsuppLinearMap_bijective_of_moduleFinite A M A P k).surjective
    (s.comp f)
  refine ⟨φ.sum (fun p ψ ↦ BalancedTensorProduct.tmul k A ψ (g p)), ?_⟩
  ext x
  -- Mathlib's map to finitely supported functions evaluates each coordinate functional.
  have hφx : Finsupp.mapRange (fun ψ : M →ₗ[A] A ↦ ψ x) (by simp) φ = s (f x) :=
    LinearMap.congr_fun hφ x
  have hsum : φ.sum (fun p ψ ↦ ψ x • p) = f x := by
    have hx := hs (f x)
    rw [← hφx, Finsupp.linearCombination_apply] at hx
    simp only [_root_.id_eq] at hx
    rw [Finsupp.sum_mapRange_index (h := fun (p : P) (a : A) ↦ a • p)
      (fun p ↦ zero_smul A p)] at hx
    exact hx
  simpa [Finsupp.sum, map_sum, map_smul] using congrArg g hsum

end LinearMap
