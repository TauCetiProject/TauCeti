/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Dual

/-!
# Dual module maps and minimality

Precomposition dualizes a right-module map to a left-module map. Its range is the annihilator
of the original kernel, and in finite dimension an essential dual range is equivalent to a
superfluous original kernel. Thus dualizing preserves the minimality condition on the maps in
projective covers and injective envelopes.

As in `TauCeti.dualRightAction`, the dual actions are specified by equivariant linear
identifications, rather than competing global instances on linear-map types. The range
calculation reuses Mathlib's `LinearMap.range_dualMap_eq_dualAnnihilator_ker`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Sections I.4 and I.5.
-/

public section

namespace TauCeti

universe u v w t w' t'

section Semiring

variable {k : Type u} {A : Type v} {M : Type w} {N : Type t} {P : Type w'} {Q : Type t'}
  [CommSemiring k] [Semiring A] [Algebra k A]
  [AddCommMonoid M] [Module Aᵐᵒᵖ M] [Module k M] [IsScalarTower k Aᵐᵒᵖ M]
  [AddCommMonoid N] [Module A N] [Module k N]
  [AddCommMonoid P] [Module Aᵐᵒᵖ P] [Module k P] [IsScalarTower k Aᵐᵒᵖ P]
  [AddCommMonoid Q] [Module A Q] [Module k Q]
  (f : M →ₗ[Aᵐᵒᵖ] P)
  (eM : N ≃ₗ[k] Module.Dual k M)
  (heM : ∀ (a : A) (n : N) (m : M), eM (a • n) m = eM n (MulOpposite.op a • m))
  (eP : Q ≃ₗ[k] Module.Dual k P)
  (heP : ∀ (a : A) (q : Q) (p : P), eP (a • q) p = eP q (MulOpposite.op a • p))

/-- Precomposition, transported to the specified left duals of right modules. -/
def moduleDualMap : Q →ₗ[A] N where
  toFun q := eM.symm ((f.restrictScalars k).dualMap (eP q))
  map_add' _ _ := by simp
  map_smul' a q := by
    apply eM.injective
    ext m
    simp only [LinearEquiv.apply_symm_apply, heM, heP, LinearMap.dualMap_apply,
      LinearMap.restrictScalars_apply, map_smul, RingHom.id_apply]

/-- The dual map transports ordinary linear precomposition along the dual identifications. -/
@[simp]
theorem moduleDualMap_apply (q : Q) :
    moduleDualMap f eM heM eP heP q = eM.symm ((f.restrictScalars k).dualMap (eP q)) := (rfl)

/-- A dual module map evaluates by precomposition. -/
theorem moduleDualMap_apply_apply (q : Q) (m : M) :
    eM (moduleDualMap f eM heM eP heP q) m = eP q (f m) := by
  simp [LinearMap.dualMap_apply]

/-- Dualizing the identity gives the identity on the specified dual module. -/
@[simp]
theorem moduleDualMap_id :
    moduleDualMap (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) eM heM eM heM = LinearMap.id := by
  ext n
  apply eM.injective
  ext m
  simp

variable {S : Type*} {T : Type*}
  [AddCommMonoid S] [Module Aᵐᵒᵖ S] [Module k S] [IsScalarTower k Aᵐᵒᵖ S]
  [AddCommMonoid T] [Module A T] [Module k T]

/-- Dualizing a composite reverses the order of the two module maps. -/
theorem moduleDualMap_comp (g : P →ₗ[Aᵐᵒᵖ] S)
    (eS : T ≃ₗ[k] Module.Dual k S)
    (heS : ∀ (a : A) (t : T) (s : S), eS (a • t) s = eS t (MulOpposite.op a • s)) :
    moduleDualMap (g ∘ₗ f) eM heM eS heS =
      moduleDualMap f eM heM eP heP ∘ₗ moduleDualMap g eP heP eS heS := by
  ext t
  apply eM.injective
  ext m
  simp

end Semiring

section Field

variable {k : Type u} {A : Type v} {M : Type w} {N : Type t} {P : Type w'} {Q : Type t'}
  [Field k] [Semiring A] [Algebra k A]
  [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module k M] [IsScalarTower k Aᵐᵒᵖ M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [AddCommGroup P] [Module Aᵐᵒᵖ P] [Module k P] [IsScalarTower k Aᵐᵒᵖ P]
  [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q]
  (f : M →ₗ[Aᵐᵒᵖ] P)
  (eM : N ≃ₗ[k] Module.Dual k M)
  (heM : ∀ (a : A) (n : N) (m : M), eM (a • n) m = eM n (MulOpposite.op a • m))
  (eP : Q ≃ₗ[k] Module.Dual k P)
  (heP : ∀ (a : A) (q : Q) (p : P), eP (a • q) p = eP q (MulOpposite.op a • p))

/-- The image of a dual module map is the annihilator of the original kernel. Neither
module needs to be finite-dimensional for this range calculation. -/
theorem range_moduleDualMap :
    LinearMap.range (moduleDualMap f eM heM eP heP) =
      moduleDualAnnihilator eM heM (LinearMap.ker f) := by
  have hsquare : eM.toLinearMap ∘ₗ (moduleDualMap f eM heM eP heP).restrictScalars k =
      (f.restrictScalars k).dualMap ∘ₗ eP.toLinearMap := by
    ext q m
    exact moduleDualMap_apply_apply f eM heM eP heP q m
  apply Submodule.restrictScalars_injective k
  apply Submodule.map_injective_of_injective eM.injective
  rw [← LinearMap.range_restrictScalars, ← LinearMap.range_comp, hsquare,
    LinearEquiv.range_comp, LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_restrictScalars, moduleDualAnnihilator_restrictScalars,
    Submodule.map_comap_eq_of_surjective eM.surjective]

/-- In finite dimension, dualizing turns a superfluous kernel into an essential range,
and reflects this minimality condition. Only the original source needs to be finite. -/
theorem isEssential_range_moduleDualMap_iff [FiniteDimensional k M] :
    IsEssential (LinearMap.range (moduleDualMap f eM heM eP heP)) ↔
      IsSuperfluous (LinearMap.ker f) := by
  rw [range_moduleDualMap f eM heM eP heP, isEssential_moduleDualAnnihilator_iff]

end Field

end TauCeti
