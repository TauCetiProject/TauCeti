/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import TauCeti.Algebra.Module.Projective.Semilinear

/-!
# Projectivity of a reduction along a surjective ring homomorphism

Let `f : A →+* B` be a surjective ring homomorphism and `I` an ideal of `A` contained in the kernel
of `f`. If `M` is a projective `A`-module, then its reduction `M ⧸ I • M`, endowed with any
`B`-module structure through which `A` acts via `f`, is a projective `B`-module.

No commutativity is assumed. A typical application is reduction of coefficients: a projective
`ℤ_p[G]`-module reduces modulo `p` to a projective `𝔽_p[G]`-module.

## Main results

* `RingHom.projective_quotient_smul_top`: the reduction of a projective module along a surjective
  ring homomorphism is projective.
-/

public section

open scoped Pointwise

namespace RingHom

variable {A B M : Type*} [Ring A] [Ring B] [AddCommGroup M] [Module A M]

/-- **Reduction along a surjective ring homomorphism preserves projectivity.** Let
`f : A →+* B` be surjective and `I ≤ ker f`. If `M` is a projective `A`-module, then
`M ⧸ I • M` is a projective `B`-module for any `B`-module structure through which each `a : A` acts
as `f a`. -/
theorem projective_quotient_smul_top [Module.Projective A M] (f : A →+* B)
    (hf : Function.Surjective f) {I : Ideal A} (hI : I ≤ RingHom.ker f)
    [Module B (M ⧸ I • (⊤ : Submodule A M))]
    (hsmul : ∀ (a : A) (q : M ⧸ I • (⊤ : Submodule A M)), f a • q = a • q) :
    Module.Projective B (M ⧸ I • (⊤ : Submodule A M)) := by
  let Q := M ⧸ I • (⊤ : Submodule A M)
  apply Module.Projective.of_lifting_property''
  intro g hg
  -- Lift the semilinear quotient map through a surjection from a free `B`-module.
  let π : M →ₛₗ[f] Q :=
    { (I • (⊤ : Submodule A M)).mkQ.toAddMonoidHom with
      map_smul' := fun a x ↦ ((I • (⊤ : Submodule A M)).mkQ.map_smul a x).trans
        (hsmul a _).symm }
  obtain ⟨h, hh⟩ := Module.projective_lifting_property_semilinear g hg π
  have hkill : I • (⊤ : Submodule A M) ≤ LinearMap.ker h := by
    refine Submodule.smul_le.mpr fun a ha x _ ↦ ?_
    rw [LinearMap.mem_ker, h.map_smulₛₗ, RingHom.mem_ker.mp (hI ha), zero_smul]
  -- The lift kills `I • M`, so it descends to the quotient.
  let hA : Q →ₛₗ[f] (Q →₀ B) := (I • (⊤ : Submodule A M)).liftQ h hkill
  let hB : Q →ₗ[B] (Q →₀ B) :=
    { toFun := hA
      map_add' := hA.map_add
      map_smul' := fun b q ↦ by
        obtain ⟨a, rfl⟩ := hf b
        rw [RingHom.id_apply, hsmul, hA.map_smulₛₗ] }
  refine ⟨hB, LinearMap.ext fun q ↦ ?_⟩
  induction q using Submodule.Quotient.induction_on with
  | _ x => exact LinearMap.congr_fun hh x

end RingHom
