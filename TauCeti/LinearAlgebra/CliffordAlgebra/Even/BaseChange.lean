/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-!
# Even Clifford algebras along a change of base ring

Let `R → S` be an algebra, `Q` a quadratic form over `R` on `M` and `Q'` a quadratic form over
`S` on `N`, where `N` is also an `R`-module through `S`. An `R`-linear map `f : M → N` with
`Q' (f m) = Q m` in `S` induces an `R`-algebra map `ι m₁ ι m₂ ↦ ι (f m₁) ι (f m₂)` between the even
Clifford algebras. No hypothesis on `2` is needed, unlike for Mathlib's
`CliffordAlgebra.ofBaseChange`, and `N` need not be the tensor product `S ⊗[R] M`.

## Main definitions

* `TauCeti.evenBaseChange`: the map `CliffordAlgebra.even Q →ₐ[R] CliffordAlgebra.even Q'`
  induced by such an `f`.

## Main results

* `TauCeti.evenBaseChange_ι`: the map sends `ι m₁ ι m₂` to `ι (f m₁) ι (f m₂)`.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  {Q : QuadraticForm R M} {Q' : QuadraticForm S N}

/-- The bilinear map `(m₁, m₂) ↦ ι (f m₁) ι (f m₂)`. -/
private noncomputable def evenBaseChangeHom (f : M →ₗ[R] N)
    (hf : ∀ m, Q' (f m) = algebraMap R S (Q m)) : EvenHom Q (even Q') where
  bilin := LinearMap.mk₂ R (fun m₁ m₂ ↦ (even.ι Q').bilin (f m₁) (f m₂))
    (fun _ _ _ ↦ by simp only [map_add, LinearMap.add_apply])
    (fun c _ _ ↦ by
      simp only [map_smul, ← algebraMap_smul S c, LinearMap.smul_apply])
    (fun _ _ _ ↦ by simp only [map_add])
    (fun c _ _ ↦ by simp only [map_smul, ← algebraMap_smul S c])
  contract m := by
    rw [LinearMap.mk₂_apply, (even.ι _).contract, hf, ← IsScalarTower.algebraMap_apply]
  contract_mid m₁ m₂ m₃ := by
    rw [LinearMap.mk₂_apply, LinearMap.mk₂_apply, LinearMap.mk₂_apply,
      (even.ι _).contract_mid, hf, algebraMap_smul]

/-- The `R`-algebra map `CliffordAlgebra.even Q → CliffordAlgebra.even Q'` induced by an
`R`-linear map `f : M → N` into an `S`-module with `Q' (f m) = algebraMap R S (Q m)`, sending
`ι m₁ ι m₂` to `ι (f m₁) ι (f m₂)`. -/
noncomputable def evenBaseChange (f : M →ₗ[R] N) (hf : ∀ m, Q' (f m) = algebraMap R S (Q m)) :
    even Q →ₐ[R] even Q' :=
  even.lift Q (evenBaseChangeHom f hf)

/-- The map `evenBaseChange f hf` sends `ι m₁ ι m₂` to `ι (f m₁) ι (f m₂)`. -/
@[simp]
theorem evenBaseChange_ι (f : M →ₗ[R] N) (hf : ∀ m, Q' (f m) = algebraMap R S (Q m))
    (m₁ m₂ : M) :
    evenBaseChange f hf ((even.ι Q).bilin m₁ m₂) = (even.ι Q').bilin (f m₁) (f m₂) := by
  simp [evenBaseChange, evenBaseChangeHom]

end TauCeti
