/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Algebraize
import TauCeti.LinearAlgebra.Unimodular

/-!
# Free ring homomorphisms

A ring homomorphism `f : R →+* S` is *free* when `S` is a free `R`-module through `f`, in the
same way that `RingHom.Flat` and `RingHom.Finite` transport `Module.Flat` and `Module.Finite`
to ring homomorphisms. Phrasing freeness for a ring homomorphism rather than an algebra keeps the
module structure of `f.toAlgebra` apart from the multiplication of `R` on itself when `f` is an
endomorphism `R →+* R`, such as the Frobenius of a ring of characteristic `p`. Saying that `R` is
free over the image of an injective endomorphism `σ` is then `σ.Free`.

## Main definitions

* `RingHom.Free f`: `S` is a free `R`-module through `f : R →+* S`.

## Main results

* `RingHom.free_algebraMap_iff`: for an `R`-algebra `S`, `(algebraMap R S).Free` is
  `Module.Free R S`.
* `RingHom.Free.comp`: free ring homomorphisms compose.
* `RingHom.Free.pow`: every iterate of a free endomorphism is free.
* `RingHom.Free.exists_addMonoidHom_eq_one`: if `f : R →+* S` is free with `R` local, every
  `y ∉ f(𝔪) S` is sent to `1` by an additive map `S → R` that is linear along `f`.
-/

public section

namespace RingHom

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/-- A ring homomorphism `f : R →+* S` is free if `S` is a free `R`-module through `f`. -/
def Free (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Module.Free R S

/-- Unfolding `RingHom.Free`: `f` is free when `S` is a free `R`-module through `f`. -/
theorem free_iff (f : R →+* S) : f.Free ↔ letI := f.toAlgebra; Module.Free R S :=
  Iff.rfl

/-- For an `R`-algebra `S`, the structure map is free exactly when `S` is a free `R`-module. -/
@[simp]
theorem free_algebraMap_iff [Algebra R S] : (algebraMap R S).Free ↔ Module.Free R S := by
  rw [RingHom.Free, toAlgebra_algebraMap]

namespace Free

variable (R) in
/-- The identity of a semiring is free. -/
theorem id : (RingHom.id R).Free :=
  Module.Free.self R

/-- Free ring homomorphisms compose: if `S` is free over `R` through `f` and `T` is free over
`S` through `g`, then `T` is free over `R` through `g.comp f`. -/
theorem comp {f : R →+* S} {g : S →+* T} (hf : f.Free) (hg : g.Free) : (g.comp f).Free := by
  algebraize [f, g, g.comp f]
  have : Module.Free R S := hf
  have : Module.Free S T := hg
  exact Module.Free.trans (S := S)

/-- Every iterate `f ^ n` of a free endomorphism `f` is free. -/
theorem pow {f : R →+* R} (hf : f.Free) (n : ℕ) : (f ^ n).Free := by
  induction n with
  | zero => exact id R
  | succ n ih => rw [pow_succ, RingHom.mul_def]; exact hf.comp ih

end Free

open IsLocalRing in
/-- Let `f : R →+* S` be free with `R` local. An element `y ∉ f(𝔪) S` is sent to `1` by an
additive map `μ : S → R` that is linear along `f`, that is `μ (f a * x) = a * μ x`: in a basis of
`S` over `R`, some coordinate of `y` is a unit. For an endomorphism `f : R →+* R` this is a
functional on `R` over the image of `f`. -/
theorem Free.exists_addMonoidHom_eq_one [IsLocalRing R] {f : R →+* S} (hf : f.Free) {y : S}
    (hy : y ∉ (maximalIdeal R).map f) :
    ∃ μ : S →+ R, (∀ a x, μ (f a * x) = a * μ x) ∧ μ y = 1 := by
  let := f.toAlgebra
  have : Module.Free R S := hf
  obtain ⟨μ, hμ⟩ := Module.isUnimodular_iff.1 <|
    (Module.Free.isUnimodular_iff_notMem_smul_top (R := R) (v := y)).2
      (by rwa [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, RingHom.algebraMap_toAlgebra])
  exact ⟨μ.toAddMonoidHom, fun a x ↦ by simpa [RingHom.smul_toAlgebra] using μ.map_smul a x, hμ⟩

end RingHom
