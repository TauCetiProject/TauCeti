/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.IntSubring
public import TauCeti.RingTheory.Dagger.IntegralWashnitzer.Basic

/-!
# The integral Monsky–Washnitzer algebra is the integral subring of `K⟨X⟩†`

Let `K` be a complete nontrivially normed ultrametric field and `W = K⟨X⟩†` the Monsky–Washnitzer
algebra in finitely many variables. Its integral subring `W^int = {f | |f|sup ≤ 1}`
(`TauCeti.Dagger.intSubring`) is the Gauss unit ball of `W`, which is exactly the integral
Monsky–Washnitzer algebra `K°⟨X⟩†` of overconvergent series with coefficients in `K°`.

## Main results

* `TauCeti.Dagger.intWashnitzerAlgebra.range_toWashnitzerAlgebra`: `W^int = K°⟨X⟩†` inside `W`.
* `TauCeti.Dagger.intWashnitzerAlgebra.equivIntSubring`: the induced ring isomorphism
  `K°⟨X⟩† ≃+* W^int`, with `TauCeti.Dagger.intWashnitzerAlgebra.coe_equivIntSubring` describing
  it on series.

## References

* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006),
  §3.2.
-/

public section

namespace TauCeti.Dagger.intWashnitzerAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (σ : Type*) [Finite σ]

/-- **`W^int = K°⟨X⟩†`.** The integral subring of the Monsky–Washnitzer algebra `W = K⟨X⟩†` is the
integral Monsky–Washnitzer algebra of overconvergent series with coefficients in `K°`. -/
theorem range_toWashnitzerAlgebra :
    (toWashnitzerAlgebra σ K).range = intSubring K (washnitzerAlgebra σ K) := by
  ext f
  rw [RingHom.mem_range, washnitzerAlgebra.mem_intSubring_iff_norm_le_one,
    ← mem_intWashnitzerAlgebra_iff_norm_le_one]
  exact ⟨by rintro ⟨g, rfl⟩; simp, fun hf ↦ ⟨⟨f, hf⟩, toWashnitzerAlgebra_mk f hf⟩⟩

/-- The ring isomorphism `K°⟨X⟩† ≃+* W^int` between the integral Monsky–Washnitzer algebra and the
integral subring of `W = K⟨X⟩†`: the codomain restriction of the inclusion `toWashnitzerAlgebra`,
which is bijective onto `W^int` by `range_toWashnitzerAlgebra`. -/
noncomputable def equivIntSubring :
    intWashnitzerAlgebra σ K ≃+* intSubring K (washnitzerAlgebra σ K) :=
  RingEquiv.ofBijective ((toWashnitzerAlgebra σ K).codRestrict _ fun f ↦
      (range_toWashnitzerAlgebra σ).le (RingHom.mem_range_self _ f))
    (show Function.Bijective _ from
      ⟨RingHom.injective_codRestrict.mpr toWashnitzerAlgebra_injective, fun g ↦ by
        obtain ⟨f, hf⟩ := RingHom.mem_range.mp ((range_toWashnitzerAlgebra σ).ge g.property)
        exact ⟨f, Subtype.ext ((RingHom.codRestrict_apply _ _ _ f).trans hf)⟩⟩)

/-- The isomorphism `K°⟨X⟩† ≃+* W^int` is the inclusion `toWashnitzerAlgebra` on series. -/
@[simp]
theorem coe_equivIntSubring (f : intWashnitzerAlgebra σ K) :
    (equivIntSubring σ f : washnitzerAlgebra σ K) = toWashnitzerAlgebra σ K f := by
  rw [equivIntSubring, RingEquiv.ofBijective_apply, RingHom.codRestrict_apply]

end TauCeti.Dagger.intWashnitzerAlgebra
