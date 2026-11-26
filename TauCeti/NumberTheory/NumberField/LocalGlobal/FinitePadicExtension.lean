/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.Data.Nat.Prime.Basic
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# The completion of a number field at a finite place is a finite extension of `ℚ_p`

Let `K` be a number field and `v` a finite place of `K`, lying over the prime `p` of `ℚ`
(`Rat.HeightOneSpectrum.primesEquiv (v.under (𝓞 ℚ))`). The completion `K_v` contains a copy of
`ℚ_p`: Mathlib identifies the completion `ℚ_{(p)}` of `ℚ` at the prime below `v` with `ℚ_p`
(`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`), and the inclusion `ℚ → K` extends to the
canonical continuous map `ℚ_{(p)} → K_v`
(`IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension`).
The composite `ℚ_p → K_v` is the unique continuous ring homomorphism, since `ℚ` is dense in
`ℚ_p` (`RingHom.ext_padic_of_continuous`).

Through this map `K_v` is a finite extension of `ℚ_p` compatible with the valuative relations,
that is, a `TauCeti.FinitePadicExtension`. Results proved over a finite extension of `ℚ_p` —
finite generation of the absolute Galois group, Tate's local Euler characteristic formula, and
the local duality statements built on them — therefore apply at every finite place of a number
field. The structure is a definition, not a global instance: it carries the `ℚ_p`-algebra
structure of `K_v` as data, which a consumer activates locally.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.padicRingHom`: the ring homomorphism `ℚ_p → K_v`.
* `IsDedekindDomain.HeightOneSpectrum.finitePadicExtension`: `K_v` as a finite extension of
  `ℚ_p`, with structure map `padicRingHom`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.continuous_padicRingHom`: `padicRingHom` is continuous.
* `IsDedekindDomain.HeightOneSpectrum.finite_padicRingHom`: `K_v` is finite-dimensional over
  `ℚ_p`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §§4–6.
-/

public section

noncomputable section

open IsDedekindDomain NumberField TauCeti Rat.HeightOneSpectrum
open scoped NumberField AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **The embedding `ℚ_p → K_v`** of the `p`-adic numbers into the completion of a number field
at a finite place `v` above `p`: the inverse of Mathlib's identification of the completion of `ℚ`
at `p` with `ℚ_p`, followed by the canonical map of completions `ℚ_{(p)} → K_v`. -/
def padicRingHom : ℚ_[primesEquiv (v.under (𝓞 ℚ))] →+* v.adicCompletion K :=
  have : v.asIdeal.LiesOver (v.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  (adicCompletionExtension ℚ K (v.under (𝓞 ℚ)) v).comp
    (RingEquivClass.toRingEquiv (adicCompletion.padicEquiv (v.under (𝓞 ℚ)))).symm.toRingHom

/-- The embedding `ℚ_p → K_v` is continuous. -/
theorem continuous_padicRingHom : Continuous v.padicRingHom :=
  have : v.asIdeal.LiesOver (v.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  (continuous_adicCompletionExtension ℚ K (v.under (𝓞 ℚ)) v).comp
    (Homeomorph.ofClass (adicCompletion.padicEquiv (v.under (𝓞 ℚ)))).symm.continuous

/-- The embedding `ℚ_p → K_v` is finite: `K_v` is a finite-dimensional `ℚ_p`-vector space. -/
theorem finite_padicRingHom : v.padicRingHom.Finite := by
  have : v.asIdeal.LiesOver (v.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  have h : (adicCompletionExtension ℚ K (v.under (𝓞 ℚ)) v).Finite := by
    rw [← algebraMap_adicCompletionExtensionAlgebra]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact h.comp (RingHom.Finite.of_surjective _
    (RingEquivClass.toRingEquiv (adicCompletion.padicEquiv (v.under (𝓞 ℚ)))).symm.surjective)

/-- **The completion of a number field at a finite place `v` is a finite extension of `ℚ_p`**,
`p` being the prime below `v`, with structure map `padicRingHom`
(`algebraMap_finitePadicExtension`). -/
@[instance_reducible]
def finitePadicExtension :
    FinitePadicExtension (v.adicCompletion K) (primesEquiv (v.under (𝓞 ℚ))) :=
  letI := v.padicRingHom.toAlgebra
  { algebra := v.padicRingHom.toAlgebra
    toModuleFinite := v.finite_padicRingHom
    toValuativeExtension :=
      ValuativeExtension.of_continuous_algebraMap v.continuous_padicRingHom }

/-- The `ℚ_p`-algebra structure of `finitePadicExtension v` is given by `padicRingHom`. -/
theorem algebraMap_finitePadicExtension :
    letI := v.finitePadicExtension
    algebraMap ℚ_[primesEquiv (v.under (𝓞 ℚ))] (v.adicCompletion K) = v.padicRingHom :=
  (rfl)

end IsDedekindDomain.HeightOneSpectrum
