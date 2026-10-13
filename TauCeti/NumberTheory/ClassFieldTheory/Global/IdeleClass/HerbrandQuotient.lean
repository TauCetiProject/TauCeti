/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.SIdeles
import TauCeti.NumberTheory.ClassFieldTheory.Global.OrdinaryUnits
import TauCeti.NumberTheory.ClassFieldTheory.Global.SUnitsCohomology
import TauCeti.NumberTheory.ClassFieldTheory.Global.Units
import TauCeti.NumberTheory.NumberField.Global.Ideles.Support

/-!
# The Herbrand quotient of the idele classes

For a cyclic extension `L/K` of number fields, the idele class group `C_L` with its Galois action
has Herbrand quotient

```text
h(C_L) = [L : K]
```

(`herbrandQuotient_ideleClassRep_eq_finrank`). This is the cohomological content of the first
fundamental inequality of global class field theory.

The proof chooses a finite set `S` of finite places of `K` outside which `L/K` is unramified and
whose primes upstairs generate the ideal class group of `L`, so that
`0 → U_{L,S} → I_{L,S} → C_L → 0` is short exact and `h(C_L) = h(I_{L,S}) / h(U_{L,S})`. Both
quotients split into an archimedean and a finite-place factor:

```text
h(I_{L,S}) = h(L_∞ˣ) · ∏_{v ∈ S} [L_w : K_v],
h(U_{L,S}) = h((𝓞 L)ˣ) · ∏_{v ∈ S} [L_w : K_v],
```

and the Herbrand quotient of the units is that of the infinite ideles divided by the degree,
`h((𝓞 L)ˣ) = h(ℤ[S_∞(L)]) / [L : K] = h(L_∞ˣ) / [L : K]`. The local degrees at `S` and the
archimedean factor cancel, leaving `[L : K]`.

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_ideleClassRep_eq_finrank`: `h(C_L) = [L : K]` for a
  cyclic extension `L/K` of number fields.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §4, Theorem 4.3.
-/

public noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdicCompletionExtension

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- **The Herbrand quotient of the idele classes** of a cyclic extension `L/K` of number fields is
the degree: `h(C_L) = [L : K]`. -/
theorem herbrandQuotient_ideleClassRep_eq_finrank :
    TateCohomology.herbrandQuotient (ideleClassRep K L) = Module.finrank K L := by
  obtain ⟨S, hgen, hunram⟩ :=
    GlobalNumberFields.exists_finset_primesAbove_closure_eq_top_and_isUnramified K L
  have := finite_tateCohomology_zero_sUnitsRep (L := L) (S : Set (HeightOneSpectrum (𝓞 K)))
  have := finite_tateCohomology_negOne_sUnitsRep (L := L) (S : Set (HeightOneSpectrum (𝓞 K)))
  have := (finite_tateCohomology_sIdelesRep (K := K) (L := L) hunram).2
  rw [herbrandQuotient_ideleClassRep L hgen,
    herbrandQuotient_sIdelesRep_eq_herbrandQuotient_ofMulAction hunram,
    herbrandQuotient_ofMulAction_places S (placeAbove L S),
    herbrandQuotient_sUnitsRep S (placeAbove L S), herbrandQuotient_sUnitsRep_empty,
    herbrandQuotient_units_eq_div, herbrandQuotient_ofMulAction_infinitePlace]
  -- The archimedean factor `2 ^ r` and the local degrees at `S` cancel.
  have hP : ∏ v : S, (Module.finrank (v.1.adicCompletion K)
      ((placeAbove L S v).1.adicCompletion L) : ℚ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ ↦ Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn : (Module.finrank K L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  field_simp

end TauCeti.ClassFieldTheory
