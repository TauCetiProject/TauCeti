/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Derivations on generated intermediate fields

If an `R`-derivation `d : Derivation R F M` into an `F`-module vanishes on an intermediate base
field `E` and maps every generator in `s : Set F` into an `F`-submodule `S`, then `d` maps the
entire intermediate field `E(s)` into `S`.

## Main results

* `Derivation.map_mem_of_mem_adjoin`: derivatives on `IntermediateField.adjoin E s` stay in any
  `F`-submodule containing the derivatives of `s`, provided `d` vanishes on `E`.
* `Derivation.ext_of_intermediateField_adjoin_eq_top`: two `R`-derivations out of `F` agreeing
  on `E` and on a generating set `s` over `E` are equal.
-/

public section

namespace Derivation

/-- If an `R`-derivation `d : Derivation R F M` into an `F`-module vanishes on an intermediate
field `E` and maps every generator in `s` into an `F`-submodule `S`, then `d` maps the entire
intermediate field `E(s)` into `S`. -/
theorem map_mem_of_mem_adjoin {R E F M : Type*} [CommRing R] [Field E] [Field F]
    [Algebra R F] [Algebra E F] [AddCommGroup M] [Module R M] [Module F M]
    (d : Derivation R F M) (S : Submodule F M) {s : Set F}
    (hE : ∀ e : E, d (algebraMap E F e) = 0) (hs : ∀ z ∈ s, d z ∈ S) {x : F}
    (hx : x ∈ IntermediateField.adjoin E s) : d x ∈ S := by
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz => exact hs z hz
  | algebraMap e => simp [hE e]
  | add a b _ _ ha hb => rw [map_add]; exact S.add_mem ha hb
  | mul a b _ _ ha hb => rw [d.leibniz]; exact S.add_mem (S.smul_mem a hb) (S.smul_mem b ha)
  | inv a _ ha =>
    rw [d.leibniz_inv]
    exact S.smul_mem _ ha

/-- Two `R`-derivations out of a field `F` into an `F`-module that agree on an intermediate field
`E` and on a generating set `s` of `F` over `E` are equal. -/
theorem ext_of_intermediateField_adjoin_eq_top {R E F M : Type*} [CommRing R] [Field E] [Field F]
    [Algebra R F] [Algebra E F] [AddCommGroup M] [Module R M] [Module F M]
    {s : Set F} (hs : IntermediateField.adjoin E s = ⊤) {d₁ d₂ : Derivation R F M}
    (hE : ∀ e : E, d₁ (algebraMap E F e) = d₂ (algebraMap E F e))
    (h : Set.EqOn d₁ d₂ s) : d₁ = d₂ := by
  ext x
  have hmem := (d₁ - d₂).map_mem_of_mem_adjoin (⊥ : Submodule F M)
    (fun e ↦ by simp [hE e])
    (fun z hz ↦ (Submodule.mem_bot F).mpr (sub_eq_zero.mpr (h hz)))
    (hs.symm ▸ IntermediateField.mem_top (x := x))
  exact sub_eq_zero.mp ((Submodule.mem_bot F).mp hmem)

end Derivation
