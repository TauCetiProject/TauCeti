/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.LanguageMap

/-!
# Constants interpreted through a map

For a language `L` and a map `c : A → M`, Mathlib's `constantsOn.structure c` makes `M` an
`L[[A]]`-structure in which the constant symbol of `a : A` is interpreted by `c a`. This file
records that interpretation as a simp lemma.

## Main results

* `FirstOrder.Language.coe_con_constantsOn`: under `constantsOn.structure c`, the constant symbol
  of `a` denotes `c a`.
-/

public section

namespace FirstOrder.Language

variable {L : Language} {A : Type*} {M : Type*}

/-- Under the structure `constantsOn.structure c`, the constant symbol of `a : A` in `L[[A]]`
denotes `c a`. -/
@[simp]
theorem coe_con_constantsOn [L.Structure M] (c : A → M) (a : A) :
    letI := constantsOn.structure c
    ((L.con a : L[[A]].Constants) : M) = c a := (rfl)

end FirstOrder.Language
