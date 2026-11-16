/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.Basic

/-!
# Primitive-recursive maps of products and sums

Applying primitive-recursive maps to the two components of a pair (`Prod.map`) or to the two
summands of a sum (`Sum.map`) is primitive recursive, for the standard encodings of products and
sums. Renaming the letters of words along a primitive-recursive map is an instance.
-/

public section

namespace Primrec

variable {α β γ δ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]

/-- Applying primitive-recursive maps to the two components of a pair is primitive recursive. -/
theorem prodMap {f : α → γ} {g : β → δ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Prod.map f g) :=
  (hf.comp fst).pair (hg.comp snd)

/-- Applying primitive-recursive maps to the two summands of a sum is primitive recursive. -/
theorem sumMap {f : α → γ} {g : β → δ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Sum.map f g) :=
  sumCasesOn .id (sumInl.comp (hf.comp snd)).to₂ (sumInr.comp (hg.comp snd)).to₂

end Primrec
