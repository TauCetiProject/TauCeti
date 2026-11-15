/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Option.Basic

/-!
# Basic lemmas on `Option`

* `Option.unattach_bind`: forgetting subtype membership commutes with `Option.bind`.
-/

public section

namespace Option

/-- Forgetting subtype membership commutes with `Option.bind`. -/
@[simp]
theorem unattach_bind {α β : Type*} {q : β → Prop} (o : Option α)
    (f : α → Option {y // q y}) :
    (o.bind f).unattach = o.bind fun x ↦ (f x).unattach := by
  cases o <;> simp

end Option
