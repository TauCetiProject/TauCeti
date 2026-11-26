/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Tendsto

/-!
# Limits along filters restricted to a set

## Main results

* `Filter.Tendsto.inf_principal_of_mapsTo`: a map sending `s` into `t` which tends to `l'` along
  `l ⊓ 𝓟 s` tends to `l' ⊓ 𝓟 t`.
-/

public section

namespace Filter

variable {α β : Type*}

/-- A map sending `s` into `t` which tends to `l'` along `l ⊓ 𝓟 s` tends to `l' ⊓ 𝓟 t`. -/
theorem Tendsto.inf_principal_of_mapsTo {f : α → β} {l : Filter α} {l' : Filter β} {s : Set α}
    {t : Set β} (hf : Tendsto f (l ⊓ 𝓟 s) l') (hst : Set.MapsTo f s t) :
    Tendsto f (l ⊓ 𝓟 s) (l' ⊓ 𝓟 t) :=
  tendsto_inf.mpr ⟨hf, hst.tendsto.mono_left inf_le_right⟩

end Filter
