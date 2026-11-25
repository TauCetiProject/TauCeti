/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.AlexandrovDiscrete
import TauCeti.Topology.LocallyConstant.CompactSupport.OpenClosed

/-!
# Examples of the open-closed sequence of locally constant functions with compact support

This file tests extension by zero and restriction on `C_c^∞(X, M)`:

* extension by zero from the empty subset is zero;
* extension by zero from the whole space does not change the function;
* restriction to the complement annihilates an extension by zero;
* on the discrete space `ℕ`, which is an l-space, every finitely supported function on the even
  numbers is the restriction of one on `ℕ`.
-/

open Set LocallyConstant LocallyConstant.compactlySupported

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-! ### 1. Extension from the empty space -/

example (f : compactlySupported ℤ (∅ : Set X) ℤ) : extendByZero ℤ ℤ isOpen_empty f = 0 :=
  compactlySupported.ext fun x => extendByZero_apply_of_notMem _ f (notMem_empty x)

/-! ### 2. Extension from the whole space -/

example (f : compactlySupported ℤ (univ : Set X) ℤ) (x : X) :
    (extendByZero ℤ ℤ isOpen_univ f : LocallyConstant X ℤ) x =
      (f : LocallyConstant (univ : Set X) ℤ) ⟨x, mem_univ x⟩ :=
  extendByZero_apply_coe isOpen_univ f ⟨x, mem_univ x⟩

/-! ### 3. Restriction to the complement annihilates the extension -/

example {U : Set X} (hU : IsOpen U) (f : compactlySupported ℤ U ℤ) :
    restrict ℤ ℤ hU.isClosed_compl (extendByZero ℤ ℤ hU f) = 0 := by
  simp

/-! ### 4. Surjectivity of restriction on a discrete space -/

example (f : compactlySupported ℤ {n : ℕ | Even n} ℤ) :
    ∃ g : compactlySupported ℤ ℕ ℤ, restrict ℤ ℤ (isClosed_discrete _) g = f :=
  restrict_surjective _ f
