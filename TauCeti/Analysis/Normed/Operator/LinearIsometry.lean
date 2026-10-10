/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T01.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
addition to `Mathlib/Analysis/Normed/Operator/LinearIsometry.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry


/-! # `LinearIsometryEquiv.ofEq` on subtype elements

`LinearIsometryEquiv.ofEq` is the identity on underlying elements.  The existing
`coe_ofEq_apply` says so after coercion to the ambient space; this `rfl` variant keeps
the result in subtype form, so `simp` can push `ofEq` through explicit `Subtype.mk`s.
That matters when the result is fed to another bundled map (as in the Gram-rigidity
composites in `ForTauCeti/Analysis/InnerProductSpace/GramMatrix.lean`, topic T04),
where no
ambient coercion is available for `coe_ofEq_apply` to rewrite under.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.Normed.Operator.LinearIsometry`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `36d670a`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

variable {E R' : Type*} [SeminormedAddCommGroup E] [Ring R'] [Module R' E]
  {p q : Submodule R' E}

/-- Transporting along an equality of submodules does not move the underlying vector. -/
@[simp]
theorem LinearIsometryEquiv.ofEq_apply_mk (h : p = q) (x : E) (hx : x ∈ p) :
    LinearIsometryEquiv.ofEq p q h ⟨x, hx⟩ = ⟨x, h ▸ hx⟩ :=
  rfl

end TauCeti
