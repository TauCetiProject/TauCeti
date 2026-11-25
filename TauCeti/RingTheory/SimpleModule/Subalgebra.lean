/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Semisimple subalgebras of an endomorphism algebra

Let `M` be a finite module over a commutative ring `k` and let `B` be a `k`-subalgebra of
`End_k(M)`. If `M` is a semisimple `B`-module, then `B` is a semisimple ring: for generators
`m₁, …, mₙ` of `M` over `k`, the map `b ↦ (b m₁, …, b mₙ)` embeds `B` in `Mⁿ` as a `B`-module,
because a `k`-linear endomorphism is determined by its values on generators.

## Main results

* `Subalgebra.isSemisimpleRing_of_isSemisimpleModule`: a subalgebra of `End_k(M)`, for `M` finite
  over `k`, over which `M` is semisimple, is a semisimple ring.
-/

public section

namespace Subalgebra

/-- **A subalgebra of `End_k(M)` over which `M` is semisimple is a semisimple ring**, when `M` is
finite over `k`: evaluation at finitely many generators of `M` embeds it in a finite power of
`M`. -/
theorem isSemisimpleRing_of_isSemisimpleModule {k M : Type*} [CommRing k] [AddCommGroup M]
    [Module k M] [Module.Finite k M] (B : Subalgebra k (Module.End k M))
    [IsSemisimpleModule B M] : IsSemisimpleRing B := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := k) (M := M)
  let e : B →ₗ[B] (Fin n → M) := LinearMap.pi fun i ↦ LinearMap.toSpanSingleton _ M (s i)
  refine IsSemisimpleModule.of_injective e fun a b hab ↦ Subtype.ext ?_
  exact LinearMap.ext_on_range hs fun i ↦ congr_fun hab i

end Subalgebra
