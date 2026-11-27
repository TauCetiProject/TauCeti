/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
-- Non-public: the trace criterion for nilpotence and the Jacobson radical are used only
-- inside the proof of `Subalgebra.eq_zero_of_forall_trace_mul_eq_zero`.
import TauCeti.LinearAlgebra.Trace.Nilpotent
import TauCeti.RingTheory.Jacobson.Basic

/-!
# Semisimple subalgebras of an endomorphism algebra

Let `M` be a finite module over a commutative ring `k` and let `B` be a `k`-subalgebra of
`End_k(M)`. If `M` is a semisimple `B`-module, then `B` is a semisimple ring: for generators
`m₁, …, mₙ` of `M` over `k`, the map `b ↦ (b m₁, …, b mₙ)` embeds `B` in `Mⁿ` as a `B`-module,
because a `k`-linear endomorphism is determined by its values on generators.

Over a field `k` of characteristic zero and for `M` finite-dimensional, the trace pairing
`(x, y) ↦ tr(x y)` of `End_k(M)` is then nondegenerate on such a `B`. If `x ∈ B` pairs to zero
with all of `B`, every left multiple `a x` has
`tr((a x) ^ (m + 1)) = tr(x (a x) ^ m a) = 0` for all `m`, so it is nilpotent. Hence `x` lies in
the Jacobson radical of `B`, which vanishes for a semisimple ring, so `x = 0`. This pairing recovers
an element of `B` from its traces against `B`. Characteristic zero is needed: in characteristic `p`
the identity of `k ^ p` spans a semisimple subalgebra and pairs to zero with it.

## Main results

* `Subalgebra.isSemisimpleRing_of_isSemisimpleModule`: a subalgebra of `End_k(M)`, for `M` finite
  over `k`, over which `M` is semisimple, is a semisimple ring.
* `Subalgebra.eq_zero_of_forall_trace_mul_eq_zero`: in characteristic zero, the trace pairing of
  `End_k(M)` is nondegenerate on such a subalgebra.
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

/-- **The trace pairing is nondegenerate on a subalgebra over which the module is semisimple.** Let
`M` be a finite-dimensional vector space over a field of characteristic zero and `B` a subalgebra of
`End_k(M)` over which `M` is semisimple. An element `x ∈ B` with `tr(x b) = 0` for every `b ∈ B` is
zero. -/
theorem eq_zero_of_forall_trace_mul_eq_zero {k M : Type*} [Field k] [CharZero k] [AddCommGroup M]
    [Module k M] [FiniteDimensional k M] (B : Subalgebra k (Module.End k M))
    [IsSemisimpleModule B M] {x : Module.End k M} (hx : x ∈ B)
    (h : ∀ b ∈ B, LinearMap.trace k M (x * b) = 0) : x = 0 := by
  have := B.isSemisimpleRing_of_isSemisimpleModule
  have hxrad : (⟨x, hx⟩ : B) ∈ Ring.jacobson B :=
    TauCeti.Ring.mem_jacobson_of_forall_isNilpotent_mul fun a ↦
      B.val.isNilpotent_of_forall_trace_mul_eq_zero Subtype.val_injective fun b ↦ by
        simp only [map_mul]
        rw [← mul_assoc, LinearMap.trace_mul_comm]
        exact h _ (B.mul_mem b.property a.property)
  rw [IsSemisimpleRing.jacobson_eq_bot] at hxrad
  exact congrArg Subtype.val (Ideal.mem_bot.mp hxrad)

end Subalgebra
