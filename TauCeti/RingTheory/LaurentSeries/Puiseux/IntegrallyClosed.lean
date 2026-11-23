/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.IntegrallyClosed
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Basic

/-!
# Constants are integrally closed in the Puiseux field

For any field `K`, every Puiseux series lies in some ramified level `K⸨t ^ (1 / n)⸩`, and `K` is
integrally closed in `K⸨X⸩` (`TauCeti.LaurentSeries.isIntegrallyClosedIn`). Consequently, the
Puiseux series algebraic over `K` are precisely the constants: `K` is integrally closed in
`puiseuxField K`.

Combined with `TauCeti.rootsOfUnityMulEquiv`, this implies in particular that all roots of unity in
`puiseuxField K` lie in `K`.

## Main results

* `TauCeti.puiseuxField.isIntegrallyClosedIn`: `K` is integrally closed in `puiseuxField K`.
-/

public section

namespace TauCeti.puiseuxField

variable (K : Type*) [Field K]

/-- A field `K` is integrally closed in `puiseuxField K`: the Puiseux series algebraic over `K`
are the constants. -/
instance isIntegrallyClosedIn : IsIntegrallyClosedIn K (puiseuxField K) := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap K (puiseuxField K)).injective, fun {x} hx ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    ((isIntegral_algHom_iff (levelEmbedding K n) (levelEmbedding K n).injective).mp hx)
  exact ⟨c, by rw [← AlgHom.commutes (levelEmbedding K n), hc]⟩

end TauCeti.puiseuxField
