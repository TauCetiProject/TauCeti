/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Fibre dimensions under change of scalars

The dimension of the fibre of a finite module is unchanged by extending its residue field.
In particular, the fibre dimension function of a base-changed module is the pullback of the
original dimension function on prime spectra. No flatness of the change of scalars is needed.

Over a Jacobson ring the fibre dimensions of a finite module are determined by its closed fibres:
if all closed points specializing a prime `p` have fibre dimension `k`, then so does `p`. This is
how a constant rank condition checked at closed points of a scheme of finite type over a field
propagates to all points.

These statements use the fibre-dimension characterization of Fitting ideals.
-/

public section

open TensorProduct Module

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
  (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Extending the residue field does not change the dimension of the fibre of a finite module.
The field `K` may be any `R`-algebra whose structure map has kernel `p`. -/
theorem finrank_tensorProduct_eq_finrank_fiber (K : Type*) [Field K] [Algebra R K]
    (hK : RingHom.ker (algebraMap R K) = p) :
    finrank K (K ⊗[R] M) = finrank p.ResidueField (p.Fiber M) := by
  apply eq_of_forall_lt_iff
  intro n
  rw [← TauCeti.fittingIdeal_map_eq_bot_iff_lt_finrank,
    Ideal.map_eq_bot_iff_le_ker, hK, TauCeti.fittingIdeal_le_iff_lt_finrank]

variable {M}

/-- Fibre dimensions commute with arbitrary base change of the ring: the fibre over `q` of
`S ⊗[R] M` has the same dimension as the fibre of `M` at the inverse image of `q`. -/
theorem finrank_fiber_baseChange {S : Type*} [CommRing S] [Algebra R S] (q : Ideal S)
    [q.IsPrime] :
    finrank q.ResidueField (q.Fiber (S ⊗[R] M)) =
      finrank (q.comap (algebraMap R S)).ResidueField
        ((q.comap (algebraMap R S)).Fiber M) := by
  apply eq_of_forall_lt_iff
  intro n
  rw [← TauCeti.fittingIdeal_le_iff_lt_finrank,
    ← TauCeti.fittingIdeal_le_iff_lt_finrank,
    TauCeti.fittingIdeal_baseChange, Ideal.map_le_iff_le_comap]

variable (M)

/-- The fibre of a product of finite modules has dimension the sum of the dimensions of the
fibres. -/
theorem finrank_fiber_prod (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    finrank p.ResidueField (p.Fiber (M × N)) =
      finrank p.ResidueField (p.Fiber M) + finrank p.ResidueField (p.Fiber N) := by
  rw [(TensorProduct.prodRight R p.ResidueField p.ResidueField M N).finrank_eq, finrank_prod]

/-- Over a Jacobson ring, the fibres of a finite module at closed points determine all fibre
dimensions: if every maximal ideal containing the prime `p` has fibre dimension `k`, then the
fibre at `p` has dimension `k` too. -/
theorem finrank_fiber_eq_of_forall_isMaximal [IsJacobsonRing R] {k : ℕ}
    (h : ∀ (m : Ideal R) [m.IsMaximal], p ≤ m → finrank m.ResidueField (m.Fiber M) = k) :
    finrank p.ResidueField (p.Fiber M) = k := by
  obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal ‹p.IsPrime›.ne_top
  apply le_antisymm
  · -- Fibre dimensions can only grow under specialization.
    by_contra! hlt
    have hle := ((TauCeti.fittingIdeal_le_iff_lt_finrank p k).2 hlt).trans hpm
    rw [TauCeti.fittingIdeal_le_iff_lt_finrank, h m hpm] at hle
    exact lt_irrefl k hle
  · -- The prime `p` is the intersection of the maximal ideals containing it.
    cases k with
    | zero => exact Nat.zero_le _
    | succ j =>
      rw [Nat.succ_le_iff, ← TauCeti.fittingIdeal_le_iff_lt_finrank,
        ← IsJacobsonRing.out ‹_› ‹p.IsPrime›.isRadical]
      refine le_sInf fun n ⟨hpn, hn⟩ ↦ ?_
      rw [TauCeti.fittingIdeal_le_iff_lt_finrank, h n hpn]
      exact Nat.lt_succ_self j

end Ideal
