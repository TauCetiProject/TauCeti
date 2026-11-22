/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
public import TauCeti.Algebra.Lie.Reductive.Decomposition

/-!
# Reductive splitting of the Cartan `-1`-eigenspace

When the centre `Z(L)` and derived ideal `[L, L]` of a Lie algebra `L` are complementary, any
automorphism `θ` restricts to automorphisms `θ.centerCongr` on `Z(L)` and
`θ.derivedSeriesCongr 1` on `[L, L]`. Addition identifies the product of their `-1`-eigenspaces
with `θ.cartanP`, independently of any Cartan-involution predicate.

## Main definitions

* `LieEquiv.cartanPCenterDerivedEquiv`: linear splitting of `θ.cartanP` into its central and
  derived components when `L = Z(L) ⊕ [L, L]`.

## Main results

* `LieEquiv.coe_cartanPCenterDerivedEquiv_apply`: `cartanPCenterDerivedEquiv` acts by addition
  in `L`.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- When `L = Z(L) ⊕ [L, L]`, addition identifies the product of the `-1`-eigenspaces on `Z(L)` and
`[L, L]` with `θ.cartanP`. -/
noncomputable def cartanPCenterDerivedEquiv (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    (θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) ≃ₗ[R] θ.cartanP :=
  let f : (θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) →ₗ[R] θ.cartanP :=
    { toFun := fun p ↦ ⟨(p.1.val : L) + (p.2.val : L), by
        have h1 : θ p.1.val = -(p.1.val : L) := by
          simpa [coe_centerCongr] using congrArg Subtype.val (mem_cartanP.mp p.1.property)
        have h2 : θ p.2.val = -(p.2.val : L) := by
          simpa [coe_derivedSeriesCongr] using congrArg Subtype.val (mem_cartanP.mp p.2.property)
        rw [mem_cartanP, map_add, h1, h2, neg_add]⟩
      map_add' := fun p q ↦ by
        apply Subtype.ext
        simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, LieSubmodule.coe_add]
        abel
      map_smul' := fun c p ↦ by
        apply Subtype.ext
        simp [smul_add] }
  let e := LieIdeal.prodEquivOfIsCompl (center R L) (derivedSeries R L 1) h
  have hf_coe (p : θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) :
      (f p : L) = e (p.1.val, p.2.val) :=
    (LieIdeal.prodEquivOfIsCompl_apply (center R L) (derivedSeries R L 1) h
      (p.1.val, p.2.val)).symm
  LinearEquiv.ofBijective f <| by
    constructor
    · intro p q hpq
      have heq : (p.1.val, p.2.val) = (q.1.val, q.2.val) := by
        apply e.injective
        rw [LieEquiv.coe_toLieHom, ← hf_coe, ← hf_coe, hpq]
      exact Prod.ext (Subtype.ext (congrArg Prod.fst heq)) (Subtype.ext (congrArg Prod.snd heq))
    · intro x
      obtain ⟨⟨z, d⟩, hzd⟩ := e.surjective (x : L)
      have hsum : (z : L) + (d : L) = (x : L) :=
        (LieIdeal.prodEquivOfIsCompl_apply (center R L) (derivedSeries R L 1) h (z, d)).symm.trans
          hzd
      have hx : θ (x : L) = -(x : L) := mem_cartanP.mp x.property
      have hneg : (θ.centerCongr z, θ.derivedSeriesCongr 1 d) = (-z, -d) := by
        apply e.injective
        simp only [e, LieEquiv.coe_toLieHom, LieIdeal.prodEquivOfIsCompl_apply, coe_centerCongr,
          coe_derivedSeriesCongr, NegMemClass.coe_neg]
        rw [← map_add, hsum, hx, ← hsum, neg_add]
      have hz : z ∈ θ.centerCongr.cartanP :=
        mem_cartanP.mpr (congrArg Prod.fst hneg)
      have hd : d ∈ (θ.derivedSeriesCongr 1).cartanP :=
        mem_cartanP.mpr (congrArg Prod.snd hneg)
      exact ⟨(⟨z, hz⟩, ⟨d, hd⟩), Subtype.ext hsum⟩

/-- `cartanPCenterDerivedEquiv` acts by addition in `L`. -/
@[simp]
theorem coe_cartanPCenterDerivedEquiv_apply (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1))
    (p : θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) :
    (θ.cartanPCenterDerivedEquiv h p : L) = (p.1.val : L) + (p.2.val : L) := by
  rfl

end LieEquiv
