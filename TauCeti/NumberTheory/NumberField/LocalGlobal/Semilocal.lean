/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The semi-local map `K_v ⊗[K] L → ∏_{w ∣ v} L_w`

Let `L/K` be an extension of number fields and `v` a finite place of `K`. Every finite place `w`
of `L` above `v` gives a completion `L_w`, which is a `K_v`-algebra through the canonical
completion map `completionAlgHom v w`. Together these give the semi-local map

```text
semilocalHom v : K_v ⊗[K] L →ₐ[K_v] ∏_{w ∣ v} L_w,    a ⊗ x ↦ (a · x)_w .
```

This file constructs that map, proves that it is surjective, and derives the degree bound
`∑_{w ∣ v} [L_w : K_v] ≤ [L : K]`.

The map is in fact an isomorphism, and equality holds in the degree inequality (Neukirch II
(8.3)). Injectivity is the reverse inequality `∑_{w ∣ v} [L_w : K_v] ≥ [L : K]`, which is not
proved here.

The places above `v` are indexed by the subtype
`{w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}`, which is finite
(`IsDedekindDomain.HeightOneSpectrum.finite_liesOver`) and which
`IsDedekindDomain.HeightOneSpectrum.liesOverEquivPrimesOver` identifies with
`Ideal.primesOver v.asIdeal (𝓞 L)`.

## Main definitions

* `TauCeti.semilocalHom`: the semi-local map
  `K_v ⊗[K] L →ₐ[K_v] ∏_{w ∣ v} L_w`.

## Main results

* `TauCeti.semilocalHom_tmul`: its value on pure tensors,
  `semilocalHom v (a ⊗ₜ x) w = algebraMap K_v L_w a * algebraMap L L_w x`.
* `TauCeti.denseRange_algebraMap_pi_liesOver`: `L` is dense in
  `∏_{w ∣ v} L_w`.
* `TauCeti.semilocalHom_surjective`: the semi-local map is surjective.
* `TauCeti.sum_finrank_adicCompletion_le_finrank`:
  `∑_{w ∣ v} [L_w : K_v] ≤ [L : K]`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, Proposition (8.3).
-/

public section
noncomputable section

open IsDedekindDomain NumberField Module
open scoped TensorProduct NumberField AdicCompletionExtension Valued

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

/-- The semi-local map `K_v ⊗[K] L → ∏_{w ∣ v} L_w` of a finite place `v` of `K`, sending
`a ⊗ x` to the family `(a · x)_w` over the places `w` of `L` above `v`. Each `L_w` is a
`K_v`-algebra through the canonical completion map `completionAlgHom v w`. -/
def semilocalHom :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦ IsScalarTower.toAlgHom K L (w.1.adicCompletion L))
    fun _ _ ↦ .all _ _

variable {L v}

/-- The semi-local map on a pure tensor. -/
@[simp]
theorem semilocalHom_tmul (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    semilocalHom L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a *
        algebraMap L (w.1.adicCompletion L) x := by
  simp [semilocalHom]

variable (L v)

/-- **Weak approximation above `v`.** The diagonal image of `L` is dense in the product of the
completions of `L` at the places above `v`. -/
theorem denseRange_algebraMap_pi_liesOver :
    DenseRange fun (x : L) (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) ↦
      algebraMap L (w.1.adicCompletion L) x := by
  let S := (Set.finite_coe_iff.mp (finite_liesOver (𝒪 L) v)).toFinset
  have hS {w : HeightOneSpectrum (𝒪 L)} : w ∈ S ↔ w.asIdeal.LiesOver v.asIdeal :=
    Set.Finite.mem_toFinset _
  -- Weak approximation is stated for the places of a `Finset`, together with a (here empty)
  -- family of infinite places; reindex its product along `S ↔ {w ∣ v}`.
  let Φ : ((w : {w // w ∈ S}) → w.1.adicCompletion L) ×
      ((u : {u : InfinitePlace L // u ∈ (∅ : Finset (InfinitePlace L))}) → u.1.Completion) →
      (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L :=
    fun p w ↦ p.1 ⟨w.1, hS.mpr w.2⟩
  have hΦc : Continuous Φ :=
    continuous_pi fun w ↦ (continuous_apply _).comp continuous_fst
  have hΦs : Function.Surjective Φ := fun y ↦
    ⟨(fun w ↦ y ⟨w.1, hS.mp w.2⟩, fun u ↦ (Finset.notMem_empty _ u.2).elim), by
      funext w
      change y ⟨w.1, hS.mp (hS.mpr w.2)⟩ = y w
      have hw : (⟨w.1, hS.mp (hS.mpr w.2)⟩ :
          {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) = w :=
        Subtype.ext rfl
      cases hw
      rfl⟩
  exact hΦs.denseRange.comp (TauCeti.GlobalNumberFields.weakApproximation_denseRange S ∅) hΦc

/-- **The semi-local map is surjective**: every family `(y_w)_{w ∣ v}` of elements of the
completions `L_w` is the image of an element of `K_v ⊗[K] L`. -/
theorem semilocalHom_surjective : Function.Surjective (semilocalHom L v) := by
  let s := LinearMap.range (semilocalHom L v).toLinearMap
  have hs : Set.range (fun (x : L) (w : {w : HeightOneSpectrum (𝒪 L) //
      w.asIdeal.LiesOver v.asIdeal}) ↦ algebraMap L (w.1.adicCompletion L) x) ⊆ s := by
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, funext fun w ↦ by simp⟩
  intro y
  exact s.closed_of_finiteDimensional.closure_subset_iff.mpr hs
    (denseRange_algebraMap_pi_liesOver L v y)

attribute [local instance] Fintype.ofFinite in
/-- The local degrees above `v` add up to at most the global degree:
`∑_{w ∣ v} [L_w : K_v] ≤ [L : K]`. -/
theorem sum_finrank_adicCompletion_le_finrank :
    ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        finrank (v.adicCompletion K) (w.1.adicCompletion L) ≤ finrank K L := by
  have h := (semilocalHom L v).toLinearMap.finrank_range_le
  rwa [LinearMap.range_eq_top (f := (semilocalHom L v).toLinearMap).mpr
    (semilocalHom_surjective L v), finrank_top, finrank_pi_fintype, finrank_baseChange] at h

end TauCeti
