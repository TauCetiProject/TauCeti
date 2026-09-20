/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The semi-local map `K_v ⊗[K] L → ∏_{w ∣ v} L_w`

Let `L/K` be an extension of number fields and `v` a finite place of `K`. Every finite place `w`
of `L` above `v` gives a completion `L_w`, which is a `K_v`-algebra through the canonical
completion map `completionAlgHom v w`. Together these give the semi-local map

```text
semilocalHom v : K_v ⊗[K] L →ₐ[K_v] ∏_{w ∣ v} L_w,    a ⊗ x ↦ (a · x)_w .
```

This file constructs that map and shows that it is an isomorphism `semilocalEquiv v`: the
semi-local decomposition of Neukirch II (8.3). Surjectivity is weak approximation above `v`
together with the closedness of a finite-dimensional subspace. Injectivity is then a count of
degrees, because the source has degree `[L : K]` over `K_v` and the target has degree
`∑_{w ∣ v} [L_w : K_v]`, which is `∑_{w ∣ v} e(w ∣ v) · f(w ∣ v) = [L : K]` by the fundamental
identity. The counterpart at the infinite places is Mathlib's
`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`.

The places above `v` are indexed by the subtype
`{w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}`, which is finite
(`IsDedekindDomain.HeightOneSpectrum.finite_liesOver`) and which
`IsDedekindDomain.HeightOneSpectrum.liesOverEquivPrimesOver` identifies with
`Ideal.primesOver v.asIdeal (𝓞 L)`.

## Main definitions

* `TauCeti.semilocalHom`: the semi-local map
  `K_v ⊗[K] L →ₐ[K_v] ∏_{w ∣ v} L_w`.
* `TauCeti.semilocalEquiv`: that map, as an isomorphism of `K_v`-algebras.

## Main results

* `TauCeti.semilocalHom_tmul` and `TauCeti.semilocalEquiv_tmul`: the value on pure tensors,
  `semilocalEquiv v (a ⊗ₜ x) w = algebraMap K_v L_w a * algebraMap L L_w x`, which determines
  the map.
* `TauCeti.denseRange_algebraMap_pi_liesOver`: `L` is dense in
  `∏_{w ∣ v} L_w`.
* `TauCeti.semilocalHom_surjective` and `TauCeti.semilocalHom_injective`: the semi-local map is
  surjective and injective.
* `TauCeti.sum_finrank_adicCompletion_eq_finrank`:
  `∑_{w ∣ v} [L_w : K_v] = [L : K]`.

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
  let e : {w : HeightOneSpectrum (𝒪 L) // w ∈ S} ≃
      {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Equiv.subtypeEquivRight fun w ↦ hS (w := w)
  -- Weak approximation is stated for the places of a `Finset`, together with a (here empty)
  -- family of infinite places; reindex its product along `S ↔ {w ∣ v}`.
  let Φ : (((w : {w // w ∈ S}) → w.1.adicCompletion L) ×
      ((u : {u : InfinitePlace L // u ∈ (∅ : Finset (InfinitePlace L))}) → u.1.Completion)) ≃ₜ
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L) :=
    (Homeomorph.prodUnique _ _).trans
      (Homeomorph.piCongrLeft
        (Y := fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦
          w.1.adicCompletion L) e)
  exact Φ.surjective.denseRange.comp
    (TauCeti.GlobalNumberFields.weakApproximation_denseRange S ∅) Φ.continuous

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
/-- **The local degrees above `v` add up to the global degree**:
`∑_{w ∣ v} [L_w : K_v] = [L : K]`. Each local degree is `e(w ∣ v) · f(w ∣ v)`, and the sum of
those products over the primes above `v` is the global degree. -/
theorem sum_finrank_adicCompletion_eq_finrank :
    ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        finrank (v.adicCompletion K) (w.1.adicCompletion L) = finrank K L := by
  let _ : Fintype (v.asIdeal.primesOver (𝒪 L)) :=
    Fintype.ofEquiv _ (liesOverEquivPrimesOver (𝒪 L) v)
  calc ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
          finrank (v.adicCompletion K) (w.1.adicCompletion L)
      = ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
          w.1.asIdeal.ramificationIdx (𝒪 K) * w.1.asIdeal.inertiaDeg (𝒪 K) :=
        Finset.sum_congr rfl fun w _ ↦
          have _ : Finite (𝒪 L ⧸ w.1.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.1.ne_bot
          finrank_adicCompletion v w.1
    _ = ∑ Q : v.asIdeal.primesOver (𝒪 L),
          (Q : Ideal (𝒪 L)).ramificationIdx (𝒪 K) * (Q : Ideal (𝒪 L)).inertiaDeg (𝒪 K) :=
        Fintype.sum_equiv (liesOverEquivPrimesOver (𝒪 L) v) _ _ fun w ↦ by
          rw [liesOverEquivPrimesOver_apply]
    _ = finrank (𝒪 K) (𝒪 L) := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝒪 L)
    _ = finrank K L := (IsFractionRing.finrank_eq (𝒪 K) K (𝒪 L) L).symm

attribute [local instance] Fintype.ofFinite in
/-- **The semi-local map is injective.** Its source and target have the same degree over `K_v`,
by `sum_finrank_adicCompletion_eq_finrank`, and it is surjective. -/
theorem semilocalHom_injective : Function.Injective (semilocalHom L v) := by
  have hdim : finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) =
      finrank (v.adicCompletion K)
        ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
          w.1.adicCompletion L) := by
    rw [finrank_pi_fintype, finrank_baseChange, sum_finrank_adicCompletion_eq_finrank]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (semilocalHom L v).toLinearMap)).2 (semilocalHom_surjective L v)

/-- **The semi-local decomposition** `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w`: completing `L` at the
finitely many places above a finite place `v` of `K` decomposes the scalar extension of `L` to
`K_v` into the product of those completions. -/
def semilocalEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (semilocalHom L v)
    -- The `show` is load-bearing. `Function.Bijective` is semireducible, so the bare anonymous
    -- constructor elaborates at the unfolded conjunction instead, and the resulting
    -- `AlgEquiv.ofBijective` term is then not type-correct at `instances` transparency: `simp`
    -- refuses to rewrite it with `AlgEquiv.coe_ofBijective`, which is what proves
    -- `semilocalEquiv_tmul` below.
    (show Function.Bijective (semilocalHom L v) from
      ⟨semilocalHom_injective L v, semilocalHom_surjective L v⟩)

variable {L v}

/-- **The semi-local decomposition on a pure tensor**, the formula that determines it. -/
@[simp]
theorem semilocalEquiv_tmul (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    semilocalEquiv L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a *
        algebraMap L (w.1.adicCompletion L) x := by
  simp [semilocalEquiv]

end TauCeti
