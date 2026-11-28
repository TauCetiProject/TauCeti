/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.FieldTheory.IsAlgClosed.Automorphism
import Mathlib.LinearAlgebra.StdBasis
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Descent for finite-dimensional spaces of functions stable under a coordinatewise action

Let a monoid `G` act on a field `L` through ring homomorphisms, and let `φ : V → (ι → L)` be a
linear map from a finite-dimensional `L`-vector space `V` to the `L`-valued functions on an
arbitrary index set `ι`. Suppose the image is stable under the coordinatewise action: for each
`g : G` and `v : V` the function `i ↦ g • φ v i` is again `φ w` for some `w`. Then `V` has a basis
whose coordinates `φ (b k) i` are all fixed by `G`, so `V` is spanned over `L` by the vectors with
`G`-fixed coordinates. Neither `G` nor `ι` needs to be finite, `φ` need not be injective, and `G`
is not assumed to be a Galois group of any kind.

For an algebraically closed field `Ω` and the automorphism group of `Ω` over a perfect subfield
`K`, the fixed elements are exactly those of `K`
(`TauCeti.IsAlgClosed.mem_range_algebraMap_iff_fixed`). So a finite-dimensional space of
`Ω`-valued functions stable under every automorphism of `Ω` over `K` is spanned by its `K`-valued
members. With `Ω = ℂ`, `ι = ℕ` and `φ` the coefficients of a `q`-expansion, this is the descent
step that turns the stability of a space of modular forms under conjugation of Fourier
coefficients by `Aut(ℂ / K)` into a basis with coefficients in `K`.

## Main results

* `TauCeti.GaloisDescent.exists_basis_forall_smul_apply_eq`: a basis with `G`-fixed coordinates.
* `TauCeti.GaloisDescent.span_setOf_forall_smul_apply_eq_eq_top`: the vectors with `G`-fixed
  coordinates span.
* `TauCeti.GaloisDescent.exists_basis_apply_mem_range_algebraMap` and
  `TauCeti.GaloisDescent.span_setOf_apply_mem_range_algebraMap_eq_top`: the same with
  `K`-valued coordinates, for the automorphisms of an algebraically closed `Ω` over `K`.

## Proof

When `φ` is injective, finitely many coordinates `c k` of `ι` already determine a vector of `V`,
and the map `v ↦ (φ v (c k))ₖ` is a linear isomorphism `V ≃ L^(finrank L V)`
(`Module.Dual.exists_bijective_pi_of_iInf_ker_eq_bot`). The preimages `b k` of the standard
basis vectors form a basis of `V`. The coordinatewise translate of `b k` by `g` is again in `V`
and has the same coordinates `0` and `1` at the `c k'`, so it is `b k` itself. In general, apply
this to the image of `φ`; the kernel of `φ` consists of vectors with coordinates `0`.
-/

public section

open Module

namespace TauCeti.GaloisDescent

variable {ι V : Type*} [AddCommGroup V]

section Monoid

variable {G L : Type*} [Monoid G] [Field L] [MulSemiringAction G L] [Module L V]
  [FiniteDimensional L V]

/-- The injective case of `exists_basis_forall_smul_apply_eq`, through a coordinate basis. -/
private theorem exists_basis_forall_smul_apply_eq_of_injective (φ : V →ₗ[L] ι → L)
    (hφ : Function.Injective φ) (hG : ∀ (g : G) (v : V), ∃ w, φ w = fun i ↦ g • φ v i) :
    ∃ b : Basis (Fin (finrank L V)) L V, ∀ k (g : G) i, g • φ (b k) i = φ (b k) i := by
  -- Finitely many coordinates `c k` of `ι` identify `V` with `L^(finrank L V)`.
  obtain ⟨c, hc⟩ := Dual.exists_bijective_pi_of_iInf_ker_eq_bot
    (fun i ↦ LinearMap.proj i ∘ₗ φ) (by
      refine eq_bot_iff.mpr fun v hv ↦ (Submodule.mem_bot L).mpr (hφ ?_)
      ext i
      simpa using Submodule.mem_iInf _ |>.mp hv i)
  let e := LinearEquiv.ofBijective _ hc
  have he (v : V) (k' : Fin (finrank L V)) : e v k' = φ v (c k') := by simp [e]
  let b := (Pi.basisFun L _).map e.symm
  refine ⟨b, fun k g i ↦ ?_⟩
  obtain ⟨w, hw⟩ := hG g (b k)
  -- The translate `w` of `b k` has the same coordinates `0` and `1` at every `c k'`.
  have hwk : w = b k := e.injective <| funext fun k' ↦ by
    have hb : e (b k) = Pi.single k 1 := by simp [b]
    rw [he, congr_fun hw, ← he, hb, Pi.single_apply]
    split_ifs <;> simp
  rw [← congr_fun hw i, hwk]

/-- **Descent for a coordinatewise action, spanning form.** Let a monoid `G` act on the field `L`
through ring homomorphisms and let `φ : V → (ι → L)` be a linear map from a finite-dimensional
`L`-vector space, with image stable under the coordinatewise action of `G`. Then `V` is spanned by
the vectors whose coordinates are all fixed by `G`. -/
theorem span_setOf_forall_smul_apply_eq_eq_top (φ : V →ₗ[L] ι → L)
    (hG : ∀ (g : G) (v : V), ∃ w, φ w = fun i ↦ g • φ v i) :
    Submodule.span L {v | ∀ (g : G) i, g • φ v i = φ v i} = ⊤ := by
  set S := {v : V | ∀ (g : G) i, g • φ v i = φ v i}
  -- The image of `φ` is a finite-dimensional subspace of `ι → L` with the same stability.
  obtain ⟨b, hb⟩ := exists_basis_forall_smul_apply_eq_of_injective (LinearMap.range φ).subtype
    (Submodule.injective_subtype _) fun (g : G) ⟨_, v, hv⟩ ↦ by
      obtain ⟨w, hw⟩ := hG g v
      exact ⟨⟨φ w, w, rfl⟩, by simpa [← hv] using hw⟩
  -- `S` contains the kernel of `φ` and a preimage of each basis vector of the image.
  have hker : LinearMap.ker φ ≤ Submodule.span L S := fun v hv ↦
    Submodule.subset_span fun g i ↦ by simp [LinearMap.mem_ker.mp hv]
  have hrange : LinearMap.range φ ≤ (Submodule.span L S).map φ := fun x hx ↦ by
    have hmem := Submodule.mem_map_of_mem (f := (LinearMap.range φ).subtype)
      (b.span_eq ▸ Submodule.mem_top : (⟨x, hx⟩ : LinearMap.range φ) ∈ _)
    rw [Submodule.map_span] at hmem
    refine Submodule.span_le.mpr ?_ hmem
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    obtain ⟨v, hv⟩ := (b k).property
    exact ⟨v, Submodule.subset_span fun g i ↦ by simpa [hv] using hb k g i, hv⟩
  refine eq_top_iff.mpr fun v _ ↦ ?_
  obtain ⟨u, hu, huv⟩ := hrange (LinearMap.mem_range_self φ v)
  rw [← sub_add_cancel v u]
  exact add_mem (hker (by simp [huv])) hu

/-- **Descent for a coordinatewise action.** Let a monoid `G` act on the field `L` through ring
homomorphisms and let `φ : V → (ι → L)` be a linear map from a finite-dimensional `L`-vector space
`V`, with image stable under the coordinatewise action of `G`. Then `V` has a basis all of whose
coordinates `φ (b k) i` are fixed by `G`. -/
theorem exists_basis_forall_smul_apply_eq (φ : V →ₗ[L] ι → L)
    (hG : ∀ (g : G) (v : V), ∃ w, φ w = fun i ↦ g • φ v i) :
    ∃ b : Basis (Fin (finrank L V)) L V, ∀ k (g : G) i, g • φ (b k) i = φ (b k) i := by
  let b := Basis.ofSpan (span_setOf_forall_smul_apply_eq_eq_top φ hG).ge
  exact ⟨b.reindex (b.indexEquiv (finBasis L V)), fun k ↦
    Basis.ofSpan_subset _ ⟨_, (b.reindex_apply _ k).symm⟩⟩

end Monoid

section IsAlgClosed

variable {K Ω : Type*} [Field K] [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
  [Module Ω V] [FiniteDimensional Ω V]

/-- **Descent to a subfield of an algebraically closed field.** Let `K` be a perfect field and
`Ω` an algebraically closed extension. Let `φ : V → (ι → Ω)` be a linear map from a
finite-dimensional `Ω`-vector space, with image stable under applying any automorphism of `Ω`
over `K` to every coordinate. Then `V` has a basis whose coordinates `φ (b k) i` all lie in `K`. -/
theorem exists_basis_apply_mem_range_algebraMap (φ : V →ₗ[Ω] ι → Ω)
    (hK : ∀ (τ : Ω ≃ₐ[K] Ω) (v : V), ∃ w, φ w = fun i ↦ τ (φ v i)) :
    ∃ b : Basis (Fin (finrank Ω V)) Ω V, ∀ k i, φ (b k) i ∈ Set.range (algebraMap K Ω) := by
  obtain ⟨b, hb⟩ := exists_basis_forall_smul_apply_eq φ (G := Ω ≃ₐ[K] Ω)
    (by simpa only [AlgEquiv.smul_def] using hK)
  exact ⟨b, fun k i ↦ (IsAlgClosed.mem_range_algebraMap_iff_fixed _).mpr fun τ ↦ by
    simpa only [AlgEquiv.smul_def] using hb k τ i⟩

/-- **Descent to a subfield of an algebraically closed field, spanning form.** Let `K` be a
perfect field and `Ω` an algebraically closed extension. Let `φ : V → (ι → Ω)` be a linear map from
a finite-dimensional `Ω`-vector space, with image stable under applying any automorphism of `Ω`
over `K` to every coordinate. Then `V` is spanned over `Ω` by the vectors whose coordinates all
lie in `K`. -/
theorem span_setOf_apply_mem_range_algebraMap_eq_top (φ : V →ₗ[Ω] ι → Ω)
    (hK : ∀ (τ : Ω ≃ₐ[K] Ω) (v : V), ∃ w, φ w = fun i ↦ τ (φ v i)) :
    Submodule.span Ω {v | ∀ i, φ v i ∈ Set.range (algebraMap K Ω)} = ⊤ :=
  eq_top_iff.mpr <| (span_setOf_forall_smul_apply_eq_eq_top φ (G := Ω ≃ₐ[K] Ω)
    (by simpa only [AlgEquiv.smul_def] using hK)).ge.trans <| Submodule.span_mono fun v hv i ↦
      (IsAlgClosed.mem_range_algebraMap_iff_fixed _).mpr fun τ ↦ by
        simpa only [AlgEquiv.smul_def] using hv τ i

end IsAlgClosed

end TauCeti.GaloisDescent
