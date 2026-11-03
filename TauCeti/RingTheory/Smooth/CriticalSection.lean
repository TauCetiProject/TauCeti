/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Kaehler.FormallyEtale
import TauCeti.RingTheory.Kaehler.Hypersurface
import TauCeti.RingTheory.Kaehler.UnramifiedBase
import TauCeti.RingTheory.Spectrum.Prime.Point
import TauCeti.RingTheory.TensorProduct.ResidueField
import TauCeti.RingTheory.Unramified.Diagonal

/-!
# Functions critical along a section of étale coordinates

Let `W` be a smooth `A`-algebra and `x : ι → W` étale coordinates: finitely many elements whose
differentials form a basis of `Ω[W⁄A]`. Their common zero locus `W ⧸ (x)` is étale over `A`, as
the base change of the étale map `A[Xᵢ] → W`, `Xᵢ ↦ xᵢ`, along `Xᵢ ↦ 0`
(`Module.Basis.etale_quotient_span_range`).

Let `f ∈ W` be critical along this section, in the sense that `df ∈ (x) • Ω[W⁄A]`. Then, étale
locally on the base and on `W` around any point `P` of the section, `f` is a function on the base
plus an element of `(x) ^ 2`: there are an étale `A`-algebra `A'`, an étale `W`-algebra `W'` over
`A'` in which `x` are again étale coordinates, a prime `P'` above `P` with the same residue field,
and `h ∈ A'` with `f - h ∈ (x) ^ 2` in `W'`. With two coordinates `p, q` this says
`f = h + a p² + b p q + c q²` with `a, b, c ∈ W'`. This is the second-order normal form of the
equation of a plane curve near a point where its partial derivatives cut out the section. Up to
sign it is the shape `a p² + b p q + c q² - h` from which `TauCeti.exists_etale_nodeAlgebra_hom`
builds étale charts of a node, when the quadratic part is nondegenerate and split at `P`.

One may take `A' = W ⧸ (x)`. As it is unramified over `A`, the diagonal of
`Spec A' ×_A Spec A'` is the locus where some `t ∈ A' ⊗[A] A'` is invertible, with
`t (1 ⊗ s - s ⊗ 1) = 0` for all `s` and `s₁ ⊗ s₂ ↦ s₁ s₂` sending `t` to `1`
(`Algebra.FormallyUnramified.iff_exists_tensorProduct`). Let `W'` be `A' ⊗[A] W` with a lift of
`t` inverted. There the two images of `f` in the section agree, so `f - h ∈ (x)` for
`h = f mod (x) ∈ A'`. As `d(f - h) = df ∈ (x) • Ω`, this forces
`f - h ∈ (x) ^ 2` (`Module.Basis.mem_span_range_sq_of_D_mem`).

## Main results

* `Module.Basis.exists_etale_sub_algebraMap_mem_span_range_sq`: étale locally, a function critical
  along the section of étale coordinates is a function on the base plus an element of `(x) ^ 2`.

## References

* B. Iversen, *Generic local structure of the morphisms in commutative algebra*, Lecture Notes in
  Mathematics 310, Propositions I.2.3 and I.2.6, for the diagonal of an unramified algebra, as in
  Mathlib's `Algebra.FormallyUnramified.iff_exists_tensorProduct`.
* [Stacks Project, Section 53.20, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): families
  of nodal curves and their étale local structure.
-/

public section

noncomputable section

open KaehlerDifferential TensorProduct

universe u

namespace Module.Basis

open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Étale locally, a function critical along a section of étale coordinates is a function on
the base up to second order.** Let `W` be a smooth `A`-algebra, `x : ι → W` elements whose
differentials form a basis of `Ω[W⁄A]`, all lying in a prime `P`, and `f ∈ W` with
`df ∈ (x) • Ω[W⁄A]`. Then there are an étale `A`-algebra `A'`, an étale `W`-algebra `W'` which is
a smooth `A'`-algebra in which the images of `x` are again étale coordinates, a prime `P'` of `W'`
above `P` with the same residue field, and `h ∈ A'` such that `f - h ∈ (x) ^ 2` in `W'`. -/
theorem exists_etale_sub_algebraMap_mem_span_range_sq {A W : Type u} [CommRing A] [CommRing W]
    [Algebra A W] [Algebra.Smooth A W] {ι : Type*} [Finite ι] {x : ι → W}
    (b : Module.Basis ι W Ω[W⁄A]) (hb : ∀ i, b i = D A W (x i))
    (P : Ideal W) [P.IsPrime] (hx : ∀ i, x i ∈ P) {f : W}
    (hf : D A W f ∈ Ideal.span (Set.range x) • (⊤ : Submodule W Ω[W⁄A])) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (W' : Type u) (_ : CommRing W') (_ : Algebra W W') (_ : Algebra.Etale W W')
      (_ : Algebra A' W') (_ : Algebra A W') (_ : IsScalarTower A W W')
      (_ : IsScalarTower A A' W') (_ : Algebra.Smooth A' W') (b' : Module.Basis ι W' Ω[W'⁄A'])
      (P' : Ideal W') (_ : P'.IsPrime) (hP' : P = P'.comap (algebraMap W W')) (h : A'),
      (∀ i, b' i = D A' W' (algebraMap W W' (x i))) ∧
      Function.Bijective (Ideal.ResidueField.map P P' (algebraMap W W') hP') ∧
      algebraMap W W' f - algebraMap A' W' h ∈
        Ideal.span (Set.range (algebraMap W W' ∘ x)) ^ 2 := by
  set I := Ideal.span (Set.range x)
  have hIP : I ≤ P := Ideal.span_le.mpr (Set.range_subset_iff.mpr hx)
  let S := W ⧸ I
  have : Algebra.Etale A S := b.etale_quotient_span_range hb
  let T := S ⊗[A] W
  obtain ⟨t, ht₁, ht⟩ :=
    TauCeti.Algebra.FormallyUnramified.exists_mul_tmul_sub_mem_map_includeRight A I
  obtain ⟨ψ₀, hψ₀⟩ := Ideal.ResidueField.exists_algHom_tensorProduct_eq_lmul' A I P hIP
  have hψ₀t : IsUnit (ψ₀ t) := by
    rw [hψ₀, ht₁, map_one]
    exact isUnit_one
  -- Invert `t` and take the point `P'` of `W' = T[1/t]` given by `ψ₀`.
  let W' := Localization.Away t
  let ψ : W' →ₐ[W] P.ResidueField := IsLocalization.Away.liftAlgHom t (f := ψ₀) hψ₀t
  let P' := RingHom.ker ψ
  have : Algebra.Etale W T := .of_equiv (Algebra.IsPushout.equiv A W S T)
  have : Algebra.Etale W W' := .comp W T W'
  have : Algebra.Smooth S W' := .comp S T W'
  -- The basis `dx` of `Ω[W⁄A]` gives one of `Ω[W'⁄A]`, which is `Ω[W'⁄S]` as `S` is étale over `A`.
  let b' := (TauCeti.kaehlerBasisOfFormallyEtale A W W' b).map
    (equivOfFormallyUnramifiedBase A S W')
  have hb' (i : ι) : b' i = D S W' (algebraMap W W' (x i)) := by
    simp [b', hb, equivOfFormallyUnramifiedBase_apply]
  have hrepr (w : W) (i : ι) :
      b'.repr (D S W' (algebraMap W W' w)) i = algebraMap W W' (b.repr (D A W w) i) := by
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply, equivOfFormallyUnramifiedBase_symm_D,
      ← map_D A A W W', TauCeti.kaehlerBasisOfFormallyEtale_repr_map]
  -- `t (1 ⊗ f - h ⊗ 1) ∈ (x) T` for `h = f mod (x)`, so `f - h ∈ (x) W'` after inverting `t`.
  let h : S := Ideal.Quotient.mk I f
  set J := Ideal.span (Set.range (algebraMap W W' ∘ x))
  have hJ : I.map (algebraMap W W') = J := by rw [Ideal.map_span, ← Set.range_comp]
  have hfh : algebraMap W W' f - algebraMap S W' h ∈ J := by
    have := Ideal.mem_map_of_mem (algebraMap T W') (ht f)
    rw [← Ideal.map_coe (f := (includeRight : W →ₐ[A] T)), ← algebraMap_eq_includeRight,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq, hJ, map_mul,
      Ideal.mul_unit_mem_iff_mem _ (IsLocalization.Away.algebraMap_isUnit t), map_sub] at this
    have h₁ : algebraMap T W' (1 ⊗ₜ f) = algebraMap W W' f := by
      rw [IsScalarTower.algebraMap_apply W T W', right_algebraMap_apply]
    have h₂ : algebraMap T W' (h ⊗ₜ 1) = algebraMap S W' h := by
      rw [IsScalarTower.algebraMap_apply S T W', Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
    rwa [h₁, h₂] at this
  -- `d(f - h) = df` lies in `(x) • Ω[W'⁄S]`, so `f - h ∈ (x) ^ 2`.
  have hD : D S W' (algebraMap W W' f - algebraMap S W' h) ∈ J • (⊤ : Submodule W' Ω[W'⁄S]) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero, b'.mem_smul_top_iff]
    intro i
    rw [hrepr, ← hJ]
    exact Ideal.mem_map_of_mem _ (b.mem_smul_top_iff.mp hf i)
  exact ⟨S, inferInstance, inferInstance, inferInstance, W', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, b',
    P', RingHom.ker_isPrime _, ψ.comap_ker_eq_of_residueField.symm, h, hb',
    ψ.residueFieldMap_bijective, b'.mem_span_range_sq_of_D_mem hb' hfh hD⟩

end Module.Basis
