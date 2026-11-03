/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Unramified.Finite
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Kaehler.FormallyEtale
import TauCeti.RingTheory.Kaehler.Hypersurface
import TauCeti.RingTheory.Kaehler.UnramifiedBase
import TauCeti.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.Spectrum.Prime.Point

/-!
# Functions critical along a section of étale coordinates

Let `W` be a smooth `A`-algebra and `x : ι → W` étale coordinates: finitely many elements whose
differentials form a basis of `Ω[W⁄A]`. Their common zero locus `W ⧸ (x)` is étale over `A`, as
the base change of the étale map `A[Xᵢ] → W`, `Xᵢ ↦ xᵢ`, along `Xᵢ ↦ 0`.

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
`f - h ∈ (x) ^ 2` (`TauCeti.mem_span_range_sq_of_D_mem`).

## Main results

* `TauCeti.etale_quotient_span_range_of_basis`: the common zero locus of étale coordinates of a
  smooth algebra is étale over the base.
* `TauCeti.exists_etale_sub_algebraMap_mem_span_range_sq`: étale locally, a function critical
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

open KaehlerDifferential MvPolynomial TensorProduct

namespace TauCeti

section

variable {A W : Type*} [CommRing A] [CommRing W] [Algebra A W]

/-- **The common zero locus of étale coordinates is étale over the base.** If `W` is smooth over
`A` and the differentials of `x : ι → W` form a basis of `Ω[W⁄A]`, then `W ⧸ (x)` is étale over
`A`. It is the base change of the étale map `A[Xᵢ] → W`, `Xᵢ ↦ xᵢ`, along `A[Xᵢ] → A`,
`Xᵢ ↦ 0`. -/
theorem etale_quotient_span_range_of_basis [Algebra.Smooth A W] {ι : Type*} [Finite ι] {x : ι → W}
    (b : Module.Basis ι W Ω[W⁄A]) (hb : ∀ i, b i = D A W (x i)) :
    Algebra.Etale A (W ⧸ Ideal.span (Set.range x)) := by
  set I := Ideal.span (Set.range x)
  let R := MvPolynomial ι A
  let _ : Algebra R W := (aeval x).toRingHom.toAlgebra
  have : Algebra.Etale R W := RingHom.etale_algebraMap.mp (etale_aeval_of_basis x b hb)
  let _ : Algebra R A := (constantCoeff : R →+* A).toAlgebra
  -- `A ⊗[R] W` is the base change of `W` along `R → R ⧸ (X) = A`, that is, `W ⧸ (x)`.
  have hR (r : R) : Ideal.Quotient.mk I (aeval x r) =
      Ideal.Quotient.mk I (algebraMap A W (constantCoeff r)) := by
    rw [Ideal.Quotient.eq, ← aeval_C (R := A) x, ← map_sub]
    have : r - C (constantCoeff r) ∈ idealOfVars ι A := by
      rw [← ker_constantCoeff, RingHom.mem_ker]; simp
    have := Ideal.mem_map_of_mem (aeval x : R →ₐ[A] W) this
    rw [Ideal.map_span, ← Set.range_comp] at this
    convert this using 4
    ext i; simp
  have : IsScalarTower R A (W ⧸ I) := .of_algebraMap_eq fun r ↦ by
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
    exact hR r
  let f : A ⊗[R] W →ₐ[A] W ⧸ I :=
    Algebra.TensorProduct.lift (Algebra.ofId A (W ⧸ I)) (Ideal.Quotient.mkₐ R I)
      fun _ _ ↦ .all _ _
  let g₀ : W →ₐ[A] A ⊗[R] W :=
    { (Algebra.TensorProduct.includeRight : W →ₐ[R] A ⊗[R] W) with
      commutes' a := by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_ofClass, Algebra.TensorProduct.algebraMap_apply]
        have h₁ : algebraMap A W a = (C a : R) • (1 : W) := by
          rw [Algebra.smul_def, mul_one]; exact (aeval_C x a).symm
        have h₂ : (C a : R) • (1 : A) = a := by
          rw [Algebra.smul_def, mul_one]; exact constantCoeff_C ι a
        rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          Algebra.TensorProduct.includeRight_apply, h₁, ← TensorProduct.smul_tmul, h₂,
          Algebra.algebraMap_self, RingHom.id_apply] }
  have hg₀w (w : W) : g₀ w = 1 ⊗ₜ w := rfl
  have hg₀ : I ≤ RingHom.ker g₀ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have h₁ : x i = (X i : R) • (1 : W) := by
      rw [Algebra.smul_def, mul_one]; exact (aeval_X x i).symm
    have h₂ : (X i : R) • (1 : A) = 0 := by
      rw [Algebra.smul_def, mul_one]; exact constantCoeff_X A i
    rw [SetLike.mem_coe, RingHom.mem_ker, hg₀w, h₁, ← TensorProduct.smul_tmul, h₂,
      TensorProduct.zero_tmul]
  let g : W ⧸ I →ₐ[A] A ⊗[R] W := Ideal.Quotient.liftₐ I g₀ hg₀
  have hg (w : W) : g (Ideal.Quotient.mk I w) = 1 ⊗ₜ w := rfl
  let e : A ⊗[R] W ≃ₐ[A] W ⧸ I := AlgEquiv.ofAlgHom f g (by
    refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun w ↦ ?_)
    simp [f, hg]) (by
    ext w
    simp [f, hg])
  exact Algebra.Etale.of_equiv e

end

universe u

open Algebra.TensorProduct

section Diagonal

variable {A W : Type*} [CommRing A] [CommRing W] [Algebra A W] (I : Ideal W)

/-- For a quotient `S = W ⧸ I` unramified over `A`, some `t ∈ S ⊗[A] W` maps to `1` on the
diagonal and makes the two images `1 ⊗ w` and `(w mod I) ⊗ 1` of every `w ∈ W` congruent modulo
`I`. -/
private theorem exists_mul_tmul_sub_mem_map_includeRight
    [Algebra.FormallyUnramified A (W ⧸ I)] [Algebra.EssFiniteType A (W ⧸ I)] :
    ∃ t : (W ⧸ I) ⊗[A] W,
      lmul' A (map (AlgHom.id A (W ⧸ I)) (Ideal.Quotient.mkₐ A I) t) = 1 ∧
      ∀ w : W, ((1 : W ⧸ I) ⊗ₜ[A] w - Ideal.Quotient.mk I w ⊗ₜ[A] (1 : W)) * t ∈
        I.map (includeRight : W →ₐ[A] (W ⧸ I) ⊗[A] W) := by
  obtain ⟨t, ht, ht₁⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.mp
    (inferInstance : Algebra.FormallyUnramified A (W ⧸ I))
  obtain ⟨t, rfl⟩ := Algebra.TensorProduct.map_surjective (f := AlgHom.id A (W ⧸ I))
    (g := Ideal.Quotient.mkₐ A I) Function.surjective_id Ideal.Quotient.mk_surjective t
  refine ⟨t, ht₁, fun w ↦ ?_⟩
  -- The kernel of `W ⧸ I ⊗[A] W → W ⧸ I ⊗[A] W ⧸ I` is generated by `I`.
  have hker := Algebra.TensorProduct.lTensor_ker (A := W ⧸ I) (Ideal.Quotient.mkₐ A I)
    Ideal.Quotient.mk_surjective
  have hI : RingHom.ker (Ideal.Quotient.mkₐ A I) = I := Ideal.Quotient.mkₐ_ker A I
  rw [hI] at hker
  rw [← hker, RingHom.mem_ker, map_mul, map_sub, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul]
  simpa using ht (Ideal.Quotient.mk I w)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The diagonal point of `(W ⧸ I) ⊗[A] W` over a prime `P ⊇ I`: the `W`-algebra map to `κ(P)`
sending `s ⊗ w` to `s(P) w(P)`. It factors through multiplication on `(W ⧸ I) ⊗[A] (W ⧸ I)`. -/
private theorem exists_algHom_residueField_eq_lmul' (P : Ideal W) [P.IsPrime] (hIP : I ≤ P) :
    ∃ ψ : (W ⧸ I) ⊗[A] W →ₐ[W] P.ResidueField, ∀ z,
      ψ z = Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom A W P.ResidueField)
        (fun _ hw ↦ Ideal.algebraMap_residueField_eq_zero.mpr (hIP hw))
        (lmul' A (map (AlgHom.id A (W ⧸ I)) (Ideal.Quotient.mkₐ A I) z)) := by
  let φW : W →ₐ[A] P.ResidueField := IsScalarTower.toAlgHom A W P.ResidueField
  let φS : W ⧸ I →ₐ[A] P.ResidueField := Ideal.Quotient.liftₐ I φW fun _ hw ↦
    Ideal.algebraMap_residueField_eq_zero.mpr (hIP hw)
  refine ⟨{ productMap φS φW with
    commutes' w := (productMap_apply_tmul φS φW 1 w).trans (by rw [map_one, one_mul]; rfl) },
    fun z ↦ ?_⟩
  induction z using TensorProduct.inductionOn with
  | tmul s w =>
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [Algebra.TensorProduct.map_tmul, lmul'_apply_tmul, map_mul]
    exact productMap_apply_tmul φS φW _ w
  | add z z' hz hz' => simp only [map_add, hz, hz']

end Diagonal

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
  have : Algebra.Etale A S := etale_quotient_span_range_of_basis b hb
  let T := S ⊗[A] W
  obtain ⟨t, ht₁, ht⟩ := exists_mul_tmul_sub_mem_map_includeRight (A := A) I
  obtain ⟨ψ₀, hψ₀⟩ := exists_algHom_residueField_eq_lmul' (A := A) I P hIP
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
  let b' := (kaehlerBasisOfFormallyEtale A W W' b).map (equivOfFormallyUnramifiedBase A S W')
  have hb' (i : ι) : b' i = D S W' (algebraMap W W' (x i)) := by
    simp [b', hb, equivOfFormallyUnramifiedBase_apply]
  have hrepr (w : W) (i : ι) :
      b'.repr (D S W' (algebraMap W W' w)) i = algebraMap W W' (b.repr (D A W w) i) := by
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply, equivOfFormallyUnramifiedBase_symm_D,
      ← map_D A A W W', kaehlerBasisOfFormallyEtale_repr_map]
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
    ψ.residueFieldMap_bijective, mem_span_range_sq_of_D_mem b' hb' hfh hD⟩

end TauCeti
