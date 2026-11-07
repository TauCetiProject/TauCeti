/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import TauCeti.RingTheory.LocalRing.Hessian
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.Kaehler.FormallyEtale
import TauCeti.RingTheory.Kaehler.Hypersurface
import TauCeti.RingTheory.Kaehler.UnramifiedBase
import TauCeti.RingTheory.Spectrum.Prime.Point
import TauCeti.RingTheory.TensorProduct.ResidueField
import TauCeti.RingTheory.Unramified.Diagonal

/-!
# Functions critical along a section of étale coordinates, and at a nondegenerate point

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

A function with a nondegenerate critical point is critical along such a section. Let `∂ᵢ` be the
partial derivatives dual to a basis `bᵢ` of `Ω[W⁄A]`, and let `f ∈ W` have Hessian determinant
`det (∂ᵢ ∂ⱼ f)` invertible. Then the partial derivatives `yᵢ = ∂ᵢ f` are étale coordinates, as the
matrix of their differentials in the basis `b` is the Hessian; and `df = Σ yᵢ bᵢ ∈ (y) • Ω`. If `f`
is critical at a point `P`, that is `yᵢ ∈ P`, the result above therefore applies along `y`. In two
variables it puts `f`, étale locally around `P`, in the form `h + a s² + b s t + c t²` with
`s = ∂₀ f`, `t = ∂₁ f` and `h ∈ A'`. The discriminant `b² - 4ac` does not vanish at `P'`: modulo
`P'` the Hessian of `f` along `s, t` is the transposed inverse of its Hessian along `b`, and the
Hessian of the quadratic form has determinant `-(b² - 4ac)`
(`TauCeti.algebraMap_residueField_det_hessian_ne_zero_iff`). This is the input shape of
`TauCeti.exists_etale_nodeAlgebra_hom`, up to the sign of `h`; that theorem further asks the
quadratic form to split over `κ(P')`.

## Main results

* `Module.Basis.exists_etale_sub_algebraMap_mem_span_range_sq`: étale locally, a function critical
  along the section of étale coordinates is a function on the base plus an element of `(x) ^ 2`.
* `Module.Basis.exists_basis_D_localizationAway_det_hessian`: after inverting the Hessian
  determinant of `f`, the partial derivatives of `f` are étale coordinates.
* `Module.Basis.exists_etale_eq_algebraMap_add_quadratic`: étale locally around a nondegenerate
  critical point, a function of two coordinates is `h + a s² + b s t + c t²` with `h` from the
  base, `s, t` its partial derivatives, and `b² - 4ac` nonvanishing at the point.

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

section CriticalPoint

open TauCeti

variable {A W : Type*} [CommRing A] [CommRing W] [Algebra A W]

/-- **Partial derivatives with invertible Hessian are étale coordinates.** Let `b` be a basis of
`Ω[W⁄A]`, with dual partial derivatives `∂ᵢ`, and let `f ∈ W`. After inverting the Hessian
determinant `det (∂ᵢ ∂ⱼ f)`, the differentials of the partial derivatives `∂ᵢ f` form a basis of
`Ω`. -/
theorem exists_basis_D_localizationAway_det_hessian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι W Ω[W⁄A]) (f : W) :
    ∃ b' : Basis ι (Localization.Away (hessian (fun i ↦ (b.coord i).compDer (D A W)) f).det)
        Ω[Localization.Away (hessian (fun i ↦ (b.coord i).compDer (D A W)) f).det⁄A],
      ∀ i, b' i = D A _ (algebraMap W _ ((b.coord i).compDer (D A W) f)) := by
  set δ := (hessian (fun i ↦ (b.coord i).compDer (D A W)) f).det
  set b₀ := kaehlerBasisOfFormallyEtale A W (Localization.Away δ) b
  -- In the basis `b`, the matrix of the differentials `d(∂ⱼ f)` is the Hessian of `f`.
  have hdet : b₀.det (fun j ↦ D A _ (algebraMap W _ ((b.coord j).compDer (D A W) f))) =
      algebraMap W (Localization.Away δ) δ := by
    have : b.det (fun j ↦ D A W ((b.coord j).compDer (D A W) f)) = δ := by
      rw [Basis.det_apply]
      congr 1
      ext i j
      simp [Basis.toMatrix_apply]
    rw [← congrArg (algebraMap W _) this, ← kaehlerBasisOfFormallyEtale_det_map]
    simp [b₀]
  obtain ⟨hli, hspan⟩ := b₀.is_basis_iff_det.mpr (hdet ▸ IsLocalization.Away.algebraMap_isUnit δ)
  exact ⟨.mk hli hspan.ge, fun i ↦ by simp⟩

/-- Let `bW` be a basis of `Ω[W⁄A]` with dual partial derivatives `∂ᵢ`, and let `W'` be an
`A'`-algebra over `W` in which the partial derivatives `yᵢ = ∂ᵢ f` of `f ∈ W` become étale
coordinates: the `dyᵢ` form a basis `bW'` of `Ω[W'⁄A']`. If the `yᵢ` lie in a prime `P'`, then
the Hessian of `f` along the coordinates `y` has determinant nonzero in `κ(P')`. Indeed, writing
`Mⱼₖ` for the `dyⱼ`-coordinate of the image of `bₖ`, the matrix `M` inverts the Hessian of `f`
along `bW`, and modulo `P'` the Hessian of `f` along `y` is the transpose of `M`. -/
private theorem algebraMap_residueField_det_hessian_ne_zero {A A' W W' : Type*} [CommRing A]
    [CommRing A'] [CommRing W] [CommRing W'] [Algebra A W] [Algebra A A'] [Algebra W W']
    [Algebra A' W'] [Algebra A W'] [IsScalarTower A W W'] [IsScalarTower A A' W'] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (bW : Basis ι W Ω[W⁄A]) (bW' : Basis ι W' Ω[W'⁄A']) (f : W)
    (hbW' : ∀ i, bW' i = D A' W' (algebraMap W W' ((bW.coord i).compDer (D A W) f)))
    (P' : Ideal W') [P'.IsPrime]
    (hy : ∀ i, algebraMap W W' ((bW.coord i).compDer (D A W) f) ∈ P') :
    algebraMap W' P'.ResidueField
      (hessian (fun i ↦ (bW'.coord i).compDer (D A' W')) (algebraMap W W' f)).det ≠ 0 := by
  set dW : ι → Derivation A W W := fun i ↦ (bW.coord i).compDer (D A W)
  set dW' : ι → Derivation A' W' W' := fun i ↦ (bW'.coord i).compDer (D A' W')
  set y : ι → W' := fun i ↦ algebraMap W W' (dW i f) with hy_def
  have hbW'' (i : ι) : bW' i = D A' W' (y i) := hbW' i
  have hD' (i j : ι) : dW' i (y j) = if i = j then 1 else 0 := by
    simp [dW', ← hbW'', Finsupp.single_apply, eq_comm]
  let M : Matrix ι ι W' := Matrix.of fun j k ↦ bW'.repr (map A A' W W' (bW k)) j
  -- The chain rule `∂'ⱼ w = Σₖ (∂ₖ w) Mⱼₖ`, from `dw = Σₖ (∂ₖ w) bₖ`.
  have hrepr (w : W) (j : ι) :
      dW' j (algebraMap W W' w) = ∑ k, algebraMap W W' (dW k w) * M j k := by
    have : D A' W' (algebraMap W W' w) =
        ∑ k, algebraMap W W' (dW k w) • map A A' W W' (bW k) := by
      rw [← map_D A A' W W', ← bW.sum_repr (D A W w), map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_smul, algebraMap_smul]
      simp [dW]
    simp [dW', this, M, -algebraMap_smul]
  -- Applied to `w = ∂ᵢ f`, the chain rule says that `M` inverts the Hessian of `f` along `bW`.
  have hMH : M * (hessian dW f).map (algebraMap W W') = 1 := by
    ext j i
    rw [Matrix.mul_apply, Matrix.one_apply, ← hD' j i, hy_def, hrepr]
    simp [mul_comm]
  -- Applied to `w = f`, it gives `∂'ⱼ f = Σₖ yₖ Mⱼₖ`, so `∂'ᵢ ∂'ⱼ f ≡ Mⱼᵢ` modulo `P'`.
  let ψ := algebraMap W' P'.ResidueField
  have hψy (i : ι) : ψ (y i) = 0 := Ideal.algebraMap_residueField_eq_zero.mpr (hy i)
  have hhess : (hessian dW' (algebraMap W W' f)).map ψ = M.transpose.map ψ := by
    ext i j
    have : dW' j (algebraMap W W' f) = ∑ k, y k * M j k := hrepr f j
    simp [hessian_apply, this, hD', hψy, apply_ite ψ]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hhess, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, Matrix.det_transpose]
  intro h0
  have := congrArg (fun N ↦ ψ N.det) hMH
  simp only [Matrix.det_mul, map_mul, h0, zero_mul, Matrix.det_one, map_one] at this
  exact zero_ne_one this

/-- **Nondegeneracy of the quadratic part.** In the setting of
`algebraMap_residueField_det_hessian_ne_zero` with two coordinates, suppose that `f` equals
`h + a y₀² + b y₀ y₁ + c y₁²` in `W'` for some `h ∈ A'`, where `yᵢ = ∂ᵢ f`. Then the discriminant
`b² - 4ac` is nonzero in `κ(P')`. Indeed, as `h` is constant along `A'`, the Hessian of `f` along
`y` is that of the quadratic form. -/
private theorem discrim_ne_zero_of_eq_algebraMap_add_quadratic {A A' W W' : Type*} [CommRing A]
    [CommRing A'] [CommRing W] [CommRing W'] [Algebra A W] [Algebra A A'] [Algebra W W']
    [Algebra A' W'] [Algebra A W'] [IsScalarTower A W W'] [IsScalarTower A A' W']
    (bW : Basis (Fin 2) W Ω[W⁄A]) (bW' : Basis (Fin 2) W' Ω[W'⁄A']) (f : W)
    (hbW' : ∀ i, bW' i = D A' W' (algebraMap W W' ((bW.coord i).compDer (D A W) f)))
    (P' : Ideal W') [P'.IsPrime]
    (hy : ∀ i, algebraMap W W' ((bW.coord i).compDer (D A W) f) ∈ P') (h : A') (a b c : W')
    (hfQ : algebraMap W W' f = algebraMap A' W' h +
      (a * algebraMap W W' ((bW.coord 0).compDer (D A W) f) ^ 2 +
        b * algebraMap W W' ((bW.coord 0).compDer (D A W) f) *
          algebraMap W W' ((bW.coord 1).compDer (D A W) f) +
        c * algebraMap W W' ((bW.coord 1).compDer (D A W) f) ^ 2)) :
    algebraMap W' P'.ResidueField (discrim a b c) ≠ 0 := by
  set y : Fin 2 → W' := fun i ↦ algebraMap W W' ((bW.coord i).compDer (D A W) f)
  set dW' : Fin 2 → Derivation A' W' W' := fun i ↦ (bW'.coord i).compDer (D A' W') with hdW'
  have hQ : hessian dW' (algebraMap W W' f) =
      hessian dW' (a * y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2) := by
    -- `hfQ` is stated with the unfolded coordinates; `rw [hfQ]` alone leaves the right-hand side
    -- unfolded and no longer syntactically matching `y`, so restate it in terms of `y` (defeq).
    rw [show algebraMap W W' f = algebraMap A' W' h +
      (a * y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2) from hfQ]
    ext i j
    simp only [hessian_apply, map_add, Derivation.map_algebraMap, zero_add]
  have hbW'' (i : Fin 2) : bW' i = D A' W' (y i) := hbW' i
  have hD' (i j : Fin 2) : dW' i (y j) = if i = j then 1 else 0 := by
    simp [dW', ← hbW'', Finsupp.single_apply, eq_comm]
  have hdet' := algebraMap_residueField_det_hessian_ne_zero bW bW' f hbW' P' hy
  rw [← hdW', hQ] at hdet'
  exact (algebraMap_residueField_det_hessian_ne_zero_iff hy hD' a b c).mp hdet'

/-- **Second-order normal form at a nondegenerate critical point.** Let `W` be a smooth
`A`-algebra, `bW` a basis of `Ω[W⁄A]` with dual partial derivatives `∂₀, ∂₁`, and `P` a prime of
`W`. Let `f ∈ W` be critical at `P`, in the sense that `∂₀ f, ∂₁ f ∈ P`, with Hessian determinant
`det (∂ᵢ ∂ⱼ f)` not in `P`. Then there are an étale `A`-algebra `A'`, an étale `W`-algebra `W'`
which is a smooth `A'`-algebra, a prime `P'` of `W'` above `P` with the same residue field,
`h ∈ A'` and `a, b, c ∈ W'` with the following properties: the partial derivatives
`s = ∂₀ f, t = ∂₁ f` are étale coordinates of `W'` over `A'` (their differentials form a basis of
`Ω[W'⁄A']`), `f = h + a s² + b s t + c t²` in `W'`, and the discriminant `b² - 4ac` does not
vanish at `P'`. -/
theorem exists_etale_eq_algebraMap_add_quadratic {A W : Type u} [CommRing A] [CommRing W]
    [Algebra A W] [Algebra.Smooth A W] (bW : Basis (Fin 2) W Ω[W⁄A]) (f : W) (P : Ideal W)
    [P.IsPrime] (hf : ∀ i, (bW.coord i).compDer (D A W) f ∈ P)
    (hdet : (hessian (fun i ↦ (bW.coord i).compDer (D A W)) f).det ∉ P) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (W' : Type u) (_ : CommRing W') (_ : Algebra W W') (_ : Algebra.Etale W W')
      (_ : Algebra A' W') (_ : Algebra A W') (_ : IsScalarTower A W W')
      (_ : IsScalarTower A A' W') (_ : Algebra.Smooth A' W') (bW' : Basis (Fin 2) W' Ω[W'⁄A'])
      (P' : Ideal W') (_ : P'.IsPrime) (hP' : P = P'.comap (algebraMap W W')) (h : A')
      (a b c : W'),
      (∀ i, bW' i = D A' W' (algebraMap W W' ((bW.coord i).compDer (D A W) f))) ∧
      Function.Bijective (Ideal.ResidueField.map P P' (algebraMap W W') hP') ∧
      algebraMap W W' f = algebraMap A' W' h +
        (a * algebraMap W W' ((bW.coord 0).compDer (D A W) f) ^ 2 +
          b * algebraMap W W' ((bW.coord 0).compDer (D A W) f) *
            algebraMap W W' ((bW.coord 1).compDer (D A W) f) +
          c * algebraMap W W' ((bW.coord 1).compDer (D A W) f) ^ 2) ∧
      algebraMap W' P'.ResidueField (discrim a b c) ≠ 0 := by
  set dW : Fin 2 → Derivation A W W := fun i ↦ (bW.coord i).compDer (D A W)
  set δ := (hessian dW f).det
  obtain ⟨b₀, hb₀⟩ := bW.exists_basis_D_localizationAway_det_hessian f
  let W₀ := Localization.Away δ
  have : Algebra.Smooth A W₀ := .comp A W W₀
  -- The point `P₀` of `W₀ = W[1/δ]` above `P`.
  let ψ₀ : W₀ →ₐ[W] P.ResidueField := IsLocalization.Away.liftAlgHom δ
    (f := IsScalarTower.toAlgHom W W P.ResidueField)
    (by simpa [Ideal.algebraMap_residueField_eq_zero] using hdet)
  have hψ₀ (w : W) : ψ₀ (algebraMap W W₀ w) = algebraMap W P.ResidueField w := ψ₀.commutes w
  have hy (i : Fin 2) : algebraMap W W₀ (dW i f) ∈ RingHom.ker ψ₀ := by
    rw [RingHom.mem_ker, hψ₀, Ideal.algebraMap_residueField_eq_zero]
    exact hf i
  -- `f` is critical along the section of the coordinates `∂ᵢ f`, since `df = Σ (∂ᵢ f) bᵢ`.
  have hcrit : D A W₀ (algebraMap W W₀ f) ∈
      Ideal.span (Set.range fun i ↦ algebraMap W W₀ (dW i f)) • (⊤ : Submodule W₀ Ω[W₀⁄A]) := by
    rw [← map_D A A W W₀, ← bW.sum_repr (D A W f), map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul, ← algebraMap_smul W₀]
    exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, by simp [dW]⟩) trivial
  have := RingHom.ker_isPrime ψ₀
  obtain ⟨A', _, _, _, W', _, _, _, _, _, _, _, _, bW', P', _, hP'₀, h, hbW', hκ, hmem⟩ :=
    b₀.exists_etale_sub_algebraMap_mem_span_range_sq hb₀ (RingHom.ker ψ₀) hy hcrit
  let : Algebra W W' := ((algebraMap W₀ W').comp (algebraMap W W₀)).toAlgebra
  have : IsScalarTower W W₀ W' := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale W W' := .comp W W₀ W'
  have : IsScalarTower A W W' := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply A W₀ W', IsScalarTower.algebraMap_apply A W W₀,
      IsScalarTower.algebraMap_apply W W₀ W']
  have hP' : P = P'.comap (algebraMap W W') := by
    rw [IsScalarTower.algebraMap_eq W W₀ W', ← Ideal.comap_comap, ← hP'₀]
    exact ψ₀.comap_ker_eq_of_residueField.symm
  -- The new coordinates `y = (∂₀ f, ∂₁ f)` and the quadratic form `f - h ∈ (y) ^ 2`.
  set y : Fin 2 → W' := fun i ↦ algebraMap W W' (dW i f)
  have hyP' (i : Fin 2) : y i ∈ P' := by
    have := hy i
    rwa [hP'₀] at this
  have hbW'' (i : Fin 2) : bW' i = D A' W' (y i) := hbW' i
  obtain ⟨a, b, c, habc⟩ := (Ideal.mem_span_range_fin_two_sq_iff y).mp hmem
  have hfQ : algebraMap W W' f = algebraMap A' W' h + (a * y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2) :=
    sub_eq_iff_eq_add'.mp habc
  refine ⟨A', inferInstance, inferInstance, inferInstance, W', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, bW',
    P', inferInstance, hP', h, a, b, c, hbW'', ?_, hfQ, ?_⟩
  · -- The residue fields `κ(P) → κ(P₀) → κ(P')` are preserved at each step.
    have := Ideal.ResidueField.map_comp_map P (RingHom.ker ψ₀) P' _ _
      ψ₀.comap_ker_eq_of_residueField.symm hP'₀
    exact this ▸ hκ.comp ψ₀.residueFieldMap_bijective
  exact discrim_ne_zero_of_eq_algebraMap_add_quadratic bW bW' f hbW'' P' hyP' h a b c hfQ

end CriticalPoint

end Module.Basis
