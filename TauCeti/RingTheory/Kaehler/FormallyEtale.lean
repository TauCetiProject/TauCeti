/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Kähler differentials along a formally étale extension

For a tower `R → S → T` with `T` formally étale over `S`, Mathlib's
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` identifies `T ⊗[S] Ω[S⁄R]` with
`Ω[T⁄R]`. This file records what that says about bases, and proves a converse.

An `S`-basis of `Ω[S⁄R]` becomes a `T`-basis of `Ω[T⁄R]` on the same index type, each basis
vector going to its image under `KaehlerDifferential.map`. The motivating application is a tower of
fields `k → K → F` with `F/K` separable algebraic, so that `Algebra.FormallyEtale.of_isSeparable`
supplies the hypothesis: the differentials of `F` over `k` are then computed by those of `K`
over `k`.

Conversely, if `T` is formally smooth over `R` and `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective, then `T`
is formally étale over `S`. By the Jacobi–Zariski sequence

`H¹(L_{T/R}) → H¹(L_{T/S}) → T ⊗[S] Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0`,

`Ω[T⁄S]` vanishes when the middle map is surjective, and `H¹(L_{T/S})` vanishes when it is
injective, since `H¹(L_{T/R}) = 0` by formal smoothness. The typical use is with `S` a polynomial
ring over `R`: if the differentials `d aᵢ` of elements `aᵢ` of a formally smooth `R`-algebra `T`
form a basis of `Ω[T⁄R]`, then `T` is formally étale over `R[Xᵢ]` via `Xᵢ ↦ aᵢ`, and étale when `T`
is smooth over `R` (`TauCeti.etale_aeval_of_basis`). Base changing along `R[Xᵢ] → R`, `Xᵢ ↦ 0`,
the common zero locus `T ⧸ (aᵢ)` of such elements is then étale over `R`
(`Module.Basis.etale_quotient_span_range`).

## Main declarations

* `TauCeti.kaehlerBasisOfFormallyEtale`: the induced basis of `Ω[T⁄R]`, with coordinates
  computed by `TauCeti.kaehlerBasisOfFormallyEtale_repr_map` and determinants by
  `TauCeti.kaehlerBasisOfFormallyEtale_det_map`;
* `TauCeti.formallyEtale_of_bijective_mapBaseChange` and
  `TauCeti.formallyEtale_iff_bijective_mapBaseChange`: formal étaleness of `T` over `S` when `T`
  is formally smooth over `R`;
* `TauCeti.bijective_mapBaseChange_of_basis`: `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective when it
  carries a basis to a basis;
* `TauCeti.etale_aeval_of_basis`: a smooth algebra is étale over the polynomial ring on elements
  whose differentials form a basis of its differentials;
* `Module.Basis.etale_quotient_span_range`: the common zero locus of such elements is étale over
  the base.

## References

* The Stacks Project, Tag 00S2, for the Jacobi–Zariski sequence.
-/

public section

noncomputable section

namespace TauCeti

open Module TensorProduct KaehlerDifferential

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

section Basis

variable [Algebra.FormallyEtale S T]

/-- The `T`-basis of `Ω[T⁄R]` induced by an `S`-basis of `Ω[S⁄R]`, when `T` is formally étale
over `S`. Its vectors are the images of the given ones under `KaehlerDifferential.map`, as
recorded in `TauCeti.kaehlerBasisOfFormallyEtale_apply`. -/
def kaehlerBasisOfFormallyEtale {ι : Type*} (b : Basis ι S Ω[S⁄R]) : Basis ι T Ω[T⁄R] :=
  (b.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)

@[simp]
theorem kaehlerBasisOfFormallyEtale_apply {ι : Type*} (b : Basis ι S Ω[S⁄R]) (i : ι) :
    kaehlerBasisOfFormallyEtale R S T b i = KaehlerDifferential.map R R S T (b i) := by
  simp [kaehlerBasisOfFormallyEtale, KaehlerDifferential.mapBaseChange_tmul]

/-- The coordinates of the image of `ω ∈ Ω[S⁄R]` in the induced basis of `Ω[T⁄R]` are the images
of the coordinates of `ω`. -/
@[simp]
theorem kaehlerBasisOfFormallyEtale_repr_map {ι : Type*} (b : Basis ι S Ω[S⁄R]) (ω : Ω[S⁄R])
    (i : ι) :
    (kaehlerBasisOfFormallyEtale R S T b).repr (map R R S T ω) i = algebraMap S T (b.repr ω i) := by
  have : map R R S T ω = tensorKaehlerEquivOfFormallyEtale R S T (1 ⊗ₜ ω) := by
    simp [mapBaseChange_tmul]
  simp [kaehlerBasisOfFormallyEtale, -tensorKaehlerEquivOfFormallyEtale_apply, this,
    Algebra.smul_def]

/-- The determinant, in the induced basis of `Ω[T⁄R]`, of the images of differentials of `S` is
the image of their determinant in the original basis. -/
theorem kaehlerBasisOfFormallyEtale_det_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι S Ω[S⁄R]) (v : ι → Ω[S⁄R]) :
    (kaehlerBasisOfFormallyEtale R S T b).det (fun i ↦ map R R S T (v i)) =
      algebraMap S T (b.det v) := by
  simp only [Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply]

end Basis

variable {R S T}

/-- If `T` is formally smooth over `R` and `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective, then `T` is
formally étale over `S`. -/
theorem formallyEtale_of_bijective_mapBaseChange [Algebra.FormallySmooth R T]
    (h : Function.Bijective (mapBaseChange R S T)) : Algebra.FormallyEtale S T := by
  refine ⟨subsingleton_of_forall_eq 0 fun x ↦ ?_, subsingleton_of_forall_eq 0 fun x ↦ ?_⟩
  · -- `Ω[T⁄R] → Ω[T⁄S]` is onto, and its kernel is the image of `T ⊗[S] Ω[S⁄R]`, which is all.
    obtain ⟨y, rfl⟩ := map_surjective R S T x
    exact (exact_mapBaseChange_map R S T y).mpr (h.2 y)
  · -- `δ` vanishes since `mapBaseChange` is injective, so `x` comes from `H¹(L_{T/R}) = 0`.
    have hδ : Algebra.H1Cotangent.δ R S T x = 0 := (map_eq_zero_iff _ h.1).mp <|
      (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp hδ
    rw [Subsingleton.elim y 0, map_zero]

/-- For `T` formally smooth over `R`, `T` is formally étale over `S` exactly when
`T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective. -/
theorem formallyEtale_iff_bijective_mapBaseChange [Algebra.FormallySmooth R T] :
    Algebra.FormallyEtale S T ↔ Function.Bijective (mapBaseChange R S T) :=
  ⟨fun _ ↦ (tensorKaehlerEquivOfFormallyEtale R S T).bijective,
    formallyEtale_of_bijective_mapBaseChange⟩

/-- The map `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective when it carries the base change of a basis of
`Ω[S⁄R]` to a basis of `Ω[T⁄R]`. -/
theorem bijective_mapBaseChange_of_basis {ι : Type*} (bS : Basis ι S Ω[S⁄R])
    (bT : Basis ι T Ω[T⁄R]) (h : ∀ i, map R R S T (bS i) = bT i) :
    Function.Bijective (mapBaseChange R S T) := by
  have : mapBaseChange R S T = ((bS.baseChange T).equiv bT (Equiv.refl ι)).toLinearMap :=
    (bS.baseChange T).ext fun i ↦ by
      simp only [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply]
      simpa using h i
  rw [this]
  exact LinearEquiv.bijective _

/-- **The Jacobian criterion for étaleness.** If `T` is smooth over `R` and the differentials
`d aᵢ` of finitely many elements `aᵢ` of `T` form a basis of `Ω[T⁄R]`, then `T` is étale over the
polynomial ring `R[Xᵢ]` via `Xᵢ ↦ aᵢ`. -/
theorem etale_aeval_of_basis [Algebra.Smooth R T] {ι : Type*} [Finite ι] (a : ι → T)
    (b : Basis ι T Ω[T⁄R]) (hb : ∀ i, b i = D R T (a i)) :
    (MvPolynomial.aeval (R := R) a).toRingHom.Etale := by
  let := (MvPolynomial.aeval (R := R) a).toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) T := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.FormallyEtale (MvPolynomial ι R) T :=
    formallyEtale_of_bijective_mapBaseChange <|
      bijective_mapBaseChange_of_basis (mvPolynomialBasis R ι) b fun i ↦ by
        rw [mvPolynomialBasis_apply, map_D, hb, RingHom.algebraMap_toAlgebra]
        simp
  have : Algebra.FinitePresentation (MvPolynomial ι R) T :=
    .of_restrict_scalars_finitePresentation R _ _
  exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩

end TauCeti

namespace Module.Basis

open KaehlerDifferential MvPolynomial

/-- **The common zero locus of étale coordinates is étale over the base.** If `W` is smooth over
`A` and the differentials of `x : ι → W` form a basis of `Ω[W⁄A]`, then `W ⧸ (x)` is étale over
`A`. It is the base change of the étale map `A[Xᵢ] → W`, `Xᵢ ↦ xᵢ`
(`TauCeti.etale_aeval_of_basis`), along `A[Xᵢ] → A[Xᵢ] ⧸ (Xᵢ) ≃ A`. -/
theorem etale_quotient_span_range {A W : Type*} [CommRing A] [CommRing W] [Algebra A W]
    [Algebra.Smooth A W] {ι : Type*} [Finite ι] {x : ι → W}
    (b : Basis ι W Ω[W⁄A]) (hb : ∀ i, b i = D A W (x i)) :
    Algebra.Etale A (W ⧸ Ideal.span (Set.range x)) := by
  let R := MvPolynomial ι A
  let _ : Algebra R W := (aeval x).toRingHom.toAlgebra
  have : Algebra.Etale R W := RingHom.etale_algebraMap.mp (TauCeti.etale_aeval_of_basis x b hb)
  have : IsScalarTower A R W := .of_algebraMap_eq fun a ↦ (aeval_C x a).symm
  let J := idealOfVars ι A
  -- `R ⧸ (X) ≃ A` through the constant coefficient.
  let c : R →ₐ[A] A := { constantCoeff with commutes' := constantCoeff_C ι }
  have hc : J = RingHom.ker c := (ker_constantCoeff A ι).symm
  have : Algebra.Etale A (R ⧸ J) := .of_equiv ((Ideal.quotientEquivAlgOfEq A hc).trans
    (Ideal.quotientKerAlgEquivOfRightInverse (f := c) (g := C) (constantCoeff_C ι))).symm
  -- `W ⧸ (X) W` is the base change of `W` along `R → R ⧸ (X)`. This is stated over an arbitrary
  -- base ring, so that the instances on `R ⧸ J` are those of a quotient of a commutative ring.
  have hbase (R : Type _) [CommRing R] [Algebra R W] [Algebra.Etale R W] (J : Ideal R) :
      Algebra.Etale (R ⧸ J) (W ⧸ J.map (algebraMap R W)) :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor W J).symm
  have := hbase R J
  have : IsScalarTower A (R ⧸ J) (W ⧸ J.map (algebraMap R W)) :=
    .of_algebraMap_eq (R := A) (S := R ⧸ J) fun a ↦ by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap,
        IsScalarTower.algebraMap_apply A R W, Ideal.Quotient.algebraMap_quotient_map_quotient]
  have : Algebra.Etale A (W ⧸ J.map (algebraMap R W)) := .comp A (R ⧸ J) _
  -- `(X) W = (x)`.
  refine .of_equiv (Ideal.quotientEquivAlgOfEq A (I := J.map (algebraMap R W)) ?_)
  rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, Ideal.map_coe,
    map_aeval_idealOfVars]

end Module.Basis
