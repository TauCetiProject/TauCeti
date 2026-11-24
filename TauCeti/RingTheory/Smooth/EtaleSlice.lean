/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import TauCeti.LinearAlgebra.SymmetricAlgebra.Kaehler
import TauCeti.LinearAlgebra.SymmetricAlgebra.Smooth
import TauCeti.RingTheory.Kaehler.BaseChange
import TauCeti.RingTheory.Kaehler.FormallyEtale

/-!
# Factoring closed-fibre points of smooth algebras through étale slices

Let `R → T` be a surjective commutative algebra map (typically `T = R ⧸ I`) and let `A` be a smooth
`R`-algebra together with an `R`-algebra map `ψ : A →ₐ[R] T`. Even when `Spec T` is disconnected or
`Ω[A⁄R]` does not have constant rank along `Spec T`, `ψ` factors through an étale `R`-algebra `C`:
there exist an étale `R`-algebra `C` (either in the universe of `A` or in the universe of `R`), an
`R`-algebra map `f : A →ₐ[R] C`, and an `R`-algebra map `ψC : C →ₐ[R] T` with `ψC ∘ f = ψ`
(`Algebra.Smooth.exists_etale_algHom_comp_eq`).

Geometrically, a smooth morphism `Spec A → Spec R` equipped with a section over a closed subscheme
`Spec T ↪ Spec R` admits an étale `R`-scheme ("étale slice") mapping to `Spec A` through which that
closed-fibre section factors. No Henselian or Noetherian hypothesis on `R` is required; when
`(R, I)` is a Henselian pair, lifting the induced `T`-point of the étale slice `C` immediately
yields Elkik's smooth lifting theorem (`TauCeti.HenselianRing.comp_surjective`).

The construction has two steps, following Stacks Project Lemma 15.13.3 (Tag 0H74):
1. **Free-cotangent retract** (`Algebra.Smooth.exists_retract_basis_kaehlerDifferential`): because
   `Ω[A⁄R]` is finitely generated projective over `A`, there is a split surjection
   `(Fin n → A) →ₗ[A] Ω[A⁄R]` with finite projective kernel `K`. Passing to
   `B := SymmetricAlgebra A K` makes `A` an `R`-algebra retract of a smooth `R`-algebra `B` whose
   Jacobi–Zariski sequence splits globally, giving a global `B`-basis of `Ω[B⁄R]` of rank `n`.
2. **Transverse coordinates along `ker ψ`**
   (`Module.Basis.exists_ker_and_det_D_eq_one_of_surjective` and
   `Module.Basis.exists_etale_quotient_localizationAway`): expanding each basis vector of `Ω[B⁄R]`
   as `∑ c_j • d y_j` and shifting each `y_j` by an `R`-lift of `ψ(y_j)` produces elements
   `x : Fin n → B` in `ker ψ` whose Jacobian matrix in the basis reduces under `ψ` to the identity
   matrix over `T`. Inverting the Jacobian determinant `d` and quotienting `B[1/d]` by `(x₁, …, xₙ)`
   cuts out an étale `R`-algebra (`Module.Basis.etale_quotient_span_range`) through which `ψ`
   factors.

## Main results

* `Module.Basis.exists_ker_and_det_D_eq_one_of_surjective`: given a finite basis `b` of `Ω[B⁄R]` and
  `ψ : B →ₐ[R] T` with `algebraMap R T` surjective, there are `x : ι → B` in `ker ψ` whose
  differentials have Jacobian matrix congruent to `1` under `ψ` (in particular `ψ(det(d x)) = 1`).
* `Module.Basis.exists_etale_quotient_localizationAway`: when `B` is smooth over `R` with free
  differentials indexed by `ι`, `ψ` factors through an explicit étale quotient `B[1/d] ⧸ (xᵢ)`.
* `Algebra.Smooth.exists_retract_basis_kaehlerDifferential`: every smooth `R`-algebra `A` is an
  `R`-algebra retract of a smooth `R`-algebra `B` in the same universe with globally finite free
  `Ω[B⁄R]`.
* `Algebra.Smooth.exists_etale_algHom_comp_eq'` and `Algebra.Smooth.exists_etale_algHom_comp_eq`:
  every `R`-algebra map `A →ₐ[R] T` out of a smooth `R`-algebra along a surjective base map `R → T`
  factors through an étale `R`-algebra (in the universe of `A`, or in the universe of `R`).

## References

* [Stacks Project, Lemma 15.13.3](https://stacks.math.columbia.edu/tag/0H74).
-/

public section

noncomputable section

open KaehlerDifferential TensorProduct

universe u v

namespace Module.Basis

/-- Given an `R`-algebra `B`, a finite `B`-basis `b` of `Ω[B⁄R]`, and an `R`-algebra map
`ψ : B →ₐ[R] T` with `algebraMap R T` surjective, there exist elements `x : ι → B` in `ker ψ` whose
Jacobian matrix in the basis `b` maps under `ψ` to the identity matrix `1` over `T`; in particular
`ψ (b.det (D R B ∘ x)) = 1`. -/
theorem exists_ker_and_det_D_eq_one_of_surjective {R B T ι : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [CommRing T] [Algebra R T] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι B Ω[B⁄R]) (hsurj : Function.Surjective (algebraMap R T)) (ψ : B →ₐ[R] T) :
    ∃ x : ι → B, (∀ i, ψ (x i) = 0) ∧
      ψ.toRingHom.mapMatrix (b.toMatrix (fun i ↦ D R B (x i))) = 1 ∧
      ψ (b.det fun i ↦ D R B (x i)) = 1 := by
  -- Express each basis element `b j` as a `B`-linear combination `∑ y, f j y • D R B y`.
  have hspan (j : ι) : b j ∈ Submodule.span B (Set.range (D R B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  choose f hf using fun j ↦ Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan j)
  -- Lift each `ψ y` along the surjection `algebraMap R T` so `y' y := y - s y` lies in `ker ψ`
  -- while having the same `R`-differential `D R B (y' y) = D R B y`.
  choose s hs using fun y : B ↦ hsurj (ψ y)
  let y' : B → B := fun y ↦ y - algebraMap R B (s y)
  have hψy' (y : B) : ψ (y' y) = 0 := by
    simp [y', AlgHom.commutes, hs]
  have hDy' (y : B) : D R B (y' y) = D R B y := by
    simp [y']
  let x : ι → B := fun j ↦ (f j).sum fun y c ↦ c * y' y
  have hψx (j : ι) : ψ (x j) = 0 := by
    simp [x, Finsupp.sum, map_sum, hψy']
  have hDx (j : ι) : D R B (x j) = b j + (f j).sum fun y c ↦ y' y • D R B c := by
    have hfj : ∑ y ∈ (f j).support, f j y • D R B y = b j := by
      simpa [Finsupp.sum] using hf j
    calc D R B (x j)
        = ∑ y ∈ (f j).support, (f j y • D R B (y' y) + y' y • D R B (f j y)) := by
          simp only [x, Finsupp.sum, map_sum, Derivation.leibniz]
      _ = (∑ y ∈ (f j).support, f j y • D R B y) +
            ∑ y ∈ (f j).support, y' y • D R B (f j y) := by
          simp only [Finset.sum_add_distrib, hDy']
      _ = b j + (f j).sum fun y c ↦ y' y • D R B c := by
          rw [hfj, Finsupp.sum]
  have hmat : ψ.toRingHom.mapMatrix (b.toMatrix (fun j ↦ D R B (x j))) = 1 := by
    ext i j
    have hij : ψ (b.repr (D R B (x j)) i) = if i = j then 1 else 0 := by
      rw [← Module.Basis.coord_apply, hDx j, map_add, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.sum, map_sum, map_add, map_sum]
      simp only [LinearMap.map_smul, smul_eq_mul, map_mul, hψy', zero_mul, Finset.sum_const_zero,
        add_zero, Finsupp.single_apply, @eq_comm _ j i]
      split_ifs <;> simp
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.one_apply] using hij
  refine ⟨x, hψx, hmat, ?_⟩
  have hmat' := hmat
  rw [AlgHom.toRingHom_eq_coe] at hmat'
  rw [Module.Basis.det_apply, ← AlgHom.coe_toRingHom, RingHom.map_det, hmat', Matrix.det_one]

/-- When `B` is smooth over `R` and `Ω[B⁄R]` admits a `B`-basis `b` indexed by `ι`, any `R`-algebra
map `ψ : B →ₐ[R] T` with `algebraMap R T` surjective factors through an étale quotient
`Localization.Away d ⧸ (xᵢ)` with `ψ d = 1` and `ψ (x i) = 0` for all `i : ι`. -/
theorem exists_etale_quotient_localizationAway {R B T ι : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.Smooth R B] [CommRing T] [Algebra R T]
    (b : Module.Basis ι B Ω[B⁄R]) (hsurj : Function.Surjective (algebraMap R T)) (ψ : B →ₐ[R] T) :
    ∃ (d : B) (x : ι → B)
      (ψC : (Localization.Away d ⧸
        Ideal.span (Set.range (algebraMap B (Localization.Away d) ∘ x))) →ₐ[R] T),
      ψ d = 1 ∧ (∀ i, ψ (x i) = 0) ∧
      Algebra.Etale R (Localization.Away d ⧸
        Ideal.span (Set.range (algebraMap B (Localization.Away d) ∘ x))) ∧
      ψC.comp ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R B _)) = ψ := by
  by_cases hB : Subsingleton B
  · -- When `B` is subsingleton, `T` and `B[1/0] ⧸ (0)` are subsingleton and hence étale over `R`.
    have : Subsingleton T := ψ.toRingHom.codomain_trivial
    let C := Localization.Away (0 : B) ⧸
      Ideal.span (Set.range (algebraMap B (Localization.Away (0 : B)) ∘ (0 : ι → B)))
    have : Subsingleton C := (algebraMap B C).codomain_trivial
    let ψC : C →ₐ[R] T :=
      { toFun := 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ ↦ Subsingleton.elim _ _
        commutes' := fun _ ↦ Subsingleton.elim _ _ }
    exact ⟨0, 0, ψC, Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _, inferInstance,
      Subsingleton.elim _ _⟩
  · classical
    have : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
    have : Finite ι := Module.Finite.finite_basis b
    let _ : Fintype ι := Fintype.ofFinite ι
    obtain ⟨x, hψx, -, hψd⟩ := b.exists_ker_and_det_D_eq_one_of_surjective hsurj ψ
    set d := b.det fun i ↦ D R B (x i)
    let W := Localization.Away d
    -- On `W = B[1/d]`, `d` is invertible so the images of `x i` have differentials forming a basis.
    let bW := TauCeti.kaehlerBasisOfFormallyEtale R B W b
    let xW : ι → W := algebraMap B W ∘ x
    have hdetW : bW.det (fun i ↦ D R W (xW i)) = algebraMap B W d := by
      rw [← TauCeti.kaehlerBasisOfFormallyEtale_det_map]
      congr 1
      ext i
      simp [xW]
    obtain ⟨hli, hspan⟩ := bW.is_basis_iff_det.mpr
      (hdetW ▸ IsLocalization.Away.algebraMap_isUnit d)
    have : Algebra.Smooth R W := .comp R B W
    let bx : Module.Basis ι W Ω[W⁄R] := .mk hli hspan.ge
    have het : Algebra.Etale R (W ⧸ Ideal.span (Set.range xW)) :=
      bx.etale_quotient_span_range fun i ↦ by simp [bx]
    -- `ψ` inverts `d` (`ψ d = 1`) and vanishes on every `x i`, so it factors through `W ⧸ (xW)`.
    let ψW : W →ₐ[R] T := IsLocalization.Away.liftAlgHom d (f := ψ) (by simp [hψd])
    have hψW (a : B) : ψW (algebraMap B W a) = ψ a := by
      simp [ψW, IsLocalization.Away.lift_eq]
    have hker (w : W) (hw : w ∈ Ideal.span (Set.range xW)) : ψW w = 0 := by
      rw [← RingHom.mem_ker]
      refine Ideal.span_le.mpr ?_ hw
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, xW, hψW, hψx i]
    exact ⟨d, x, Ideal.Quotient.liftₐ (Ideal.span (Set.range xW)) ψW hker, hψd, hψx, het,
      AlgHom.ext hψW⟩

end Module.Basis

namespace Algebra.Smooth

/-- **Every smooth algebra is a retract of a smooth algebra with globally free differentials.**
For a smooth `R`-algebra `A`, choosing a split surjection `(Fin n → A) →ₗ[A] Ω[A⁄R]` with finite
projective kernel `K` makes `B := SymmetricAlgebra A K` a smooth `R`-algebra containing `A` as a
retract via the augmentation `SymmetricAlgebra.algebraMapInv`, while the split Jacobi–Zariski
sequence identifies `Ω[B⁄R]` with `(Fin n → B)`. -/
theorem exists_retract_basis_kaehlerDifferential (R : Type u) (A : Type v) [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] :
    ∃ (n : ℕ) (B : Type v) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.Smooth R B)
      (α : A →ₐ[R] B) (β : B →ₐ[R] A),
      β.comp α = AlgHom.id R A ∧ Nonempty (Module.Basis (Fin n) B Ω[B⁄R]) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' A Ω[A⁄R]
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  let K := LinearMap.ker g
  obtain ⟨e₀, -⟩ := (LinearMap.exact_subtype_ker_map g).splitSurjectiveEquiv
    K.injective_subtype ⟨l, hl⟩
  -- `K` is a direct summand of the finite free `A`-module `Fin n → A`, hence finite projective.
  have hKproj : Module.Projective A K :=
    .of_split (e₀.symm.toLinearMap ∘ₗ LinearMap.inl A K Ω[A⁄R])
      (LinearMap.fst A K Ω[A⁄R] ∘ₗ e₀.toLinearMap) (by ext x; simp)
  have hKfin : Module.Finite A K :=
    .of_surjective (LinearMap.fst A K Ω[A⁄R] ∘ₗ e₀.toLinearMap)
      (Prod.fst_surjective.comp e₀.surjective)
  let B := SymmetricAlgebra A K
  have : Algebra.Smooth R B := .comp R A B
  obtain ⟨eB, -⟩ := TauCeti.exists_kaehlerDifferentialProdEquiv R A B
  -- Transport `Pi.basisFun A (Fin n)` along `B ⊗[A] (Fin n → A) ≃ B ⊗[A] (K × Ω[A⁄R]) ≃ Ω[B⁄R]`.
  let bAK : Module.Basis (Fin n) B (B ⊗[A] (K × Ω[A⁄R])) :=
    Algebra.TensorProduct.basis B ((Pi.basisFun A (Fin n)).map e₀)
  let eTot : (B ⊗[A] (K × Ω[A⁄R])) ≃ₗ[B] Ω[B⁄R] :=
    TensorProduct.prodRight A B B K Ω[A⁄R] ≪≫ₗ
      LinearEquiv.prodComm B (B ⊗[A] K) (B ⊗[A] Ω[A⁄R]) ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl B (B ⊗[A] Ω[A⁄R]))
        (SymmetricAlgebra.kaehlerDifferentialEquiv A K).symm ≪≫ₗ
      eB.symm
  refine ⟨n, B, inferInstance, inferInstance, inferInstance,
    IsScalarTower.toAlgHom R A B,
    (SymmetricAlgebra.algebraMapInv (R := A) (M := K)).restrictScalars R, ?_, ⟨bAK.map eTot⟩⟩
  ext a
  exact SymmetricAlgebra.algebraMap_leftInverse K a

/-- **Étale slice factorization (in the universe of `A`).** Every `R`-algebra homomorphism
`ψ : A →ₐ[R] T` out of a smooth `R`-algebra `A` along a surjective base map `R → T` factors through
an étale `R`-algebra `C` in the universe of `A`. -/
@[stacks 0H74 "étale factorization step"]
theorem exists_etale_algHom_comp_eq' {R : Type u} {A : Type v} {T : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] [CommRing T] [Algebra R T]
    (hsurj : Function.Surjective (algebraMap R T)) (ψ : A →ₐ[R] T) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (f : A →ₐ[R] C) (ψC : C →ₐ[R] T), ψC.comp f = ψ := by
  obtain ⟨n, B, _, _, _, α, β, hβα, ⟨b⟩⟩ := exists_retract_basis_kaehlerDifferential R A
  obtain ⟨d, x, ψC, -, -, het, hψC⟩ := b.exists_etale_quotient_localizationAway hsurj (ψ.comp β)
  refine ⟨_, inferInstance, inferInstance, het,
    ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R B _)).comp α, ψC, ?_⟩
  rw [← AlgHom.comp_assoc, hψC, AlgHom.comp_assoc, hβα, AlgHom.comp_id]

/-- **Étale slice factorization (in the universe of `R`).** Every `R`-algebra homomorphism
`ψ : A →ₐ[R] T` out of a smooth `R`-algebra `A` along a surjective base map `R → T` factors through
an étale `R`-algebra `C : Type u` in the universe of the base ring `R`. -/
@[stacks 0H74 "small-universe étale factorization"]
theorem exists_etale_algHom_comp_eq {R : Type u} {A T : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Smooth R A] [CommRing T] [Algebra R T]
    (hsurj : Function.Surjective (algebraMap R T)) (ψ : A →ₐ[R] T) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (f : A →ₐ[R] C) (ψC : C →ₐ[R] T), ψC.comp f = ψ := by
  obtain ⟨C₀, _, _, _, f₀, ψ₀, h₀⟩ := exists_etale_algHom_comp_eq' hsurj ψ
  have : Small.{u} C₀ := Algebra.FiniteType.small (R := R) (S := C₀)
  let e : Shrink.{u} C₀ ≃ₐ[R] C₀ := Shrink.algEquiv R C₀
  have : Algebra.Etale R (Shrink.{u} C₀) := .of_equiv e.symm
  refine ⟨Shrink.{u} C₀, inferInstance, inferInstance, inferInstance,
    e.symm.toAlgHom.comp f₀, ψ₀.comp e.toAlgHom, ?_⟩
  rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc e.toAlgHom, AlgEquiv.comp_symm, AlgHom.id_comp, h₀]

end Algebra.Smooth
