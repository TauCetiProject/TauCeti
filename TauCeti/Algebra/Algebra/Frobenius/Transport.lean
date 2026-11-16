/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Algebra.Frobenius.Coalgebra
public import TauCeti.LinearAlgebra.TensorProduct.Dual

/-!
# Transport, tensor products, and scalar extension of Frobenius algebras

This file develops structural operations on Frobenius coalgebras and trace-reconstructed Frobenius
algebras over an arbitrary commutative semiring `R`.

## Main definitions and results

* `CoalgEquiv.isFrobenius_iff`, `AlgEquiv.toCoalgEquivOfIsFrobenius`,
  `AlgEquiv.frobeniusCoalgEquiv`, `LinearMap.isPerfPair_compr₂_mul_iff_of_algEquiv`,
  `LinearMap.traceDualBasis_map`, `LinearMap.map_frobeniusCoalgebra_comul_of_algEquiv`: transport
  along algebra and coalgebra isomorphisms.
* `TensorProduct.instIsFrobenius`: the heterobasic tensor product `A ⊗[R] B` of an `S`-Frobenius
  coalgebra `A` and an `R`-Frobenius coalgebra `B` is `S`-Frobenius, unifying tensor products
  (`S = R`) and scalar extension (`A = S`).
* `LinearMap.isPerfPair_compr₂_mul_algebraTensorModule_dualDistrib`,
  `LinearMap.isPerfPair_compr₂_mul_dualDistrib`, `LinearMap.isPerfPair_compr₂_mul_baseChange`:
  perfectness of tensor-product and base-changed traces on finite projective (not necessarily
  commutative or associative) algebras.
* `LinearMap.frobeniusCoalgebra_algebraTensorModule_dualDistrib`,
  `LinearMap.frobeniusCoalgebra_dualDistrib`, `LinearMap.traceDualBasis_dualDistrib`,
  `LinearMap.frobeniusCoalgebra_baseChange`, `LinearMap.traceDualBasis_baseChange`: compatibility
  of `LinearMap.frobeniusCoalgebra` and `LinearMap.traceDualBasis` with tensor products and scalar
  extension for commutative algebras.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
-/

public section

noncomputable section

open TensorProduct

/-! ### Transport along algebra and coalgebra isomorphisms -/

namespace CoalgEquiv

section NonUnital

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

private theorem isFrobenius_of_mul (e : A ≃ₗc[R] B) (hmul : ∀ x y, e (x * y) = e x * e y)
    [Coalgebra.IsFrobenius R A] : Coalgebra.IsFrobenius R B := by
  constructor
  refine TensorProduct.ext' fun x y ↦ ?_
  obtain ⟨a, rfl⟩ := EquivLike.surjective e x
  obtain ⟨b, rfl⟩ := EquivLike.surjective e y
  have hcomul (c : A) : Coalgebra.comul (R := R) (e c) =
      TensorProduct.map e.toLinearMap e.toLinearMap (Coalgebra.comul (R := R) c) :=
    (congrArg (fun f : A →ₗ[R] B ⊗[R] B ↦ f c) e.map_comp_comul).symm
  have hleft : Coalgebra.IsFrobenius.left R B (e a ⊗ₜ[R] e b) =
      TensorProduct.map e.toLinearMap e.toLinearMap
        (Coalgebra.IsFrobenius.left R A (a ⊗ₜ[R] b)) := by
    simp only [Coalgebra.IsFrobenius.left_def, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      LinearEquiv.coe_coe, hcomul]
    induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
    | tmul u v => simp [hmul]
    | add t u ht hu => simp_all [add_tmul]
  have hright : Coalgebra.IsFrobenius.right R B (e a ⊗ₜ[R] e b) =
      TensorProduct.map e.toLinearMap e.toLinearMap
        (Coalgebra.IsFrobenius.right R A (a ⊗ₜ[R] b)) := by
    simp only [Coalgebra.IsFrobenius.right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul,
      LinearEquiv.coe_coe, hcomul]
    induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
    | tmul u v => simp [hmul]
    | add t u ht hu => simp_all [tmul_add]
  rw [hleft, hright, Coalgebra.IsFrobenius.left_eq_right (R := R) (A := A)]

/-- A multiplicative coalgebra equivalence preserves and reflects the Frobenius equation. -/
theorem isFrobenius_iff (e : A ≃ₗc[R] B) (hmul : ∀ x y, e (x * y) = e x * e y) :
    Coalgebra.IsFrobenius R A ↔ Coalgebra.IsFrobenius R B :=
  ⟨fun _ ↦ isFrobenius_of_mul e hmul,
    fun _ ↦ isFrobenius_of_mul e.symm fun x y ↦ e.injective (by simp [hmul])⟩

end NonUnital

end CoalgEquiv

namespace AlgEquiv

section IsFrobenius

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Coalgebra R A] [Coalgebra R B] [Coalgebra.IsFrobenius R A] [Coalgebra.IsFrobenius R B]

/-- A counit-preserving algebra isomorphism between Frobenius coalgebras is automatically a
coalgebra isomorphism. -/
def toCoalgEquivOfIsFrobenius (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) :
    A ≃ₗc[R] B where
  __ := e.toLinearEquiv
  counit_comp := hε
  map_comp_comul := by
    ext a
    apply (LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := B))).injective
    refine TensorProduct.ext' fun x y ↦ ?_
    have hε_apply (u : A) : Coalgebra.counit (R := R) (e u) = Coalgebra.counit (R := R) u :=
      congrFun (congrArg DFunLike.coe hε) u
    have hmap (t : A ⊗[R] A) :
        LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := B))
            (TensorProduct.map e.toLinearMap e.toLinearMap t) (x ⊗ₜ[R] y) =
          LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A)) t
            (e.symm x ⊗ₜ[R] e.symm y) := by
      induction t using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
          LinearMap.traceTensorEquiv_tmul]
        rw [← hε_apply (e.symm x * u), ← hε_apply (v * e.symm y), map_mul e, map_mul e,
          e.apply_symm_apply, e.apply_symm_apply]
      | add t u ht hu => simp_all
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.toLinearMap_apply]
    calc
      LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := B))
          (TensorProduct.map e.toLinearMap e.toLinearMap (Coalgebra.comul (R := R) a))
          (x ⊗ₜ[R] y)
        = LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A))
            (Coalgebra.comul (R := R) a) (e.symm x ⊗ₜ[R] e.symm y) := hmap _
      _ = Coalgebra.counit (R := R) (e.symm x * a * e.symm y) :=
          LinearMap.traceTensorEquiv_comul_of_isFrobenius _ ‹Coalgebra R A› rfl inferInstance _ _ _
      _ = Coalgebra.counit (R := R) (x * e a * y) := by
          rw [← hε_apply, map_mul e, map_mul e, e.apply_symm_apply, e.apply_symm_apply]
      _ = LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := B))
            (Coalgebra.comul (R := R) (e a)) (x ⊗ₜ[R] y) :=
          (LinearMap.traceTensorEquiv_comul_of_isFrobenius _ ‹Coalgebra R B› rfl inferInstance
            _ _ _).symm

/-- The underlying function of `toCoalgEquivOfIsFrobenius` is the algebra equivalence. -/
@[simp]
theorem coe_toCoalgEquivOfIsFrobenius (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) : ⇑(e.toCoalgEquivOfIsFrobenius hε) = e := (rfl)

/-- The underlying linear equivalence of `toCoalgEquivOfIsFrobenius` is `e.toLinearEquiv`. -/
@[simp]
theorem toLinearEquiv_toCoalgEquivOfIsFrobenius (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) :
    (e.toCoalgEquivOfIsFrobenius hε).toLinearEquiv = e.toLinearEquiv := (rfl)

/-- The inverse of `toCoalgEquivOfIsFrobenius` has `e.symm` as underlying function. -/
@[simp]
theorem coe_toCoalgEquivOfIsFrobenius_symm (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) :
    ⇑(e.toCoalgEquivOfIsFrobenius hε).symm = e.symm := (rfl)

end IsFrobenius

end AlgEquiv

/-! ### Tensor products and scalar extension of Frobenius coalgebras -/

namespace TensorProduct

section IsFrobenius

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [NonUnitalNonAssocSemiring A] [Module R A] [Module S A] [IsScalarTower R S A]
  [SMulCommClass R S A] [SMulCommClass R A A] [IsScalarTower R A A]
  [SMulCommClass S A A] [IsScalarTower S A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct S A] [CoalgebraStruct R B]
  [Coalgebra.IsFrobenius S A] [Coalgebra.IsFrobenius R B]

/-- The heterobasic tensor product `A ⊗[R] B` of an `S`-Frobenius coalgebra `A` and an
`R`-Frobenius coalgebra `B` is an `S`-Frobenius coalgebra. Taking `S = R` gives the tensor product
of Frobenius algebras; taking `A = S` gives scalar extension `S ⊗[R] B`. -/
instance instIsFrobenius : Coalgebra.IsFrobenius S (A ⊗[R] B) := by
  constructor
  refine TensorProduct.ext' fun x y ↦ ?_
  let φ := AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [add_tmul, map_add, hx₁, hx₂]
  | tmul a₁ b₁ =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [tmul_add, map_add, hy₁, hy₂]
    | tmul a₂ b₂ =>
      have hleft : Coalgebra.IsFrobenius.left S (A ⊗[R] B)
            ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
          φ (Coalgebra.IsFrobenius.left S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
            Coalgebra.IsFrobenius.left R B (b₁ ⊗ₜ[R] b₂)) := by
        simp only [Coalgebra.IsFrobenius.left_def, LinearMap.comp_apply, LinearMap.rTensor_tmul,
          TensorProduct.comul_tmul, LinearEquiv.coe_coe]
        induction Coalgebra.comul (R := S) a₁ using TensorProduct.inductionOn with
        | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
        | tmul u₁ u₂ =>
          induction Coalgebra.comul (R := R) b₁ using TensorProduct.inductionOn with
          | add v w hv hw => simp only [tmul_add, add_tmul, map_add, hv, hw]
          | tmul v₁ v₂ => simp [φ]
      have hright : Coalgebra.IsFrobenius.right S (A ⊗[R] B)
            ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
          φ (Coalgebra.IsFrobenius.right S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
            Coalgebra.IsFrobenius.right R B (b₁ ⊗ₜ[R] b₂)) := by
        simp only [Coalgebra.IsFrobenius.right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul,
          TensorProduct.comul_tmul, LinearEquiv.coe_coe]
        induction Coalgebra.comul (R := S) a₂ using TensorProduct.inductionOn with
        | add u v hu hv => simp only [add_tmul, tmul_add, map_add, hu, hv]
        | tmul u₁ u₂ =>
          induction Coalgebra.comul (R := R) b₂ using TensorProduct.inductionOn with
          | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
          | tmul v₁ v₂ => simp [φ]
      rw [hleft, hright, Coalgebra.IsFrobenius.left_eq_right (R := S) (A := A),
        Coalgebra.IsFrobenius.left_eq_right (R := R) (A := B)]

end IsFrobenius

end TensorProduct

/-! ### Trace-reconstructed Frobenius coalgebras under isomorphisms, tensor products, and
base change -/

namespace LinearMap

section AlgEquivTransport

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- Pulling back a linear functional along an algebra isomorphism preserves and reflects
perfectness of its trace pairing. -/
theorem isPerfPair_compr₂_mul_iff_of_algEquiv (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R) :
    ((mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair ↔ ((mul R B).compr₂ ε).IsPerfPair := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hcomp : (mul R B).compr₂ ε =
        ((mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).compl₁₂
          e.symm.toLinearMap e.symm.toLinearMap := by ext; simp
    rw [hcomp]
    exact IsPerfPair.compl₁₂ (p := (mul R A).compr₂ (ε ∘ₗ e.toLinearMap))
      e.symm.toLinearEquiv e.symm.toLinearEquiv
  · have hcomp : (mul R A).compr₂ (ε ∘ₗ e.toLinearMap) =
        ((mul R B).compr₂ ε).compl₁₂ e.toLinearMap e.toLinearMap := by ext; simp
    rw [hcomp]
    exact IsPerfPair.compl₁₂ (p := (mul R B).compr₂ ε) e.toLinearEquiv e.toLinearEquiv

end AlgEquivTransport

section CommAlgEquiv

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]

/-- Transporting a basis along an algebra isomorphism commutes with forming the trace-dual basis. -/
theorem traceDualBasis_map {ι : Type*} [Finite ι] (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((mul R B).compr₂ ε).IsPerfPair] [((mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair]
    (b : Module.Basis ι R A) :
    traceDualBasis ε (b.map e.toLinearEquiv) =
      (traceDualBasis (ε ∘ₗ e.toLinearMap) b).map e.toLinearEquiv := by
  ext i
  apply ((mul R B).compr₂ ε).toPerfPair.injective
  ext y
  calc
    ((mul R B).compr₂ ε).toPerfPair (traceDualBasis ε (b.map e.toLinearEquiv) i) y
      = b.repr (e.symm y) i := by simp
    _ = (ε ∘ₗ e.toLinearMap) (traceDualBasis (ε ∘ₗ e.toLinearMap) b i * e.symm y) :=
        (traceDualBasis_mul (ε ∘ₗ e.toLinearMap) b i (e.symm y)).symm
    _ = ((mul R B).compr₂ ε).toPerfPair
          ((traceDualBasis (ε ∘ₗ e.toLinearMap) b).map e.toLinearEquiv i) y := by
        simp [-traceDualBasis_mul]

variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]

/-- An algebra isomorphism intertwines the trace-reconstructed comultiplications of `ε ∘ e` and
`ε`. -/
theorem map_frobeniusCoalgebra_comul_of_algEquiv (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((mul R B).compr₂ ε).IsPerfPair] [((mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair]
    (a : A) :
    TensorProduct.map e.toLinearMap e.toLinearMap
        ((ε ∘ₗ e.toLinearMap).frobeniusCoalgebra.comul a) =
      ε.frobeniusCoalgebra.comul (e a) := by
  let := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra; let := ε.frobeniusCoalgebra
  have := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra_isFrobenius
  have := ε.frobeniusCoalgebra_isFrobenius
  exact congrFun (congrArg DFunLike.coe (e.toCoalgEquivOfIsFrobenius (by simp)).map_comp_comul) a

end CommAlgEquiv

end LinearMap

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

/-- An algebra isomorphism induces a coalgebra isomorphism between the trace-reconstructed
Frobenius coalgebras for `ε ∘ e` and `ε`. -/
def frobeniusCoalgEquiv (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((LinearMap.mul R B).compr₂ ε).IsPerfPair]
    [((LinearMap.mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair] :
    letI := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra
    letI := ε.frobeniusCoalgebra
    A ≃ₗc[R] B :=
  letI := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra
  letI := ε.frobeniusCoalgebra
  haveI := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra_isFrobenius
  haveI := ε.frobeniusCoalgebra_isFrobenius
  e.toCoalgEquivOfIsFrobenius (by simp)

/-- The underlying function of `frobeniusCoalgEquiv` is `e`. -/
@[simp]
theorem coe_frobeniusCoalgEquiv (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((LinearMap.mul R B).compr₂ ε).IsPerfPair]
    [((LinearMap.mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair] :
    ⇑(e.frobeniusCoalgEquiv ε) = e := by simp [frobeniusCoalgEquiv]

/-- The inverse of `frobeniusCoalgEquiv` has `e.symm` as underlying function. -/
@[simp]
theorem coe_frobeniusCoalgEquiv_symm (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((LinearMap.mul R B).compr₂ ε).IsPerfPair]
    [((LinearMap.mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair] :
    letI := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra
    letI := ε.frobeniusCoalgebra
    ⇑(e.frobeniusCoalgEquiv ε).symm = e.symm := by simp [frobeniusCoalgEquiv]

end AlgEquiv

namespace LinearMap

section NonUnitalHeterobasicTensor

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [NonUnitalNonAssocSemiring A] [Module R A] [Module S A] [IsScalarTower R S A]
  [SMulCommClass R S A] [SMulCommClass R A A] [IsScalarTower R A A]
  [SMulCommClass S A A] [IsScalarTower S A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [Module.Finite S A] [Module.Projective S A] [Module.Finite R B] [Module.Projective R B]
  (εA : A →ₗ[S] S) (εB : B →ₗ[R] R)
  [((mul S A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]

/-- The heterobasic tensor product of two perfect traces is a perfect trace on `A ⊗[R] B`. -/
theorem isPerfPair_compr₂_mul_algebraTensorModule_dualDistrib :
    ((mul S (A ⊗[R] B)).compr₂
      (TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB))).IsPerfPair := by
  let eL : A ⊗[R] B ≃ₗ[S] Module.Dual S (A ⊗[R] B) :=
    (TensorProduct.AlgebraTensorModule.congr
        (((mul S A).compr₂ εA).toPerfPair)
        (((mul R B).compr₂ εB).toPerfPair)).trans
      (TauCeti.TensorProduct.AlgebraTensorModule.dualDistribEquiv R S A B)
  let eR : A ⊗[R] B ≃ₗ[S] Module.Dual S (A ⊗[R] B) :=
    (TensorProduct.AlgebraTensorModule.congr
        (((mul S A).compr₂ εA).flip.toPerfPair)
        (((mul R B).compr₂ εB).flip.toPerfPair)).trans
      (TauCeti.TensorProduct.AlgebraTensorModule.dualDistribEquiv R S A B)
  have hL : ((mul S (A ⊗[R] B)).compr₂
      (TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB))) =
      eL.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun a₁ b₁ ↦ ?_
    refine TensorProduct.AlgebraTensorModule.ext fun a₂ b₂ ↦ ?_
    simp [eL]
  have hR : ((mul S (A ⊗[R] B)).compr₂
      (TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB))).flip =
      eR.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun a₁ b₁ ↦ ?_
    refine TensorProduct.AlgebraTensorModule.ext fun a₂ b₂ ↦ ?_
    simp [eR]
  exact ⟨hL ▸ eL.bijective, hR ▸ eR.bijective⟩

end NonUnitalHeterobasicTensor

section HeterobasicTensor

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  [CommSemiring B] [Algebra R B]
  [Module.Finite S A] [Module.Projective S A] [Module.Finite R B] [Module.Projective R B]
  (εA : A →ₗ[S] S) (εB : B →ₗ[R] R)
  [((mul S A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]

/-- On a heterobasic tensor product `A ⊗[R] B`, the Frobenius coalgebra reconstructed from the
tensor-product trace equals the tensor product of the reconstructed Frobenius coalgebras. -/
theorem frobeniusCoalgebra_algebraTensorModule_dualDistrib [Module.Finite S (A ⊗[R] B)]
    [((mul S (A ⊗[R] B)).compr₂
      (TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB))).IsPerfPair] :
    (TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra =
      (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
        TensorProduct.instCoalgebra (R := R) (S := S) (A := A) (B := B)) := by
  let : Coalgebra S A := εA.frobeniusCoalgebra; let : Coalgebra R B := εB.frobeniusCoalgebra
  have := εA.frobeniusCoalgebra_isFrobenius; have := εB.frobeniusCoalgebra_isFrobenius
  exact frobeniusCoalgebra_eq _ _
    (TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by
      simp [TensorProduct.AlgebraTensorModule.dualDistrib_apply, Coalgebra.counit])
    inferInstance

end HeterobasicTensor

section NonUnitalTensorProduct

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]
  (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
  [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]

/-- The tensor product of two perfect traces on finite projective `R`-algebras is a perfect trace
on `A ⊗[R] B`. -/
instance isPerfPair_compr₂_mul_dualDistrib :
    ((mul R (A ⊗[R] B)).compr₂ (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).IsPerfPair := by
  have heq : TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB) =
      TensorProduct.AlgebraTensorModule.dualDistrib R R A B (εA ⊗ₜ[R] εB) := by
    ext a b; simp [mul_comm]
  rw [heq]
  exact isPerfPair_compr₂_mul_algebraTensorModule_dualDistrib εA εB

end NonUnitalTensorProduct

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]
  (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
  [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]

/-- The Frobenius coalgebra reconstructed from the tensor product of two perfect traces is the
tensor product of the reconstructed Frobenius coalgebras. -/
theorem frobeniusCoalgebra_dualDistrib :
    (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra =
      (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
        TensorProduct.instCoalgebra (R := R) (S := R) (A := A) (B := B)) := by
  let : Coalgebra R A := εA.frobeniusCoalgebra; let : Coalgebra R B := εB.frobeniusCoalgebra
  have := εA.frobeniusCoalgebra_isFrobenius; have := εB.frobeniusCoalgebra_isFrobenius
  exact frobeniusCoalgebra_eq _ _ (by ext a b; simp [Coalgebra.counit, mul_comm]) inferInstance

omit [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B] in
/-- The trace-dual basis of a tensor product of bases is the tensor product of the trace-dual
bases. -/
theorem traceDualBasis_dualDistrib {ι κ : Type*} [Finite ι] [Finite κ]
    [((mul R (A ⊗[R] B)).compr₂ (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).IsPerfPair]
    (bA : Module.Basis ι R A) (bB : Module.Basis κ R B) :
    traceDualBasis (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)) (bA.tensorProduct bB) =
      (traceDualBasis εA bA).tensorProduct (traceDualBasis εB bB) := by
  ext ⟨i, j⟩
  apply ((mul R (A ⊗[R] B)).compr₂
    (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).toPerfPair.injective
  refine TensorProduct.ext' fun x y ↦ ?_
  simpa [Algebra.TensorProduct.tmul_mul_tmul] using mul_comm ((bB.repr y) j) ((bA.repr x) i)

end TensorProduct

section NonUnitalBaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [Module.Finite R A] [Module.Projective R A]
  (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]

/-- Extending scalars preserves perfectness of a trace on a finite projective algebra. -/
instance isPerfPair_compr₂_mul_baseChange :
    ((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).IsPerfPair := by
  have : ((mul S S).compr₂ (LinearMap.id (R := S) (M := S))).IsPerfPair :=
    TauCeti.Coalgebra.IsFrobenius.isPerfPair_compr₂_mul_counit (R := S) (A := S)
  have heq : Module.Dual.baseChange S ε =
      TensorProduct.AlgebraTensorModule.dualDistrib R S S A
        ((LinearMap.id (R := S) (M := S)) ⊗ₜ[R] ε) :=
    TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by simp
  rw [heq]
  exact isPerfPair_compr₂_mul_algebraTensorModule_dualDistrib (LinearMap.id (R := S) (M := S)) ε

end NonUnitalBaseChange

section BaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring A] [Algebra R A] [Module.Finite R A] [Module.Projective R A]
  (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]

/-- The Frobenius coalgebra reconstructed from a base-changed trace `Module.Dual.baseChange S ε` is
the base change of the Frobenius coalgebra reconstructed from `ε`. -/
theorem frobeniusCoalgebra_baseChange :
    (Module.Dual.baseChange S ε).frobeniusCoalgebra =
      (letI := ε.frobeniusCoalgebra;
        TensorProduct.instCoalgebra (R := R) (S := S) (A := S) (B := A)) := by
  let : Coalgebra R A := ε.frobeniusCoalgebra
  have := ε.frobeniusCoalgebra_isFrobenius
  exact frobeniusCoalgebra_eq _ _
    (TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by simp [Coalgebra.counit]) inferInstance

omit [Module.Finite R A] [Module.Projective R A] in
/-- Base change of a finite basis commutes with forming the trace-dual basis. -/
theorem traceDualBasis_baseChange {ι : Type*} [Finite ι]
    [((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).IsPerfPair]
    (b : Module.Basis ι R A) :
    traceDualBasis (Module.Dual.baseChange S ε) (b.baseChange S) =
      (traceDualBasis ε b).baseChange S := by
  ext i
  apply ((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).toPerfPair.injective
  refine TensorProduct.AlgebraTensorModule.ext fun s a ↦ ?_
  simp [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]

end BaseChange

end LinearMap
