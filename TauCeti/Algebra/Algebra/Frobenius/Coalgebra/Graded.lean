/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Coalgebra.Transport
public import TauCeti.Algebra.Coalgebra.Graded
public import TauCeti.RingTheory.GradedAlgebra.TensorProduct

/-!
# Graded Frobenius coalgebras

This file develops the degree theory of `ℤ`-graded Frobenius coalgebras on top of
`TauCeti.Algebra.Coalgebra.Graded`.

On a `ℤ`-graded Frobenius coalgebra `A` over a commutative semiring `R`, the counit has degree `-d`
into `TauCeti.trivialGrading R R` iff the coproduct has degree `d` into the total-degree tensor
grading (`Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul`), without
commutativity or projectivity assumptions on `A`. Consequently, `Coalgebra.handleOp R A` has degree
`d`, `Coalgebra.handleElem R A ∈ 𝒜 d`, and trace-dual basis elements lie in `𝒜 (d - deg i)`. With
`TauCeti.Algebra.Coalgebra.Graded`, this gives closure under counit-preserving degree-zero algebra
equivalences, tensor products, and trivially graded scalar extensions; for `ℤ`-graded base algebras
`S`, `TauCeti.Algebra.Coalgebra.Graded` proves `R`-linear counit homogeneity and this file proves
the total degree of the scalar-extended handle element
(`Coalgebra.handleElem_baseChange_mem_tensorProduct`).

## Main results

* `Coalgebra.IsFrobenius.comul_one_mem_graded`,
  `Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul`.
* `Coalgebra.isHomogeneous_handleOp`, `Coalgebra.handleElem_mem_graded`,
  `Coalgebra.IsFrobenius.handleElem_pow_mem_graded`, `LinearMap.traceDualBasis_mem_graded`.
* `AlgEquiv.isHomogeneous_comul_iff`, `Coalgebra.handleElem_tensorProduct_mem_tensorProduct`,
  `Coalgebra.handleElem_baseChange_mem_tensorProduct`.

## References

* F. Goertz, L. Marino, P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  `arXiv:2602.11120v1`, §§2–3.
* M. Khovanov, *Link homology and Frobenius extensions*, Fund. Math. 190 (2006), 179–190.
-/

public section

noncomputable section

open scoped DirectSum TensorProduct

/-! ### Counit-coproduct degree duality -/

section DegreeDuality

open TauCeti

private def lidCounitMulLeft {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [CoalgebraStruct R A] : A →ₗ[R] A ⊗[R] A →ₗ[R] A where
  toFun a := (_root_.TensorProduct.lid R A).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) ∘ₗ _root_.LinearMap.mulLeft R a).rTensor A
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp [add_mul, add_smul]
  map_smul' _ _ := TensorProduct.ext' fun _ _ => by simp [mul_smul]

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

private theorem isHomogeneous_lidCounitMulLeft [CoalgebraStruct R A] {d p : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) (-d)) {a : A} (ha : a ∈ 𝒜 p) :
    TauCeti.LinearMap.IsHomogeneous (lidCounitMulLeft (R := R) a)
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece 𝒜 (p - d) := by
  let G := InternalGrading.ofDecomposition 𝒜
  refine TauCeti.LinearMap.isHomogeneous_def.mpr fun m z hz =>
    G.tensorProduct_piece_le G (C := (𝒜 (m + (p - d))).comap (lidCounitMulLeft (R := R) a))
      (fun q u hu v hv => ?_) hz
  rw [InternalGrading.ofDecomposition_piece] at hu hv
  simp only [Submodule.mem_comap, lidCounitMulLeft, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    _root_.LinearMap.mulLeft_apply, _root_.TensorProduct.lid_tmul]
  by_cases hpq : p + q + -d = 0
  · have hdeg : m + (p - d) = m - q := by omega
    exact hdeg ▸ (𝒜 (m - q)).smul_mem (Coalgebra.counit (R := R) (a * u)) hv
  · simp [((mem_trivialGrading_iff R R).mp (hε.map_mem (SetLike.mul_mem_graded ha hu))).resolve_left
      hpq]

/-- On a `ℤ`-graded Frobenius coalgebra whose counit has degree `-d`, the Casimir tensor
`comul 1` has total degree `d`. -/
theorem Coalgebra.IsFrobenius.comul_one_mem_graded [Coalgebra R A] [Coalgebra.IsFrobenius R A]
    {d : ℤ} (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) (-d)) :
    Coalgebra.comul (R := R) (1 : A) ∈
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d := by
  classical
  let G := InternalGrading.ofDecomposition 𝒜
  set f : A →ₗ[R] A ⊗[R] A →ₗ[R] A := lidCounitMulLeft (R := R) with hf_def
  set c := Coalgebra.comul (R := R) (1 : A) with hc_def
  rw [← DirectSum.sum_support_decompose (G.tensorProduct G).piece c]
  refine Submodule.sum_mem _ fun n hn => ?_
  by_cases hnd : n = d
  · exact hnd ▸ (DirectSum.decompose (G.tensorProduct G).piece c n).2
  · exfalso; apply DFinsupp.mem_support_iff.mp hn; ext
    refine tensor_eq_of_forall_lid_rTensor_counit_mulLeft fun a => ?_
    set zn : A ⊗[R] A := ↑(DirectSum.decompose (G.tensorProduct G).piece c n) with hzn_def
    have hF : f.flip zn = 0 := G.linearMap_ext fun p b hb => by
      have hb' : b ∈ 𝒜 p := by simpa [G] using hb
      have hdecomp := (isHomogeneous_lidCounitMulLeft 𝒜 hε hb').map_decompose n c
      have hf1 : lidCounitMulLeft (R := R) b c = b := by
        simpa [hc_def, lidCounitMulLeft] using lid_rTensor_counit_mulLeft_comul (R := R) b 1
      rw [LinearMap.flip_apply, LinearMap.zero_apply, hf_def, hzn_def, hdecomp, hf1,
        DirectSum.decompose_of_mem_ne 𝒜 hb' (by omega)]
    simpa [hf_def, lidCounitMulLeft, hzn_def] using DFunLike.congr_fun hF a

/-- **Degree duality for graded Frobenius coalgebras**: on a `ℤ`-graded Frobenius coalgebra `A`
(without commutativity or projectivity assumptions on `A`), the counit has degree `-d` if and only
if the coproduct has degree `d`. -/
theorem Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul
    [Coalgebra R A] [Coalgebra.IsFrobenius R A] (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
        (trivialGrading R R) (-d) ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece d := by
  let G := InternalGrading.ofDecomposition 𝒜
  refine ⟨fun hε => TauCeti.LinearMap.isHomogeneous_def.mpr fun p a ha => ?_, fun hΔ => ?_⟩
  · rw [comul_eq_rTensor_mulLeft_comul_one]
    have hmulLeft : TauCeti.LinearMap.IsHomogeneous (_root_.LinearMap.mulLeft R a) G.piece G.piece
        p := TauCeti.LinearMap.isHomogeneous_def.mpr fun q x hx => by
      rw [InternalGrading.ofDecomposition_piece] at hx ⊢
      exact add_comm p q ▸ SetLike.mul_mem_graded ha hx
    simpa [add_comm] using (hmulLeft.rTensor G).map_mem (comul_one_mem_graded 𝒜 hε)
  · simpa [G] using Coalgebra.isHomogeneous_counit_of_isHomogeneous_comul G (by simpa [G] using hΔ)

/-- Even-degree specialization (`-2 * c` and `2 * c`) of
`Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul`. -/
theorem Coalgebra.IsFrobenius.isHomogeneous_counit_neg_two_mul_iff_isHomogeneous_comul_two_mul
    [Coalgebra R A] [Coalgebra.IsFrobenius R A] (c : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
        (trivialGrading R R) (-2 * c) ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece (2 * c) := by
  simpa [neg_mul] using isHomogeneous_counit_iff_isHomogeneous_comul 𝒜 (2 * c)

/-! ### Degrees of the handle operator, handle element, and trace-dual basis -/

/-- When the coproduct of a `ℤ`-graded `R`-algebra `A` is homogeneous of degree `d`, the handle
operator `Coalgebra.handleOp R A` is homogeneous of degree `d`. -/
theorem Coalgebra.isHomogeneous_handleOp [CoalgebraStruct R A] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.handleOp R A) 𝒜 𝒜 d :=
  TauCeti.LinearMap.isHomogeneous_def.mpr fun _ _ ha => by
    simpa [Coalgebra.handleOp_apply] using (TauCeti.isHomogeneous_mul' 𝒜).map_mem (hΔ.map_mem ha)

/-- When the coproduct of a `ℤ`-graded `R`-algebra `A` is homogeneous of degree `d`, the handle
element `Coalgebra.handleElem R A` lies in `𝒜 d`. -/
theorem Coalgebra.handleElem_mem_graded [CoalgebraStruct R A] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d) : Coalgebra.handleElem R A ∈ 𝒜 d := by
  simpa [← Coalgebra.handleOp_one] using
    (Coalgebra.isHomogeneous_handleOp 𝒜 hΔ).map_mem (SetLike.one_mem_graded 𝒜)

/-- On a `ℤ`-graded Frobenius coalgebra whose counit has degree `-d`, the handle element lies in
`𝒜 d`, and its `g`-th power lies in `𝒜 (g • d)`. -/
theorem Coalgebra.IsFrobenius.handleElem_pow_mem_graded
    [Coalgebra R A] [Coalgebra.IsFrobenius R A] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) (-d)) (g : ℕ) : Coalgebra.handleElem R A ^ g ∈ 𝒜 (g • d) :=
  SetLike.pow_mem_graded g
    (Coalgebra.handleElem_mem_graded 𝒜 ((isHomogeneous_counit_iff_isHomogeneous_comul 𝒜 d).mp hε))

end Semiring

/-- `InternalGrading` form of `Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul`,
stated directly with `(G.tensorProduct G).piece`. -/
theorem Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul_piece {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] (G : InternalGrading R A ℤ) [GradedAlgebra G.piece]
    [Coalgebra R A] [Coalgebra.IsFrobenius R A] (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) G.piece
        (trivialGrading R R) (-d) ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) G.piece
        (G.tensorProduct G).piece d := by
  convert isHomogeneous_counit_iff_isHomogeneous_comul G.piece d using 3
  congr 2 <;> refine InternalGrading.ext fun p => ?_ <;> rw [InternalGrading.ofDecomposition_piece]

/-- For the Frobenius coalgebra reconstructed from a perfect trace `ε` on a finite projective
commutative graded `R`-algebra, `ε` has degree `-d` if and only if the reconstructed coproduct has
degree `d`. -/
theorem LinearMap.isHomogeneous_frobeniusCoalgebra_comul_iff {R A : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A] [Module.Finite R A] [Module.Projective R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]
    (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (letI := ε.frobeniusCoalgebra; Coalgebra.comul (R := R)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece d ↔
      TauCeti.LinearMap.IsHomogeneous ε 𝒜 (trivialGrading R R) (-d) := by
  let := ε.frobeniusCoalgebra; have := ε.frobeniusCoalgebra_isFrobenius
  rw [← Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul,
    ε.frobeniusCoalgebra_counit]

/-- If `ε : A →ₗ[R] R` is a homogeneous perfect trace of degree `-d` and `b` is a homogeneous
basis with `b i ∈ 𝒜 (deg i)`, then the `i`-th trace-dual basis element lies in `𝒜 (d - deg i)`. -/
theorem LinearMap.traceDualBasis_mem_graded {R A ι : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] [Finite ι]
    (b : Module.Basis ι R A) {deg : ι → ℤ} (hb : ∀ i, b i ∈ 𝒜 (deg i)) {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε 𝒜 (trivialGrading R R) (-d)) (i : ι) :
    ε.traceDualBasis b i ∈ 𝒜 (d - deg i) := by
  classical
  set w := ε.traceDualBasis b i with hw_def
  suffices hw : w = DirectSum.decompose 𝒜 w (d - deg i) by
    rw [hw]; exact (DirectSum.decompose 𝒜 w (d - deg i)).2
  refine ((mul R A).compr₂ ε).toPerfPair.injective (b.ext fun j => ?_)
  simp only [toPerfPair_apply, compr₂_apply, mul_apply_apply]
  have hkill {q : ℤ} {x : A} (hx : x ∈ 𝒜 q) (hq : q ≠ d - deg j) : ε (x * b j) = 0 :=
    ((mem_trivialGrading_iff R R).mp
      (hε.map_mem (SetLike.mul_mem_graded hx (hb j)))).resolve_left (by omega)
  by_cases hij : deg j = deg i
  · have hmap := (InternalGrading.ofDecomposition 𝒜).map_eq_map_decompose
      (ε ∘ₗ mulRight R (b j)).toAddMonoidHom (i := d - deg i)
      (fun q x hx hq => by
        rw [InternalGrading.ofDecomposition_piece] at hx
        exact hkill hx (hij ▸ hq)) w
    simpa [InternalGrading.coe_decompose_ofDecomposition_piece_apply] using hmap
  · rw [hkill (DirectSum.decompose 𝒜 w (d - deg i)).2 (by omega), hw_def]
    simp only [ε.traceDualBasis_mul, Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right_iff]
    rintro rfl; exact (hij rfl).elim

end DegreeDuality

/-! ### Compatibility with algebra equivalences, tensor products, and scalar extensions -/

section Compatibility

open TauCeti

/-- A counit-preserving degree-zero algebra equivalence between Frobenius coalgebras with internal
`ℤ`-gradings preserves homogeneity of the coproduct at any degree `d`. -/
theorem AlgEquiv.isHomogeneous_comul_iff {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] [Coalgebra R A] [Coalgebra R B]
    [Coalgebra.IsFrobenius R A] [Coalgebra.IsFrobenius R B]
    (e : A ≃ₐ[R] B) (he_hom : TauCeti.LinearMap.IsHomogeneous e.toLinearMap 𝒜 ℬ 0)
    (he_counit : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece d ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := B)) ℬ
        ((InternalGrading.ofDecomposition ℬ).tensorProduct
          (InternalGrading.ofDecomposition ℬ)).piece d :=
  (e.toFrobeniusCoalgEquiv he_counit).isHomogeneous_comul_iff 𝒜 ℬ (by simpa using he_hom) d

/-- On a heterogeneous tensor product `A ⊗[R] B`, if `Coalgebra.handleElem S A` has degree `dA` in
`GA` and `Coalgebra.handleElem R B` has degree `dB` in `GB`, then
`Coalgebra.handleElem S (A ⊗[R] B)` has total degree `dA + dB` in `(GA.tensorProduct GB).piece`. -/
theorem Coalgebra.handleElem_tensorProduct_mem_tensorProduct {R S A B : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [NonAssocSemiring A] [Module R A] [Module S A]
    [IsScalarTower R S A] [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass S A A]
    [IsScalarTower S A A] [NonAssocSemiring B] [Module R B] [SMulCommClass R B B]
    [IsScalarTower R B B] [CoalgebraStruct S A] [CoalgebraStruct R B]
    (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ) {dA dB : ℤ}
    (hA : Coalgebra.handleElem S A ∈ GA.piece dA)
    (hB : Coalgebra.handleElem R B ∈ GB.piece dB) :
    haveI : SMulCommClass R S A := IsScalarTower.to_smulCommClass
    Coalgebra.handleElem S (A ⊗[R] B) ∈ (GA.tensorProduct GB).piece (dA + dB) := by
  have : SMulCommClass R S A := IsScalarTower.to_smulCommClass
  rw [Coalgebra.handleElem_tensorProduct]
  exact GA.tmul_mem_tensorProduct GB hA hB

/-- On `S ⊗[R] A` over a `ℤ`-graded commutative `R`-algebra `S` with `1 ∈ 𝒮 0`, if
`Coalgebra.handleElem R A` lies in `𝒜 d`, then `Coalgebra.handleElem S (S ⊗[R] A)` has total degree
`d` in `((ofDecomposition 𝒮).tensorProduct (ofDecomposition 𝒜)).piece`. -/
theorem Coalgebra.handleElem_baseChange_mem_tensorProduct {R S A : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [NonAssocSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A]
    (𝒮 : ℤ → Submodule R S) [DirectSum.Decomposition 𝒮] [SetLike.GradedOne 𝒮]
    (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜] {d : ℤ}
    (hh : Coalgebra.handleElem R A ∈ 𝒜 d) :
    Coalgebra.handleElem S (S ⊗[R] A) ∈
      ((InternalGrading.ofDecomposition 𝒮).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d := by
  simpa using Coalgebra.handleElem_tensorProduct_mem_tensorProduct (S := S)
    (InternalGrading.ofDecomposition 𝒮) (InternalGrading.ofDecomposition 𝒜) (dA := 0) (dB := d)
    (by simpa [Coalgebra.handleElem_self] using SetLike.one_mem_graded 𝒮) (by simpa using hh)

end Compatibility
