/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Transport
public import TauCeti.Algebra.Module.GradedModule.BaseChange
public import TauCeti.Algebra.Module.GradedModule.Dual.TensorProduct

/-!
# Graded commutative Frobenius algebras

A finite projective commutative graded `R`-algebra `A` equipped with an internal `ℤ`-grading `G` and
a perfect trace `ε : A →ₗ[R] R` of degree `-d` (meaning `ε` vanishes outside degree `d`, i.e.
`ε ∈ G.dualPiece (-d)`) carries a graded Frobenius coalgebra structure over an arbitrary commutative
semiring `R`:

* multiplication `m : A ⊗[R] A →ₗ[R] A` and unit `η : R →ₗ[R] A` have degree `0`
  (`TauCeti.InternalGrading.isHomogeneous_mul'`, `TauCeti.isHomogeneous_algebraLinearMap`);
* the reconstructed coproduct `Δ : A →ₗ[R] A ⊗[R] A` automatically has degree `d`, without
  requiring additive inverses in `R` or existence of a homogeneous basis;
* the handle element `m (Δ 1)` is homogeneous of degree `d`;
* for any finite homogeneous basis `b` with `b i ∈ G.piece (deg i)`, the trace-dual basis satisfies
  `ε.traceDualBasis b i ∈ G.piece (d - deg i)` (without requiring `Module.Finite R A` or
  `Module.Projective R A` beyond the given basis).

When `A` and `B` have even-supported gradings (`parityGrading G.piece 1 = ⊥`, so all odd-degree
pieces vanish), Koszul signs are trivial and the ordinary tensor product `A ⊗[R] B`, degree-`0`
trace-preserving algebra equivalences, and scalar extensions `S ⊗[R] A` (both for ungraded `S` via
`G.baseChange S` and for even-supported graded `S` via `GS.tensorProduct G`) preserve even support
and shift degrees additively (in particular when `d = 2 * c`).

## Main results

* `LinearMap.isHomogeneous_frobeniusCoalgebra_comul`,
  `LinearMap.frobeniusCoalgebra_handle_mem_piece`,
  `LinearMap.traceDualBasis_mem_piece`: degree of the reconstructed coproduct, handle element, and
  trace-dual basis.
* `TauCeti.Coalgebra.IsFrobenius.isHomogeneous_comul`,
  `TauCeti.Coalgebra.IsFrobenius.handle_mem_piece`: the same degree laws for any commutative
  Frobenius coalgebra whose counit has degree `-d`.
* `AlgEquiv.isHomogeneous_symm`, `AlgEquiv.isHomogeneous_of_apply_eq`: inverse homogeneity and
  homogeneity transport along algebra equivalences over arbitrary semirings.
* `AlgEquiv.isHomogeneous_frobeniusCoalgEquiv`,
  `AlgEquiv.isHomogeneous_frobeniusCoalgEquiv_symm`,
  `LinearMap.isHomogeneous_frobeniusCoalgebra_comul_dualDistrib_tmul`,
  `LinearMap.frobeniusCoalgebra_handle_dualDistrib_tmul_mem_piece`,
  `LinearMap.isHomogeneous_frobeniusCoalgebra_comul_baseChange`,
  `LinearMap.frobeniusCoalgebra_handle_baseChange_mem_piece`,
  `LinearMap.frobeniusCoalgebra_handle_baseChange_mem_tensorProduct_piece`: graded compatibility of
  reconstructed Frobenius coalgebras and handles with transport, tensor products, and scalar
  extension.

## References

* M. Khovanov, *Link homology and Frobenius extensions*, Fund. Math. 190 (2006), 179–190.
* A. D. Lauda and H. Pfeiffer, *Open-closed TQFTs extend Khovanov homology to tangles in surfaces*,
  J. Knot Theory Ramifications 18 (2009).
-/

public section

noncomputable section

open TensorProduct TauCeti

namespace LinearMap

section Core

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]
  (G : InternalGrading R A ℤ) [SetLike.GradedMonoid G.piece]
  (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]

private theorem traceTensorEquiv_eq_zero_of_mem_piece {d m i j : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d))
    {u : A ⊗[R] A} (hu : u ∈ (G.tensorProduct G).piece m)
    {x y : A} (hx : x ∈ G.piece i) (hy : y ∈ G.piece j) (hm : m + i + j ≠ 2 * d) :
    traceTensorEquiv ε u (x ⊗ₜ[R] y) = 0 := by
  have hε' := (G.isHomogeneous_trivialGrading_iff_mem_dualPiece ε (-d)).mp hε
  have hle : (G.tensorProduct G).piece m ≤
      ker (applyₗ (x ⊗ₜ[R] y) ∘ₗ (traceTensorEquiv ε).toLinearMap) :=
    G.tensorProduct_piece_le G fun q b₁ hb₁ b₂ hb₂ ↦ by
      simp only [mem_ker, comp_apply, LinearEquiv.coe_coe, applyₗ_apply_apply,
        traceTensorEquiv_tmul]
      by_cases hqi : q + i = d
      · rw [G.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero hε'
          (SetLike.mul_mem_graded hb₂ hy) (by omega), mul_zero]
      · rw [G.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero hε'
          (SetLike.mul_mem_graded hb₁ hx) (by omega), zero_mul]
  exact hle hu

/-- If a perfect trace `ε` on a finite projective graded commutative algebra `A` has degree `-d`,
then the reconstructed Frobenius coproduct `Δ` has degree `d`. -/
theorem isHomogeneous_frobeniusCoalgebra_comul {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (ε.frobeniusCoalgebra).comul
      G.piece (G.tensorProduct G).piece d := by
  let GG := G.tensorProduct G
  have hε' := (G.isHomogeneous_trivialGrading_iff_mem_dualPiece ε (-d)).mp hε
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p a ha
  refine GG.mem_piece_of_decompose_eq_zero fun n hn ↦ ?_
  apply (traceTensorEquiv ε).injective
  rw [map_zero]
  refine TensorProduct.ext (G.linearMap_ext fun i x hx ↦ G.linearMap_ext fun j y hy ↦ ?_)
  simp only [compr₂ₛₗ_apply, TensorProduct.mk_apply, _root_.LinearMap.zero_apply]
  by_cases hnij : n + i + j = 2 * d
  · have hmap := GG.map_eq_map_decompose
      ((applyₗ (x ⊗ₜ[R] y)).comp (traceTensorEquiv ε).toLinearMap).toAddMonoidHom
      (i := n)
      (fun m u hu hmn ↦ traceTensorEquiv_eq_zero_of_mem_piece G ε hε hu hx hy (by omega))
      ((ε.frobeniusCoalgebra).comul a)
    simp only [toAddMonoidHom_coe, comp_apply, LinearEquiv.coe_coe,
      applyₗ_apply_apply] at hmap
    rw [← hmap, traceTensorEquiv_frobeniusCoalgebra_comul]
    exact G.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero hε'
      (SetLike.mul_mem_graded ha (SetLike.mul_mem_graded hx hy)) (by omega)
  · exact traceTensorEquiv_eq_zero_of_mem_piece G ε hε
      (DirectSum.decompose GG.piece ((ε.frobeniusCoalgebra).comul a) n).2 hx hy hnij

/-- If a perfect trace `ε` on a finite projective graded commutative algebra `A` has degree `-d`,
then the handle element of `ε.frobeniusCoalgebra` lies in degree `d`. -/
theorem frobeniusCoalgebra_handle_mem_piece {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    (letI := ε.frobeniusCoalgebra; TauCeti.Coalgebra.handle R A) ∈ G.piece d := by
  let := ε.frobeniusCoalgebra
  rw [TauCeti.Coalgebra.handle_def]
  have h1 : (1 : A) ∈ G.piece 0 := SetLike.one_mem_graded G.piece
  have hcomul := (isHomogeneous_frobeniusCoalgebra_comul G ε hε).map_mem h1
  simpa using (G.isHomogeneous_mul').map_mem hcomul

omit [Module.Finite R A] [Module.Projective R A] in
/-- For a homogeneous finite basis `b` with `b i ∈ G.piece (deg i)` and a perfect trace `ε` of
degree `-d` on a graded commutative algebra `A`, the trace-dual vector `ε.traceDualBasis b i` lies
in degree `d - deg i`. -/
theorem traceDualBasis_mem_piece {ι : Type*} [Finite ι] (b : Module.Basis ι R A) (deg : ι → ℤ)
    (hb : ∀ i, b i ∈ G.piece (deg i)) {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) (i : ι) :
    ε.traceDualBasis b i ∈ G.piece (d - deg i) := by
  classical
  have hε' := (G.isHomogeneous_trivialGrading_iff_mem_dualPiece ε (-d)).mp hε
  refine G.mem_piece_of_decompose_eq_zero fun m hm ↦ ?_
  apply ((mul R A).compr₂ ε).toPerfPair.injective
  rw [map_zero]
  refine b.ext fun j ↦ ?_
  simp only [toLinearMap_toPerfPair, compr₂_apply, mul_apply_apply, _root_.LinearMap.zero_apply]
  by_cases hmj : m + deg j = d
  · have hmap := G.map_eq_map_decompose (ε.comp (mulRight R (b j))).toAddMonoidHom (i := m)
      (fun k u hu hkm ↦ G.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero hε'
        (SetLike.mul_mem_graded hu (hb j)) (by omega))
      (ε.traceDualBasis b i)
    simp only [toAddMonoidHom_coe, comp_apply, mulRight_apply] at hmap
    rw [← hmap, traceDualBasis_mul, Module.Basis.repr_self, Finsupp.single_apply]
    have hij : j ≠ i := fun h ↦ by subst h; omega
    simp [hij]
  · exact G.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero hε'
      (SetLike.mul_mem_graded
        (DirectSum.decompose G.piece (ε.traceDualBasis b i) m).2 (hb j)) (by omega)

end Core

end LinearMap

namespace TauCeti.Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [_root_.Coalgebra R A] [_root_.Coalgebra.IsFrobenius R A]
  (G : InternalGrading R A ℤ) [SetLike.GradedMonoid G.piece]

/-- In any commutative Frobenius coalgebra whose counit has degree `-d`, comultiplication has
degree `d`. -/
theorem isHomogeneous_comul {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (CoalgebraStruct.counit (R := R))
      G.piece (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (CoalgebraStruct.comul (R := R))
      G.piece (G.tensorProduct G).piece d := by
  have h := LinearMap.isHomogeneous_frobeniusCoalgebra_comul G
    (CoalgebraStruct.counit (R := R) (A := A)) hε
  rwa [frobeniusCoalgebra_counit_eq] at h

/-- In any commutative Frobenius coalgebra whose counit has degree `-d`, the handle element lies in
degree `d`. -/
theorem handle_mem_piece {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (CoalgebraStruct.counit (R := R))
      G.piece (trivialGrading R R) (-d)) :
    TauCeti.Coalgebra.handle R A ∈ G.piece d := by
  have h := LinearMap.frobeniusCoalgebra_handle_mem_piece G
    (CoalgebraStruct.counit (R := R) (A := A)) hε
  rwa [frobeniusCoalgebra_counit_eq] at h

end TauCeti.Coalgebra.IsFrobenius

section Operations

namespace AlgEquiv

section Semiring

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- The inverse of a degree-`0` algebra equivalence between internally graded `R`-algebras is
homogeneous of degree `0`. -/
theorem isHomogeneous_symm {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (f : A ≃ₐ[R] B) (GA : InternalGrading R A ι) (GB : InternalGrading R B ι)
    (hf : TauCeti.LinearMap.IsHomogeneous f.toLinearMap GA.piece GB.piece 0) :
    TauCeti.LinearMap.IsHomogeneous f.symm.toLinearMap GB.piece GA.piece 0 := by
  rw [← f.symm.toLinearEquiv_toLinearMap, f.toLinearEquiv_symm]
  rw [← f.toLinearEquiv_toLinearMap] at hf
  exact hf.linearEquiv_symm

/-- A degree-`0` algebra equivalence `f : A ≃ₐ[R] B` intertwining `ψ (f a) = φ a` transports
homogeneity of `φ` into any target grading `L` to `ψ`. -/
theorem isHomogeneous_of_apply_eq {ι P σP : Type*} [DecidableEq ι] [AddMonoid ι]
    [AddCommMonoid P] [Module R P] [SetLike σP P]
    (f : A ≃ₐ[R] B) (GA : InternalGrading R A ι) (GB : InternalGrading R B ι)
    {L : ι → σP} {φ : A →ₗ[R] P} {ψ : B →ₗ[R] P}
    (hfG : TauCeti.LinearMap.IsHomogeneous f.toLinearMap GA.piece GB.piece 0)
    (hfφ : ∀ a, ψ (f a) = φ a) {d : ι}
    (hφ : TauCeti.LinearMap.IsHomogeneous φ GA.piece L d) :
    TauCeti.LinearMap.IsHomogeneous ψ GB.piece L d :=
  f.toLinearEquiv.isHomogeneous_of_apply_eq GA GB (by rwa [f.toLinearEquiv_toLinearMap]) hfφ hφ

end Semiring

section CommSemiring

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

/-- If `f : A ≃ₐ[R] B` is homogeneous of degree `0` between finite projective commutative
`R`-algebras and intertwines perfect traces, then the forward direction of `f.frobeniusCoalgEquiv`
is homogeneous of degree `0`. -/
theorem isHomogeneous_frobeniusCoalgEquiv (f : A ≃ₐ[R] B)
    (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ)
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hfG : TauCeti.LinearMap.IsHomogeneous f.toLinearMap GA.piece GB.piece 0)
    (hfε : ∀ a, εB (f a) = εA a) :
    (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
      TauCeti.LinearMap.IsHomogeneous (f.frobeniusCoalgEquiv εA εB hfε).toLinearMap
        GA.piece GB.piece 0) := by
  rw [f.toLinearMap_frobeniusCoalgEquiv]
  exact hfG

/-- If `f : A ≃ₐ[R] B` is homogeneous of degree `0` between finite projective commutative
`R`-algebras and intertwines perfect traces, then the inverse of `f.frobeniusCoalgEquiv` is
homogeneous of degree `0`. -/
theorem isHomogeneous_frobeniusCoalgEquiv_symm (f : A ≃ₐ[R] B)
    (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ)
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hfG : TauCeti.LinearMap.IsHomogeneous f.toLinearMap GA.piece GB.piece 0)
    (hfε : ∀ a, εB (f a) = εA a) :
    (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
      TauCeti.LinearMap.IsHomogeneous (f.frobeniusCoalgEquiv εA εB hfε).symm.toLinearMap
        GB.piece GA.piece 0) := by
  rw [f.symm_frobeniusCoalgEquiv, f.symm.toLinearMap_frobeniusCoalgEquiv]
  exact f.isHomogeneous_symm GA GB hfG

end CommSemiring

end AlgEquiv

namespace LinearMap

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]
  (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ)
  [SetLike.GradedMonoid GA.piece] [SetLike.GradedMonoid GB.piece]

/-- For finite projective graded commutative algebras with perfect traces of degrees `-dA` and
`-dB`, the tensor-product Frobenius coproduct has degree `dA + dB`. -/
theorem isHomogeneous_frobeniusCoalgebra_comul_dualDistrib_tmul
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair] {dA dB : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous εA GA.piece (trivialGrading R R) (-dA))
    (hB : TauCeti.LinearMap.IsHomogeneous εB GB.piece (trivialGrading R R) (-dB)) :
    TauCeti.LinearMap.IsHomogeneous
      ((TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra).comul
      (GA.tensorProduct GB).piece
      ((GA.tensorProduct GB).tensorProduct (GA.tensorProduct GB)).piece (dA + dB) :=
  isHomogeneous_frobeniusCoalgebra_comul (GA.tensorProduct GB) _
    (by simpa only [neg_add] using GA.isHomogeneous_dualDistrib_tmul GB hA hB)

/-- For finite projective graded commutative algebras with perfect traces of degrees `-dA` and
`-dB`, the tensor-product handle element lies in total degree `dA + dB`. -/
theorem frobeniusCoalgebra_handle_dualDistrib_tmul_mem_piece
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair] {dA dB : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous εA GA.piece (trivialGrading R R) (-dA))
    (hB : TauCeti.LinearMap.IsHomogeneous εB GB.piece (trivialGrading R R) (-dB)) :
    (letI := (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra;
      TauCeti.Coalgebra.handle R (A ⊗[R] B)) ∈ (GA.tensorProduct GB).piece (dA + dB) :=
  frobeniusCoalgebra_handle_mem_piece (GA.tensorProduct GB) _
    (by simpa only [neg_add] using GA.isHomogeneous_dualDistrib_tmul GB hA hB)

end TensorProduct

section BaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring A] [Algebra R A] (G : InternalGrading R A ℤ)
  [Module.Finite R A] [Module.Projective R A] [SetLike.GradedMonoid G.piece]

/-- Scalar extension of a finite projective graded commutative algebra with perfect trace of degree
`-d` along an ungraded commutative `R`-algebra `S` produces a graded Frobenius coalgebra over `S`
whose coproduct has degree `d`. -/
theorem isHomogeneous_frobeniusCoalgebra_comul_baseChange
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous ((Module.Dual.baseChange S ε).frobeniusCoalgebra).comul
      (G.baseChange S).piece ((G.baseChange S).tensorProduct (G.baseChange S)).piece d :=
  isHomogeneous_frobeniusCoalgebra_comul (G.baseChange S) _ (G.isHomogeneous_dualBaseChange S hε)

/-- Under scalar extension along an ungraded commutative `R`-algebra `S`, the handle element of a
degree-`-d` perfect trace on a finite projective graded commutative `R`-algebra `A` lies in degree
`d` of `G.baseChange S`. -/
theorem frobeniusCoalgebra_handle_baseChange_mem_piece
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    (letI := (Module.Dual.baseChange S ε).frobeniusCoalgebra;
      TauCeti.Coalgebra.handle S (S ⊗[R] A)) ∈ (G.baseChange S).piece d :=
  frobeniusCoalgebra_handle_mem_piece (G.baseChange S) _ (G.isHomogeneous_dualBaseChange S hε)

variable {S}

/-- When a commutative `R`-algebra `S` carries a graded monoid `GS` over `R` and `ε` has degree
`-d` on a finite projective graded commutative `R`-algebra `A`, the base-changed handle element in
`S ⊗[R] A` lies in total degree `d` of `GS.tensorProduct G`. -/
theorem frobeniusCoalgebra_handle_baseChange_mem_tensorProduct_piece
    (GS : InternalGrading R S ℤ) [SetLike.GradedMonoid GS.piece]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    (letI := (Module.Dual.baseChange S ε).frobeniusCoalgebra;
      TauCeti.Coalgebra.handle S (S ⊗[R] A)) ∈ (GS.tensorProduct G).piece d := by
  rw [frobeniusCoalgebra_handle_baseChange S ε]
  simpa using InternalGrading.tmul_mem_tensorProduct GS G
    (SetLike.one_mem_graded GS.piece) (frobeniusCoalgebra_handle_mem_piece G ε hε)

end BaseChange

end LinearMap

end Operations

end
