/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Transport
public import TauCeti.Algebra.Module.GradedModule.BaseChange
public import TauCeti.Algebra.Module.GradedModule.Dual.TensorProduct
public import TauCeti.Algebra.Module.GradedModule.Trivial

/-!
# Graded commutative Frobenius algebras

A commutative graded `R`-algebra `A` equipped with an internal `ℤ`-grading `G` and a perfect trace
`ε : A →ₗ[R] R` of degree `-d` (meaning `ε` vanishes outside degree `d`, i.e.
`ε ∈ G.dualPiece (-d)`) carries a graded Frobenius coalgebra structure over an arbitrary
commutative semiring `R`:

* multiplication `m : A ⊗[R] A →ₗ[R] A` and unit `η : R →ₗ[R] A` have degree `0`;
* the reconstructed coproduct `Δ : A →ₗ[R] A ⊗[R] A` automatically has degree `d`, without
  requiring additive inverses in `R` or existence of a homogeneous basis;
* the handle element `m (Δ 1)` is homogeneous of degree `d`;
* for any finite homogeneous basis `b` with `b i ∈ G.piece (deg i)`, the trace-dual basis satisfies
  `ε.traceDualBasis b i ∈ G.piece (d - deg i)`.

When `A` and `B` have even-supported gradings (`parityGrading G.piece 1 = ⊥`, so all odd-degree
pieces vanish), Koszul signs are trivial and the ordinary tensor product `A ⊗[R] B`, degree-`0`
trace-preserving algebra equivalences, and scalar extensions `S ⊗[R] A` (both for ungraded `S` via
`G.baseChange S` and for even-supported graded `S` via `GS.tensorProduct G`) preserve even support
and shift degrees additively (in particular when `d = 2 * c`).

## Main results

* `TauCeti.InternalGrading.isHomogeneous_trivialGrading_iff_mem_dualPiece`: a linear functional is
  homogeneous of degree `p` into `trivialGrading R R` iff it lies in `G.dualPiece p`.
* `TauCeti.parityGrading_one_eq_bot_iff`,
  `TauCeti.InternalGrading.parityGrading_tensorProduct_one_eq_bot`:
  characterization of even support and closure under tensor products.
* `TauCeti.InternalGrading.instGradedMonoidTensorProduct`,
  `TauCeti.InternalGrading.isHomogeneous_tensorTensorTensorComm`: graded monoid structure on
  `A ⊗[R] B` and degree-`0` homogeneity of the middle-four-exchange isomorphism.
* `LinearMap.isHomogeneous_frobeniusCoalgebra_comul`,
  `LinearMap.frobeniusCoalgebra_handle_mem_piece`,
  `LinearMap.traceDualBasis_mem_piece`: degree of the reconstructed coproduct, handle element, and
  trace-dual basis.
* `Coalgebra.IsFrobenius.isHomogeneous_comul`, `Coalgebra.IsFrobenius.handle_mem_piece`: the same
  degree laws for any commutative Frobenius coalgebra whose counit has degree `-d`.
* `AlgEquiv.isHomogeneous_frobeniusCoalgEquiv`,
  `AlgEquiv.isHomogeneous_frobeniusCoalgEquiv_symm`,
  `AlgEquiv.isHomogeneous_trace_of_algEquiv`,
  `LinearMap.isHomogeneous_dualDistrib_tmul`, `LinearMap.isHomogeneous_dualBaseChange`,
  `LinearMap.isHomogeneous_restrictScalars_dualBaseChange`: graded compatibility with transport,
  tensor products, and scalar extension.

## References

* M. Khovanov, *Link homology and Frobenius extensions*, Fund. Math. 190 (2006), 179–190.
* A. D. Lauda and H. Pfeiffer, *Open-closed TQFTs extend Khovanov homology to tangles in surfaces*,
  J. Knot Theory Ramifications 18 (2009).
-/

public section

noncomputable section

open TensorProduct TauCeti

namespace TauCeti

section Parity

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An integer-indexed family of submodules is supported in even degrees (`parityGrading ℳ 1 = ⊥`)
iff every odd-degree piece `ℳ (2 * k + 1)` vanishes. -/
theorem parityGrading_one_eq_bot_iff (ℳ : ℤ → Submodule R M) :
    parityGrading ℳ 1 = ⊥ ↔ ∀ k : ℤ, ℳ (2 * k + 1) = ⊥ := by
  rw [parityGrading_one, iSup_eq_bot]

/-- Transporting an integer grading along a degree-`0` linear equivalence preserves even support. -/
theorem parityGrading_one_eq_bot_of_linearEquiv {N : Type*} [AddCommMonoid N] [Module R N]
    {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} (e : M ≃ₗ[R] N)
    (he : LinearMap.IsHomogeneous e.symm.toLinearMap 𝒩 ℳ 0) (hM : parityGrading ℳ 1 = ⊥) :
    parityGrading 𝒩 1 = ⊥ := by
  rw [parityGrading_one_eq_bot_iff] at hM ⊢
  intro k
  rw [Submodule.eq_bot_iff]
  intro y hy
  have h0 : e.symm y ∈ ℳ (2 * k + 1) := by simpa using he.map_mem hy
  rw [hM k, Submodule.mem_bot] at h0
  exact e.symm.injective (by simpa using h0)

end Parity

namespace InternalGrading

section TensorAndDual

variable {R : Type*} [CommSemiring R]

/-- A functional `φ : M →ₗ[R] R` is homogeneous of degree `p` into the trivial grading on `R` iff
it belongs to `G.dualPiece p`. -/
@[simp]
theorem isHomogeneous_trivialGrading_iff_mem_dualPiece {M : Type*} [AddCommMonoid M] [Module R M]
    (G : InternalGrading R M ℤ) (φ : Module.Dual R M) (p : ℤ) :
    LinearMap.IsHomogeneous φ G.piece (trivialGrading R R) p ↔ φ ∈ G.dualPiece p := by
  rw [LinearMap.isHomogeneous_def, mem_dualPiece_iff]
  refine ⟨fun h q x hx hq ↦ ?_, fun h q x hx ↦ ?_⟩
  · exact (mem_trivialGrading_iff R R).mp (h q x hx) |>.resolve_left (by omega)
  · rw [mem_trivialGrading_iff]
    by_cases hq : q + p = 0
    · exact Or.inl hq
    · exact Or.inr (h q x hx (by omega))

/-- Even support is preserved under tensor products of internally `ℤ`-graded modules. -/
theorem parityGrading_tensorProduct_one_eq_bot {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ)
    (hG : parityGrading G.piece 1 = ⊥) (hH : parityGrading H.piece 1 = ⊥) :
    parityGrading (G.tensorProduct H).piece 1 = ⊥ := by
  rw [parityGrading_one_eq_bot_iff] at hG hH ⊢
  intro k
  rw [← le_bot_iff]
  refine G.tensorProduct_piece_le H fun p x hx y hy ↦ ?_
  have hparity : p = 2 * (p / 2) + 1 ∨ 2 * k + 1 - p = 2 * ((2 * k + 1 - p) / 2) + 1 := by omega
  rcases hparity with hp | hq
  · rw [hp, hG, Submodule.mem_bot] at hx
    simp [hx]
  · rw [hq, hH, Submodule.mem_bot] at hy
    simp [hy]

/-- Ordinary tensor product of two internally `ℤ`-graded algebras is a graded monoid for the
total-degree grading. -/
instance instGradedMonoidTensorProduct {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ)
    [SetLike.GradedMonoid GA.piece] [SetLike.GradedMonoid GB.piece] :
    SetLike.GradedMonoid (GA.tensorProduct GB).piece where
  one_mem := by
    simpa [Algebra.TensorProduct.one_def] using
      tmul_mem_tensorProduct GA GB (SetLike.one_mem_graded GA.piece)
        (SetLike.one_mem_graded GB.piece)
  mul_mem i j u v hu hv := by
    refine GA.tensorProduct_piece_le GB
      (C := ((GA.tensorProduct GB).piece (i + j)).comap
        ((_root_.LinearMap.mul R (A ⊗[R] B)).flip v))
      (fun p a₁ ha₁ b₁ hb₁ ↦ ?_) hu
    refine GA.tensorProduct_piece_le GB
      (C := ((GA.tensorProduct GB).piece (i + j)).comap
        (_root_.LinearMap.mul R (A ⊗[R] B) (a₁ ⊗ₜ[R] b₁)))
      (fun q a₂ ha₂ b₂ hb₂ ↦ ?_) hv
    simp only [Submodule.mem_comap, _root_.LinearMap.mul_apply_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
    have hdeg : i + j = (p + q) + ((i - p) + (j - q)) := by omega
    rw [hdeg]
    exact tmul_mem_tensorProduct GA GB
      (SetLike.mul_mem_graded ha₁ ha₂) (SetLike.mul_mem_graded hb₁ hb₂)

/-- Multiplication on an internally `ℤ`-graded algebra has degree `0` for the total-degree grading
on `A ⊗[R] A`. -/
theorem isHomogeneous_mul' {A : Type*} [Semiring A] [Algebra R A]
    (G : InternalGrading R A ℤ) [SetLike.GradedMonoid G.piece] :
    LinearMap.IsHomogeneous (_root_.LinearMap.mul' R A) (G.tensorProduct G).piece G.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine G.tensorProduct_piece_le G
    (C := (G.piece (n + 0)).comap (_root_.LinearMap.mul' R A))
    (fun p a ha b hb ↦ ?_) hz
  simp only [Submodule.mem_comap, _root_.LinearMap.mul'_apply]
  have hdeg : n + 0 = p + (n - p) := by omega
  rw [hdeg]
  exact SetLike.mul_mem_graded ha hb

/-- The unit map `η : R →ₗ[R] A` of an internally `ℤ`-graded algebra has degree `0`. -/
theorem isHomogeneous_algebraLinearMap {A : Type*} [Semiring A] [Algebra R A]
    (G : InternalGrading R A ℤ) [SetLike.GradedMonoid G.piece] :
    LinearMap.IsHomogeneous (Algebra.linearMap R A) (trivialGrading R R) G.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p r hr
  rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
  · simpa [Algebra.algebraMap_eq_smul_one] using
      Submodule.smul_mem _ r (SetLike.one_mem_graded G.piece)
  · simp

/-- The middle-four-exchange isomorphism `(M ⊗ N) ⊗ (P ⊗ Q) ≃ₗ (M ⊗ P) ⊗ (N ⊗ Q)` preserves total
degree. -/
theorem isHomogeneous_tensorTensorTensorComm {M N P Q : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
    (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ)
    (GP : InternalGrading R P ℤ) (GQ : InternalGrading R Q ℤ) :
    LinearMap.IsHomogeneous (TensorProduct.tensorTensorTensorComm R M N P Q).toLinearMap
      ((GM.tensorProduct GN).tensorProduct (GP.tensorProduct GQ)).piece
      ((GM.tensorProduct GP).tensorProduct (GN.tensorProduct GQ)).piece 0 := by
  let F := (TensorProduct.tensorTensorTensorComm R M N P Q).toLinearMap
  let T := (GM.tensorProduct GP).tensorProduct (GN.tensorProduct GQ)
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (GM.tensorProduct GN).tensorProduct_piece_le (GP.tensorProduct GQ)
    (C := (T.piece (n + 0)).comap F) (fun p u hu v hv ↦ ?_) hz
  refine GM.tensorProduct_piece_le GN
    (C := (T.piece (n + 0)).comap (F ∘ₗ (TensorProduct.mk R _ _).flip v))
    (fun i m hm k hk ↦ ?_) hu
  refine GP.tensorProduct_piece_le GQ
    (C := (T.piece (n + 0)).comap (F ∘ₗ TensorProduct.mk R _ _ (m ⊗ₜ[R] k)))
    (fun j x hx y hy ↦ ?_) hv
  simp only [Submodule.mem_comap, _root_.LinearMap.comp_apply, TensorProduct.mk_apply, F,
    LinearEquiv.coe_coe, TensorProduct.tensorTensorTensorComm_tmul]
  have hdeg : n + 0 = (i + j) + ((p - i) + (n - p - j)) := by omega
  rw [hdeg]
  exact tmul_mem_tensorProduct _ _
    (tmul_mem_tensorProduct GM GP hm hx) (tmul_mem_tensorProduct GN GQ hk hy)

end TensorAndDual

end InternalGrading

end TauCeti

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
      · have h2 : ε (b₂ * y) = 0 :=
          (InternalGrading.mem_dualPiece_iff G (-d) ε).mp hε' (m - q + j) (b₂ * y)
            (SetLike.mul_mem_graded hb₂ hy) (by omega)
        rw [h2, mul_zero]
      · have h1 : ε (b₁ * x) = 0 :=
          (InternalGrading.mem_dualPiece_iff G (-d) ε).mp hε' (q + i) (b₁ * x)
            (SetLike.mul_mem_graded hb₁ hx) (by omega)
        rw [h1, zero_mul]
  exact hle hu

/-- If a perfect trace `ε` on a finite projective graded commutative algebra `A` has degree `-d`,
then the reconstructed Frobenius coproduct `Δ` has degree `d`. -/
theorem isHomogeneous_frobeniusCoalgebra_comul {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (ε.frobeniusCoalgebra).comul
      G.piece (G.tensorProduct G).piece d := by
  classical
  let GG := G.tensorProduct G
  have hε' := (G.isHomogeneous_trivialGrading_iff_mem_dualPiece ε (-d)).mp hε
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p a ha
  have hzero (n : ℤ) (hn : n ≠ p + d) :
      (DirectSum.decompose GG.piece ((ε.frobeniusCoalgebra).comul a) n : A ⊗[R] A) = 0 := by
    apply (traceTensorEquiv ε).injective
    rw [map_zero]
    refine TensorProduct.ext (G.linearMap_ext fun i x hx ↦ G.linearMap_ext fun j y hy ↦ ?_)
    simp only [compr₂ₛₗ_apply, TensorProduct.mk_apply]
    by_cases hnij : n + i + j = 2 * d
    · have htotal : traceTensorEquiv ε ((ε.frobeniusCoalgebra).comul a) (x ⊗ₜ[R] y) = 0 := by
        rw [traceTensorEquiv_frobeniusCoalgebra_comul]
        exact (InternalGrading.mem_dualPiece_iff G (-d) ε).mp hε' (p + (i + j)) (a * (x * y))
          (SetLike.mul_mem_graded ha (SetLike.mul_mem_graded hx hy)) (by omega)
      conv_lhs at htotal =>
        rw [← DirectSum.sum_support_decompose GG.piece ((ε.frobeniusCoalgebra).comul a)]
      rw [map_sum, LinearMap.sum_apply] at htotal
      by_cases hnsupp : n ∈ (DirectSum.decompose GG.piece ((ε.frobeniusCoalgebra).comul a)).support
      · rw [Finset.sum_eq_single n] at htotal
        · exact htotal
        · intro m _ hmn
          exact traceTensorEquiv_eq_zero_of_mem_piece G ε hε
            (DirectSum.decompose GG.piece ((ε.frobeniusCoalgebra).comul a) m).2 hx hy (by omega)
        · intro habs
          exact absurd hnsupp habs
      · have hun :
            (DirectSum.decompose GG.piece ((ε.frobeniusCoalgebra).comul a) n : A ⊗[R] A) = 0 := by
          simpa [DFinsupp.mem_support_toFun] using hnsupp
        simp [hun]
    · exact traceTensorEquiv_eq_zero_of_mem_piece G ε hε
        (DirectSum.decompose GG.piece ((ε.frobeniusCoalgebra).comul a) n).2 hx hy hnij
  rw [← DirectSum.sum_support_decompose GG.piece ((ε.frobeniusCoalgebra).comul a)]
  refine Submodule.sum_mem _ fun n _ ↦ ?_
  by_cases hn : n = p + d
  · subst hn
    exact (DirectSum.decompose GG.piece ((ε.frobeniusCoalgebra).comul a) (p + d)).2
  · rw [hzero n hn]
    exact zero_mem _

/-- If a perfect trace `ε` has degree `-d`, then the handle element of `ε.frobeniusCoalgebra` lies
in degree `d`. -/
theorem frobeniusCoalgebra_handle_mem_piece {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    (letI := ε.frobeniusCoalgebra; Coalgebra.handle R A) ∈ G.piece d := by
  let := ε.frobeniusCoalgebra
  rw [Coalgebra.handle_def]
  have h1 : (1 : A) ∈ G.piece 0 := SetLike.one_mem_graded G.piece
  have hcomul := (isHomogeneous_frobeniusCoalgebra_comul G ε hε).map_mem h1
  simpa using (G.isHomogeneous_mul').map_mem hcomul

omit [Module.Finite R A] [Module.Projective R A] in
/-- For a homogeneous finite basis `b` with `b i ∈ G.piece (deg i)` and a perfect trace `ε` of
degree `-d`, the trace-dual vector `ε.traceDualBasis b i` lies in degree `d - deg i`. -/
theorem traceDualBasis_mem_piece {ι : Type*} [Finite ι] (b : Module.Basis ι R A) (deg : ι → ℤ)
    (hb : ∀ i, b i ∈ G.piece (deg i)) {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) (i : ι) :
    ε.traceDualBasis b i ∈ G.piece (d - deg i) := by
  classical
  have hε' := (G.isHomogeneous_trivialGrading_iff_mem_dualPiece ε (-d)).mp hε
  have hzero (m : ℤ) (hm : m ≠ d - deg i) :
      (DirectSum.decompose G.piece (ε.traceDualBasis b i) m : A) = 0 := by
    apply ((mul R A).compr₂ ε).toPerfPair.injective
    rw [map_zero]
    refine b.ext fun j ↦ ?_
    simp only [toLinearMap_toPerfPair, compr₂_apply, mul_apply_apply, _root_.LinearMap.zero_apply]
    by_cases hmj : m + deg j = d
    · have htotal : ε (ε.traceDualBasis b i * b j) = 0 := by
        rw [traceDualBasis_mul, Module.Basis.repr_self, Finsupp.single_apply]
        have hij : j ≠ i := fun h ↦ by subst h; omega
        simp [hij]
      conv_lhs at htotal => rw [← DirectSum.sum_support_decompose G.piece (ε.traceDualBasis b i)]
      rw [Finset.sum_mul, map_sum] at htotal
      by_cases hmsupp : m ∈ (DirectSum.decompose G.piece (ε.traceDualBasis b i)).support
      · rw [Finset.sum_eq_single m] at htotal
        · exact htotal
        · intro k _ hkm
          exact (InternalGrading.mem_dualPiece_iff G (-d) ε).mp hε' (k + deg j) _
            (SetLike.mul_mem_graded
              (DirectSum.decompose G.piece (ε.traceDualBasis b i) k).2 (hb j)) (by omega)
        · intro habs
          exact absurd hmsupp habs
      · have hum : (DirectSum.decompose G.piece (ε.traceDualBasis b i) m : A) = 0 := by
          simpa [DFinsupp.mem_support_toFun] using hmsupp
        simp [hum]
    · exact (InternalGrading.mem_dualPiece_iff G (-d) ε).mp hε' (m + deg j) _
        (SetLike.mul_mem_graded
          (DirectSum.decompose G.piece (ε.traceDualBasis b i) m).2 (hb j)) (by omega)
  rw [← DirectSum.sum_support_decompose G.piece (ε.traceDualBasis b i)]
  refine Submodule.sum_mem _ fun m _ ↦ ?_
  by_cases hm : m = d - deg i
  · subst hm
    exact (DirectSum.decompose G.piece (ε.traceDualBasis b i) (d - deg i)).2
  · rw [hzero m hm]
    exact zero_mem _

omit [SetLike.GradedMonoid G.piece] [Module.Finite R A] [Module.Projective R A]
  [((mul R A).compr₂ ε).IsPerfPair] in
/-- Over a nontrivial base semiring, every vector in a homogeneous basis of an even-supported
graded module has even degree. -/
theorem even_deg_of_parityGrading_one_eq_bot [Nontrivial R] {ι : Type*} (b : Module.Basis ι R A)
    (deg : ι → ℤ) (hb : ∀ i, b i ∈ G.piece (deg i)) (heven : parityGrading G.piece 1 = ⊥)
    (i : ι) : Even (deg i) := by
  by_contra hodd
  obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hodd
  have hmem : b i ∈ G.piece (2 * k + 1) := hk ▸ hb i
  rw [(parityGrading_one_eq_bot_iff G.piece).mp heven k, Submodule.mem_bot] at hmem
  exact b.ne_zero i hmem

end Core

end LinearMap

namespace Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Coalgebra R A] [IsFrobenius R A]
  (G : InternalGrading R A ℤ) [SetLike.GradedMonoid G.piece]

/-- In any commutative Frobenius coalgebra whose counit has degree `-d`, comultiplication has
degree `d`. -/
theorem isHomogeneous_comul {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R))
      G.piece (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R))
      G.piece (G.tensorProduct G).piece d := by
  have h := LinearMap.isHomogeneous_frobeniusCoalgebra_comul G
    (Coalgebra.counit (R := R) (A := A)) hε
  rwa [frobeniusCoalgebra_counit_eq] at h

/-- In any commutative Frobenius coalgebra whose counit has degree `-d`, the handle element lies in
degree `d`. -/
theorem handle_mem_piece {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R))
      G.piece (trivialGrading R R) (-d)) :
    Coalgebra.handle R A ∈ G.piece d := by
  have h := LinearMap.frobeniusCoalgebra_handle_mem_piece G
    (Coalgebra.counit (R := R) (A := A)) hε
  rwa [frobeniusCoalgebra_counit_eq] at h

end Coalgebra.IsFrobenius

section Operations

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

/-- If `f : A ≃ₐ[R] B` is homogeneous of degree `0` and intertwines perfect traces, then the
forward direction of `f.frobeniusCoalgEquiv` is homogeneous of degree `0`. -/
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

/-- If `f : A ≃ₐ[R] B` is homogeneous of degree `0` and intertwines perfect traces, then the
inverse of `f.frobeniusCoalgEquiv` is homogeneous of degree `0`. -/
theorem isHomogeneous_frobeniusCoalgEquiv_symm (f : A ≃ₐ[R] B)
    (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ)
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hfG : TauCeti.LinearMap.IsHomogeneous f.toLinearMap GA.piece GB.piece 0)
    (hfε : ∀ a, εB (f a) = εA a) :
    (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
      TauCeti.LinearMap.IsHomogeneous (f.frobeniusCoalgEquiv εA εB hfε).symm.toLinearMap
        GB.piece GA.piece 0) := by
  have hfG' : TauCeti.LinearMap.IsHomogeneous f.toLinearEquiv.toLinearMap GA.piece GB.piece 0 :=
    hfG
  rw [f.symm_frobeniusCoalgEquiv, f.symm.toLinearMap_frobeniusCoalgEquiv]
  exact hfG'.linearEquiv_symm

omit [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B] in
/-- A degree-`0` algebra equivalence intertwining `εA` and `εB` transports the trace degree from
`εA` to `εB`. -/
theorem isHomogeneous_trace_of_algEquiv (f : A ≃ₐ[R] B)
    (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ)
    {εA : A →ₗ[R] R} {εB : B →ₗ[R] R}
    (hfG : TauCeti.LinearMap.IsHomogeneous f.toLinearMap GA.piece GB.piece 0)
    (hfε : ∀ a, εB (f a) = εA a) {d : ℤ}
    (hεA : TauCeti.LinearMap.IsHomogeneous εA GA.piece (trivialGrading R R) d) :
    TauCeti.LinearMap.IsHomogeneous εB GB.piece (trivialGrading R R) d := by
  have hfG' : TauCeti.LinearMap.IsHomogeneous f.toLinearEquiv.toLinearMap GA.piece GB.piece 0 :=
    hfG
  have hεB : εB = εA ∘ₗ f.symm.toLinearMap := by
    ext b
    simpa using hfε (f.symm b)
  rw [hεB]
  simpa using hεA.comp hfG'.linearEquiv_symm

end AlgEquiv

namespace LinearMap

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]
  (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ)

/-- Tensoring functionals of degrees `-dA` and `-dB` produces a functional of degree `-(dA + dB)`
on `A ⊗[R] B`. -/
theorem isHomogeneous_dualDistrib_tmul {εA : A →ₗ[R] R} {εB : B →ₗ[R] R} {dA dB : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous εA GA.piece (trivialGrading R R) (-dA))
    (hB : TauCeti.LinearMap.IsHomogeneous εB GB.piece (trivialGrading R R) (-dB)) :
    TauCeti.LinearMap.IsHomogeneous (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))
      (GA.tensorProduct GB).piece (trivialGrading R R) (-(dA + dB)) := by
  rw [InternalGrading.isHomogeneous_trivialGrading_iff_mem_dualPiece] at hA hB ⊢
  have h := GA.dualDistrib_tmul_mem_dualPiece GB hA hB
  have hdeg : -dA + -dB = -(dA + dB) := by omega
  rwa [hdeg] at h

/-- For finite projective graded commutative algebras with perfect traces of degrees `-dA` and
`-dB`, the tensor-product Frobenius coproduct has degree `dA + dB`. -/
theorem isHomogeneous_frobeniusCoalgebra_comul_dualDistrib_tmul
    [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]
    [SetLike.GradedMonoid GA.piece] [SetLike.GradedMonoid GB.piece]
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair] {dA dB : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous εA GA.piece (trivialGrading R R) (-dA))
    (hB : TauCeti.LinearMap.IsHomogeneous εB GB.piece (trivialGrading R R) (-dB)) :
    (letI := isPerfPair_compr₂_mul_dualDistrib_tmul εA εB;
      TauCeti.LinearMap.IsHomogeneous
        ((TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra).comul
        (GA.tensorProduct GB).piece
        ((GA.tensorProduct GB).tensorProduct (GA.tensorProduct GB)).piece (dA + dB)) := by
  let := isPerfPair_compr₂_mul_dualDistrib_tmul εA εB
  exact isHomogeneous_frobeniusCoalgebra_comul (GA.tensorProduct GB) _
    (isHomogeneous_dualDistrib_tmul GA GB hA hB)

/-- For finite projective graded commutative algebras with perfect traces of degrees `-dA` and
`-dB`, the tensor-product handle element lies in total degree `dA + dB`. -/
theorem frobeniusCoalgebra_handle_dualDistrib_tmul_mem_piece
    [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]
    [SetLike.GradedMonoid GA.piece] [SetLike.GradedMonoid GB.piece]
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair] {dA dB : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous εA GA.piece (trivialGrading R R) (-dA))
    (hB : TauCeti.LinearMap.IsHomogeneous εB GB.piece (trivialGrading R R) (-dB)) :
    (letI := isPerfPair_compr₂_mul_dualDistrib_tmul εA εB;
      letI := (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra;
      Coalgebra.handle R (A ⊗[R] B) ∈ (GA.tensorProduct GB).piece (dA + dB)) := by
  let := isPerfPair_compr₂_mul_dualDistrib_tmul εA εB
  exact frobeniusCoalgebra_handle_mem_piece (GA.tensorProduct GB) _
    (isHomogeneous_dualDistrib_tmul GA GB hA hB)

end TensorProduct

section BaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring A] [Algebra R A] (G : InternalGrading R A ℤ)

/-- Extending scalars of a degree-`-d` functional `ε : A →ₗ[R] R` along an ungraded commutative
`R`-algebra `S` gives an `S`-linear functional of degree `-d` for `G.baseChange S`. -/
theorem isHomogeneous_dualBaseChange {ε : A →ₗ[R] R} {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (Module.Dual.baseChange S ε)
      (G.baseChange S).piece (trivialGrading S S) (-d) := by
  rw [InternalGrading.isHomogeneous_trivialGrading_iff_mem_dualPiece] at hε ⊢
  exact G.dualBaseChange_mem_dualPiece S hε

/-- Scalar extension of a finite projective graded commutative algebra with perfect trace of degree
`-d` along an ungraded commutative `R`-algebra `S` produces a graded Frobenius coalgebra over `S`
whose coproduct has degree `d`. -/
theorem isHomogeneous_frobeniusCoalgebra_comul_baseChange
    [Module.Finite R A] [Module.Projective R A] [SetLike.GradedMonoid G.piece]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous ((Module.Dual.baseChange S ε).frobeniusCoalgebra).comul
      (G.baseChange S).piece ((G.baseChange S).tensorProduct (G.baseChange S)).piece d :=
  isHomogeneous_frobeniusCoalgebra_comul (G.baseChange S) _ (isHomogeneous_dualBaseChange S G hε)

/-- Under scalar extension along an ungraded commutative `R`-algebra `S`, the handle element of a
degree-`-d` perfect trace lies in degree `d` of `G.baseChange S`. -/
theorem frobeniusCoalgebra_handle_baseChange_mem_piece
    [Module.Finite R A] [Module.Projective R A] [SetLike.GradedMonoid G.piece]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    (letI := (Module.Dual.baseChange S ε).frobeniusCoalgebra;
      Coalgebra.handle S (S ⊗[R] A)) ∈ (G.baseChange S).piece d :=
  frobeniusCoalgebra_handle_mem_piece (G.baseChange S) _ (isHomogeneous_dualBaseChange S G hε)

variable {S}

/-- When `S` itself carries an internal `ℤ`-grading `GS` over `R`, the scalar-extended functional
`Module.Dual.baseChange S ε : S ⊗[R] A →ₗ[S] S` restricted to `R` has degree `-d` from
`(GS.tensorProduct G).piece` into `GS.piece`. -/
theorem isHomogeneous_restrictScalars_dualBaseChange
    (GS : InternalGrading R S ℤ) {ε : A →ₗ[R] R} {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous ((Module.Dual.baseChange S ε).restrictScalars R)
      (GS.tensorProduct G).piece GS.piece (-d) := by
  have hε' := (G.isHomogeneous_trivialGrading_iff_mem_dualPiece ε (-d)).mp hε
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro n z hz
  refine GS.tensorProduct_piece_le G
    (C := (GS.piece (n + -d)).comap ((Module.Dual.baseChange S ε).restrictScalars R))
    (fun p s hs a ha ↦ ?_) hz
  simp only [Submodule.mem_comap, coe_restrictScalars, Module.Dual.baseChange_apply_tmul]
  by_cases ha_deg : n - p = d
  · have hp : p = n + -d := by omega
    rw [← hp]
    exact Submodule.smul_mem _ (ε a) hs
  · rw [(InternalGrading.mem_dualPiece_iff G (-d) ε).mp hε' (n - p) a ha (by omega), zero_smul]
    exact zero_mem _

/-- When `S` carries a graded monoid `GS` over `R` and `ε` has degree `-d` on `A`, the base-changed
handle element in `S ⊗[R] A` lies in total degree `d` of `GS.tensorProduct G`. -/
theorem frobeniusCoalgebra_handle_baseChange_mem_tensorProduct_piece
    (GS : InternalGrading R S ℤ) [SetLike.GradedMonoid GS.piece]
    [Module.Finite R A] [Module.Projective R A] [SetLike.GradedMonoid G.piece]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε G.piece (trivialGrading R R) (-d)) :
    (letI := (Module.Dual.baseChange S ε).frobeniusCoalgebra;
      Coalgebra.handle S (S ⊗[R] A)) ∈ (GS.tensorProduct G).piece d := by
  rw [frobeniusCoalgebra_handle_baseChange S ε]
  simpa using InternalGrading.tmul_mem_tensorProduct GS G
    (SetLike.one_mem_graded GS.piece) (frobeniusCoalgebra_handle_mem_piece G ε hε)

end BaseChange

end LinearMap

end Operations

end
