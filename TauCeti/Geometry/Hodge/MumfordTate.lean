/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.MultiplicativeMatrix
public import TauCeti.Algebra.Bialgebra.GaloisDescent
public import TauCeti.FieldTheory.Galois.Complex
public import TauCeti.Geometry.Hodge.BaseChange
public import TauCeti.Geometry.Hodge.DeligneTorus

/-!
# The Mumford–Tate group of a rational Hodge structure

A pure Hodge structure of weight `n` on a complex vector space `W` with conjugation `ω` determines
a homomorphism of real algebraic groups `h : S → GL(W_ℝ)` from the Deligne torus
`S = Res_{ℂ/ℝ} 𝔾ₘ`. In the homology convention a point of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ` with coordinates
`(z₁, z₂)` acts on the Hodge component `H^{p,q}` by `z₁ ^ (-p) * z₂ ^ (-q)`, so a real point
`z ∈ S(ℝ) = ℂˣ` acts by `z ^ (-p) * conj z ^ (-q)`. This file constructs `h` on coordinate rings,
as a morphism of Hopf `ℝ`-algebras `O(GL_d)_ℝ → O(S)` in a basis of `W` fixed by `ω`, and for a
rational Hodge structure `V` defines its Mumford–Tate group as the Hopf ideal of `O(GL_V)` cutting
out the smallest closed `ℚ`-subgroup through whose real extension `h` factors.

The construction goes through `ℂ`. Over `ℂ` the coordinate ring of `S` is the group algebra
`ℂ[ℤ²]` (`TauCeti.DeligneTorus.splittingBialgEquiv`), and the action of `S_ℂ` is the matrix
`∑ p, P p * X^{(-p, p - n)}`, where `P p` is the matrix of the projection onto `H^{p,n-p}`.
Since the `P p` are orthogonal idempotents summing to the identity and the `X^{(a,b)}` are
group-like, this matrix is multiplicative, so it is a morphism `O(GL_d)_ℂ → ℂ[ℤ²]`
(`TauCeti.GeneralLinear.coordinateBialgHomOfMultiplicative`). Complex conjugation exchanges
`H^{p,q}` and `H^{q,p}`, which in a basis fixed by `ω` makes the matrix invariant under the
conjugation `TauCeti.DeligneTorus.conjSwap` of `ℂ[ℤ²]`; this is the real structure of `S`, so the
morphism descends to `ℝ` (`BialgHom.galoisDescend`).

## Main definitions

* `TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom`: the homomorphism `h : S → GL_d` over
  `ℝ` of a Hodge structure in a basis fixed by the conjugation, on coordinate rings.
* `TauCeti.Hodge.HodgeStructureOn.deligneHom`: for a rational Hodge structure with a basis of its
  rational structure, the homomorphism `h_V : S → GL_{V,ℝ}`, as a morphism
  `ℝ ⊗[ℚ] O(GL_d) ⟶ O(S)` of commutative Hopf `ℝ`-algebras.
* `TauCeti.Hodge.HodgeStructureOn.mumfordTateGroup`: the Mumford–Tate group `MT(V)` of a rational
  Hodge structure, as the Hopf ideal `TauCeti.DeligneTorus.mumfordTateHopfIdeal` of `h_V`.

## Main results

* `TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom_genericMatrix`: a complex point of `S`
  acts through `h` by the action `TauCeti.Hodge.HodgeStructureOn.complexDeligneAction` of the
  Hodge structure.
* `TauCeti.Hodge.HodgeStructureOn.le_mumfordTateGroup_iff`: minimality of `MT(V)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27, and the aside after Definition 2.16, p. 31.
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), §3.
-/

public section

open CategoryTheory TauCeti.DeligneTorus TauCeti.GeneralLinear WithConv
open scoped TensorProduct

namespace TauCeti.DeligneTorus

/-- **Complex conjugation of `ℂ ⊗[ℝ] S` is `conjSwap`**: through the splitting
`ℂ ⊗[ℝ] S ≃ ℂ[ℤ²]`, conjugating the scalars becomes `conjSwap`. -/
theorem splittingBialgEquiv_map_conj (z : ℂ ⊗[ℝ] S) :
    splittingBialgEquiv (TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id z) =
      conjSwap (splittingBialgEquiv z) := by
  induction z with
  | tmul c s =>
    have h (c' : ℂ) : (c' ⊗ₜ[ℝ] s : ℂ ⊗[ℝ] S) = c' • (1 ⊗ₜ s) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgEquiv.toLinearMap_apply, h, h c, map_smul,
      map_smul, splittingBialgEquiv_one_tmul, conjSwap_smul, Complex.conjAe_coe]
    congr 1
    exact (congrArg (fun φ ↦ φ s) conjSwap_comp_splittingPoint).symm
  | add x y hx hy => simp only [map_add, hx, hy]

end TauCeti.DeligneTorus

namespace TauCeti.Hodge.HodgeStructureOn

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ω : Conjugation W} {n : ℤ}
variable (hs : HodgeStructureOn W ω n)

/-! ### Hodge projections, conjugation and a support of the Hodge decomposition -/

/-- The Hodge projections are orthogonal idempotents. -/
theorem proj_proj (p q : ℤ) (x : W) :
    hs.proj p (hs.proj q x) = if p = q then hs.proj p x else 0 := by
  split_ifs with hpq
  · subst hpq
    exact hs.proj_apply_of_mem (hs.proj_mem p x)
  · exact hs.proj_apply_eq_zero_of_mem_of_ne (hs.proj_mem q x) (Ne.symm hpq)

/-- **Conjugation exchanges the Hodge projections of degrees `p` and `n - p`.** -/
theorem conj_proj (p : ℤ) (x : W) :
    ω.toEquiv (hs.proj p x) = hs.proj (n - p) (ω.toEquiv x) := by
  refine hs.piece_induction_on (motive := fun x ↦
    ω.toEquiv (hs.proj p x) = hs.proj (n - p) (ω.toEquiv x)) x (fun q y hy ↦ ?_)
    fun y z hy hz ↦ ?_
  · rcases eq_or_ne q p with rfl | hqp
    · rw [hs.proj_apply_of_mem hy, hs.proj_apply_of_mem (hs.conj_mem_piece hy)]
    · rw [hs.proj_apply_eq_zero_of_mem_of_ne hy hqp, map_zero,
        hs.proj_apply_eq_zero_of_mem_of_ne (hs.conj_mem_piece hy) (by omega)]
  · rw [map_add, map_add, hy, hz, map_add, map_add]

/-- A finite set of degrees, stable under `p ↦ n - p`, outside which every Hodge component
`H^{p,n-p}` vanishes. -/
noncomputable def hodgeSupport : Finset ℤ :=
  hs.finite_setOf_piece_ne_bot.toFinset ∪
    hs.finite_setOf_piece_ne_bot.toFinset.image (n - ·)

/-- Outside `hodgeSupport` the Hodge projections vanish. -/
theorem proj_eq_zero_of_notMem_hodgeSupport {p : ℤ} (hp : p ∉ hs.hodgeSupport) :
    hs.proj p = 0 := by
  have hbot : hs.piece p = ⊥ := by
    by_contra h
    exact hp (Finset.mem_union_left _ (hs.finite_setOf_piece_ne_bot.mem_toFinset.mpr h))
  ext x
  have hx := hs.proj_mem p x
  rw [hbot, Submodule.mem_bot] at hx
  simp [hx]

/-- `hodgeSupport` is stable under `p ↦ n - p`. -/
theorem sub_mem_hodgeSupport {p : ℤ} (hp : p ∈ hs.hodgeSupport) :
    n - p ∈ hs.hodgeSupport := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [sub_sub_cancel]
    exact Finset.mem_union_left _ hq

/-- A vector is the sum of its Hodge projections over `hodgeSupport`. -/
theorem sum_proj_hodgeSupport (x : W) : ∑ p ∈ hs.hodgeSupport, hs.proj p x = x :=
  hs.sum_proj_eq x fun _ hp ↦ by rw [hs.proj_eq_zero_of_notMem_hodgeSupport hp,
    LinearMap.zero_apply]

/-! ### The complexified action as a matrix over `ℂ[ℤ²]` -/

variable {d : ℕ} (e : Module.Basis (Fin d) ℂ W)

/-- The matrix, over the coordinate ring `ℂ[ℤ²]` of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`, of the action of `S_ℂ` on
`W` in the basis `e`: the sum over `p` of the matrix of the projection onto `H^{p,n-p}` times the
character `X^{(-p,p-n)}` by which `S_ℂ` acts on that component. -/
noncomputable def splitCoordinateMatrix :
    Matrix (Fin d) (Fin d) (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :=
  Matrix.of fun i j ↦ ∑ p ∈ hs.hodgeSupport,
    MonoidAlgebra.single (Multiplicative.ofAdd (-p, p - n)) (e.repr (hs.proj p (e j)) i)

/-- The entries of `splitCoordinateMatrix`. -/
theorem splitCoordinateMatrix_apply (i j : Fin d) :
    hs.splitCoordinateMatrix e i j = ∑ p ∈ hs.hodgeSupport,
      MonoidAlgebra.single (Multiplicative.ofAdd (-p, p - n)) (e.repr (hs.proj p (e j)) i) :=
  (rfl)

/-- The coordinates of the composite of two Hodge projections. -/
private theorem sum_repr_proj_mul_repr_proj (p q : ℤ) (i j : Fin d) :
    ∑ k, e.repr (hs.proj p (e k)) i * e.repr (hs.proj q (e j)) k =
      if p = q then e.repr (hs.proj p (e j)) i else 0 := by
  have h := congrArg (fun f ↦ f i j)
    (LinearMap.toMatrix_mul e (hs.proj p) (hs.proj q))
  simp only [LinearMap.toMatrix_apply, Matrix.mul_apply, mul_apply_eq_comp] at h
  rw [← h, hs.proj_proj]
  split_ifs <;> simp

/-- **`splitCoordinateMatrix` is multiplicative**: its entries comultiply as the entries of a
matrix-valued group homomorphism, because the Hodge projections are orthogonal idempotents and the
characters are group-like. -/
theorem splitCoordinateMatrix_comul :
    (hs.splitCoordinateMatrix e).map
        (Bialgebra.comulAlgHom ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))) =
      (hs.splitCoordinateMatrix e).map (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ)) *
        (hs.splitCoordinateMatrix e).map (Algebra.TensorProduct.includeRight (R := ℂ)) := by
  ext i j
  have hsingle (g h : Multiplicative (ℤ × ℤ)) (c c' : ℂ) :
      MonoidAlgebra.single g c ⊗ₜ[ℂ] MonoidAlgebra.single h c' =
        (c * c') • (MonoidAlgebra.single g (1 : ℂ) ⊗ₜ[ℂ] MonoidAlgebra.single h (1 : ℂ)) := by
    rw [← TensorProduct.smul_tmul_smul, MonoidAlgebra.smul_single', MonoidAlgebra.smul_single',
      mul_one, mul_one]
  simp only [Matrix.map_apply, Matrix.mul_apply, splitCoordinateMatrix_apply, map_sum,
    Bialgebra.comulAlgHom_apply, MonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let v : ℤ → ℤ → MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) ⊗[ℂ]
      MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) := fun p q ↦
    MonoidAlgebra.single (Multiplicative.ofAdd (-p, p - n)) (1 : ℂ) ⊗ₜ[ℂ]
      MonoidAlgebra.single (Multiplicative.ofAdd (-q, q - n)) (1 : ℂ)
  calc _ = ∑ p ∈ hs.hodgeSupport, e.repr (hs.proj p (e j)) i • v p p :=
        Finset.sum_congr rfl fun p _ ↦ by rw [hsingle, one_mul]
    _ = ∑ p ∈ hs.hodgeSupport, ∑ q ∈ hs.hodgeSupport,
          (if p = q then e.repr (hs.proj p (e j)) i else 0) • v p q := by
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        simp [ite_smul, Finset.sum_ite_eq, hp]
    _ = ∑ p ∈ hs.hodgeSupport, ∑ q ∈ hs.hodgeSupport,
          (∑ k, e.repr (hs.proj p (e k)) i * e.repr (hs.proj q (e j)) k) • v p q := by
        simp only [sum_repr_proj_mul_repr_proj]
    _ = ∑ k, ∑ p ∈ hs.hodgeSupport, ∑ q ∈ hs.hodgeSupport,
          (e.repr (hs.proj p (e k)) i * e.repr (hs.proj q (e j)) k) • v p q := by
        simp only [Finset.sum_smul]
        refine (Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm).trans Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun p _ ↦
        Finset.sum_congr rfl fun q _ ↦ (hsingle _ _ _ _).symm

/-- The counit sends `splitCoordinateMatrix` to the identity matrix, because the Hodge projections
sum to the identity. -/
theorem splitCoordinateMatrix_counit :
    (hs.splitCoordinateMatrix e).map
        (Bialgebra.counitAlgHom ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))) = 1 := by
  ext i j
  simp only [Matrix.map_apply, splitCoordinateMatrix_apply, map_sum,
    Bialgebra.counitAlgHom_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  rw [← Finsupp.finsetSum_apply, ← map_sum, hs.sum_proj_hodgeSupport, e.repr_self,
    Finsupp.single_apply, Matrix.one_apply]
  simp [eq_comm]

/-- **The complexified action of `S` on coordinate rings**: the morphism of Hopf `ℂ`-algebras
`O(GL_d)_ℂ → ℂ[ℤ²]` sending the generic matrix to `splitCoordinateMatrix`. -/
noncomputable def splitCoordinateBialgHom :
    coordinateHopfAlgebra ℂ d →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
  coordinateBialgHomOfMultiplicative ℂ d (hs.splitCoordinateMatrix e)
    (hs.splitCoordinateMatrix_comul e) (hs.splitCoordinateMatrix_counit e)

/-- The complexified action of `S` as a morphism `ℂ ⊗[ℝ] O(GL_d) → ℂ ⊗[ℝ] O(S)` of Hopf
`ℂ`-algebras. -/
noncomputable def complexCoordinateBialgHom :
    ℂ ⊗[ℝ] coordinateHopfAlgebra ℝ d →ₐc[ℂ] ℂ ⊗[ℝ] S :=
  ((splittingBialgEquiv.symm : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) ≃ₐc[ℂ] ℂ ⊗[ℝ] S) :
      MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) →ₐc[ℂ] ℂ ⊗[ℝ] S).comp
    ((hs.splitCoordinateBialgHom e).comp
      (coordinateHopfAlgebraBaseChangeBialgEquiv ℝ ℂ d :
        ℂ ⊗[ℝ] coordinateHopfAlgebra ℝ d →ₐc[ℂ] coordinateHopfAlgebra ℂ d))

/-- `complexCoordinateBialgHom` sends the generic matrix to `splitCoordinateMatrix`, read in
`ℂ ⊗[ℝ] S` through the splitting. -/
theorem complexCoordinateBialgHom_one_tmul_genericMatrix (i j : Fin d) :
    hs.complexCoordinateBialgHom e (1 ⊗ₜ genericMatrix ℝ d i j) =
      splittingBialgEquiv.symm (hs.splitCoordinateMatrix e i j) := by
  simp only [complexCoordinateBialgHom, genericMatrix_apply, BialgHom.comp_apply,
    BialgEquiv.coe_toBialgHom, splitCoordinateBialgHom]
  erw [coordinateHopfAlgebraBaseChangeBialgEquiv_one_tmul_X ℝ ℂ d i j]
  rw [coordinateBialgHomOfMultiplicative_X]

/-! ### Descent to `ℝ` -/

section Real

variable {e}

/-- In a basis fixed by the conjugation, the coordinates of a conjugate vector are the conjugate
coordinates. -/
theorem repr_conj (he : ∀ i, ω.toEquiv (e i) = e i) (x : W) (i : Fin d) :
    e.repr (ω.toEquiv x) i = starRingEnd ℂ (e.repr x i) := by
  have hx : ω.toEquiv x = ∑ k, starRingEnd ℂ (e.repr x k) • e k := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, LinearEquiv.map_smulₛₗ, he]
  rw [hx, e.repr_sum_self]

/-- In a basis fixed by the conjugation, the matrix of the complexified action is fixed by
`conjSwap`. -/
theorem conjSwap_splitCoordinateMatrix (he : ∀ i, ω.toEquiv (e i) = e i) (i j : Fin d) :
    conjSwap (hs.splitCoordinateMatrix e i j) = hs.splitCoordinateMatrix e i j := by
  rw [splitCoordinateMatrix_apply, map_sum]
  refine Finset.sum_nbij' (n - ·) (n - ·) (fun p hp ↦ hs.sub_mem_hodgeSupport hp)
    (fun p hp ↦ hs.sub_mem_hodgeSupport hp) (fun p _ ↦ by simp) (fun p _ ↦ by simp)
    fun p _ ↦ ?_
  rw [conjSwap_single, ← repr_conj he, hs.conj_proj, he]
  congr 2
  ring_nf

/-- The complexified action of `S` on coordinate rings, in a basis fixed by the conjugation,
takes real values on real coordinates: it commutes with every automorphism of `ℂ` over `ℝ`
acting on the scalars of `ℂ ⊗[ℝ] S`. -/
theorem map_complexCoordinateBialgHom_one_tmul (he : ∀ i, ω.toEquiv (e i) = e i)
    (σ : ℂ ≃ₐ[ℝ] ℂ) (a : coordinateHopfAlgebra ℝ d) :
    TensorProduct.map σ.toLinearMap LinearMap.id (hs.complexCoordinateBialgHom e (1 ⊗ₜ a)) =
      hs.complexCoordinateBialgHom e (1 ⊗ₜ a) := by
  let f : coordinateHopfAlgebra ℝ d →ₐ[ℝ] ℂ ⊗[ℝ] S :=
    ((hs.complexCoordinateBialgHom e).toAlgHom.restrictScalars ℝ).comp
      Algebra.TensorProduct.includeRight
  have key : (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id ℝ S)).comp f = f := by
    refine coordinateHopfAlgebra_algHom_ext ℝ d fun i j ↦ ?_
    have hij := hs.complexCoordinateBialgHom_one_tmul_genericMatrix e i j
    rw [genericMatrix_apply] at hij
    simp only [AlgHom.comp_apply, f, Algebra.TensorProduct.includeRight_apply,
      AlgHom.restrictScalars_apply, BialgHom.coe_toAlgHom, hij]
    rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with hσ | hσ
    · rw [hσ, Algebra.TensorProduct.map_id, AlgHom.id_apply]
    · rw [hσ]
      have h := splittingBialgEquiv_map_conj
        (splittingBialgEquiv.symm (hs.splitCoordinateMatrix e i j))
      rw [splittingBialgEquiv.apply_symm_apply, hs.conjSwap_splitCoordinateMatrix he] at h
      exact splittingBialgEquiv.injective (h.trans (splittingBialgEquiv.apply_symm_apply _).symm)
  exact congrArg (fun φ : coordinateHopfAlgebra ℝ d →ₐ[ℝ] ℂ ⊗[ℝ] S ↦ φ a) key

/-- **Galois equivariance of the complexified action.** In a basis fixed by the conjugation, the
complexified action of `S` on coordinate rings commutes with every automorphism of `ℂ` over `ℝ`
acting on the scalars. -/
theorem complexCoordinateBialgHom_map (he : ∀ i, ω.toEquiv (e i) = e i) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (x : ℂ ⊗[ℝ] coordinateHopfAlgebra ℝ d) :
    hs.complexCoordinateBialgHom e (TensorProduct.map σ.toLinearMap LinearMap.id x) =
      TensorProduct.map σ.toLinearMap LinearMap.id (hs.complexCoordinateBialgHom e x) := by
  induction x with
  | tmul c a =>
    have h (c' : ℂ) : (c' ⊗ₜ[ℝ] a : ℂ ⊗[ℝ] coordinateHopfAlgebra ℝ d) = c' • (1 ⊗ₜ a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgEquiv.toLinearMap_apply, h, h c, map_smul,
      map_smul]
    exact (congrArg _ (hs.map_complexCoordinateBialgHom_one_tmul he σ a)).symm.trans
      (TauCeti.ScalarAut.smul_smulₛₗ σ c _).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **The homomorphism `h : S → GL_{d,ℝ}` of a Hodge structure, on coordinate rings**, in a
basis `e` fixed by the conjugation: the morphism of Hopf `ℝ`-algebras `O(GL_d)_ℝ → O(S)` whose
complexification is the action of `S_ℂ` on `W` through the characters of the Hodge components
(`TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom_genericMatrix`). It is the Galois descent
of `complexCoordinateBialgHom`. -/
noncomputable def realCoordinateBialgHom (he : ∀ i, ω.toEquiv (e i) = e i) :
    coordinateHopfAlgebra ℝ d →ₐc[ℝ] S :=
  (hs.complexCoordinateBialgHom e).galoisDescend (hs.complexCoordinateBialgHom_map he)

/-- The complexification of `realCoordinateBialgHom` is `complexCoordinateBialgHom`. -/
theorem one_tmul_realCoordinateBialgHom (he : ∀ i, ω.toEquiv (e i) = e i)
    (a : coordinateHopfAlgebra ℝ d) :
    (1 : ℂ) ⊗ₜ[ℝ] hs.realCoordinateBialgHom he a = hs.complexCoordinateBialgHom e (1 ⊗ₜ a) :=
  BialgHom.one_tmul_galoisDescend _ _ a

/-- **`h` acts on complex points through the Hodge decomposition.** A complex point `g` of `S`
sends the generic matrix through `h` to the matrix, in the basis `e`, of the action
`h_ℂ(g)` of `g` on `W` (`TauCeti.Hodge.HodgeStructureOn.complexDeligneAction`), which acts on
`H^{p,q}` by `z₁ ^ (-p) * z₂ ^ (-q)` for `g` with coordinates `(z₁, z₂)`. -/
theorem realCoordinateBialgHom_genericMatrix (he : ∀ i, ω.toEquiv (e i) = e i)
    (g : WithConv (S →ₐ[ℝ] ℂ)) (i j : Fin d) :
    g.ofConv (hs.realCoordinateBialgHom he (genericMatrix ℝ d i j)) =
      LinearMap.toMatrix e e (hs.complexDeligneAction g) i j := by
  have h1 (s : S) : g.ofConv s = AlgHom.liftEquiv ℝ ℂ S ℂ g.ofConv (1 ⊗ₜ s) := by simp
  have h2 (q : Multiplicative (ℤ × ℤ)) (c : ℂ) :
      MonoidAlgebra.single q c = c • MonoidAlgebra.single q (1 : ℂ) := by
    rw [MonoidAlgebra.smul_single', mul_one]
  rw [h1, one_tmul_realCoordinateBialgHom, complexCoordinateBialgHom_one_tmul_genericMatrix,
    splitCoordinateMatrix_apply, map_sum, map_sum, LinearMap.toMatrix_apply]
  conv_rhs => rw [← hs.sum_proj_hodgeSupport (e j)]
  simp only [map_sum, hs.complexDeligneAction_apply_of_mem g (hs.proj_mem _ _), map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [h2, map_smul, map_smul, liftEquiv_splittingBialgEquiv_symm_single, smul_eq_mul, mul_comm]

end Real

/-! ### Rational Hodge structures -/

section Rational

attribute [local instance] moduleRatOfComplex ratComplexScalarTower

variable {Vℤ Vℚ Vℂ : Type*} [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
  [AddCommGroup Vℂ] [Module ℂ Vℂ] {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

/-- The basis of the complexification `Vℂ` induced by a basis of the rational structure `Vℚ`. -/
noncomputable def rationalBasis (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (b : Module.Basis (Fin d) ℚ Vℚ) : Module.Basis (Fin d) ℂ Vℂ :=
  (isBaseChange_rationalToComplexMap hℚ hℂ).basis b

variable (hℚ : IsBaseChange ℚ ιℚ) {hℂ : IsBaseChange ℂ ιℂ} (b : Module.Basis (Fin d) ℚ Vℚ)

/-- The induced basis consists of the images of the rational basis vectors. -/
theorem rationalBasis_apply (i : Fin d) :
    rationalBasis hℚ hℂ b i = rationalToComplexMap hℚ ιℂ (b i) :=
  IsBaseChange.basis_apply _ _ i

/-- The lattice conjugation fixes a basis induced by a rational basis. -/
theorem latticeConjugation_rationalBasis (i : Fin d) :
    (latticeConjugation hℂ).toEquiv (rationalBasis hℚ hℂ b i) = rationalBasis hℚ hℂ b i := by
  rw [rationalBasis_apply, latticeConjugation_toEquiv_apply,
    ← rationalToComplexLinearEquiv_one_tmul hℚ hℂ,
    latticeConj_rationalToComplexLinearEquiv_one_tmul]

variable (hs : HodgeStructureOn Vℂ (latticeConjugation hℂ) n)

/-- **The homomorphism `h_V : S → GL_{V,ℝ}` of a rational Hodge structure** (Definition 13.1),
on coordinate rings, with `GL_V ≅ GL_d` through the rational basis `b`: the morphism of Hopf
`ℝ`-algebras `ℝ ⊗[ℚ] O(GL_d) → O(S)` through which a point `z ∈ S(ℝ) = ℂˣ` acts on `V^{p,q}` by
`z ^ (-p) * conj z ^ (-q)` (`TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom_genericMatrix`
and `TauCeti.Hodge.HodgeStructureOn.complexDeligneAction_apply_of_mem`). -/
noncomputable def deligneHom :
    CommHopfAlgCat.baseChange (K := ℝ) (coordinateHopfAlgebra ℚ d) ⟶
      _root_.CommHopfAlgCat.of ℝ S :=
  (coordinateHopfAlgebraBaseChangeIso ℚ ℝ d).hom ≫
    _root_.CommHopfAlgCat.ofHom
      (hs.realCoordinateBialgHom (latticeConjugation_rationalBasis hℚ b))

/-- On the generic matrix, `deligneHom` is `realCoordinateBialgHom` in the induced basis. -/
theorem deligneHom_one_tmul_genericMatrix (i j : Fin d) :
    (hs.deligneHom hℚ b).hom (1 ⊗ₜ genericMatrix ℚ d i j) =
      hs.realCoordinateBialgHom (latticeConjugation_rationalBasis hℚ b)
        (genericMatrix ℝ d i j) := by
  rw [deligneHom, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply, genericMatrix_apply,
    coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X, _root_.CommHopfAlgCat.hom_ofHom,
    genericMatrix_apply]

/-- **The Mumford–Tate group `MT(V)` of a rational Hodge structure** (Definition 13.2), as the
Hopf ideal of `O(GL_d) = O(GL_V)` cutting it out: the largest Hopf ideal whose real extension is
killed by `h_V`. `MT(V)` is the smallest closed `ℚ`-subgroup of `GL_V` through whose real
extension `h_V` factors (`TauCeti.Hodge.HodgeStructureOn.le_mumfordTateGroup_iff`). The ideal of
rational functions vanishing on `h_V(S)` need not be a Hopf ideal, so `MT(V)` is cut out by the
largest Hopf ideal inside it rather than by that ideal itself. -/
noncomputable def mumfordTateGroup : HopfIdeal ℚ (coordinateHopfAlgebra ℚ d) :=
  mumfordTateHopfIdeal (hs.deligneHom hℚ b)

/-- **Minimality of `MT(V)`**: a Hopf ideal `I` of `O(GL_V)` lies below the Mumford–Tate ideal
exactly when `h_V` kills its real extension, that is, when `h_V` factors through the real
extension of the closed `ℚ`-subgroup cut out by `I`. -/
theorem le_mumfordTateGroup_iff {I : HopfIdeal ℚ (coordinateHopfAlgebra ℚ d)} :
    I ≤ hs.mumfordTateGroup hℚ b ↔
      (CommHopfAlgCat.baseChangeHopfIdeal (K := ℝ) I).toIdeal ≤
        RingHom.ker (hs.deligneHom hℚ b).hom.toAlgHom.toRingHom :=
  le_mumfordTateHopfIdeal_iff

end Rational

end TauCeti.Hodge.HodgeStructureOn
