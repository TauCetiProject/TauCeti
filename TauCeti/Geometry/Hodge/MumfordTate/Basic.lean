/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.Bialgebra.GaloisDescent
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Internal
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
`ℂ[ℤ²]` (`TauCeti.DeligneTorus.splittingBialgEquiv`). Indexing the Hodge decomposition by the
characters `X^{(-p, p - n)}` of `S_ℂ` makes `W` a comodule over `ℂ[ℤ²]`
(`DirectSum.IsInternal.monoidAlgebraComodule`), whose coordinate morphism
`O(GL_d)_ℂ → ℂ[ℤ²]` (`TauCeti.Comodule.coordinateBialgHom`) sends the generic matrix to
`∑ p, P p * X^{(-p, p - n)}`, where `P p` is the matrix of the projection onto `H^{p,n-p}`.
Complex conjugation exchanges
`H^{p,q}` and `H^{q,p}`, which in a basis fixed by `ω` makes the matrix invariant under the
conjugation `TauCeti.DeligneTorus.conjSwap` of `ℂ[ℤ²]`; this is the real structure of `S`, so the
morphism descends to `ℝ` (`BialgHom.galoisDescend`).

## Main definitions

* `TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom`: the homomorphism `h : S → GL_d` over
  `ℝ` of a Hodge structure in a basis fixed by the conjugation, on coordinate rings.
* `TauCeti.Hodge.HodgeStructureOn.deligneHom`: for a rational Hodge structure with a basis of its
  rational structure, the homomorphism `h_V : S → GL_{V,ℝ}`, as a morphism
  `ℝ ⊗[ℚ] O(GL_d) ⟶ O(S)` of commutative Hopf `ℝ`-algebras.
* `TauCeti.Hodge.HodgeStructureOn.mumfordTateHopfIdeal`: the Hopf ideal cutting out the
  Mumford–Tate group `MT(V)` of a rational Hodge structure, the
  `TauCeti.DeligneTorus.mumfordTateHopfIdeal` of `h_V`.

## Main results

* `TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom_genericMatrix`: a complex point of `S`
  acts through `h` by the action `TauCeti.Hodge.HodgeStructureOn.complexDeligneAction` of the
  Hodge structure.
* `TauCeti.Hodge.HodgeStructureOn.le_mumfordTateHopfIdeal_iff`: minimality of `MT(V)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27, and the aside after Definition 2.16, p. 31.
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), §3.
-/

public section

open CategoryTheory TauCeti.DeligneTorus TauCeti.GeneralLinear WithConv
open scoped TensorProduct Matrix

namespace TauCeti.Hodge.HodgeStructureOn

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ω : Conjugation W} {n : ℤ}
variable (hs : HodgeStructureOn W ω n)

/-! ### The complexified action as a comodule over `ℂ[ℤ²]` -/

/-- The Hodge decomposition indexed by the characters of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`: the summand of the
character `X^{(-p,p-n)}` is `H^{p,n-p}`, and the summands of the other characters vanish. -/
noncomputable def characterPiece (g : Multiplicative (ℤ × ℤ)) : Submodule ℂ W :=
  if g.toAdd.1 + g.toAdd.2 = -n then hs.piece (-g.toAdd.1) else ⊥

/-- The summand of the character `X^{(-p,p-n)}` is `H^{p,n-p}`. -/
@[simp]
theorem characterPiece_ofAdd (p : ℤ) :
    hs.characterPiece (Multiplicative.ofAdd (-p, p - n)) = hs.piece p := by
  simp [characterPiece, show -p + (p - n) = -n by ring]

/-- The summand of a character off the line `a + b = -n` vanishes. -/
@[simp]
theorem characterPiece_eq_bot_of_ne {g : Multiplicative (ℤ × ℤ)} (h : g.toAdd.1 + g.toAdd.2 ≠ -n) :
    hs.characterPiece g = ⊥ := by
  simp [characterPiece, h]

/-- The Hodge decomposition indexed by characters is an internal direct sum. -/
theorem isInternal_characterPiece : DirectSum.IsInternal hs.characterPiece := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hline {g : Multiplicative (ℤ × ℤ)} (hg : hs.characterPiece g ≠ ⊥) :
      g.toAdd.1 + g.toAdd.2 = -n := by
    by_contra h
    exact hg (hs.characterPiece_eq_bot_of_ne h)
  refine ⟨iSupIndep_ne_bot.mp ?_, eq_top_iff.mpr ?_⟩
  · have hinj : Function.Injective
        fun g : {g // hs.characterPiece g ≠ ⊥} ↦ -(g : Multiplicative (ℤ × ℤ)).toAdd.1 := by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
      have h₁ := hline hg
      have h₂ := hline hg'
      have h₃ : g.toAdd.1 = g'.toAdd.1 := neg_inj.mp h
      exact Subtype.ext (show g = g' from Multiplicative.toAdd.injective (Prod.ext h₃ (by omega)))
    convert hs.piece_iSupIndep.comp hinj using 1
    ext1 ⟨g, hg⟩
    simp [characterPiece, hline hg]
  · rw [← hs.iSup_piece_eq_top]
    exact iSup_le fun p ↦ hs.characterPiece_ofAdd p ▸ le_iSup hs.characterPiece _

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

/-- The matrix of the complexified action of `S` in the basis `e`, applied to the coordinates of a
vector of `H^{p,n-p}`, multiplies them by the character `X^{(-p,p-n)}`. -/
theorem splitCoordinateMatrix_mulVec_of_mem {p : ℤ} {v : W} (hv : v ∈ hs.piece p) :
    hs.splitCoordinateMatrix e *ᵥ
        (algebraMap ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) ∘ e.repr v) =
      MonoidAlgebra.single (Multiplicative.ofAdd (-p, p - n)) (1 : ℂ) •
        (algebraMap ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) ∘ e.repr v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, splitCoordinateMatrix_apply, Finset.sum_mul,
    Pi.smul_apply, smul_eq_mul, MonoidAlgebra.coe_algebraMap, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, MonoidAlgebra.single_mul_single, mul_one, one_mul]
  rw [Finset.sum_comm]
  have hp' (p' : ℤ) : ∑ j, MonoidAlgebra.single (Multiplicative.ofAdd (-p', p' - n))
      (e.repr (hs.proj p' (e j)) i * e.repr v j) =
        MonoidAlgebra.single (Multiplicative.ofAdd (-p', p' - n)) (e.repr (hs.proj p' v) i) := by
    simp_rw [← MonoidAlgebra.singleAddHom_apply, ← map_sum,
      ← LinearMap.toMatrix_mulVec_repr e e (hs.proj p') v, Matrix.mulVec, dotProduct,
      LinearMap.toMatrix_apply]
  simp_rw [hp']
  by_cases hmem : p ∈ hs.hodgeSupport
  · rw [Finset.sum_eq_single p (fun p' _ hp'p ↦ by
      rw [hs.proj_apply_eq_zero_of_mem_of_ne hv (Ne.symm hp'p), map_zero, Finsupp.zero_apply,
        MonoidAlgebra.single_zero]) (fun h ↦ absurd hmem h), hs.proj_apply_of_mem hv]
  · have hv0 : v = 0 := by
      have hbot : hs.piece p = ⊥ := by simpa [mem_hodgeSupport] using hmem
      simpa [hbot] using hv
    simp [hv0]

/-- **The complexified action of `S` on coordinate rings**: the morphism of Hopf `ℂ`-algebras
`O(GL_d)_ℂ → ℂ[ℤ²]` of the comodule `DirectSum.IsInternal.monoidAlgebraComodule` given by the
Hodge decomposition indexed by characters, in the basis `e`. It sends the generic matrix to
`splitCoordinateMatrix` (`TauCeti.Hodge.HodgeStructureOn.splitCoordinateBialgHom_X`). -/
noncomputable def splitCoordinateBialgHom :
    coordinateHopfAlgebra ℂ d →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
  letI := hs.isInternal_characterPiece.monoidAlgebraComodule
  TauCeti.Comodule.coordinateBialgHom e

/-- `splitCoordinateBialgHom` sends the generic matrix to `splitCoordinateMatrix`. -/
@[simp]
theorem splitCoordinateBialgHom_X (i j : Fin d) :
    hs.splitCoordinateBialgHom e
        (coordinateHopfAlgebraAlgEquiv ℂ d (coordinateRingMap ℂ d (MvPolynomial.X (i, j)))) =
      hs.splitCoordinateMatrix e i j := by
  let := hs.isInternal_characterPiece.monoidAlgebraComodule
  refine (TauCeti.Comodule.coordinateBialgHom_X
    (H := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) e i j).trans ?_
  rw [TauCeti.Comodule.coefficientMatrix_apply, TauCeti.Comodule.matrixCoefficient_def]
  conv_lhs => rw [← hs.sum_proj_hodgeSupport (e j)]
  rw [map_sum, map_sum, map_sum, splitCoordinateMatrix_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hp : hs.proj p (e j) ∈ hs.characterPiece (Multiplicative.ofAdd (-p, p - n)) := by
    rw [characterPiece_ofAdd]
    exact hs.proj_mem p (e j)
  rw [hs.isInternal_characterPiece.coact_monoidAlgebraComodule_of_mem hp, TensorProduct.map_tmul,
    TensorProduct.lid_tmul, Module.Basis.coord_apply, LinearMap.id_apply,
    MonoidAlgebra.smul_single', mul_one]

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
@[simp]
theorem complexCoordinateBialgHom_one_tmul_X (i j : Fin d) :
    hs.complexCoordinateBialgHom e
        (1 ⊗ₜ coordinateHopfAlgebraAlgEquiv ℝ d (coordinateRingMap ℝ d (MvPolynomial.X (i, j)))) =
      splittingBialgEquiv.symm (hs.splitCoordinateMatrix e i j) := by
  rw [complexCoordinateBialgHom, BialgHom.comp_apply, BialgHom.comp_apply,
    BialgEquiv.coe_toBialgHom, BialgEquiv.coe_toBialgHom,
    coordinateHopfAlgebraBaseChangeBialgEquiv_one_tmul_X, splitCoordinateBialgHom_X]

/-! ### Descent to `ℝ` -/

section Real

variable {e}

/-- In a basis fixed by the conjugation, the matrix of the complexified action is fixed by
`conjSwap`. -/
theorem conjSwap_splitCoordinateMatrix (he : ∀ i, ω.toEquiv (e i) = e i) (i j : Fin d) :
    conjSwap (hs.splitCoordinateMatrix e i j) = hs.splitCoordinateMatrix e i j := by
  rw [splitCoordinateMatrix_apply, map_sum]
  refine Finset.sum_nbij' (n - ·) (n - ·) (fun p hp ↦ hs.sub_mem_hodgeSupport hp)
    (fun p hp ↦ hs.sub_mem_hodgeSupport hp) (fun p _ ↦ by simp) (fun p _ ↦ by simp)
    fun p _ ↦ ?_
  rw [conjSwap_single, ← ω.repr_toEquiv_of_fixed e he, hs.conj_proj, he]
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
  -- Both `Algebra.TensorProduct.map σ id` and `TensorProduct.map σ id` are the scalar action.
  have hmap (y : ℂ ⊗[ℝ] S) :
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id ℝ S) y =
        TensorProduct.map σ.toLinearMap LinearMap.id y := by
    rw [ScalarAut.algebraTensorProductMap_eq_smul, ScalarAut.tensorProductMap_eq_smul]
  have key : (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id ℝ S)).comp f = f := by
    refine coordinateHopfAlgebra_algHom_ext ℝ d fun i j ↦ ?_
    have hij := hs.complexCoordinateBialgHom_one_tmul_X e i j
    simp only [AlgHom.comp_apply, f, Algebra.TensorProduct.includeRight_apply,
      AlgHom.restrictScalars_apply, BialgHom.coe_toAlgHom, hij]
    rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with hσ | hσ
    · rw [hσ, Algebra.TensorProduct.map_id, AlgHom.id_apply]
    · rw [hmap]
      obtain rfl : σ = Complex.conjAe := AlgEquiv.coe_toAlgHom_injective hσ
      refine EquivLike.injective splittingBialgEquiv ?_
      rw [splittingBialgEquiv_map_conj, splittingBialgEquiv.apply_symm_apply,
        hs.conjSwap_splitCoordinateMatrix he]
  have ha := DFunLike.congr_fun key a
  simp only [AlgHom.comp_apply, f, Algebra.TensorProduct.includeRight_apply,
    AlgHom.restrictScalars_apply, BialgHom.coe_toAlgHom] at ha
  rwa [hmap] at ha

/-- **Galois equivariance of the complexified action.** In a basis fixed by the conjugation, the
complexified action of `S` on coordinate rings commutes with every automorphism of `ℂ` over `ℝ`
acting on the scalars. -/
theorem complexCoordinateBialgHom_map (he : ∀ i, ω.toEquiv (e i) = e i) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (x : ℂ ⊗[ℝ] coordinateHopfAlgebra ℝ d) :
    hs.complexCoordinateBialgHom e (TensorProduct.map σ.toLinearMap LinearMap.id x) =
      TensorProduct.map σ.toLinearMap LinearMap.id (hs.complexCoordinateBialgHom e x) := by
  let F : ℂ ⊗[ℝ] coordinateHopfAlgebra ℝ d →ₗ[ℂ] ℂ ⊗[ℝ] S := hs.complexCoordinateBialgHom e
  have hF (a : coordinateHopfAlgebra ℝ d) :
      ScalarAut.semilinearMap σ (F (1 ⊗ₜ a)) = F (1 ⊗ₜ a) := by
    rw [ScalarAut.semilinearMap_apply, ← ScalarAut.tensorProductMap_eq_smul,
      BialgHom.coe_toLinearMap, hs.map_complexCoordinateBialgHom_one_tmul he σ a]
  have h := ScalarAut.map_smul_eq_of_forall_one_tmul σ F _ hF x
  rwa [BialgHom.coe_toLinearMap, ScalarAut.semilinearMap_apply,
    ← ScalarAut.tensorProductMap_eq_smul, ← ScalarAut.tensorProductMap_eq_smul] at h

/-- **The homomorphism `h : S → GL_{d,ℝ}` of a Hodge structure, on coordinate rings**, in a
basis `e` fixed by the conjugation: the morphism of Hopf `ℝ`-algebras `O(GL_d)_ℝ → O(S)` whose
complexification is the action of `S_ℂ` on `W` through the characters of the Hodge components
(`TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom_genericMatrix`). It is the Galois descent
of `complexCoordinateBialgHom`. -/
noncomputable def realCoordinateBialgHom (he : ∀ i, ω.toEquiv (e i) = e i) :
    coordinateHopfAlgebra ℝ d →ₐc[ℝ] S :=
  (hs.complexCoordinateBialgHom e).galoisDescend (hs.complexCoordinateBialgHom_map he)

/-- The complexification of `realCoordinateBialgHom` is `complexCoordinateBialgHom`. -/
@[simp]
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
  rw [h1, one_tmul_realCoordinateBialgHom, genericMatrix_apply,
    complexCoordinateBialgHom_one_tmul_X, splitCoordinateMatrix_apply, map_sum, map_sum,
    LinearMap.toMatrix_apply]
  conv_rhs => rw [← hs.sum_proj_hodgeSupport (e j)]
  simp only [map_sum, hs.complexDeligneAction_apply_of_mem g (hs.proj_mem _ _), map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [h2, map_smul, map_smul, liftEquiv_splittingBialgEquiv_symm_single, smul_eq_mul, mul_comm]

/-- The universal point of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ` acts through `h` by the matrix
`∑ p, P p * X^{(-p, p - n)}` of the Hodge projections. -/
theorem coe_pointToGeneralLinear_splittingPoint_comp_realCoordinateBialgHom
    (he : ∀ i, ω.toEquiv (e i) = e i) :
    (pointToGeneralLinear d (toConv (splittingPoint.ofConv.comp
      (hs.realCoordinateBialgHom he : coordinateHopfAlgebra ℝ d →ₐ[ℝ] S))) :
        Matrix (Fin d) (Fin d) (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))) =
      hs.splitCoordinateMatrix e := by
  rw [← map_genericMatrix_eq_coe_pointToGeneralLinear]
  refine Matrix.ext fun i j ↦ ?_
  simp [← splittingBialgEquiv_one_tmul, one_tmul_realCoordinateBialgHom, genericMatrix_apply,
    complexCoordinateBialgHom_one_tmul_X]

end Real

/-! ### Rational Hodge structures -/

section Rational

variable {Vℤ Vℚ Vℂ : Type*} [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
  [AddCommGroup Vℂ] [Module ℂ Vℂ] {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable (hℚ : IsBaseChange ℚ ιℚ) {hℂ : IsBaseChange ℂ ιℂ} (b : Module.Basis (Fin d) ℚ Vℚ)

variable (hs : HodgeStructureOn Vℂ (latticeConjugation hℂ) n)

/-- **The homomorphism `h_V : S → GL_{V,ℝ}` of a rational Hodge structure** (Milne,
*Introduction to Shimura varieties*, §2, pp. 26–27), on coordinate rings, with `GL_V ≅ GL_d`
through the rational basis `b`: the morphism of Hopf `ℝ`-algebras `ℝ ⊗[ℚ] O(GL_d) → O(S)` through
which a point `z ∈ S(ℝ) = ℂˣ` acts on `V^{p,q}` by `z ^ (-p) * conj z ^ (-q)`
(`TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom_genericMatrix` and
`TauCeti.Hodge.HodgeStructureOn.complexDeligneAction_apply_of_mem`). -/
noncomputable def deligneHom :
    CommHopfAlgCat.baseChange (K := ℝ) (coordinateHopfAlgebra ℚ d) ⟶
      _root_.CommHopfAlgCat.of ℝ S :=
  (coordinateHopfAlgebraBaseChangeIso ℚ ℝ d).hom ≫
    _root_.CommHopfAlgCat.ofHom
      (hs.realCoordinateBialgHom (latticeConjugation_toEquiv_rationalBasis hℚ b))

/-- On the generic matrix, `deligneHom` is `realCoordinateBialgHom` in the induced basis. -/
@[simp]
theorem deligneHom_one_tmul_X (i j : Fin d) :
    (hs.deligneHom hℚ b).hom
        (1 ⊗ₜ coordinateHopfAlgebraAlgEquiv ℚ d (coordinateRingMap ℚ d (MvPolynomial.X (i, j)))) =
      hs.realCoordinateBialgHom (latticeConjugation_toEquiv_rationalBasis hℚ b)
        (coordinateHopfAlgebraAlgEquiv ℝ d (coordinateRingMap ℝ d (MvPolynomial.X (i, j)))) := by
  rw [deligneHom, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X, _root_.CommHopfAlgCat.hom_ofHom]

/-- **The Mumford–Tate group `MT(V)` of a rational Hodge structure**, as the Hopf ideal of
`O(GL_d) = O(GL_V)` cutting it out (Milne, *Introduction to Shimura varieties*, the aside after
Definition 2.16, p. 31): the largest Hopf ideal whose real extension is killed by `h_V`, that is,
`TauCeti.DeligneTorus.mumfordTateHopfIdeal` of `h_V`. `MT(V)` is the smallest closed `ℚ`-subgroup
of `GL_V` through whose real extension `h_V` factors
(`TauCeti.Hodge.HodgeStructureOn.le_mumfordTateHopfIdeal_iff`). As a supremum of Hopf ideals it
needs no argument that the kernel of `O(GL_V) → ℝ ⊗[ℚ] O(GL_V) → O(S)` is itself a Hopf ideal. -/
noncomputable def mumfordTateHopfIdeal : HopfIdeal ℚ (coordinateHopfAlgebra ℚ d) :=
  TauCeti.DeligneTorus.mumfordTateHopfIdeal (hs.deligneHom hℚ b)

/-- **Minimality of `MT(V)`**: a Hopf ideal `I` of `O(GL_V)` lies below the Mumford–Tate ideal
exactly when `h_V` kills its real extension, that is, when `h_V` factors through the real
extension of the closed `ℚ`-subgroup cut out by `I`. -/
theorem le_mumfordTateHopfIdeal_iff {I : HopfIdeal ℚ (coordinateHopfAlgebra ℚ d)} :
    I ≤ hs.mumfordTateHopfIdeal hℚ b ↔
      (CommHopfAlgCat.baseChangeHopfIdeal (K := ℝ) I).toIdeal ≤
        RingHom.ker (hs.deligneHom hℚ b).hom.toAlgHom.toRingHom :=
  TauCeti.DeligneTorus.le_mumfordTateHopfIdeal_iff

end Rational

end TauCeti.Hodge.HodgeStructureOn
