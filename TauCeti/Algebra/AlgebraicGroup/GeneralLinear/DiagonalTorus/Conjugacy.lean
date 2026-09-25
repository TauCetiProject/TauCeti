/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Torus.Conjugation
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
import TauCeti.Algebra.Coalgebra.Comodule.Weight.Decomposition

/-!
# Conjugating diagonalizable subgroups of `GLₙ` into the diagonal torus

Over a field `k`, every diagonalizable closed subgroup of `GLₙ` is conjugate, by a rational point,
into the diagonal torus. In Hopf coordinates, a closed subgroup is diagonalizable when the
group-like elements span its quotient coordinate Hopf algebra, and containment is reversed: the
conclusion reads `(diagonalTorusDefiningIdeal k n).conjugate g ≤ I`.

The proof restricts the standard representation of `GLₙ` to the subgroup. The restricted
comodule is spanned by weight vectors, so `kⁿ` has a basis `w` of weight vectors with weights
`χⱼ`. If `P` is the matrix with columns `wⱼ` and `M` is the generic point of the subgroup, the
weight equations say `M P = P diag(χ)`. Hence conjugating the generic point by `P⁻¹` lands in the
diagonal torus, which is the inclusion of closed subgroups to be proved.

As a consequence, every split maximal torus of `GLₙ` is conjugate to the diagonal torus,
and any two split maximal tori are conjugate over the base field.
Over an algebraically closed field every torus is split, so the maximal tori are exactly the
conjugates of the diagonal torus, and any two maximal tori are conjugate.

## Main declarations

* `TauCeti.GeneralLinear.exists_mul_map_eq_map_mul_diagGL`: a point of `GLₙ` with values in a
  Hopf algebra spanned by its group-like elements is diagonalized by a rational matrix.
* `TauCeti.GeneralLinear.exists_conjugate_diagonalTorusDefiningIdeal_le`: a diagonalizable closed
  subgroup of `GLₙ` is contained in a conjugate of the diagonal torus.
* `TauCeti.GeneralLinear.exists_eq_conjugate_diagonalTorusDefiningIdeal_of_isMaximalTorus`: a
  split maximal torus of `GLₙ` is a conjugate of the diagonal torus.
* `TauCeti.GeneralLinear.exists_conjugate_eq_of_isMaximalTorus_of_split`: any two split maximal
  tori of `GLₙ` over a field are conjugate.
* `TauCeti.GeneralLinear.isMaximalTorus_iff_exists_eq_conjugate_diagonalTorusDefiningIdeal`:
  over an algebraically closed field, the maximal tori are exactly those conjugates.
* `TauCeti.GeneralLinear.exists_conjugate_eq_of_isMaximalTorus`: any two maximal tori of `GLₙ`
  over an algebraically closed field are conjugate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12 and Section 17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Proposition 8.4.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {k : Type u} [Field k] {n : ℕ}

attribute [local instance] standardComodule

/-- A weight vector of the standard comodule corestricted along a coalgebra morphism
`π : O(GLₙ) → Q` is an eigenvector of the matrix `π(X)` with eigenvalue its weight. -/
private theorem sum_mul_algebraMap_eq_of_coact_eq {Q : Type u} [CommRing Q] [Bialgebra k Q]
    (π : coordinateHopfAlgebra k n →ₗc[k] Q) (v : Fin n → k) (χ : Q)
    (hv : TensorProduct.map LinearMap.id (π : coordinateHopfAlgebra k n →ₗ[k] Q)
      (standardCoact k n v) = v ⊗ₜ[k] χ)
    (i : Fin n) :
    ∑ l, π (genericMatrix k n i l) * algebraMap k Q (v l) = algebraMap k Q (v i) * χ := by
  let T : (Fin n → k) ⊗[k] Q →ₗ[k] Q :=
    (TensorProduct.lid k Q).toLinearMap ∘ₗ (LinearMap.proj i).rTensor Q
  have hsum : v = ∑ l, v l • (Pi.single l (1 : k) : Fin n → k) := by
    conv_lhs => rw [← (Pi.basisFun k (Fin n)).sum_repr v]
    simp only [Pi.basisFun_repr, Pi.basisFun_apply]
  have hL : T (TensorProduct.map LinearMap.id (π : coordinateHopfAlgebra k n →ₗ[k] Q)
      (standardCoact k n v)) =
      ∑ l, π (genericMatrix k n i l) * algebraMap k Q (v l) := by
    conv_lhs => rw [hsum]
    simp only [T, map_sum, map_smul, standardCoact_apply_basisFun, TensorProduct.map_tmul,
      LinearMap.id_coe, id_eq, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearMap.proj_apply, TensorProduct.lid_tmul, Pi.single_apply,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      CoalgHom.coe_linearMapOfClass]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [genericMatrix_apply, Algebra.smul_def, mul_comm]
  have hR : T (v ⊗ₜ[k] χ) = algebraMap k Q (v i) * χ := by
    simp [T, Algebra.smul_def]
  rw [← hL, ← hR, hv]

/-- If the group-like elements of `Q` span it, the standard comodule corestricted along a
coalgebra morphism `π : O(GLₙ) → Q` has a basis of weight vectors. -/
private theorem exists_basis_coact_eq_tmul {Q : Type u} [AddCommGroup Q] [Module k Q]
    [Coalgebra k Q] (hQ : Subcoalgebra.groupLikeSetSpan (R := k) (C := Q) Set.univ = ⊤)
    (π : coordinateHopfAlgebra k n →ₗc[k] Q) :
    ∃ (w : Module.Basis (Fin n) k (Fin n → k)) (χ : Fin n → GroupLike k Q),
      ∀ j, TensorProduct.map LinearMap.id (π : coordinateHopfAlgebra k n →ₗ[k] Q)
        (standardCoact k n (w j)) = w j ⊗ₜ[k] (χ j).val := by
  let _ : Comodule k Q (Fin n → k) := Comodule.Corestrict π
  let S : Set (Fin n → k) :=
    ⋃ g : GroupLike k Q, (_root_.GroupLike.weightSpace (M := Fin n → k) g : Set (Fin n → k))
  have hS : Submodule.span k S = ⊤ := by
    rw [← Submodule.iSup_eq_span]
    exact Comodule.iSup_groupLikeWeightSpace_eq_top hQ
  obtain ⟨B, hBS, hspan, hli⟩ := exists_linearIndependent k S
  let b : Module.Basis B k (Fin n → k) :=
    Module.Basis.mk hli (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hspan, hS])
  let w := b.reindex (b.indexEquiv (Pi.basisFun k (Fin n)))
  have hw (j : Fin n) :
      ∃ g : GroupLike k Q, w j ∈ _root_.GroupLike.weightSpace (M := Fin n → k) g := by
    have hj : w j ∈ S := hBS (by simp [w, b])
    simpa [S] using hj
  choose χ hχ using hw
  refine ⟨w, χ, fun j ↦ ?_⟩
  have h := _root_.GroupLike.mem_weightSpace.mp (hχ j)
  rwa [Comodule.corestrict_coact_apply, standardComodule_coact,
    CoalgHom.toLinearMap_eq_ofClass] at h

/-- **Simultaneous diagonalization over a diagonalizable Hopf algebra.**

If the group-like elements of `Q` span it, then for every bialgebra morphism
`π : O(GLₙ) → Q` some rational matrix `P` diagonalizes the `Q`-valued point `π`:
`π P = P diag(t)`. The columns of `P` are weight vectors of the standard comodule corestricted
along `π`, and the entries of `t` are their weights. -/
theorem exists_mul_map_eq_map_mul_diagGL {Q : Type u} [CommRing Q] [HopfAlgebra k Q]
    (hQ : Subcoalgebra.groupLikeSetSpan (R := k) (C := Q) Set.univ = ⊤)
    (π : coordinateHopfAlgebra k n →ₐc[k] Q) :
    ∃ (P : GL (Fin n) k) (t : Fin n → Qˣ),
      pointsMulEquiv n (toConv (π : coordinateHopfAlgebra k n →ₐ[k] Q)) *
          Matrix.GeneralLinearGroup.map (algebraMap k Q) P =
        Matrix.GeneralLinearGroup.map (algebraMap k Q) P * diagGL t := by
  obtain ⟨w, χ, hw⟩ := exists_basis_coact_eq_tmul (n := n) (Q := Q) hQ
    (π : coordinateHopfAlgebra k n →ₗc[k] Q)
  let _ := (Pi.basisFun k (Fin n)).invertibleToMatrix w
  refine ⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix w),
    fun j ↦ GroupLike.toUnits k (χ j), ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, diagGL_coe,
    Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.GeneralLinearGroup.map_apply, pointsMulEquiv_apply,
    pointToGeneralLinear_apply, val_unitOfInvertible, Module.Basis.toMatrix_apply,
    Pi.basisFun_repr, BialgHom.coe_toAlgHom, ← genericMatrix_apply]
  have h := sum_mul_algebraMap_eq_of_coact_eq (π : coordinateHopfAlgebra k n →ₗc[k] Q)
    (w j) (χ j) (hw j) i
  rwa [BialgHom.coe_toCoalgHom] at h

/-- **A diagonalizable closed subgroup of `GLₙ` is conjugate into the diagonal torus.**

If the quotient coordinate Hopf algebra of `I` is spanned by its group-like elements, then some
rational point `g` conjugates the diagonal torus to a closed subgroup containing the one cut out
by `I`. Containment of closed subgroups is the reversed inequality of Hopf ideals. -/
theorem exists_conjugate_diagonalTorusDefiningIdeal_le
    (I : HopfIdeal k (coordinateHopfAlgebra k n))
    (hI : DiagonalizableGroup.groupLikeSpannedProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ I)) :
    ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k),
      (diagonalTorusDefiningIdeal k n).conjugate g ≤ I := by
  let Q := CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I
  let π : coordinateHopfAlgebra k n →ₐc[k] Q := (CommHopfAlgCat.mkQuotient _ I).hom
  obtain ⟨P, t, hmat⟩ := exists_mul_map_eq_map_mul_diagGL (n := n) (Q := Q)
    ((DiagonalizableGroup.groupLikeSpannedProperty_iff k _).mp hI) π
  let τ : WithConv (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k] Q) :=
    (SplitTorus.pointsMulEquiv (R := k) (A := Q)).symm fun i ↦ t i.down
  let g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k) :=
    (pointsMulEquiv (R := k) (A := k) n).symm P⁻¹
  have hkey : toConv ((π : coordinateHopfAlgebra k n →ₐ[k] Q).comp
      (HopfAlgebra.pointConjugationAlgHom g)) = diagonalTorusPoints τ := by
    apply (pointsMulEquiv (R := k) (A := Q) n).injective
    rw [HopfAlgebra.comp_pointConjugationAlgHom, map_mul, map_mul, map_inv,
      pointsMulEquiv_mapValue, pointsMulEquiv_diagonalTorusPoints]
    have hτ : diagonalTorusCoordinates (SplitTorus.pointsMulEquiv τ) = t := by
      funext i
      rw [diagonalTorusCoordinates_apply, MulEquiv.apply_symm_apply]
    rw [hτ, MulEquiv.apply_symm_apply, map_inv, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
    exact hmat
  refine ⟨g⁻¹, ?_⟩
  have hle : diagonalTorusDefiningIdeal k n ≤ I.conjugate g := by
    intro x hx
    rw [HopfIdeal.mem_conjugate, ← HopfIdeal.mem_toIdeal,
      ← CommHopfAlgCat.mkQuotient_eq_zero_iff]
    rw [mem_diagonalTorusDefiningIdeal] at hx
    have h := congrArg (fun f ↦ f.ofConv x) hkey
    refine h.trans ?_
    rw [← mapPointsFunctor_diagonalTorusCoordinateMap_app (A := CommAlgCat.of k Q),
      CommHopfAlgCat.mapPointsFunctor_app_apply_apply, hx, map_zero]
  simpa using HopfIdeal.conjugate_mono g⁻¹ hle

/-- **Split maximal tori of `GLₙ` are conjugate to the diagonal torus.** A maximal torus of `GLₙ`
over `k` which is split over `k` is the conjugate of the diagonal torus by a rational point. -/
theorem exists_eq_conjugate_diagonalTorusDefiningIdeal_of_isMaximalTorus
    {I : HopfIdeal k (coordinateHopfAlgebra k n)}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n) I)
    (hsplit : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ I)) :
    ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k),
      I = (diagonalTorusDefiningIdeal k n).conjugate g := by
  exact HopfIdeal.exists_eq_conjugate_of_isMaximalTorus_of_split
    (diagonalTorusDefiningIdeal k n) (isMaximalTorus_diagonalTorusDefiningIdeal k n)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I) hI hsplit

/-- **Any two split maximal tori of `GLₙ` over a field are conjugate** by a rational point
of `GLₙ`. -/
theorem exists_conjugate_eq_of_isMaximalTorus_of_split
    {I J : HopfIdeal k (coordinateHopfAlgebra k n)}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n) I)
    (hJ : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n) J)
    (hsplitI : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ I))
    (hsplitJ : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ J)) :
    ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k), I.conjugate g = J := by
  exact HopfIdeal.exists_conjugate_eq_of_isMaximalTorus_of_split
    (diagonalTorusDefiningIdeal k n) (isMaximalTorus_diagonalTorusDefiningIdeal k n)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I)
    (exists_conjugate_diagonalTorusDefiningIdeal_le J) hI hJ hsplitI hsplitJ

/-- **Maximal tori of `GLₙ` over an algebraically closed field are exactly the conjugates of the
diagonal torus.** The equality is an equality of defining Hopf ideals, hence of closed subgroup
schemes, rather than only of their rational points. -/
theorem isMaximalTorus_iff_exists_eq_conjugate_diagonalTorusDefiningIdeal [IsAlgClosed k]
    (I : HopfIdeal k (coordinateHopfAlgebra k n)) :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n) I ↔
      ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k),
        I = (diagonalTorusDefiningIdeal k n).conjugate g := by
  exact HopfIdeal.isMaximalTorus_iff_exists_eq_conjugate
    (diagonalTorusDefiningIdeal k n) (isMaximalTorus_diagonalTorusDefiningIdeal k n)
    I (exists_conjugate_diagonalTorusDefiningIdeal_le I)

/-- **Any two maximal tori of `GLₙ` over an algebraically closed field are conjugate** by a
rational point of `GLₙ`. -/
theorem exists_conjugate_eq_of_isMaximalTorus [IsAlgClosed k]
    {I J : HopfIdeal k (coordinateHopfAlgebra k n)}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n) I)
    (hJ : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n) J) :
    ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k), I.conjugate g = J := by
  exact HopfIdeal.exists_conjugate_eq_of_isMaximalTorus
    (diagonalTorusDefiningIdeal k n) (isMaximalTorus_diagonalTorusDefiningIdeal k n)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I)
    (exists_conjugate_diagonalTorusDefiningIdeal_le J) hI hJ

end

end TauCeti.GeneralLinear
